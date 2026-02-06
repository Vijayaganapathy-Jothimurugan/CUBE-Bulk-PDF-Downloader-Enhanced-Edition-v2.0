import os
import threading
import time
import uuid
import warnings
import re
import json
import logging
from datetime import datetime
from zipfile import ZipFile
from concurrent.futures import ThreadPoolExecutor, as_completed, TimeoutError
from urllib.parse import urljoin, urlparse, unquote, parse_qs
from typing import Dict, List, Tuple, Optional

import requests
from flask import Flask, render_template, request, send_file, jsonify
from bs4 import BeautifulSoup
from requests.exceptions import SSLError, Timeout, RequestException

warnings.filterwarnings('ignore', message='Unverified HTTPS request')

logging.basicConfig(level=logging.INFO, format='%(asctime)s - %(levelname)s - %(message)s')
logger = logging.getLogger(__name__)

app = Flask(__name__)

MAX_WORKERS = int(os.getenv('MAX_WORKERS', '100'))
PER_REQUEST_TIMEOUT = int(os.getenv('REQUEST_TIMEOUT', '100'))
PER_ITEM_HARD_TIMEOUT = int(os.getenv('ITEM_TIMEOUT', '500'))
MAX_REDIRECT_FOLLOW = 10
MAX_PDF_SIZE_MB = int(os.getenv('MAX_PDF_SIZE_MB', '500'))

BASE_DIR = os.path.dirname(os.path.abspath(__file__))
BASE_OUTPUT = os.path.join(BASE_DIR, 'outputs')

VERIFY_SSL = False

JOBS = {}
LOCK = threading.Lock()

USER_AGENTS = [
    'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/121.0.0.0 Safari/537.36',
    'Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/121.0.0.0 Safari/537.36',
    'Mozilla/5.0 (Windows NT 10.0; Win64; x64; rv:122.0) Gecko/20100101 Firefox/122.0',
    'Mozilla/5.0 (X11; Linux x86_64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/121.0.0.0 Safari/537.36',
    'Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) AppleWebKit/605.1.15 (KHTML, like Gecko) Version/17.2 Safari/605.1.15',
    'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/121.0.0.0 Safari/537.36 Edg/121.0.0.0',
]

ANTI_BOT_HEADERS = {
    'sec-ch-ua': '"Not A(Brand";v="99", "Google Chrome";v="121", "Chromium";v="121"',
    'sec-ch-ua-mobile': '?0',
    'sec-ch-ua-platform': '"Windows"',
    'sec-fetch-dest': 'document',
    'sec-fetch-mode': 'navigate',
    'sec-fetch-site': 'none',
    'sec-fetch-user': '?1',
    'dnt': '1',
}


def get_headers(ua_index=0, referer=None):
    """Generate realistic browser headers with anti-bot measures"""
    base = {
        'User-Agent': USER_AGENTS[ua_index % len(USER_AGENTS)],
        'Accept': 'text/html,application/xhtml+xml,application/xml;q=0.9,application/pdf;q=0.9,image/avif,image/webp,*/*;q=0.8',
        'Accept-Language': 'en-US,en;q=0.9',
        'Accept-Encoding': 'gzip, deflate, br',
        'Connection': 'keep-alive',
        'Upgrade-Insecure-Requests': '1',
        'Cache-Control': 'max-age=0',
    }
    base.update(ANTI_BOT_HEADERS)
    
    if referer:
        base['Referer'] = referer
    
    return base

def ensure_dir(path):
    """Create directory if it doesn't exist"""
    try:
        os.makedirs(path, exist_ok=True)
    except Exception as e:
        logger.error(f"Error creating directory {path}: {e}")

def sanitize_filename(filename):
    """Sanitize filename for safe filesystem usage"""
    if not filename:
        return "unnamed_file.pdf"

    filename = re.sub(r'[<>:"/\\|?*\x00-\x1f\x7f-\x9f]', '_', filename)
    filename = filename.strip('. ')

    if not filename or filename == '.pdf':
        filename = f"file_{int(datetime.utcnow().timestamp())}.pdf"

    if len(filename) > 200:
        name, ext = os.path.splitext(filename)
        filename = name[:200-len(ext)] + ext

    if not filename.lower().endswith('.pdf'):
        filename = filename + '.pdf'

    return filename

def is_pdf_content(content_bytes):
    """Check if content is a PDF by inspecting the header"""
    if not content_bytes or len(content_bytes) < 5:
        return False

    head = content_bytes[:2048]
    head = head.lstrip(b'\x00\x09\x0a\x0c\x0d\x20\xef\xbb\xbf')

    return head.startswith(b'%PDF')

def is_html_content(content_type, content_bytes):
    """Check if content is HTML"""
    if content_type and 'html' in content_type.lower():
        return True
    
    if content_bytes:
        head = content_bytes[:512].lower()
        return b'<html' in head or b'<!doctype' in head or b'<head' in head
    
    return False

def create_session_with_retry(attempt=0):
    """Create a requests session with advanced retry and connection pooling"""
    session = requests.Session()
    session.headers.update(get_headers(attempt))

    from requests.adapters import HTTPAdapter
    from urllib3.util.retry import Retry

    retry_strategy = Retry(
        total=2,  
        backoff_factor=0.3,
        status_forcelist=[429, 500, 502, 503, 504],
        allowed_methods=["HEAD", "GET", "OPTIONS", "POST"],
        raise_on_status=False
    )

    adapter = HTTPAdapter(
        max_retries=retry_strategy,
        pool_connections=15,
        pool_maxsize=30,
        pool_block=False
    )

    session.mount("http://", adapter)
    session.mount("https://", adapter)

    return session

def extract_filename(response, url):
    """Extract filename from response headers or URL"""
    fname = None

    cd = response.headers.get('Content-Disposition', '')
    if cd:
        fname_match = re.findall(r'filename[^;=\n]*=(([\'"]).*?\2|[^;\n]*)', cd)
        if fname_match:
            fname = fname_match[0][0].strip('\'"')
            fname = unquote(fname)

    if not fname:
        fname = os.path.basename(urlparse(url).path)
        fname = unquote(fname)

    if not fname or len(fname) < 3:
        fname = f"file_{int(datetime.utcnow().timestamp())}.pdf"

    return sanitize_filename(fname)

def find_pdf_links_from_html(content, base_url) -> List[Dict]:
    """
    Advanced PDF link extraction with scoring system
    Returns list of dicts: [{'url': str, 'score': int, 'source': str}, ...]
    """
    try:
        soup = BeautifulSoup(content, 'html.parser')
        candidates = []

        def add_candidate(href, text_hint='', source='', extra_score=0):
            if not href or len(href) < 3:
                return
            
            try:
                href_abs = urljoin(base_url, href)
            except Exception:
                return
            
            href_lower = href_abs.lower()
            text_lower = (text_hint or '').lower()
            score = 0

            if '.pdf' in href_lower:
                score += 15
            if href_lower.endswith('.pdf'):
                score += 5  # Boost for exact .pdf extension
            if 'pdf=' in href_lower or 'file=' in href_lower or 'doc=' in href_lower:
                score += 10
            if 'download' in href_lower or 'attach' in href_lower or 'export' in href_lower:
                score += 7
            if any(x in href_lower for x in ['document', 'file', 'nrs', 'publish', 'resource', 'asset']):
                score += 4
            if any(x in href_lower for x in ['/pdf/', '/docs/', '/files/', '/downloads/']):
                score += 6

            if 'pdf' in text_lower:
                score += 8
            if any(x in text_lower for x in ['download', 'view pdf', 'open pdf', 'get pdf']):
                score += 6
            if any(x in text_lower for x in ['full text', 'full document', 'complete document']):
                score += 5
            
            # File extension in URL path
            parsed = urlparse(href_abs)
            if parsed.path.lower().endswith('.pdf'):
                score += 8

            score += extra_score

            if score > 0:
                candidates.append({
                    'url': href_abs,
                    'score': score,
                    'source': source or 'link',
                    'text': text_hint[:100]
                })

        # 1) Common tags - links and embeds
        for tag in soup.find_all(['a', 'link', 'iframe', 'embed', 'object', 'source']):
            href = tag.get('href') or tag.get('src') or tag.get('data')
            text = tag.get_text(strip=True)
            tag_name = tag.name
            add_candidate(href, text, f'{tag_name}-tag')

        # 2) Meta refresh redirects
        for meta in soup.find_all('meta'):
            http_equiv = (meta.get('http-equiv') or '').lower()
            if http_equiv == 'refresh':
                content_attr = meta.get('content') or ''
                m = re.search(r'url=([^;]+)', content_attr, re.IGNORECASE)
                if m:
                    target = m.group(1).strip('"\' ')
                    add_candidate(target, 'meta-refresh', 'meta-refresh', extra_score=12)

        # 3) Form actions
        for form in soup.find_all('form'):
            action = form.get('action')
            if action:
                button_text = ' '.join([btn.get_text(strip=True) for btn in form.find_all(['button', 'input'])])
                add_candidate(action, button_text, 'form-action', extra_score=8)

        # 4) data-* attributes (common in SPAs)
        for attr in ['data-url', 'data-file', 'data-href', 'data-src', 'data-pdf', 'data-download']:
            for tag in soup.find_all(attrs={attr: True}):
                add_candidate(tag.get(attr), tag.get_text(strip=True), f'data-attr-{attr}', extra_score=10)

        # 5) onclick JavaScript
        for tag in soup.find_all(attrs={'onclick': True}):
            onclick = tag.get('onclick', '')
            # Extract URLs from JS
            urls_in_js = re.findall(r'["\']([^"\']+\.pdf[^"\']*)["\']', onclick, re.IGNORECASE)
            for url in urls_in_js:
                add_candidate(url, tag.get_text(strip=True), 'onclick-js', extra_score=11)

        # 6) Script tags with PDF URLs
        for script in soup.find_all('script'):
            script_text = script.string or ''
            urls_in_script = re.findall(r'["\']([^"\']+\.pdf[^"\']*)["\']', script_text, re.IGNORECASE)
            for url in urls_in_script[:5]:  # Limit to avoid too many false positives
                add_candidate(url, '', 'script-tag', extra_score=7)

        if candidates:
            # Sort by score (highest first)
            candidates.sort(key=lambda x: x['score'], reverse=True)
            
            # Deduplicate while preserving order
            seen = set()
            unique_candidates = []
            for c in candidates:
                if c['url'] not in seen:
                    seen.add(c['url'])
                    unique_candidates.append(c)
            
            return unique_candidates

        # 7) Fallback: Aggressive regex scan on raw HTML
        fallback_patterns = [
            r'https?://[^\s"\'<>)]+\.pdf(?:\?[^\s"\'<>)]+)?',
            r'["\']([/][^"\'<>\s]+\.pdf(?:\?[^"\'<>\s]+)?)["\']',
            r'(?:href|src|data|action)=["\']?([^"\'<>\s]+\.pdf[^"\'<>\s]*)["\']?',
        ]

        found = []
        for pattern in fallback_patterns:
            matches = re.findall(pattern, content if isinstance(content, str) else content.decode('utf-8', errors='ignore'), re.IGNORECASE)
            for match in matches:
                try:
                    url = urljoin(base_url, match)
                    if url not in found:
                        found.append(url)
                except Exception:
                    pass

        if found:
            return [{'url': url, 'score': 5, 'source': 'regex-fallback', 'text': ''} for url in found]

    except Exception as e:
        logger.warning(f"Error parsing HTML for PDFs: {e}")

    return []

def try_download_pdf(session, url, referer=None, max_size_bytes=None) -> Dict:
    """
    Attempt to download PDF from URL
    Returns dict with status, content, size, etc.
    """
    if max_size_bytes is None:
        max_size_bytes = MAX_PDF_SIZE_MB * 1024 * 1024

    try:
        headers = session.headers.copy()
        if referer:
            headers['Referer'] = referer

        # Skip HEAD request for speed - go straight to GET
        # Now try GET request with streaming
        resp = session.get(
            url,
            timeout=(PER_REQUEST_TIMEOUT, PER_REQUEST_TIMEOUT * 2),
            allow_redirects=True,
            verify=VERIFY_SSL,
            stream=True,
            headers=headers
        )

        content_type = resp.headers.get('Content-Type', '').lower()
        
        # Download content in chunks with size limit
        content_chunks = []
        total_size = 0
        
        for chunk in resp.iter_content(chunk_size=8192):
            if chunk:
                content_chunks.append(chunk)
                total_size += len(chunk)
                
                if total_size > max_size_bytes:
                    return {
                        'status': 'Failed',
                        'reason': f'File exceeds size limit during download ({MAX_PDF_SIZE_MB}MB)',
                        'content': None,
                        'size': total_size
                    }
        
        content = b''.join(content_chunks)
        
        return {
            'status': 'Success',
            'reason': '',
            'content': content,
            'size': len(content),
            'content_type': content_type,
            'url': resp.url
        }

    except Timeout:
        return {'status': 'Timeout', 'reason': 'Request timeout', 'content': None, 'size': 0}
    except SSLError as e:
        return {'status': 'SSL Error', 'reason': str(e)[:100], 'content': None, 'size': 0}
    except RequestException as e:
        return {'status': 'Connection Error', 'reason': str(e)[:100], 'content': None, 'size': 0}
    except Exception as e:
        return {'status': 'Error', 'reason': str(e)[:100], 'content': None, 'size': 0}

def process_single_url(url, session, referer=None) -> Dict:
    """
    Process a single URL and return comprehensive information about PDFs found
    Returns: {
        'status': str,
        'reason': str,
        'content': bytes or None,
        'size': int,
        'content_type': str,
        'final_url': str,
        'pdfs_found': [{'url': str, 'score': int, 'source': str}],
        'pdf_count': int
    }
    """
    result = try_download_pdf(session, url, referer)
    
    if result['status'] == 'Success' and result['content']:
        # Check if it's actually a PDF
        if is_pdf_content(result['content']):
            result['pdfs_found'] = [{'url': url, 'score': 100, 'source': 'direct'}]
            result['pdf_count'] = 1
            result['final_url'] = result.get('url', url)
            return result
        
        # If it's HTML, scan for PDF links
        if is_html_content(result.get('content_type', ''), result['content']):
            try:
                pdf_links = find_pdf_links_from_html(result['content'], url)
                
                if pdf_links:
                    result['status'] = 'Multiple PDFs Found'
                    result['reason'] = f'Found {len(pdf_links)} potential PDF link(s) in HTML page'
                    result['pdfs_found'] = pdf_links
                    result['pdf_count'] = len(pdf_links)
                    result['content'] = None  # Don't keep HTML content
                    return result
                else:
                    result['status'] = 'No PDF'
                    result['reason'] = 'HTML page with no PDF links detected'
                    result['content'] = None
                    result['pdfs_found'] = []
                    result['pdf_count'] = 0
                    return result
            except Exception as e:
                result['status'] = 'Error'
                result['reason'] = f'Error parsing HTML: {str(e)[:100]}'
                result['content'] = None
                result['pdfs_found'] = []
                result['pdf_count'] = 0
                return result
        else:
            # Unknown content type that's not PDF
            result['status'] = 'No PDF'
            result['reason'] = f'Downloaded content is not PDF (type: {result.get("content_type", "unknown")})'
            result['content'] = None
            result['pdfs_found'] = []
            result['pdf_count'] = 0
            return result
    
    result['pdfs_found'] = []
    result['pdf_count'] = 0
    return result

def process_single_item_with_timeout(i, url, fname, out_dir, total):
    """
    Process a single item with retry logic and comprehensive error handling
    """
    max_retries = 2  # Reduced for speed
    info = {}
    
    print(f"[{i+1}/{total}] Processing: {url[:60]}...")  # Progress indicator
    
    for attempt in range(max_retries):
        try:
            session = create_session_with_retry(attempt)
            
            # Add small delay between attempts
            if attempt > 0:
                time.sleep(0.5)  # Shorter delay for speed
            
            result = process_single_url(url, session, referer=None)
            
            # Handle different scenarios
            if result['status'] == 'Success' and result['content'] and is_pdf_content(result['content']):
                # Direct PDF download success
                if not fname:
                    fname = extract_filename(
                        type('obj', (object,), {'headers': {'Content-Disposition': ''}}),
                        result.get('final_url', url)
                    )
                
                final_fname = sanitize_filename(fname)
                save_path = os.path.join(out_dir, final_fname)
                
                # Handle duplicate filenames
                base, ext = os.path.splitext(final_fname)
                counter = 1
                while os.path.exists(save_path):
                    final_fname = f"{base}_{counter}{ext}"
                    save_path = os.path.join(out_dir, final_fname)
                    counter += 1
                
                with open(save_path, 'wb') as f:
                    f.write(result['content'])
                
                info = {
                    'status': 'Success',
                    'reason': 'PDF downloaded successfully',
                    'content_type': result.get('content_type', 'application/pdf'),
                    'saved_path': save_path,
                    'found_pdf': result.get('final_url', url),
                    'file_size': result['size'],
                    'pdf_count': 1
                }
                break
                
            elif result['status'] == 'Multiple PDFs Found':
                # Multiple PDFs detected - try to download the best one
                pdf_links = result.get('pdfs_found', [])
                best_pdf = None
                
                # Try top 3 candidates
                for pdf_candidate in pdf_links[:3]:
                    pdf_url = pdf_candidate['url']
                    pdf_result = try_download_pdf(session, pdf_url, referer=url)
                    
                    if pdf_result['status'] == 'Success' and pdf_result['content']:
                        if is_pdf_content(pdf_result['content']):
                            best_pdf = pdf_result
                            best_pdf['found_pdf'] = pdf_url
                            break
                
                if best_pdf and best_pdf['content']:
                    # Successfully downloaded a PDF from the page
                    if not fname:
                        fname = extract_filename(
                            type('obj', (object,), {'headers': {'Content-Disposition': ''}}),
                            best_pdf.get('found_pdf', url)
                        )
                    
                    final_fname = sanitize_filename(fname)
                    save_path = os.path.join(out_dir, final_fname)
                    
                    # Handle duplicates
                    base, ext = os.path.splitext(final_fname)
                    counter = 1
                    while os.path.exists(save_path):
                        final_fname = f"{base}_{counter}{ext}"
                        save_path = os.path.join(out_dir, final_fname)
                        counter += 1
                    
                    with open(save_path, 'wb') as f:
                        f.write(best_pdf['content'])
                    
                    info = {
                        'status': 'Success',
                        'reason': f'Found {len(pdf_links)} PDF link(s), downloaded best match',
                        'content_type': best_pdf.get('content_type', 'application/pdf'),
                        'saved_path': save_path,
                        'found_pdf': best_pdf.get('found_pdf', ''),
                        'file_size': best_pdf['size'],
                        'pdf_count': len(pdf_links)
                    }
                    break
                else:
                    # Couldn't download any of the PDFs
                    info = {
                        'status': 'Multiple PDFs Found',
                        'reason': f'Detected {len(pdf_links)} PDF link(s) but could not download any',
                        'content_type': 'text/html',
                        'saved_path': '',
                        'found_pdf': ', '.join([p['url'] for p in pdf_links[:3]]),
                        'file_size': 0,
                        'pdf_count': len(pdf_links)
                    }
                    # Don't break, try next attempt
                    
            elif result['status'] in ['Timeout', 'Connection Error', 'SSL Error']:
                info = {
                    'status': result['status'],
                    'reason': result['reason'],
                    'content_type': '',
                    'saved_path': '',
                    'found_pdf': '',
                    'file_size': 0,
                    'pdf_count': 0
                }
                # These are retryable
                if attempt < max_retries - 1:
                    continue
                    
            elif result['status'] == 'No PDF':
                info = {
                    'status': 'No PDF',
                    'reason': result['reason'],
                    'content_type': result.get('content_type', ''),
                    'saved_path': '',
                    'found_pdf': '',
                    'file_size': 0,
                    'pdf_count': 0
                }
                # Try once more with different user agent
                if attempt < max_retries - 1:
                    continue
                else:
                    break
                    
            else:
                # Other errors
                info = {
                    'status': result['status'],
                    'reason': result['reason'],
                    'content_type': result.get('content_type', ''),
                    'saved_path': '',
                    'found_pdf': '',
                    'file_size': 0,
                    'pdf_count': 0
                }
                if attempt < max_retries - 1:
                    continue
                else:
                    break

        except Timeout:
            info = {
                'status': 'Timeout',
                'reason': f'Request timeout after {PER_REQUEST_TIMEOUT}s',
                'content_type': '',
                'saved_path': '',
                'found_pdf': '',
                'file_size': 0,
                'pdf_count': 0
            }
            if attempt < max_retries - 1:
                continue
                
        except Exception as e:
            info = {
                'status': 'Error',
                'reason': str(e)[:200],
                'content_type': '',
                'saved_path': '',
                'found_pdf': '',
                'file_size': 0,
                'pdf_count': 0
            }
            if attempt < max_retries - 1:
                continue

    file_size_mb = round(info.get('file_size', 0) / (1024 * 1024), 2) if info.get('file_size') else 0

    return {
        'Line': i + 1,
        'URL': url,
        'File Name': fname,
        'Status': info.get('status', 'Unknown'),
        'Reason': info.get('reason', ''),
        'Content-Type': info.get('content_type', ''),
        'Found PDF': info.get('found_pdf', ''),
        'Saved Path': info.get('saved_path', ''),
        'File Size (MB)': file_size_mb,
        'PDF Count': info.get('pdf_count', 0)
    }

def process_job(job_id, urls, file_names, base_out):
    """Process all URLs in a job with parallel execution"""
    total = len(urls)
    out_pdfs = os.path.join(base_out, 'pdfs')

    try:
        ensure_dir(base_out)
        ensure_dir(out_pdfs)
    except Exception as e:
        logger.error(f"CRITICAL ERROR: Cannot create directories: {e}")
        with LOCK:
            JOBS[job_id]['status'] = 'error'
        return

    summary = [None] * total
    max_workers = min(MAX_WORKERS, max(3, total))  # More conservative

    with ThreadPoolExecutor(max_workers=max_workers) as executor:
        future_to_index = {}
        for i in range(total):
            url = urls[i]
            fname = file_names[i] if i < len(file_names) else ''
            future = executor.submit(process_single_item_with_timeout, i, url, fname, out_pdfs, total)
            future_to_index[future] = i

        completed = 0
        for future in as_completed(future_to_index, timeout=None):
            i = future_to_index[future]
            try:
                result = future.result(timeout=PER_ITEM_HARD_TIMEOUT + 10)
                summary[i] = result
                completed += 1

                with LOCK:
                    JOBS[job_id]['processed'] = completed
                    JOBS[job_id]['summary'] = [s for s in summary if s is not None]

            except TimeoutError:
                summary[i] = {
                    'Line': i + 1,
                    'URL': urls[i],
                    'File Name': file_names[i] if i < len(file_names) else '',
                    'Status': 'Timeout',
                    'Reason': f'Download exceeded {PER_ITEM_HARD_TIMEOUT}s hard limit',
                    'Content-Type': '',
                    'Found PDF': '',
                    'Saved Path': '',
                    'File Size (MB)': 0,
                    'PDF Count': 0
                }
                completed += 1
                with LOCK:
                    JOBS[job_id]['processed'] = completed
                    JOBS[job_id]['summary'] = [s for s in summary if s is not None]
            except Exception as e:
                logger.error(f"Error processing URL {i}: {e}")
                summary[i] = {
                    'Line': i + 1,
                    'URL': urls[i],
                    'File Name': file_names[i] if i < len(file_names) else '',
                    'Status': 'Error',
                    'Reason': str(e)[:200],
                    'Content-Type': '',
                    'Found PDF': '',
                    'Saved Path': '',
                    'File Size (MB)': 0,
                    'PDF Count': 0
                }
                completed += 1
                with LOCK:
                    JOBS[job_id]['processed'] = completed
                    JOBS[job_id]['summary'] = [s for s in summary if s is not None]

    summary = [s for s in summary if s is not None]

    # Create PDFs zip
    zip_path = os.path.join(base_out, 'pdfs.zip')
    with ZipFile(zip_path, 'w') as zf:
        for r in summary:
            sp = r.get('Saved Path')
            if sp and os.path.exists(sp):
                try:
                    zf.write(sp, os.path.basename(sp))
                except Exception as e:
                    logger.error(f"Error adding file to zip: {e}")

    with LOCK:
        JOBS[job_id]['status'] = 'done'
        JOBS[job_id]['summary'] = summary

# ------------------ FLASK ROUTES ------------------

@app.route('/')
def index():
    return render_template('index.html')

@app.route('/start', methods=['POST'])
def start_job():
    url_text = request.form.get('urls', '').strip()
    file_text = request.form.get('file_names', '').strip()

    urls = [l.strip() for l in url_text.splitlines() if l.strip()]
    file_names = [l.strip() for l in file_text.splitlines() if l.strip()]

    if not urls:
        return jsonify({'error': 'No URLs provided'}), 400

    while len(file_names) < len(urls):
        file_names.append('')

    timestamp = datetime.now().strftime('%Y-%m-%d_%H-%M-%S')
    session_folder = f'session_{timestamp}_{uuid.uuid4().hex[:6]}'
    base_out = os.path.join(BASE_OUTPUT, session_folder)
    ensure_dir(base_out)

    job_id = session_folder
    with LOCK:
        JOBS[job_id] = {
            'status': 'running',
            'processed': 0,
            'total': len(urls),
            'summary': [],
            'out': base_out
        }

    t = threading.Thread(target=process_job, args=(job_id, urls, file_names, base_out), daemon=True)
    t.start()

    return jsonify({'job_id': job_id, 'status': 'started'})

@app.route('/status/<job_id>')
def job_status(job_id):
    with LOCK:
        job = JOBS.get(job_id)
        if not job:
            return jsonify({'error': 'not found'}), 404
        return jsonify({
            'status': job['status'],
            'processed': job['processed'],
            'total': job['total']
        })

@app.route('/results/<job_id>')
def results(job_id):
    with LOCK:
        job = JOBS.get(job_id)
        if not job:
            return "Job not found", 404
        summary = job.get('summary', [])
        session_folder = os.path.basename(job['out'])

    stats = {
        'total': len(summary),
        'success': 0,
        'failed': 0,
        'no_pdf': 0,
        'error': 0,
        'timeout': 0,
        'forbidden': 0,
        'ssl_error': 0,
        'not_found': 0,
        'protected': 0,
        'multiple_pdfs': 0,
        'other': 0,
        'total_size_mb': 0,
        'total_pdfs_detected': 0
    }

    for row in summary:
        status = row.get('Status', '')
        stats['total_size_mb'] += row.get('File Size (MB)', 0)
        stats['total_pdfs_detected'] += row.get('PDF Count', 0)

        if status == 'Success':
            stats['success'] += 1
        elif status == 'Multiple PDFs Found':
            stats['multiple_pdfs'] += 1
        elif status == 'Failed':
            stats['failed'] += 1
        elif status == 'No PDF':
            stats['no_pdf'] += 1
        elif status == 'Timeout':
            stats['timeout'] += 1
        elif '404' in status:
            stats['not_found'] += 1
        elif '403' in status or 'Forbidden' in status:
            stats['forbidden'] += 1
        elif 'SSL' in status:
            stats['ssl_error'] += 1
        elif status == 'Protected':
            stats['protected'] += 1
        elif status in ['Error', 'Network Error', 'Connection Error', 'HTTP Error']:
            stats['error'] += 1
        else:
            stats['other'] += 1

    stats['success_rate'] = round((stats['success'] / stats['total'] * 100), 1) if stats['total'] > 0 else 0
    stats['total_size_mb'] = round(stats['total_size_mb'], 2)

    return render_template('results.html', summary=summary, session_folder=session_folder, stats=stats)

@app.route('/download_zip/<session_folder>')
def download_zip(session_folder):
    p = os.path.join(BASE_OUTPUT, session_folder, 'pdfs.zip')
    if not os.path.exists(p):
        return ('Missing', 404)
    return send_file(p, as_attachment=True, download_name='pdfs.zip')

if __name__ == '__main__':
    ensure_dir(BASE_OUTPUT)
    app.run(host='0.0.0.0', port=5000, debug=True, threaded=True)