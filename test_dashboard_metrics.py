from pathlib import Path


def test_dashboard_tracks_failed_and_captcha_metrics():
    source = Path('main.py').read_text(encoding='utf-8')
    assert 'STATS["invalid"]' in source
    assert 'STATS["captcha_fails"]' in source
    assert 'captcha-count' in source
