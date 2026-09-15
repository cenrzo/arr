from pathlib import Path


def test_safe_token_limits():
    source = Path('main.py').read_text(encoding='utf-8')
    assert '"token_join_limit": 5' in source
    assert '"max_guild_limit": 8' in source
