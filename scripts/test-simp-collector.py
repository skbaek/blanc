#!/usr/bin/env python3
"""Light IO controls. Every native call must stop before frontend initialization.

Runtime parser/TryThis/replay evidence needs an admitted fixture run separately.
"""
from pathlib import Path
import subprocess
import tempfile


ROOT = Path(__file__).resolve().parent.parent
BINARY = ROOT / '.lake/build/bin/simpCollector'
LAUNCHER = ROOT / 'scripts/run-simp-collector.sh'


def invoke(command, output):
    return subprocess.run(
        [str(command), 'missing-original.lean', 'missing-buffer.lean',
         'missing-setup.json', str(output)],
        cwd=ROOT, capture_output=True, text=True, timeout=10,
    )


def main():
    assert BINARY.is_file(), 'Build simpCollector through the owned wrapper first'
    with tempfile.TemporaryDirectory(prefix='simp-collector-io-') as directory:
        folder = Path(directory)
        sentinel = folder / 'sentinel.json'
        original = b'PREEXISTING evidence must survive\n'
        sentinel.write_bytes(original)
        for command, diagnostic in [
            (LAUNCHER, 'COLLECTOR output already exists'),
            (BINARY, 'COLLECTOR fresh output required'),
        ]:
            result = invoke(command, sentinel)
            assert result.returncode == 1, result
            assert diagnostic in result.stderr, result
            assert sentinel.read_bytes() == original
            assert 'COLLECTOR-ADMISSION' not in result.stderr
        dangling = folder / 'dangling.json'
        dangling.symlink_to(folder / 'absent-target')
        for command in [LAUNCHER, BINARY]:
            result = invoke(command, dangling)
            assert result.returncode == 1, result
            assert 'COLLECTOR' in result.stderr, result
            assert dangling.is_symlink() and not dangling.exists()
        fresh = folder / 'fresh.json'
        result = invoke(BINARY, fresh)
        assert result.returncode == 1, result
        assert 'missing-buffer.lean' in result.stderr, result
        assert not fresh.exists(), 'Failed collection retained reserved output'
    print('PASS collector IO controls: sentinel, no admission, dangling link, failed reservation cleanup')


if __name__ == '__main__':
    main()
