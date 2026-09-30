#!/usr/bin/env python3
"""Light IO controls. Every native call must stop before frontend initialization.

Runtime parser/TryThis/replay evidence needs an admitted fixture run separately.
"""
from pathlib import Path
import os
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
        # A stand-in admission function refuses before any native worker starts.
        # Copy only the launcher; no build or Lean elaboration occurs here.
        standin = folder / 'standin'
        (standin / 'scripts').mkdir(parents=True)
        (standin / '.lake/build/bin').mkdir(parents=True)
        fake_binary = standin / '.lake/build/bin/simpCollector'
        fake_binary.touch()
        fake_binary.chmod(0o755)
        launcher = standin / 'scripts/run-simp-collector.sh'
        launcher.write_bytes(LAUNCHER.read_bytes())
        launcher.chmod(0o755)
        request = standin / 'request.txt'
        (standin / 'scripts/gate-semaphore.sh').write_text(
            'GATE_SEMAPHORE_ENTRY="$ROOT/.lake/build/bin/simpCollector"\n'
            'gate_semaphore_release() { :; }\n'
            'gate_semaphore_acquire() { printf "%s\\n" "$@" > "$ROOT/request.txt"; return 1; }\n'
        )
        result = invoke(launcher, folder / 'not-created.json')
        assert result.returncode == 2, result
        assert request.read_text().splitlines()[1:] == ['8', 'sensitive']
        request.unlink()
        for overrides in [
            {'BLANC_GATE_SEMAPHORE_MEMORY_GIB': '1'},
            {'BLANC_GATE_SEMAPHORE': 'off'},
            {'BLANC_GATE_SEMAPHORE': 'inherited'},
        ]:
            result = subprocess.run(
                [str(launcher), 'a', 'b', 'c', str(folder / 'not-created.json')],
                capture_output=True, text=True, env={**os.environ, **overrides}, timeout=10,
            )
            assert result.returncode == 2 and 'REFUSED' in result.stderr, result
            assert not request.exists(), 'Override reached admission'
    print('PASS collector IO/admission controls: sentinel, no admission, dangling link, failed reservation cleanup, 8GiB sensitive, override refusal')


if __name__ == '__main__':
    main()
