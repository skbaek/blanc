#!/usr/bin/env python3
"""Stable, private host identity for Blanc's local evidence stores.

The identifier is deliberately derived from an OS-owned installation token
rather than a network hostname.  Only a domain-separated digest leaves this
module; the raw token is never returned, logged, or stored.  Linux machine-id
and a virtual machine's IOPlatformUUID can be cloned deliberately, so this is
not a hardware-uniqueness claim.  The existing same-host, same-user local trust
boundary assumes those OS tokens are provisioned distinctly.

Production callers get no identity override.  Tests exercise the OS boundary
through the private reader-shaped helper instead of patching a production
caller-provided identity into the trust decision.
"""

from __future__ import annotations

import hashlib
import platform
import re
import subprocess
import uuid
from pathlib import Path
from typing import Protocol


IDENTITY_VERSION = "v2"
_IDENTITY_DOMAIN = b"blanc-local-host-identity-v2\0"
_LINUX_MACHINE_ID_PATHS = (Path("/etc/machine-id"), Path("/var/lib/dbus/machine-id"))
_MACOS_IOREG = Path("/usr/sbin/ioreg")
_MACOS_UUID = re.compile(r'"IOPlatformUUID"\s*=\s*"([0-9A-Fa-f-]{36})"')
_LINUX_MACHINE_ID = re.compile(r"[0-9a-fA-F]{32}")
_SUPPORTED_MACHINES = {
    "darwin": frozenset({"arm64", "x86_64"}),
    "linux": frozenset({
        "aarch64", "amd64", "arm64", "i386", "i486", "i586", "i686",
        "ppc64le", "riscv64", "s390x", "x86_64",
    }),
}

# The grammar an untrusted store label must match before it may be echoed in a
# diagnostic.  It is *derived* from the supported set the derivation itself
# uses, because two hand-maintained lists that agree today drift tomorrow and
# the failure is a legitimate identity rendered `<unrecognized>`; there is only
# one list.  The version field is bounded rather than open: everything here is
# attacker-chosen text from a file this process did not write, and an unbounded
# `v[0-9]+-` let `darwin-arm64-v8005551212-...` through a check whose entire
# purpose is to bound what may be echoed.
_IDENTITY_VERSION_DIGITS = 3
_IDENTITY_DIGEST_HEX = 16


def _public_identity_pattern(supported: dict[str, frozenset[str]]) -> re.Pattern[str]:
    platforms = "|".join(
        "{}-(?:{})".format(
            re.escape(system),
            "|".join(re.escape(machine) for machine in sorted(machines)),
        )
        for system, machines in sorted(supported.items())
    )
    return re.compile(
        f"(?:{platforms})"
        f"-(?:v[0-9]{{1,{_IDENTITY_VERSION_DIGITS}}}-)?[0-9a-f]{{{_IDENTITY_DIGEST_HEX}}}"
    )


_PUBLIC_IDENTITY = _public_identity_pattern(_SUPPORTED_MACHINES)


class HostIdentityError(RuntimeError):
    """The host cannot be bound to a supported stable OS installation identity."""


class _HostReader(Protocol):
    def system(self) -> str: ...

    def machine(self) -> str: ...

    def read_text(self, path: Path) -> str: ...

    def run(self, command: tuple[str, ...]) -> str: ...


class _ProductionHostReader:
    def system(self) -> str:
        return platform.system()

    def machine(self) -> str:
        return platform.machine()

    def read_text(self, path: Path) -> str:
        return path.read_text(encoding="utf-8")

    def run(self, command: tuple[str, ...]) -> str:
        try:
            result = subprocess.run(
                command,
                capture_output=True,
                text=True,
                check=False,
                timeout=5,
            )
        except (OSError, subprocess.SubprocessError) as error:
            raise HostIdentityError("stable macOS machine identity is unavailable") from error
        if result.returncode != 0:
            raise HostIdentityError("stable macOS machine identity is unavailable")
        return result.stdout


def _macos_token(reader: _HostReader) -> tuple[str, str]:
    output = reader.run((str(_MACOS_IOREG), "-rd1", "-c", "IOPlatformExpertDevice"))
    match = _MACOS_UUID.search(output)
    if match is None:
        raise HostIdentityError("stable macOS machine identity is unavailable")
    try:
        token = str(uuid.UUID(match.group(1)))
    except ValueError as error:
        raise HostIdentityError("stable macOS machine identity is malformed") from error
    if uuid.UUID(token).int == 0:
        raise HostIdentityError("stable macOS machine identity is invalid")
    return "ioplatformuuid", token


def _linux_token(reader: _HostReader) -> tuple[str, str]:
    tokens: set[str] = set()
    for path in _LINUX_MACHINE_ID_PATHS:
        try:
            text = reader.read_text(path).strip()
        except (OSError, UnicodeError):
            continue
        if not _LINUX_MACHINE_ID.fullmatch(text) or int(text, 16) == 0:
            raise HostIdentityError("stable Linux machine identity is malformed")
        tokens.add(text.lower())
    if not tokens:
        raise HostIdentityError("stable Linux machine identity is unavailable")
    if len(tokens) != 1:
        raise HostIdentityError("stable Linux machine identity sources disagree")
    return "machine-id", next(iter(tokens))


def _derive_host_identity(reader: _HostReader) -> str:
    """Derive through an injectable OS reader used only by focused controls."""

    system = reader.system().strip().lower()
    machine = reader.machine().strip().lower()
    if not system or not machine:
        raise HostIdentityError("host platform identity is unavailable")
    supported = _SUPPORTED_MACHINES.get(system)
    if supported is None:
        raise HostIdentityError(f"stable host identity is unsupported on {system}")
    if machine not in supported:
        raise HostIdentityError("stable host identity is unsupported on this architecture")
    if system == "darwin":
        source, token = _macos_token(reader)
    elif system == "linux":
        source, token = _linux_token(reader)
    else:
        # Unreachable while the supported set and the branches above agree.
        # Adding an architecture family to `_SUPPORTED_MACHINES` without a
        # token source must refuse identity, not raise `UnboundLocalError`:
        # a contract whose promise is "unsupported platforms fail closed"
        # cannot answer an unsupported platform with a crash.
        raise HostIdentityError(f"stable host identity has no token source on {system}")
    payload = _IDENTITY_DOMAIN + b"\0".join(
        part.encode("utf-8") for part in (system, machine, source, token)
    )
    digest = hashlib.sha256(payload).hexdigest()[:16]
    return f"{system}-{machine}-{IDENTITY_VERSION}-{digest}"


def stable_host_identity() -> str:
    """Return this machine's stable hashed identity; accepts no override."""

    return _derive_host_identity(_ProductionHostReader())


def is_public_host_identity(value: str) -> bool:
    """Whether an untrusted store label is safe to echo in diagnostics."""

    return _PUBLIC_IDENTITY.fullmatch(value) is not None
