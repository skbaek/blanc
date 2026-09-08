"""Strict JSON primitive shared by Blanc's evidence tools.

This module owns syntax parsing plus rejection of duplicate object keys and
the named non-finite tokens ``NaN`` and ``Infinity`` (including
``-Infinity``). Callers retain their own exception types and diagnostic
wording by translating the structured errors below.
"""

from __future__ import annotations

import json
from typing import Any


class DuplicateKeyError(ValueError):
    def __init__(self, key: str):
        super().__init__(key)
        self.key = key


class NonFiniteNumberError(ValueError):
    def __init__(self, value: str):
        super().__init__(value)
        self.value = value


def loads(data: bytes | str) -> Any:
    """Parse one strict JSON value.

    ``json.loads`` already rejects malformed syntax. These hooks reject its
    named non-finite token extension. They do not add a post-parse finiteness
    check: a finite-spelling overflow such as ``1e999`` retains stdlib behavior
    and produces infinity. Every evidence entry point gets the same primitive
    behavior without sharing any higher-level schema policy.
    """

    def object_pairs(items: list[tuple[str, Any]]) -> dict[str, Any]:
        result: dict[str, Any] = {}
        for key, value in items:
            if key in result:
                raise DuplicateKeyError(key)
            result[key] = value
        return result

    def invalid_constant(value: str) -> None:
        raise NonFiniteNumberError(value)

    return json.loads(
        data, object_pairs_hook=object_pairs, parse_constant=invalid_constant
    )
