#!/usr/bin/env python3
"""Extract audited static-check requests; none is usage until candidate resolution.

Descriptors select actual inspected positive checks, not arbitrary string mentions.
Only AST literals are read; modules and their functions are never executed.
"""
from __future__ import annotations

import ast
import hashlib
from module_path_policy import _raw_components, validate_source_path


class StaticConsumerError(ValueError):
    pass


def relative_path(value: str) -> str:
    try:
        _raw_components(value, module=False)
    except ValueError as error:
        raise StaticConsumerError(str(error)) from error
    return value


def target_source_path(value: str) -> str:
    """Production targets use the shared source language; scripts use bound syntax."""
    relative_path(value)
    if value == "Blanc.lean" or value.split("/")[0].casefold() == "blanc":
        try:
            validate_source_path(value)
        except ValueError as error:
            raise StaticConsumerError(str(error)) from error
    return value


def _span(node: ast.AST, raw: bytes) -> list[int]:
    lines = raw.splitlines(keepends=True)
    return [sum(map(len, lines[:node.lineno - 1])) + node.col_offset,
            sum(map(len, lines[:node.end_lineno - 1])) + node.end_col_offset]


def literal_requests(path: str, raw: bytes, descriptor: dict) -> list[dict]:
    """Read a selected literal collection plus its actual consumer Name loads.

    A descriptor's rationale must be independently reviewed; AST load existence
    does not establish semantic consumer intent. Missing/dynamic collections fail.
    """
    path = relative_path(path)
    target = target_source_path(descriptor["target_source"])
    binding, function = descriptor["binding"], descriptor["function"]
    kind = descriptor["kind"]
    if kind not in {"checked-name", "checked-type", "checked-axioms", "script-check"}:
        raise StaticConsumerError(f"unsupported check kind: {kind}")
    if not isinstance(descriptor.get("rationale"), str) or not descriptor["rationale"].strip():
        raise StaticConsumerError("audited consumer rationale required")
    try:
        tree = ast.parse(raw.decode("utf-8"), filename=path)
    except (UnicodeDecodeError, SyntaxError) as error:
        raise StaticConsumerError(f"invalid Python consumer {path}: {error}") from error
    assignments = [n for n in tree.body if isinstance(n, ast.Assign)
                   and any(isinstance(t, ast.Name) and t.id == binding for t in n.targets)]
    functions = [n for n in tree.body if isinstance(n, (ast.FunctionDef, ast.AsyncFunctionDef))
                 and n.name == function]
    if len(assignments) != 1 or len(functions) != 1:
        raise StaticConsumerError("selected binding/function must occur exactly once at top level")
    value = assignments[0].value
    nodes = value.keys if isinstance(value, ast.Dict) else (
        value.elts if isinstance(value, (ast.Set, ast.List, ast.Tuple)) else None)
    if not nodes or any(not isinstance(n, ast.Constant) or not isinstance(n.value, str)
                        or not n.value for n in nodes):
        raise StaticConsumerError("selected collection must contain nonempty literal names only")
    names = [n.value for n in nodes]
    if len(set(names)) != len(names):
        raise StaticConsumerError("duplicate static consumer name")
    shadowed = any((isinstance(n, ast.Name) and n.id == binding and isinstance(n.ctx, (ast.Store, ast.Del)))
                   or (isinstance(n, ast.arg) and n.arg == binding)
                   for n in ast.walk(functions[0]))
    if shadowed:
        raise StaticConsumerError("selected consumer shadows or rebinds collection")
    loads = [n for n in ast.walk(functions[0]) if isinstance(n, ast.Name)
             and n.id == binding and isinstance(n.ctx, ast.Load)]
    if not loads:
        raise StaticConsumerError("selected function does not consume binding")
    digest = hashlib.sha256(raw).hexdigest()
    result = []
    for node in nodes:
        start, end = _span(node, raw)
        identity = f"{path}:{digest}:{binding}:{function}:{start}:{end}:{target}:{kind}"
        result.append({"id": hashlib.sha256(identity.encode()).hexdigest(),
                       "path": path, "source_sha256": digest, "span": [start, end],
                       "name": node.value, "target_source": target, "kind": kind,
                       "binding": binding, "function": function,
                       "consumer_spans": sorted(_span(n, raw) for n in loads),
                       "rationale": descriptor["rationale"]})
    return result
