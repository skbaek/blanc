#!/usr/bin/env python3
"""Extract audited static-check requests; none is usage until candidate resolution.

Descriptors select actual inspected positive checks, not arbitrary string mentions.
Only AST literals are read; modules and their functions are never executed.
"""
from __future__ import annotations

import ast
import copy
import hashlib
import json
from pathlib import Path
import stat
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


def ascii_digest(value: object) -> str:
    """The existing v3 request/witness digest, not a native identity."""
    return hashlib.sha256(json.dumps(value, sort_keys=True, separators=(",", ":"),
                                     ensure_ascii=True, allow_nan=False).encode()).hexdigest()


class ConsumerSources:
    """Exact candidate bytes for the inspected adapters; no checker execution."""

    def __init__(self, root: Path):
        root = Path(root)
        if not root.is_absolute() or any(part in {".", ".."} for part in root.parts):
            raise StaticConsumerError("candidate root must be absolute without traversal")
        for part in (root, *root.parents):
            if part.is_symlink():
                raise StaticConsumerError("linked candidate root")
        self.root = root.resolve(strict=True)
        if not self.root.is_dir():
            raise StaticConsumerError("candidate root is not a directory")
        self.raw: dict[str, bytes] = {}

    def _path(self, path: str) -> Path:
        relative_path(path)
        current = self.root
        for component in path.split("/"):
            current = current / component
            if current.is_symlink():
                raise StaticConsumerError(f"linked candidate input: {path}")
        return current

    def read(self, path: str) -> str:
        candidate = self._path(path)
        try:
            if not stat.S_ISREG(candidate.stat().st_mode):
                raise StaticConsumerError(f"nonregular candidate input: {path}")
            raw = candidate.read_bytes()
            text = raw.decode("utf-8")
        except (OSError, UnicodeError) as error:
            raise StaticConsumerError(f"unreadable candidate input {path}: {error}") from error
        if path in self.raw and self.raw[path] != raw:
            raise StaticConsumerError(f"candidate input drift: {path}")
        self.raw[path] = raw
        return text

    def recheck(self) -> None:
        for path in list(self.raw):
            self.read(path)

    def span(self, path: str, start: int, end: int | None = None) -> dict:
        self.read(path)
        lines = self.raw[path].splitlines(keepends=True)
        end = start if end is None else end
        if not 1 <= start <= end <= len(lines):
            raise StaticConsumerError(f"invalid candidate line span: {path}")
        return {"path": path, "line": start, "end_line": end,
                "sha256": hashlib.sha256(self.raw[path]).hexdigest(),
                "byte_span": [sum(map(len, lines[:start-1])), sum(map(len, lines[:end]))]}

    def node_span(self, path: str, node: ast.AST) -> dict:
        value = self.span(path, node.lineno, node.end_lineno)
        value["byte_span"] = _span(node, self.raw[path])
        return value

    def location(self, path: str, needle: str) -> dict:
        text = self.read(path)
        at = text.find(needle)
        if at < 0 or text.count(needle) != 1:
            raise StaticConsumerError(f"missing/ambiguous inspected source clause: {path}: {needle}")
        return self.span(path, text[:at].count("\n")+1,
                         text[:at+len(needle)].count("\n")+1)


def literal_module(sources: ConsumerSources, path: str):
    """Inspect constant/path table syntax. No eval, import or function call."""
    try:
        tree = ast.parse(sources.read(path), filename=path)
    except SyntaxError as error:
        raise StaticConsumerError(f"invalid checker syntax: {path}") from error
    env, nodes = {"ROOT": ""}, {}

    def value(node):
        if isinstance(node, ast.Constant):
            return node.value
        if isinstance(node, ast.Name):
            return env[node.id]
        if isinstance(node, (ast.Tuple, ast.List, ast.Set)):
            return [value(n) for n in node.elts]
        if isinstance(node, ast.Dict):
            keys = [value(n) for n in node.keys]
            if len(set(keys)) != len(keys):
                raise StaticConsumerError(f"duplicate selected literal key: {path}")
            return dict(zip(keys, [value(n) for n in node.values]))
        if isinstance(node, ast.BinOp) and isinstance(node.op, ast.Div):
            return str(Path(value(node.left))/value(node.right))
        if isinstance(node, ast.Call) and isinstance(node.func, ast.Name) and not node.keywords:
            if node.func.id == "Path" and len(node.args) == 1:
                return value(node.args[0])
            if node.func.id in {"set", "frozenset", "tuple", "list"} and len(node.args) <= 1:
                return value(node.args[0]) if node.args else []
        raise StaticConsumerError(f"unsupported selected literal shape: {path}")

    for node in tree.body:
        target = (node.targets[0] if isinstance(node, ast.Assign) and len(node.targets) == 1
                  else node.target if isinstance(node, ast.AnnAssign) else None)
        if isinstance(target, ast.Name) and node.value is not None:
            if target.id in nodes:
                raise StaticConsumerError(f"duplicate checker binding: {path}:{target.id}")
            nodes[target.id] = node
            try:
                env[target.id] = value(node.value)
            except (StaticConsumerError, KeyError, TypeError):
                # Unselected computed globals are never run. Selected ones fail
                # when requested below; ROOT retains its symbolic path prefix.
                if target.id != "ROOT":
                    env.pop(target.id, None)

    class Selected(dict):
        def __getitem__(self, key):
            if key not in self:
                raise StaticConsumerError(f"missing/unsupported selected binding: {path}:{key}")
            return super().__getitem__(key)

    def origin(key):
        if key not in nodes:
            raise StaticConsumerError(f"missing selected binding: {path}:{key}")
        # Some inspected structural checks use an unevaluated re.compile table;
        # the producer's full AST contract retains that computed syntax.
        return sources.node_span(path, nodes[key])
    return Selected(env), origin, tree


def checker_shape(text: str, table_bindings: set[str]) -> str:
    """Internal inspected adapter contract; table values stay candidate-derived.

    Positive predicates, callers, imports, function-local data flow and branch
    polarity remain in the AST. This is not a theorem-retention allowlist.
    """
    try:
        tree = copy.deepcopy(ast.parse(text))
    except SyntaxError as error:
        raise StaticConsumerError("invalid inspected checker syntax") from error
    for node in tree.body:
        target = (node.targets[0] if isinstance(node, ast.Assign) and len(node.targets) == 1
                  else node.target if isinstance(node, ast.AnnAssign) else None)
        if isinstance(target, ast.Name) and target.id in table_bindings:
            node.value = ast.Constant("candidate-derived-inspected-table")
    # Documentation edits and line movement are not predicate changes.
    for node in ast.walk(tree):
        if isinstance(node, (ast.Module, ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)):
            if node.body and isinstance(node.body[0], ast.Expr) and isinstance(node.body[0].value, ast.Constant) and isinstance(node.body[0].value.value, str):
                node.body.pop(0)
    return hashlib.sha256(ast.dump(tree, include_attributes=False).encode()).hexdigest()
