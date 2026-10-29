"""Restricted independent L5 literal reader for the isolated writer prototype.

Source-fidelity grammar only: no writer import, Lean parser, proof, validator,
archive admission or fetched-data authority. Adapted from the prior separately
recorded synthetic-prototype/strict_reader.py; its evidence remains unchanged.
"""
from dataclasses import dataclass
import re

IDENT = r"[A-Za-z][A-Za-z0-9_]*"
HEADER = re.compile(r"(private )?def (" + IDENT + r") : Bytes :=\n")
LITERAL = re.compile(r"  \[([^]]*)\]\n")
TOKEN_LIST = re.compile(r"[ \t\n]*(?:0x[0-9a-f]{2}(?:[ \t\n]*,[ \t\n]*0x[0-9a-f]{2})*)?[ \t\n]*")
APPEND = re.compile(r"  (" + IDENT + r") \+\+ (" + IDENT + r")\n")
ALIAS = re.compile(r"  (" + IDENT + r")\n")


class FidelityError(ValueError):
    pass


def require(condition, message):
    if not condition:
        raise FidelityError(message)


@dataclass(frozen=True)
class Declaration:
    private: bool
    name: str
    kind: str
    value: object


def parse_syntax(text):
    """Consume the complete region; syntax alone permits arbitrary join names."""
    result = []
    position = 0
    while position < len(text):
        header = HEADER.match(text, position)
        require(header is not None, f"fidelity: declaration grammar at {position}")
        position = header.end()
        literal = LITERAL.match(text, position)
        append = APPEND.match(text, position)
        alias = ALIAS.match(text, position)
        if literal:
            tokens = literal[1]
            require(TOKEN_LIST.fullmatch(tokens) is not None, "fidelity: byte literal grammar")
            value = bytes(int(token, 16) for token in re.findall(r"0x[0-9a-f]{2}", tokens))
            kind, end = "literal", literal.end()
        elif append:
            value, kind, end = (append[1], append[2]), "append", append.end()
        elif alias:
            value, kind, end = alias[1], "alias", alias.end()
        else:
            raise FidelityError(f"fidelity: body grammar at {position}")
        result.append(Declaration(bool(header[1]), header[2], kind, value))
        position = end
        if position < len(text):
            require(text[position:position + 1] == "\n", "fidelity: declaration separator")
            position += 1
            require(position < len(text), "fidelity: trailing empty declaration")
    require(bool(result), "fidelity: empty region")
    return result


def validate_source(text, root, expected, shared_literals=None):
    """Validate exact source shape and bytes from independently supplied data.

    The tree is derived recursively from chunk-index ranges and powers of two,
    rather than reproducing the serializer's iterative pairing loop. Its
    completed join nodes are sorted into required declaration order afterward.
    With a shared context, equal leaves must name the first previously validated
    literal. The context advances only after this complete field passes.
    """
    require(re.fullmatch(r"[A-Za-z][A-Za-z0-9]*", root) is not None,
            "fidelity: expected root identifier")
    declarations = parse_syntax(text)
    # Only validated literal leaves enter this context. Joins, public roots and
    # aliases cannot become external dependencies; no runtime name is accepted.
    literals = {} if shared_literals is None else dict(shared_literals)
    first_literal = {value: name for name, value in reversed(list(literals.items()))}
    require(len({decl.name for decl in declarations}) == len(declarations),
            "fidelity: duplicate declaration")
    if len(expected) <= 128:
        require(len(declarations) == 1, "fidelity: direct declaration population")
        decl = declarations[0]
        require(not decl.private and decl.name == root and decl.kind == "literal",
                "fidelity: direct root declaration")
        require(decl.value == expected, "fidelity: raw code bytes")
        return {"bytes": len(expected), "leaves": 1, "joins": 0, "join_height": 0}

    count = (len(expected) + 127) // 128
    require(len(declarations) == 2 * count, "fidelity: declaration population")
    decoded = {}
    for index in range(count):
        leaf = declarations[index]
        name = f"{root}Chunk{index:04d}"
        require(leaf.private and leaf.name == name,
                "fidelity: leaf declaration/order")
        if leaf.kind == "literal":
            value = leaf.value
            require(shared_literals is None or value not in first_literal,
                    "fidelity: repeated literal must share its first leaf")
            literals[name] = value
            first_literal.setdefault(value, name)
        elif leaf.kind == "alias":
            require(shared_literals is not None and leaf.value in literals,
                    "fidelity: shared leaf must reference an earlier literal")
            value = literals[leaf.value]
            require(first_literal[value] == leaf.value,
                    "fidelity: shared leaf must reference its first literal")
        else:
            raise FidelityError("fidelity: leaf declaration/order")
        require(len(value) == min(128, len(expected) - 128 * index),
                "fidelity: leaf width")
        decoded[name] = value

    joins = {}

    def subtree(start, stop):
        size = stop - start
        if size == 1:
            return f"{root}Chunk{start:04d}", 0
        half = 1 << ((size - 1).bit_length() - 1)
        left, height_left = subtree(start, start + half)
        right, height_right = subtree(start + half, stop)
        level, pair = half.bit_length() - 1, start // (2 * half)
        name = f"{root}Join{level:04d}_{pair:04d}"
        require((level, pair) not in joins, "fidelity: internal checker topology")
        joins[(level, pair)] = (name, left, right)
        return name, 1 + max(height_left, height_right)

    expected_root, height = subtree(0, count)
    for decl, (_, node) in zip(declarations[count:-1], sorted(joins.items())):
        name, left, right = node
        require(decl.private and decl.name == name and decl.kind == "append",
                "fidelity: join declaration/order")
        require(decl.value == (left, right), "fidelity: append references/order")
        require(left in decoded and right in decoded, "fidelity: non-topological join")
        decoded[name] = decoded[left] + decoded[right]
    final = declarations[-1]
    require(not final.private and final.name == root and final.kind == "alias"
            and final.value == expected_root, "fidelity: public root reference")
    require(decoded[expected_root] == expected, "fidelity: raw code bytes")
    if shared_literals is not None:
        shared_literals.update(literals)
    return {"bytes": len(expected), "leaves": count, "joins": count - 1,
            "join_height": height}


def code_regions(text, named_fields, values, header_declarations, namespace):
    """Consume the entire fixed writer envelope and return exact code regions.

    Nothing outside the regions is skipped. This framing prevents an extra
    private declaration from hiding before, between, or after field bodies.
    Header and word/provenance checks in the calling payload reader are retained.
    """
    prefix = "\n".join([
        "-- GENERATED literal data only; UNADMITTED fetched evidence, no kernel verdict.",
        "-- Source template UNELABORATED until separately admitted owned Lean checking.",
        "-- Sole writer: python3 -B scripts/gen-live-usdc-weth9-data.py --archive PATH --write",
        "import Blanc.Basic", "", "namespace " + namespace, "", "open Jaune", "",
        *header_declarations, "", ""])
    position = 0

    def consume(expected, diagnostic):
        nonlocal position
        require(text.startswith(expected, position), diagnostic)
        position += len(expected)

    consume(prefix, "fidelity: source header boundary")
    regions = {}
    for index, (field, name) in enumerate(named_fields):
        consume(f'-- Frozen read {field["id"]}; account {field["account"]}.\n'
                f'def {name}Account : B256 := {field["account"]}\n',
                "fidelity: field/account boundary")
        if field["kind"] == "code":
            if index + 1 < len(named_fields):
                next_field = named_fields[index + 1][0]
                following = f'-- Frozen read {next_field["id"]}; account {next_field["account"]}.\n'
            else:
                following = "end " + namespace + "\n"
            boundary = text.find("\n\n" + following, position)
            require(boundary >= position, "fidelity: code region boundary")
            require(name not in regions, "fidelity: duplicate code region")
            regions[name] = text[position:boundary + 1]
            position = boundary + 2
        else:
            slot = "0x" + int(field["rpc_slot"], 16).to_bytes(32, "big").hex()
            consume(f'def {name}Slot : B256 := {slot}\n'
                    f'def {name} : B256 := {values[field["id"]]}\n\n',
                    "fidelity: word region boundary")
    consume("end " + namespace + "\n", "fidelity: final namespace boundary")
    require(position == len(text), "fidelity: trailing source boundary")
    return regions
