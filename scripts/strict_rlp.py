"""Small dependency-free strict RLP decoder for evidence tools."""

from __future__ import annotations


class RLPDecodeError(ValueError):
    pass


def decode(data: bytes):
    value, rest = _item(data)
    if rest:
        raise RLPDecodeError(
            f"{len(rest)} trailing byte(s) after the top-level RLP item"
        )
    return value


def _item(data: bytes):
    if not data:
        raise RLPDecodeError("empty RLP input")
    prefix = data[0]
    if prefix < 0x80:
        return bytes([prefix]), data[1:]
    if prefix < 0xB8:
        length = prefix - 0x80
        if len(data) < 1 + length:
            raise RLPDecodeError("short RLP string: declared length overruns input")
        return data[1:1 + length], data[1 + length:]
    if prefix < 0xC0:
        length_of_length = prefix - 0xB7
        if len(data) < 1 + length_of_length:
            raise RLPDecodeError("long RLP string: length-of-length overruns input")
        length = int.from_bytes(data[1:1 + length_of_length], "big")
        start = 1 + length_of_length
        if len(data) < start + length:
            raise RLPDecodeError("long RLP string: declared length overruns input")
        return data[start:start + length], data[start + length:]
    if prefix < 0xF8:
        length = prefix - 0xC0
        if len(data) < 1 + length:
            raise RLPDecodeError("short RLP list: declared length overruns input")
        payload, rest = data[1:1 + length], data[1 + length:]
        return _list_payload(payload), rest
    length_of_length = prefix - 0xF7
    if len(data) < 1 + length_of_length:
        raise RLPDecodeError("long RLP list: length-of-length overruns input")
    length = int.from_bytes(data[1:1 + length_of_length], "big")
    start = 1 + length_of_length
    if len(data) < start + length:
        raise RLPDecodeError("long RLP list: declared length overruns input")
    payload, rest = data[start:start + length], data[start + length:]
    return _list_payload(payload), rest


def _list_payload(payload: bytes):
    items = []
    while payload:
        item, payload = _item(payload)
        items.append(item)
    return items


def decode_legacy_block_transactions(rlp_hex: str):
    """Return ``(to, calldata)`` pairs from a legacy-transaction block body."""
    if not isinstance(rlp_hex, str) or not rlp_hex.startswith("0x"):
        raise RLPDecodeError(f"block 'rlp' field is not a 0x-hex string: {rlp_hex!r}")
    try:
        raw = bytes.fromhex(rlp_hex[2:])
    except ValueError as exc:
        raise RLPDecodeError(f"block 'rlp' is not valid hex: {exc}") from exc
    block = decode(raw)
    if not isinstance(block, list) or len(block) < 2:
        raise RLPDecodeError(
            f"decoded block RLP is not a >=2-element list: got "
            f"{type(block).__name__} of length "
            f"{len(block) if isinstance(block, list) else '?'}"
        )
    transactions = block[1]
    if not isinstance(transactions, list):
        raise RLPDecodeError("block RLP's second element (transactions) is not a list")
    result = []
    for index, transaction in enumerate(transactions):
        if not isinstance(transaction, list) or len(transaction) < 6:
            raise RLPDecodeError(
                f"transaction {index}: expected a >=6-element legacy-tx RLP "
                f"list [nonce, gasPrice, gas, to, value, data, ...], got "
                f"{transaction!r}"
            )
        to_bytes, calldata = transaction[3], transaction[5]
        if not isinstance(to_bytes, (bytes, bytearray)) or len(to_bytes) not in (0, 20):
            raise RLPDecodeError(
                f"transaction {index}: 'to' field is not a 0- or 20-byte "
                f"string: {to_bytes!r}"
            )
        if not isinstance(calldata, (bytes, bytearray)):
            raise RLPDecodeError(
                f"transaction {index}: 'data' field is not a byte string"
            )
        to = "0x" + bytes(to_bytes).hex().lower().rjust(40, "0") if to_bytes else None
        result.append((to, bytes(calldata)))
    return result
