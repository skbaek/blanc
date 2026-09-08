"""Generic Prague BlockchainTest mechanics shared by fixture generators."""

from __future__ import annotations

import json
import os
import subprocess
import sys
import tempfile


def quantity(value) -> str:
    """Return an even-width hexadecimal quantity.

    Jaune's header and account decoders reject an odd hex-digit count, while
    t8n emits minimal ``hex()`` form, so every quantity is padded here.
    """

    number = int(value, 16) if isinstance(value, str) else int(value)
    digits = format(number, "x")
    return "0x" + ("0" + digits if len(digits) % 2 else digits)


def norm_alloc(alloc):
    return {
        address: {
            "nonce": quantity(account.get("nonce", "0x0")),
            "balance": quantity(account.get("balance", "0x0")),
            "code": account.get("code", "0x"),
            "storage": {
                quantity(key): quantity(value)
                for key, value in account.get("storage", {}).items()
                if int(value, 16) != 0
            },
        }
        for address, account in alloc.items()
    }


def alloc_state_root(alloc):
    from ethereum.prague.fork_types import Account, Address
    from ethereum.prague.state import State, set_account, set_storage, state_root
    from ethereum_types.bytes import Bytes, Bytes32
    from ethereum_types.numeric import U256, Uint
    from ethereum.utils.hexadecimal import hex_to_bytes

    state = State()
    for address, account in alloc.items():
        set_account(state, Address(hex_to_bytes(address)), Account(
            nonce=Uint(int(account.get("nonce", "0x0"), 16)),
            balance=U256(int(account.get("balance", "0x0"), 16)),
            code=Bytes(hex_to_bytes(account.get("code", "0x"))),
        ))
        for key, value in account.get("storage", {}).items():
            numeric_value = U256(int(value, 16))
            if numeric_value != 0:
                set_storage(
                    state,
                    Address(hex_to_bytes(address)),
                    Bytes32(int(key, 16).to_bytes(32, "big")),
                    numeric_value,
                )
    return "0x" + state_root(state).hex()


def header_json(header, header_hash):
    return {
        "parentHash": "0x" + header.parent_hash.hex(),
        "uncleHash": "0x" + header.ommers_hash.hex(),
        "coinbase": "0x" + header.coinbase.hex(),
        "stateRoot": "0x" + header.state_root.hex(),
        "transactionsTrie": "0x" + header.transactions_root.hex(),
        "receiptTrie": "0x" + header.receipt_root.hex(),
        "bloom": "0x" + header.bloom.hex(),
        "difficulty": quantity(header.difficulty),
        "number": quantity(header.number),
        "gasLimit": quantity(header.gas_limit),
        "gasUsed": quantity(header.gas_used),
        "timestamp": quantity(header.timestamp),
        "extraData": "0x" + header.extra_data.hex(),
        "mixHash": "0x" + header.prev_randao.hex(),
        "nonce": "0x" + header.nonce.hex(),
        "baseFeePerGas": quantity(header.base_fee_per_gas),
        "withdrawalsRoot": "0x" + header.withdrawals_root.hex(),
        "blobGasUsed": quantity(header.blob_gas_used),
        "excessBlobGas": quantity(header.excess_blob_gas),
        "parentBeaconBlockRoot": "0x" + header.parent_beacon_block_root.hex(),
        "requestsHash": "0x" + header.requests_hash.hex(),
        "hash": "0x" + header_hash.hex(),
    }


def mk_header(data):
    from ethereum.crypto.hash import keccak256
    from ethereum.prague.blocks import Header
    from ethereum.prague.fork_types import Address
    from ethereum_rlp import rlp
    from ethereum_types.bytes import Bytes, Bytes8, Bytes32, Bytes256
    from ethereum_types.numeric import U64, U256, Uint
    from ethereum.utils.hexadecimal import hex_to_bytes

    header = Header(
        parent_hash=hex_to_bytes(data["parentHash"]),
        ommers_hash=hex_to_bytes(data["uncleHash"]),
        coinbase=Address(hex_to_bytes(data["coinbase"])),
        state_root=hex_to_bytes(data["stateRoot"]),
        transactions_root=hex_to_bytes(data["transactionsTrie"]),
        receipt_root=hex_to_bytes(data["receiptTrie"]),
        bloom=Bytes256(hex_to_bytes(data["bloom"])),
        difficulty=Uint(int(data["difficulty"], 16)),
        number=Uint(int(data["number"], 16)),
        gas_limit=Uint(int(data["gasLimit"], 16)),
        gas_used=Uint(int(data["gasUsed"], 16)),
        timestamp=U256(int(data["timestamp"], 16)),
        extra_data=Bytes(hex_to_bytes(data["extraData"])),
        prev_randao=Bytes32(hex_to_bytes(data["mixHash"])),
        nonce=Bytes8(hex_to_bytes(data["nonce"])),
        base_fee_per_gas=Uint(int(data["baseFeePerGas"], 16)),
        withdrawals_root=hex_to_bytes(data["withdrawalsRoot"]),
        blob_gas_used=U64(int(data["blobGasUsed"], 16)),
        excess_blob_gas=U64(int(data["excessBlobGas"], 16)),
        parent_beacon_block_root=hex_to_bytes(data["parentBeaconBlockRoot"]),
        requests_hash=hex_to_bytes(data["requestsHash"]),
    )
    return header, keccak256(rlp.encode(header))


def run_t8n(env, alloc, txs, *, eels_root):
    with tempfile.TemporaryDirectory() as directory:
        def path(name: str) -> str:
            return os.path.join(directory, name)

        with open(path("env.json"), "w") as stream:
            json.dump(env, stream)
        with open(path("alloc.json"), "w") as stream:
            json.dump(alloc, stream)
        with open(path("txs.json"), "w") as stream:
            json.dump(txs, stream)
        command = [
            sys.executable, "-m", "ethereum_spec_tools.evm_tools", "t8n",
            "--input.env", path("env.json"), "--input.alloc", path("alloc.json"),
            "--input.txs", path("txs.json"), "--output.basedir", directory,
            "--output.alloc", "out-alloc.json", "--output.result", "out-result.json",
            "--output.body", "out-body.txt", "--state.fork", "Prague",
            "--state.chainid", "1", "--state.reward", "0",
        ]
        subprocess.run(
            command, check=True, capture_output=True, text=True,
            env={**os.environ, "PYTHONPATH": os.path.join(str(eels_root), "src")},
        )
        with open(path("out-alloc.json")) as stream:
            post = json.load(stream)
        with open(path("out-result.json")) as stream:
            result = json.load(stream)
        with open(path("out-body.txt")) as stream:
            body = json.load(stream)
    return post, result, body
