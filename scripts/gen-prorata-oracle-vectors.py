#!/usr/bin/env python3
"""Write/check timing-free exact-arithmetic PRORATA golden vectors.

The committed JSON is generated only by this script.  ``--check`` regenerates
the same canonical bytes and fails on drift; it is intentionally distinct from
the wide brute-force battery, whose elapsed-time fields are evidence rather
than stable golden data.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path

from prorata_oracle import DEFAULT_O, ProRata, run_transcript


ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / "scripts" / "prorata-oracle-vectors.json"


def replay(name, ops):
    model, steps = run_transcript(ops, O=DEFAULT_O, offset_enabled=True)
    if any(step["reverted"] for step in steps):
        raise AssertionError(f"{name}: canonical vector unexpectedly reverted")
    return {
        "name": name,
        "ops": [list(op) for op in ops],
        "steps": [{
            "pre_B": step["pre_B"], "pre_S": step["pre_S"],
            "result": step["result"], "reverted": step["reverted"],
            "step": step["step"], "post_B": step["post_B"], "post_S": step["post_S"],
        } for step in steps],
        "final": {"B": model.B, "S": model.S, "ledger": model.ledger},
    }


def build() -> bytes:
    g6_ops = [
        ("deposit", "A", 1),
        ("donate", 1_000_000),
        ("deposit", "V", 1_000_000),
        ("withdraw", "A", 1000),
        ("withdraw", "V", 1999),
    ]
    g6 = replay("g6_real_offset_attack", g6_ops)
    attacker_in = 1 + 1_000_000
    attacker_out = g6["steps"][3]["result"]
    victim_minted = g6["steps"][2]["result"]
    victim_out = g6["steps"][4]["result"]
    victim_loss = 1_000_000 - victim_out
    bound = (1_000_001 + 1) // (1000 + DEFAULT_O) + 1
    if not (attacker_out <= attacker_in and victim_minted == 1999 and
            victim_loss <= bound):
        raise AssertionError("G6 concrete vector no longer satisfies its bounds")

    obj = {
        "meta": {
            "generator": "scripts/gen-prorata-oracle-vectors.py",
            "arithmetic": "Python integers and floor division only",
            "offset": DEFAULT_O,
        },
        "vectors": [
            replay("genesis_deposit", [("deposit", "A", 1)]),
            replay("donation_price_shift", [
                ("deposit", "A", 5), ("donate", 3), ("deposit", "V", 3),
            ]),
            replay("full_exit", [
                ("deposit", "A", 7), ("withdraw", "A", 7000),
            ]),
            g6,
        ],
        "g6": {
            "attacker_in": attacker_in,
            "attacker_out": attacker_out,
            "attacker_loss": attacker_in - attacker_out,
            "victim_deposit": 1_000_000,
            "victim_minted": victim_minted,
            "victim_out": victim_out,
            "victim_loss": victim_loss,
            "victim_loss_bound": bound,
        },
    }
    return (json.dumps(obj, sort_keys=True, separators=(",", ":")) + "\n").encode()


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true",
                        help="regenerate and byte-compare against committed vectors")
    args = parser.parse_args()
    data = build()
    if args.check:
        if not OUT.exists() or OUT.read_bytes() != data:
            raise SystemExit("REGRESSION — prorata oracle vectors: committed vectors differ from regeneration")
        print(f"OK — prorata oracle vectors: {OUT} matches regeneration byte-for-byte ({len(data)} bytes)")
    else:
        OUT.write_bytes(data)
        print(f"OK — wrote {OUT} ({len(data)} bytes)")


if __name__ == "__main__":
    main()
