#!/usr/bin/env python3
"""Registered generator for the lifted Lido CircuitBreaker's live finite registry observation.

Two modes, two outputs:

* ``fetch`` (network; explicit): queries three independent public JSON-RPC operators for the
  CircuitBreaker creation transaction, its receipt and block header (block 24993190), the
  boundary block header and, at the boundary block 26141229, the raw storage words the finite
  registry observation reads.  Every answer must be identical across the three operators
  (compared after JSON canonicalisation of the ``result`` member).  Raw responses go to
  ``<root>/.lake/reach-observations/`` (ignored); the agreed values are written to the committed
  observation JSON ``scripts/observations/lido-circuit-breaker-live-26141229.json``.  These are
  candidate observations until the user adopts them.

* default / ``--check`` (offline) and ``--write``: reads only the committed observation JSON,
  validates it (schema, the creation coordinates against
  ``scripts/lido-circuit-breaker-reference.json``, that every slot the finite check reads is
  present and that the probe list is exactly what the observation derives), and renders the sole
  generated Lean data module ``Blanc/Lift/LidoCircuitBreakerDeployed/LiveObservation.lean``.
  ``--check`` byte-compares without writing; ``--write`` writes.  The kernel check of the
  observation (``LiveRegistry.lean``) is handwritten and not generator-owned.

Probe list: every address touched by the PauserSet events from deployment to the boundary
(target, previous and new pauser; a block-range census, class B, used only to choose probes),
every live target and pauser, and the fixed absent probes 1, 2, 3 and 2^160-1.  The Lean
statement promises equations only at these probes.
"""
import argparse
import json
import sys
import time
import urllib.error
import urllib.request
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from keccak import keccak256, keccak256_hex  # noqa: E402

ROOT = Path(__file__).resolve().parent.parent
OBS = ROOT / "scripts/observations/lido-circuit-breaker-live-26141229.json"
LEAN = ROOT / "Blanc/Lift/LidoCircuitBreakerDeployed/LiveObservation.lean"
REFERENCE = ROOT / "scripts/lido-circuit-breaker-reference.json"
RAW = ROOT / ".lake/reach-observations"

ADDRESS = "0x6019cb557978296ba3c08a7b73225c0975dfb2f7"
DEPLOY_BLOCK = 24993190
DEPLOY_INDEX = 1219
BOUNDARY = 26141229
MASK = 2 ** 160 - 1
MOD = 2 ** 256
EVENT = keccak256_hex(b"PauserSet(address,address,address)")
PROVIDERS = {
    "drpc": "https://eth.drpc.org",
    "blastapi": "https://eth-mainnet.public.blastapi.io",
    "mevblocker": "https://rpc.mevblocker.io",
    "1rpc": "https://1rpc.io/eth",
    "publicnode": "https://ethereum-rpc.publicnode.com",
}
QUORUM = 3
SCHEMA = "blanc.lido-circuit-breaker.live-registry-observation.v1"


def map_slot(key, base):
    return int.from_bytes(keccak256(key.to_bytes(32, "big") + base.to_bytes(32, "big")), "big")


ARRAY_BASE = int.from_bytes(keccak256((5).to_bytes(32, "big")), "big")


def array_slot(i):
    return (ARRAY_BASE + i) % MOD


# ---------------------------------------------------------------- fetch (network)

class RPC:
    def __init__(self):
        self.counter = 0
        self.used = {}
        RAW.mkdir(parents=True, exist_ok=True)

    def call(self, provider, method, params):
        body = json.dumps({"jsonrpc": "2.0", "id": 1, "method": method, "params": params}).encode()
        for attempt in range(5):
            try:
                req = urllib.request.Request(PROVIDERS[provider], data=body,
                                             headers={"Content-Type": "application/json",
                                                      "User-Agent": "blanc-observation/1"})
                with urllib.request.urlopen(req, timeout=60) as resp:
                    raw = resp.read()
                data = json.loads(raw)
                if "result" not in data:
                    raise RuntimeError(f"{provider} {method}: {data}")
                self.counter += 1
                (RAW / f"{self.counter:05d}-{provider}-{method}.json").write_bytes(
                    json.dumps({"request": {"method": method, "params": params},
                                "response": data}).encode())
                return data["result"]
            except Exception as exc:  # retry transient failures, then fail closed
                if attempt == 2 or (isinstance(exc, urllib.error.HTTPError) and exc.code in (400, 403)):
                    raise
                print(f"retry {provider} {method}: {exc}", file=sys.stderr)
                time.sleep(2 + 2 * attempt)

    def first(self, method, params, order=None):
        for p in order or PROVIDERS:
            try:
                return self.call(p, method, params)
            except Exception as exc:
                print(f"skip {p} {method}: {exc}", file=sys.stderr)
        raise SystemExit(f"no operator served {method}")

    def agreed(self, method, params):
        """The first QUORUM operators (in PROVIDERS order) that return a non-null answer must
        agree exactly; a null answer (pruned history) moves to the next operator."""
        answers = {}
        for p in PROVIDERS:
            try:
                a = self.call(p, method, params)
            except Exception as exc:  # an operator refusing (e.g. no archive) is skipped
                print(f"skip {p} {method}: {exc}", file=sys.stderr)
                continue
            if a is not None:
                answers[p] = a
            if len(answers) == QUORUM:
                break
        if len(answers) < QUORUM:
            raise SystemExit(f"fewer than {QUORUM} operators answered {method} {params}")
        canon = {p: json.dumps(a, sort_keys=True) for p, a in answers.items()}
        if len(set(canon.values())) != 1:
            raise SystemExit(f"operators disagree on {method} {params}: {canon}")
        self.used.setdefault(method, set()).update(answers)
        return next(iter(answers.values()))


def fetch():
    rpc = RPC()
    tx = rpc.agreed("eth_getTransactionByBlockNumberAndIndex", [hex(DEPLOY_BLOCK), hex(DEPLOY_INDEX)])
    receipt = rpc.agreed("eth_getTransactionReceipt", [tx["hash"]])
    deploy_header = rpc.agreed("eth_getBlockByNumber", [hex(DEPLOY_BLOCK), False])
    boundary_header = rpc.agreed("eth_getBlockByNumber", [hex(BOUNDARY), False])
    code = rpc.agreed("eth_getCode", [ADDRESS, hex(BOUNDARY)])
    # Probe choice only: PauserSet census (first operator that serves it; it selects probes,
    # it is not a premise).
    logs = []
    for start in range(DEPLOY_BLOCK, BOUNDARY + 1, 50000):
        stop = min(start + 49999, BOUNDARY)
        logs += rpc.first("eth_getLogs", [{"address": ADDRESS, "topics": [EVENT],
                                           "fromBlock": hex(start), "toBlock": hex(stop)}],
                          order=["mevblocker", "mevblocker", "mevblocker"])
    touched = {0}
    for lg in logs:
        touched.update(int(w, 16) for w in lg["topics"][1:])
    length = int(rpc.agreed("eth_getStorageAt", [ADDRESS, "0x5", hex(BOUNDARY)]), 16)
    if length > 1000:
        raise SystemExit("refusing an unexpectedly large array")
    targets = [int(rpc.agreed("eth_getStorageAt", [ADDRESS, hex(array_slot(i)), hex(BOUNDARY)]), 16) & MASK
               for i in range(length)]
    pausers = [int(rpc.agreed("eth_getStorageAt", [ADDRESS, hex(map_slot(t, 3)), hex(BOUNDARY)]), 16) & MASK
               for t in targets]
    probes = sorted(touched | set(targets) | set(pausers) | {1, 2, 3, MASK})
    slots = [5] + [array_slot(i) for i in range(length)] + \
        [map_slot(p, b) for p in probes for b in (3, 4, 6)]
    words = {}
    for s in slots:
        if s not in words:
            words[s] = rpc.agreed("eth_getStorageAt", [ADDRESS, hex(s), hex(BOUNDARY)])
    out = {
        "schema": SCHEMA,
        "status": "candidate observation; not adopted by the user",
        "contract": ADDRESS,
        "providers": PROVIDERS,
        "agreement": "every value below was returned identically (canonical JSON) by three providers",
        "providersUsed": {m: sorted(ps) for m, ps in rpc.used.items()},
        "creation": {
            "blockNumber": DEPLOY_BLOCK, "blockHash": deploy_header["hash"],
            "blockTimestamp": int(deploy_header["timestamp"], 16),
            "transactionIndex": int(tx["transactionIndex"], 16), "txHash": tx["hash"],
            "type": int(tx["type"], 16), "from": tx["from"], "to": tx["to"],
            "nonce": int(tx["nonce"], 16), "value": int(tx["value"], 16), "gas": int(tx["gas"], 16),
            "inputKeccak": keccak256_hex(bytes.fromhex(tx["input"][2:])),
            "inputLength": len(tx["input"][2:]) // 2,
            "receiptStatus": int(receipt["status"], 16),
            "receiptContractAddress": receipt["contractAddress"],
            "receiptGasUsed": int(receipt["gasUsed"], 16),
        },
        "boundary": {
            "blockNumber": BOUNDARY, "blockHash": boundary_header["hash"],
            "runtimeKeccak": keccak256_hex(bytes.fromhex(code[2:])),
            "pauserSetEvents": len(logs),
        },
        "probes": [hex(p) for p in probes],
        "storage": [[hex(s), w] for s, w in words.items()],
    }
    OBS.parent.mkdir(parents=True, exist_ok=True)
    OBS.write_text(json.dumps(out, indent=1) + "\n")
    print(f"fetched {len(words)} words, {length} entries, {len(probes)} probes; {rpc.counter} calls")


# ---------------------------------------------------------------- generate (offline)

def word(hexstr):
    v = int(hexstr, 16)
    if not 0 <= v < MOD:
        raise SystemExit(f"bad word {hexstr}")
    return v


def load():
    obs = json.loads(OBS.read_text())
    if obs.get("schema") != SCHEMA:
        raise SystemExit("observation schema mismatch")
    meta = json.loads(REFERENCE.read_text())["deployment"]["manifest"]["meta"]
    c = obs["creation"]
    if (c["blockNumber"], c["txHash"], c["from"].lower(), c["blockTimestamp"]) != \
            (meta["blockNumber"], meta["txHash"], meta["deployer"].lower(), meta["timestamp"]):
        raise SystemExit("creation coordinates disagree with the reference manifest")
    if c["receiptStatus"] != 1 or c["to"] is not None or c["nonce"] != 0 or c["value"] != 0 \
            or (c["receiptContractAddress"] or "").lower() != obs["contract"]:
        raise SystemExit("creation observation is not a successful nonce-0 zero-value creation")
    storage = {}
    for s, w in obs["storage"]:
        s, w = word(s), word(w)
        if s in storage and storage[s] != w:
            raise SystemExit("duplicate slot with different words")
        storage[s] = w
    probes = [word(p) for p in obs["probes"]]
    if probes != sorted(set(probes)) or not all(p <= MASK for p in probes):
        raise SystemExit("probes must be sorted, distinct and canonical")
    length = storage[5]
    entries = [(storage[array_slot(i)] & MASK, storage[map_slot(storage[array_slot(i)] & MASK, 3)] & MASK)
               for i in range(length)]
    needed = [5] + [array_slot(i) for i in range(length)] + [map_slot(p, b) for p in probes for b in (3, 4, 6)]
    missing = [s for s in needed if s not in storage]
    if missing:
        raise SystemExit(f"observation lacks {len(missing)} slot(s) the finite check reads")
    if set(storage) != set(needed):
        raise SystemExit("observation carries slots the finite check does not read")
    return obs, storage, needed, entries, probes


def render(obs, storage, needed, entries, probes):
    c, b = obs["creation"], obs["boundary"]
    lines = [
        "import Blanc.Lift.LidoCircuitBreakerDeployed.FiniteRegistry",
        "",
        "/-! GENERATED by scripts/lido-circuit-breaker-live-registry.py from",
        "scripts/observations/lido-circuit-breaker-live-26141229.json -- do not edit.",
        "",
        f"Raw storage words of the Lido CircuitBreaker {obs['contract']} at block {b['blockNumber']}",
        f"(hash {b['blockHash']}), each returned identically by three public JSON-RPC operators;",
        "a candidate one-block observation until adopted. The entry and probe lists are derived from",
        "these words and the probe choice recorded in the observation. -/",
        "",
        "namespace Blanc.Lift.LidoCircuitBreakerDeployed.Live",
        "",
        "open Jaune",
        "",
        "/-- The observed `(slot, word)` pairs, in the order the finite check reads them. -/",
        "def words : List (B256 × B256) := [",
    ]
    rows = [f"  ({hex(s)}, {hex(storage[s])})" for s in needed]
    lines += [",\n".join(rows), "]", ""]
    lines += ["/-- The live entries `(target, pauser)`, in array order. -/",
              "def entries : List (B256 × B256) := ["]
    lines += [",\n".join(f"  ({hex(t)}, {hex(p)})" for t, p in entries), "]", ""]
    lines += ["/-- The probe addresses. -/", "def probes : List B256 := ["]
    lines += [",\n".join(f"  {hex(p)}" for p in probes), "]", ""]
    lines += ["end Blanc.Lift.LidoCircuitBreakerDeployed.Live", ""]
    return "\n".join(lines)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("mode", nargs="?", choices=["fetch"], help="network fetch of the observation")
    ap.add_argument("--check", action="store_true", help="byte-compare the generated Lean (default)")
    ap.add_argument("--write", action="store_true", help="write the generated Lean")
    args = ap.parse_args()
    if args.mode == "fetch":
        fetch()
        return
    text = render(*load())
    if args.write:
        LEAN.write_text(text)
        print(f"wrote {LEAN.relative_to(ROOT)}")
    elif LEAN.exists() and LEAN.read_text() == text:
        print("OK — lido-circuit-breaker live registry: generated Lean matches the observation")
    else:
        raise SystemExit("REGRESSION — generated LiveObservation.lean differs from the observation")


if __name__ == "__main__":
    main()
