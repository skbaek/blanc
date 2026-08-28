# PRORATA exact-arithmetic oracle — findings

Independent Python 3 (stdlib only, exact integers, **no floats**) oracle and
brute-force harness for the PRORATA pro-rata share ledger.

- Model + views + property helpers: `scripts/prorata_oracle.py`
- Search / sweep harness: `scripts/prorata_bruteforce.py`
- Machine-readable run dump (regenerable): `scripts/prorata-bruteforce-summary.json`

Reproducibility: all randomized checks use fixed seed `20260828`; all sweeps
are deterministic exhaustive enumerations. A full `python3 prorata_bruteforce.py`
run took **151.8 s** wall (single process), well under the ~10 min budget. The
harness inlines the model arithmetic for speed and then **re-runs every reported
witness transcript through the reference `ProRata` model** (fidelity gate) — all
witnesses below are fidelity-confirmed identical to the reference semantics.

Headline: **every P1/P2/P3 check passed with ZERO violations** across millions
of exhaustive transitions and 320 000 randomized ops. The single open question,
P4(i), is now decided (see below): the strong "no attacker profit" claim is
**true for offset O ≥ 2 (hence for the real O = 10³ contract) and FALSE at
O = 1**, where a 1-wei rounding leak exists.

---

## Guard soundness (symbolic, defaults O = 10³, MAXA = 2⁹⁶−1, MAXS = MAXB = 2¹²⁶−1)

| product | worst case | bits | margin to 2²⁵⁶ | fits |
|---|---|---|---|---|
| deposit  `MAXA·(MAXS+O)` | 2²²²-ish | 222 | **34 bits** | yes |
| withdraw `MAXS·(MAXB+1)` | 2²⁵²-ish | 252 | **4 bits** | yes |

Both worst-case numerators are below 2²⁵⁶, so the on-chain 256-bit arithmetic
cannot overflow within the guard caps. **Flag for the lead:** the withdraw
product leaves only a **4-bit** margin (`MAXS·(MAXB+1) = 252 bits`). It is safe
at the specified caps, but MAXS and MAXB are effectively maxed against a 256-bit
word — any future widening of either cap would overflow. The deposit side is
comfortable (34 bits).

---

## P1 — rounding direction / price monotonicity (per op)

Checked on **every** applied transition of every exhaustive sweep and every
randomized op, exact cross-multiplied forms, zero tolerance.

- deposit never over-mints: `m·(B_pre+1) ≤ a·(S+O)` — **0 violations**
- deposit price monotone: `(B_pre+a+1)·(S+O) ≥ (B_pre+1)·(S+m+O)` — **0 violations**
- withdraw pays ≤ proportional: `p·(S+O) ≤ s·(B+1)` — **0 violations**
- withdraw price non-decreasing: `(B−p+1)·(S+O) ≥ (B+1)·(S−s+O)` — **0 violations**
  (this is the form the packet settled on after flagging its own earlier
  scratch; it holds exactly)
- donate price non-decreasing (cross-multiplied) — **0 violations**
- structural solvency `p ≤ B` at every withdraw — **0 violations**, the
  `SOLVENCY_VIOLATION_p_gt_B` flag never fired

Ranges: exhaustive reachable-state sweeps at O ∈ {1,2,3,10}, per-op values
0..6, two addresses, depth 5–6 (unique states 7 571 → 151 631; transitions
149 493 → 3 300 003 per config). Randomized: O ∈ {1000, 1, 10}, values up to
2⁹⁶, 8 000 sequences / 320 000 ops total.

## P2 — view == mutating op, and view-revert iff arithmetic-guard-revert

Checked at every reachable transition (deposit `convertToShares(a)` at B_pre = B;
withdraw `convertToAssets(s)`). **0 violations.**

A dedicated **binding-cap sweep** (O = 2, MAXA = 20, MAXS = MAXB = 40, depth 5,
19 906 states, 20 908 guard reverts) confirmed the view reverts on exactly the
arithmetic guards (a > MAXA, S + m > MAXS, B > MAXB) — **0 P2 revert
disagreements**. The ledger-sufficiency exclusion was verified structurally
(12 checks, 0 violations): `convertToAssets(s)` returns a value even for
`s > ledger[addr]`, i.e. the view does not see balances.

## P3 — dust conservation (induction nucleus)

Checked at every reachable state / transition:

- (a) price monotone along every transition — **0 violations** (same forms as P1)
- (b) genesis anchor `O·B ≥ S` at every reachable state — **0 violations**
  (this is also the fact that makes `p ≤ B` structural: `p ≤ B ⇐ S ≤ O·B`)
- (c) exact residue — deposit `a·(S+O) = m·(B_pre+1) + r`, `0 ≤ r ≤ B_pre`;
  withdraw `s·(B+1) = p·(S+O) + r'`, `0 ≤ r' < S+O` — **0 violations**
- (d) exact flow conservation (B by +a/−p/+a, S by +m/−s, Σledger == S) —
  **0 violations**; Σledger == S is a hard model assertion that never tripped

---

## P4 — the adversarial burden

### P4(i) — attacker-profit search (THE decisive output)

Attacker profit ≔ Σ(attacker withdrawal payouts) − Σ(attacker deposit values +
donations). Exhaustive DFS over all op interleavings (attacker
deposit/withdraw/donate + at most one victim deposit and one later
victim withdraw-all), profit evaluated at **every** prefix node.

Configs (all exhaustive): O ∈ {1,2,3,10}, V = 8, depth 5, 1 attacker
(7.7M–149M nodes); plus O = 1 V = 6 depth 6 (35.5M nodes); plus O = 1 V = 5
depth 5, **2 attackers** (4.4M nodes).

**Answer:** the strong claim "attacker profit ≤ 0" is **NOT universally true.**

| O | max attacker profit (exhaustive) |
|---|---|
| **1** | **1** (positive — leak) |
| 2 | 0 |
| 3 | 0 |
| 10 | 0 |

Leak-boundary study (V = 4, depth 4→7) confirms the leak is confined to O = 1
and does **not** grow with depth:

```
O=1: d4=0  d5=1  d6=1  d7=1
O=2: d4=0  d5=0  d6=0  d7=0
O=3: d4=0  d5=0  d6=0  d7=0
```

**Positive-profit witness (O = 1)**, fidelity-confirmed through the reference
model (attacker_in = 7, attacker_out = 8, profit = **+1**):

```
deposit  A0 4      # genesis: m = 4·(0+1)//(0+1) = 4   -> S=4  B=4
donate   3         #                                   -> S=4  B=7
deposit  V  3      # m = 3·(4+1)//(7+1) = 15//8 = 1     -> S=5  B=10  (victim: 3 in, 1 share)
withdraw V  1      # p = 1·(10+1)//(5+1) = 11//6 = 1    -> S=4  B=9   (victim gets 1 back)
withdraw A0 4      # p = 4·(9+1)//(4+1) = 40//5 = 8     -> S=0  B=1
```

Accounting: attacker pays 4 + 3 = 7, receives 8 → **+1**. The victim deposited 3
for 1 share and recovered 1 → victim loss 2. One wei of the victim's rounded-away
value is skimmed by the attacker; 1 wei is stranded as contract dust (B = 1 at
end). This is a genuine 1-wei O = 1 rounding leak, not an accounting artifact.

**Consequence for the theorem form:** the real contract uses O = 10³ ≥ 2, so the
strong statement **"Σ(attacker withdrawals) ≤ Σ(attacker deposits + donations)"
is exhaustively supported for O ≥ 2 in the tested ranges (V ≤ 8, depth ≤ 7, up
to 2 attackers).** For O = 1 it is false by the exhibited witness; O ≥ 2 is
therefore load-bearing and belongs as a hypothesis of the no-profit theorem.

### P4(ii) — victim-loss bounds

For every victim deposit-then-withdraw-all pair reached in the P4 sweeps
(1.4M+ loss records total), loss ≔ v − payout was measured; (B_dep, S_dep) is
the pre-credit state the victim's deposit saw. All three candidate bounds hold
with **zero violations**:

| candidate | expression | violations | verdict |
|---|---|---|---|
| C1 | `loss ≤ (B_dep+1)//(S_dep+O) + 1` | 0 | **holds — tightest, and tight** |
| C2 | `loss ≤ (B_dep+1+v)//(S_dep+O) + 1` | 0 | holds (looser) |
| C3 | `loss ≤ v//O + (B_dep+1)//(S_dep+O) + 1` | 0 | holds (looser) |

C1 is the tightest of the three and is **achieved with slack 0** (e.g. O = 10
witness: loss = 2, v = 3, S_dep = 0, B_dep = 15 → C1 = 16//10 + 1 = 2), so the
`+1` term is necessary and C1 cannot be uniformly reduced.

Empirical max-loss frontier (per config, all within C1):

| O | max loss | witness (loss, v, S_dep, B_dep) | C1 bound |
|---|---|---|---|
| 1 | 4 | (4, 8, 4, 20) | 21//5+1 = 5 |
| 2 | 4 | (4, 8, 3, 20) | 21//5+1 = 5 |
| 3 | 4 | (4, 8, 2, 20) | 21//5+1 = 5 |
| 10 | 2 | (2, 3, 0, 15) | 16//10+1 = 2 (tight) |

**Recommended exact victim-loss bound: `loss ≤ (B_dep+1) // (S_dep+O) + 1`** (C1).

### P4(iii) — offset-DISABLED control (must succeed; it does)

Classic first-depositor inflation on the no-offset variant. Minimal transcript
found (lexicographically smallest; 5 482 qualifying nodes in the search),
fidelity-confirmed (attacker profit = +1, victim payout = 0, final S = 0, B = 0):

```
deposit  A 1   # S==0 -> m = 1                 -> S=1  B=1   (attacker: 1 share)
donate   1     #                               -> S=1  B=2
deposit  V 1   # m = 1·1 // 2 = 0  (ROUNDS TO 0)-> S=1  B=3   (victim: 1 in, 0 shares!)
withdraw A 1   # p = 1·3 // 1 = 3              -> S=0  B=0   (attacker drains all)
```

Attacker pays 1 + 1 = 2, receives 3 → **profit +1**; the victim deposited 1,
minted **0 shares**, and is unrecoverable — **loses their whole deposit.** This
is the load-bearing control: the vulnerability is real when the virtual offset
is removed.

### P4(iv) — same shape on the REAL O = 10³ contract (must fail; it does)

```
deposit  A 1          -> shares 1000       (S=1000  B=1)
donate   1000000      ->                   (S=1000  B=1000001)
deposit  V 1000000    -> shares 1999       (S_dep=1000 B_dep=1000001; S=2999 B=2000001)
withdraw A 1000       -> assets 500125
withdraw V 1999       -> assets 999751
```

- attacker_in = 1 000 001, attacker_out = 500 125 → **attacker profit = −499 876**
  (the donation is not recoverable; the attacker subsidises the pool).
- victim_loss = 1 000 000 − 999 751 = **249**, inside every P4(ii) bound
  (C1 = 501, C2 = 1001, C3 = 1501).

The inflation attack that drains the victim under the disabled variant is
neutralised by the virtual offset on the real contract. This transcript seeds a
Lean fixture later.

---

## Wide-range randomized P1–P3 (~2⁹⁶ magnitudes, seed 20260828)

| O | sequences | ops | deposits | withdraws | donates | reverts | violations |
|---|---|---|---|---|---|---|---|
| 1000 | 4000 | 160000 | 80086 | 34057 | 39782 | 0 | **0** |
| 1 | 2000 | 80000 | 40236 | 12453 | 19753 | 0 | **0** |
| 10 | 2000 | 80000 | 40154 | 16274 | 19883 | 0 | **0** |

---

## Recommended exact statement forms

Based on the evidence above:

1. **Invariants (P3, exactly provable, unconditional in O ≥ 1):**
   - genesis anchor `O·B ≥ S` is preserved by every op from genesis — this is
     the induction nucleus and directly yields `price ≥ 1/O` and the structural
     `p ≤ B` solvency of the outbound send.
   - per-op exact residues `a·(S+O) = m·(B_pre+1) + r`, `0 ≤ r ≤ B_pre` and
     `s·(B+1) = p·(S+O) + r'`, `0 ≤ r' < S+O`.
   - price monotone across deposit/withdraw/donate in the cross-multiplied
     forms verified under P1.

2. **View faithfulness (P2, exactly provable):** `convertToShares` /
   `convertToAssets` equal the minted/paid amount of the corresponding mutating
   op, and revert on exactly the arithmetic guards (ledger sufficiency excluded).

3. **No-attacker-profit (P4(i)) — condition on O ≥ 2:**
   > For `O ≥ 2`, over any interleaving of attacker deposit/withdraw/donate
   > around a single victim deposit (+ optional victim withdraw-all),
   > `Σ(attacker withdrawals) ≤ Σ(attacker deposits + donations)`.

   Do **not** state this for `O ≥ 1`: it is false at `O = 1` (exhibited +1-wei
   witness). The real contract's `O = 10³` satisfies the hypothesis.

4. **Victim-loss bound (P4(ii), exactly provable, tightest surviving):**
   > `v − payout ≤ (B_dep + 1) // (S_dep + O) + 1`
   where `(S_dep, B_dep)` is the pre-credit state the victim's deposit observed.

5. **Guard soundness:** `MAXA·(MAXS+O) < 2²⁵⁶` and `MAXS·(MAXB+1) < 2²⁵⁶` at the
   defaults (margins 34 and 4 bits). The withdraw side is tight; keep MAXS/MAXB
   fixed unless the 256-bit headroom is re-derived.

---

## Spec items flagged (not silently fixed)

1. **P4(i) is not airtight for O ≥ 1.** The packet framed "attacker profit ≤ 0"
   as the airtight expectation. Exhaustive search shows a **+1-wei leak at
   O = 1** (witness above), profit exactly 0 for O ∈ {2,3,10} and stable across
   depth. The provable theorem must carry `O ≥ 2` as a hypothesis. The real
   contract (O = 10³) is unaffected. This is the packet's requested
   theorem-deciding output — surfaced rather than smoothed over.

2. **Withdraw guard margin is only 4 bits.** `MAXS·(MAXB+1) = 252 bits` vs the
   256-bit word. Safe at spec caps, but there is essentially no headroom; any
   widening of MAXS or MAXB overflows. Worth an explicit note wherever the caps
   are chosen.

3. **Withdraw price-monotonicity form:** the packet itself flagged confusion and
   settled on `(B−p+1)·(S+O) ≥ (B+1)·(S−s+O)`. Confirmed: this form holds with
   zero violations; the discarded direction was correctly discarded.

4. **Disabled-variant offset value:** `O` is meaningless when the offset is
   disabled (the disabled formulas never reference it). For the fidelity replay
   the reference model was fed `O = 1` (ignored) to satisfy its `O ≥ 1`
   precondition — a modelling detail, no semantic effect.

All other spec formulas matched exactly and produced zero violations.
