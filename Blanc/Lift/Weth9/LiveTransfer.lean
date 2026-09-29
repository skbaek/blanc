import Blanc.Lift.Weth9.LiveApprove
import Blanc.ForwardStorageAccess

namespace Blanc.Lift.Weth9

open Jaune Blanc.Lift

/-! ## The base states a `transferFrom` walk passes through

Each selected `SLOAD` warms its slot (`afterSload`), each `SSTORE` warms it and writes it
(`afterSstore`); the next charge and the next value read are taken at the state so far.  The tail
(entry `0x08cf`) is entered at a state `t0` and debits `src`, then credits `dst`. -/

section Chain

variable (sevm : Sevm) (t0 : Devm) (src dst : Adr) (wad : B256)

/-- After the tail's read of `src`'s balance. -/
abbrev tT1 : Devm := afterSload sevm t0 (balSlot src)
/-- The debited balance of `src`. -/
abbrev tV1 : B256 := t0.getStorVal sevm.currentTarget (balSlot src) - wad
/-- After the debit of `src`. -/
abbrev tT2 : Devm := afterSstore sevm (tT1 sevm t0 src) (balSlot src) (tV1 sevm t0 src wad)
/-- After the read of `dst`'s balance. -/
abbrev tT3 : Devm := afterSload sevm (tT2 sevm t0 src wad) (balSlot dst)
/-- The credited balance of `dst` (read after the debit, so a self-transfer restores the balance). -/
abbrev tV2 : B256 := (tT2 sevm t0 src wad).getStorVal sevm.currentTarget (balSlot dst) + wad

/-- The gas of the tail from its entry at `t0` to its return jump, from the `G` left after it:
`106` up to the first `SLOAD`, `16` to the `SSTORE`, `107` to the second `SLOAD`, `16` to the second
`SSTORE`, `1862` after it (`1756` for the `LOG3`, a word of expansion included). -/
def xfTailGas (G : Nat) : Nat :=
  G + 1862 + sstoreCost sevm (tT3 sevm t0 src dst wad) (balSlot dst) (tV2 sevm t0 src dst wad) + 16 +
    sloadCost sevm (tT2 sevm t0 src wad) (balSlot dst) + 107 +
    sstoreCost sevm (tT1 sevm t0 src) (balSlot src) (tV1 sevm t0 src wad) + 16 +
    sloadCost sevm t0 (balSlot src) + 106

end Chain

section PathChain

variable (sevm : Sevm) (b : Devm) (src : Adr) (wad : B256)

/-- After the balance check of `src` (the body's first `SLOAD`). -/
abbrev pB1 : Devm := afterSload sevm b (balSlot src)
/-- After the allowance's first read (the maximal-allowance test). -/
abbrev pA1 : Devm := afterSload sevm (pB1 sevm b src) (allowSlot src sevm.caller)
/-- After its second read (the `require(allowance >= wad)`). -/
abbrev pA2 : Devm := afterSload sevm (pA1 sevm b src) (allowSlot src sevm.caller)
/-- After its third read (the debit's). -/
abbrev pA3 : Devm := afterSload sevm (pA2 sevm b src) (allowSlot src sevm.caller)
/-- The debited allowance. -/
abbrev pV : B256 := (pA2 sevm b src).getStorVal sevm.currentTarget (allowSlot src sevm.caller) - wad
/-- After the allowance's debit. -/
abbrev pT0 : Devm := afterSstore sevm (pA3 sevm b src) (allowSlot src sevm.caller) (pV sevm b src wad)

end PathChain

/-- The `transferFrom` body's opening: the hash of `src`'s balance slot, its `SLOAD`, and the
`require(balanceOf[src] >= wad)` branch (taken). -/
macro "rxf_head " h:ident : tactic => `(tactic|
  (rdest; rpush; rdup; rpush; rpush; rdup; rhash; rsloadC; rreq $h; rdest))

/-- The `transferFrom` body's tail (entry `0x08cf`) from the balance `SLOAD`s on: the two balance
updates, the `Transfer` event, `true`, up to the return jump.  The charges are named atoms
(`rsloadC`, `rsstoreC`). -/
theorem xfer_tail {sevm : Sevm} {t0 : Devm} {G : Nat} {S : List B256} {M : Mem} {wad ret : B256}
    {src dst : Adr} {cL2 cS1 cL3 cS2 : Nat}
    (hfork : CoveredFork sevm.benvStat.fork) (hstatic : sevm.isStatic = false)
    (hM : FpMem 96 M) (hroom : S.length < 1000)
    (h1 : cL2 = sloadCost sevm t0 (balSlot src))
    (h2 : cS1 = sstoreCost sevm (tT1 sevm t0 src) (balSlot src) (tV1 sevm t0 src wad))
    (h3 : cL3 = sloadCost sevm (tT2 sevm t0 src wad) (balSlot dst))
    (h4 : cS2 = sstoreCost sevm (tT3 sevm t0 src dst wad) (balSlot dst) (tV2 sevm t0 src dst wad))
    (hsentry : gCallStipend < G + 1862 + cS2) :
    ∃ b', ∀ x, SFunc.RunExact prog sevm (St t0 (x :: wad :: dst.toB256 :: src.toB256 :: ret :: S) M
      (G + 1862 + cS2 + 16 + cL3 + 107 + cS1 + 16 + cL2 + 106)) t_08cf_c9
      (.returned (St b' (1 :: S)
        ((scratchW (scratchW M src.toB256 3) dst.toB256 3).write 96 wad.toBytes) G)) := by
  refine ⟨?b', fun x => ?run⟩
  case run =>
    rdest
    rdup
    rpush
    rpush
    rdup
    rhash
    rpush
    rdup
    rdup
    rsloadC
    rsub
    rswap
    rpop
    rpop
    rdup
    rswap
    rsstoreC
    rpop
    rdup
    rpush
    rpush
    rdup
    rhash
    rpush
    rdup
    rdup
    rsloadC
    refine rx_add (by rroom) ?_
    rswap
    rpop
    rpop
    rdup
    rswap
    rsstoreC
    rpop
    rdup
    rmask
    rdup
    rmask
    rpush
    rdup
    rpush
    rmld
    rdup
    rdup
    rdup
    refine rx_mstoreOut (by assumption) (by decide) (fun _ => ?_)
    rpush
    radd
    rswap
    rpop
    rpop
    rpush
    rmld
    rdup
    rswap
    rsub
    rswap
    rlog3
    rpush
    rswap
    rpop
    rswap
    rswap
    rpop
    rpop
    rpop
    refine rx_ret (d := ret) (b := ?_) (M := ?_)


/-- The gas of the body when `caller = src`: neither the allowance nor its slot is touched. -/
def xferGasSelf (sevm : Sevm) (b : Devm) (src dst : Adr) (wad : B256) (G : Nat) : Nat :=
  xfTailGas sevm (pB1 sevm b src) src dst wad G + 60 + 25 + sloadCost sevm b (balSlot src) + 100

/-- `transferFrom` and `transfer` with `caller = src`, in the body (charges named). -/
theorem xfer_body_self_gen {sevm : Sevm} {b : Devm} {G : Nat} {S : List B256} {M : Mem}
    {wad ret : B256} {src dst : Adr} {cH cL2 cS1 cL3 cS2 : Nat}
    (hfork : CoveredFork sevm.benvStat.fork) (hstatic : sevm.isStatic = false)
    (hM : FpMem 96 M) (hroom : S.length < 1000)
    (hle : wad ≤ b.getStorVal sevm.currentTarget (balSlot src)) (hcs : sevm.caller = src)
    (h0 : cH = sloadCost sevm b (balSlot src))
    (h1 : cL2 = sloadCost sevm (pB1 sevm b src) (balSlot src))
    (h2 : cS1 = sstoreCost sevm (tT1 sevm (pB1 sevm b src) src) (balSlot src)
      (tV1 sevm (pB1 sevm b src) src wad))
    (h3 : cL3 = sloadCost sevm (tT2 sevm (pB1 sevm b src) src wad) (balSlot dst))
    (h4 : cS2 = sstoreCost sevm (tT3 sevm (pB1 sevm b src) src dst wad) (balSlot dst)
      (tV2 sevm (pB1 sevm b src) src dst wad))
    (hsentry : gCallStipend < G + 1862 + cS2) :
    ∃ b', SFunc.RunExact prog sevm (St b (wad :: dst.toB256 :: src.toB256 :: ret :: S) M
      (G + 1862 + cS2 + 16 + cL3 + 107 + cS1 + 16 + cL2 + 106 + 60 + 25 + cH + 100)) t_068c_c9
      (.returned (St b' (1 :: S)
        ((scratchW (scratchW (scratchW M src.toB256 3) src.toB256 3) dst.toB256 3).write 96
          wad.toBytes) G)) := by
  obtain ⟨b', htail⟩ := xfer_tail (t0 := pB1 sevm b src) (M := scratchW M src.toB256 3) (G := G)
    (S := S) (wad := wad) (ret := ret) hfork hstatic (hM.scratchW _ _) hroom h1 h2 h3 h4 hsentry
  refine ⟨b', ?_⟩
  rxf_head hle
  refine rx_caller (by rroom) ?_
  rmask
  rdup
  rmask
  refine rx_eq (v := 1) (by simp [B256.eqCheck, hcs]) (by rroom) ?_
  riszero
  rdup
  riszero
  rpush
  refine rx_branch_succ (by decide) ?_
  rdest
  riszero
  rpush
  refine rx_branch_succ (by decide) ?_
  exact htail _

/-- The two hashes of an allowance slot: `keccak(src ‖ 4)`, then `keccak(who ‖ that)`. -/
def alwW (M : Mem) (src who : Adr) : Mem :=
  scratchW (scratchW M src.toB256 4) who.toB256 (mapSlot src.toB256 4)

theorem alwW_fp {n : Nat} {M : Mem} (h : FpMem n M) (src who : Adr) : FpMem n (alwW M src who) :=
  (h.scratchW _ _).scratchW _ _

/-- The `PUSH32 0xff..ff` literal is the maximal word. -/
theorem w_ff32 : Bytes.toB256 [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff] = B256.max := by
  decide

theorem toB256_ne_of_ne {a b : Adr} (h : a ≠ b) : a.toB256 ≠ b.toB256 := fun e =>
  h (by have := congrArg B256.toAdr e; simpa [toAdr_toB256] using this)

/-- The allowance's slot and its `SLOAD`: `keccak(src ‖ 4)`, then `keccak(caller ‖ that)`. -/
macro "rxf_alw" : tactic => `(tactic|
  (rpush; rpush; rdup; rhash; rpush; refine rx_caller (by rroom) ?_; rhash; rsloadC))

/-- The gas of the body when `caller ≠ src` and the allowance is the maximal word: it is read once. -/
def xferGasMax (sevm : Sevm) (b : Devm) (src dst : Adr) (wad : B256) (G : Nat) : Nat :=
  xfTailGas sevm (pA1 sevm b src) src dst wad G + 23 +
    sloadCost sevm (pB1 sevm b src) (allowSlot src sevm.caller) + 255 +
    sloadCost sevm b (balSlot src) + 100

/-- `transferFrom` with `caller ≠ src` and the maximal allowance: the allowance is read (once) and
neither checked nor debited (charges named). -/
theorem xfer_body_max_gen {sevm : Sevm} {b : Devm} {G : Nat} {S : List B256} {M : Mem}
    {wad ret : B256} {src dst : Adr} {cH cA1 cL2 cS1 cL3 cS2 : Nat}
    (hfork : CoveredFork sevm.benvStat.fork) (hstatic : sevm.isStatic = false)
    (hM : FpMem 96 M) (hroom : S.length < 1000)
    (hle : wad ≤ b.getStorVal sevm.currentTarget (balSlot src)) (hcs : sevm.caller ≠ src)
    (hmax : b.getStorVal sevm.currentTarget (allowSlot src sevm.caller) = B256.max)
    (h0 : cH = sloadCost sevm b (balSlot src))
    (hA1 : cA1 = sloadCost sevm (pB1 sevm b src) (allowSlot src sevm.caller))
    (h1 : cL2 = sloadCost sevm (pA1 sevm b src) (balSlot src))
    (h2 : cS1 = sstoreCost sevm (tT1 sevm (pA1 sevm b src) src) (balSlot src)
      (tV1 sevm (pA1 sevm b src) src wad))
    (h3 : cL3 = sloadCost sevm (tT2 sevm (pA1 sevm b src) src wad) (balSlot dst))
    (h4 : cS2 = sstoreCost sevm (tT3 sevm (pA1 sevm b src) src dst wad) (balSlot dst)
      (tV2 sevm (pA1 sevm b src) src dst wad))
    (hsentry : gCallStipend < G + 1862 + cS2) :
    ∃ b', SFunc.RunExact prog sevm (St b (wad :: dst.toB256 :: src.toB256 :: ret :: S) M
      (G + 1862 + cS2 + 16 + cL3 + 107 + cS1 + 16 + cL2 + 106 + 23 + cA1 + 255 + cH + 100))
      t_068c_c9
      (.returned (St b' (1 :: S)
        ((scratchW (scratchW (alwW (scratchW M src.toB256 3) src sevm.caller) src.toB256 3)
          dst.toB256 3).write 96 wad.toBytes) G)) := by
  obtain ⟨b', htail⟩ := xfer_tail (t0 := pA1 sevm b src)
    (M := alwW (scratchW M src.toB256 3) src sevm.caller) (G := G) (S := S) (wad := wad)
    (ret := ret) hfork hstatic (alwW_fp (hM.scratchW _ _) _ _) hroom h1 h2 h3 h4 hsentry
  refine ⟨b', ?_⟩
  simp only [allowSlot] at hmax
  have hne := toB256_ne_of_ne hcs
  rxf_head hle
  refine rx_caller (by rroom) ?_
  rmask
  rdup
  rmask
  refine rx_eq (v := 0) (by simp [B256.eqCheck, hne.symm]) (by rroom) ?_
  riszero
  rdup
  riszero
  rpush
  refine rx_branch_zero ?_
  rpop
  rpush
  rxf_alw
  refine rx_eq (v := 1) (by simp [B256.eqCheck, getStorVal_afterSload, hmax, w_ff32]) (by rroom) ?_
  riszero
  rdest
  riszero
  rpush
  refine rx_branch_succ (by decide) ?_
  exact htail _

/-- The allowance check and debit (entries `0x07ba` and `0x0844`): `require(allowance >= wad)`, then
`allowance -= wad`; `2` gas after the debit's `SSTORE`, `16` after its `SLOAD`, `220` after the
check's, `185` before it.  The continuation is the tail entered at the debited state. -/
theorem xfer_allowance {sevm : Sevm} {a1 : Devm} {G : Nat} {S : List B256} {M : Mem} {y wad ret : B256}
    {src dst : Adr} {o : Outcome} {cA2 cA3 cSA : Nat}
    (hfork : CoveredFork sevm.benvStat.fork) (hstatic : sevm.isStatic = false)
    (hM : FpMem 96 M) (hroom : S.length < 1000)
    (hal : wad ≤ a1.getStorVal sevm.currentTarget (allowSlot src sevm.caller))
    (hA2 : cA2 = sloadCost sevm a1 (allowSlot src sevm.caller))
    (hA3 : cA3 = sloadCost sevm (afterSload sevm a1 (allowSlot src sevm.caller))
      (allowSlot src sevm.caller))
    (hSA : cSA = sstoreCost sevm (afterSload sevm (afterSload sevm a1 (allowSlot src sevm.caller))
      (allowSlot src sevm.caller)) (allowSlot src sevm.caller)
      ((afterSload sevm a1 (allowSlot src sevm.caller)).getStorVal sevm.currentTarget
        (allowSlot src sevm.caller) - wad))
    (hsentry : gCallStipend < G + 2 + cSA)
    (htail : ∀ x, SFunc.RunExact prog sevm
      (St (afterSstore sevm (afterSload sevm (afterSload sevm a1 (allowSlot src sevm.caller))
        (allowSlot src sevm.caller)) (allowSlot src sevm.caller)
        ((afterSload sevm a1 (allowSlot src sevm.caller)).getStorVal sevm.currentTarget
          (allowSlot src sevm.caller) - wad))
        (x :: wad :: dst.toB256 :: src.toB256 :: ret :: S)
        (alwW (alwW M src sevm.caller) src sevm.caller) G) t_08cf_c9 o) :
    SFunc.RunExact prog sevm (St a1 (y :: wad :: dst.toB256 :: src.toB256 :: ret :: S) M
      (G + 2 + cSA + 16 + cA3 + 220 + cA2 + 185)) t_07ba_c9 o := by
  simp only [allowSlot] at hal hA2 hA3 hSA hsentry htail ⊢
  rdup
  rpush
  rpush
  rdup
  rhash
  rpush
  refine rx_caller (by rroom) ?_
  rhash
  rsloadC
  rreq hal
  rdest
  rdup
  rpush
  rpush
  rdup
  rhash
  rpush
  refine rx_caller (by rroom) ?_
  rhash
  rpush
  rdup
  rdup
  rsloadC
  rsub
  rswap
  rpop
  rpop
  rdup
  rswap
  rsstoreC
  rpop
  exact htail _

/-- The gas of the body when `caller ≠ src` and the allowance is neither maximal nor short: it is read
three times and debited. -/
def xferGasAllow (sevm : Sevm) (b : Devm) (src dst : Adr) (wad : B256) (G : Nat) : Nat :=
  xfTailGas sevm (pT0 sevm b src wad) src dst wad G + 2 +
    sstoreCost sevm (pA3 sevm b src) (allowSlot src sevm.caller) (pV sevm b src wad) + 16 +
    sloadCost sevm (pA2 sevm b src) (allowSlot src sevm.caller) + 220 +
    sloadCost sevm (pA1 sevm b src) (allowSlot src sevm.caller) + 185 + 23 +
    sloadCost sevm (pB1 sevm b src) (allowSlot src sevm.caller) + 255 +
    sloadCost sevm b (balSlot src) + 100

/-- `transferFrom` with `caller ≠ src`, a non-maximal allowance that covers `wad`: the allowance
is checked and debited before the balances move (charges named). -/
theorem xfer_body_allow_gen {sevm : Sevm} {b : Devm} {G : Nat} {S : List B256} {M : Mem}
    {wad ret : B256} {src dst : Adr} {cH cA1 cA2 cA3 cSA cL2 cS1 cL3 cS2 : Nat}
    (hfork : CoveredFork sevm.benvStat.fork) (hstatic : sevm.isStatic = false)
    (hM : FpMem 96 M) (hroom : S.length < 1000)
    (hle : wad ≤ b.getStorVal sevm.currentTarget (balSlot src)) (hcs : sevm.caller ≠ src)
    (hmax : b.getStorVal sevm.currentTarget (allowSlot src sevm.caller) ≠ B256.max)
    (hal : wad ≤ b.getStorVal sevm.currentTarget (allowSlot src sevm.caller))
    (h0 : cH = sloadCost sevm b (balSlot src))
    (hA1 : cA1 = sloadCost sevm (pB1 sevm b src) (allowSlot src sevm.caller))
    (hA2 : cA2 = sloadCost sevm (pA1 sevm b src) (allowSlot src sevm.caller))
    (hA3 : cA3 = sloadCost sevm (pA2 sevm b src) (allowSlot src sevm.caller))
    (hSA : cSA = sstoreCost sevm (pA3 sevm b src) (allowSlot src sevm.caller) (pV sevm b src wad))
    (h1 : cL2 = sloadCost sevm (pT0 sevm b src wad) (balSlot src))
    (h2 : cS1 = sstoreCost sevm (tT1 sevm (pT0 sevm b src wad) src) (balSlot src)
      (tV1 sevm (pT0 sevm b src wad) src wad))
    (h3 : cL3 = sloadCost sevm (tT2 sevm (pT0 sevm b src wad) src wad) (balSlot dst))
    (h4 : cS2 = sstoreCost sevm (tT3 sevm (pT0 sevm b src wad) src dst wad) (balSlot dst)
      (tV2 sevm (pT0 sevm b src wad) src dst wad))
    (hsentry : gCallStipend < G + 1862 + cS2) :
    ∃ b', SFunc.RunExact prog sevm (St b (wad :: dst.toB256 :: src.toB256 :: ret :: S) M
      (G + 1862 + cS2 + 16 + cL3 + 107 + cS1 + 16 + cL2 + 106 + 2 + cSA + 16 + cA3 + 220 + cA2 +
        185 + 23 + cA1 + 255 + cH + 100)) t_068c_c9
      (.returned (St b' (1 :: S)
        ((scratchW (scratchW (alwW (alwW (alwW (scratchW M src.toB256 3) src sevm.caller) src sevm.caller)
          src sevm.caller) src.toB256 3) dst.toB256 3).write 96 wad.toBytes) G)) := by
  obtain ⟨b', htail⟩ := xfer_tail (t0 := pT0 sevm b src wad)
    (M := alwW (alwW (alwW (scratchW M src.toB256 3) src sevm.caller) src sevm.caller)
      src sevm.caller) (G := G) (S := S) (wad := wad)
    (ret := ret) hfork hstatic (alwW_fp (alwW_fp (alwW_fp (hM.scratchW _ _) _ _) _ _) _ _)
    hroom h1 h2 h3 h4 hsentry
  refine ⟨b', ?_⟩
  simp only [allowSlot] at hmax
  have hne := toB256_ne_of_ne hcs
  rxf_head hle
  refine rx_caller (by rroom) ?_
  rmask
  rdup
  rmask
  refine rx_eq (v := 0) (by simp [B256.eqCheck, hne.symm]) (by rroom) ?_
  riszero
  rdup
  riszero
  rpush
  refine rx_branch_zero ?_
  rpop
  rpush
  rxf_alw
  refine rx_eq (v := 0) (by simp [B256.eqCheck, getStorVal_afterSload, w_ff32, hmax]) (by rroom) ?_
  riszero
  rdest
  riszero
  rpush
  refine rx_branch_zero ?_
  refine xfer_allowance (a1 := pA1 sevm b src) (cA2 := cA2) (cA3 := cA3) (cSA := cSA) hfork hstatic
    (alwW_fp (hM.scratchW _ _) _ _) hroom ?_ hA2 hA3 hSA (by rsent) ?_
  · simp only [getStorVal_afterSload]; exact hal
  · exact htail


/-! ## The wrappers -/

/-- The `transferFrom` wrapper (entry 25, `0x01ca`): the `nonpayable` guard, the three argument decodes,
the call into the body, the boolean tail.  `128` gas before the body, `62` after it. -/
theorem transferFrom_wrapper {sevm : Sevm} {b b' : Devm} {G X : Nat} {sel : B256} {M' : Mem}
    (hval : sevm.value = 0)
    (hbody : SFunc.RunExact prog sevm
      (St b [Sevm.dataWord sevm 68, (Sevm.dataWord sevm 36).toAdr.toB256,
        (Sevm.dataWord sevm 4).toAdr.toB256, Bytes.toB256 [2, 41], sel] memFp X) t_068c_c9
      (.returned (St b' [1, sel] M' (G + 62))))
    (hM' : FpMem 128 M') :
    ∃ post, SFunc.RunExact prog sevm (St b [sel] memFp (X + 128)) t_01ca_c25 (.halted post) ∧
      post.gasLeft = G ∧ post.output = (1 : B256).toBytes := by
  obtain ⟨post, htail, hg, ho⟩ := bool_tail (sevm := sevm) (b := b') (G := G) (sel := sel) hM'
  refine ⟨post, ?_, hg, ho⟩
  rdest
  refine rx_callvalue (by simp) ?_
  refine rx_iszero (v := 1) (by simp [B256.eqCheck, hval]) (by simp) ?_
  rpush
  refine rx_branch_succ (by decide) ?_
  rdest
  rpush
  rpush
  rdup
  rdup
  refine rx_calldataload (by rroom) ?_
  rmask
  rswap
  rpush
  radd
  rswap
  rswap
  rswap
  rdup
  refine rx_calldataload (by rroom) ?_
  rmask
  rswap
  rpush
  radd
  rswap
  rswap
  rswap
  rdup
  refine rx_calldataload (by rroom) ?_
  rswap
  rpush
  radd
  rswap
  rswap
  rswap
  rpop
  rpop
  rpush
  exact rx_callRet (j := 9) rfl hbody htail

/-- The `transfer` wrapper (entry 20, `0x0370`) and its inner entry (entry 3, `0x0bce`): the guard, the
two argument decodes, the call into the `transferFrom` body with the caller as `src`, the return
juggling, the boolean tail.  `98 + 26` gas before the body, `24 + 62` after it. -/
theorem transfer_wrapper {sevm : Sevm} {b b' : Devm} {G X : Nat} {sel : B256} {M' : Mem}
    (hval : sevm.value = 0)
    (hbody : SFunc.RunExact prog sevm
      (St b [Sevm.dataWord sevm 36, (Sevm.dataWord sevm 4).toAdr.toB256, sevm.caller.toB256,
        Bytes.toB256 [0x0b, 0xdb], 0, Sevm.dataWord sevm 36, (Sevm.dataWord sevm 4).toAdr.toB256,
        Bytes.toB256 [0x03, 0xb0], sel] memFp X) t_068c_c9
      (.returned (St b' [1, 0, Sevm.dataWord sevm 36, (Sevm.dataWord sevm 4).toAdr.toB256,
        Bytes.toB256 [0x03, 0xb0], sel] M' (G + 24 + 62))))
    (hM' : FpMem 128 M') :
    ∃ post, SFunc.RunExact prog sevm (St b [sel] memFp (X + 26 + 98)) t_0370_c20 (.halted post) ∧
      post.gasLeft = G ∧ post.output = (1 : B256).toBytes := by
  obtain ⟨post, htail, hg, ho⟩ := bool_tail (sevm := sevm) (b := b') (G := G) (sel := sel) hM'
  refine ⟨post, ?_, hg, ho⟩
  rdest
  refine rx_callvalue (by simp) ?_
  refine rx_iszero (v := 1) (by simp [B256.eqCheck, hval]) (by simp) ?_
  rpush
  refine rx_branch_succ (by decide) ?_
  rdest
  rpush
  rpush
  rdup
  rdup
  refine rx_calldataload (by rroom) ?_
  rmask
  rswap
  rpush
  radd
  rswap
  rswap
  rswap
  rdup
  refine rx_calldataload (by rroom) ?_
  rswap
  rpush
  radd
  rswap
  rswap
  rswap
  rpop
  rpop
  rpush
  refine rx_callRet (D := St b' [1, sel] M' (G + 62)) (j := 3) rfl ?_ htail
  · rdest
    rpush
    rpush
    refine rx_caller (by rroom) ?_
    rdup
    rdup
    rpush
    refine rx_callRet (j := 9) rfl hbody ?_
    rdest
    rswap
    rpop
    rswap
    rswap
    rpop
    rpop
    exact rx_ret


/-! ## The bodies at their exact costs -/

theorem xferGasSelf_eq {sevm : Sevm} {b : Devm} {src dst : Adr} {wad : B256} {G : Nat} :
    xferGasSelf sevm b src dst wad G = xferGasSelf sevm b src dst wad 0 + G := by
  unfold xferGasSelf xfTailGas; omega

theorem xferGasMax_eq {sevm : Sevm} {b : Devm} {src dst : Adr} {wad : B256} {G : Nat} :
    xferGasMax sevm b src dst wad G = xferGasMax sevm b src dst wad 0 + G := by
  unfold xferGasMax xfTailGas; omega

theorem xferGasAllow_eq {sevm : Sevm} {b : Devm} {src dst : Adr} {wad : B256} {G : Nat} :
    xferGasAllow sevm b src dst wad G = xferGasAllow sevm b src dst wad 0 + G := by
  unfold xferGasAllow xfTailGas; omega

/-- `xfer_body_self_gen` at the costs the states determine. -/
theorem xfer_body_self {sevm : Sevm} {b : Devm} {G : Nat} {S : List B256} {M : Mem}
    {wad ret : B256} {src dst : Adr}
    (hfork : CoveredFork sevm.benvStat.fork) (hstatic : sevm.isStatic = false)
    (hM : FpMem 96 M) (hroom : S.length < 1000)
    (hle : wad ≤ b.getStorVal sevm.currentTarget (balSlot src)) (hcs : sevm.caller = src)
    (hsentry : gCallStipend < G + 1862 + sstoreCost sevm
      (tT3 sevm (pB1 sevm b src) src dst wad) (balSlot dst) (tV2 sevm (pB1 sevm b src) src dst wad)) :
    ∃ b', SFunc.RunExact prog sevm (St b (wad :: dst.toB256 :: src.toB256 :: ret :: S) M
      (xferGasSelf sevm b src dst wad G)) t_068c_c9
      (.returned (St b' (1 :: S)
        ((scratchW (scratchW (scratchW M src.toB256 3) src.toB256 3) dst.toB256 3).write 96
          wad.toBytes) G)) :=
  xfer_body_self_gen hfork hstatic hM hroom hle hcs rfl rfl rfl rfl rfl hsentry

/-- `xfer_body_max_gen` at the costs the states determine. -/
theorem xfer_body_max {sevm : Sevm} {b : Devm} {G : Nat} {S : List B256} {M : Mem}
    {wad ret : B256} {src dst : Adr}
    (hfork : CoveredFork sevm.benvStat.fork) (hstatic : sevm.isStatic = false)
    (hM : FpMem 96 M) (hroom : S.length < 1000)
    (hle : wad ≤ b.getStorVal sevm.currentTarget (balSlot src)) (hcs : sevm.caller ≠ src)
    (hmax : b.getStorVal sevm.currentTarget (allowSlot src sevm.caller) = B256.max)
    (hsentry : gCallStipend < G + 1862 + sstoreCost sevm
      (tT3 sevm (pA1 sevm b src) src dst wad) (balSlot dst) (tV2 sevm (pA1 sevm b src) src dst wad)) :
    ∃ b', SFunc.RunExact prog sevm (St b (wad :: dst.toB256 :: src.toB256 :: ret :: S) M
      (xferGasMax sevm b src dst wad G)) t_068c_c9
      (.returned (St b' (1 :: S)
        ((scratchW (scratchW (alwW (scratchW M src.toB256 3) src sevm.caller) src.toB256 3)
          dst.toB256 3).write 96 wad.toBytes) G)) :=
  xfer_body_max_gen hfork hstatic hM hroom hle hcs hmax rfl rfl rfl rfl rfl rfl hsentry

/-- `xfer_body_allow_gen` at the costs the states determine. -/
theorem xfer_body_allow {sevm : Sevm} {b : Devm} {G : Nat} {S : List B256} {M : Mem}
    {wad ret : B256} {src dst : Adr}
    (hfork : CoveredFork sevm.benvStat.fork) (hstatic : sevm.isStatic = false)
    (hM : FpMem 96 M) (hroom : S.length < 1000)
    (hle : wad ≤ b.getStorVal sevm.currentTarget (balSlot src)) (hcs : sevm.caller ≠ src)
    (hmax : b.getStorVal sevm.currentTarget (allowSlot src sevm.caller) ≠ B256.max)
    (hal : wad ≤ b.getStorVal sevm.currentTarget (allowSlot src sevm.caller))
    (hsentry : gCallStipend < G + 1862 + sstoreCost sevm
      (tT3 sevm (pT0 sevm b src wad) src dst wad) (balSlot dst)
      (tV2 sevm (pT0 sevm b src wad) src dst wad)) :
    ∃ b', SFunc.RunExact prog sevm (St b (wad :: dst.toB256 :: src.toB256 :: ret :: S) M
      (xferGasAllow sevm b src dst wad G)) t_068c_c9
      (.returned (St b' (1 :: S)
        ((scratchW (scratchW (alwW (alwW (alwW (scratchW M src.toB256 3) src sevm.caller) src sevm.caller)
          src sevm.caller) src.toB256 3) dst.toB256 3).write 96 wad.toBytes) G)) :=
  xfer_body_allow_gen hfork hstatic hM hroom hle hcs hmax hal rfl rfl rfl rfl rfl rfl rfl rfl rfl
    hsentry


/-! ## The dispatcher and the whole call -/

/-- WETH9's `transferFrom(address,address,uint256)` selector. -/
abbrev tfSel : B256 := selector "transferFrom" [.address, .address, .uint256]

theorem tfSel_eq : tfSel = 0x23b872dd := by decide +kernel

/-- WETH9's `transfer(address,uint256)` selector. -/
abbrev trSel : B256 := selector "transfer" [.address, .uint256]

theorem trSel_eq : trSel = 0xa9059cbb := by decide +kernel

/-- The dispatcher path to `transferFrom`: two non-matching comparisons after the head's, then the
match at the fourth, jumping to entry 25.  150 gas. -/
theorem dispatch_transferFrom {sevm : Sevm} {b : Devm} {g : Nat} {o : Outcome}
    (h_len : 4 ≤ sevm.data.length) (h_len' : sevm.data.length < 2 ^ 256)
    (hsel : Sevm.selector sevm = 0x23b872dd)
    (k : SFunc.RunExact prog sevm (St b [Sevm.selector sevm] memFp g) t_01ca_c25 o) :
    SFunc.RunExact prog sevm (St b [] Mem.empty (g + 150)) t_0000_c0 o := by
  refine dispatch_head h_len h_len' (by rw [hsel]; decide) ?_
  refine cmp_miss (by rw [hsel]; decide) ?_
  refine cmp_miss (by rw [hsel]; decide) ?_
  exact cmp_hit (j := 25) (by rw [hsel]; decide) rfl k

/-- The dispatcher path to `transfer`: seven non-matching comparisons after the head's, then the match
at the ninth, jumping to entry 20.  260 gas. -/
theorem dispatch_transfer {sevm : Sevm} {b : Devm} {g : Nat} {o : Outcome}
    (h_len : 4 ≤ sevm.data.length) (h_len' : sevm.data.length < 2 ^ 256)
    (hsel : Sevm.selector sevm = 0xa9059cbb)
    (k : SFunc.RunExact prog sevm (St b [Sevm.selector sevm] memFp g) t_0370_c20 o) :
    SFunc.RunExact prog sevm (St b [] Mem.empty (g + 260)) t_0000_c0 o := by
  refine dispatch_head h_len h_len' (by rw [hsel]; decide) ?_
  refine cmp_miss (by rw [hsel]; decide) ?_
  refine cmp_miss (by rw [hsel]; decide) ?_
  refine cmp_miss (by rw [hsel]; decide) ?_
  refine cmp_miss (by rw [hsel]; decide) ?_
  refine cmp_miss (by rw [hsel]; decide) ?_
  refine cmp_miss (by rw [hsel]; decide) ?_
  refine cmp_miss (by rw [hsel]; decide) ?_
  exact cmp_hit (j := 20) (by rw [hsel]; decide) rfl k

/-- **What `transferFrom(src, dst, wad)` costs when the caller is `src`**: the dispatcher (150), the
wrapper (128), the body (`xferGasSelf`), the boolean tail (62). -/
def transferFromGasSelf (sevm : Sevm) (pre : Devm) : Nat :=
  xferGasSelf sevm pre (Sevm.dataWord sevm 4).toAdr (Sevm.dataWord sevm 36).toAdr
    (Sevm.dataWord sevm 68) 0 + 340

/-- **What `transferFrom(src, dst, wad)` costs when the caller is not `src` and the allowance is the
maximal word.** -/
def transferFromGasMax (sevm : Sevm) (pre : Devm) : Nat :=
  xferGasMax sevm pre (Sevm.dataWord sevm 4).toAdr (Sevm.dataWord sevm 36).toAdr
    (Sevm.dataWord sevm 68) 0 + 340

/-- **What `transferFrom(src, dst, wad)` costs when the caller is not `src`, the allowance is not the
maximal word and covers `wad`.** -/
def transferFromGasAllow (sevm : Sevm) (pre : Devm) : Nat :=
  xferGasAllow sevm pre (Sevm.dataWord sevm 4).toAdr (Sevm.dataWord sevm 36).toAdr
    (Sevm.dataWord sevm 68) 0 + 340

/-- **What `transfer(dst, wad)` costs**: the dispatcher (260), the wrapper (98 + 26), the body at
`src = caller` (`xferGasSelf`), the return juggling (24), the boolean tail (62). -/
def transferGas (sevm : Sevm) (pre : Devm) : Nat :=
  xferGasSelf sevm pre sevm.caller (Sevm.dataWord sevm 4).toAdr (Sevm.dataWord sevm 36) 0 + 470

/-- A frame entering `transferFrom` with `caller = src` and `balanceOf[src] >= wad` succeeds at exactly
`transferFromGasSelf`.  (`h_sentry`: the `SSTORE` of `dst`'s balance runs with more than `gCallStipend`
gas.) -/
theorem weth9_transferFrom_self_runExact {sevm : Sevm} {pre : Devm} {G : Nat}
    (hfork : CoveredFork sevm.benvStat.fork) (h_static : sevm.isStatic = false)
    (h_value : sevm.value = 0) (h_sel : Sevm.selector sevm = tfSel)
    (h_len : 4 ≤ sevm.data.length) (h_len' : sevm.data.length < 2 ^ 256)
    (h_stack : pre.stack = []) (h_mem : pre.memory = Mem.empty)
    (hcs : sevm.caller = (Sevm.dataWord sevm 4).toAdr)
    (hle : Sevm.dataWord sevm 68 ≤
      pre.getStorVal sevm.currentTarget (balSlot (Sevm.dataWord sevm 4).toAdr))
    (h_gas : pre.gasLeft = G + transferFromGasSelf sevm pre)
    (h_sentry : gCallStipend < G + 62 + 1862 + sstoreCost sevm
      (tT3 sevm (pB1 sevm pre (Sevm.dataWord sevm 4).toAdr) (Sevm.dataWord sevm 4).toAdr
        (Sevm.dataWord sevm 36).toAdr (Sevm.dataWord sevm 68))
      (balSlot (Sevm.dataWord sevm 36).toAdr)
      (tV2 sevm (pB1 sevm pre (Sevm.dataWord sevm 4).toAdr) (Sevm.dataWord sevm 4).toAdr
        (Sevm.dataWord sevm 36).toAdr (Sevm.dataWord sevm 68))) :
    ∃ post, SProg.RunExact prog sevm pre post ∧ post.gasLeft = G ∧
      post.output = (1 : B256).toBytes := by
  have hsel : Sevm.selector sevm = 0x23b872dd := h_sel.trans tfSel_eq
  have hg : xferGasSelf sevm pre (Sevm.dataWord sevm 4).toAdr (Sevm.dataWord sevm 36).toAdr
      (Sevm.dataWord sevm 68) (G + 62) + 128 + 150 = pre.gasLeft := by
    rw [h_gas, xferGasSelf_eq]; unfold transferFromGasSelf; omega
  obtain ⟨b', hb⟩ := xfer_body_self (S := [Sevm.selector sevm]) (ret := Bytes.toB256 [2, 41])
    (G := G + 62) (b := pre) hfork h_static fp_memFp (by simp) hle hcs h_sentry
  obtain ⟨post, hw, hpg, hpo⟩ := transferFrom_wrapper (sevm := sevm) (b := pre) (b' := b') (G := G)
    (sel := Sevm.selector sevm) h_value hb
    (((((fp_memFp.scratchW _ _).scratchW _ _).scratchW _ _)).write_out _)
  refine ⟨post, ⟨_, rfl, ?_⟩, hpg, hpo⟩
  have h0 := dispatch_transferFrom (b := pre) h_len h_len' hsel hw
  rw [pre_eq_St h_stack h_mem hg] at h0
  exact h0


/-- A frame entering `transferFrom` with `caller ≠ src`, the maximal allowance and
`balanceOf[src] >= wad` succeeds at exactly `transferFromGasMax` (the allowance is read, not debited). -/
theorem weth9_transferFrom_max_runExact {sevm : Sevm} {pre : Devm} {G : Nat}
    (hfork : CoveredFork sevm.benvStat.fork) (h_static : sevm.isStatic = false)
    (h_value : sevm.value = 0) (h_sel : Sevm.selector sevm = tfSel)
    (h_len : 4 ≤ sevm.data.length) (h_len' : sevm.data.length < 2 ^ 256)
    (h_stack : pre.stack = []) (h_mem : pre.memory = Mem.empty)
    (hcs : sevm.caller ≠ (Sevm.dataWord sevm 4).toAdr)
    (hle : Sevm.dataWord sevm 68 ≤
      pre.getStorVal sevm.currentTarget (balSlot (Sevm.dataWord sevm 4).toAdr))
    (hmax : pre.getStorVal sevm.currentTarget
      (allowSlot (Sevm.dataWord sevm 4).toAdr sevm.caller) = B256.max)
    (h_gas : pre.gasLeft = G + transferFromGasMax sevm pre)
    (h_sentry : gCallStipend < G + 62 + 1862 + sstoreCost sevm
      (tT3 sevm (pA1 sevm pre (Sevm.dataWord sevm 4).toAdr) (Sevm.dataWord sevm 4).toAdr
        (Sevm.dataWord sevm 36).toAdr (Sevm.dataWord sevm 68))
      (balSlot (Sevm.dataWord sevm 36).toAdr)
      (tV2 sevm (pA1 sevm pre (Sevm.dataWord sevm 4).toAdr) (Sevm.dataWord sevm 4).toAdr
        (Sevm.dataWord sevm 36).toAdr (Sevm.dataWord sevm 68))) :
    ∃ post, SProg.RunExact prog sevm pre post ∧ post.gasLeft = G ∧
      post.output = (1 : B256).toBytes := by
  have hsel : Sevm.selector sevm = 0x23b872dd := h_sel.trans tfSel_eq
  have hg : xferGasMax sevm pre (Sevm.dataWord sevm 4).toAdr (Sevm.dataWord sevm 36).toAdr
      (Sevm.dataWord sevm 68) (G + 62) + 128 + 150 = pre.gasLeft := by
    rw [h_gas, xferGasMax_eq]; unfold transferFromGasMax; omega
  obtain ⟨b', hb⟩ := xfer_body_max (S := [Sevm.selector sevm]) (ret := Bytes.toB256 [2, 41])
    (G := G + 62) (b := pre) hfork h_static fp_memFp (by simp) hle hcs hmax h_sentry
  obtain ⟨post, hw, hpg, hpo⟩ := transferFrom_wrapper (sevm := sevm) (b := pre) (b' := b') (G := G)
    (sel := Sevm.selector sevm) h_value hb
    ((((alwW_fp (fp_memFp.scratchW _ _) _ _).scratchW _ _).scratchW _ _).write_out _)
  refine ⟨post, ⟨_, rfl, ?_⟩, hpg, hpo⟩
  have h0 := dispatch_transferFrom (b := pre) h_len h_len' hsel hw
  rw [pre_eq_St h_stack h_mem hg] at h0
  exact h0

/-- A frame entering `transferFrom` with `caller ≠ src`, an allowance that is not the maximal word and
covers `wad`, and `balanceOf[src] >= wad` succeeds at exactly `transferFromGasAllow`. -/
theorem weth9_transferFrom_allow_runExact {sevm : Sevm} {pre : Devm} {G : Nat}
    (hfork : CoveredFork sevm.benvStat.fork) (h_static : sevm.isStatic = false)
    (h_value : sevm.value = 0) (h_sel : Sevm.selector sevm = tfSel)
    (h_len : 4 ≤ sevm.data.length) (h_len' : sevm.data.length < 2 ^ 256)
    (h_stack : pre.stack = []) (h_mem : pre.memory = Mem.empty)
    (hcs : sevm.caller ≠ (Sevm.dataWord sevm 4).toAdr)
    (hle : Sevm.dataWord sevm 68 ≤
      pre.getStorVal sevm.currentTarget (balSlot (Sevm.dataWord sevm 4).toAdr))
    (hmax : pre.getStorVal sevm.currentTarget
      (allowSlot (Sevm.dataWord sevm 4).toAdr sevm.caller) ≠ B256.max)
    (hal : Sevm.dataWord sevm 68 ≤ pre.getStorVal sevm.currentTarget
      (allowSlot (Sevm.dataWord sevm 4).toAdr sevm.caller))
    (h_gas : pre.gasLeft = G + transferFromGasAllow sevm pre)
    (h_sentry : gCallStipend < G + 62 + 1862 + sstoreCost sevm
      (tT3 sevm (pT0 sevm pre (Sevm.dataWord sevm 4).toAdr (Sevm.dataWord sevm 68))
        (Sevm.dataWord sevm 4).toAdr (Sevm.dataWord sevm 36).toAdr (Sevm.dataWord sevm 68))
      (balSlot (Sevm.dataWord sevm 36).toAdr)
      (tV2 sevm (pT0 sevm pre (Sevm.dataWord sevm 4).toAdr (Sevm.dataWord sevm 68))
        (Sevm.dataWord sevm 4).toAdr (Sevm.dataWord sevm 36).toAdr (Sevm.dataWord sevm 68))) :
    ∃ post, SProg.RunExact prog sevm pre post ∧ post.gasLeft = G ∧
      post.output = (1 : B256).toBytes := by
  have hsel : Sevm.selector sevm = 0x23b872dd := h_sel.trans tfSel_eq
  have hg : xferGasAllow sevm pre (Sevm.dataWord sevm 4).toAdr (Sevm.dataWord sevm 36).toAdr
      (Sevm.dataWord sevm 68) (G + 62) + 128 + 150 = pre.gasLeft := by
    rw [h_gas, xferGasAllow_eq]; unfold transferFromGasAllow; omega
  obtain ⟨b', hb⟩ := xfer_body_allow (S := [Sevm.selector sevm]) (ret := Bytes.toB256 [2, 41])
    (G := G + 62) (b := pre) hfork h_static fp_memFp (by simp) hle hcs hmax hal h_sentry
  obtain ⟨post, hw, hpg, hpo⟩ := transferFrom_wrapper (sevm := sevm) (b := pre) (b' := b') (G := G)
    (sel := Sevm.selector sevm) h_value hb
    ((((alwW_fp (alwW_fp (alwW_fp (fp_memFp.scratchW _ _) _ _) _ _) _ _).scratchW _ _).scratchW _ _).write_out _)
  refine ⟨post, ⟨_, rfl, ?_⟩, hpg, hpo⟩
  have h0 := dispatch_transferFrom (b := pre) h_len h_len' hsel hw
  rw [pre_eq_St h_stack h_mem hg] at h0
  exact h0

/-- A frame entering `transfer(dst, wad)` with `balanceOf[caller] >= wad` succeeds at exactly
`transferGas`. -/
theorem weth9_transfer_runExact {sevm : Sevm} {pre : Devm} {G : Nat}
    (hfork : CoveredFork sevm.benvStat.fork) (h_static : sevm.isStatic = false)
    (h_value : sevm.value = 0) (h_sel : Sevm.selector sevm = trSel)
    (h_len : 4 ≤ sevm.data.length) (h_len' : sevm.data.length < 2 ^ 256)
    (h_stack : pre.stack = []) (h_mem : pre.memory = Mem.empty)
    (hle : Sevm.dataWord sevm 36 ≤ pre.getStorVal sevm.currentTarget (balSlot sevm.caller))
    (h_gas : pre.gasLeft = G + transferGas sevm pre)
    (h_sentry : gCallStipend < G + 24 + 62 + 1862 + sstoreCost sevm
      (tT3 sevm (pB1 sevm pre sevm.caller) sevm.caller (Sevm.dataWord sevm 4).toAdr
        (Sevm.dataWord sevm 36)) (balSlot (Sevm.dataWord sevm 4).toAdr)
      (tV2 sevm (pB1 sevm pre sevm.caller) sevm.caller (Sevm.dataWord sevm 4).toAdr
        (Sevm.dataWord sevm 36))) :
    ∃ post, SProg.RunExact prog sevm pre post ∧ post.gasLeft = G ∧
      post.output = (1 : B256).toBytes := by
  have hsel : Sevm.selector sevm = 0xa9059cbb := h_sel.trans trSel_eq
  have hg : xferGasSelf sevm pre sevm.caller (Sevm.dataWord sevm 4).toAdr (Sevm.dataWord sevm 36)
      (G + 24 + 62) + 26 + 98 + 260 = pre.gasLeft := by
    rw [h_gas, xferGasSelf_eq]; unfold transferGas; omega
  obtain ⟨b', hb⟩ := xfer_body_self (S := [0, Sevm.dataWord sevm 36, (Sevm.dataWord sevm 4).toAdr.toB256,
      Bytes.toB256 [0x03, 0xb0], Sevm.selector sevm]) (ret := Bytes.toB256 [0x0b, 0xdb])
    (G := G + 24 + 62) (b := pre) hfork h_static fp_memFp (by simp) hle rfl h_sentry
  obtain ⟨post, hw, hpg, hpo⟩ := transfer_wrapper (sevm := sevm) (b := pre) (b' := b') (G := G)
    (sel := Sevm.selector sevm) h_value hb
    (((((fp_memFp.scratchW _ _).scratchW _ _).scratchW _ _)).write_out _)
  refine ⟨post, ⟨_, rfl, ?_⟩, hpg, hpo⟩
  have h0 := dispatch_transfer (b := pre) h_len h_len' hsel hw
  rw [pre_eq_St h_stack h_mem hg] at h0
  exact h0

end Blanc.Lift.Weth9
