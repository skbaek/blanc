import Blanc.Lift.Curve3Pool.ExchangeLive
import Blanc.Lift.Curve3Pool.Walk.ExchangeExactWalk
import Blanc.ExecDeterminism

/-!
# Exact-gas liveness of `exchange`

`exchange_live_exact`: at a `Checkpoint`, when the model's `exchange` succeeds in
`exEnv sevm i j (exBalOpt i B1) (exBalOpt i B2)` and the calls are exact profiles with the data
`P` (the input coin's `transferFrom`, for the fee coin its two `balanceOf(self)` reads, the output
coin's `transfer` of the model's amount), the checked model words `x0 x1 x2 amp v` (pinned by
`xpChk`, `aChk` and `getYChk`) and with them the cost `c = exExactCost sevm pre P x0 x1 x2 B1 B2
amp v` are fixed before any residual gas. For every `R ≥ costExchange … + 4 U + 60000`
(headroom, not cost) at which the entry's gas measure is a word and every execution's children
keep the pool's storage and the code at `4` (`hkeep`, at that entry gas, as `exchange_live` takes
it), the frame entered with `R + c` has an actual successful execution ending with exactly `R` gas,
whose effect is `exchange_live`'s: the same `RawEffect`, `Checkpoint` and post-push invariant.

The route is `removeLiquidity_live_exact`'s: the exact byte walk `rx_ex_frame_exact` gives a run
ending with `R`; `lift_exactM` makes it an `Exec`. `exchange_live`, applied at the same entry gas
with the exact profiles' bounded projections, gives an `Exec` with the effect; executions from one
entry have one result (`Exec.result_unique`), so that post is the exact walk's.
-/

namespace Blanc.Lift.Curve3Pool

open Jaune Blanc.Lift Blanc.StableSwapNewton

/-- **Exact-gas liveness of `exchange`** (see the module note). -/
theorem exchange_live_exact {sevm : Sevm} {pre : Devm} {s : State} {o : Out} {i j : Fin 3}
    {B1 B2 : B256} {W W' W'' : Devm → Prop} {U : Nat} (P : ExchangeExactCalls)
    (hcode : sevm.code = code) (hfork : CoveredFork sevm.benvStat.fork)
    (hstatic : sevm.isStatic = false) (hdepth : sevm.depth ≠ 0)
    (hlen : 4 ≤ sevm.data.length) (hcd : sevm.data.length < 2 ^ 256)
    (hsel : Sevm.selector sevm = selExchange)
    (hi : i.val = (exI sevm).toNat) (hj : j.val = (exJ sevm).toNat)
    (hck : Checkpoint (pre.getStor sevm.currentTarget) s)
    (hstep : step s (exEnv sevm i j (exBalOpt i B1) (exBalOpt i B2)) (decodeCall sevm) = some o)
    (hcoin : ∀ k : Fin 3,
      ¬ sevm.benvStat.rules.isPrecomp ((pre.getStor sevm.currentTarget).get (coinSlot k)).toAdr)
    (hpc : pre.getCode sevm.currentTarget ≠ .empty) (hid : IdReady sevm pre)
    (hWc : WClosed sevm W) (hW'c : WClosed sevm W') (hWb : W pre)
    (hbal : i = feeIndex →
      StaticWordCallProfile sevm W W ((pre.getStor sevm.currentTarget).get (coinSlot i))
        (balanceOfData sevm.currentTarget) B1 U 0x3dc 0x24 0x440 P.balD1 P.balN1 ∧
      StaticWordCallProfile sevm W' W' ((pre.getStor sevm.currentTarget).get (coinSlot i))
        (balanceOfData sevm.currentTarget) B2 U 0x71c 0x24 0x780 P.balD2 P.balN2)
    (hpull : MutableCallProfile sevm W W' ((pre.getStor sevm.currentTarget).get (coinSlot i))
      (transferFromSel ++ sevm.caller.toB256.toBytes ++ sevm.currentTarget.toB256.toBytes ++
        (exDx sevm).toBytes) RawCallOk U 0x600 0x64 0x6c0 P.pullD P.pullN)
    (hW''c : WClosed sevm W'')
    (hpush : MutableCallProfile sevm W' W'' ((pre.getStor sevm.currentTarget).get (coinSlot j))
      (transferSel ++ sevm.caller.toB256.toBytes ++ (Nat.toB256 (exPushAmt o)).toBytes) RawCallOk U
      0xb60 0x44 0xc00 P.pushD P.pushN) :
    ∃ (x0 x1 x2 : B256) (amp v : Nat),
      xpChk ⟨(balAt (pre.getStor sevm.currentTarget) 0).toNat,
        (balAt (pre.getStor sevm.currentTarget) 1).toNat,
        (balAt (pre.getStor sevm.currentTarget) 2).toNat⟩ = some ⟨x0.toNat, x1.toNat, x2.toNat⟩ ∧
      aChk s sevm.benvStat.time.toNat = some amp ∧
      (∃ (hi3 : (exI sevm).toNat < 3) (hj3 : (exJ sevm).toNat < 3),
        getYChk amp ⟨(exI sevm).toNat, hi3⟩ ⟨(exJ sevm).toNat, hj3⟩
          (exW3 x0 x1 x2 (exI sevm).toNat + exCred sevm B1 B2 * exRate (exI sevm).toNat /
            exR0).toNat (V3.mk x0.toNat x1.toNat x2.toNat).get = some v) ∧
      ∀ R, costExchange sevm pre s (exEnv sevm i j (exBalOpt i B1) (exBalOpt i B2)) i j
          (exDx sevm).toNat + 4 * U + 60000 ≤ R →
        (St pre [] Mem.empty (R + exExactCost sevm pre P x0 x1 x2 B1 B2 amp v)).gasMeasure <
          2 ^ 256 →
        (∀ post (exc : Exec 0 sevm
            (St pre [] Mem.empty (R + exExactCost sevm pre P x0 x1 x2 B1 B2 amp v)) (.ok post)),
          PoolCallsKeep ⟨0, sevm, St pre [] Mem.empty
            (R + exExactCost sevm pre P x0 x1 x2 B1 B2 amp v), .ok post, exc⟩ ∧
            ∀ c ∈ Exec.childFrames exc, c.post.getCode 4 = c.pre.getCode 4) →
        ∃ post, ∃ exc : Exec 0 sevm
            (St pre [] Mem.empty (R + exExactCost sevm pre P x0 x1 x2 B1 B2 amp v)) (.ok post),
          ∃ bp bq,
          pullIn (exEnv sevm i j bp bq) i (exDx sevm).toNat =
            pullIn (exEnv sevm i j (exBalOpt i B1) (exBalOpt i B2)) i (exDx sevm).toNat ∧
          RawEffect ⟨0, sevm, St pre [] Mem.empty
            (R + exExactCost sevm pre P x0 x1 x2 B1 B2 amp v), .ok post, exc⟩ post
            (exEnv sevm i j bp bq) o ∧
          Checkpoint (post.getStor sevm.currentTarget) o.state ∧ W'' post ∧ post.gasLeft = R := by
  have hi3 : (exI sevm).toNat < 3 := hi ▸ i.isLt
  have hj3 : (exJ sevm).toNat < 3 := hj ▸ j.isLt
  obtain rfl : i = ⟨(exI sevm).toNat, hi3⟩ := Fin.ext hi
  obtain rfl : j = ⟨(exJ sevm).toNat, hj3⟩ := Fin.ext hj
  obtain ⟨hv0, hex⟩ := ex_body hi3 hj3 hlen hsel hstep
  have hval : sevm.value = 0 := B256.toNat_inj _ _ (by rw [show sevm.value.toNat = 0 from hv0]; rfl)
  obtain ⟨x0, x1, x2, amp, v, hi3', hj3', hk, hX, hsub, hmx, hax, hA, hres, hy1, hy2, hmf, hsf, hmo,
    hmin, hma, hmap, hbi, hbj1, hbj2, hpa, -, -, -, -⟩ := ex_words hck.abs rfl rfl hex
  refine ⟨x0, x1, x2, amp, v, hX, hA, ⟨hi3', hj3', hres⟩, fun R hR hGm hkeep => ?_⟩
  have hG256 : R + exExactCost sevm pre P x0 x1 x2 B1 B2 amp v < 2 ^ 256 := by
    have e : (St pre [] Mem.empty (R + exExactCost sevm pre P x0 x1 x2 B1 B2 amp v)).gasMeasure =
      R + exExactCost sevm pre P x0 x1 x2 B1 B2 amp v + pre.mach.stateGas.spilled +
        pre.mach.stateGas.committedSpill := rfl
    omega
  have hci : coinSlot ⟨(exI sevm).toNat, hi3⟩ = coinsBase + exI sevm := by
    simp only [coinSlot, toB256_toNat]
  have hcj : coinSlot ⟨(exJ sevm).toNat, hj3⟩ = coinsBase + exJ sevm := by
    simp only [coinSlot, toB256_toNat]
  have hpull' := hpull
  rw [hci] at hpull'
  have hpush' := hpush
  rw [hcj, hpa, toB256_toNat] at hpush'
  -- the exact run
  obtain ⟨r, hr, D, rfl, hDg⟩ := rx_ex_frame_exact (pre := pre) (s0 := s)
    (Q := fun r => ∃ D', r = .halted D' ∧ D'.gasLeft = R) P
    hfork hstatic hdepth hlen hcd hsel hid hWc hW'c hWb hck.abs hck.unlocked hval
    (by rw [hck.abs.isKilled, hk]; rfl) hi3 hj3 hX
    (fun h2 => by
      have hb := hbal (Fin.ext (show (exI sevm).toNat = 2 by rw [h2]; rfl))
      rw [hci] at hb
      exact ⟨hb.1, hb.2, hsub h2⟩)
    hpull' hmx hax hA hres hy1 hy2 hmf hsf hmo hmin hma hmap hbi hbj1 hbj2 hW''c hpush'
    (by omega) hG256 (fun D' _ hg => ⟨D', rfl, hg⟩)
  obtain ⟨exD⟩ := lift_exactM cert_checkM cert_jumpsOkM hcode hfork ⟨t_0000_c0, rfl, hr⟩
  -- the effect, at the same entry gas
  obtain ⟨post, exc, bp, bq, hpe, hraw, hckp, hW''⟩ := exchange_live
    (G := R + exExactCost sevm pre P x0 x1 x2 B1 B2 amp v) hcode hfork hstatic hdepth hlen hcd hsel
    rfl rfl hck hstep hcoin hpc hid hkeep hWc hW'c hWb
    (fun h => ⟨StaticWordExactAt.bounded ⟨_, _, (hbal h).1⟩,
      StaticWordExactAt.bounded ⟨_, _, (hbal h).2⟩⟩)
    (MutCallExactAt.bounded ⟨_, _, hpull⟩) hW''c (MutCallExactAt.bounded ⟨_, _, hpush⟩)
    (by omega) hGm
  have hpost : post = D := by
    have := Exec.result_unique exc exD
    injection this
  subst hpost
  exact ⟨post, exc, bp, bq, hpe, hraw, hckp, hW'', hDg⟩

end Blanc.Lift.Curve3Pool
