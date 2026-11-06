import Blanc.Composition.Curve3PoolPublicPrice
import Blanc.Composition.Curve3PoolJointRoot
import Blanc.Lift.Curve3Pool.U3Ledger

/-!
# The public observers against the proofs' vocabulary

Controls for the public statements, not part of them. Each theorem compares an observer with what the
existing proofs pin, so a mis-stated observer breaks this module:

* the literal addresses are the deployment's, and `Deployment` plus the premises it moved out gives
  `JointDeployment` (`Deployment.toJoint`);
* `recorded`, `books`, `scaled` and `ampAt` read what the replay's `Checkpoint` pins;
* `Within` follows from `U3Ledger` at those observers, arm by arm, for the arms with no existential.
-/

namespace Blanc.Composition.Curve3PoolPublic

open Jaune Blanc Blanc.Lift Blanc.ExecutionTrace
open Blanc.Lift.Curve3Pool (V3 Abstracts aChk U3Ledger Env Out feeDen getDMem)

example : pool = Curve3Pool.Creation.poolAddress := rfl
example : c3 = Curve3Crv.Creation.tokenAddress := rfl
example : dai = Curve3Pool.adrOf (Curve3Pool.Creation.coinsN.get 0) := by decide +kernel
example : usdc = Curve3Pool.adrOf (Curve3Pool.Creation.coinsN.get 1) := by decide +kernel
example : usdt = Curve3Pool.adrOf (Curve3Pool.Creation.coinsN.get 2) := by decide +kernel

/-- The anchored deployment rebuilds `JointDeployment`, given the fields that moved to `Assumes` or left
the statement: U5's `toJoint`, on this module's `Deployment`. -/
noncomputable def Deployment.toJoint (d : Deployment) (facts : d.Facts) :
    Curve3PoolJointRoot.JointDeployment :=
  Curve3PoolBlockAnchor.AnchoredDeployment.toJoint facts

section Observers

variable {w : Jaune.State} {s : Curve3Pool.State}

/-- **`recorded` reads the replay's balances.** Pointing it at another slot breaks this. -/
theorem recorded_of_abstracts (h : Abstracts (w.getStor pool) s) (k : Fin 3) :
    recorded w k = s.balances.get k := h.balances k

/-- `books` is the replay's balance vector. -/
theorem books_of_abstracts (h : Abstracts (w.getStor pool) s) : books w = s.balances :=
  Curve3Pool.V3.ext_get fun k => by
    have := recorded_of_abstracts h k
    match k with
    | 0 => exact this
    | 1 => exact this
    | 2 => exact this

/-- `ampAt` is the model's `_A()`. -/
theorem ampAt_of_abstracts (h : Abstracts (w.getStor pool) s) (t : Nat) :
    ampAt w t = aChk s t := by
  have a0 : word w pool Curve3Pool.initialASlot = s.initialA := h.initialA
  have a1 : word w pool Curve3Pool.futureASlot = s.futureA := h.futureA
  have t0 : word w pool Curve3Pool.initialATimeSlot = s.initialATime := h.initialATime
  have t1 : word w pool Curve3Pool.futureATimeSlot = s.futureATime := h.futureATime
  simp only [ampAt, rampMoved, aChk, a0, a1, t0, t1, Option.bind_eq_bind, Option.bind_assoc]

/-- `invariant` is the model's `get_D_mem` of the replay's balances. -/
theorem invariant_of_abstracts (h : Abstracts (w.getStor pool) s) (amp : Nat) :
    invariant w amp = getDMem s.balances amp := by
  rw [invariant, books_of_abstracts h]

end Observers

section Decode

/-- `opOf` reads the dispatcher's `exchange`: the same words `decodeCall` gives its arguments. -/
theorem opOf_exchange {e : Sevm} (hlen : 4 ≤ e.data.length)
    (hs : Sevm.selector e = Curve3Pool.selExchange) :
    Curve3Pool.decodeCall e = .exchange (Curve3Pool.arg e 0) (Curve3Pool.arg e 1)
        (Curve3Pool.arg e 2) (Curve3Pool.arg e 3) ∧
      opOf e = .exchange (Curve3Pool.arg e 0) (Curve3Pool.arg e 1) := by
  have hn : ¬ e.data.length < 4 := by omega
  refine ⟨Curve3Pool.decodeCall_at (k := 6) (by decide +kernel) hs hlen, ?_⟩
  have h1 : Curve3Pool.selExchange ≠ Curve3Pool.selRemoveLiquidity := by decide +kernel
  have h2 : Curve3Pool.selExchange ≠ Curve3Pool.selDonateAdminFees := by decide +kernel
  have h3 : Curve3Pool.selExchange ≠ Curve3Pool.selAddLiquidity := by decide +kernel
  have h4 : Curve3Pool.selExchange ≠ Curve3Pool.selRemoveLiquidityImbalance := by decide +kernel
  simp only [opOf, hn, hs, h1, h2, h3, h4, ↓reduceIte]

end Decode

section Within

variable {w w' : Jaune.State} {s : Curve3Pool.State} {e : Env} {o : Out} {amp D D' : Nat}

/-- `remove_liquidity`'s arm of `Within` follows from its ledger arm. -/
theorem within_removeLiquidity {a : Nat} {mins : V3}
    (l : U3Ledger s e (.removeLiquidity a mins) o (supply w) (supply w'))
    (hs : Abstracts (w.getStor pool) s) (hT : 0 < supply w)
    (hD : invariant w amp = some D) (hD' : getDMem o.state.balances amp = some D') :
    Within w w' .removeLiquidity amp D D' := by
  rw [invariant_of_abstracts hs] at hD
  have := (l.1 a mins rfl amp D D' hT hD hD').2
  simpa only [Within, overshoot, scaled, books_of_abstracts hs] using this

/-- `exchange`'s arm of `Within` follows from its ledger arm: `T' = T` moves into the inequality. -/
theorem within_exchange {i j dx md : Nat} (hi : i < 3) (hj : j < 3)
    (l : U3Ledger s e (.exchange i j dx md) o (supply w) (supply w'))
    (hs : Abstracts (w.getStor pool) s) (hs' : Abstracts (w'.getStor pool) o.state)
    (hA : aChk s e.time = some amp) (hadm : s.adminFee ≤ feeDen)
    (hD : invariant w amp = some D) (hD' : invariant w' amp = some D') :
    Within w w' (.exchange i j) amp D D' := by
  rw [invariant_of_abstracts hs] at hD
  rw [invariant_of_abstracts hs'] at hD'
  obtain ⟨i', j', ei, ej, rest⟩ := l.2.2.2.2.1 i j dx md rfl
  obtain ⟨-, hTT, hle⟩ := rest amp D D' hA hadm hD hD'
  have ei' : i' = Fin.ofNat 3 i := by
    simp only [Curve3Pool.idx, hi, ↓reduceDIte, Option.some.injEq] at ei
    subst ei
    exact Fin.ext (Nat.mod_eq_of_lt hi).symm
  have ej' : j' = Fin.ofNat 3 j := by
    simp only [Curve3Pool.idx, hj, ↓reduceDIte, Option.some.injEq] at ej
    subst ej
    exact Fin.ext (Nat.mod_eq_of_lt hj).symm
  subst ei' ej'
  simp only [Within, allowance, scaled, books_of_abstracts hs, books_of_abstracts hs', hTT]
  rw [Nat.mul_comm D]
  exact Nat.mul_comm (supply w) _ ▸ Nat.mul_le_mul_left _ hle

/-- `remove_liquidity_one_coin`'s arm of `Within` follows from its ledger arm. -/
theorem within_oneCoin {a i mn : Nat} (hi : i < 3)
    (l : U3Ledger s e (.removeLiquidityOneCoin a i mn) o (supply w) (supply w'))
    (hs : Abstracts (w.getStor pool) s) (hs' : Abstracts (w'.getStor pool) o.state)
    (hA : aChk s e.time = some amp) (hadm : s.adminFee ≤ feeDen)
    (hD : invariant w amp = some D) (hD' : invariant w' amp = some D') :
    Within w w' (.oneCoin a i) amp D D' := by
  rw [invariant_of_abstracts hs] at hD
  rw [invariant_of_abstracts hs'] at hD'
  obtain ⟨i', ei, rest⟩ := l.2.2.2.2.2 a i mn rfl
  obtain ⟨-, hle⟩ := rest amp D D' hA hadm hD hD'
  have ei' : i' = Fin.ofNat 3 i := by
    simp only [Curve3Pool.idx, hi, ↓reduceDIte, Option.some.injEq] at ei
    subst ei
    exact Fin.ext (Nat.mod_eq_of_lt hi).symm
  subst ei'
  simpa only [Within, allowance, scaled, books_of_abstracts hs] using hle

end Within

section Authority

/-- **`NoKeyHolder` gives `dai_entry_local`'s `PoolAuthorityEmpty`**, given what the pool sends DAI
(`ownCalls`, U4's to discharge). -/
theorem NoKeyHolder.daiAuthority {cfg : ChainConfig} {start : Benv} {future : BlockChain} {noAuthority : Prop}
    (trace : MidHistoryTraceIn HistFork cfg start future)
    (keys : NoKeyHolder start.state trace.settledFrames noAuthority)
    (installed : start.state.getCode dai = Lift.Dai.code)
    (own : ∀ F ∈ coinFrames dai (fun _ => True) trace.settledFrames, F.sevm.caller = pool →
      CurveCoins.PoolCoinSel (Sevm.selector F.sevm)) :
    PoolAuthorityEmpty CurveCoins.Dai.SignedAs Dai.allowSlot CurveCoins.PoolCoinSel pool
      (wordsAt dai start.state) (coinFrames dai (fun _ => True) trace.settledFrames) where
  rowsAtCut := keys.rowsAtCut 0
  noSignature := CurveCoins.Dai.dai_noSignature_of_logs trace installed keys.daiNoApproval
  ownCalls := own

/-- **`NoKeyHolder` gives `usdt_entry_local`'s `PoolAuthorityEmpty`**: USDT has no signed writer. -/
theorem NoKeyHolder.usdtAuthority {settled : List Exec.Frame} {w : Jaune.State} {noAuthority : Prop}
    (keys : NoKeyHolder w settled noAuthority)
    (own : ∀ F ∈ coinFrames usdt (fun _ => True) settled, F.sevm.caller = pool →
      CurveCoins.PoolCoinSel (Sevm.selector F.sevm)) :
    PoolAuthorityEmpty CurveCoins.Usdt.NoSigned Usdt.allowSlot CurveCoins.PoolCoinSel pool
      (wordsAt usdt w) (coinFrames usdt (fun _ => True) settled) where
  rowsAtCut := keys.rowsAtCut 2
  noSignature := fun _ _ h => h
  ownCalls := own

end Authority

end Blanc.Composition.Curve3PoolPublic
