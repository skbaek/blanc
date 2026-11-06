import Blanc.Composition.Curve3PoolPublicPrice
import Blanc.Composition.Curve3PoolJointRoot
import Blanc.Lift.Curve3Pool.U3Ledger

/-!
# The public observers against the proofs' vocabulary

Controls for the public statements, not part of them. Each theorem compares an observer with what the
existing proofs pin, so a mis-stated observer breaks this module:

* the literal addresses are the deployment's, and `Deployment` plus the premises it moved out rebuilds
  `JointDeployment` field for field (`Deployment.toJoint`);
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

/-- The record rebuilds `JointDeployment`, given the fields that moved to `Assumes` or left the
statement. So `Deployment` drops nothing else. -/
noncomputable def Deployment.toJoint (d : Deployment)
    (fresh : Curve3Crv.FreshKeys (fun _ => False)
      (Curve3Crv.midTouchedKeysIn Curve3PoolPublic.c3
        (d.c3.rest.append (((d.toPool.step d.pool.trace).append d.toMinter).step d.minter.trace))))
    (callbacks : (((MidHistoryTraceIn.tail d.pool.trace d.pool.cut).append d.toMinter).step
      d.minter.trace).FrameAdmitted Curve3PoolPublic.pool (Exec.derivEntry fun D =>
        Curve3Pool.PoolCallsKeep D ∧ Curve3Pool.PoolCoinCallsKeepToken D))
    (idEmpty : d.c3.post.state.getCode 4 = ByteArray.empty)
    (idNoFrame : ∀ root ∈ (((d.toPool.step d.pool.trace).append d.toMinter).step d.minter.trace).rawFrames,
      root.sevm.codeAddress = none → root.sevm.currentTarget ≠ 4) :
    Curve3PoolJointRoot.JointDeployment where
  c3Pre := d.c3.pre
  c3Completed := d.c3.post
  c3Block := d.c3.trace
  c3Number := d.c3.recorded.number
  c3Time := d.c3.recorded.time
  c3Entry := d.c3.recorded.entry
  c3Slot := d.c3.recorded.slot
  c3Decoded := d.c3.recorded.decoded
  c3Receipt := d.c3.recorded.receipt
  c3Lookup := d.c3.recorded.lookup
  c3Succeeded := d.c3.recorded.succeeded
  poolPre := d.pool.pre
  toPool := d.toPool
  poolCompleted := d.pool.post
  poolBlock := d.pool.trace
  poolNumber := d.pool.recorded.number
  poolTime := d.pool.recorded.time
  poolEntry := d.pool.recorded.entry
  poolSlot := d.pool.recorded.slot
  poolDecoded := d.pool.recorded.decoded
  poolReceipt := d.pool.recorded.receipt
  poolLookup := d.pool.recorded.lookup
  poolSucceeded := d.pool.recorded.succeeded
  minterPre := d.minter.pre
  toMinter := d.toMinter
  minterCompleted := d.minter.post
  minterBlock := d.minter.trace
  minterNumber := d.minter.recorded.number
  minterTime := d.minter.recorded.time
  minterEntry := d.minter.recorded.entry
  minterSlot := d.minter.recorded.slot
  minterDecoded := d.minter.recorded.decoded
  minterReceipt := d.minter.recorded.receipt
  minterLookup := d.minter.recorded.lookup
  minterSucceeded := d.minter.recorded.succeeded
  fresh := fresh
  callbacks := callbacks
  idEmpty := idEmpty
  idNoFrame := idNoFrame

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

section Within

variable {w w' : Jaune.State} {s : Curve3Pool.State} {e : Env} {o : Out} {amp D D' : Nat}

/-- `remove_liquidity`'s arm of `Within` follows from its ledger arm. -/
theorem within_removeLiquidity {a : Nat} {mins : V3}
    (l : U3Ledger s e (.removeLiquidity a mins) o (supply w) (supply w'))
    (hs : Abstracts (w.getStor pool) s) (hT : 0 < supply w)
    (hD : invariant w amp = some D) (hD' : getDMem o.state.balances amp = some D') :
    Within w w' (.removeLiquidity a mins) amp D D' := by
  rw [invariant_of_abstracts hs] at hD
  have := (l.1 a mins rfl amp D D' hT hD hD').2
  simpa only [Within, overshoot, scaled, books_of_abstracts hs] using this

/-- `exchange`'s arm of `Within` follows from its ledger arm: `T' = T` moves into the inequality. -/
theorem within_exchange {i j dx md : Nat} (hi : i < 3) (hj : j < 3)
    (l : U3Ledger s e (.exchange i j dx md) o (supply w) (supply w'))
    (hs : Abstracts (w.getStor pool) s) (hs' : Abstracts (w'.getStor pool) o.state)
    (hA : aChk s e.time = some amp) (hadm : s.adminFee ≤ feeDen)
    (hD : invariant w amp = some D) (hD' : invariant w' amp = some D') :
    Within w w' (.exchange i j dx md) amp D D' := by
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
    Within w w' (.removeLiquidityOneCoin a i mn) amp D D' := by
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

end Blanc.Composition.Curve3PoolPublic
