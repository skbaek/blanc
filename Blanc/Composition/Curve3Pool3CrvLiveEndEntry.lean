import Blanc.Composition.Curve3Pool3CrvLiveConcrete
import Blanc.Composition.Curve3Pool3CrvExRoot
import Blanc.Composition.Curve3Pool3CrvTxFrame
import Blanc.Composition.Curve3Pool3CrvCapstoneFrame

/-!
# The concrete entry machine of the end-to-end liveness instances

`Curve3Pool3CrvLiveConcrete`'s entry message `cMsg` starts with an empty warm-address set, so the
identity precompile `4` the pool's copies call is cold there and `IdReady` fails.  `wMsg d` is
`cMsg d` with `4` warm (as a transaction's message has every precompile warm); its machine is
`cSevm d` unchanged (the static part of a frame does not read the warm set), its entry devm
`wPre d` differs from `cPre d` only in that set.  At `wPre d`, for any calldata `d`:

* `wPre_c3Entry`, `wPre_coins`: 3Crv and the three `Token20` coins as `cPre`'s;
* `wPre_checkpoint`: the pool's `Checkpoint` at `poolState` (`p0_checkPool`, no code read);
* `wPre_id`: the identity precompile premises `IdReady`;
* `wPre_poolCode`: the pool's code is nonempty;
* `wPre_gas`: the gas measure at the frame's `878400` is a word.

The code facts go through the state equations, so no code byte array is evaluated.
-/

namespace Blanc.Composition.Curve3Pool3CrvInstance

open Jaune Blanc Blanc.Lift Blanc.Lift.Curve3Pool Blanc.Composition.Curve3PoolCalleeLive
open Blanc.Composition.Curve3Pool3CrvJoint

/-- The concrete entry message with the identity precompile warm. -/
def wMsg (d : Bytes) : Msg :=
  { cMsg d with accessedAddresses := (Std.HashSet.emptyWithCapacity : AdrSet).insert 4 }

/-- The entry devm of the message `wMsg d`. -/
abbrev wPre (d : Bytes) : Devm := initDevm (wMsg d)

theorem wSevm_eq (d : Bytes) : initSevm (wMsg d) = cSevm d := rfl

theorem wPre_getStor (d : Bytes) (a : Adr) : (wPre d).getStor a = cState.getStor a := rfl

theorem wPre_getCode (d : Bytes) (a : Adr) : (wPre d).getCode a = cState.getCode a := rfl

theorem wPre_tok (d : Bytes) : tokOf (cSevm d) (wPre d) = c3crvAddr := cPre_tok d

theorem wPre_coin (d : Bytes) (k : Fin 3) : coinOf (cSevm d) (wPre d) k = coinAdr k := cPre_coin d k

theorem wPre_c3Entry (d : Bytes) : C3Entry (cSevm d) (wPre d) 6000 :=
  let h := c3Entry_of d
  ⟨h.code, h.supply, h.pool, h.prec⟩

theorem wPre_coins (d : Bytes) : T20Coins (cSevm d) (wPre d) :=
  let h := coins_of d
  ⟨h.code, h.prec, h.pool, h.tok, h.apart⟩

theorem cState_get_pool : cState.get poolAddr = poolAcct := by
  unfold cState
  rw [State.get_set_ne _ (by decide +kernel), State.get_set_ne _ (by decide +kernel),
    State.get_set_ne _ (by decide +kernel), p0_pool]

theorem cState_stor_pool : cState.getStor poolAddr = poolStor :=
  congrArg Acct.stor cState_get_pool

theorem cState_code_pool : cState.getCode poolAddr = Curve3Pool.code :=
  congrArg Acct.code cState_get_pool

theorem p0_get4_code : (P0.get 4).code = .empty := by decide +kernel

theorem cState_code4 : cState.getCode 4 = .empty := by
  change (cState.get 4).code = _
  unfold cState
  rw [State.get_set_ne _ (by decide +kernel), State.get_set_ne _ (by decide +kernel),
    State.get_set_ne _ (by decide +kernel)]
  exact p0_get4_code

/-- **The pool's checkpoint at the entry**: `poolState`. -/
theorem wPre_checkpoint (d : Bytes) :
    Checkpoint ((wPre d).getStor (cSevm d).currentTarget) poolState := by
  rw [wPre_getStor, cSevm_target, cState_stor_pool]
  exact checkPool_sound p0_checkPool

theorem wPre_poolCode (d : Bytes) : (wPre d).getCode (cSevm d).currentTarget ≠ .empty := by
  rw [wPre_getCode, cSevm_target, cState_code_pool]
  intro h
  have := pool_code_ne
  rw [h, ByteArray.toList_eq_toList_data] at this
  exact this rfl

theorem cSevm_time (d : Bytes) : (cSevm d).benvStat.time = 1 := rfl

theorem cSevm_caller (d : Bytes) : (cSevm d).caller = trader := rfl

theorem cSevm_value (d : Bytes) : (cSevm d).value = 0 := rfl

theorem cSevm_fork (d : Bytes) : CoveredFork (cSevm d).benvStat.fork := .bpo2

/-- **The identity precompile premises at the entry.** -/
theorem wPre_id (d : Bytes) : IdReady (cSevm d) (wPre d) := by
  refine ⟨?_, ?_, ?_, cSevm_fork d⟩
  · rw [wPre_getCode, cState_code4]
    decide +kernel
  · exact Std.HashSet.mem_insert_self
  · rw [cSevm_benv]
    decide +kernel

theorem wPre_gas (d : Bytes) (G : Nat) (hG : G + 2000 < 2 ^ 256) :
    (St (wPre d) [] Mem.empty G).gasMeasure + 2000 < 2 ^ 256 := by
  have e : (St (wPre d) [] Mem.empty G).gasMeasure =
    G + (wPre d).mach.stateGas.spilled + (wPre d).mach.stateGas.committedSpill := rfl
  rw [e]
  exact hG

end Blanc.Composition.Curve3Pool3CrvInstance
