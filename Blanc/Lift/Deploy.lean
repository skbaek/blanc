import Blanc.Lift.Exact
import Blanc.Lift.SolcStorageReturn
import Blanc.Lift.InvWalkWorld
import Blanc.Lift.ExactWalkCutOps
import Blanc.Lift.WalkSteps
import Blanc.DeploymentMessage
import Blanc.DeploymentTouch

/-!
# Deploying lifted creation code

The bridge from a gas-exact synthetic run of a lifted constructor (`SProg.RunExact` of a
checked certificate of the creation input, `Blanc/Lift/Exact.lean`) to Jaune's CREATE
settlement `processCreateMessage`: the run is a real Jaune execution (`lift_exact`), it
settles as the inner message's result (`processMessage_ok_of_exec`), the returned output is
charged as code (`processCreateMessage.chargeCodeGas`, legacy schedule) and installed at the
new address (`processCreateMessage_ok_of_processMessage_and_charge`).

The walk steps a constructor needs beyond the shared kits (`SSTORE` and `CALLVALUE` in cut
runs, `RETURN` with its halting state named over a variable state, `returnPost`) are here too.

`liftCreate_ok` is contract-neutral: a contract supplies its checked creation certificate and a
run from the creation frame's start state, and receives the settled post-state with the
constructor's output installed as the new account's code and the exact normalized account storage.
-/

namespace Blanc.Lift

open Jaune

/-! ## Constructor walk steps

`SSTORE`, `CALLVALUE` and `RETURN` in cut runs, and `RETURN` of an arbitrary state in exact runs,
with the halting state named over a variable state (`returnPost`) so that nothing reduces a
concrete memory image. -/

section Steps

variable {fs : List SFunc} {sevm : Sevm} {C : List Nat} {b : Devm} {f : SFunc} {r : Seg}
  {S : List B256} {M : Mem} {G : Nat}

/-- `SSTORE` at its selected cost, in a cut run. -/
theorem rxc_sstore {k' v : B256} (hfork : CoveredFork sevm.benvStat.fork)
    (hsentry : gCallStipend < G + sstoreCost sevm b k' v) (hstatic : sevm.isStatic = false)
    (k : SFunc.RunExactCut fs sevm C (St (afterSstore sevm b k' v) S M G) f r) :
    SFunc.RunExactCut fs sevm C (St b (k' :: v :: S) M (G + sstoreCost sevm b k' v))
      (.next (.reg .sstore) f) r := by
  refine .next (Ninst.runCompiled_sstore_selected_setMach hfork hsentry hstatic) ?_
  rw [← afterSstore_stateGas (sevm := sevm) (devm := b) (key := k') (value := v)]
  exact k

/-- `CALLVALUE`, in a cut run. -/
theorem rxc_callvalue (hroom : S.length < 1024)
    (k : SFunc.RunExactCut fs sevm C (St b (sevm.value :: S) M G) f r) :
    SFunc.RunExactCut fs sevm C (St b S M (G + 2)) (.next (.reg .callvalue) f) r :=
  .next (Ninst.runCompiled_pushItem (devm := St b S M (G + 2)) (G := G) (cost := gBase)
    (by rintro ⟨⟩) rfl rfl hroom) k

/-- `St` keeps the world's error and storage. -/
theorem St_error (b : Devm) (S : List B256) (M : Mem) (G : Nat) : (St b S M G).error = b.error :=
  rfl

theorem St_getStor (b : Devm) (S : List B256) (M : Mem) (G : Nat) (a : Adr) :
    Devm.getStor (St b S M G) a = Devm.getStor b a := rfl

/-- A synthetic machine replacement preserves the persistent world state. -/
theorem St_state (b : Devm) (S : List B256) (M : Mem) (G : Nat) :
    (St b S M G).state = b.state := rfl

/-- The state `RETURN` leaves (stated over a variable state, so nothing reduces a concrete
memory image). -/
def returnPost (d : Devm) (i sz : B256) (S : List B256) : Devm :=
  ((d.setMach ⟨S, d.memory, d.gasLeft, d.stateGas⟩).memRead i.toNat sz.toNat).2.withOutput
    (d.memory.read i.toNat sz.toNat).1

/-- Project through the RETURN post before substituting its concrete memory. -/
theorem returnPost_state (d : Devm) (i sz : B256) (S : List B256) :
    (returnPost d i sz S).state = d.state :=
  congrArg World.state (Devm.returnPost_world d S d.gasLeft i.toNat sz.toNat
    (d.memory.read i.toNat sz.toNat).1)

theorem returnPost_facts (d : Devm) (i sz : B256) (S : List B256) :
    (returnPost d i sz S).output = (d.memory.read i.toNat sz.toNat).1 ∧
      (returnPost d i sz S).error = d.error ∧
      (∀ a, Devm.getStor (returnPost d i sz S) a = Devm.getStor d a) ∧
      (returnPost d i sz S).gasLeft = d.gasLeft :=
  ⟨rfl, rfl, fun _ => rfl, rfl⟩

/-- `RETURN` of a window that needs no expansion, in a cut run. -/
theorem rxc_return_any {fs : List SFunc} {sevm : Sevm} {C : List Nat} {d : Devm} {i sz : B256}
    {S : List B256} (hstk : d.stack = i :: sz :: S) (hext : d.extCost [⟨i.toNat, sz.toNat⟩] = 0) :
    SFunc.RunExactCut fs sevm C d (.last .return_) (.done (.halted (returnPost d i sz S))) := by
  refine .last ?_
  show Linst.run sevm _ .return_ = _
  exact Linst.run_return_eq_ok hstk (by rw [hext]; exact Nat.zero_le _)
    (by rw [hext, Nat.sub_zero]; rfl)

/-- `RETURN` of a window that needs no expansion, in an exact run. -/
theorem rx_return_any {fs : List SFunc} {sevm : Sevm} {d : Devm} {i sz : B256}
    {S : List B256} (hstk : d.stack = i :: sz :: S) (hext : d.extCost [⟨i.toNat, sz.toNat⟩] = 0) :
    SFunc.RunExact fs sevm d (.last .return_) (.halted (returnPost d i sz S)) := by
  refine .last ?_
  show Linst.run sevm _ .return_ = _
  exact Linst.run_return_eq_ok hstk (by rw [hext]; exact Nat.zero_le _)
    (by rw [hext, Nat.sub_zero]; rfl)

/-- `CODECOPY`, with the whole charge named, in an exact run. -/
theorem rx_codecopy {o : Outcome} {di si sz : B256} {c : Nat} {M' : Mem}
    (hc : gVerylow + gasCopy * ceilDiv sz.toNat 32 +
      (St b (di :: si :: sz :: S) M (G + c)).extCost [⟨di.toNat, sz.toNat⟩] = c)
    (hw : M.write di.toNat (sevm.code.sliceD si.toNat sz.toNat (Linst.toUInt8 .stop)) = M')
    (k : SFunc.RunExact fs sevm (St b S M' G) f o) :
    SFunc.RunExact fs sevm (St b (di :: si :: sz :: S) M (G + c)) (.next (.reg .codecopy) f) o :=
  .next (Ninst.runCompiled_codecopy_of (devm := St b (di :: si :: sz :: S) M (G + c)) rfl hc hw
    rfl) k

end Steps

/-- Solidity's terminal constructor window: load a length, duplicate it for
RETURN, copy executing code to memory zero, then return that same window. -/
def solcRuntimeReturn (sizeBytes offsetBytes : Bytes)
    (sizeBound : sizeBytes.length ≤ 32) (offsetBound : offsetBytes.length ≤ 32) : SFunc :=
  .dest (.next (.push sizeBytes sizeBound) (.next (.reg (.dup 0))
    (.next (.push offsetBytes offsetBound) (.next (.push [0x00] (by decide))
      (.next (.reg .codecopy) (.next (.push [0x00] (by decide)) (.last .return_)))))))

/-- Construct the terminal copy/return walk over symbolic memory. The charge
includes CODECOPY's word charge and the exact expansion; RETURN adds none. -/
theorem solcRuntimeReturn_runExact
    {fs : List SFunc} {sevm : Sevm} {b : Devm} {S : List B256} {M : Mem} {G : Nat}
    {sizeHead offsetHead : UInt8} {sizeTail offsetTail : Bytes}
    {sizeBound : (sizeHead :: sizeTail).length ≤ 32}
    {offsetBound : (offsetHead :: offsetTail).length ≤ 32} {size offset : B256}
    (sizeWord : Bytes.toB256 (sizeHead :: sizeTail) = size)
    (offsetWord : Bytes.toB256 (offsetHead :: offsetTail) = offset)
    (nonzero : size.toNat ≠ 0)
    (aligned : M.size % 32 = 0) (room : S.length + 4 ≤ 1024) :
    SFunc.RunExact fs sevm
      (St b S M (G + (calculateMemoryGasCost (memExtSize M.size 0 size.toNat) -
        calculateMemoryGasCost M.size) + gasCopy * ceilDiv size.toNat 32 + 19))
      (solcRuntimeReturn (sizeHead :: sizeTail) (offsetHead :: offsetTail)
        sizeBound offsetBound)
      (.halted ((St b S
        (M.write 0 (sevm.code.sliceD offset.toNat size.toNat (Linst.toUInt8 .stop))) G).withOutput (sevm.code.sliceD offset.toNat size.toNat (Linst.toUInt8 .stop)))) := by
  let window := sevm.code.sliceD offset.toNat size.toNat (Linst.toUInt8 .stop)
  let copied := M.write 0 window
  have length : window.length = size.toNat := ByteArray.length_sliceD _ _ _ _
  have nonempty : window ≠ [] := by
    intro empty
    apply nonzero
    rw [empty] at length
    exact length.symm
  have memorySize : copied.size = memExtSize M.size 0 size.toNat :=
    Mem.size_write_of_size rfl aligned length
  have memoryAligned : copied.size % 32 = 0 := by
    rw [memorySize]
    exact memExtSize_mod_32 aligned
  have fits : 0 + size.toNat ≤ copied.size := by
    have bound := Mem.write_end_le_size M 0 nonempty
    simpa only [length] using bound
  have read : (copied.read 0 size.toNat).1 = window := by
    change ((M.write 0 window).read 0 size.toNat).1 = window
    rw [← length]
    exact Mem.read_write_zero M nonempty
  have memory : (copied.read 0 size.toNat).2 = copied :=
    Mem.read_snd_eq_self (memExtSize_of_le memoryAligned fits)
  have post : returnPost (St b (0 :: size :: S) copied G) 0 size S =
      (St b S copied G).withOutput window := by
    change ((St b S copied G).withMemory (copied.read 0 size.toNat).2).withOutput
      (copied.read 0 size.toNat).1 = _
    rw [memory, read]
    rfl
  change SFunc.RunExact fs sevm _ _ (.halted ((St b S copied G).withOutput window))
  rw [← post]
  unfold solcRuntimeReturn
  apply rx_dest
  apply rx_push sizeWord (by omega)
  apply rx_dup (n := 0) rfl (by simp only [List.length_cons]; omega)
  apply rx_push offsetWord (by simp only [List.length_cons]; omega)
  apply rx_push (w := 0) (by decide) (by simp only [List.length_cons]; omega)
  rw [show G + (calculateMemoryGasCost (memExtSize M.size 0 size.toNat) -
      calculateMemoryGasCost M.size) + gasCopy * ceilDiv size.toNat 32 + 6 =
      (G + 3) + ((calculateMemoryGasCost (memExtSize M.size 0 size.toNat) -
        calculateMemoryGasCost M.size) + gasCopy * ceilDiv size.toNat 32 + 3) by omega]
  refine rx_codecopy (G := G + 3)
    (c := (calculateMemoryGasCost (memExtSize M.size 0 size.toNat) -
      calculateMemoryGasCost M.size) + gasCopy * ceilDiv size.toNat 32 + 3)
    (M' := copied) ?_ ?_ ?_
  · rw [St.extCost_eq rfl]
    change 3 + gasCopy * ceilDiv size.toNat 32 +
      (calculateMemoryGasCost (memExtSize M.size 0 size.toNat) -
        calculateMemoryGasCost M.size) = _
    omega
  · rfl
  · apply rx_push (w := 0) (by decide) (by simp only [List.length_cons]; omega)
    exact rx_return_any rfl (Devm.extCost_zero_of_le memoryAligned fits)

/-- Invert a successful terminal copy/return walk. No fork or initial-memory
alignment premise is needed: the actual returned window and storage follow
from the successful source instructions. -/
theorem solcRuntimeReturn_effects
    {fs : List SFunc} {sevm : Sevm} {b post : Devm} {S : List B256} {M : Mem} {G : Nat}
    {sizeBytes offsetBytes : Bytes} {sizeBound : sizeBytes.length ≤ 32}
    {offsetBound : offsetBytes.length ≤ 32} {size offset : B256}
    (sizeWord : sizeBytes.toB256 = size) (offsetWord : offsetBytes.toB256 = offset)
    (nonzero : size.toNat ≠ 0)
    (run : SFunc.Run fs sevm (St b S M G)
      (solcRuntimeReturn sizeBytes offsetBytes sizeBound offsetBound) (.halted post)) :
    post.getStor = b.getStor ∧
      post.output = sevm.code.sliceD offset.toNat size.toNat (Linst.toUInt8 .stop) := by
  obtain ⟨copied, copiedEq⟩ : ∃ copied : Mem,
      M.write 0 (sevm.code.sliceD offset.toNat size.toNat (Linst.toUInt8 .stop)) = copied :=
    ⟨_, rfl⟩
  have length : (sevm.code.sliceD offset.toNat size.toNat (Linst.toUInt8 .stop)).length =
      size.toNat := ByteArray.length_sliceD _ _ _ _
  have nonempty : sevm.code.sliceD offset.toNat size.toNat (Linst.toUInt8 .stop) ≠ [] := by
    intro empty
    apply nonzero
    rw [empty] at length
    exact length.symm
  have read : (copied.read 0 size.toNat).1 =
      sevm.code.sliceD offset.toNat size.toNat (Linst.toUInt8 .stop) := by
    have read := Mem.read_write_zero M nonempty
    rw [length, copiedEq] at read
    exact read
  have run := run.cut
  unfold solcRuntimeReturn at run
  obtain ⟨_, run⟩ := ric_dest run
  obtain ⟨_, step, run⟩ := ric_next run
  obtain ⟨_, equal⟩ := ri_push step
  rw [sizeWord] at equal
  subst equal
  obtain ⟨_, step, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_dup (n := 0) rfl step
  obtain ⟨_, step, run⟩ := ric_next run
  obtain ⟨_, equal⟩ := ri_push step
  rw [offsetWord] at equal
  subst equal
  obtain ⟨_, step, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_push step
  obtain ⟨_, step, run⟩ := ric_next run
  obtain ⟨_, equal⟩ := ri_codecopy step
  change _ = St b (size :: S)
    (M.write 0 (sevm.code.sliceD offset.toNat size.toNat (Linst.toUInt8 .stop))) _ at equal
  rw [copiedEq] at equal
  subst equal
  obtain ⟨_, step, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_push step
  cases run with
  | last terminal =>
      have effect := ri_return terminal
      exact ⟨funext effect.2.1, effect.1.trans read⟩

/-- The packed flag word retained by this Solidity constructor prologue. -/
def solcConstructorFlagWord (raw : B256) : B256 :=
  (~~~ ((255 : B256) <<< 160)) &&& raw

/-- The reverting arm of the nonpayable constructor check. -/
def solcConstructorRevert : SFunc :=
  .next (.push [0x00] (by decide)) (.next (.reg (.dup 0)) (.last .revert))

/-- Solidity prologue clearing a packed flag in slot one and resetting slot eleven. -/
def solcConstructorPrelude (success : SFunc) : SFunc := (.next (.push [0x80] (by decide)) (.next (.push [0x40] (by decide)) (.next (.reg .mstore) (.next (.push [0x01] (by decide)) (.next (.reg (.dup 0)) (.next (.reg .sload) (.next (.push [0xff] (by decide)) (.next (.push [0xa0] (by decide)) (.next (.reg .shl) (.next (.reg .not) (.next (.reg .and) (.next (.reg (.swap 0)) (.next (.reg .sstore) (.next (.push [0x00] (by decide)) (.next (.push [0x0b] (by decide)) (.next (.reg .sstore) (.next (.reg .callvalue) (.next (.reg (.dup 0)) (.next (.reg .iszero) (.next (.push [0x00, 0x00, 0x23] (by decide)) (.branch solcConstructorRevert success)))))))))))))))))))))

/-- Invert the storage/memory prologue and successful nonpayable guard. The
continuation is left explicit so the source pattern can be composed with an
actual internal owner call and terminal code return. -/
theorem solcConstructorPrelude_effects
    {fs : List SFunc} {sevm : Sevm} {b post : Devm} {S : List B256}
    {M : Mem} {G : Nat} {success : SFunc}
    (run : SFunc.Run fs sevm (St b S M G) (solcConstructorPrelude success) (.halted post)) :
    sevm.value = 0 ∧ ∃ after G',
      after.getStor sevm.currentTarget =
        ((b.getStor sevm.currentTarget).set 1
          (solcConstructorFlagWord (b.getStorVal sevm.currentTarget 1))).set 11 0 ∧
      (∀ a, a ≠ sevm.currentTarget → after.getStor a = b.getStor a) ∧
      SFunc.Run fs sevm (St after (0 :: S) (M.write 64 (128 : B256).toBytes) G')
        success (.halted post) := by
  let memory := M.write 64 (128 : B256).toBytes
  have run := run.cut
  unfold solcConstructorPrelude at run
  obtain ⟨_, step, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_push step
  obtain ⟨_, step, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_push step
  obtain ⟨_, step, run⟩ := ric_next run
  obtain ⟨_, eq⟩ := ri_mstore step
  change _ = St b S memory _ at eq
  subst eq
  obtain ⟨_, step, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_push step
  obtain ⟨_, step, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_dup (n := 0) rfl step
  obtain ⟨loaded, load, run⟩ := ric_next run
  have storage : loaded.getStor = b.getStor := (Ninst.Hinv.inv (f := Devm.getStor) load).symm
  have loadMemory : loaded.memory = memory := SolcStorageReturn.sload_memory load
  obtain ⟨key, tail, popped, pushed⟩ := of_run_sload load
  simp only [Stack.Pop, Stack.Push, Split, St.stack, List.cons_append, List.nil_append,
    List.cons.injEq] at popped pushed
  obtain ⟨rfl, rfl⟩ := popped
  rw [St.self pushed loadMemory] at run
  obtain ⟨_, step, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_push step
  obtain ⟨_, step, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_push step
  obtain ⟨_, step, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_shl step
  obtain ⟨_, step, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_not step
  obtain ⟨_, step, run⟩ := ric_next run
  obtain ⟨_, eq⟩ := ri_and step
  change _ = St loaded (solcConstructorFlagWord (b.getStorVal sevm.currentTarget 1) ::
    1 :: S) memory _ at eq
  subst eq
  obtain ⟨_, step, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_swap (n := 0) rfl step
  obtain ⟨cleared, clear, run⟩ := ric_next run
  have clearOwn := sstore_getStor_set (xs := []) clear (by exact ⟨_, rfl⟩)
  have clearForeign : ∀ a, a ≠ sevm.currentTarget → cleared.getStor a = b.getStor a := by
    intro a different
    obtain ⟨pc, regular⟩ := of_run_reg clear
    exact (sstore_preserves_getStor_ne regular different.symm).trans (congrFun storage a)
  obtain ⟨b1, G1, eq⟩ := SolcStorageReturn.ri_sstore_any clear
  rw [eq] at run clearOwn clearForeign
  obtain ⟨_, step, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_push step
  obtain ⟨_, step, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_push step
  obtain ⟨reset, resetStore, run⟩ := ric_next run
  have resetOwn := sstore_getStor_set (xs := []) resetStore (by exact ⟨_, rfl⟩)
  have resetForeign : ∀ a, a ≠ sevm.currentTarget → reset.getStor a = b.getStor a := by
    intro a different
    obtain ⟨pc, regular⟩ := of_run_reg resetStore
    exact (sstore_preserves_getStor_ne regular different.symm).trans (clearForeign a different)
  obtain ⟨b2, G2, eq⟩ := SolcStorageReturn.ri_sstore_any resetStore
  rw [eq] at run resetOwn resetForeign
  obtain ⟨_, step, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_callvalue step
  obtain ⟨_, step, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_dup (n := 0) rfl step
  obtain ⟨_, step, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_iszero step
  obtain ⟨_, step, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_push step
  rcases ric_branch run with ⟨_, _, failed⟩ | ⟨nonzero, G3, run⟩
  · exact (SFunc.RunCutP.false_of_noOk failed (by decide)).elim
  · have zero : sevm.value = 0 := by
      by_contra different
      simp only [B256.eqCheck, different, ↓reduceIte] at nonzero
      exact nonzero rfl
    refine ⟨zero, b2, G3, ?_, resetForeign, ?_⟩
    · change b2.getStor sevm.currentTarget = (b1.getStor sevm.currentTarget).set 11 0 at resetOwn
      change b1.getStor sevm.currentTarget = _ at clearOwn
      rw [resetOwn, clearOwn]
      exact congrArg (fun s => (s.set 1
        (solcConstructorFlagWord (b.getStorVal sevm.currentTarget 1))).set 11 0)
        (congrFun storage sevm.currentTarget)
    · rw [zero] at run
      exact run.uncut

/-- Continuation after the owner initializer returns. -/
def solcConstructorExit : SFunc :=
  .dest (.next (.push [0x00, 0x00, 0x57] (by decide)) (.jump 2))

/-- The nonpayable arm calls the owner initializer with the actual caller. -/
def solcConstructorOwnerCall : SFunc :=
  .dest (.next (.reg .pop) (.next (.push [0x00, 0x00, 0x2f] (by decide))
    (.next (.reg .caller) (.next (.push [0x00, 0x00, 0x35] (by decide))
      (.callNext 1 solcConstructorExit)))))

/-- The complete constructor entry pattern, with owner and return entries
supplied by its function table. -/
def solcOwnerConstructor : SFunc := solcConstructorPrelude solcConstructorOwnerCall

/-- Exact storage resulting from the constructor's three writes. -/
def solcOwnerConstructorStorage (initial : Stor) (owner : Adr) : Stor :=
  (((initial.set 1 (solcConstructorFlagWord (initial.get 1))).set 11 0).set 0
    (addressSlotWriteWord (initial.get 0) owner.toB256))

/-- Invert the complete source constructor. All storage effects and the actual
returned code window follow from its successful run, including the internal
owner call. No gas schedule, initial-memory alignment or prepared output is
assumed. A concrete certificate and its runtime-window identity remain separate. -/
theorem solcOwnerConstructor_effects
    {fs : List SFunc} {sevm : Sevm} {b post : Devm} {S : List B256}
    {M : Mem} {G : Nat} {sizeBytes offsetBytes : Bytes}
    {sizeBound : sizeBytes.length ≤ 32} {offsetBound : offsetBytes.length ≤ 32}
    {size offset : B256}
    (ownerEntry : fs[1]? = some SolcStorageReturn.ownerInit)
    (returnEntry : fs[2]? = some (solcRuntimeReturn sizeBytes offsetBytes sizeBound offsetBound))
    (sizeWord : sizeBytes.toB256 = size) (offsetWord : offsetBytes.toB256 = offset)
    (nonzero : size.toNat ≠ 0)
    (run : SFunc.Run fs sevm (St b S M G) solcOwnerConstructor (.halted post)) :
    sevm.value = 0 ∧
      post.getStor sevm.currentTarget =
        solcOwnerConstructorStorage (b.getStor sevm.currentTarget) sevm.caller ∧
      (∀ a, a ≠ sevm.currentTarget → post.getStor a = b.getStor a) ∧
      post.output = sevm.code.sliceD offset.toNat size.toNat (Linst.toUInt8 .stop) := by
  obtain ⟨zero, after, G1, own, foreign, run⟩ := solcConstructorPrelude_effects run
  have run := run.cut
  unfold solcConstructorOwnerCall at run
  obtain ⟨_, run⟩ := ric_dest run
  obtain ⟨_, step, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_pop step
  obtain ⟨_, step, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_push step
  obtain ⟨_, step, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_caller step
  obtain ⟨_, step, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_push step
  obtain ⟨G2, called⟩ := ric_call ownerEntry run
  rcases called with ⟨D, callee, cont⟩ | ⟨D, callee, _⟩
  · have effects := SolcStorageReturn.ownerInit_effects callee
    have slotZero : after.getStorVal sevm.currentTarget 0 = b.getStorVal sevm.currentTarget 0 := by
      change (after.getStor sevm.currentTarget).get 0 = _
      rw [own, Stor.get_set_ne _ (by decide : (11 : B256) ≠ 0),
        Stor.get_set_ne _ (by decide : (1 : B256) ≠ 0)]
      rfl
    have ownerOwn : D.getStor sevm.currentTarget =
        solcOwnerConstructorStorage (b.getStor sevm.currentTarget) sevm.caller := by
      rw [effects.2.2.1]
      rw [slotZero, toAdr_toB256, own]
      rfl
    rw [St.self effects.1 effects.2.1] at cont
    unfold solcConstructorExit at cont
    obtain ⟨_, cont⟩ := ric_dest cont
    obtain ⟨_, step, cont⟩ := ric_next cont
    obtain ⟨_, rfl⟩ := ri_push step
    obtain ⟨_, terminal⟩ := ric_jump (by intro h; cases h) returnEntry cont
    have final := solcRuntimeReturn_effects sizeWord offsetWord nonzero terminal.uncut
    refine ⟨zero, (congrFun final.1 sevm.currentTarget).trans ownerOwn, ?_, final.2⟩
    intro a different
    exact (congrFun final.1 a).trans ((effects.2.2.2 a different).trans (foreign a different))
  · exact (SFunc.RunP.not_halted (S := []) rfl (by decide) (by decide) callee rfl).elim

/-- The actual execution and code charge of this owner constructor install
its returned code window and initialized storage. The zero-value premise and
nonempty output are consequences of the source run, not supplied effects. -/
theorem solcOwnerConstructor_message_effects
    {fs : List SFunc} {msg : Msg} {benv : Benv} {raw charged : Devm}
    {sizeBytes offsetBytes : Bytes}
    {sizeBound : sizeBytes.length ≤ 32} {offsetBound : offsetBytes.length ≤ 32}
    {size offset : B256}
    (ownerEntry : fs[1]? = some SolcStorageReturn.ownerInit)
    (returnEntry : fs[2]? = some (solcRuntimeReturn sizeBytes offsetBytes sizeBound offsetBound))
    (sizeWord : sizeBytes.toB256 = size) (offsetWord : offsetBytes.toB256 = offset)
    (nonzero : size.toNat ≠ 0)
    (transfer : (processCreateMessage.msg msg).benvAfterTransfer = .ok benv)
    (codeAddress : msg.codeAddress = none)
    (executed : exec (initEvm ((processCreateMessage.msg msg).withBenv benv)) = .ok raw)
    (clean : raw.error = none)
    (charge : processCreateMessage.chargeCodeGas msg.benv.stat.rules
      (raw.recordTouch msg.benv.stat.rules true msg.currentTarget) = .ok charged)
    (run : SFunc.Run fs
      (initEvm ((processCreateMessage.msg msg).withBenv benv)).sta
      (initEvm ((processCreateMessage.msg msg).withBenv benv)).dyna
      solcOwnerConstructor (.halted raw)) :
    msg.value = 0 ∧ ∃ installed, processCreateMessage msg = .ok installed ∧
      (installed.getCode msg.currentTarget).toList =
        msg.code.sliceD offset.toNat size.toNat (Linst.toUInt8 .stop) ∧
      installed.getStor msg.currentTarget = solcOwnerConstructorStorage Stor.empty msg.caller ∧
      (∀ a, a ≠ msg.currentTarget → installed.getStor a = benv.state.getStor a) := by
  have source : SFunc.Run fs
      (initEvm ((processCreateMessage.msg msg).withBenv benv)).sta
      (St (initEvm ((processCreateMessage.msg msg).withBenv benv)).dyna [] Mem.empty
        (initEvm ((processCreateMessage.msg msg).withBenv benv)).dyna.gasLeft)
      solcOwnerConstructor (.halted raw) := run
  have effects := solcOwnerConstructor_effects ownerEntry returnEntry
    sizeWord offsetWord nonzero source
  have zero : msg.value = 0 := effects.1
  have initial : benv.state.getStor msg.currentTarget = Stor.empty := by
    rw [benvAfterTransfer_ok_getStor transfer msg.currentTarget (Or.inl zero)]
    exact processCreateMessage_msg_getStor_currentTarget msg
  have outputNonempty : raw.output ≠ [] := by
    intro empty
    have length := congrArg List.length empty
    rw [effects.2.2.2, ByteArray.length_sliceD, List.length_nil] at length
    exact nonzero length
  obtain ⟨installed, settled, code, storage⟩ :=
    processCreateMessage_effects_of_exec_and_charge msg transfer codeAddress
      executed clean charge outputNonempty
  refine ⟨zero, installed, settled, ?_, ?_, ?_⟩
  · rw [code, ByteArray.toList_eq_toList_data]
    exact effects.2.2.2
  · rw [storage]
    have own : raw.getStor msg.currentTarget =
        solcOwnerConstructorStorage (benv.state.getStor msg.currentTarget) msg.caller :=
      effects.2.1
    rw [initial] at own
    exact own
  · intro a different
    rw [storage]
    exact effects.2.2.1 a different

/-- Recover the checked constructor's source run from the same clean retained
CREATE, keeping its actual transfer, raw execution and successful code charge. -/
theorem createTrace_source_witness
    {code : ByteArray} {c : Cert} {entry : SFunc} {msg : Msg} {installed : Devm}
    (checked : Cert.check code c = true) (codeEq : msg.code = code)
    (first : c.prog[0]? = some entry)
    (trace : ExecutionTrace.ProcessCreateMessageTrace msg (.ok installed))
    (clean : installed.error.isSome = false)
    (codeAddress : msg.codeAddress = none)
    (stateGas : msg.benv.stat.rules.stateGas = none) :
    ∃ (benv : Benv) (raw charged : Devm),
      (processCreateMessage.msg msg).benvAfterTransfer = .ok benv ∧
      exec (initEvm ((processCreateMessage.msg msg).withBenv benv)) = .ok raw ∧
      raw.error = none ∧
      processCreateMessage.chargeCodeGas msg.benv.stat.rules
        (raw.recordTouch msg.benv.stat.rules true msg.currentTarget) = .ok charged ∧
      SFunc.Run c.prog (initEvm ((processCreateMessage.msg msg).withBenv benv)).sta
        (initEvm ((processCreateMessage.msg msg).withBenv benv)).dyna entry (.halted raw) ∧
      installed = charged.setCode msg.currentTarget ⟨⟨charged.output⟩⟩ := by
  obtain ⟨benv, raw, charged, transfer, ⟨run⟩, rawClean, charge, installedEq⟩ :=
    createTrace_exec_witness trace clean codeAddress
  have hsg :
      (initEvm ((processCreateMessage.msg msg).withBenv benv)).sta.benvStat.rules.stateGas =
        none := by
    change benv.stat.rules.stateGas = none
    rw [Msg.benvAfterTransfer_ok_stateGas transfer]
    exact stateGas
  obtain ⟨body, found, source⟩ := lift_sound_noStateGas checked
    (show (initEvm ((processCreateMessage.msg msg).withBenv benv)).sta.code = code from codeEq)
    hsg run
  have same : body = entry := Option.some.inj (found.symm.trans first)
  rw [same] at source
  exact ⟨benv, raw, charged, transfer, (exec_iff_exec_eq _ _ _ _).mp ⟨run⟩,
    rawClean, charge, source, installedEq⟩

/-- A clean retained CREATE of a checked owner-constructor pattern installs
the exact returned window and initialized storage. The trace supplies the
execution witnesses; the source run derives zero call value. -/
theorem solcOwnerConstructor_effects_of_createTrace
    {code : ByteArray} {c : Cert} {msg : Msg} {installed : Devm}
    {sizeBytes offsetBytes : Bytes}
    {sizeBound : sizeBytes.length ≤ 32} {offsetBound : offsetBytes.length ≤ 32}
    {size offset : B256}
    (checked : Cert.check code c = true) (codeEq : msg.code = code)
    (first : c.prog[0]? = some solcOwnerConstructor)
    (ownerEntry : c.prog[1]? = some SolcStorageReturn.ownerInit)
    (returnEntry : c.prog[2]? = some (solcRuntimeReturn sizeBytes offsetBytes sizeBound offsetBound))
    (sizeWord : sizeBytes.toB256 = size) (offsetWord : offsetBytes.toB256 = offset)
    (nonzero : size.toNat ≠ 0)
    (trace : ExecutionTrace.ProcessCreateMessageTrace msg (.ok installed))
    (clean : installed.error.isSome = false)
    (codeAddress : msg.codeAddress = none)
    (stateGas : msg.benv.stat.rules.stateGas = none) :
    msg.value = 0 ∧
      (installed.getCode msg.currentTarget).toList =
        code.sliceD offset.toNat size.toNat (Linst.toUInt8 .stop) ∧
      installed.getStor msg.currentTarget = solcOwnerConstructorStorage Stor.empty msg.caller := by
  obtain ⟨benv, raw, charged, transfer, executed, rawClean, charge, source, -⟩ :=
    createTrace_source_witness checked codeEq first trace clean codeAddress stateGas
  obtain ⟨zero, result, resultEq, output, storage, -⟩ :=
    solcOwnerConstructor_message_effects ownerEntry returnEntry sizeWord offsetWord nonzero
      transfer codeAddress executed rawClean charge source
  have same : installed = result := Except.ok.inj (trace.result.symm.trans resultEq)
  rw [codeEq] at output
  exact ⟨zero, same ▸ output, same ▸ storage⟩

/-- The creation frame of `msg` over the post-transfer environment `benv`. -/
abbrev createSeed (msg : Msg) (benv : Benv) : Msg := (processCreateMessage.msg msg).withBenv benv

/-- The settled world of a successful lifted CREATE: the constructor's final state charged
the code deposit, with its output installed at the new address. -/
def liftCreatePost (target : Adr) (raw : Devm) : Devm :=
  (raw.setMach ⟨raw.stack, raw.memory, raw.gasLeft - raw.output.length * gasCodeDeposit,
    raw.stateGas⟩).setCode target ⟨⟨raw.output⟩⟩

/-- **Deploying lifted creation code, exactly.**  If the checked creation certificate's
constructor runs, gas-exactly, from the creation frame's start state to `raw` without error,
and `raw`'s output is admissible code (no `0xEF` prefix, affordable, within the size limit),
then `processCreateMessage msg` succeeds with exactly `liftCreatePost msg.currentTarget raw`. -/
theorem liftCreate_post {code : ByteArray} {c : Cert}
    (hc : Cert.check code c = true) (hj : Cert.jumpsOk code c = true)
    (msg : Msg) (hcodeAddress : msg.codeAddress = .none) (hcode : msg.code = code)
    (hfork : CoveredFork msg.benv.stat.fork) {benv : Benv} {raw : Devm}
    (htransfer : (processCreateMessage.msg msg).benvAfterTransfer = .ok benv)
    (hrun : SProg.RunExact c.prog (initSevm (createSeed msg benv))
      (initDevm (createSeed msg benv)) raw)
    (herror : raw.error = .none) (hprefix : raw.output.head? ≠ some 0xEF)
    (hgas : raw.output.length * gasCodeDeposit ≤ raw.gasLeft)
    (hmax : raw.output.length ≤ msg.benv.stat.rules.code.maxCodeSize) :
    processCreateMessage msg = .ok (liftCreatePost msg.currentTarget raw) := by
  have hstat : (initSevm (createSeed msg benv)).benvStat = msg.benv.stat := by
    show benv.stat = (processCreateMessage.msg msg).benv.stat
    exact benvAfterTransfer_stat htransfer
  obtain ⟨exc⟩ := lift_exact hc hj (sevm := initSevm (createSeed msg benv)) hcode
    (by rw [hstat]; exact hfork) hrun
  have hexec : exec (initEvm (createSeed msg benv)) = .ok raw :=
    (exec_iff_exec_eq _ _ _ _).mp ⟨exc⟩
  have hprocess : processMessage (processCreateMessage.msg msg) = .ok raw :=
    processMessage_ok_of_exec htransfer hcodeAddress hexec herror
      (hfork.cases (motive := fun f => f.ruleSet.settle.touchedSweep = false) rfl rfl rfl rfl)
  have hcharge := processCreateMessage.chargeCodeGas_legacy_eq_ok
    (rules := msg.benv.stat.rules) (d := raw) hfork.rules_stateGas_none hprefix hgas hmax
  exact processCreateMessage_ok_of_processMessage_and_charge msg hprocess herror hcharge

/-- The settled world's projections: error, remaining gas, code and storage at the new
address after account normalization, and every other account unchanged from the constructor's final state. -/
theorem liftCreatePost_facts (target : Adr) (raw : Devm) :
    (liftCreatePost target raw).error = raw.error ∧
    (liftCreatePost target raw).gasLeft = raw.gasLeft - raw.output.length * gasCodeDeposit ∧
    (liftCreatePost target raw).state.get target =
      ({ raw.state.get target with code := ⟨⟨raw.output⟩⟩ } : Acct).clearIfEmpty ∧
    (∀ a, a ≠ target → (liftCreatePost target raw).state.get a = raw.state.get a) := by
  refine ⟨Devm.setCode_error _ _ _, rfl, ?_, fun a ha => ?_⟩
  · show (raw.state.setCode target _).get target = _
    unfold State.setCode
    rw [State.setAccount_get_self]
  · show (raw.state.setCode target _).get a = _
    unfold State.setCode
    rw [State.setAccount_get_ne _ (Ne.symm ha)]

/-- **Deploying lifted creation code.**  If the checked creation certificate's constructor
runs, gas-exactly, from the creation frame's start state to `raw` without error, and `raw`'s
output is admissible code (no `0xEF` prefix, affordable, within the size limit), then
`processCreateMessage msg` succeeds, installs `raw.output` at `msg.currentTarget`, and keeps
the exact normalized storage there. -/
theorem liftCreate_ok {code : ByteArray} {c : Cert}
    (hc : Cert.check code c = true) (hj : Cert.jumpsOk code c = true)
    (msg : Msg) (hcodeAddress : msg.codeAddress = .none) (hcode : msg.code = code)
    (hfork : CoveredFork msg.benv.stat.fork) {benv : Benv} {raw : Devm}
    (htransfer : (processCreateMessage.msg msg).benvAfterTransfer = .ok benv)
    (hrun : SProg.RunExact c.prog (initSevm (createSeed msg benv))
      (initDevm (createSeed msg benv)) raw)
    (herror : raw.error = .none) (hprefix : raw.output.head? ≠ some 0xEF)
    (hgas : raw.output.length * gasCodeDeposit ≤ raw.gasLeft)
    (hmax : raw.output.length ≤ msg.benv.stat.rules.code.maxCodeSize) :
    ∃ post, processCreateMessage msg = .ok post ∧
      (post.getCode msg.currentTarget).toList = raw.output ∧
      Devm.getStor post msg.currentTarget =
        ({ raw.state.get msg.currentTarget with code := ⟨⟨raw.output⟩⟩ } : Acct).clearIfEmpty.stor ∧
      post.error = .none := by
  refine ⟨_, liftCreate_post hc hj msg hcodeAddress hcode hfork htransfer hrun herror hprefix
    hgas hmax, ?_, ?_, ?_⟩
  · unfold Devm.getCode Devm.getAcct
    rw [(liftCreatePost_facts _ raw).2.2.1]
    simp only [Acct.clearIfEmpty_code, ByteArray.toList_eq_toList_data]
  · unfold Devm.getStor Devm.getAcct
    rw [(liftCreatePost_facts _ raw).2.2.1]
  · rw [(liftCreatePost_facts _ raw).1]
    exact herror

end Blanc.Lift
