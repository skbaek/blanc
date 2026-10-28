import Blanc.Lift.Exact
import Blanc.Lift.ExactWalkCutOps
import Blanc.Lift.WalkSteps
import Blanc.DeploymentMessage

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
