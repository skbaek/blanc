import Blanc.LockExclusion
import Blanc.Lift.WitnessChild
import Blanc.Lift.CheckFast

/-!
# Node-exposing concrete walks

The witness engine of `Blanc/Lift/Witness.lean` turns a kernel-evaluated run into
`Nonempty (Exec …)`: it names machines, never the nodes (`Exec.Deriv`) of a derivation.
Statements quantified over nodes — `Exec.Deriv.ParentPrefix` chains, `Exec.rawFrameRoots`,
`Spawns` — need the nodes themselves.  This module provides them for *every* derivation
from a concrete machine, whatever its outcome:

* `Exec.Deriv.step_cont`, `step_halt`, `step_spawn`: one driver step pins the shape of
  any derivation node (its same-frame successor, its outcome, its spawned child);
* `pstepH`/`pwalkH`: a pc-level kernel interpreter over a `CodeTries` of the code, with the
  witness engine's shadows (`Agree`): the instruction is decoded from the trie and checked
  against the bytes (`bytesAtT`), jumps are checked by `jumpdestOkT`, `SLOAD`/`SSTORE`
  go through the forward lemmas on the key shadow, `SELFBALANCE` reads the account
  shadow, `RETURNDATACOPY` by Jaune's own step (`returndatacopy_accKeep`), every other
  instruction through the witness engine's `wstep`, and `KECCAK256` by its `keccakStep`.  The hash policy `HashPol` says what a walk does at
  `KECCAK256`: `.refuse` stops there, `.avoid slot` runs it and refuses a step whose digest
  is `slot`.  The frame-entering instructions stop a walk.  Each walk step is the real
  `Evm.step` (`pstepH_cont`, `pstepH_halt`).  `pstep`/`pwalk` are the `.refuse` walks;
* `pwalkH_cont`, `pwalkH_halt`: any derivation node at a walk's start configuration has a
  same-frame successor at its end, every node strictly between passes the walk's pc check
  and satisfies the hash policy (`NodeOKH`: no `KECCAK256` under `.refuse`; under
  `.avoid slot` every `KECCAK256` leaves a digest other than `slot`, so a whole frame
  chain is `HashAvoid slot`, `hashAvoid_of_hashOK`), and the raw frame descendants are
  unchanged; a halting walk pins the frame's outcome and shows it enters no child frame.
  `pwalk_cont`, `pwalk_halt` are the `.refuse` specialisations;
* `staticcall_node`, `call_node`, `delegatecall_node` (over `spawn_node`): the frame a
  call-family instruction spawns and its child's start configuration; `PrepFacts` gives the
  settle (`PrepFacts.settle_ok`, `.settle_error`) and resume (`resume_agree_ok_of`,
  `resume_agree_error_of`) facts.

The chain and frame layer over these (`chain_trans`, `spawn_resume_ok`, `leaf_frame`, …) is
`Blanc/Lift/NodeWalkFrames.lean`.  Nothing here is contract-specific.
-/

namespace Blanc.Lift.NodeWalk

open Jaune Blanc.Lift Blanc.Lift.Witness
open Jaune.Exec.Deriv (ParentStep ParentPrefix)

/-! ## One step, any derivation -/

/-- A continuing step: every derivation node has the step's successor as its same-frame
successor, with the same outcome and the same raw frame descendants. -/
theorem Exec.Deriv.step_cont {x : Exec.Deriv} {pc' : Nat} {d' : Devm}
    (h : Evm.step ⟨x.pc, x.sevm, x.devm⟩ = .cont pc' d') :
    ∃ x', ParentStep x' x ∧ x'.pc = pc' ∧ x'.sevm = x.sevm ∧ x'.devm = d' ∧
      x'.exn = x.exn ∧ Exec.rawFrameDescendants x'.exc = Exec.rawFrameDescendants x.exc := by
  obtain ⟨pc, sevm, devm, exn, exc⟩ := x
  cases exc with
  | halt h' => simp only at h; rw [h] at h'; cases h'
  | cont h' next =>
    simp only at h; rw [h] at h'; cases h'
    exact ⟨_, .cont h next, rfl, rfl, rfl, rfl, by simp [Exec.rawFrameDescendants]⟩
  | doneErr h' _ _ => simp only at h; rw [h] at h'; cases h'
  | doneOk h' _ _ _ => simp only at h; rw [h] at h'; cases h'
  | runErr h' _ _ _ => simp only at h; rw [h] at h'; cases h'
  | runOk h' _ _ _ _ => simp only at h; rw [h] at h'; cases h'

/-- A halting step: the node's outcome is the step's, it has no same-frame successor and
no raw frame descendant. -/
theorem Exec.Deriv.step_halt {x : Exec.Deriv} {ex : Execution}
    (h : Evm.step ⟨x.pc, x.sevm, x.devm⟩ = .halt ex) :
    x.exn = ex ∧ (∀ y, ParentPrefix x y → y = x) ∧ Exec.rawFrameDescendants x.exc = [] := by
  obtain ⟨pc, sevm, devm, exn, exc⟩ := x
  cases exc with
  | halt h' =>
    simp only at h; rw [h] at h'; cases h'
    refine ⟨rfl, fun y hy => ?_, by simp [Exec.rawFrameDescendants]⟩
    cases hy with
    | refl => rfl
    | step head _ => cases head
  | cont h' _ => simp only at h; rw [h] at h'; cases h'
  | doneErr h' _ _ => simp only at h; rw [h] at h'; cases h'
  | doneOk h' _ _ _ => simp only at h; rw [h] at h'; cases h'
  | runErr h' _ _ _ => simp only at h; rw [h] at h'; cases h'
  | runOk h' _ _ _ _ => simp only at h; rw [h] at h'; cases h'

/-- A spawning step whose frame enters: every derivation node spawns the child rooted at
the entry machine (`Spawns`); if the parent resumes, its continuation is the node's
same-frame successor, and otherwise the node halts with the resume error. -/
theorem Exec.Deriv.step_spawn {x : Exec.Deriv} {f : Frame} {rsm : Resume} {pc' : Nat}
    {cevm : Evm}
    (h : Evm.step ⟨x.pc, x.sevm, x.devm⟩ = .spawn f rsm pc') (henter : f.enter = .run cevm) :
    ∃ c : Exec.Deriv, Blanc.LockExclusion.Spawns x c ∧ c.pc = cevm.pc ∧ c.sevm = cevm.sta ∧
      c.devm = cevm.dyna ∧
      (∀ post, rsm.run (f.settle c.exn) = .ok post →
        ∃ x', ParentStep x' x ∧ x'.pc = pc' ∧ x'.sevm = x.sevm ∧ x'.devm = post ∧
          x'.exn = x.exn ∧
          Exec.rawFrameDescendants x.exc =
            c :: (Exec.rawFrameDescendants c.exc ++ Exec.rawFrameDescendants x'.exc)) ∧
      (∀ e, rsm.run (f.settle c.exn) = .error e →
        x.exn = .error e ∧ (∀ y, ParentPrefix x y → y = x) ∧
          Exec.rawFrameDescendants x.exc = c :: Exec.rawFrameDescendants c.exc) := by
  obtain ⟨pc, sevm, devm, exn, exc⟩ := x
  cases exc with
  | halt h' => simp only at h; rw [h] at h'; cases h'
  | cont h' _ => simp only at h; rw [h] at h'; cases h'
  | doneErr h' he _ =>
    simp only at h; rw [h] at h'; cases h'; rw [henter] at he; cases he
  | doneOk h' he _ _ =>
    simp only at h; rw [h] at h'; cases h'; rw [henter] at he; cases he
  | runErr h' he child hr =>
    simp only at h; rw [h] at h'; cases h'; rw [henter] at he; cases he
    refine ⟨⟨_, _, _, _, child⟩, .runErr h henter child hr, rfl, rfl, rfl, fun post hp => ?_, fun e he => ?_⟩
    · simp only at hp; rw [hr] at hp; cases hp
    · simp only at he; rw [hr] at he; cases he
      refine ⟨rfl, fun y hy => ?_, by simp [Exec.rawFrameDescendants]⟩
      cases hy with
      | refl => rfl
      | step head _ => cases head
  | runOk h' he child hr next =>
    simp only at h; rw [h] at h'; cases h'; rw [henter] at he; cases he
    refine ⟨⟨_, _, _, _, child⟩, .runOk h henter child hr next, rfl, rfl, rfl, fun post hp => ?_, fun e he => ?_⟩
    · simp only at hp; rw [hr] at hp; cases hp
      exact ⟨_, .runOk h henter child hr next, rfl, rfl, rfl, rfl,
        by simp [Exec.rawFrameDescendants]⟩
    · simp only at he; rw [hr] at he; cases he

/-! ## The pc-level walk -/

/-- A walk configuration: the program counter, the machine, and the witness engine's
shadows of the accessed storage keys and addresses, the storage and the accounts. -/
structure PCfg where
  pc : Nat
  devm : Devm
  keys : List (Adr × B256)
  adrs : List Adr
  stor : StorShadow
  acs : AcctShadow

/-- The witness-engine configuration of `c` at the tree `f`, no pending returns. -/
def PCfg.cfg (c : PCfg) (f : SFunc) : Cfg := ⟨c.devm, f, [], c.keys, c.adrs, c.stor, c.acs⟩

/-- The shadows of `c` describe its machine. -/
def PAgree (c : PCfg) : Prop := Agree (c.cfg .undefined)

theorem PAgree.cfg {c : PCfg} (h : PAgree c) (f : SFunc) : Agree (c.cfg f) := h

/-- The bytes an instruction occupies. -/
def instBytes : Inst → Bytes
  | .next n => Ninst.toBytes n
  | .jump j => [j.toUInt8]
  | .last l => [l.toUInt8]

/-- The 33 trie bytes from `pc` (zero past the trie). -/
def windowT (d : Nat) (t : LTrie UInt8) (pc : Nat) : Array UInt8 :=
  ((List.range 33).map fun i => (LTrie.get? d t (pc + i)).getD 0).toArray

/-- The instruction at `pc`: decoded from the trie window by Jaune's decoder and checked
against the trie bytes. -/
def decodeT (d : Nat) (t : LTrie UInt8) (pc : Nat) : Option Inst :=
  match (ByteArray.mk (windowT d t pc)).getInst 0 with
  | some i => if bytesAtT d t pc (instBytes i) then some i else none
  | none => none

theorem bytesAtT_eq' {code : ByteArray} {d : Nat} {t : LTrie UInt8}
    (ht : ∀ i, LTrie.get? d t i = code.data.toList[i]?) (pc : Nat) (bs : Bytes) :
    bytesAtT d t pc bs = bytesAt code pc bs := by
  induction bs generalizing pc with
  | nil => rfl
  | cons b bs ih =>
    rw [bytesAtT, ht, ih]
    simp only [bytesAt]
    have hd : ∀ (xs : List UInt8) (i : Nat), xs[i]? = (xs.drop i).head? := by
      intro xs i
      induction i generalizing xs with
      | zero => cases xs <;> rfl
      | succ i ih => cases xs with
        | nil => simp
        | cons x xs => exact ih xs
    rw [hd]
    cases h : code.data.toList.drop pc with
    | nil => simp
    | cons c cs =>
      have hnext : code.data.toList.drop (pc + 1) = cs := by
        rw [← List.drop_drop, h]; rfl
      have hbeq : (c == b) = decide (c = b) := rfl
      simp [hnext, hbeq]

/-- A decoded instruction is the real one. -/
theorem decodeT_sound {code : ByteArray} {d : Nat} (T : CodeTries code d) {pc : Nat}
    {i : Inst} (h : decodeT d T.bytes pc = some i) : code.getInst pc = some i := by
  unfold decodeT at h
  split at h
  · split at h
    · rename_i hb
      cases h
      rw [bytesAtT_eq' T.bytes_eq] at hb
      cases i with
      | next n => exact Ninst.at_of_slice (bytesAt_slice (ninst_bytes_ne_nil n) hb)
      | jump j => exact Jinst.at_of_slice (xs := []) (bytesAt_slice (by simp) hb)
      | last l => exact Linst.at_of_slice (xs := []) (bytesAt_slice (by simp) hb)
    · cases h
  · cases h

/-- `Jinst.runCore` with the destination check read from the tries. -/
def jrunT {code : ByteArray} {d : Nat} (T : CodeTries code d) (pc : Nat) (devm : Devm) :
    Jinst → Except (EvmError × Devm) (Nat × Devm)
  | .jumpdest => do
    let devm' ← chargeGas gJumpdest devm
    .ok ⟨pc + 1, devm'⟩
  | .jump => do
    let ⟨jump_dest, devm'⟩ ← devm.pop
    let devm'' ← chargeGas gMid devm'
    .assert (jumpdestOkT code d T jump_dest.toNat) ⟨.halt (.invalidJumpDest .none), devm''⟩
    .ok ⟨jump_dest.toNat, devm''⟩
  | .jumpi => do
    let ⟨dest, devm'⟩ ← devm.pop
    let ⟨cond, devm''⟩ ← devm'.pop
    let devm''' ← chargeGas gHigh devm''
    let pc' : Nat ←
      if cond = 0
      then .ok <| pc + 1
      else
        .assert (jumpdestOkT code d T dest.toNat) ⟨.halt (.invalidJumpDest .none), devm'''⟩
        .ok dest.toNat
    .ok ⟨pc', devm'''⟩

theorem jrunT_eq {code : ByteArray} {d : Nat} (T : CodeTries code d) {pc : Nat} {sevm : Sevm}
    {devm : Devm} (hcode : sevm.code = code) (j : Jinst) :
    jrunT T pc devm j = Jinst.runCore pc devm sevm j := by
  cases j <;> simp only [jrunT, Jinst.runCore, hcode, jumpdestOkT_eq, jumpable_eq_jumpdestOk]

/-- `SELFBALANCE` with the balance read from the account shadow (no EIP-7928 read set). -/
def selfbalanceP (sevm : Sevm) (c : PCfg) : Option Devm :=
  if sevm.benvStat.rules.bal.isNone then
    match chargeGas gLow c.devm with
    | .ok d =>
      match d.push (lookupA c.acs sevm.currentTarget).bal with
      | .ok d' => some d'
      | .error _ => none
    | .error _ => none
  else none

/-- A walk step's result. -/
inductive PRes
  | cont : PCfg → PRes
  | halt : Execution → PRes
  | stuck : PRes

/-- What a walk does at `KECCAK256`: `refuse` stops there (the walk is stuck), `avoid slot`
runs it and is stuck if the digest it leaves on the stack is `slot`. -/
inductive HashPol
  | refuse
  | avoid (slot : B256)

/-- The instruction `n`, run to the machine `d'`, is allowed by `pol`: only `KECCAK256` is
ever refused. -/
def HashPol.allows : HashPol → Ninst → Devm → Bool
  | .refuse, .reg .keccak256, _ => false
  | .avoid s, .reg .keccak256, d' => decide (d'.stack.head? ≠ some s)
  | _, _, _ => true

/-- One instruction under the hash policy `pol`.  `SELFDESTRUCT` and the frame-entering
instructions are not run (the walk is stuck there); `KECCAK256` runs through the witness
engine's `keccakStep` unless `pol` refuses it. -/
def pstepH (pol : HashPol) {code : ByteArray} {d : Nat} (T : CodeTries code d) (sevm : Sevm)
    (c : PCfg) : PRes :=
  match decodeT d T.bytes c.pc with
  | none => .stuck
  | some (.next (.exec _)) => .stuck
  | some (.next (.reg .selfbalance)) =>
    match selfbalanceP sevm c with
    | some d' => .cont { c with pc := c.pc + 1, devm := d' }
    | none => .stuck
  | some (.next (.reg .returndatacopy)) =>
    match Ninst.step ⟨c.pc, sevm, c.devm⟩ (.reg .returndatacopy) with
    | .cont pc' d' => .cont { c with pc := pc', devm := d' }
    | _ => .stuck
  | some (.next n) =>
    match wstep [] sevm (c.cfg (.next n (.last .stop))) with
    | .cont ⟨d1, .last .stop, [], k1, a1, s1, ac1⟩ =>
      if pol.allows n d1 then .cont ⟨c.pc + n.size, d1, k1, a1, s1, ac1⟩ else .stuck
    | _ => .stuck
  | some (.jump j) =>
    match jrunT T c.pc c.devm j with
    | .ok (pc', d') => .cont { c with pc := pc', devm := d' }
    | .error e => .halt (.error e)
  | some (.last .selfdestruct) => .stuck
  | some (.last l) => .halt (l.run sevm c.devm)

/-- One instruction, `KECCAK256` refused (`pstepH .refuse`). -/
def pstep {code : ByteArray} {d : Nat} (T : CodeTries code d) (sevm : Sevm) (c : PCfg) :
    PRes :=
  pstepH .refuse T sevm c

/-- At most `n` steps under the hash policy `pol`, each first checking `ok` at its pc. -/
def pwalkH (pol : HashPol) {code : ByteArray} {d : Nat} (T : CodeTries code d) (sevm : Sevm)
    (ok : Nat → Bool) : Nat → PCfg → PRes
  | 0, c => .cont c
  | n + 1, c =>
    if ok c.pc then
      match pstepH pol T sevm c with
      | .cont c' => pwalkH pol T sevm ok n c'
      | r => r
    else .stuck

/-- At most `n` steps, each first checking `ok` at its pc, `KECCAK256` refused. -/
def pwalk {code : ByteArray} {d : Nat} (T : CodeTries code d) (sevm : Sevm) (ok : Nat → Bool) :
    Nat → PCfg → PRes :=
  pwalkH .refuse T sevm ok

/-! ## One walk step is one driver step -/

theorem ninst_step_of_runCompiled {sevm : Sevm} {devm devm' : Devm} {n : Ninst}
    (hn : ∀ x, n ≠ .exec x) (h : Ninst.RunCompiled sevm devm n devm') (pc : Nat) :
    Ninst.step ⟨pc, sevm, devm⟩ n = .cont (pc + n.size) devm' := by
  obtain ⟨xl, -, h⟩ := h
  have h := h pc
  unfold Ninst.StepRun at h
  cases n with
  | exec x => exact absurd rfl (hn x)
  | _ =>
    simp only [Ninst.step] at h ⊢
    obtain ⟨-, he⟩ := Step.run_ofExecution.mp h
    rw [← he]; rfl

/-- A witness-engine step from `.next n (.last .stop)` to `.last .stop` is one compiled
run of `n`. -/
theorem runCompiled_of_stepOk {sevm : Sevm} {c c' : Cfg} {n : Ninst}
    (hf : c.f = .next n (.last .stop)) (hK : c.K = []) (hf' : c'.f = .last .stop)
    (hK' : c'.K = []) (h : StepOk [] sevm c c') (hag : Agree c) :
    Ninst.RunCompiled sevm c.devm n c'.devm := by
  have r' : RunK [] sevm c'.devm c'.f c'.K (.halted c'.devm) := by
    rw [hf', hK']; exact .last rfl
  have r := h.2 _ hag r'
  rw [hf, hK] at r
  cases r with
  | next hr rest =>
    cases rest with
    | last hl =>
      have : _ = _ := hl
      simp only [Linst.run] at this
      cases this
      exact hr

theorem agree_accKeep {c : PCfg} {d : Devm} (hag : PAgree c) (hk : AccKeep c.devm d) :
    PAgree { c with devm := d } := by
  refine ⟨fun x => ?_, fun a => ?_, fun a k => ?_, fun a => ?_⟩
  · show x ∈ d.accessedStorageKeys ↔ x ∈ c.keys
    rw [hk.2.1]; exact hag.1 x
  · show a ∈ d.accessedAddresses ↔ a ∈ c.adrs
    rw [hk.1]; exact hag.2.1 a
  · show storOf d.state a k = lookupS c.stor a k
    rw [hk.2.2]; exact hag.2.2.1 a k
  · show acctView (d.state.get a) = lookupA c.acs a
    rw [hk.2.2]; exact hag.2.2.2 a

theorem selfbalanceP_sound {sevm : Sevm} {c : PCfg} {d' : Devm} (hag : PAgree c)
    (h : selfbalanceP sevm c = some d') (pc : Nat) :
    Rinst.runCore pc c.devm sevm .selfbalance = .ok d' ∧ AccKeep c.devm d' := by
  unfold selfbalanceP at h
  split at h
  · rename_i hbal
    split at h
    · rename_i d hd
      split at h
      · rename_i d'' hp
        cases h
        have hk := accKeep_chargeGas hd
        have hb : d.balReadAccount sevm.benvStat.rules sevm.currentTarget = d := by
          have hn : sevm.benvStat.rules.bal = none := Option.isNone_iff_eq_none.mp hbal
          simp only [Devm.balReadAccount, hn, Option.isSome_none, Bool.false_eq_true,
            ↓reduceIte]
          rfl
        have hv : d.getBal sevm.currentTarget = (lookupA c.acs sevm.currentTarget).bal := by
          show (d.state.get _).bal = _
          rw [hk.2.2]; exact bal_eq_lookupA hag.2.2.2 _
        refine ⟨?_, hk.trans (accKeep_push hp)⟩
        simp only [Rinst.runCore, bind, Except.bind, hd, hb, hv, hp]
      · cases h
    · cases h
  · cases h

theorem jrunT_accKeep {code : ByteArray} {d : Nat} (T : CodeTries code d) {pc pc' : Nat}
    {devm d' : Devm} {j : Jinst} (h : jrunT T pc devm j = .ok (pc', d')) : AccKeep devm d' := by
  cases j with
  | jumpdest =>
    simp only [jrunT, bind, Except.bind] at h
    split at h
    · cases h
    · rename_i e he; cases h; exact accKeep_chargeGas he
  | jump =>
    simp only [jrunT, bind, Except.bind] at h
    split at h
    · cases h
    · rename_i p hp
      split at h
      · cases h
      · rename_i e he
        simp only [Except.assert] at h
        split at h
        · cases h
        · cases h; exact (accKeep_pop hp).trans (accKeep_chargeGas he)
  | jumpi =>
    simp only [jrunT, bind, Except.bind] at h
    split at h
    · cases h
    · rename_i p hp
      split at h
      · cases h
      · rename_i p2 hp2
        split at h
        · cases h
        · rename_i e he
          have hk := (accKeep_pop hp).trans ((accKeep_pop hp2).trans (accKeep_chargeGas he))
          split at h
          · cases h; exact hk
          · simp only [Except.assert] at h
            split at h
            · cases h
            · cases h; exact hk

/-- `RETURNDATACOPY` touches neither the accessed sets nor the world. -/
theorem returndatacopy_accKeep {pc : Nat} {sevm : Sevm} {devm devm' : Devm}
    (h : Rinst.runCore pc devm sevm .returndatacopy = .ok devm') : AccKeep devm devm' := by
  simp only [Rinst.runCore] at h
  obtain ⟨⟨i, d1⟩, h1, e1⟩ := Except.bind_eq_ok h
  obtain ⟨⟨j, d2⟩, h2, e2⟩ := Except.bind_eq_ok e1
  obtain ⟨⟨n, d3⟩, h3, e3⟩ := Except.bind_eq_ok e2
  obtain ⟨d4, h4, h5⟩ := Except.bind_eq_ok e3
  split at h5
  · cases h5
  · cases h5
    exact (accKeep_popToNat h1).trans ((accKeep_popToNat h2).trans
      ((accKeep_popToNat h3).trans ((accKeep_chargeGas h4).trans ⟨rfl, rfl, rfl⟩)))

/-- One `RETURNDATACOPY` step touches neither the accessed sets nor the world. -/
theorem returndatacopy_step_accKeep {pc pc' : Nat} {sevm : Sevm} {devm devm' : Devm}
    (h : Ninst.step ⟨pc, sevm, devm⟩ (.reg .returndatacopy) = .cont pc' devm') :
    AccKeep devm devm' := by
  rw [Ninst.step_reg] at h
  unfold Step.ofExecution at h
  split at h
  · cases h
  · cases h
    rename_i hd
    exact returndatacopy_accKeep hd

/-- The code does not execute `KECCAK256` at `pc`. -/
def NoKeccakAt (code : ByteArray) (pc : Nat) : Prop := ¬ Ninst.At code pc (.reg .keccak256)

/-- `pol` accepts the step at `pc` of `code` that leaves the machine `d'`: a refusing policy
means no `KECCAK256` at `pc`; an avoiding one means that a `KECCAK256` at `pc` left a digest
other than `slot`. -/
def HashPol.StepOK (code : ByteArray) (pc : Nat) (d' : Devm) : HashPol → Prop
  | .refuse => NoKeccakAt code pc
  | .avoid slot => Ninst.At code pc (.reg .keccak256) → d'.stack.head? ≠ some slot

theorem HashPol.stepOK_of_noKeccak {code : ByteArray} {pc : Nat} {d' : Devm}
    (pol : HashPol) (h : NoKeccakAt code pc) : pol.StepOK code pc d' := by
  cases pol with
  | refuse => exact h
  | avoid s => exact fun hk => absurd hk h

/-- **A continuing walk step is the real driver step**, keeps the shadows, and `pol` accepts
it (a `KECCAK256` step under `.avoid slot` leaves a digest other than `slot`). -/
theorem pstepH_cont {pol : HashPol} {code : ByteArray} {d : Nat} (T : CodeTries code d)
    {sevm : Sevm} (hcode : sevm.code = code) {c c' : PCfg} (hag : PAgree c)
    (h : pstepH pol T sevm c = .cont c') :
    Evm.step ⟨c.pc, sevm, c.devm⟩ = .cont c'.pc c'.devm ∧ PAgree c' ∧
      pol.StepOK code c.pc c'.devm := by
  unfold pstepH at h
  split at h
  · cases h
  · cases h
  · rename_i hdec
    have hat : Ninst.At sevm.code c.pc (.reg .selfbalance) := by
      rw [hcode]; exact decodeT_sound T hdec
    have hnk : NoKeccakAt code c.pc := by
      intro hk; rw [← hcode, Ninst.At, hat] at hk; cases hk
    split at h
    · rename_i d' hs
      cases h
      obtain ⟨hr, hk⟩ := selfbalanceP_sound hag hs c.pc
      refine ⟨?_, agree_accKeep hag hk, pol.stepOK_of_noKeccak hnk⟩
      rw [Evm.step_next hat]
      simp only [Ninst.step, Rinst.run, hr]
      rfl
    · cases h
  · rename_i hdec
    have hat : Ninst.At sevm.code c.pc (.reg .returndatacopy) := by
      rw [hcode]; exact decodeT_sound T hdec
    have hnk : NoKeccakAt code c.pc := by
      intro hk; rw [← hcode, Ninst.At, hat] at hk; cases hk
    split at h
    · rename_i pc' d' hs
      cases h
      refine ⟨?_, agree_accKeep hag (returndatacopy_step_accKeep hs), pol.stepOK_of_noKeccak hnk⟩
      rw [Evm.step_next hat]; exact hs
    · cases h
  · rename_i n hne hnsb hnrd hdec
    have hat : Ninst.At sevm.code c.pc n := by rw [hcode]; exact decodeT_sound T hdec
    split at h
    · rename_i d1 k1 a1 s1 ac1 hw
      split at h
      · rename_i hal
        cases h
        have hok := wstep_cont hw
        have hag1 : Agree ⟨d1, .last .stop, [], k1, a1, s1, ac1⟩ := hok.1 (hag.cfg _)
        have hrc := runCompiled_of_stepOk (c := c.cfg (.next n (.last .stop)))
          (c' := ⟨d1, .last .stop, [], k1, a1, s1, ac1⟩) rfl rfl rfl rfl hok (hag.cfg _)
        refine ⟨?_, hag1, ?_⟩
        · rw [Evm.step_next hat]
          exact ninst_step_of_runCompiled (fun x hx => hne x hx) hrc c.pc
        · cases pol with
          | refuse =>
            intro hk
            rw [← hcode, Ninst.At, hat] at hk
            cases hk
            simp [HashPol.allows] at hal
          | avoid s =>
            intro hk
            rw [← hcode, Ninst.At, hat] at hk
            cases hk
            simpa [HashPol.allows] using hal
      · cases h
    · cases h
  · rename_i j hdec
    have hat : Jinst.At sevm.code c.pc j := by rw [hcode]; exact decodeT_sound T hdec
    have hnk : NoKeccakAt code c.pc := by
      intro hk; rw [← hcode, Ninst.At, hat] at hk; cases hk
    split at h
    · rename_i pc' d' hj
      cases h
      refine ⟨?_, agree_accKeep hag (jrunT_accKeep T hj), pol.stepOK_of_noKeccak hnk⟩
      rw [Evm.step_jump hat]
      show Step.ofJump (Jinst.runCore c.pc c.devm sevm j) = _
      rw [← jrunT_eq T hcode, hj]; rfl
    · cases h
  · cases h
  · cases h

/-- **A halting walk step is the real driver step** (under any hash policy: a halting
instruction is never `KECCAK256`). -/
theorem pstepH_halt {pol : HashPol} {code : ByteArray} {d : Nat} (T : CodeTries code d)
    {sevm : Sevm} (hcode : sevm.code = code) {c : PCfg} {ex : Execution}
    (h : pstepH pol T sevm c = .halt ex) :
    Evm.step ⟨c.pc, sevm, c.devm⟩ = .halt ex ∧ NoKeccakAt code c.pc := by
  unfold pstepH at h
  split at h
  · cases h
  · cases h
  · split at h <;> cases h
  · split at h <;> cases h
  · split at h
    · split at h <;> cases h
    · cases h
  · rename_i j hdec
    have hat : Jinst.At sevm.code c.pc j := by rw [hcode]; exact decodeT_sound T hdec
    have hnk : NoKeccakAt code c.pc := by
      intro hk; rw [← hcode, Ninst.At, hat] at hk; cases hk
    split at h
    · cases h
    · rename_i e hj
      cases h
      refine ⟨?_, hnk⟩
      rw [Evm.step_jump hat]
      show Step.ofJump (Jinst.runCore c.pc c.devm sevm j) = _
      rw [← jrunT_eq T hcode, hj]; rfl
  · cases h
  · rename_i l _ hdec
    cases h
    have hat : Linst.At sevm.code c.pc l := by rw [hcode]; exact decodeT_sound T hdec
    have hnk : NoKeccakAt code c.pc := by
      intro hk; rw [← hcode, Ninst.At, hat] at hk; cases hk
    exact ⟨Evm.step_last hat, hnk⟩

/-! ## Walks over derivation nodes -/

/-- The derivation node `x` sits at the configuration `c` of a frame running `sevm`. -/
def NodeAt (sevm : Sevm) (c : PCfg) (x : Exec.Deriv) : Prop :=
  x.pc = c.pc ∧ x.sevm = sevm ∧ x.devm = c.devm

/-- The node `y` satisfies the hash policy: under `.refuse` it executes no `KECCAK256`; under
`.avoid slot`, if it executes one, its every same-frame successor has a digest other than
`slot` on top of its stack. -/
def HashPol.NodeOK (code : ByteArray) (y : Exec.Deriv) : HashPol → Prop
  | .refuse => NoKeccakAt code y.pc
  | .avoid slot =>
    Ninst.At code y.pc (.reg .keccak256) →
      ∀ y', ParentStep y' y → y'.devm.stack.head? ≠ some slot

/-- The node passes the walk's pc check and executes no `KECCAK256`. -/
def NodeOK (code : ByteArray) (ok : Nat → Bool) (y : Exec.Deriv) : Prop :=
  ok y.pc = true ∧ NoKeccakAt code y.pc

/-- The node passes the walk's pc check and satisfies the hash policy `pol`
(`NodeOKH code ok .refuse = NodeOK code ok`). -/
def NodeOKH (code : ByteArray) (ok : Nat → Bool) (pol : HashPol) (y : Exec.Deriv) : Prop :=
  ok y.pc = true ∧ pol.NodeOK code y

theorem HashPol.nodeOK_of_noKeccak {code : ByteArray} {y : Exec.Deriv} (pol : HashPol)
    (h : NoKeccakAt code y.pc) : pol.NodeOK code y := by
  cases pol with
  | refuse => exact h
  | avoid s => exact fun hk => absurd hk h

/-- A node whose same-frame successor `x1` is the step `pol` accepts satisfies `pol`. -/
theorem HashPol.nodeOK_of_stepOK {code : ByteArray} {pol : HashPol} {x x1 : Exec.Deriv}
    (e1 : ParentStep x1 x) (h : pol.StepOK code x.pc x1.devm) : pol.NodeOK code x := by
  cases pol with
  | refuse => exact h
  | avoid s =>
    intro hk y' hy'
    have := Jaune.Exec.Deriv.ParentStep.unique hy' e1
    subst this
    exact h hk

theorem step_eq_of_nodeAt {sevm : Sevm} {c : PCfg} {x : Exec.Deriv} (hx : NodeAt sevm c x) :
    Evm.step ⟨x.pc, x.sevm, x.devm⟩ = Evm.step ⟨c.pc, sevm, c.devm⟩ := by
  rw [hx.1, hx.2.1, hx.2.2]

/-- **A continuing walk, on any derivation.**  Every node at the start configuration has a
same-frame successor at the end configuration, with the same outcome and raw frame
descendants; every node from the start up to (excluding) that successor passes the check
and satisfies the hash policy `pol`. -/
theorem pwalkH_cont (pol : HashPol) {code : ByteArray} {d : Nat} (T : CodeTries code d)
    {sevm : Sevm} (hcode : sevm.code = code) (ok : Nat → Bool) :
    ∀ (n : Nat) (c c' : PCfg), PAgree c → pwalkH pol T sevm ok n c = .cont c' →
      PAgree c' ∧ ∀ x, NodeAt sevm c x → ∃ x', NodeAt sevm c' x' ∧ ParentPrefix x x' ∧
        x'.exn = x.exn ∧ Exec.rawFrameDescendants x'.exc = Exec.rawFrameDescendants x.exc ∧
        ∀ y, ParentPrefix x y → ParentPrefix y x' → y ≠ x' → NodeOKH code ok pol y
  | 0, c, c', hag, h => by
    simp only [pwalkH, PRes.cont.injEq] at h
    subst h
    refine ⟨hag, fun x hx => ⟨x, hx, .refl _, rfl, rfl, fun y h1 h2 hne => ?_⟩⟩
    exact absurd (Blanc.Exec.Deriv.ParentPrefix.antisymm h2 h1) hne
  | n + 1, c, c', hag, h => by
    simp only [pwalkH] at h
    split at h
    · rename_i hok
      cases h1 : pstepH pol T sevm c with
      | stuck => rw [h1] at h; cases h
      | halt ex' => rw [h1] at h; cases h
      | cont c1 =>
        rw [h1] at h
        obtain ⟨hs, hag1, hst⟩ := pstepH_cont T hcode hag h1
        obtain ⟨hag', ih⟩ := pwalkH_cont pol T hcode ok n c1 c' hag1 h
        refine ⟨hag', fun x hx => ?_⟩
        obtain ⟨x1, e1, hp1, hs1, hd1, hex1, hdesc1⟩ :=
          Exec.Deriv.step_cont ((step_eq_of_nodeAt hx).trans hs)
        obtain ⟨x', hx', hpp, hex', hdesc', hbet⟩ :=
          ih x1 ⟨hp1, hs1.trans hx.2.1, hd1⟩
        refine ⟨x', hx', .step e1 hpp, hex'.trans hex1, hdesc'.trans hdesc1,
          fun y hy1 hy2 hne => ?_⟩
        cases hy1 with
        | refl =>
          exact ⟨hx.1 ▸ hok, HashPol.nodeOK_of_stepOK e1 (by rw [hx.1, hd1]; exact hst)⟩
        | step head rest =>
          have := Jaune.Exec.Deriv.ParentStep.unique head e1
          subst this
          exact hbet y rest hy2 hne
    · cases h

/-- **A halting walk, on any derivation.**  Every node at the start configuration has
the walk's outcome and no raw frame descendant, and every node of its same-frame chain
passes the check and satisfies the hash policy `pol`. -/
theorem pwalkH_halt (pol : HashPol) {code : ByteArray} {d : Nat} (T : CodeTries code d)
    {sevm : Sevm} (hcode : sevm.code = code) (ok : Nat → Bool) :
    ∀ (n : Nat) (c : PCfg) (ex : Execution), PAgree c → pwalkH pol T sevm ok n c = .halt ex →
      ∀ x, NodeAt sevm c x → x.exn = ex ∧ Exec.rawFrameDescendants x.exc = [] ∧
        ∀ y, ParentPrefix x y → NodeOKH code ok pol y
  | 0, c, ex, _, h => by simp [pwalkH] at h
  | n + 1, c, ex, hag, h => by
    simp only [pwalkH] at h
    split at h
    · rename_i hok
      cases h1 : pstepH pol T sevm c with
      | stuck => rw [h1] at h; cases h
      | cont c1 =>
        rw [h1] at h
        obtain ⟨hs, hag1, hst⟩ := pstepH_cont T hcode hag h1
        have ih := pwalkH_halt pol T hcode ok n c1 ex hag1 h
        intro x hx
        obtain ⟨x1, e1, hp1, hs1, hd1, hex1, hdesc1⟩ :=
          Exec.Deriv.step_cont ((step_eq_of_nodeAt hx).trans hs)
        obtain ⟨hex, hdesc, hall⟩ := ih x1 ⟨hp1, hs1.trans hx.2.1, hd1⟩
        refine ⟨hex1 ▸ hex, hdesc1 ▸ hdesc, fun y hy => ?_⟩
        cases hy with
        | refl =>
          exact ⟨hx.1 ▸ hok, HashPol.nodeOK_of_stepOK e1 (by rw [hx.1, hd1]; exact hst)⟩
        | step head rest =>
          have := Jaune.Exec.Deriv.ParentStep.unique head e1
          subst this
          exact hall y rest
      | halt ex' =>
        rw [h1] at h
        cases h
        obtain ⟨hs, hnk⟩ := pstepH_halt T hcode h1
        intro x hx
        obtain ⟨hex, hno, hdesc⟩ := Exec.Deriv.step_halt ((step_eq_of_nodeAt hx).trans hs)
        refine ⟨hex, hdesc, fun y hy => ?_⟩
        rw [hno y hy]
        exact ⟨hx.1 ▸ hok, pol.nodeOK_of_noKeccak (hx.1 ▸ hnk)⟩
    · cases h

/-- **A continuing walk, on any derivation** (`pwalkH_cont` at `.refuse`): every node
passes the check and executes no `KECCAK256`. -/
theorem pwalk_cont {code : ByteArray} {d : Nat} (T : CodeTries code d) {sevm : Sevm}
    (hcode : sevm.code = code) (ok : Nat → Bool) :
    ∀ (n : Nat) (c c' : PCfg), PAgree c → pwalk T sevm ok n c = .cont c' →
      PAgree c' ∧ ∀ x, NodeAt sevm c x → ∃ x', NodeAt sevm c' x' ∧ ParentPrefix x x' ∧
        x'.exn = x.exn ∧ Exec.rawFrameDescendants x'.exc = Exec.rawFrameDescendants x.exc ∧
        ∀ y, ParentPrefix x y → ParentPrefix y x' → y ≠ x' → NodeOK code ok y :=
  fun n c c' hag h => pwalkH_cont .refuse T hcode ok n c c' hag h

/-- **A halting walk, on any derivation** (`pwalkH_halt` at `.refuse`). -/
theorem pwalk_halt {code : ByteArray} {d : Nat} (T : CodeTries code d) {sevm : Sevm}
    (hcode : sevm.code = code) (ok : Nat → Bool) :
    ∀ (n : Nat) (c : PCfg) (ex : Execution), PAgree c → pwalk T sevm ok n c = .halt ex →
      ∀ x, NodeAt sevm c x → x.exn = ex ∧ Exec.rawFrameDescendants x.exc = [] ∧
        ∀ y, ParentPrefix x y → NodeOK code ok y :=
  fun n c ex hag h => pwalkH_halt .refuse T hcode ok n c ex hag h

/-! ## `STATICCALL` up to its spawn, and back -/

/-- The `.staticcall` arm of `Xinst.step` up to its spawn (`Xinst.step_staticcall_spawn`),
warm/cold on the address shadow `adrs`, the callee's code from the account shadow `acs`. -/
def scallPrep (sevm : Sevm) (devm : Devm) (adrs : List Adr) (acs : AcctShadow) :
    Option CallPrep :=
  match devm.stack with
  | gw :: tw :: iiw :: isw :: oiw :: osw :: s =>
    if decide (CoveredFork sevm.benvStat.fork) ∧ sevm.depth ≠ 0 then
      let d0 := devm.setMach ⟨s, devm.memory, devm.gasLeft, devm.stateGas⟩
      let ext := d0.extCost [⟨iiw.toNat, isw.toNat⟩, ⟨oiw.toNat, osw.toNat⟩]
      let callee := tw.toAdr
      let dA := addAccessedAddress d0 callee
      let code := (lookupA acs callee).code
      match getDelegatedCodeAddress code with
      | some _ => none
      | none =>
        let acc := accessCostL callee adrs
        let r := calculateMsgCallGas 0 gw.toNat dA.gasLeft ext acc
        if r.1 + ext ≤ dA.gasLeft then
          let p := callSpawnParent dA (r.1 + ext) iiw.toNat isw.toNat oiw.toNat osw.toNat
          some ⟨Frame.ofCall (staticcallSpawnMsg sevm p r.2 callee callee iiw.toNat isw.toNat
            code false), p, oiw.toNat, osw.toNat, callee :: adrs⟩
        else none
    else none
  | _ => none

theorem scallPrep_spec {sevm : Sevm} {devm : Devm} {adrs : List Adr} {acs : AcctShadow}
    {cp : CallPrep} (h : scallPrep sevm devm adrs acs = some cp)
    (hA : ∀ a, a ∈ devm.accessedAddresses ↔ a ∈ adrs) (hC : AcctAgree devm.state acs) :
    Xinst.step sevm devm .staticcall = .spawn cp.f (.call cp.p cp.oi cp.os) ∧
      (∀ a, a ∈ cp.p.accessedAddresses ↔ a ∈ cp.adrs) ∧
      cp.p.accessedStorageKeys = devm.accessedStorageKeys ∧
      cp.f.isCreate = false ∧ cp.f.inner.accessedAddresses = cp.p.accessedAddresses ∧
      cp.f.inner.accessedStorageKeys = cp.p.accessedStorageKeys ∧
      cp.f.inner.benv.stat.rules.stateGas = none ∧ cp.f.inner.benv.state = devm.state ∧
      cp.p.state = devm.state := by
  simp only [scallPrep] at h
  split at h
  · rename_i gw tw iiw isw oiw osw s hs
    have hcode : (lookupA acs tw.toAdr).code = (addAccessedAddress
        (devm.setMach ⟨s, devm.memory, devm.gasLeft, devm.stateGas⟩) tw.toAdr).state.getCode
        tw.toAdr := (congrArg Acct.code (hC tw.toAdr)).symm
    simp only [hcode] at h
    split at h
    · rename_i hcond
      obtain ⟨hfork, hdepth⟩ := hcond
      have hfork' : CoveredFork sevm.benvStat.fork := of_decide_eq_true hfork
      split at h
      · cases h
      · rename_i hdel
        have hdel' : accessDelegation
            (addAccessedAddress (devm.setMach ⟨s, devm.memory, devm.gasLeft, devm.stateGas⟩)
              tw.toAdr) tw.toAdr =
            ⟨false, tw.toAdr, (addAccessedAddress
              (devm.setMach ⟨s, devm.memory, devm.gasLeft, devm.stateGas⟩) tw.toAdr).state.getCode
              tw.toAdr, 0,
              addAccessedAddress (devm.setMach ⟨s, devm.memory, devm.gasLeft, devm.stateGas⟩)
                tw.toAdr⟩ := by
          unfold accessDelegation
          simp only at hdel ⊢
          rw [hdel]
        have hacc : accessCost tw.toAdr
            (devm.setMach ⟨s, devm.memory, devm.gasLeft, devm.stateGas⟩).accessedAddresses + 0 =
            accessCostL tw.toAdr adrs := by
          rw [Nat.add_zero]; exact accessCost_eq_L hA
        have hins : ∀ a, a ∈ (addAccessedAddress
            (devm.setMach ⟨s, devm.memory, devm.gasLeft, devm.stateGas⟩) tw.toAdr).accessedAddresses ↔
            a ∈ tw.toAdr :: adrs := by
          intro a
          show a ∈ devm.accessedAddresses.insert tw.toAdr ↔ _
          rw [Std.HashSet.mem_insert, List.mem_cons, hA a, beq_iff_eq]
          constructor <;> rintro (h | h) <;> first | exact .inl h.symm | exact .inr h
        have hsg := hfork'.rules_stateGas_none
        split at h
        · rename_i hgas
          cases h
          exact ⟨Xinst.step_staticcall_spawn hfork' hs rfl hdel' hacc rfl hgas hdepth,
            hins, rfl, rfl, rfl, rfl, hsg, rfl, rfl⟩
        · cases h
    · cases h
  · cases h

/-- The walk configuration a frame entered with shadows starts at. -/
def childCfg (cevm : Evm) (f : Frame) (keys : List (Adr × B256)) (adrs : List Adr)
    (stor : StorShadow) (acs : AcctShadow) : PCfg :=
  ⟨cevm.pc, cevm.dyna, keys, adrs, stor, acsTransfer f.inner acs⟩

/-- What a call-family preparation `cp` (`scallPrep`, `callPrepP`, `dcallPrep`) at the
configuration `c` fixes: the suspended parent's accessed sets, the entry frame's message
(accessed sets those of the parent, its world the caller's, not a create, no state gas). -/
structure PrepFacts (c : PCfg) (cp : CallPrep) : Prop where
  adrs : ∀ a, a ∈ cp.p.accessedAddresses ↔ a ∈ cp.adrs
  keys : cp.p.accessedStorageKeys = c.devm.accessedStorageKeys
  entryAdrs : cp.f.inner.accessedAddresses = cp.p.accessedAddresses
  entryKeys : cp.f.inner.accessedStorageKeys = cp.p.accessedStorageKeys
  create : cp.f.isCreate = false
  stateGas : cp.f.inner.benv.stat.rules.stateGas = none
  state : cp.f.inner.benv.state = c.devm.state

/-- **Any call-family spawn node, on any derivation.**  At a node sitting at an agreeing
configuration whose code has the frame-entering instruction `x` at its pc, if the
instruction spawns the prepared frame `cp.f` (resumed by `.call`), the frame is entered
with the machine `frameEnterS` computes and the child's start configuration agrees. -/
theorem spawn_node {sevm : Sevm} {c : PCfg} {cp : CallPrep} {cevm : Evm} {x : Xinst}
    (hag : PAgree c) (hat : Ninst.At sevm.code c.pc (.exec x))
    (hstep : Xinst.step sevm c.devm x = .spawn cp.f (.call cp.p cp.oi cp.os))
    (hF : PrepFacts c cp) (he : frameEnterS cp.f c.acs = .run cevm) :
    Evm.step ⟨c.pc, sevm, c.devm⟩ = .spawn cp.f (.call cp.p cp.oi cp.os) (c.pc + 1) ∧
      cp.f.enter = .run cevm ∧ cevm.pc = 0 ∧
      PAgree (childCfg cevm cp.f c.keys cp.adrs c.stor c.acs) := by
  have hC : AcctAgree cp.f.inner.benv.state c.acs := by rw [hF.state]; exact hag.2.2.2
  refine ⟨?_, by rw [frame_enter_eq_B, frameEnterB_eq_S hC]; exact he, ?_, ?_⟩
  · rw [Evm.step_next hat]
    simp only [Ninst.step, hstep]
    rfl
  · obtain ⟨benv, -, rfl⟩ := frameEnterS_run he
    rfl
  · exact frameStart_agree .undefined he
      (fun y => by rw [hF.entryKeys, hF.keys]; exact hag.1 y)
      (fun a => by rw [hF.entryAdrs]; exact hF.adrs a)
      (fun a k => by rw [hF.state]; exact hag.2.2.1 a k)
      (by rw [hF.state]; exact hag.2.2.2)

/-- `scallPrep`'s instruction and frame facts. -/
theorem scallPrep_node_facts {sevm : Sevm} {c : PCfg} {cp : CallPrep}
    (hag : PAgree c) (hp : scallPrep sevm c.devm c.adrs c.acs = some cp) :
    Xinst.step sevm c.devm .staticcall = .spawn cp.f (.call cp.p cp.oi cp.os) ∧
      PrepFacts c cp := by
  obtain ⟨hstep, hpa, hpk, hcr, hia, hik, hsg, hst, -⟩ := scallPrep_spec hp hag.2.1 hag.2.2.2
  exact ⟨hstep, ⟨hpa, hpk, hia, hik, hcr, hsg, hst⟩⟩

/-- **A `STATICCALL` node, on any derivation.**  At a node sitting at an agreeing
configuration whose code has a `STATICCALL` at its pc, the call spawns the frame
`scallPrep` computes, entered with the machine `frameEnterS` computes; the child's start
configuration agrees. -/
theorem staticcall_node {sevm : Sevm} {c : PCfg} {cp : CallPrep} {cevm : Evm}
    (hag : PAgree c) (hat : Ninst.At sevm.code c.pc (.exec .staticcall))
    (hp : scallPrep sevm c.devm c.adrs c.acs = some cp)
    (he : frameEnterS cp.f c.acs = .run cevm) :
    Evm.step ⟨c.pc, sevm, c.devm⟩ = .spawn cp.f (.call cp.p cp.oi cp.os) (c.pc + 1) ∧
      cp.f.enter = .run cevm ∧ cevm.pc = 0 ∧
      PAgree (childCfg cevm cp.f c.keys cp.adrs c.stor c.acs) :=
  let ⟨hstep, hF⟩ := scallPrep_node_facts hag hp
  spawn_node hag hat hstep hF he

/-- `CALL` up to its spawn at a walk configuration (`callPrep` at its witness-engine
configuration). -/
def callPrepP (sevm : Sevm) (c : PCfg) : Option CallPrep := callPrep sevm (c.cfg .undefined)

/-- `callPrepP`'s instruction and frame facts. -/
theorem callPrepP_node_facts {sevm : Sevm} {c : PCfg} {cp : CallPrep}
    (hag : PAgree c) (hp : callPrepP sevm c = some cp) :
    Xinst.step sevm c.devm .call = .spawn cp.f (.call cp.p cp.oi cp.os) ∧ PrepFacts c cp := by
  obtain ⟨hstep, hpa, hpk, hcr, hia, hik, hsg, hst⟩ := callPrep_spec hp hag.2.1 hag.2.2.2
  exact ⟨hstep, ⟨hpa, hpk, hia, hik, hcr, hsg, hst⟩⟩

/-- **A `CALL` node, on any derivation** (value or not): at a node sitting at an agreeing
configuration whose code has a `CALL` at its pc, the call spawns the frame `callPrepP`
computes, entered with the machine `frameEnterS` computes (the value transfer applied to
the account shadow); the child's start configuration agrees.  `PrepFacts` gives the settle
and resume hypotheses (`PrepFacts.settle_ok`, `PrepFacts.settle_error`,
`resume_agree_ok_of`, `resume_agree_error_of`). -/
theorem call_node {sevm : Sevm} {c : PCfg} {cp : CallPrep} {cevm : Evm}
    (hag : PAgree c) (hat : Ninst.At sevm.code c.pc (.exec .call))
    (hp : callPrepP sevm c = some cp) (he : frameEnterS cp.f c.acs = .run cevm) :
    Evm.step ⟨c.pc, sevm, c.devm⟩ = .spawn cp.f (.call cp.p cp.oi cp.os) (c.pc + 1) ∧
      cp.f.enter = .run cevm ∧ cevm.pc = 0 ∧
      PAgree (childCfg cevm cp.f c.keys cp.adrs c.stor c.acs) ∧ PrepFacts c cp :=
  let ⟨hstep, hF⟩ := callPrepP_node_facts hag hp
  let ⟨h1, h2, h3, h4⟩ := spawn_node hag hat hstep hF he
  ⟨h1, h2, h3, h4, hF⟩

/-- `dcallPrep`'s instruction and frame facts. -/
theorem dcallPrep_node_facts {sevm : Sevm} {c : PCfg} {cp : CallPrep}
    (hag : PAgree c) (hp : dcallPrep sevm c.devm c.adrs c.acs = some cp) :
    Xinst.step sevm c.devm .delegatecall = .spawn cp.f (.call cp.p cp.oi cp.os) ∧
      PrepFacts c cp := by
  obtain ⟨hstep, hpa, hpk, hcr, hia, hik, hsg, hst, -⟩ := dcallPrep_spec hp hag.2.1 hag.2.2.2
  exact ⟨hstep, ⟨hpa, hpk, hia, hik, hcr, hsg, hst⟩⟩

/-- **A `DELEGATECALL` node, on any derivation**: as `call_node`, for the frame `dcallPrep`
computes (the callee's code run in the caller's context, no value transfer). -/
theorem delegatecall_node {sevm : Sevm} {c : PCfg} {cp : CallPrep} {cevm : Evm}
    (hag : PAgree c) (hat : Ninst.At sevm.code c.pc (.exec .delegatecall))
    (hp : dcallPrep sevm c.devm c.adrs c.acs = some cp)
    (he : frameEnterS cp.f c.acs = .run cevm) :
    Evm.step ⟨c.pc, sevm, c.devm⟩ = .spawn cp.f (.call cp.p cp.oi cp.os) (c.pc + 1) ∧
      cp.f.enter = .run cevm ∧ cevm.pc = 0 ∧
      PAgree (childCfg cevm cp.f c.keys cp.adrs c.stor c.acs) ∧ PrepFacts c cp :=
  let ⟨hstep, hF⟩ := dcallPrep_node_facts hag hp
  let ⟨h1, h2, h3, h4⟩ := spawn_node hag hat hstep hF he
  ⟨h1, h2, h3, h4, hF⟩

/-- A reverted or halted call child settles to a machine with an error, the world
rolled back to the frame's message world. -/
theorem frame_settle_error {f : Frame} {e : EvmError} {d : Devm} (hcr : f.isCreate = false)
    (hsg : f.inner.benv.stat.rules.stateGas = none)
    (hk : e = .revert ∨ ∃ r, e = .halt r) :
    ∃ child, f.settle (.error (e, d)) = .ok child ∧ child.error.isSome = true ∧
      child.state = f.inner.benv.state := by
  rcases hk with rfl | ⟨r, rfl⟩
  · refine ⟨(d.withError (some .revert)).rollback f.inner.benv.state
      f.inner.tenv.transientStorage, ?_, rfl, rfl⟩
    simp [Frame.settle, Frame.settleMsg, hcr, executeCode.handleErrorWith, hsg,
      executeCode.handleError, processMessage.settle, bind, Except.bind]
    intro h; cases h
  · refine ⟨(let evm := d.withGasLeft 0
      evm.setMeta {evm.meta with output := [], error := some (.halt r)}).rollback
      f.inner.benv.state f.inner.tenv.transientStorage, ?_, rfl, rfl⟩
    simp [Frame.settle, Frame.settleMsg, hcr, executeCode.handleErrorWith, hsg,
      executeCode.handleError, processMessage.settle, bind, Except.bind]
    intro h; cases h

/-- A failed child: the parent resumes with its own shadows (the child's world was rolled
back to the parent's, and its accessed sets are dropped). -/
theorem resume_agree_error_of {c : PCfg} {cp : CallPrep} {child d : Devm}
    (hag : PAgree c) (hF : PrepFacts c cp)
    (hce : child.error.isSome = true) (hst : child.state = cp.f.inner.benv.state)
    (hr : resumeCallB cp.p cp.oi cp.os (.ok child) = some d) :
    PAgree ⟨c.pc + 1, d, c.keys, cp.adrs, c.stor, c.acs⟩ := by
  obtain ⟨hda, hdk⟩ := resumeCallB_acc hr
  have hds : d.state = c.devm.state := (resumeCallB_state hr).trans (hst.trans hF.state)
  refine ⟨fun x => ?_, fun a => ?_, fun a k => ?_, fun a => ?_⟩
  · show x ∈ d.accessedStorageKeys ↔ x ∈ c.keys
    rw [hdk x, hce, hF.keys]; simp only [Bool.true_eq_false, false_and, or_false]; exact hag.1 x
  · show a ∈ d.accessedAddresses ↔ a ∈ cp.adrs
    rw [hda a, hce]; simp only [Bool.true_eq_false, false_and, or_false]; exact hF.adrs a
  · show storOf d.state a k = lookupS c.stor a k
    rw [hds]; exact hag.2.2.1 a k
  · show acctView (d.state.get a) = lookupA c.acs a
    rw [hds]; exact hag.2.2.2 a

/-- A successful child whose world and accessed sets the shadows describe. -/
theorem resume_agree_ok_of {c : PCfg} {cp : CallPrep} {child d : Devm}
    {ckeys : List (Adr × B256)} {cadrs : List Adr} {cstor : StorShadow} {cacs : AcctShadow}
    (hag : PAgree c) (hF : PrepFacts c cp)
    (hce : child.error.isSome = false) (hca : ChildAgree child ckeys cadrs cstor cacs)
    (hr : resumeCallB cp.p cp.oi cp.os (.ok child) = some d) :
    PAgree ⟨c.pc + 1, d, c.keys ++ ckeys, cp.adrs ++ cadrs, cstor, cacs⟩ := by
  obtain ⟨hda, hdk⟩ := resumeCallB_acc hr
  refine ⟨fun x => ?_, fun a => ?_, fun a k => ?_, fun a => ?_⟩
  · show x ∈ d.accessedStorageKeys ↔ x ∈ c.keys ++ ckeys
    rw [hdk x, hce, hF.keys, show x ∈ c.devm.accessedStorageKeys ↔ x ∈ c.keys from hag.1 x,
      hca.2.1 x, List.mem_append]
    simp
  · show a ∈ d.accessedAddresses ↔ a ∈ cp.adrs ++ cadrs
    rw [hda a, hce, hF.adrs a, hca.1 a, List.mem_append]
    simp
  · show storOf d.state a k = lookupS cstor a k
    rw [resumeCallB_state hr]; exact hca.2.2.1 a k
  · show acctView (d.state.get a) = lookupA cacs a
    rw [resumeCallB_state hr]; exact hca.2.2.2 a

/-- A failed child: the parent resumes with its own shadows (`resume_agree_error_of` for a
`STATICCALL`). -/
theorem resume_agree_error {sevm : Sevm} {c : PCfg} {cp : CallPrep} {child d : Devm}
    (hag : PAgree c) (hp : scallPrep sevm c.devm c.adrs c.acs = some cp)
    (hce : child.error.isSome = true) (hst : child.state = cp.f.inner.benv.state)
    (hr : resumeCallB cp.p cp.oi cp.os (.ok child) = some d) :
    PAgree ⟨c.pc + 1, d, c.keys, cp.adrs, c.stor, c.acs⟩ :=
  resume_agree_error_of hag (scallPrep_node_facts hag hp).2 hce hst hr

/-- A successful child whose world and accessed sets the shadows describe
(`resume_agree_ok_of` for a `STATICCALL`). -/
theorem resume_agree_ok {sevm : Sevm} {c : PCfg} {cp : CallPrep} {child d : Devm}
    {ckeys : List (Adr × B256)} {cadrs : List Adr} {cstor : StorShadow} {cacs : AcctShadow}
    (hag : PAgree c) (hp : scallPrep sevm c.devm c.adrs c.acs = some cp)
    (hce : child.error.isSome = false) (hca : ChildAgree child ckeys cadrs cstor cacs)
    (hr : resumeCallB cp.p cp.oi cp.os (.ok child) = some d) :
    PAgree ⟨c.pc + 1, d, c.keys ++ ckeys, cp.adrs ++ cadrs, cstor, cacs⟩ :=
  resume_agree_ok_of hag (scallPrep_node_facts hag hp).2 hce hca hr

/-- A failed (reverted or halted) call child settles to a machine with an error, the world
rolled back to the frame's message world (`frame_settle_error` for a prepared frame). -/
theorem PrepFacts.settle_error {c : PCfg} {cp : CallPrep} {e : EvmError} {d : Devm}
    (hF : PrepFacts c cp) (hk : e = .revert ∨ ∃ r, e = .halt r) :
    ∃ child, cp.f.settle (.error (e, d)) = .ok child ∧ child.error.isSome = true ∧
      child.state = cp.f.inner.benv.state :=
  frame_settle_error hF.create hF.stateGas hk

/-- A successful call child settles to itself (`frame_settle_ok` for a prepared frame). -/
theorem PrepFacts.settle_ok {c : PCfg} {cp : CallPrep} {post : Devm}
    (hF : PrepFacts c cp) (he : post.error = none) : cp.f.settle (.ok post) = .ok post :=
  frame_settle_ok hF.create hF.stateGas he

/-- An agreeing configuration's shadows describe its machine as a child. -/
theorem childAgree_of_pagree {c : PCfg} (h : PAgree c) :
    ChildAgree c.devm c.keys c.adrs c.stor c.acs :=
  ⟨h.2.1, h.1, h.2.2.1, h.2.2.2⟩

/-! ## Chains -/

/-- Two nodes of one same-frame chain are comparable. -/
theorem parentPrefix_total {a x b : Exec.Deriv} (hx : ParentPrefix a x) (hb : ParentPrefix a b) :
    ParentPrefix x b ∨ ParentPrefix b x := by
  induction hx generalizing b with
  | refl => exact .inl hb
  | step head rest ih =>
    cases hb with
    | refl => exact .inr (.step head rest)
    | step head' rest' =>
      have := Jaune.Exec.Deriv.ParentStep.unique head head'
      subst this
      exact ih rest'

/-- A frame whose chain executes no `KECCAK256` avoids every slot with its hashes. -/
theorem hashAvoid_of_noKeccak {F : Exec.Deriv} {code : ByteArray} {slot : B256}
    (hcode : F.sevm.code = code) (h : ∀ x, ParentPrefix F x → NoKeccakAt code x.pc) :
    Blanc.LockExclusion.HashAvoid slot F := by
  intro x y hx _ hat
  rw [Blanc.Exec.Deriv.ParentPrefix.sevm_eq hx, hcode] at hat
  exact absurd hat (h x hx)

/-- **Trace-local hash avoidance from a walk.**  A frame whose same-frame chain satisfies
`.avoid slot` (every `KECCAK256` it executes leaves a digest other than `slot`) is
`HashAvoid slot`. -/
theorem hashAvoid_of_hashOK {F : Exec.Deriv} {code : ByteArray} {slot : B256}
    (hcode : F.sevm.code = code)
    (h : ∀ x, ParentPrefix F x → (HashPol.avoid slot).NodeOK code x) :
    Blanc.LockExclusion.HashAvoid slot F := by
  intro x y hx hy hat
  rw [Blanc.Exec.Deriv.ParentPrefix.sevm_eq hx, hcode] at hat
  exact h x hx hat y hy

/-! ## Controls: the hash policy bites at `KECCAK256`

The code `KECCAK256` alone, at a machine with `0 0` on the stack and gas: the walk stops
under `.refuse`, and under `.avoid slot` it runs exactly when the digest of the empty input
is not `slot`. -/

/-- The one-instruction code `KECCAK256`. -/
def keccakCode : ByteArray := ⟨#[0x20]⟩

/-- Its tries. -/
def keccakTries : CodeTries keccakCode 1 :=
  CodeTries.ofCode keccakCode 1 (by decide) (by decide)

/-- A machine about to hash the empty input, with gas. -/
def keccakStart : PCfg :=
  ⟨0, (default : Devm).setMach ⟨[0, 0], (default : Devm).memory, 1000, (default : Devm).stateGas⟩,
    [], [], [], []⟩

/-- The walk step continued. -/
def PRes.isCont : PRes → Bool
  | .cont _ => true
  | _ => false

theorem hashPol_bites :
    (pstepH .refuse keccakTries default keccakStart).isCont = false ∧
    (pstepH (.avoid 0) keccakTries default keccakStart).isCont = true ∧
    (pstepH (.avoid (Bytes.keccak [])) keccakTries default keccakStart).isCont = false := by
  refine ⟨?_, ?_, ?_⟩ <;> decide +kernel

end Blanc.Lift.NodeWalk
