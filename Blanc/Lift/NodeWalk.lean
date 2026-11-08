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

Nothing here is contract-specific.
-/

namespace Blanc.Lift.NodeWalk

open Jaune Blanc.Lift Blanc.Lift.Witness
open Jaune.Exec.Deriv (ParentStep ParentPrefix)

/-! ## One step, any derivation -/

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

/-- The bytes an instruction occupies. -/
def instBytes : Inst → Bytes
  | .next n => Ninst.toBytes n
  | .jump j => [j.toUInt8]
  | .last l => [l.toUInt8]

/-- The instruction at `pc`: decoded from the trie window by Jaune's decoder and checked
against the trie bytes. -/
def decodeT (d : Nat) (t : LTrie UInt8) (pc : Nat) : Option Inst :=
  match (ByteArray.mk (windowT d t pc)).getInst 0 with
  | some i => if bytesAtT d t pc (instBytes i) then some i else none
  | none => none

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

/-- `SELFBALANCE` with the balance read from the account shadow (no EIP-7928 read set). -/
def selfbalanceP (sevm : Sevm) (c : PCfg) : Option Devm :=
  if sevm.benvStat.rules.op.selfBalance && sevm.benvStat.rules.bal.isNone then
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
    try (split at h <;> simp_all only [↓reduceIte])
    all_goals (obtain ⟨-, he⟩ := Step.run_ofExecution.mp h; rw [← he]; rfl)

/-! ## Walks over derivation nodes -/

/-- The derivation node `x` sits at the configuration `c` of a frame running `sevm`. -/
def NodeAt (sevm : Sevm) (c : PCfg) (x : Exec.Deriv) : Prop :=
  x.pc = c.pc ∧ x.sevm = sevm ∧ x.devm = c.devm

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

/-- The walk configuration a frame entered with shadows starts at. -/
def childCfg (cevm : Evm) (f : Frame) (keys : List (Adr × B256)) (adrs : List Adr)
    (stor : StorShadow) (acs : AcctShadow) : PCfg :=
  ⟨cevm.pc, cevm.dyna, keys, adrs, storTransfer f.inner stor acs, acsTransfer f.inner acs⟩

/-- `CALL` up to its spawn at a walk configuration (`callPrep` at its witness-engine
configuration). -/
def callPrepP (sevm : Sevm) (c : PCfg) : Option CallPrep := callPrep sevm (c.cfg .undefined)

/-! ## Chains -/

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
