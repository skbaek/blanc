-- Semantics.lean : formalized semantics of the EVM and Blanc

import Blanc.Basic
import Jaune.Hash
import Jaune.Sufficiency



def Rinst.toB8 : Rinst → B8
  | add          => 0x01
  | mul          => 0x02
  | sub          => 0x03
  | div          => 0x04
  | sdiv         => 0x05
  | mod          => 0x06
  | smod         => 0x07
  | addmod       => 0x08
  | mulmod       => 0x09
  | exp          => 0x0A
  | signextend   => 0x0B
  | lt           => 0x10
  | gt           => 0x11
  | slt          => 0x12
  | sgt          => 0x13
  | eq           => 0x14
  | iszero       => 0x15
  | and          => 0x16
  | or           => 0x17
  | xor          => 0x18
  | not          => 0x19
  | byte         => 0x1A
  | shl          => 0x1B
  | shr          => 0x1C
  | sar          => 0x1D
  | clz          => 0x1E
  | kec          => 0x20
  | address      => 0x30
  | balance      => 0x31
  | origin       => 0x32
  | caller       => 0x33
  | callvalue    => 0x34
  | calldataload => 0x35
  | calldatasize => 0x36
  | calldatacopy => 0x37
  | codesize     => 0x38
  | codecopy     => 0x39
  | gasprice     => 0x3A
  | extcodesize  => 0x3B
  | extcodecopy  => 0x3C
  | retdatasize  => 0x3D
  | retdatacopy  => 0x3E
  | extcodehash  => 0x3F
  | blockhash    => 0x40
  | coinbase     => 0x41
  | timestamp    => 0x42
  | number       => 0x43
  | prevrandao   => 0x44
  | gaslimit     => 0x45
  | chainid      => 0x46
  | selfbalance  => 0x47
  | basefee      => 0x48
  | blobhash     => 0x49
  | blobbasefee  => 0x4A
  | pop          => 0x50
  | mload        => 0x51
  | mstore       => 0x52
  | mstore8      => 0x53
  | sload        => 0x54
  | sstore       => 0x55
  | pc           => 0x58
  | msize        => 0x59
  | gas          => 0x5A
  | tload        => 0x5C
  | tstore       => 0x5D
  | mcopy        => 0x5E
  | dup n        => 0x80 + n.val.toUInt8
  | swap n       => 0x90 + n.val.toUInt8
  | log n        => 0xA0 + n.val.toUInt8

abbrev Stack : Type := List B256

def Stack.Push (x y xy : Stack) : Prop := x <++ xy ++> y
def Stack.Pop (x xy y : Stack) : Prop := x <++ xy ++> y

inductive Func : Type
  | branch : Func → Func → Func
  | last : Linst → Func
  | next : Ninst → Func → Func
  | call : Nat → Func

structure Prog : Type where
  (main : Func)
  (aux : List Func)

def Jinst.Run (evm : Evm) :
    Jinst → Except (String × Devm) (Nat × Devm) → Prop :=
  λ j ex => j.run evm = ex

def Linst.Run (sevm : Sevm) (devm : Devm) : Linst → Execution → Prop :=
  λ l ex => l.run sevm devm = ex

def Xlot : Type := Option (Evm × Execution)

/-- Fieldwise relations used to assemble the canonical `Devm.Rel` frames. -/
structure Devm.Rels : Type where
  (stack : List B256 → List B256 → Prop)
  (memory : Mem → Mem → Prop)
  (gasLeft : Nat → Nat → Prop)
  (logs : List Log → List Log → Prop)
  (refundCounter : Int → Int → Prop)
  (output : B8L → B8L → Prop)
  (accountsToDelete : AdrSet → AdrSet → Prop)
  (returnData : B8L → B8L → Prop)
  (error : Option String → Option String → Prop)
  (accessedAddresses : AdrSet → AdrSet → Prop)
  (accessedStorageKeys : KeySet → KeySet → Prop)
  (state : State → State → Prop)
  (createdAccounts : AdrSet → AdrSet → Prop)
  (transientStorage : Tra → Tra → Prop)

/-- Canonical relation between dynamic EVM states, assembled field by field. -/
structure Devm.Rel (rels : Devm.Rels) (devm devm' : Devm) : Prop where
  (stack : rels.stack devm.stack devm'.stack)
  (memory : rels.memory devm.memory devm'.memory)
  (gasLeft : rels.gasLeft devm.gasLeft devm'.gasLeft)
  (logs : rels.logs devm.logs devm'.logs)
  (refundCounter : rels.refundCounter devm.refundCounter devm'.refundCounter)
  (output : rels.output devm.output devm'.output)
  ( accountsToDelete :
    rels.accountsToDelete devm.accountsToDelete devm'.accountsToDelete)
  (returnData : rels.returnData devm.returnData devm'.returnData)
  (error : rels.error devm.error devm'.error)
  ( accessedAddresses :
    rels.accessedAddresses devm.accessedAddresses devm'.accessedAddresses )
  ( accessedStorageKeys :
    rels.accessedStorageKeys devm.accessedStorageKeys devm'.accessedStorageKeys )
  (state : rels.state devm.state devm'.state)
  ( createdAccounts :
    rels.createdAccounts devm.createdAccounts devm'.createdAccounts )
  ( transientStorage :
    rels.transientStorage devm.transientStorage devm'.transientStorage )

def Devm.Rels.eq : Devm.Rels :=
  {
    stack := _root_.Eq,
    memory := _root_.Eq,
    gasLeft := _root_.Eq,
    logs := _root_.Eq,
    refundCounter := _root_.Eq,
    output := _root_.Eq,
    accountsToDelete := _root_.Eq,
    returnData := _root_.Eq,
    error := _root_.Eq,
    accessedAddresses := _root_.Eq,
    accessedStorageKeys := _root_.Eq,
    state := _root_.Eq,
    createdAccounts := _root_.Eq,
    transientStorage := _root_.Eq
  }

def Devm.Burn : Devm → Devm → Prop :=
  Rel {
    Rels.eq with
    gasLeft := (· ≥ · )
  }


def Devm.PopBurn (xs : List B256) : Devm → Devm → Prop :=
  Rel {
    Rels.eq with
    stack := Stack.Pop xs
    gasLeft := (· ≥ ·)
  }

def Linst.At (code : ByteArray) (pc : Nat) (l : Linst) : Prop := code.getInst pc = some (.last l)
def Ninst.At (code : ByteArray) (pc : Nat) (n : Ninst) : Prop := code.getInst pc = some (.next n)
def Jinst.At (code : ByteArray) (pc : Nat) (j : Jinst) : Prop := code.getInst pc = some (.jump j)
def Rinst.At (code : ByteArray) (pc : Nat) (r : Rinst) : Prop := code.getInst pc = some (.next (.reg r))
def Xinst.At (code : ByteArray) (pc : Nat) (x : Xinst) : Prop := code.getInst pc = some (.next (.exec x))

def Except.Split {ξ υ ζ : Type}
    (e : Except ξ υ) (e' : Except ξ ζ) (q : υ → Prop) : Prop :=
  (∃ x, e = .error x ∧ e' = .error x) ∨ (∃ y : υ, e = .ok y ∧ q y)

/-! ### The recursion-facing relational layer.

Each former hand-maintained mirror is now a thin, non-recursive wrapper: an
equation about the flattened frame/step functions of Jaune.  `RunFrame` is the
generic frame relation; the named mirrors specialize it so that the statements
consumed by `Common.lean` and `Solvent.lean` keep their current shape. -/

def RunFrame (f : Frame) (xl : Xlot)
    (r : Except (String × State × AdrSet × Tra) Devm) : Prop :=
  match f.enter with
  | .done r' => xl = .none ∧ r = r'
  | .run evm => ∃ raw, xl = .some ⟨evm, raw⟩ ∧ r = f.settle raw

def ExecuteCode (msg : Msg) (xl : Xlot)
    (ex : Except (String × State × AdrSet × Tra) Devm) : Prop :=
  match executeCode.enter msg with
  | .inl evm => ∃ raw, xl = .some ⟨evm, raw⟩ ∧ ex = executeCode.handleError raw
  | .inr raw => xl = .none ∧ ex = executeCode.handleError raw

def ProcessMessage (msg : Msg) (xl : Xlot)
    (ex : Except (String × State × AdrSet × Tra) Devm) : Prop :=
  RunFrame (Frame.ofCall msg) xl ex

def ProcessCreateMessage (msg : Msg) (xl : Xlot)
    (ex : Except (String × State × AdrSet × Tra) Devm) : Prop :=
  RunFrame (Frame.ofCreate msg) xl ex

def XStep.Run (s : XStep) (xl : Xlot) (ex : Execution) : Prop :=
  match s with
  | .done ex' => xl = .none ∧ ex = ex'
  | .spawn f rsm => ∃ r, RunFrame f xl r ∧ ex = rsm.run r

def GenericCreate (sevm : Sevm) (devm : Devm) (endowment : B256) (newAddress : Adr)
    (memoryIndex memorySize : Nat) (xl : Xlot) (ex : Execution) : Prop :=
  XStep.Run
    (genericCreate.step sevm devm endowment newAddress memoryIndex memorySize)
    xl ex

def GenericCall
    (sevm: Sevm)
    (devm: Devm)
    (gas: Nat)
    (value: B256)
    (caller: Adr)
    (target: Adr)
    (codeAddress: Adr)
    (shouldTransferValue: Bool)
    (isStaticcall: Bool)
    (input_index:  Nat)
    (input_size:   Nat)
    (output_index: Nat)
    (output_size:  Nat)
    (code : ByteArray)
    (disablePrecompiles: Bool)
    (xl : Xlot)
    (ex : Execution) : Prop :=
  XStep.Run
    (genericCall.step sevm devm gas value caller target codeAddress
      shouldTransferValue isStaticcall input_index input_size
      output_index output_size code disablePrecompiles)
    xl ex

def Xinst.Run (sevm : Sevm) (devm : Devm) :
    Xinst → Xlot → Execution → Prop :=
  fun x xl ex => XStep.Run (Xinst.step sevm devm x) xl ex

def Step.Run (s : Step) (xl : Xlot) (ex : Execution) : Prop :=
  match s with
  | .halt ex' => xl = .none ∧ ex = ex'
  | .cont _ devm => xl = .none ∧ ex = .ok devm
  | .spawn f rsm _ => ∃ r, RunFrame f xl r ∧ ex = rsm.run r

def Ninst.Run' (pc : Nat) (sevm : Sevm) (devm : Devm)
    (n : Ninst) (xl : Xlot) (ex : Execution) : Prop :=
  Step.Run (Ninst.step ⟨pc, sevm, devm⟩ n) xl ex

/-- A childless step outcome built from a plain `Execution` carries exactly
that result.  This is the workhorse for the non-spawning instruction kinds. -/
lemma Step.run_ofExecution {pc : Nat} {e ex : Execution} {xl : Xlot} :
    Step.Run (Step.ofExecution pc e) xl ex ↔ (xl = .none ∧ ex = e) := by
  unfold Step.ofExecution
  split <;> simp [Step.Run]

lemma Step.ofExecution_ne_spawn {pc : Nat} {ex : Execution}
    {f : Frame} {rsm : Resume} {pc' : Nat} :
    Step.ofExecution pc ex ≠ .spawn f rsm pc' := by
  cases ex <;> simp [Step.ofExecution]

lemma Step.ofJump_ne_spawn {j : Except (String × Devm) (Nat × Devm)}
    {f : Frame} {rsm : Resume} {pc' : Nat} :
    Step.ofJump j ≠ .spawn f rsm pc' := by
  cases j <;> simp [Step.ofJump]

lemma XStep.toStep_spawn {pc : Nat} {s : XStep}
    {f : Frame} {rsm : Resume} {pc' : Nat}
    (h : XStep.toStep pc s = .spawn f rsm pc') : s = .spawn f rsm := by
  cases s
  · cases Step.ofExecution_ne_spawn h
  · cases h; rfl

/-- Wrapping a call-type step outcome for the driver does not change what it
relates: the program counter it records is only consulted after the child
returns. -/
lemma XStep.run_toStep {pc : Nat} {s : XStep} {xl : Xlot} {ex : Execution} :
    Step.Run (XStep.toStep pc s) xl ex ↔ XStep.Run s xl ex := by
  cases s with
  | done e => simp only [XStep.toStep, XStep.Run, Step.run_ofExecution]
  | spawn f rsm => exact Iff.rfl

/-- A jump's step outcome carries the jump's own result, whichever branch it
took, and never suspends. -/
lemma Step.run_ofJump {j : Except (String × Devm) (Nat × Devm)} {xl : Xlot}
    {ex : Execution} (h : Step.Run (Step.ofJump j) xl ex) :
    xl = .none ∧
      ((∃ e, j = .error e ∧ ex = .error e) ∨
        (∃ pc' d, j = .ok ⟨pc', d⟩ ∧ ex = .ok d)) := by
  rcases j with e | ⟨pc', devm'⟩ <;> simp only [Step.ofJump, Step.Run] at h <;>
    obtain ⟨rfl, rfl⟩ := h
  · exact ⟨rfl, Or.inl ⟨e, rfl, rfl⟩⟩
  · exact ⟨rfl, Or.inr ⟨pc', devm', rfl, rfl⟩⟩

lemma Step.ofExecution_cont {pc pc' : Nat} {e : Execution} {devm' : Devm}
    (h : Step.ofExecution pc e = .cont pc' devm') : pc' = pc ∧ e = .ok devm' := by
  unfold Step.ofExecution at h
  split at h <;> cases h
  exact ⟨rfl, rfl⟩

lemma Step.ofExecution_ne_halt_ok {pc : Nat} {e : Execution} {devm' : Devm} :
    Step.ofExecution pc e ≠ .halt (.ok devm') := by
  unfold Step.ofExecution
  split <;> simp

lemma Step.ofJump_cont {j : Except (String × Devm) (Nat × Devm)}
    {pc' : Nat} {devm' : Devm} (h : Step.ofJump j = .cont pc' devm') :
    j = .ok ⟨pc', devm'⟩ := by
  unfold Step.ofJump at h
  split at h <;> cases h
  rfl

lemma Step.ofJump_ne_halt_ok {j : Except (String × Devm) (Nat × Devm)}
    {devm' : Devm} : Step.ofJump j ≠ .halt (.ok devm') := by
  unfold Step.ofJump
  split <;> simp

/-- Every step outcome of an ordinary instruction resumes at `pc + n.size`;
the program-counter arithmetic that used to live in `exec` now lives in
`Ninst.step`, so it is recovered here once. -/
lemma Ninst.step_cont_pc {evm : Evm} {n : Ninst} {pc' : Nat} {devm' : Devm}
    (h : Ninst.step evm n = .cont pc' devm') : pc' = evm.pc + n.size := by
  unfold Ninst.step at h
  rcases n with r | x | ⟨xs, hxs⟩ <;> simp only [] at h
  · exact (Step.ofExecution_cont h).1
  · unfold XStep.toStep at h
    split at h
    · exact (Step.ofExecution_cont h).1
    · cases h
  · exact (Step.ofExecution_cont h).1

lemma Ninst.step_spawn_pc {evm : Evm} {n : Ninst}
    {f : Frame} {rsm : Resume} {pc' : Nat}
    (h : Ninst.step evm n = .spawn f rsm pc') : pc' = evm.pc + n.size := by
  unfold Ninst.step at h
  rcases n with r | x | ⟨xs, hxs⟩ <;> simp only [] at h
  · cases Step.ofExecution_ne_spawn h
  · unfold XStep.toStep at h
    split at h
    · cases Step.ofExecution_ne_spawn h
    · cases h; rfl
  · cases Step.ofExecution_ne_spawn h

lemma Ninst.step_ne_halt_ok {evm : Evm} {n : Ninst} {devm' : Devm} :
    Ninst.step evm n ≠ .halt (.ok devm') := by
  unfold Ninst.step
  rcases n with r | x | ⟨xs, hxs⟩ <;> simp only []
  · exact Step.ofExecution_ne_halt_ok
  · unfold XStep.toStep
    split
    · exact Step.ofExecution_ne_halt_ok
    · simp
  · exact Step.ofExecution_ne_halt_ok

/-! ### The three branches of `Ninst.step`, made explicit. -/

lemma Ninst.step_reg {evm : Evm} {r : Rinst} :
    Ninst.step evm (.reg r) = Step.ofExecution (evm.pc + 1) (r.run evm) := rfl

lemma Ninst.step_push {evm : Evm} {xs : B8L} {le : xs.length ≤ 32} :
    Ninst.step evm (.push xs le) =
      Step.ofExecution (evm.pc + xs.length + 1)
        (do let d ← chargeGas (if xs = [] then gBase else gVerylow) evm.dyna
            d.push xs.toB256) := rfl

lemma Ninst.step_exec {evm : Evm} {x : Xinst} :
    Ninst.step evm (.exec x) =
      XStep.toStep (evm.pc + 1) (Xinst.step evm.sta evm.dyna x) := rfl

/-! ### Introducing frame relations from the frame-entry equation. -/

lemma RunFrame.of_done {f : Frame} {r} (h : f.enter = .done r) :
    RunFrame f .none r := by
  unfold RunFrame; rw [h]; exact ⟨rfl, rfl⟩

lemma RunFrame.of_run {f : Frame} {cevm : Evm} {raw : Execution}
    (h : f.enter = .run cevm) :
    RunFrame f (.some ⟨cevm, raw⟩) (f.settle raw) := by
  unfold RunFrame; rw [h]; exact ⟨raw, rfl, rfl⟩

/-- Entering a frame preserves the frame's own depth. -/
lemma Frame.enter_run_depth {f : Frame} {cevm : Evm}
    (h : f.enter = .run cevm) : cevm.sta.depth = f.inner.depth := by
  unfold Frame.enter at h
  split at h
  · cases h
  · rename_i benv hbenv
    split at h
    · cases h
      rename_i heq
      unfold executeCode.enter at heq
      simp only [] at heq
      split at heq
      · cases heq; rfl
      · split at heq
        · cases heq
        · cases heq; rfl
    · cases h

/-- A filled slot means the frame was actually entered, and the suspended
machine is exactly the one `Frame.enter` produced. -/
lemma RunFrame.some_inv {f : Frame} {evm_ : Evm} {exn_ : Execution} {r}
    (run : RunFrame f (.some ⟨evm_, exn_⟩) r) :
    f.enter = .run evm_ ∧ r = f.settle exn_ := by
  unfold RunFrame at run
  rcases henter : f.enter with r' | cevm <;> rw [henter] at run
  · cases run.1
  · rcases run with ⟨raw, hxl, hr⟩
    cases hxl
    exact ⟨rfl, hr⟩

/-- The depth of a suspended child frame, read off the slot. -/
lemma RunFrame.depth_eq {f : Frame} {evm_ : Evm} {exn_ : Execution} {r}
    (run : RunFrame f (.some ⟨evm_, exn_⟩) r) :
    evm_.sta.depth = f.inner.depth :=
  Frame.enter_run_depth (RunFrame.some_inv run).1

/-- A filled slot on a call-type instruction means the step spawned, and the
slot holds that spawn's child frame. -/
lemma XStep.Run.some_inv {s : XStep} {evm_ : Evm} {exn_ : Execution} {ex : Execution}
    (run : XStep.Run s (.some ⟨evm_, exn_⟩) ex) :
    ∃ f rsm, s = .spawn f rsm ∧ f.enter = .run evm_ ∧ ex = rsm.run (f.settle exn_) := by
  unfold XStep.Run at run
  cases s with
  | done ex' => cases run.1
  | spawn f rsm =>
    rcases run with ⟨r, hframe, hex⟩
    obtain ⟨henter, hr⟩ := RunFrame.some_inv hframe
    exact ⟨f, rsm, rfl, henter, by rw [hex, hr]⟩

lemma Step.Run.some_inv {s : Step} {evm_ : Evm} {exn_ : Execution} {ex : Execution}
    (run : Step.Run s (.some ⟨evm_, exn_⟩) ex) :
    ∃ f rsm pc', s = .spawn f rsm pc' ∧ f.enter = .run evm_ ∧
      ex = rsm.run (f.settle exn_) := by
  unfold Step.Run at run
  cases s with
  | halt ex' => cases run.1
  | cont pc devm => cases run.1
  | spawn f rsm pc' =>
    rcases run with ⟨r, hframe, hex⟩
    obtain ⟨henter, hr⟩ := RunFrame.some_inv hframe
    exact ⟨f, rsm, pc', rfl, henter, by rw [hex, hr]⟩

/-- Only a call-type instruction spawns, and it delegates to `Xinst.step`. -/
lemma Ninst.step_spawn_inv {evm : Evm} {n : Ninst}
    {f : Frame} {rsm : Resume} {pc' : Nat}
    (h : Ninst.step evm n = .spawn f rsm pc') :
    ∃ x, n = .exec x ∧ Xinst.step evm.sta evm.dyna x = .spawn f rsm := by
  rcases n with r | x | ⟨xs, hxs⟩
  · rw [Ninst.step_reg] at h; cases Step.ofExecution_ne_spawn h
  · rw [Ninst.step_exec] at h; exact ⟨x, rfl, XStep.toStep_spawn h⟩
  · rw [Ninst.step_push] at h; cases Step.ofExecution_ne_spawn h

/-- The initial machine of an entered code frame is `initEvm` of the message,
whichever decode branch `executeCode.enter` took. -/
lemma executeCode.enter_inl {msg : Msg} {evm : Evm}
    (h : executeCode.enter msg = .inl evm) : evm = initEvm msg := by
  unfold executeCode.enter at h
  split at h
  · cases h; rfl
  · split at h
    · cases h
    · cases h; rfl

/-- Frame entry, inverted: an entered frame transferred value successfully and
then suspends on the initial machine of the transferred message.  This is the
single fact every downstream "what does the child start from?" argument needs. -/
lemma Frame.enter_run_inv {f : Frame} {cevm : Evm} (h : f.enter = .run cevm) :
    ∃ benv, f.inner.benvAfterTransfer = .ok benv ∧
      cevm = initEvm (f.inner.withBenv benv) := by
  unfold Frame.enter at h
  rcases hbenv : f.inner.benvAfterTransfer with e | benv <;> simp only [hbenv] at h
  · cases h
  · refine ⟨benv, rfl, ?_⟩
    rcases henter : executeCode.enter (f.inner.withBenv benv) with evm | raw <;>
      simp only [henter] at h
    · cases h; exact executeCode.enter_inl henter
    · cases h

lemma ExecuteCode.some_inv {msg : Msg} {evm_ : Evm} {exn_ : Execution}
    {ex : Except (String × State × AdrSet × Tra) Devm}
    (run : ExecuteCode msg (.some ⟨evm_, exn_⟩) ex) :
    evm_ = initEvm msg ∧ ex = executeCode.handleError exn_ := by
  unfold ExecuteCode at run
  rcases henter : executeCode.enter msg with evm | raw <;> rw [henter] at run
  · rcases run with ⟨raw, hxl, hex⟩
    cases hxl
    exact ⟨executeCode.enter_inl henter, hex⟩
  · cases run.1

/-- The precompile branch of frame entry runs `executePrecomp` on the initial
machine and produces no child derivation. -/
lemma executeCode.enter_inr {msg : Msg} {raw : Execution}
    (h : executeCode.enter msg = .inr raw) :
    ∃ adr, raw = executePrecomp (initEvm msg) adr := by
  unfold executeCode.enter at h
  split at h
  · cases h
  · rename_i adr _
    split at h
    · cases h; exact ⟨adr, rfl⟩
    · cases h

/-- The frame-independent part of a frame relation: value transfer followed by
code execution, before the frame's own settlement is applied.  Splitting
`RunFrame` into `FrameBody` plus `Frame.settleMsg` is what lets the former
`ProcessMessage`/`ProcessCreateMessage` arguments be phrased once and reused
for both frame kinds. -/
def FrameBody (m : Msg) (xl : Xlot)
    (r : Except (String × State × AdrSet × Tra) Devm) : Prop :=
  match m.benvAfterTransfer with
  | .error e => xl = .none ∧ r = .error e
  | .ok benv => ExecuteCode (m.withBenv benv) xl r

/-- Frame entry is `benvAfterTransfer` followed by `executeCode.enter`, so a
frame relation decomposes into a transfer failure or a code-execution relation
on the transferred message.  This is the bridge that lets every former
`ProcessMessage`/`ProcessCreateMessage` argument be phrased once. -/
lemma RunFrame.decompose {f : Frame} {xl : Xlot}
    {r : Except (String × State × AdrSet × Tra) Devm}
    (run : RunFrame f xl r) :
    (∃ e, f.inner.benvAfterTransfer = .error e ∧ xl = .none ∧
        r = f.settleMsg (.error e)) ∨
    (∃ benv r', f.inner.benvAfterTransfer = .ok benv ∧
        ExecuteCode (f.inner.withBenv benv) xl r' ∧ r = f.settleMsg r') := by
  unfold RunFrame Frame.enter at run
  rcases hbenv : f.inner.benvAfterTransfer with e | benv <;>
    simp only [hbenv] at run
  · exact Or.inl ⟨e, rfl, run.1, run.2⟩
  · rcases henter : executeCode.enter (f.inner.withBenv benv) with evm | raw <;>
      simp only [henter] at run
    · rcases run with ⟨raw, hxl, hr⟩
      exact Or.inr ⟨benv, executeCode.handleError raw, rfl,
        by unfold ExecuteCode; rw [henter]; exact ⟨raw, hxl, rfl⟩, hr⟩
    · exact Or.inr ⟨benv, executeCode.handleError raw, rfl,
        by unfold ExecuteCode; rw [henter]; exact ⟨run.1, rfl⟩, run.2⟩

/-- `RunFrame` is exactly `FrameBody` composed with the frame's settlement. -/
lemma RunFrame.iff_settleMsg {f : Frame} {xl : Xlot}
    {r : Except (String × State × AdrSet × Tra) Devm} :
    RunFrame f xl r ↔ ∃ r0, FrameBody f.inner xl r0 ∧ r = f.settleMsg r0 := by
  constructor
  · intro run
    rcases RunFrame.decompose run with ⟨e, hbenv, hxl, hr⟩ | ⟨benv, r0, hbenv, hec, hr⟩
    · exact ⟨.error e, by unfold FrameBody; rw [hbenv]; exact ⟨hxl, rfl⟩, hr⟩
    · exact ⟨r0, by unfold FrameBody; rw [hbenv]; exact hec, hr⟩
  · rintro ⟨r0, hbody, rfl⟩
    unfold FrameBody at hbody
    unfold RunFrame Frame.enter
    rcases hbenv : f.inner.benvAfterTransfer with e | benv <;>
      simp only [hbenv] at hbody ⊢
    · exact ⟨hbody.1, by rw [hbody.2]⟩
    · unfold ExecuteCode at hbody
      rcases henter : executeCode.enter (f.inner.withBenv benv) with evm | raw <;>
        simp only [henter] at hbody ⊢
      · rcases hbody with ⟨raw, hxl, hr0⟩
        exact ⟨raw, hxl, by rw [hr0]; rfl⟩
      · exact ⟨hbody.1, by rw [hbody.2]; rfl⟩

lemma ProcessMessage.iff_body {msg : Msg} {xl : Xlot}
    {r : Except (String × State × AdrSet × Tra) Devm} :
    ProcessMessage msg xl r ↔
      ∃ r0, FrameBody msg xl r0 ∧ r = processMessage.settle msg r0 :=
  RunFrame.iff_settleMsg

lemma ProcessCreateMessage.iff_processMessage {msg : Msg} {xl : Xlot}
    {r : Except (String × State × AdrSet × Tra) Devm} :
    ProcessCreateMessage msg xl r ↔
      ∃ r', ProcessMessage (processCreateMessage.msg msg) xl r' ∧
        r = processCreateMessage.settle msg r' := by
  rw [ProcessCreateMessage, RunFrame.iff_settleMsg]
  constructor
  · rintro ⟨r0, hbody, rfl⟩
    exact ⟨_, ProcessMessage.iff_body.mpr ⟨r0, hbody, rfl⟩, rfl⟩
  · rintro ⟨r', hpm, rfl⟩
    obtain ⟨r0, hbody, rfl⟩ := ProcessMessage.iff_body.mp hpm
    exact ⟨r0, hbody, rfl⟩


/-! ### Decode bridge.

`Evm.step` dispatches on the instruction at the program counter, so each of the
four `*.At` decode predicates pins the driver's step outcome.  These four
equations are what let the former per-instruction relational reasoning survive
against the single step function. -/

lemma Evm.step_invOp {pc : Nat} {sevm : Sevm} {devm : Devm}
    (h : sevm.code.getInst pc = none) :
    Evm.step ⟨pc, sevm, devm⟩ = .halt (.error ⟨"InvalidOpcode", devm⟩) := by
  unfold Evm.step
  rw [show (Evm.getInst ⟨pc, sevm, devm⟩) = none from h]

lemma Evm.step_next {pc : Nat} {sevm : Sevm} {devm : Devm} {n : Ninst}
    (h : n.At sevm.code pc) :
    Evm.step ⟨pc, sevm, devm⟩ = Ninst.step ⟨pc, sevm, devm⟩ n := by
  unfold Evm.step
  rw [show (Evm.getInst ⟨pc, sevm, devm⟩) = some (.next n) from h]

lemma Evm.step_jump {pc : Nat} {sevm : Sevm} {devm : Devm} {j : Jinst}
    (h : j.At sevm.code pc) :
    Evm.step ⟨pc, sevm, devm⟩ = Step.ofJump (j.run ⟨pc, sevm, devm⟩) := by
  unfold Evm.step
  rw [show (Evm.getInst ⟨pc, sevm, devm⟩) = some (.jump j) from h]

lemma Evm.step_last {pc : Nat} {sevm : Sevm} {devm : Devm} {l : Linst}
    (h : l.At sevm.code pc) :
    Evm.step ⟨pc, sevm, devm⟩ = .halt (l.run sevm devm) := by
  unfold Evm.step
  rw [show (Evm.getInst ⟨pc, sevm, devm⟩) = some (.last l) from h]

/-- Only a call-type instruction spawns a child frame. -/
lemma Evm.step_spawn_inv {pc : Nat} {sevm : Sevm} {devm : Devm}
    {f : Frame} {rsm : Resume} {pc' : Nat}
    (hs : Evm.step ⟨pc, sevm, devm⟩ = .spawn f rsm pc') :
    ∃ x : Xinst, Xinst.At sevm.code pc x ∧
      Xinst.step sevm devm x = .spawn f rsm ∧ pc' = pc + 1 := by
  unfold Evm.step at hs
  split at hs
  · cases hs
  · rename_i n hgi
    rcases n with r | x | ⟨xs, hxs⟩ <;> simp only [Ninst.step] at hs
    · cases Step.ofExecution_ne_spawn hs
    · refine ⟨x, hgi, XStep.toStep_spawn hs, ?_⟩
      unfold XStep.toStep at hs
      split at hs
      · cases Step.ofExecution_ne_spawn hs
      · cases hs; rfl
    · cases Step.ofExecution_ne_spawn hs
  · cases Step.ofJump_ne_spawn hs
  · cases hs

/- Exec pc sevm devm ex is provable iff
    exec ⟨pc, sevm, devm⟩ = ex
   holds (`exec_iff_exec_eq`): with sufficiency proved in Jaune, the total
   `exec` is the executable side of the adequacy bridge, and no fuel appears
   in it.  The relation is the generic derivation tree over the flattened
   driver's step outcomes: every premise other than a sub-derivation is an
   equation about a non-recursive function. -/
inductive Exec : Nat → Sevm → Devm → Execution → Type
  | halt {pc sevm devm ex} :
    Evm.step ⟨pc, sevm, devm⟩ = .halt ex →
    Exec pc sevm devm ex
  | cont {pc sevm devm pc' devm' ex} :
    Evm.step ⟨pc, sevm, devm⟩ = .cont pc' devm' →
    Exec pc' sevm devm' ex →
    Exec pc sevm devm ex
  | doneErr {pc sevm devm f rsm pc' r e} :
    Evm.step ⟨pc, sevm, devm⟩ = .spawn f rsm pc' →
    f.enter = .done r →
    rsm.run r = .error e →
    Exec pc sevm devm (.error e)
  | doneOk {pc sevm devm f rsm pc' r devm' ex} :
    Evm.step ⟨pc, sevm, devm⟩ = .spawn f rsm pc' →
    f.enter = .done r →
    rsm.run r = .ok devm' →
    Exec pc' sevm devm' ex →
    Exec pc sevm devm ex
  | runErr {pc sevm devm f rsm pc' cevm raw e} :
    Evm.step ⟨pc, sevm, devm⟩ = .spawn f rsm pc' →
    f.enter = .run cevm →
    Exec cevm.pc cevm.sta cevm.dyna raw →
    rsm.run (f.settle raw) = .error e →
    Exec pc sevm devm (.error e)
  | runOk {pc sevm devm f rsm pc' cevm raw devm' ex} :
    Evm.step ⟨pc, sevm, devm⟩ = .spawn f rsm pc' →
    f.enter = .run cevm →
    Exec cevm.pc cevm.sta cevm.dyna raw →
    rsm.run (f.settle raw) = .ok devm' →
    Exec pc' sevm devm' ex →
    Exec pc sevm devm ex

def Xlot.Filled : Xlot → Prop
  | .none => True
  | .some ⟨evm, exn⟩ => Nonempty (Exec evm.pc evm.sta evm.dyna exn)

/-! ### Inversion against the step outcome.

A derivation is determined at its root by the step outcome, so an equation
pinning that outcome collapses the six-way case analysis.  `halt_inv` is what
replaces the old "wrong instruction kind" branches of every `cases` on `Exec`:
where a proof knows the instruction at `pc` halts, the derivation's result is
that halt value. -/

lemma Exec.halt_inv {pc sevm devm exn ex}
    (cr : Exec pc sevm devm exn)
    (h : Evm.step ⟨pc, sevm, devm⟩ = .halt ex) : exn = ex := by
  cases cr with
  | halt h' => cases h.symm.trans h'; rfl
  | cont h' _ => cases h.symm.trans h'
  | doneErr h' _ _ => cases h.symm.trans h'
  | doneOk h' _ _ _ => cases h.symm.trans h'
  | runErr h' _ _ _ => cases h.symm.trans h'
  | runOk h' _ _ _ _ => cases h.symm.trans h'

/-- A `Linst` at the program counter settles the whole derivation. -/
lemma Exec.last_inv {pc sevm devm exn l}
    (cr : Exec pc sevm devm exn) (h : Linst.At sevm.code pc l) :
    exn = l.run sevm devm :=
  cr.halt_inv (Evm.step_last h)

def Ninst.Run (sevm : Sevm) (devm : Devm) (n : Ninst) (devm' : Devm) : Prop :=
  ∃ xl : Xlot, xl.Filled ∧ ∃ pc, Ninst.Run' pc sevm devm n xl (.ok devm')

inductive Func.Run : List Func → Sevm → Devm → Func → Devm → Prop
  | zero :
    ∀ {fs sevm devm devm' f g devm''},
      Devm.PopBurn [0] devm devm' →
      Func.Run fs sevm devm' f devm'' →
      Func.Run fs sevm devm (branch f g) devm''
  | succ :
    ∀ {fs sevm devm w devm' f g devm_jd devm''},
      w ≠ 0 →
      Devm.PopBurn [w] devm devm' →
      Devm.Burn devm' devm_jd →
      Func.Run fs sevm devm_jd g devm'' →
      Func.Run fs sevm devm (branch f g) devm''
  | last :
    ∀ {fs sevm devm i devm' },
      Linst.Run sevm devm i (.ok devm') →
      Func.Run fs sevm devm (last i) devm'
  | next :
    ∀ {fs sevm devm i devm' f devm''},
      Ninst.Run sevm devm i devm' →
      Func.Run fs sevm devm' f devm'' →
      Func.Run fs sevm devm (next i f) devm''
  | call :
    ∀ {fs sevm devm devm' k f devm''},
      fs[k]? = some f →
      Devm.Burn devm devm' →
      Func.Run fs sevm devm' f devm'' →
      Func.Run fs sevm devm (call k) devm''

def Prog.Run (sevm : Sevm) (devm : Devm) (p : Prog) (devm' : Devm) : Prop :=
  Func.Run (p.main :: p.aux) sevm devm (.call 0) devm'

-------------------------------------------------------------------------------



/- The residue of the fuel-bounded (`Fueled`) reasoning layer.  With
   sufficiency proved in Jaune, fuel never reaches a Blanc statement: these
   three lemmas exist only so that the adequacy bridge between `Exec` and the
   total `exec` can be proved by induction over `execFueled`. -/

namespace Fueled

variable {ε : Type} {α : Type}

lemma ext {x y : Fueled ε α} (h : x.run = y.run) : x = y := h

lemma exhausted_ne_ofExcept {x : Except ε α} :
    (Fueled.exhausted : Fueled ε α) ≠ Fueled.ofExcept x :=
  fun h => nomatch congrArg ExceptT.run h

@[simp] lemma ofExcept_inj {x y : Except ε α} :
    (Fueled.ofExcept x : Fueled ε α) = Fueled.ofExcept y ↔ x = y :=
  ⟨fun h => Option.some.inj (congrArg ExceptT.run h), fun h => by rw [h]⟩

end Fueled

/-! ### Depth side conditions for the strong induction of `Common.lean`.

Every `.spawn` produced by the step functions is depth-guarded, so a child
frame always sits strictly below its parent, and entering a frame preserves
the frame's own depth. -/

lemma genericCall.step_spawn_depth
    {sevm : Sevm} {devm : Devm} {gas : Nat} {value : B256}
    {caller target codeAddress : Adr} {shouldTransferValue isStaticcall : Bool}
    {inputIndex inputSize outputIndex outputSize : Nat} {code : ByteArray}
    {disablePrecompiles : Bool} {f : Frame} {rsm : Resume}
    (hs : genericCall.step sevm devm gas value caller target codeAddress
      shouldTransferValue isStaticcall inputIndex inputSize outputIndex
      outputSize code disablePrecompiles = .spawn f rsm) :
    f.inner.depth < sevm.depth := by
  simp only [genericCall.step, Bind.bind, Except.bind, Pure.pure,
    Except.pure] at hs
  repeat' split at hs
  all_goals simp only [XStep.ofExcept, XStep.spawn.injEq, reduceCtorEq] at hs
  all_goals obtain ⟨rfl, -⟩ := hs
  all_goals simp only [Frame.ofCall, callMsg]
  all_goals omega

lemma genericCreate.step_spawn_depth
    {sevm : Sevm} {devm : Devm} {endowment : B256} {newAddress : Adr}
    {memoryIndex memorySize : Nat} {f : Frame} {rsm : Resume}
    (hs : genericCreate.step sevm devm endowment newAddress memoryIndex
      memorySize = .spawn f rsm) :
    f.inner.depth < sevm.depth := by
  simp only [genericCreate.step, Bind.bind, Except.bind, Except.assert,
    assertDynamic, Pure.pure, Except.pure] at hs
  repeat' split at hs
  all_goals simp only [XStep.ofExcept, XStep.spawn.injEq, reduceCtorEq] at hs
  all_goals obtain ⟨rfl, -⟩ := hs
  all_goals
    simp only [Frame.ofCreate, processCreateMessage.msg, Msg.withBenv,
      createMsg, not_or] at *
  all_goals omega

lemma Xinst.step_spawn_depth {sevm : Sevm} {devm : Devm} {x : Xinst}
    {f : Frame} {rsm : Resume}
    (hs : Xinst.step sevm devm x = .spawn f rsm) :
    f.inner.depth < sevm.depth := by
  cases x <;>
    simp only [Xinst.step, Bind.bind, Except.bind, Except.assert,
      Pure.pure, Except.pure] at hs <;>
    repeat' split at hs
  all_goals simp only [XStep.ofExcept, reduceCtorEq] at hs
  all_goals
    first
      | exact genericCreate.step_spawn_depth hs
      | exact genericCall.step_spawn_depth hs

lemma Ninst.step_spawn_depth {evm : Evm} {n : Ninst}
    {f : Frame} {rsm : Resume} {pc' : Nat}
    (h : Ninst.step evm n = .spawn f rsm pc') : f.inner.depth < evm.sta.depth := by
  obtain ⟨x, _, hx⟩ := Ninst.step_spawn_inv h
  exact Xinst.step_spawn_depth hx

/-- A spawned child frame sits strictly below its parent's depth. -/
lemma Step.spawn_depth_lt {pc : Nat} {sevm : Sevm} {devm : Devm}
    {f : Frame} {rsm : Resume} {pc' : Nat}
    (hs : Evm.step ⟨pc, sevm, devm⟩ = .spawn f rsm pc') :
    f.inner.depth < sevm.depth := by
  unfold Evm.step at hs
  split at hs
  · cases hs
  · rename_i n hgi
    rcases n with r | x | ⟨xs, hxs⟩ <;> simp only [Ninst.step] at hs
    · cases Step.ofExecution_ne_spawn hs
    · exact Xinst.step_spawn_depth (XStep.toStep_spawn hs)
    · cases Step.ofExecution_ne_spawn hs
  · cases Step.ofJump_ne_spawn hs
  · cases hs

/-! ### Adequacy: the relational and executable semantics agree. -/

lemma of_exec' :
    ∀ (pc : Nat) (sevm : Sevm) (devm : Devm) (exn : Execution),
      Exec pc sevm devm exn →
      ∃ fuel, ∀ fuel' > fuel, (execFueled ⟨pc, sevm, devm⟩ fuel' = Fueled.ofExcept exn) := by
  apply Exec.rec
  · intro pc sevm devm ex hstep
    refine ⟨0, fun fuel' gt => ?_⟩
    rcases fuel' with _ | fuel'
    · cases Nat.not_lt_zero _ gt
    simp only [execFueled, hstep]
  · intro pc sevm devm pc' devm' ex hstep _ ih
    rcases ih with ⟨fuel, ih⟩
    refine ⟨fuel + 1, fun fuel' gt => ?_⟩
    rcases fuel' with _ | fuel'
    · cases Nat.not_lt_zero _ gt
    simp only [execFueled, hstep]
    exact ih fuel' (by omega)
  · intro pc sevm devm f rsm pc' r e hstep henter hr
    refine ⟨0, fun fuel' gt => ?_⟩
    rcases fuel' with _ | fuel'
    · cases Nat.not_lt_zero _ gt
    simp only [execFueled, hstep, henter, hr]
  · intro pc sevm devm f rsm pc' r devm' ex hstep henter hr _ ih
    rcases ih with ⟨fuel, ih⟩
    refine ⟨fuel + 1, fun fuel' gt => ?_⟩
    rcases fuel' with _ | fuel'
    · cases Nat.not_lt_zero _ gt
    simp only [execFueled, hstep, henter, hr]
    exact ih fuel' (by omega)
  · intro pc sevm devm f rsm pc' cevm raw e hstep henter _ hr ihc
    rcases ihc with ⟨fuelc, ihc⟩
    refine ⟨fuelc + 1, fun fuel' gt => ?_⟩
    rcases fuel' with _ | fuel'
    · cases Nat.not_lt_zero _ gt
    have hc : execFueled cevm fuel' = Fueled.ofExcept raw := ihc fuel' (by omega)
    simp only [execFueled, hstep, henter]
    rw [hc]
    simp only [Fueled.ofExcept_run, hr]
  · intro pc sevm devm f rsm pc' cevm raw devm' ex hstep henter _ hr _ ihc ih
    rcases ihc with ⟨fuelc, ihc⟩
    rcases ih with ⟨fuelp, ih⟩
    refine ⟨max fuelc fuelp + 1, fun fuel' gt => ?_⟩
    rcases fuel' with _ | fuel'
    · cases Nat.not_lt_zero _ gt
    have hc : execFueled cevm fuel' = Fueled.ofExcept raw := ihc fuel' (by omega)
    simp only [execFueled, hstep, henter]
    rw [hc]
    simp only [Fueled.ofExcept_run, hr]
    exact ih fuel' (by omega)

set_option linter.defProp false in
@[reducible] def of_exec :
    ∀ (fuel : Nat) (pc : Nat) (sevm : Sevm) (devm : Devm) (exn : Execution),
      (execFueled ⟨pc, sevm, devm⟩ fuel = Fueled.ofExcept exn) →
      Nonempty (Exec pc sevm devm exn) := by
  apply Nat.strongRec
  intro fuel ih pc sevm devm exn exec_eq
  cases fuel with
  | zero =>
    simp only [execFueled] at exec_eq
    cases Fueled.exhausted_ne_ofExcept exec_eq
  | succ fuel =>
    simp only [execFueled] at exec_eq
    rcases hstep : Evm.step ⟨pc, sevm, devm⟩ with ex | ⟨pc', devm'⟩ | ⟨f, rsm, pc'⟩ <;>
      rw [hstep] at exec_eq <;> simp only [] at exec_eq
    · rw [← Fueled.ofExcept_inj.mp exec_eq]
      exact ⟨Exec.halt hstep⟩
    · rcases ih fuel (Nat.lt_succ_self _) pc' sevm devm' exn exec_eq with ⟨exc⟩
      exact ⟨Exec.cont hstep exc⟩
    · rcases henter : f.enter with r | cevm <;>
        rw [henter] at exec_eq <;> simp only [] at exec_eq
      · rcases hr : rsm.run r with e | devm' <;>
          rw [hr] at exec_eq <;> simp only [] at exec_eq
        · rw [← Fueled.ofExcept_inj.mp exec_eq]
          exact ⟨Exec.doneErr hstep henter hr⟩
        · rcases ih fuel (Nat.lt_succ_self _) pc' sevm devm' exn exec_eq with ⟨exc⟩
          exact ⟨Exec.doneOk hstep henter hr exc⟩
      · rcases hrun : (execFueled cevm fuel).run with _ | raw <;>
          rw [hrun] at exec_eq <;> simp only [] at exec_eq
        · cases Fueled.exhausted_ne_ofExcept exec_eq
        · have hc : execFueled cevm fuel = Fueled.ofExcept raw := Fueled.ext hrun
          rcases ih fuel (Nat.lt_succ_self _) cevm.pc cevm.sta cevm.dyna raw hc with
            ⟨excChild⟩
          rcases hr : rsm.run (f.settle raw) with e | devm' <;>
            rw [hr] at exec_eq <;> simp only [] at exec_eq
          · rw [← Fueled.ofExcept_inj.mp exec_eq]
            exact ⟨Exec.runErr hstep henter excChild hr⟩
          · rcases ih fuel (Nat.lt_succ_self _) pc' sevm devm' exn exec_eq with ⟨exc⟩
            exact ⟨Exec.runOk hstep henter excChild hr exc⟩

/-- **Adequacy, fuel-free.**  A closed derivation is exactly a total-`exec`
equation.  Forward: `of_exec'` produces the driver equation at every budget
past some threshold, and Jaune's `exec_eq_of_run` reads it off at a budget
that also exceeds the frame's gas.  Backward: the sufficiency bridge
`execFueled_run_sufficientFuel` turns the total result into the driver equation
`of_exec` recurses over. -/
lemma exec_iff_exec_eq (pc : Nat) (sevm : Sevm) (devm : Devm) (exn : Execution) :
    Nonempty (Exec pc sevm devm exn) ↔ exec ⟨pc, sevm, devm⟩ = exn := by
  constructor
  · intro ⟨exc⟩
    rcases of_exec' _ _ _ _ exc with ⟨fuel, eq⟩
    have hlt : devm.gasLeft < max (fuel + 1) (devm.gasLeft + 1) :=
      Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.le_max_right _ _)
    refine exec_eq_of_run hlt ?_
    rw [eq _ (Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.le_max_left _ _))]
    rfl
  · intro heq
    have h := execFueled_run_sufficientFuel ⟨pc, sevm, devm⟩
    rw [heq] at h
    exact of_exec _ _ _ _ _ (Fueled.ext h)

/-- The driver at the child's seeded budget reaches exactly the total `exec`
result, so every entered frame carries a closed derivation for it.  This is the
bridge from the total wrappers to the relational layer: no threshold obligation
survives, because sufficiency discharges it once and for all. -/
lemma Xlot.filled_exec (evm : Evm) : Xlot.Filled (.some ⟨evm, exec evm⟩) :=
  of_exec (sufficientFuel evm.dyna.gasLeft) evm.pc evm.sta evm.dyna (exec evm)
    (Fueled.ext (execFueled_run_sufficientFuel evm))

lemma of_runFrame {f : Frame}
    {r : Except (String × State × AdrSet × Tra) Devm}
    (eq : runFrame f = r) :
    ∃ xl : Xlot, xl.Filled ∧ RunFrame f xl r := by
  unfold runFrame at eq
  rcases henter : f.enter with r' | evm <;> rw [henter] at eq
  · refine ⟨.none, trivial, ?_⟩
    unfold RunFrame
    rw [henter]
    exact ⟨rfl, eq.symm⟩
  · refine ⟨.some ⟨evm, exec evm⟩, Xlot.filled_exec evm, ?_⟩
    unfold RunFrame
    rw [henter]
    exact ⟨exec evm, rfl, eq.symm⟩

lemma of_processMessage (msg : Msg)
    (ex : Except (String × State × AdrSet × Tra) Devm)
    (eq : processMessage msg = ex) :
    ∃ xl : Xlot, xl.Filled ∧ ProcessMessage msg xl ex :=
  of_runFrame eq

lemma of_processCreateMessage (msg : Msg)
    (ex : Except (String × State × AdrSet × Tra) Devm)
    (eq : processCreateMessage msg = ex) :
    ∃ xl : Xlot,
      xl.Filled ∧
      ProcessCreateMessage msg xl ex :=
  of_runFrame eq
