import Blanc.CommonProofs
import Blanc.ExecutionWarmth

/-!
# The code of one address along an execution

`Blanc/CommonProofs.lean` shows that every execution keeps the code of every nonempty-code
address.  This module is its counterpart for one address `a` whose code may be empty: an
execution keeps the code at `a` unless a CREATE derives `a`.  The address of a CREATE is a hash of
the creator and a nonce or salt, so a fixed address such as a precompile's is never derived
(`NoCreateAt`, an explicit cryptographic premise, never an axiom).

The proofs follow the nonempty-code masters step for step; the only place they used the
nonemptiness of the code was to conclude that a child's CREATE target differs from the address
watched, which `NoCreateAt` now states.
-/

namespace Blanc

open Jaune Jaune.List Jaune.Except _root_.List _root_.Nat

/-- The code at `a` is the same. -/
def Devm.CodeAt (a : Adr) (d d' : Devm) : Prop := d'.getCode a = d.getCode a

/-- No CREATE or CREATE2 derives the address `a`. -/
def NoCreateAt (a : Adr) : Prop :=
  (∀ creator nonce, computeContractAddress creator nonce ≠ a) ∧
    (∀ creator salt code, create2NewAddress creator salt code ≠ a)

/-- A suspended child keeps the code at `a`. -/
def Xlot.InvAt (a : Adr) : Xlot → Prop
  | .none => True
  | .some ⟨evm, exn⟩ => evm.dyna.getCode a = Execution.getCode exn a

lemma Xlot.invAt_of_rel {a : Adr} {xl : Xlot} (h : Xlot.Rel (Devm.CodeAt a) xl) :
    Xlot.InvAt a xl := by
  rcases xl with _ | ⟨evm, exn⟩
  · trivial
  · cases exn with
    | error e => exact (h : Devm.CodeAt a evm.dyna e.2).symm
    | ok d => exact (h : Devm.CodeAt a evm.dyna d).symm

lemma ExecuteCode.codeAt
    {a : Adr} {msg : Msg} {xl : Xlot}
    {exn : Except (EvmError × State × AdrSet × Tra) Devm}
    (inv : Xlot.InvAt a xl) (run : ExecuteCode msg xl exn) :
    MsgResult.getCode exn a = msg.benv.state.getCode a := by
  unfold ExecuteCode at run
  rcases henter : executeCode.enter msg with evm | raw <;> rw [henter] at run
  · rcases run with ⟨raw, h_xl, h_err⟩
    subst h_err
    rw [executeCode.handleErrorWith_getCode]
    rw [h_xl] at inv
    dsimp [Xlot.InvAt] at inv
    rw [executeCode.enter_inl henter] at inv
    exact inv.symm
  · rcases run with ⟨h_xl, h_err⟩
    subst h_err
    rw [executeCode.handleErrorWith_getCode]
    obtain ⟨adr, hraw⟩ := executeCode.enter_inr henter
    rw [hraw]
    exact executePrecomp_preserves_getCode (initEvm msg) adr _ rfl a

lemma ProcessMessage.codeAt
    {a : Adr} {msg : Msg} {xl : Xlot}
    {exn : Except (EvmError × State × AdrSet × Tra) Devm}
    (inv : Xlot.InvAt a xl) (run : ProcessMessage msg xl exn) :
    MsgResult.getCode exn a = msg.benv.state.getCode a := by
  obtain ⟨r0, hbody, rfl⟩ := ProcessMessage.iff_body.mp run
  unfold FrameBody at hbody
  rcases h_benv : msg.benvAfterTransfer with e | benv <;> rw [h_benv] at hbody
  · rw [hbody.2]
    dsimp [MsgResult.getCode, processMessage.settle]
    dsimp [Msg.benvAfterTransfer, Msg.shouldTransferValue] at h_benv
    split at h_benv
    · cases h_sub : msg.benv.subBal msg.caller msg.value
      · simp [h_sub, Option.toExcept, Bind.bind, Except.bind] at h_benv
        subst h_benv
        rfl
      · simp [h_sub, Option.toExcept, Bind.bind, Except.bind] at h_benv
    · contradiction
  · have h_benv_code := benvAfterTransfer_ok_getCode h_benv a
    have h_exec_cond := ExecuteCode.codeAt inv hbody
    dsimp [Msg.withBenv] at h_exec_cond
    rw [h_benv_code] at h_exec_cond
    unfold processMessage.settle
    rcases r0 with e' | evm
    · exact h_exec_cond
    · dsimp only [bind, Except.bind]
      split
      · exact Devm.rollback_getCode evm msg.benv.state msg.tenv.transientStorage a
      · exact h_exec_cond

lemma ProcessCreateMessage.codeAt
    {a : Adr} {msg : Msg} {xl : Xlot}
    {exn : Except (EvmError × State × AdrSet × Tra) Devm}
    (hne : a ≠ msg.currentTarget) (inv : Xlot.InvAt a xl)
    (run : ProcessCreateMessage msg xl exn) :
    MsgResult.getCode exn a = msg.benv.state.getCode a := by
  have h_benv_code := processCreateMessage.msg_getCode msg a
  obtain ⟨ex', h_exec, rfl⟩ := ProcessCreateMessage.iff_processMessage.mp run
  have h_exec_cond := ProcessMessage.codeAt inv h_exec
  rw [h_benv_code] at h_exec_cond
  unfold processCreateMessage.settle
  rcases ex' with x | evm
  · exact h_exec_cond
  · dsimp only [bind, Except.bind]
    split
    · rename_i h_none
      cases h_charge : processCreateMessage.chargeCodeGas msg.benv.stat.rules evm with
      | error err =>
        rcases err with ⟨err_msg, err_evm⟩
        have h_getCode := processCreateMessage.chargeCodeGas_getCode_gen h_charge a
        change err_evm.state.getCode a = evm.state.getCode a at h_getCode
        cases err_msg with
        | halt reason =>
            simp only [MsgResult.getCode, processCreateMessage.exceptionalHalt]
            split
            · rfl
            · rfl
        | _ =>
            simp only [MsgResult.getCode]
            rw [h_getCode]; exact h_exec_cond
      | ok devm_charge =>
        dsimp only [MsgResult.getCode]
        have h_getCode := processCreateMessage.chargeCodeGas_getCode_gen h_charge a
        dsimp [Execution.getCode] at h_getCode
        rw [setCode_getCode hne.symm]
        rw [h_getCode]
        exact h_exec_cond
    · rename_i h_some
      exact Devm.rollback_getCode evm msg.benv.state msg.tenv.transientStorage a

lemma GenericCall.codeAt
    {a : Adr} {sevm : Sevm} {devm : Devm} {gas : Nat} {value : B256}
    {caller target codeAddress : Adr} {shouldTransferValue isStaticcall : Bool}
    {input_index input_size output_index output_size : Nat} {code : ByteArray}
    {disablePrecompiles : Bool} {xl : Xlot} {exn : Execution}
    (inv : Xlot.InvAt a xl)
    (run : GenericCall sevm devm gas value caller target codeAddress shouldTransferValue
      isStaticcall input_index input_size output_index output_size code disablePrecompiles
      xl exn) :
    Execution.getCode exn a = devm.getCode a := by
  unfold GenericCall genericCall.step at run
  simp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at run
  repeat' split at run
  all_goals simp only [XStep.ofExcept, XStep.Run] at run
  -- depth-zero early exit, push failed
  · obtain ⟨-, rfl⟩ := run
    rename_i heq
    rw [Devm.push_getCode_gen heq a]
    rfl
  -- depth-zero early exit, push succeeded
  · obtain ⟨-, rfl⟩ := run
    rename_i heq
    rw [Devm.push_getCode_gen heq a]
    rfl
  -- the child frame is entered
  · obtain ⟨r, hframe, rfl⟩ := run
    rw [Resume.call_getCode ?_]
    · rfl
    · rw [ProcessMessage.codeAt inv hframe]
      exact callMsg_benv_state_getCode a

lemma GenericCreate.codeAt
    {a : Adr} {sevm : Sevm} {devm : Devm} {endowment : B256} {newAddress : Adr}
    {memoryIndex memorySize : Nat} {xl : Xlot} {exn : Execution}
    (hne : ∀ f rsm, genericCreate.step sevm devm endowment newAddress memoryIndex memorySize =
      .spawn f rsm → a ≠ newAddress)
    (inv : Xlot.InvAt a xl)
    (run : GenericCreate sevm devm endowment newAddress memoryIndex memorySize xl exn) :
    Execution.getCode exn a = devm.getCode a := by
  have hne0 := hne
  unfold GenericCreate genericCreate.step at run
  simp only [Bind.bind, Except.bind, Except.assert, assertDynamic,
    Pure.pure, Except.pure] at run
  repeat' split at run
  all_goals simp only [XStep.ofExcept, XStep.Run] at run
  -- init-code-size assertion failed
  · obtain ⟨-, rfl⟩ := run
    rename_i heq
    split at heq <;> cases heq
    rfl
  -- static-context assertion failed
  · obtain ⟨-, rfl⟩ := run
    rename_i heq
    split at heq <;> cases heq
    rfl
  -- balance / max-nonce / depth-zero early exit, push failed
  · obtain ⟨-, rfl⟩ := run
    rename_i heq
    rw [Devm.push_getCode_gen heq a]
    rfl
  -- balance / max-nonce / depth-zero early exit, push succeeded
  · obtain ⟨-, rfl⟩ := run
    rename_i heq
    rw [Devm.push_getCode_gen heq a]
    rfl
  -- address-collision early exit, push failed
  · obtain ⟨-, rfl⟩ := run
    rename_i heq
    rw [Devm.push_getCode_gen heq a]
    rw [addAccessedAddress_getCode]
    exact Devm.incrNonce_getCode
  -- address-collision early exit, push succeeded
  · obtain ⟨-, rfl⟩ := run
    rename_i heq
    rw [Devm.push_getCode_gen heq a]
    rw [addAccessedAddress_getCode]
    exact Devm.incrNonce_getCode
  -- the child frame is entered
  · obtain ⟨r, hframe, rfl⟩ := run
    have h_parent : ∀ b : Adr,
        (addAccessedAddress
          (((devm.withGasLeft (devm.gasLeft - except64th devm.gasLeft)).withReturnData
            []).incrNonce sevm.currentTarget) newAddress).getCode b = devm.getCode b := by
      intro b
      rw [addAccessedAddress_getCode]
      exact Devm.incrNonce_getCode
    have hne' : a ≠ newAddress := by
      refine hne (Frame.ofCreate (createMsg sevm
        (addAccessedAddress
          (((devm.withGasLeft (devm.gasLeft - except64th devm.gasLeft)).withReturnData
            []).incrNonce sevm.currentTarget) newAddress)
        (except64th devm.gasLeft) endowment newAddress
        (Array.sliceD devm.memory.data memoryIndex memorySize 0)))
        (Resume.create (addAccessedAddress
          (((devm.withGasLeft (devm.gasLeft - except64th devm.gasLeft)).withReturnData
            []).incrNonce sevm.currentTarget) newAddress) newAddress) ?_
      unfold genericCreate.step
      simp only [Bind.bind, Except.bind, Except.assert, assertDynamic, Pure.pure, Except.pure]
      repeat' split
      all_goals first | rfl | simp_all
    rw [Resume.create_getCode ?_, h_parent a]
    exact ProcessCreateMessage.codeAt hne' inv hframe |>.trans
      (by rw [createMsg_benv_state_getCode, h_parent a])

/-! ### The address a CREATE-family spawn writes -/

/-- A CREATE-family spawn never targets `a`. -/
def XStep.SpawnNe (a : Adr) : XStep → Prop
  | .done _ => True
  | .spawn f _ => f.isCreate = true → f.inner.currentTarget ≠ a

theorem XStep.SpawnNe.ofExcept {a : Adr} {e : Except (EvmError × Devm) XStep}
    (h : Except.OkOn (XStep.SpawnNe a) e) : XStep.SpawnNe a (XStep.ofExcept e) := by
  cases e with
  | error e => trivial
  | ok st => exact h st rfl

theorem XStep.SpawnNe.done {a : Adr} {ex : Execution} : XStep.SpawnNe a (.done ex) := trivial

theorem XStep.SpawnNe.spawn {a : Adr} {f : Frame} {rsm : Resume}
    (h : f.isCreate = true → f.inner.currentTarget ≠ a) : XStep.SpawnNe a (.spawn f rsm) := h

theorem Except.OkOn.triv {ε α : Type} (x : Except ε α) : Except.OkOn (fun _ => True) x :=
  fun _ _ => trivial

/-- Walk a do-block that returns a call-type outcome: every intermediate value is irrelevant, and
each leaf is a `done` or one of the generic steps whose lemma `leaf` closes. -/
macro "sp_walk " leaf:tacticSeq : tactic =>
  `(tactic| repeat (first
      | with_reducible exact Except.OkOn.error
      | (with_reducible refine Except.OkOn.bind_ok ?_)
      | (with_reducible refine Except.OkOn.bind (P := fun _ => True) (Except.OkOn.triv _) ?_; intro _ _)
      | focus ((with_reducible apply Except.OkOn.ok); ($leaf))
      | focus ((with_reducible apply Except.OkOn.pure); ($leaf))
      | split))

theorem genericCall.step_spawnNe {a : Adr} (sevm : Sevm) (devm : Devm) (gas : Nat)
    (value : B256) (caller target codeAddress : Adr) (stv isSt : Bool) (ii isz oi osz : Nat)
    (code : ByteArray) (dp : Bool) :
    XStep.SpawnNe a
      (genericCall.step sevm devm gas value caller target codeAddress stv isSt ii isz oi osz
        code dp) := by
  unfold genericCall.step
  dsimp only
  split
  · refine XStep.SpawnNe.ofExcept ?_
    sp_walk exact XStep.SpawnNe.done
  · intro h
    exact absurd h (by simp [Frame.ofCall])

theorem genericCreate.step_spawnNe {a : Adr} (sevm : Sevm) (devm : Devm) (endowment : B256)
    (newAddress : Adr) (mi ms : Nat) (h : newAddress ≠ a) :
    XStep.SpawnNe a (genericCreate.step sevm devm endowment newAddress mi ms) := by
  unfold genericCreate.step
  dsimp only
  refine XStep.SpawnNe.ofExcept ?_
  sp_walk (first | exact XStep.SpawnNe.done | (refine XStep.SpawnNe.spawn ?_; intro _; exact h))

set_option hygiene false in
/-- The leaves of `Xinst.step`. -/
macro "sp_leaf" : tactic =>
  `(tactic| first
      | (with_reducible exact XStep.SpawnNe.done)
      | (with_reducible apply genericCall.step_spawnNe)
      | ((with_reducible apply genericCreate.step_spawnNe)
         first | (with_reducible exact hn1 _ _) | (with_reducible exact hn2 _ _ _)))

theorem Xinst.step_spawnNe {a : Adr} (hno : NoCreateAt a) (sevm : Sevm) (devm : Devm) (x : Xinst)
    (hsg : sevm.benvStat.rules.stateGas = none) :
    XStep.SpawnNe a (Xinst.step sevm devm x) := by
  obtain ⟨hn1, hn2⟩ := hno
  cases x <;> simp only [Xinst.step, hsg]
  all_goals refine XStep.SpawnNe.ofExcept ?_
  all_goals sp_walk sp_leaf

theorem genericCreate.step_spawn_isCreate
    {sevm : Sevm} {devm : Devm} {endowment : B256} {newAddress : Adr}
    {mi ms : Nat} {f : Frame} {rsm : Resume}
    (hs : genericCreate.step sevm devm endowment newAddress mi ms = .spawn f rsm) :
    f.isCreate = true := by
  simp only [genericCreate.step, Bind.bind, Except.bind, Except.assert,
    assertDynamic, Pure.pure, Except.pure] at hs
  repeat' split at hs
  all_goals simp only [XStep.ofExcept, XStep.spawn.injEq, reduceCtorEq] at hs
  all_goals obtain ⟨rfl, -⟩ := hs
  rfl

/-- **The code at `a` along one call-type instruction**, given that its child keeps it. -/
lemma Xinst.codeAt_effectRecFork {a : Adr} (hno : NoCreateAt a) (x : Xinst) :
    ∀ {sevm : Sevm} {pre : Devm} {xl : Xlot} {out : Execution},
      CoveredFork sevm.benvStat.fork → Xlot.Rel (Devm.CodeAt a) xl →
      Xinst.Run sevm pre x xl out → Execution.Rel (Devm.CodeAt a) pre out := by
  intro sevm devm xl exn hfork hxl run
  have inv := Xlot.invAt_of_rel hxl
  unfold Xinst.Run at run
  have hsp := Xinst.step_spawnNe hno sevm devm x hfork.rules_stateGas_none
  have lift : ∀ {d : Devm}, Devm.InstructionFrame devm d →
      Execution.getCode exn a = d.getCode a → Execution.Rel (Devm.CodeAt a) devm exn := by
    intro d hf h
    cases exn with
    | error e => exact h.trans (hf.getCode a).symm
    | ok d' => exact h.trans (hf.getCode a).symm
  rcases Xinst.step_shapeCovered sevm devm x hfork with ⟨ex, hs, hframe⟩ |
    ⟨d, e, na, mi, ms, hf, hs⟩ |
    ⟨d, d₀, g, v, c, t, cadr, stv, isSt, ii, isz, oi, osz, code, dp,
      hf, -, -, -, hs⟩ <;> rw [hs] at run hsp
  · obtain ⟨-, rfl⟩ := run
    cases exn with
    | error e => exact (hframe.getCode a).symm
    | ok d' => exact (hframe.getCode a).symm
  · refine lift hf (GenericCreate.codeAt ?_ inv run)
    intro f rsm hsf
    have hc := genericCreate.step_spawn_frame hsf
    have hcreate := genericCreate.step_spawn_isCreate hsf
    rw [hsf] at hsp
    intro h
    exact hsp hcreate (hc.2.1.trans h.symm)
  · exact lift hf (GenericCall.codeAt inv run)

theorem Devm.codeAt_refl (a : Adr) : ReflexiveRel (Devm.CodeAt a) := fun _ => rfl

theorem Devm.codeAt_trans (a : Adr) : TransitiveRel (Devm.CodeAt a) :=
  fun _ _ _ h1 h2 => h2.trans h1

lemma Rinst.codeAt_effect (a : Adr) (r : Rinst) : Rinst.Effect (Devm.CodeAt a) r := by
  intro pc sevm pre out hrun
  cases out with
  | error e => exact Rinst.preserves_getCode_err hrun a
  | ok d => exact Rinst.preserves_getCode hrun a

lemma Jinst.codeAt_effect (a : Adr) (j : Jinst) : Jinst.Effect (Devm.CodeAt a) j := by
  intro evm out hrun
  have hf := Jinst.run_instructionFrame evm j
  rw [hrun] at hf
  cases out <;> exact (Devm.InstructionFrame.getCode hf a).symm

lemma Linst.codeAt_effect (a : Adr) (l : Linst) : Linst.Effect (Devm.CodeAt a) l := by
  intro sevm pre out hrun
  have hf := Linst.run_codeFrame hrun
  cases out <;> exact hf a

lemma Ninst.effectRecFork_exec {R : Devm → Devm → Prop} {x : Xinst}
    (hx : ∀ {sevm : Sevm} {pre : Devm} {xl : Xlot} {out : Execution},
      CoveredFork sevm.benvStat.fork → Xlot.Rel R xl → Xinst.Run sevm pre x xl out →
        Execution.Rel R pre out) :
    Ninst.EffectRecFork R (.exec x) := by
  intro pc sevm pre xl out hfork hxl hrun
  simp only [Ninst.StepRun, Ninst.step_exec] at hrun
  exact hx hfork hxl (XStep.run_toStep.mp hrun)

lemma Ninst.codeAt_effectRecFork {a : Adr} (hno : NoCreateAt a) (n : Ninst) :
    Ninst.EffectRecFork (Devm.CodeAt a) n := by
  have hIR : ∀ ⦃d d' : Devm⦄, Devm.InstructionFrame d d' → Devm.CodeAt a d d' :=
    fun _ _ hf => (hf.getCode a).symm
  cases n with
  | reg r =>
    intro pc sevm pre xl out hfork hxl hrun
    exact Ninst.effectRec_reg (Rinst.codeAt_effect a r) hxl hrun
  | exec x =>
    intro pc sevm pre xl out hfork hxl hrun
    exact Ninst.effectRecFork_exec (Xinst.codeAt_effectRecFork hno x) hfork hxl hrun
  | push xs hxs =>
    intro pc sevm pre xl out hfork hxl hrun
    exact Ninst.push_effectRec_of_instructionFrame hIR hxl hrun
  | dupn imm =>
    intro pc sevm pre xl out hfork hxl hrun
    exact Ninst.dupn_effectRec_of_instructionFrame hIR hxl hrun
  | swapn imm =>
    intro pc sevm pre xl out hfork hxl hrun
    exact Ninst.swapn_effectRec_of_instructionFrame hIR hxl hrun
  | exchange imm =>
    intro pc sevm pre xl out hfork hxl hrun
    exact Ninst.exchange_effectRec_of_instructionFrame hIR hxl hrun

/-- **An execution keeps the code at `a`** (on the covered forks, when no CREATE derives `a`). -/
theorem Exec.codeAt_effect {a : Adr} (hno : NoCreateAt a)
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution} (run : Exec pc sevm pre out)
    (hfork : CoveredFork sevm.benvStat.fork) :
    Execution.Rel (Devm.CodeAt a) pre out :=
  Exec.effectFork (Devm.codeAt_refl a) (Devm.codeAt_trans a) (Ninst.codeAt_effectRecFork hno)
    (Jinst.codeAt_effect a) (Linst.codeAt_effect a) run hfork

/-- **Every frame an execution enters starts with the code at `a` it started with**, including
the frames of subtrees that later revert. -/
theorem Exec.rawFrameRoots_codeAt {a : Adr} (hno : NoCreateAt a)
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution} (run : Exec pc sevm pre out)
    (hfork : CoveredFork sevm.benvStat.fork) :
    ∀ root ∈ Exec.rawFrameRoots run, root.devm.getCode a = pre.getCode a := by
  have step := fun {pc : Nat} {sevm : Sevm} {devm : Devm} {xl : Xlot} {out : Execution}
      (hfork : CoveredFork sevm.benvStat.fork) (hxl : Xlot.Rel (Devm.CodeAt a) xl)
      (hrun : Step.Run (Evm.step ⟨pc, sevm, devm⟩) xl out) =>
    Evm.step_effectFork (Devm.codeAt_refl a) (Ninst.codeAt_effectRecFork hno)
      (Jinst.codeAt_effect a) (Linst.codeAt_effect a) hfork hxl hrun
  revert hfork
  induction run with
  | halt hstep =>
      intro hfork root member
      simp only [Exec.rawFrameRoots, Exec.rawFrameDescendants, List.mem_cons,
        List.not_mem_nil, or_false] at member
      subst member
      rfl
  | cont hstep next ih =>
      intro hfork root member
      have hc : Devm.CodeAt a _ _ := step (xl := .none) (out := .ok _) hfork trivial
        (by rw [hstep]; exact ⟨rfl, rfl⟩)
      simp only [Exec.rawFrameRoots, Exec.rawFrameDescendants, List.mem_cons] at member
      rcases member with rfl | member
      · rfl
      · exact (ih hfork root (by simp [Exec.rawFrameRoots, member])).trans hc
  | doneErr hstep henter hresume =>
      intro hfork root member
      simp only [Exec.rawFrameRoots, Exec.rawFrameDescendants, List.mem_cons,
        List.not_mem_nil, or_false] at member
      subst member
      rfl
  | doneOk hstep henter hresume next ih =>
      intro hfork root member
      have hc : Devm.CodeAt a _ _ := step (xl := .none) (out := .ok _) hfork trivial
        (by rw [hstep]; exact ⟨_, RunFrame.of_done henter, hresume.symm⟩)
      simp only [Exec.rawFrameRoots, Exec.rawFrameDescendants, List.mem_cons] at member
      rcases member with rfl | member
      · rfl
      · exact (ih hfork root (by simp [Exec.rawFrameRoots, member])).trans hc
  | runErr hstep henter child hresume ih =>
      intro hfork root member
      have hfork_c := Evm.step_spawn_child_fork hstep henter hfork
      have hstart := (Evm.step_spawn_child hstep henter).2.1 a
      simp only [Exec.rawFrameRoots, Exec.rawFrameDescendants, List.mem_cons] at member
      rcases member with rfl | rfl | member
      · rfl
      · exact hstart
      · exact (ih hfork_c root (by simp [Exec.rawFrameRoots, member])).trans hstart
  | runOk hstep henter child hresume next ihChild ihNext =>
      intro hfork root member
      have hfork_c := Evm.step_spawn_child_fork hstep henter hfork
      have hstart := (Evm.step_spawn_child hstep henter).2.1 a
      have hchild := Exec.codeAt_effect hno child hfork_c
      have hc : Devm.CodeAt a _ _ := step (xl := .some ⟨_, _⟩) (out := .ok _) hfork hchild
        (by rw [hstep]; exact ⟨_, RunFrame.of_run henter, hresume.symm⟩)
      simp only [Exec.rawFrameRoots, Exec.rawFrameDescendants, List.mem_cons,
        List.mem_append] at member
      rcases member with rfl | rfl | member | member
      · rfl
      · exact hstart
      · exact (ihChild hfork_c root (by simp [Exec.rawFrameRoots, member])).trans hstart
      · exact (ihNext hfork root (by simp [Exec.rawFrameRoots, member])).trans hc

end Blanc
