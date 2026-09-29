import Blanc.CommonProofs
import Blanc.ExecutionWarmth

/-!
# The code of one address along an execution

`Blanc/CommonProofs.lean` shows that every execution keeps the code of every nonempty-code
address.  This module is its counterpart for one address `a` whose code may be empty: an
execution keeps the code at `a` unless a CREATE frame it enters targets `a`, and then so does
every frame it enters (`Exec.codeAt_avoid`).  The hypothesis is trace-local: it names the frames
the execution actually enters (`Exec.rawFrameRoots`), not a property of the CREATE address
function, which no fixed address can be assumed to avoid.

The proofs follow the nonempty-code masters step for step; the only place they used the
nonemptiness of the code was to conclude that a child's CREATE target differs from the address
watched, which the hypothesis now states for the frames that are entered.
-/

namespace Blanc

open Jaune Jaune.List Jaune.Except _root_.List _root_.Nat

/-- The code at `a` is the same. -/
def Devm.CodeAt (a : Adr) (d d' : Devm) : Prop := d'.getCode a = d.getCode a

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

/-- A frame with no interpreter slot whose message has no code address is a value-transfer
failure, so it ends in an error. -/
lemma ProcessMessage.none_error {msg : Msg}
    {ex : Except (EvmError × State × AdrSet × Tra) Devm}
    (hca : msg.codeAddress = none) (run : ProcessMessage msg .none ex) :
    ∃ e, ex = .error e := by
  rcases RunFrame.decompose run with ⟨e, -, -, hr⟩ | ⟨benv, r', -, hec, hr⟩
  · exact ⟨e, hr⟩
  · unfold ExecuteCode at hec
    have hca' : ((Frame.ofCall msg).inner.withBenv benv).codeAddress = none := hca
    have hen : executeCode.enter ((Frame.ofCall msg).inner.withBenv benv) =
        .inl (initEvm ((Frame.ofCall msg).inner.withBenv benv)) := by
      unfold executeCode.enter
      simp only [hca']
    rw [hen] at hec
    obtain ⟨raw, hx, -⟩ := hec
    cases hx

lemma ProcessCreateMessage.codeAt_none
    {a : Adr} {msg : Msg}
    {exn : Except (EvmError × State × AdrSet × Tra) Devm}
    (hca : msg.codeAddress = none) (run : ProcessCreateMessage msg .none exn) :
    MsgResult.getCode exn a = msg.benv.state.getCode a := by
  have h_benv_code := processCreateMessage.msg_getCode msg a
  obtain ⟨ex', h_exec, rfl⟩ := ProcessCreateMessage.iff_processMessage.mp run
  have hca' : (processCreateMessage.msg msg).codeAddress = none := hca
  obtain ⟨e, rfl⟩ := ProcessMessage.none_error hca' h_exec
  have h_exec_cond := ProcessMessage.codeAt (a := a) (xl := .none) trivial h_exec
  rw [h_benv_code] at h_exec_cond
  unfold processCreateMessage.settle
  exact h_exec_cond

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
    (hne : ∀ f rsm cevm, genericCreate.step sevm devm endowment newAddress memoryIndex
        memorySize = .spawn f rsm → f.enter = .run cevm → a ≠ newAddress)
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
    have hmsg : MsgResult.getCode r a =
        (createMsg sevm
          (addAccessedAddress
            (((devm.withGasLeft (devm.gasLeft - except64th devm.gasLeft)).withReturnData
              []).incrNonce sevm.currentTarget) newAddress)
          (except64th devm.gasLeft) endowment newAddress
          (Array.sliceD devm.memory.data memoryIndex memorySize 0)).benv.state.getCode a := by
      rcases xl with _ | ⟨cevm, raw⟩
      · exact ProcessCreateMessage.codeAt_none rfl hframe
      · have henter := (RunFrame.some_inv hframe).1
        have hne' : a ≠ newAddress := by
          refine hne (Frame.ofCreate (createMsg sevm
            (addAccessedAddress
              (((devm.withGasLeft (devm.gasLeft - except64th devm.gasLeft)).withReturnData
                []).incrNonce sevm.currentTarget) newAddress)
            (except64th devm.gasLeft) endowment newAddress
            (Array.sliceD devm.memory.data memoryIndex memorySize 0)))
            (Resume.create (addAccessedAddress
              (((devm.withGasLeft (devm.gasLeft - except64th devm.gasLeft)).withReturnData
                []).incrNonce sevm.currentTarget) newAddress) newAddress) cevm ?_ henter
          unfold genericCreate.step
          simp only [Bind.bind, Except.bind, Except.assert, assertDynamic, Pure.pure,
            Except.pure]
          repeat' split
          all_goals first | rfl | simp_all
        exact ProcessCreateMessage.codeAt hne' inv hframe
    rw [Resume.create_getCode ?_, h_parent a]
    exact hmsg.trans (by rw [createMsg_benv_state_getCode, h_parent a])


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

/-- The CREATE frame this instruction enters, if any, never targets `a`. -/
def Xinst.AvoidsAt (a : Adr) (sevm : Sevm) (devm : Devm) (x : Xinst) : Prop :=
  ∀ f rsm cevm, Xinst.step sevm devm x = .spawn f rsm → f.enter = .run cevm →
    f.isCreate = true → f.inner.currentTarget ≠ a

/-- **The code at `a` along one call-type instruction**, given that its child keeps it and that
the instruction enters no CREATE frame at `a`. -/
lemma Xinst.codeAt_effectRecAvoid {a : Adr} (x : Xinst) :
    ∀ {sevm : Sevm} {pre : Devm} {xl : Xlot} {out : Execution},
      CoveredFork sevm.benvStat.fork → Xinst.AvoidsAt a sevm pre x →
      Xlot.Rel (Devm.CodeAt a) xl →
      Xinst.Run sevm pre x xl out → Execution.Rel (Devm.CodeAt a) pre out := by
  intro sevm devm xl exn hfork havoid hxl run
  have inv := Xlot.invAt_of_rel hxl
  unfold Xinst.Run at run
  have lift : ∀ {d : Devm}, Devm.InstructionFrame devm d →
      Execution.getCode exn a = d.getCode a → Execution.Rel (Devm.CodeAt a) devm exn := by
    intro d hf h
    cases exn with
    | error e => exact h.trans (hf.getCode a).symm
    | ok d' => exact h.trans (hf.getCode a).symm
  rcases Xinst.step_shapeCovered sevm devm x hfork with ⟨ex, hs, hframe⟩ |
    ⟨d, e, na, mi, ms, hf, hs⟩ |
    ⟨d, d₀, g, v, c, t, cadr, stv, isSt, ii, isz, oi, osz, code, dp,
      hf, -, -, -, hs⟩ <;> rw [hs] at run
  · obtain ⟨-, rfl⟩ := run
    cases exn with
    | error e => exact (hframe.getCode a).symm
    | ok d' => exact (hframe.getCode a).symm
  · refine lift hf (GenericCreate.codeAt ?_ inv run)
    intro f rsm cevm hsf henter
    have hc := genericCreate.step_spawn_frame hsf
    have hcreate := genericCreate.step_spawn_isCreate hsf
    intro h
    exact havoid f rsm cevm (hs.trans hsf) henter hcreate (hc.2.1.trans h.symm)
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

/-- **One interpreter step keeps the code at `a`**, given that its child keeps it and that it
enters no CREATE frame at `a`. -/
lemma Evm.step_codeAt {a : Adr} {pc : Nat} {sevm : Sevm} {devm : Devm} {xl : Xlot}
    {out : Execution} (hfork : CoveredFork sevm.benvStat.fork)
    (hav : ∀ x, Xinst.At sevm.code pc x → Xinst.AvoidsAt a sevm devm x)
    (hxl : Xlot.Rel (Devm.CodeAt a) xl)
    (hrun : Step.Run (Evm.step ⟨pc, sevm, devm⟩) xl out) :
    Execution.Rel (Devm.CodeAt a) devm out := by
  have hIR : ∀ ⦃d d' : Devm⦄, Devm.InstructionFrame d d' → Devm.CodeAt a d d' :=
    fun _ _ hf => (hf.getCode a).symm
  rcases hgi : (Evm.getInst ⟨pc, sevm, devm⟩) with _ | i
  · rw [Evm.step_invOp hgi] at hrun
    obtain ⟨-, rfl⟩ := hrun
    exact Devm.codeAt_refl a _
  · cases i with
    | next n =>
      rw [Evm.step_next (n := n) hgi] at hrun
      cases n with
      | reg r => exact Ninst.effectRec_reg (Rinst.codeAt_effect a r) hxl hrun
      | exec x =>
        simp only [Ninst.step_exec] at hrun
        exact Xinst.codeAt_effectRecAvoid x hfork (hav x hgi) hxl (XStep.run_toStep.mp hrun)
      | push xs hxs => exact Ninst.push_effectRec_of_instructionFrame hIR hxl hrun
      | dupn imm => exact Ninst.dupn_effectRec_of_instructionFrame hIR hxl hrun
      | swapn imm => exact Ninst.swapn_effectRec_of_instructionFrame hIR hxl hrun
      | exchange imm => exact Ninst.exchange_effectRec_of_instructionFrame hIR hxl hrun
    | jump j =>
      rw [Evm.step_jump (j := j) hgi] at hrun
      obtain ⟨-, hcase⟩ := Step.run_ofJump hrun
      have hjr := Jinst.codeAt_effect a j (evm := ⟨pc, sevm, devm⟩)
        (out := j.run ⟨pc, sevm, devm⟩) rfl
      rcases hcase with ⟨e, hje, rfl⟩ | ⟨pc', d, hje, rfl⟩ <;> rw [hje] at hjr <;> exact hjr
    | last l =>
      rw [Evm.step_last (l := l) hgi] at hrun
      obtain ⟨-, rfl⟩ := hrun
      exact Linst.codeAt_effect a l rfl

lemma Xinst.avoidsAt_of_step {a : Adr} {pc : Nat} {sevm : Sevm} {devm : Devm}
    (H : ∀ f rsm pc' cevm, Evm.step ⟨pc, sevm, devm⟩ = .spawn f rsm pc' →
      f.enter = .run cevm → f.isCreate = true → f.inner.currentTarget ≠ a) :
    ∀ x, Xinst.At sevm.code pc x → Xinst.AvoidsAt a sevm devm x := by
  intro x hx f rsm cevm hs henter hc
  refine H f rsm (pc + 1) cevm ?_ henter hc
  rw [Evm.step_next hx]
  simp only [Ninst.step, XStep.toStep, hs, Ninst.size]

/-- **An execution keeps the code at `a`, and so does every frame it enters**, when it enters no
frame targeting `a` (in particular no CREATE frame that could install code there). -/
theorem Exec.codeAt_avoid {a : Adr} {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out) (hfork : CoveredFork sevm.benvStat.fork)
    (avoid : ∀ root ∈ Exec.rawFrameRoots run, root.sevm.currentTarget ≠ a) :
    Execution.Rel (Devm.CodeAt a) pre out ∧
      ∀ root ∈ Exec.rawFrameRoots run, root.devm.getCode a = pre.getCode a := by
  revert hfork avoid
  induction run with
  | halt hstep =>
      intro hfork avoid
      have hc := Evm.step_codeAt (a := a) (xl := .none) hfork
        (Xinst.avoidsAt_of_step (fun f rsm pc' cevm h => by rw [hstep] at h; cases h))
        trivial (by rw [hstep]; exact ⟨rfl, rfl⟩)
      refine ⟨hc, ?_⟩
      intro root member
      simp only [Exec.rawFrameRoots, Exec.rawFrameDescendants, List.mem_cons,
        List.not_mem_nil, or_false] at member
      subst member
      rfl
  | @cont pc sevm devm pc' devm' ex hstep next ih =>
      intro hfork avoid
      have hself : sevm.currentTarget ≠ a :=
        avoid ⟨pc, sevm, devm, ex, Exec.cont hstep next⟩ (List.mem_cons_self ..)
      have hc : Devm.CodeAt a _ _ := Evm.step_codeAt (xl := .none) (out := .ok _) hfork
        (Xinst.avoidsAt_of_step (fun f rsm pc' cevm h => by rw [hstep] at h; cases h))
        trivial (by rw [hstep]; exact ⟨rfl, rfl⟩)
      obtain ⟨hrel, hroots⟩ := ih hfork (by
        intro root member
        simp only [Exec.rawFrameRoots, List.mem_cons] at member
        rcases member with rfl | member
        · exact hself
        · exact avoid root (by simp [Exec.rawFrameRoots, Exec.rawFrameDescendants, member]))
      refine ⟨Execution.Rel.trans_left (Devm.codeAt_trans a) hc hrel, ?_⟩
      intro root member
      simp only [Exec.rawFrameRoots, Exec.rawFrameDescendants, List.mem_cons] at member
      rcases member with rfl | member
      · rfl
      · exact (hroots root (by simp [Exec.rawFrameRoots, member])).trans hc
  | doneErr hstep henter hresume =>
      intro hfork avoid
      have hc := Evm.step_codeAt (a := a) (xl := .none) (out := .error _) hfork
        (Xinst.avoidsAt_of_step (fun f' rsm' pc' cevm h hen => by
          rw [hstep] at h; cases h; rw [henter] at hen; cases hen))
        trivial (by rw [hstep]; exact ⟨_, RunFrame.of_done henter, hresume.symm⟩)
      refine ⟨hc, ?_⟩
      intro root member
      simp only [Exec.rawFrameRoots, Exec.rawFrameDescendants, List.mem_cons,
        List.not_mem_nil, or_false] at member
      subst member
      rfl
  | @doneOk pc sevm devm f rsm pc' r devm' ex hstep henter hresume next ih =>
      intro hfork avoid
      have hself : sevm.currentTarget ≠ a :=
        avoid ⟨pc, sevm, devm, ex, Exec.doneOk hstep henter hresume next⟩
          (List.mem_cons_self ..)
      have hc : Devm.CodeAt a _ _ := Evm.step_codeAt (xl := .none) (out := .ok _) hfork
        (Xinst.avoidsAt_of_step (fun f' rsm' pc' cevm h hen => by
          rw [hstep] at h; cases h; rw [henter] at hen; cases hen))
        trivial (by rw [hstep]; exact ⟨_, RunFrame.of_done henter, hresume.symm⟩)
      obtain ⟨hrel, hroots⟩ := ih hfork (by
        intro root member
        simp only [Exec.rawFrameRoots, List.mem_cons] at member
        rcases member with rfl | member
        · exact hself
        · exact avoid root (by simp [Exec.rawFrameRoots, Exec.rawFrameDescendants, member]))
      refine ⟨Execution.Rel.trans_left (Devm.codeAt_trans a) hc hrel, ?_⟩
      intro root member
      simp only [Exec.rawFrameRoots, Exec.rawFrameDescendants, List.mem_cons] at member
      rcases member with rfl | member
      · rfl
      · exact (hroots root (by simp [Exec.rawFrameRoots, member])).trans hc
  | @runErr pc sevm devm f rsm pc' cevm raw e hstep henter child hresume ih =>
      intro hfork avoid
      have hfork_c := Evm.step_spawn_child_fork hstep henter hfork
      have hstart := (Evm.step_spawn_child hstep henter).2.1 a
      have hcavoid : cevm.sta.currentTarget ≠ a :=
        avoid ⟨cevm.pc, cevm.sta, cevm.dyna, raw, child⟩
          (by simp [Exec.rawFrameRoots, Exec.rawFrameDescendants])
      obtain ⟨hrel, hroots⟩ := ih hfork_c (by
        intro root member
        exact avoid root (by
          simp only [Exec.rawFrameRoots, Exec.rawFrameDescendants, List.mem_cons] at member ⊢
          exact Or.inr member))
      have hc := Evm.step_codeAt (a := a) (xl := .some ⟨_, _⟩) (out := .error _) hfork
        (Xinst.avoidsAt_of_step (fun f' rsm' pc'' cevm' h hen hcr => by
          rw [hstep] at h; cases h; rw [henter] at hen; cases hen
          rw [← Frame.enter_run_currentTarget henter]; exact hcavoid))
        hrel (by rw [hstep]; exact ⟨_, RunFrame.of_run henter, hresume.symm⟩)
      refine ⟨hc, ?_⟩
      intro root member
      simp only [Exec.rawFrameRoots, Exec.rawFrameDescendants, List.mem_cons] at member
      rcases member with rfl | rfl | member
      · rfl
      · exact hstart
      · exact (hroots root (by simp [Exec.rawFrameRoots, member])).trans hstart
  | @runOk pc sevm devm f rsm pc' cevm raw devm' ex hstep henter child hresume next
      ihChild ihNext =>
      intro hfork avoid
      have hself : sevm.currentTarget ≠ a :=
        avoid ⟨pc, sevm, devm, ex, Exec.runOk hstep henter child hresume next⟩
          (List.mem_cons_self ..)
      have hfork_c := Evm.step_spawn_child_fork hstep henter hfork
      have hstart := (Evm.step_spawn_child hstep henter).2.1 a
      have hcavoid : cevm.sta.currentTarget ≠ a :=
        avoid ⟨cevm.pc, cevm.sta, cevm.dyna, raw, child⟩
          (by simp [Exec.rawFrameRoots, Exec.rawFrameDescendants])
      obtain ⟨hrelChild, hrootsChild⟩ := ihChild hfork_c (by
        intro root member
        exact avoid root (by
          simp only [Exec.rawFrameRoots, Exec.rawFrameDescendants, List.mem_cons,
            List.mem_append] at member ⊢
          rcases member with h | h
          · exact Or.inr (Or.inl h)
          · exact Or.inr (Or.inr (Or.inl h))))
      have hc : Devm.CodeAt a _ _ := Evm.step_codeAt (xl := .some ⟨_, _⟩) (out := .ok _) hfork
        (Xinst.avoidsAt_of_step (fun f' rsm' pc'' cevm' h hen hcr => by
          rw [hstep] at h; cases h; rw [henter] at hen; cases hen
          rw [← Frame.enter_run_currentTarget henter]; exact hcavoid))
        hrelChild (by rw [hstep]; exact ⟨_, RunFrame.of_run henter, hresume.symm⟩)
      obtain ⟨hrel, hroots⟩ := ihNext hfork (by
        intro root member
        simp only [Exec.rawFrameRoots, List.mem_cons] at member
        rcases member with rfl | member
        · exact hself
        · exact avoid root (by
            simp only [Exec.rawFrameRoots, Exec.rawFrameDescendants, List.mem_cons,
              List.mem_append]
            exact Or.inr (Or.inr (Or.inr member))))
      refine ⟨Execution.Rel.trans_left (Devm.codeAt_trans a) hc hrel, ?_⟩
      intro root member
      simp only [Exec.rawFrameRoots, Exec.rawFrameDescendants, List.mem_cons,
        List.mem_append] at member
      rcases member with rfl | rfl | member | member
      · rfl
      · exact hstart
      · exact (hrootsChild root (by simp [Exec.rawFrameRoots, member])).trans hstart
      · exact (hroots root (by simp [Exec.rawFrameRoots, member])).trans hc

end Blanc
