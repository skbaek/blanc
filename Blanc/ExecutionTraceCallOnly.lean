import Blanc.ExecutionTraceSystemCode
import Blanc.ExecutionDirectCode
import Blanc.ExecutionReachable
import Blanc.TransactionForward

/-!
# Executions that enter only `CALL` frames

A world whose every installed code reaches no call-type instruction other than `CALL`
(`CallOnlyReach`), and holds no EIP-7702 delegation designator, runs no `CREATE`: every frame an
execution started from such a world enters has a code address.  The fact is carried from one
interpreter derivation (`Exec.callOnly_roots`) through the message, transaction, system-call,
request, body and configured-block traces; the trace-level statements are exactly the creation
avoidance premise (`root.sevm.codeAddress = none → …`) that history theorems take.
-/

namespace Blanc

open Jaune

/-- Every call-type instruction at a reachable position (one no `PUSH` immediate covers) is
`CALL`. -/
def CallOnlyReach (code : ByteArray) : Prop :=
  ∀ pc x, noPushBefore code pc 32 = true → Xinst.At code pc x → x = .call

/-- Every installed code reaches only `CALL`, and none is a delegation designator. -/
def CodesCallOnly (code : Adr → ByteArray) : Prop :=
  ∀ a, CallOnlyReach (code a) ∧ ¬ isValidDelegation (code a)

theorem callOnlyReach_of_spawnFreeReach {code : ByteArray} (h : SpawnFreeReach code) :
    CallOnlyReach code :=
  fun pc x hb hx => absurd hx (h pc x hb)

/-- A `CALL` child frame carries a code address. -/
theorem genericCall.step_spawn_codeAddress
    {sevm : Sevm} {devm : Devm} {gas : Nat} {value : B256}
    {caller target codeAddress : Adr} {stv isSt : Bool}
    {ii isz oi osz : Nat} {code : ByteArray} {dp : Bool}
    {f : Frame} {rsm : Resume}
    (hs : genericCall.step sevm devm gas value caller target codeAddress stv
      isSt ii isz oi osz code dp = .spawn f rsm) :
    f.inner.codeAddress = some codeAddress := by
  simp only [genericCall.step, Bind.bind, Except.bind, Pure.pure,
    Except.pure] at hs
  repeat' split at hs
  all_goals simp only [XStep.ofExcept, XStep.spawn.injEq, reduceCtorEq] at hs
  all_goals obtain ⟨rfl, -⟩ := hs
  rfl

/-- **The frame a covered-fork `CALL` spawns** has a code address and runs the callee's own code
when the callee holds no delegation designator. -/
theorem Xinst.step_call_spawn
    {sevm : Sevm} {devm : Devm} {f : Frame} {rsm : Resume}
    (hfork : CoveredFork sevm.benvStat.fork)
    (spawn : Xinst.step sevm devm .call = XStep.spawn f rsm) :
    f.inner.codeAddress ≠ none ∧
      (¬ isValidDelegation (devm.getCode f.inner.currentTarget) →
        f.inner.code = devm.getCode f.inner.currentTarget) := by
  have hsg : sevm.benvStat.rules.stateGas = none := hfork.rules_stateGas_none
  rcases h1 : devm.pop with err | ⟨gas, d1⟩
  · simp only [Xinst.step, hsg, h1, Bind.bind, Except.bind, XStep.ofExcept,
      reduceCtorEq] at spawn
  rcases h2 : d1.popToAdr with err | ⟨callee, d2⟩
  · simp only [Xinst.step, hsg, h1, h2, Bind.bind, Except.bind, XStep.ofExcept,
      reduceCtorEq] at spawn
  rcases h3 : d2.pop with err | ⟨value, d3⟩
  · simp only [Xinst.step, hsg, h1, h2, h3, Bind.bind, Except.bind, XStep.ofExcept,
      reduceCtorEq] at spawn
  rcases h4 : d3.popToNat with err | ⟨ii, d4⟩
  · simp only [Xinst.step, hsg, h1, h2, h3, h4, Bind.bind, Except.bind, XStep.ofExcept,
      reduceCtorEq] at spawn
  rcases h5 : d4.popToNat with err | ⟨isz, d5⟩
  · simp only [Xinst.step, hsg, h1, h2, h3, h4, h5, Bind.bind, Except.bind, XStep.ofExcept,
      reduceCtorEq] at spawn
  rcases h6 : d5.popToNat with err | ⟨oi, d6⟩
  · simp only [Xinst.step, hsg, h1, h2, h3, h4, h5, h6, Bind.bind, Except.bind,
      XStep.ofExcept, reduceCtorEq] at spawn
  rcases h7 : d6.popToNat with err | ⟨osz, d7⟩
  · simp only [Xinst.step, hsg, h1, h2, h3, h4, h5, h6, h7, Bind.bind, Except.bind,
      XStep.ofExcept, reduceCtorEq] at spawn
  have hcode : (addAccessedAddress d7 callee).getCode callee =
      devm.getCode callee := by
    rw [addAccessedAddress_getCode]
    exact (Devm.popToNat_getCode h7).trans
      ((Devm.popToNat_getCode h6).trans
      ((Devm.popToNat_getCode h5).trans
      ((Devm.popToNat_getCode h4).trans
      ((Devm.pop_getCode h3).trans
      ((Devm.popToAdr_getCode h2).trans
        (Devm.pop_getCode h1))))))
  simp only [Xinst.step, hsg, h1, h2, h3, h4, h5, h6, h7,
    Bind.bind, Except.bind, Except.assert] at spawn
  repeat' split at spawn
  all_goals simp only [XStep.ofExcept, reduceCtorEq] at spawn
  all_goals first
    | cases spawn
    | have hf := genericCall.step_spawn_frame spawn
      have hca := genericCall.step_spawn_codeAddress spawn
      refine ⟨by rw [hca]; exact Option.some_ne_none _, fun notDelegation => ?_⟩
      have hnd : ¬ isValidDelegation
          ((addAccessedAddress d7 callee).getCode callee) := by
        rw [hcode, ← hf.2.1]
        exact notDelegation
      have hdel := Blanc.GasSchedule.accessDelegation_of_not_delegation
        (gas := sevm.benvStat.rules.gas) hnd
      rw [hf.2.2, congrArg (fun t => t.2.2.1) hdel, hcode]
      exact congrArg devm.getCode hf.2.1.symm

/-- A call-type byte is no `PUSH`, so the position after it is again reachable. -/
theorem noPushBefore_succ_of_xinst {code : ByteArray} {pc : Nat} {x : Xinst}
    (hx : Xinst.At code pc x) (hb : noPushBefore code pc 32 = true) :
    noPushBefore code (pc + 1) 32 = true := by
  obtain ⟨hpc, hty⟩ := getInst_exec_inv hx
  exact noPushBefore_succ_of_ne_p hpc hb (by rw [hty]; exact fun h => by cases h)

/-- **An execution of call-only code in a call-only world enters only frames with a code
address**, and so is creation-free. -/
theorem Exec.callOnly_roots {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out) (hfork : CoveredFork sevm.benvStat.fork)
    (hb : noPushBefore sevm.code pc 32 = true) (hcode : CallOnlyReach sevm.code)
    (hca : sevm.codeAddress ≠ none) (hworld : CodesCallOnly pre.getCode) :
    ∀ root ∈ Exec.rawFrameRoots run, root.sevm.codeAddress ≠ none := by
  revert hb hworld
  induction run with
  | halt hstep =>
      intro _ _ root member
      simp only [Exec.rawFrameRoots, Exec.rawFrameDescendants, List.mem_cons,
        List.not_mem_nil, or_false] at member
      subst member
      exact hca
  | @cont pc sevm devm pc' devm' ex hstep next ih =>
      intro hb hworld
      have hcodes : ∀ a, devm'.getCode a = devm.getCode a := by
        intro a
        exact Evm.step_codeAt (a := a) (xl := .none) (out := .ok _) hfork
          (Xinst.avoidsAt_of_step (fun f rsm pc' cevm h => by rw [hstep] at h; cases h))
          trivial (by rw [hstep]; exact ⟨rfl, rfl⟩)
      have hnext := ih hfork hcode hca (Evm.step_cont_noPush hstep hb)
        (fun a => by rw [hcodes a]; exact hworld a)
      intro root member
      simp only [Exec.rawFrameRoots, Exec.rawFrameDescendants, List.mem_cons] at member
      rcases member with rfl | member
      · exact hca
      · exact hnext root (List.mem_cons_of_mem _ member)
  | doneErr hstep henter hresume =>
      intro _ _ root member
      simp only [Exec.rawFrameRoots, Exec.rawFrameDescendants, List.mem_cons,
        List.not_mem_nil, or_false] at member
      subst member
      exact hca
  | @doneOk pc sevm devm f rsm pc' r devm' ex hstep henter hresume next ih =>
      intro hb hworld
      obtain ⟨x, hx, -, hpc'⟩ := Evm.step_spawn_inv hstep
      have hcodes : ∀ a, devm'.getCode a = devm.getCode a := by
        intro a
        exact Evm.step_codeAt (a := a) (xl := .none) (out := .ok _) hfork
          (Xinst.avoidsAt_of_step (fun f' rsm' pc' cevm h hen => by
            rw [hstep] at h; cases h; rw [henter] at hen; cases hen))
          trivial (by rw [hstep]; exact ⟨_, RunFrame.of_done henter, hresume.symm⟩)
      have hnext := ih hfork hcode hca (by rw [hpc']; exact noPushBefore_succ_of_xinst hx hb)
        (fun a => by rw [hcodes a]; exact hworld a)
      intro root member
      simp only [Exec.rawFrameRoots, Exec.rawFrameDescendants, List.mem_cons] at member
      rcases member with rfl | member
      · exact hca
      · exact hnext root (List.mem_cons_of_mem _ member)
  | @runErr pc sevm devm f rsm pc' cevm raw e hstep henter child hresume ih =>
      intro hb hworld
      obtain ⟨x, hx, hxs, -⟩ := Evm.step_spawn_inv hstep
      have hxcall : x = .call := hcode pc x hb hx
      subst hxcall
      obtain ⟨hcaf, hcodef⟩ := Xinst.step_call_spawn hfork hxs
      have hcac : cevm.sta.codeAddress ≠ none := by
        obtain ⟨_, _, hcev⟩ := Frame.enter_run_inv henter
        rw [hcev]; exact hcaf
      have hchild := Evm.step_spawn_child hstep henter
      have hccode : cevm.sta.code = devm.getCode cevm.sta.currentTarget := by
        rw [Frame.enter_run_code henter, Frame.enter_run_currentTarget henter]
        exact hcodef (hworld _).2
      have hroots := ih (Evm.step_spawn_child_fork hstep henter hfork)
        (by rw [hccode]; exact (hworld _).1) hcac
        (by rw [hchild.1]; exact noPushBefore_zero _ _)
        (fun a => by rw [hchild.2.1 a]; exact hworld a)
      intro root member
      simp only [Exec.rawFrameRoots, Exec.rawFrameDescendants, List.mem_cons] at member
      rcases member with rfl | member
      · exact hca
      · exact hroots root (by simp only [Exec.rawFrameRoots, List.mem_cons]; exact member)
  | @runOk pc sevm devm f rsm pc' cevm raw devm' ex hstep henter child hresume next
      ihChild ihNext =>
      intro hb hworld
      obtain ⟨x, hx, hxs, hpc'⟩ := Evm.step_spawn_inv hstep
      have hxcall : x = .call := hcode pc x hb hx
      subst hxcall
      obtain ⟨hcaf, hcodef⟩ := Xinst.step_call_spawn hfork hxs
      have hcac : cevm.sta.codeAddress ≠ none := by
        obtain ⟨_, _, hcev⟩ := Frame.enter_run_inv henter
        rw [hcev]; exact hcaf
      have hchild := Evm.step_spawn_child hstep henter
      have hforkc := Evm.step_spawn_child_fork hstep henter hfork
      have hccode : cevm.sta.code = devm.getCode cevm.sta.currentTarget := by
        rw [Frame.enter_run_code henter, Frame.enter_run_currentTarget henter]
        exact hcodef (hworld _).2
      have hrootsChild := ihChild hforkc
        (by rw [hccode]; exact (hworld _).1) hcac
        (by rw [hchild.1]; exact noPushBefore_zero _ _)
        (fun a => by rw [hchild.2.1 a]; exact hworld a)
      have hcodes : ∀ a, devm'.getCode a = devm.getCode a := by
        intro a
        obtain ⟨hrelChild, -⟩ := Exec.codeAt_avoid (a := a) child hforkc
          (fun root member hnone => absurd hnone (hrootsChild root member))
        exact Evm.step_codeAt (a := a) (xl := .some ⟨_, _⟩) (out := .ok _) hfork
          (Xinst.avoidsAt_of_step (fun f' rsm' pc'' cevm' h hen hcr => by
            rw [hstep] at h; cases h; rw [henter] at hen; cases hen
            exact absurd (Xinst.step_spawn_create_codeAddress hfork hxs hcr) hcaf))
          hrelChild (by rw [hstep]; exact ⟨_, RunFrame.of_run henter, hresume.symm⟩)
      have hrootsNext := ihNext hfork hcode hca
        (by rw [hpc']; exact noPushBefore_succ_of_xinst hx hb)
        (fun a => by rw [hcodes a]; exact hworld a)
      intro root member
      simp only [Exec.rawFrameRoots, Exec.rawFrameDescendants, List.mem_cons,
        List.mem_append] at member
      rcases member with rfl | rfl | member | member
      · exact hca
      · exact hcac
      · exact hrootsChild root (List.mem_cons_of_mem _ member)
      · exact hrootsNext root (List.mem_cons_of_mem _ member)

/-- A decoded instruction that is a call-type instruction other than `CALL`. -/
def nonCallExec : Option Inst → Bool
  | some (.next (.exec x)) => x != .call
  | _ => false

/-- The linear instruction walk refusing every decoded call-type instruction but `CALL`. -/
def callOnlyScan (cd : ByteArray) : Nat → Nat → Bool
  | 0, _ => true
  | fuel + 1, k =>
      if hk : k < cd.size then
        !nonCallExec (cd.getInst k) && callOnlyScan cd fuel (k + 1 + pushWidth cd[k])
      else true

/-- The decidable check for `CallOnlyReach`. -/
def callOnlyCheck (cd : ByteArray) : Bool := callOnlyScan cd cd.size 0

private theorem callOnlyScan_good {cd : ByteArray} {j : Nat}
    (h : ∃ fuel, cd.size ≤ j + fuel ∧ callOnlyScan cd fuel j = true) (hj : j < cd.size) :
    nonCallExec (cd.getInst j) = false ∧
      ∃ fuel, cd.size ≤ (j + 1 + pushWidth cd[j]) + fuel ∧
        callOnlyScan cd fuel (j + 1 + pushWidth cd[j]) = true := by
  obtain ⟨fuel, hfuel, hscan⟩ := h
  cases fuel with
  | zero => omega
  | succ f =>
      simp only [callOnlyScan, hj, ↓reduceDIte, Bool.and_eq_true, Bool.not_eq_true'] at hscan
      exact ⟨hscan.1, f, by omega, hscan.2⟩

theorem callOnlyReach_of_check {cd : ByteArray} (h : callOnlyCheck cd = true) :
    CallOnlyReach cd := by
  intro pc x hb hx
  obtain ⟨hpc, -⟩ := getInst_exec_inv hx
  have hreach := PushReach.of_noPushBefore cd pc hpc hb
  have key : ∀ j, PushReach cd j →
      ∃ fuel, cd.size ≤ j + fuel ∧ callOnlyScan cd fuel j = true := by
    intro j hj
    induction hj with
    | zero => exact ⟨cd.size, by omega, h⟩
    | step hp _ ih => exact (callOnlyScan_good ih hp).2
  have hgood := (callOnlyScan_good (key pc hreach) hpc).1
  have hxat : cd.getInst pc = some (.next (.exec x)) := hx
  rw [hxat] at hgood
  simp only [nonCallExec, bne_eq_false_iff_eq] at hgood
  exact hgood

theorem callOnlyReach_empty : CallOnlyReach ByteArray.empty := by
  intro pc x _ hx
  obtain ⟨hpc, -⟩ := getInst_exec_inv hx
  exact absurd hpc (Nat.not_lt_zero pc)

theorem not_isValidDelegation_empty : ¬ isValidDelegation ByteArray.empty := by
  intro h
  exact absurd h.1 (by decide)

/-- Destroying an account keeps a call-only world call-only: the destroyed code becomes empty. -/
theorem codesCallOnly_destroyAccount {w : State} (x : Adr) (h : CodesCallOnly w.getCode) :
    CodesCallOnly (destroyAccount w x).getCode := by
  intro a
  have hcases : (destroyAccount w x).getCode a = w.getCode a ∨
      (destroyAccount w x).getCode a = ByteArray.empty := by
    unfold destroyAccount State.getCode State.get
    rw [Std.TreeMap.getD_erase]
    split
    · exact Or.inr rfl
    · exact Or.inl rfl
  rcases hcases with heq | heq
  · rw [heq]; exact h a
  · rw [heq]; exact ⟨callOnlyReach_empty, not_isValidDelegation_empty⟩

theorem codesCallOnly_foldl_destroyAccount :
    ∀ (xs : List Adr) {w : State}, CodesCallOnly w.getCode →
      CodesCallOnly (xs.foldl destroyAccount w).getCode := by
  intro xs
  induction xs with
  | nil => intro w h; exact h
  | cons x xs ih =>
      intro w h
      exact ih (codesCallOnly_destroyAccount x h)

theorem codesCallOnly_congr {c c' : Adr → ByteArray} (heq : ∀ a, c' a = c a)
    (h : CodesCallOnly c) : CodesCallOnly c' := by
  intro a
  rw [heq a]
  exact h a

namespace ExecutionTrace

/-- A retained slot entered by a call-only frame into a call-only world holds only frames with a
code address. -/
theorem RetainedXlot.callOnly {frame : Frame} {slot : Xlot}
    {out : Except (EvmError × State × AdrSet × Tra) Devm}
    (retained : RetainedXlot slot) (hrun : RunFrame frame slot out)
    (hfork : CoveredFork frame.inner.benv.stat.fork)
    (hca : frame.inner.codeAddress ≠ Option.none) (hcode : CallOnlyReach frame.inner.code)
    (hworld : CodesCallOnly frame.inner.benv.state.getCode) :
    ∀ root ∈ retained.rawFrames, root.sevm.codeAddress ≠ Option.none := by
  cases retained with
  | none => intro root member; simp only [RetainedXlot.rawFrames, List.not_mem_nil] at member
  | @some pc sevm pre execution run =>
      obtain ⟨henter, _⟩ := RunFrame.some_inv hrun
      have hpc : pc = 0 := Frame.enter_run_pc henter
      have hstat := Frame.enter_run_benvStat henter
      obtain ⟨_, _, hevm⟩ := Frame.enter_run_inv henter
      have hsevm : sevm.code = frame.inner.code := Frame.enter_run_code henter
      have hcas : sevm.codeAddress = frame.inner.codeAddress := by
        have := congrArg (fun e : Evm => e.sta.codeAddress) hevm
        exact this
      exact Exec.callOnly_roots run (by rw [hstat]; exact hfork)
        (by rw [hpc]; exact noPushBefore_zero _ _) (by rw [hsevm]; exact hcode)
        (by rw [hcas]; exact hca)
        (codesCallOnly_congr (fun a => Frame.enter_run_getCode henter a) hworld)

/-- **A settled call message running call-only, non-delegating code in a call-only world, with no
authorizations, enters only frames with a code address, and leaves a call-only world.** -/
theorem MessageCallTrace.callOnly {msg : Msg} {state : State} {out : MsgCallOutput}
    (trace : MessageCallTrace msg state out) (hfork : CoveredFork msg.benv.stat.fork)
    (htarget : msg.target.isNone = false)
    (hauths : msg.tenv.stat.auths.isEmpty = true)
    (hnd : getDelegatedCodeAddress msg.code = none)
    (hca : msg.codeAddress ≠ Option.none) (hcode : CallOnlyReach msg.code)
    (hworld : CodesCallOnly msg.benv.state.getCode) :
    (∀ root ∈ trace.rawFrames, root.sevm.codeAddress ≠ Option.none) ∧
      CodesCallOnly state.getCode := by
  have hroots : ∀ root ∈ trace.rawFrames, root.sevm.codeAddress ≠ Option.none := by
    cases trace with
    | createCollision =>
        intro root member
        simp only [MessageCallTrace.rawFrames, List.not_mem_nil] at member
    | createRun target =>
        rw [htarget] at target
        cases target
    | callRun target delegated refund delegation execMsg execMsgEq evm core coreTrace result =>
        have hdeleg : messageCallDelegation msg = .ok ⟨msg, 0⟩ := by
          unfold messageCallDelegation
          simp only [hauths, ↓reduceIte]
        have hdelegEq := Except.ok.inj (hdeleg.symm.trans delegation)
        simp only [Prod.mk.injEq] at hdelegEq
        obtain ⟨rfl, -⟩ := hdelegEq
        have hexec : execMsg = msg := by
          rw [execMsgEq]
          unfold messageCallExecutionMessage
          simp only [hnd]
        subst hexec
        exact RetainedXlot.callOnly coreTrace.retained coreTrace.run hfork hca hcode hworld
  refine ⟨hroots, ?_⟩
  have hpost := fun a => (trace.codeAt (a := a) hfork
    (fun h => by rw [htarget] at h; cases h)
    (fun auth hmem => by
      rw [List.isEmpty_iff] at hauths
      rw [hauths] at hmem
      exact absurd hmem List.not_mem_nil)
    (fun root member hnone => absurd hnone (hroots root member))).1
  exact codesCallOnly_congr hpost hworld

/-- The message call trace's frames, in the message vocabulary of a system call. -/
theorem SystemMessageTrace.callOnly {benv : Benv} {target : Adr} {data : Bytes}
    {state : State} {out : MsgCallOutput}
    (trace : SystemMessageTrace benv target data state out)
    (hfork : CoveredFork benv.stat.fork)
    (hworld : CodesCallOnly benv.state.getCode) :
    (∀ root ∈ trace.rawFrames, root.sevm.codeAddress ≠ Option.none) ∧
      CodesCallOnly state.getCode := by
  have hcode : (systemTransactionMessage benv target data).code = benv.state.getCode target := rfl
  have hnd : getDelegatedCodeAddress (systemTransactionMessage benv target data).code = none := by
    rw [hcode]
    have h : ¬ isValidDelegation (benv.state.getCode target) := (hworld target).2
    simp only [getDelegatedCodeAddress, h, ite_false]
  exact trace.message.callOnly hfork rfl rfl hnd (Option.some_ne_none _)
    (by rw [hcode]; exact (hworld target).1) hworld

/-- A type-2 (or other) call transaction with no authorizations, in a call-only world, enters
only frames with a code address and leaves a call-only world. -/
theorem TransactionTrace.callOnly {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    {state : State} {bout' : BlockOutput}
    (trace : TransactionTrace benv bout tx index state bout')
    (hfork : CoveredFork benv.stat.fork) {t : Adr}
    (hreceiver : tx.type.receiver? = some t) (hauths : tx.auths = [])
    (hworld : CodesCallOnly benv.state.getCode) :
    (∀ root ∈ trace.rawFrames, root.sevm.codeAddress ≠ Option.none) ∧
      CodesCallOnly state.getCode := by
  have hmsgEq : trace.msg = callMessage { benv.beginTransaction with state := trace.debitState }
      (transactionTenv benv.beginTransaction tx index trace.sender trace.effectiveGasPrice
        trace.intrinsicGas trace.blobVersionedHashes) tx t :=
    Except.ok.inj (trace.prepared.symm.trans (prepareMessage_call hreceiver))
  have hdebit : ∀ a, trace.debitState.getCode a = benv.state.getCode a := by
    intro a
    rw [State.subBal_getCode trace.debit]
    unfold State.getCode
    rw [State.incrNonce_get_code]
  have hmsgWorld : CodesCallOnly trace.msg.benv.state.getCode := by
    rw [hmsgEq]
    exact codesCallOnly_congr hdebit hworld
  have hmsgCode : trace.msg.code = benv.state.getCode t := by
    rw [hmsgEq]
    exact hdebit t
  have hnd : getDelegatedCodeAddress trace.msg.code = none := by
    rw [hmsgCode]
    have h : ¬ isValidDelegation (benv.state.getCode t) := (hworld t).2
    simp only [getDelegatedCodeAddress, h, ite_false]
  have hmsgFork : CoveredFork trace.msg.benv.stat.fork := by
    rw [hmsgEq]; exact hfork
  obtain ⟨hroots, hstate⟩ := trace.message.callOnly hmsgFork
    (by rw [hmsgEq]; rfl)
    (by rw [hmsgEq]; simp only [callMessage, transactionTenv, hauths, List.isEmpty_nil])
    hnd (by rw [hmsgEq]; exact Option.some_ne_none _)
    (by rw [hmsgCode]; exact (hworld t).1) hmsgWorld
  refine ⟨hroots, ?_⟩
  obtain ⟨refundCounter, -, hfinal⟩ := trace.exists_finalStateForm hfork
  rw [hfinal]
  apply codesCallOnly_foldl_destroyAccount
  refine codesCallOnly_congr (fun a => ?_) hstate
  rw [State.addBal_getCode, State.addBal_getCode]

theorem ApplyTransactionsTrace.callOnly {txs : List (Nat × Tx)} {benv finalBenv : Benv}
    {bout finalBout : BlockOutput}
    (trace : ApplyTransactionsTrace txs benv bout finalBenv finalBout)
    (hfork : CoveredFork benv.stat.fork)
    (hcalls : ∀ p ∈ txs, (∃ t, p.2.type.receiver? = some t) ∧ p.2.auths = [])
    (hworld : CodesCallOnly benv.state.getCode) :
    (∀ root ∈ trace.rawFrames, root.sevm.codeAddress ≠ Option.none) ∧
      CodesCallOnly finalBenv.state.getCode := by
  induction trace with
  | nil =>
      exact ⟨fun root member => by
        simp only [ApplyTransactionsTrace.rawFrames, List.not_mem_nil] at member, hworld⟩
  | @cons index tx txs benv bout txState txBout finalBenv finalBout head tail ih =>
      obtain ⟨⟨t, ht⟩, hauths⟩ := hcalls _ (List.mem_cons_self ..)
      obtain ⟨hheadRoots, hheadWorld⟩ := head.callOnly hfork ht hauths hworld
      obtain ⟨htailRoots, htailWorld⟩ := ih hfork
        (fun p hp => hcalls p (List.mem_cons_of_mem _ hp)) hheadWorld
      refine ⟨fun root member => ?_, htailWorld⟩
      simp only [ApplyTransactionsTrace.rawFrames, List.mem_append] at member
      rcases member with member | member
      · exact hheadRoots root member
      · exact htailRoots root member

theorem RequestsTrace.callOnly {benv : Benv} {bout : BlockOutput} {state : State}
    {bout' : BlockOutput} (trace : RequestsTrace benv bout state bout')
    (hfork : CoveredFork benv.stat.fork)
    (hworld : CodesCallOnly benv.state.getCode) :
    (∀ root ∈ trace.rawFrames, root.sevm.codeAddress ≠ Option.none) ∧
      CodesCallOnly state.getCode := by
  obtain ⟨hW, hWworld⟩ := trace.withdrawal.callOnly hfork hworld
  obtain ⟨hC, hCworld⟩ := trace.consolidation.callOnly hfork hWworld
  refine ⟨fun root member => ?_, ?_⟩
  · simp only [RequestsTrace.rawFrames, List.mem_append] at member
    rcases member with member | member
    · exact hW root member
    · exact hC root member
  · rw [trace.state_eq_consolidationState]
    exact hCworld

/-- **A block body whose transactions are calls without authorizations, in a call-only world,
enters only frames with a code address and leaves a call-only world.** -/
theorem AppliedBodyTrace.callOnly {benv : Benv} {txs : List (Bytes ⊕ Tx)}
    {wds : List Withdrawal} {state : State} {bout : BlockOutput}
    (trace : AppliedBodyTrace benv txs wds state bout)
    (hfork : CoveredFork benv.stat.fork)
    (hcalls : ∀ p ∈ trace.decodedTxs.putIndex,
      (∃ t, p.2.type.receiver? = some t) ∧ p.2.auths = [])
    (hworld : CodesCallOnly benv.state.getCode) :
    (∀ root ∈ trace.rawFrames, root.sevm.codeAddress ≠ Option.none) ∧
      CodesCallOnly state.getCode := by
  obtain ⟨hB, hBworld⟩ := trace.beacon.callOnly hfork hworld
  obtain ⟨hH, hHworld⟩ := trace.history.callOnly hfork hBworld
  obtain ⟨hT, hTworld⟩ := trace.transactions.callOnly hfork hcalls hHworld
  have hforkT : CoveredFork trace.transactionBenv.stat.fork := by
    rw [trace.transactions.stat_eq]
    exact hfork
  obtain ⟨hR, hRworld⟩ := trace.requests.callOnly hforkT
    (codesCallOnly_congr (fun a => processWithdrawalsState_getCode _ wds a) hTworld)
  refine ⟨fun root member => ?_, ?_⟩
  · simp only [AppliedBodyTrace.rawFrames, List.mem_append] at member
    rcases member with ((member | member) | member) | member
    · exact hB root member
    · exact hH root member
    · exact hT root member
    · exact hR root member
  · rw [← trace.requestState_eq]
    exact hRworld

/-- The configured-block form: every raw frame has a code address (so the trace satisfies every
creation-avoidance premise), and the post-chain world is again call-only. -/
theorem ConfiguredBlockTrace.callOnly {cfg : ChainConfig} {pre post : BlockChain}
    (trace : ConfiguredBlockTrace cfg pre post)
    (hcalls : ∀ p ∈ trace.bodyTrace.decodedTxs.putIndex,
      (∃ t, p.2.type.receiver? = some t) ∧ p.2.auths = [])
    (hworld : CodesCallOnly pre.state.getCode) :
    (∀ root ∈ trace.rawFrames, root.sevm.codeAddress ≠ Option.none) ∧
      CodesCallOnly post.state.getCode := by
  obtain ⟨hroots, hstate⟩ := trace.bodyTrace.callOnly trace.covered hcalls hworld
  refine ⟨hroots, ?_⟩
  rw [trace.postEq]
  exact hstate

end ExecutionTrace

end Blanc
