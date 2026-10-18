import Blanc.Lift.FrameSkip
import Blanc.Lift.Quiet
import Blanc.Lift.CursorFrames
import Blanc.Lift.SpawnExact
import Blanc.ExecutionMessageEffects
import Blanc.StaticStorage

/-!
# Quiet-`DELEGATECALL` skip: crossing code whose only external call runs quiet code

Route C's second skip theorem (C2).  A `DELEGATECALL` runs foreign code at the caller's storage
owner; when that code is *quiet* — a successful frame running it keeps its storage owner's
storage (`QuietCode`) — the call keeps the caller's storage, and a closure of internal calls whose
only external instruction is such a call keeps it too:

* `ProcessMessage.getStor_of_quietCode`: a call message running quiet code with no value transfer
  leaves its storage owner's storage as the message found it (committed, rolled back or
  childless);
* `Ninst.delegatecall_getStor_of_quiet`: one `DELEGATECALL` step whose code-address operand holds
  quiet, undelegated code keeps the frame's storage owner's storage;
* `Ninst.Run.getCode_eq`: every step keeps a nonempty account code;
* `ric_delegatecall_quiet`: the walk form of that step over `St b (g :: w :: ii :: is :: oi ::
  os :: S) M G`;
* `SFunc.RunP.framed`: a checked run whose certificate satisfies a frame predicate `P`
  (`Cert.framesSat`) satisfies `P` at every step it takes, over a frame matching the actual stack;
* `SFunc.RunP.qdKeep`: a framed run of a `QuietDelegateSet` closure whose every `DELEGATECALL`
  names the constant word `aw` keeps the storage owner's storage and `aw`'s code (`QDKeep`);
* `ric_call_quietDelegate`: a `callNext` into such a closure, inverted over the walk state
  `St b (dd :: S) M G`: the continuation runs from a state with `b`'s storage owner storage and
  `aw`'s code, and the stack `Y ++ S.drop e.frame.length`, `Y.length = e.rets`.

Nothing here mentions a contract.
-/

namespace Blanc.Lift

open Jaune Blanc

/-! ## Quiet code -/

/-- **Quiet code**: a successful frame running `code` from pc `0` on a covered fork keeps its
storage owner's storage.  (The shape of a library-quietness fact, with no contract named.) -/
def QuietCode (code : ByteArray) : Prop :=
  ∀ {sevm : Sevm} {pre post : Devm}, Exec 0 sevm pre (.ok post) → sevm.code = code →
    CoveredFork sevm.benvStat.fork →
      Devm.getStor post sevm.currentTarget = Devm.getStor pre sevm.currentTarget

/-- **A call message running quiet code keeps its owner's storage.**  With no value transfer, a
message whose code is quiet settles to a world whose storage owner's storage is the message's:
a committed child is quiet, a rolled-back or childless one restores or keeps the entry world. -/
theorem ProcessMessage.getStor_of_quietCode {code : ByteArray} (hq : QuietCode code)
    {msg : Msg} {xl : Xlot} {child : Devm} (filled : xl.Filled)
    (process : ProcessMessage msg xl (.ok child)) (noTransfer : msg.shouldTransferValue = false)
    (hcode : msg.code = code) (fork : CoveredFork msg.benv.stat.fork) :
    child.state.getStor msg.currentTarget = msg.benv.state.getStor msg.currentTarget := by
  have safe : msg.shouldTransferValue = false ∨ msg.value = 0 ∨
      (msg.caller = msg.currentTarget ∧ State.Protected msg.benv.state msg.caller) := .inl noTransfer
  cases xl with
  | none =>
      rcases ProcessMessage.none_ok_state_cases process with rollback | ⟨benv, transfer, eq⟩
      · rw [rollback]
      · rw [eq, Msg.getStor_eq_of_safeTransfer transfer safe]
  | some p =>
      obtain ⟨cevm, raw⟩ := p
      obtain ⟨childRun⟩ := filled
      obtain ⟨enter, settledEq⟩ := RunFrame.some_inv process
      by_cases settles : Frame.settlementCommits (Frame.ofCall msg) raw = true
      · have committed := Frame.raw_commits_of_settlementCommits settles
        have cfork : CoveredFork cevm.sta.benvStat.fork := by
          rw [Frame.enter_run_benvStat enter]; exact fork
        obtain ⟨cpc, csevm, cdevm⟩ := cevm
        have postState : child.state = (Execution.committedPost raw committed).state :=
          ProcessMessage.ok_state_eq_committedPost process committed
        obtain ⟨benv, transfer, evmEq⟩ := Frame.enter_run_inv enter
        simp only [Frame.ofCall, initEvm, Evm.mk.injEq] at evmEq
        obtain ⟨rfl, rfl, rfl⟩ := evmEq
        cases raw with
        | error e => simp only [Execution.commits, Bool.false_eq_true] at committed
        | ok x =>
            have quiet := hq childRun (by rw [← hcode]; rfl) cfork
            rw [postState]
            refine quiet.trans ?_
            show benv.state.getStor msg.currentTarget = _
            rw [Msg.getStor_eq_of_safeTransfer transfer safe]
            rfl
      · have postError : child.error.isSome = true := by
          cases errorEq : child.error with
          | some e => rfl
          | none =>
              exfalso
              apply settles
              unfold Frame.settlementCommits
              rw [← settledEq]
              simp only [errorEq, Option.isNone_none]
        rw [(ProcessMessage.rollback_of_error process postError).1]

/-- **One `DELEGATECALL` into quiet code keeps the frame's storage owner's storage.**  The
code-address operand `w` holds undelegated quiet code; the child (if any) runs it at the caller's
storage owner with no value transfer. -/
theorem Ninst.delegatecall_getStor_of_quiet {code : ByteArray} (hq : QuietCode code)
    {sevm : Sevm} {pre post : Devm} (hfork : CoveredFork sevm.benvStat.fork)
    {g w : B256} {s : List B256} (hstack : pre.stack = g :: w :: s)
    (hcode : pre.getCode w.toAdr = code) (undelegated : getDelegatedCodeAddress code = none)
    (run : Ninst.Run sevm pre (.exec .delegatecall) post) :
    Devm.getStor post sevm.currentTarget = Devm.getStor pre sevm.currentTarget := by
  obtain ⟨xl, filled, pc, stepRun⟩ := run
  have xrun : XStep.Run (Xinst.step sevm pre .delegatecall) xl (.ok post) := by
    simpa only [Ninst.StepRun, Ninst.step_exec, XStep.run_toStep] using stepRun
  cases hs : Xinst.step sevm pre .delegatecall with
  | done e =>
      rw [hs] at xrun
      obtain ⟨-, rfl⟩ := xrun
      exact Xinst.step_done_getStor hfork hs _
  | spawn f rsm =>
      rw [hs] at xrun
      obtain ⟨r, frameRun, resumed⟩ := xrun
      obtain ⟨htarget, -, -, -, -, hfcode, -⟩ :=
        Xinst.step_delegatecall_spawn_exact hfork hs hstack (by rw [hcode]; exact undelegated)
      obtain ⟨-, -, -, hnoTransfer, hstat, -⟩ := Xinst.step_delegatecall_spawn_meta hfork hs
      rcases Xinst.step_shapeCovered sevm pre .delegatecall hfork with
        ⟨_, shape, -⟩ | ⟨_, _, _, _, _, _, shape⟩ |
        ⟨d, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hprefix, -, -, -, shape⟩ <;>
        rw [shape] at hs
      · cases hs
      · obtain ⟨rfl, -⟩ := genericCreate_step_spawn_exact hs
        obtain ⟨-, -, hcreate, -⟩ := Xinst.step_delegatecall_spawn_meta hfork (shape ▸ hs)
        cases hcreate
      · obtain ⟨rfl, rfl⟩ := genericCall_step_spawn_exact hs
        dsimp only [Frame.ofCall] at htarget hfcode hnoTransfer hstat
        cases r with
        | error e => exact (Resume.call_run_error resumed.symm).elim
        | ok child =>
            have childState : post.state = child.state := Resume.call_state resumed.symm
            have keep := ProcessMessage.getStor_of_quietCode hq filled frameRun hnoTransfer
              (hfcode.trans hcode) (hstat ▸ hfork)
            show post.state.getStor sevm.currentTarget = pre.state.getStor sevm.currentTarget
            rw [childState, ← htarget]
            refine keep.trans ?_
            rw [htarget]
            exact (hprefix.getStor sevm.currentTarget).symm

/-- Every step keeps the code of an account whose code is nonempty (only `CREATE` installs code,
at a fresh account). -/
theorem Ninst.Run.getCode_eq {sevm : Sevm} {pre post : Devm} {n : Ninst} {a : Adr}
    (run : Ninst.Run sevm pre n post) (nonempty : (pre.getCode a).toList ≠ []) :
    post.getCode a = pre.getCode a := by
  obtain ⟨xl, filled, pc, steps⟩ := run
  have slotCode : Xlot.Rel Devm.CodePreserve xl := by
    rcases xl with _ | ⟨evm, raw⟩
    · trivial
    · obtain ⟨childRun⟩ := filled
      cases raw <;> exact Exec.preserves_getCode childRun
  exact Ninst.codePreserve_effectRec n slotCode steps a nonempty

/-- **Crossing one `DELEGATECALL` into quiet code, walk form.**  From
`St b (g :: w :: ii :: is :: oi :: os :: S) M G`, with `w` holding nonempty undelegated quiet code,
the continuation runs from a state with `b`'s storage owner storage, `w`'s code, and a flag above
`S`. -/
theorem ric_delegatecall_quiet {code : ByteArray} (hq : QuietCode code) {fs : List SFunc}
    {sevm : Sevm} {C : List Nat} {b : Devm} {g w ii is oi os : B256} {S : List B256} {M : Mem}
    {G : Nat} {f : SFunc} {r : Seg} (hfork : CoveredFork sevm.benvStat.fork)
    (hcode : b.getCode w.toAdr = code) (undelegated : getDelegatedCodeAddress code = none)
    (nonempty : code.toList ≠ [])
    (run : SFunc.RunCut fs sevm C (St b (g :: w :: ii :: is :: oi :: os :: S) M G)
      (.next (.exec .delegatecall) f) r) :
    ∃ b' x M' G', Devm.getStor b' sevm.currentTarget = Devm.getStor b sevm.currentTarget ∧
      b'.getCode w.toAdr = code ∧ SFunc.RunCut fs sevm C (St b' (x :: S) M' G') f r := by
  obtain ⟨d, step, k⟩ := ric_next run
  have hframe : FrameMatches 0 [.unk, .unk, .unk, .unk, .unk, .unk] [g, w, ii, is, oi, os] :=
    .cons trivial (.cons trivial (.cons trivial (.cons trivial (.cons trivial
      (.cons trivial .nil)))))
  obtain ⟨X, hX, hfr⟩ := Cursor.absNinst_run_stack (a' := [.unk]) hfork rfl
    (rest := S) rfl hframe step
  obtain ⟨x, rfl⟩ : ∃ x, X = [x] := by
    match X, List.Forall₂.length_eq hfr with
    | [x], _ => exact ⟨x, rfl⟩
  refine ⟨d, x, d.memory, d.gasLeft,
    Ninst.delegatecall_getStor_of_quiet (pre := St b _ M G) hq hfork rfl hcode undelegated step,
    (Ninst.Run.getCode_eq step (by exact hcode ▸ nonempty)).trans hcode, ?_⟩
  rw [← St.self (S := x :: S) hX rfl]
  exact k

/-! ## Frame predicates along a checked run -/

/-- A step that runs and, when it is an external instruction, runs from a stack whose top words
match an abstract frame `a` with `P n a`. -/
def FramedStep (P : Ninst → List AVal → Bool) (sevm : Sevm) (d : Devm) (n : Ninst) (d' : Devm) :
    Prop :=
  Ninst.Run sevm d n d' ∧ ∀ x, n = .exec x →
    ∃ ρ a X R, d.stack = X ++ R ∧ FrameMatches ρ a X ∧ P n a = true

/-- `FrameAt` with the frame predicate `P` holding along the tree at the same frame. -/
def FrameSat (code : ByteArray) (c : Cert) (P : Ninst → List AVal → Bool) (m pc : Nat)
    (a : List AVal) (ρ : B256) (R : List B256) (d : Devm) (f : SFunc) : Prop :=
  FrameAt code c m pc a ρ R d f ∧ f.framesSat c.entries P a = true

section Framed

variable {code : ByteArray} {c : Cert} {P : Ninst → List AVal → Bool}

/-- Entry `k` of a certificate passing `Cert.framesSat` passes `framesSat` at its declared
frame. -/
theorem Cert.framesSat_entry (hfs : c.framesSat P = true) {k : Nat} {e : Entry} {g : SFunc}
    (he : c.entries[k]? = some e) (hg : c.prog[k]? = some g) :
    g.framesSat c.entries P e.frame = true := by
  simp only [Cert.entries, Cert.prog, List.getElem?_map, Option.map_eq_some_iff] at he hg
  obtain ⟨p, hp, rfl⟩ := he
  obtain ⟨q, hq, rfl⟩ := hg
  rw [hp] at hq
  cases hq
  exact List.all_eq_true.mp hfs p (List.mem_of_getElem? hp)

/-- Entering entry `k` from its declared frame above `R`. -/
theorem FrameSat.enter (hc : Cert.check code c = true) (hfs : c.framesSat P = true) {k : Nat}
    {e : Entry} {g : SFunc} (he : c.entries[k]? = some e) (hg : c.prog[k]? = some g) {m : Nat}
    (hrets : e.rets = m) {ρ : B256} {X R : List B256} {d : Devm} (hst : d.stack = X ++ R)
    (hfr : FrameMatches ρ e.frame X) : FrameSat code c P m e.pc e.frame ρ R d g :=
  ⟨⟨hrets ▸ cert_check_at hc k e g he hg, X, hst, hfr⟩, Cert.framesSat_entry hfs he hg⟩

/-- **A checked run satisfies the frame predicate at every step.**  From a node whose tree checks
and passes `framesSat` at its frame, a run of a certificate passing `Cert.framesSat P` is a run
whose every step is a `FramedStep P`. -/
theorem SFunc.RunP.framed (hc : Cert.check code c = true) (hfs : c.framesSat P = true)
    {sevm : Sevm} (hfork : CoveredFork sevm.benvStat.fork) {d : Devm} {f : SFunc} {o : Outcome}
    (run : SFunc.Run c.prog sevm d f o) :
    ∀ {m pc : Nat} {a : List AVal} {ρ : B256} {R : List B256},
      FrameSat code c P m pc a ρ R d f → SFunc.RunP (FramedStep P) c.prog sevm d f o := by
  induction run with
  | @zero _ _ f g _ t pop _ ih =>
    intro m pc a ρ R ⟨⟨hcheck, X, hst, hfr⟩, hsat⟩
    match a, hcheck, hfr, hsat with
    | .const tt :: v :: a', hcheck, hfr, hsat =>
      have h' : (byteAt code pc = some (Jinst.toUInt8 .jumpi) ∧
            (v.jumps? = some true ∨ checkNode code c.entries m (pc + 1) a' f = true)) ∧
          (v.jumps? = some false ∨ checkNode code c.entries m tt.toNat a' g = true) := by
        simpa only [checkNode, Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true] using hcheck
      simp only [SFunc.framesSat, Bool.and_eq_true] at hsat
      obtain ⟨_, X1, hst1, hfr1⟩ := Cursor.pop_two_frame hst hfr pop
      exact .zero t pop (ih ⟨⟨live_fall (Cursor.pop_two_second hst hfr pop) h'.1.2, X1, hst1,
        hfr1⟩, hsat.1⟩)
    | [], hcheck, _, _ => simp only [checkNode, Bool.false_eq_true] at hcheck
    | [.const _], hcheck, _, _ => simp only [checkNode, Bool.false_eq_true] at hcheck
    | .ret :: _, hcheck, _, _ => simp only [checkNode, Bool.false_eq_true] at hcheck
    | .unk :: _, hcheck, _, _ => simp only [checkNode, Bool.false_eq_true] at hcheck
  | @succ _ _ f g _ t w hw pop _ ih =>
    intro m pc a ρ R ⟨⟨hcheck, X, hst, hfr⟩, hsat⟩
    match a, hcheck, hfr, hsat with
    | .const tt :: v :: a', hcheck, hfr, hsat =>
      have h' : (byteAt code pc = some (Jinst.toUInt8 .jumpi) ∧
            (v.jumps? = some true ∨ checkNode code c.entries m (pc + 1) a' f = true)) ∧
          (v.jumps? = some false ∨ checkNode code c.entries m tt.toNat a' g = true) := by
        simpa only [checkNode, Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true] using hcheck
      simp only [SFunc.framesSat, Bool.and_eq_true] at hsat
      obtain ⟨_, X1, hst1, hfr1⟩ := Cursor.pop_two_frame hst hfr pop
      exact .succ t w hw pop (ih ⟨⟨live_taken hw (Cursor.pop_two_second hst hfr pop) h'.2, X1,
        hst1, hfr1⟩, hsat.2⟩)
    | [], hcheck, _, _ => simp only [checkNode, Bool.false_eq_true] at hcheck
    | [.const _], hcheck, _, _ => simp only [checkNode, Bool.false_eq_true] at hcheck
    | .ret :: _, hcheck, _, _ => simp only [checkNode, Bool.false_eq_true] at hcheck
    | .unk :: _, hcheck, _, _ => simp only [checkNode, Bool.false_eq_true] at hcheck
  | @toZero _ _ f k _ t pop _ ih =>
    intro m pc a ρ R ⟨⟨hcheck, X, hst, hfr⟩, hsat⟩
    match a, hcheck, hfr, hsat with
    | .const tt :: v :: a', hcheck, hfr, hsat =>
      cases hk : c.entries[k]? with
      | none => simp only [checkNode, hk, Bool.false_eq_true] at hcheck
      | some e =>
        have h' : (((byteAt code pc = some (Jinst.toUInt8 .jumpi) ∧ e.pc = tt.toNat) ∧
              e.rets = m) ∧ gotoCompat a' e.frame = true) ∧
              (v.jumps? = some true ∨ checkNode code c.entries m (pc + 1) a' f = true) := by
          simpa only [checkNode, hk, Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true] using hcheck
        simp only [SFunc.framesSat] at hsat
        obtain ⟨_, X1, hst1, hfr1⟩ := Cursor.pop_two_frame hst hfr pop
        exact .toZero t pop (ih ⟨⟨live_fall (Cursor.pop_two_second hst hfr pop) h'.2, X1, hst1,
          hfr1⟩, hsat⟩)
    | [], hcheck, _, _ => simp only [checkNode, Bool.false_eq_true] at hcheck
    | [.const _], hcheck, _, _ => simp only [checkNode, Bool.false_eq_true] at hcheck
    | .ret :: _, hcheck, _, _ => simp only [checkNode, Bool.false_eq_true] at hcheck
    | .unk :: _, hcheck, _, _ => simp only [checkNode, Bool.false_eq_true] at hcheck
  | @toSucc _ _ f _ k _ t w hw lookup pop _ ih =>
    intro m pc a ρ R ⟨⟨hcheck, X, hst, hfr⟩, _⟩
    match a, hcheck, hfr with
    | .const tt :: v :: a', hcheck, hfr =>
      cases hk : c.entries[k]? with
      | none => simp only [checkNode, hk, Bool.false_eq_true] at hcheck
      | some e =>
        have h' : (((byteAt code pc = some (Jinst.toUInt8 .jumpi) ∧ e.pc = tt.toNat) ∧
              e.rets = m) ∧ gotoCompat a' e.frame = true) ∧
              (v.jumps? = some true ∨ checkNode code c.entries m (pc + 1) a' f = true) := by
          simpa only [checkNode, hk, Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true] using hcheck
        obtain ⟨_, X1, hst1, hfr1⟩ := Cursor.pop_two_frame hst hfr pop
        exact .toSucc t w hw lookup pop (ih (FrameSat.enter hc hfs hk lookup h'.1.1.2 hst1
          (frameMatches_gotoCompat h'.1.2 hfr1)))
    | [], hcheck, _ => simp only [checkNode, Bool.false_eq_true] at hcheck
    | [.const _], hcheck, _ => simp only [checkNode, Bool.false_eq_true] at hcheck
    | .ret :: _, hcheck, _ => simp only [checkNode, Bool.false_eq_true] at hcheck
    | .unk :: _, hcheck, _ => simp only [checkNode, Bool.false_eq_true] at hcheck
  | last hl => intro _ _ _ _ _ _; exact .last hl
  | @next _ _ n _ _ hrun _ ih =>
    intro m pc a ρ R ⟨⟨hcheck, X, hst, hfr⟩, hsat⟩
    simp only [checkNode, Bool.and_eq_true] at hcheck
    obtain ⟨_, hrest⟩ := hcheck
    cases habs : absNinst n a with
    | none => simp only [habs, Bool.false_eq_true] at hrest
    | some a' =>
      simp only [habs] at hrest
      simp only [SFunc.framesSat, habs, Bool.and_eq_true] at hsat
      obtain ⟨X', hst', hfr'⟩ := Cursor.absNinst_run_stack hfork habs hst hfr hrun
      exact .next ⟨hrun, fun _ _ => ⟨ρ, a, X, R, hst, hfr, hsat.1⟩⟩ (ih ⟨⟨hrest, X', hst', hfr'⟩, hsat.2⟩)
  | @dest _ _ f _ burn _ ih =>
    intro m pc a ρ R ⟨⟨hcheck, X, hst, hfr⟩, hsat⟩
    have h' : byteAt code pc = some (Jinst.toUInt8 .jumpdest) ∧
        checkNode code c.entries m (pc + 1) a f = true := by
      simpa only [checkNode, Bool.and_eq_true, beq_iff_eq] using hcheck
    exact .dest burn (ih ⟨⟨h'.2, X, by rw [← burn.stack, hst], hfr⟩, hsat⟩)
  | @jump _ _ k _ _ t lookup pop _ ih =>
    intro m pc a ρ R ⟨⟨hcheck, X, hst, hfr⟩, _⟩
    match a, hcheck, hfr with
    | .const tt :: a', hcheck, hfr =>
      cases hk : c.entries[k]? with
      | none => simp only [checkNode, hk, Bool.false_eq_true] at hcheck
      | some e =>
        have h' : (((byteAt code pc = some (Jinst.toUInt8 .jump) ∧ e.pc = tt.toNat) ∧
              e.rets = m) ∧
              gotoCompat a' e.frame = true) := by
          simpa only [checkNode, hk, Bool.and_eq_true, beq_iff_eq] using hcheck
        obtain ⟨_, X1, hst1, hfr1⟩ := Cursor.pop_one_frame hst hfr pop
        exact .jump t lookup pop (ih (FrameSat.enter hc hfs hk lookup h'.1.2 hst1
          (frameMatches_gotoCompat h'.2 hfr1)))
    | [], hcheck, _ => simp only [checkNode, Bool.false_eq_true] at hcheck
    | .ret :: _, hcheck, _ => simp only [checkNode, Bool.false_eq_true] at hcheck
    | .unk :: _, hcheck, _ => simp only [checkNode, Bool.false_eq_true] at hcheck
  | ret t pop => intro _ _ _ _ _ _; exact .ret t pop
  | @callHalt _ _ _ k _ g t lookup pop _ ih =>
    intro m pc a ρ R ⟨h, _⟩
    obtain ⟨e, r, sr, he, hcallee, -⟩ := h.call hc pop lookup
    exact .callHalt t lookup pop (ih ⟨hcallee, Cert.framesSat_entry hfs he lookup⟩)
  | @callRet _ d1 _ k f g _ t lookup pop calleeRun _ ihRun ihTail =>
    intro m pc a ρ R ⟨⟨hcheck, X, hst, hfr⟩, hsat⟩
    match a, f, hcheck, hfr, hsat with
    | .const _ :: a', .dest f0, hcheck, hfr, hsat =>
      cases hk : c.entries[k]? with
      | none => simp only [checkNode, hk, Bool.false_eq_true] at hcheck
      | some e =>
        simp only [checkNode, hk, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hcheck
        simp only [SFunc.framesSat, hk] at hsat
        obtain ⟨_, hmatch⟩ := hcheck
        obtain ⟨_, X0, hst0, hfr0⟩ := Cursor.pop_one_frame hst hfr pop
        have hentry := cert_check_at hc k e g hk lookup
        have hsatE := Cert.framesSat_entry hfs hk lookup
        cases hi : e.frame.findIdx? (· == .ret) with
        | none =>
          simp only [hi] at hmatch
          obtain ⟨sf, sr, hX0, hsf, _⟩ := frameMatches_callCompat (r := 0) hmatch hfr0
          have hst0' : d1.stack = sf ++ (sr ++ R) := by rw [hst0, hX0, List.append_assoc]
          obtain ⟨hm, -⟩ := calleeRun.stack_below id hc hfork
            ⟨hentry, sf, hst0', hsf⟩ rfl
          exact (ret_not_mem_of_findIdx_none hi _ hm rfl).elim
        | some i =>
          simp only [hi] at hmatch
          cases har : a'[i]? with
          | none => simp only [har, Bool.false_eq_true] at hmatch
          | some av =>
            cases av with
            | ret => simp only [har, Bool.false_eq_true] at hmatch
            | unk => simp only [har, Bool.false_eq_true] at hmatch
            | const r =>
              simp only [har, Bool.and_eq_true] at hmatch
              obtain ⟨hcall, hcont⟩ := hmatch
              obtain ⟨sf, sr, hX0, hsf, hsr⟩ := frameMatches_callCompat hcall hfr0
              have hst0' : d1.stack = sf ++ (sr ++ R) := by rw [hst0, hX0, List.append_assoc]
              obtain ⟨-, Y, hY, hlen⟩ := calleeRun.stack_below id hc hfork
                ⟨hentry, sf, hst0', hsf⟩ rfl
              refine .callRet t lookup pop (ihRun ⟨⟨hentry, sf, hst0', hsf⟩, hsatE⟩)
                (ihTail (m := m) (pc := r.toNat) (ρ := ρ) ⟨⟨?_, Y ++ sr, by rw [hY, List.append_assoc], ?_⟩, hsat⟩)
              · simpa only [checkNode, Bool.and_eq_true] using hcont
              · rw [← hlen]
                exact List.rel_append (frameMatches_unk_length Y) hsr
    | [], _, hcheck, _, _ => simp only [checkNode, Bool.false_eq_true] at hcheck
    | .ret :: _, _, hcheck, _, _ => simp only [checkNode, Bool.false_eq_true] at hcheck
    | .unk :: _, _, hcheck, _, _ => simp only [checkNode, Bool.false_eq_true] at hcheck
    | .const _ :: _, .next _ _, hcheck, _, _ => simp only [checkNode, Bool.false_eq_true] at hcheck
    | .const _ :: _, .branch _ _, hcheck, _, _ => simp only [checkNode, Bool.false_eq_true] at hcheck
    | .const _ :: _, .branchTo _ _, hcheck, _, _ =>
      simp only [checkNode, Bool.false_eq_true] at hcheck
    | .const _ :: _, .last _, hcheck, _, _ => simp only [checkNode, Bool.false_eq_true] at hcheck
    | .const _ :: _, .jump _, hcheck, _, _ => simp only [checkNode, Bool.false_eq_true] at hcheck
    | .const _ :: _, .callNext _ _, hcheck, _, _ =>
      simp only [checkNode, Bool.false_eq_true] at hcheck
    | .const _ :: _, .ret, hcheck, _, _ => simp only [checkNode, Bool.false_eq_true] at hcheck
    | .const _ :: _, .pcAt _ _, hcheck, _, _ => simp only [checkNode, Bool.false_eq_true] at hcheck
    | .const _ :: _, .undefined, hcheck, _, _ =>
      simp only [checkNode, Bool.false_eq_true] at hcheck
  | @pcAt _ _ p f _ hrunP hstep _ ih =>
    intro m pc a ρ R ⟨⟨hcheck, X, hst, hfr⟩, hsat⟩
    have h' : (bytesAt code pc (Ninst.toBytes (Ninst.reg .pc)) = true ∧ p = pc) ∧
        checkNode code c.entries m (pc + 1) (.const (Nat.toB256 pc) :: a) f = true := by
      simpa only [checkNode, Bool.and_eq_true, beq_iff_eq] using hcheck
    obtain ⟨⟨_, rfl⟩, hrest⟩ := h'
    simp only [SFunc.framesSat] at hsat
    refine .pcAt ⟨hrunP, fun _ h => by cases h⟩ hstep
      (ih (R := R) ⟨⟨hrest, Nat.toB256 p :: X, ?_, List.Forall₂.cons rfl hfr⟩, hsat⟩)
    rw [pc_stepRun_stack hstep, hst]
    rfl

end Framed

/-! ## Closures whose only external instruction is a quiet `DELEGATECALL` -/

/-- A synthetic tree whose instructions are quiet (`Ninst.quiet`) or `DELEGATECALL`, and whose
terminals are not `SELFDESTRUCT`. -/
def SFunc.quietDelegate : SFunc → Bool
  | .branch f g => f.quietDelegate && g.quietDelegate
  | .branchTo f _ => f.quietDelegate
  | .last l => l != .selfdestruct
  | .next n f => (n.quiet || n == .exec .delegatecall) && f.quietDelegate
  | .dest f => f.quietDelegate
  | .jump _ => true
  | .callNext _ f => f.quietDelegate
  | .ret => true
  | .pcAt _ f => f.quietDelegate
  | .undefined => true

/-- `S` is closed under the entries referenced by its members, and all of them are
`quietDelegate`. -/
def QuietDelegateSet (fs : List SFunc) (S : List Nat) : Bool :=
  S.all fun k => match fs[k]? with
    | some g => g.quietDelegate && g.refs.all (· ∈ S)
    | none => false

section QuietDelegate

variable {code : ByteArray} {aw : B256} {sevm : Sevm}

/-- What a quiet-delegate run keeps: the storage owner's storage and `aw`'s code. -/
def QDKeep (aw : B256) (sevm : Sevm) (d d' : Devm) : Prop :=
  Devm.getStor d' sevm.currentTarget = Devm.getStor d sevm.currentTarget ∧
    d'.getCode aw.toAdr = d.getCode aw.toAdr

theorem QDKeep.trans {d₁ d₂ d₃ : Devm} (h₂ : QDKeep aw sevm d₂ d₃)
    (h₁ : QDKeep aw sevm d₁ d₂) : QDKeep aw sevm d₁ d₃ :=
  ⟨h₂.1.trans h₁.1, h₂.2.trans h₁.2⟩

theorem QDKeep.of_state {d d' : Devm} (h : d'.state = d.state) : QDKeep aw sevm d d' :=
  ⟨getStor_eq_of_state_eq h _, getCode_eq_of_state_eq h _⟩

/-- **One step of a quiet-delegate tree.**  A quiet instruction keeps every storage map; a framed
`DELEGATECALL` whose frame names `aw`, holding nonempty undelegated quiet code, keeps the storage
owner's storage; every step keeps `aw`'s code. -/
theorem FramedStep.qdKeep {P : Ninst → List AVal → Bool} (hq : QuietCode code)
    (hP : ∀ a, P (.exec .delegatecall) a = true → a[1]? = some (.const aw))
    (undelegated : getDelegatedCodeAddress code = none) (nonempty : code.toList ≠ [])
    (hfork : CoveredFork sevm.benvStat.fork) {d d' : Devm} {n : Ninst}
    (hn : (n.quiet || n == .exec .delegatecall) = true) (step : FramedStep P sevm d n d')
    (hcode : d.getCode aw.toAdr = code) : QDKeep aw sevm d d' := by
  have codeKeep : d'.getCode aw.toAdr = d.getCode aw.toAdr :=
    Ninst.Run.getCode_eq step.1 (by rw [hcode]; exact nonempty)
  rcases Bool.or_eq_true_iff.mp hn with hq' | hd
  · exact ⟨congrFun (Ninst.world_of_quiet hfork hq' step.1).1 _, codeKeep⟩
  · have hd : n = .exec .delegatecall := by simpa only [beq_iff_eq] using hd
    subst hd
    obtain ⟨ρ, a, X, R, hst, hfr, hPa⟩ := step.2 _ rfl
    have hX := FrameMatches.getElem?_const hfr (hP a hPa)
    have h1 : d.stack[1]? = some aw := by
      obtain ⟨hi, -⟩ := List.getElem?_eq_some_iff.mp hX
      rw [hst, List.getElem?_append_left hi]
      exact hX
    obtain ⟨g, s, hs⟩ : ∃ g s, d.stack = g :: aw :: s := by
      match hds : d.stack, h1 with
      | g :: w :: s, h1 =>
        simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at h1
        exact ⟨g, s, by rw [h1]⟩
    exact ⟨Ninst.delegatecall_getStor_of_quiet hq hfork hs hcode undelegated step.1, codeKeep⟩

/-- **The quiet-delegate frame theorem.**  A framed run of a `quietDelegate` tree whose gotos and
calls stay in a `QuietDelegateSet`, every `DELEGATECALL` of which names the word `aw` holding
nonempty undelegated quiet code, keeps the storage owner's storage and `aw`'s code. -/
theorem SFunc.RunP.qdKeep {P : Ninst → List AVal → Bool} (hq : QuietCode code)
    (hP : ∀ a, P (.exec .delegatecall) a = true → a[1]? = some (.const aw))
    (undelegated : getDelegatedCodeAddress code = none) (nonempty : code.toList ≠ [])
    (hfork : CoveredFork sevm.benvStat.fork) {fs : List SFunc} {S : List Nat}
    (hS : QuietDelegateSet fs S = true) {d : Devm} {f : SFunc} {o : Outcome}
    (run : SFunc.RunP (FramedStep P) fs sevm d f o) :
    f.quietDelegate = true → f.refs.all (· ∈ S) = true → d.getCode aw.toAdr = code →
      QDKeep aw sevm d (Outcome.devm o) := by
  have closed : ∀ {k g}, k ∈ S → fs[k]? = some g →
      g.quietDelegate = true ∧ g.refs.all (· ∈ S) = true := by
    intro k g hk hget
    have h := (List.all_eq_true.mp hS) k hk
    rw [hget] at h
    simpa only [List.all_eq_true, decide_eq_true_eq, Bool.and_eq_true] using h
  have popKeep : ∀ {ws : List B256} {a b : Devm}, Devm.PopBurn ws a b →
      QDKeep aw sevm a b := fun pop => QDKeep.of_state pop.state.symm
  have keepCode : ∀ {a b : Devm}, QDKeep aw sevm a b → a.getCode aw.toAdr = code →
      b.getCode aw.toAdr = code := fun h hc => h.2.trans hc
  induction run with
  | zero _ pop _ ih =>
    intro hf hr hc
    simp only [SFunc.quietDelegate, Bool.and_eq_true] at hf
    simp only [SFunc.refs, List.all_append, Bool.and_eq_true] at hr
    exact (ih hf.1 hr.1 (keepCode (popKeep pop) hc)).trans (popKeep pop)
  | succ _ _ _ pop _ ih =>
    intro hf hr hc
    simp only [SFunc.quietDelegate, Bool.and_eq_true] at hf
    simp only [SFunc.refs, List.all_append, Bool.and_eq_true] at hr
    exact (ih hf.2 hr.2 (keepCode (popKeep pop) hc)).trans (popKeep pop)
  | toZero _ pop _ ih =>
    intro hf hr hc
    simp only [SFunc.refs, List.all_cons, Bool.and_eq_true] at hr
    exact (ih hf hr.2 (keepCode (popKeep pop) hc)).trans (popKeep pop)
  | toSucc _ _ _ lookup pop _ ih =>
    intro _ hr hc
    simp only [SFunc.refs, List.all_cons, Bool.and_eq_true] at hr
    have ht := closed (of_decide_eq_true hr.1) lookup
    exact (ih ht.1 ht.2 (keepCode (popKeep pop) hc)).trans (popKeep pop)
  | last hl =>
    intro hf _ _
    refine ⟨congrFun (Linst.world_of_ok (by simpa only [ne_eq, SFunc.quietDelegate, bne_iff_ne]
      using hf) hl).1 _, Linst.run_codeFrame hl _⟩
  | next step _ ih =>
    intro hf hr hc
    simp only [SFunc.quietDelegate, Bool.and_eq_true] at hf
    have h := FramedStep.qdKeep hq hP undelegated nonempty hfork hf.1 step hc
    exact (ih hf.2 hr (keepCode h hc)).trans h
  | dest burn _ ih =>
    intro hf hr hc
    have h : QDKeep aw sevm _ _ := QDKeep.of_state burn.state.symm
    exact (ih hf hr (keepCode h hc)).trans h
  | jump _ lookup pop _ ih =>
    intro _ hr hc
    simp only [SFunc.refs, List.all_cons, Bool.and_eq_true] at hr
    have ht := closed (of_decide_eq_true hr.1) lookup
    exact (ih ht.1 ht.2 (keepCode (popKeep pop) hc)).trans (popKeep pop)
  | ret _ pop => intro _ _ _; exact popKeep pop
  | callHalt _ lookup pop _ ih =>
    intro _ hr hc
    simp only [SFunc.refs, List.all_cons, Bool.and_eq_true] at hr
    have ht := closed (of_decide_eq_true hr.1) lookup
    exact (ih ht.1 ht.2 (keepCode (popKeep pop) hc)).trans (popKeep pop)
  | callRet _ lookup pop _ _ ihRun ihTail =>
    intro hf hr hc
    simp only [SFunc.refs, List.all_cons, Bool.and_eq_true] at hr
    have ht := closed (of_decide_eq_true hr.1) lookup
    simp only [SFunc.quietDelegate] at hf
    have h1 := (ihRun ht.1 ht.2 (keepCode (popKeep pop) hc)).trans (popKeep pop)
    exact (ihTail hf hr.2 (keepCode h1 hc)).trans h1
  | pcAt hrun _ _ ih =>
    intro hf hr hc
    simp only [SFunc.quietDelegate] at hf
    simp only [SFunc.refs] at hr
    have h : QDKeep aw sevm _ _ :=
      ⟨congrFun (Ninst.world_of_quiet (n := .reg .pc) hfork rfl hrun.1).1 _,
        Ninst.Run.getCode_eq hrun.1 (by rw [hc]; exact nonempty)⟩
    exact (ih hf hr (keepCode h hc)).trans h

end QuietDelegate

/-- **Crossing a quiet-delegate internal call.**  A `callNext` into an entry of a
`QuietDelegateSet` closure of a checked certificate passing `Cert.framesSat P` (every
`DELEGATECALL` frame names `aw`, holding nonempty undelegated quiet code), from the walk state
`St b (dd :: S) M G` whose top words match the callee's declared frame: either the callee returns
and the continuation runs from a state keeping `b`'s storage owner storage and `aw`'s code, with
the stack `Y ++ S.drop e.frame.length`, `Y.length = e.rets`, or it halts the frame keeping them. -/
theorem ric_call_quietDelegate {code : ByteArray} {c : Cert} {P : Ninst → List AVal → Bool}
    {qcode : ByteArray} {aw : B256} {sevm : Sevm} (hc : Cert.check code c = true)
    (hfs : c.framesSat P = true) (hfork : CoveredFork sevm.benvStat.fork) (hq : QuietCode qcode)
    (hP : ∀ a, P (.exec .delegatecall) a = true → a[1]? = some (.const aw))
    (undelegated : getDelegatedCodeAddress qcode = none) (nonempty : qcode.toList ≠ [])
    {Sk : List Nat} (hS : QuietDelegateSet c.prog Sk = true) {k : Nat} (hkS : k ∈ Sk)
    {e : Entry} {g : SFunc} (he : c.entries[k]? = some e) (hg : c.prog[k]? = some g)
    {C : List Nat} {b : Devm} {S : List B256} {M : Mem} {G : Nat} {dd ρ : B256} {f : SFunc}
    {r : Seg} (hframe : FrameMatches ρ e.frame (S.take e.frame.length))
    (hcode : b.getCode aw.toAdr = qcode)
    (run : SFunc.RunCut c.prog sevm C (St b (dd :: S) M G) (.callNext k f) r) :
    (∃ b' Y M' G', QDKeep aw sevm b b' ∧ Y.length = e.rets ∧
        SFunc.RunCut c.prog sevm C (St b' (Y ++ S.drop e.frame.length) M' G') f r) ∨
      (∃ D, QDKeep aw sevm b D ∧ r = .done (.halted D)) := by
  have hgS : g.quietDelegate = true ∧ g.refs.all (· ∈ Sk) = true := by
    have h := (List.all_eq_true.mp hS) k hkS
    rw [hg] at h
    simpa only [Bool.and_eq_true] using h
  have keep : ∀ {G' : Nat} {o : Outcome}, SFunc.Run c.prog sevm (St b S M G') g o →
      QDKeep aw sevm b (Outcome.devm o) := fun callee =>
    (callee.framed hc hfs hfork (FrameSat.enter hc hfs he hg rfl
      (by rw [St.stack, List.take_append_drop]) hframe)).qdKeep hq hP undelegated nonempty hfork
      hS hgS.1 hgS.2 hcode
  obtain ⟨G', h⟩ := ric_call hg run
  rcases h with ⟨D, callee, cont⟩ | ⟨D, callee, hr⟩
  · obtain ⟨Y, hY, hlen⟩ := callee.entry_stack_below id hc hfork he hg
      (List.take_append_drop _ _).symm hframe
    rw [St.stack] at hY
    refine .inl ⟨D, Y, D.memory, D.gasLeft, keep callee, hlen, ?_⟩
    rw [← St.self hY rfl]
    exact cont
  · exact .inr ⟨D, keep callee, hr⟩

end Blanc.Lift
