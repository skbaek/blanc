import Blanc.ExecutionReceiptLogLink
import Blanc.ExecutionMidHistoryInOwnCode
import Blanc.Lift.CurveCoins.ApprovalLogsDai
import Blanc.Lift.CurveCoins.ApprovalLogsUsdt

/-!
# The coins' premises, from logs and state reads

A reader's facts are logs and state reads at named blocks. These theorems turn them into the premises of the coins'
locality laws, over a mid history:

* `notDeprecated_of_receipts`: the flag clear at the start and no `Deprecate` log in the receipts give `NotDeprecated` at
  every settled frame at USDT;
* `noConfiscation_of_receipts`: no `DestroyedBlackFunds` naming the holder gives `¬ Confiscates`;
* `dai_noSignature_of_receipts`: no `Approval` naming the holder as owner gives DAI's `noSignature`;
* `dai_rows_of_logs`, `usdt_rows_of_logs`: over a history from a state with the holder's tracked rows empty, no `Approval`
  naming it keeps them empty.

Receipts do not speak for system stages, so each receipt form takes `sysNe`. `MidHistoryTraceIn.system_ne` gives it from
`SystemConfined` for a coin outside the four system addresses.
-/

namespace Blanc.Lift.CurveCoins

open Jaune Blanc Blanc.Lift Blanc.Lift.WriteSite Blanc.ExecutionTrace

/-- What a reader's filter for `Deprecate` at `T` matches. -/
def DeprecateLog (T : Adr) (l : Log) : Prop := l.address = T ∧ l.topics = [Usdt.deprecateTopic]

/-- What a reader's filter for `DestroyedBlackFunds` at `T` matches, on the first data word `h`. -/
def DestroyedLog (T h : Adr) (l : Log) : Prop :=
  l.address = T ∧ l.topics = [Usdt.destroyedTopic] ∧ l.data.take 32 = h.toB256.toBytes

/-- What a reader's filter for `Approval` at `T` matches, with owner `h`. -/
def ApprovalLog (T h : Adr) (l : Log) : Prop := l.address = T ∧ l.topics.take 2 = [approvalTopic, h.toB256]

variable {T h : Adr} {cfg : ChainConfig} {start : Benv} {future : BlockChain}

/-- **A settled frame's memory starts well formed**: an entered frame's memory is empty. -/
theorem settled_wf (trace : MidHistoryTraceIn HistFork cfg start future) {F : Exec.Frame}
    (member : F ∈ trace.settledFrames) : Mem.Wf F.pre.memory := by
  have fresh := (trace.rawFrames_entered enteredCondition_fresh _ (trace.mem_rawFrames_of_mem_settledFrames F member)).2
  change F.pre.memory = Mem.empty at fresh
  rw [fresh]
  exact Mem.wf_empty

namespace Usdt

open Blanc.Lift.Usdt Blanc.Lift.CurveCoins.Usdt

theorem code_callKinds : callKindsCheck code = true := by decide +kernel

/-- TetherToken's runtime spawns only by `CALL` and `STATICCALL`. -/
theorem ownSpawnsIn (ca : Adr) : OwnSpawnsIn ca code := by
  intro R N x pcZero hcode _ _ chain instruction
  have hb := Exec.Deriv.ParentPrefix.noPush chain (by rw [pcZero]; exact noPushBefore_zero _ _)
  have hNs : N.sevm = R.sevm := Blanc.Exec.Deriv.ParentPrefix.sevm_eq chain
  rw [hNs, hcode] at hb instruction
  rcases callKinds_of_check code_callKinds hb instruction with e | e
  · exact .inl e
  · exact .inr (.inl e)

/-- **Every settled frame at `T` runs TetherToken's code**, deprecated or not: a frame that forwards only does so by
`CALL`. -/
theorem settled_codeFrame (capabilities : BodyStageCapabilities HistFork)
    (trace : MidHistoryTraceIn HistFork cfg start future) (installed : start.state.getCode T = code)
    {F : Exec.Frame} (member : F ∈ trace.settledFrames) (target : F.sevm.currentTarget = T) :
    CodeFrame T HistFork code F := by
  let sem := Usdc.CodeSem.ofBytes code code_ne code_notDelegated
  have ne : code.toList ≠ [] := sem.ne_nil rfl
  obtain ⟨hc, pc, fork, -, run⟩ := trace.settled_ownCodeIn (F := HistFork) sem T HistFork.stateGas_none ne
    (sem.not_delegation (show some code.toList = sem.image from rfl)) (ownSpawnsIn T) capabilities
    (by rw [installed]; rfl) runtimeSafety rfl F member
  exact ⟨pc, run target, fork, by rw [hc]; exact ne⟩

/-- A frame of the certified code, not deprecated, encloses no frame. -/
theorem descendants_nil {A : Exec.Frame} (good : CodeFrame T HistFork code A) (target : A.sevm.currentTarget = T)
    (live : NotDeprecated T A) : Exec.descendantFrames A.run = [] := by
  obtain ⟨pc, sevm, pre, out, run, committed⟩ := A
  obtain ⟨hpc, hcode, fork, -⟩ := good
  dsimp only at hpc hcode fork target live
  subst hpc
  have raw := usdt_descendants_nil run hcode fork.stateGas_none fork.bal_none (by rw [target]; exact live)
  refine List.eq_nil_iff_forall_not_mem.mpr fun D member => ?_
  have := Exec.mem_rawFrameDescendants_of_mem_descendantFrames run D member
  rw [raw] at this
  exact absurd this List.not_mem_nil

/-- **The flag stays clear along the settled frames at `T`** when no frame among them is on `deprecate`. By position: a
frame's prefix is live by induction, so nothing in it encloses the frame, so the chain reaches its entry; a live frame
off `deprecate` keeps the word. -/
theorem notDeprecated_of_selectors (capabilities : BodyStageCapabilities HistFork)
    (trace : MidHistoryTraceIn HistFork cfg start future) (installed : start.state.getCode T = code)
    (clear : flag20 ((start.state.getStor T).get 10) = 0)
    (keys : UsdtKeysFresh h (coinFrames T (fun _ => True) trace.settledFrames))
    (off : ∀ F ∈ coinFrames T (fun _ => True) trace.settledFrames, Blanc.Sevm.selector F.sevm ≠ 0x0753c30c) :
    ∀ F ∈ coinFrames T (fun _ => True) trace.settledFrames, NotDeprecated T F := by
  have main : ∀ (n : Nat) (before : List Exec.Frame) (f : Exec.Frame) (after : List Exec.Frame),
      trace.settledFrames = before ++ f :: after → before.length = n → f.sevm.currentTarget = T →
      f.sevm.isStatic = false → NotDeprecated T f := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro before f after split len _ _
      have inCoin : ∀ G ∈ coinFrames T (fun _ => True) before,
          G ∈ coinFrames T (fun _ => True) trace.settledFrames := fun G hG => by
        rw [split, coinFrames_append]
        exact List.mem_append_left _ hG
      have all : ∀ G ∈ coinFrames T (fun _ => True) before, NotDeprecated T G := by
        intro G hG
        obtain ⟨member, ht, hs, -⟩ := mem_coinFrames.mp hG
        obtain ⟨b, m, rfl⟩ := List.append_of_mem member
        refine ih b.length ?_ b G (m ++ f :: after) ?_ rfl ht hs
        · rw [← len, List.length_append, List.length_cons]
          omega
        · rw [split, List.append_assoc, List.cons_append]
      have noOpaque : Exec.NoOpaqueAbove (fun A => A.sevm.currentTarget = T ∧ A.sevm.isStatic = false) before f := by
        rintro b A m k rfl desc ⟨ht, hs⟩
        have hA : A ∈ b ++ A :: m := List.mem_append_right _ List.mem_cons_self
        have coin : A ∈ coinFrames T (fun _ => True) (b ++ A :: m) := mem_coinFrames.mpr ⟨hA, ht, hs, trivial⟩
        have settled : A ∈ trace.settledFrames := by
          rw [split]
          exact List.mem_append_left _ hA
        have nil := descendants_nil (settled_codeFrame capabilities trace installed settled ht) ht (all A coin)
        rw [nil] at desc
        simp only [List.nil_eq, List.append_eq_nil_iff, reduceCtorEq, and_false] at desc
      have chain := (usdt_chain capabilities trace installed).2 split noOpaque all
      have law : ∀ G ∈ coinFrames T (fun _ => True) before, CodeFrame T HistFork code G →
          flag20 (wordsAt T G.pre.state 10) = 0 →
          flag20 (wordsAt T G.post.state 10) = 0 ∧ (fun _ => 0) (wordsAt T G.pre.state) + (fun _ => 0) G ≤
            (fun _ => 0) (wordsAt T G.post.state) + (fun _ => 0) G := by
        intro G hG good flag
        refine ⟨?_, Nat.le_refl _⟩
        have whole := inCoin G hG
        have target := (mem_coinFrames.mp hG).2.1
        have keep := frame_flag_keep whole keys good target (all G hG) (off G whole)
        change flag20 ((G.post.getStor T).get 10) = 0
        rw [keep]
        exact flag
      exact (chain.fold (held := fun _ => 0) (credit := fun _ => 0) (debit := fun _ => 0)
        (I := fun w => flag20 (w 10) = 0) law clear).1
  intro F hF
  obtain ⟨member, ht, hs, -⟩ := mem_coinFrames.mp hF
  obtain ⟨b, m, split⟩ := List.append_of_mem member
  exact main _ b F m split rfl ht hs

/-- **The flag stays clear along the settled frames at `T`** when no frame among them logs `Deprecate`: a frame on
`deprecate` logs it. -/
theorem notDeprecated_of_frames (capabilities : BodyStageCapabilities HistFork)
    (trace : MidHistoryTraceIn HistFork cfg start future) (installed : start.state.getCode T = code)
    (clear : flag20 ((start.state.getStor T).get 10) = 0)
    (keys : UsdtKeysFresh h (coinFrames T (fun _ => True) trace.settledFrames))
    (noLog : ∀ F ∈ coinFrames T (fun _ => True) trace.settledFrames, ∀ l ∈ F.post.logs, ¬ DeprecateLog T l) :
    ∀ F ∈ coinFrames T (fun _ => True) trace.settledFrames, NotDeprecated T F := by
  refine notDeprecated_of_selectors capabilities trace installed clear keys fun F hF sel => ?_
  obtain ⟨member, target, -, -⟩ := mem_coinFrames.mp hF
  obtain ⟨l, mem, logged⟩ := deprecate_logs (settled_codeFrame capabilities trace installed member target) target
    (settled_wf trace member) sel
  exact noLog F hF l mem logged

/-- **`notDeprecated` from a clear flag and no `Deprecate` receipt log.** -/
theorem notDeprecated_of_receipts (capabilities : BodyStageCapabilities HistFork)
    (trace : MidHistoryTraceIn HistFork cfg start future) (installed : start.state.getCode T = code)
    (clear : flag20 ((start.state.getStor T).get 10) = 0)
    (keys : UsdtKeysFresh h (coinFrames T (fun _ => True) trace.settledFrames))
    (receipts : trace.NoLogInReceipts (DeprecateLog T))
    (sysNe : ∀ root ∈ trace.systemRawFrames, root.sevm.currentTarget ≠ T) :
    ∀ F ∈ coinFrames T (fun _ => True) trace.settledFrames, NotDeprecated T F :=
  notDeprecated_of_frames capabilities trace installed clear keys fun F hF =>
    trace.no_log_at HistFork.stateGas_none _ receipts sysNe F (mem_coinFrames.mp hF).1 (mem_coinFrames.mp hF).2.1

/-- **`noConfiscation` from no `DestroyedBlackFunds(h, _)` receipt log.** -/
theorem noConfiscation_of_receipts (capabilities : BodyStageCapabilities HistFork)
    (trace : MidHistoryTraceIn HistFork cfg start future) (installed : start.state.getCode T = code)
    (live : ∀ F ∈ coinFrames T (fun _ => True) trace.settledFrames, NotDeprecated T F)
    (receipts : trace.NoLogInReceipts (DestroyedLog T h))
    (sysNe : ∀ root ∈ trace.systemRawFrames, root.sevm.currentTarget ≠ T) :
    ∀ F ∈ coinFrames T (fun _ => True) trace.settledFrames, ¬ Confiscates h F.sevm := by
  intro F hF named
  obtain ⟨member, target, -, -⟩ := mem_coinFrames.mp hF
  obtain ⟨l, mem, logged⟩ := confiscates_logs (settled_codeFrame capabilities trace installed member target) target
    (live F hF) (settled_wf trace member) named
  exact trace.no_log_at HistFork.stateGas_none _ receipts sysNe F member target l mem logged

/-- **The holder's tracked rows, across a history from a state with them empty**, when no frame logs `Approval` naming
it. `frames` may be longer than the history's own, for example add the frames after a cut: the rows tracked at the cut
are then those frames' callers'. -/
theorem usdt_rows_of_logs (capabilities : BodyStageCapabilities HistFork)
    (trace : MidHistoryTraceIn HistFork cfg start future) (installed : start.state.getCode T = code)
    (live : ∀ F ∈ coinFrames T (fun _ => True) trace.settledFrames, NotDeprecated T F)
    {frames : List Exec.Frame} (sub : coinFrames T (fun _ => True) trace.settledFrames ⊆ frames)
    (keys : UsdtKeysFresh h frames) (rows : RowsEmpty h frames (wordsAt T start.state))
    (noLog : ∀ F ∈ coinFrames T (fun _ => True) trace.settledFrames, ∀ l ∈ F.post.logs, ¬ ApprovalLog T h l) :
    RowsEmpty h frames (wordsAt T future.state) := by
  refine ((usdt_chain capabilities trace installed).1 live |>.fold (held := fun _ => 0) (credit := fun _ => 0)
    (debit := fun _ => 0) (I := RowsEmpty h frames) (fun F hF good empty => ⟨?_, Nat.le_refl _⟩) rows).1
  refine Classical.byContradiction fun raised => ?_
  obtain ⟨l, mem, addr, topics⟩ := frame_rows_raised_logs (sub hF) good (mem_coinFrames.mp hF).2.1 (live F hF) keys
    empty raised
  exact noLog F hF l mem ⟨addr, topics⟩

end Usdt

namespace Dai

open Blanc.Lift.Dai Blanc.Lift.CurveCoins.Dai

/-- **DAI's `noSignature` from no `Approval(h, _)` receipt log.** -/
theorem dai_noSignature_of_receipts (trace : MidHistoryTraceIn HistFork cfg start future)
    (installed : start.state.getCode T = code) (receipts : trace.NoLogInReceipts (ApprovalLog T h))
    (sysNe : ∀ root ∈ trace.systemRawFrames, root.sevm.currentTarget ≠ T) :
    ∀ F ∈ coinFrames T (fun _ => True) trace.settledFrames, ¬ SignedAs h F.sevm :=
  dai_noSignature_of_logs trace installed fun F hF ⟨l, mem, addr, topics⟩ =>
    trace.no_log_at HistFork.stateGas_none _ receipts sysNe F (mem_coinFrames.mp hF).1 (mem_coinFrames.mp hF).2.1 l mem
      ⟨addr, topics⟩

/-- **The holder's tracked rows, across a history from a state with them empty**, when no frame logs `Approval` naming
it. `frames` as in `Usdt.usdt_rows_of_logs`. -/
theorem dai_rows_of_logs (trace : MidHistoryTraceIn HistFork cfg start future)
    (installed : start.state.getCode T = code)
    {frames : List Exec.Frame} (sub : coinFrames T (fun _ => True) trace.settledFrames ⊆ frames)
    (keys : CoinKeysFresh (wsRoot DaiWs.implWsAnn) 2 3 h frames) (rows : RowsEmpty h frames (wordsAt T start.state))
    (noLog : ∀ F ∈ coinFrames T (fun _ => True) trace.settledFrames, ∀ l ∈ F.post.logs, ¬ ApprovalLog T h l) :
    RowsEmpty h frames (wordsAt T future.state) := by
  refine ((dai_chain trace installed).1 (fun _ _ => trivial) |>.fold (held := fun _ => 0) (credit := fun _ => 0)
    (debit := fun _ => 0) (I := RowsEmpty h frames) (fun F hF good empty => ⟨?_, Nat.le_refl _⟩) rows).1
  refine Classical.byContradiction fun raised => ?_
  have target := (mem_coinFrames.mp hF).2.1
  obtain ⟨l, mem, addr, topics⟩ := frame_rows_raised_logs (sub hF) good target
    (CertFrame.of_staticOnly cert_check staticOnly HistFork.stateGas_none good target) keys empty raised
  exact noLog F hF l mem ⟨addr, topics⟩

end Dai

end Blanc.Lift.CurveCoins
