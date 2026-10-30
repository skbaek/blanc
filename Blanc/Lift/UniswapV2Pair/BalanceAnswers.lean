import Blanc.Lift.UniswapV2Pair.PairOuterCalls
import Blanc.Lift.UniswapV2Pair.PairFeeAnswer
import Blanc.Lift.UniswapV2Pair.PairCallSettle
import Blanc.Lift.UniswapV2Pair.BurnForwardAccept
import Blanc.Lift.UniswapV2Pair.PropertiesMintBurn
import Blanc.Lift.ReachChain

/-!
# The backing answers of one outer Pair call, read from its child frames

`sync` and `burn` are the two entries whose share-value law needs a condition on the token
answers (`EntryNoShrink`, stated over the transcript).  `BalanceAnswersBacked pair f` states the
same condition over the call itself: the first output words of the frames the call's own calls
entered (`answerWord f i`, the `i`-th call), the call's own output (`outputWord`, the burn's
two payouts), and its entry storage (`reserve0Word`, `reserve1Word`):

* `sync`: both `balanceOf(pair)` answers are at least the stored reserves;
* `burn`: both first answers are at least the stored reserves, and each first answer is at most
  the final answer (the sixth and seventh calls, after the two transfers) plus the payout the burn
  returned: the transfer debited the Pair at most the payout.

Along the call's positional consumption (`PositionalConsumes`), the `i`-th reply of the transcript
is the output of the frame the `i`-th call entered whenever that call entered a committed frame
(`reply_of_childAt`).  Hence `BalanceAnswersBacked` gives `EntryNoShrink` at the call's own step
(`entryNoShrink_of_backed`), and it is exactly `EntryNoShrink` plus "every consulted answer came
from a committed frame" (`balanceAnswersBacked_iff`).

The per-call share value built on these facts is `pair_share_value` (`HeadlineShare.lean`); it
consults only the answers of the call it is about.
-/

namespace Blanc.Lift.UniswapV2Pair

open Jaune Blanc

/-! ## Call-tree paths -/

/-- A frame none of whose same-frame nodes decodes an external instruction has no located
descendants. -/
theorem Exec.descendantFramePaths_eq_nil_of_noExec {pc : Nat} {sevm : Sevm} {d : Devm}
    {out : Execution} (run : Exec pc sevm d out)
    (h : ∀ N, Exec.Deriv.ParentPrefix ⟨pc, sevm, d, out, run⟩ N →
      ∀ x, ¬ Ninst.At N.sevm.code N.pc (.exec x)) (p : List Nat) (k : Nat) :
    Exec.descendantFramePaths p k run = [] := by
  induction run generalizing k with
  | halt step => simp only [Exec.descendantFramePaths]
  | cont step next ih =>
      simp only [Exec.descendantFramePaths]
      exact ih (fun N hN x => h N (.step (.cont step next) hN) x) k
  | doneErr step enter resume => simp only [Exec.descendantFramePaths]
  | doneOk step enter resume next ih =>
      obtain ⟨x, instruction, -, -⟩ := Evm.step_spawn_inv step
      exact (h _ (.refl _) x instruction).elim
  | runErr step enter child resume ih => simp only [Exec.descendantFramePaths]
  | runOk step enter child resume next childIH nextIH =>
      obtain ⟨x, instruction, -, -⟩ := Evm.step_spawn_inv step
      exact (h _ (.refl _) x instruction).elim

/-- Every top-level located descendant collected from child counter `k` lies below a child index
at least `k`. -/
theorem descendantFramePaths_head_ge (k : Nat) {pc : Nat} {sevm : Sevm} {pre : Devm}
    {out : Execution} (run : Exec pc sevm pre out) :
    ∀ c ∈ Exec.descendantFramePaths [] k run, ∃ j rest, k ≤ j ∧ c.path = j :: rest := by
  induction run generalizing k with
  | halt => intro c member; simp only [Exec.descendantFramePaths, List.not_mem_nil] at member
  | cont _ _ ih =>
    intro c member
    simp only [Exec.descendantFramePaths] at member
    exact ih k c member
  | doneErr => intro c member; simp only [Exec.descendantFramePaths, List.not_mem_nil] at member
  | doneOk _ _ _ _ ih =>
    intro c member
    simp only [Exec.descendantFramePaths] at member
    obtain ⟨j, rest, le, eq⟩ := ih (k + 1) c member
    exact ⟨j, rest, by omega, eq⟩
  | runErr => intro c member; simp only [Exec.descendantFramePaths, List.not_mem_nil] at member
  | runOk _ _ _ _ _ _ nextIh =>
    intro c member
    simp only [Exec.descendantFramePaths, List.mem_append] at member
    rcases member with inChild | inNext
    · split at inChild
      · rcases List.mem_cons.mp inChild with rfl | deeper
        · exact ⟨k, [], Nat.le_refl _, rfl⟩
        · obtain ⟨rest, eq⟩ := descendantFramePaths_prefix ([] ++ [k]) 0 _ c deeper
          exact ⟨k, rest, Nat.le_refl _, eq.symm⟩
      · cases inChild
    · obtain ⟨j, rest, le, eq⟩ := nextIh (k + 1) c inNext
      exact ⟨j, rest, by omega, eq⟩

/-- No top-level descendant collected from counter `k` sits at a child index below `k`. -/
theorem descendantFramePaths_find_lt {i k : Nat} (lt : i < k) {pc : Nat} {sevm : Sevm}
    {pre : Devm} {out : Execution} (run : Exec pc sevm pre out) :
    (Exec.descendantFramePaths [] k run).find? (fun c => c.path == [i]) = none := by
  rw [List.find?_eq_none]
  intro c member
  obtain ⟨j, rest, le, eq⟩ := descendantFramePaths_head_ge k run c member
  rw [eq]
  simp only [beq_iff_eq, List.cons.injEq, not_and]
  intro same
  omega

/-- A list of frames all below child index `i` holds no frame at another index `j`. -/
theorem find_none_of_below {C : List Exec.LocatedFrame} {i j : Nat} (off : i ≠ j)
    (below : ∀ c ∈ C, [i] <+: c.path) : C.find? (fun c => c.path == [j]) = none := by
  rw [List.find?_eq_none]
  intro c member
  obtain ⟨rest, pathEq⟩ := below c member
  rw [← pathEq]
  simp only [List.singleton_append, beq_iff_eq, List.cons.injEq, off, false_and,
    not_false_eq_true]

/-- A spawning parent edge with a located frame at its own child index entered code. -/
theorem ParentStep.enters_of_found {F N : Exec.Deriv} (edge : Exec.Deriv.ParentStep N F)
    {frame : Jaune.Frame} {resume : Resume} {pc : Nat}
    (spawned : Evm.step ⟨F.pc, F.sevm, F.devm⟩ = .spawn frame resume pc) {index : Nat}
    {c : Exec.LocatedFrame}
    (found : (Exec.descendantFramePaths [] index F.exc).find? (fun c => c.path == [index]) =
      some c) : ∃ evm, frame.enter = .run evm := by
  cases edge with
  | cont hstep next =>
    have impossible := hstep.symm.trans spawned
    cases impossible
  | doneOk hstep henter hresume next =>
    simp only [Exec.descendantFramePaths] at found
    rw [descendantFramePaths_find_lt (Nat.lt_succ_self index) next] at found
    cases found
  | runOk hstep henter child hresume next =>
    have same := hstep.symm.trans spawned
    simp only [Step.spawn.injEq] at same
    obtain ⟨rfl, -, -⟩ := same
    exact ⟨_, henter⟩

/-! ## One reply is the entered frame's output -/

/-- **The reply of an observed call is the output of the frame it entered**, whenever the call's
child index holds a located (committed) frame. -/
theorem SourceCallAt.reply_of_found {root : Exec.Deriv} {frame : Frame} {request : Request}
    {reply : ExternalResult} {index : Nat} (obs : SourceCallAt root frame request reply index)
    {c : Exec.LocatedFrame}
    (found : (Exec.descendantFramePaths [] index obs.call.occurrence.node.exc).find?
      (fun c => c.path == [index]) = some c) :
    reply.returndata = c.frame.post.output := by
  have replyEq : reply.returndata = obs.child.output := by
    cases obs.replyAt with
    | bytes _ _ returndata => exact returndata
    | recovery _ _ returndata _ => exact returndata
  have response := obs.response
  rcases obs.queue with ⟨slotNone, -⟩ |
    ⟨childEvm, raw, callee, resume, pc', childRun, next, spawn, enter, resumed, slotSome, nodeExc,
      -⟩
  · obtain ⟨evm, entered⟩ := ParentStep.enters_of_found obs.call.edge obs.spawned found
    rw [slotNone] at response
    unfold ProcessMessage RunFrame at response
    rw [entered] at response
    obtain ⟨_, impossible, _⟩ := response
    cases impossible
  · have same := spawn.symm.trans obs.spawned
    simp only [Step.spawn.injEq] at same
    obtain ⟨rfl, -, -⟩ := same
    rw [slotSome] at response
    obtain ⟨-, settleEq⟩ := RunFrame.some_inv response
    by_cases settles : Jaune.Frame.settlementCommits (Jaune.Frame.ofCall obs.message) raw = true
    · rw [nodeExc, Exec.descendantFramePaths, dite_eq_left_of_eq_true (eq_true settles)] at found
      simp only [List.cons_append, List.find?_cons, List.nil_append, beq_self_eq_true,
        Option.some.injEq] at found
      subst found
      have settled := settleEq.trans
        (ofCall_settle_committed (Jaune.Frame.raw_commits_of_settlementCommits settles))
      rw [replyEq, Except.ok.inj settled, Devm.recordTouch_output]
      rfl
    · rw [nodeExc, Exec.descendantFramePaths, dite_eq_right_of_eq_false (eq_false settles),
        List.nil_append, descendantFramePaths_find_lt (Nat.lt_succ_self index) next] at found
      cases found

/-- The `n`-th own-level reply of a transcript. -/
def Transcript.replyAt : Transcript → Nat → Option ExternalResult
  | .next r _ _, 0 => some r
  | .next _ _ tail, n + 1 => tail.replyAt n
  | _, _ => none

theorem Transcript.replyAt_succ (t : Transcript) (n : Nat) :
    t.replyAt (n + 1) = t.ownTail.replyAt n := by
  cases t <;> simp only [Transcript.replyAt, Transcript.ownTail]

theorem Transcript.firstWord_of_replyAt {t : Transcript} {r : ExternalResult}
    (at0 : t.replyAt 0 = some r) : t.firstWord = Bytes.toB256 (r.returndata.take 32) := by
  cases t <;> simp only [Transcript.replyAt, reduceCtorEq] at at0
  cases at0
  rfl

/-- **Along a successful positional consumption, every reply whose call entered a located frame is
that frame's output** (the frame at child index `index + n` answers the `n`-th reply). -/
theorem PositionalConsumes.reply_of_found {root : Exec.Deriv} (n : Nat) :
    ∀ {start : Exec.Deriv} {index : Nat} {seg : SegmentResult} {t : Transcript} {out : RunResult}
      {bytes : Bytes}, PositionalConsumes root start index seg t out →
      out.status = .success bytes → ∀ c : Exec.LocatedFrame,
      (Exec.descendantFramePaths [] index start.exc).find? (fun c => c.path == [index + n]) =
        some c →
      ∃ r, t.replyAt n = some r ∧ r.returndata = c.frame.post.output := by
  induction n with
  | zero =>
    intro start index seg t out bytes consumed success c found
    rcases seg with ⟨fr, b⟩ | ⟨fr, failure⟩ | ⟨fr, request, k⟩
    · cases consumed with
      | finished frame bytes free =>
        rcases start with ⟨pc, sevm, pre, xout, run⟩
        rw [Exec.descendantFramePaths_eq_nil_of_noExec run free] at found
        cases found
    · rw [consumed.failed_status] at success
      cases success
    · obtain ⟨reply, turns, tail, obs, prior, out', C, rfl, gap, -, -, -, -, -⟩ :=
        consumed.suspended_inv
      rw [gap.descendantFramePaths_eq] at found
      exact ⟨reply, rfl, obs.reply_of_found found⟩
  | succ n ih =>
    intro start index seg t out bytes consumed success c found
    rcases seg with ⟨fr, b⟩ | ⟨fr, failure⟩ | ⟨fr, request, k⟩
    · cases consumed with
      | finished frame bytes free =>
        rcases start with ⟨pc, sevm, pre, xout, run⟩
        rw [Exec.descendantFramePaths_eq_nil_of_noExec run free] at found
        cases found
    · rw [consumed.failed_status] at success
      cases success
    · obtain ⟨reply, turns, tail, obs, prior, out', C, rfl, -, eq, below, -, rest, status⟩ :=
        consumed.suspended_inv
      rw [eq, List.find?_append, find_none_of_below (by omega) below, Option.none_or,
        show index + (n + 1) = index + 1 + n by omega] at found
      exact ih rest (status ▸ success) c found

/-- The committed frame `f`'s `i`-th call entered, as located in `f`'s run. -/
theorem childAt_found {f c : Exec.Frame} {i : Nat} (child : childAt f i = some c) :
    ∃ lc : Exec.LocatedFrame,
      (Exec.descendantFramePaths [] 0 (Blanc.Exec.Frame.rootDeriv f).exc).find?
        (fun c => c.path == [0 + i]) = some lc ∧ lc.frame = c := by
  unfold childAt at child
  obtain ⟨lc, found, eq⟩ := Option.map_eq_some_iff.mp child
  exact ⟨lc, by rw [Nat.zero_add]; exact found, eq⟩

/-- **The `i`-th reply of an outer call's transcript is the output of the frame its `i`-th call
entered**, whenever that call entered a committed frame. -/
theorem reply_of_childAt {f : Exec.Frame} {seg : SegmentResult} {t : Transcript}
    {out : RunResult} {bytes : Bytes}
    (consumed : PositionalConsumes (Blanc.Exec.Frame.rootDeriv f) (Blanc.Exec.Frame.rootDeriv f) 0
      seg t out)
    (success : out.status = .success bytes) {i : Nat} {c : Exec.Frame}
    (child : childAt f i = some c) :
    ∃ r, t.replyAt i = some r ∧ r.returndata = c.post.output := by
  obtain ⟨lc, found, rfl⟩ := childAt_found child
  exact PositionalConsumes.reply_of_found i consumed success lc found

/-! ## Observers -/

/-- The first output word of the frame `f`'s `i`-th call entered (`none` when that call entered no
committed frame). -/
def answerWord (f : Exec.Frame) (i : Nat) : Option B256 :=
  (childAt f i).map fun c => Bytes.toB256 (c.post.output.take 32)

/-- The `i`-th output word of the call `f` itself. -/
def outputWord (f : Exec.Frame) (i : Nat) : B256 :=
  Bytes.toB256 ((f.post.output.drop (32 * i)).take 32)

/-- **The token answers of a Pair call back its stored reserves.**  For `sync` (selector
`0xfff6cae9`): the frames entered by its first two calls (the two `balanceOf(pair)` reads) answered
at least the stored reserves.  For `burn` (selector `0x89afcb44`): its first two answers are at
least the stored reserves, and each is at most the matching final answer (calls 5 and 6, after the
two transfers) plus the payout the call returned.  Other calls: no condition. -/
def BalanceAnswersBacked (pair : Adr) (f : Exec.Frame) : Prop :=
  (Blanc.Sevm.selector f.sevm = 0xfff6cae9 →
    ∃ b0 b1 : B256, answerWord f 0 = some b0 ∧ answerWord f 1 = some b1 ∧
      (reserve0Word (preS pair f)).toNat ≤ b0.toNat ∧
      (reserve1Word (preS pair f)).toNat ≤ b1.toNat) ∧
  (Blanc.Sevm.selector f.sevm = 0x89afcb44 →
    ∃ b0 b1 final0 final1 : B256, answerWord f 0 = some b0 ∧ answerWord f 1 = some b1 ∧
      answerWord f 5 = some final0 ∧ answerWord f 6 = some final1 ∧
      (reserve0Word (preS pair f)).toNat ≤ b0.toNat ∧
      (reserve1Word (preS pair f)).toNat ≤ b1.toNat ∧
      b0.toNat ≤ final0.toNat + (outputWord f 0).toNat ∧
      b1.toNat ≤ final1.toNat + (outputWord f 1).toNat)

/-- The answers `BalanceAnswersBacked` consults came from committed frames. -/
def BalanceAnswersEntered (f : Exec.Frame) : Prop :=
  (Blanc.Sevm.selector f.sevm = 0xfff6cae9 →
    (childAt f 0).isSome ∧ (childAt f 1).isSome) ∧
  (Blanc.Sevm.selector f.sevm = 0x89afcb44 →
    (childAt f 0).isSome ∧ (childAt f 1).isSome ∧ (childAt f 5).isSome ∧ (childAt f 6).isSome)

/-! ## The bridge to the transcript condition -/

theorem answerWord_reply {f : Exec.Frame} {seg : SegmentResult} {t : Transcript}
    {out : RunResult} {bytes : Bytes}
    (consumed : PositionalConsumes (Blanc.Exec.Frame.rootDeriv f) (Blanc.Exec.Frame.rootDeriv f) 0
      seg t out)
    (success : out.status = .success bytes) {i : Nat} {w : B256}
    (answer : answerWord f i = some w) :
    ∃ r, t.replyAt i = some r ∧ Bytes.toB256 (r.returndata.take 32) = w := by
  unfold answerWord at answer
  obtain ⟨c, child, rfl⟩ := Option.map_eq_some_iff.mp answer
  obtain ⟨r, at_, eq⟩ := reply_of_childAt consumed success child
  exact ⟨r, at_, by rw [eq]⟩

theorem Transcript.secondWord_of_replyAt {t : Transcript} {r : ExternalResult}
    (at1 : t.replyAt 1 = some r) : t.ownTail.firstWord = Bytes.toB256 (r.returndata.take 32) := by
  rw [Transcript.replyAt_succ] at at1
  exact Transcript.firstWord_of_replyAt at1

/-- The final answers a burn reads are the transcript's sixth and seventh replies. -/
theorem burnFinalAnswers_of_replyAt {t : Transcript} {r5 r6 : ExternalResult}
    (at5 : t.replyAt 5 = some r5) (at6 : t.replyAt 6 = some r6) :
    burnFinalAnswers t.ownTail.ownTail.ownTail =
      some (Bytes.toB256 (r5.returndata.take 32), Bytes.toB256 (r6.returndata.take 32)) := by
  simp only [Transcript.replyAt_succ] at at5 at6
  generalize t.ownTail.ownTail.ownTail = t3 at at5 at6 ⊢
  rcases t3 with _ | ⟨x3, u3, t4⟩ | _ | _ <;> simp only [Transcript.ownTail,
    Transcript.replyAt, reduceCtorEq] at at5
  rcases t4 with _ | ⟨x4, u4, t5⟩ | _ | _ <;>
    simp only [Transcript.replyAt, reduceCtorEq] at at5
  rcases t5 with _ | ⟨x5, u5, t6⟩ | _ | _ <;>
    simp only [Transcript.replyAt, reduceCtorEq, Option.some.injEq] at at5
  rcases t6 with _ | ⟨x6, u6, t7⟩ | _ | _ <;> simp only [Transcript.ownTail,
    Transcript.replyAt, reduceCtorEq, Option.some.injEq] at at6
  subst at5 at6
  rfl

theorem encodeWords_two_word0 (a b : B256) : Bytes.toB256 ((encodeWords [a, b]).take 32) = a := by
  simp only [encodeWords, List.flatMap_cons, List.flatMap_nil, List.append_nil]
  rw [List.take_left' (B256.length_toBytes a), B256.toB256_toBytes]

theorem encodeWords_two_word1 (a b : B256) :
    Bytes.toB256 (((encodeWords [a, b]).drop (32 * 1)).take 32) = b := by
  simp only [encodeWords, List.flatMap_cons, List.flatMap_nil, List.append_nil]
  rw [List.drop_left' (B256.length_toBytes a), List.take_of_length_le
    (Nat.le_of_eq (B256.length_toBytes b)), B256.toB256_toBytes]

/-- The fee mint of the entry state with the lock taken is that of the entry state. -/
theorem feeAmount_unlocked (st : State) (u : B256) (feeTo : Adr) (r0 r1 : Nat) :
    feeAmount { st with unlocked := u } feeTo r0 r1 = feeAmount st feeTo r0 r1 := rfl

/-- **A successful burn returns its two payouts**: the call's output words are
`⌊L·b_i/(T + F)⌋`, `L` the Pair's own LP balance, `b_i` the transcript's first two answers and `F` the
fee minted at its third. -/
theorem burn_outputWords {f : Exec.Frame} {st : State} {ctx : Context} {recipient : Adr}
    {t : Transcript}
    (accepted : (runTyped st ctx (.burn recipient) t).status = .success f.post.output) :
    outputWord f 0 = Nat.toB256 (AMMArithmetic.burnPayment (st.balanceOf ctx.pair).toNat
        t.firstWord.toNat (st.totalSupply.toNat +
          feeAmount st t.ownTail.ownTail.firstWord.toAdr st.reserve0.val st.reserve1.val)) ∧
      outputWord f 1 = Nat.toB256 (AMMArithmetic.burnPayment (st.balanceOf ctx.pair).toNat
        t.ownTail.firstWord.toNat (st.totalSupply.toNat +
          feeAmount st t.ownTail.ownTail.firstWord.toAdr st.reserve0.val st.reserve1.val)) := by
  obtain ⟨-, -, -, fee, -, -, -, -, charged, -⟩ := runTyped_burn_conditions accepted
  obtain ⟨-, -, -, -, -, -, -, output⟩ := runTyped_burn_payout charged accepted
  have spec := mintFee_spec charged
  have supply : fee.state.totalSupply.toNat = st.totalSupply.toNat +
      feeAmount st t.ownTail.ownTail.firstWord.toAdr st.reserve0.val st.reserve1.val := by
    rw [spec.1, spec.2.2]; rfl
  have out0 := congrArg (fun b => Bytes.toB256 (b.take 32)) output
  have out1 := congrArg (fun b => Bytes.toB256 ((b.drop (32 * 1)).take 32)) output
  simp only [encodeWords_two_word0, encodeWords_two_word1] at out0 out1
  rw [← supply]
  exact ⟨out0, out1⟩

/-- **The backed answers give the transcript's backing condition at the call's own step.** -/
theorem entryNoShrink_of_backed {pair : Adr} {f : Exec.Frame} {K : WriterKey → Prop} {st : State}
    {ctx : Context} {entry : Entry} {t : Transcript} {out : RunResult}
    (rep : WriterRep K (preS pair f) st) (auth : PairEntryAt (Blanc.Exec.Frame.rootDeriv f) entry)
    (consumed : PositionalConsumes (Blanc.Exec.Frame.rootDeriv f) (Blanc.Exec.Frame.rootDeriv f) 0
      (startTyped { state := st, logs := [], updates := [] } ctx entry) t out)
    (success : out.status = .success f.post.output)
    (backed : BalanceAnswersBacked pair f) : EntryNoShrink st ctx entry t := by
  have runEq : runTyped st ctx entry t = out := (runTyped_of_exact consumed.forget).1
  have accepted : (runTyped st ctx entry t).status = .success f.post.output := by
    rw [runEq]; exact success
  cases auth
  case sync selector =>
    obtain ⟨b0, b1, a0, a1, le0, le1⟩ := backed.1 selector
    obtain ⟨r0, at0, w0⟩ := answerWord_reply consumed success a0
    obtain ⟨r1, at1, w1⟩ := answerWord_reply consumed success a1
    have word0 := Transcript.firstWord_of_replyAt at0
    have word1 := Transcript.secondWord_of_replyAt at1
    rw [rep.reserve0Word_toNat] at le0
    rw [rep.reserve1Word_toNat] at le1
    refine ⟨?_, ?_⟩
    · rw [word0, w0]; exact le0
    · rw [word1, w1]; exact le1
  case burn selector =>
    obtain ⟨b0, b1, final0, final1, a0, a1, a5, a6, le0, le1, cover0, cover1⟩ :=
      backed.2 selector
    obtain ⟨r0, at0, w0⟩ := answerWord_reply consumed success a0
    obtain ⟨r1, at1, w1⟩ := answerWord_reply consumed success a1
    obtain ⟨r5, at5, w5⟩ := answerWord_reply consumed success a5
    obtain ⟨r6, at6, w6⟩ := answerWord_reply consumed success a6
    have word0 := Transcript.firstWord_of_replyAt at0
    have word1 := Transcript.secondWord_of_replyAt at1
    rw [w0] at word0
    rw [w1] at word1
    have finals := burnFinalAnswers_of_replyAt at5 at6
    rw [w5, w6] at finals
    obtain ⟨out0, out1⟩ := burn_outputWords (f := f) accepted
    rw [rep.reserve0Word_toNat] at le0
    rw [rep.reserve1Word_toNat] at le1
    unfold EntryNoShrink BurnEntryNoShrink BurnFeeNoShrink
    rw [word0, word1]
    refine ⟨le0, le1, fun g0 g1 fin => ?_⟩
    rw [finals, Option.some.injEq, Prod.mk.injEq] at fin
    obtain ⟨rfl, rfl⟩ := fin
    rw [word0] at out0
    rw [word1] at out1
    rw [out0] at cover0
    rw [out1] at cover1
    exact ⟨cover0, cover1⟩
  case view view selector =>
    rcases view with ((s | s | s) | s | _ | s | _ | _) <;> (try cases s) <;> trivial
  all_goals trivial

theorem entry_sync_of_selector {f : Exec.Frame} {entry : Entry}
    (auth : PairEntryAt (Blanc.Exec.Frame.rootDeriv f) entry)
    (selector : Blanc.Sevm.selector f.sevm = 0xfff6cae9) : entry = .sync := by
  cases auth
  case sync => rfl
  case view view selector' =>
    change Blanc.Sevm.selector f.sevm = _ at selector'
    rw [selector] at selector'
    rcases view with ((s | s | s) | s | _ | s | _ | _) <;> (try cases s) <;> cases selector'
  all_goals
    rename_i selector'
    change Blanc.Sevm.selector f.sevm = _ at selector'
    rw [selector] at selector'
    cases selector'

theorem entry_burn_of_selector {f : Exec.Frame} {entry : Entry}
    (auth : PairEntryAt (Blanc.Exec.Frame.rootDeriv f) entry)
    (selector : Blanc.Sevm.selector f.sevm = 0x89afcb44) : ∃ recipient, entry = .burn recipient := by
  cases auth
  case burn => exact ⟨_, rfl⟩
  case view view selector' =>
    change Blanc.Sevm.selector f.sevm = _ at selector'
    rw [selector] at selector'
    rcases view with ((s | s | s) | s | _ | s | _ | _) <;> (try cases s) <;> cases selector'
  all_goals
    rename_i selector'
    change Blanc.Sevm.selector f.sevm = _ at selector'
    rw [selector] at selector'
    cases selector'

/-- A committed frame entered by call `i` answers the transcript's `i`-th own word. -/
theorem answerWord_of_entered {f : Exec.Frame} {seg : SegmentResult} {t : Transcript}
    {out : RunResult} {bytes : Bytes}
    (consumed : PositionalConsumes (Blanc.Exec.Frame.rootDeriv f) (Blanc.Exec.Frame.rootDeriv f) 0
      seg t out)
    (success : out.status = .success bytes) {i : Nat} (entered : (childAt f i).isSome) :
    ∃ r, t.replyAt i = some r ∧ answerWord f i = some (Bytes.toB256 (r.returndata.take 32)) := by
  obtain ⟨c, child⟩ := Option.isSome_iff_exists.mp entered
  obtain ⟨r, at_, eq⟩ := reply_of_childAt consumed success child
  exact ⟨r, at_, by rw [answerWord, child, Option.map_some, eq]⟩

/-- **The transcript's backing condition, with every consulted answer from a committed frame, gives
the backed answers.** -/
theorem backed_of_entryNoShrink {pair : Adr} {f : Exec.Frame} {K : WriterKey → Prop} {st : State}
    {ctx : Context} {entry : Entry} {t : Transcript} {out : RunResult}
    (rep : WriterRep K (preS pair f) st) (auth : PairEntryAt (Blanc.Exec.Frame.rootDeriv f) entry)
    (consumed : PositionalConsumes (Blanc.Exec.Frame.rootDeriv f) (Blanc.Exec.Frame.rootDeriv f) 0
      (startTyped { state := st, logs := [], updates := [] } ctx entry) t out)
    (success : out.status = .success f.post.output)
    (noShrink : EntryNoShrink st ctx entry t) (entered : BalanceAnswersEntered f) :
    BalanceAnswersBacked pair f := by
  have runEq : runTyped st ctx entry t = out := (runTyped_of_exact consumed.forget).1
  have accepted : (runTyped st ctx entry t).status = .success f.post.output := by
    rw [runEq]; exact success
  unfold BalanceAnswersBacked
  rw [rep.reserve0Word_toNat, rep.reserve1Word_toNat]
  refine ⟨fun selector => ?_, fun selector => ?_⟩
  · have entryEq := entry_sync_of_selector auth selector
    subst entryEq
    obtain ⟨e0, e1⟩ := entered.1 selector
    obtain ⟨r0, at0, a0⟩ := answerWord_of_entered consumed success e0
    obtain ⟨r1, at1, a1⟩ := answerWord_of_entered consumed success e1
    obtain ⟨le0, le1⟩ := noShrink
    rw [Transcript.firstWord_of_replyAt at0] at le0
    rw [Transcript.secondWord_of_replyAt at1] at le1
    exact ⟨_, _, a0, a1, le0, le1⟩
  · obtain ⟨recipient, entryEq⟩ := entry_burn_of_selector auth selector
    subst entryEq
    obtain ⟨e0, e1, e5, e6⟩ := entered.2 selector
    obtain ⟨r0, at0, a0⟩ := answerWord_of_entered consumed success e0
    obtain ⟨r1, at1, a1⟩ := answerWord_of_entered consumed success e1
    obtain ⟨r5, at5, a5⟩ := answerWord_of_entered consumed success e5
    obtain ⟨r6, at6, a6⟩ := answerWord_of_entered consumed success e6
    obtain ⟨out0, out1⟩ := burn_outputWords (f := f) accepted
    obtain ⟨le0, le1, covers⟩ := noShrink
    obtain ⟨cover0, cover1⟩ := covers _ _ (burnFinalAnswers_of_replyAt at5 at6)
    have word0 := Transcript.firstWord_of_replyAt at0
    have word1 := Transcript.secondWord_of_replyAt at1
    change st.reserve0.val ≤ t.firstWord.toNat at le0
    change st.reserve1.val ≤ t.ownTail.firstWord.toNat at le1
    change t.firstWord.toNat ≤ _ + (Nat.toB256 (AMMArithmetic.burnPayment
      (st.balanceOf ctx.pair).toNat t.firstWord.toNat
      (st.totalSupply.toNat +
        feeAmount st t.ownTail.ownTail.firstWord.toAdr st.reserve0.val st.reserve1.val))).toNat at cover0
    change t.ownTail.firstWord.toNat ≤ _ + (Nat.toB256 (AMMArithmetic.burnPayment
      (st.balanceOf ctx.pair).toNat t.ownTail.firstWord.toNat
      (st.totalSupply.toNat +
        feeAmount st t.ownTail.ownTail.firstWord.toAdr st.reserve0.val st.reserve1.val))).toNat at cover1
    rw [← out0] at cover0
    rw [← out1] at cover1
    rw [word0] at le0 cover0
    rw [word1] at le1 cover1
    exact ⟨_, _, _, _, a0, a1, a5, a6, le0, le1, cover0, cover1⟩

/-- **`BalanceAnswersBacked` is the transcript's backing condition `EntryNoShrink`, plus "every
consulted answer came from a committed frame"**, at an outer call's own consumed step. -/
theorem balanceAnswersBacked_iff {pair : Adr} {f : Exec.Frame} {K : WriterKey → Prop}
    {st : State} {ctx : Context} {entry : Entry} {t : Transcript} {out : RunResult}
    (rep : WriterRep K (preS pair f) st) (auth : PairEntryAt (Blanc.Exec.Frame.rootDeriv f) entry)
    (consumed : PositionalConsumes (Blanc.Exec.Frame.rootDeriv f) (Blanc.Exec.Frame.rootDeriv f) 0
      (startTyped { state := st, logs := [], updates := [] } ctx entry) t out)
    (success : out.status = .success f.post.output) :
    BalanceAnswersBacked pair f ↔ EntryNoShrink st ctx entry t ∧ BalanceAnswersEntered f := by
  refine ⟨fun backed => ⟨entryNoShrink_of_backed rep auth consumed success backed, ?_⟩,
    fun ⟨noShrink, entered⟩ => backed_of_entryNoShrink rep auth consumed success noShrink entered⟩
  have some_of {i : Nat} {w : B256} (h : answerWord f i = some w) : (childAt f i).isSome := by
    unfold answerWord at h
    obtain ⟨c, child, -⟩ := Option.map_eq_some_iff.mp h
    rw [child]; rfl
  refine ⟨fun selector => ?_, fun selector => ?_⟩
  · obtain ⟨_, _, a0, a1, -⟩ := backed.1 selector
    exact ⟨some_of a0, some_of a1⟩
  · obtain ⟨_, _, _, _, a0, a1, a5, a6, -⟩ := backed.2 selector
    exact ⟨some_of a0, some_of a1, some_of a5, some_of a6⟩

end Blanc.Lift.UniswapV2Pair
