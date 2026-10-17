import Blanc.Composition.PairTokenCallers

/-!
# The token ledger across one child of a Pair frame (C3 per-child frame layer)

Against the token core only (no token storage layout).  Take a settled frame `P` at the Pair and
one of its committed direct children `c`, whose committed subtree is a contiguous run of the
history's settled frames, with booked ledger `l` before it and the Pair holding no allowance.
Then (`pair_token_child_frames`), with `l'` the ledger after the subtree:

* the Pair keeps a zero allowance at `l'`;
* a static child leaves the ledger unchanged;
* a child at the token reading `balanceOf(pair)` answers the word `Nat.toB256 (bal l pair)`, and
  the balance is below `2 ^ 256` (A9), so the word reads back as the balance;
* a non-static `transfer` child at the token of `v` leaves the Pair at least `bal l pair - v`;
* any child elsewhere leaves the Pair at least `bal l pair`.

The local caller fold (`child_subtree_entries_caller`): inside the child's subtree, no non-static
token entry is called by the Pair, because non-static Pair frames there have only static children
(`LockedBelow`) and the token never forwards a foreign caller into its own entries (`SelfCaller`).
-/

namespace Blanc.Composition.PairTokenJoint

open Jaune Blanc Blanc.ExecutionTrace Blanc.Lift Blanc.Lift.Token Blanc.Lift.UniswapV2Pair

/-! ## List and frame facts -/

/-- A retained frame's committed frames are the frame itself, then its descendants. -/
theorem committedFrames_frame (F : Exec.Frame) :
    Exec.committedFrames F.run = F :: Exec.descendantFrames F.run := by
  obtain ⟨pc, sevm, pre, out, run, committed⟩ := F
  simp only [Exec.committedFrames, committed, ↓reduceDIte]
  rfl

open Classical in
/-- A list with no non-static entry asks nothing of the token. -/
theorem entryAsks_eq_nil {T : Adr} {frames : List Exec.Frame}
    (none : ∀ F ∈ frames, IsEntry T F → F.sevm.isStatic = false → False) :
    entryAsks T frames = [] := by
  unfold entryAsks
  rw [List.filter_eq_nil_iff.mpr fun F member picked =>
    none F member (of_decide_eq_true picked).1 (of_decide_eq_true picked).2]
  rfl

/-- The entry messages of a list with no non-static entry called by `h` contain no message of
`h`. -/
theorem entryAsks_filter_caller_nil {T h : Adr} {frames : List Exec.Frame}
    (none : ∀ F ∈ frames, IsEntry T F → F.sevm.isStatic = false → F.sevm.caller = h → False) :
    (entryAsks T frames).filter (fun a => decide (a.caller = h)) = [] :=
  List.filter_eq_nil_iff.mpr fun a member picked => by
    obtain ⟨F, inFrames, entry, static, rfl⟩ := mem_entryAsks member
    exact none F inFrames entry static (of_decide_eq_true picked)

/-- A run of the book that succeeds on an extension succeeds on the prefix. -/
theorem Book.run_some_of_append {B : Book} {l : B.Ledger} {xs ys : List Sevm} {m : B.Ledger}
    (whole : B.run l (xs ++ ys) = some m) : ∃ l', B.run l xs = some l' := by
  rw [Book.run_append] at whole
  cases prefixRun : B.run l xs with
  | none => rw [prefixRun, Option.bind_none] at whole; cases whole
  | some l' => exact ⟨l', rfl⟩

/-! ## Calldata of the Pair's token requests -/

theorem balanceOf_encode_length (owner : Adr) :
    (ExternalOperation.balanceOf owner).encode.length = 36 := by
  simp only [ExternalOperation.encode, encodeWords, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, List.length_append, B256.length_toBytes, List.length_cons, List.length_nil]

/-- A message carrying a `transfer` request is read by an ERC-20 book as that transfer. -/
theorem abi_op_transfer {B : Book} (abi : Erc20Abi B) {s : Sevm} {recipient : Adr}
    {value : B256} (data : s.data = (ExternalOperation.transfer recipient value).encode) :
    B.op s = .transfer recipient value.toNat := by
  have length := transfer_encode_length recipient value
  have words := transfer_encode_words data
  have selector : Blanc.Sevm.selector s = 0xa9059cbb := by
    rw [Blanc.Sevm.selector_eq_toB256_takeD_four, data]
    simp only [ExternalOperation.encode, List.cons_append, List.takeD, List.headD_cons,
      List.tail_cons]
    rfl
  rw [abi.transfer s (by rw [data, length]) selector, words.1, words.2, toAdr_toB256]

/-- A message carrying a `balanceOf(owner)` request is read by an ERC-20 book as that read. -/
theorem abi_op_balanceOf {B : Book} (abi : Erc20Abi B) {s : Sevm} {owner : Adr}
    (data : s.data = (ExternalOperation.balanceOf owner).encode) :
    B.op s = .balanceOf owner := by
  have length := balanceOf_encode_length owner
  have oLen : owner.toB256.toBytes.length = 32 := B256.length_toBytes _
  have selector : Blanc.Sevm.selector s = 0x70a08231 := by
    rw [Blanc.Sevm.selector_eq_toB256_takeD_four, data]
    simp only [ExternalOperation.encode, List.cons_append, List.takeD, List.headD_cons,
      List.tail_cons]
    rfl
  have dropFour : List.drop 4 s.data = owner.toB256.toBytes := by
    rw [data]
    simp only [ExternalOperation.encode, encodeWords, List.flatMap_cons, List.flatMap_nil,
      List.append_nil]
    rfl
  have word : Sevm.dataWord s 4 = owner.toB256 := by
    unfold Sevm.dataWord List.sliceD
    rw [show (4 : B256).toNat = 4 from rfl, dropFour, List.takeD_eq_self 0 oLen.symm,
      B256.toB256_toBytes]
  rw [abi.balanceOf s (by rw [data, length]) selector, word, toAdr_toB256]

/-! ## The local caller fold -/

/-- **Inside a committed subtree whose Pair frames are locked, no non-static token entry is called
by the Pair.** -/
theorem child_subtree_entries_caller {pair T : Adr} {B : Book} (C : Core T B) (self : SelfCaller C)
    {cfg : ChainConfig} {checkpoint future : BlockChain}
    (trace : ConfiguredHistoryTrace cfg checkpoint future) (hist : C.Hist trace) (apart : pair ≠ T)
    {c : Exec.Frame} (settled : ∀ G ∈ Exec.committedFrames c.run, G ∈ trace.settledFrames)
    (locked : LockedBelow pair (Exec.committedFrames c.run)) :
    ∀ F ∈ Exec.descendantFrames c.run, IsEntry T F → F.sevm.isStatic = false →
      F.sevm.caller = pair → False := by
  have children : ∀ G ∈ Exec.committedFrames c.run,
      CallerChildren pair T (fun s => s.isStatic = false → s.codeAddress = some T → False) G.sevm
        (Exec.childFrames G.run) := by
    intro G member which d child target caller static codeAddress
    rcases which with atPair | atToken
    · cases staticG : G.sevm.isStatic
      · rw [locked G member atPair staticG d child] at static
        cases static
      · rw [Exec.childFrames_isStatic G.run staticG d child] at static
        cases static
    · cases staticG : G.sevm.isStatic
      · have selfCaller := self.child_caller trace hist G (settled G member) atToken staticG d child
          ⟨target, codeAddress⟩
        exact apart (caller.symm.trans selfCaller)
      · rw [Exec.childFrames_isStatic G.run staticG d child] at static
        cases static
  rw [committedFrames_frame] at children
  have fold := Exec.descendantFrames_callerTarget_of_children c.run
    (children c List.mem_cons_self) (fun G member => children G (List.mem_cons_of_mem _ member))
  intro F member entry static caller
  exact fold F member entry.1 caller static entry.2

/-- A committed child at the token of a settled Pair frame is an entry of the token (A8
`decodes`: the parent is not at the token). -/
theorem child_isEntry {pair T : Adr} {B : Book} (C : Core T B) {cfg : ChainConfig}
    {checkpoint future : BlockChain} (trace : ConfiguredHistoryTrace cfg checkpoint future)
    (hist : C.Hist trace) (apart : pair ≠ T) {P c : Exec.Frame}
    (settledP : P ∈ trace.settledFrames) (atPair : P.sevm.currentTarget = pair)
    (child : c ∈ Exec.childFrames P.run) (settledC : c ∈ trace.settledFrames)
    (target : c.sevm.currentTarget = T) : IsEntry T c := by
  by_cases entry : IsEntry T c
  · exact entry
  · exact absurd (atPair.symm.trans (C.decodes trace hist c settledC target entry P settledP child))
      apart

/-! ## One child -/

/-- **The token ledger across one child of a Pair frame.** -/
theorem pair_token_child_frames {pair T : Adr} {B : Book} (C : Core T B) (laws : BookLaws B)
    (abi : Erc20Abi B) (self : SelfCaller C) {cfg : ChainConfig} {checkpoint future : BlockChain}
    (trace : ConfiguredHistoryTrace cfg checkpoint future) (hist : C.Hist trace)
    (apart : pair ≠ T) (answerable : C.Answerable trace pair)
    {P c : Exec.Frame} (settledP : P ∈ trace.settledFrames) (atPair : P.sevm.currentTarget = pair)
    (child : c ∈ Exec.childFrames P.run) (callerPair : c.sevm.caller = pair)
    (locked : LockedBelow pair (Exec.committedFrames c.run))
    (toT : c.sevm.currentTarget = T → c.sevm.isStatic = false →
      ∃ recipient value, c.sevm.data = (ExternalOperation.transfer recipient value).encode)
    {pre post : List Exec.Frame}
    (split : trace.settledFrames = pre ++ Exec.committedFrames c.run ++ post)
    {l : B.Ledger} (atPre : B.run (C.ledgerOf trace checkpoint.state) (entryAsks T pre) = some l)
    (zero : ∀ g, B.allow l pair g = 0) :
    ∃ l', B.run l (entryAsks T (Exec.committedFrames c.run)) = some l' ∧
      (∀ g, B.allow l' pair g = 0) ∧
      (c.sevm.isStatic = true → l' = l) ∧
      (c.sevm.currentTarget = T → c.sevm.data = (ExternalOperation.balanceOf pair).encode →
        c.post.output = (Nat.toB256 (B.bal l pair)).toBytes ∧ B.bal l pair < 2 ^ 256) ∧
      (∀ {recipient : Adr} {value : B256}, c.sevm.currentTarget = T → c.sevm.isStatic = false →
        c.sevm.data = (ExternalOperation.transfer recipient value).encode →
        B.bal l pair ≤ B.bal l' pair + value.toNat) ∧
      (c.sevm.currentTarget ≠ T → B.bal l pair ≤ B.bal l' pair) := by
  have settled : ∀ G ∈ Exec.committedFrames c.run, G ∈ trace.settledFrames := fun G member => by
    rw [split]
    exact List.mem_append_left _ (List.mem_append_right _ member)
  have settledC : c ∈ trace.settledFrames :=
    settled c (by rw [committedFrames_frame]; exact List.mem_cons_self)
  have inner := child_subtree_entries_caller C self trace hist apart settled locked
  -- the ledger after the subtree
  obtain ⟨l', step⟩ : ∃ l', B.run l (entryAsks T (Exec.committedFrames c.run)) = some l' := by
    have whole := C.replayEnd trace hist
    rw [split, entryAsks_append, entryAsks_append, List.append_assoc, Book.run_append, atPre,
      Option.bind_some] at whole
    exact Book.run_some_of_append whole
  -- the Pair's own messages in the subtree: at most the child itself
  have callerAsks : (entryAsks T (Exec.committedFrames c.run)).filter
      (fun a => decide (a.caller = pair)) =
      (entryAsks T [c]).filter (fun a => decide (a.caller = pair)) := by
    rw [committedFrames_frame, entryAsks_cons, List.filter_append,
      entryAsks_filter_caller_nil inner, List.append_nil]
  have safe : ∀ a ∈ entryAsks T (Exec.committedFrames c.run), a.caller = pair →
      (B.op a).HolderSafe := by
    intro a member caller
    obtain ⟨F, inSub, entry, static, rfl⟩ := mem_entryAsks member
    rw [committedFrames_frame] at inSub
    rcases List.mem_cons.mp inSub with rfl | deeper
    · obtain ⟨recipient, value, data⟩ := toT entry.1 static
      rw [abi_op_transfer abi data]
      trivial
    · exact (inner F deeper entry static caller).elim
  obtain ⟨bound, zero'⟩ := C.run_holder_segment laws trace hist split atPre step zero safe
  rw [callerAsks] at bound
  refine ⟨l', step, zero', ?_, ?_, ?_, ?_⟩
  · -- static child
    intro static
    have none : entryAsks T (Exec.committedFrames c.run) = [] := by
      apply entryAsks_eq_nil
      intro F member _ mutable
      rw [committedFrames_frame] at member
      rcases List.mem_cons.mp member with rfl | deeper
      · rw [static] at mutable; cases mutable
      · rw [Exec.descendantFrames_isStatic c.run static F deeper] at mutable; cases mutable
    rw [none] at step
    exact (Option.some.inj step).symm
  · -- a read of the token
    intro target data
    have entry := child_isEntry C trace hist apart settledP atPair child settledC target
    have answer :=
      C.balanceAnswer trace hist c settledC entry (abi_op_balanceOf abi data) answerable
    have atC := C.replayAt trace hist pre c (Exec.descendantFrames c.run ++ post) (by
      rw [split, committedFrames_frame, List.append_assoc, List.cons_append])
    rw [atPre] at atC
    have ledgerEq : C.ledgerOf trace c.pre.state = l := (Option.some.inj atC).symm
    rw [ledgerEq] at answer
    have good : B.Good l := by
      rw [← ledgerEq]
      exact C.goodAt trace hist c settledC
    exact ⟨answer, laws.bal_lt good⟩
  · -- a transfer to the token
    intro recipient value target static data
    have entry := child_isEntry C trace hist apart settledP atPair child settledC target
    rw [entryAsks_single_of_entry ⟨entry, static⟩] at bound
    simp only [List.filter_cons, callerPair, decide_true, ite_true, List.filter_nil,
      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero] at bound
    rw [abi_op_transfer abi data] at bound
    exact bound
  · -- any child elsewhere
    intro target
    have notEntry : ¬ (IsEntry T c ∧ c.sevm.isStatic = false) := fun h => target h.1.1
    rw [entryAsks_single_of_not_entry notEntry] at bound
    simpa only [List.filter_nil, List.map_nil, List.sum_nil, Nat.add_zero] using bound

end Blanc.Composition.PairTokenJoint
