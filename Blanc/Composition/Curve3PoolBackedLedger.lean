import Blanc.Composition.Curve3PoolBackedModel
import Blanc.Lift.ViewChain
import Blanc.Lift.BalanceLocality

/-!
# One coin's ledger against the pool's books, by position in the settled frames

A coin's frames carry a view of its storage (`ViewChain`), each frame moving what it reads by the amounts its message
names. `CoinBook` collects how a coin is read; `Ledger` is what its locality theorem gives over a list of settled
frames; `Covered` says the books are at most what the position after a prefix of the frames reads. It is stated at the
position, not at a world, so a frame nested anywhere in the list has a position.

* `Ledger.gap`: frames whose callers are not the pool do not lower the reading;
* `Ledger.invocation`: across one pool frame, the books follow `Flow`, so they stay covered.
-/

namespace Blanc.Composition.Curve3PoolBacked

open Jaune Blanc Blanc.Lift
open Blanc.Lift.Curve3Pool (Env Out feeIndex)

/-- How a coin's ledger is read. `Rd xs` reads the position after chain frames `xs`. -/
structure CoinBook where
  T : Adr
  V : StorWords → StorWords
  Obs : Exec.Frame → Prop
  Good : Exec.Frame → Prop
  held : Exec.Frame → StorWords → Nat
  debit : Sevm → Nat
  credit : Sevm → Nat
  Rd : List Exec.Frame → StorWords → Nat

namespace CoinBook

variable (B : CoinBook)

/-- The chain's frames among `fs`. -/
noncomputable abbrev cf (fs : List Exec.Frame) : List Exec.Frame := coinFrames B.T B.Obs fs

/-- Frames carrying the view. -/
abbrev Chain (a : StorWords) (xs : List Exec.Frame) (b : StorWords) : Prop := ViewChain B.T B.V B.Good a xs b

/-- What the frames' messages say goes in. -/
def sumCredit (xs : List Exec.Frame) : Nat := (xs.map fun F => B.credit F.sevm).sum

/-- What the frames' messages say goes out. -/
def sumDebit (xs : List Exec.Frame) : Nat := (xs.map fun F => B.debit F.sevm).sum

/-- **The books at most what the position after `pre` reads.** -/
def Covered (a : StorWords) (pre : List Exec.Frame) (r : Nat) : Prop :=
  ∃ m, B.Chain a (B.cf pre) m ∧ r ≤ B.Rd (B.cf pre) m

end CoinBook

variable {B : CoinBook}

theorem cf_append (xs ys : List Exec.Frame) : B.cf (xs ++ ys) = B.cf xs ++ B.cf ys := coinFrames_append _ _ _ _

theorem chain_det {a b b' : StorWords} : ∀ {xs : List Exec.Frame}, B.Chain a xs b → B.Chain a xs b' → b = b'
  | [], h, h' => h.trans h'.symm
  | _ :: _, h, h' => chain_det h.2.2 h'.2.2

theorem chain_split : ∀ {a c : StorWords} {xs ys : List Exec.Frame}, B.Chain a (xs ++ ys) c →
    ∃ b, B.Chain a xs b ∧ B.Chain b ys c
  | a, _, [], _, h => ⟨a, rfl, h⟩
  | _, _, _ :: _, _, h => by
    obtain ⟨b, hx, hy⟩ := chain_split h.2.2
    exact ⟨b, ⟨h.1, h.2.1, hx⟩, hy⟩

/-- **What a coin's locality gives**, over the settled frames `frames`, from `a` to `b`. -/
structure Ledger (B : CoinBook) (pool : Adr) (frames : List Exec.Frame) (a b : StorWords) : Prop where
  loc : EntryLocalAt B.T B.V B.Obs B.Good B.held B.debit B.credit a b frames
  /-- Entering a frame: the position's reading is at most the frame's. -/
  seam : ∀ xs F ys, B.cf frames = xs ++ F :: ys → B.Rd xs (B.V (wordsAt B.T F.pre.state)) ≤
    B.held F (B.V (wordsAt B.T F.pre.state))
  /-- Leaving a frame: the frame's reading is at most the position's. -/
  leave : ∀ xs F ys, B.cf frames = xs ++ F :: ys →
    B.held F (B.V (wordsAt B.T F.post.state)) ≤ B.Rd (xs ++ [F]) (B.V (wordsAt B.T F.post.state))
  /-- A frame the pool did not call takes nothing out by its message. -/
  third : ∀ F ∈ B.cf frames, F.sevm.caller ≠ pool → B.debit F.sevm = 0

variable {pool : Adr} {frames : List Exec.Frame} {a b : StorWords}

/-- **A run of chain frames moves the reading by their amounts.** -/
theorem Ledger.run (L : Ledger B pool frames a b) :
    ∀ (zs xs ys : List Exec.Frame) {m m' : StorWords}, B.cf frames = xs ++ zs ++ ys → B.Chain m zs m' →
      B.Rd xs m + B.sumCredit zs ≤ B.Rd (xs ++ zs) m' + B.sumDebit zs
  | [], xs, ys, m, m', _, h => by
    cases h
    simp only [CoinBook.sumCredit, CoinBook.sumDebit, List.map_nil, List.sum_nil, List.append_nil, Nat.add_zero,
      Nat.le_refl]
  | F :: zs, xs, ys, m, m', split, h => by
    obtain ⟨-, rfl, rest⟩ := h
    have split' : B.cf frames = xs ++ F :: (zs ++ ys) := by
      rw [split]
      simp only [List.append_assoc, List.cons_append]
    have mem : F ∈ B.cf frames := by
      rw [split']
      exact List.mem_append_right _ List.mem_cons_self
    have hs := L.seam xs F _ split'
    have hl := L.loc.law F mem
    have hv := L.leave xs F (zs ++ ys) split'
    have ih := L.run zs (xs ++ [F]) ys (m := B.V (wordsAt B.T F.post.state)) (m' := m')
      (by rw [split]; simp only [List.append_assoc, List.cons_append, List.nil_append]) rest
    have e : xs ++ [F] ++ zs = xs ++ F :: zs := by simp only [List.append_assoc, List.cons_append, List.nil_append]
    rw [e] at ih
    simp only [CoinBook.sumCredit, CoinBook.sumDebit, List.map_cons, List.sum_cons] at ih ⊢
    omega

theorem sumDebit_zero {zs : List Exec.Frame} (h : ∀ F ∈ zs, B.debit F.sevm = 0) : B.sumDebit zs = 0 := by
  induction zs with
  | nil => rfl
  | cons F zs ih =>
    simp only [CoinBook.sumDebit, List.map_cons, List.sum_cons] at ih ⊢
    rw [h F List.mem_cons_self, ih fun G hG => h G (List.mem_cons_of_mem _ hG)]

/-- The position after a prefix of the settled frames. -/
theorem Ledger.position (L : Ledger B pool frames a b) {pre post : List Exec.Frame} (split : frames = pre ++ post) :
    ∃ m m', B.Chain a (B.cf pre) m ∧ B.Chain m (B.cf post) m' := by
  have whole := L.loc.chain
  rw [split, coinFrames_append] at whole
  obtain ⟨m, hx, hy⟩ := chain_split whole
  exact ⟨m, b, hx, hy⟩

/-- **Frames the pool did not call do not lower the reading.** -/
theorem Ledger.gap (L : Ledger B pool frames a b) {pre gap post : List Exec.Frame} (split : frames = pre ++ gap ++ post)
    (callers : ∀ F ∈ B.cf gap, F.sevm.caller ≠ pool) {r : Nat} (cover : B.Covered a pre r) :
    B.Covered a (pre ++ gap) r := by
  obtain ⟨m, hm, hr⟩ := cover
  obtain ⟨m₁, m₂, h₁, h₂⟩ := L.position (pre := pre ++ gap) (post := post) split
  rw [cf_append] at h₁
  obtain ⟨m₃, h₃, h₄⟩ := chain_split h₁
  obtain rfl := chain_det h₃ hm
  have full : B.cf frames = B.cf pre ++ B.cf gap ++ B.cf post := by
    rw [split, cf_append, cf_append]
  have mv := L.run (B.cf gap) (B.cf pre) (B.cf post) full h₄
  have memGap : ∀ F ∈ B.cf gap, F ∈ B.cf frames := fun F hF => by
    rw [full]
    exact List.mem_append_left _ (List.mem_append_right _ hF)
  have zero : B.sumDebit (B.cf gap) = 0 := sumDebit_zero fun F hF => L.third F (memGap F hF) (callers F hF)
  refine ⟨m₁, ?_, ?_⟩
  · rw [cf_append]
    exact h₁
  · rw [cf_append]
    omega

/-- `Ledger.run` between two positions named by their chains from the start. -/
theorem Ledger.run' (L : Ledger B pool frames a b) {xs zs ys : List Exec.Frame} {m m' : StorWords}
    (full : B.cf frames = xs ++ zs ++ ys) (h : B.Chain a xs m) (h' : B.Chain a (xs ++ zs) m') :
    B.Rd xs m + B.sumCredit zs ≤ B.Rd (xs ++ zs) m' + B.sumDebit zs := by
  obtain ⟨m₃, h₃, h₄⟩ := chain_split h'
  obtain rfl := chain_det h₃ h
  exact L.run zs xs ys full h₄

theorem sumDebit_append (xs ys : List Exec.Frame) : B.sumDebit (xs ++ ys) = B.sumDebit xs + B.sumDebit ys := by
  simp only [CoinBook.sumDebit, List.map_append, List.sum_append]

section Invocation

variable {P : Exec.Frame} {pre rest kids : List Exec.Frame}

/-- The frames of the children `cs`, their subtrees included. -/
def blocks (cs : List Exec.Frame) : List Exec.Frame := cs.flatMap fun c => Exec.committedFrames c.run

theorem blocks_append (xs ys : List Exec.Frame) : blocks (xs ++ ys) = blocks xs ++ blocks ys :=
  List.flatMap_append

/-- The position before the children `L₁` reads `w`. -/
def ReadsAt (B : CoinBook) (a : StorWords) (pre L₁ : List Exec.Frame) (w : Nat) : Prop :=
  ∃ m, B.Chain a (B.cf pre ++ B.cf (blocks L₁)) m ∧ w = B.Rd (B.cf pre ++ B.cf (blocks L₁)) m

/-- **Across one pool frame the books stay covered**, given how its children's messages add up against the model's
calls, and where the coin's answers were read. -/
theorem Ledger.invocation (L : Ledger B pool frames a b) {k : Fin 3} {s : Curve3Pool.State} {e : Env} {o : Out}
    (split : frames = pre ++ P :: (blocks kids ++ rest)) (notAt : B.cf [P] = [])
    (flow : Flow s e o k)
    (sumD : B.sumDebit (B.cf (blocks kids)) ≤ pushed k o.calls)
    (sumC : k ≠ feeIndex → pulled k o.calls ≤ B.sumCredit (B.cf (blocks kids)))
    (reads : ∀ w, (e.coin k).balPre = some w → ∃ L₁ L₂, kids = L₁ ++ L₂ ∧ ReadsAt B a pre L₁ w)
    (pair : ∀ p q, (e.coin k).balPre = some p → (e.coin k).balPost = some q →
      ∃ L₁ M L₂, kids = L₁ ++ M ++ L₂ ∧ ReadsAt B a pre L₁ p ∧ ReadsAt B a pre (L₁ ++ M) q)
    {r : Nat} (hs : r = s.balances.get k) (cover : B.Covered a pre r) :
    B.Covered a (pre ++ P :: blocks kids) (o.state.balances.get k) := by
  obtain ⟨m0, hm0, hr⟩ := cover
  have cfEq : B.cf (pre ++ P :: blocks kids) = B.cf pre ++ B.cf (blocks kids) := by
    rw [show pre ++ P :: blocks kids = pre ++ ([P] ++ blocks kids) from rfl, cf_append, cf_append, notAt,
      List.nil_append]
  have full : B.cf frames = B.cf pre ++ B.cf (blocks kids) ++ B.cf rest := by
    rw [split, show pre ++ P :: (blocks kids ++ rest) = pre ++ P :: blocks kids ++ rest by
      simp only [List.append_assoc, List.cons_append], cf_append, cfEq]
  obtain ⟨m1, -, hz, -⟩ := L.position (pre := pre ++ P :: blocks kids) (post := rest) (by
    rw [split]
    simp only [List.append_assoc, List.cons_append])
  rw [cfEq] at hz
  have mv := L.run' full hm0 hz
  refine ⟨m1, by rw [cfEq]; exact hz, ?_⟩
  rw [cfEq]
  have kidsEq : ∀ {A C : List Exec.Frame}, kids = A ++ C → B.cf (blocks kids) = B.cf (blocks A) ++ B.cf (blocks C) := by
    intro A C e
    rw [e, blocks_append, cf_append]
  cases flow with
  | plain books fits notFee =>
    have hpull : pulled k o.calls ≤ B.sumCredit (B.cf (blocks kids)) := by
      by_cases f : k = feeIndex
      · rw [notFee f]
        exact Nat.zero_le _
      · exact sumC f
    omega
  | read hp books inn =>
    obtain ⟨L₁, L₂, e, m2, hm2, rfl⟩ := reads _ hp
    have split2 := kidsEq e
    have full2 : B.cf frames = (B.cf pre ++ B.cf (blocks L₁)) ++ B.cf (blocks L₂) ++ B.cf rest := by
      rw [full, split2]
      simp only [List.append_assoc]
    have hz2 : B.Chain a ((B.cf pre ++ B.cf (blocks L₁)) ++ B.cf (blocks L₂)) m1 := by
      rw [List.append_assoc, ← split2]
      exact hz
    have mv2 := L.run' full2 hm2 hz2
    rw [List.append_assoc, ← split2] at mv2
    have dsplit : B.sumDebit (B.cf (blocks kids)) =
        B.sumDebit (B.cf (blocks L₁)) + B.sumDebit (B.cf (blocks L₂)) := by
      rw [split2, sumDebit_append]
    omega
  | measured fee hp hq le books out =>
    obtain ⟨L₁, M, L₂, e, ⟨mp, hmp, ep⟩, ⟨mq, hmq, eq⟩⟩ := pair _ _ hp hq
    rename_i p q
    have eA : kids = L₁ ++ (M ++ L₂) := by rw [e, List.append_assoc]
    have s1 : B.cf (blocks kids) = B.cf (blocks L₁) ++ (B.cf (blocks M) ++ B.cf (blocks L₂)) := by
      rw [kidsEq eA, blocks_append, cf_append]
    have xs1 : B.cf (blocks (L₁ ++ M)) = B.cf (blocks L₁) ++ B.cf (blocks M) :=
      (congrArg B.cf (blocks_append _ _)).trans (coinFrames_append _ _ _ _)
    rw [xs1] at hmq eq
    have dz : B.sumDebit (B.cf (blocks kids)) = 0 := by omega
    rw [s1, sumDebit_append, sumDebit_append] at dz
    have zero1 : B.sumDebit (B.cf (blocks L₁)) = 0 := by omega
    have zero2 : B.sumDebit (B.cf (blocks M)) = 0 := by omega
    have zero3 : B.sumDebit (B.cf (blocks L₂)) = 0 := by omega
    have f1 : B.cf frames = B.cf pre ++ B.cf (blocks L₁) ++ (B.cf (blocks M) ++ B.cf (blocks L₂) ++ B.cf rest) := by
      rw [full, s1]
      simp only [List.append_assoc]
    have m1' := L.run' f1 hm0 hmp
    have f2 : B.cf frames = (B.cf pre ++ B.cf (blocks L₁)) ++ B.cf (blocks M) ++ (B.cf (blocks L₂) ++ B.cf rest) := by
      rw [full, s1]
      simp only [List.append_assoc]
    have hmq' : B.Chain a ((B.cf pre ++ B.cf (blocks L₁)) ++ B.cf (blocks M)) mq := by
      rw [List.append_assoc]
      exact hmq
    have m2' := L.run' f2 hmp hmq'
    have f3 : B.cf frames = (B.cf pre ++ (B.cf (blocks L₁) ++ B.cf (blocks M))) ++ B.cf (blocks L₂) ++ B.cf rest := by
      rw [full, s1]
      simp only [List.append_assoc]
    have hz3 : B.Chain a ((B.cf pre ++ (B.cf (blocks L₁) ++ B.cf (blocks M))) ++ B.cf (blocks L₂)) m1 := by
      rw [show (B.cf pre ++ (B.cf (blocks L₁) ++ B.cf (blocks M))) ++ B.cf (blocks L₂) = B.cf pre ++ B.cf (blocks kids) by
        rw [s1]; simp only [List.append_assoc]]
      exact hz
    have m3' := L.run' f3 hmq hz3
    rw [show (B.cf pre ++ (B.cf (blocks L₁) ++ B.cf (blocks M))) ++ B.cf (blocks L₂) = B.cf pre ++ B.cf (blocks kids) by
      rw [s1]; simp only [List.append_assoc]] at m3'
    rw [List.append_assoc] at m2'
    omega

/-- **Where the frame moves nothing out, what the coin answers covers the books at its entry.** -/
theorem Ledger.reply_cover (L : Ledger B pool frames a b) (split : frames = pre ++ P :: (blocks kids ++ rest))
    (notAt : B.cf [P] = []) {L₁ L₂ : List Exec.Frame} (e : kids = L₁ ++ L₂)
    (none : B.sumDebit (B.cf (blocks kids)) = 0) {w r : Nat} (h : ReadsAt B a pre L₁ w) (cover : B.Covered a pre r) :
    r ≤ w := by
  obtain ⟨m0, hm0, hr⟩ := cover
  obtain ⟨m, hm, rfl⟩ := h
  have kidsEq : B.cf (blocks kids) = B.cf (blocks L₁) ++ B.cf (blocks L₂) := by
    rw [e, blocks_append, cf_append]
  have full : B.cf frames = B.cf pre ++ B.cf (blocks L₁) ++ (B.cf (blocks L₂) ++ B.cf rest) := by
    rw [split, show pre ++ P :: (blocks kids ++ rest) = pre ++ ([P] ++ (blocks kids ++ rest)) from rfl, cf_append,
      cf_append, notAt, cf_append, kidsEq]
    simp only [List.nil_append, List.append_assoc]
  have mv := L.run' full hm0 hm
  rw [kidsEq, sumDebit_append] at none
  omega

end Invocation

end Blanc.Composition.Curve3PoolBacked
