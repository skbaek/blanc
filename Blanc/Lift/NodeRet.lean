import Blanc.Lift.Cursor

/-!
# A callee whose frame holds no return marker never returns (bytes-free)

A symbolic checker that walks a certificate's trees alongside `checkNode`'s abstract stack
(`List AVal`) and, like `checkNode`, requires the abstract return marker `.ret` on top at every
`.ret` node and `gotoCompat` at every goto, has this property without reading any byte: a
returning run of a tree accepted from abstract frame `a` has `.ret ∈ a`.  So a `callNext` whose
callee's declared frame holds no `.ret` returns from no run, and its continuation needs no check.

The property is stated once over any node predicate `Q a f` closed under the checker's
arms (`RetClosed`): the free-pointer walk (`fpNode`) and the write-site walk (`wsNode`) each
instantiate it with `Q a f := ∃ …, node … a … f = true`.  Contract-neutral.
-/

namespace Blanc.Lift

open Jaune AbstractStackSafety

/-- A node predicate over (abstract frame, tree) with `checkNode`'s return discipline: the
entries of `fs` hold from their declared frames, instructions move the frame through
`absNinst`, gotos admit their target's frame (`gotoCompat`), a returning call's continuation
holds from the frame `checkNode` gives it, and a `.ret` node has `.ret` on top. -/
structure RetClosed (es : List Entry) (fs : List SFunc) (Q : List AVal → SFunc → Prop) : Prop where
  entry : ∀ {k : Nat} {e : Entry} {g : SFunc}, es[k]? = some e → fs[k]? = some g → Q e.frame g
  next : ∀ {a : List AVal} {n : Ninst} {f : SFunc}, Q a (.next n f) → ∃ a', absNinst n a = some a' ∧ Q a' f
  dest : ∀ {a : List AVal} {f : SFunc}, Q a (.dest f) → Q a f
  branch : ∀ {a : List AVal} {f g : SFunc}, Q a (.branch f g) → ∃ (x y : AVal) (a' : List AVal), a = x :: y :: a' ∧ Q a' f ∧ Q a' g
  branchTo : ∀ {a : List AVal} {f : SFunc} {k : Nat}, Q a (.branchTo f k) →
    ∃ (x y : AVal) (a' : List AVal) (e : Entry), a = x :: y :: a' ∧ es[k]? = some e ∧ gotoCompat a' e.frame = true ∧ Q a' f
  jump : ∀ {a : List AVal} {k : Nat}, Q a (.jump k) →
    ∃ (x : AVal) (a' : List AVal) (e : Entry), a = x :: a' ∧ es[k]? = some e ∧ gotoCompat a' e.frame = true
  callNext : ∀ {a : List AVal} {k : Nat} {f : SFunc}, Q a (.callNext k f) →
    ∃ (x : AVal) (a' : List AVal) (e : Entry), a = x :: a' ∧ es[k]? = some e ∧
      ∀ i, e.frame.findIdx? (· == .ret) = some i →
        Q (List.replicate e.rets .unk ++ a'.drop e.frame.length) f
  ret : ∀ {a : List AVal}, Q a .ret → ∃ a', a = .ret :: a'
  pcAt : ∀ {a : List AVal} {p : Nat} {f : SFunc}, Q a (.pcAt p f) → Q (.const (Nat.toB256 p) :: a) f

private theorem ret_mem_of_cont {rets : Nat} {a : List AVal} {n : Nat}
    (h : AVal.ret ∈ List.replicate rets .unk ++ a.drop n) : AVal.ret ∈ a := by
  rcases List.mem_append.mp h with h | h
  · exact absurd (List.eq_of_mem_replicate h) (by decide)
  · exact List.mem_of_mem_drop h

/-- **A returning run starts from a frame holding the return marker.** -/
theorem SFunc.RunP.ret_mem {es : List Entry} {Q : List AVal → SFunc → Prop}
    {P : Sevm → Devm → Ninst → Devm → Prop} {fs : List SFunc} {sevm : Sevm}
    (hQ : RetClosed es fs Q) {d d' : Devm} {f : SFunc}
    (run : SFunc.RunP P fs sevm d f (.returned d')) {a : List AVal} (ha : Q a f) :
    AVal.ret ∈ a := by
  generalize ho : Outcome.returned d' = o at run
  induction run generalizing a d' with
  | zero _ _ _ ih =>
    obtain ⟨x, y, a', rfl, h1, -⟩ := hQ.branch ha
    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (ih h1 ho))
  | succ _ _ _ _ _ ih =>
    obtain ⟨x, y, a', rfl, -, h2⟩ := hQ.branch ha
    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (ih h2 ho))
  | toZero _ _ _ ih =>
    obtain ⟨x, y, a', e, rfl, -, -, h1⟩ := hQ.branchTo ha
    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (ih h1 ho))
  | toSucc _ _ _ hk _ _ ih =>
    obtain ⟨x, y, a', e, rfl, he, hc, -⟩ := hQ.branchTo ha
    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (ret_mem_of_gotoCompat hc (ih (hQ.entry he hk) ho)))
  | last _ => cases ho
  | next _ _ ih =>
    obtain ⟨a', habs, h1⟩ := hQ.next ha
    exact Cursor.ret_mem_of_absNinst habs (ih h1 ho)
  | dest _ _ ih => exact ih (hQ.dest ha) ho
  | jump _ hk _ _ ih =>
    obtain ⟨x, a', e, rfl, he, hc⟩ := hQ.jump ha
    exact List.mem_cons_of_mem _ (ret_mem_of_gotoCompat hc (ih (hQ.entry he hk) ho))
  | ret _ _ =>
    obtain ⟨a', rfl⟩ := hQ.ret ha
    exact List.mem_cons_self
  | callHalt _ _ _ _ _ => cases ho
  | callRet _ hk _ _ _ ihRun ihTail =>
    obtain ⟨x, a', e, rfl, he, hcont⟩ := hQ.callNext ha
    cases hidx : e.frame.findIdx? (· == .ret) with
    | none =>
      exact absurd (ihRun (hQ.entry he hk) rfl) (ret_not_mem_of_findIdx_none hidx _ · rfl)
    | some i =>
      exact List.mem_cons_of_mem _ (ret_mem_of_cont (ihTail (hcont i hidx) ho))
  | pcAt _ _ _ ih =>
    have := ih (hQ.pcAt ha) ho
    simpa only [List.mem_cons, reduceCtorEq, false_or] using this

/-- **A callee whose declared frame holds no return marker never returns.** -/
theorem SFunc.RunP.not_returned_of_noRet {es : List Entry} {Q : List AVal → SFunc → Prop}
    {P : Sevm → Devm → Ninst → Devm → Prop} {fs : List SFunc} {sevm : Sevm}
    (hQ : RetClosed es fs Q) {k : Nat} {e : Entry} {g : SFunc} (he : es[k]? = some e)
    (hg : fs[k]? = some g) (hidx : e.frame.findIdx? (· == .ret) = none) {d d' : Devm}
    (run : SFunc.RunP P fs sevm d g (.returned d')) : False :=
  ret_not_mem_of_findIdx_none hidx _ (run.ret_mem hQ (hQ.entry he hg)) rfl

end Blanc.Lift
