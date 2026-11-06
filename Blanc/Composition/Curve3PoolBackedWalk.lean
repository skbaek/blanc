import Blanc.Composition.Curve3PoolBackedLedger
import Blanc.Composition.Curve3PoolVirtualPriceFrames
import Blanc.Composition.Curve3PoolSupply

/-!
# The pool's books against one coin, along the settled frames

`caller_ne_of_closed`: a non-static frame positioned after a pool-closed prefix and pool-quiet frames is not called by
the pool, unless it is a delegate below a frame at its own target. So the pool's calls to a coin are its frames' children.

`CoinWalk` collects what the walk needs of a coin. `coin_walk` is `supply_walk`'s walk: between two outermost pool frames
the reading doesn't fall, and across one the books follow `Flow`.
-/

namespace Blanc.Composition.Curve3PoolBacked

open Jaune Blanc Blanc.Lift Blanc.ExecutionTrace
open Blanc.Lift.Curve3Pool (PoolInvocation PoolRun PoolEntries poolFrameObs poolSubtreeFrames Env Out feeIndex V3
  CallReq encodeCall ExtCall step decodeCall ReplyAt balanceOfData answerWord adrOf transferSel transferFromSel word
  children CallsOf)
open Blanc.Composition.Curve3PoolSupply (poolFrameObs_eq_pair targetClosed_of_forest descendantFrames_eq_children)

/-- **Who calls a non-static frame after a pool-closed prefix.** -/
theorem caller_ne_of_closed {pool : Adr} {frames rootList : List Exec.Frame}
    (forest : frames = rootList.flatMap fun R => Exec.committedFrames R.run)
    (roots : ∀ R ∈ rootList, R.sevm.caller ≠ pool) {pre gap post : List Exec.Frame} {F : Exec.Frame}
    (split : frames = pre ++ gap ++ F :: post) (closed : TargetClosed pool pre)
    (quiet : gap.flatMap (poolFrameObs pool) = []) (mutable : F.sevm.isStatic = false)
    (delegate : ∀ G ∈ frames, F ∈ Exec.childFrames G.run → G.sevm.isStatic = false →
      G.sevm.currentTarget = F.sevm.currentTarget → F.sevm.currentTarget ≠ pool → F.sevm.caller ≠ pool) :
    F.sevm.caller ≠ pool := by
  intro caller
  rcases (rootFrames_forest (forest.symm.trans split)).2 with root | ⟨b₁, G, b₂, hb, child, ⟨relation, static⟩, shorter⟩
  · exact roots F root caller
  · have settledG : G ∈ frames := by
      rw [split, hb]
      exact List.mem_append_left _ (List.mem_append_right _ List.mem_cons_self)
    cases mutableG : G.sevm.isStatic
    · have atPool : G.sevm.currentTarget = pool := by
        rcases relation with callerEq | targetEq
        · exact callerEq.symm.trans caller
        · by_cases hF : F.sevm.currentTarget = pool
          · exact targetEq.symm.trans hF
          · exact absurd caller (delegate G settledG child mutableG targetEq.symm hF)
      rcases List.split_append_cons hb with ⟨m, inPre, rfl⟩ | ⟨n, -, inGap⟩
      · have short := closed b₁ G m inPre atPool mutableG
        rw [List.length_append] at shorter
        omega
      · have inG : G ∈ gap := by
          rw [inGap]
          exact List.mem_append_right _ List.mem_cons_self
        have obs' := mem_flatMap_obsAt (pair := pool) (fs := gap) inG atPool mutableG
        rw [← poolFrameObs_eq_pair, quiet] at obs'
        cases obs'
    · rw [static mutableG] at mutable
      cases mutable

/-- A committed child's caller: its parent's target, or it keeps its parent's target. -/
theorem child_spawned {sevm : Sevm} {b : Devm} {out : Execution} (run : Exec 0 sevm b out) {c : Exec.Frame}
    (hc : c ∈ Exec.childFrames run) : Exec.SpawnedBy sevm c := by
  obtain ⟨N, f, rsm, pc', cevm, pp, hstep, henter, hsevm, -⟩ :=
    Exec.childFrames_spawnedAt_entry run (.refl _) c hc
  have hNs : N.sevm = sevm := Blanc.Exec.Deriv.ParentPrefix.sevm_eq pp
  obtain ⟨x, -, spawn, -⟩ := Evm.step_spawn_inv hstep
  subst hNs
  rw [Exec.SpawnedBy, hsevm]
  exact ⟨Evm.step_spawn_child_caller hstep henter, fun static =>
    (Frame.enter_run_isStatic henter).trans (Xinst.step_spawn_isStatic spawn static)⟩

variable {B : CoinBook} {pool : Adr} {k : Fin 3}

/-- What a coin's chain frames do with the pool's calls, among one pool frame's children. -/
structure KidFacts (B : CoinBook) (pool : Adr) (k : Fin 3) (kids : List Exec.Frame) : Prop where
  /-- A child's subtree holds no chain frame but the child. -/
  sub : ∀ c ∈ kids, B.cf (Exec.committedFrames c.run) =
    if c.sevm.isStatic = false ∧ c.sevm.currentTarget = B.T then [c] else []
  /-- A `transfer` takes out at most what it names. -/
  push : ∀ c ∈ kids, c.sevm.currentTarget = B.T → ∀ dst amt, c.sevm.data = transferSel ++ word dst ++ word amt →
    B.debit c.sevm ≤ amt
  /-- A `transferFrom` from someone else takes nothing out of the pool. -/
  pullOut : ∀ c ∈ kids, c.sevm.currentTarget = B.T → ∀ src amt,
    c.sevm.data = transferFromSel ++ word src ++ pool.toB256.toBytes ++ word amt → adrOf src ≠ pool → B.debit c.sevm = 0
  /-- A `transferFrom` from someone else brings in what it names, off the fee coin. -/
  pullIn : k ≠ feeIndex → ∀ c ∈ kids, c.sevm.currentTarget = B.T → ∀ src amt,
    c.sevm.data = transferFromSel ++ word src ++ pool.toB256.toBytes ++ word amt → adrOf src ≠ pool → amt < 2 ^ 256 →
    B.credit c.sevm = amt

/-- The request a child makes. -/
def reqOf (c : Exec.Frame) : Option CallReq :=
  if c.sevm.isStatic then none else some ⟨c.sevm.currentTarget, c.sevm.data, c.sevm.value⟩

theorem sums {coin : Fin 3 → Adr} {token : Adr} (hk : coin k = B.T) (hj : ∀ j, j ≠ k → coin j ≠ B.T)
    (ht : token ≠ B.T) {src₀ : Nat} (hsrc : adrOf src₀ ≠ pool) :
    ∀ (kids : List Exec.Frame) (calls : List ExtCall), KidFacts B pool k kids →
      kids.filterMap reqOf = calls.map (encodeCall pool coin token) →
      (∀ j src a, ExtCall.pull j src a ∈ calls → src = src₀) →
      B.sumDebit (B.cf (blocks kids)) ≤ pushed k calls ∧
        (k ≠ feeIndex → pulled k calls < 2 ^ 256 → pulled k calls ≤ B.sumCredit (B.cf (blocks kids)))
  | [], calls, _, h, _ => by
    cases calls with
    | nil => exact ⟨Nat.zero_le _, fun _ _ => Nat.zero_le _⟩
    | cons _ _ => cases h
  | c :: kids, calls, F, h, srcs => by
    have Ftail : KidFacts B pool k kids :=
      ⟨fun x hx => F.sub x (List.mem_cons_of_mem _ hx), fun x hx => F.push x (List.mem_cons_of_mem _ hx),
        fun x hx => F.pullOut x (List.mem_cons_of_mem _ hx),
        fun f x hx => F.pullIn f x (List.mem_cons_of_mem _ hx)⟩
    have hsub := F.sub c List.mem_cons_self
    have hblocks : B.cf (blocks (c :: kids)) = B.cf (Exec.committedFrames c.run) ++ B.cf (blocks kids) := by
      rw [show c :: kids = [c] ++ kids from rfl, blocks_append, cf_append]
      simp only [blocks, List.flatMap_cons, List.flatMap_nil, List.append_nil]
    rw [hblocks, hsub]
    rw [List.filterMap_cons] at h
    cases hs : c.sevm.isStatic with
    | true =>
      simp only [reqOf, hs, ↓reduceIte] at h
      simp only [Bool.true_eq_false, false_and, ↓reduceIte, List.nil_append]
      exact sums hk hj ht hsrc kids calls Ftail h srcs
    | false =>
      simp only [reqOf, hs, Bool.false_eq_true, ↓reduceIte] at h
      cases calls with
      | nil => cases h
      | cons x xs =>
        simp only [List.map_cons, List.cons.injEq] at h
        obtain ⟨hx, hrest⟩ := h
        have ih := sums hk hj ht hsrc kids xs Ftail hrest (fun j s a m => srcs j s a (List.mem_cons_of_mem _ m))
        have htg : c.sevm.currentTarget = (encodeCall pool coin token x).target := congrArg CallReq.target hx.symm ▸ rfl
        have hdt : c.sevm.data = (encodeCall pool coin token x).input := congrArg CallReq.input hx.symm ▸ rfl
        by_cases hT : c.sevm.currentTarget = B.T
        · simp only [hs, hT, and_self, ↓reduceIte, true_and]
          simp only [CoinBook.sumDebit, CoinBook.sumCredit, List.cons_append, List.nil_append, List.map_cons,
            List.sum_cons] at ih ⊢
          cases x with
          | pull i src a =>
            have ie : i = k := by
              by_contra ne
              exact hj i ne (htg.symm.trans hT)
            subst ie
            have s0 : adrOf src ≠ pool := by
              rw [srcs i src a List.mem_cons_self]
              exact hsrc
            have hd0 := F.pullOut c List.mem_cons_self hT src a hdt s0
            simp only [pushed, pulled, ↓reduceIte]
            refine ⟨by omega, fun f fits => ?_⟩
            rw [F.pullIn f c List.mem_cons_self hT src a hdt s0 (by omega)]
            have := ih.2 f (by omega)
            omega
          | push i dst a =>
            have ie : i = k := by
              by_contra ne
              exact hj i ne (htg.symm.trans hT)
            subst ie
            have hd := F.push c List.mem_cons_self hT dst a hdt
            simp only [pushed, pulled, ↓reduceIte]
            refine ⟨by omega, fun f fits => ?_⟩
            have := ih.2 f fits
            omega
          | mint dst a => exact absurd (htg.symm.trans hT) ht
          | burn src a => exact absurd (htg.symm.trans hT) ht
        · simp only [hs, hT, and_false, ↓reduceIte, List.nil_append]
          cases x with
          | pull i src a =>
            have ne : i ≠ k := fun e => hT (htg.trans (by rw [e]; exact hk))
            simpa only [pushed, pulled, ne, ↓reduceIte, Nat.zero_add] using ih
          | push i dst a =>
            have ne : i ≠ k := fun e => hT (htg.trans (by rw [e]; exact hk))
            simpa only [pushed, pulled, ne, ↓reduceIte, Nat.zero_add] using ih
          | mint dst a => simpa only [pushed, pulled] using ih
          | burn src a => simpa only [pushed, pulled] using ih

end Blanc.Composition.Curve3PoolBacked
