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

/-- **What the walk needs of one coin**, over the settled frames below their roots. -/
structure CoinWalk (B : CoinBook) (pool : Adr) (k : Fin 3) (frames rootList : List Exec.Frame) (a b : StorWords)
    (coins : V3) (tok : Nat) : Prop where
  ledger : Ledger B pool frames a b
  forest : frames = rootList.flatMap fun R => Exec.committedFrames R.run
  roots : ∀ R ∈ rootList, R.sevm.caller ≠ pool
  targetNe : B.T ≠ pool
  coinAt : adrOf (coins.get k) = B.T
  coinOther : ∀ j, j ≠ k → adrOf (coins.get j) ≠ B.T
  tokNe : adrOf tok ≠ B.T
  parties : ∀ f ∈ frames, f.sevm.currentTarget = pool →
    (∀ j : Fin 3, ¬ f.sevm.benvStat.rules.isPrecomp (adrOf (coins.get j))) ∧
      ¬ f.sevm.benvStat.rules.isPrecomp (adrOf tok)
  /-- A chain frame that keeps its parent's target is not the pool's call. -/
  delegate : ∀ F ∈ B.cf frames, ∀ G ∈ frames, F ∈ Exec.childFrames G.run → G.sevm.isStatic = false →
    G.sevm.currentTarget = F.sevm.currentTarget → F.sevm.caller ≠ pool
  kids : ∀ f ∈ frames, f.sevm.currentTarget = pool → f.sevm.isStatic = false → ∀ st : Curve3Pool.State,
    Curve3Pool.Checkpoint (f.pre.getStor f.sevm.currentTarget) st → st.coins = coins → st.token = tok →
    KidFacts B pool k (Exec.childFrames f.run)
  /-- What a pool frame's `balanceOf` child reads is the position there. -/
  reply : ∀ {pre rest L₁ L₂ : List Exec.Frame} {P c : Exec.Frame},
    frames = pre ++ P :: (blocks (L₁ ++ c :: L₂) ++ rest) → Exec.childFrames P.run = L₁ ++ c :: L₂ →
    P.sevm.currentTarget = pool → P.sevm.isStatic = false → c.sevm.currentTarget = B.T →
    c.sevm.data = balanceOfData pool → 32 ≤ c.post.output.length → ReadsAt B a pre L₁ (answerWord c.post.output)

/-- **At each step that moves nothing out of coin `k`, what the coin answers covers the books at the frame's entry.** -/
def RepliesCovered (T pool : Adr) (k : Fin 3) : Curve3Pool.State → List PoolInvocation → Prop
  | _, [] => True
  | s, i :: rest => ∀ o, step s i.env (decodeCall i.frame.sevm) = some o →
      (pushed k o.calls = 0 → ∀ n w, ReplyAt (Exec.Frame.rootDeriv i.frame) n T (balanceOfData pool) w →
        s.balances.get k ≤ w) ∧ RepliesCovered T pool k o.state rest

section Walk

variable {frames rootList : List Exec.Frame} {a b : StorWords} {coins : V3} {tok : Nat}

/-- A reply's position among a pool frame's children. -/
theorem CoinWalk.replyAt (W : CoinWalk B pool k frames rootList a b coins tok) {pre rest : List Exec.Frame}
    {P : Exec.Frame} (split : frames = pre ++ P :: (blocks (Exec.childFrames P.run) ++ rest))
    (at' : P.sevm.currentTarget = pool) (mutable : P.sevm.isStatic = false) {n w : Nat}
    (h : ReplyAt (Exec.Frame.rootDeriv P) n B.T (balanceOfData pool) w) :
    ReadsAt B a pre ((Exec.childFrames P.run).take n) w := by
  obtain ⟨c, hget, ht, hd, hlen, rfl⟩ := h
  have hget' : (Exec.childFrames P.run)[n]? = some c := hget
  obtain ⟨hn, hc⟩ := List.getElem?_eq_some_iff.mp hget'
  have hsplit : Exec.childFrames P.run =
      (Exec.childFrames P.run).take n ++ c :: (Exec.childFrames P.run).drop (n + 1) := by
    have e := List.take_append_drop n (Exec.childFrames P.run)
    rw [List.drop_eq_getElem_cons hn, hc] at e
    exact e.symm
  refine W.reply (rest := rest) (P := P) ?_ hsplit at' mutable ht hd hlen
  rw [← hsplit]
  exact split

/-- **The pool sends coin `T` no chain frame inside a gap.** -/
theorem CoinWalk.gap_callers (W : CoinWalk B pool k frames rootList a b coins tok) {pre gap post : List Exec.Frame}
    (split : frames = pre ++ gap ++ post) (closed : TargetClosed pool pre)
    (quiet : gap.flatMap (poolFrameObs pool) = []) : ∀ F ∈ B.cf gap, F.sevm.caller ≠ pool := by
  intro F hF
  obtain ⟨inGap, target, mutable, obs⟩ := mem_coinFrames.mp hF
  obtain ⟨g₁, g₂, rfl⟩ := List.mem_iff_append.mp inGap
  have memF : F ∈ frames := by
    rw [split]
    exact List.mem_append_left _ (List.mem_append_right _ inGap)
  have quiet₁ : g₁.flatMap (poolFrameObs pool) = [] := by
    rw [List.flatMap_append] at quiet
    exact (List.append_eq_nil_iff.mp quiet).1
  have split' : frames = pre ++ g₁ ++ F :: (g₂ ++ post) := by
    rw [split]
    simp only [List.append_assoc, List.cons_append]
  exact caller_ne_of_closed W.forest W.roots split' closed quiet₁ mutable fun G hG child mg te _ =>
    W.delegate F (mem_coinFrames.mpr ⟨memF, target, mutable, obs⟩) G hG child mg te

/-- The word a frame's caller is, read back. -/
theorem adrOf_caller (x : Adr) : adrOf x.toB256.toNat = x := by
  simp only [adrOf, toB256_toNat, toAdr_toB256]

/-- **The walk.** Along a replay whose invocations observe exactly the settled run `fs` after a pool-closed prefix, the
books stay covered. -/
theorem coin_walk (W : CoinWalk B pool k frames rootList a b coins tok) :
    ∀ (invs : List PoolInvocation) {st st' : Curve3Pool.State} {pre fs post : List Exec.Frame},
      PoolRun st invs st' → PoolEntries st invs → (∀ i ∈ invs, i.Authentic pool) →
      invs.flatMap (fun i => poolSubtreeFrames pool i.frame) = fs.flatMap (poolFrameObs pool) →
      frames = pre ++ fs ++ post → TargetClosed pool pre → TargetClosed pool (pre ++ fs) →
      st.coins = coins → st.token = tok → B.Covered a pre (st.balances.get k) →
      B.Covered a (pre ++ fs) (st'.balances.get k) ∧ RepliesCovered B.T pool k st invs := by
  intro invs
  induction invs with
  | nil =>
    intro st st' pre fs post run _ _ observed split closedPre _ _ _ cover
    have quiet : fs.flatMap (poolFrameObs pool) = [] := observed.symm
    cases run
    exact ⟨W.ledger.gap split (W.gap_callers split closedPre quiet) cover, trivial⟩
  | cons i rest ih =>
    intro st st' pre fs post run entries auth observed split closedPre closedAll hcoins htoken cover
    obtain ⟨o, hstep, hraw, tail⟩ := run
    obtain ⟨hpc, -, atPool, mutable, -⟩ := auth i List.mem_cons_self
    have selfObs : poolSubtreeFrames pool i.frame =
        i.frame :: (Exec.descendantFrames i.frame.run).flatMap (poolFrameObs pool) :=
      Blanc.Exec.Frame.subtreeAt_of_target atPool mutable
    rw [List.flatMap_cons, selfObs, List.cons_append] at observed
    obtain ⟨gap, rest', rfl, quiet, -, -, restObs⟩ := obsAt_first (pair := pool) (by
      rw [← poolFrameObs_eq_pair]; exact observed.symm)
    rw [← poolFrameObs_eq_pair] at quiet restObs
    have closedAt := closedAll (pre ++ gap) i.frame rest' (by simp only [List.append_assoc]) atPool mutable
    have globalSplit : frames = (pre ++ gap) ++ i.frame :: (rest' ++ post) := by
      rw [split]
      simp only [List.append_assoc, List.cons_append]
    obtain ⟨r, contig⟩ := (rootFrames_forest (W.forest.symm.trans globalSplit)).1
    have descPrefix : Exec.descendantFrames i.frame.run <+: rest' :=
      List.prefix_of_prefix_length_le ⟨r, contig.symm⟩ (List.prefix_append rest' post) closedAt
    obtain ⟨rest'', rfl⟩ := descPrefix
    rw [List.flatMap_append, List.append_cancel_left_eq] at restObs
    -- across the gap
    have gapSplit : frames = pre ++ gap ++ (i.frame :: (Exec.descendantFrames i.frame.run ++ rest'' ++ post)) := by
      rw [globalSplit]
    have coverGap := W.ledger.gap gapSplit (W.gap_callers gapSplit closedPre quiet) cover
    -- the invocation's frame
    have settledP : i.frame ∈ frames := by
      rw [globalSplit]
      exact List.mem_append_right _ List.mem_cons_self
    have entryCk := entries.1
    have callerP : i.frame.sevm.caller ≠ pool :=
      caller_ne_of_closed W.forest W.roots (pre := pre) (gap := gap) globalSplit closedPre quiet mutable
        fun _ _ _ _ _ hne => absurd atPool hne
    have F := W.kids _ settledP atPool mutable st entryCk hcoins htoken
    have abs : Curve3Pool.Abstracts (Curve3Pool.entryStor (Exec.Frame.rootDeriv i.frame)) st := entryCk.abs
    have coinIs : ∀ j, Curve3Pool.coinAdr (Exec.Frame.rootDeriv i.frame) j = adrOf (coins.get j) := fun j => by
      rw [Curve3Pool.coinAdr_eq abs, hcoins]
    have tokIs : Curve3Pool.tokenAdr (Exec.Frame.rootDeriv i.frame) = adrOf tok := by
      rw [Curve3Pool.tokenAdr_eq abs, htoken]
    have parties := W.parties _ settledP atPool
    have notPre : ∀ t, ¬ i.frame.sevm.benvStat.rules.isPrecomp t →
        Curve3Pool.framed (Exec.Frame.rootDeriv i.frame) t = true := by
      intro t ht
      simp only [Curve3Pool.framed, Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not]
      exact Or.inl ht
    have calls : CallsOf (Exec.Frame.rootDeriv i.frame) = o.calls.map (encodeCall pool
        (Curve3Pool.coinAdr (Exec.Frame.rootDeriv i.frame)) (Curve3Pool.tokenAdr (Exec.Frame.rootDeriv i.frame))) := by
      rw [hraw.calls mutable, ← atPool]
      apply Curve3Pool.modelCalls_of_framed
      intro req member
      obtain ⟨call, -, rfl⟩ := List.mem_map.mp member
      cases call with
      | pull j _ _ => exact notPre (Curve3Pool.coinAdr (Exec.Frame.rootDeriv i.frame) j) (by rw [coinIs]; exact parties.1 j)
      | push j _ _ => exact notPre (Curve3Pool.coinAdr (Exec.Frame.rootDeriv i.frame) j) (by rw [coinIs]; exact parties.1 j)
      | mint _ _ => exact notPre (Curve3Pool.tokenAdr (Exec.Frame.rootDeriv i.frame)) (by rw [tokIs]; exact parties.2)
      | burn _ _ => exact notPre (Curve3Pool.tokenAdr (Exec.Frame.rootDeriv i.frame)) (by rw [tokIs]; exact parties.2)
    have hsrc : adrOf i.env.caller ≠ pool := by
      rw [hraw.env.caller]
      change adrOf i.frame.sevm.caller.toB256.toNat ≠ pool
      rw [adrOf_caller]
      exact callerP
    obtain ⟨sumD, sumC⟩ := sums (B := B) (pool := pool) (k := k)
      (coin := Curve3Pool.coinAdr (Exec.Frame.rootDeriv i.frame))
      (token := Curve3Pool.tokenAdr (Exec.Frame.rootDeriv i.frame)) (by rw [coinIs]; exact W.coinAt)
      (fun j hj => by rw [coinIs]; exact W.coinOther j hj) (by rw [tokIs]; exact W.tokNe) hsrc
      (Exec.childFrames i.frame.run) o.calls F calls (fun _ _ _ m => step_pull_src hstep m)
    have flow := step_flow hstep k
    have fits : k ≠ feeIndex → pulled k o.calls < 2 ^ 256 := fun hf => by
      cases flow with
      | plain _ fits _ => exact fits
      | measured fee => exact absurd fee hf
      | read _ _ inn =>
        rw [inn]
        exact Nat.two_pow_pos _
    have descEq : Exec.descendantFrames i.frame.run = blocks (Exec.childFrames i.frame.run) :=
      descendantFrames_eq_children _
    have split2 : frames = (pre ++ gap) ++ i.frame :: (blocks (Exec.childFrames i.frame.run) ++ (rest'' ++ post)) := by
      rw [globalSplit, descEq]
      simp only [List.append_assoc]
    have notAt : B.cf [i.frame] = [] := by
      refine List.eq_nil_iff_forall_not_mem.mpr fun F' hF' => ?_
      obtain ⟨m, target, -, -⟩ := mem_coinFrames.mp hF'
      rw [List.mem_singleton] at m
      subst m
      exact W.targetNe (target.symm.trans atPool)
    have unframed : ∀ {x : Prop}, Curve3Pool.framed (Exec.Frame.rootDeriv i.frame) B.T = false → x := fun h => by
      have := notPre B.T (by rw [← W.coinAt]; exact parties.1 k)
      rw [this] at h
      cases h
    have tEq : Curve3Pool.coinAdr (Exec.Frame.rootDeriv i.frame) k = B.T := by
      rw [coinIs]
      exact W.coinAt
    have dEq : (Exec.Frame.rootDeriv i.frame).sevm.currentTarget = pool := atPool
    have readsAll : ∀ w, (i.env.coin k).balPre = some w →
        ∃ L₁ L₂, Exec.childFrames i.frame.run = L₁ ++ L₂ ∧ ReadsAt B a (pre ++ gap) L₁ w := by
      intro w hw
      rcases (hraw.env.coin k).balPre w hw with un | ⟨n, hr⟩
      · rw [tEq] at un
        exact unframed un
      · rw [tEq, dEq] at hr
        exact ⟨_, _, (List.take_append_drop n _).symm, W.replyAt split2 atPool mutable hr⟩
    have pairAll : ∀ p q, (i.env.coin k).balPre = some p → (i.env.coin k).balPost = some q →
        ∃ L₁ M L₂, Exec.childFrames i.frame.run = L₁ ++ M ++ L₂ ∧ ReadsAt B a (pre ++ gap) L₁ p ∧
          ReadsAt B a (pre ++ gap) (L₁ ++ M) q := by
      intro p q hp hq
      rcases (hraw.env.coin k).balPost q hq with un | ⟨w, n, m, hw, hlt, h₁, h₂⟩
      · rw [tEq] at un
        exact unframed un
      · cases Option.some.inj (hp.symm.trans hw)
        rw [tEq, dEq] at h₁ h₂
        have e₁ : (Exec.childFrames i.frame.run).take n ++ ((Exec.childFrames i.frame.run).take m).drop n =
            (Exec.childFrames i.frame.run).take m := by
          conv => rhs; rw [← List.take_append_drop n ((Exec.childFrames i.frame.run).take m)]
          rw [List.take_take, Nat.min_eq_left (Nat.le_of_lt hlt)]
        refine ⟨(Exec.childFrames i.frame.run).take n, ((Exec.childFrames i.frame.run).take m).drop n,
          (Exec.childFrames i.frame.run).drop m, ?_, W.replyAt split2 atPool mutable h₁, ?_⟩
        · rw [e₁, List.take_append_drop]
        · rw [e₁]
          exact W.replyAt split2 atPool mutable h₂
    have coverNext := W.ledger.invocation (k := k) (s := st) (e := i.env) (o := o) split2 notAt flow sumD
      (fun hf => sumC hf (fits hf)) readsAll pairAll rfl coverGap
    -- the rest of the walk
    have restSplit : frames = ((pre ++ gap) ++ Exec.committedFrames i.frame.run) ++ rest'' ++ post := by
      rw [globalSplit, Exec.Frame.committedFrames_self]
      simp only [List.append_assoc, List.cons_append]
    have closedNext : TargetClosed pool ((pre ++ gap) ++ Exec.committedFrames i.frame.run) :=
      (closedPre.append (TargetClosed.gap (by rw [← poolFrameObs_eq_pair]; exact quiet))).append
        (TargetClosed.committed pool i.frame)
    have closedAll' : TargetClosed pool (((pre ++ gap) ++ Exec.committedFrames i.frame.run) ++ rest'') := by
      rw [Exec.Frame.committedFrames_self]
      simpa only [List.append_assoc, List.cons_append] using closedAll
    obtain ⟨hc', ht'⟩ := (Curve3Pool.step_keeps hstep).coins_token
    have coverNext' : B.Covered a ((pre ++ gap) ++ Exec.committedFrames i.frame.run) (o.state.balances.get k) := by
      rw [Exec.Frame.committedFrames_self, descEq]
      exact coverNext
    obtain ⟨final, repliesRest⟩ := ih tail (entries.2 o hstep) (fun j member => auth j (List.mem_cons_of_mem _ member))
      restObs restSplit closedNext closedAll' (hc'.trans hcoins) (ht'.trans htoken) coverNext'
    refine ⟨?_, fun o' hstep' => ?_⟩
    · rw [Exec.Frame.committedFrames_self] at final
      simpa only [List.append_assoc, List.cons_append] using final
    · cases Option.some.inj (hstep.symm.trans hstep')
      refine ⟨fun none n w hr => ?_, repliesRest⟩
      exact W.ledger.reply_cover split2 notAt (List.take_append_drop n _).symm
        (Nat.le_zero.mp (none ▸ sumD)) (W.replyAt split2 atPool mutable hr) coverGap

end Walk

end Blanc.Composition.Curve3PoolBacked
