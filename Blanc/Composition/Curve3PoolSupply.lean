import Blanc.Composition.Curve3PoolSupplyStep
import Blanc.Composition.Curve3Pool3CrvCheckpoint
import Blanc.Composition.PairTokenJointWalk
import Blanc.Lift.Curve3Pool.History
import Blanc.ExecutionHistoryFrameTime

/-!
# The pool and 3Crv over one configured history: minter persistence and the supply identity (U8c)

`pool_3crv_history`: over one configured history from a joint checkpoint (`JointCheckpoint`: the
pool's token is 3Crv, 3Crv's minter is the pool), with the pool history's premises
(`PoolTraceEnv`, whose callback premise makes every coin child keep 3Crv's storage: decision R1,
option B) and 3Crv's collision premise, the pool history's conclusion holds and

* 3Crv's model replays exactly its committed invocations to a state `cs` its future storage
  abstracts (`c3crv_history_committed_derived`);
* **minter persistence**: `cs.minter = pool`;
* **supply identity**: `cs.totalSupply + poolBurned = cs₀.totalSupply + poolMinted`, where
  `poolMinted`/`poolBurned` sum the `mint`/`burn` amounts of the model calls the pool invocations'
  replayed steps emit (word values, as 3Crv receives them);
* **per invocation**: 3Crv's supply word at the invocation frame's post is its supply word at the
  frame's entry plus the invocation's own minted amounts minus its burned amounts.

The proof is a positional walk over the settled frames in the shape of the sibling's pair walk
(`PairTokenJointWalk.lean`, whose `PairClosed` prefixes and first-observation split it reuses):
between two outermost pool invocations lies a *gap* holding no non-static pool frame, where no 3Crv
invocation is sent by the pool (`gap_callers`), so supply and minter are kept
(`SupplyFacet.run_keep`); each invocation's committed subtree moves the supply by its own token
calls (`pool_frame_supply`, net-zero across coin children).  The invocation's token is 3Crv because
it entered at a `Checkpoint` of the replayed pool state (`PoolEntries`).
-/

namespace Blanc.Composition.Curve3PoolSupply

open Jaune Blanc Blanc.Lift Blanc.Lift.Token Blanc.Lift.Curve3Crv Blanc.ExecutionTrace
  Blanc.ExecutionAccountingReplay Blanc.Composition.Curve3CrvToken
open Blanc.Curve3Crv (Call)
open Blanc.Lift.Curve3Pool (PoolInvocation PoolRun PoolEntries poolFrameObs poolSubtreeFrames)

/-! ## Pool-side sums and per-invocation statements -/

/-- The amounts the replayed pool steps mint, read off their model calls. -/
def poolMinted : Curve3Pool.State → List PoolInvocation → Nat
  | _, [] => 0
  | s, i :: rest =>
    match Curve3Pool.step s i.env (Curve3Pool.decodeCall i.frame.sevm) with
    | some o => callsMinted o.calls + poolMinted o.state rest
    | none => 0

/-- The amounts the replayed pool steps burn, read off their model calls. -/
def poolBurned : Curve3Pool.State → List PoolInvocation → Nat
  | _, [] => 0
  | s, i :: rest =>
    match Curve3Pool.step s i.env (Curve3Pool.decodeCall i.frame.sevm) with
    | some o => callsBurned o.calls + poolBurned o.state rest
    | none => 0

/-- 3Crv's supply word in a world. -/
def supplyAt (ca : Adr) (w : Jaune.State) : Nat := ((w.getStor ca).get vySupplySlot).toNat

/-- Each replayed invocation moves 3Crv's supply word from its frame's entry to its frame's post by
its own minted and burned amounts. -/
def StepSupplies (ca : Adr) : Curve3Pool.State → List PoolInvocation → Prop
  | _, [] => True
  | s, i :: rest => ∀ o, Curve3Pool.step s i.env (Curve3Pool.decodeCall i.frame.sevm) = some o →
      supplyAt ca i.frame.post.state + callsBurned o.calls =
        supplyAt ca i.frame.pre.state + callsMinted o.calls ∧ StepSupplies ca o.state rest

theorem StepSupplies.split {ca : Adr} :
    ∀ {s m : Curve3Pool.State} {pre : List PoolInvocation} {i : PoolInvocation}
      {post : List PoolInvocation}, StepSupplies ca s (pre ++ i :: post) → PoolRun s pre m →
      ∀ o, Curve3Pool.step m i.env (Curve3Pool.decodeCall i.frame.sevm) = some o →
        supplyAt ca i.frame.post.state + callsBurned o.calls =
          supplyAt ca i.frame.pre.state + callsMinted o.calls
  | _, _, [], _, _, h, hp => by
    simp only [PoolRun] at hp
    subst hp
    exact fun o ho => (h o ho).1
  | _, _, _ :: _, _, _, h, hp => by
    obtain ⟨o, hstep, -, rest⟩ := hp
    exact StepSupplies.split (h o hstep).2 rest

/-! ## Trace facts -/

/-- A settled frame came from a raw frame of the history. -/
theorem settled_mem_rawFrames {cfg : ChainConfig} {checkpoint future : BlockChain}
    (trace : ConfiguredHistoryTrace cfg checkpoint future) :
    ∀ f ∈ trace.settledFrames, Blanc.Exec.Frame.rootDeriv f ∈ trace.rawFrames := by
  induction trace with
  | refl => intro f member; cases member
  | step prior block ih =>
    intro f member
    simp only [ConfiguredHistoryTrace.settledFrames, ConfiguredHistoryTrace.rawFrames,
      List.mem_append] at member ⊢
    rcases member with member | member
    · exact Or.inl (ih f member)
    · exact Or.inr (block.mem_rawFrames_of_settled f member)

/-- A derivation entry condition at a frame starting at pc `0` holds of the frame's derivation. -/
theorem derivEntry_frame {Q : Exec.Deriv → Prop} {f : Exec.Frame} (hpc : f.pc = 0)
    (h : Exec.derivEntry Q f.sevm f.pre) : Q (Blanc.Exec.Frame.rootDeriv f) := by
  obtain ⟨pc, sevm, pre, out, run, committed⟩ := f
  dsimp only at hpc h ⊢
  subst hpc
  exact h out run

theorem adrOf_toNat (a : Adr) : Curve3Pool.adrOf a.toNat = a := by
  have h := toAdr_toNat a
  obtain ⟨hi, lo⟩ := a
  simp only [Nat.toAdr, Adr.toNat] at h
  simp only [Curve3Pool.adrOf, Nat.toB256, B256.toAdr, Adr.toNat]
  conv => rhs; rw [← h]
  simp only [Nat.toB128]
  congr 1
  exact UInt64.toUInt32_ofNat' _

/-- **3Crv's view replay to the entry of a settled frame** no earlier non-static 3Crv frame
encloses. -/
theorem view_at {ca : Adr} {cfg : ChainConfig} {checkpoint future : BlockChain}
    {initial : Blanc.Curve3Crv.State} {initialKeys : Key → Prop}
    (trace : ConfiguredHistoryTrace cfg checkpoint future)
    (installed : some (checkpoint.state.getCode ca).toList = c3crvSem.image)
    (invariant : VyInv (checkpoint.state.getStor ca) initial initialKeys)
    (fresh : FreshKeys initialKeys (historyTouchedKeys ca trace))
    {before : List Exec.Frame} {f : Exec.Frame} {after : List Exec.Frame}
    (split : trace.settledFrames = before ++ f :: after)
    (noOpaque : ∀ A ∈ before, A.Encloses f →
      ¬ (A.sevm.currentTarget = ca ∧ A.sevm.isStatic = false)) :
    ViewReplay (historyKeyUniverse ca trace initialKeys) (viewOf (checkpoint.state.getStor ca))
      (before.flatMap (viewFrameObs ca)) (viewOf (f.pre.state.getStor ca)) := by
  let U := historyKeyUniverse ca trace initialKeys
  have topology : VyInv (checkpoint.state.getStor ca) initial U := invariant.extend fresh
  have touched : trace.FrameAdmitted ca
      (fun sevm _ => ∀ k ∈ callKeys sevm.caller (decodeCall sevm), U k) := by
    apply (trace.frameAdmitted_iff_rawFrames ca _).2
    intro root member target k hk
    exact Or.inr (touchedKeys_mem member target hk)
  have admitted : trace.FrameAdmitted ca (carriedFrameEntry U) :=
    (trace.freshFrameAdmitted ca).and (trace.frameAdmitted_calldata.and touched)
  have start : (curveSpec U).StateInv ca checkpoint.state :=
    ⟨installed, trivial, ⟨initial, initialKeys, fun _ hk => Or.inl hk, invariant⟩⟩
  obtain ⟨steps, replay, observed⟩ :=
    (c3crvPositionalLadder ca U topology.inj topology.apart).configuredHistory_at trace admitted
      start before f after split noOpaque
  change ViewReplay U (viewOf (checkpoint.state.getStor ca)) steps
    (viewOf (f.pre.state.getStor ca)) at replay
  change steps = before.flatMap (viewFrameObs ca) at observed
  subst observed
  exact replay

/-- **3Crv's view replay to the end of the history.** -/
theorem view_end {ca : Adr} {cfg : ChainConfig} {checkpoint future : BlockChain}
    {initial : Blanc.Curve3Crv.State} {initialKeys : Key → Prop}
    (trace : ConfiguredHistoryTrace cfg checkpoint future)
    (installed : some (checkpoint.state.getCode ca).toList = c3crvSem.image)
    (invariant : VyInv (checkpoint.state.getStor ca) initial initialKeys)
    (fresh : FreshKeys initialKeys (historyTouchedKeys ca trace)) :
    ViewReplay (historyKeyUniverse ca trace initialKeys) (viewOf (checkpoint.state.getStor ca))
      (trace.settledFrames.flatMap (viewFrameObs ca)) (viewOf (future.state.getStor ca)) := by
  let U := historyKeyUniverse ca trace initialKeys
  have topology : VyInv (checkpoint.state.getStor ca) initial U := invariant.extend fresh
  have touched : trace.FrameAdmitted ca
      (fun sevm _ => ∀ k ∈ callKeys sevm.caller (decodeCall sevm), U k) := by
    apply (trace.frameAdmitted_iff_rawFrames ca _).2
    intro root member target k hk
    exact Or.inr (touchedKeys_mem member target hk)
  have admitted : trace.FrameAdmitted ca (carriedFrameEntry U) :=
    (trace.freshFrameAdmitted ca).and (trace.frameAdmitted_calldata.and touched)
  have start : (curveSpec U).StateInv ca checkpoint.state :=
    ⟨installed, trivial, ⟨initial, initialKeys, fun _ hk => Or.inl hk, invariant⟩⟩
  obtain ⟨steps, replay, observed⟩ :=
    (c3crvPositionalLadder ca U topology.inj topology.apart).toAccountingLadderAdmitted.configuredHistory
      trace admitted start
  change ViewReplay U (viewOf (checkpoint.state.getStor ca)) steps
    (viewOf (future.state.getStor ca)) at replay
  change steps = trace.settledFrames.flatMap (viewFrameObs ca) at observed
  subst observed
  exact replay

/-- On settled frames 3Crv's view observation is its committed writer extraction (a static frame
runs no writer). -/
theorem viewObs_eq_committed {ca : Adr} {U : Key → Prop} {cfg : ChainConfig}
    {checkpoint future : BlockChain} (trace : ConfiguredHistoryTrace cfg checkpoint future)
    (ready : ∀ f ∈ trace.settledFrames, FrameReady ca U f) :
    trace.settledFrames.flatMap (viewFrameObs ca) = committedInvocations ca trace := by
  unfold committedInvocations
  apply List.flatMap_congr
  intro f member
  unfold viewFrameObs
  split
  · rfl
  · rename_i hs
    have hs' : f.sevm.isStatic = true := by simpa only [Bool.not_eq_false] using hs
    unfold committedFrameInvocations
    split
    · rename_i sel
      exfalso
      obtain ⟨hpc, fork, at_, admitted, -⟩ := ready f member
      obtain ⟨⟨hstack, hmem⟩, hcd, -⟩ := admitted.root sel.1
      have hcode : f.sevm.code = code := c3crv_code_of_image (at_.2 sel.1).1
      obtain ⟨pc, sevm, pre, out, run, committed⟩ := f
      dsimp only at hpc hs' sel hstack hmem hcd hcode
      subst hpc
      cases out with
      | error e => simp only [Execution.commits, Bool.false_eq_true] at committed
      | ok post =>
        have := c3crv_writer_nonstatic hcode fork hcd hstack hmem run sel.2
        rw [hs'] at this
        cases this
    · rfl

/-! ## Gaps -/

theorem poolFrameObs_eq_pair (pool : Adr) : poolFrameObs pool = UniswapV2Pair.pairFrameObs pool := rfl

/-- **The pool sends no 3Crv invocation inside a gap** after a pool-closed prefix: such an
invocation's positional parent would be a non-static pool frame whose block ends inside the gap,
or a non-static 3Crv frame, whose children are static. -/
theorem gap_callers {pool ca : Adr} {U : Key → Prop} {cfg : ChainConfig}
    {checkpoint future : BlockChain} (trace : ConfiguredHistoryTrace cfg checkpoint future)
    (ready : ∀ f ∈ trace.settledFrames, FrameReady ca U f)
    (roots : ∀ R ∈ trace.settledRoots, R.sevm.caller ≠ pool)
    {pre gap post : List Exec.Frame} (split : trace.settledFrames = pre ++ gap ++ post)
    (closed : PairTokenJoint.PairClosed pool pre)
    (quiet : gap.flatMap (poolFrameObs pool) = []) :
    ∀ inv ∈ gap.flatMap (viewFrameObs ca), inv.sevm.caller ≠ pool := by
  intro inv member caller
  obtain ⟨F, inGap, obs⟩ := List.mem_flatMap.mp member
  have hF : F.sevm.isStatic = false ∧ F.sevm.currentTarget = ca ∧ inv = frameInvocation F := by
    unfold viewFrameObs committedFrameInvocations at obs
    split at obs
    · split at obs
      · rename_i hs sel
        exact ⟨by simpa only [decide_eq_true_eq] using hs, sel.1,
          List.mem_singleton.mp obs⟩
      · cases obs
    · cases obs
  obtain ⟨mutable, atCa, rfl⟩ := hF
  change F.sevm.caller = pool at caller
  obtain ⟨g₁, g₂, rfl⟩ := List.mem_iff_append.mp inGap
  have at' : trace.settledFrames = (pre ++ g₁) ++ F :: (g₂ ++ post) := by
    rw [split]
    simp only [List.append_assoc, List.cons_append]
  rcases trace.settledFrames_parent at' with root | ⟨b₁, G, b₂, hb, child, ⟨relation, static⟩,
    shorter⟩
  · exact roots F root caller
  · have settledG : G ∈ trace.settledFrames := by
      rw [at', hb]
      exact List.mem_append_left _ (List.mem_append_right _ List.mem_cons_self)
    cases mutableG : G.sevm.isStatic
    · rcases relation with callerEq | targetEq
      · have atPool : G.sevm.currentTarget = pool := callerEq.symm.trans caller
        rcases List.split_append_cons hb with ⟨m, inPre, rfl⟩ | ⟨n, -, inGap'⟩
        · have short := closed b₁ G m inPre atPool mutableG
          rw [List.length_append] at shorter
          omega
        · have inG₁ : G ∈ g₁ := by
            rw [inGap']
            exact List.mem_append_right _ List.mem_cons_self
          have obs' := PairTokenJoint.mem_pairObs (pair := pool) (fs := g₁ ++ F :: g₂)
            (List.mem_append_left _ inG₁) atPool mutableG
          rw [← poolFrameObs_eq_pair, quiet] at obs'
          cases obs'
      · have desc := c3crv_descendants_static (ready G settledG) (targetEq.symm.trans atCa) F
          (Exec.mem_descendantFrames_of_mem_childFrames G.run F child)
        rw [mutable] at desc
        cases desc
    · rw [static mutableG] at mutable
      cases mutable

/-! ## The walk -/

/-- The fixed inputs of the walk. -/
structure WalkEnv {cfg : ChainConfig} {checkpoint future : BlockChain}
    (trace : ConfiguredHistoryTrace cfg checkpoint future) (pool ca : Adr) (coins : Curve3Pool.V3)
    (cs₀ : Blanc.Curve3Crv.State) (K₀ U : Key → Prop) : Prop where
  injective : ∀ k k', U k → U k' → k.slot = k'.slot → k = k'
  apartU : ∀ k, U k → k.slot ∉ vyFixedSlots
  ready : ∀ f ∈ trace.settledFrames, FrameReady ca U f
  hK : ∀ k, K₀ k → U k
  invariant : VyInv (checkpoint.state.getStor ca) cs₀ K₀
  apart : pool ≠ ca
  roots : ∀ R ∈ trace.settledRoots, R.sevm.caller ≠ pool
  view : ∀ {before : List Exec.Frame} {f : Exec.Frame} {after : List Exec.Frame},
    trace.settledFrames = before ++ f :: after → f.sevm.isStatic = false →
    ViewReplay U (viewOf (checkpoint.state.getStor ca)) (before.flatMap (viewFrameObs ca))
      (viewOf (f.pre.state.getStor ca))
  whole : ∃ Z, runInvocations cs₀ (trace.settledFrames.flatMap (viewFrameObs ca)) = some Z
  env : Curve3Pool.PoolTraceEnv trace pool coins ca.toNat

theorem runInvocations_prefix {s t : Blanc.Curve3Crv.State} {xs ys : List WriterInvocation}
    (h : runInvocations s (xs ++ ys) = some t) : ∃ m, runInvocations s xs = some m := by
  rw [runInvocations_append] at h
  cases hm : runInvocations s xs with
  | none => rw [hm, Option.bind_none] at h; cases h
  | some m => exact ⟨m, rfl⟩

/-- 3Crv's fold reaches every prefix of the settled frames. -/
theorem WalkEnv.prefix {pool ca : Adr} {coins : Curve3Pool.V3} {cfg : ChainConfig}
    {checkpoint future : BlockChain} {cs₀ : Blanc.Curve3Crv.State} {K₀ U : Key → Prop}
    {trace : ConfiguredHistoryTrace cfg checkpoint future}
    (W : WalkEnv trace pool ca coins cs₀ K₀ U) {pre post : List Exec.Frame}
    (split : trace.settledFrames = pre ++ post) :
    ∃ m, runInvocations cs₀ (pre.flatMap (viewFrameObs ca)) = some m := by
  obtain ⟨Z, hZ⟩ := W.whole
  rw [split, List.flatMap_append] at hZ
  exact runInvocations_prefix hZ

/-- **Supply and minter are kept across a gap** after a pool-closed prefix. -/
theorem WalkEnv.gap_keep {pool ca : Adr} {coins : Curve3Pool.V3} {cfg : ChainConfig}
    {checkpoint future : BlockChain} {cs₀ : Blanc.Curve3Crv.State} {K₀ U : Key → Prop}
    {trace : ConfiguredHistoryTrace cfg checkpoint future}
    (W : WalkEnv trace pool ca coins cs₀ K₀ U) {pre gap post : List Exec.Frame}
    (split : trace.settledFrames = pre ++ gap ++ post)
    (closed : PairTokenJoint.PairClosed pool pre) (quiet : gap.flatMap (poolFrameObs pool) = [])
    {X Y : Blanc.Curve3Crv.State} (hX : runInvocations cs₀ (pre.flatMap (viewFrameObs ca)) = some X)
    (hY : runInvocations cs₀ ((pre ++ gap).flatMap (viewFrameObs ca)) = some Y)
    (minter : X.minter = pool) :
    Y.totalSupply = X.totalSupply ∧ Y.minter = X.minter := by
  rw [List.flatMap_append] at hY
  have step := runInvocations_split hY hX
  have book : c3crvBook.run X (invMessages (gap.flatMap (viewFrameObs ca))) = some Y := by
    rw [c3crvBook_run_eq _ _ (viewObs_canonical ca gap)]
    exact step
  have callers := gap_callers trace W.ready W.roots split closed quiet
  obtain ⟨hs, hm⟩ := c3crvSupply.run_keep book fun a member => by
    obtain ⟨inv, hinv, rfl⟩ := List.mem_map.mp member
    change inv.sevm.caller ≠ X.minter
    rw [minter]
    exact callers inv hinv
  change Y.totalSupply.toNat = X.totalSupply.toNat at hs
  exact ⟨B256.toNat_inj _ _ hs, hm⟩

/-- **The positional walk**: along a pool replay whose invocations observe exactly the settled run
`fs` after a pool-closed prefix `pre`, 3Crv's fold carries the minter `pool` and moves the supply by
the invocations' minted and burned amounts, and each invocation moves the supply word across its
frame by its own amounts. -/
theorem supply_walk {pool ca : Adr} {coins : Curve3Pool.V3} {cfg : ChainConfig}
    {checkpoint future : BlockChain} {cs₀ : Blanc.Curve3Crv.State} {K₀ U : Key → Prop}
    {trace : ConfiguredHistoryTrace cfg checkpoint future}
    (W : WalkEnv trace pool ca coins cs₀ K₀ U) :
    ∀ (invs : List PoolInvocation) {st st' : Curve3Pool.State} {pre fs post : List Exec.Frame}
      {X : Blanc.Curve3Crv.State},
      PoolRun st invs st' → PoolEntries st invs → (∀ i ∈ invs, i.Authentic pool) →
      invs.flatMap (fun i => poolSubtreeFrames pool i.frame) = fs.flatMap (poolFrameObs pool) →
      trace.settledFrames = pre ++ fs ++ post →
      PairTokenJoint.PairClosed pool pre → PairTokenJoint.PairClosed pool (pre ++ fs) →
      st.coins = coins → st.token = ca.toNat →
      runInvocations cs₀ (pre.flatMap (viewFrameObs ca)) = some X → X.minter = pool →
      ∃ Y, runInvocations cs₀ ((pre ++ fs).flatMap (viewFrameObs ca)) = some Y ∧ Y.minter = pool ∧
        Y.totalSupply.toNat + poolBurned st invs = X.totalSupply.toNat + poolMinted st invs ∧
        StepSupplies ca st invs := by
  intro invs
  induction invs with
  | nil =>
    intro st st' pre fs post X _ _ _ observed split closedPre _ _ _ atPre minter
    have quiet : fs.flatMap (poolFrameObs pool) = [] := observed.symm
    obtain ⟨Y, hY⟩ := W.prefix (pre := pre ++ fs) (post := post) split
    obtain ⟨hs, hm⟩ := W.gap_keep split closedPre quiet atPre hY minter
    refine ⟨Y, hY, hm.trans minter, ?_, trivial⟩
    rw [hs]
    rfl
  | cons i rest ih =>
    intro st st' pre fs post X run entries auth observed split closedPre closedAll hcoins htoken
      atPre minter
    obtain ⟨o, hstep, hraw, tail⟩ := run
    obtain ⟨hpc, -, atPool, mutable, -⟩ := auth i List.mem_cons_self
    have selfObs : poolSubtreeFrames pool i.frame =
        i.frame :: (Exec.descendantFrames i.frame.run).flatMap (poolFrameObs pool) :=
      PairTokenJoint.pairSubtreeFrames_self atPool mutable
    rw [List.flatMap_cons, selfObs, List.cons_append] at observed
    obtain ⟨gap, rest', rfl, quiet, -, -, restObs⟩ :=
      PairTokenJoint.pairFrameObs_first (pair := pool) (by
        rw [← poolFrameObs_eq_pair]; exact observed.symm)
    rw [← poolFrameObs_eq_pair] at quiet restObs
    -- the invocation's subtree is contiguous and inside `fs`
    have closedAt := closedAll (pre ++ gap) i.frame rest' (by
      simp only [List.append_assoc]) atPool mutable
    have globalSplit : trace.settledFrames = (pre ++ gap) ++ i.frame :: (rest' ++ post) := by
      rw [split]
      simp only [List.append_assoc, List.cons_append]
    obtain ⟨r, contig⟩ := trace.settledFrames_contig globalSplit
    have descPrefix : Exec.descendantFrames i.frame.run <+: rest' :=
      List.prefix_of_prefix_length_le ⟨r, contig.symm⟩ (List.prefix_append rest' post) closedAt
    obtain ⟨rest'', rfl⟩ := descPrefix
    rw [List.flatMap_append, List.append_cancel_left_eq] at restObs
    -- across the gap
    have gapSplit : trace.settledFrames = pre ++ gap ++
        (i.frame :: (Exec.descendantFrames i.frame.run ++ rest'' ++ post)) := by
      rw [globalSplit]
    obtain ⟨Xg, hXg⟩ := W.prefix (pre := pre ++ gap) (post := _) (by
      rw [gapSplit, List.append_assoc])
    obtain ⟨gapSup, gapMin⟩ := W.gap_keep gapSplit closedPre quiet atPre hXg minter
    -- the invocation's frame
    have settledP : i.frame ∈ trace.settledFrames := by
      rw [globalSplit]; exact List.mem_append_right _ List.mem_cons_self
    have raw := settled_mem_rawFrames trace i.frame settledP
    have entryCk := entries.1
    rw [atPool] at entryCk
    have abs : Curve3Pool.Abstracts (Curve3Pool.entryStor (Blanc.Exec.Frame.rootDeriv i.frame))
        st := by
      have := entryCk.abs
      rw [← atPool] at this
      exact this
    have token : Curve3Pool.tokenAdr (Blanc.Exec.Frame.rootDeriv i.frame) = ca := by
      rw [Curve3Pool.tokenAdr_eq abs, htoken, adrOf_toNat]
    have parties := W.env.parties _ raw atPool
    have calls : Curve3Pool.CallsOf (Blanc.Exec.Frame.rootDeriv i.frame) =
        o.calls.map (Curve3Pool.encodeCall i.frame.sevm.currentTarget
          (Curve3Pool.coinAdr (Blanc.Exec.Frame.rootDeriv i.frame))
          (Curve3Pool.tokenAdr (Blanc.Exec.Frame.rootDeriv i.frame))) := by
      rw [hraw.calls mutable]
      apply Curve3Pool.modelCalls_of_framed
      intro req member
      obtain ⟨call, -, rfl⟩ := List.mem_map.mp member
      have notPre : ∀ t, ¬ i.frame.sevm.benvStat.rules.isPrecomp t →
          Curve3Pool.framed (Blanc.Exec.Frame.rootDeriv i.frame) t = true := by
        intro t ht
        simp only [Curve3Pool.framed, Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true,
          decide_eq_false_iff_not]
        exact Or.inl ht
      cases call with
      | pull k _ _ =>
        apply notPre
        change ¬ i.frame.sevm.benvStat.rules.isPrecomp
          (Curve3Pool.coinAdr (Blanc.Exec.Frame.rootDeriv i.frame) k)
        rw [Curve3Pool.coinAdr_eq abs, hcoins]
        exact parties.1 k
      | push k _ _ =>
        apply notPre
        change ¬ i.frame.sevm.benvStat.rules.isPrecomp
          (Curve3Pool.coinAdr (Blanc.Exec.Frame.rootDeriv i.frame) k)
        rw [Curve3Pool.coinAdr_eq abs, hcoins]
        exact parties.1 k
      | mint _ _ =>
        apply notPre
        change ¬ i.frame.sevm.benvStat.rules.isPrecomp
          (Curve3Pool.tokenAdr (Blanc.Exec.Frame.rootDeriv i.frame))
        rw [Curve3Pool.tokenAdr_eq abs, htoken]
        exact parties.2
      | burn _ _ =>
        apply notPre
        change ¬ i.frame.sevm.benvStat.rules.isPrecomp
          (Curve3Pool.tokenAdr (Blanc.Exec.Frame.rootDeriv i.frame))
        rw [Curve3Pool.tokenAdr_eq abs, htoken]
        exact parties.2
    have keepToken : Curve3Pool.PoolCoinCallsKeepToken (Blanc.Exec.Frame.rootDeriv i.frame) :=
      (derivEntry_frame hpc
        ((trace.frameAdmitted_iff_rawFrames pool _).1 W.env.callbacks _ raw atPool)).2
    obtain ⟨X', Y', runX', runY', invX', invY', moved, kept⟩ :=
      pool_frame_supply trace W.injective W.apartU W.ready W.hK W.invariant W.apart globalSplit
        atPool (W.view globalSplit mutable) token calls keepToken
    have hX' : X' = Xg := Option.some.inj (runX'.symm.trans hXg)
    subst hX'
    -- the rest of the walk
    have restSplit : trace.settledFrames =
        ((pre ++ gap) ++ Exec.committedFrames i.frame.run) ++ rest'' ++ post := by
      rw [globalSplit, Exec.Frame.committedFrames_self]
      simp only [List.append_assoc, List.cons_append]
    have closedNext : PairTokenJoint.PairClosed pool ((pre ++ gap) ++ Exec.committedFrames i.frame.run) :=
      (closedPre.append (PairTokenJoint.PairClosed.gap (by rw [← poolFrameObs_eq_pair]; exact quiet))).append
        (PairTokenJoint.PairClosed.committed pool i.frame)
    have closedAll' : PairTokenJoint.PairClosed pool
        (((pre ++ gap) ++ Exec.committedFrames i.frame.run) ++ rest'') := by
      rw [Exec.Frame.committedFrames_self]
      simpa only [List.append_assoc, List.cons_append] using closedAll
    obtain ⟨hc', ht'⟩ := (Curve3Pool.step_keeps hstep).coins_token
    obtain ⟨Y, runY, minY, supY, steps⟩ := ih tail (entries.2 o hstep)
      (fun j member => auth j (List.mem_cons_of_mem _ member)) restObs restSplit closedNext
      closedAll' (hc'.trans hcoins) (ht'.trans htoken) runY' (kept.trans (gapMin.trans minter))
    refine ⟨Y, ?_, minY, ?_, ?_⟩
    · rw [Exec.Frame.committedFrames_self] at runY
      simpa only [List.append_assoc, List.cons_append] using runY
    · simp only [poolMinted, poolBurned, hstep]
      rw [gapSup] at moved
      omega
    · intro o' hstep'
      cases Option.some.inj (hstep.symm.trans hstep')
      refine ⟨?_, steps⟩
      unfold supplyAt
      rw [invY'.supply, invX'.supply]
      exact moved

/-! ## The headline -/

open Blanc.Composition.Curve3Pool3CrvJoint in
/-- **The pool and 3Crv over one configured history (U8c).**  From a joint checkpoint (the pool's
token is 3Crv, 3Crv's minter is the pool) with both runtimes installed, under the pool history's
premises (`PoolTraceEnv`, whose callback premise makes coin children keep 3Crv's storage),
3Crv's collision premise (`FreshKeys`, its HASH-T, inherited) and `pool ≠ systemAddress`:

* the pool history of `pool_history_committed_env` (the same invocations and replay);
* 3Crv's model replays exactly its committed invocations to `cs`, abstracting its future storage;
* **minter persistence**: `cs.minter = pool`;
* **supply identity**: 3Crv's final supply plus the pool's committed burns equals the checkpoint
  supply plus the pool's committed mints, the amounts read off the replayed steps' model calls
  (`poolMinted`, `poolBurned`; word values);
* **per invocation**: 3Crv's supply word at the invocation frame's post plus the step's own burned
  amounts equals its supply word at the frame's entry plus the step's own minted amounts. -/
theorem pool_3crv_history {pool c3 : Adr} {cfg : ChainConfig} {checkpoint future : BlockChain}
    {ps₀ : Curve3Pool.State} {cs₀ : Blanc.Curve3Crv.State} {K₀ : Key → Prop}
    (trace : ConfiguredHistoryTrace cfg checkpoint future)
    (poolInstalled : some (checkpoint.state.getCode pool).toList = Curve3Pool.poolSem.image)
    (c3Installed : some (checkpoint.state.getCode c3).toList = c3crvSem.image)
    (joint : JointCheckpoint pool c3 ps₀ cs₀ K₀ checkpoint.state)
    (fresh : FreshKeys K₀ (historyTouchedKeys c3 trace))
    (env : Curve3Pool.PoolTraceEnv trace pool ps₀.coins ps₀.token)
    (notSystem : pool ≠ systemAddress) :
    some (future.state.getCode pool).toList = Curve3Pool.poolSem.image ∧
    ∃ invs : List PoolInvocation,
      invs.flatMap (fun i => poolSubtreeFrames pool i.frame) =
        Curve3Pool.committedPoolFrames pool trace ∧
      (∀ i ∈ invs, i.Authentic pool) ∧
      ∃ s, PoolRun ps₀ invs s ∧ Curve3Pool.runPool ps₀ invs = some s ∧
        Curve3Pool.Checkpoint (future.state.getStor pool) s ∧ s.coins = ps₀.coins ∧
        s.token = ps₀.token ∧
      ∃ cs, runInvocations cs₀ (committedInvocations c3 trace) = some cs ∧
        VyInv (future.state.getStor c3) cs
          (Key.extend K₀ (invocationKeys (committedInvocations c3 trace))) ∧
        cs.minter = pool ∧
        cs.totalSupply.toNat + poolBurned ps₀ invs = cs₀.totalSupply.toNat + poolMinted ps₀ invs ∧
        ∀ (pre : List PoolInvocation) (i : PoolInvocation) (post : List PoolInvocation)
          (sᵢ : Curve3Pool.State), invs = pre ++ i :: post → PoolRun ps₀ pre sᵢ →
          ∃ o, Curve3Pool.step sᵢ i.env (Curve3Pool.decodeCall i.frame.sevm) = some o ∧
            Curve3Pool.RawEffect (Blanc.Exec.Frame.rootDeriv i.frame) i.frame.post i.env o ∧
            supplyAt c3 i.frame.post.state + callsBurned o.calls =
              supplyAt c3 i.frame.pre.state + callsMinted o.calls := by
  let U := historyKeyUniverse c3 trace K₀
  have topology : VyInv (checkpoint.state.getStor c3) cs₀ U := joint.c3.extend fresh
  have ready := settled_ready trace c3Installed joint.c3 fresh
  have poolCode := Curve3Pool.code_eq_of_toList poolInstalled
  have nonempty : Curve3Pool.code.toList ≠ [] := fun h => by
    have := Curve3Pool.code_toList_length
    rw [h] at this
    cases this
  have nondelegating : ¬ isValidDelegation Curve3Pool.code :=
    Curve3Pool.poolSem.not_delegation (show some Curve3Pool.code.toList = Curve3Pool.poolSem.image from rfl)
  have roots := trace.settledRoots_caller_ne_of_code nonempty nondelegating poolCode notSystem
  obtain ⟨Z, runZ, -⟩ := replay_run (fun _ hk => Or.inl hk) joint.c3
    (view_end trace c3Installed joint.c3 fresh)
  have W : WalkEnv trace pool c3 ps₀.coins cs₀ K₀ U :=
    { injective := topology.inj
      apartU := topology.apart
      ready := ready
      hK := fun _ hk => Or.inl hk
      invariant := joint.c3
      apart := joint.apart
      roots := roots
      view := fun split nonstatic => view_at trace c3Installed joint.c3 fresh split
        (noOpaque_of_nonstatic trace ready split nonstatic)
      whole := ⟨Z, runZ⟩
      env := joint.tokenIs ▸ env }
  obtain ⟨code, invs, obs, auth, entries, s, run, fold, hc, hcoins, htoken, -⟩ :=
    Curve3Pool.pool_history_committed_entries (Curve3Pool.poolParties_keeps ps₀.coins ps₀.token)
      (Curve3Pool.pool_frame_refines_at ps₀.coins ps₀.token) trace poolInstalled joint.poolCk
      ⟨rfl, rfl⟩
      (Curve3Pool.pool_trace_admitted trace poolInstalled env.callbacks env.parties env.idEmpty
        env.idNoAuthority env.idNoFrame env.sysInstalled env.sysNoAuthority env.sysNoFrame)
  obtain ⟨Y, runY, minY, supY, steps⟩ := supply_walk W invs run entries auth obs
    (pre := []) (post := []) (by rw [List.nil_append, List.append_nil])
    (PairTokenJoint.PairClosed.nil pool) (by
      rw [List.nil_append]; exact PairTokenJoint.settledFrames_pairClosed trace)
    rfl joint.tokenIs rfl joint.minterIs
  rw [List.nil_append, viewObs_eq_committed trace ready] at runY
  obtain ⟨-, cs, -, runCs, final, -⟩ :=
    c3crv_history_committed_derived trace c3Installed joint.c3 fresh
  have hY : Y = cs := Option.some.inj (runY.symm.trans runCs)
  subst hY
  refine ⟨code, invs, obs, auth, s, run, fold, hc, hcoins, htoken, Y, runCs, final, minY, supY, ?_⟩
  intro pre i post sᵢ split hpre
  obtain ⟨o, hstep, hraw, -⟩ := PoolRun.split (split ▸ run) hpre
  exact ⟨o, hstep, hraw, StepSupplies.split (split ▸ steps) hpre o hstep⟩

end Blanc.Composition.Curve3PoolSupply
