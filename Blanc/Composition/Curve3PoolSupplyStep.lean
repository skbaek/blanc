import Blanc.Composition.Curve3PoolSupplyFrames
import Blanc.Composition.Curve3PoolSupplyCalls
import Blanc.Lift.Curve3Pool.FrameEnv

/-!
# One pool frame moves 3Crv's supply by exactly its own mint and burn calls (U8c, R1 option B)

`pool_frame_supply`: a settled non-static pool frame `P` whose token is 3Crv, whose state-changing
calls are the encoded model calls `o.calls` (`RawEffect.calls`) and whose coin children keep 3Crv's
storage (`PoolCoinCallsKeepToken`) takes 3Crv's model fold from the state at its entry to the state
at its post with the supply moved by `callsMinted o.calls - callsBurned o.calls` and the minter
kept.  The proof walks `P`'s committed children in order, with 3Crv's positional replay inside `P`
(`frame_positional`) at each child's entry and the core replay across it (`frame_core`):

* a static child observes nothing;
* a non-static child at 3Crv is one of `P`'s token calls: a single model step whose supply move is
  the facet's, read off its calldata (`encode_decoded`), keeping the minter (never `setMinter`);
* a non-static child elsewhere is a coin call; it keeps 3Crv's storage, so the fold states at its
  entry and post read the same supply and minter (**net-zero**: whatever runs inside it, including
  re-entered pool frames, cancels out).

No enclosing non-static 3Crv frame precedes a child inside `P`: an earlier frame of `P` that
enclosed it would sit at least as deep as its earlier sibling (`descendantFrames_depth_lt`,
`childFrames_depth`).
-/

namespace Blanc.Composition.Curve3PoolSupply

open Jaune Blanc Blanc.Lift Blanc.Lift.Token Blanc.Lift.Curve3Crv Blanc.ExecutionTrace
  Blanc.ExecutionAccountingReplay Blanc.Composition.Curve3CrvToken
open Blanc.Curve3Crv (Call)

/-! ## Folds -/

theorem runInvocations_append :
    ∀ (s : Blanc.Curve3Crv.State) (xs ys : List WriterInvocation),
      runInvocations s (xs ++ ys) = (runInvocations s xs).bind fun m => runInvocations m ys
  | s, [], ys => rfl
  | s, inv :: rest, ys => by
    simp only [List.cons_append, runInvocations]
    split
    · exact runInvocations_append _ rest ys
    · rfl

theorem runInvocations_split {s m t : Blanc.Curve3Crv.State} {xs ys : List WriterInvocation}
    (h : runInvocations s (xs ++ ys) = some t) (hm : runInvocations s xs = some m) :
    runInvocations m ys = some t := by
  rw [runInvocations_append, hm, Option.bind_some] at h
  exact h

/-- A 3Crv view replay from the checkpoint is a model fold from its state. -/
theorem replay_run {U K₀ : Key → Prop} {cs₀ : Blanc.Curve3Crv.State} {σ₀ σ : Stor}
    {L : List WriterInvocation} (hK : ∀ k, K₀ k → U k) (invariant : VyInv σ₀ cs₀ K₀)
    (r : ViewReplay U (viewOf σ₀) L (viewOf σ)) :
    ∃ s, runInvocations cs₀ L = some s ∧ VyInv σ s (Key.extend K₀ (invocationKeys L)) := by
  obtain ⟨s, run, final⟩ := (r _ _ rfl rfl).2 cs₀ K₀ hK invariant
  exact ⟨s, run.runInvocations_eq, final⟩

/-- Two abstractions of storages with the same words have the same supply and minter. -/
theorem vyInv_same {σ σ' : Stor} {s s' : Blanc.Curve3Crv.State} {K K' : Key → Prop}
    (h : VyInv σ s K) (h' : VyInv σ' s' K') (same : ∀ x, σ'.get x = σ.get x) :
    s'.totalSupply = s.totalSupply ∧ s'.minter = s.minter := by
  refine ⟨by rw [← h'.supply, same, h.supply], Adr.toB256_inj ?_⟩
  rw [← h'.minter, same, h.minter]

/-- Every observed invocation records its canonical owner word and runs a writer. -/
theorem viewObs_canonical (ca : Adr) (fs : List Exec.Frame) :
    ∀ inv ∈ fs.flatMap (viewFrameObs ca),
      inv.ownerWord = ownerWordOf inv.sevm ∧ IsWriter (decodeCall inv.sevm) := by
  intro inv member
  obtain ⟨f, -, h⟩ := List.mem_flatMap.mp member
  unfold viewFrameObs committedFrameInvocations at h
  split at h
  · split at h
    · rename_i sel
      rw [List.mem_singleton] at h
      subst h
      exact ⟨rfl, sel.2⟩
    · cases h
  · cases h

/-! ## The token calls of a frame -/

/-- A frame is one of the token calls: non-static, at `ca`. -/
def isTok (ca : Adr) (c : Exec.Frame) : Bool := decide (c.sevm.isStatic = false ∧ c.sevm.currentTarget = ca)

/-- The token calls' messages among frames. -/
def tokMsgs (ca : Adr) (cs : List Exec.Frame) : List Sevm := (cs.filter (isTok ca)).map (·.sevm)

theorem tokMsgs_data (ca : Adr) :
    ∀ cs : List Exec.Frame, (tokMsgs ca cs).map (·.data) =
      ((cs.filterMap fun c => if c.sevm.isStatic then none else
          some (⟨c.sevm.currentTarget, c.sevm.data, c.sevm.value⟩ : Curve3Pool.CallReq)).filter
        (fun r => decide (r.target = ca))).map (·.input)
  | [] => rfl
  | c :: cs => by
    have ih := tokMsgs_data ca cs
    unfold tokMsgs at ih ⊢
    cases hs : c.sevm.isStatic <;> by_cases ht : c.sevm.currentTarget = ca <;>
      simp only [List.filter_cons, List.filterMap_cons, isTok, hs, ht, Bool.false_eq_true,
        ↓reduceIte, decide_true, decide_false, and_self, and_true, and_false, List.map_cons,
        Option.some.injEq, Bool.true_eq_false, false_and, ih]

/-- The encoded calls at the token mint and burn exactly the model calls' amounts. -/
theorem encoded_minted_burned (pool token : Adr) (coin : Fin 3 → Adr) :
    ∀ calls : List Curve3Pool.ExtCall,
      ((((calls.map (Curve3Pool.encodeCall pool coin token)).filter
          (fun r => decide (r.target = token))).map (·.input)).map msgMinted).sum = callsMinted calls ∧
      ((((calls.map (Curve3Pool.encodeCall pool coin token)).filter
          (fun r => decide (r.target = token))).map (·.input)).map msgBurned).sum = callsBurned calls
  | [] => ⟨rfl, rfl⟩
  | c :: cs => by
    obtain ⟨ihm, ihb⟩ := encoded_minted_burned pool token coin cs
    obtain ⟨hm, hb, -⟩ := encode_decoded pool coin token c
    unfold callsMinted at ihm ⊢
    unfold callsBurned at ihb ⊢
    by_cases ht : (Curve3Pool.encodeCall pool coin token c).target = token
    · simp only [List.map_cons, List.filter_cons, ht, decide_true, ↓reduceIte, List.sum_cons, hm,
        hb, ihm, ihb, and_self]
    · have h0 : callMinted c = 0 ∧ callBurned c = 0 := by
        cases c with
        | pull => exact ⟨rfl, rfl⟩
        | push => exact ⟨rfl, rfl⟩
        | mint => exact absurd rfl ht
        | burn => exact absurd rfl ht
      simp only [List.map_cons, List.filter_cons, ht, decide_false, Bool.false_eq_true,
        ↓reduceIte, List.sum_cons, h0.1, h0.2, Nat.zero_add, ihm, ihb, and_self]

/-! ## One pool frame -/

/-- **One pool frame moves 3Crv's supply by its own mint and burn calls.** -/
theorem pool_frame_supply {pool ca : Adr} {cfg : ChainConfig} {checkpoint future : BlockChain}
    {cs₀ : Blanc.Curve3Crv.State} {U K₀ : Key → Prop}
    (trace : ConfiguredHistoryTrace cfg checkpoint future)
    (injective : ∀ k k', U k → U k' → k.slot = k'.slot → k = k')
    (apartU : ∀ k, U k → k.slot ∉ vyFixedSlots)
    (ready : ∀ f ∈ trace.settledFrames, FrameReady ca U f)
    (hK : ∀ k, K₀ k → U k) (invariant : VyInv (checkpoint.state.getStor ca) cs₀ K₀)
    (apart : pool ≠ ca)
    {before after : List Exec.Frame} {P : Exec.Frame}
    (split : trace.settledFrames = before ++ P :: after)
    (target : P.sevm.currentTarget = pool)
    (entry : ViewReplay U (viewOf (checkpoint.state.getStor ca))
      (before.flatMap (viewFrameObs ca)) (viewOf (P.pre.state.getStor ca)))
    {o : Curve3Pool.Out}
    (token : Curve3Pool.tokenAdr (Blanc.Exec.Frame.rootDeriv P) = ca)
    (calls : Curve3Pool.CallsOf (Blanc.Exec.Frame.rootDeriv P) =
      o.calls.map (Curve3Pool.encodeCall P.sevm.currentTarget
        (Curve3Pool.coinAdr (Blanc.Exec.Frame.rootDeriv P))
        (Curve3Pool.tokenAdr (Blanc.Exec.Frame.rootDeriv P))))
    (keepToken : Curve3Pool.PoolCoinCallsKeepToken (Blanc.Exec.Frame.rootDeriv P)) :
    ∃ X Y, runInvocations cs₀ (before.flatMap (viewFrameObs ca)) = some X ∧
      runInvocations cs₀ ((before ++ Exec.committedFrames P.run).flatMap (viewFrameObs ca)) =
        some Y ∧
      VyInv (P.pre.state.getStor ca) X
        (Key.extend K₀ (invocationKeys (before.flatMap (viewFrameObs ca)))) ∧
      VyInv (P.post.state.getStor ca) Y
        (Key.extend K₀ (invocationKeys
          ((before ++ Exec.committedFrames P.run).flatMap (viewFrameObs ca)))) ∧
      Y.totalSupply.toNat + callsBurned o.calls = X.totalSupply.toNat + callsMinted o.calls ∧
      Y.minter = X.minter := by
  let D := Blanc.Exec.Frame.rootDeriv P
  let cs := Exec.childFrames P.run
  let g : Exec.Frame → List WriterInvocation := fun c =>
    (Exec.committedFrames c.run).flatMap (viewFrameObs ca)
  let L₀ := before.flatMap (viewFrameObs ca)
  have hcf : Exec.committedFrames P.run =
      P :: cs.flatMap fun c => Exec.committedFrames c.run := by
    rw [Exec.Frame.committedFrames_self, descendantFrames_eq_children]
  have obP : viewFrameObs ca P = [] := viewFrameObs_foreign (by rw [target]; exact apart)
  have hobs : (Exec.committedFrames P.run).flatMap (viewFrameObs ca) = cs.flatMap g := by
    rw [hcf, List.flatMap_cons, obP, List.nil_append, List.flatMap_assoc]
  have settledP : P ∈ trace.settledFrames := by
    rw [split]; exact List.mem_append_right _ List.mem_cons_self
  obtain ⟨r, contig⟩ := trace.settledFrames_contig split
  have childSettled : ∀ c ∈ cs, c ∈ trace.settledFrames := by
    intro c member
    rw [split, contig]
    exact List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_append_left _
      (Exec.mem_descendantFrames_of_mem_childFrames P.run c member)))
  have readyP := ready P settledP
  obtain ⟨X, runX, invX⟩ := replay_run hK invariant entry
  -- the children, in order
  have walk : ∀ ys xs : List Exec.Frame, cs = xs ++ ys →
      (∃ Xn, runInvocations cs₀ (L₀ ++ xs.flatMap g) = some Xn ∧
        Xn.totalSupply.toNat + c3crvSupply.burned (tokMsgs ca xs) =
          X.totalSupply.toNat + c3crvSupply.minted (tokMsgs ca xs) ∧ Xn.minter = X.minter) →
      ∃ Xn, runInvocations cs₀ (L₀ ++ cs.flatMap g) = some Xn ∧
        Xn.totalSupply.toNat + c3crvSupply.burned (tokMsgs ca cs) =
          X.totalSupply.toNat + c3crvSupply.minted (tokMsgs ca cs) ∧ Xn.minter = X.minter := by
    intro ys
    induction ys with
    | nil =>
      intro xs hxs claim
      rw [List.append_nil] at hxs
      rw [hxs]
      exact claim
    | cons c ys ih =>
      intro xs hxs claim
      apply ih (xs ++ [c]) (by rw [hxs, List.append_assoc, List.singleton_append])
      obtain ⟨Xn, runXn, supXn, minXn⟩ := claim
      have memc : c ∈ cs := by rw [hxs]; exact List.mem_append_right _ List.mem_cons_self
      -- 3Crv at the child's entry, inside `P`
      have localSplit : Exec.committedFrames P.run =
          (P :: xs.flatMap fun c => Exec.committedFrames c.run) ++
            c :: (Exec.descendantFrames c.run ++ ys.flatMap fun c => Exec.committedFrames c.run) := by
        rw [hcf]
        change P :: (Exec.childFrames P.run).flatMap _ = _
        rw [show Exec.childFrames P.run = xs ++ c :: ys from hxs, List.flatMap_append,
          List.flatMap_cons, Exec.Frame.committedFrames_self]
        simp only [List.cons_append, List.append_assoc]
      have noOpaque : ∀ A ∈ P :: xs.flatMap (fun c => Exec.committedFrames c.run), A.Encloses c →
          ¬ (A.sevm.currentTarget = ca ∧ A.sevm.isStatic = false) := by
        rintro A member encloses ⟨tA, -⟩
        rcases List.mem_cons.mp member with rfl | inXs
        · exact apart (target.symm.trans tA)
        · obtain ⟨c', memc', inC'⟩ := List.mem_flatMap.mp inXs
          have deeper := descendantFrames_depth_lt A.run c encloses
          have hA : A.sevm.depth ≤ c'.sevm.depth := by
            rcases Exec.Frame.mem_committedFrames.mp inC' with rfl | below
            · exact Nat.le_refl _
            · exact Nat.le_of_lt (descendantFrames_depth_lt c'.run A below)
          have dc := childFrames_depth P.run c memc
          have dc' := childFrames_depth P.run c' (by
            rw [show Exec.childFrames P.run = xs ++ c :: ys from hxs]
            exact List.mem_append_left _ memc')
          omega
      have posR := frame_positional injective apartU readyP localSplit noOpaque
      have hpos : (P :: xs.flatMap fun c => Exec.committedFrames c.run).flatMap (viewFrameObs ca) =
          xs.flatMap g := by
        rw [List.flatMap_cons, obP, List.nil_append, List.flatMap_assoc]
      rw [hpos] at posR
      have R1 := viewReplay_append entry posR
      have readyC := ready c (childSettled c memc)
      have R2 := viewReplay_append R1 (frame_core injective apartU readyC)
      obtain ⟨Xc, runXc, invXc⟩ := replay_run hK invariant R1
      have hXc : Xc = Xn := Option.some.inj (runXc.symm.trans runXn)
      subst hXc
      obtain ⟨Y, runY, invY⟩ := replay_run hK invariant R2
      have stepY : runInvocations Xc (g c) = some Y := runInvocations_split runY runXc
      have listEq : L₀ ++ (xs ++ [c]).flatMap g = L₀ ++ xs.flatMap g ++ g c := by
        rw [List.flatMap_append, List.flatMap_singleton, List.append_assoc]
      have tokEq : tokMsgs ca (xs ++ [c]) = tokMsgs ca xs ++ tokMsgs ca [c] := by
        unfold tokMsgs
        rw [List.filter_append, List.map_append]
      refine ⟨Y, by rw [listEq]; exact runY, ?_⟩
      rw [tokEq, SupplyFacet.minted_append, SupplyFacet.burned_append]
      by_cases hs : c.sevm.isStatic = true
      · -- a static child observes nothing
        have gnil : g c = [] := List.flatMap_eq_nil_iff.mpr fun D member =>
          viewFrameObs_static (committedFrames_isStatic c.run hs D member)
        rw [gnil] at stepY
        have hY : Xc = Y := Option.some.inj stepY
        subst hY
        have tnil : tokMsgs ca [c] = [] := by
          simp only [tokMsgs, isTok, List.filter_cons, hs, Bool.true_eq_false, false_and,
            decide_false, Bool.false_eq_true, ↓reduceIte, List.filter_nil, List.map_nil]
        rw [tnil]
        exact ⟨supXn, minXn⟩
      have hs' : c.sevm.isStatic = false := by simpa only [Bool.not_eq_true] using hs
      -- a non-static child is one of the encoded model calls
      have inCalls : (⟨c.sevm.currentTarget, c.sevm.data, c.sevm.value⟩ : Curve3Pool.CallReq) ∈
          Curve3Pool.CallsOf D := by
        refine List.mem_filterMap.mpr ⟨c, memc, ?_⟩
        simp only [hs', Bool.false_eq_true, ↓reduceIte]
      rw [calls] at inCalls
      obtain ⟨call, -, encEq⟩ := List.mem_map.mp inCalls
      have dataEq : c.sevm.data = (Curve3Pool.encodeCall P.sevm.currentTarget
          (Curve3Pool.coinAdr D) (Curve3Pool.tokenAdr D) call).input := by rw [encEq]
      have targetEq : c.sevm.currentTarget = (Curve3Pool.encodeCall P.sevm.currentTarget
          (Curve3Pool.coinAdr D) (Curve3Pool.tokenAdr D) call).target := by rw [encEq]
      obtain ⟨-, -, notSet⟩ := encode_decoded P.sevm.currentTarget (Curve3Pool.coinAdr D)
        (Curve3Pool.tokenAdr D) call
      by_cases ht : c.sevm.currentTarget = ca
      · -- a token call: one model step
        have tone : tokMsgs ca [c] = [c.sevm] := by
          simp only [tokMsgs, isTok, List.filter_cons, hs', ht, and_self, decide_true, ↓reduceIte,
            List.filter_nil, List.map_cons, List.map_nil]
        rw [tone]
        have desc := c3crv_descendants_static readyC ht
        have gOne : g c = viewFrameObs ca c := by
          change (Exec.committedFrames c.run).flatMap _ = _
          rw [Exec.Frame.committedFrames_self, List.flatMap_cons,
            List.flatMap_eq_nil_iff.mpr fun D member => viewFrameObs_static (desc D member),
            List.append_nil]
        rw [gOne] at stepY
        have book : c3crvBook.step Xc c.sevm = some Y := by
          by_cases hw : IsWriter (decodeCall c.sevm)
          · have one : viewFrameObs ca c = [frameInvocation c] := by
              simp only [viewFrameObs, hs', committedFrameInvocations, ht, hw, and_self,
                ↓reduceIte]
            rw [one] at stepY
            change (match Blanc.Curve3Crv.step (c3ctx c.sevm (ownerWordOf c.sevm))
              (decodeCall c.sevm) Xc with
              | .ok o => runInvocations o.1 []
              | .error _ => none) = some Y at stepY
            split at stepY
            · rename_i o' hstep
              have hY : o'.1 = Y := Option.some.inj stepY
              subst hY
              exact c3crvStep_of_ok hw hstep
            · cases stepY
          · have none : viewFrameObs ca c = [] := by
              simp only [viewFrameObs, hs', committedFrameInvocations, ht, hw, and_false,
                ↓reduceIte]
            rw [none] at stepY
            have hY : Xc = Y := Option.some.inj stepY
            subst hY
            change c3crvStep Xc c.sevm = some Xc
            unfold c3crvStep
            rw [if_neg hw]
        have keeps : c3crvSupply.KeepsMinter c.sevm := c3crv_keepsMinter fun m h =>
          notSet m (by rw [← decodeCall_congr (e := c.sevm) dataEq]; exact h)
        obtain ⟨-, moved⟩ := c3crvSupply.step_supply book
        have minY : Y.minter = Xc.minter := keeps book
        refine ⟨?_, minY.trans minXn⟩
        have m1 : c3crvSupply.minted [c.sevm] = ((c3crvSupply.mintOf c.sevm).map Prod.snd).getD 0 := by
          rw [SupplyFacet.minted_cons]; rfl
        have b1 : c3crvSupply.burned [c.sevm] = ((c3crvSupply.burnOf c.sevm).map Prod.snd).getD 0 := by
          rw [SupplyFacet.burned_cons]; rfl
        change Y.totalSupply.toNat + _ = Xc.totalSupply.toNat + _ at moved
        rw [m1, b1]
        omega
      · -- a coin call: net zero on 3Crv's storage
        have tnil : tokMsgs ca [c] = [] := by
          simp only [tokMsgs, isTok, List.filter_cons, ht, and_false, decide_false,
            Bool.false_eq_true, ↓reduceIte, List.filter_nil, List.map_nil]
        rw [tnil]
        have coin : ∃ k, c.sevm.currentTarget = Curve3Pool.coinAdr D k := by
          rw [targetEq]
          cases call with
          | pull i _ _ => exact ⟨i, rfl⟩
          | push i _ _ => exact ⟨i, rfl⟩
          | mint _ _ => exact absurd (targetEq.trans token) ht
          | burn _ _ => exact absurd (targetEq.trans token) ht
        have same := keepToken c memc coin (by rw [token]; exact ht)
        rw [token] at same
        obtain ⟨hsup, hmin⟩ := vyInv_same invXc invY same
        refine ⟨?_, hmin.trans minXn⟩
        simp only [SupplyFacet.minted, SupplyFacet.burned, List.filterMap_nil, List.map_nil,
          List.sum_nil, Nat.add_zero]
        rw [hsup]
        simpa only [SupplyFacet.minted, SupplyFacet.burned, List.filterMap_nil, List.map_nil,
          List.sum_nil, Nat.add_zero] using supXn
  obtain ⟨Xn, runXn, supXn, minXn⟩ := walk cs [] (List.nil_append cs).symm
    ⟨X, by rw [List.flatMap_nil, List.append_nil]; exact runX, rfl, rfl⟩
  -- 3Crv across `P`
  have RP := viewReplay_append entry (frame_core injective apartU readyP)
  rw [hobs] at RP
  obtain ⟨Y, runY, invY⟩ := replay_run hK invariant RP
  have hY : Y = Xn := Option.some.inj (runY.symm.trans runXn)
  subst hY
  -- the token calls are the model's token calls
  have tokData := tokMsgs_data ca cs
  change (tokMsgs ca cs).map (·.data) = ((Curve3Pool.CallsOf D).filter _).map (·.input) at tokData
  rw [calls] at tokData
  have mb := encoded_minted_burned P.sevm.currentTarget (Curve3Pool.tokenAdr D)
    (Curve3Pool.coinAdr D) o.calls
  rw [token] at tokData mb
  obtain ⟨mintEq, burnEq⟩ := mb
  rw [← tokData, List.map_map] at mintEq burnEq
  rw [minted_eq_sum, burned_eq_sum] at supXn
  refine ⟨X, Y, runX, ?_, invX, ?_, ?_, minXn⟩
  · rw [List.flatMap_append, hobs]; exact runY
  · rw [List.flatMap_append, hobs]; exact invY
  · rw [← mintEq, ← burnEq]
    exact supXn

/-! ## The supply a frame observes -/

/-- **3Crv at the entry of a pool frame's child**: some model state abstracts 3Crv's storage there
(the positional replay inside the frame, from 3Crv's replay at the frame's entry). -/
theorem child_entry_vyInv {pool ca : Adr} {cfg : ChainConfig} {checkpoint future : BlockChain}
    {cs₀ : Blanc.Curve3Crv.State} {U K₀ : Key → Prop}
    (trace : ConfiguredHistoryTrace cfg checkpoint future)
    (injective : ∀ k k', U k → U k' → k.slot = k'.slot → k = k')
    (apartU : ∀ k, U k → k.slot ∉ vyFixedSlots)
    (ready : ∀ f ∈ trace.settledFrames, FrameReady ca U f)
    (hK : ∀ k, K₀ k → U k) (invariant : VyInv (checkpoint.state.getStor ca) cs₀ K₀)
    (apart : pool ≠ ca)
    {before after : List Exec.Frame} {P : Exec.Frame}
    (split : trace.settledFrames = before ++ P :: after)
    (target : P.sevm.currentTarget = pool)
    (entry : ViewReplay U (viewOf (checkpoint.state.getStor ca))
      (before.flatMap (viewFrameObs ca)) (viewOf (P.pre.state.getStor ca))) :
    ∀ c ∈ Exec.childFrames P.run, ∃ X K, VyInv (c.pre.state.getStor ca) X K := by
  intro c memc
  obtain ⟨xs, ys, hxs⟩ := List.mem_iff_append.mp memc
  have settledP : P ∈ trace.settledFrames := by
    rw [split]; exact List.mem_append_right _ List.mem_cons_self
  have localSplit : Exec.committedFrames P.run =
      (P :: xs.flatMap fun c => Exec.committedFrames c.run) ++
        c :: (Exec.descendantFrames c.run ++ ys.flatMap fun c => Exec.committedFrames c.run) := by
    rw [Exec.Frame.committedFrames_self, descendantFrames_eq_children, hxs, List.flatMap_append,
      List.flatMap_cons, Exec.Frame.committedFrames_self]
    simp only [List.cons_append, List.append_assoc]
  have noOpaque : ∀ A ∈ P :: xs.flatMap (fun c => Exec.committedFrames c.run), A.Encloses c →
      ¬ (A.sevm.currentTarget = ca ∧ A.sevm.isStatic = false) := by
    rintro A member encloses ⟨tA, -⟩
    rcases List.mem_cons.mp member with rfl | inXs
    · exact apart (target.symm.trans tA)
    · obtain ⟨c', memc', inC'⟩ := List.mem_flatMap.mp inXs
      have deeper := descendantFrames_depth_lt A.run c encloses
      have hA : A.sevm.depth ≤ c'.sevm.depth := by
        rcases Exec.Frame.mem_committedFrames.mp inC' with rfl | below
        · exact Nat.le_refl _
        · exact Nat.le_of_lt (descendantFrames_depth_lt c'.run A below)
      have dc := childFrames_depth P.run c memc
      have dc' := childFrames_depth P.run c' (by rw [hxs]; exact List.mem_append_left _ memc')
      omega
  have posR := frame_positional injective apartU (ready P settledP) localSplit noOpaque
  obtain ⟨X, -, invX⟩ := replay_run hK invariant (viewReplay_append entry posR)
  exact ⟨X, _, invX⟩

theorem totalSupplySel_eq : Curve3Pool.totalSupplySel = abiSelectorBytes selTotalSupply := by decide

theorem decode_totalSupply {e : Sevm} (h : e.data = Curve3Pool.totalSupplyData) :
    decodeCall e = .totalSupply := by
  have hsel : Sevm.selector e = selTotalSupply :=
    selector_eq_of_data_eq_abiSelectorBytes_append (tail := []) (by decide)
      (by rw [h, List.append_nil]; exact totalSupplySel_eq)
  have hlen : ¬ e.data.length < 4 := by rw [h]; decide
  unfold decodeCall
  rw [if_neg hlen]
  simp only [hsel]
  rw [if_neg (by decide), if_neg (by decide), if_pos trivial]

/-- **3Crv's `totalSupply()` answers the supply of the state abstracting its storage.** -/
theorem totalSupply_answer {ca : Adr} {U : Key → Prop} {S : Exec.Frame}
    (ready : FrameReady ca U S) (target : S.sevm.currentTarget = ca)
    (data : S.sevm.data = Curve3Pool.totalSupplyData) {X : Blanc.Curve3Crv.State} {K : Key → Prop}
    (inv : VyInv (S.pre.state.getStor ca) X K) :
    S.post.output = X.totalSupply.toBytes := by
  obtain ⟨hpc, fork, at_, admitted, -⟩ := ready
  obtain ⟨⟨hstack, hmem⟩, hcd, -⟩ := admitted.root target
  have hcode : S.sevm.code = code := c3crv_code_of_image (at_.2 target).1
  have hdec := decode_totalSupply data
  obtain ⟨pc, sevm, pre, out, run, committed⟩ := S
  dsimp only at hpc hstack hmem hcd hcode target data hdec inv ⊢
  subst hpc
  subst target
  cases out with
  | error e => simp only [Execution.commits, Bool.false_eq_true] at committed
  | ok post =>
    have hfresh : FreshKeys K (callKeys sevm.caller (decodeCall sevm)) := by
      rw [hdec]
      exact ⟨fun k hk => absurd hk List.not_mem_nil, fun k hk => absurd hk List.not_mem_nil⟩
    have refinement := c3crv_frame_refines_raw hcode fork hcd hstack hmem inv hfresh run
    obtain ⟨-, -, o, hstep, hret⟩ := refinement.2 (by rw [hdec]; exact id)
    rw [hdec] at hstep
    obtain ⟨-, hbody⟩ := Blanc.Curve3Crv.step_eq_ok.mp hstep
    change Blanc.Curve3Crv.totalSupplyView X = .ok o at hbody
    unfold Blanc.Curve3Crv.totalSupplyView at hbody
    cases hbody
    exact hret

end Blanc.Composition.Curve3PoolSupply
