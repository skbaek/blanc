import Blanc.ExecutionAccountingPositionalHistory
import Blanc.ExecutionMidHistoryInFacts
import Blanc.ExecutionWholeFrameAccountingIn
import Blanc.ExecutionAccountingMidHistoryIn
import Blanc.StorageOnlySpec
import Blanc.Lift.Usdc.CodeImage

/-!
# An account's storage moves frame by frame

`FrameChain T Good a fs b`: the frames `fs` carry `T`'s storage from `a` to `b`, each entered where the
last one left it, each satisfying `Good`. `chainCarrier` is the replay carrier of that relation: a replay
over frames is claimed only when every frame is `Allowed`, so a frame outside a code's premises (say, a
deprecated token's re-entrant forward) leaves the claim vacuous rather than assumed away.

* `coinFrames T Obs fs`: the non-static frames at `T` that `Obs` selects, in order;
* `chainCarrier`, `chainView`: the carrier and its observation;
* `mid_frameChain`: over a mid history, for code whose allowed frames have no observed committed
  descendant (`quiet`), the settled frames at `T` carry its storage to the end and to the entry of every
  settled frame no earlier non-static frame at `T` encloses. A rolled-back frame is not settled, so it is
  in no chain.

This reads no value of the storage and names no contract. Laws about a frame's effect are stated
separately, on the chain's frames.
-/

namespace Blanc.Lift

open Jaune Blanc Blanc.ExecutionTrace Blanc.ExecutionAccountingReplay

/-- A storage, as the words it reads. -/
abbrev Words := B256 → B256

/-- The words of `T`'s storage in a world. -/
def wordsAt (T : Adr) (w : State) : Words := (w.getStor T).get

/-- Frames `fs` carry `T`'s storage from `a` to `b`, each entered where the last one left it. -/
def FrameChain (T : Adr) (Good : Exec.Frame → Prop) : Words → List Exec.Frame → Words → Prop
  | a, [], b => b = a
  | a, F :: fs, b => Good F ∧ wordsAt T F.pre.state = a ∧ FrameChain T Good (wordsAt T F.post.state) fs b

namespace FrameChain

variable {T : Adr} {Good : Exec.Frame → Prop}

theorem append : ∀ {a b c : Words} {xs ys : List Exec.Frame},
    FrameChain T Good a xs b → FrameChain T Good b ys c → FrameChain T Good a (xs ++ ys) c
  | _, _, _, [], _, hx, hy => by
    cases hx
    exact hy
  | _, _, _, _ :: _, _, hx, hy => ⟨hx.1, hx.2.1, append hx.2.2 hy⟩

/-- Every frame of a chain is good. -/
theorem good : ∀ {a b : Words} {xs : List Exec.Frame}, FrameChain T Good a xs b →
    ∀ F ∈ xs, Good F
  | _, _, [], _, _, h => absurd h List.not_mem_nil
  | _, _, _ :: _, hx, F, h => by
    rcases List.mem_cons.mp h with rfl | h
    · exact hx.1
    · exact good hx.2.2 F h

/-- A chain splits at any point, through the storage the second part starts from. -/
theorem split : ∀ {a c : Words} {xs ys : List Exec.Frame}, FrameChain T Good a (xs ++ ys) c →
    ∃ b, FrameChain T Good a xs b ∧ FrameChain T Good b ys c
  | a, _, [], _, h => ⟨a, rfl, h⟩
  | _, _, _ :: _, _, h => by
    obtain ⟨b, hx, hy⟩ := split h.2.2
    exact ⟨b, ⟨h.1, h.2.1, hx⟩, hy⟩

/-- **A property every frame carries holds along the chain, and a quantity moves by the frames'
amounts.** Each frame keeps `I` and moves `held` by `credit` and `debit`. -/
theorem fold {held : Words → Nat} {I : Words → Prop} {debit credit : Exec.Frame → Nat} :
    ∀ {a b : Words} {xs : List Exec.Frame}, FrameChain T Good a xs b →
      (∀ F ∈ xs, Good F → I (wordsAt T F.pre.state) → I (wordsAt T F.post.state) ∧
        held (wordsAt T F.pre.state) + credit F ≤ held (wordsAt T F.post.state) + debit F) → I a →
      I b ∧ held a + (xs.map credit).sum ≤ held b + (xs.map debit).sum
  | _, _, [], h, _, ha => by
    cases h
    simp only [List.map_nil, List.sum_nil, Nat.add_zero, Nat.le_refl, and_self, ha]
  | _, _, F :: _, h, law, ha => by
    obtain ⟨hg, rfl, rest⟩ := h
    obtain ⟨hI, hlaw⟩ := law F List.mem_cons_self hg ha
    obtain ⟨hb, hsum⟩ := fold rest (fun G hG => law G (List.mem_cons_of_mem _ hG)) hI
    refine ⟨hb, ?_⟩
    simp only [List.map_cons, List.sum_cons]
    omega

/-- A property every frame carries holds at each frame's entry and exit. -/
theorem inv_all {I : Words → Prop} :
    ∀ {a b : Words} {xs : List Exec.Frame}, FrameChain T Good a xs b →
      (∀ F ∈ xs, Good F → I (wordsAt T F.pre.state) → I (wordsAt T F.post.state)) → I a →
      ∀ F ∈ xs, I (wordsAt T F.pre.state)
  | _, _, [], _, _, _, _, h => absurd h List.not_mem_nil
  | _, _, G :: _, h, keep, ha, F, member => by
    obtain ⟨hg, rfl, rest⟩ := h
    rcases List.mem_cons.mp member with rfl | member
    · exact ha
    · exact inv_all rest (fun H hH => keep H (List.mem_cons_of_mem _ hH))
        (keep G List.mem_cons_self hg ha) F member

end FrameChain

open Classical in
/-- A frame's observation: itself, when it is a non-static frame at `T` that `Obs` selects. -/
noncomputable def coinObs (T : Adr) (Obs : Exec.Frame → Prop) (f : Exec.Frame) : List Exec.Frame :=
  if f.sevm.currentTarget = T ∧ f.sevm.isStatic = false ∧ Obs f then [f] else []

/-- The non-static frames at `T` that `Obs` selects, in order. -/
noncomputable def coinFrames (T : Adr) (Obs : Exec.Frame → Prop) (fs : List Exec.Frame) :
    List Exec.Frame :=
  fs.flatMap (coinObs T Obs)

theorem mem_coinFrames {T : Adr} {Obs : Exec.Frame → Prop} {fs : List Exec.Frame} {F : Exec.Frame} :
    F ∈ coinFrames T Obs fs ↔
      F ∈ fs ∧ F.sevm.currentTarget = T ∧ F.sevm.isStatic = false ∧ Obs F := by
  unfold coinFrames coinObs
  rw [List.mem_flatMap]
  constructor
  · rintro ⟨g, hg, hmem⟩
    split at hmem
    · rename_i h
      rw [List.mem_singleton] at hmem
      subst hmem
      exact ⟨hg, h⟩
    · exact absurd hmem List.not_mem_nil
  · rintro ⟨hF, h⟩
    refine ⟨F, hF, ?_⟩
    rw [ite_eq_left h]
    exact List.mem_singleton.mpr rfl

theorem coinFrames_append (T : Adr) (Obs : Exec.Frame → Prop) (xs ys : List Exec.Frame) :
    coinFrames T Obs (xs ++ ys) = coinFrames T Obs xs ++ coinFrames T Obs ys :=
  List.flatMap_append

/-- **The chain carrier** at `T`: the boundary is `T`'s storage; a replay over frames, claimed when
every frame is allowed, is a `FrameChain`. -/
noncomputable def chainCarrier (T : Adr) (Good Allowed : Exec.Frame → Prop) : ReplayCarrier T where
  readsStorage := true
  Snap := Words
  Step := Exec.Frame
  Tag := Unit
  Replay a xs b := (∀ F ∈ xs, Allowed F) → FrameChain T Good a xs b
  ofState w := wordsAt T w
  frameEntry _ w := wordsAt T w
  nil := fun _ _ => rfl
  silent := fun storage _ => congrArg Stor.get (storage rfl)
  credit := by
    intro _ pre post _ storage _ _
    exact ⟨[], fun _ => congrArg Stor.get storage⟩
  entry_eq_ofState := by
    intro _ _ caller_ne _ transfer sum_nof
    exact congrArg Stor.get (benvAfterTransfer_getStor_eq_of_safe transfer sum_nof
      (fun h1 _ => Or.inl (caller_ne h1)))

/-- The chain carrier's observation: the frames themselves. -/
noncomputable def chainView (T : Adr) (Obs Good Allowed : Exec.Frame → Prop) :
    ReplayObservation (chainCarrier T Good Allowed) where
  O := Exec.Frame
  obs := id
  obs_nil := rfl
  obs_append := fun _ _ => rfl
  frameObs := coinObs T Obs
  credit := by
    intro _ pre post _ storage _ _
    exact ⟨[], fun _ => congrArg Stor.get storage, rfl⟩

theorem chainCarrier_append {T : Adr} {Good Allowed : Exec.Frame → Prop} {a b c : Words}
    {xs ys : List Exec.Frame} (hx : (chainCarrier T Good Allowed).Replay a xs b)
    (hy : (chainCarrier T Good Allowed).Replay b ys c) :
    (chainCarrier T Good Allowed).Replay a (xs ++ ys) c := fun all =>
  (hx fun F h => all F (List.mem_append_left _ h)).append
    (hy fun F h => all F (List.mem_append_right _ h))

/-- A frame of code `C` entered at `pc = 0` on a fork of `F`, with code at `T` at its entry. -/
def CodeFrame (T : Adr) (F : Fork → Prop) (C : ByteArray) (f : Exec.Frame) : Prop :=
  f.pc = 0 ∧ f.sevm.code = C ∧ F f.sevm.benvStat.fork ∧ (f.pre.getCode T).toList ≠ []

/-- What `mid_frameChain` concludes: the settled frames at `T` carry its storage to the end and to
the entry of every settled frame no earlier non-static frame at `T` encloses, whenever the frames
concerned are allowed. -/
def SettledChain (T : Adr) (Obs Good Allowed : Exec.Frame → Prop) (a b : Words)
    (frames : List Exec.Frame) : Prop :=
  ((∀ F ∈ coinFrames T Obs frames, Allowed F) → FrameChain T Good a (coinFrames T Obs frames) b) ∧
    ∀ {before : List Exec.Frame} {f : Exec.Frame} {after : List Exec.Frame},
      frames = before ++ f :: after →
      Exec.NoOpaqueAbove (fun A => A.sevm.currentTarget = T ∧ A.sevm.isStatic = false) before f →
      (∀ F ∈ coinFrames T Obs before, Allowed F) →
      FrameChain T Good a (coinFrames T Obs before) (wordsAt T f.pre.state)

section Mid

variable {F : Fork → Prop} {T : Adr} {C : ByteArray} {Allowed : Exec.Frame → Prop}

/-- The whole-frame obligation of a chain: an allowed frame observes only itself. -/
theorem chain_whole (nonempty : C.size ≠ 0) (notDelegation : C.size ≠ eoaDelegatedCodeLength)
    (quiet : ∀ {sevm : Sevm} {pre post : Devm} (run : Exec 0 sevm pre (.ok post))
      (committed : Execution.commits (.ok post) = true),
      sevm.code = C → F sevm.benvStat.fork → sevm.currentTarget = T → sevm.isStatic = false →
      Allowed (Exec.Frame.ofRun run committed) →
      (Exec.descendantFrames run).flatMap (coinObs T fun _ => True) = []) :
    Exec.CoreAccounting.WholeFrameReplayIn F T (Usdc.CodeSem.ofBytes C nonempty notDelegation)
      (fun _ _ => True) (chainCarrier T (CodeFrame T F C) Allowed)
      (chainView T (fun _ => True) (CodeFrame T F C) Allowed) := by
  intro sevm pre post run committed hrun target fork installed _ _ hs
  have hframes : Exec.committedFrames run = Exec.Frame.ofRun run committed ::
      Exec.descendantFrames run := by
    simp only [Exec.committedFrames, dite_eq_left committed]
  have hobs : coinObs T (fun _ => True) (Exec.Frame.ofRun run committed) =
      [Exec.Frame.ofRun run committed] :=
    ite_eq_left ⟨target, hs, trivial⟩
  have hlist : (Exec.committedFrames run).flatMap (coinObs T fun _ => True) =
      Exec.Frame.ofRun run committed ::
        (Exec.descendantFrames run).flatMap (coinObs T fun _ => True) := by
    rw [hframes, List.flatMap_cons, hobs]
    rfl
  refine ⟨(Exec.committedFrames run).flatMap (coinObs T fun _ => True), ?_, rfl⟩
  intro all
  have all' : ∀ G ∈ (Exec.committedFrames run).flatMap (coinObs T fun _ => True), Allowed G := all
  change FrameChain T (CodeFrame T F C) (wordsAt T pre.state)
    ((Exec.committedFrames run).flatMap (coinObs T fun _ => True)) (wordsAt T post.state)
  rw [hlist] at all' ⊢
  have hnil := quiet run committed hrun fork target hs (all' _ List.mem_cons_self)
  rw [hnil]
  exact ⟨⟨rfl, hrun, fork, fun empty =>
    (Usdc.CodeSem.ofBytes C nonempty notDelegation).ne_nil
      (installed.1.symm.trans (congrArg some empty)) rfl⟩, rfl, rfl⟩

/-- **The settled frames at `T` carry its storage**, over a mid history from a state with `C`
installed at `T`, when an allowed frame of `C` has no observed committed descendant. -/
theorem mid_frameChain (hsgF : ∀ {f : Fork}, F f → (Fork.ruleSet f).stateGas = none)
    (capabilities : BodyStageCapabilities F)
    (nonempty : C.size ≠ 0) (notDelegation : C.size ≠ eoaDelegatedCodeLength)
    (K : InstalledRuntimeSafety C)
    (quiet : ∀ {sevm : Sevm} {pre post : Devm} (run : Exec 0 sevm pre (.ok post))
      (committed : Execution.commits (.ok post) = true),
      sevm.code = C → F sevm.benvStat.fork → sevm.currentTarget = T → sevm.isStatic = false →
      Allowed (Exec.Frame.ofRun run committed) →
      (Exec.descendantFrames run).flatMap (coinObs T fun _ => True) = [])
    {cfg : ChainConfig} {start : Benv} {future : BlockChain}
    (trace : MidHistoryTraceIn F cfg start future) (installed : start.state.getCode T = C) :
    SettledChain T (fun _ => True) (CodeFrame T F C) Allowed (wordsAt T start.state) (wordsAt T future.state)
      trace.settledFrames := by
  have startInv : (ContractSpecSem.ofStorageOnly (Usdc.CodeSem.ofBytes C nonempty notDelegation)
      (fun _ => True)).StateInv T start.state :=
    ⟨by rw [installed]; rfl, trivial, trivial⟩
  obtain ⟨steps, replay, observed⟩ :=
    (wholeFramePositionalLadderIn (F := F) hsgF
      (c := ContractSpecSem.ofStorageOnly (Usdc.CodeSem.ofBytes C nonempty notDelegation)
        (fun _ => True))
      (entry := fun _ _ => True)
      (chainCarrier T (CodeFrame T F C) Allowed) (chainView T (fun _ => True) (CodeFrame T F C) Allowed)
      chainCarrier_append (fun _ _ => ()) (fun _ _ => ()) (fun _ _ => rfl)
      (fun h => funext h)
      (fun f hf => ite_eq_right fun h => by rw [h.2.1] at hf; cases hf)
      (fun f hf => ite_eq_right fun h => hf h.1)
      (chain_whole nonempty notDelegation quiet)
      (fun _ _ _ _ _ _ _ _ _ => ⟨trivial, trivial⟩)).midHistoryIn trace
      ((trace.frameAdmitted_iff_rawFrames T _).2 fun _ _ _ => trivial) capabilities
      (trace.rewardCreditsFunded capabilities) startInv K rfl
  obtain ⟨⟨whole, wholeReplay, wholeObserved⟩, positional⟩ := framesCarrier_read replay observed
  refine ⟨?_, fun {before f after} split noOpaque => ?_⟩
  · change whole = _ at wholeObserved
    subst wholeObserved
    exact wholeReplay
  · obtain ⟨atSteps, atReplay, atObserved⟩ := positional before f after split noOpaque
    change atSteps = _ at atObserved
    subst atObserved
    exact atReplay

end Mid

end Blanc.Lift
