import Blanc.Lift.Curve3Crv.CarriedHistory
import Blanc.ExecutionAccountingReplay
import Blanc.ExecutionTraceSettledFrames

/-!
# The committed writer invocations of a Curve history, and their model run

Extraction is definitional and mentions no model: a settlement-retained frame at
the contract address contributes one `WriterInvocation` exactly when it executes
a writer selector. The invocation records the frame's own
message data and machines. `ownerWordOf` is the owner answer the model needs in
order to accept the call at all: `set_name` succeeds only if `owner()` answered
the caller, and every other call ignores the owner. The frame's actual static
`owner()` call is tied to that word by the `OwnerAnswer` evidence carried in each
`InvRun` step, not by choice.

No static filter is needed: a writer frame of the deployed runtime cannot succeed
in a static context at all (`c3crv_writer_nonstatic`: every writer body reaches an
`SSTORE` or a `LOG3`, which Jaune halts with `writeInStaticContext`), so every
extracted frame is non-static by the execution itself, not by the extraction.
-/

namespace Blanc.Lift.Curve3Crv

open Jaune Blanc.ExecutionAccountingReplay Blanc.ExecutionTrace
open Blanc.Curve3Crv (Call)

instance : DecidablePred IsWriter := fun call => by
  cases call <;> (unfold IsWriter; infer_instance)

/-- The owner answer the model must be given for a call to be accepted:
`set_name` needs the caller's word, every other call reads none. -/
def ownerWordOf (sevm : Sevm) : Option B256 :=
  match decodeCall sevm with
  | .setName _ _ => some sevm.caller.toB256
  | _ => none

/-- The invocation a committed frame records: its own message and machines. -/
def frameInvocation (frame : Exec.Frame) : WriterInvocation :=
  ⟨frame.sevm, frame.pre, frame.post, ownerWordOf frame.sevm⟩

/-- A settled frame contributes its invocation exactly when it runs a writer
selector at the selected address.

The `currentTarget = ca` filter is the storage owner, so frames running Curve's code at another address (e.g. entered by `DELEGATECALL` from another contract, which touch that contract's storage) are correctly excluded; the certified runtime itself only spawns `STATICCALL`, so no frame with `currentTarget = ca` runs other code. -/
def committedFrameInvocations (ca : Adr) (frame : Exec.Frame) : List WriterInvocation :=
  if frame.sevm.currentTarget = ca ∧ IsWriter (decodeCall frame.sevm) then
    [frameInvocation frame] else []

/-- Writer invocations extracted in execution order from the settlement-retained
frames of a configured history; interpreter and message settlement prune rolled-back
subtrees first. -/
def committedInvocations {cfg : ChainConfig} {checkpoint future : BlockChain}
    (ca : Adr) (trace : ConfiguredHistoryTrace cfg checkpoint future) :
    List WriterInvocation :=
  trace.settledFrames.flatMap (committedFrameInvocations ca)

/-- Every extracted invocation is the record of a settlement-committed frame at the
contract address that runs a writer selector; a rolled-back
frame is never in `settledFrames`, so it is never extracted. -/
theorem mem_committedInvocations {cfg : ChainConfig} {checkpoint future : BlockChain}
    {ca : Adr} {trace : ConfiguredHistoryTrace cfg checkpoint future}
    {inv : WriterInvocation} (member : inv ∈ committedInvocations ca trace) :
    ∃ frame ∈ trace.settledFrames, Execution.commits frame.out = true ∧
      frame.sevm.currentTarget = ca ∧ IsWriter (decodeCall frame.sevm) ∧
      inv = frameInvocation frame := by
  obtain ⟨frame, settled, selected⟩ := List.mem_flatMap.mp member
  refine ⟨frame, settled, frame.committed, ?_⟩
  unfold committedFrameInvocations at selected
  split at selected
  · rename_i selectedFrame
    exact ⟨selectedFrame.1, selectedFrame.2, List.mem_singleton.mp selected⟩
  · cases selected

/-- The mapping keys touched by a list of invocations. -/
def invocationKeys (invs : List WriterInvocation) : List Key :=
  invs.flatMap fun inv => callKeys inv.sevm.caller (decodeCall inv.sevm)

theorem invocationKeys_singleton (inv : WriterInvocation) :
    invocationKeys [inv] = callKeys inv.sevm.caller (decodeCall inv.sevm) := by
  simp [invocationKeys]

/-- One model step of an invocation, with the frame's own static-call evidence:
the model accepts the call with the recorded owner word, and a recorded owner
word is what the frame's `owner()` call on the model's minter answered. -/
def ModelStep (inv : WriterInvocation) (s : Blanc.Curve3Crv.State)
    (o : Blanc.Curve3Crv.Out) : Prop :=
  Blanc.Curve3Crv.step (c3ctx inv.sevm inv.ownerWord) (decodeCall inv.sevm) s = .ok o ∧
    ∀ w, inv.ownerWord = some w → OwnerAnswer inv.sevm inv.pre s.minter w

/-- The model run over exactly the given invocations, in order, from `s`. -/
def InvRun : Blanc.Curve3Crv.State → List WriterInvocation → Blanc.Curve3Crv.State → Prop
  | s, [], s' => s' = s
  | s, inv :: rest, s' => ∃ o, ModelStep inv s o ∧ InvRun o.1 rest s'

/-- The model's final state, by folding `Curve3Crv.step` over the invocations. -/
def runInvocations : Blanc.Curve3Crv.State → List WriterInvocation →
    Option Blanc.Curve3Crv.State
  | s, [] => some s
  | s, inv :: rest =>
      match Blanc.Curve3Crv.step (c3ctx inv.sevm inv.ownerWord) (decodeCall inv.sevm) s with
      | .ok o => runInvocations o.1 rest
      | .error _ => none

theorem InvRun.runInvocations_eq :
    ∀ {s : Blanc.Curve3Crv.State} {invs : List WriterInvocation} {s' : Blanc.Curve3Crv.State},
      InvRun s invs s' → runInvocations s invs = some s'
  | s, [], s', h => by rw [InvRun] at h; rw [h]; rfl
  | s, inv :: rest, s', h => by
      obtain ⟨o, ⟨accepted, _⟩, rest⟩ := h
      simp only [runInvocations, accepted]
      exact InvRun.runInvocations_eq rest

theorem InvRun.append :
    ∀ {s m s' : Blanc.Curve3Crv.State} {xs ys : List WriterInvocation},
      InvRun s xs m → InvRun m ys s' → InvRun s (xs ++ ys) s'
  | s, m, s', [], ys, h₁, h₂ => by
      rw [InvRun] at h₁
      subst h₁
      exact h₂
  | s, m, s', inv :: rest, ys, h₁, h₂ => by
      obtain ⟨o, step, tail⟩ := h₁
      exact ⟨o, step, InvRun.append tail h₂⟩

/-- A step's model acceptance, re-expressed at the canonical owner word. Only
`set_name` reads the owner, and it is accepted only when the answer is the caller. -/
theorem step_ownerWordOf {sevm : Sevm} {ow : Option B256} {s : Blanc.Curve3Crv.State}
    {o : Blanc.Curve3Crv.Out}
    (accepted : Blanc.Curve3Crv.step (c3ctx sevm ow) (decodeCall sevm) s = .ok o) :
    Blanc.Curve3Crv.step (c3ctx sevm (ownerWordOf sevm)) (decodeCall sevm) s = .ok o ∧
      ∀ w, ownerWordOf sevm = some w → ow = some w := by
  unfold ownerWordOf
  generalize decodeCall sevm = call at accepted ⊢
  cases call with
  | setName name symbol =>
    have key : ow = some sevm.caller.toB256 := by
      simp only [Blanc.Curve3Crv.step, Blanc.Curve3Crv.body, Blanc.Curve3Crv.setName,
        c3ctx] at accepted
      by_cases h1 : sevm.value = 0
      · by_cases h2 : name.length ≤ 64
        · by_cases h3 : symbol.length ≤ 32
          · simp only [h1, h2, h3, ↓reduceIte] at accepted
            cases ow with
            | none => cases accepted
            | some w =>
              by_cases h4 : w = sevm.caller.toB256
              · rw [h4]
              · simp only [h4, ↓reduceIte] at accepted
                cases accepted
          · simp [h1, h2, h3] at accepted
        · simp [h1, h2] at accepted
      · simp [h1] at accepted
    subst key
    exact ⟨accepted, fun w h => h⟩
  | setMinter _ => exact ⟨accepted, fun _ h => by cases h⟩
  | totalSupply => exact ⟨accepted, fun _ h => by cases h⟩
  | allowance _ _ => exact ⟨accepted, fun _ h => by cases h⟩
  | transfer _ _ => exact ⟨accepted, fun _ h => by cases h⟩
  | transferFrom _ _ _ => exact ⟨accepted, fun _ h => by cases h⟩
  | approve _ _ => exact ⟨accepted, fun _ h => by cases h⟩
  | mint _ _ => exact ⟨accepted, fun _ h => by cases h⟩
  | burnFrom _ _ => exact ⟨accepted, fun _ h => by cases h⟩
  | name => exact ⟨accepted, fun _ h => by cases h⟩
  | symbol => exact ⟨accepted, fun _ h => by cases h⟩
  | decimals => exact ⟨accepted, fun _ h => by cases h⟩
  | balanceOf _ => exact ⟨accepted, fun _ h => by cases h⟩
  | other => exact ⟨accepted, fun _ h => by cases h⟩

/-- The abstraction reads storage only through `Stor.get`. -/
theorem VyInv.of_get_eq {stor stor' : Stor} {s : Blanc.Curve3Crv.State} {K : Key → Prop}
    (same : ∀ x, stor'.get x = stor.get x) (h : VyInv stor s K) : VyInv stor' s K := by
  have vyStr : ∀ base n bs, VyStr stor base n bs → VyStr stor' base n bs := by
    intro base n bs hs
    unfold VyStr vyStrWords at hs ⊢
    simp only [same]
    exact hs
  exact
    { decimals := by rw [same]; exact h.decimals
      supply := by rw [same]; exact h.supply
      minter := by rw [same]; exact h.minter
      name := vyStr _ _ _ h.name
      symbol := vyStr _ _ _ h.symbol
      known := fun k hk => by rw [same]; exact h.known k hk
      unknown := h.unknown
      support := fun x hx => h.support x (by rw [← same]; exact hx)
      inj := h.inj
      apart := h.apart
      conserved := h.conserved }

theorem Key.extend_nil (K : Key → Prop) : Key.extend K [] = K := by
  funext k
  simp [Key.extend, SlotFootprint.extendBy]

theorem Key.extend_append (K : Key → Prop) (xs ys : List Key) :
    Key.extend (Key.extend K xs) ys = Key.extend K (xs ++ ys) := by
  funext k
  simp [Key.extend, SlotFootprint.extendBy, or_assoc]

/-- The connected replay of committed writer invocations over one storage
boundary of the contract. It is stated for every model abstraction of the opening
storage whose live keys lie in the collision universe `U`: the extracted
invocations' own keys stay in `U`, the model run of exactly those invocations
succeeds with the frames' owner evidence, and the closing storage abstracts its
result over the extended keys. -/
def CurveReplay (U : Key → Prop) (pre : Stor) (invs : List WriterInvocation)
    (post : Stor) : Prop :=
  (∀ k ∈ invocationKeys invs, U k) ∧
    ∀ s K, (∀ k, K k → U k) → VyInv pre s K →
      ∃ s', InvRun s invs s' ∧ VyInv post s' (Key.extend K (invocationKeys invs))

theorem CurveReplay.nil (U : Key → Prop) (stor : Stor) : CurveReplay U stor [] stor := by
  refine ⟨by simp [invocationKeys], fun s K _ h => ⟨s, rfl, ?_⟩⟩
  simpa only [invocationKeys, List.flatMap_nil, Key.extend_nil] using h

/-- A storage boundary with the same `Stor.get` observation replays no invocation. -/
theorem CurveReplay.of_get_eq {U : Key → Prop} {pre post : Stor}
    (same : ∀ x, post.get x = pre.get x) : CurveReplay U pre [] post := by
  refine ⟨by simp [invocationKeys], fun s K _ h => ⟨s, rfl, ?_⟩⟩
  simpa only [invocationKeys, List.flatMap_nil, Key.extend_nil] using h.of_get_eq same

theorem CurveReplay.append {U : Key → Prop} {a b c : Stor} {xs ys : List WriterInvocation}
    (first : CurveReplay U a xs b) (second : CurveReplay U b ys c) :
    CurveReplay U a (xs ++ ys) c := by
  refine ⟨?_, fun s K hK h => ?_⟩
  · intro k hk
    simp only [invocationKeys, List.flatMap_append, List.mem_append] at hk
    exact hk.elim (first.1 k) (second.1 k)
  · obtain ⟨s₁, run₁, inv₁⟩ := first.2 s K hK h
    have hK₁ : ∀ k, Key.extend K (invocationKeys xs) k → U k := by
      intro k hk
      exact hk.elim (hK k) (first.1 k)
    obtain ⟨s₂, run₂, inv₂⟩ := second.2 s₁ _ hK₁ inv₁
    refine ⟨s₂, run₁.append run₂, ?_⟩
    simpa only [Key.extend_append, invocationKeys, List.flatMap_append] using inv₂

/-- The storage-only replay carrier of a Curve history: boundaries are the
contract's storage, so value credits and foreign frames contribute nothing. -/
def curveCarrier (ca : Adr) (U : Key → Prop) : ReplayCarrier ca where
  Snap := Stor
  Step := WriterInvocation
  Tag := Unit
  Replay := CurveReplay U
  ofState state := state.getStor ca
  frameEntry _ state := state.getStor ca
  nil := CurveReplay.nil U
  silent := fun storage _ => storage
  credit := by
    intro _ _ _ _ storage _ _
    exact ⟨[], by rw [storage]; exact CurveReplay.nil U _⟩
  entry_eq_ofState := by
    intro _ _ _ _ transfer _
    exact congrFun (benvAfterTransfer_getStor_eq transfer) ca

/-- Replay steps and committed-frame invocations use the same ordered
observation. -/
def curveObservation (ca : Adr) (U : Key → Prop) : ReplayObservation (curveCarrier ca U) where
  O := WriterInvocation
  obs := id
  obs_nil := rfl
  obs_append := fun _ _ => rfl
  frameObs := committedFrameInvocations ca
  credit := by
    intro _ pre post _ storage _ _
    refine ⟨[], ?_, rfl⟩
    change CurveReplay U (pre.getStor ca) [] (post.getStor ca)
    rw [storage]
    exact CurveReplay.nil U _

end Blanc.Lift.Curve3Crv
