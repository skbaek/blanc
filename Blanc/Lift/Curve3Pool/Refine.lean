import Blanc.Lift.Curve3Pool.Spec

/-!
# The raw effect refines the model (pure)

No bytecode appears here: these are statements about `Stor.get`, the model's `step` and the
footprints of `Spec.lean`.

* `step_keeps`: every successful step changes only its call's footprint fields, and keeps the
  address fields addresses (`Keeps`);
* `checkpoint_of_storEffect`: a checkpoint storage, a step, and a storage effect at that step's
  footprint give a checkpoint storage for the new state — every slot off the footprint, the lock
  included, keeps its word, and the slots are pairwise distinct (`Fld.slot_inj`,
  `Fld.slot_ne_lock`, from `poolSlots_nodup`);
* `rawEffect_refines`: **the pure refinement**. A walk's `RawEffect` for a step of the decoded
  call, from a frame whose entry storage is a checkpoint, leaves a checkpoint storage for the
  model's new state, the model's events after the children's logs, the model's return data, and
  (for a non-static frame) the model's calls encoded at the state's coin and token addresses.
-/

namespace Blanc.Lift.Curve3Pool

open Jaune

/-! ## Results of an optional computation -/

/-- `P` holds of every result `m` can return. -/
def OptAll {α : Type} (P : α → Prop) (m : Option α) : Prop := ∀ a, m = some a → P a

namespace OptAll

variable {α β : Type} {P : α → Prop}

theorem none' : OptAll P none := fun _ h => by cases h

theorem some' {a : α} (h : P a) : OptAll P (some a) := fun _ e => Option.some.inj e ▸ h

theorem bind {x : Option β} {f : β → Option α} (h : ∀ b, x = some b → OptAll P (f b)) :
    OptAll P (x >>= f) := by
  intro a e
  cases hx : x with
  | none => rw [hx] at e; cases e
  | some b => rw [hx] at e; exact h b hx a e

theorem req {c : Prop} [Decidable c] {f : Unit → Option α} (h : c → OptAll P (f ())) :
    OptAll P (Curve3Pool.req c >>= f) := by
  intro a e
  by_cases hc : c
  · simp only [Curve3Pool.req, hc, ↓reduceIte] at e
    exact h hc a e
  · simp only [Curve3Pool.req, hc, ↓reduceIte] at e
    cases e

theorem ite {c : Prop} [Decidable c] {m m' : Option α} (h : c → OptAll P m)
    (h' : ¬ c → OptAll P m') : OptAll P (if c then m else m') := by
  by_cases hc : c
  · simp only [hc, ↓reduceIte]; exact h hc
  · simp only [hc, ↓reduceIte]; exact h' hc

end OptAll

/-! ## Footprints -/

/-- `s'` differs from `s` only at `c`'s footprint, and keeps the address fields addresses. -/
def Keeps (c : Call) (s s' : State) : Prop :=
  (∀ f, f ∉ footprint c → Fld.Same s s' f) ∧ (s.AddrBounded → s'.AddrBounded)

theorem bal_mem : ∀ i : Fin 3, Fld.bal i ∈ balFlds
  | ⟨0, _⟩ => .head _
  | ⟨1, _⟩ => .tail _ (.head _)
  | ⟨2, _⟩ => .tail _ (.tail _ (.head _))

/-- Descend an optional computation to its results. -/
syntax "opt_walk" : tactic
macro_rules
  | `(tactic| opt_walk) => `(tactic| repeat' (first
      | (with_reducible apply OptAll.req; intro _)
      | (with_reducible apply OptAll.bind; intro _ _)
      | (with_reducible apply OptAll.ite <;> intro _)
      | dsimp only
      | split))

/-- Close a `some` result that is a structure update of `s` off the footprint. -/
syntax "keeps_close" : tactic
macro_rules
  | `(tactic| keeps_close) => `(tactic| (
      with_reducible apply OptAll.some'
      refine ⟨fun f hf => ?_, fun hb => ?_⟩
      · cases f <;> first | rfl | exact absurd (bal_mem _) hf | exact absurd (by simp only [footprint, List.mem_cons, List.mem_singleton, true_or, or_true]) hf
      · first | exact hb | exact ⟨hb.1, hb.2.1, hb.2.2.1, hb.2.2.2.1, hb.2.2.2.2.1, by assumption⟩ | exact ⟨hb.2.2.2.2.2, hb.2.1, hb.2.2.1, hb.2.2.2.1, hb.2.2.2.2.1, hb.2.2.2.2.2⟩))

/-- **Every successful step changes only its call's footprint**, and keeps the address fields
addresses. -/
theorem body_keeps (s : State) (e : Env) (c : Call) :
    OptAll (fun o => Keeps c s o.state) (body s e c) := by
  cases c <;> simp only [body, Curve3Pool.addLiquidity, Curve3Pool.exchange,
    Curve3Pool.removeLiquidity, Curve3Pool.removeLiquidityImbalance,
    Curve3Pool.removeLiquidityOneCoin, Curve3Pool.rampA, Curve3Pool.stopRampA,
    Curve3Pool.commitNewFee, Curve3Pool.applyNewFee, Curve3Pool.revertNewParameters,
    Curve3Pool.commitTransferOwnership, Curve3Pool.applyTransferOwnership,
    Curve3Pool.revertTransferOwnership, Curve3Pool.withdrawAdminFees,
    Curve3Pool.donateAdminFees, Curve3Pool.killMe, Curve3Pool.unkillMe] <;> opt_walk
  all_goals first
    | exact OptAll.none'
    | keeps_close

/-- **Every successful step changes only its call's footprint** (and keeps the address fields
addresses). -/
theorem step_keeps {s : State} {e : Env} {c : Call} {o : Out} (h : step s e c = some o) :
    Keeps c s o.state := by
  have hall : OptAll (fun o => Keeps c s o.state) (step s e c) := by
    unfold step
    split
    · exact OptAll.none'
    · exact OptAll.ite (fun _ => body_keeps s e _) (fun _ => OptAll.none')
  exact hall o h

/-- No step moves the coins or the token. -/
theorem Keeps.coins_token {c : Call} {s s' : State} (h : Keeps c s s') :
    s'.coins = s.coins ∧ s'.token = s.token := by
  have hc : ∀ i, Fld.coin i ∉ footprint c := fun i hm => by
    cases c <;> simp only [footprint, balFlds, List.mem_cons, List.not_mem_nil, reduceCtorEq,
      or_self] at hm
  have ht : Fld.token ∉ footprint c := fun hm => by
    cases c <;> simp only [footprint, balFlds, List.mem_cons, List.not_mem_nil, reduceCtorEq,
      or_self] at hm
  exact ⟨(V3.ext_get fun i => h.1 _ (hc i)).symm, (h.1 _ ht).symm⟩

/-! ## Slots -/

namespace Fld

/-- A field's position in `poolSlots`. -/
def idx : Fld → Nat
  | coin i => i.val
  | bal i => 3 + i.val
  | fee => 6
  | adminFee => 7
  | owner => 8
  | token => 9
  | initialA => 10
  | futureA => 11
  | initialATime => 12
  | futureATime => 13
  | adminActionsDeadline => 14
  | transferOwnershipDeadline => 15
  | futureFee => 16
  | futureAdminFee => 17
  | futureOwner => 18
  | isKilled => 19
  | killDeadline => 20

theorem idx_lt (f : Fld) : f.idx < 21 := by
  cases f <;> simp only [idx] <;> omega

theorem slot_at (f : Fld) : poolSlots[f.idx]'(by
    have := f.idx_lt; simp only [poolSlots, List.length_cons, List.length_nil]; omega) = f.slot := by
  cases f with
  | coin i => rcases i with ⟨_ | _ | _ | n, h⟩ <;> first | rfl | omega
  | bal i => rcases i with ⟨_ | _ | _ | n, h⟩ <;> first | rfl | omega
  | _ => rfl

theorem idx_inj {f g : Fld} (h : f.idx = g.idx) : f = g := by
  cases f <;> cases g <;> simp only [idx] at h <;>
    first | rfl | omega | (congr 1; exact Fin.ext (by omega))

/-- Distinct fields have distinct slots (`poolSlots_nodup`). -/
theorem slot_inj {f g : Fld} (h : f.slot = g.slot) : f = g := by
  rw [← f.slot_at, ← g.slot_at] at h
  exact idx_inj (poolSlots_nodup.getElem_inj_iff.mp h)

/-- No field sits at the lock slot. -/
theorem slot_ne_lock (f : Fld) : f.slot ≠ lockSlot := by
  intro h
  have hl : poolSlots[21]'(by simp only [poolSlots, List.length_cons, List.length_nil]; omega) =
      lockSlot := rfl
  rw [← f.slot_at, ← hl] at h
  have := f.idx_lt
  have := poolSlots_nodup.getElem_inj_iff.mp h
  omega

/-- A slot that keeps its word and a field the state keeps keep the reading. -/
theorem Reads.congr {stor stor' : Stor} {s s' : State} {f : Fld}
    (hget : stor'.get f.slot = stor.get f.slot) (hs : Same s s' f) (h : Reads stor s f) :
    Reads stor' s' f := by
  cases f <;> simp only [Reads, slot, Same] at hget hs h ⊢ <;> rw [hget, h, hs]

end Fld

/-- The abstraction, field by field. -/
theorem Abstracts.reads {stor : Stor} {s : State} (h : Abstracts stor s) : ∀ f : Fld, f.Reads stor s
  | .coin i => h.coins i
  | .bal i => h.balances i
  | .fee => h.fee
  | .adminFee => h.adminFee
  | .owner => h.owner
  | .token => h.token
  | .initialA => h.initialA
  | .futureA => h.futureA
  | .initialATime => h.initialATime
  | .futureATime => h.futureATime
  | .adminActionsDeadline => h.adminActionsDeadline
  | .transferOwnershipDeadline => h.transferOwnershipDeadline
  | .futureFee => h.futureFee
  | .futureAdminFee => h.futureAdminFee
  | .futureOwner => h.futureOwner
  | .isKilled => h.isKilled
  | .killDeadline => h.killDeadline

theorem Abstracts.of_reads {stor : Stor} {s : State} (h : ∀ f : Fld, f.Reads stor s) :
    Abstracts stor s :=
  ⟨fun i => h (.coin i), fun i => h (.bal i), h .fee, h .adminFee, h .owner, h .token, h .initialA,
    h .futureA, h .initialATime, h .futureATime, h .adminActionsDeadline,
    h .transferOwnershipDeadline, h .futureFee, h .futureAdminFee, h .futureOwner, h .isKilled,
    h .killDeadline⟩

/-! ## The refinement -/

/-- **A storage effect at a step's footprint keeps the checkpoint**: off the footprint every
slot (the lock included) keeps its word and the state its field; on it the walk supplies the
reading. -/
theorem checkpoint_of_storEffect {c : Call} {pre post : Stor} {s s' : State}
    (hc : Checkpoint pre s) (hk : Keeps c s s') (he : StorEffect c pre post s') :
    Checkpoint post s' := by
  have reads : ∀ f : Fld, f.Reads post s' := by
    intro f
    by_cases hf : f ∈ footprint c
    · exact he.written f hf
    · refine Fld.Reads.congr (he.kept _ fun g hg heq => hf ?_) (hk.1 f hf) (hc.abs.reads f)
      exact (Fld.slot_inj heq) ▸ hg
  refine ⟨Abstracts.of_reads reads, ?_, hk.2 hc.addr⟩
  rw [he.kept _ fun g _ heq => Fld.slot_ne_lock g heq, hc.unlocked]

/-- **The pure refinement.** A frame `D` whose entry storage is a checkpoint for `s`, a model
step of the decoded call with the observed environment, and the walk's raw effect give: a
checkpoint storage for the new state; the model's events after the children's logs; the model's
return data; for a non-static frame, the model's calls encoded at the state's coin and token
addresses (those of every target that enters a code frame); and the coins and token unchanged. -/
theorem rawEffect_refines {D : Exec.Deriv} {post : Devm} {s : State} {e : Env} {o : Out}
    (hc : Checkpoint (entryStor D) s) (hstep : step s e (decodeCall D.sevm) = some o)
    (hraw : RawEffect D post e o) :
    Checkpoint (post.getStor D.sevm.currentTarget) o.state ∧
      post.logs = D.devm.logs ++ (children D).flatMap (fun c => c.post.logs) ++
        o.events.map (eventLog D.sevm.currentTarget) ∧
      post.output = retOut D.devm.output o.ret ∧
      (D.sevm.isStatic = false → CallsOf D =
        (o.calls.map (encodeCall D.sevm.currentTarget (fun k => adrOf (s.coins.get k))
          (adrOf s.token))).filter fun r => framed D r.target) ∧
      o.state.coins = s.coins ∧ o.state.token = s.token := by
  have hk := step_keeps hstep
  refine ⟨checkpoint_of_storEffect hc hk hraw.stor, hraw.logs, hraw.output, fun hs => ?_,
    hk.coins_token⟩
  rw [hraw.calls hs, modelCalls, encodeCall_entry hc.abs]

end Blanc.Lift.Curve3Pool
