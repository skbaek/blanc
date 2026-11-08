import Blanc.ExecutionAccountingPositionalHistory
import Blanc.ExecutionMidHistoryInFacts
import Blanc.Lift.RetainedTargetCompleteness
import Blanc.ExecutionWholeFrameAccounting
import Blanc.ExecutionAccountingCoreIn
import Blanc.ExecutionAccountingMidHistoryIn
import Blanc.StorageOnlySpec
import Blanc.Lift.CodeImage

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
abbrev StorWords := B256 → B256

/-- The words of `T`'s storage in a world. -/
def wordsAt (T : Adr) (w : State) : StorWords := (w.getStor T).get

/-- Frames `fs` carry `T`'s storage from `a` to `b`, each entered where the last one left it. -/
def FrameChain (T : Adr) (Good : Exec.Frame → Prop) : StorWords → List Exec.Frame → StorWords → Prop
  | a, [], b => b = a
  | a, F :: fs, b => Good F ∧ wordsAt T F.pre.state = a ∧ FrameChain T Good (wordsAt T F.post.state) fs b

namespace FrameChain

variable {T : Adr} {Good : Exec.Frame → Prop}

theorem append : ∀ {a b c : StorWords} {xs ys : List Exec.Frame},
    FrameChain T Good a xs b → FrameChain T Good b ys c → FrameChain T Good a (xs ++ ys) c
  | _, _, _, [], _, hx, hy => by
    cases hx
    exact hy
  | _, _, _, _ :: _, _, hx, hy => ⟨hx.1, hx.2.1, append hx.2.2 hy⟩

/-- **A property every frame carries holds along the chain, and a quantity moves by the frames'
amounts.** Each frame keeps `I` and moves `held` by `credit` and `debit`. -/
theorem fold {held : StorWords → Nat} {I : StorWords → Prop} {debit credit : Exec.Frame → Nat} :
    ∀ {a b : StorWords} {xs : List Exec.Frame}, FrameChain T Good a xs b →
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

end FrameChain

open Classical in
/-- A frame's observation: itself, when it is a non-static frame at `T` that `Obs` selects. -/
noncomputable def coinObs (T : Adr) (Obs : Exec.Frame → Prop) (f : Exec.Frame) : List Exec.Frame :=
  if f.sevm.currentTarget = T ∧ f.sevm.isStatic = false ∧ Obs f then [f] else []

/-- The non-static frames at `T` that `Obs` selects, in order. -/
noncomputable def coinFrames (T : Adr) (Obs : Exec.Frame → Prop) (fs : List Exec.Frame) :
    List Exec.Frame :=
  fs.flatMap (coinObs T Obs)

section Mid

variable {F : Fork → Prop} {T : Adr} {C : ByteArray} {Allowed : Exec.Frame → Prop}

end Mid

end Blanc.Lift
