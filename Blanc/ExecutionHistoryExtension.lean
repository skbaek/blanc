import Blanc.ExecutionTraceSettledFrames
import Blanc.ExecutionBodyGas
import Blanc.ExecutionTraceCallerExclusion

/-!
Extensions of configured history traces: a history followed by exactly `n`
further configured blocks. Retained frames, block counts and the per-history
exclusion premises (`NoSenderAt`, `NoAuthorityAt`, raw-frame avoidance) of an
extension restrict to the history it extends.
-/

namespace Blanc.ExecutionTrace

open Jaune

/-- `base.ExtendsBy trace n`: `trace` is `base` followed by exactly `n` configured blocks. -/
inductive ConfiguredHistoryTrace.ExtendsBy {cfg : ChainConfig} {checkpoint current : BlockChain}
    (base : ConfiguredHistoryTrace cfg checkpoint current) :
    {future : BlockChain} → ConfiguredHistoryTrace cfg checkpoint future → Nat → Prop
  | refl : ConfiguredHistoryTrace.ExtendsBy base base 0
  | step {middle future : BlockChain} {trace : ConfiguredHistoryTrace cfg checkpoint middle}
      {n : Nat} (prior : ConfiguredHistoryTrace.ExtendsBy base trace n)
      (block : ConfiguredBlockTrace cfg middle future) :
      ConfiguredHistoryTrace.ExtendsBy base (.step trace block) (n + 1)

namespace ConfiguredHistoryTrace.ExtendsBy

variable {cfg : ChainConfig} {checkpoint current : BlockChain}
  {base : ConfiguredHistoryTrace cfg checkpoint current}

/-- An extension's retained frames are the base's frames followed by the new blocks' frames. -/
theorem settledFrames {future : BlockChain} {trace : ConfiguredHistoryTrace cfg checkpoint future}
    {n : Nat} (extends_ : base.ExtendsBy trace n) :
    ∃ suffix, trace.settledFrames = base.settledFrames ++ suffix := by
  induction extends_ with
  | refl => exact ⟨[], (List.append_nil _).symm⟩
  | step _ block ih =>
    obtain ⟨suffix, eq⟩ := ih
    exact ⟨suffix ++ block.settledFrames, by
      rw [ConfiguredHistoryTrace.settledFrames, eq, List.append_assoc]⟩

/-- Every raw frame of the base is a raw frame of the extension. -/
theorem rawFrames_mem {future : BlockChain} {trace : ConfiguredHistoryTrace cfg checkpoint future}
    {n : Nat} (extends_ : base.ExtendsBy trace n) :
    ∀ root ∈ base.rawFrames, root ∈ trace.rawFrames := by
  induction extends_ with
  | refl => exact fun _ member => member
  | step _ block ih =>
    intro root member
    rw [ConfiguredHistoryTrace.rawFrames]
    exact List.mem_append_left _ (ih root member)

/-- An extension by `n` blocks has exactly `n` more blocks. -/
theorem blockCount {future : BlockChain} {trace : ConfiguredHistoryTrace cfg checkpoint future}
    {n : Nat} (extends_ : base.ExtendsBy trace n) :
    trace.blockCount = base.blockCount + n := by
  induction extends_ with
  | refl => rfl
  | step _ block ih =>
    rw [ConfiguredHistoryTrace.blockCount, ih, Nat.add_assoc]

theorem noSenderAt {future : BlockChain} {trace : ConfiguredHistoryTrace cfg checkpoint future}
    {n : Nat} (extends_ : base.ExtendsBy trace n) {a : Adr} (senders : trace.NoSenderAt a) :
    base.NoSenderAt a := by
  induction extends_ with
  | refl => exact senders
  | step _ block ih => exact ih senders.1

theorem noAuthorityAt {future : BlockChain} {trace : ConfiguredHistoryTrace cfg checkpoint future}
    {n : Nat} (extends_ : base.ExtendsBy trace n) {a : Adr} (authorities : trace.NoAuthorityAt a) :
    base.NoAuthorityAt a := by
  induction extends_ with
  | refl => exact authorities
  | step _ block ih => exact ih authorities.1

end ConfiguredHistoryTrace.ExtendsBy

end Blanc.ExecutionTrace
