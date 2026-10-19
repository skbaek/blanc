import Blanc.Lift.Curve3Pool.Walk.AddLiquidityExactKit
import Blanc.Lift.Curve3Pool.Walk.RemoveImbalanceFeeLoop

/-!
# Literal-memory glue for `remove_liquidity_imbalance`'s exact walk

`slice_memWord`: a word the walk loads off its image carrier is the literal memory's word, so a
stage core can name a saved and later restored word as `memWord` of its literal memory.
`eqB_saveMem` and `eqB_memWord` carry two memories equal at every byte
(`Mem.EqExcept M N fun _ => False`, what `get_D_mem` leaves) through a frame save's counter writes
and its pushed words, up to the next growing store that makes them literally equal
(`eqB_write_word_grow`). `RliDif.unique` and `RliFeeIter.unique`: a fee iteration's words are
functions of its inputs, so an exact cost stated at them is pinned by the model's checks.
-/

namespace Blanc.Lift.Curve3Pool

open Jaune Blanc.Lift

/-- A word read off the image carrier is the literal memory's word. -/
theorem slice_memWord {M : Mem} {img : Bytes} (hR : Mem.Reads M img) (o : Nat) :
    Bytes.toB256 (img.sliceD o 32 0) = memWord M o := by
  unfold memWord
  rw [hR.read]

/-- The words a frame save reads off the image carrier are the literal memory's. -/
theorem slice_memWord_fun {M : Mem} {img : Bytes} (hR : Mem.Reads M img) :
    (fun o => Bytes.toB256 (img.sliceD o 32 0)) = memWord M :=
  funext (slice_memWord hR)

/-- Two memories equal at every byte read the same words. -/
theorem eqB_memWord {M N : Mem} (h : Mem.EqExcept M N fun _ => False) (o : Nat) :
    memWord M o = memWord N o :=
  (memWord_congr fun j _ => (h.2.2.2 (o + j) id).symm).symm

/-- A frame save's counter writes keep two memories equal at every byte. -/
theorem eqB_saveMem {M N : Mem} (h : Mem.EqExcept M N fun _ => False) (c lo : Nat) :
    ∀ n, Mem.EqExcept (saveMem M c lo n) (saveMem N c lo n) fun _ => False
  | 0 => h
  | n + 1 => eqB_write (eqB_saveMem h c lo n) _ _

/-- A log leaves the price of a later `SSTORE` alone. -/
theorem sstoreCost_addLog (sevm : Sevm) (b : Devm) (l : Log) (k v : B256) :
    sstoreCost sevm (b.addLog l) k v = sstoreCost sevm b k v := rfl

/-- A fee iteration's `difference` is a function of `ideal` and the new balance. -/
theorem RliDif.unique {I N d d' : B256} (h : RliDif I N d) (h' : RliDif I N d') : d = d' := by
  rcases h with ⟨h1, rfl⟩ | ⟨h1, rfl⟩ <;> rcases h' with ⟨h2, rfl⟩ | ⟨h2, rfl⟩
  · rfl
  · exact absurd h1 h2
  · exact absurd h2 h1
  · rfl

/-- A fee iteration's fee, stored balance and adjusted balance are functions of its inputs. -/
theorem RliFeeIter.unique {F AF D0 D1 B N f st af f' st' af' : B256}
    (h : RliFeeIter F AF D0 D1 B N f st af) (h' : RliFeeIter F AF D0 D1 B N f' st' af') :
    f = f' ∧ st = st' ∧ af = af' := by
  obtain ⟨-, -, d, hd, -, rfl, -, -, rfl, -, rfl⟩ := h
  obtain ⟨-, -, d', hd', -, rfl, -, -, rfl, -, rfl⟩ := h'
  obtain rfl := hd.unique hd'
  exact ⟨rfl, rfl, rfl⟩

end Blanc.Lift.Curve3Pool
