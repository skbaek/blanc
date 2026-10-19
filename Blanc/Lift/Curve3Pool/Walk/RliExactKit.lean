import Blanc.Lift.Curve3Pool.Walk.AddLiquidityExactKit

/-!
# Literal-memory glue for `remove_liquidity_imbalance`'s exact walk

`slice_memWord`: a word the walk loads off its image carrier is the literal memory's word, so a
stage core can name a saved and later restored word as `memWord` of its literal memory.
`eqB_saveMem` and `eqB_memWord` carry two memories equal at every byte
(`Mem.EqExcept M N fun _ => False`, what `get_D_mem` leaves) through a frame save's counter writes
and its pushed words, up to the next growing store that makes them literally equal
(`eqB_write_word_grow`).
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

end Blanc.Lift.Curve3Pool
