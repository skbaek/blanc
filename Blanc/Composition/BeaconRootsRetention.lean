import Blanc.Corpus.Proofs.RingHistory

namespace Blanc.Composition.BeaconRootsRetention

open Jaune Blanc.Corpus.Freeze Blanc.Corpus.Freeze.BeaconRoots

/-- A positive timestamp's root survives every later accepted block in its local 8191-second window. -/
theorem r_s8_time : Blanc.Corpus.Freeze.BeaconRoots.R_S8_time := by
  intro cfg start stop blocks history covered code empty clean i hi positive fits window
  apply (Blanc.Corpus.Proofs.RingHistory.R.r_s3 history covered code empty clean).2 i hi positive
  intro j hj later same
  have strict := history.timestamp_lt later (List.getElem?_eq_getElem hi) (List.getElem?_eq_getElem hj)
  have upper := window j hj later
  let T := blocks[i].block.header.timestamp
  let U := blocks[j].block.header.timestamp
  have ti : T < 2 ^ 256 := by dsimp only [T]; omega
  have uj : U < 2 ^ 256 := by dsimp only [U]; omega
  have keys := congrArg B256.toNat same
  change (timeKey U.toB256).toNat = (timeKey T.toB256).toNat at keys
  rw [timeKey, timeKey, B256.toNat_mod (by decide), B256.toNat_mod (by decide),
    B256.toNat_toB256_of_lt uj, B256.toNat_toB256_of_lt ti,
    show ring.toNat = 8191 from rfl] at keys
  change T < U at strict
  change U < T + 8191 at upper
  omega

end Blanc.Composition.BeaconRootsRetention
