import Blanc.Separated
import Blanc.RlpRoundTrip

/-!
# Binding a header to a recorded block hash

A trace's header `h` and a recorded header `h₀` with equal hashes have equal canonical encodings
under the trace-local premise `Separated Bytes.keccak [h.toBLT.toBytes, h₀.toBLT.toBytes]`
(no universal Keccak injectivity), and then, by Jaune's RLP round trip
(`RlpConcrete.toBLT?_toBytes`), equal `Header.toBLT` trees (`toBLT_eq_of_hash_eq`). Equal trees give
the fifteen pre-London fields that `Header.toBLT` always writes (`fields_of_toBLT_eq`); the
fork-dependent optional tail is left untouched, so this needs no knowledge of either header's fork.
The coinbase and seal nonce are not recovered (no `Adr`/`UInt64` byte round trip is used here).
-/

namespace Blanc.HeaderBinding

open Jaune

/-- **Hash binding.** Equal hashes and Keccak separation of the two encodings give equal encoded
trees. -/
theorem toBLT_eq_of_hash_eq {h h₀ : Header} (hash : h.hash = h₀.hash)
    (sep : Separated Bytes.keccak [h.toBLT.toBytes, h₀.toBLT.toBytes])
    (small : h₀.toBLT.toBytes.length < 2 ^ 64) : h.toBLT = h₀.toBLT := by
  have e : h.toBLT.toBytes = h₀.toBLT.toBytes := sep.pair_eq hash
  have d := RlpConcrete.toBLT?_toBytes h.toBLT (e ▸ small)
  rw [e, RlpConcrete.toBLT?_toBytes _ small] at d
  exact (Option.some.inj d).symm

private theorem b256_of_bytes {x y : B256} (e : x.toBytes = y.toBytes) : x = y := by
  rw [← B256.toB256_toBytes x, e, B256.toB256_toBytes]

private theorem nat_of_bytes {m n : Nat} (e : m.toBytes = n.toBytes) : m = n := by
  rw [← RlpConcrete.nat_bytes_roundtrip m, e, RlpConcrete.nat_bytes_roundtrip]

/-- The fields every header encoding carries, from equal encoded trees. -/
structure Fields (h h₀ : Header) : Prop where
  parentHash : h.parentHash = h₀.parentHash
  ommersHash : h.ommersHash = h₀.ommersHash
  stateRoot : h.stateRoot = h₀.stateRoot
  txsRoot : h.txsRoot = h₀.txsRoot
  receiptRoot : h.receiptRoot = h₀.receiptRoot
  bloom : h.bloom = h₀.bloom
  difficulty : h.difficulty = h₀.difficulty
  number : h.number = h₀.number
  gasLimit : h.gasLimit = h₀.gasLimit
  gasUsed : h.gasUsed = h₀.gasUsed
  timestamp : h.timestamp = h₀.timestamp
  extraData : h.extraData = h₀.extraData
  prevRandao : h.prevRandao = h₀.prevRandao

theorem fields_of_toBLT_eq {h h₀ : Header} (e : h.toBLT = h₀.toBLT) : Fields h h₀ := by
  unfold Header.toBLT at e
  have l := (List.append_inj (BLT.list.inj e) rfl).1
  simp only [List.cons.injEq, BLT.bytes.injEq] at l
  obtain ⟨p, o, _, s, t, r, b, d, n, gl, gu, ts, x, pr, _⟩ := l
  exact ⟨b256_of_bytes p, b256_of_bytes o, b256_of_bytes s, b256_of_bytes t, b256_of_bytes r, b,
    nat_of_bytes d, nat_of_bytes n, nat_of_bytes gl, nat_of_bytes gu, nat_of_bytes ts, x,
    b256_of_bytes pr⟩

end Blanc.HeaderBinding
