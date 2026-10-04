import Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.TxTopC

/-!
The signature of `TxTopC.txC` recovers `E`, as a kernel theorem.

`recoverSender` hashes the transaction's signing payload and recovers the signer from `(r, s)`;
for the one concrete transaction `txC` both steps are closed terms.  The kernel evaluates the
hash and the recovery (`decide +kernel`) but not the RLP encoder `BLT.toBytes` or `Nat.toBytes`
(well-founded recursion), so the encoding is first rewritten to its bytes by `simp only`, the
pattern of `Blanc.Lift.WithdrawalRequest.FloodTx.txC_signingEncoded`; the 19-entry access list is
encoded by a lemma over entries, not entry by entry.  The V- transaction theorem therefore
carries no signature premise.
-/

namespace Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.TxC

open Jaune Blanc.Lift Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.TxTop

/-- One access-list entry with no storage keys, as RLP. -/
def entryOf (a : Bytes) : BLT := .list [.bytes a, .list []]

/-- A 20-byte address entry encodes as `0xd6 0x94 <address> 0xc0`. -/
theorem entry_toBytes (a : Bytes) (h : a.length = 20) :
    (entryOf a).toBytes = 0xd6 :: 0x94 :: (a ++ [0xc0]) := by
  rcases a with _ | ⟨b, _ | ⟨c, a⟩⟩
  · simp only [List.length_nil] at h
    omega
  · simp only [List.length_cons, List.length_nil] at h
    omega
  · have ha : a.length = 18 := by
      simp only [List.length_cons] at h
      omega
    simp only [entryOf, BLT.toBytes, BLTs.toBytes, BLTs.toBytesJoin, List.length_cons,
      List.length_nil, List.length_append, ha, Nat.reduceLT, ↓reduceIte, Nat.reduceAdd,
      Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.cons_append, List.append_nil]

/-- The items of a list of address entries are the entries' bytes, one after another. -/
theorem join_entries (as : List Bytes) (h : ∀ a ∈ as, a.length = 20) :
    BLTs.toBytesJoin (as.map entryOf) =
      (as.map fun a => 0xd6 :: 0x94 :: (a ++ [0xc0])).flatten := by
  induction as with
  | nil => simp only [List.map_nil, BLTs.toBytesJoin, List.flatten_nil]
  | cons a as ih =>
    simp only [List.map_cons, BLTs.toBytesJoin, List.flatten_cons]
    rw [entry_toBytes a (h a List.mem_cons_self), ih (fun b hb => h b (List.mem_cons_of_mem a hb))]

/-- An access list with no storage keys is the list of its address entries. -/
theorem toBLT_noKeys (al : AccessList) (h : ∀ p ∈ al, p.2 = []) :
    AccessList.toBLT al = BLT.list (al.map fun p => entryOf p.1.toBytes) := by
  dsimp only [AccessList.toBLT]
  congr 1
  apply List.map_congr_left
  intro p hp
  simp only [h p hp, entryOf, List.map_nil]

/-- The access list of `txC`, as RLP bytes: a long-list header (437 bytes of items) and the
entries. -/
def accessEnc : Bytes :=
  0xf9 :: 0x01 :: 0xb5 :: (accessListC.map fun p => 0xd6 :: 0x94 :: (p.1.toBytes ++ [0xc0])).flatten

theorem accessEnc_length : accessEnc.length = 440 := by decide +kernel

theorem accessListC_toBytes : (AccessList.toBLT accessListC).toBytes = accessEnc := by
  have hk : ∀ p ∈ accessListC, p.2 = [] := by decide +kernel
  have hl : ∀ a ∈ accessListC.map (fun p => p.1.toBytes), a.length = 20 := by decide +kernel
  have hj := join_entries _ hl
  rw [toBLT_noKeys accessListC hk]
  have e : ∀ rs, (BLT.list rs).toBytes = BLTs.toBytes rs := fun rs => by
    simp only [BLT.toBytes]
  rw [e]
  simp only [List.map_map, Function.comp_def] at hj
  simp only [BLTs.toBytes, accessEnc, hj]
  decide +kernel

/-- `txC`'s signing hash. -/
theorem txC_signingHash :
    txC.signingHash =
      some (0x78aa991530dc569e45b407aa19e78c5618f35fe01357b2547ade0c3f2727d90d : B256) := by
  have h0 : Nat.toBytes 0 = [] := by decide +kernel
  have hg : Nat.toBytes 16043200 = [0xf4, 0xcc, 0xc0] := by
    simp only [Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod,
      Nat.toUInt8_eq, UInt8.reduceOfNat, Nat.reduceDiv]
  have hc : (UInt64.toBytes 0).sig = [] := by decide +kernel
  have hto : ((some a2Address <&> Adr.toBytes).getD []) =
      [0xaa, 0xaa, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
       0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0xa2, 0xa2, 0xa2, 0xa2] := by decide +kernel
  have hp : Nat.toBytesPack 475 = [0x01, 0xdb] := by
    simp only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd,
      Nat.reduceMod, Nat.toUInt8_eq, UInt8.reduceOfNat, Nat.reduceDiv]
  simp only [Tx.signingHash, txC, hc, h0, hg, hto, START]
  simp only [BLT.toBytes, BLTs.toBytes, BLTs.toBytesJoin, accessListC_toBytes, 
    ↓reduceIte, List.length_nil, Nat.ofNat_pos, Nat.toUInt8_eq, UInt8.reduceOfNat, add_zero,
    List.length_cons, accessEnc_length, zero_add, Nat.reduceAdd, Nat.reduceLT,
    UInt8.reduceAdd, List.cons_append, List.nil_append, List.append_nil, hp]
  decide +kernel

/-- **`txC`'s signature recovers `E`**, by kernel evaluation of the signing hash and of
secp256k1 recovery. -/
theorem txC_recoveredSender : recoverSender 0 txC = .ok eAddress := by
  rw [recoverSender, txC_signingHash]
  decide +kernel

end Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.TxC
