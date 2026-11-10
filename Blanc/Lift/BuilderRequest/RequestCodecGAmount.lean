import Blanc.Lift.BuilderRequest.RequestCodecG

/-!
# B2's endianness chain: a deposit record's amount, decoded

Goal `eip8282-gloas-cross-layer-v1`, frozen statements rev 3.1 (Plans `recon/statements.md` B2, F3).

A deposit record's `amount` is the 8 calldata bytes at offset 80, as submitted, read big-endian
(`Bytes.toNat`). The record the system call returns (`Deposit.Record.out`) carries those bytes reversed, so the
returned 184 bytes decode, as the fixed-size SSZ container `BuilderDepositRequest` (pubkey 48 ‖ credentials 32 ‖
amount 8 little-endian ‖ signature 96), to a request whose `amount` is the big-endian value of the record's
bytes (`depositRecord_amount`).

The control (`depositRecord_amount_byte_order`): `10^9` gwei (`0x3B9ACA00`) submitted big-endian is returned as
the little-endian bytes `00 CA 9A 3B 00 00 00 00`; SSZ decodes those to `10^9`, while reading them through the
big-endian `Bytes.toNat` gives `0x00CA9A3B00000000`.

`leNat_reverse`, `deserialize_u64_ok`, `deserialize_byteVector_ok` and `deserialize_builderDepositRequest` are
generic over Jaune's SSZ: hoist candidates for Jaune `SSZ/Basic.lean` / `SSZ/Container.lean`.
-/

namespace Blanc.Lift.BuilderRequest.RequestCodecG

open Jaune JauneConsensus ChainLink

/-! ## Generic SSZ facts (hoist candidates) -/

/-- Little-endian decoding of `l ++ [b]`. -/
theorem leNat_append_singleton : ∀ (l : Bytes) (b : UInt8),
    leNat (l ++ [b]) = leNat l + 256 ^ l.length * b.toNat
  | [], b => by simp only [List.nil_append, leNat, mul_zero, add_zero, List.length_nil, pow_zero, one_mul, zero_add]
  | x :: l, b => by
    simp only [List.cons_append, leNat, leNat_append_singleton l b, List.length_cons, Nat.pow_succ]
    ring

/-- The big-endian accumulator, in terms of little-endian decoding of the reversed bytes. -/
theorem toNat_aux_eq : ∀ (acc : Nat) (bs : Bytes),
    Bytes.toNat.aux acc bs = acc * 256 ^ bs.length + leNat bs.reverse
  | acc, [] => by simp only [Bytes.toNat.aux, List.length_nil, pow_zero, mul_one, List.reverse_nil, leNat, add_zero]
  | acc, b :: bs => by
    simp only [Bytes.toNat.aux, toNat_aux_eq _ bs, List.reverse_cons, leNat_append_singleton,
      List.length_reverse, List.length_cons, Nat.pow_succ]
    ring

/-- **Big-endian is little-endian of the reverse.** -/
theorem leNat_reverse (bs : Bytes) : leNat bs.reverse = Bytes.toNat bs := by
  rw [Bytes.toNat, toNat_aux_eq]
  simp only [zero_mul, zero_add]

/-- An 8-byte scope decodes as a `uint64` to its little-endian value. -/
theorem deserialize_u64_ok {bs : Bytes} (h : bs.length = 8) :
    ∃ x : U64, (Ssz.deserialize bs : M U64) = .ok x ∧ x.toNat = leNat bs := by
  have hlt : leNat bs < 2 ^ 64 := by have := leNat_lt bs; rw [h] at this; exact this
  refine ⟨U64.ofNatLt (leNat bs) hlt, ?_, ?_⟩
  · show (if h : bs.length = 8 then _ else _) = _
    simp only [h, ↓reduceDIte]
    rfl
  · show (leNat bs).toUInt64.toNat = leNat bs
    rw [Nat.toUInt64_eq, UInt64.toNat_ofNat', Nat.mod_eq_of_lt hlt]

/-- A pointwise-successful `mapM` succeeds. -/
theorem mapM_except_ok {α β ε : Type} (f : α → Except ε β) :
    ∀ l : List α, (∀ a ∈ l, ∃ b, f a = .ok b) → ∃ bs, l.mapM f = .ok bs ∧ bs.length = l.length
  | [], _ => ⟨[], rfl, rfl⟩
  | a :: l, h => by
    obtain ⟨b, hb⟩ := h a List.mem_cons_self
    obtain ⟨bs, hbs, hl⟩ := mapM_except_ok f l fun x hx => h x (List.mem_cons_of_mem _ hx)
    refine ⟨b :: bs, ?_, by simp only [List.length_cons, hl]⟩
    rw [List.mapM_cons, hb, hbs]
    rfl

/-- An `n`-byte scope (`n ≠ 0`) decodes as a byte vector of length `n`. -/
theorem deserialize_byteVector_ok {n : Nat} (hn : n ≠ 0) {bs : Bytes} (h : bs.length = n) :
    ∃ v : SszVector UInt8 n, (Ssz.deserialize bs : M (SszVector UInt8 n)) = .ok v := by
  rw [SszVector.deserialize_eq]
  simp only [hn, ↓reduceIte]
  have hfix : Ssz.fixedSize? UInt8 = some 1 := rfl
  obtain ⟨ys, hys, hl⟩ := mapM_except_ok
    (fun i => (Ssz.deserialize (slice bs.toArray (1 * i) (1 * (i + 1))) : M UInt8)) (List.range n)
    (fun i hi => by
      have hi' : i < bs.length := h ▸ List.mem_range.mp hi
      have : slice bs.toArray (1 * i) (1 * (i + 1)) = [bs[i]] := by
        rw [slice_eq_take_drop, Nat.one_mul, Nat.one_mul, Nat.add_sub_cancel_left, List.toList_toArray,
          List.drop_eq_getElem_cons hi', List.take_succ_cons, List.take_zero]
      exact ⟨bs[i], by rw [this]; rfl⟩)
  have hseq : deserializeSeq (α := UInt8) bs (some n) n = .ok ys.toArray := by
    unfold deserializeSeq deserializeSeqWith
    simp only [hfix, h, Nat.one_ne_zero, ↓reduceIte, Nat.mod_one, ne_eq, not_true_eq_false,
      Nat.div_one, bind, Except.bind, pure, Except.pure]
    rw [hys]
  rw [hseq]
  have hs : ys.toArray.size = n := by simp only [List.size_toArray, hl, List.length_range]
  exact ⟨⟨ys.toArray, hs⟩, by simp only [bind, Except.bind, hs, ↓reduceDIte]; rfl⟩

/-- **The fixed 184-byte `BuilderDepositRequest` layout decodes field by field.** -/
theorem deserialize_builderDepositRequest {pk cr am sg : Bytes} (hpk : pk.length = 48)
    (hcr : cr.length = 32) (ham : am.length = 8) (hsg : sg.length = 96) :
    ∃ req : Gloas.BuilderDepositRequest,
      (Ssz.deserialize (pk ++ cr ++ am ++ sg) : M Gloas.BuilderDepositRequest) = .ok req ∧
      (Ssz.deserialize am : M U64) = .ok req.amount := by
  obtain ⟨vpk, hvpk⟩ := deserialize_byteVector_ok (n := 48) (by decide) hpk
  obtain ⟨vsg, hvsg⟩ := deserialize_byteVector_ok (n := 96) (by decide) hsg
  obtain ⟨a, ha, -⟩ := deserialize_u64_ok ham
  have hlen : (pk ++ cr ++ am ++ sg).length = 184 := by simp only [List.append_assoc, List.length_append, hpk, hcr,
      ham, hsg, Nat.reduceAdd]
  have s0 : slice (pk ++ cr ++ am ++ sg).toArray 0 (0 + 48) = pk := by
    rw [slice_eq_take_drop]; simp only [zero_add, tsub_zero, List.append_assoc, List.drop_zero, hpk, List.take_left']
  have s1 : slice (pk ++ cr ++ am ++ sg).toArray (0 + 48) (0 + 48 + 32) = cr := by
    rw [slice_eq_take_drop]; simp only [zero_add, Nat.reduceAdd, Nat.reduceSub, List.append_assoc, hpk,
        List.drop_left', hcr, List.take_left']
  have s2 : slice (pk ++ cr ++ am ++ sg).toArray (0 + 48 + 32) (0 + 48 + 32 + 8) = am := by
    rw [slice_eq_take_drop]
    simp only [zero_add, Nat.reduceAdd, Nat.reduceSub, List.append_assoc, List.drop_append, hpk, Nat.reduceLeDiff,
      List.drop_eq_nil_of_le, hcr, List.nil_append, ham, List.drop_zero, List.take_left']
  have s3 : slice (pk ++ cr ++ am ++ sg).toArray (0 + 48 + 32 + 8) (0 + 48 + 32 + 8 + 96) = sg := by
    rw [slice_eq_take_drop]
    simp only [zero_add, Nat.reduceAdd, Nat.reduceSub, List.append_assoc, List.drop_append, hpk, Nat.reduceLeDiff,
      List.drop_eq_nil_of_le, hcr, List.nil_append, ham, List.drop_zero]
    exact List.take_of_length_le (by rw [hsg])
  refine ⟨⟨vpk, Bytes.toB256 cr, a, vsg⟩, ?_, ha⟩
  show (do
    let scopes ← splitContainer (pk ++ cr ++ am ++ sg)
      [Ssz.fixedSize? BLSPubkey, Ssz.fixedSize? Bytes32, Ssz.fixedSize? Gwei, Ssz.fixedSize? BLSSignature]
    StateT.run' (do
      let v ← (Gloas.BuilderDepositRequest.mk <$> nextField <*> nextField <*> nextField <*> nextField :
        FieldDecoder Gloas.BuilderDepositRequest)
      if (← get).isEmpty then pure v else throw (Reject.decode (.offset "extra fields"))) scopes) = _
  have hsplit : splitContainer (pk ++ cr ++ am ++ sg)
      [Ssz.fixedSize? BLSPubkey, Ssz.fixedSize? Bytes32, Ssz.fixedSize? Gwei, Ssz.fixedSize? BLSSignature] =
        .ok [pk, cr, am, sg] := by
    rw [show [Ssz.fixedSize? BLSPubkey, Ssz.fixedSize? Bytes32, Ssz.fixedSize? Gwei,
      Ssz.fixedSize? BLSSignature] = [some 48, some 32, some 8, some 96] from rfl]
    unfold splitContainer
    simp only [hlen, fixedPartLength, List.foldl, readFixedPart, offsetsOf, s0, s1, s2, s3]
    rfl
  rw [hsplit]
  have hcr' : (Ssz.deserialize cr : M Bytes32) = .ok (Bytes.toB256 cr) := by
    show (if cr.length = 32 then _ else _) = _
    simp only [hcr, ↓reduceIte]; rfl
  simp only [bind, Except.bind, StateT.run', Functor.map, Seq.seq, StateT.bind, StateT.map,
    nextField, get, set, getThe, MonadStateOf.get, MonadStateOf.set, StateT.get, StateT.set,
    StateT.lift, hvpk, hcr', ha, hvsg, List.isEmpty_nil, ↓reduceIte, pure, StateT.pure, Except.pure,
    Except.map]

/-! ## B2: the deposit record's amount -/

/-- **B2, F3: the endianness chain of a deposit record.** The record a kept frame at the deposit contract submits
carries, as its amount, the calldata's 8 bytes at offset 80 (big-endian, as submitted). The bytes the contract
returns for it decode, as a Gloas `BuilderDepositRequest`, to a request whose amount is the big-endian value of
those bytes, and that amount is the SSZ `uint64` decoding of the reversed (little-endian) bytes.

Adaptation: Jaune has no total `U64.ofNat`; the frozen `U64.ofNat (Bytes.toNat r.amount)` is stated through
`toNat` (`req.amount.toNat = Bytes.toNat r.amount`, which determines the `U64`), and the decoding of the reversed
bytes is stated equal to that same `req.amount`. -/
theorem depositRecord_amount (f : Exec.Frame) (r : Deposit.Record)
    (h : submittedBy Deposit.contract f = some r) :
    r.amount = f.sevm.data.sliceD 80 8 0 ∧
      ∃ req : Gloas.BuilderDepositRequest,
        (Ssz.deserialize (Deposit.Record.out r) : M Gloas.BuilderDepositRequest) = .ok req ∧
        req.amount.toNat = Bytes.toNat r.amount ∧
        (Ssz.deserialize r.amount.reverse : M U64) = .ok req.amount := by
  refine ⟨?_, ?_⟩
  · unfold submittedBy at h
    split at h
    · cases h; rfl
    · cases h
  · obtain ⟨req, hreq, ham⟩ := deserialize_builderDepositRequest r.pubkey_length r.credentials_length
      (by rw [List.length_reverse]; exact r.amount_length) r.signature_length
    obtain ⟨a, ha, hav⟩ := deserialize_u64_ok (bs := r.amount.reverse)
      (by rw [List.length_reverse]; exact r.amount_length)
    rw [ha] at ham
    obtain rfl : a = req.amount := Except.ok.inj ham
    exact ⟨req, hreq, by rw [hav, leNat_reverse], ha⟩

/-- `10^9` gwei as 8 big-endian bytes, as a submitter writes it (`0x000000003B9ACA00`). -/
def gweiBillionBE : Bytes := [0x00, 0x00, 0x00, 0x00, 0x3B, 0x9A, 0xCA, 0x00]

/-- **B2's byte-order control.** `10^9` gwei submitted big-endian is returned little-endian
(`00 CA 9A 3B 00 00 00 00`); SSZ decodes the returned bytes to `10^9`, but reading the same returned bytes
through the big-endian `Bytes.toNat` gives `0x00CA9A3B00000000 ≠ 10^9`. So a decoder that read `Record.out`'s
amount big-endian would credit the wrong amount; the real chain (`depositRecord_amount`) does not. -/
theorem depositRecord_amount_byte_order :
    Bytes.toNat gweiBillionBE = 10 ^ 9 ∧
      (∃ x : U64, (Ssz.deserialize gweiBillionBE.reverse : M U64) = .ok x ∧ x.toNat = 10 ^ 9) ∧
      Bytes.toNat gweiBillionBE.reverse = 0x00CA9A3B00000000 ∧
      Bytes.toNat gweiBillionBE.reverse ≠ 10 ^ 9 := by
  refine ⟨by decide, ?_, by decide, by decide⟩
  obtain ⟨x, hx, hv⟩ := deserialize_u64_ok (bs := gweiBillionBE.reverse) rfl
  exact ⟨x, hx, by rw [hv, leNat_reverse]; decide⟩

end Blanc.Lift.BuilderRequest.RequestCodecG
