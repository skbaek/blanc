-- RevertPayload.lean : compile-time constant `Error(string)` payloads.
--
-- This module is the shared, contract-independent bridge from an ABI reason
-- string to a `REVERT` whose output is exactly that encoding.  Existing
-- `Func.rev` remains the empty-data combinator; nothing here changes its bytes
-- or retrofits a deployed contract.

import Blanc.Reverts
import Blanc.ForwardCall
import Blanc.Ladder

namespace Blanc

open Jaune

/-! ## ABI encoding -/

/-- The ABI `Error(string)` returndata for `s`.

The selector is derived from its preimage, followed by the dynamic head,
UTF-8 byte length, and a zero-padded data tail.  Callers that need Solidity
compatibility must establish that the source string is ASCII: Blanc's existing
`String.toBytes` truncates non-ASCII characters to `UInt8`. -/
def errorData (s : String) : Bytes :=
  let data : Bytes := String.toBytes s
  let pad : Nat := (32 - data.length % 32) % 32
  (String.keccak "Error(string)").toBytes.take 4 ++
    (32 : B256).toBytes ++
    (Nat.toB256 data.length).toBytes ++
    data ++ List.replicate pad 0

/-! ## Constant-word emission -/

/-- Split a byte string into 32-byte words, padding only the final word.
The empty string has no words. -/
def bytesWords : Bytes → List B256
  | [] => []
  | b :: bs =>
      Bytes.toB256 ((b :: bs).take 32 ++
        List.replicate (32 - min 32 (b :: bs).length) 0)
        :: bytesWords ((b :: bs).drop 32)
termination_by xs => xs.length
decreasing_by
  simp only [List.length_drop, List.length_cons]
  omega

private lemma UInt64.high_concat32 (x y : UInt32) :
    ((((x.toUInt64 <<< 32) ||| y.toUInt64) >>> 32).toUInt32) = x := by
  rw [← UInt32.toNat_inj]
  rw [UInt64.toNat_toUInt32, UInt64.toNat_shiftRight]
  simp only [UInt64.toNat_or, UInt64.toNat_shiftLeft_lo]
  have widen (z : UInt32) : z.toUInt64.toNat = z.toNat := rfl
  have n32 : UInt64.toNat 32 % 64 = 32 := rfl
  rw [widen, widen, n32]
  have hx : x.toNat <<< 32 < 2 ^ 64 := by
    rw [Nat.shiftLeft_eq]
    have := UInt32.toNat_lt x
    norm_num at this ⊢
    omega
  unfold Nat.lo
  rw [Nat.mod_eq_of_lt hx, Nat.shiftRight_or_distrib,
    Nat.shiftLeft_shiftRight,
    Nat.shiftRight_eq_zero y.toNat 32 (UInt32.toNat_lt y), Nat.or_zero,
    Nat.mod_eq_of_lt (UInt32.toNat_lt x)]

private lemma UInt64.low_concat32 (x y : UInt32) :
    (((x.toUInt64 <<< 32) ||| y.toUInt64).toUInt32) = y := by
  rw [← UInt32.toNat_inj]
  rw [UInt64.toNat_toUInt32]
  simp only [UInt64.toNat_or, UInt64.toNat_shiftLeft_lo]
  have widen (z : UInt32) : z.toUInt64.toNat = z.toNat := rfl
  have n32 : UInt64.toNat 32 % 64 = 32 := rfl
  rw [widen, widen, n32]
  have hx : x.toNat <<< 32 < 2 ^ 64 := by
    rw [Nat.shiftLeft_eq]
    have := UInt32.toNat_lt x
    norm_num at this ⊢
    omega
  unfold Nat.lo
  rw [Nat.mod_eq_of_lt hx, Nat.or_mod_two_pow]
  simp only [Nat.shiftLeft_eq]
  rw [Nat.mul_comm, Nat.mul_mod_right,
    Nat.mod_eq_of_lt (UInt32.toNat_lt y), Nat.zero_or]

private lemma UInt32.high_concat16 (x y : UInt16) :
    ((((x.toUInt32 <<< 16) ||| y.toUInt32) >>> 16).toUInt16) = x := by
  rw [← UInt16.toNat_inj]
  rw [UInt32.toNat_toUInt16, UInt32.toNat_shiftRight]
  simp only [UInt32.toNat_or, UInt32.toNat_shiftLeft_lo]
  have widen (z : UInt16) : z.toUInt32.toNat = z.toNat := rfl
  have n16 : UInt32.toNat 16 % 32 = 16 := rfl
  rw [widen, widen, n16]
  have hx : x.toNat <<< 16 < 2 ^ 32 := by
    rw [Nat.shiftLeft_eq]
    have := UInt16.toNat_lt x
    norm_num at this ⊢
    omega
  unfold Nat.lo
  rw [Nat.mod_eq_of_lt hx, Nat.shiftRight_or_distrib,
    Nat.shiftLeft_shiftRight,
    Nat.shiftRight_eq_zero y.toNat 16 (UInt16.toNat_lt y), Nat.or_zero,
    Nat.mod_eq_of_lt (UInt16.toNat_lt x)]

private lemma UInt32.low_concat16 (x y : UInt16) :
    (((x.toUInt32 <<< 16) ||| y.toUInt32).toUInt16) = y := by
  rw [← UInt16.toNat_inj]
  rw [UInt32.toNat_toUInt16]
  simp only [UInt32.toNat_or, UInt32.toNat_shiftLeft_lo]
  have widen (z : UInt16) : z.toUInt32.toNat = z.toNat := rfl
  have n16 : UInt32.toNat 16 % 32 = 16 := rfl
  rw [widen, widen, n16]
  have hx : x.toNat <<< 16 < 2 ^ 32 := by
    rw [Nat.shiftLeft_eq]
    have := UInt16.toNat_lt x
    norm_num at this ⊢
    omega
  unfold Nat.lo
  rw [Nat.mod_eq_of_lt hx, Nat.or_mod_two_pow]
  simp only [Nat.shiftLeft_eq]
  rw [Nat.mul_comm, Nat.mul_mod_right,
    Nat.mod_eq_of_lt (UInt16.toNat_lt y), Nat.zero_or]

private lemma UInt16.high_concat8 (x y : UInt8) :
    ((((x.toUInt16 <<< 8) ||| y.toUInt16) >>> 8).toUInt8) = x := by
  rw [← UInt8.toNat_inj]
  rw [UInt16.toNat_toUInt8, UInt16.toNat_shiftRight]
  simp only [UInt16.toNat_or, UInt16.toNat_shiftLeft_lo]
  have widen (z : UInt8) : z.toUInt16.toNat = z.toNat := rfl
  have n8 : UInt16.toNat 8 % 16 = 8 := rfl
  rw [widen, widen, n8]
  have hx : x.toNat <<< 8 < 2 ^ 16 := by
    rw [Nat.shiftLeft_eq]
    have := UInt8.toNat_lt x
    norm_num at this ⊢
    omega
  unfold Nat.lo
  rw [Nat.mod_eq_of_lt hx, Nat.shiftRight_or_distrib,
    Nat.shiftLeft_shiftRight,
    Nat.shiftRight_eq_zero y.toNat 8 (UInt8.toNat_lt y), Nat.or_zero,
    Nat.mod_eq_of_lt (UInt8.toNat_lt x)]

private lemma UInt16.low_concat8 (x y : UInt8) :
    (((x.toUInt16 <<< 8) ||| y.toUInt16).toUInt8) = y := by
  rw [← UInt8.toNat_inj]
  rw [UInt16.toNat_toUInt8]
  simp only [UInt16.toNat_or, UInt16.toNat_shiftLeft_lo]
  have widen (z : UInt8) : z.toUInt16.toNat = z.toNat := rfl
  have n8 : UInt16.toNat 8 % 16 = 8 := rfl
  rw [widen, widen, n8]
  have hx : x.toNat <<< 8 < 2 ^ 16 := by
    rw [Nat.shiftLeft_eq]
    have := UInt8.toNat_lt x
    norm_num at this ⊢
    omega
  unfold Nat.lo
  rw [Nat.mod_eq_of_lt hx, Nat.or_mod_two_pow]
  simp only [Nat.shiftLeft_eq]
  rw [Nat.mul_comm, Nat.mul_mod_right,
    Nat.mod_eq_of_lt (UInt8.toNat_lt y), Nat.zero_or]

/-- Encoding eight bytes as a limb and decoding it again is exact. -/
lemma UInt64.toBytes_ofBytes (a b c d e f g h : UInt8) :
    (UInt64.ofBytes a b c d e f g h).toBytes = [a, b, c, d, e, f, g, h] := by
  rw [UInt64.ofBytes_eq_halves]
  simp only [UInt64.toBytes, UInt64.high_concat32, UInt64.low_concat32,
    UInt32.toBytes]
  rw [UInt32.ofBytes_eq_halves, UInt32.ofBytes_eq_halves]
  simp only [UInt32.high_concat16, UInt32.low_concat16, UInt16.toBytes,
    UInt16.ofBytes, UInt16.high_concat8, UInt16.low_concat8]
  simp

/-- The 32-byte codec is an exact round trip, in the concrete shape used by
`Bytes.toBytes_toB256_of_length`. -/
lemma Bytes.toBytes_toB256_32
    (a00 a01 a02 a03 a04 a05 a06 a07
     a08 a09 a10 a11 a12 a13 a14 a15
     a16 a17 a18 a19 a20 a21 a22 a23
     a24 a25 a26 a27 a28 a29 a30 a31 : UInt8) :
    (Bytes.toB256
      [a00, a01, a02, a03, a04, a05, a06, a07,
       a08, a09, a10, a11, a12, a13, a14, a15,
       a16, a17, a18, a19, a20, a21, a22, a23,
       a24, a25, a26, a27, a28, a29, a30, a31]).toBytes =
      [a00, a01, a02, a03, a04, a05, a06, a07,
       a08, a09, a10, a11, a12, a13, a14, a15,
       a16, a17, a18, a19, a20, a21, a22, a23,
       a24, a25, a26, a27, a28, a29, a30, a31] := by
  simp only [Bytes.toB256]
  rw [Bytes.toB256_go_eight_cons, Bytes.toB256_go_eight_cons,
      Bytes.toB256_go_eight_cons, Bytes.toB256_go_eight_cons]
  simp only [Bytes.toB256.go, B256.toBytes, B128.toBytes, List.append_assoc,
    UInt64.toBytes_ofBytes]
  simp

/-- `Bytes.toB256` loses no information on an exact word. -/
lemma Bytes.toBytes_toB256_of_length {xs : Bytes} (h : xs.length = 32) :
    (Bytes.toB256 xs).toBytes = xs := by
  rcases xs with _ | ⟨a00, xs⟩
  · simp at h
  rcases xs with _ | ⟨a01, xs⟩
  · simp at h
  rcases xs with _ | ⟨a02, xs⟩
  · simp at h
  rcases xs with _ | ⟨a03, xs⟩
  · simp at h
  rcases xs with _ | ⟨a04, xs⟩
  · simp at h
  rcases xs with _ | ⟨a05, xs⟩
  · simp at h
  rcases xs with _ | ⟨a06, xs⟩
  · simp at h
  rcases xs with _ | ⟨a07, xs⟩
  · simp at h
  rcases xs with _ | ⟨a08, xs⟩
  · simp at h
  rcases xs with _ | ⟨a09, xs⟩
  · simp at h
  rcases xs with _ | ⟨a10, xs⟩
  · simp at h
  rcases xs with _ | ⟨a11, xs⟩
  · simp at h
  rcases xs with _ | ⟨a12, xs⟩
  · simp at h
  rcases xs with _ | ⟨a13, xs⟩
  · simp at h
  rcases xs with _ | ⟨a14, xs⟩
  · simp at h
  rcases xs with _ | ⟨a15, xs⟩
  · simp at h
  rcases xs with _ | ⟨a16, xs⟩
  · simp at h
  rcases xs with _ | ⟨a17, xs⟩
  · simp at h
  rcases xs with _ | ⟨a18, xs⟩
  · simp at h
  rcases xs with _ | ⟨a19, xs⟩
  · simp at h
  rcases xs with _ | ⟨a20, xs⟩
  · simp at h
  rcases xs with _ | ⟨a21, xs⟩
  · simp at h
  rcases xs with _ | ⟨a22, xs⟩
  · simp at h
  rcases xs with _ | ⟨a23, xs⟩
  · simp at h
  rcases xs with _ | ⟨a24, xs⟩
  · simp at h
  rcases xs with _ | ⟨a25, xs⟩
  · simp at h
  rcases xs with _ | ⟨a26, xs⟩
  · simp at h
  rcases xs with _ | ⟨a27, xs⟩
  · simp at h
  rcases xs with _ | ⟨a28, xs⟩
  · simp at h
  rcases xs with _ | ⟨a29, xs⟩
  · simp at h
  rcases xs with _ | ⟨a30, xs⟩
  · simp at h
  rcases xs with _ | ⟨a31, xs⟩
  · simp at h
  cases xs with
  | nil =>
      simpa using (Bytes.toBytes_toB256_32 a00 a01 a02 a03 a04 a05 a06 a07
        a08 a09 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23
        a24 a25 a26 a27 a28 a29 a30 a31)
  | cons a32 xs => simp at h

/-- The byte image represented by the emitted words, including the final
word's right padding. -/
def bytesWordsBytes (bs : Bytes) : Bytes :=
  (bytesWords bs).flatMap B256.toBytes

/-- The emitted word image begins with the source bytes exactly. -/
lemma bytesWordsBytes_take (bs : Bytes) :
    (bytesWordsBytes bs).take bs.length = bs := by
  fun_induction bytesWords bs with
  | case1 => simp [bytesWordsBytes]
  | case2 b bs ih =>
      simp only [bytesWordsBytes, bytesWords, List.flatMap_cons]
      rw [Bytes.toBytes_toB256_of_length]
      · simp_all [bytesWordsBytes]
        by_cases hlen : bs.length ≤ 31
        · simp [List.take_of_length_le hlen]
        · simp only [min_eq_left (by omega : 32 ≤ bs.length + 1),
            min_eq_left (by omega : 31 ≤ bs.length), Nat.sub_self,
            List.replicate_zero, List.nil_append, List.take_append,
            List.length_take]
          rw [ih, List.take_of_length_le (by simp)]
          exact List.take_append_drop 31 bs
      · simp
        omega

/-- The represented image is a whole number of memory words. -/
lemma bytesWordsBytes_length (bs : Bytes) :
    (bytesWordsBytes bs).length = 32 * (bytesWords bs).length := by
  simp [bytesWordsBytes, B256.length_toBytes]
  omega

/-- The represented image covers the unpadded blob. -/
lemma bytesWordsBytes_covers (bs : Bytes) :
    bs.length ≤ (bytesWordsBytes bs).length := by
  have h := congrArg List.length (bytesWordsBytes_take bs)
  simp only [List.length_take] at h
  omega

/-! ## Reverse-store memory image -/

lemma List.takeD_length_add_append {α} (xs ys : List α) (m : Nat) (d : α) :
    List.takeD (xs.length + m) (xs ++ ys) d =
      xs ++ List.takeD m ys d := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      rw [show (x :: xs).length + m = (xs.length + m) + 1 by simp; omega]
      show (x :: (xs ++ ys)).head?.getD d ::
        List.takeD (xs.length + m) (x :: (xs ++ ys)).tail d = _
      rw [show (x :: (xs ++ ys)).tail = xs ++ ys from rfl, ih]
      rfl

/-- A write read from its own offset consists of the payload followed by the
corresponding read of the untouched suffix. -/
lemma Bytes.sliceD_writeAt_append (bs xs : Bytes) (n m : Nat) :
    (Bytes.writeAt bs n xs).sliceD n (xs.length + m) 0 =
      xs ++ bs.sliceD (n + xs.length) m 0 := by
  unfold List.sliceD
  rw [Bytes.writeAt, List.append_assoc,
    List.drop_append_of_le_length (by rw [List.takeD_length]),
    List.drop_eq_nil_of_le (by rw [List.takeD_length]), List.nil_append,
    List.takeD_length_add_append]

/-- The reader-level image obtained by the emitter's highest-first stores. -/
def Bytes.writeStoresRev (bs : Bytes) : List (B256 × Nat) → Bytes
  | [] => bs
  | iw :: iws =>
      Bytes.writeAt (writeStoresRev bs iws) (32 * iw.2) iw.1.toBytes

/-- Reading the window written by an indexed word list returns those words in
ascending index order, even though the stores execute highest first. -/
lemma Bytes.sliceD_writeStoresRev_zipIdx
    (img : Bytes) (ws : List B256) (k : Nat) :
    (Bytes.writeStoresRev img (ws.zipIdx k)).sliceD
        (32 * k) (32 * ws.length) 0 =
      ws.flatMap B256.toBytes := by
  induction ws generalizing k with
  | nil => rfl
  | cons w ws ih =>
      simp only [List.zipIdx_cons, Bytes.writeStoresRev, List.length_cons,
        List.flatMap_cons]
      rw [show 32 * (ws.length + 1) = w.toBytes.length + 32 * ws.length by
          rw [B256.length_toBytes]; omega,
        Bytes.sliceD_writeAt_append, B256.length_toBytes,
        show 32 * k + 32 = 32 * (k + 1) by omega, ih]

/-- The concrete memory produced by the emitter's highest-first stores. -/
def Mem.writeStoresRev (M : Mem) : List (B256 × Nat) → Mem
  | [] => M
  | iw :: iws => (writeStoresRev M iws).write (32 * iw.2) iw.1.toBytes

/-- Reverse stores preserve well-formedness and carry their reader-level image
over arbitrary prior memory content. -/
lemma Mem.writeStoresRev_inv {M : Mem} {img : Bytes}
    (iws : List (B256 × Nat)) (hwf : Mem.Wf M) (hr : Mem.Reads M img) :
    Mem.Wf (Mem.writeStoresRev M iws) ∧
      Mem.Reads (Mem.writeStoresRev M iws) (Bytes.writeStoresRev img iws) := by
  induction iws with
  | nil => exact ⟨hwf, hr⟩
  | cons iw iws ih =>
      exact ⟨Mem.Wf.write ih.1 _ _, Mem.Reads.write ih.1 ih.2 _ _⟩

lemma List.take_takeD_of_le {α} (xs : List α) (m n : Nat) (d : α)
    (h : m ≤ n) : (List.takeD n xs d).take m = List.takeD m xs d := by
  induction m generalizing n xs with
  | zero => rfl
  | succ m ih =>
      cases n with
      | zero => omega
      | succ n =>
          cases xs with
          | nil =>
              simp only [List.takeD_nil_eq_replicate, List.take_replicate,
                min_eq_left (by omega)]
          | cons x xs =>
              simp only [List.takeD, List.tail, List.take, List.cons.injEq]
              exact ⟨trivial, ih xs n (by omega)⟩

/-- After the aligned stores for `blob`, reading exactly its unpadded length
returns exactly `blob`, independently of the prior memory image. -/
lemma Mem.read_writeStoresRev_bytesWords {M : Mem} {img blob : Bytes}
    (hwf : Mem.Wf M) (hr : Mem.Reads M img) :
    ((Mem.writeStoresRev M (bytesWords blob).zipIdx).read 0 blob.length).1 =
      blob := by
  have hinv := Mem.writeStoresRev_inv (M := M) (img := img)
    (bytesWords blob).zipIdx hwf hr
  rw [Mem.Reads.read hinv.2]
  have hfull := Bytes.sliceD_writeStoresRev_zipIdx img (bytesWords blob) 0
  simp only [Nat.mul_zero] at hfull
  have hlen := bytesWordsBytes_length blob
  have hcov := bytesWordsBytes_covers blob
  unfold List.sliceD at hfull ⊢
  simp only [List.drop_zero] at hfull ⊢
  calc
    List.takeD blob.length
        (Bytes.writeStoresRev img (bytesWords blob).zipIdx) 0 =
        (List.takeD (32 * (bytesWords blob).length)
          (Bytes.writeStoresRev img (bytesWords blob).zipIdx) 0).take
            blob.length := by
          symm
          exact List.take_takeD_of_le _ _ _ _ (by omega)
    _ = (bytesWordsBytes blob).take blob.length := by
      simpa [bytesWordsBytes] using congrArg (List.take blob.length) hfull
    _ = blob := bytesWordsBytes_take blob

/-- One aligned constant-word store. -/
def prependStore (w : B256) (i : Nat) (rest : Func) : Func :=
  .next (Ninst.pushB256 w)
    (.next (Ninst.pushB256 (Nat.toB256 (32 * i)))
      (.next (Ninst.reg Rinst.mstore) rest))

/-- Prepend stores in reverse index order.  Writing the highest word first
charges memory expansion once; every later aligned word lies in that image. -/
def prependStoresRev : List (B256 × Nat) → Func → Func
  | [], rest => rest
  | iw :: iws, rest => prependStoresRev iws (prependStore iw.1 iw.2 rest)

/-- Revert with an arbitrary compile-time constant byte blob.

The words are written at `0, 32, ...`, highest first, then the exact (unpadded)
blob length and offset zero are supplied to `REVERT`. -/
def Func.revData (blob : Bytes) : Func :=
  prependStoresRev (bytesWords blob |>.zipIdx)
    (.next (Ninst.pushB256 (Nat.toB256 blob.length))
      (.next (Ninst.pushB256 0) (.last .rev)))

/-- Revert with an exact four-byte selector using a fixed-width `PUSH4`.

`MSTORE` right-aligns the pushed value in its word, so the final `(28, 4)`
window returns the original bytes without carrying a 32-byte immediate.  The
length proof fixes the compiled instruction width even when the selector starts
with zero. -/
def Func.revSelector (data : Bytes) (h : data.length = 4) : Func :=
  .next (.push data (by omega))
    (.next (Ninst.pushB256 0)
      (.next (Ninst.reg Rinst.mstore)
        (.next (Ninst.pushB256 4)
          (.next (Ninst.pushB256 28) (.last .rev)))))

/-- The compact selector reverter is exactly twelve bytes. -/
lemma Func.compsize_revSelector (data : Bytes) (h : data.length = 4) :
    compsize (Func.revSelector data h) = 12 := by
  have h0 : (Ninst.toBytes (Ninst.pushB256 0)).length = 1 := by
    rfl
  have h4 : (Ninst.toBytes (Ninst.pushB256 4)).length = 2 := by
    rfl
  have h28 : (Ninst.toBytes (Ninst.pushB256 28)).length = 2 := by
    rfl
  simp only [Func.revSelector, compsize]
  rw [h0, h4, h28]
  simp [Ninst.toBytes, pushToB8L, h]

/-- `Func.revData` specialized to ABI `Error(string)` returndata. -/
def Func.revWith (s : String) : Func := .revData (errorData s)

/-- A constant `Error(string)` reverter has no successful `Func.Run`.
`Func.Inv` makes the proof independent of the blob's computed word count: a
hypothetical successful terminal path would identify `True` with `False`. -/
theorem Func.not_run_revWith {fs : List Func} {sevm : Sevm} {d r : Devm}
    {reason : String} : ¬ Func.Run fs sevm d (Func.revWith reason) r := by
  have no_last : ∀ {s r : Devm},
      ¬ Func.Run fs sevm s (.last .rev) r := by
    intro s r run
    cases run with
    | last h_run =>
      simp only [Linst.Run, Linst.run] at h_run
      rcases Except.bind_eq_ok h_run with ⟨v1, h1, h2⟩
      rcases Except.bind_eq_ok h2 with ⟨v2, h3, h4⟩
      rcases Except.bind_eq_ok h4 with ⟨v3, h5, h6⟩
      contradiction
  have no_stores :
      ∀ (iws : List (B256 × Nat)) (rest : Func),
        (∀ {s r : Devm}, ¬ Func.Run fs sevm s rest r) →
        ∀ {s r : Devm},
          ¬ Func.Run fs sevm s (prependStoresRev iws rest) r := by
    intro iws
    induction iws with
    | nil =>
      intro rest h s r run
      exact h run
    | cons iw iws ih =>
      intro rest h
      simp only [prependStoresRev]
      apply ih
      intro s r run
      unfold prependStore at run
      rcases of_run_next run with ⟨s1, h1, run1⟩
      rcases of_run_next run1 with ⟨s2, h2, run2⟩
      rcases of_run_next run2 with ⟨s3, h3, run3⟩
      exact h run3
  unfold Func.revWith Func.revData
  apply no_stores
  intro s r run
  rcases of_run_next run with ⟨s1, h1, run1⟩
  rcases of_run_next run1 with ⟨s2, h2, run2⟩
  exact no_last run2

/-- Revert with the complete returndata from the immediately preceding call.

The second `RETURNDATASIZE` avoids retaining a fourth live stack word across
`RETURNDATACOPY`; this is also one gas cheaper than saving the length with
`DUP1`.  A zero-length child revert is therefore the ordinary empty revert. -/
def Func.revReturnData : Func :=
  Ninst.retdatasize :::
  Ninst.pushB256 0 :::
  Ninst.pushB256 0 :::
  Ninst.retdatacopy :::
  Ninst.retdatasize :::
  Ninst.pushB256 0 :::
  .last .rev

/-- Exact frame-local cost of `Func.revSelector`. -/
def revSelectorCost (devm : Devm) : Nat :=
  4 * gVerylow + gBase + devm.extCost [⟨0, 32⟩]

/-- Exact frame-local cost of `Func.revReturnData` at its entry state. -/
def revReturnDataCost (devm : Devm) : Nat :=
  5 * gBase + gVerylow +
    gReturnDataCopy * ceilDiv devm.returnData.length 32 +
    devm.extCost [⟨0, devm.returnData.length⟩]

/-! ## Exact-cost store walk -/

/-- The memory-expansion part of an access, exposed at `Mem` altitude. -/
def Mem.expansionCost (M : Mem) (i n : Nat) : Nat :=
  calculateMemoryGasCost (memExtSize M.size i n) -
    calculateMemoryGasCost M.size

/-- The exact cost of one emitted constant-word store against memory `M`. -/
def storeCost (M : Mem) (iw : B256 × Nat) : Nat :=
  pushCost iw.1.toBytes.sig +
  pushCost (Nat.toB256 (32 * iw.2)).toBytes.sig +
  gVerylow + Blanc.Mem.expansionCost M (32 * iw.2) 32

/-- The exact cost of the highest-first store sequence. -/
def storesRevCost (M : Mem) : List (B256 × Nat) → Nat
  | [] => 0
  | iw :: iws =>
      storesRevCost M iws + storeCost (Mem.writeStoresRev M iws) iw

/-- Execute the highest-first constant stores, handing their exact written
memory and remaining gas to a continuation. -/
lemma Func.runCompiledTo_prependStoresRev {fs : List Func} {sevm : Sevm}
    {devm : Devm} {M : Mem} {iws : List (B256 × Nat)} {rest : Func}
    {ex : Execution} {G : Nat}
    (h_mem : devm.memory = M)
    (h_gas : devm.gasLeft = G + storesRevCost M iws)
    (h_room : devm.stack.length < 1023)
    (h_bound : ∀ iw ∈ iws, 32 * iw.2 < 2 ^ 256)
    (h_next : Func.RunCompiledTo fs sevm
      (devm.setMach ⟨devm.stack, Mem.writeStoresRev M iws, G⟩) rest ex) :
    Func.RunCompiledTo fs sevm devm (prependStoresRev iws rest) ex := by
  induction iws generalizing devm G rest with
  | nil =>
      simp only [storesRevCost, Mem.writeStoresRev, prependStoresRev,
        Nat.add_zero] at h_gas h_next ⊢
      rw [← h_mem, ← h_gas] at h_next
      convert h_next using 1
      apply Devm.eq_of_proj <;> rfl
  | cons iw iws ih =>
      let Mt := Mem.writeStoresRev M iws
      let e := Blanc.Mem.expansionCost Mt (32 * iw.2) 32
      let cw := pushCost iw.1.toBytes.sig
      let ci := pushCost (Nat.toB256 (32 * iw.2)).toBytes.sig
      have hb : 32 * iw.2 < 2 ^ 256 := h_bound iw (by simp)
      have htail := ih h_mem
        (G := G + (cw + ci + gVerylow + e))
        (rest := prependStore iw.1 iw.2 rest)
        (by
          simp only [storesRevCost, storeCost] at h_gas ⊢
          dsimp only [Mt, e, cw, ci] at h_gas ⊢
          omega)
        h_room (fun x hx => h_bound x (by simp [hx])) ?_
      · simpa only [prependStoresRev] using htail
      · refine Func.RunCompiledTo.next
          (Ninst.runCompiled_pushB256 (c := cw)
            (G := G + (ci + gVerylow + e)) (by rfl)
            (by simp only [Devm.gasLeft_setMach]; omega)
            (by simp only [Devm.stack_setMach]; omega)) ?_
        refine Func.RunCompiledTo.next
          (Ninst.runCompiled_pushB256
            (devm := (devm.setMach
              ⟨devm.stack, Mem.writeStoresRev M iws,
                G + (cw + ci + gVerylow + e)⟩).setMach
              ⟨iw.1 :: devm.stack, Mem.writeStoresRev M iws,
                G + (ci + gVerylow + e)⟩)
            (c := ci) (G := G + (gVerylow + e)) (by rfl)
            (by simp only [Devm.gasLeft_setMach]; omega)
            (by simp only [Devm.stack_setMach, List.length_cons]; omega)) ?_
        simp only [Devm.setMach_setMach]
        have hoff : (Nat.toB256 (32 * iw.2)).toNat = 32 * iw.2 :=
          B256.toNat_toB256_of_lt hb
        refine Func.RunCompiledTo.next
          (Ninst.runCompiled_mstore_of
            (i := Nat.toB256 (32 * iw.2)) (v := iw.1) (s := devm.stack)
            (G := G) (e := e) (M := Mem.writeStoresRev M (iw :: iws))
            rfl ?_ rfl ?_) ?_
        · simp only [Devm.extCost, Devm.memory_setMach, memExtsSize, hoff]
          rfl
        · simp only [Devm.memory_setMach, Mem.writeStoresRev, hoff]
        · simpa only [Devm.setMach_setMach] using h_next

/-- A four-byte value occupies the last four bytes of its `B256` image. -/
private lemma Bytes.toB256_toBytes_drop28_of_length_four
    (data : Bytes) (h : data.length = 4) :
    data.toB256.toBytes.drop 28 = data := by
  have hp := Bytes.toBytes_toB256_of_length
    (xs := List.replicate 28 0 ++ data) (by simp [h])
  exact (by
    simpa [Bytes.toB256_zero_cons] using congrArg (List.drop 28) hp)

/-- Reading the low four bytes of the selector word returns the exact input,
independently of the prior memory image. -/
private lemma Bytes.sliceD_writeAt_selector
    (img data : Bytes) (h : data.length = 4) :
    (Bytes.writeAt img 0 data.toB256.toBytes).sliceD 28 4 0 = data := by
  rw [List.sliceD_eq_map]
  apply List.ext_getElem
  · simp [h]
  · intro i h₁ h₂
    simp only [List.getElem_map, List.getElem_range]
    rw [Bytes.getD_writeAt, if_pos (by
      simp only [Nat.zero_le, true_and, B256.length_toBytes]
      omega)]
    have hd := congrArg (fun bs : Bytes => bs.getD i 0)
      (Bytes.toB256_toBytes_drop28_of_length_four data h)
    rw [List.getD_drop] at hd
    simpa [List.getD_eq_getElem?_getD, h₂] using hd

/-- A word write preserves word alignment of the logical memory size. -/
lemma Mem.aligned_write_word {M : Mem} {i : Nat} {w : B256}
    (h : M.size % 32 = 0) : (M.write i w.toBytes).size % 32 = 0 := by
  rw [Mem.size_write_word_at]
  split
  · exact h
  · rw [ceil32_eq_mul]
    omega

/-- The compact selector emitter reverts with exactly its four input bytes,
with exact gas and final memory for an arbitrary aligned prior image. -/
lemma Func.runCompiledTo_revSelector {fs : List Func} {sevm : Sevm}
    {devm : Devm} {data img : Bytes} {G : Nat}
    (hlen : data.length = 4)
    (hwf : Mem.Wf devm.memory) (hr : Mem.Reads devm.memory img)
    (halign : devm.memory.size % 32 = 0)
    (h_gas : devm.gasLeft = G + revSelectorCost devm)
    (h_room : devm.stack.length < 1023) :
    Func.RunCompiledTo fs sevm devm (Func.revSelector data hlen)
      (.error (.revert,
        (devm.setMach ⟨devm.stack,
          devm.memory.write 0 data.toB256.toBytes, G⟩).withOutput data)) := by
  let w := data.toB256
  let M' := devm.memory.write 0 w.toBytes
  let e := devm.extCost [⟨0, 32⟩]
  have hdata : data ≠ [] := by
    intro hd
    rw [hd] at hlen
    simp at hlen
  have hpush : pushCost data = gVerylow := by
    simp [pushCost, hdata]
  have hn4 : Nat.toB256 4 ≠ 0 := by
    intro hz
    have hh := congrArg B256.toNat hz
    rw [B256.toNat_toB256_of_lt (by norm_num), B256.toNat_zero] at hh
    omega
  have hn28 : Nat.toB256 28 ≠ 0 := by
    intro hz
    have hh := congrArg B256.toNat hz
    rw [B256.toNat_toB256_of_lt (by norm_num), B256.toNat_zero] at hh
    omega
  have hc4 : pushCost (Nat.toB256 4).toBytes.sig = gVerylow :=
    pushCost_of_ne_zero hn4
  have hc28 : pushCost (Nat.toB256 28).toBytes.sig = gVerylow :=
    pushCost_of_ne_zero hn28
  change Func.RunCompiledTo fs sevm devm
    (.next (.push data _) (.next (Ninst.pushB256 0)
      (.next (Ninst.reg Rinst.mstore)
        (.next (Ninst.pushB256 4)
          (.next (Ninst.pushB256 28) (.last .rev)))))) _
  refine Func.RunCompiledTo.next
    (Ninst.runCompiled_pushBytes (c := gVerylow)
      (G := G + (3 * gVerylow + gBase + e)) hpush ?_ (by omega)) ?_
  · unfold revSelectorCost at h_gas
    dsimp only [e] at h_gas ⊢
    omega
  · refine Func.RunCompiledTo.next
      (Ninst.runCompiled_pushB256 (w := 0) (c := gBase)
        (G := G + (3 * gVerylow + e)) pushCost_zero
        (by simp only [Devm.gasLeft_setMach]; omega)
        (by simp only [Devm.stack_setMach, List.length_cons]; omega)) ?_
    simp only [Devm.setMach_setMach]
    refine Func.RunCompiledTo.next
      (Ninst.runCompiled_mstore_of
        (i := 0) (v := w) (s := devm.stack)
        (G := G + 2 * gVerylow) (e := e) (M := M') rfl ?_ ?_ rfl) ?_
    · dsimp only [e]
      simp only [Devm.extCost, Devm.memory_setMach, B256.toNat_zero]
    · simp only [Devm.gasLeft_setMach]
      omega
    · simp only [Devm.setMach_setMach]
      refine Func.RunCompiledTo.next
        (Ninst.runCompiled_pushB256 (w := 4) (c := gVerylow)
          (G := G + gVerylow) hc4
          (by simp only [Devm.gasLeft_setMach]; omega)
          (by simp only [Devm.stack_setMach]; omega)) ?_
      simp only [Devm.setMach_setMach]
      refine Func.RunCompiledTo.next
        (Ninst.runCompiled_pushB256 (w := 28) (c := gVerylow)
          (G := G) hc28
          (by simp only [Devm.gasLeft_setMach])
          (by simp only [Devm.stack_setMach, List.length_cons]; omega)) ?_
      simp only [Devm.setMach_setMach]
      have h4nat : (Nat.toB256 4).toNat = 4 :=
        B256.toNat_toB256_of_lt (by norm_num)
      have h28nat : (Nat.toB256 28).toNat = 28 :=
        B256.toNat_toB256_of_lt (by norm_num)
      have ha : M'.size % 32 = 0 := by
        dsimp only [M']
        exact Mem.aligned_write_word halign
      have hc : 32 ≤ M'.size := by
        dsimp only [M']
        rw [Mem.size_write_word_at]
        split
        case isTrue h => omega
        case isFalse h => exact Nat.le_ceil32 _
      have hcover : 28 + 4 ≤ M'.size := by omega
      have hinv := Mem.Reads.write hwf hr 0 w.toBytes
      have hout : (M'.read 28 4).1 = data := by
        rw [Mem.Reads.read hinv]
        exact Bytes.sliceD_writeAt_selector img data hlen
      have himg : (M'.read 28 4).2 = M' :=
        Mem.read_snd_eq_self (memExtSize_of_le ha hcover)
      have hread :
          (devm.setMach ⟨devm.stack, M', G⟩).memRead 28 4 =
            ⟨data, devm.setMach ⟨devm.stack, M', G⟩⟩ := by
        apply Prod.ext hout
        show (devm.setMach ⟨devm.stack, M', G⟩).withMemory
            (M'.read 28 4).2 = devm.setMach ⟨devm.stack, M', G⟩
        rw [himg]
        apply Devm.eq_of_proj <;> rfl
      exact Func.runCompiledTo_rev_of
        (i := Nat.toB256 28) (sz := Nat.toB256 4) (s := devm.stack)
        (G := G) (e := 0) (out := data)
        (d' := devm.setMach ⟨devm.stack, M', G⟩)
        rfl
        (by
          simp only [h28nat, h4nat, Devm.extCost, Devm.memory_setMach,
            memExtsSize]
          change Mem.expansionCost M' 28 4 = 0
          unfold Mem.expansionCost
          rw [memExtSize_of_le ha hcover, Nat.sub_self])
        rfl
        (by simpa only [h28nat, h4nat, Devm.setMach_setMach,
          Devm.stack_setMach, Devm.memory_setMach] using hread)

/-- Every store sequence emitted here preserves logical-size alignment. -/
lemma Mem.aligned_writeStoresRev {M : Mem} {iws : List (B256 × Nat)}
    (h : M.size % 32 = 0) :
    (Mem.writeStoresRev M iws).size % 32 = 0 := by
  induction iws with
  | nil => exact h
  | cons iw iws ih => exact Mem.aligned_write_word ih

/-- A nonempty indexed word sequence covers its complete aligned window. -/
lemma Mem.size_writeStoresRev_zipIdx_of_ne_nil
    (M : Mem) (ws : List B256) (k : Nat) (hne : ws ≠ []) :
    32 * (k + ws.length) ≤
      (Mem.writeStoresRev M (ws.zipIdx k)).size := by
  induction ws generalizing k with
  | nil => exact absurd rfl hne
  | cons w ws ih =>
      simp only [List.zipIdx_cons, Mem.writeStoresRev, List.length_cons]
      by_cases ht : ws = []
      · subst ws
        simp only [List.zipIdx_nil, Mem.writeStoresRev, List.length_nil,
          Nat.zero_add]
        rw [Mem.size_write_word_at]
        split
        · omega
        · exact Nat.le_ceil32 _
      · have hc := ih (k := k + 1) ht
        rw [Mem.size_write_of_le (show 32 * k + w.toBytes.length ≤
            (Mem.writeStoresRev M (ws.zipIdx (k + 1))).size by
          rw [B256.length_toBytes]; omega)]
        convert hc using 1
        all_goals omega

/-- The tail window and the whole window have the same end, hence the same
expansion charge when the tail is nonempty. -/
lemma Mem.expansionCost_tail_eq_full (M : Mem) (k n : Nat) (hn : 0 < n) :
    Mem.expansionCost M (32 * (k + 1)) (32 * n) =
      Mem.expansionCost M (32 * k) (32 * (n + 1)) := by
  unfold Mem.expansionCost
  congr 2
  unfold memExtSize
  simp only [Nat.mul_eq_zero, OfNat.ofNat_ne_zero, false_or,
    Nat.ne_of_gt hn, ↓reduceIte]
  congr 2
  rw [show 32 * (k + 1) + 32 * n = 32 * k + 32 * (n + 1) by omega]

/-- Once a nonempty higher tail has run, its lower predecessor is an
inside-image write and pays no further expansion. -/
lemma Mem.expansionCost_writeStoresRev_lower_zero
    (M : Mem) (ws : List B256) (k : Nat)
    (halign : M.size % 32 = 0) (hne : ws ≠ []) :
    Mem.expansionCost (Mem.writeStoresRev M (ws.zipIdx (k + 1)))
      (32 * k) 32 = 0 := by
  have ha := Mem.aligned_writeStoresRev
    (iws := ws.zipIdx (k + 1)) halign
  have hc := Mem.size_writeStoresRev_zipIdx_of_ne_nil M ws (k + 1) hne
  unfold Mem.expansionCost
  rw [memExtSize_of_le ha (by omega), Nat.sub_self]

/-- The fixed instruction cost of a highest-first constant-store sequence. -/
def storesFixedCost : List (B256 × Nat) → Nat
  | [] => 0
  | iw :: iws => storesFixedCost iws +
      pushCost iw.1.toBytes.sig +
      pushCost (Nat.toB256 (32 * iw.2)).toBytes.sig + gVerylow

/-- All per-store expansion charges telescope to the single complete aligned
window charge. -/
lemma storesRevCost_zipIdx (M : Mem) (ws : List B256) (k : Nat)
    (halign : M.size % 32 = 0) :
    storesRevCost M (ws.zipIdx k) =
      storesFixedCost (ws.zipIdx k) +
        Mem.expansionCost M (32 * k) (32 * ws.length) := by
  induction ws generalizing k with
  | nil =>
      simp [storesRevCost, storesFixedCost, Mem.expansionCost, memExtSize]
  | cons w ws ih =>
      simp only [List.zipIdx_cons, storesRevCost, storesFixedCost, storeCost]
      by_cases hnil : ws = []
      · subst ws
        simp [storesRevCost, storesFixedCost, Mem.writeStoresRev]
      · have hi := ih (k := k + 1)
        have hz := Mem.expansionCost_writeStoresRev_lower_zero
          M ws k halign hnil
        have he := Mem.expansionCost_tail_eq_full M k ws.length
          (List.length_pos_iff.mpr hnil)
        simp only [List.length_cons] at *
        omega

/-- Reading the payload window after its complete store sequence needs no
further memory expansion. -/
lemma Mem.expansionCost_writeStoresRev_blob_zero
    (M : Mem) (blob : Bytes) (halign : M.size % 32 = 0) :
    Mem.expansionCost
      (Mem.writeStoresRev M (bytesWords blob).zipIdx) 0 blob.length = 0 := by
  by_cases hb : blob = []
  · subst blob
    simp [bytesWords, Mem.writeStoresRev, Mem.expansionCost, memExtSize]
  · have hw : bytesWords blob ≠ [] := by
      cases blob with
      | nil => contradiction
      | cons b bs => simp [bytesWords]
    have ha := Mem.aligned_writeStoresRev
      (iws := (bytesWords blob).zipIdx) halign
    have hc := Mem.size_writeStoresRev_zipIdx_of_ne_nil M (bytesWords blob) 0 hw
    have hp := bytesWordsBytes_covers blob
    have hl := bytesWordsBytes_length blob
    unfold Mem.expansionCost
    rw [memExtSize_of_le ha (by omega), Nat.sub_self]

/-- `revData blob` emits a gas-exact constant-store program whose revert output
is exactly `blob`.

This is a single compiled-code execution claim at message-call/code-frame
altitude. It is not an exhaustiveness theorem, makes no claim about callee
behavior, and does not state transaction-level rollback. The memory hypotheses
permit arbitrary prior contents: `Wf` and `Reads` describe that memory image,
while word alignment makes the one-window expansion-cost equation exact. The
two numeric bounds are precisely the `B256` representability obligations for
the revert length and emitted store offsets. -/
lemma Func.runCompiledTo_revData {fs : List Func} {sevm : Sevm}
    {devm : Devm} {blob img : Bytes} {G : Nat}
    (hwf : Mem.Wf devm.memory) (hr : Mem.Reads devm.memory img)
    (halign : devm.memory.size % 32 = 0)
    (h_blob : blob.length < 2 ^ 256)
    (h_words : 32 * (bytesWords blob).length < 2 ^ 256)
    (h_gas : devm.gasLeft =
      G + (storesFixedCost (bytesWords blob).zipIdx +
        pushCost (Nat.toB256 blob.length).toBytes.sig + gBase +
        devm.extCost [⟨0, 32 * (bytesWords blob).length⟩]))
    (h_room : devm.stack.length < 1023) :
    Func.RunCompiledTo fs sevm devm (Func.revData blob)
      (.error (.revert,
        (devm.setMach ⟨devm.stack,
          Mem.writeStoresRev devm.memory (bytesWords blob).zipIdx, G⟩).withOutput
            blob)) := by
  let ws := bytesWords blob
  let M' := Mem.writeStoresRev devm.memory ws.zipIdx
  let clen := pushCost (Nat.toB256 blob.length).toBytes.sig
  have hcost := storesRevCost_zipIdx devm.memory ws 0 halign
  have hext : devm.extCost [⟨0, 32 * ws.length⟩] =
      Mem.expansionCost devm.memory 0 (32 * ws.length) := rfl
  have hbound : ∀ iw ∈ ws.zipIdx, 32 * iw.2 < 2 ^ 256 := by
    intro iw hi
    have hm : ws[iw.2]? = some iw.1 :=
      (List.mk_mem_zipIdx_iff_getElem?).mp hi
    have hlt : iw.2 < ws.length := (List.getElem?_eq_some_iff).mp hm |>.1
    change 32 * ws.length < 2 ^ 256 at h_words
    omega
  change Func.RunCompiledTo fs sevm devm
    (prependStoresRev ws.zipIdx
      (.next (Ninst.pushB256 (Nat.toB256 blob.length))
        (.next (Ninst.pushB256 0) (.last .rev)))) _
  refine Func.runCompiledTo_prependStoresRev
    (G := G + (clen + gBase)) rfl ?_ h_room hbound ?_
  · dsimp only [ws, clen] at hcost hext h_gas ⊢
    simp only [Nat.mul_zero] at hcost
    omega
  · refine Func.RunCompiledTo.next
      (Ninst.runCompiled_pushB256 (c := clen) (G := G + gBase) rfl
        (by simp only [Devm.gasLeft_setMach]; omega)
        (by simp only [Devm.stack_setMach]; omega)) ?_
    refine Func.RunCompiledTo.next
      (Ninst.runCompiled_pushB256
        (devm := (devm.setMach
          ⟨devm.stack, M', G + (clen + gBase)⟩).setMach
          ⟨Nat.toB256 blob.length :: devm.stack, M', G + gBase⟩)
        (c := gBase) (G := G) pushCost_zero rfl
        (by simp only [Devm.stack_setMach, List.length_cons]; omega)) ?_
    simp only [Devm.setMach_setMach]
    have hlen : (Nat.toB256 blob.length).toNat = blob.length :=
      B256.toNat_toB256_of_lt h_blob
    have he0 := Mem.expansionCost_writeStoresRev_blob_zero
      devm.memory blob halign
    have hext0 :
        (devm.setMach ⟨(0 : B256) :: Nat.toB256 blob.length :: devm.stack,
          M', G⟩).extCost [⟨0, (Nat.toB256 blob.length).toNat⟩] = 0 := by
      simp only [Devm.extCost, Devm.memory_setMach, memExtsSize, hlen]
      exact he0
    have hout :
        ((devm.setMach ⟨devm.stack, M', G⟩).memRead 0 blob.length).1 = blob := by
      show (M'.read 0 blob.length).1 = blob
      exact Mem.read_writeStoresRev_bytesWords hwf hr
    have ha : M'.size % 32 = 0 :=
      Mem.aligned_writeStoresRev (iws := ws.zipIdx) halign
    have hc : blob.length ≤ M'.size := by
      by_cases hb : blob = []
      · subst blob; simp
      · have hw : ws ≠ [] := by
          dsimp only [ws]
          cases blob with
          | nil => contradiction
          | cons b bs => simp [bytesWords]
        have hcov := Mem.size_writeStoresRev_zipIdx_of_ne_nil
          devm.memory ws 0 hw
        have hp := bytesWordsBytes_covers blob
        have hl := bytesWordsBytes_length blob
        change (bytesWordsBytes blob).length = 32 * ws.length at hl
        change blob.length ≤
          (Mem.writeStoresRev devm.memory ws.zipIdx).size
        omega
    have himg : (M'.read 0 blob.length).2 = M' :=
      Mem.read_snd_eq_self (memExtSize_of_le ha (by omega))
    have hread :
        (devm.setMach ⟨devm.stack, M', G⟩).memRead 0 blob.length =
          ⟨blob, devm.setMach ⟨devm.stack, M', G⟩⟩ := by
      apply Prod.ext hout
      show (devm.setMach ⟨devm.stack, M', G⟩).withMemory
          (M'.read 0 blob.length).2 =
        devm.setMach ⟨devm.stack, M', G⟩
      rw [himg]
      apply Devm.eq_of_proj <;> rfl
    exact Func.runCompiledTo_rev_of
      (i := 0) (sz := Nat.toB256 blob.length) (s := devm.stack)
      (G := G) (e := 0) (out := blob)
      (d' := devm.setMach ⟨devm.stack, M', G⟩)
      rfl hext0 rfl (by simpa only [hlen, B256.toNat_zero,
        Devm.setMach_setMach,
        Devm.stack_setMach, Devm.memory_setMach] using hread)

/-- The exact-output theorem specialized to the string-encoding emitter. -/
lemma Func.runCompiledTo_revWith {fs : List Func} {sevm : Sevm}
    {devm : Devm} {s : String} {img : Bytes} {G : Nat}
    (hwf : Mem.Wf devm.memory) (hr : Mem.Reads devm.memory img)
    (halign : devm.memory.size % 32 = 0)
    (h_blob : (errorData s).length < 2 ^ 256)
    (h_words : 32 * (bytesWords (errorData s)).length < 2 ^ 256)
    (h_gas : devm.gasLeft =
      G + (storesFixedCost (bytesWords (errorData s)).zipIdx +
        pushCost (Nat.toB256 (errorData s).length).toBytes.sig + gBase +
        devm.extCost [⟨0, 32 * (bytesWords (errorData s)).length⟩]))
    (h_room : devm.stack.length < 1023) :
    Func.RunCompiledTo fs sevm devm (Func.revWith s)
      (.error (.revert,
        (devm.setMach ⟨devm.stack,
          Mem.writeStoresRev devm.memory (bytesWords (errorData s)).zipIdx,
          G⟩).withOutput (errorData s))) := by
  simpa only [Func.revWith] using
    Func.runCompiledTo_revData hwf hr halign h_blob h_words h_gas h_room

/-- `revReturnData` copies and reverts with the preceding call's complete
returndata, with exact gas and final memory.

The length bound is exactly the `B256` round-trip needed by both
`RETURNDATASIZE` instructions.  The memory-image hypotheses establish that the
copied window reads back byte-for-byte; alignment makes the final `REVERT`'s
already-covered window cost zero. -/
lemma Func.runCompiledTo_revReturnData {fs : List Func} {sevm : Sevm}
    {devm : Devm} {img : Bytes} {G : Nat}
    (hwf : Mem.Wf devm.memory) (hr : Mem.Reads devm.memory img)
    (halign : devm.memory.size % 32 = 0)
    (h_len : devm.returnData.length < 2 ^ 256)
    (h_gas : devm.gasLeft = G + revReturnDataCost devm)
    (h_room : devm.stack.length < 1022) :
    Func.RunCompiledTo fs sevm devm Func.revReturnData
      (.error (.revert,
        (devm.setMach ⟨devm.stack,
          devm.memory.write 0 devm.returnData, G⟩).withOutput
            devm.returnData)) := by
  let n := devm.returnData.length
  let w := Nat.toB256 n
  let c := gVerylow + gReturnDataCopy * ceilDiv n 32 +
    devm.extCost [⟨0, n⟩]
  let M' := devm.memory.write 0 devm.returnData
  have hw : w.toNat = n := B256.toNat_toB256_of_lt h_len
  change Func.RunCompiledTo fs sevm devm
    (Ninst.retdatasize :::
      Ninst.pushB256 0 :::
      Ninst.pushB256 0 :::
      Ninst.retdatacopy :::
      Ninst.retdatasize :::
      Ninst.pushB256 0 :::
      .last .rev) _
  refine Func.RunCompiledTo.next
    (Ninst.runCompiled_pushItem (r := .retdatasize) (x := w)
      (cost := gBase) (G := G + (4 * gBase + c))
      (by rintro ⟨⟩) rfl ?_ (by omega)) ?_
  · unfold revReturnDataCost at h_gas
    dsimp only [n, c] at h_gas ⊢
    omega
  · refine Func.RunCompiledTo.next
      (Ninst.runCompiled_pushB256 (w := 0) (c := gBase)
        (G := G + (3 * gBase + c)) pushCost_zero
        (by simp only [Devm.gasLeft_setMach]; omega)
        (by simp only [Devm.stack_setMach, List.length_cons]; omega)) ?_
    simp only [Devm.setMach_setMach]
    refine Func.RunCompiledTo.next
      (Ninst.runCompiled_pushB256 (w := 0) (c := gBase)
        (G := G + (2 * gBase + c)) pushCost_zero
        (by simp only [Devm.gasLeft_setMach]; omega)
        (by simp only [Devm.stack_setMach, List.length_cons]; omega)) ?_
    simp only [Devm.setMach_setMach]
    refine Func.RunCompiledTo.next
      (Ninst.runCompiled_retdatacopy_of
        (di := 0) (ri := 0) (sz := w) (s := devm.stack)
        (c := c) (G := G + 2 * gBase) (M := M')
        rfl ?_ ?_ ?_ ?_) ?_
    · dsimp only [c]
      simp only [Devm.extCost, Devm.memory_setMach, memExtsSize,
        B256.toNat_zero, hw]
    · simp only [n, Devm.returnData_setMach, B256.toNat_zero, hw,
        Nat.zero_add]
      exact Nat.le_refl _
    · dsimp only [M']
      simp only [Devm.memory_setMach, Devm.returnData_setMach,
        B256.toNat_zero, hw]
      rw [show n = devm.returnData.length from rfl]
      simp only [List.sliceD, List.drop_zero]
      rw [List.takeD_eq_self (0 : UInt8) rfl]
    · simp only [Devm.gasLeft_setMach]
      omega
    · simp only [Devm.setMach_setMach]
      refine Func.RunCompiledTo.next
        (Ninst.runCompiled_pushItem (r := .retdatasize) (x := w)
          (cost := gBase) (G := G + gBase)
          (by rintro ⟨⟩) rfl
          (by simp only [Devm.gasLeft_setMach]; omega)
          (by simp only [Devm.stack_setMach]; omega)) ?_
      refine Func.RunCompiledTo.next
        (Ninst.runCompiled_pushB256 (w := 0) (c := gBase) (G := G)
          pushCost_zero
          (by simp only [Devm.gasLeft_setMach])
          (by simp only [Devm.stack_setMach, List.length_cons]; omega)) ?_
      simp only [Devm.setMach_setMach]
      have ha : M'.size % 32 = 0 := by
        rcases hrd : devm.returnData with _ | ⟨b, bs⟩
        · simpa [M', hrd, Mem.write] using halign
        · dsimp only [M']
          rw [hrd, Mem.size_write_cons]
          split
          · exact halign
          · rw [ceil32_eq_mul]
            omega
      have hc : n ≤ M'.size := by
        rcases hrd : devm.returnData with _ | ⟨b, bs⟩
        · simp [n, M', hrd]
        · dsimp only [n, M']
          rw [hrd, Mem.size_write_cons]
          split
          · omega
          · simpa using Nat.le_ceil32 (b :: bs).length
      have hext :
          (devm.setMach
            ⟨(0 : B256) :: w :: devm.stack, M', G⟩).extCost
              [⟨0, w.toNat⟩] = 0 := by
        rw [hw]
        exact Devm.extCost_zero_of_le ha (by omega)
      have hreads :
          Mem.Reads M' (Bytes.writeAt img 0 devm.returnData) := by
        dsimp only [M']
        exact Mem.Reads.write hwf hr 0 devm.returnData
      have hout : (M'.read 0 n).1 = devm.returnData := by
        dsimp only [n]
        calc
          (M'.read 0 devm.returnData.length).1 =
              (Bytes.writeAt img 0 devm.returnData).sliceD
                0 devm.returnData.length 0 :=
            Mem.Reads.read hreads 0 devm.returnData.length
          _ = devm.returnData :=
            Bytes.sliceD_writeAt img devm.returnData 0
      have himg : (M'.read 0 n).2 = M' :=
        Mem.read_snd_eq_self (memExtSize_of_le ha (by omega))
      have hread :
          (devm.setMach ⟨devm.stack, M', G⟩).memRead 0 n =
            ⟨devm.returnData, devm.setMach ⟨devm.stack, M', G⟩⟩ := by
        apply Prod.ext hout
        show (devm.setMach ⟨devm.stack, M', G⟩).withMemory
            (M'.read 0 n).2 =
          devm.setMach ⟨devm.stack, M', G⟩
        rw [himg]
        apply Devm.eq_of_proj <;> rfl
      exact Func.runCompiledTo_rev_of
        (i := 0) (sz := w) (s := devm.stack)
        (G := G) (e := 0) (out := devm.returnData)
        (d' := devm.setMach ⟨devm.stack, M', G⟩)
        rfl hext rfl
        (by simpa only [hw, B256.toNat_zero, Devm.setMach_setMach,
          Devm.memory_setMach] using hread)

/-! ## Inverting the `revReturnData` walk

Everything above *builds* a derivation.  A caller that holds one it did not
build — the bubble arm of an outgoing call, which learns only that the frame
settled somewhere — needs the other direction: read the reverting frame's
output off an arbitrary walk, with no premise about gas, memory, code or world
content.

Three one-step inversions do all of it.  `Func.next` and `Func.last` are each
produced by exactly one rule of `Func.RunCompiledTo`, so `cases` recovers their
premises verbatim; and once the `REVERT`'s two operands are known to be on the
stack, `chargeGas` is the only step of `Linst.run … .rev` left that can fail. -/

/-- One `.next` step of a walk, inverted: the intermediate state and both
premises, unchanged. -/
private lemma of_runCompiledTo_next {fs : List Func} {sevm : Sevm}
    {devm : Devm} {i : Ninst} {f : Func} {ex : Execution}
    (h : Func.RunCompiledTo fs sevm devm (.next i f) ex) :
    ∃ d, Ninst.RunCompiled sevm devm i d ∧
      Func.RunCompiledTo fs sevm d f ex := by
  cases h with | next h_n h_f => exact ⟨_, h_n, h_f⟩

/-- The terminal step of a walk, inverted. -/
private lemma of_runCompiledTo_last {fs : List Func} {sevm : Sevm}
    {devm : Devm} {i : Linst} {ex : Execution}
    (h : Func.RunCompiledTo fs sevm devm (.last i) ex) :
    Linst.Run sevm devm i ex := by
  cases h with | last h_l => exact h_l

/-- `chargeGas`, evaluated forward on the arm the forward library never takes:
without the gas the charge is refused, and the state is handed back untouched.
The mirror of `Blanc.chargeGas_eq_ok`. -/
private lemma chargeGas_eq_outOfGas {cost : Nat} {devm : Devm}
    (h : devm.gasLeft < cost) :
    chargeGas cost devm = .error ⟨.halt (.outOfGas .none), devm⟩ := by
  rw [chargeGas_def]
  have hs : safeSub devm.gasLeft cost = none := by
    unfold safeSub
    rw [if_neg (by omega)]
  rw [hs]

/-- `REVERT` over a stack whose top two words are known, inverted.

Both operands are present, so neither `Devm.popToNat` can underflow and the
window's expansion charge is the walk's last chance to fail.  Either it does —
and the frame settles at an out-of-gas exceptional halt — or the `REVERT` goes
through, in which case the output is the window read out of the frame's own
memory.  The read is left as `Mem.read`, unevaluated, for the reason
`Func.runCompiledTo_rev`'s docstring gives. -/
private lemma of_run_rev {sevm : Sevm} {devm : Devm} {i sz : B256}
    {s : List B256} {ex : Execution}
    (h_stk : devm.stack = i :: sz :: s)
    (h_run : Linst.Run sevm devm .rev ex) :
    (∃ d, ex = .error (.halt (.outOfGas .none), d)) ∨
      (∃ post, ex = .error (.revert, post) ∧
        post.output = (devm.memory.read i.toNat sz.toNat).1) := by
  have h_eq : Linst.run sevm devm .rev = ex := h_run
  rcases Nat.lt_or_ge devm.gasLeft (devm.extCost [⟨i.toNat, sz.toNat⟩])
    with h_gas | h_gas
  · have h_oog : Linst.run sevm devm .rev
        = .error ⟨.halt (.outOfGas .none),
            devm.setMach ⟨s, devm.memory, devm.gasLeft⟩⟩ := by
      show (do
        let ⟨index, d⟩ ← devm.popToNat
        let ⟨size, d⟩ ← d.popToNat
        let cost := d.extCost [⟨index, size⟩]
        let d ← chargeGas cost d
        let ⟨output, d⟩ := d.memRead index size
        let d := d.withOutput output
        Except.error ⟨.revert, d⟩) = _
      rw [Devm.popToNat_eq_ok h_stk]
      simp only [bind, Except.bind]
      rw [Devm.popToNat_eq_ok
        (devm := devm.setMach ⟨sz :: s, devm.memory, devm.gasLeft⟩) rfl]
      simp only [Devm.setMach_setMach, Devm.memory_setMach,
        Devm.gasLeft_setMach]
      have h_ext : (devm.setMach ⟨s, devm.memory, devm.gasLeft⟩).extCost
          [⟨i.toNat, sz.toNat⟩] = devm.extCost [⟨i.toNat, sz.toNat⟩] := rfl
      rw [h_ext, chargeGas_eq_outOfGas
        (devm := devm.setMach ⟨s, devm.memory, devm.gasLeft⟩) h_gas]
    exact Or.inl ⟨_, h_eq.symm.trans h_oog⟩
  · exact Or.inr ⟨_, h_eq.symm.trans (Linst.run_rev_eq_error h_stk h_gas rfl),
      rfl⟩

/-- Reading a window back at offset zero immediately after writing it there
returns it, with no well-formedness premise and no side condition: the empty
payload reads back as the empty window, and `Mem.read_write_zero` covers every
other. -/
private lemma Mem.read_write_zero_len (μ : Mem) (ys : Bytes) :
    ((μ.write 0 ys).read 0 ys.length).1 = ys := by
  cases ys with
  | nil => rfl
  | cons b bs => exact Mem.read_write_zero μ (by simp)

/-- **`Func.revReturnData`'s walk, inverted.**

The converse of `Func.runCompiledTo_revReturnData`: rather than producing a run
from a gas budget, this reads the settled outcome off a run somebody else
produced.  It carries no premise at all — not about gas, not about the frame's
memory, not about the callee, its code, or any world content — because a
derivation of the walk already witnesses that all six instructions before the
`REVERT` succeeded.

The disjunct is the honest residue of that.  `Func.revReturnData` ends in a
`REVERT` over the window it has just filled, and a window costs memory
expansion; the walk's derivation says nothing about the gas left when the
charge falls due, so the frame may settle at an out-of-gas exceptional halt
instead.  That is the left disjunct, and it is frame-local: it is the `REVERT`'s
own charge that was refused, not the callee's gas and not the caller's.

The output is stated raw, as `List.take` at the `B256` round trip of the
returndata's length, because that is what the machine writes: `RETURNDATACOPY`
copies `size` bytes where `size` is the word `RETURNDATASIZE` pushed.  Reading
it as `devm.returnData` needs `devm.returnData.length < 2 ^ 256`, which is the
consumer's obligation and not this lemma's — forcing it here would buy a
premise for a rewrite the consumer can do itself. -/
lemma Func.runCompiledTo_revReturnData_inv {fs : List Func} {sevm : Sevm}
    {devm : Devm} {ex : Execution}
    (run : Func.RunCompiledTo fs sevm devm Func.revReturnData ex) :
    (∃ d, ex = .error (.halt (.outOfGas .none), d)) ∨
      (∃ post, ex = .error (.revert, post) ∧
        post.output =
          devm.returnData.take devm.returnData.length.toB256.toNat) := by
  unfold Func.revReturnData at run
  obtain ⟨d1, r1, run⟩ := of_runCompiledTo_next run
  obtain ⟨d2, r2, run⟩ := of_runCompiledTo_next run
  obtain ⟨d3, r3, run⟩ := of_runCompiledTo_next run
  obtain ⟨d4, r4, run⟩ := of_runCompiledTo_next run
  obtain ⟨d5, r5, run⟩ := of_runCompiledTo_next run
  obtain ⟨d6, r6, run⟩ := of_runCompiledTo_next run
  have hrev := of_runCompiledTo_last run
  have p1 := of_run_retdatasize_val (Ninst.Run.of_runCompiled r1)
  have p2 := of_run_pushB256 (Ninst.Run.of_runCompiled r2)
  have p3 := of_run_pushB256 (Ninst.Run.of_runCompiled r3)
  obtain ⟨x, y, z, hpop, hle, hmem4, hrd4⟩ :=
    of_run_retdatacopy_val (Ninst.Run.of_runCompiled r4)
  have p5 := of_run_retdatasize_val (Ninst.Run.of_runCompiled r5)
  have p6 := of_run_pushB256 (Ninst.Run.of_runCompiled r6)
  have hrd3 : d3.returnData = devm.returnData :=
    (p1.returnData.trans (p2.returnData.trans p3.returnData)).symm
  have hm3 : d3.memory = devm.memory :=
    (p1.memory.trans (p2.memory.trans p3.memory)).symm
  obtain ⟨hs4, hx, hy, hz⟩ :
      d4.stack = devm.stack ∧ x = 0 ∧ y = 0 ∧
        z = Nat.toB256 devm.returnData.length := by
    have e4 : d3.stack = x :: y :: z :: d4.stack := hpop
    have e1 : d1.stack = Nat.toB256 devm.returnData.length :: devm.stack :=
      p1.stack
    have e2 : d2.stack = 0 :: d1.stack := p2.stack
    have e3 : d3.stack = 0 :: d2.stack := p3.stack
    rw [e2, e1] at e3
    rw [e4] at e3
    simp only [List.cons.injEq] at e3
    exact ⟨e3.2.2.2, e3.1, e3.2.1, e3.2.2.1⟩
  rw [hy, hz, hrd3, B256.toNat_zero, Nat.zero_add] at hle
  have hm6 : d6.memory
      = devm.memory.write 0
          (devm.returnData.take (Nat.toB256 devm.returnData.length).toNat) := by
    rw [← p6.memory, ← p5.memory, hmem4, hx, hy, hz, hm3, hrd3, B256.toNat_zero,
      List.sliceD, List.drop_zero, List.takeD_eq_take _ hle]
  have hs6 : d6.stack
      = 0 :: Nat.toB256 devm.returnData.length :: devm.stack := by
    have e5 : d5.stack = Nat.toB256 d4.returnData.length :: d4.stack := p5.stack
    have e6 : d6.stack = 0 :: d5.stack := p6.stack
    rw [e6, e5, hs4, hrd4, hrd3]
  rcases of_run_rev hs6 hrev with h_oog | ⟨post, hpost, hout⟩
  · exact Or.inl h_oog
  · refine Or.inr ⟨post, hpost, ?_⟩
    have hlt : (devm.returnData.take
        (Nat.toB256 devm.returnData.length).toNat).length
          = (Nat.toB256 devm.returnData.length).toNat := by
      rw [List.length_take]; omega
    have hread := Mem.read_write_zero_len devm.memory
      (devm.returnData.take (Nat.toB256 devm.returnData.length).toNat)
    rw [hlt] at hread
    rw [hout, hm6, B256.toNat_zero, hread]

/-! ## Message-altitude transport -/

/-- **A frame whose code reverts settles with `.revert`, and rolled back.**

The strong-form counterpart of `Blanc/Ladder.lean`'s
`Blanc.rollback_of_no_success`, stated once over the abstract premise `h_exec`
so that a target instantiates it in two lines.  Where that theorem takes "no
successful `Exec` starts here" and concludes `out.error.isSome`, this one takes
the total function's own equation at the frame's entry machine and concludes
the error *kind*, plus the output the code chose.

Its three structural premises are that theorem's and are there for its reasons:
`h_fill`, because `ProcessMessage msg xl (.ok out)` leaves the slot otherwise
unconstrained; `h_bt`, which names the post-transfer environment the entry
machine is built from; and `h_prec`, because the precompile entry mode has no
`Exec` at all and the conclusion is simply false in that branch.

This theorem is contract-agnostic: nothing in its statement or proof mentions
fmint or another contract. -/
theorem rollback_revert_of_exec_revert {msg : Msg} {benv : Benv} {xl : Xlot}
    {out post : Devm}
    (h_pm : ProcessMessage msg xl (.ok out))
    (h_fill : Xlot.Filled xl)
    (h_bt : msg.benvAfterTransfer = .ok benv)
    (h_prec : ∀ adr, msg.codeAddress = some adr →
      ¬ (!msg.disablePrecompiles && decide (benv.stat.rules.isPrecomp adr)) = true)
    (h_exec : exec ⟨0, initSevm (msg.withBenv benv), initDevm (msg.withBenv benv)⟩
      = .error (.revert, post)) :
    out.error = some .revert ∧ out.output = post.output ∧
      out.state = msg.benv.state ∧
      out.transientStorage = msg.tenv.transientStorage := by
  obtain ⟨r0, hbody, hset⟩ := ProcessMessage.iff_body.mp h_pm
  unfold FrameBody at hbody
  rw [h_bt] at hbody
  have h_r0 : r0 = .ok (post.withError (some .revert)) := by
    rcases h_ca : (msg.withBenv benv).codeAddress with _ | adr
    · obtain ⟨ex', h_xl, h_he⟩ := of_executeCode_noneCode h_ca hbody
      subst h_xl
      obtain ⟨exc⟩ := h_fill
      rw [((exec_iff_exec_eq _ _ _ _).mp ⟨exc⟩).symm.trans h_exec] at h_he
      exact h_he.symm
    · rcases of_executeCode_someCode h_ca hbody with ⟨h_pre, -, -⟩ | ⟨-, ex', h_xl, h_he⟩
      · exact absurd h_pre (h_prec adr h_ca)
      · subst h_xl
        obtain ⟨exc⟩ := h_fill
        rw [((exec_iff_exec_eq _ _ _ _).mp ⟨exc⟩).symm.trans h_exec] at h_he
        exact h_he.symm
  subst h_r0
  unfold processMessage.settle at hset
  dsimp only [bind, Except.bind] at hset
  rw [if_pos (show (post.withError (some SettledHalt.revert)).error.isSome = true
    from rfl)] at hset
  have h_out := Except.ok.inj hset
  have h_err : out.error = some .revert := by rw [h_out]; rfl
  exact ⟨h_err, by rw [h_out]; rfl,
    ProcessMessage.rollback_of_error h_pm (by rw [h_err]; rfl)⟩

/-- Fuse a gas-exact compiled walk ending in a revert with the message-frame
transport.  This is message-call altitude: it claims neither transaction-level
reversion nor exhaustiveness, and it does not attribute a child call's outcome
to its caller. -/
theorem rollback_revert_of_runCompiledTo
    {msg : Msg} {benv : Benv} {xl : Xlot} {out d : Devm} {p : Prog} {bs : Bytes}
    (h_pm : ProcessMessage msg xl (.ok out))
    (h_fill : Xlot.Filled xl)
    (h_bt : msg.benvAfterTransfer = .ok benv)
    (h_prec : ∀ adr, msg.codeAddress = some adr →
      ¬ (!msg.disablePrecompiles && decide (benv.stat.rules.isPrecomp adr)) = true)
    (h_code : some (initSevm (msg.withBenv benv)).code.toList = p.compile)
    (h_run : Prog.RunCompiledTo (initSevm (msg.withBenv benv))
      (initDevm (msg.withBenv benv)) p (.error (.revert, d.withOutput bs))) :
    out.error = some .revert ∧ out.output = bs ∧
      out.state = msg.benv.state ∧
      out.transientStorage = msg.tenv.transientStorage := by
  exact rollback_revert_of_exec_revert h_pm h_fill h_bt h_prec
    (Prog.exec_of_runCompiledTo h_run h_code)

end Blanc
