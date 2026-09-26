import Blanc.Lift.BeaconDeposit.BodySpec

/-!
# Body segment 2 kit: memory steps over a known image

Step lemmas for the event encoding's walk (`BodyEvent.lean`): `MSTORE`, `MLOAD` and
`CALLDATACOPY` with the memory size and the window offsets as numerals, and the `peel` tactic
that reads a window of an image through a chain of `Bytes.writeAt`s.
-/

namespace Blanc.Lift.BeaconDeposit

open Jaune

/-- A well-formed memory reading as an image. -/
def RW (M : Mem) (X : Bytes) : Prop := Mem.Wf M ∧ Mem.Reads M X

theorem RW.write {M : Mem} {X : Bytes} (h : RW M X) (n : Nat) (ys : Bytes) :
    RW (M.write n ys) (Bytes.writeAt X n ys) :=
  ⟨h.1.write _ _, h.2.write h.1 _ _⟩

/-- The size after a write, from the size before it. -/
theorem sz_step {N : Mem} {bs : Bytes} {i n len n' : Nat} (hN : N.size = n) (h32 : n % 32 = 0)
    (hlen : bs.length = len) (h : memExtSize n i len = n') : (N.write i bs).size = n' := by
  rw [Mem.size_write_of_size hN h32 hlen, h]

/-- Split a window read into its first `la` bytes and the rest. -/
theorem sliceD_cat {X a b : Bytes} {m la lb : Nat} (ha : X.sliceD m la 0 = a)
    (hb : X.sliceD (m + la) lb 0 = b) : X.sliceD m (la + lb) 0 = a ++ b := by
  rw [List.sliceD_split, ha, hb]

/-- A window starting at `0` of a payload's own length is the payload. -/
theorem sliceD_self_of (xs : Bytes) (s len : Nat) (h1 : s = 0) (h2 : xs.length = len) :
    xs.sliceD s len 0 = xs := by
  subst h1; exact Bytes.sliceD_zero_length h2

/-- A closed numeral comparison, after rewriting a payload length. -/
macro "len_decide" : tactic => `(tactic| first
  | decide
  | (rw [B256.length_toBytes] <;> decide)
  | (rw [List.length_sliceD] <;> decide))

/-- One step of `peel`: the outermost write of a window read is skipped when it misses the
window, or read through when it covers it.  Side conditions are closed numeral comparisons,
discharged in tactic mode so that a false one fails the step. -/
macro "peel1" : tactic => `(tactic| first
  | (rw [Bytes.sliceD_writeAt_before]; rotate_left; decide)
  | (rw [Bytes.sliceD_writeAt_after]; rotate_left; len_decide)
  | (rw [Bytes.sliceD_writeAt_inside]; rotate_left; decide; len_decide))

/-- Read a window of a `writeAt` chain down to the write that covers it, or to the base. -/
macro "peel" : tactic => `(tactic| repeat peel1)

/-- Close `payload.sliceD 0 payload.length 0 = payload` for a word or calldata payload. -/
macro "self_slice" : tactic => `(tactic| first
  | exact sliceD_self_of _ _ _ (by decide) (B256.length_toBytes _)
  | exact sliceD_self_of _ _ _ (by decide) (List.length_sliceD _ _ _ _))

section Steps

variable {fs : List SFunc} {sevm : Sevm} {b : Devm} {f : SFunc} {o : Outcome}
  {S : List B256} {M : Mem} {G : Nat}

theorem ex_mstore {i v : B256} {n inat c : Nat} (hs : M.size = n) (hi : i.toNat = inat)
    (hc : gVerylow + (calculateMemoryGasCost (memExtSize n inat 32) -
      calculateMemoryGasCost n) = c)
    (k : SFunc.RunExact fs sevm (St b S (M.write inat v.toBytes) G) f o) :
    SFunc.RunExact fs sevm (St b (i :: v :: S) M (G + c)) (.next (.reg .mstore) f) o :=
  rx_mstore (by rw [St.extCost_eq hs, hi]; exact hc) (by rw [hi]) k

theorem ex_mload {X : Bytes} {i v : B256} {n inat : Nat} (h : RW M X) (hs : M.size = n)
    (hi : i.toNat = inat) (h32 : n % 32 = 0) (hfit : inat + 32 ≤ n)
    (hv : Bytes.toB256 (X.sliceD inat 32 0) = v) (hroom : S.length < 1024)
    (k : SFunc.RunExact fs sevm (St b (v :: S) M G) f o) :
    SFunc.RunExact fs sevm (St b (i :: S) M (G + 3)) (.next (.reg .mload) f) o :=
  rx_mload (c := 3)
    (by rw [St.extCost_eq hs, hi, memExtSize_of_le h32 hfit, Nat.sub_self]; rfl)
    (by rw [hi, h.2.read, hv])
    (by rw [hi]; exact Mem.read_snd_eq_self (by rw [hs]; exact memExtSize_of_le h32 hfit))
    hroom k

theorem ex_cdc {di si sz : B256} {n dn zn c : Nat} (hs : M.size = n) (hi : di.toNat = dn)
    (hz : sz.toNat = zn)
    (hc : gVerylow + gasCopy * ceilDiv zn 32 + (calculateMemoryGasCost (memExtSize n dn zn) -
      calculateMemoryGasCost n) = c)
    (k : SFunc.RunExact fs sevm (St b S (M.write dn (sevm.data.sliceD si.toNat zn 0)) G) f o) :
    SFunc.RunExact fs sevm (St b (di :: si :: sz :: S) M (G + c))
      (.next (.reg .calldatacopy) f) o :=
  rx_calldatacopy (by rw [St.extCost_eq hs, hi, hz]; exact hc) (by rw [hi, hz]) k

end Steps

end Blanc.Lift.BeaconDeposit
