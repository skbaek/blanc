import Blanc.Compiled

namespace Blanc

open Jaune

/-- The number of immediate bytes consumed by a byte which is a `PUSH1`--`PUSH32`.

This deliberately follows `noPushBefore`, which only treats the PUSH opcode
range specially.  Jaune's Osaka decoder also gives DUPN, SWAPN, and EXCHANGE
one immediate byte, but those bytes do not affect `jumpable` and hence do not
belong in this scan. -/
def pushWidth (b : UInt8) : Nat :=
  if 0x60 ≤ b.toNat ∧ b.toNat ≤ 0x7f then b.toNat - 0x5f else 0

private def scanStarts : List UInt8 → Nat → List Bool
  | [], _ => []
  | _ :: bs, n + 1 => false :: scanStarts bs n
  | b :: bs, 0 => true :: scanStarts bs (pushWidth b)

private lemma scanStarts_skip (xs : List UInt8) :
    ∀ n, n ≤ xs.length →
      scanStarts xs n = List.replicate n false ++ scanStarts (xs.drop n) 0 := by
  intro n
  induction n generalizing xs with
  | zero => simp
  | succ n ih =>
    intro h
    cases xs with
    | nil => simp at h
    | cons b bs =>
      have hbs : n ≤ bs.length := by simp at h; omega
      simp only [scanStarts]
      rw [ih bs hbs]
      simp [List.drop, List.replicate_succ, List.cons_append]

private lemma getD_replicate_shift (q j : Nat) (xs : List Bool) :
    (List.replicate q false ++ xs).getD (q + j) false = xs.getD j false := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [show Nat.succ q + j = q + (j + 1) by omega]
    simp only [List.replicate_succ, List.getD_eq_getElem?_getD,
      List.getElem?_cons_succ]
    exact ih


/-- The linear forward instruction-start scan.

The list has one flag for each byte: a `true` flag is an instruction start,
and a `false` flag is a byte consumed as PUSH immediate data. -/
def instStarts (cd : ByteArray) : List Bool :=
  scanStarts cd.toList 0

private def instStartAt (cd : ByteArray) (k : Nat) : Bool :=
  (instStarts cd).getD k false

private inductive Instrs : List UInt8 → Prop
  | nil : Instrs []
  | step (b : UInt8) (ys rest : List UInt8)
      (hy : ys.length = pushWidth b) (hr : Instrs rest) :
      Instrs ((b :: ys) ++ rest)

private def ScanCover (xs : List UInt8) (k : Nat) : Prop :=
  ∃ pre b ys rest, xs = pre ++ (b :: ys) ++ rest ∧ Instrs pre ∧
    pre.length + 1 + ys.length = k ∧ ys.length < pushWidth b

private lemma scanStarts_false_cover :
    ∀ n, ∀ xs : List UInt8, xs.length = n →
      ∀ k, k < xs.length →
      (scanStarts xs 0).getD k false = false → ScanCover xs k := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro xs hxs k hk hf
    cases xs with
    | nil => simp at hxs hk
    | cons b bs =>
      simp only [List.length_cons] at hxs hk
      cases k with
      | zero => simp [scanStarts] at hf
      | succ j =>
        simp only [scanStarts, List.getD_cons_succ] at hf
        have hj : j < bs.length := by omega
        by_cases hq : pushWidth b = 0
        · have hf0 : (scanStarts bs 0).getD j false = false := by simpa [hq] using hf
          have hc := ih bs.length (by omega) bs rfl j hj hf0
          rcases hc with ⟨pre, c, ys, rest, heq, hpre, hlen, hys⟩
          refine ⟨(b :: []) ++ pre, c, ys, rest, ?_, ?_, ?_, hys⟩
          · simp [heq, List.append_assoc]
          · exact Instrs.step b [] pre (by simpa [hq]) hpre
          · simp only [List.length_cons, List.length_nil, List.length_append]
            omega
        · by_cases hsmall : j < pushWidth b
          · refine ⟨[], b, bs.take j, bs.drop j, ?_, Instrs.nil, ?_, ?_⟩
            · simp [List.take_append_drop]
            · simp [List.length_take_of_le (Nat.le_of_lt hj), Nat.add_comm]
            · rw [List.length_take_of_le (Nat.le_of_lt hj)]
              exact hsmall
          · have hqj : pushWidth b ≤ j := by omega
            have hqbs : pushWidth b ≤ bs.length := le_trans hqj (Nat.le_of_lt hj)
            have hskip := scanStarts_skip bs (pushWidth b) hqbs
            rw [hskip] at hf
            have hf' :
                (scanStarts (bs.drop (pushWidth b)) 0).getD
                    (j - pushWidth b) false = false := by
              rw [← getD_replicate_shift (pushWidth b) (j - pushWidth b)]
              simpa [Nat.add_sub_of_le hqj] using hf
            have hdrop : (bs.drop (pushWidth b)).length < n := by
              simp [List.length_drop]
              omega
            have hc := ih (bs.drop (pushWidth b)).length hdrop
              (bs.drop (pushWidth b)) rfl (j - pushWidth b) (by
                simp [List.length_drop]
                omega) hf'
            rcases hc with ⟨pre, c, ys, rest, heq, hpre, hlen, hys⟩
            have htake : (bs.take (pushWidth b)).length = pushWidth b :=
              List.length_take_of_le hqbs
            refine ⟨(b :: bs.take (pushWidth b)) ++ pre, c, ys, rest,
              ?_, ?_, ?_, hys⟩
            · calc
                b :: bs = b :: (bs.take (pushWidth b) ++ bs.drop (pushWidth b)) := by
                  rw [List.take_append_drop]
                _ = b :: (bs.take (pushWidth b) ++ (pre ++ (c :: ys) ++ rest)) := by
                  rw [heq]
                _ = (b :: bs.take (pushWidth b)) ++ pre ++ (c :: ys) ++ rest := by
                  simp [List.append_assoc]
            · exact Instrs.step b (bs.take (pushWidth b)) pre htake hpre
            · simp only [List.length_cons, List.length_append]
              omega

private def ScanPrefix (xs : List UInt8) (rem k : Nat) : Prop :=
  ∃ ys pre rest, xs = ys ++ pre ++ rest ∧ ys.length = rem ∧
    rem ≤ k ∧ k < xs.length ∧ pre.length = k - rem ∧ Instrs pre

private lemma scanPrefix_cons_skip :
    ScanPrefix (b :: bs) (r + 1) (j + 1) ↔ ScanPrefix bs r j := by
  constructor
  · rintro ⟨ys, pre, rest, heq, hys, hrj, hbound, hpre, hi⟩
    cases ys with
    | nil => simp at hys
    | cons y ys' =>
      cases heq
      simp only [List.length_cons] at hys
      refine ⟨ys', pre, rest, rfl, by omega, by omega, ?_, ?_, hi⟩
      · exact Nat.lt_of_succ_lt_succ hbound
      · omega
  · rintro ⟨ys, pre, rest, heq, hys, hrj, hbound, hpre, hi⟩
    refine ⟨b :: ys, pre, rest, ?_, by simp [hys], by omega, ?_, ?_, hi⟩
    · simp [heq]
    · simp at hbound ⊢
      omega
    · omega

private lemma instrs_cons_inv {b : UInt8} {xs : List UInt8} (h : Instrs (b :: xs)) :
    ∃ ys rest, xs = ys ++ rest ∧ ys.length = pushWidth b ∧ Instrs rest := by
  cases h with
  | step b ys rest hy hr => exact ⟨ys, rest, rfl, hy, hr⟩

private lemma pushWidth_spec (b : UInt8) :
    (96 ≤ b.toNat ∧ b.toNat ≤ 127 ∧ pushWidth b = b.toNat - 95) ∨
    ((b.toNat < 96 ∨ 127 < b.toNat) ∧ pushWidth b = 0) := by
  unfold pushWidth
  by_cases h : 96 ≤ b.toNat ∧ b.toNat ≤ 127
  · left; simp [h]
  · right
    constructor
    · omega
    · simp [h]

private lemma noPushBefore_instrs {cd : ByteArray} {k : Nat}
    {pre rest : List UInt8}
    (hslice : List.Slice cd.toList k (pre ++ rest))
    (hb : noPushBefore cd k 32 = true) (hpre : Instrs pre) :
    noPushBefore cd (k + pre.length) 32 = true ∧
      List.Slice cd.toList (k + pre.length) rest := by
  induction hpre generalizing k rest with
  | nil =>
    simpa using And.intro hb hslice
  | @step b ys rest0 hy hr ih =>
    have hinst :
        (96 ≤ b.toNat ∧ b.toNat ≤ 127 ∧ ys.length + 1 = b.toNat - 94) ∨
          ((b.toNat < 96 ∨ 127 < b.toNat) ∧ ys = []) := by
      rcases pushWidth_spec b with ⟨hlo, hhi, hw⟩ | ⟨hnp, hw⟩
      · left
        refine ⟨hlo, hhi, ?_⟩
        calc
          ys.length + 1 = (b.toNat - 95) + 1 := by rw [hy, hw]
          _ = b.toNat - 94 := by omega
      · right
        refine ⟨hnp, ?_⟩
        have : ys.length = 0 := by simpa [hw] using hy
        simpa using this
    have hpeel := noPushBefore_peel (code := cd) (k := k)
      (s := ys.length + 1) (b := b) (ys := ys) (zs := rest0 ++ rest)
      (by simpa [List.append_assoc] using hslice) hb rfl hinst
    rcases ih (k := k + ys.length + 1) (rest := rest) hpeel.2 hpeel.1
      with ⟨hnext, hslice'⟩
    constructor
    · simpa [List.length_append, Nat.add_assoc, Nat.add_left_comm,
        Nat.add_comm] using hnext
    · simpa [List.length_append, Nat.add_assoc, Nat.add_left_comm,
        Nat.add_comm] using hslice'

private lemma scanStarts_true_iff :
    ∀ n, ∀ xs : List UInt8, xs.length = n →
      ∀ rem k, k < xs.length →
      ((scanStarts xs rem).getD k false = true ↔ ScanPrefix xs rem k) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro xs hxs rem k hk
    cases xs with
    | nil => simp at hxs hk
    | cons b bs =>
      simp only [List.length_cons] at hxs hk
      cases rem with
      | zero =>
        cases k with
        | zero => simp [scanStarts, ScanPrefix, Instrs.nil]
        | succ j =>
          simp only [scanStarts, List.getD_cons_succ]
          have hbs : bs.length = n - 1 := by omega
          have hj : j < bs.length := by omega
          have hi := ih bs.length (by omega) bs rfl (pushWidth b) j hj
          rw [hi]
          constructor
          · rintro ⟨ys, pre, rest, heq, hys, hqj, hbound, hpre, hinst⟩
            refine ⟨[], (b :: ys) ++ pre, rest, ?_, by simp, by omega,
              by omega, ?_, ?_⟩
            · simp [heq, List.append_assoc]
            · simp [hpre]
              rw [hys]
              omega
            · exact Instrs.step b ys pre hys hinst
          · rintro ⟨ys, pre, rest, heq, hys, hqj, hbound, hpre, hinst⟩
            have hys0 : ys = [] := by simpa using hys
            subst ys
            have hpre' : pre ≠ [] := by
              intro hnil
              simp [hnil] at hpre
            cases pre with
            | nil => contradiction
            | cons c pre' =>
              have heq' : b :: bs = c :: pre' ++ rest := by simpa using heq
              cases heq'
              rcases instrs_cons_inv hinst with ⟨ys', tail, htail, hq, hr'⟩
              have htail_len : tail.length = j - pushWidth b := by
                simp only [List.length_cons] at hpre
                simp [htail, hq] at hpre
                omega
              have hp_tail : ScanPrefix (pre' ++ rest) (pushWidth b) j := by
                have hqj' : pushWidth b ≤ j := by
                  simp [htail, hq] at hpre
                  omega
                refine ⟨ys', tail, rest, ?_, hq, hqj', ?_, htail_len, hr'⟩
                · simp [htail, List.append_assoc]
                · omega
              exact hp_tail
      | succ rem =>
        cases k with
        | zero => simp [scanStarts, ScanPrefix]
        | succ j =>
          simp only [scanStarts, List.getD_cons_succ]
          have hbs : bs.length = n - 1 := by omega
          have hj : j < bs.length := by omega
          have hi := ih bs.length (by omega) bs rfl rem j hj
          rw [hi, scanPrefix_cons_skip]

private lemma noPushBefore_of_scan_start {cd : ByteArray} {k : Nat}
    (hk : k < cd.size) (hstart : instStartAt cd k = true) :
    noPushBefore cd k 32 = true := by
  have hk' : k < cd.toList.length := by
    simpa [ByteArray.size_eq_length_toList] using hk
  have hs : (scanStarts cd.toList 0).getD k false = true := by
    simpa [instStartAt, instStarts] using hstart
  have hp := (scanStarts_true_iff cd.toList.length cd.toList rfl 0 k hk').mp hs
  rcases hp with ⟨ys, pre, rest, heq, hys, hzero, hbound, hpre, hinst⟩
  have hys0 : ys = [] := by simpa using hys
  subst ys
  have hslice : List.Slice cd.toList 0 (pre ++ rest) := by
    have heq' : cd.toList = pre ++ rest := by simpa using heq
    rw [heq']
    simpa using List.slice_refl (pre ++ rest)
  have hno := noPushBefore_instrs hslice (by rfl) hinst
  have hpre_len : pre.length = k := by simpa using hpre
  simpa [hpre_len] using hno.1

private lemma noPushBefore_iff_scan_start {cd : ByteArray} {k : Nat}
    (hk : k < cd.size) :
    noPushBefore cd k 32 = true ↔ instStartAt cd k = true := by
  constructor
  · intro hn
    by_cases hstart : instStartAt cd k = true
    · exact hstart
    · have hstart' : instStartAt cd k = false := by
        cases h : instStartAt cd k <;> simp_all
      have hk' : k < cd.toList.length := by
        simpa [ByteArray.size_eq_length_toList] using hk
      have hs : (scanStarts cd.toList 0).getD k false = false := by
        simpa [instStartAt, instStarts] using hstart'
      have hc := scanStarts_false_cover cd.toList.length cd.toList rfl k hk' hs
      rcases hc with ⟨pre, b, ys, rest, heq, hpre, hlen, hys⟩
      have hslice : List.Slice cd.toList 0 (pre ++ ((b :: ys) ++ rest)) := by
        rw [heq]
        simpa [List.append_assoc] using List.slice_refl _
      have hpre_no := noPushBefore_instrs (cd := cd) (k := 0) (pre := pre)
        (rest := (b :: ys) ++ rest) hslice (by rfl) hpre
      have hpre_no' : noPushBefore cd pre.length 32 = true := by
        simpa using hpre_no.1
      have hslice_p : List.Slice cd.toList pre.length (b :: ys ++ rest) := by
        rw [heq]
        simpa [List.append_assoc] using
          (List.append_slice_suffix (xs := pre) (ys := (b :: ys) ++ rest))
      have hget : cd.toList[pre.length]? = some b :=
        List.get?_eq_of_slice hslice_p
      have hp_lt_list : pre.length < cd.toList.length :=
        (List.getElem?_eq_some_iff.mp hget).1
      have hp_lt : pre.length < cd.size := by
        simpa [ByteArray.size_eq_length_toList] using hp_lt_list
      have hbyte : cd[pre.length] = b :=
        ByteArray.getElem_of_getElem?_eq_some hget hp_lt
      rcases pushWidth_spec b with ⟨hlo, hhi, hw⟩ | ⟨hnp, hw⟩
      · have hwidth : pushWidth b ≤ 32 := by omega
        have hlo' : 96 ≤ cd[pre.length].toNat := by simpa [hbyte] using hlo
        have hhi' : cd[pre.length].toNat ≤ 127 := by simpa [hbyte] using hhi
        have hfalse := (noPushBefore_eq_true_iff cd k 32 (le_refl 32)).mp hn
          pre.length (by omega) (by omega) hp_lt hlo' hhi' (by simpa [hbyte] using
            (show k ≤ pre.length + (b.toNat - 95) by omega))
        rw [hfalse] at hpre_no'
        contradiction
      · have : ys.length < 0 := by simpa [hw] using hys
        omega
  · exact noPushBefore_of_scan_start hk

/-- A byte is an accepted jump destination exactly when it is an in-range
JUMPDEST at a start found by the linear scan. -/
def jumpdestOk (cd : ByteArray) (k : Nat) : Bool :=
  if hk : k < cd.size then
    decide (cd[k] = Jinst.toUInt8 .jumpdest ∧ instStartAt cd k = true)
  else false

theorem jumpable_eq_jumpdestOk (cd : ByteArray) (k : Nat) :
    jumpable cd k = jumpdestOk cd k := by
  unfold jumpable jumpdestOk
  split
  · rename_i hk
    split
    · rename_i hbyte
      simp [hbyte]
      apply Bool.eq_iff_iff.mpr
      exact noPushBefore_iff_scan_start hk
    · rename_i hbyte
      simp [hbyte]
  · rename_i hk
    simp [hk]

example : jumpdestOk ⟨#[0x60, 0x5b, 0x5b]⟩ 1 = false := by decide +kernel

example : jumpdestOk ⟨#[0x60, 0x5b, 0x5b]⟩ 2 = true := by decide +kernel

example :
    [jumpdestOk ⟨#[0x60, 0x5b, 0x5b]⟩ 1,
      jumpdestOk ⟨#[0x60, 0x5b, 0x5b]⟩ 2] = [false, true] := by decide +kernel

end Blanc
