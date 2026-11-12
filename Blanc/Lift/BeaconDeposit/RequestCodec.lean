import Blanc.ConsensusSszDeposit
import Blanc.Corpus.Freeze.DepositCells
import Blanc.Lift.BeaconDeposit.LogCodec

/-! The original deposit event record and the actual consensus request codec. -/
namespace Blanc.Lift.BeaconDeposit.RequestCodec

open Jaune JauneConsensus Blanc.ConsensusSsz
open Blanc.Corpus.Freeze.Deposit

/-- The contract's fixed-width little-endian image is the consensus image. -/
theorem le64_eq_leBytes (n : Nat) : Blanc.BeaconDeposit.le64 n = JauneConsensus.leBytes 8 n := by
  simp only [Blanc.BeaconDeposit.le64, JauneConsensus.leBytes,
    Nat.shiftRight_eq_div_pow, Nat.div_div_eq_div_mul, Nat.reducePow, Nat.reduceMul,
    List.cons.injEq, and_true]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> apply UInt8.toNat_inj.mp <;>
    simp only [Nat.toUInt8_eq, UInt8.toNat_ofNat', Nat.reducePow, Nat.mod_mod]

/-- The original five-field event record is the actual request's SSZ serialization. -/
theorem request_record (dr : DepositRequest) :
    depositRecord ⟨dr.pubkey.toArray.toList, dr.withdrawal_credentials.toBytes,
      Blanc.BeaconDeposit.le64 dr.amount.toNat, dr.signature.toArray.toList,
      Blanc.BeaconDeposit.le64 dr.index.toNat⟩ = Ssz.serialize dr := by
  rw [serialize_depositRequest]
  simp only [depositRecord, le64_eq_leBytes]

/-- Exact record equality recovers payload, amount and index without identifying occurrences by payload. -/
theorem fields_of_record {dr : DepositRequest} {pk wc sig : Bytes} {amount index : Nat}
    (hpk : pk.length = 48) (hwc : wc.length = 32) (hsig : sig.length = 96)
    (hamount : amount < 2 ^ 64) (hindex : index < 2 ^ 64)
    (record : Ssz.serialize dr = depositRecord
      ⟨pk, wc, Blanc.BeaconDeposit.le64 amount, sig, Blanc.BeaconDeposit.le64 index⟩) :
    dr.pubkey.toArray.toList = pk ∧ dr.withdrawal_credentials.toBytes = wc ∧
      dr.signature.toArray.toList = sig ∧ dr.amount.toNat = amount ∧ dr.index.toNat = index := by
  rw [serialize_depositRequest, depositRecord, le64_eq_leBytes, le64_eq_leBytes] at record
  have pkLen : dr.pubkey.toArray.toList.length = 48 := by rw [Array.length_toList, dr.pubkey.size_eq]
  have sigLen : dr.signature.toArray.toList.length = 96 := by rw [Array.length_toList, dr.signature.size_eq]
  obtain ⟨record, hi⟩ := List.append_inj record (by
    simp only [List.length_append, pkLen, sigLen, B256.length_toBytes, length_leBytes,
      hpk, hwc, hsig])
  obtain ⟨record, hs⟩ := List.append_inj record (by
    simp only [List.length_append, pkLen, B256.length_toBytes, length_leBytes, hpk, hwc])
  obtain ⟨record, ha⟩ := List.append_inj record (by
    simp only [List.length_append, pkLen, B256.length_toBytes, hpk, hwc])
  obtain ⟨hp, hw⟩ := List.append_inj record (pkLen.trans hpk.symm)
  have amountEq := congrArg leNat ha
  have indexEq := congrArg leNat hi
  rw [leNat_leBytes, leNat_leBytes,
    Nat.mod_eq_of_lt (by simpa only [Nat.reducePow] using dr.amount.toNat_lt),
    Nat.mod_eq_of_lt (by simpa only [Nat.reducePow] using hamount)] at amountEq
  rw [leNat_leBytes, leNat_leBytes,
    Nat.mod_eq_of_lt (by simpa only [Nat.reducePow] using dr.index.toNat_lt),
    Nat.mod_eq_of_lt (by simpa only [Nat.reducePow] using hindex)] at indexEq
  exact ⟨hp, hw, hs, amountEq, indexEq⟩

open Blanc.Lift.BeaconDeposit

/-- A classified contract deposit contributes its exact occurrence-indexed request record. -/
theorem frame_record (fr : Exec.Frame) (history : List B256)
    (invariant : SolInv (fr.pre.getStor depositAddr) history)
    (classified : Classified fr history .deposit) :
    frameRecords fr = [depositRecord
      ⟨argBytes fr.sevm 0, argBytes fr.sevm 1,
        Blanc.BeaconDeposit.le64 (fr.sevm.value.toNat / Blanc.BeaconDeposit.oneGwei),
        argBytes fr.sevm 2, Blanc.BeaconDeposit.le64 history.length⟩] ∧
    (argBytes fr.sevm 0).length = 48 ∧ (argBytes fr.sevm 1).length = 32 ∧
    (argBytes fr.sevm 2).length = 96 ∧
    fr.sevm.value.toNat / Blanc.BeaconDeposit.oneGwei < 2 ^ 64 ∧
    history.length < 2 ^ 32 - 1 ∧
    (fr.sevm.value.toNat / Blanc.BeaconDeposit.oneGwei) * 10 ^ 9 = fr.sevm.value.toNat := by
  obtain ⟨_, _, post, ev, executed, _, _, _, _, logs, _, _⟩ := classified
  obtain ⟨pk, wc, sig, floor, multiple, amount, _, count, br, walk, postEq, eventEq⟩ :=
    deposit_ok_facts executed
  have countEq : (solAcc (fr.pre.getStor depositAddr)).count = history.length := invariant.2.1
  rw [countEq] at count eventEq
  subst ev
  have amountLen : (Blanc.BeaconDeposit.le64
      (fr.sevm.value.toNat / Blanc.BeaconDeposit.oneGwei)).length = 8 := by
    rw [le64_eq_leBytes, length_leBytes]
  have indexLen : (Blanc.BeaconDeposit.le64 history.length).length = 8 := by
    rw [le64_eq_leBytes, length_leBytes]
  have extracted := extractDepositData_abiDepositEvent
    ⟨argBytes fr.sevm 0, argBytes fr.sevm 1,
      Blanc.BeaconDeposit.le64 (fr.sevm.value.toNat / Blanc.BeaconDeposit.oneGwei),
      argBytes fr.sevm 2, Blanc.BeaconDeposit.le64 history.length⟩ pk wc amountLen sig indexLen
  refine ⟨?_, pk, wc, sig, by omega, count, ?_⟩
  · simp only [frameRecords, depositLogs, logs, Blanc.BeaconDeposit.depositEventLog,
      depositEventTopic_eq_signatureHash, List.filter_cons, List.filter_nil,
      List.getElem?_cons_zero, eq_self, and_self, decide_true, ite_true,
      List.filterMap_cons, List.filterMap_nil, extracted]
    rfl
  · exact Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero multiple)

end Blanc.Lift.BeaconDeposit.RequestCodec
