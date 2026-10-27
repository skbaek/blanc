import Blanc.Lift.Usdc.ModernCallerHashBodies
import Blanc.Lift.FrameSkip
import Blanc.Lift.ObservedReachSplit

/-! Original owner arguments through V2 allowance arithmetic and its shared setter. -/
namespace Blanc.Lift.Usdc.V2AllowanceSetterReach

open Jaune Blanc Blanc.Lift

variable {observe : Conf → Conf → Prop}

private theorem add_return_stack {Q : Sevm → Devm → Ninst → Devm → Prop}
    (erase : ∀ {s d n d'}, Q s d n d' → Ninst.Run s d n d')
    {sevm : Sevm} (hsg : sevm.benvStat.rules.stateGas = none)
    {base D : Devm} {a b tag : B256} {S : List B256} {M : Mem} {G : Nat}
    (run : SFunc.RunP Q ImplV2.cert.prog sevm
      (St base (a :: b :: tag :: S) M G) ImplV2.t_41fd_c77 (.returned D)) :
    ∃ result, D.stack = result :: S := by
  obtain ⟨Y, stack, len⟩ := run.entry_stack_below_noStateGas erase ImplV2.cert_check hsg
    (k := 77) (e := ⟨0x41fd, [.unk, .unk, .ret], 1⟩) rfl rfl
    (ρ := tag) (X := [a, b, tag]) (R := S) rfl (.cons trivial (.cons trivial (.cons rfl .nil)))
  cases Y with
  | nil => cases len
  | cons result rest =>
    have empty : rest = [] := List.eq_nil_of_length_eq_zero (by
      simp only [List.length_cons] at len
      omega)
    subst rest
    exact ⟨result, stack⟩

private theorem sub_return_stack {Q : Sevm → Devm → Ninst → Devm → Prop}
    (erase : ∀ {s d n d'}, Q s d n d' → Ninst.Run s d n d')
    {sevm : Sevm} (hsg : sevm.benvStat.rules.stateGas = none)
    {base D : Devm} {a b message tag : B256} {S : List B256} {M : Mem} {G : Nat}
    (run : SFunc.RunP Q ImplV2.cert.prog sevm
      (St base (a :: b :: message :: tag :: S) M G) ImplV2.t_4be2_c88 (.returned D)) :
    ∃ result, D.stack = result :: S := by
  obtain ⟨Y, stack, len⟩ := run.entry_stack_below_noStateGas erase ImplV2.cert_check hsg
    (k := 88) (e := ⟨0x4be2, [.unk, .unk, .unk, .ret], 1⟩) rfl rfl
    (ρ := tag) (X := [a, b, message, tag]) (R := S) rfl (.cons trivial (.cons trivial (.cons trivial (.cons rfl .nil))))
  cases Y with
  | nil => cases len
  | cons result rest =>
    have empty : rest = [] := List.eq_nil_of_length_eq_zero (by
      simp only [List.length_cons] at len
      omega)
    subst rest
    exact ⟨result, stack⟩

theorem increase_source {Q : Sevm → Devm → Ninst → Devm → Prop}
    (erase : ∀ {s d n d'}, Q s d n d' → Ninst.Run s d n d')
    {sevm : Sevm} (hsg : sevm.benvStat.rules.stateGas = none)
    {b : Devm} {owner a : Adr} {value : B256} {S : List B256}
    {M : Mem} {G : Nat} {K : List SFunc} {T : Conf}
    (run : ObservedReach Q observe ImplV2.cert.prog sevm
      ⟨St b (value :: a.toB256 :: owner.toB256 :: S) M G, ImplV2.t_41b3_c79, K⟩ T)
    (hT : AtSstore T) (cont : ∀ f ∈ K, f.sstoreFreeIn [] = true) :
    ModernCallerReach.ApprovalSource Q observe .v2 sevm owner a T := by
  unfold ImplV2.t_41b3_c79 at run
  orsd
  iterate 4 orsx
  rw [B256.and_comm, ff20_and_adr] at run
  iterate 12 orsx
  obtain ⟨_, firstHash, run⟩ := ObservedKeccak.of_next erase run hT
    (input := owner.toB256.toBytes ++ (10 : B256).toBytes) (shape := fun _ => True)
    (by exact Mem.read_two_word_writes_at_raw _ 0 _ _) (by trivial)
  simp only [show (Bytes.toB256 [0]).toNat = 0 from rfl,
    show (Bytes.toB256 [32]).toNat = 32 from rfl] at run
  rw [Mem.read_two_word_writes_at_raw] at run
  iterate 3 orsx
  rw [B256.and_comm, ff20_and_adr] at run
  iterate 5 orsx
  obtain ⟨_, secondHash, run⟩ := ObservedKeccak.of_next erase run hT
    (input := a.toB256.toBytes ++ (mapSlot owner.toB256 10).toBytes)
    (shape := fun _ => True)
    (by exact Mem.read_two_word_writes_at_raw _ 0 _ _) (by trivial)
  simp only [show (Bytes.toB256 [0]).toNat = 0 from rfl,
    show (Bytes.toB256 [32]).toNat = 32 from rfl] at run
  rw [Mem.read_two_word_writes_at_raw] at run
  orsld
  iterate 10 orsx
  obtain ⟨g, _, hg, run⟩ := ObservedReach.rs_callIn run hT
  rw [show ImplV2.cert.prog[77]? = some ImplV2.t_41fd_c77 from rfl] at hg
  cases hg
  have free : SstoreFreeSet ImplV2.cert.prog [77] = true := by decide +kernel
  obtain ⟨D, returned, _, run⟩ := ObservedReach.return_of_sstoreFree free (by decide +kernel) run hT
  obtain ⟨result, stack⟩ := add_return_stack erase hsg returned
  rw [St.self' D, stack] at run
  unfold ImplV2.t_41f8_c79 at run
  orsd
  orsx
  obtain ⟨g, _, hg, run⟩ := ObservedReach.rs_callIn run hT
  rw [show ImplV2.cert.prog[81]? = some ImplV2.t_3db1_c81 from rfl] at hg
  cases hg
  exact ModernCallerReach.approval_core_source erase run hT (by
    intro f member
    rcases List.mem_cons.mp member with rfl | member
    · decide +kernel
    exact cont f member)

theorem decrease_source {Q : Sevm → Devm → Ninst → Devm → Prop}
    (erase : ∀ {s d n d'}, Q s d n d' → Ninst.Run s d n d')
    {sevm : Sevm} (hsg : sevm.benvStat.rules.stateGas = none)
    {b : Devm} {owner a : Adr} {value : B256} {S : List B256}
    {M : Mem} {G : Nat} {K : List SFunc} {T : Conf}
    (run : ObservedReach Q observe ImplV2.cert.prog sevm
      ⟨St b (value :: a.toB256 :: owner.toB256 :: S) M G, ImplV2.t_43fa_c75, K⟩ T)
    (hT : AtSstore T) (cont : ∀ f ∈ K, f.sstoreFreeIn [] = true) :
    ModernCallerReach.ApprovalSource Q observe .v2 sevm owner a T := by
  unfold ImplV2.t_43fa_c75 at run
  orsd
  iterate 26 orsx
  rw [B256.and_comm, ff20_and_adr] at run
  iterate 12 orsx
  obtain ⟨_, firstHash, run⟩ := ObservedKeccak.of_next erase run hT
    (input := owner.toB256.toBytes ++ (10 : B256).toBytes) (shape := fun _ => True)
    (by exact Mem.read_two_word_writes_at_raw _ 0 _ _) (by trivial)
  simp only [show (Bytes.toB256 [0]).toNat = 0 from rfl,
    show (Bytes.toB256 [32]).toNat = 32 from rfl] at run
  rw [Mem.read_two_word_writes_at_raw] at run
  iterate 3 orsx
  rw [B256.and_comm, ff20_and_adr] at run
  iterate 5 orsx
  obtain ⟨_, secondHash, run⟩ := ObservedKeccak.of_next erase run hT
    (input := a.toB256.toBytes ++ (mapSlot owner.toB256 10).toBytes)
    (shape := fun _ => True)
    (by exact Mem.read_two_word_writes_at_raw _ 0 _ _) (by trivial)
  simp only [show (Bytes.toB256 [0]).toNat = 0 from rfl,
    show (Bytes.toB256 [32]).toNat = 32 from rfl] at run
  rw [Mem.read_two_word_writes_at_raw] at run
  orsld
  iterate 3 orsx
  obtain ⟨g, _, hg, run⟩ := ObservedReach.rs_callIn run hT
  rw [show ImplV2.cert.prog[88]? = some ImplV2.t_4be2_c88 from rfl] at hg
  cases hg
  have free : SstoreFreeSet ImplV2.cert.prog [5, 88, 93] = true := by decide +kernel
  obtain ⟨D, returned, _, run⟩ := ObservedReach.return_of_sstoreFree free (by decide +kernel) run hT
  obtain ⟨result, stack⟩ := sub_return_stack erase hsg returned
  rw [St.self' D, stack] at run
  unfold ImplV2.t_41f8_c75 at run
  orsd
  orsx
  obtain ⟨g, _, hg, run⟩ := ObservedReach.rs_callIn run hT
  rw [show ImplV2.cert.prog[81]? = some ImplV2.t_3db1_c81 from rfl] at hg
  cases hg
  exact ModernCallerReach.approval_core_source erase run hT (by
    intro f member
    rcases List.mem_cons.mp member with rfl | member
    · decide +kernel
    exact cont f member)

end Blanc.Lift.Usdc.V2AllowanceSetterReach
