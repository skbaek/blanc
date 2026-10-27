import Blanc.Lift.CursorKeccakOrder
import Blanc.Lift.Usdc.ModernCallerMappingTouches
import Blanc.Lift.WalkCutKit

/-! Ordered hash witnesses from the actual inner caller-allowance paths. -/
namespace Blanc.Lift.Usdc.ModernCallerReach

open Jaune Blanc Blanc.Lift

inductive Action
  | approve | increase | decrease
  deriving DecidableEq

def Action.selector : Action → B256
  | .approve => 0x095ea7b3
  | .increase => 0x39509351
  | .decrease => 0xa457c2d7

def core : ModernVersion → Action → SFunc
  | .v2, .approve => ImplV2.t_3db1_c81
  | .v2, .increase => ImplV2.t_41b3_c79
  | .v2, .decrease => ImplV2.t_43fa_c75
  | .v2_1, .approve => ImplV2_1.t_39da_c79
  | .v2_1, .increase => ImplV2_1.t_3ddc_c77
  | .v2_1, .decrease => ImplV2_1.t_4023_c72
  | .v2_2, .approve => Impl.t_3e18_c81
  | .v2_2, .increase => Impl.t_436b_c102
  | .v2_2, .decrease => Impl.t_4956_c92

variable {observe : Conf → Conf → Prop}

def approvalLine : List Ninst := [.reg .sstore, .reg (.dup 1), .reg .mload]

/-- The shared approval setter's actual owner/spender key and original ordered hashes. -/
def ApprovalSource (Q : Sevm → Devm → Ninst → Devm → Prop)
    (observe : Conf → Conf → Prop) (version : ModernVersion) (sevm : Sevm)
    (owner spender : Adr) (T : Conf) : Prop :=
  (∃ rest, T.d.stack = allowSlot owner spender :: rest) ∧
  (∃ tail, T.f = approvalLine.foldr SFunc.next tail) ∧
  ObservedKeccakPair Q observe version.cert.prog sevm
    (owner.toB256.toBytes ++ (10 : B256).toBytes)
    (spender.toB256.toBytes ++ (mapSlot owner.toB256 10).toBytes)

/-- Approve's address guards precede the original nested-mapping hashes. -/
theorem approval_core_source {version : ModernVersion}
    {Q : Sevm → Devm → Ninst → Devm → Prop}
    (erase : ∀ {s d n d'}, Q s d n d' → Ninst.Run s d n d')
    {sevm : Sevm} {b : Devm} {a owner : Adr} {value : B256} {S : List B256}
    {M : Mem} {G : Nat} {K : List SFunc} {T : Conf}
    (run : ObservedReach Q observe version.cert.prog sevm
      ⟨St b (value :: a.toB256 :: owner.toB256 :: S) M G, core version .approve, K⟩ T)
    (hT : AtSstore T) (cont : ∀ f ∈ K, f.sstoreFreeIn [] = true) :
    ApprovalSource Q observe version sevm owner a T := by
  cases version
  all_goals
    simp only [core] at run
    first
    | unfold ImplV2.t_3db1_c81 at run
    | unfold ImplV2_1.t_39da_c79 at run
    | unfold Impl.t_3e18_c81 at run
    orsd
    iterate 4 orsx
    rcases ObservedReach.rs_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
    · exact (Reach.false_of_sstoreFree (E := []) rfl run.forget hT (by decide +kernel) cont).elim
    first
    | unfold ImplV2.t_3e1d_c81 at run
    | unfold ImplV2_1.t_3a46_c79 at run
    | unfold Impl.t_3e84_c81 at run
    orsd
    iterate 4 orsx
    rcases ObservedReach.rs_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
    · exact (Reach.false_of_sstoreFree (E := []) rfl run.forget hT (by decide +kernel) cont).elim
    first
    | unfold ImplV2.t_3e89_c81 at run
    | unfold ImplV2_1.t_3ab2_c79 at run
    | unfold Impl.t_3ef0_c81 at run
    orsd
    iterate 4 orsx
    rw [B256.and_comm, ff20_and_adr] at run
    iterate 12 orsx
    obtain ⟨_, firstHash, run⟩ := ObservedKeccak.of_next_linked erase run hT
      (input := owner.toB256.toBytes ++ (10 : B256).toBytes) (shape := fun _ => True)
      (by exact Mem.read_two_word_writes_at_raw _ 0 _ _) (by trivial)
    simp only [show (Bytes.toB256 [0]).toNat = 0 from rfl,
      show (Bytes.toB256 [32]).toNat = 32 from rfl] at run firstHash
    rw [Mem.read_two_word_writes_at_raw] at run firstHash
    have run := run.withPrefix
    iterate 3 orsx
    rw [B256.and_comm, ff20_and_adr] at run
    iterate 9 orsx
    obtain ⟨_, secondHash, run⟩ := ObservedKeccak.of_next erase run hT
      (input := a.toB256.toBytes ++ (mapSlot owner.toB256 10).toBytes)
      (shape := fun _ => True)
      (by exact Mem.read_two_word_writes_at_raw _ 0 _ _) (by trivial)
    simp only [show (Bytes.toB256 [0]).toNat = 0 from rfl,
      show (Bytes.toB256 [32]).toNat = 32 from rfl] at run
    rw [Mem.read_two_word_writes_at_raw] at run
    iterate 2 orsx
    rcases ObservedReach.sstoreS run with rfl | ⟨d', step, _, run⟩
    · exact ⟨⟨_, rfl⟩, ⟨_, rfl⟩, _, firstHash, secondHash⟩
    exact (Reach.false_of_sstoreFree (E := []) rfl run.forget hT
      (by decide +kernel) cont).elim

/-- Caller approval is the existing specialization of the shared setter. -/
theorem approve_core_hashes {version : ModernVersion}
    {Q : Sevm → Devm → Ninst → Devm → Prop}
    (erase : ∀ {s d n d'}, Q s d n d' → Ninst.Run s d n d')
    {sevm : Sevm} {b : Devm} {a : Adr} {value : B256} {S : List B256}
    {M : Mem} {G : Nat} {K : List SFunc} {T : Conf}
    (run : ObservedReach Q observe version.cert.prog sevm
      ⟨St b (value :: a.toB256 :: sevm.caller.toB256 :: S) M G, core version .approve, K⟩ T)
    (hT : AtSstore T) (cont : ∀ f ∈ K, f.sstoreFreeIn [] = true) :
    ObservedKeccakPair Q observe version.cert.prog sevm
      (sevm.caller.toB256.toBytes ++ (10 : B256).toBytes)
      (a.toB256.toBytes ++ (mapSlot sevm.caller.toB256 10).toBytes) := by
  exact (approval_core_source erase run hT cont).2.2

/-- Increase reads the old allowance using both original hashes before its arithmetic. -/
theorem increase_core_hashes {version : ModernVersion}
    {Q : Sevm → Devm → Ninst → Devm → Prop}
    (erase : ∀ {s d n d'}, Q s d n d' → Ninst.Run s d n d')
    {sevm : Sevm} {b : Devm} {a : Adr} {value : B256} {S : List B256}
    {M : Mem} {G : Nat} {K : List SFunc} {T : Conf}
    (run : ObservedReach Q observe version.cert.prog sevm
      ⟨St b (value :: a.toB256 :: sevm.caller.toB256 :: S) M G, core version .increase, K⟩ T)
    (hT : AtSstore T) :
    ObservedKeccakPair Q observe version.cert.prog sevm
      (sevm.caller.toB256.toBytes ++ (10 : B256).toBytes)
      (a.toB256.toBytes ++ (mapSlot sevm.caller.toB256 10).toBytes) := by
  cases version
  all_goals
    simp only [core] at run
    first
    | unfold ImplV2.t_41b3_c79 at run
    | unfold ImplV2_1.t_3ddc_c77 at run
    | unfold Impl.t_436b_c102 at run
    orsd
    iterate 4 orsx
    rw [B256.and_comm, ff20_and_adr] at run
    iterate 12 orsx
    obtain ⟨_, firstHash, run⟩ := ObservedKeccak.of_next_linked erase run hT
      (input := sevm.caller.toB256.toBytes ++ (10 : B256).toBytes) (shape := fun _ => True)
      (by exact Mem.read_two_word_writes_at_raw _ 0 _ _) (by trivial)
    simp only [show (Bytes.toB256 [0]).toNat = 0 from rfl,
      show (Bytes.toB256 [32]).toNat = 32 from rfl] at run firstHash
    rw [Mem.read_two_word_writes_at_raw] at run firstHash
    have run := run.withPrefix
    iterate 3 orsx
    rw [B256.and_comm, ff20_and_adr] at run
    iterate 5 orsx
    obtain ⟨_, secondHash, _⟩ := ObservedKeccak.of_next erase run hT
      (input := a.toB256.toBytes ++ (mapSlot sevm.caller.toB256 10).toBytes)
      (shape := fun _ => True)
      (by exact Mem.read_two_word_writes_at_raw _ 0 _ _) (by trivial)
    exact ⟨_, firstHash, secondHash⟩

/-- Decrease's error-string allocation preserves the exact later mapping inputs. -/
theorem decrease_core_hashes {version : ModernVersion}
    {Q : Sevm → Devm → Ninst → Devm → Prop}
    (erase : ∀ {s d n d'}, Q s d n d' → Ninst.Run s d n d')
    {sevm : Sevm} {b : Devm} {a : Adr} {value : B256} {S : List B256}
    {M : Mem} {G : Nat} {K : List SFunc} {T : Conf}
    (run : ObservedReach Q observe version.cert.prog sevm
      ⟨St b (value :: a.toB256 :: sevm.caller.toB256 :: S) M G, core version .decrease, K⟩ T)
    (hT : AtSstore T) :
    ObservedKeccakPair Q observe version.cert.prog sevm
      (sevm.caller.toB256.toBytes ++ (10 : B256).toBytes)
      (a.toB256.toBytes ++ (mapSlot sevm.caller.toB256 10).toBytes) := by
  cases version
  all_goals
    simp only [core] at run
    first
    | unfold ImplV2.t_43fa_c75 at run
    | unfold ImplV2_1.t_4023_c72 at run
    | unfold Impl.t_4956_c92 at run
    orsd
    iterate 26 orsx
    rw [B256.and_comm, ff20_and_adr] at run
    iterate 12 orsx
    obtain ⟨_, firstHash, run⟩ := ObservedKeccak.of_next_linked erase run hT
      (input := sevm.caller.toB256.toBytes ++ (10 : B256).toBytes) (shape := fun _ => True)
      (by exact Mem.read_two_word_writes_at_raw _ 0 _ _) (by trivial)
    simp only [show (Bytes.toB256 [0]).toNat = 0 from rfl,
      show (Bytes.toB256 [32]).toNat = 32 from rfl] at run firstHash
    rw [Mem.read_two_word_writes_at_raw] at run firstHash
    have run := run.withPrefix
    iterate 3 orsx
    rw [B256.and_comm, ff20_and_adr] at run
    iterate 5 orsx
    obtain ⟨_, secondHash, _⟩ := ObservedKeccak.of_next erase run hT
      (input := a.toB256.toBytes ++ (mapSlot sevm.caller.toB256 10).toBytes)
      (shape := fun _ => True)
      (by exact Mem.read_two_word_writes_at_raw _ 0 _ _) (by trivial)
    exact ⟨_, firstHash, secondHash⟩

theorem core_hashes {version : ModernVersion} {action : Action}
    {Q : Sevm → Devm → Ninst → Devm → Prop}
    (erase : ∀ {s d n d'}, Q s d n d' → Ninst.Run s d n d')
    {sevm : Sevm} {b : Devm} {a : Adr} {value : B256} {S : List B256}
    {M : Mem} {G : Nat} {K : List SFunc} {T : Conf}
    (run : ObservedReach Q observe version.cert.prog sevm
      ⟨St b (value :: a.toB256 :: sevm.caller.toB256 :: S) M G, core version action, K⟩ T)
    (hT : AtSstore T) (cont : ∀ f ∈ K, f.sstoreFreeIn [] = true) :
    ObservedKeccakPair Q observe version.cert.prog sevm
      (sevm.caller.toB256.toBytes ++ (10 : B256).toBytes)
      (a.toB256.toBytes ++ (mapSlot sevm.caller.toB256 10).toBytes) := by
  cases action
  · exact approve_core_hashes erase run hT cont
  · exact increase_core_hashes erase run hT
  · exact decrease_core_hashes erase run hT

end Blanc.Lift.Usdc.ModernCallerReach
