import Blanc.Lift.Usdc.V22ConfigureMinterReach
import Blanc.Lift.Usdc.SelTrees
import Blanc.Lift.CursorReturnToward
import Blanc.Lift.Usdc.RefineAdminLedger

/-! Original V2.2 transfer stores, distinguished by their retained setter return tags. -/
namespace Blanc.Lift.Usdc.V22TransferReach
open Jaune Blanc Blanc.Lift
variable {observe : Conf → Conf → Prop}

/-- The original account/base9 hash and actual return tag at one successful store. -/
def StoreSource (Q : Sevm → Devm → Ninst → Devm → Prop)
    (observe : Conf → Conf → Prop) (sevm : Sevm) (account : Adr) (tag : B256)
    (T : Conf) : Prop :=
  (∃ value rest, T.d.stack = mapSlot account.toB256 9 :: value :: tag :: rest) ∧
  T.f = .next (.reg .sstore) .ret ∧
  ObservedKeccak Q observe sevm (account.toB256.toBytes ++ (9 : B256).toBytes) (fun _ => True)

/-- The packed balance query returns into its original continuation. -/
theorem balance_reach_observed {Q : Sevm → Devm → Ninst → Devm → Prop}
    (erase : ∀ {s d n d'}, Q s d n d' → Ninst.Run s d n d')
    {sevm : Sevm} {b : Devm} {account tag : B256} {S : List B256}
    {M : Mem} {G : Nat} {f : SFunc} {K : List SFunc} {T : Conf}
    (run : ObservedReach Q observe Impl.cert.prog sevm
      ⟨St b (account :: tag :: S) M G, Impl.t_41da_c96, f :: K⟩ T)
    (hT : AtSstore T) :
    ∃ b' value M' G', ObservedReach Q observe Impl.cert.prog sevm
      ⟨St b' (value :: S) M' G', f, K⟩ T := by
  unfold Impl.t_41da_c96 at run
  orsd
  iterate 12 orsx
  orsld
  iterate 3 orsx
  obtain ⟨f', K', b', G', same, run⟩ := ObservedReach.rs_retM run hT
  cases same
  exact ⟨_, _, _, _, run⟩

/-- The subtraction helper either reverts or returns before the selected store. -/
theorem sub_reach_observed {Q : Sevm → Devm → Ninst → Devm → Prop}
    (erase : ∀ {s d n d'}, Q s d n d' → Ninst.Run s d n d')
    {sevm : Sevm} {b : Devm} {x y tag : B256} {S : List B256}
    {M : Mem} {G : Nat} {f : SFunc} {K : List SFunc} {T : Conf}
    (run : ObservedReach Q observe Impl.cert.prog sevm
      ⟨St b (x :: y :: tag :: S) M G, Impl.t_4163_c100, f :: K⟩ T)
    (hT : AtSstore T) :
    ∃ b' value G', ObservedReach Q observe Impl.cert.prog sevm
      ⟨St b' (value :: S) M G', f, K⟩ T := by
  unfold Impl.t_4163_c100 at run
  orsd
  iterate 6 orsx
  rcases ObservedReach.rs_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
  · exact (Reach.false_of_sstoreFree_halting run.forget hT
      (by decide +kernel) (by decide +kernel)).elim
  unfold Impl.t_41d4_c100 at run
  orsd
  iterate 4 orsx
  obtain ⟨f', K', b', G', same, run⟩ := ObservedReach.rs_retM run hT
  cases same
  exact ⟨_, _, _, run⟩

/-- The addition helper crosses its checked return branch before the selected store. -/
theorem add_reach_observed {Q : Sevm → Devm → Ninst → Devm → Prop}
    (erase : ∀ {s d n d'}, Q s d n d' → Ninst.Run s d n d')
    {sevm : Sevm} {b : Devm} {x y tag : B256} {S : List B256}
    {M : Mem} {G : Nat} {f : SFunc} {K : List SFunc} {T : Conf}
    (run : ObservedReach Q observe Impl.cert.prog sevm
      ⟨St b (x :: y :: tag :: S) M G, Impl.t_43b5_c98, f :: K⟩ T)
    (hT : AtSstore T) :
    ∃ b' value G', ObservedReach Q observe Impl.cert.prog sevm
      ⟨St b' (value :: S) M G', f, K⟩ T := by
  unfold Impl.t_43b5_c98 at run
  orsd
  iterate 9 orsx
  rcases ObservedReach.rs_branchTo run hT with ⟨-, _, run⟩ | ⟨-, g, _, hg, run⟩
  · exact (Reach.false_of_sstoreFree_halting run.forget hT
      (by decide +kernel) (by decide +kernel)).elim
  rw [show Impl.cert.prog[7]? = some Impl.t_4429_c7 from rfl] at hg
  cases hg
  unfold Impl.t_4429_c7 at run
  orsd
  iterate 5 orsx
  obtain ⟨f', K', b', G', same, run⟩ := ObservedReach.rs_retM run hT
  cases same
  exact ⟨_, _, _, run⟩

/-- The packed blacklist query keeps the target's storage. -/
theorem blacklist_reach_valued {Q : Sevm → Devm → Ninst → Devm → Prop}
    (erase : ∀ {s d n d'}, Q s d n d' → Ninst.Run s d n d')
    {sevm : Sevm} {b : Devm} {account tag : B256} {S : List B256}
    {M : Mem} {G : Nat} {f : SFunc} {K : List SFunc} {T : Conf}
    (run : ObservedReach Q observe Impl.cert.prog sevm
      ⟨St b (account :: tag :: S) M G, Impl.t_3f6a_c83, f :: K⟩ T)
    (hT : AtSstore T) :
    ∃ b' value M' G', (∀ k, b'.getStorVal sevm.currentTarget k = b.getStorVal sevm.currentTarget k) ∧
      ObservedReach Q observe Impl.cert.prog sevm ⟨St b' (value :: S) M' G', f, K⟩ T := by
  unfold Impl.t_3f6a_c83 at run
  orsd
  iterate 12 orsx
  obtain ⟨loadedPost, loadStep, run⟩ := ObservedReach.rs_next run hT
  have loadRun := erase loadStep
  obtain ⟨key, rest, pop, push⟩ := of_run_sload loadRun
  simp only [Stack.Pop, Stack.Push, Split, St.stack, List.cons_append, List.nil_append,
    List.cons.injEq] at pop push
  obtain ⟨rfl, rfl⟩ := pop
  rw [St.self push (SolcStorageReturn.sload_memory loadRun), St.getStorVal] at run
  have storage := Devm.getStorVal_of_state (of_run_sload_state loadRun) sevm.currentTarget
  simp only [St.getStorVal] at storage
  iterate 5 orsx
  obtain ⟨f', K', G', same, run⟩ := ObservedReach.rs_retBase run hT
  cases same
  exact ⟨_, _, _, _, fun k => (storage k).symm, run⟩

/-- The packed blacklist query returns into its original continuation. -/
theorem blacklist_reach_observed {Q : Sevm → Devm → Ninst → Devm → Prop}
    (erase : ∀ {s d n d'}, Q s d n d' → Ninst.Run s d n d')
    {sevm : Sevm} {b : Devm} {account tag : B256} {S : List B256}
    {M : Mem} {G : Nat} {f : SFunc} {K : List SFunc} {T : Conf}
    (run : ObservedReach Q observe Impl.cert.prog sevm
      ⟨St b (account :: tag :: S) M G, Impl.t_3f6a_c83, f :: K⟩ T)
    (hT : AtSstore T) :
    ∃ b' value M' G', ObservedReach Q observe Impl.cert.prog sevm
      ⟨St b' (value :: S) M' G', f, K⟩ T :=
  have ⟨b', value, M', G', _, reach⟩ := blacklist_reach_valued erase run hT
  ⟨b', value, M', G', reach⟩

/-- The packed balance query returns the low bits of the account's entry and keeps the storage. -/
theorem balance_reach_valued {Q : Sevm → Devm → Ninst → Devm → Prop}
    (erase : ∀ {s d n d'}, Q s d n d' → Ninst.Run s d n d')
    {sevm : Sevm} {b : Devm} {account : Adr} {tag : B256} {S : List B256}
    {M : Mem} {G : Nat} {f : SFunc} {K : List SFunc} {T : Conf}
    (run : ObservedReach Q observe Impl.cert.prog sevm
      ⟨St b (account.toB256 :: tag :: S) M G, Impl.t_41da_c96, f :: K⟩ T)
    (hT : AtSstore T) :
    ∃ b' M' G', (∀ k, b'.getStorVal sevm.currentTarget k = b.getStorVal sevm.currentTarget k) ∧
      ObservedReach Q observe Impl.cert.prog sevm
        ⟨St b' ((lo255 &&& b.getStorVal sevm.currentTarget (mapSlot account.toB256 9)) :: S) M' G',
          f, K⟩ T := by
  unfold Impl.t_41da_c96 at run
  orsd
  iterate 12 orsx
  rw [show Bytes.toB256 [0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,
      0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff] = ff20 from rfl,
    ff20_and_adr, keccak_scratch,
    show Bytes.toB256 [9] = (9 : B256) from rfl] at run
  obtain ⟨loadedPost, loadStep, run⟩ := ObservedReach.rs_next run hT
  have loadRun := erase loadStep
  obtain ⟨key, rest, pop, push⟩ := of_run_sload loadRun
  simp only [Stack.Pop, Stack.Push, Split, St.stack, List.cons_append, List.nil_append,
    List.cons.injEq] at pop push
  obtain ⟨rfl, rfl⟩ := pop
  rw [St.self push (SolcStorageReturn.sload_memory loadRun), St.getStorVal] at run
  have storage := Devm.getStorVal_of_state (of_run_sload_state loadRun) sevm.currentTarget
  simp only [St.getStorVal] at storage
  iterate 3 orsx
  obtain ⟨f', K', G', same, run⟩ := ObservedReach.rs_retBase run hT
  cases same
  exact ⟨_, _, _, fun k => (storage k).symm, run⟩

/-- The addition helper returns the unwrapped sum over the same base. -/
theorem add_reach_valued {Q : Sevm → Devm → Ninst → Devm → Prop}
    (erase : ∀ {s d n d'}, Q s d n d' → Ninst.Run s d n d')
    {sevm : Sevm} {b : Devm} {x y tag : B256} {S : List B256}
    {M : Mem} {G : Nat} {f : SFunc} {K : List SFunc} {T : Conf}
    (run : ObservedReach Q observe Impl.cert.prog sevm
      ⟨St b (x :: y :: tag :: S) M G, Impl.t_43b5_c98, f :: K⟩ T)
    (hT : AtSstore T) :
    (x + y).toNat = x.toNat + y.toNat ∧ ∃ G', ObservedReach Q observe Impl.cert.prog sevm
      ⟨St b ((x + y) :: S) M G', f, K⟩ T := by
  unfold Impl.t_43b5_c98 at run
  orsd
  iterate 9 orsx
  rcases ObservedReach.rs_branchTo run hT with ⟨-, _, run⟩ | ⟨safe, g, _, hg, run⟩
  · exact (Reach.false_of_sstoreFree_halting run.forget hT
      (by decide +kernel) (by decide +kernel)).elim
  rw [show Impl.cert.prog[7]? = some Impl.t_4429_c7 from rfl] at hg
  cases hg
  unfold Impl.t_4429_c7 at run
  orsd
  iterate 5 orsx
  obtain ⟨f', K', G', same, run⟩ := ObservedReach.rs_retBase run hT
  cases same
  exact ⟨(add_nof_of_ltCheck (eq_zero_of_iszero_ne_zero safe)).2, _, run⟩

/-- The shared setter either is this store or returns to its original continuation.
The store retains its actual return tag, its own successful mapping hash and its value, whose bits are
the whole word, over the storage the setter was entered on. -/
theorem setter_reach_valued {Q : Sevm → Devm → Ninst → Devm → Prop}
    (erase : ∀ {s d n d'}, Q s d n d' → Ninst.Run s d n d')
    {sevm : Sevm} {b : Devm} {value tag : B256} {account : Adr} {S : List B256}
    {M : Mem} {G : Nat} {f : SFunc} {K : List SFunc} {T : Conf}
    (run : ObservedReach Q observe Impl.cert.prog sevm
      ⟨St b (value :: account.toB256 :: tag :: S) M G, Impl.t_4430_c99, f :: K⟩ T)
    (hT : AtSstore T) :
    (StoreSource Q observe sevm account tag T ∧ balanceBits value = value.toNat ∧
        (∃ rest, T.d.stack = mapSlot account.toB256 9 :: value :: rest) ∧
        ∀ k, T.d.getStorVal sevm.currentTarget k = b.getStorVal sevm.currentTarget k) ∨
      ∃ b' M' G', ObservedReach Q observe Impl.cert.prog sevm
        ⟨St b' S M' G', f, K⟩ T := by
  unfold Impl.t_4430_c99 at run
  orsd
  iterate 5 orsx
  rcases ObservedReach.rs_branch run hT with ⟨-, _, run⟩ | ⟨safe, _, run⟩
  · exact (Reach.false_of_sstoreFree_halting run.forget hT
      (by decide +kernel) (by decide +kernel)).elim
  have bits : balanceBits value = value.toNat :=
    balanceBits_of_le (eq_zero_of_iszero_ne_zero safe)
  unfold Impl.t_44a9_c99 at run
  orsd
  iterate 3 orsx
  obtain ⟨g, _, hg, run⟩ := ObservedReach.rs_callIn run hT
  rw [show Impl.cert.prog[83]? = some Impl.t_3f6a_c83 from rfl] at hg
  cases hg
  obtain ⟨_, _, _, _, keep, run⟩ := blacklist_reach_valued erase run hT
  unfold Impl.t_44b2_c99 at run
  orsd
  iterate 2 orsx
  rcases ObservedReach.rs_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
  · exact (Reach.false_of_sstoreFree_halting run.forget hT
      (by decide +kernel) (by decide +kernel)).elim
  unfold Impl.t_4508_c99 at run
  orsd
  iterate 4 orsx
  rw [show Bytes.toB256 [0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,
      0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff] = ff20 from rfl,
    B256.and_comm account.toB256 ff20, ff20_and_adr] at run
  iterate 9 orsx
  obtain ⟨_, hash, run⟩ := ObservedKeccak.of_next erase run hT
    (input := account.toB256.toBytes ++ (9 : B256).toBytes) (shape := fun _ => True)
    (by exact Mem.read_two_word_writes_at_raw _ 0 _ _) (by trivial)
  simp only [show (Bytes.toB256 [0]).toNat = 0 from rfl,
    show (Bytes.toB256 [32]).toNat = 32 from rfl] at run
  rw [Mem.read_two_word_writes_at_raw] at run
  rcases ObservedReach.sstoreS run with rfl | ⟨d', step, _, run⟩
  · exact .inl ⟨⟨⟨_, _, rfl⟩, rfl, hash⟩, bits, ⟨_, rfl⟩, keep⟩
  obtain ⟨b', G', rfl⟩ := SolcStorageReturn.ri_sstore_any (erase step)
  obtain ⟨f', K', b'', G'', same, run⟩ := ObservedReach.rs_retM run hT
  cases same
  exact .inr ⟨_, _, _, run⟩

/-- The shared setter either is this store or returns to its original continuation.
The store retains its actual return tag and its own successful mapping hash. -/
theorem setter_reach_observed {Q : Sevm → Devm → Ninst → Devm → Prop}
    (erase : ∀ {s d n d'}, Q s d n d' → Ninst.Run s d n d')
    {sevm : Sevm} {b : Devm} {value tag : B256} {account : Adr} {S : List B256}
    {M : Mem} {G : Nat} {f : SFunc} {K : List SFunc} {T : Conf}
    (run : ObservedReach Q observe Impl.cert.prog sevm
      ⟨St b (value :: account.toB256 :: tag :: S) M G, Impl.t_4430_c99, f :: K⟩ T)
    (hT : AtSstore T) :
    StoreSource Q observe sevm account tag T ∨
      ∃ b' M' G', ObservedReach Q observe Impl.cert.prog sevm
        ⟨St b' S M' G', f, K⟩ T :=
  (setter_reach_valued erase run hT).imp (·.1) id

def ObservedSource (Q : Sevm → Devm → Ninst → Devm → Prop)
    (observe : Conf → Conf → Prop) (sevm : Sevm) (owner recipient : Adr) (T : Conf) : Prop :=
  StoreSource Q observe sevm owner 0x40e8 T ∨ StoreSource Q observe sevm recipient 0x40f9 T

/-- The recipient alternative also retains that the store's bits do not fall. -/
def CreditSource (Q : Sevm → Devm → Ninst → Devm → Prop)
    (observe : Conf → Conf → Prop) (sevm : Sevm) (owner recipient : Adr) (T : Conf) : Prop :=
  StoreSource Q observe sevm owner 0x40e8 T ∨ (StoreSource Q observe sevm recipient 0x40f9 T ∧
    ∀ value rest, T.d.stack = mapSlot recipient.toB256 9 :: value :: rest →
      balanceBits (T.d.getStorVal sevm.currentTarget (mapSlot recipient.toB256 9)) ≤
        balanceBits value)

theorem CreditSource.forget {Q : Sevm → Devm → Ninst → Devm → Prop}
    {sevm : Sevm} {owner recipient : Adr} {T : Conf}
    (source : CreditSource Q observe sevm owner recipient T) :
    ObservedSource Q observe sevm owner recipient T :=
  source.imp id (·.1)

/-- The second setter call carries the recipient tag through its actual helpers. -/
theorem credit_reach_credit {Q : Sevm → Devm → Ninst → Devm → Prop}
    (erase : ∀ {s d n d'}, Q s d n d' → Ninst.Run s d n d')
    {sevm : Sevm} {b : Devm} {amount : B256} {owner recipient : Adr} {S : List B256}
    {M : Mem} {G : Nat} {K : List SFunc} {T : Conf}
    (run : ObservedReach Q observe Impl.cert.prog sevm
      ⟨St b (amount :: recipient.toB256 :: owner.toB256 :: S) M G, Impl.t_40e8_c93, K⟩ T)
    (hT : AtSstore T) (cont : ∀ f ∈ K, f.sstoreFreeIn [] = true) :
    CreditSource Q observe sevm owner recipient T := by
  unfold Impl.t_40e8_c93 at run
  orsd
  iterate 7 orsx
  obtain ⟨g, _, hg, run⟩ := ObservedReach.rs_callIn run hT
  rw [show Impl.cert.prog[96]? = some Impl.t_41da_c96 from rfl] at hg
  cases hg
  obtain ⟨b₁, _, _, keep₁, run⟩ := balance_reach_valued erase run hT
  unfold Impl.t_21c9_c93 at run
  orsd
  iterate 2 orsx
  obtain ⟨g, _, hg, run⟩ := ObservedReach.rs_callIn run hT
  rw [show Impl.cert.prog[98]? = some Impl.t_43b5_c98 from rfl] at hg
  cases hg
  obtain ⟨sum, _, run⟩ := add_reach_valued erase run hT
  unfold Impl.t_21cf_c93_1 at run
  orsd
  orsx
  obtain ⟨g, _, hg, run⟩ := ObservedReach.rs_callIn run hT
  rw [show Impl.cert.prog[99]? = some Impl.t_4430_c99 from rfl] at hg
  cases hg
  rcases setter_reach_valued erase run hT with ⟨source, bits, ⟨rest, stack⟩, keep⟩ | ⟨_, _, _, run⟩
  · refine .inr ⟨source, fun value other same => ?_⟩
    have word := (List.cons.inj (List.cons.inj (stack.symm.trans same)).2).1
    subst word
    rw [bits, keep, keep₁, sum, lo255_and_toNat]
    omega
  exact (Reach.false_of_sstoreFree (E := []) rfl run.forget hT
    (by decide +kernel) cont).elim

/-- The first setter call retains the owner tag, then continues to the recipient. -/
theorem debit_reach_credit {Q : Sevm → Devm → Ninst → Devm → Prop}
    (erase : ∀ {s d n d'}, Q s d n d' → Ninst.Run s d n d')
    {sevm : Sevm} {b : Devm} {amount : B256} {owner recipient : Adr} {S : List B256}
    {M : Mem} {G : Nat} {K : List SFunc} {T : Conf}
    (run : ObservedReach Q observe Impl.cert.prog sevm
      ⟨St b (amount :: recipient.toB256 :: owner.toB256 :: S) M G, Impl.t_40d1_c93, K⟩ T)
    (hT : AtSstore T) (cont : ∀ f ∈ K, f.sstoreFreeIn [] = true) :
    CreditSource Q observe sevm owner recipient T := by
  unfold Impl.t_40d1_c93 at run
  orsd
  iterate 7 orsx
  obtain ⟨g, _, hg, run⟩ := ObservedReach.rs_callIn run hT
  rw [show Impl.cert.prog[96]? = some Impl.t_41da_c96 from rfl] at hg
  cases hg
  obtain ⟨_, _, _, _, run⟩ := balance_reach_observed erase run hT
  unfold Impl.t_40e2_c93 at run
  orsd
  iterate 2 orsx
  obtain ⟨g, _, hg, run⟩ := ObservedReach.rs_callIn run hT
  rw [show Impl.cert.prog[100]? = some Impl.t_4163_c100 from rfl] at hg
  cases hg
  obtain ⟨_, _, _, run⟩ := sub_reach_observed erase run hT
  unfold Impl.t_21cf_c93 at run
  orsd
  orsx
  obtain ⟨g, _, hg, run⟩ := ObservedReach.rs_callIn run hT
  rw [show Impl.cert.prog[99]? = some Impl.t_4430_c99 from rfl] at hg
  cases hg
  rcases setter_reach_observed erase run hT with source | ⟨_, _, _, run⟩
  · exact .inl source
  exact credit_reach_credit erase run hT cont

/-- The actual internal transfer guards lead to the two original setter calls. -/
theorem body_reach_credit {Q : Sevm → Devm → Ninst → Devm → Prop}
    (erase : ∀ {s d n d'}, Q s d n d' → Ninst.Run s d n d')
    {sevm : Sevm} {b : Devm} {amount : B256} {owner recipient : Adr} {S : List B256}
    {M : Mem} {G : Nat} {K : List SFunc} {T : Conf}
    (run : ObservedReach Q observe Impl.cert.prog sevm
      ⟨St b (amount :: recipient.toB256 :: owner.toB256 :: S) M G, Impl.t_3f98_c93, K⟩ T)
    (hT : AtSstore T) (cont : ∀ f ∈ K, f.sstoreFreeIn [] = true) :
    CreditSource Q observe sevm owner recipient T := by
  unfold Impl.t_3f98_c93 at run
  orsd
  iterate 4 orsx
  rcases ObservedReach.rs_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
  · exact (Reach.false_of_sstoreFree_halting run.forget hT
      (by decide +kernel) (by decide +kernel)).elim
  unfold Impl.t_4004_c93 at run
  orsd
  iterate 4 orsx
  rcases ObservedReach.rs_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
  · exact (Reach.false_of_sstoreFree_halting run.forget hT
      (by decide +kernel) (by decide +kernel)).elim
  unfold Impl.t_4070_c93 at run
  orsd
  iterate 3 orsx
  obtain ⟨g, _, hg, run⟩ := ObservedReach.rs_callIn run hT
  rw [show Impl.cert.prog[96]? = some Impl.t_41da_c96 from rfl] at hg
  cases hg
  obtain ⟨_, _, _, _, run⟩ := balance_reach_observed erase run hT
  unfold Impl.t_4079_c93 at run
  orsd
  iterate 4 orsx
  rcases ObservedReach.rs_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
  · exact (Reach.false_of_sstoreFree_halting run.forget hT
      (by decide +kernel) (by decide +kernel)).elim
  exact debit_reach_credit erase run hT cont

/-- Original interface of the internal transfer walk. -/
theorem body_reach_observed {Q : Sevm → Devm → Ninst → Devm → Prop}
    (erase : ∀ {s d n d'}, Q s d n d' → Ninst.Run s d n d')
    {sevm : Sevm} {b : Devm} {amount : B256} {owner recipient : Adr} {S : List B256}
    {M : Mem} {G : Nat} {K : List SFunc} {T : Conf}
    (run : ObservedReach Q observe Impl.cert.prog sevm
      ⟨St b (amount :: recipient.toB256 :: owner.toB256 :: S) M G, Impl.t_3f98_c93, K⟩ T)
    (hT : AtSstore T) (cont : ∀ f ∈ K, f.sstoreFreeIn [] = true) :
    ObservedSource Q observe sevm owner recipient T :=
  (body_reach_credit erase run hT cont).forget

/-- The checked dispatcher routes transfer through its original ABI wrapper. -/
theorem route_transfer : Impl.selTree.selWalk 0xa9059cbb =
    .inl (Bytes.toB256 [0xa9, 0x05, 0x9c, 0xbb], 145) := by
  decide +kernel

/-- Follow the selected prefix to its store; the final frame outcome is unrestricted. -/
theorem transfer_reach_observed {Q : Sevm → Devm → Ninst → Devm → Prop}
    (erase : ∀ {s d n d'}, Q s d n d' → Ninst.Run s d n d')
    {sevm : Sevm} {b : Devm} {S : List B256} {M : Mem} {G : Nat} {T : Conf}
    (selected : Blanc.Sevm.selector sevm = 0xa9059cbb)
    (run : ObservedReach Q observe Impl.cert.prog sevm
      ⟨St b S M G, Impl.t_0000_c0, []⟩ T)
    (hT : AtSstore T) : ObservedSource Q observe sevm sevm.caller (Sevm.dataWord sevm 4).toAdr T := by
  unfold Impl.t_0000_c0 at run
  iterate 7 orsx
  rcases ObservedReach.rs_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
  · exact (Reach.false_of_sstoreFree (E := []) rfl run.forget hT (by decide +kernel)
      (fun _ h => by cases h)).elim
  unfold Impl.t_0010_c0 at run
  orsd
  iterate 5 orsx
  rcases ObservedReach.rs_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
  swap
  · exact (Reach.false_of_sstoreFree (E := []) rfl run.forget hT (by decide +kernel)
      (fun _ h => by cases h)).elim
  unfold Impl.t_001a_c0 at run
  iterate 4 orsx
  have word : Sevm.dataWord sevm (Bytes.toB256 [0]) >>> (Bytes.toB256 [0xe0]).toNat =
      0xa9059cbb := selected
  rw [word] at run
  obtain ⟨-, g, _, hg, run⟩ := ObservedReach.selWalk_inlS erase route_transfer run hT
  rw [show Impl.cert.prog[145]? = some Impl.t_0c9b_c145 from rfl] at hg
  cases hg
  unfold Impl.t_0c9b_c145 at run
  orsd
  iterate 10 orsx
  rcases ObservedReach.rs_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
  · exact (Reach.false_of_sstoreFree (E := []) rfl run.forget hT (by decide +kernel)
      (fun _ h => by cases h)).elim
  unfold Impl.t_0cb1_c145 at run
  orsd
  iterate 10 orsx
  rw [show Bytes.toB256 [0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,
      0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff] = ff20 from rfl,
    B256.and_comm (Sevm.dataWord sevm (Bytes.toB256 [4])) ff20] at run
  rw [ff20_and_word] at run
  obtain ⟨g, _, hg, run⟩ := ObservedReach.rs_callIn run hT
  rw [show Impl.cert.prog[37]? = some Impl.t_2fa6_c37 from rfl] at hg
  cases hg
  have cont : ∀ f ∈ [Impl.t_0428_c145], f.sstoreFreeIn [] = true := by
    intro f member
    have same := List.mem_singleton.mp member
    subst f
    decide +kernel
  unfold Impl.t_2fa6_c37 at run
  orsd
  orsx
  orsld
  iterate 9 orsx
  rcases ObservedReach.rs_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
  · exact (Reach.false_of_sstoreFree (E := []) rfl run.forget hT (by decide +kernel) cont).elim
  unfold Impl.t_3033_c37 at run
  orsd
  iterate 4 orsx
  obtain ⟨g, _, hg, run⟩ := ObservedReach.rs_callIn run hT
  rw [show Impl.cert.prog[83]? = some Impl.t_3f6a_c83 from rfl] at hg
  cases hg
  obtain ⟨_, _, _, _, run⟩ := blacklist_reach_observed erase run hT
  unfold Impl.t_303d_c37 at run
  orsd
  iterate 2 orsx
  rcases ObservedReach.rs_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
  · exact (Reach.false_of_sstoreFree_halting run.forget hT
      (by decide +kernel) (by decide +kernel)).elim
  unfold Impl.t_3093_c37 at run
  orsd
  iterate 4 orsx
  obtain ⟨g, _, hg, run⟩ := ObservedReach.rs_callIn run hT
  rw [show Impl.cert.prog[83]? = some Impl.t_3f6a_c83 from rfl] at hg
  cases hg
  obtain ⟨_, _, _, _, run⟩ := blacklist_reach_observed erase run hT
  unfold Impl.t_309d_c37 at run
  orsd
  iterate 2 orsx
  rcases ObservedReach.rs_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
  · exact (Reach.false_of_sstoreFree_halting run.forget hT
      (by decide +kernel) (by decide +kernel)).elim
  unfold Impl.t_30f3_c37 at run
  orsd
  iterate 5 orsx
  obtain ⟨g, _, hg, run⟩ := ObservedReach.rs_callIn run hT
  rw [show Impl.cert.prog[93]? = some Impl.t_3f98_c93 from rfl] at hg
  cases hg
  apply body_reach_observed erase run hT
  intro f member
  rcases List.mem_cons.mp member with rfl | member
  · decide +kernel
  exact cont f member

/-- Every selected successful store retains its actual call tag, key and earlier hash. -/
theorem successfulSstore_source {root node : Exec.Deriv}
    (pc : root.pc = 0) (code : root.sevm.code = Impl.code)
    (hsg : root.sevm.benvStat.rules.stateGas = none)
    (chain : Exec.Deriv.ParentPrefix root node)
    (selected : Blanc.Sevm.selector root.sevm = 0xa9059cbb)
    {write : Exec.StorageWrite} (found : Exec.Deriv.successfulSstore? node = some write) :
    (node.devm.stack[2]? = some 0x40e8 ∧ write.key = mapSlot root.sevm.caller.toB256 9 ∧
      ∃ hashPc, KeccakBefore root node
        (root.sevm.caller.toB256.toBytes ++ (9 : B256).toBytes) hashPc) ∨
    (node.devm.stack[2]? = some 0x40f9 ∧
      write.key = mapSlot (Sevm.dataWord root.sevm 4).toAdr.toB256 9 ∧
      ∃ hashPc, KeccakBefore root node
        ((Sevm.dataWord root.sevm 4).toAdr.toB256.toBytes ++ (9 : B256).toBytes) hashPc) := by
  obtain ⟨decoded, rest, stack⟩ := Exec.Deriv.successfulSstore?_decoded found
  obtain ⟨κ, reach, ok⟩ :=
    observed_reach_of_parentPrefix_noStateGas Impl.cert_check pc code hsg chain
  obtain ⟨g, tree, -⟩ := ok.tree_of_sstore decoded
  have target : AtSstore (κ.conf node.devm) := ⟨g, tree⟩
  have walk := reach
  change ObservedReach (StepIn root) (Cursor.RawEdgeAt Impl.code Impl.cert root node)
    Impl.cert.prog root.sevm ⟨root.devm, Impl.t_0000_c0, []⟩ (κ.conf node.devm) at walk
  rw [St.self' root.devm] at walk
  rcases transfer_reach_observed (fun h => StepIn.toRun h) selected walk target with
    ⟨⟨value, other, keyStack⟩, _, hash⟩ | ⟨⟨value, other, keyStack⟩, _, hash⟩
  · obtain ⟨occ, next, here, instruction, result, before, edge, after, _, _, hashStack, read⟩ :=
      hash.actual
    exact .inl ⟨by change node.devm.stack = _ at keyStack; rw [keyStack]; rfl,
      (List.cons.inj (stack.symm.trans keyStack)).1,
      _, occ, next, rfl, instruction, result, before, edge, after, hashStack, read⟩
  · obtain ⟨occ, next, here, instruction, result, before, edge, after, _, _, hashStack, read⟩ :=
      hash.actual
    exact .inr ⟨by change node.devm.stack = _ at keyStack; rw [keyStack]; rfl,
      (List.cons.inj (stack.symm.trans keyStack)).1,
      _, occ, next, rfl, instruction, result, before, edge, after, hashStack, read⟩

end Blanc.Lift.Usdc.V22TransferReach
