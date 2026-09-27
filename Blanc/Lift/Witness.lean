import Blanc.Lift.WitnessArms

/-!
# Executable witnesses for lifted certificates

`lift_exactM` turns an `SProg.RunExact` over a checked certificate into a Jaune
`Exec`.  This module produces such a run for a *concrete* start state by
kernel evaluation of a small interpreter, `wrun`, over the certificate's own
tree.  The tree carries each instruction already decoded, so the interpreter
never reads the runtime bytes (no `ByteArray` code reads, no `jumpable`);
jumps are `fs[k]?` lookups.

Each node is executed by Jaune's own `Ninst.step`, except where Jaune's step
tests warm/cold access (`SLOAD`, `SSTORE`): `Std.HashSet` membership does not
reduce in the kernel (its bucket index goes through the opaque
`System.Platform.numBits`).  There the interpreter decides membership on a
list shadow of the accessed-key set and takes the post-state from the
forward lemmas `Ninst.runCompiled_sload_warm`/`_cold` and
`Ninst.runCompiled_sstore_warm`/`_cold`; the shadow agrees with the set
(`Agree`) because every other executed instruction keeps the accessed sets
(`ninstAccKeeps_run`).  The resulting states still carry Jaune's own
`HashSet.insert` terms; the kernel builds them but never inspects them.

`wrun_exact` is the soundness theorem: a successful evaluation gives the
continuation-stack form `RunK` of `SFunc.RunExact` (`wrun_cont`, `wrun_done`),
and a run that halts from entry `0` with an empty stack is `SProg.RunExact`.
Chunks compose through `wrun_add`/`wrun_add_cont`.  The interpreter and its
instruction arms are in `Blanc/Lift/WitnessArms.lean`; this module holds their
soundness.  Nothing here is contract-specific.
-/

namespace Blanc.Lift.Witness

open Jaune Blanc.Lift

/-! ## Soundness -/

/-- `SFunc.RunExact` with a stack of pending internal-call continuations:
the current callee returns into the first, or the whole frame halts. -/
def RunK (fs : List SFunc) (sevm : Sevm) : Devm → SFunc → List SFunc → Outcome → Prop
  | devm, f, [], o => SFunc.RunExact fs sevm devm f o
  | devm, f, g :: K, o =>
    (∃ d, SFunc.RunExact fs sevm devm f (.returned d) ∧ RunK fs sevm d g K o) ∨
      (∃ d, o = .halted d ∧ SFunc.RunExact fs sevm devm f (.halted d))

/-- The shadows are the accessed-key and accessed-address sets, the world's storage
and the world's accounts. -/
def Agree (c : Cfg) : Prop :=
  (∀ x, x ∈ c.devm.accessedStorageKeys ↔ x ∈ c.keys) ∧
    (∀ a, a ∈ c.devm.accessedAddresses ↔ a ∈ c.adrs) ∧
    (∀ a k, storOf c.devm.state a k = lookupS c.stor a k) ∧
    AcctAgree c.devm.state c.acs

theorem RunK.lift {fs : List SFunc} {sevm : Sevm} {devm devm' : Devm} {f f' : SFunc}
    (h : ∀ o, SFunc.RunExact fs sevm devm' f' o → SFunc.RunExact fs sevm devm f o) :
    ∀ {K o}, RunK fs sevm devm' f' K o → RunK fs sevm devm f K o
  | [], _, r => h _ r
  | _ :: _, _, .inl ⟨d, r, rest⟩ => .inl ⟨d, h _ r, rest⟩
  | _ :: _, _, .inr ⟨d, ho, r⟩ => .inr ⟨d, ho, h _ r⟩

theorem RunK.halted {fs : List SFunc} {sevm : Sevm} {devm d : Devm} {f : SFunc}
    (h : SFunc.RunExact fs sevm devm f (.halted d)) : ∀ {K}, RunK fs sevm devm f K (.halted d)
  | [] => h
  | _ :: _ => .inr ⟨d, rfl, h⟩

theorem popBurnBy1 {devm : Devm} {x : B256} {s : List B256} {cost : Nat}
    (hs : devm.stack = x :: s) (hg : cost ≤ devm.gasLeft) :
    Devm.PopBurnBy [x] cost devm (mach' devm s cost) :=
  Devm.popBurnBy_setMach hs (by omega)

theorem popBurnBy2 {devm : Devm} {x w : B256} {s : List B256} {cost : Nat}
    (hs : devm.stack = x :: w :: s) (hg : cost ≤ devm.gasLeft) :
    Devm.PopBurnBy [x, w] cost devm (mach' devm s cost) :=
  { stack := hs, memory := rfl, gasLeft := by simp [mach']; omega,
    logs := rfl, refundCounter := rfl, output := rfl, accountsToDelete := rfl,
    returnData := rfl, error := rfl, accessedAddresses := rfl,
    accessedStorageKeys := rfl, state := rfl, createdAccounts := rfl,
    transientStorage := rfl, stateGas := rfl, accountReads := rfl,
    storageReads := rfl }

/-- A step to a configuration: agreement is kept, and a run from the new
configuration is a run from the old one. -/
def StepOk (fs : List SFunc) (sevm : Sevm) (c c' : Cfg) : Prop :=
  (Agree c → Agree c') ∧ ∀ o, Agree c → RunK fs sevm c'.devm c'.f c'.K o → RunK fs sevm c.devm c.f c.K o

theorem StepOk.same {fs : List SFunc} {sevm : Sevm} {c c' : Cfg} (hk : c'.keys = c.keys)
    (hA : c'.adrs = c.adrs) (hS : c'.stor = c.stor) (hC : c'.acs = c.acs)
    (ha : AccKeep c.devm c'.devm) (hK : c'.K = c.K)
    (h : ∀ o, SFunc.RunExact fs sevm c'.devm c'.f o → SFunc.RunExact fs sevm c.devm c.f o) :
    StepOk fs sevm c c' := by
  refine ⟨fun hc => ⟨fun x => ?_, fun a => ?_, fun a k => ?_, fun a => ?_⟩, fun o _ r => ?_⟩
  · rw [ha.2.1, hk]; exact hc.1 x
  · rw [ha.1, hA]; exact hc.2.1 a
  · rw [ha.2.2, hS]; exact hc.2.2.1 a k
  · rw [ha.2.2, hC]; exact hc.2.2.2 a
  · rw [hK] at r; exact RunK.lift h r

theorem pc_step_accKeep {sevm : Sevm} {devm d : Devm} {p q : Nat}
    (h : Ninst.step ⟨p, sevm, devm⟩ (.reg .pc) = .cont q d) : AccKeep devm d := by
  rw [Ninst.step_reg] at h
  unfold Step.ofExecution at h
  split at h
  · cases h
  · cases h
    rename_i hd
    exact accKeep_pushItem hd

theorem keys_addAccessedStorageKey (d : Devm) (a : Adr) (k : B256) :
    (addAccessedStorageKey d a k).accessedStorageKeys = d.accessedStorageKeys.insert (a, k) := rfl

theorem agree_insert {d : Devm} {keys : List (Adr × B256)} {a : Adr} {k : B256}
    (hc : ∀ x, x ∈ d.accessedStorageKeys ↔ x ∈ keys) :
    ∀ x, x ∈ (addAccessedStorageKey d a k).accessedStorageKeys ↔ x ∈ (a, k) :: keys := by
  intro x
  rw [keys_addAccessedStorageKey, Std.HashSet.mem_insert, List.mem_cons, hc x, beq_iff_eq]
  constructor <;> rintro (h | h) <;> first | exact .inl h.symm | exact .inr h

theorem StepOk.of {fs : List SFunc} {sevm : Sevm} {c c' : Cfg} (hk : Agree c → Agree c')
    (hK : c'.K = c.K)
    (h : Agree c → ∀ o, SFunc.RunExact fs sevm c'.devm c'.f o → SFunc.RunExact fs sevm c.devm c.f o) :
    StepOk fs sevm c c' := by
  refine ⟨hk, fun o hc r => ?_⟩
  rw [hK] at r; exact RunK.lift (h hc) r

theorem storOf_setStorVal (st : State) (ct a : Adr) (k k' v : B256) :
    storOf (st.setStorVal ct k v) a k' = if ct = a ∧ k = k' then v else storOf st a k' := by
  unfold storOf State.setStorVal
  by_cases h : ct = a
  · subst h; rw [State.get_set_self]; simp only [true_and]; exact Stor.get_set_ite _ _ _ _
  · rw [State.get_set_ne _ h]; simp [h]

/-- A storage-empty state agrees with the empty storage shadow `[]`. -/
theorem storAgree_nil {st : State} (h : ∀ a k, storOf st a k = 0) :
    ∀ a k, storOf st a k = lookupS [] a k := by
  intro a k
  rw [h a k]
  rfl

theorem storOf_empty (a : Adr) (k : B256) : storOf (default : State) a k = 0 := rfl

/-- Setting an account with empty storage preserves storage-emptiness. -/
theorem storOf_set_empty (st : State) (p a : Adr) (ac : Acct) (k : B256)
    (h_st : storOf st a k = 0) (h_ac : ac.stor.get k = 0) :
    storOf (st.set p ac) a k = 0 := by
  unfold storOf
  by_cases h : p = a
  · subst h; rw [State.get_set_self]; exact h_ac
  · rw [State.get_set_ne _ h]; exact h_st

/-- Setting an account with empty storage via `stateSetB` preserves storage-emptiness. -/
theorem storOf_stateSetB_empty (st : State) (p a : Adr) (ac : Acct) (k : B256)
    (h_st : storOf st a k = 0) (h_ac : ac.stor.get k = 0) :
    storOf (stateSetB st p ac) a k = 0 := by
  rw [← state_set_eq_setB]
  exact storOf_set_empty st p a ac k h_st h_ac

/-- Writing `(ct, k, v)` into a state (via `stateSetStorValB`) and prepending to the shadow
preserves storage agreement. -/
theorem storOf_stateSetStorValB {st : State} {l : StorShadow} {ct : Adr} {k v : B256}
    (h : ∀ a k, storOf st a k = lookupS l a k) :
    ∀ a k', storOf (stateSetStorValB st ct k v) a k' = lookupS (((ct, k), v) :: l) a k' := by
  intro a k'
  rw [← state_setStorVal_eq_B]
  rw [storOf_setStorVal]
  simp only [lookupS]
  split
  · rfl
  · exact h a k'

/-- A storage write moves the storage shadow by one entry. -/
theorem storOf_sstore {d : Devm} {l : StorShadow} {ct : Adr} {k v : B256}
    (h : ∀ a k, storOf d.state a k = lookupS l a k) :
    ∀ a k', storOf (devmSetStorValB d ct k v).state a k' = lookupS (((ct, k), v) :: l) a k' :=
  storOf_stateSetStorValB h

/-- Apply a list of storage writes to a world state, in order. -/
def stateFoldStor (st : State) (writes : List ((Adr × B256) × B256)) : State :=
  writes.foldl (fun s ((a, k), v) => stateSetStorValB s a k v) st

/-- Storage shadow constructed by folding writes (newest first). -/
def storShadowOf (writes : List ((Adr × B256) × B256)) : StorShadow :=
  writes.foldl (fun s w => w :: s) []

/-- Agreement accumulator induction over a list of writes. -/
theorem storOf_foldl_writes (writes : List ((Adr × B256) × B256)) :
    ∀ (st : State) (s : StorShadow),
      (∀ a k, storOf st a k = lookupS s a k) →
      ∀ a k, storOf (writes.foldl (fun st ((a, k), v) => stateSetStorValB st a k v) st) a k =
             lookupS (writes.foldl (fun s w => w :: s) s) a k := by
  induction writes with
  | nil =>
    intro st s h a k
    exact h a k
  | cons w ws ih =>
    intro st s h a k
    rcases w with ⟨⟨ct, key⟩, val⟩
    simp only [List.foldl_cons]
    apply ih
    exact storOf_stateSetStorValB h

/-- Agreement for a state built by folding a list of writes from an empty-storage base,
with the shadow built from the same list. -/
theorem storOf_stateFoldStor (writes : List ((Adr × B256) × B256)) {st : State}
    (h : ∀ a k, storOf st a k = 0) :
    ∀ a k, storOf (stateFoldStor st writes) a k = lookupS (storShadowOf writes) a k :=
  storOf_foldl_writes writes st [] (storAgree_nil h)


theorem sloadStep_cont {fs : List SFunc} {sevm : Sevm} {c c' : Cfg} {g : SFunc}
    (h : sloadStep sevm c g = some c') (hf : c.f = .next (.reg .sload) g) :
    StepOk fs sevm c c' := by
  rcases c with ⟨devm, f, K, keys, adrs, stor, acs⟩
  simp only at hf; subst hf
  simp only [sloadStep] at h
  split at h
  · rename_i k s hs
    split at h
    · rename_i hcond
      obtain ⟨hleg, hroom⟩ := hcond
      have hleg' : sevm.benvStat.rules.stateGas = none := Option.isNone_iff_eq_none.mp hleg
      split at h
      · rename_i hw
        split at h
        · rename_i hgas
          cases h
          exact StepOk.of (fun hc => hc) rfl fun hc o r =>
            .next (Ninst.runCompiled_sload_warm hleg' hs ((hc.1 _).mpr hw) (hc.2.2.1 _ _)
              (G := devm.gasLeft - gasWarmAccess) (by show devm.gasLeft = _; omega) hroom) r
        · cases h
      · rename_i hw
        split at h
        · rename_i hgas
          cases h
          exact StepOk.of (fun hc => ⟨agree_insert hc.1, hc.2.1, hc.2.2⟩) rfl fun hc o r =>
            .next (Ninst.runCompiled_sload_cold hleg' hs (fun hm => hw ((hc.1 _).mp hm)) (hc.2.2.1 _ _)
              (G := devm.gasLeft - gasColdSload) (by show devm.gasLeft = _; omega) hroom) r
        · cases h
    · cases h
  · cases h

theorem sstoreStep_cont {fs : List SFunc} {sevm : Sevm} {c c' : Cfg} {g : SFunc}
    (h : sstoreStep sevm c g = some c') (hf : c.f = .next (.reg .sstore) g) :
    StepOk fs sevm c c' := by
  rcases c with ⟨devm, f, K, keys, adrs, stor, acs⟩
  simp only at hf; subst hf
  simp only [sstoreStep] at h
  split at h
  · rename_i k v s hs
    split at h
    · rename_i hcond
      obtain ⟨hleg, hsentry, hstatic⟩ := hcond
      have hleg' : sevm.benvStat.rules.stateGas = none := Option.isNone_iff_eq_none.mp hleg
      split at h
      · rename_i hw
        split at h
        · rename_i hgas
          cases h
          refine StepOk.of (fun hc => ⟨hc.1, hc.2.1, storOf_sstore hc.2.2.1,
            acctAgree_stateSetStorValB hc.2.2.2 _ _ _⟩) rfl fun hc o r => .next ?_ r
          have hcur : devm.getStorVal sevm.currentTarget k = lookupS stor sevm.currentTarget k :=
            hc.2.2.1 _ _
          have h := Ninst.runCompiled_sstore_warm hleg' hs ((hc.1 _).mpr hw) hsentry hstatic
            (congrArg (fun x => sstoreValueCost (getOrigStorVal sevm sevm.currentTarget k) x v) hcur)
            (congrArg (fun x => sstoreNewRefundCounter sevm.benvStat.rules.gas v
              (getOrigStorVal sevm sevm.currentTarget k) x devm.refundCounter) hcur)
            (G := devm.gasLeft - _) (by exact (Nat.sub_add_cancel hgas).symm)
          rwa [devm_setStorVal_eq_B] at h
        · cases h
      · rename_i hw
        split at h
        · rename_i hgas
          cases h
          refine StepOk.of (fun hc => ⟨agree_insert hc.1, hc.2.1, storOf_sstore hc.2.2.1,
            acctAgree_stateSetStorValB hc.2.2.2 _ _ _⟩) rfl
            fun hc o r => .next ?_ r
          have hcur : devm.getStorVal sevm.currentTarget k = lookupS stor sevm.currentTarget k :=
            hc.2.2.1 _ _
          have h := Ninst.runCompiled_sstore_cold hleg' hs (fun hm => hw ((hc.1 _).mp hm)) hsentry
            hstatic
            (congrArg (fun x => gasColdSload + sstoreValueCost (getOrigStorVal sevm sevm.currentTarget k) x v)
              hcur)
            (congrArg (fun x => sstoreNewRefundCounter sevm.benvStat.rules.gas v
              (getOrigStorVal sevm sevm.currentTarget k) x devm.refundCounter) hcur)
            (G := devm.gasLeft - _) (by exact (Nat.sub_add_cancel hgas).symm)
          rwa [devm_setStorVal_eq_B] at h
        · cases h
    · cases h
  · cases h

theorem generic_cont {fs : List SFunc} {sevm : Sevm} {c : Cfg} {n : Ninst} {g : SFunc}
    {q : Nat} {d : Devm} (hn : ninstAccKeeps n = true)
    (hstep : Ninst.step ⟨0, sevm, c.devm⟩ n = .cont q d) (hf : c.f = .next n g) :
    StepOk fs sevm c ⟨d, g, c.K, c.keys, c.adrs, c.stor, c.acs⟩ := by
  have hk := ninstAccKeeps_step hn hstep
  refine StepOk.of (fun hc => ⟨fun x => ?_, fun a => ?_, fun a k => ?_, fun a => ?_⟩) rfl
    fun _ o r => ?_
  · show x ∈ d.accessedStorageKeys ↔ x ∈ c.keys
    rw [hk.2.1]; exact hc.1 x
  · show a ∈ d.accessedAddresses ↔ a ∈ c.adrs
    rw [hk.1]; exact hc.2.1 a
  · show storOf d.state a k = lookupS c.stor a k
    rw [hk.2.2]; exact hc.2.2.1 a k
  · show acctView (d.state.get a) = lookupA c.acs a
    rw [hk.2.2]; exact hc.2.2.2 a
  · rw [hf]
    exact .next (Ninst.runCompiled_of_run (pcFree_of_ninstAccKeeps hn)
      ⟨.none, trivial, 0, by simp [Ninst.StepRun, hstep, Step.Run]⟩) r

theorem mstoreStep_cont {fs : List SFunc} {sevm : Sevm} {c c' : Cfg} {g : SFunc}
    (h : mstoreStep c g = some c') (hf : c.f = .next (.reg .mstore) g) :
    StepOk fs sevm c c' := by
  rcases c with ⟨devm, f, K, keys, adrs, stor, acs⟩
  simp only at hf; subst hf
  simp only [mstoreStep] at h
  split at h
  · rename_i i v s hs
    split at h
    · rename_i hgas
      cases h
      exact StepOk.same rfl rfl rfl rfl (AccKeep.setMach _ _) rfl fun o r =>
        .next (Ninst.runCompiled_mstore hs (by exact (Nat.sub_add_cancel hgas).symm)
          (mem_write_eq_B _ _ _)) r
    · cases h
  · cases h

theorem mloadStep_cont {fs : List SFunc} {sevm : Sevm} {c c' : Cfg} {g : SFunc}
    (h : mloadStep c g = some c') (hf : c.f = .next (.reg .mload) g) :
    StepOk fs sevm c c' := by
  rcases c with ⟨devm, f, K, keys, adrs, stor, acs⟩
  simp only at hf; subst hf
  simp only [mloadStep] at h
  split at h
  · rename_i i s hs
    split at h
    · rename_i hc
      obtain ⟨hgas, hroom⟩ := hc
      cases h
      exact StepOk.same rfl rfl rfl rfl (AccKeep.setMach _ _) rfl fun o r =>
        .next (Ninst.runCompiled_mload_of hs rfl
          (by simp only [Mem.read, array_sliceD_eq_list]) rfl
          (by exact (Nat.sub_add_cancel hgas).symm) hroom) r
    · cases h
  · cases h

theorem calldatacopyStep_cont {fs : List SFunc} {sevm : Sevm} {c c' : Cfg} {g : SFunc}
    (h : calldatacopyStep sevm c g = some c') (hf : c.f = .next (.reg .calldatacopy) g) :
    StepOk fs sevm c c' := by
  rcases c with ⟨devm, f, K, keys, adrs, stor, acs⟩
  simp only at hf; subst hf
  simp only [calldatacopyStep] at h
  split at h
  · rename_i di si sz s hs
    split at h
    · rename_i hgas
      cases h
      exact StepOk.same rfl rfl rfl rfl (AccKeep.setMach _ _) rfl fun o r =>
        .next (Ninst.runCompiled_calldatacopy_of hs rfl (mem_write_eq_B _ _ _)
          (by exact (Nat.sub_add_cancel hgas).symm)) r
    · cases h
  · cases h

theorem keccakStep_cont {fs : List SFunc} {sevm : Sevm} {c c' : Cfg} {g : SFunc}
    (h : keccakStep c g = some c') (hf : c.f = .next (.reg .keccak256) g) :
    StepOk fs sevm c c' := by
  rcases c with ⟨devm, f, K, keys, adrs, stor, acs⟩
  simp only at hf; subst hf
  simp only [keccakStep] at h
  split at h
  · rename_i i sz s hs
    split at h
    · rename_i hc
      obtain ⟨hgas, hroom⟩ := hc
      cases h
      exact StepOk.same rfl rfl rfl rfl (AccKeep.setMach _ _) rfl fun o r =>
        .next (Ninst.runCompiled_keccak256_of hs rfl
          (by simp only [Mem.read, array_sliceD_eq_list]) rfl
          (by exact (Nat.sub_add_cancel hgas).symm) hroom) r
    · cases h
  · cases h

theorem logStep_cont {fs : List SFunc} {sevm : Sevm} {c c' : Cfg} {g : SFunc} {n : Fin 5}
    (h : logStep sevm n c g = some c') (hf : c.f = .next (.reg (.log n)) g) :
    StepOk fs sevm c c' := by
  rcases c with ⟨devm, f, K, keys, adrs, stor, acs⟩
  simp only at hf; subst hf
  simp only [logStep] at h
  split at h
  · rename_i i sz rest hs
    split at h
    · rename_i hc
      obtain ⟨hlen, hstatic, hgas⟩ := hc
      cases h
      have hs' : devm.stack = i :: sz :: (rest.take n.val ++ rest.drop n.val) := by
        rw [List.take_append_drop]; exact hs
      exact StepOk.same rfl rfl rfl rfl ⟨rfl, rfl, rfl⟩ rfl fun o r =>
        .next (Ninst.runCompiled_log_of hs' (by simp; omega) hstatic rfl
          (by simp only [Mem.read, array_sliceD_eq_list]) rfl
          (by exact (Nat.sub_add_cancel hgas).symm)) r
    · cases h
  · cases h

theorem callStep_cont {fs : List SFunc} {sevm : Sevm} {c c' : Cfg} {g : SFunc}
    (h : callStep sevm c g = some c') (hf : c.f = .next (.exec .call) g) :
    StepOk fs sevm c c' := by
  simp only [callStep] at h
  split at h
  · rename_i cp hp
    split at h
    · rename_i child he
      split at h
      · rename_i hce
        split at h
        · rename_i d hr
          cases h
          refine StepOk.of ?_ rfl ?_
          · intro hc
            obtain ⟨_, hpa, hpk, hcr, hia, hik, hsg, hst⟩ := callPrep_spec hp hc.2.1 hc.2.2.2
            have hC : AcctAgree cp.f.inner.benv.state c.acs := by rw [hst]; exact hc.2.2.2
            have heB : frameEnterB cp.f = .done (.ok child) := by rw [frameEnterB_eq_S hC]; exact he
            obtain ⟨hda, hdk⟩ := resumeCallB_acc hr
            obtain ⟨hca, hck, hcs⟩ := frameEnterB_done_acc hcr hsg heB
            obtain ⟨benv, hb, hcst⟩ := frameEnterB_done_ok_state hcr hsg heB hce
            rw [benvAfterTransfer_eq_S hC] at hb
            refine ⟨fun x => ?_, fun a => ?_, fun a k => ?_, fun a => ?_⟩
            · show x ∈ d.accessedStorageKeys ↔ x ∈ c.keys
              rw [hdk x, hck, hik, hpk, hc.1 x]
              exact ⟨fun h => h.elim id (·.2), .inl⟩
            · show a ∈ d.accessedAddresses ↔ a ∈ cp.adrs
              rw [hda a, hca, hia, hpa a]
              exact ⟨fun h => h.elim id (·.2), .inl⟩
            · show storOf d.state a k = lookupS c.stor a k
              rw [resumeCallB_state hr, hcs, hst]; exact hc.2.2.1 a k
            · show acctView (d.state.get a) = lookupA (acsTransfer cp.f.inner c.acs) a
              rw [resumeCallB_state hr, hcst]; exact acctAgree_transfer hC hb a
          · intro hc o r'
            obtain ⟨hstep, -, -, -, -, -, -, hst⟩ := callPrep_spec hp hc.2.1 hc.2.2.2
            have hC : AcctAgree cp.f.inner.benv.state c.acs := by rw [hst]; exact hc.2.2.2
            rw [hf]
            exact .next (Ninst.runCompiled_exec_doneFrame hstep
              (by rw [frame_enter_eq_B, frameEnterB_eq_S hC]; exact he) (resumeCallB_sound hr)) r'
        · cases h
      · cases h
    all_goals cases h
  · cases h

/-- The shadows of a settled child: its accessed sets, storage and accounts. -/
def ChildAgree (child : Devm) (ckeys : List (Adr × B256)) (cadrs : List Adr) (cstor : StorShadow)
    (cacs : AcctShadow) : Prop :=
  (∀ a, a ∈ child.accessedAddresses ↔ a ∈ cadrs) ∧
    (∀ k, k ∈ child.accessedStorageKeys ↔ k ∈ ckeys) ∧
    (∀ a k, storOf child.state a k = lookupS cstor a k) ∧ AcctAgree child.state cacs

/-- **A `CALL` into code.**  The child's execution `raw` is supplied with its
`Exec` derivation from the machine the frame enters with; a successful child
contributes its accessed sets, and its world, described by the shadows
`ckeys`/`cadrs`/`cstor`/`cacs`. -/
theorem callRun_cont {fs : List SFunc} {sevm : Sevm} {c : Cfg} {g : SFunc} {cp : CallPrep}
    {cevm : Evm} {raw : Execution} {child d : Devm}
    {ckeys : List (Adr × B256)} {cadrs : List Adr} {cstor : StorShadow} {cacs : AcctShadow}
    (hf : c.f = .next (.exec .call) g) (hp : callPrep sevm c = some cp)
    (he : frameEnterS cp.f c.acs = .run cevm) (hx : Nonempty (Exec cevm.pc cevm.sta cevm.dyna raw))
    (hs : cp.f.settle raw = .ok child) (hce : child.error.isSome = false)
    (hr : resumeCallB cp.p cp.oi cp.os (.ok child) = some d)
    (hca : ChildAgree child ckeys cadrs cstor cacs) :
    StepOk fs sevm c ⟨d, g, c.K, c.keys ++ ckeys, cp.adrs ++ cadrs, cstor, cacs⟩ := by
  refine StepOk.of ?_ rfl ?_
  · intro hc
    obtain ⟨_, hpa, hpk, -⟩ := callPrep_spec hp hc.2.1 hc.2.2.2
    obtain ⟨hda, hdk⟩ := resumeCallB_acc hr
    refine ⟨fun x => ?_, fun a => ?_, fun a k => ?_, fun a => ?_⟩
    · show x ∈ d.accessedStorageKeys ↔ x ∈ c.keys ++ ckeys
      rw [hdk x, hce, hpk, hc.1 x, hca.2.1 x, List.mem_append]
      simp
    · show a ∈ d.accessedAddresses ↔ a ∈ cp.adrs ++ cadrs
      rw [hda a, hce, hpa a, hca.1 a, List.mem_append]
      simp
    · show storOf d.state a k = lookupS cstor a k
      rw [resumeCallB_state hr]; exact hca.2.2.1 a k
    · show acctView (d.state.get a) = lookupA cacs a
      rw [resumeCallB_state hr]; exact hca.2.2.2 a
  · intro hc o r'
    obtain ⟨hstep, -, -, -, -, -, -, hst⟩ := callPrep_spec hp hc.2.1 hc.2.2.2
    have hC : AcctAgree cp.f.inner.benv.state c.acs := by rw [hst]; exact hc.2.2.2
    rw [hf]
    refine .next ⟨.some ⟨cevm, raw⟩, hx, fun pc => ?_⟩ r'
    apply XStep.run_toStep.mpr
    show XStep.Run (Xinst.step sevm c.devm .call) _ _
    rw [hstep]
    refine ⟨_, RunFrame.of_run (by rw [frame_enter_eq_B, frameEnterB_eq_S hC]; exact he), ?_⟩
    rw [hs]; exact (resumeCallB_sound hr).symm

theorem wstep_cont {fs : List SFunc} {sevm : Sevm} {c c' : Cfg}
    (h : wstep fs sevm c = .cont c') : StepOk fs sevm c c' := by
  rcases c with ⟨devm, f, K, keys, adrs, stor, acs⟩
  cases f with
  | dest g =>
    simp only [wstep] at h
    split at h
    · cases h
      refine StepOk.same rfl rfl rfl rfl (AccKeep.setMach _ _) rfl fun o r => .dest ?_ r
      exact Devm.burnBy_setMach (by assumption)
    · cases h
  | jump k =>
    simp only [wstep] at h
    split at h
    · rename_i d s g hs hg
      split at h
      · cases h
        exact StepOk.same rfl rfl rfl rfl (AccKeep.setMach _ _) rfl fun o r =>
          .jump d hg (popBurnBy1 hs (by assumption)) r
      · cases h
    · cases h
  | branch f g =>
    simp only [wstep] at h
    split at h
    · rename_i d w s hs
      split at h
      · cases h
        refine StepOk.same rfl rfl rfl rfl (AccKeep.setMach _ _) rfl fun o r => ?_
        by_cases hw : w = 0
        · subst hw; simp only [ite_true] at r
          exact .zero d (popBurnBy2 hs (by assumption)) r
        · simp only [hw, ite_false] at r
          exact .succ d w hw (popBurnBy2 hs (by assumption)) r
      · cases h
    · cases h
  | branchTo f k =>
    simp only [wstep] at h
    split at h
    · rename_i d w s hs
      split at h
      · rename_i hgas
        split at h
        · rename_i hw
          cases h; subst hw
          exact StepOk.same rfl rfl rfl rfl (AccKeep.setMach _ _) rfl fun o r =>
            .toZero d (popBurnBy2 hs hgas) r
        · rename_i hw
          split at h
          · rename_i g hg
            cases h
            exact StepOk.same rfl rfl rfl rfl (AccKeep.setMach _ _) rfl fun o r =>
              .toSucc d w hw hg (popBurnBy2 hs hgas) r
          · cases h
      · cases h
    · cases h
  | callNext k f =>
    simp only [wstep] at h
    split at h
    · rename_i d s g hs hg
      split at h
      · rename_i hgas
        cases h
        refine ⟨fun hc => hc, fun o _ r => ?_⟩
        have hpop := popBurnBy1 (cost := gMid) hs hgas
        rcases r with ⟨d1, r1, rest⟩ | ⟨d1, rfl, r1⟩
        · cases K with
          | nil => exact .callRet d hg hpop r1 rest
          | cons h' K =>
            rcases rest with ⟨d2, r2, rest⟩ | ⟨d2, rfl, r2⟩
            · exact .inl ⟨d2, .callRet d hg hpop r1 r2, rest⟩
            · exact .inr ⟨d2, rfl, .callRet d hg hpop r1 r2⟩
        · exact RunK.halted (.callHalt d hg hpop r1)
      · cases h
    · cases h
  | ret =>
    simp only [wstep] at h
    split at h
    · rename_i d s hs
      split at h
      · rename_i hgas
        split at h
        · cases h
        · rename_i g K' _
          cases h
          refine ⟨fun hc => hc, fun o _ r => ?_⟩
          exact .inl ⟨_, .ret d (popBurnBy1 hs hgas), r⟩
      · cases h
    · cases h
  | pcAt p g =>
    simp only [wstep] at h
    split at h
    · rename_i q d hstep
      cases h
      refine StepOk.same rfl rfl rfl rfl (pc_step_accKeep hstep) rfl fun o r => .pcAt ?_ r
      simp [Ninst.StepRun, hstep, Step.Run]
    · cases h
  | last l =>
    cases l <;> simp only [wstep] at h <;> (try split at h) <;> cases h
  | undefined => simp [wstep] at h
  | next n g =>
    simp only [wstep] at h
    split at h
    · split at h
      · cases h; exact sloadStep_cont (by assumption) rfl
      · cases h
    · split at h
      · cases h; exact sstoreStep_cont (by assumption) rfl
      · cases h
    · split at h
      · cases h; exact mstoreStep_cont (by assumption) rfl
      · cases h
    · split at h
      · cases h; exact mloadStep_cont (by assumption) rfl
      · cases h
    · split at h
      · cases h; exact calldatacopyStep_cont (by assumption) rfl
      · cases h
    · split at h
      · cases h; exact keccakStep_cont (by assumption) rfl
      · cases h
    · split at h
      · cases h; exact logStep_cont (by assumption) rfl
      · cases h
    · split at h
      · cases h; exact callStep_cont (by assumption) rfl
      · cases h
    · split at h
      · rename_i hn
        split at h
        · rename_i q d hstep
          cases h
          exact generic_cont hn hstep rfl
        · cases h
      · cases h

/-- `RETURN` keeps the world state. -/
theorem linst_return_state {sevm : Sevm} {devm d : Devm}
    (h : Linst.run sevm devm .return_ = .ok d) : d.state = devm.state := by
  simp only [Linst.run] at h
  obtain ⟨⟨i, d1⟩, h1, e1⟩ := Except.bind_eq_ok h
  obtain ⟨⟨n, d2⟩, h2, e2⟩ := Except.bind_eq_ok e1
  obtain ⟨d3, h3, h4⟩ := Except.bind_eq_ok e2
  cases h4
  exact ((accKeep_popToNat h1).trans ((accKeep_popToNat h2).trans (accKeep_chargeGas h3))).2.2

/-- A step to an outcome: it is a run, it names its own configuration, and a
halted outcome keeps that configuration's world state. -/
theorem wstep_done {fs : List SFunc} {sevm : Sevm} {c c' : Cfg} {o : Outcome}
    (h : wstep fs sevm c = .done o c') :
    RunK fs sevm c.devm c.f c.K o ∧ c' = c ∧ ∀ d, o = .halted d → d.state = c.devm.state := by
  rcases c with ⟨devm, f, K, keys, adrs, stor, acs⟩
  cases f with
  | ret =>
    simp only [wstep] at h
    split at h
    · rename_i d s hs
      split at h
      · rename_i hgas
        split at h
        · cases h
          exact ⟨SFunc.RunExact.ret d (popBurnBy1 hs hgas), rfl, fun _ h => by cases h⟩
        · cases h
      · cases h
    · cases h
  | last l =>
    cases l <;> simp only [wstep] at h
    · split at h
      · rename_i d hd
        cases h
        refine ⟨RunK.halted (.last hd), rfl, fun d' e => ?_⟩
        cases e; simp only [Linst.run, Except.ok.injEq] at hd; rw [hd]
      · cases h
    · split at h
      · rename_i d hd
        cases h
        exact ⟨RunK.halted (.last hd), rfl, fun d' e => by cases e; exact linst_return_state hd⟩
      · cases h
    · split at h
      · rename_i d hd
        simp only [Linst.run] at hd
        obtain ⟨_, _, e1⟩ := Except.bind_eq_ok hd
        obtain ⟨_, _, e2⟩ := Except.bind_eq_ok e1
        obtain ⟨_, _, e3⟩ := Except.bind_eq_ok e2
        cases e3
      · cases h
    · cases h
  | next n g =>
    simp only [wstep] at h
    split at h <;> (try split at h) <;> (try split at h) <;> cases h
  | dest g => simp only [wstep] at h; split at h <;> cases h
  | jump k => simp only [wstep] at h; split at h <;> (try split at h) <;> cases h
  | branch f g => simp only [wstep] at h; split at h <;> (try split at h) <;> cases h
  | branchTo f k =>
    simp only [wstep] at h; split at h <;> (try split at h) <;> (try split at h) <;>
      (try split at h) <;> cases h
  | callNext k f => simp only [wstep] at h; split at h <;> (try split at h) <;> cases h
  | pcAt p g => simp only [wstep] at h; split at h <;> cases h
  | undefined => simp [wstep] at h

/-- A chunk of `n` steps to a configuration. -/
theorem wrun_cont {fs : List SFunc} {sevm : Sevm} :
    ∀ {n : Nat} {c c' : Cfg}, wrun fs sevm n c = .cont c' → StepOk fs sevm c c'
  | 0, c, c', h => by
    simp only [wrun, Res.cont.injEq] at h; subst h
    exact ⟨id, fun _ _ r => r⟩
  | n + 1, c, c', h => by
    simp only [wrun] at h
    split at h
    · rename_i c1 h1
      have s1 := wstep_cont h1
      have s2 := wrun_cont h
      exact ⟨fun hc => s2.1 (s1.1 hc), fun o hc r => s1.2 o hc (s2.2 o (s1.1 hc) r)⟩
    · rename_i r hr
      exact absurd h (hr _)

/-- A chunk of at most `n` steps to an outcome: a run, agreement at the
configuration that produced it, and (halted) that configuration's world. -/
theorem wrun_done {fs : List SFunc} {sevm : Sevm} :
    ∀ {n : Nat} {c c' : Cfg} {o : Outcome}, wrun fs sevm n c = .done o c' → Agree c →
      RunK fs sevm c.devm c.f c.K o ∧ Agree c' ∧ ∀ d, o = .halted d → d.state = c'.devm.state
  | 0, c, c', o, h, _ => by simp [wrun] at h
  | n + 1, c, c', o, h, hc => by
    simp only [wrun] at h
    split at h
    · rename_i c1 h1
      have s1 := wstep_cont h1
      obtain ⟨r, ha, hs⟩ := wrun_done h (s1.1 hc)
      exact ⟨s1.2 o hc r, ha, hs⟩
    · obtain ⟨r, rfl, hs⟩ := wstep_done h
      exact ⟨r, hc, hs⟩

/-- **The witness engine.**  A frame whose interpreter run from entry `0`
halts is a gas-exact run of the certificate's program. -/
theorem wrun_exact {fs : List SFunc} {sevm : Sevm} {pre post : Devm} {f0 : SFunc}
    {keys : List (Adr × B256)} {adrs : List Adr} {stor : StorShadow} {acs : AcctShadow} {n : Nat}
    {cl : Cfg}
    (h0 : fs[0]? = some f0) (hagree : Agree ⟨pre, f0, [], keys, adrs, stor, acs⟩)
    (h : wrun fs sevm n ⟨pre, f0, [], keys, adrs, stor, acs⟩ = .done (.halted post) cl) :
    SProg.RunExact fs sevm pre post :=
  ⟨f0, h0, (wrun_done h hagree).1⟩

/-! ## Seeding the account shadow -/

/-- A world built from storage-free accounts (each placed through `stateSetB`). -/
def stateFoldAcct (st : State) (accts : List (Adr × Acct)) : State :=
  accts.foldl (fun s (a, ac) => stateSetB s a (acctView ac)) st

/-- The account shadow of `stateFoldAcct`'s accounts (newest first). -/
def acctShadowOf (accts : List (Adr × Acct)) : AcctShadow :=
  accts.foldl (fun s (a, ac) => (a, acctView ac) :: s) []

theorem acctAgree_foldAcct (accts : List (Adr × Acct)) :
    ∀ (st : State) (acs : AcctShadow), AcctAgree st acs →
      AcctAgree (accts.foldl (fun s (a, ac) => stateSetB s a (acctView ac)) st)
        (accts.foldl (fun s (a, ac) => (a, acctView ac) :: s) acs) := by
  induction accts with
  | nil => intro st acs h; exact h
  | cons x xs ih =>
    intro st acs h
    rcases x with ⟨a, ac⟩
    exact ih _ _ (acctAgree_stateSetB h a (acctView ac))

theorem acctAgree_stateFoldAcct (accts : List (Adr × Acct)) :
    AcctAgree (stateFoldAcct default accts) (acctShadowOf accts) :=
  acctAgree_foldAcct accts default [] fun _ => rfl

theorem storOf_foldAcct (accts : List (Adr × Acct)) :
    ∀ (st : State), (∀ a k, storOf st a k = 0) →
      ∀ a k, storOf (accts.foldl (fun s (a, ac) => stateSetB s a (acctView ac)) st) a k = 0 := by
  induction accts with
  | nil => intro st h; exact h
  | cons x xs ih =>
    intro st h
    rcases x with ⟨b, ac⟩
    exact ih _ fun a k => storOf_stateSetB_empty st b a (acctView ac) k (h a k) rfl

theorem storOf_stateFoldAcct (accts : List (Adr × Acct)) (a : Adr) (k : B256) :
    storOf (stateFoldAcct default accts) a k = 0 :=
  storOf_foldAcct accts default storOf_empty a k

theorem acctAgree_foldStor (writes : List ((Adr × B256) × B256)) :
    ∀ (st : State) (acs : AcctShadow), AcctAgree st acs →
      AcctAgree (writes.foldl (fun st ((a, k), v) => stateSetStorValB st a k v) st) acs := by
  induction writes with
  | nil => intro st acs h; exact h
  | cons w ws ih =>
    intro st acs h
    rcases w with ⟨⟨a, k⟩, v⟩
    exact ih _ _ (acctAgree_stateSetStorValB h a k v)

theorem acctAgree_stateFoldStor (writes : List ((Adr × B256) × B256)) {st : State}
    {acs : AcctShadow} (h : AcctAgree st acs) : AcctAgree (stateFoldStor st writes) acs :=
  acctAgree_foldStor writes st acs h

/-! ## Code children supplied as data

A code child's execution is not run by the interpreter: its settled machine is
supplied, and the parent resumes from it (`callResume`).  The supplied machine
is tied to the real child by `ChildOk` (it is the settlement of an `Exec` from the
machine the frame enters with) and its world by `ChildAgree`: exactly the
premises of `callRun_cont`. -/

/-- The configuration after a code-child `CALL`, from the settled child and its shadows. -/
def callResume (sevm : Sevm) (c : Cfg) (child : Devm) (ckeys : List (Adr × B256))
    (cadrs : List Adr) (cstor : StorShadow) (cacs : AcctShadow) : Option Cfg :=
  match c.f with
  | .next (.exec .call) g =>
    match callPrep sevm c with
    | some cp =>
      match frameEnterS cp.f c.acs with
      | .run _ =>
        if child.error.isSome = false then
          match resumeCallB cp.p cp.oi cp.os (.ok child) with
          | some d => some ⟨d, g, c.K, c.keys ++ ckeys, cp.adrs ++ cadrs, cstor, cacs⟩
          | none => none
        else none
      | .done _ => none
    | none => none
  | _ => none

/-- A settled machine is the child of the code `CALL` at `c`: the settlement of an
`Exec` from the machine that `CALL`'s frame enters with. -/
def ChildOk (sevm : Sevm) (c : Cfg) (child : Devm) : Prop :=
  ∀ cp cevm, callPrep sevm c = some cp → frameEnterS cp.f c.acs = .run cevm →
    ∃ raw, Nonempty (Exec cevm.pc cevm.sta cevm.dyna raw) ∧ cp.f.settle raw = .ok child

theorem callResume_cont {fs : List SFunc} {sevm : Sevm} {c c' : Cfg} {child : Devm}
    {ckeys : List (Adr × B256)} {cadrs : List Adr} {cstor : StorShadow} {cacs : AcctShadow}
    (h : callResume sevm c child ckeys cadrs cstor cacs = some c') (hk : ChildOk sevm c child)
    (ha : ChildAgree child ckeys cadrs cstor cacs) : StepOk fs sevm c c' := by
  unfold callResume at h
  split at h
  · rename_i g hf
    split at h
    · rename_i cp hp
      split at h
      · rename_i cevm he
        split at h
        · rename_i hce
          split at h
          · rename_i d hr
            cases h
            obtain ⟨raw, hx, hs⟩ := hk cp cevm hp he
            exact callRun_cont hf hp he hx hs hce hr ha
          · cases h
        · cases h
      · cases h
    · cases h
  · cases h

/-- `d` with its gas, output and error replaced: the parts of a settled child the
parent's continuation inspects, as literals. -/
def childObs (g : Nat) (out : Bytes) (d : Devm) : Devm :=
  ⟨{ d.mach with gasLeft := g }, { d.meta with output := out, error := none }, d.world⟩

theorem childObs_eq {d : Devm} {g : Nat} {out : Bytes} (hg : d.gasLeft = g) (ho : d.output = out)
    (he : d.error = none) : childObs g out d = d := by
  rcases d with ⟨⟨_, _, _, _⟩, ⟨_, _, _, _, _, _, _, _, _, _, _⟩, _⟩
  simp only [Devm.gasLeft, Devm.output, Devm.error] at hg ho he
  subst hg ho he
  rfl

open _root_.Lean _root_.Lean.Meta _root_.Lean.Elab _root_.Lean.Elab.Tactic in
/-- Close `∀ xs, a xs = b xs` with `fun xs => Eq.refl (a xs)`, checked by the kernel
alone (as `kernel_rfl`, for statements over free parts the evaluation never
inspects). -/
elab "kernel_forall_rfl" : tactic => closeMainGoalUsing `kernel_forall_rfl fun type _ => do
  let type ← instantiateMVars type
  let pf ← forallTelescope type fun xs body => do
    let some (α, lhs, _) := body.eq? | throwError "kernel_forall_rfl: not an equality"
    let u ← getLevel α
    mkLambdaFVars xs (mkApp2 (mkConst ``Eq.refl [u]) α lhs)
  let levelsInType := (collectLevelParams {} type).params
  let lemmaLevels := (← Term.getLevelNames).reverse.filter levelsInType.contains
  let name ← withOptions (Elab.async.set · false) do
    mkAuxLemma lemmaLevels type pf
  return mkConst name (lemmaLevels.map .param)

end Blanc.Lift.Witness
