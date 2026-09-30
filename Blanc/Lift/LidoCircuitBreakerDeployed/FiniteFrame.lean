import Blanc.Lift.LidoCircuitBreakerDeployed.FiniteUpdate
import Blanc.Lift.LidoCircuitBreakerDeployed.L2Frame

/-!
# Finite registry agreement for the deployed registerPauser frame

The observed footprint includes every listed target and pauser, plus explicit
caller-selected probes. Omitted addresses have no mapping or count guarantee.
-/

namespace Blanc.Lift.LidoCircuitBreakerDeployed

open Jaune Blanc Blanc.Lift Blanc.LidoCircuitBreaker

/-- Updating an entry retains finite coverage when both new components are
explicit probes. No assumption about unlisted addresses is used. -/
theorem checkLiveCovered_setEntryAt {entries : List LidoCircuitBreaker.Entry}
    {probes : List B256} {target newPauser : B256} {index : Nat}
    (hcover : checkLiveCovered entries probes = true)
    (ht : target ∈ probes) (hn : newPauser ∈ probes) :
    checkLiveCovered (setEntryAt index (target, newPauser) entries) probes = true := by
  rw [checkLiveCovered_eq_true] at hcover ⊢
  induction entries generalizing index with
  | nil => simp [setEntryAt]
  | cons e rest ih =>
      cases index with
      | zero =>
          intro x hx
          simp only [setEntryAt, List.mem_cons] at hx
          rcases hx with rfl | hx
          · exact ⟨ht, hn⟩
          · exact hcover x (by simp [hx])
      | succ index =>
          intro x hx
          simp only [setEntryAt, List.mem_cons] at hx
          rcases hx with rfl | hx
          · exact hcover x (by simp)
          · exact ih (fun x hx => hcover x (by simp [hx])) x hx

/-- Lift the finite entry-32 observation through both heartbeat calls. The only
extra separation check compares their two expiry slots against the same finite
query footprint. -/
theorem registerPauser_body_finite {sevm : Sevm} {b : Devm} {M : Mem} {G : Nat}
    {target newPauser oldPauser ra : B256} {base : List B256} {post : Devm}
    {entries : List LidoCircuitBreaker.Entry} {probes : List B256} {index : Nat}
    (hfork : CoveredFork sevm.benvStat.fork) (hmem : MemOK M)
    (hw : RegistryOn (solRegistryStorage (Devm.getStor b sevm.currentTarget)) entries probes)
    (ht : target ∈ probes) (ho : oldPauser ∈ probes) (hn : newPauser ∈ probes)
    (hnew : newPauser ≠ 0) (hfind : findEntry entries target = some (index, oldPauser))
    (hfaithful : SlotFootprint.checkFaithfulOn solKey (registryQueries probes entries.length)
      ((nonzeroWrites entries target newPauser oldPauser).map Prod.fst) = true)
    (hapart : SlotFootprint.checkApartOn solKey (registryQueries probes entries.length)
      [mapSlot oldPauser 2, mapSlot newPauser 2] = true)
    (run : SFunc.Run prog sevm (St b (newPauser :: target :: ra :: base) M G)
      t_031c_c21 (.returned post)) :
    RegistryOn (solRegistryStorage (Devm.getStor post sevm.currentTarget))
      (setEntryAt index (target, newPauser) entries) probes := by
  have htarget := hw.targetsValid (target, oldPauser) (mem_of_findEntry hfind)
  have hp0 : addressSlotReadWord (b.getStorVal sevm.currentTarget (mapSlot target 3)) =
      oldPauser := by
    have h := hw.assignments target ht
    rw [solRegistryStorage_assignment _ _ htarget.2, findEntry_assignmentAt hfind] at h
    exact h
  have hsingle : ∀ w ∈ [mapSlot oldPauser 2, mapSlot newPauser 2],
      SlotFootprint.checkApartOn solKey
        (registryQueries probes (setEntryAt index (target, newPauser) entries).length) [w] = true := by
    intro w hw'
    rw [setEntryAt_length_of_findEntry hfind, SlotFootprint.checkApartOn_eq_true]
    intro x hx k hk
    simp only [List.mem_singleton] at hx
    subst x
    exact SlotFootprint.checkApartOn_eq_true.mp hapart w hw' k hk
  apply entry21_preserves
    (Φ := fun s => RegistryOn (solRegistryStorage s)
      (setEntryAt index (target, newPauser) entries) probes)
    (Apart := fun w => SlotFootprint.checkApartOn solKey
      (registryQueries probes (setEntryAt index (target, newPauser) entries).length) [w] = true)
    (fun ha hs => hs.set_foreign ha) hfork hmem htarget.2 (hw.probesValid newPauser hn)
    (b := b) (ra := ra) (xs := base) (D := post)
  · intro _ _
    rw [hp0]
    exact hsingle _ (by simp)
  · intro _ _
    exact hsingle _ (by simp)
  · intro _ b' M' G' post' hs hm rmid
    have hw' : RegistryOn (solRegistryStorage (Devm.getStor b' sevm.currentTarget))
        entries probes := by rw [hs]; exact hw
    exact setPauser_nonzero_finite hfork hm hw' ht ho hn hnew hfind hfaithful rmid
  · exact run

/-- **Finite agreement from an actual installed-runtime call.** Every listed
entry's target and pauser is explicitly covered, as are the updated target,
old pauser and new pauser. The state check reads only this footprint; both
separation checks compare finite lists. A successful pc-zero execution updates
the observed registry and retains live-entry coverage. This says nothing about
assignment/index/count cells for addresses omitted from `probes`. -/
theorem registerPauser_nonzero_finite {sevm : Sevm} {pre post : Devm}
    {entries : List LidoCircuitBreaker.Entry} {probes : List B256}
    {index : Nat} {oldPauser : B256}
    (hfork : CoveredFork sevm.benvStat.fork)
    (hinstalled : Devm.getCode pre sevm.currentTarget = code)
    (hcode : sevm.code = Devm.getCode pre sevm.currentTarget)
    (hfresh : Exec.FreshEntry sevm pre)
    (hsig : Sevm.dataWord sevm 0 >>> 224 = selector "registerPauser" [.address, .address])
    (hpre : checkRegistryOn (solRegistryStorage (Devm.getStor pre sevm.currentTarget))
      entries probes = true)
    (hcover : checkLiveCovered entries probes = true)
    (hclosure : Sevm.dataWord sevm 4 ∈ probes ∧ oldPauser ∈ probes ∧
      Sevm.dataWord sevm 36 ∈ probes)
    (hnew : Sevm.dataWord sevm 36 ≠ 0)
    (hfind : findEntry entries (Sevm.dataWord sevm 4) = some (index, oldPauser))
    (hfaithful : SlotFootprint.checkFaithfulOn solKey (registryQueries probes entries.length)
      ((nonzeroWrites entries (Sevm.dataWord sevm 4) (Sevm.dataWord sevm 36) oldPauser).map
        Prod.fst) = true)
    (hapart : SlotFootprint.checkApartOn solKey (registryQueries probes entries.length)
      [mapSlot oldPauser 2, mapSlot (Sevm.dataWord sevm 36) 2] = true)
    (execution : Exec 0 sevm pre (.ok post)) :
    checkRegistryOn (solRegistryStorage (Devm.getStor post sevm.currentTarget))
      (setEntryAt index (Sevm.dataWord sevm 4, Sevm.dataWord sevm 36) entries) probes = true ∧
    checkLiveCovered
      (setEntryAt index (Sevm.dataWord sevm 4, Sevm.dataWord sevm 36) entries) probes = true := by
  have hw := checkRegistryOn_eq_true.mp hpre
  obtain ⟨ht, ho, hn⟩ := hclosure
  refine ⟨checkRegistryOn_eq_true.mpr ?_, checkLiveCovered_setEntryAt hcover ht hn⟩
  obtain ⟨f, hf, run⟩ := lift_sound cert_check (hcode.trans hinstalled) hfork execution
  rw [entry0_lookup] at hf
  cases hf
  obtain ⟨G, run⟩ := registerPauser_dispatch hsig hfresh run
  apply registerPauser_wrapper_of_body
    (Φ := fun s => RegistryOn (solRegistryStorage s)
      (setEntryAt index (Sevm.dataWord sevm 4, Sevm.dataWord sevm 36) entries) probes)
    (by rfl) (d := St pre [selector "registerPauser" [.address, .address]]
      (Mem.empty.write 64 (128 : B256).toBytes) G) (o := .halted post)
  · intro _ _ G' D rbody
    apply registerPauser_body_finite hfork (memOK_empty.write_word 64 128)
      (by simpa only [getStor_St] using hw) ht ho hn hnew hfind hfaithful hapart
    exact rbody
  · exact run

end Blanc.Lift.LidoCircuitBreakerDeployed
