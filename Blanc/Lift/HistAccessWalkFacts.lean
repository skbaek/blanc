import Blanc.Lift.HistAccessWalk
import Blanc.Lift.HistStaticCall
import Blanc.Lift.Quiet
import Blanc.ForwardStorageAccess

/-!
# Missing successor projections for historical access walks

`Blanc/Lift/HistAccessWalk.lean` carries the projections its own steps need.
The Beacon historical safety chain additionally reads the code, address-set,
error, created-account and key-set projections of `afterSloadH`/`afterSstoreH`,
the `ite`-form storage projection of `afterSstoreH`, and the quiet frame
theorem over `Ninst.world_of_quietH`. All premises are dischargeable over
`HistFork` (`HistFork.stateGas_none`, `HistFork.bal_none`, decision lemmas);
no `CoveredFork` appears.

Contract-neutral: no contract name in any statement.
-/

namespace Blanc.Lift

open Jaune

/-! ## `afterSloadH` projections -/

theorem afterSloadH_getCode (sevm : Sevm) (base : Devm) (key : B256) (address : Adr) :
    (afterSloadH sevm base key).getCode address = base.getCode address := by
  unfold afterSloadH
  split
  · exact afterSload_getCode sevm base key address
  · rfl

theorem afterSloadH_accessedAddresses (sevm : Sevm) (base : Devm) (key : B256) :
    (afterSloadH sevm base key).accessedAddresses = base.accessedAddresses := by
  unfold afterSloadH
  split
  · exact afterSload_accessedAddresses sevm base key
  · rfl

theorem afterSloadH_error (sevm : Sevm) (base : Devm) (key : B256) :
    (afterSloadH sevm base key).error = base.error := by
  unfold afterSloadH
  split
  · exact afterSload_error sevm base key
  · rfl

theorem afterSloadH_createdAccounts (sevm : Sevm) (base : Devm) (key : B256) :
    (afterSloadH sevm base key).createdAccounts = base.createdAccounts := by
  unfold afterSloadH
  split
  · exact afterSload_createdAccounts sevm base key
  · rfl

theorem afterSloadH_accessedStorageKeys (sevm : Sevm) (base : Devm) (key : B256) :
    (afterSloadH sevm base key).accessedStorageKeys =
      match sevm.benvStat.rules.access with
      | .eip2929 =>
        sloadAccessedStorageKeys sevm.currentTarget base.accessedStorageKeys key
      | .flat _ => base.accessedStorageKeys := by
  unfold afterSloadH
  cases sevm.benvStat.rules.access with
  | eip2929 =>
    exact afterSload_accessedStorageKeys sevm base key
  | flat _ =>
    rfl

/-! ## `afterSstoreH` projections -/

theorem afterSstoreH_getCode (sevm : Sevm) (base : Devm) (key value : B256) (address : Adr) :
    (afterSstoreH sevm base key value).getCode address = base.getCode address := by
  unfold afterSstoreH storageAccessH
  split
  · by_cases h : sevm.currentTarget = address
    · subst h
      show ((((base.withRefundCounter _).state.setStorVal _ _ _).get _)).code = _
      rw [State.setStorVal_get_self]
      rfl
    · show ((((base.withRefundCounter _).state.setStorVal _ _ _).get _)).code = _
      rw [State.setStorVal_get_ne _ h]
      rfl
  · by_cases hw : (⟨sevm.currentTarget, key⟩ : Adr × B256) ∈ base.accessedStorageKeys
    · simp only [hw, ite_true]
      by_cases h : sevm.currentTarget = address
      · subst h
        show ((((base.withRefundCounter _).state.setStorVal _ _ _).get _)).code = _
        rw [State.setStorVal_get_self]
        rfl
      · show ((((base.withRefundCounter _).state.setStorVal _ _ _).get _)).code = _
        rw [State.setStorVal_get_ne _ h]
        rfl
    · simp only [hw, ite_false]
      by_cases h : sevm.currentTarget = address
      · subst h
        show (((((addAccessedStorageKey base _ _).withRefundCounter _).state.setStorVal _ _ _).get _)).code = _
        rw [State.setStorVal_get_self]
        rfl
      · show (((((addAccessedStorageKey base _ _).withRefundCounter _).state.setStorVal _ _ _).get _)).code = _
        rw [State.setStorVal_get_ne _ h]
        rfl

theorem afterSstoreH_accessedStorageKeys (sevm : Sevm) (base : Devm) (key value : B256) :
    (afterSstoreH sevm base key value).accessedStorageKeys =
      match sevm.benvStat.rules.access with
      | .eip2929 =>
        sloadAccessedStorageKeys sevm.currentTarget base.accessedStorageKeys key
      | .flat _ => base.accessedStorageKeys := by
  unfold afterSstoreH storageAccessH
  cases sevm.benvStat.rules.access with
  | eip2929 =>
    by_cases hw : (⟨sevm.currentTarget, key⟩ : Adr × B256) ∈ base.accessedStorageKeys
    · simp only [hw, ite_true, sloadAccessedStorageKeys]
      rfl
    · simp only [hw, ite_false, sloadAccessedStorageKeys]
      rfl
  | flat _ =>
    rfl

theorem getStor_afterSstoreH (sevm : Sevm) (b : Devm) (k v : B256) (a : Adr) :
    Devm.getStor (afterSstoreH sevm b k v) a =
      if a = sevm.currentTarget then (Devm.getStor b sevm.currentTarget).set k v
      else Devm.getStor b a := by
  split_ifs with h
  · subst h
    exact afterSstoreH_getStor_self _ _ _ _
  · exact afterSstoreH_getStor_ne _ _ _ _ _ (Ne.symm h)

/-! ## The quiet frame theorem without state gas -/

/-- **The quiet frame theorem** over `Ninst.world_of_quietH`: a run of a quiet
tree whose gotos and calls stay in a `QuietSet` keeps every storage map and the
log list, from `rules.stateGas = none` alone. -/
theorem SFunc.Run.world_of_quietH {fs : List SFunc} {S : List Nat}
    (hS : QuietSet fs S = true) {sevm : Sevm}
    (hsg : sevm.benvStat.rules.stateGas = none)
    {devm : Devm} {f : SFunc} {o : Outcome}
    (hf : f.quiet = true) (hrefs : f.refs.all (· ∈ S) = true)
    (run : SFunc.Run fs sevm devm f o) :
    Devm.getStor (Outcome.devm o) = Devm.getStor devm ∧ (Outcome.devm o).logs = devm.logs := by
  have closed : ∀ {k g}, k ∈ S → fs[k]? = some g →
      g.quiet = true ∧ g.refs.all (· ∈ S) = true := by
    intro k g hk hget
    have h := (List.all_eq_true.mp hS) k hk
    rw [hget] at h
    simpa only [List.all_eq_true, decide_eq_true_eq, Bool.and_eq_true] using h
  have tr : ∀ {a b c : Devm}, (Devm.getStor c = Devm.getStor b ∧ c.logs = b.logs) →
      (Devm.getStor b = Devm.getStor a ∧ b.logs = a.logs) →
      Devm.getStor c = Devm.getStor a ∧ c.logs = a.logs :=
    fun h1 h2 => ⟨h1.1.trans h2.1, h1.2.trans h2.2⟩
  induction run with
  | zero d pop run ih =>
      simp only [SFunc.quiet, Bool.and_eq_true] at hf
      simp only [SFunc.refs, List.all_append, Bool.and_eq_true] at hrefs
      exact tr (ih hf.1 hrefs.1) (PopBurn.world pop)
  | succ d w hnz pop run ih =>
      simp only [SFunc.quiet, Bool.and_eq_true] at hf
      simp only [SFunc.refs, List.all_append, Bool.and_eq_true] at hrefs
      exact tr (ih hf.2 hrefs.2) (PopBurn.world pop)
  | toZero d pop run ih =>
      simp only [SFunc.refs, List.all_cons, Bool.and_eq_true] at hrefs
      exact tr (ih hf hrefs.2) (PopBurn.world pop)
  | toSucc d w hnz lookup pop run ih =>
      simp only [SFunc.refs, List.all_cons, Bool.and_eq_true] at hrefs
      have ht := closed (of_decide_eq_true hrefs.1) lookup
      exact tr (ih ht.1 ht.2) (PopBurn.world pop)
  | last hrun =>
      exact Linst.world_of_ok (by simpa only [ne_eq, quiet, bne_iff_ne] using hf) hrun
  | next hrun run ih =>
      simp only [SFunc.quiet, Bool.and_eq_true] at hf
      exact tr (ih hf.2 hrefs) (Ninst.world_of_quietH hsg hf.1 hrun)
  | dest burn run ih =>
      exact tr (ih hf hrefs) (Burn.world burn)
  | jump d lookup pop run ih =>
      simp only [SFunc.refs, List.all_cons, Bool.and_eq_true] at hrefs
      have ht := closed (of_decide_eq_true hrefs.1) lookup
      exact tr (ih ht.1 ht.2) (PopBurn.world pop)
  | ret d pop =>
      exact PopBurn.world pop
  | callHalt d lookup pop run ih =>
      simp only [SFunc.refs, List.all_cons, Bool.and_eq_true] at hrefs
      have ht := closed (of_decide_eq_true hrefs.1) lookup
      exact tr (ih ht.1 ht.2) (PopBurn.world pop)
  | callRet d lookup pop run tail ihRun ihTail =>
      simp only [SFunc.refs, List.all_cons, Bool.and_eq_true] at hrefs
      have ht := closed (of_decide_eq_true hrefs.1) lookup
      simp only [SFunc.quiet] at hf
      exact tr (ihTail hf hrefs.2) (tr (ihRun ht.1 ht.2) (PopBurn.world pop))
  | pcAt hrun _ run ih =>
      simp only [SFunc.quiet] at hf
      simp only [SFunc.refs] at hrefs
      exact tr (ih hf hrefs) (Ninst.world_of_quietH hsg rfl hrun)

end Blanc.Lift
