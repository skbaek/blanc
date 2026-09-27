import Blanc.Lift.Witness

/-!
# Code children of a witness run, discharged by their own witness runs

`Blanc.Lift.Witness` runs a frame over its certificate and takes each code child of a
`CALL` as data: a settled machine with `ChildOk` (it is the settlement of an `Exec` from
the machine the call's frame enters with) and `ChildAgree` (its accessed sets, storage
and accounts, as shadows).  This module discharges those two obligations by running the
child itself: the child's frame starts from the machine `Frame.enter` builds, with the
parent's shadows (the callee added to the address shadow, the value transfer applied to
the account shadow), and a halting run of the child's own checked certificate is its
`Exec` (through `lift_exact`/`lift_exactM`, supplied by the caller as `hexact`).  The
settled child is the halted machine itself (a successful call frame settles to its
result), and its shadows are those of the configuration that halted.

The same construction serves a child spawned by a `DELEGATECALL` of code the interpreter
does not run (`dcallPrep`, the `DELEGATECALL` arm up to its spawn, warm/cold on the
address shadow and the callee's code from the account shadow; `dcallPrep_spec`).
Nothing here is contract-specific.
-/

namespace Blanc.Lift.Witness

open Jaune Blanc.Lift

/-! ## Halting keeps the accessed sets -/

theorem linst_return_keep {sevm : Sevm} {devm d : Devm}
    (h : Linst.run sevm devm .return_ = .ok d) : AccKeep devm d := by
  simp only [Linst.run] at h
  obtain ⟨⟨i, d1⟩, h1, e1⟩ := Except.bind_eq_ok h
  obtain ⟨⟨n, d2⟩, h2, e2⟩ := Except.bind_eq_ok e1
  obtain ⟨d3, h3, h4⟩ := Except.bind_eq_ok e2
  cases h4
  exact (accKeep_popToNat h1).trans ((accKeep_popToNat h2).trans
    ((accKeep_chargeGas h3).trans ⟨rfl, rfl, rfl⟩))

/-- A step that halts keeps its configuration's accessed sets and world. -/
theorem wstep_halt_keep {fs : List SFunc} {sevm : Sevm} {c c' : Cfg} {d : Devm}
    (h : wstep fs sevm c = .done (.halted d) c') : AccKeep c.devm d := by
  rcases c with ⟨devm, f, K, keys, adrs, stor, acs⟩
  cases f with
  | ret =>
    simp only [wstep] at h
    split at h <;> (try split at h) <;> (try split at h) <;> cases h
  | last l =>
    cases l <;> simp only [wstep] at h
    · split at h
      · rename_i d' hd
        cases h
        simp only [Linst.run, Except.ok.injEq] at hd; rw [← hd]; exact AccKeep.refl _
      · cases h
    · split at h
      · rename_i d' hd
        cases h
        exact linst_return_keep hd
      · cases h
    · split at h
      · rename_i d' hd
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

/-- A run that halts: the halted machine keeps the halting configuration's accessed
sets and world. -/
theorem wrun_halt_keep {fs : List SFunc} {sevm : Sevm} :
    ∀ {n : Nat} {c c' : Cfg} {d : Devm}, wrun fs sevm n c = .done (.halted d) c' →
      AccKeep c'.devm d
  | 0, c, c', d, h => by simp [wrun] at h
  | n + 1, c, c', d, h => by
    simp only [wrun] at h
    split at h
    · exact wrun_halt_keep h
    · have hc := (wstep_done h).2.1
      subst hc
      exact wstep_halt_keep h

/-! ## A frame entered with shadows -/

theorem frameEnterS_run {f : Frame} {acs : AcctShadow} {cevm : Evm}
    (h : frameEnterS f acs = .run cevm) :
    ∃ benv, benvAfterTransferS f.inner acs = .ok benv ∧ cevm = initEvm (f.inner.withBenv benv) := by
  unfold frameEnterS at h
  split at h
  · cases h
  · rename_i benv hb
    refine ⟨benv, hb, ?_⟩
    split at h
    · rename_i evm hen
      cases h
      unfold executeCode.enter at hen
      dsimp only at hen
      split at hen
      · cases hen; rfl
      · split at hen
        · cases hen
        · cases hen; rfl
    · cases h

/-- A successful call frame settles to its result. -/
theorem frame_settle_ok {f : Frame} {post : Devm} (hcr : f.isCreate = false)
    (hsg : f.inner.benv.stat.rules.stateGas = none) (he : post.error = none) :
    f.settle (.ok post) = .ok post := by
  simp [Frame.settle, Frame.settleMsg, hcr, executeCode.handleErrorWith, hsg,
    executeCode.handleError, processMessage.settle, bind, Except.bind, he]

/-- **A code child run by its own certificate.**  The frame `f` enters (`frameEnterS`)
with the machine `cevm`; its message's accessed sets, storage and accounts agree with
`keys`/`adrs`/`stor`/`acs`; a halting run of `fs` from `cevm` with those shadows (the
value transfer applied to `acs`) whose halted machine has no error is an `Exec` from
`cevm` (by `hexact`), the frame settles to it, and its shadows are the halting
configuration's. -/
theorem frame_of_wrun {fs : List SFunc} {f : Frame} {acs : AcctShadow} {cevm : Evm}
    {keys : List (Adr × B256)} {adrs : List Adr} {stor : StorShadow} {f0 : SFunc} {n : Nat}
    {post : Devm} {c1 cl : Cfg}
    (he : frameEnterS f acs = .run cevm)
    (hK : ∀ x, x ∈ f.inner.accessedStorageKeys ↔ x ∈ keys)
    (hA : ∀ a, a ∈ f.inner.accessedAddresses ↔ a ∈ adrs)
    (hS : ∀ a k, storOf f.inner.benv.state a k = lookupS stor a k)
    (hC : AcctAgree f.inner.benv.state acs)
    (hcr : f.isCreate = false) (hsg : f.inner.benv.stat.rules.stateGas = none)
    (hexact : SProg.RunExact fs cevm.sta cevm.dyna post →
      Nonempty (Exec 0 cevm.sta cevm.dyna (.ok post)))
    (h0 : fs[0]? = some f0)
    (hstep : StepOk fs cevm.sta ⟨cevm.dyna, f0, [], keys, adrs, stor, acsTransfer f.inner acs⟩ c1)
    (hrun : wrun fs cevm.sta n c1 = .done (.halted post) cl)
    (herr : post.error = none) :
    Nonempty (Exec cevm.pc cevm.sta cevm.dyna (.ok post)) ∧ f.settle (.ok post) = .ok post ∧
      ChildAgree post cl.keys cl.adrs cl.stor cl.acs := by
  obtain ⟨benv, hb, rfl⟩ := frameEnterS_run he
  have hag : Agree ⟨(initEvm (f.inner.withBenv benv)).dyna, f0, [], keys, adrs, stor,
      acsTransfer f.inner acs⟩ := by
    have hbB : benvAfterTransferB f.inner = .ok benv := by
      rw [benvAfterTransfer_eq_S hC]; exact hb
    refine ⟨fun x => hK x, fun a => hA a, fun a k => ?_, ?_⟩
    · show storOf benv.state a k = lookupS stor a k
      rw [benvAfterTransferB_stor hbB]; exact hS a k
    · exact acctAgree_transfer hC hb
  obtain ⟨run, hcl, hst⟩ := wrun_done hrun (hstep.1 hag)
  have hkeep := wrun_halt_keep hrun
  refine ⟨hexact ⟨f0, h0, hstep.2 _ hag run⟩, frame_settle_ok hcr hsg herr, ?_, ?_, ?_, ?_⟩
  · intro a; rw [hkeep.1]; exact hcl.2.1 a
  · intro k; rw [hkeep.2.1]; exact hcl.1 k
  · intro a k; rw [hkeep.2.2]; exact hcl.2.2.1 a k
  · intro a; rw [hkeep.2.2]; exact hcl.2.2.2 a

/-! ## Code children of a `CALL` in a witness run -/

/-- The child frame a code `CALL` at `c` enters with: its machine, and its start
configuration at `f0` with the parent's shadows. -/
def childStart (sevm : Sevm) (c : Cfg) (f0 : SFunc) : Option (Evm × Cfg) :=
  match callPrep sevm c with
  | some cp =>
    match frameEnterS cp.f c.acs with
    | .run cevm =>
      some (cevm, ⟨cevm.dyna, f0, [], c.keys, cp.adrs, c.stor, acsTransfer cp.f.inner c.acs⟩)
    | .done _ => none
  | none => none

/-- The child of the code `CALL` at `c`, run for at most `n` steps over `fs`, provided
its code is `code` (as bytes) and its fork is covered. -/
def childRun (fs : List SFunc) (code : ByteArray) (sevm : Sevm) (n : Nat) (c : Cfg) : Res :=
  match fs[0]? with
  | some f0 =>
    match childStart sevm c f0 with
    | some (e, cc) =>
      if decide (CoveredFork e.sta.benvStat.fork) ∧ e.sta.code.data.toList = code.data.toList
      then wrun fs e.sta n cc
      else .stuck
    | none => .stuck
  | none => .stuck

theorem byteArray_eq_of_toList {a b : ByteArray} (h : a.data.toList = b.data.toList) : a = b := by
  rcases a with ⟨a⟩; rcases b with ⟨b⟩
  simp only at h
  rw [Array.toList_inj.mp h]

/-- **A code child discharged.**  If the child of the code `CALL` at an agreeing `c`,
started by `childStart`, takes the steps `hstep` (chunks, and `callResume`s of its own
code children) and then halts under its own certificate (`hexact`: a run of `fs` is an
`Exec` of `code`, e.g. `lift_exact`) with no error, the halted machine is that call's
child (`ChildOk`), and the halting configuration's shadows describe it (`ChildAgree`). -/
theorem childOk_of_start {fs : List SFunc} {code : ByteArray} {sevm : Sevm} {n : Nat}
    {c c1 cl cc : Cfg} {f0 : SFunc} {cevm : Evm} {post : Devm}
    (hexact : ∀ {sevm' : Sevm} {pre : Devm}, sevm'.code = code →
      CoveredFork sevm'.benvStat.fork → SProg.RunExact fs sevm' pre post →
      Nonempty (Exec 0 sevm' pre (.ok post)))
    (hagree : Agree c) (h0 : fs[0]? = some f0) (hs : childStart sevm c f0 = some (cevm, cc))
    (hfork : CoveredFork cevm.sta.benvStat.fork) (hcode : cevm.sta.code = code)
    (hstep : StepOk fs cevm.sta cc c1) (hrun : wrun fs cevm.sta n c1 = .done (.halted post) cl)
    (herr : post.error = none) :
    ChildOk sevm c post ∧ ChildAgree post cl.keys cl.adrs cl.stor cl.acs := by
  unfold childStart at hs
  split at hs
  · rename_i cp hp
    split at hs
    · rename_i cevm' he
      simp only [Option.some.injEq, Prod.mk.injEq] at hs
      obtain ⟨h1, h2⟩ := hs
      subst h1 h2
      obtain ⟨-, hpa, hpk, hcr, hia, hik, hsg, hst⟩ := callPrep_spec hp hagree.2.1 hagree.2.2.2
      have hC : AcctAgree cp.f.inner.benv.state c.acs := by rw [hst]; exact hagree.2.2.2
      obtain ⟨hx, hs, ha⟩ := frame_of_wrun he
        (fun x => by rw [hik, hpk]; exact hagree.1 x)
        (fun a => by rw [hia]; exact hpa a)
        (fun a k => by rw [hst]; exact hagree.2.2.1 a k) hC hcr hsg
        (hexact hcode hfork) h0 hstep hrun herr
      refine ⟨fun cp' cevm'' hp' he' => ?_, ha⟩
      rw [hp] at hp'
      cases hp'
      rw [he] at he'
      cases he'
      exact ⟨.ok post, hx, hs⟩
    · cases hs
  · cases hs

/-- `childOk_of_start` for a child that runs straight to its halt (`childRun`). -/
theorem childOk_of_childRun {fs : List SFunc} {code : ByteArray} {sevm : Sevm} {n : Nat}
    {c cl : Cfg} {post : Devm}
    (hexact : ∀ {sevm' : Sevm} {pre : Devm}, sevm'.code = code →
      CoveredFork sevm'.benvStat.fork → SProg.RunExact fs sevm' pre post →
      Nonempty (Exec 0 sevm' pre (.ok post)))
    (hagree : Agree c) (hrun : childRun fs code sevm n c = .done (.halted post) cl)
    (herr : post.error = none) :
    ChildOk sevm c post ∧ ChildAgree post cl.keys cl.adrs cl.stor cl.acs := by
  unfold childRun at hrun
  split at hrun
  · rename_i f0 h0
    split at hrun
    · rename_i cevm cc hcs
      split at hrun
      · rename_i hcond
        exact childOk_of_start hexact hagree h0 hcs (of_decide_eq_true hcond.1)
          (byteArray_eq_of_toList hcond.2) ⟨id, fun _ _ r => r⟩ hrun herr
      · cases hrun
    · cases hrun
  · cases hrun

/-- A `callResume` succeeds only on a child without error. -/
theorem callResume_error {sevm : Sevm} {c c' : Cfg} {child : Devm} {ckeys : List (Adr × B256)}
    {cadrs : List Adr} {cstor : StorShadow} {cacs : AcctShadow}
    (h : callResume sevm c child ckeys cadrs cstor cacs = some c') : child.error = none := by
  unfold callResume at h
  split at h
  · split at h
    · split at h
      · split at h
        · rename_i hce
          cases he : child.error
          · rfl
          · rw [he] at hce; cases hce
        · cases h
      · cases h
    · cases h
  · cases h

end Blanc.Lift.Witness
