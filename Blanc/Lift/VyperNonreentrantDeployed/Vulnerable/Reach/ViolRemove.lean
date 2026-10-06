import Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Reach.ViolRemoveRun4
import Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Reach.ViolRemoveSpec
import Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Reach.ViolCallback
import Blanc.Lift.NodeWalkFork

/-!
# V− P2, F2 composition: the `remove_liquidity` frame

`remove_frame (hCb : CallbackFrame) : RemoveFrame`: from the entry boundary
`bRm0` (with free tails), F2 runs 339 steps to its ETH `CALL` of the attacker
(`cRm339`/`cpRm`/`e3Rm`, `Reach/ViolRemoveRun1.lean`), whose callback child is
discharged by `CallbackFrame` via `childOk_of_start`; 234 steps later the
token's `transfer` child is discharged by `childOk_of_childRun`; 188 steps
later F2 halts with `gasRm`/`outRm` (`rmEndHalt_spec`, `Reach/ViolRemoveRun4.lean`).
Each kernel run transports to the actual machine by `rmRun_at`
(`wrun_withOrig_keys` + `wrun_withFork`, needing only agreement on the keys the
run records) and each spawn by `childStart_withOrig`/`childStart_withFork`.
The lift is `lift_exactM cert_checkM cert_jumpsOkM`, the settled shadows
`childAgree_of_halt`.
-/

namespace Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Reach.Viol

open Jaune Blanc.Lift Blanc.Lift.Witness Blanc.Lift.NodeWalk Blanc.ConcreteRun Blanc.ForkUniform
open Blanc.Lift.VyperNonreentrantDeployed
open Blanc.Lift.VyperNonreentrantDeployed.Vulnerable (cert t_0000_c0 cert_checkM cert_jumpsOkM)

/-! ## Transport -/

/-- The kernel's machine is the actual one with its original state changed back to `O0`. -/
theorem sRm_withOrig_O0 (O : State) : (sRm.withOrig O).withOrig O0 = sRm := rfl

/-- A kernel run of `sRm` that records only `Checkpoint`'s read keys is the same run at the
actual machine: any covered fork, any original state agreeing on `Checkpoint`'s read set. -/
theorem rmRun_at {g : Fork} {O : State} (hg : CoveredFork g)
    (hO : ∀ e ∈ readStor, storOf O e.1.1 e.1.2 = e.2) {n : Nat} {c : Cfg} {r : Res}
    (h : wrun fsI sRm n c = r) (hs : r ≠ .stuck) (hk : ∀ x ∈ resKeys r, x ∈ readKeys) :
    wrun fsI ((sRm.withOrig O).withFork g) n c = r := by
  have e := wrun_withOrig_keys (s := sRm.withOrig O) (O := O0) fsI n c
  rw [sRm_withOrig_O0, h] at e
  rw [wrun_withFork (s := sRm.withOrig O) CoveredFork.prague hg rfl]
  exact e hs (origAgreeOn_O0 hO hk)

/-- F2's prefix keys are `Checkpoint`'s read keys. -/
theorem rm339_sub : ∀ x ∈ [(proxyAddr, (8 : Nat).toB256), (proxyAddr, (26 : Nat).toB256),
    (proxyAddr, (2 : Nat).toB256)], x ∈ readKeys := by
  decide

/-- F2's `CALL` starts the callback child at the entered configuration, under any
covered fork and original state. -/
theorem csRm_at : ∀ (g : Fork) (O : State) (tS : StorShadow) (tA : AcctShadow)
    (m : Meta) (w : World), CoveredFork g →
    childStart ((sRm.withOrig O).withFork g) (cRm339 tS tA m w) AttackerR.t_0000_c0 =
      some (((e3Rm tS tA m w).withOrig O).withFork g, cc3Rm tS tA m w) := by
  intro g O tS tA m w hg
  have e1 : childStart (sRm.withOrig O) (cRm339 tS tA m w) AttackerR.t_0000_c0 =
      (childStart sRm (cRm339 tS tA m w) AttackerR.t_0000_c0).map
        (fun p => (p.1.withOrig O, p.2)) :=
    childStart_withOrig _ _
  rw [csRm_start tS tA m w] at e1
  have e2 := childStart_withFork (s := sRm.withOrig O) CoveredFork.prague hg
    (cRm339 tS tA m w) AttackerR.t_0000_c0
  rw [e1] at e2
  simpa only [Option.map_some] using e2


/-! ## The entered callback machine -/

/-- The literal static fields of the entered callback machine. -/
def e3StaObs (s : Sevm) : Bool :=
  decide (s.caller = proxyAddr) && decide (s.target = some attackerAddr) &&
    decide (s.currentTarget = attackerAddr) && decide (s.gas = 907011) &&
    decide (s.value = 100) && decide (s.data = []) &&
    decide (s.codeAddress = some attackerAddr) && decide (s.code = AttackerR.code) &&
    decide (s.depth = 1021) && decide (s.shouldTransferValue = true) &&
    decide (s.isStatic = false) && decide (s.disablePrecompiles = false)

/-- The environments remain those of the frozen callback machine. -/
def e3StaRest (s : Sevm) := (s.benvStat, s.tenvStat)

/-- Enter the callback from a supplied remove-prefix result. -/
def e3FromRun (tS : StorShadow) (tA : AcctShadow) (m : Meta) (w : World) (r : Res) : Evm :=
  let c := match r with
    | .cont c => c
    | _ => Boundary.cfgOfT bRm0 tS tA m w
  match frameEnterS ((callPrep sRm c).getD noPrepI).f c.acs with
  | .run e => e
  | .done _ => default

/-- The callback's literal static observation after the existing 161-step boundary. -/
theorem e3LateObs : ∀ (tS : StorShadow) (tA : AcctShadow) (m : Meta) (w : World),
    e3StaObs (e3FromRun tS tA m w
      (wrun fsI sRm 178 (Boundary.cfgOfT bRm161 tS tA m w))).sta = true := by
  kernel_forall_rfl

/-- The prepared callback inherits the remove frame's transaction environment. -/
theorem cpRm_tenvStat (tS : StorShadow) (tA : AcctShadow) (m : Meta) (w : World) :
    (cpRm tS tA m w).f.inner.tenv.stat = sRm.tenvStat := by
  have h := cpRm_eq tS tA m w
  unfold callPrep at h
  generalize (cRm339 tS tA m w).devm.stack = st at h
  match st, h with
  | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _, h =>
    simp only at h
    split at h
    · split at h
      · simp only [reduceCtorEq] at h
      · split at h
        · split at h
          · simp only [Option.some.injEq] at h
            rw [← h]
            rfl
          · simp only [reduceCtorEq] at h
        · split at h
          · simp only [Option.some.injEq] at h
            rw [← h]
            rfl
          · simp only [reduceCtorEq] at h
    · simp only [reduceCtorEq] at h

/-- Entering the callback preserves the prepared transaction environment. -/
theorem e3Rm_tenvStat (tS : StorShadow) (tA : AcctShadow) (m : Meta) (w : World) :
    (e3Rm tS tA m w).sta.tenvStat = sCb.tenvStat := by
  obtain ⟨benv, _, he⟩ := frameEnterS_run (e3Rm_eq tS tA m w)
  rw [he]
  exact cpRm_tenvStat tS tA m w

/-- The callback inherits both static environments. -/
theorem e3Rm_rest (tS : StorShadow) (tA : AcctShadow) (m : Meta) (w : World) :
    e3StaRest (e3Rm tS tA m w).sta = e3StaRest sCb := by
  apply Prod.ext
  · exact (frameEnterS_stat (e3Rm_eq tS tA m w)).trans
      (callPrep_stat (cpRm_eq tS tA m w)).2
  · exact e3Rm_tenvStat tS tA m w

/-- The full prefix's observation follows by composing through the existing boundary. -/
theorem e3Sta (tS : StorShadow) (tA : AcctShadow) (m : Meta) (w : World) :
    e3StaObs (e3Rm tS tA m w).sta = true ∧
      e3StaRest (e3Rm tS tA m w).sta = e3StaRest sCb := by
  obtain ⟨m1, w1, h1⟩ := Boundary.obsDT_cont (rmChunk161 tS tA m w)
  have hjoin : wrun fsI sRm 339 (Boundary.cfgOfT bRm0 tS tA m w) =
      wrun fsI sRm 178 (Boundary.cfgOfT bRm161 tS tA m1 w1) := by
    rw [show 339 = 161 + 178 from rfl, wrun_add, h1]
  have hlate := hjoin.symm.trans (cRm339_eq tS tA m w)
  have hE : e3Rm tS tA m w = e3FromRun tS tA m1 w1
      (wrun fsI sRm 178 (Boundary.cfgOfT bRm161 tS tA m1 w1)) := by
    unfold e3FromRun
    rw [hlate]
    rfl
  refine ⟨?_, e3Rm_rest tS tA m w⟩
  rw [hE]
  exact e3LateObs tS tA m1 w1

/-- The callback's static machine, reconstructed from its checked observation. -/
theorem e3Sta_spec {s : Sevm} (ho : e3StaObs s = true)
    (hr : e3StaRest s = e3StaRest sCb) : s = sCb := by
  simp only [e3StaObs, Bool.and_eq_true, decide_eq_true_eq] at ho
  simp only [e3StaRest, Prod.mk.injEq] at hr
  rcases s with ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14⟩
  rcases ho with ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hc, ht⟩, hct⟩, hg⟩, hv⟩, hd⟩, hca⟩, hco⟩, hdep⟩, hstv⟩, hst⟩, hdp⟩
  rcases hr with ⟨hbs, hts⟩
  subst hc ht hct hg hv hd hca hco hdep hstv hst hdp hbs hts
  rfl

/-- The callback's static machine, before fork/original-state transport. -/
theorem e3Rm_sta (tS : StorShadow) (tA : AcctShadow) (m : Meta) (w : World) :
    (e3Rm tS tA m w).sta = sCb :=
  e3Sta_spec (e3Sta tS tA m w).1 (e3Sta tS tA m w).2

theorem e3g_caller : ∀ (g : Fork) (O : State) (tS : StorShadow) (tA : AcctShadow)
    (m : Meta) (w : World),
    (((e3Rm tS tA m w).withOrig O).withFork g).sta.caller = proxyAddr := by
  intro g O tS tA m w
  simp only [Evm.withOrig, Evm.withFork, e3Rm_sta]
  rfl

theorem e3g_target : ∀ (g : Fork) (O : State) (tS : StorShadow) (tA : AcctShadow)
    (m : Meta) (w : World),
    (((e3Rm tS tA m w).withOrig O).withFork g).sta.target = some attackerAddr := by
  intro g O tS tA m w
  simp only [Evm.withOrig, Evm.withFork, e3Rm_sta]
  rfl

theorem e3g_currentTarget : ∀ (g : Fork) (O : State) (tS : StorShadow) (tA : AcctShadow)
    (m : Meta) (w : World),
    (((e3Rm tS tA m w).withOrig O).withFork g).sta.currentTarget = attackerAddr := by
  intro g O tS tA m w
  simp only [Evm.withOrig, Evm.withFork, e3Rm_sta]
  rfl

theorem e3g_gas : ∀ (g : Fork) (O : State) (tS : StorShadow) (tA : AcctShadow)
    (m : Meta) (w : World),
    (((e3Rm tS tA m w).withOrig O).withFork g).sta.gas = 907011 := by
  intro g O tS tA m w
  simp only [Evm.withOrig, Evm.withFork, e3Rm_sta]
  rfl

theorem e3g_value : ∀ (g : Fork) (O : State) (tS : StorShadow) (tA : AcctShadow)
    (m : Meta) (w : World),
    (((e3Rm tS tA m w).withOrig O).withFork g).sta.value = 100 := by
  intro g O tS tA m w
  simp only [Evm.withOrig, Evm.withFork, e3Rm_sta]
  rfl

theorem e3g_data : ∀ (g : Fork) (O : State) (tS : StorShadow) (tA : AcctShadow)
    (m : Meta) (w : World),
    (((e3Rm tS tA m w).withOrig O).withFork g).sta.data = [] := by
  intro g O tS tA m w
  simp only [Evm.withOrig, Evm.withFork, e3Rm_sta]
  rfl

theorem e3g_codeAddress : ∀ (g : Fork) (O : State) (tS : StorShadow) (tA : AcctShadow)
    (m : Meta) (w : World),
    (((e3Rm tS tA m w).withOrig O).withFork g).sta.codeAddress = some attackerAddr := by
  intro g O tS tA m w
  simp only [Evm.withOrig, Evm.withFork, e3Rm_sta]
  rfl

theorem e3g_code : ∀ (g : Fork) (O : State) (tS : StorShadow) (tA : AcctShadow)
    (m : Meta) (w : World),
    (((e3Rm tS tA m w).withOrig O).withFork g).sta.code = AttackerR.code := by
  intro g O tS tA m w
  simp only [Evm.withOrig, Evm.withFork, e3Rm_sta]
  rfl

theorem e3g_depth : ∀ (g : Fork) (O : State) (tS : StorShadow) (tA : AcctShadow)
    (m : Meta) (w : World),
    (((e3Rm tS tA m w).withOrig O).withFork g).sta.depth = 1021 := by
  intro g O tS tA m w
  simp only [Evm.withOrig, Evm.withFork, e3Rm_sta]
  rfl

theorem e3g_benvStat : ∀ (g : Fork) (O : State) (tS : StorShadow) (tA : AcctShadow)
    (m : Meta) (w : World),
    (((e3Rm tS tA m w).withOrig O).withFork g).sta.benvStat = ((sCb.withOrig O).withFork g).benvStat := by
  intro g O tS tA m w
  simp only [Evm.withOrig, Evm.withFork, e3Rm_sta]

theorem e3g_tenvStat : ∀ (g : Fork) (O : State) (tS : StorShadow) (tA : AcctShadow)
    (m : Meta) (w : World),
    (((e3Rm tS tA m w).withOrig O).withFork g).sta.tenvStat = ((sCb.withOrig O).withFork g).tenvStat := by
  intro g O tS tA m w
  simp only [Evm.withOrig, Evm.withFork, e3Rm_sta]

theorem e3g_flags : ∀ (g : Fork) (O : State) (tS : StorShadow) (tA : AcctShadow)
    (m : Meta) (w : World),
    (((e3Rm tS tA m w).withOrig O).withFork g).sta.shouldTransferValue = true ∧
      (((e3Rm tS tA m w).withOrig O).withFork g).sta.isStatic = false ∧
      (((e3Rm tS tA m w).withOrig O).withFork g).sta.disablePrecompiles = false := by
  intro g O tS tA m w
  simp only [Evm.withOrig, Evm.withFork, e3Rm_sta]
  exact ⟨rfl, rfl, rfl⟩

/-- The entered callback machine is `CallbackFrame`'s static machine. -/
theorem e3g_sta : ∀ (g : Fork) (O : State) (tS : StorShadow) (tA : AcctShadow)
    (m : Meta) (w : World),
    (((e3Rm tS tA m w).withOrig O).withFork g).sta =
      ((((sCb.withOrig O).withFork g))) := by
  intro g O tS tA m w
  change ((e3Rm tS tA m w).sta.withOrig O).withFork g = _
  rw [e3Rm_sta]

/-! ## Settled literals -/

/-- F2's settled storage literals over any tail. -/
theorem rmPost26 : ∀ (tS : StorShadow),
    lookupS (storRm ++ tS) proxyAddr 26 = 1800 := by
  kernel_forall_rfl

theorem rmPostLP : ∀ (tS : StorShadow),
    lookupS (storRm ++ tS) proxyAddr lpSlotA = 1906 := by
  kernel_forall_rfl

theorem rmPost2 : ∀ (tS : StorShadow),
    lookupS (storRm ++ tS) proxyAddr 2 = 0 := by
  kernel_forall_rfl

/-- The callback certificate's jumps check (single entry; `Check.lean` proves only
`cert_check` for `AttackerR`). -/
theorem AttackerR_jumpsOk : Cert.jumpsOk AttackerR.code AttackerR.cert = true := by
  decide +kernel

/-- The token call retains the keys already recorded before the child starts. -/
theorem cTokRm_keys : ∀ (tS : StorShadow) (tA : AcctShadow) (m : Meta) (w : World),
    (cTokRm tS tA m w).keys = keysTok.drop 2 := by
  kernel_forall_rfl

/-! ## The `remove_liquidity` frame -/


/-- **P2, F2 (with F3 by `CallbackFrame` and the token's `transfer` child)**:
the `remove_liquidity` frame from its entry boundary `bRm0`. -/
theorem remove_frame (hCb : CallbackFrame) : RemoveFrame := by
  intro g O tS tA m w hg hRead hAgree
  let S := (sRm.withOrig O).withFork g
  let E := ((e3Rm tS tA m w).withOrig O).withFork g
  have hPre : wrun fsI S 339 (Boundary.cfgOfT bRm0 tS tA m w) =
      .cont (cRm339 tS tA m w) :=
    rmRun_at hg hRead (cRm339_eq tS tA m w) (fun h => Res.noConfusion h)
      (by simpa only [resKeys, cRm339_keys tS tA m w] using rm339_sub)
  have sPre := wrun_cont hPre
  have hag339 := sPre.1 hAgree
  have hStart := csRm_at g O tS tA m w hg
  have hSpawn : SpawnedBy S (cRm339 tS tA m w).devm .call E :=
    spawnedBy_of_childStart hag339 hStart
  have hag3 := childStart_agree hag339 hStart
  have heq3 := Boundary.cfg_of_obsDT (cc3Rm_obs tS tA m w)
  have hagCb : Agree (Boundary.cfgOfT bCb0 tS tA (cc3Rm tS tA m w).devm.meta
      (cc3Rm tS tA m w).devm.world) := by
    rw [← heq3]; exact hag3
  obtain ⟨c1Cb, clCb, postCb, sCb12, hwrCb2, hgasCb, houtCb, herrCb, hkeysCb,
    hadrsCb, hstorCb, hacsCb, hreentry⟩ := hCb g O tS tA _ _ hg hRead hagCb
  have he3sta : E.sta = (sCb.withOrig O).withFork g := e3g_sta g O tS tA m w
  have hreentry3 : ReentryFacts E.sta (cc3Rm tS tA m w) := by
    rw [he3sta, heq3]; exact hreentry
  have hcbObs := childObs_eq hgasCb houtCb herrCb
  have hkCb : ChildOk S (cRm339 tS tA m w) postCb ∧
      ChildAgree postCb clCb.keys clCb.adrs clCb.stor clCb.acs := by
    have hstep : StepOk fsA E.sta (cc3Rm tS tA m w) c1Cb := by
      rw [he3sta, heq3]; exact sCb12
    have hrun : wrun fsA E.sta 2 c1Cb = .done (.halted postCb) clCb := by
      rw [he3sta]; exact hwrCb2
    exact childOk_of_start
      (fun hcode hfork hrun => lift_exact AttackerR.cert_check AttackerR_jumpsOk
        hcode hfork hrun)
      hag339 fsA_zero hStart (by rw [he3sta]; exact hg)
      (by rw [he3sta]; rfl) hstep hrun herrCb
  have aCb : ChildAgree postCb keysCb adrsCb (storCb ++ tS) (acsCb ++ tA) := by
    rw [← hkeysCb, ← hadrsCb, ← hstorCb, ← hacsCb]; exact hkCb.2
  obtain ⟨m1, w1, h1⟩ := Boundary.obsDT_cont (rmChunkX1 tS tA m w postCb)
  rw [hcbObs, cRm339_eq] at h1
  simp only [runRmA, Boundary.callPairA] at h1
  obtain ⟨cA, hR1, h1⟩ : ∃ cA,
      callResume sRm (cRm339 tS tA m w) postCb keysCb adrsCb
        (storCb ++ tS) (acsCb ++ tA) = some cA ∧
      wrun fsI sRm 3 cA = .cont (Boundary.cfgOfT bRmX1 tS tA m1 w1) := by
    cases hR : callResume sRm (cRm339 tS tA m w) postCb keysCb adrsCb
        (storCb ++ tS) (acsCb ++ tA) with
    | none => simp only [hR, reduceCtorEq] at h1
    | some cA => rw [hR] at h1; exact ⟨cA, rfl, h1⟩
  have hR1g : callResume S (cRm339 tS tA m w) postCb keysCb adrsCb
      (storCb ++ tS) (acsCb ++ tA) = some cA := by
    rw [callResume_withFork CoveredFork.prague hg, callResume_withOrig]; exact hR1
  have sRes1 : StepOk fsI S (cRm339 tS tA m w) cA := callResume_cont hR1g hkCb.1 aCb
  have h1g : wrun fsI S 3 cA = .cont (Boundary.cfgOfT bRmX1 tS tA m1 w1) :=
    rmRun_at hg hRead h1 (fun h => Res.noConfusion h) (by
      change ∀ x ∈ ([(proxyAddr, (8 : Nat).toB256), (proxyAddr, (26 : Nat).toB256),
        (proxyAddr, (2 : Nat).toB256)] ++ keysCb), x ∈ readKeys
      decide)
  obtain ⟨m2, w2, h2⟩ := Boundary.obsDT_cont (rmChunkX2 tS tA m1 w1)
  have h2g : wrun fsI S 220 (Boundary.cfgOfT bRmX1 tS tA m1 w1) =
      .cont (Boundary.cfgOfT bRmX2 tS tA m2 w2) :=
    rmRun_at hg hRead h2 (fun h => Res.noConfusion h) (by
      change ∀ x ∈ ([(proxyAddr, (8 : Nat).toB256), (proxyAddr, (26 : Nat).toB256),
        (proxyAddr, (2 : Nat).toB256)] ++ keysCb), x ∈ readKeys
      decide)
  have hCall : wrun fsI S 11 (Boundary.cfgOfT bRmX2 tS tA m2 w2) =
      .cont (cTokRm tS tA m2 w2) :=
    rmRun_at hg hRead (cTokRm_eq tS tA m2 w2) (fun h => Res.noConfusion h) (by
      intro x hx
      have hsub : ∀ x ∈ keysTok.drop 2, x ∈ readKeys := by decide
      simp only [resKeys, cTokRm_keys tS tA m2 w2] at hx
      exact hsub x hx)
  have sBeforeTok := (((sPre.trans sRes1).trans (wrun_cont h1g)).trans
    (wrun_cont h2g)).trans (wrun_cont hCall)
  have hagTok := sBeforeTok.1 hAgree
  have htokSub : ∀ x ∈ keysTok, x ∈ readKeys := by decide
  have hTok : childRun Token20.prog Token20.code S 200 (cTokRm tS tA m2 w2) =
      .done (.halted (dTokRm tS tA m2 w2)) (clTokRm tS tA m2 w2) := by
    have hne : childRun Token20.prog Token20.code ((sRm.withOrig O).withOrig O0)
        200 (cTokRm tS tA m2 w2) ≠ .stuck := by
      rw [sRm_withOrig_O0, tokChild_eq]; exact fun h => Res.noConfusion h
    have hoa : OrigAgreeOn O0 O (resKeys (childRun Token20.prog Token20.code
        ((sRm.withOrig O).withOrig O0) 200 (cTokRm tS tA m2 w2))) :=
      origAgreeOn_O0 hRead (by rw [sRm_withOrig_O0, tokRun_keys]; exact htokSub)
    have eOrig := childRun_withOrig_keys (s := sRm.withOrig O) (O := O0)
      Token20.prog Token20.code 200 (cTokRm tS tA m2 w2) hne hoa
    rw [sRm_withOrig_O0, tokChild_eq] at eOrig
    rw [childRun_withFork (s := sRm.withOrig O) CoveredFork.prague hg rfl, eOrig]
  obtain ⟨kTok, aTok⟩ := childOk_of_childRun
    (fun hcode hfork hrun => lift_exact Token20.cert_check Token20.cert_jumpsOk
      hcode hfork hrun) hagTok hTok (tokChild_err tS tA m2 w2)
  have htokObs := childObs_eq (tokChild_gas tS tA m2 w2)
    (tokChild_out tS tA m2 w2) (tokChild_err tS tA m2 w2)
  obtain ⟨m3, w3, h3⟩ := Boundary.obsDT_cont
    (rmChunkX3 tS tA m2 w2 (dTokRm tS tA m2 w2))
  rw [htokObs, cTokRm_eq] at h3
  simp only [runRmB, Boundary.callPairA] at h3
  obtain ⟨cB, hR2, h3⟩ : ∃ cB,
      callResume sRm (cTokRm tS tA m2 w2) (dTokRm tS tA m2 w2) keysTok adrsTok
        (storTok ++ tS) (acsTok ++ tA) = some cB ∧
      wrun fsI sRm 3 cB = .cont (Boundary.cfgOfT bRmX3 tS tA m3 w3) := by
    cases hR : callResume sRm (cTokRm tS tA m2 w2) (dTokRm tS tA m2 w2)
        keysTok adrsTok (storTok ++ tS) (acsTok ++ tA) with
    | none => simp only [hR, reduceCtorEq] at h3
    | some cB => rw [hR] at h3; exact ⟨cB, rfl, h3⟩
  have hR2g : callResume S (cTokRm tS tA m2 w2) (dTokRm tS tA m2 w2) keysTok adrsTok
      (storTok ++ tS) (acsTok ++ tA) = some cB := by
    rw [callResume_withFork CoveredFork.prague hg, callResume_withOrig]; exact hR2
  have aTok' : ChildAgree (dTokRm tS tA m2 w2) keysTok adrsTok
      (storTok ++ tS) (acsTok ++ tA) := by
    rw [← tokChild_keys tS tA m2 w2, ← tokChild_adrs tS tA m2 w2,
      ← tokChild_stor tS tA m2 w2, ← tokChild_acs tS tA m2 w2]; exact aTok
  have sRes2 : StepOk fsI S (cTokRm tS tA m2 w2) cB := callResume_cont hR2g kTok aTok'
  have h3g : wrun fsI S 3 cB = .cont (Boundary.cfgOfT bRmX3 tS tA m3 w3) :=
    rmRun_at hg hRead h3 (fun h => Res.noConfusion h) (by
      change ∀ x ∈ keysTok.drop 2 ++ keysTok, x ∈ readKeys
      decide)
  have sFull := (sBeforeTok.trans sRes2).trans (wrun_cont h3g)
  have hagEnd := sFull.1 hAgree
  obtain ⟨post, cl, hr, hgas, hout, herr, hkeys, hadrs, hstor, hacs⟩ :=
    rmEndHalt_spec (rmEndHalt tS tA m3 w3).1 (rmEndHalt tS tA m3 w3).2
  have hrEnd : wrun fsI S 188 (Boundary.cfgOfT bRmX3 tS tA m3 w3) =
      .done (.halted post) cl :=
    rmRun_at hg hRead hr (fun h => Res.noConfusion h) (by
      simpa only [resKeys, hkeys] using keys_sub_readKeys.2.2.1)
  obtain ⟨runE, _, _⟩ := wrun_done hrEnd hagEnd
  have hrunE : SProg.RunExact (Cert.prog cert) S
      (Boundary.cfgOfT bRm0 tS tA m w).devm post :=
    ⟨t_0000_c0, fsI_zero, sFull.2 _ hAgree runE⟩
  have hxExec : Nonempty (Exec 0 S (Boundary.cfgOfT bRm0 tS tA m w).devm (.ok post)) :=
    lift_exactM cert_checkM cert_jumpsOkM rfl hg hrunE
  have hca : ChildAgree post keysRm adrsRm (storRm ++ tS) (acsRm ++ tA) := by
    have ha := childAgree_of_halt hrEnd hagEnd
    rw [hkeys, hadrs, hstor, hacs] at ha; exact ha
  have hs2 : storOf (cRm339 tS tA m w).devm.state proxyAddr 2 = 1 := by
    have h := hag339.2.2.1 proxyAddr 2
    rw [rm339_stor2 tS tA m w] at h; exact h
  have hs26 : storOf (cRm339 tS tA m w).devm.state proxyAddr 26 = 2000 := by
    have h := hag339.2.2.1 proxyAddr 26
    rw [rm339_stor26 tS tA m w] at h; exact h
  have hpost26 : storOf post.state proxyAddr 26 = 1800 := by
    have h := hca.2.2.1 proxyAddr 26
    rw [rmPost26 tS] at h; exact h
  have hpostLP : storOf post.state proxyAddr lpSlotA = 1906 := by
    have h := hca.2.2.1 proxyAddr lpSlotA
    rw [rmPostLP tS] at h; exact h
  have hpost2 : storOf post.state proxyAddr 2 = 0 := by
    have h := hca.2.2.1 proxyAddr 2
    rw [rmPost2 tS] at h; exact h
  refine ⟨post, hxExec, hgas, hout, herr, hca, boundary_values.1,
    cRm339 tS tA m w, E, cc3Rm tS tA m w, hPre, hag339, hs2, hs26, hSpawn,
    ?_, ?_, ?_, ?_, ?_, ?_, hag3, hreentry3, hpost26, hpostLP, hpost2⟩
  · rw [he3sta]; rfl
  · rw [he3sta]; rfl
  · rw [he3sta]; rfl
  · simp only [E, cc3Rm, Evm.withOrig, Evm.withFork]
  · simp only [cc3Rm]
  · simp only [cc3Rm]

end Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Reach.Viol
