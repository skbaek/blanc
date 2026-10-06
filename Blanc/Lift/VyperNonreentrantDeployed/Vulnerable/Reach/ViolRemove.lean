import Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Reach.ViolRemoveRun2
import Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Reach.ViolCallback
import Blanc.Lift.NodeWalkFork

/-!
# V− P2, F2 composition: the `remove_liquidity` frame

`remove_frame (hCb : CallbackFrame) : RemoveFrame`: from the entry boundary
`bRm0` (with free tails), F2 runs 339 steps to its ETH `CALL` of the attacker
(`cRm339`/`cpRm`/`e3Rm`, `Reach/ViolRemoveRun1.lean`), whose callback child is
discharged by `CallbackFrame` via `childOk_of_start`; 234 steps later the
token's `transfer` child is discharged by `childOk_of_childRun`; 188 steps
later F2 halts with `gasRm`/`outRm` (`rm_kernel`, `Reach/ViolRemoveRun2.lean`).
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
      some (((((e3Rm tS tA m w).withOrig O).withFork g), cc3Rm tS tA m w) := by
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

#exit

/-! ## The entered callback machine is `CallbackFrame`'s (field by field) -/

/-- Entered caller: the pool (free fork and original state are only stored, never
inspected, so the kernel decides them). -/
theorem e3g_caller : ∀ (g : Fork) (O : State) (tS : StorShadow) (tA : AcctShadow)
    (m : Meta) (w : World),
    (((((e3Rm tS tA m w).withOrig O).withFork g).sta)).caller = proxyAddr := by
  kernel_forall_rfl

theorem e3g_target : ∀ (g : Fork) (O : State) (tS : StorShadow) (tA : AcctShadow)
    (m : Meta) (w : World),
    (((((e3Rm tS tA m w).withOrig O).withFork g).sta)).target = some attackerAddr := by
  kernel_forall_rfl

theorem e3g_currentTarget : ∀ (g : Fork) (O : State) (tS : StorShadow) (tA : AcctShadow)
    (m : Meta) (w : World),
    (((((e3Rm tS tA m w).withOrig O).withFork g).sta)).currentTarget = attackerAddr := by
  kernel_forall_rfl

theorem e3g_gas : ∀ (g : Fork) (O : State) (tS : StorShadow) (tA : AcctShadow)
    (m : Meta) (w : World),
    (((((e3Rm tS tA m w).withOrig O).withFork g).sta)).gas = 907011 := by
  kernel_forall_rfl

theorem e3g_value : ∀ (g : Fork) (O : State) (tS : StorShadow) (tA : AcctShadow)
    (m : Meta) (w : World),
    (((((e3Rm tS tA m w).withOrig O).withFork g).sta)).value = 100 := by
  kernel_forall_rfl

theorem e3g_data : ∀ (g : Fork) (O : State) (tS : StorShadow) (tA : AcctShadow)
    (m : Meta) (w : World),
    (((((e3Rm tS tA m w).withOrig O).withFork g).sta)).data = [] := by
  kernel_forall_rfl

theorem e3g_codeAddress : ∀ (g : Fork) (O : State) (tS : StorShadow) (tA : AcctShadow)
    (m : Meta) (w : World),
    (((((e3Rm tS tA m w).withOrig O).withFork g).sta)).codeAddress = some attackerAddr := by
  kernel_forall_rfl

theorem e3g_code : ∀ (g : Fork) (O : State) (tS : StorShadow) (tA : AcctShadow)
    (m : Meta) (w : World),
    (((((e3Rm tS tA m w).withOrig O).withFork g).sta)).code = AttackerR.code := by
  kernel_forall_rfl

theorem e3g_depth : ∀ (g : Fork) (O : State) (tS : StorShadow) (tA : AcctShadow)
    (m : Meta) (w : World),
    (((((e3Rm tS tA m w).withOrig O).withFork g).sta)).depth = 1021 := by
  kernel_forall_rfl

theorem e3g_flags : ∀ (g : Fork) (O : State) (tS : StorShadow) (tA : AcctShadow)
    (m : Meta) (w : World),
    ((((((e3Rm tS tA m w).withOrig O).withFork g).sta)).shouldTransferValue = true ∧
      (((((e3Rm tS tA m w).withOrig O).withFork g).sta)).isStatic = false ∧
      (((((e3Rm tS tA m w).withOrig O).withFork g).sta)).disablePrecompiles = false) := by
  kernel_forall_rfl_and

theorem e3g_benvStat : ∀ (g : Fork) (O : State) (tS : StorShadow) (tA : AcctShadow)
    (m : Meta) (w : World),
    (((((e3Rm tS tA m w).withOrig O).withFork g).sta)).benvStat =
      ((((sCb.withOrig O).withFork g)).benvStat) := by
  kernel_forall_rfl

theorem e3g_tenvStat : ∀ (g : Fork) (O : State) (tS : StorShadow) (tA : AcctShadow)
    (m : Meta) (w : World),
    (((((e3Rm tS tA m w).withOrig O).withFork g).sta)).tenvStat =
      ((((sCb.withOrig O).withFork g)).tenvStat) := by
  kernel_forall_rfl

/-- The entered callback machine is `CallbackFrame`'s static machine. -/
theorem e3g_sta : ∀ (g : Fork) (O : State) (tS : StorShadow) (tA : AcctShadow)
    (m : Meta) (w : World),
    (((((e3Rm tS tA m w).withOrig O).withFork g).sta)) =
      ((((sCb.withOrig O).withFork g))) := by
  intro g O tS tA m w
  have hc := e3g_caller g O tS tA m w
  have ht := e3g_target g O tS tA m w
  have hct := e3g_currentTarget g O tS tA m w
  have hg := e3g_gas g O tS tA m w
  have hv := e3g_value g O tS tA m w
  have hd := e3g_data g O tS tA m w
  have hca := e3g_codeAddress g O tS tA m w
  have hco := e3g_code g O tS tA m w
  have hdep := e3g_depth g O tS tA m w
  obtain ⟨hstv, hst, hdp⟩ := e3g_flags g O tS tA m w
  have hbs := e3g_benvStat g O tS tA m w
  have hts := e3g_tenvStat g O tS tA m w
  cases h : (((((e3Rm tS tA m w).withOrig O).withFork g).sta)) with
  | mk c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 =>
    simp only [h] at hc ht hct hg hv hd hca hco hdep hstv hst hdp hbs hts
    subst hc ht hct hg hv hd hca hco hdep hstv hst hdp hbs hts
    rfl

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

/-! ## The `remove_liquidity` frame -/

#exit

/-- **P2, F2 (with F3 by `CallbackFrame` and the token's `transfer` child)**:
the `remove_liquidity` frame from its entry boundary `bRm0`. -/
theorem remove_frame (hCb : CallbackFrame) : RemoveFrame := by
  intro g O tS tA m w hg hRead hAgree
  -- The actual machine and entry.
  set S : Sevm := ((sRm.withOrig O).withFork g) with hSdef
  set entry : Cfg := Boundary.cfgOfT bRm0 tS tA m w with hentry
  -- The 339-step prefix at the actual machine.
  have hPre : wrun fsI S 339 entry = .cont (cRm339 tS tA m w) :=
    rmRun_at hg hRead (cRm339_eq tS tA m w) (fun h => Res.noConfusion h)
      (by simpa only [resKeys, cRm339_keys tS tA m w] using rm339_sub)
  have sPre := wrun_cont hPre
  have hag339 : Agree (cRm339 tS tA m w) := sPre.1 hAgree
  -- The callback child starts, spawns, and agrees.
  have hStart := csRm_at g O tS tA m w hg
  have hSpawn : SpawnedBy S (cRm339 tS tA m w).devm .call
      (((((e3Rm tS tA m w).withOrig O).withFork g)) :=
    spawnedBy_of_childStart hag339 hStart
  have hag3 : Agree (cc3Rm tS tA m w) := childStart_agree hag339 hStart
  have heq3 := Boundary.cfg_of_obsDT (cc3Rm_obs tS tA m w)
  have hagCb : Agree (Boundary.cfgOfT bCb0 tS tA (cc3Rm tS tA m w).devm.meta
      (cc3Rm tS tA m w).devm.world) := by
    rw [← heq3]; exact hag3
  obtain ⟨c1Cb, clCb, postCb, sCb12, hwrCb2, hgasCb, houtCb, herrCb, hkeysCb,
    hadrsCb, hstorCb, hacsCb, hreentry⟩ :=
    hCb g O tS tA _ _ hg hRead hagCb
  -- The entered machine is `CallbackFrame`'s.
  have he3sta := e3g_sta g O tS tA m w
  have hreentry3 : ReentryFacts (((((e3Rm tS tA m w).withOrig O).withFork g).sta)
      (cc3Rm tS tA m w) := by
    rw [← he3sta, ← heq3]; exact hreentry
  -- The callback child, as `ChildOk`/`ChildAgree`.
  have hcbObs : childObs gasCb [] postCb = postCb :=
    childObs_eq hgasCb houtCb herrCb
  have hkCb : ChildOk S (cRm339 tS tA m w) postCb ∧
      ChildAgree postCb clCb.keys clCb.adrs clCb.stor clCb.acs := by
    have hstep : StepOk fsA (((((e3Rm tS tA m w).withOrig O).withFork g).sta)
        (cc3Rm tS tA m w) c1Cb := by
      rw [← he3sta, ← heq3]; exact sCb12
    have hrun : wrun fsA (((((e3Rm tS tA m w).withOrig O).withFork g).sta) 2 c1Cb =
        .done (.halted postCb) clCb := by
      rw [← he3sta, ← heq3]; exact hwrCb2
    exact childOk_of_start
      (fun hcode hfork hrun => lift_exact AttackerR.cert_check AttackerR_jumpsOk
        hcode hfork hrun)
      hag339 fsA_zero hStart (by rw [he3sta]; exact hg)
      (by rw [he3sta]; rfl) hstep hrun herrCb
  -- The staged kernel run, destructured (prefix, callback resume, 234 steps,
  -- token child, token resume, 188 steps to the halt).
  have hk := rm_kernel tS tA m w postCb
  rw [hcbObs] at hk
  unfold runRm runRmFrom at hk
  split at hk
  · rename_i c1A h1A
    have hc1A : cRm339 tS tA m w = c1A := by unfold cRm339; rw [h1A]
    subst hc1A
    split at hk
    · rename_i c2A h2A
      split at hk
      · rename_i c3A h3A
        split at hk
        · rename_i d2A cl2A hcA
          split at hk
          · rename_i c4A h4A
            generalize hrA : wrun fsI sRm 188 c4A = rA at hk
            rcases rA with c | ⟨post | post, cl⟩ | _
            · simp only [obsRm, obsRmEELS, reduceCtorEq] at hk
            · simp only [obsRm, obsRmEELS, Option.some.injEq, Prod.mk.injEq,
                Bool.and_eq_true, decide_eq_true_eq,
                Option.isNone_iff_eq_none] at hk
              obtain ⟨hgRm, houtRm, _h26, _hA, _h2, heRm⟩ := hk
              -- The whole run recomposed (for the halt-shadow pins).
              have hRunA : runRm tS tA m w postCb = .done (.halted post) cl := by
                simp only [runRm, runRmFrom, Boundary.callPairFrom, hcbObs,
                  cRm339_eq tS tA m w, h2A, h3A, hcA, h4A, hrA]
              have hHB := rmHalt_keys tS tA m w postCb
              rw [hcbObs, hRunA] at hHB
              simp only [rmHaltKeys, Option.some.injEq, Prod.mk.injEq] at hHB
              obtain ⟨hkeysRm, hadrsRm, hstorRmTake, hacsRmKeys⟩ := hHB
              have hHC := rmHalt_rest tS tA m w postCb
              rw [hcbObs, hRunA] at hHC
              simp only [rmHaltRest, Prod.mk.injEq] at hHC
              obtain ⟨hcrRm, hstRm, hatRm⟩ := hHC
              have hstorRm : cl.stor = storRm ++ tS := by
                rw [← List.take_append_drop storRm.length cl.stor, hstorRmTake, hstRm]
              have hacsRm : cl.acs = acsRm ++ tA := by
                rw [← List.take_append_drop acsRm.length cl.acs, hatRm]
                congr 1
                exact Boundary.acs_eq_of_views hacsRmKeys
                  (hcrRm.trans (Boundary.restsOf_eq acsRm))
              -- Transported stages at the actual machine.
              have hR1 : callResume S (cRm339 tS tA m w) postCb keysCb adrsCb
                  (storCb ++ tS) (acsCb ++ tA) = some c2A := by
                rw [callResume_withFork CoveredFork.prague hg, callResume_withOrig]
                exact h2A
              have aCb' : ChildAgree postCb keysCb adrsCb (storCb ++ tS)
                  (acsCb ++ tA) := by
                rw [hkeysCb, hadrsCb, hstorCb, hacsCb]; exact hkCb.2
              have sRes1 : StepOk fsI S (cRm339 tS tA m w) c2A :=
                callResume_cont hR1 hkCb.1 aCb'
              have midSub : ∀ x ∈ ([(proxyAddr, (7 : Nat).toB256),
                  (proxyAddr, (8 : Nat).toB256), (proxyAddr, (26 : Nat).toB256),
                  (proxyAddr, (2 : Nat).toB256)] ++ keysCb), x ∈ readKeys := by
                decide
              have hcTok3 : cTokRm tS tA m w postCb = c3A := by
                simp only [cTokRm, Boundary.callPairA, hcbObs, h2A, h3A]
              have hMid : wrun fsI S 234 c2A = .cont c3A :=
                rmRun_at hg hRead h3A (fun h => Res.noConfusion h) (by
                  intro x hx
                  simp only [resKeys] at hx
                  rw [← hcTok3, cTokRm_keys tS tA m w postCb] at hx
                  exact midSub x hx)
              have sMid := wrun_cont hMid
              have hag3a : Agree c3A := ((sPre.trans sRes1).trans sMid).1 hAgree
              -- Token child at the actual machine.
              have htokSub : ∀ x ∈ ([(tokenAddr, attackerAddr.toB256),
                  (tokenAddr, proxyAddr.toB256), (proxyAddr, (7 : Nat).toB256),
                  (proxyAddr, (8 : Nat).toB256), (proxyAddr, (26 : Nat).toB256),
                  (proxyAddr, (2 : Nat).toB256)] ++ keysCb), x ∈ readKeys := by
                decide
              have htokKeys : resKeys (childRun Token20.prog Token20.code sRm 200
                  c3A) = [(tokenAddr, attackerAddr.toB256),
                    (tokenAddr, proxyAddr.toB256), (proxyAddr, (7 : Nat).toB256),
                    (proxyAddr, (8 : Nat).toB256), (proxyAddr, (26 : Nat).toB256),
                    (proxyAddr, (2 : Nat).toB256)] ++ keysCb := by
                rw [← hcTok3]; exact tokResRm_keys tS tA m w postCb
              have htokKeys2 : cl2A.keys =
                  [(tokenAddr, attackerAddr.toB256), (tokenAddr, proxyAddr.toB256),
                    (proxyAddr, (7 : Nat).toB256), (proxyAddr, (8 : Nat).toB256),
                    (proxyAddr, (26 : Nat).toB256), (proxyAddr, (2 : Nat).toB256)] ++
                    keysCb := by
                rw [hcA] at htokKeys
                simpa only [resKeys] using htokKeys
              have htokNe : childRun Token20.prog Token20.code
                  ((sRm.withOrig O).withOrig O0) 200 c3A ≠ .stuck := by
                rw [sRm_withOrig_O0, hcA]
                exact fun h => Res.noConfusion h
              have htokAgree : OrigAgreeOn O0 O (resKeys (childRun Token20.prog
                  Token20.code ((sRm.withOrig O).withOrig O0) 200 c3A)) :=
                origAgreeOn_O0 hRead (by
                  rw [sRm_withOrig_O0, hcA]
                  simp only [resKeys]
                  rw [htokKeys2]
                  exact fun x hx => htokSub x hx)
              have hTok : childRun Token20.prog Token20.code S 200 c3A =
                  .done (.halted d2A) cl2A := by
                have eOrig := childRun_withOrig_keys (s := sRm.withOrig O) (O := O0)
                  Token20.prog Token20.code 200 c3A htokNe htokAgree
                rw [sRm_withOrig_O0, hcA] at eOrig
                have eFork := childRun_withFork (s := sRm.withOrig O)
                  CoveredFork.prague hg rfl Token20.prog Token20.code 200 c3A
                rw [eOrig] at eFork
                exact eFork
              obtain ⟨kTok, aTok⟩ := childOk_of_childRun
                (fun hcode hfork hrun => lift_exact Token20.cert_check
                  Token20.cert_jumpsOk hcode hfork hrun)
                hag3a hTok (callResume_error h4A)
              have hR2 : callResume S c3A d2A cl2A.keys cl2A.adrs cl2A.stor
                  cl2A.acs = some c4A := by
                rw [callResume_withFork CoveredFork.prague hg, callResume_withOrig]
                exact h4A
              have sRes2 : StepOk fsI S c3A c4A := callResume_cont hR2 kTok aTok
              have hrEnd : wrun fsI S 188 c4A = .done (.halted post) cl :=
                rmRun_at hg hRead hrA (fun h => Res.noConfusion h) (by
                  intro x hx
                  simp only [resKeys] at hx
                  rw [hkeysRm] at hx
                  exact keys_sub_readKeys.2.2.1 x hx)
              -- The full `Exec` and its shadows.
              have sFull := ((sPre.trans sRes1).trans sMid).trans sRes2
              have hag4 : Agree c4A := sFull.1 hAgree
              obtain ⟨runE, _hclE, _hstE⟩ := wrun_done hrEnd hag4
              have hrunE : SProg.RunExact (Cert.prog cert) S
                  (Boundary.cfgOfT bRm0 tS tA m w).devm post :=
                ⟨t_0000_c0, fsI_zero, sFull.2 _ hAgree runE⟩
              have hxExec : Nonempty (Exec 0 S (Boundary.cfgOfT bRm0 tS tA m w).devm
                  (.ok post)) :=
                lift_exactM cert_checkM cert_jumpsOkM rfl hg hrunE
              have hca : ChildAgree post keysRm adrsRm (storRm ++ tS)
                  (acsRm ++ tA) := by
                have hca0 : ChildAgree post cl.keys cl.adrs cl.stor cl.acs :=
                  childAgree_of_halt hrEnd hag4
                rw [hkeysRm, hadrsRm, hstorRm, hacsRm] at hca0
                exact hca0
              have houtRm' : post.output = outRm :=
                List.map_injective_iff.mpr (fun _ _ h => UInt8.toNat_inj.mp h) houtRm
              -- The `RemoveFacts` witnesses.
              have hs2 : storOf (cRm339 tS tA m w).devm.state proxyAddr 2 = 1 := by
                have h := hag339.2.2.1 proxyAddr 2
                rw [rm339_stor2 tS tA m w] at h
                exact h
              have hs26 : storOf (cRm339 tS tA m w).devm.state proxyAddr 26 = 2000 := by
                have h := hag339.2.2.1 proxyAddr 26
                rw [rm339_stor26 tS tA m w] at h
                exact h
              have htgt : (((((e3Rm tS tA m w).withOrig O).withFork g).sta)).currentTarget =
                  attackerAddr := by
                rw [he3sta]; rfl
              have hcode : (((((e3Rm tS tA m w).withOrig O).withFork g).sta)).code =
                  AttackerR.code := by
                rw [he3sta]; rfl
              have hval : (((((e3Rm tS tA m w).withOrig O).withFork g).sta)).value = 100 := by
                rw [he3sta]; rfl
              have hpost26 : storOf post.state proxyAddr 26 = 1800 := by
                have h := hca.2.2.1 proxyAddr 26
                rw [rmPost26 tS] at h
                exact h
              have hpostLP : storOf post.state proxyAddr lpSlotA = 1906 := by
                have h := hca.2.2.1 proxyAddr lpSlotA
                rw [rmPostLP tS] at h
                exact h
              have hpost2 : storOf post.state proxyAddr 2 = 0 := by
                have h := hca.2.2.1 proxyAddr 2
                rw [rmPost2 tS] at h
                exact h
              exact ⟨post, hxExec, hgRm, houtRm', heRm, hca, boundary_values.1,
                (cRm339 tS tA m w), (((((e3Rm tS tA m w).withOrig O).withFork g)),
                (cc3Rm tS tA m w), hPre, hag339, hs2, hs26, hSpawn, htgt, hcode,
                hval, rfl, rfl, rfl, hag3, hreentry3, hpost26, hpostLP, hpost2⟩
            · simp only [obsRm, obsRmEELS, reduceCtorEq] at hk
            · simp only [obsRm, obsRmEELS, reduceCtorEq] at hk
          · simp only [obsRm, obsRmEELS, reduceCtorEq] at hk
        · simp only [obsRm, obsRmEELS, reduceCtorEq] at hk
      · simp only [obsRm, obsRmEELS, reduceCtorEq] at hk
    · simp only [obsRm, obsRmEELS, reduceCtorEq] at hk
  · simp only [obsRm, obsRmEELS, reduceCtorEq] at hk

end Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Reach.Viol
