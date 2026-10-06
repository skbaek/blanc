import Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Reach.ViolBoundary

/-!
# V− P2, F0/F1 kernel run: the root frame and its forwarder child

Kernel facts over `(sR.withOrig O)` (Prague fork) with a free original state `O` and
free shadow tails: the root `AttackerR` frame from its entry boundary `bR0` runs
33 steps to its `CALL` of the clone (`cR`, empty keys/addresses); the `CALL`
spawns the forwarder (`cpR`, `e1`); the forwarder runs 11 steps to its
`DELEGATECALL` (`e1'11`), whose spawn (`cpF2`, adrs `[implAddr, proxyAddr]`)
enters the implementation frame (`e2`, start configuration `c2`, decided against
`bRm0`); the forwarder resumed from F2's settled machine halts with
`gasFwd`/`outRm`; and the root resumed from the forwarder halts with `gasV` and
the `keysV`/`adrsV`/`storV`/`acsV` shadows.

Neither the certificate runs nor the forwarder's EVM steps read the original
state (no `SSTORE` anywhere in F0/F1), so the kernel evaluates them with `O`
free: each fact is a `kernel_forall_rfl` decision, and a read of `O` (or of a
tail) would leave the run stuck and fail the fact. The observations
additionally pin the runs to the frozen literals. Fork transport to every
covered fork, and the composition into `RootFrame`, live in
`Reach/ViolRoot.lean`.
-/

namespace Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Reach.Viol

open Jaune Blanc.Lift Blanc.Lift.Witness Blanc.Lift.NodeWalk Blanc.ConcreteRun
open Blanc.Lift.VyperNonreentrantDeployed

/-! ## F0 to its `CALL` -/

/-- F0 at its `CALL` of the clone: the configuration after 33 steps. -/
def cR (O : State) (tS : StorShadow) (tA : AcctShadow) (m : Meta) (w : World) : Cfg :=
  match wrun fsA (sR.withOrig O) 33 (Boundary.cfgOfT bR0 tS tA m w) with
  | .cont c => c
  | _ => Boundary.cfgOfT bR0 tS tA m w

theorem cR_eq : ∀ (O : State) (tS : StorShadow) (tA : AcctShadow) (m : Meta) (w : World),
    wrun fsA (sR.withOrig O) 33 (Boundary.cfgOfT bR0 tS tA m w) =
      .cont (cR O tS tA m w) := by
  kernel_forall_rfl

/-- F0 records no keys or addresses reaching its `CALL`. -/
theorem cR_keys : ∀ (O : State) (tS : StorShadow) (tA : AcctShadow) (m : Meta) (w : World),
    (cR O tS tA m w).keys = [] := by
  kernel_forall_rfl

theorem cR_adrs : ∀ (O : State) (tS : StorShadow) (tA : AcctShadow) (m : Meta) (w : World),
    (cR O tS tA m w).adrs = [] := by
  kernel_forall_rfl

/-- F0's `CALL` up to its spawn. -/
def cpR (O : State) (tS : StorShadow) (tA : AcctShadow) (m : Meta) (w : World) : CallPrep :=
  (callPrep (sR.withOrig O) (cR O tS tA m w)).getD noPrepI

theorem cpR_eq : ∀ (O : State) (tS : StorShadow) (tA : AcctShadow) (m : Meta) (w : World),
    callPrep (sR.withOrig O) (cR O tS tA m w) = some (cpR O tS tA m w) := by
  kernel_forall_rfl

/-- F1's account shadow at entry: the root `CALL`'s value transfer applied. -/
def acs1R (O : State) (tS : StorShadow) (tA : AcctShadow) (m : Meta) (w : World) : AcctShadow :=
  acsTransfer (cpR O tS tA m w).f.inner (cR O tS tA m w).acs

/-- F0's `CALL` prep enters no fork-sensitive precompile. -/
theorem cpR_forkfree : ∀ (g : Fork) (O : State) (tS : StorShadow) (tA : AcctShadow)
    (m : Meta) (w : World),
    frameEntryForkFree ((((cpR O tS tA m w).withFork g).f)) = true := by
  kernel_forall_rfl

/-- Pushing a fork through F0's `CALL` preparation preserves its addresses. -/
theorem cpR_adrs_fork : ∀ (g : Fork) (O : State) (tS : StorShadow) (tA : AcctShadow)
    (m : Meta) (w : World),
    ((((cpR O tS tA m w).withFork g).adrs)) =
      (((cpR O tS tA m w).adrs)) := by
  kernel_forall_rfl

/-! ## F1 to its `DELEGATECALL`, and F2's entry -/

/-- The forwarder frame F1 as spawned by F0's `CALL`. -/
def e1 (O : State) (tS : StorShadow) (tA : AcctShadow) (m : Meta) (w : World) : Evm :=
  match frameEnterS (cpR O tS tA m w).f (acs1R O tS tA m w) with
  | .run e => e
  | .done _ => default

theorem e1_eq : ∀ (O : State) (tS : StorShadow) (tA : AcctShadow) (m : Meta) (w : World),
    frameEnterS (cpR O tS tA m w).f (cR O tS tA m w).acs = .run (e1 O tS tA m w) := by
  kernel_forall_rfl

theorem e1_facts : ∀ (O : State) (tS : StorShadow) (tA : AcctShadow) (m : Meta) (w : World),
    ((e1 O tS tA m w).sta.caller = attackerAddr ∧
      (e1 O tS tA m w).sta.currentTarget = proxyAddr ∧
      (e1 O tS tA m w).sta.code = fwdCode ∧
      (e1 O tS tA m w).pc = 0) := by
  kernel_forall_rfl_and

/-- The forwarder at its `DELEGATECALL` (pc 31). -/
def e1'11 (O : State) (tS : StorShadow) (tA : AcctShadow) (m : Meta) (w : World) : Evm :=
  (stepN 11 (e1 O tS tA m w)).getD default

theorem e1'11_eq : ∀ (O : State) (tS : StorShadow) (tA : AcctShadow) (m : Meta) (w : World),
    stepN 11 (e1 O tS tA m w) = some (e1'11 O tS tA m w) := by
  kernel_forall_rfl

/-- F1's `DELEGATECALL` up to its spawn. -/
def cpF2 (O : State) (tS : StorShadow) (tA : AcctShadow) (m : Meta) (w : World) : CallPrep :=
  (dcallPrep (e1'11 O tS tA m w).sta (e1'11 O tS tA m w).dyna (cpR O tS tA m w).adrs
    (acs1R O tS tA m w)).getD noPrepI

theorem cpF2_eq : ∀ (O : State) (tS : StorShadow) (tA : AcctShadow) (m : Meta) (w : World),
    dcallPrep (e1'11 O tS tA m w).sta (e1'11 O tS tA m w).dyna (cpR O tS tA m w).adrs
      (acs1R O tS tA m w) = some (cpF2 O tS tA m w) := by
  kernel_forall_rfl

theorem cpF2_adrs : ∀ (O : State) (tS : StorShadow) (tA : AcctShadow) (m : Meta) (w : World),
    decide ((cpF2 O tS tA m w).adrs = [implAddr, proxyAddr]) = true := by
  kernel_forall_rfl

/-- Pushing a fork through F1's `DELEGATECALL` preparation preserves its shape. -/
theorem cpF2_p_fork : ∀ (g : Fork) (O : State) (tS : StorShadow)
    (tA : AcctShadow) (m : Meta) (w : World),
    ((((cpF2 O tS tA m w).withFork g).p)) =
      (((cpF2 O tS tA m w).p)) := by
  kernel_forall_rfl

theorem cpF2_oi_fork : ∀ (g : Fork) (O : State) (tS : StorShadow)
    (tA : AcctShadow) (m : Meta) (w : World),
    ((((cpF2 O tS tA m w).withFork g).oi)) =
      (((cpF2 O tS tA m w).oi)) := by
  kernel_forall_rfl

theorem cpF2_os_fork : ∀ (g : Fork) (O : State) (tS : StorShadow)
    (tA : AcctShadow) (m : Meta) (w : World),
    ((((cpF2 O tS tA m w).withFork g).os)) =
      (((cpF2 O tS tA m w).os)) := by
  kernel_forall_rfl

/-- The implementation frame F2 as spawned by F1's `DELEGATECALL`. -/
def e2 (O : State) (tS : StorShadow) (tA : AcctShadow) (m : Meta) (w : World) : Evm :=
  match frameEnterS (cpF2 O tS tA m w).f (acs1R O tS tA m w) with
  | .run e => e
  | .done _ => default

theorem e2_eq : ∀ (O : State) (tS : StorShadow) (tA : AcctShadow) (m : Meta) (w : World),
    frameEnterS (cpF2 O tS tA m w).f (acs1R O tS tA m w) = .run (e2 O tS tA m w) := by
  kernel_forall_rfl

theorem e2_facts : ∀ (O : State) (tS : StorShadow) (tA : AcctShadow) (m : Meta) (w : World),
    ((e2 O tS tA m w).sta.currentTarget = proxyAddr ∧
      (e2 O tS tA m w).sta.code = Vulnerable.code ∧
      (e2 O tS tA m w).sta.data = removeCallR ∧
      (e2 O tS tA m w).pc = 0) := by
  kernel_forall_rfl_and

/-- Pushing a fork through entered F2 lands in its state. -/
theorem e2_sta_fork : ∀ (g : Fork) (O : State) (tS : StorShadow) (tA : AcctShadow)
    (m : Meta) (w : World),
    ((((e2 O tS tA m w).withFork g).sta)) =
      (((e2 O tS tA m w).sta.withFork g)) := by
  kernel_forall_rfl

/-- A `DELEGATECALL` preparation's frame carries the caller's transaction environment. -/
theorem dcallPrep_tenvStat {s : Sevm} {d : Devm} {adrs : List Adr} {acs : AcctShadow} {cp : CallPrep}
    (h : dcallPrep s d adrs acs = some cp) :
    cp.f.outer.tenv.stat = s.tenvStat ∧ cp.f.inner.tenv.stat = s.tenvStat := by
  unfold dcallPrep at h
  generalize d.stack = st at h
  match st, h with
  | _ :: _ :: _ :: _ :: _ :: _ :: _, h =>
    simp only at h
    split at h
    · split at h
      · simp only [reduceCtorEq] at h
      · split at h
        · simp only [Option.some.injEq] at h
          subst h
          exact ⟨rfl, rfl⟩
        · simp only [reduceCtorEq] at h
    · simp only [reduceCtorEq] at h

/-- A `CALL` preparation's frame carries the caller's transaction environment. -/
theorem callPrep_tenvStat {s : Sevm} {c : Cfg} {cp : CallPrep} (h : callPrep s c = some cp) :
    cp.f.outer.tenv.stat = s.tenvStat ∧ cp.f.inner.tenv.stat = s.tenvStat := by
  unfold callPrep at h
  generalize c.devm.stack = st at h
  match st, h with
  | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _, h =>
    simp only at h
    split at h
    · split at h
      · simp only [reduceCtorEq] at h
      · split at h
        · split at h
          · simp only [Option.some.injEq] at h
            subst h
            exact ⟨rfl, rfl⟩
          · simp only [reduceCtorEq] at h
        · split at h
          · simp only [Option.some.injEq] at h
            subst h
            exact ⟨rfl, rfl⟩
          · simp only [reduceCtorEq] at h
    · simp only [reduceCtorEq] at h

/-- An entered machine carries its frame's transaction environment. -/
theorem frameEnterS_tenvStat {f : Frame} {acs : AcctShadow} {e : Evm}
    (h : frameEnterS f acs = .run e) : e.sta.tenvStat = f.inner.tenv.stat := by
  obtain ⟨benv, hb, he⟩ := frameEnterS_run h
  rw [he]
  rfl

/-- F2's entered static machine is the frozen one, at the actual original state. -/
theorem e2_sta_caller : ∀ (O : State) (tS : StorShadow) (tA : AcctShadow) (m : Meta)
    (w : World), (e2 O tS tA m w).sta.caller = (sRm.withOrig O).caller := by
  kernel_forall_rfl

theorem e2_sta_target : ∀ (O : State) (tS : StorShadow) (tA : AcctShadow) (m : Meta)
    (w : World), (e2 O tS tA m w).sta.target = (sRm.withOrig O).target := by
  kernel_forall_rfl

theorem e2_sta_gas : ∀ (O : State) (tS : StorShadow) (tA : AcctShadow) (m : Meta)
    (w : World), decide ((e2 O tS tA m w).sta.gas = (sRm.withOrig O).gas) = true := by
  kernel_forall_rfl

theorem e2_sta_value : ∀ (O : State) (tS : StorShadow) (tA : AcctShadow) (m : Meta)
    (w : World), (e2 O tS tA m w).sta.value = (sRm.withOrig O).value := by
  kernel_forall_rfl

theorem e2_sta_codeAddress : ∀ (O : State) (tS : StorShadow) (tA : AcctShadow) (m : Meta)
    (w : World), decide ((e2 O tS tA m w).sta.codeAddress = (sRm.withOrig O).codeAddress) = true := by
  kernel_forall_rfl

theorem e2_sta_depth : ∀ (O : State) (tS : StorShadow) (tA : AcctShadow) (m : Meta)
    (w : World), (e2 O tS tA m w).sta.depth = (sRm.withOrig O).depth := by
  kernel_forall_rfl

theorem e2_sta_flags : ∀ (O : State) (tS : StorShadow) (tA : AcctShadow) (m : Meta)
    (w : World), ((e2 O tS tA m w).sta.shouldTransferValue = (sRm.withOrig O).shouldTransferValue ∧
      (e2 O tS tA m w).sta.isStatic = (sRm.withOrig O).isStatic ∧
      (e2 O tS tA m w).sta.disablePrecompiles = (sRm.withOrig O).disablePrecompiles) := by
  kernel_forall_rfl_and

theorem sR_benv : sR.benvStat = violStat := rfl

theorem sRm_benv : sRm.benvStat = violStat := rfl

theorem sR_tenv : sR.tenvStat = rootTenv.stat := rfl

theorem sRm_tenv : sRm.tenvStat = rootTenv.stat := rfl

/-- F2's entered block environment, by the spec-lemma chain (no kernel eval). -/
theorem e2_sta_benvStat : ∀ (O : State) (tS : StorShadow) (tA : AcctShadow) (m : Meta)
    (w : World), (e2 O tS tA m w).sta.benvStat = (sRm.withOrig O).benvStat := by
  intro O tS tA m w
  rw [frameEnterS_stat (e2_eq O tS tA m w),
    (dcallPrep_stat (cpF2_eq O tS tA m w)).2,
    stepN_sta (e1'11_eq O tS tA m w),
    frameEnterS_stat (e1_eq O tS tA m w),
    (callPrep_stat (cpR_eq O tS tA m w)).2]
  simp only [Sevm.withOrig, sR_benv, sRm_benv]

/-- F2's entered transaction environment, by the spec-lemma chain (no kernel eval). -/
theorem e2_sta_tenv : ∀ (O : State) (tS : StorShadow) (tA : AcctShadow) (m : Meta)
    (w : World), (e2 O tS tA m w).sta.tenvStat = (sRm.withOrig O).tenvStat := by
  intro O tS tA m w
  rw [frameEnterS_tenvStat (e2_eq O tS tA m w),
    (dcallPrep_tenvStat (cpF2_eq O tS tA m w)).2,
    stepN_sta (e1'11_eq O tS tA m w),
    frameEnterS_tenvStat (e1_eq O tS tA m w),
    (callPrep_tenvStat (cpR_eq O tS tA m w)).2]
  simp only [Sevm.withOrig, sR_tenv, sRm_tenv]

theorem e2_sta_eq : ∀ (O : State) (tS : StorShadow) (tA : AcctShadow) (m : Meta)
    (w : World), (e2 O tS tA m w).sta = sRm.withOrig O := by
  intro O tS tA m w
  have hc := e2_sta_caller O tS tA m w
  have ht := e2_sta_target O tS tA m w
  have hct := (e2_facts O tS tA m w).1
  have hg := of_decide_eq_true (e2_sta_gas O tS tA m w)
  have hv := e2_sta_value O tS tA m w
  have hd := (e2_facts O tS tA m w).2.2.1
  have hca := of_decide_eq_true (e2_sta_codeAddress O tS tA m w)
  have hco := (e2_facts O tS tA m w).2.1
  have hdep := e2_sta_depth O tS tA m w
  obtain ⟨hstv, hst, hdp⟩ := e2_sta_flags O tS tA m w
  have hbs := e2_sta_benvStat O tS tA m w
  have hts := e2_sta_tenv O tS tA m w
  have hct' : (e2 O tS tA m w).sta.currentTarget = (sRm.withOrig O).currentTarget := by
    rw [hct]; rfl
  have hd' : (e2 O tS tA m w).sta.data = (sRm.withOrig O).data := by
    rw [hd]; rfl
  have hco' : (e2 O tS tA m w).sta.code = (sRm.withOrig O).code := by
    rw [hco]; rfl
  cases h : (e2 O tS tA m w).sta with
  | mk c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 =>
    simp only [h] at hc ht hct' hg hv hd' hca hco' hdep hstv hst hdp hbs hts
    subst hc ht hct' hg hv hd' hca hco' hdep hstv hst hdp hbs hts
    rfl

/-- F2's start configuration (the probe's convention). -/
def c2 (O : State) (tS : StorShadow) (tA : AcctShadow) (m : Meta) (w : World) : Cfg :=
  ⟨(e2 O tS tA m w).dyna, Vulnerable.t_0000_c0, [], (cR O tS tA m w).keys,
    (cpF2 O tS tA m w).adrs, (cR O tS tA m w).stor,
    acsTransfer (cpF2 O tS tA m w).f.inner (acs1R O tS tA m w)⟩

/-- F2's start configuration is the entry boundary `bRm0` with the same tails. -/
theorem c2_obs : ∀ (O : State) (tS : StorShadow) (tA : AcctShadow) (m : Meta) (w : World),
    Boundary.obsDT bRm0 (.cont (c2 O tS tA m w)) = Boundary.obsDOkT bRm0 tS tA := by
  kernel_forall_rfl

/-! ## F1 resumed from F2, as data -/

/-- F2's settled machine as F1's child, its observed parts as literals. -/
abbrev obsChildF1 (d : Devm) : Devm := childObs gasFwd outRm d

/-- The forwarder resumed from a settled F2 `post2`. -/
def d1R (O : State) (tS : StorShadow) (tA : AcctShadow) (m : Meta) (w : World)
    (post2 : Devm) : Devm :=
  (resumeCallB (cpF2 O tS tA m w).p (cpF2 O tS tA m w).oi (cpF2 O tS tA m w).os
    (.ok (obsChildF1 post2))).getD default

theorem resumeF1_eq : ∀ (O : State) (tS : StorShadow) (tA : AcctShadow) (m : Meta)
    (w : World) (post2 : Devm),
    resumeCallB (cpF2 O tS tA m w).p (cpF2 O tS tA m w).oi (cpF2 O tS tA m w).os
      (.ok (obsChildF1 post2)) = some (d1R O tS tA m w post2) := by
  kernel_forall_rfl

/-- The forwarder ten steps past F2's return. -/
def e1tail (O : State) (tS : StorShadow) (tA : AcctShadow) (m : Meta) (w : World)
    (post2 : Devm) : Evm :=
  (stepN 10 ⟨32, (e1 O tS tA m w).sta, d1R O tS tA m w post2⟩).getD default

theorem tailF1_eq : ∀ (O : State) (tS : StorShadow) (tA : AcctShadow) (m : Meta)
    (w : World) (post2 : Devm),
    stepN 10 ⟨32, (e1 O tS tA m w).sta, d1R O tS tA m w post2⟩ =
      some (e1tail O tS tA m w post2) := by
  kernel_forall_rfl

/-- The forwarder's halted machine. -/
def postF1 (O : State) (tS : StorShadow) (tA : AcctShadow) (m : Meta) (w : World)
    (post2 : Devm) : Devm :=
  match Evm.step (e1tail O tS tA m w post2) with
  | .halt (.ok d') => d'
  | _ => default

theorem returnF1_eq : ∀ (O : State) (tS : StorShadow) (tA : AcctShadow) (m : Meta)
    (w : World) (post2 : Devm),
    Evm.step (e1tail O tS tA m w post2) =
      .halt (.ok (postF1 O tS tA m w post2)) := by
  kernel_forall_rfl

theorem postF1_obs : ∀ (O : State) (tS : StorShadow) (tA : AcctShadow) (m : Meta)
    (w : World) (post2 : Devm),
    ((postF1 O tS tA m w post2).output.map UInt8.toNat,
      (postF1 O tS tA m w post2).error.isNone) =
    (outRm.map UInt8.toNat, true) := by
  kernel_forall_rfl

theorem postF1_keep : ∀ (O : State) (tS : StorShadow) (tA : AcctShadow) (m : Meta)
    (w : World) (post2 : Devm),
    ((postF1 O tS tA m w post2).accessedAddresses,
      (postF1 O tS tA m w post2).accessedStorageKeys,
      (postF1 O tS tA m w post2).state) =
    ((d1R O tS tA m w post2).accessedAddresses,
      (d1R O tS tA m w post2).accessedStorageKeys,
      (d1R O tS tA m w post2).state) := by
  kernel_forall_rfl

/-! ## F0's resume devm, as data -/

/-- The root devm resumed from F1's settled machine `post2`. -/
def dResumeR (O : State) (tS : StorShadow) (tA : AcctShadow) (m : Meta) (w : World)
    (post2 : Devm) : Devm :=
  (resumeCallB (cpR O tS tA m w).p (cpR O tS tA m w).oi (cpR O tS tA m w).os
    (.ok (obsChildF1 post2))).getD (postF1 O tS tA m w post2)

theorem resumeVR_eq : ∀ (O : State) (tS : StorShadow) (tA : AcctShadow) (m : Meta)
    (w : World) (post2 : Devm),
    resumeCallB (cpR O tS tA m w).p (cpR O tS tA m w).oi (cpR O tS tA m w).os
      (.ok (obsChildF1 post2)) = some (dResumeR O tS tA m w post2) := by
  kernel_forall_rfl

/-! ## Root entry statics -/

theorem sR_fork : sR.benvStat.fork = .prague ∧ sR.benvStat.excessBlobGas = 0 := by
  decide +kernel

/-- The transported root static machine keeps its caller, target and code. -/
theorem sRw_caller : ∀ (W : State) (g : Fork),
    (((sR.withOrig W).withFork g).caller) = creator := by
  kernel_forall_rfl

theorem sRw_target : ∀ (W : State) (g : Fork),
    (((sR.withOrig W).withFork g).currentTarget) = attackerAddr := by
  kernel_forall_rfl

theorem sRw_code : ∀ (W : State) (g : Fork),
    (((sR.withOrig W).withFork g).code) = AttackerR.code := by
  kernel_forall_rfl

/-- The violating message at any fork is the Prague message pushed through. -/
theorem violMsg_withFork : ∀ (g : Fork) (W : State),
    violMsg g W = (violMsg .prague W).withFork g := by
  intro g W
  simp only [violMsg, callMsg, rootBenv, Msg.withFork, Benv.withFork,
    BenvStat.withFork]

/-! ## F0/F1 block facts, from the prep specs -/

/-- The root static machine's fork tag survives `withOrig`. -/
theorem sR_orig_fork : ∀ O : State, (sR.withOrig O).benvStat.fork = .prague := by
  intro O
  simp only [Sevm.withOrig, BenvStat.withOrig]
  exact sR_fork.1

/-- The root static machine's blob-gas exemption survives `withOrig`. -/
theorem sR_orig_hx : ∀ O : State, (sR.withOrig O).benvStat.excessBlobGas = 0 := by
  intro O
  simp only [Sevm.withOrig, BenvStat.withOrig]
  exact sR_fork.2

/-- F1's entry block facts, from the prep specs. -/
theorem e1_fork : ∀ (O : State) (tS : StorShadow) (tA : AcctShadow) (m : Meta)
    (w : World), (e1 O tS tA m w).sta.benvStat.fork = .prague ∧
      (e1 O tS tA m w).sta.benvStat.excessBlobGas = 0 := by
  intro O tS tA m w
  have hst := callPrep_stat (cpR_eq O tS tA m w)
  have he := frameEnterS_stat (e1_eq O tS tA m w)
  rw [he, hst.2]
  exact ⟨sR_orig_fork O, sR_orig_hx O⟩

/-- F0's `CALL` targets the proxy, as a kernel decision. -/
theorem cpR_codeAddr' : ∀ (O : State) (tS : StorShadow) (tA : AcctShadow) (m : Meta)
    (w : World),
    decide ((cpR O tS tA m w).f.inner.codeAddress = some proxyAddr) = true := by
  kernel_forall_rfl

/-- F0's `CALL` targets the proxy. -/
theorem cpR_codeAddr : ∀ (O : State) (tS : StorShadow) (tA : AcctShadow) (m : Meta)
    (w : World), (cpR O tS tA m w).f.inner.codeAddress = some proxyAddr :=
  fun O tS tA m w => of_decide_eq_true (cpR_codeAddr' O tS tA m w)

/-- F0's `CALL` prep enters no fork-sensitive precompile. -/
theorem cpR_neutral : ∀ (O : State) (tS : StorShadow) (tA : AcctShadow) (m : Meta)
    (w : World), (cpR O tS tA m w).f.PrecompNeutral :=
  fun O tS tA m w =>
    Frame.precompNeutral_of_codeAddress (cpR_codeAddr O tS tA m w) (by decide)
      (by decide)

/-- F1's `DELEGATECALL` targets the implementation, as a kernel decision. -/
theorem cpF2_codeAddr' : ∀ (O : State) (tS : StorShadow) (tA : AcctShadow) (m : Meta)
    (w : World),
    decide ((cpF2 O tS tA m w).f.inner.codeAddress = some implAddr) = true := by
  kernel_forall_rfl

/-- F1's `DELEGATECALL` targets the implementation. -/
theorem cpF2_codeAddr : ∀ (O : State) (tS : StorShadow) (tA : AcctShadow) (m : Meta)
    (w : World), (cpF2 O tS tA m w).f.inner.codeAddress = some implAddr :=
  fun O tS tA m w => of_decide_eq_true (cpF2_codeAddr' O tS tA m w)

/-- F1's `DELEGATECALL` prep enters no fork-sensitive precompile. -/
theorem cpF2_neutral : ∀ (O : State) (tS : StorShadow) (tA : AcctShadow) (m : Meta)
    (w : World), (cpF2 O tS tA m w).f.PrecompNeutral :=
  fun O tS tA m w =>
    Frame.precompNeutral_of_codeAddress (cpF2_codeAddr O tS tA m w) (by decide)
      (by decide)

/-- F1's entry addresses are its frame's inner addresses. -/
theorem e1_entry_acc : ∀ (O : State) (tS : StorShadow) (tA : AcctShadow) (m : Meta)
    (w : World),
    (e1 O tS tA m w).dyna.accessedAddresses =
      (cpR O tS tA m w).f.inner.accessedAddresses := by
  kernel_forall_rfl

/-- F1's entry keys are its frame's inner keys. -/
theorem e1_entry_keys : ∀ (O : State) (tS : StorShadow) (tA : AcctShadow) (m : Meta)
    (w : World),
    (e1 O tS tA m w).dyna.accessedStorageKeys =
      (cpR O tS tA m w).f.inner.accessedStorageKeys := by
  kernel_forall_rfl

/-- F1's addresses at its `DELEGATECALL` are its entry addresses. -/
theorem e1'11_acc : ∀ (O : State) (tS : StorShadow) (tA : AcctShadow) (m : Meta)
    (w : World),
    (e1'11 O tS tA m w).dyna.accessedAddresses =
      (e1 O tS tA m w).dyna.accessedAddresses := by
  kernel_forall_rfl

/-- F1's keys at its `DELEGATECALL` are its entry keys. -/
theorem e1'11_keys : ∀ (O : State) (tS : StorShadow) (tA : AcctShadow) (m : Meta)
    (w : World),
    (e1'11 O tS tA m w).dyna.accessedStorageKeys =
      (e1 O tS tA m w).dyna.accessedStorageKeys := by
  kernel_forall_rfl

/-- F1's state at its `DELEGATECALL` is its entry state. -/
theorem e1'11_state : ∀ (O : State) (tS : StorShadow) (tA : AcctShadow) (m : Meta)
    (w : World),
    (e1'11 O tS tA m w).dyna.state = (e1 O tS tA m w).dyna.state := by
  kernel_forall_rfl

/-- F1 at its `DELEGATECALL`: the forked static machine exposes the fork. -/
theorem e1'11_sta_fork : ∀ (g : Fork) (O : State) (tS : StorShadow) (tA : AcctShadow)
    (m : Meta) (w : World), ((((e1'11 O tS tA m w).withFork g).sta)) =
      (((e1'11 O tS tA m w).sta.withFork g)) := by
  kernel_forall_rfl

/-- F1 at its `DELEGATECALL`: the dynamic machine ignores the fork. -/
theorem e1'11_dyna_fork : ∀ (g : Fork) (O : State) (tS : StorShadow) (tA : AcctShadow)
    (m : Meta) (w : World), ((((e1'11 O tS tA m w).withFork g).dyna)) =
      ((e1'11 O tS tA m w).dyna) := by
  kernel_forall_rfl

/-- F2's entry dynamic machine ignores the fork. -/
theorem e2_dyna_fork : ∀ (g : Fork) (O : State) (tS : StorShadow) (tA : AcctShadow)
    (m : Meta) (w : World), ((((e2 O tS tA m w).withFork g).dyna)) =
      ((e2 O tS tA m w).dyna) := by
  kernel_forall_rfl

/-! ## Forked entry literals (avoid `withFork` defeq unfolds in assembly) -/

/-- F1's entry caller, under any covered fork. -/
theorem e1_caller_fork : ∀ (g : Fork) (O : State) (tS : StorShadow) (tA : AcctShadow)
    (m : Meta) (w : World), (((e1 O tS tA m w).withFork g).sta.caller) =
      attackerAddr := by
  kernel_forall_rfl

/-- F1's entry target, under any covered fork. -/
theorem e1_target_fork : ∀ (g : Fork) (O : State) (tS : StorShadow) (tA : AcctShadow)
    (m : Meta) (w : World), (((e1 O tS tA m w).withFork g).sta.currentTarget) =
      proxyAddr := by
  kernel_forall_rfl

/-- F1's entry code, under any covered fork. -/
theorem e1_code_fork : ∀ (g : Fork) (O : State) (tS : StorShadow) (tA : AcctShadow)
    (m : Meta) (w : World), (((e1 O tS tA m w).withFork g).sta.code) =
      fwdCode := by
  kernel_forall_rfl

/-- F1's entry pc, under any covered fork. -/
theorem e1_pc_fork : ∀ (g : Fork) (O : State) (tS : StorShadow) (tA : AcctShadow)
    (m : Meta) (w : World), (((e1 O tS tA m w).withFork g).pc) = 0 := by
  kernel_forall_rfl

/-- F2's entry target, under any covered fork. -/
theorem e2_target_fork : ∀ (g : Fork) (O : State) (tS : StorShadow) (tA : AcctShadow)
    (m : Meta) (w : World), (((e2 O tS tA m w).withFork g).sta.currentTarget) =
      proxyAddr := by
  kernel_forall_rfl

/-- F2's entry code, under any covered fork. -/
theorem e2_code_fork : ∀ (g : Fork) (O : State) (tS : StorShadow) (tA : AcctShadow)
    (m : Meta) (w : World), (((e2 O tS tA m w).withFork g).sta.code) =
      Vulnerable.code := by
  kernel_forall_rfl

/-- F2's entry data, under any covered fork. -/
theorem e2_data_fork : ∀ (g : Fork) (O : State) (tS : StorShadow) (tA : AcctShadow)
    (m : Meta) (w : World), (((e2 O tS tA m w).withFork g).sta.data) =
      removeCallR := by
  kernel_forall_rfl

/-- F2's entry pc, under any covered fork. -/
theorem e2_pc_fork : ∀ (g : Fork) (O : State) (tS : StorShadow) (tA : AcctShadow)
    (m : Meta) (w : World), (((e2 O tS tA m w).withFork g).pc) = 0 := by
  kernel_forall_rfl

/-- F2's start configuration carries F2's entry dynamic machine. -/
theorem e2_dyna_c2 : ∀ (O : State) (tS : StorShadow) (tA : AcctShadow) (m : Meta)
    (w : World),
    (e2 O tS tA m w).dyna = (c2 O tS tA m w).devm := by
  kernel_forall_rfl

end Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Reach.Viol
