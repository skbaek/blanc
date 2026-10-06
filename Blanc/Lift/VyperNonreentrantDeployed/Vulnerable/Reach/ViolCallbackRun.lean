import Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Reach.ViolBoundary

/-!
# V− P2, F3/F4 kernel run: the callback frame and its forwarder child

Kernel facts over `(sCb.withOrig O)` (Prague fork) with a free original state `O` and
free shadow tails: the callback `AttackerR` frame from its entry boundary `bCb0` runs
32 steps to its `CALL` of the clone (`cACb`); the `CALL` spawns the forwarder (`cpCb`,
`e4Cb`); the forwarder runs 11 steps to its `DELEGATECALL` (`e4Cb31`), whose spawn
(`cpCb5`) enters the re-entrant implementation frame (`e5Cb`, start configuration
`c5Cb`, decided against `bRe0`); the forwarder resumed from F5's settled machine halts
with `gasCbFwd`/`outRe`; and the callback resumed from the forwarder halts with
`gasCb` and the `keysCb`/`adrsCb`/`storCb`/`acsCb` shadows.

Neither the certificate runs nor the forwarder's EVM steps read the original state
(no `SSTORE` anywhere in F3/F4), so the kernel evaluates them with `O` free: each fact
is a `kernel_forall_rfl` decision, and a read of `O` (or of a tail) would leave the
run stuck and fail the fact. The observations additionally pin the runs to the frozen
literals. Fork transport to every covered fork, and the composition into
`CallbackFrame`, live in `Reach/ViolCallback.lean`.
-/

namespace Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Reach.Viol

open Jaune Blanc.Lift Blanc.Lift.Witness Blanc.Lift.NodeWalk Blanc.ConcreteRun
open Blanc.Lift.VyperNonreentrantDeployed

/-! ## F3 to its `CALL` -/

/-- F3 at its `CALL` of the clone: the configuration after 32 steps. -/
def cACb (O : State) (tS : StorShadow) (tA : AcctShadow) (m : Meta) (w : World) : Cfg :=
  match wrun fsA (sCb.withOrig O) 32 (Boundary.cfgOfT bCb0 tS tA m w) with
  | .cont c => c
  | _ => Boundary.cfgOfT bCb0 tS tA m w

theorem cACb_eq : ∀ (O : State) (tS : StorShadow) (tA : AcctShadow) (m : Meta) (w : World),
    wrun fsA (sCb.withOrig O) 32 (Boundary.cfgOfT bCb0 tS tA m w) =
      .cont (cACb O tS tA m w) := by
  kernel_forall_rfl

/-- F3's `CALL` up to its spawn. -/
def cpCb (O : State) (tS : StorShadow) (tA : AcctShadow) (m : Meta) (w : World) : CallPrep :=
  (callPrep (sCb.withOrig O) (cACb O tS tA m w)).getD noPrepI

theorem cpCb_eq : ∀ (O : State) (tS : StorShadow) (tA : AcctShadow) (m : Meta) (w : World),
    callPrep (sCb.withOrig O) (cACb O tS tA m w) = some (cpCb O tS tA m w) := by
  kernel_forall_rfl

/-- The forwarder frame F4 as spawned by F3's `CALL`. -/
def e4Cb (O : State) (tS : StorShadow) (tA : AcctShadow) (m : Meta) (w : World) : Evm :=
  match frameEnterS (cpCb O tS tA m w).f (cACb O tS tA m w).acs with
  | .run e => e
  | .done _ => default

theorem e4Cb_eq : ∀ (O : State) (tS : StorShadow) (tA : AcctShadow) (m : Meta) (w : World),
    frameEnterS (cpCb O tS tA m w).f (cACb O tS tA m w).acs = .run (e4Cb O tS tA m w) := by
  kernel_forall_rfl

theorem e4Cb_code : ∀ (O : State) (tS : StorShadow) (tA : AcctShadow) (m : Meta) (w : World),
    (e4Cb O tS tA m w).sta.code = fwdCode := by
  kernel_forall_rfl

theorem e4Cb_target : ∀ (O : State) (tS : StorShadow) (tA : AcctShadow) (m : Meta) (w : World),
    ((e4Cb O tS tA m w).sta.currentTarget = proxyAddr ∧
      (e4Cb O tS tA m w).sta.value = 100) := by
  kernel_forall_rfl_and

/-- F4's account shadow at entry: the `CALL`'s value transfer applied. -/
def acs4Cb (O : State) (tS : StorShadow) (tA : AcctShadow) (m : Meta) (w : World) : AcctShadow :=
  acsTransfer (cpCb O tS tA m w).f.inner (cACb O tS tA m w).acs

/-! ## F4 to its `DELEGATECALL`, and F5's entry -/

/-- The forwarder at its `DELEGATECALL` (pc 31). -/
def e4Cb31 (O : State) (tS : StorShadow) (tA : AcctShadow) (m : Meta) (w : World) : Evm :=
  (stepN 11 (e4Cb O tS tA m w)).getD default

theorem e4Cb31_eq : ∀ (O : State) (tS : StorShadow) (tA : AcctShadow) (m : Meta) (w : World),
    stepN 11 (e4Cb O tS tA m w) = some (e4Cb31 O tS tA m w) := by
  kernel_forall_rfl

/-- F4's `DELEGATECALL` up to its spawn. -/
def cpCb5 (O : State) (tS : StorShadow) (tA : AcctShadow) (m : Meta) (w : World) : CallPrep :=
  (dcallPrep (e4Cb31 O tS tA m w).sta (e4Cb31 O tS tA m w).dyna (cpCb O tS tA m w).adrs
    (acs4Cb O tS tA m w)).getD noPrepI

theorem cpCb5_eq : ∀ (O : State) (tS : StorShadow) (tA : AcctShadow) (m : Meta) (w : World),
    dcallPrep (e4Cb31 O tS tA m w).sta (e4Cb31 O tS tA m w).dyna (cpCb O tS tA m w).adrs
      (acs4Cb O tS tA m w) = some (cpCb5 O tS tA m w) := by
  kernel_forall_rfl

/-- The re-entrant implementation frame F5 as spawned by F4's `DELEGATECALL`. -/
def e5Cb (O : State) (tS : StorShadow) (tA : AcctShadow) (m : Meta) (w : World) : Evm :=
  match frameEnterS (cpCb5 O tS tA m w).f (acs4Cb O tS tA m w) with
  | .run e => e
  | .done _ => default

theorem e5Cb_eq : ∀ (O : State) (tS : StorShadow) (tA : AcctShadow) (m : Meta) (w : World),
    frameEnterS (cpCb5 O tS tA m w).f (acs4Cb O tS tA m w) = .run (e5Cb O tS tA m w) := by
  kernel_forall_rfl

theorem e5Cb_facts : ∀ (O : State) (tS : StorShadow) (tA : AcctShadow) (m : Meta) (w : World),
    ((e5Cb O tS tA m w).sta.currentTarget = proxyAddr ∧
      (e5Cb O tS tA m w).sta.code = Vulnerable.code ∧
      (e5Cb O tS tA m w).sta.data = reAddCall) := by
  kernel_forall_rfl_and

/-- F5's start configuration (the probe's convention). -/
def c5Cb (O : State) (tS : StorShadow) (tA : AcctShadow) (m : Meta) (w : World) : Cfg :=
  ⟨(e5Cb O tS tA m w).dyna, Vulnerable.t_0000_c0, [], (cACb O tS tA m w).keys,
    (cpCb5 O tS tA m w).adrs, (cACb O tS tA m w).stor,
    acsTransfer (cpCb5 O tS tA m w).f.inner (acs4Cb O tS tA m w)⟩

/-- F5's start configuration is the entry boundary `bRe0` with the same tails. -/
theorem c5Cb_obs : ∀ (O : State) (tS : StorShadow) (tA : AcctShadow) (m : Meta) (w : World),
    Boundary.obsDT bRe0 (.cont (c5Cb O tS tA m w)) = Boundary.obsDOkT bRe0 tS tA := by
  kernel_forall_rfl

/-! ## F4 resumed from F5, as data -/

/-- F5's settled machine as F4's child, its observed parts as literals. -/
abbrev obsChild5Cb (d : Devm) : Devm := childObs gasRe outRe d

/-- The forwarder resumed from a settled F5 `d`. -/
def d4Cb (O : State) (tS : StorShadow) (tA : AcctShadow) (m : Meta) (w : World)
    (d : Devm) : Devm :=
  (resumeCallB (cpCb5 O tS tA m w).p (cpCb5 O tS tA m w).oi (cpCb5 O tS tA m w).os
    (.ok (obsChild5Cb d))).getD default

/-- The forwarder at its `RETURN` (pc 44). -/
def e444Cb (O : State) (tS : StorShadow) (tA : AcctShadow) (m : Meta) (w : World)
    (d : Devm) : Evm :=
  (stepN 10 ⟨32, (e4Cb O tS tA m w).sta, d4Cb O tS tA m w d⟩).getD default

/-- The forwarder's halted machine. -/
def post4Cb (O : State) (tS : StorShadow) (tA : AcctShadow) (m : Meta) (w : World)
    (d : Devm) : Devm :=
  match Evm.step (e444Cb O tS tA m w d) with
  | .halt (.ok d') => d'
  | _ => default

theorem resumeCb_eq : ∀ (O : State) (tS : StorShadow) (tA : AcctShadow) (m : Meta) (w : World)
    (d : Devm),
    resumeCallB (cpCb5 O tS tA m w).p (cpCb5 O tS tA m w).oi (cpCb5 O tS tA m w).os
      (.ok (obsChild5Cb d)) = some (d4Cb O tS tA m w d) := by
  kernel_forall_rfl

theorem tailCb_eq : ∀ (O : State) (tS : StorShadow) (tA : AcctShadow) (m : Meta) (w : World)
    (d : Devm),
    stepN 10 ⟨32, (e4Cb O tS tA m w).sta, d4Cb O tS tA m w d⟩ =
      some (e444Cb O tS tA m w d) := by
  kernel_forall_rfl

theorem returnCb_eq : ∀ (O : State) (tS : StorShadow) (tA : AcctShadow) (m : Meta) (w : World)
    (d : Devm),
    Evm.step (e444Cb O tS tA m w d) = .halt (.ok (post4Cb O tS tA m w d)) := by
  kernel_forall_rfl

theorem post4Cb_obs : ∀ (O : State) (tS : StorShadow) (tA : AcctShadow) (m : Meta) (w : World)
    (d : Devm),
    ((post4Cb O tS tA m w d).gasLeft, (post4Cb O tS tA m w d).output.map UInt8.toNat,
      (post4Cb O tS tA m w d).error.isNone) =
    (gasCbFwd, outRe.map UInt8.toNat, true) := by
  kernel_forall_rfl

theorem post4Cb_keep : ∀ (O : State) (tS : StorShadow) (tA : AcctShadow) (m : Meta) (w : World)
    (d : Devm),
    ((post4Cb O tS tA m w d).accessedAddresses, (post4Cb O tS tA m w d).accessedStorageKeys,
      (post4Cb O tS tA m w d).state) =
    ((d4Cb O tS tA m w d).accessedAddresses, (d4Cb O tS tA m w d).accessedStorageKeys,
      (d4Cb O tS tA m w d).state) := by
  kernel_forall_rfl

/-! ## F3 resumed from F4, to its halt -/

/-- F4's settled machine as F3's child, its observed parts as literals. -/
abbrev obsChild4Cb (d : Devm) : Devm := childObs gasCbFwd outRe d

/-- The callback frame after its `CALL`, from a settled forwarder `d`. -/
def runCb (O : State) (tS : StorShadow) (tA : AcctShadow) (m : Meta) (w : World)
    (d : Devm) : Res :=
  match callResume (sCb.withOrig O) (cACb O tS tA m w) d ((cACb O tS tA m w).keys ++ keysRe)
    ((cpCb5 O tS tA m w).adrs ++ adrsRe) (storRe ++ tS) (acsRe ++ tA) with
  | some c => wrun fsA (sCb.withOrig O) 2 c
  | none => .stuck

/-- The callback's halt: gas, output, and success with the shadows `keysCb`/`adrsCb`/
`storCb`/`acsCb` followed by the tails. -/
def obsCb : Res → Option (Nat × List Nat × Bool × StorShadow × AcctShadow)
  | .done (.halted d) cl =>
    some (d.gasLeft, d.output.map UInt8.toNat, d.error.isNone &&
      decide (cl.keys = keysCb) && decide (cl.adrs = adrsCb) &&
      decide (cl.stor.take storCb.length = storCb),
      cl.stor.drop storCb.length, cl.acs.drop acsCb.length)
  | _ => none

theorem cb_kernel : ∀ (O : State) (tS : StorShadow) (tA : AcctShadow) (m : Meta) (w : World)
    (d : Devm),
    obsCb (runCb O tS tA m w (obsChild4Cb d)) = some (gasCb, [], true, tS, tA) := by
  kernel_forall_rfl

/-- `fsA` starts at the callback's entry node. -/
theorem fsA_zero : fsA[0]? = some AttackerR.t_0000_c0 := by kernel_rfl

/-! ## Entry support: code addresses, forwarder preservation, entered machines -/

theorem cpCb_codeAddr : ∀ (O : State) (tS : StorShadow) (tA : AcctShadow) (m : Meta) (w : World),
    (cpCb O tS tA m w).f.inner.codeAddress = some proxyAddr := by
  kernel_forall_rfl

theorem e4Cb31_acc : ∀ (O : State) (tS : StorShadow) (tA : AcctShadow) (m : Meta) (w : World),
    (e4Cb31 O tS tA m w).dyna.accessedAddresses =
      (e4Cb O tS tA m w).dyna.accessedAddresses := by
  kernel_forall_rfl

theorem e4Cb31_keys : ∀ (O : State) (tS : StorShadow) (tA : AcctShadow) (m : Meta) (w : World),
    (e4Cb31 O tS tA m w).dyna.accessedStorageKeys =
      (e4Cb O tS tA m w).dyna.accessedStorageKeys := by
  kernel_forall_rfl

theorem e4Cb31_state : ∀ (O : State) (tS : StorShadow) (tA : AcctShadow) (m : Meta) (w : World),
    (e4Cb31 O tS tA m w).dyna.state = (e4Cb O tS tA m w).dyna.state := by
  kernel_forall_rfl

/-- The forwarder's stack at its `DELEGATECALL` (printed by `#eval` in scratch:
`[886013, implAddr, 0, 132, 0, 0, 0]` as `Nat`s; its kernel proof exceeds the kernel's
depth budget over the `wrun`-32 + `stepN`-11 chain and is pending). -/
def stackCb31 : List B256 :=
  [⟨⟨0, 0⟩, ⟨0, 886013⟩⟩, ⟨⟨0, 1663491771⟩, ⟨12255909761681031966, 9040401190467777598⟩⟩,
    ⟨⟨0, 0⟩, ⟨0, 0⟩⟩, ⟨⟨0, 0⟩, ⟨0, 132⟩⟩, ⟨⟨0, 0⟩, ⟨0, 0⟩⟩, ⟨⟨0, 0⟩, ⟨0, 0⟩⟩,
    ⟨⟨0, 0⟩, ⟨0, 0⟩⟩]

theorem e4Cb31_gasLeft : ∀ (O : State) (tS : StorShadow) (tA : AcctShadow) (m : Meta)
    (w : World), (e4Cb31 O tS tA m w).dyna.gasLeft = 886013 := by
  kernel_forall_rfl

theorem e4Cb_depth : ∀ (O : State) (tS : StorShadow) (tA : AcctShadow) (m : Meta)
    (w : World), (e4Cb O tS tA m w).sta.depth = 1020 := by
  kernel_forall_rfl




theorem e5Cb_pc : ∀ (O : State) (tS : StorShadow) (tA : AcctShadow) (m : Meta) (w : World),
    (e5Cb O tS tA m w).pc = 0 := by
  kernel_forall_rfl

/-- The entered F5 machine's small static fields, as literals. -/
theorem e5Cb_caller : ∀ (O : State) (tS : StorShadow) (tA : AcctShadow) (m : Meta)
    (w : World), (e5Cb O tS tA m w).sta.caller = attackerAddr := by
  kernel_forall_rfl

theorem e5Cb_target : ∀ (O : State) (tS : StorShadow) (tA : AcctShadow) (m : Meta)
    (w : World), (e5Cb O tS tA m w).sta.target = some proxyAddr := by
  kernel_forall_rfl

theorem e5Cb_value : ∀ (O : State) (tS : StorShadow) (tA : AcctShadow) (m : Meta)
    (w : World), (e5Cb O tS tA m w).sta.value = 100 := by
  kernel_forall_rfl

theorem e5Cb_depth : ∀ (O : State) (tS : StorShadow) (tA : AcctShadow) (m : Meta)
    (w : World), (e5Cb O tS tA m w).sta.depth = 1019 := by
  kernel_forall_rfl

theorem e5Cb_flags : ∀ (O : State) (tS : StorShadow) (tA : AcctShadow) (m : Meta)
    (w : World),
    ((e5Cb O tS tA m w).sta.shouldTransferValue = false ∧
      (e5Cb O tS tA m w).sta.isStatic = false ∧
      (e5Cb O tS tA m w).sta.disablePrecompiles = false) := by
  kernel_forall_rfl_and

/-- The entered F5 machine inherits the block environment down the spawn chain (no
kernel evaluation: each hop is a spec lemma). -/
theorem e5Cb_sta_benvStat : ∀ (O : State) (tS : StorShadow) (tA : AcctShadow) (m : Meta)
    (w : World),
    (e5Cb O tS tA m w).sta.benvStat = (sRe.withOrig O).benvStat := by
  intro O tS tA m w
  rw [(frameEnterS_stat (e5Cb_eq O tS tA m w)).trans
      (dcallPrep_stat (cpCb5_eq O tS tA m w)).2,
    stepN_sta (e4Cb31_eq O tS tA m w),
    (frameEnterS_stat (e4Cb_eq O tS tA m w)).trans
      (callPrep_stat (cpCb_eq O tS tA m w)).2]
  rfl

theorem e5Cb_sta_tenv : ∀ (O : State) (tS : StorShadow) (tA : AcctShadow) (m : Meta)
    (w : World),
    (e5Cb O tS tA m w).sta.tenvStat = (sRe.withOrig O).tenvStat := by
  kernel_forall_rfl

end Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Reach.Viol
