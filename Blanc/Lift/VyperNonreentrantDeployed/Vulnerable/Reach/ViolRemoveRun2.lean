import Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Reach.ViolRemoveRun1

/-!
# V− P2, F2 whole: the run of `remove_liquidity` with both children

F2 (`remove_liquidity(200, [0, 0], A)`, static machine `sRm`) makes the ETH `CALL`
of the attacker at step 339 (value 100) and the token's `transfer(A, 100)` 234
steps after the callback resumes. The callback child is supplied as data (its
settled machine `d`, observed gas `gasCb`, empty output); the token child is run
by its own lifted certificate (`childRun`, 200 steps); 188 steps after the token
resume F2 `RETURN`s. Four identity-precompile (`0x04`) calls run inline by
`callStep`.

`runRmFrom` stages this with `callPairFrom` (cf. `Frame1Run.run1From`): the
prefix result `r` is an argument, so a proof about the rest cases on it without
the kernel evaluating the prefix. `rm_kernel` is the single kernel decision
(prefix 339, resume, 234, token child 200, resume, 188) against the committed
exit literals. Do not open this file in the language server.
-/

namespace Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Reach.Viol

open Jaune Blanc.Lift Blanc.Lift.Witness Blanc.Lift.NodeWalk Blanc.ConcreteRun
open Blanc.Lift.VyperNonreentrantDeployed

/-- F2 after its first 339 steps (with result `r`), with the callback child `d`
supplied; the token child (234 steps after the callback resume) is run by its
own certificate (`childRun`, 200 steps) and resumed from with the shadows of its
halting configuration; then 188 steps to `RETURN`. Taking the prefix's result as
an argument lets a proof about the rest case on it without the kernel evaluating
the prefix. -/
def runRmFrom (tS : StorShadow) (tA : AcctShadow) (r : Res) (d : Devm) : Res :=
  Boundary.callPairFrom fsI sRm Token20.prog Token20.code 234 200 188 keysCb adrsCb
    (storCb ++ tS) (acsCb ++ tA) r d

/-- The whole of F2, from its entry boundary `bRm0`, with the callback child `d`
supplied. -/
def runRm (tS : StorShadow) (tA : AcctShadow) (m : Meta) (w : World) (d : Devm) : Res :=
  runRmFrom tS tA (wrun fsI sRm 339 (Boundary.cfgOfT bRm0 tS tA m w)) d

/-- What F2's halt shows: gas, return data, and `totalSupply` (slot 26),
`balanceOf[attacker]` (`lpSlotA`) and the remove-lock (slot 2) in the halting
configuration's storage shadow, and success (no error). -/
def obsRm : Res → Option (Nat × List Nat × Nat × Nat × Nat × Bool)
  | .done (.halted d) cl => some (d.gasLeft, d.output.map UInt8.toNat,
      (lookupS cl.stor proxyAddr (26 : Nat).toB256).toNat,
      (lookupS cl.stor proxyAddr lpSlotA).toNat,
      (lookupS cl.stor proxyAddr (2 : Nat).toB256).toNat, d.error.isNone)
  | _ => none

/-- The frozen observation at F2's `RETURN`: gas `gasRm`, return data `outRm`
(`word 100 ++ word 100`), `totalSupply = 1800 < 1906 = balanceOf[A]`, lock
released, success. -/
def obsRmEELS : Option (Nat × List Nat × Nat × Nat × Nat × Bool) :=
  some (gasRm, outRm.map UInt8.toNat, 1800, 1906, 0, true)

/-- F2's whole run, with any callback child at the observed gas and output, halts
with the frozen observation: the prefix (339 steps), the callback resume, 234
steps to the token's `CALL`, the token child (200 steps), its resume, and 188
steps to `RETURN`. -/
theorem rm_kernel : ∀ (tS : StorShadow) (tA : AcctShadow) (m : Meta) (w : World)
    (d : Devm),
    obsRm (runRm tS tA m w (childObs gasCb [] d)) = obsRmEELS := by
  kernel_forall_rfl

/-! ## CALL-point small facts (each probe-checked in scratch before committing) -/

/-- F2's keys at its `CALL`: slot reads 8, 26 and the lock 2. -/
theorem cRm339_keys : ∀ (tS : StorShadow) (tA : AcctShadow) (m : Meta) (w : World),
    (cRm339 tS tA m w).keys = [(proxyAddr, (8 : Nat).toB256),
      (proxyAddr, (26 : Nat).toB256), (proxyAddr, (2 : Nat).toB256)] := by
  kernel_forall_rfl

/-- F2's `CALL` preparation addresses. -/
theorem cpRm_adrs : ∀ (tS : StorShadow) (tA : AcctShadow) (m : Meta) (w : World),
    (cpRm tS tA m w).adrs = [attackerAddr, (4 : Adr), implAddr, proxyAddr] := by
  kernel_forall_rfl

/-- F2's `CALL` targets the attacker. -/
theorem cpRm_codeAddr : ∀ (tS : StorShadow) (tA : AcctShadow) (m : Meta) (w : World),
    (cpRm tS tA m w).f.inner.codeAddress = some attackerAddr := by
  kernel_forall_rfl

/-- F2's `CALL` needs no fork check. -/
theorem cpRm_forkfree : ∀ (tS : StorShadow) (tA : AcctShadow) (m : Meta) (w : World),
    frameEntryForkFree (cpRm tS tA m w).f = true := by
  kernel_forall_rfl

/-- At F2's `CALL` the lock slot 2 is held. -/
theorem rm339_stor2 : ∀ (tS : StorShadow) (tA : AcctShadow) (m : Meta) (w : World),
    lookupS (cRm339 tS tA m w).stor proxyAddr 2 = 1 := by
  kernel_forall_rfl

/-- At F2's `CALL` the cached supply is 2000. -/
theorem rm339_stor26 : ∀ (tS : StorShadow) (tA : AcctShadow) (m : Meta) (w : World),
    lookupS (cRm339 tS tA m w).stor proxyAddr 26 = 2000 := by
  kernel_forall_rfl

/-- F2's `CALL` entered configuration (the `childStart` shape). -/
def cc3Rm (tS : StorShadow) (tA : AcctShadow) (m : Meta) (w : World) : Cfg :=
  ⟨(e3Rm tS tA m w).dyna, AttackerR.t_0000_c0, [], (cRm339 tS tA m w).keys,
    (cpRm tS tA m w).adrs, (cRm339 tS tA m w).stor,
    acsTransfer (cpRm tS tA m w).f.inner (cRm339 tS tA m w).acs⟩

/-- F2's `CALL` starts the callback child at the entered configuration. -/
theorem csRm_start : ∀ (tS : StorShadow) (tA : AcctShadow) (m : Meta) (w : World),
    childStart sRm (cRm339 tS tA m w) AttackerR.t_0000_c0 =
      some ((e3Rm tS tA m w), cc3Rm tS tA m w) := by
  intro tS tA m w
  unfold childStart
  rw [cpRm_eq tS tA m w, e3Rm_eq tS tA m w, cpRm_forkfree tS tA m w]

/-- The entered callback configuration is the entry boundary `bCb0` with the
same tails. -/
theorem cc3Rm_obs : ∀ (tS : StorShadow) (tA : AcctShadow) (m : Meta) (w : World),
    Boundary.obsDT bCb0 (.cont (cc3Rm tS tA m w)) =
      Boundary.obsDOkT bCb0 tS tA := by
  kernel_forall_rfl

/-! ## F3's entry facts under any covered fork -/

/-- F3's entry target under any covered fork (kernel form). -/
theorem e3Rm_target_at' : ∀ (g : Fork) (tS : StorShadow) (tA : AcctShadow) (m : Meta)
    (w : World),
    decide (((((e3Rm tS tA m w).withFork g).sta)).currentTarget = attackerAddr) =
      true := by
  kernel_forall_rfl

theorem e3Rm_target_at : ∀ (g : Fork) (tS : StorShadow) (tA : AcctShadow) (m : Meta)
    (w : World),
    ((((e3Rm tS tA m w).withFork g).sta)).currentTarget = attackerAddr :=
  fun g tS tA m w => of_decide_eq_true (e3Rm_target_at' g tS tA m w)

/-- F3's entry code under any covered fork (kernel form). -/
theorem e3Rm_code_at' : ∀ (g : Fork) (tS : StorShadow) (tA : AcctShadow) (m : Meta)
    (w : World),
    decide (((((e3Rm tS tA m w).withFork g).sta)).code = AttackerR.code) = true := by
  kernel_forall_rfl

theorem e3Rm_code_at : ∀ (g : Fork) (tS : StorShadow) (tA : AcctShadow) (m : Meta)
    (w : World),
    ((((e3Rm tS tA m w).withFork g).sta)).code = AttackerR.code :=
  fun g tS tA m w => of_decide_eq_true (e3Rm_code_at' g tS tA m w)

/-- F3's entry value under any covered fork (kernel form). -/
theorem e3Rm_value_at' : ∀ (g : Fork) (tS : StorShadow) (tA : AcctShadow) (m : Meta)
    (w : World),
    decide (((((e3Rm tS tA m w).withFork g).sta)).value = 100) = true := by
  kernel_forall_rfl

theorem e3Rm_value_at : ∀ (g : Fork) (tS : StorShadow) (tA : AcctShadow) (m : Meta)
    (w : World),
    ((((e3Rm tS tA m w).withFork g).sta)).value = 100 :=
  fun g tS tA m w => of_decide_eq_true (e3Rm_value_at' g tS tA m w)

/-! ## Token-CALL point and token child, as data -/

/-- F2 at the token's `CALL`: the callback resume plus 234 steps, as data (the
callback child `d` is free: keys never depend on the child's contents). -/
def cTokRm (tS : StorShadow) (tA : AcctShadow) (m : Meta) (w : World)
    (d : Devm) : Cfg :=
  match Boundary.callPairA fsI sRm keysCb adrsCb (storCb ++ tS) (acsCb ++ tA) 234
      (.cont (cRm339 tS tA m w)) (childObs gasCb [] d) with
  | .cont c3 => c3
  | _ => cRm339 tS tA m w

/-- F2's keys at the token's `CALL`: the new key `(proxy, 7)` ahead of the
resume's. -/
theorem cTokRm_keys : ∀ (tS : StorShadow) (tA : AcctShadow) (m : Meta) (w : World)
    (d : Devm),
    (cTokRm tS tA m w d).keys = [(proxyAddr, (7 : Nat).toB256),
      (proxyAddr, (8 : Nat).toB256), (proxyAddr, (26 : Nat).toB256),
      (proxyAddr, (2 : Nat).toB256)] ++ keysCb := by
  kernel_forall_rfl

/-- The token child's accessed keys: its two balance slots ahead of F2's. -/
theorem tokResRm_keys : ∀ (tS : StorShadow) (tA : AcctShadow) (m : Meta) (w : World)
    (d : Devm),
    resKeys (childRun Token20.prog Token20.code sRm 200 (cTokRm tS tA m w d)) =
      [(tokenAddr, attackerAddr.toB256), (tokenAddr, proxyAddr.toB256),
        (proxyAddr, (7 : Nat).toB256), (proxyAddr, (8 : Nat).toB256),
        (proxyAddr, (26 : Nat).toB256), (proxyAddr, (2 : Nat).toB256)] ++
        keysCb := by
  kernel_forall_rfl

/-! ## Halt shadows beyond `obsRm` -/

/-- What F2's halt shows beyond `obsRm`: keys, addresses, storage prefix and
account keys against the frozen literals. -/
def rmHaltKeys : Res → Option (Bool × Bool × Bool × Bool)
  | .done (.halted _) cl =>
    some (decide (cl.keys = keysRm), decide (cl.adrs = adrsRm),
      decide (cl.stor.take storRm.length = storRm),
      decide ((cl.acs.take acsRm.length).map Boundary.acctKey =
        acsRm.map Boundary.acctKey))
  | _ => none

theorem rmHalt_keys : ∀ (tS : StorShadow) (tA : AcctShadow) (m : Meta) (w : World)
    (d : Devm),
    rmHaltKeys (runRm tS tA m w (childObs gasCb [] d)) =
      some (true, true, true, true) := by
  kernel_forall_rfl

/-- F2's halt account rests and tails. -/
def rmHaltRest : Res → List (Stor × ByteArray) × StorShadow × AcctShadow
  | .done (.halted _) cl =>
    ((cl.acs.take acsRm.length).map Boundary.acctRest, cl.stor.drop storRm.length,
      cl.acs.drop acsRm.length)
  | _ => ([], [], [])

theorem rmHalt_rest : ∀ (tS : StorShadow) (tA : AcctShadow) (m : Meta) (w : World)
    (d : Devm),
    rmHaltRest (runRm tS tA m w (childObs gasCb [] d)) =
      (Boundary.restsOf acsRm, tS, tA) := by
  kernel_forall_rfl

end Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Reach.Viol
