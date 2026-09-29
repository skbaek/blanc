import Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Tx.Frame4

/-!
V- as an admitted transaction, frame 3: `A'` re-entered by frame 2's `CALL` at step 339 with value
100.  Its lifted certificate (`Attacker2`: the dispatcher falls through on the empty calldata)
runs 32 nodes to its `CALL` of `P`, resumes from the proxy frame (`frame4_child`, as data with
its gas and output as literals), `POP`s and `STOP`s.  The settled callback machine `post3T` is
frame 2's `CALL` child: `ChildOk` at `cfg339T`, with the shadows `keysAT`/`adrsAT`/`storAT`/`acsAT`
and the gas, output and success frame 2 takes.
-/

namespace Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Tx

open Jaune Blanc.Lift Blanc.Lift.Witness Blanc.ConcreteRun
open Blanc.Lift.VyperNonreentrantDeployed Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Frame1
open Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.TxTop
open Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Subtree (haltedOf)

attribute [local irreducible] callCfg cp0 e1T cp2T e2T cfg339T e3T cc3T aCallT cp4T e4T cp5T e5T post5T post4T

/-- `A'`'s (callback) settled gas (the EELS Prague trace's `STOP`). -/
def gasAT : Nat := 28504000

/-- The accessed storage keys after the callback subtree (the halting configuration of the
callback frame: frame 2's own, then those of the proxy frame and the implementation frame,
duplicates kept; membership is what matters). -/
def keysAT : List (Adr × B256) :=
  [(proxyAddress, (8 : Nat).toB256),
   (proxyAddress, (26 : Nat).toB256),
   (proxyAddress, (2 : Nat).toB256),
   (proxyAddress, (8 : Nat).toB256),
   (proxyAddress, (26 : Nat).toB256),
   (proxyAddress, (2 : Nat).toB256),
   (proxyAddress, balanceOfA2Slot.toB256),
   (proxyAddress, (10 : Nat).toB256),
   (proxyAddress, (16 : Nat).toB256),
   (proxyAddress, (15 : Nat).toB256),
   (proxyAddress, (9 : Nat).toB256),
   (proxyAddress, (12 : Nat).toB256),
   (proxyAddress, (14 : Nat).toB256),
   (proxyAddress, (0 : Nat).toB256),
   (proxyAddress, (8 : Nat).toB256),
   (proxyAddress, (26 : Nat).toB256),
   (proxyAddress, (2 : Nat).toB256)]

def adrsAT : List Adr :=
  [proxyAddress, a2Address, (4 : Adr), implementationAddress, proxyAddress] ++ praguePrecompiles ++ [eAddress, a2Address] ++ [implementationAddress, proxyAddress, a2Address, (4 : Adr), implementationAddress, proxyAddress] ++ praguePrecompiles ++ [eAddress, a2Address] ++ [implementationAddress, proxyAddress, a2Address, (4 : Adr), implementationAddress, proxyAddress] ++ praguePrecompiles ++ [eAddress, a2Address]

/-- The proxy frame's settled machine as the attacker's child, its observed parts as
literals. -/
abbrev obsChild4 (d : Devm) : Devm := childObs gas4T (word 106) d

/-- The attacker frame after its `CALL`, from a settled proxy frame `d3`. -/
def run3T (d3 : Devm) : Res :=
  match callResume e3T.sta aCallT d3 keysH4T adrsH4T storAT acsAT with
  | some c => wrun fs3 e3T.sta 2 c
  | none => .stuck

/-- The attacker's halt: gas, output, and success with the shadows `keysAT`/`adrsAT`/
`storAT`/`acsAT`. -/
def obs3 : Res → Option (Nat × List Nat × Bool × AcctShadow)
  | .done (.halted d) cl => some (d.gasLeft, d.output.map UInt8.toNat, d.error.isNone &&
      decide (cl.keys = keysAT) && decide (cl.adrs = adrsAT) && decide (cl.stor = storAT), cl.acs)
  | _ => none

theorem frame3_kernel : ∀ d : Devm, obs3 (run3T (obsChild4 d)) = some (gasAT, [], true, acsAT) := by
  kernel_forall_rfl

theorem fs3_zero : fs3[0]? = some Attacker2.t_0000_c0 := by kernel_rfl

theorem e3T_code : e3T.sta.code = Attacker2.code := byteArray_eq_of_toList (by decide +kernel)

theorem e3T_fork : CoveredFork e3T.sta.benvStat.fork := of_decide_eq_true (by decide +kernel)

/-- The attacker frame's settled machine. -/
def post3T : Devm := haltedOf (run3T post4T)

/-- The attacker's frame from any settled proxy frame `d3` that is the `CALL`'s child with
the proxy frame's gas, output, success and shadows. -/
theorem callback_of_child (d3 : Devm) (k3 : ChildOk e3T.sta aCallT d3)
    (a3 : ChildAgree d3 keysH4T adrsH4T storAT acsAT) (g3 : d3.gasLeft = gas4T)
    (o3 : d3.output = word 106) (e4T' : d3.error = none) :
    ChildOk e2T.sta cfg339T (haltedOf (run3T d3)) ∧
      ChildAgree (haltedOf (run3T d3)) keysAT adrsAT storAT acsAT ∧
      (haltedOf (run3T d3)).gasLeft = gasAT ∧ (haltedOf (run3T d3)).output = [] ∧
      (haltedOf (run3T d3)).error = none := by
  have hk := frame3_kernel d3
  rw [show obsChild4 d3 = d3 from childObs_eq g3 o3 e4T'] at hk
  unfold run3T at hk ⊢
  split at hk
  · rename_i c hc
    generalize hr : wrun fs3 e3T.sta 2 c = r at hk ⊢
    rcases r with c' | ⟨d | d, cl⟩ | _
    · simp [obs3] at hk
    · simp only [obs3, Option.some.injEq, Prod.mk.injEq, Bool.and_eq_true,
        decide_eq_true_eq] at hk
      obtain ⟨hg, ho, ⟨⟨⟨he, hkk⟩, hka⟩, hks⟩, hkc⟩ := hk
      have herr : d.error = none := Option.isNone_iff_eq_none.mp he
      have hstep := (wrun_cont aCallT_eq).trans (callResume_cont hc k3 a3)
      obtain ⟨hok, hag⟩ := childOk_of_start
        (fun hcode hfork hr' => lift_exact Attacker2.cert_check Attacker2.cert_jumpsOk hcode hfork hr')
        agree_cfg339T fs3_zero start3T_eq e3T_fork e3T_code hstep hr herr
      rw [hkk, hka, hks, hkc] at hag
      exact ⟨hok, hag, hg, List.map_injective_iff.mpr (fun _ _ h => UInt8.toNat_inj.mp h) ho,
        herr⟩
    · simp [obs3] at hk
    · simp [obs3] at hk
  · simp [obs3] at hk

/-- **The callback subtree as frame 2's child** (tx frames 3-5). -/
theorem callback_child : ChildOk e2T.sta cfg339T post3T ∧ ChildAgree post3T keysAT adrsAT storAT acsAT ∧
    post3T.gasLeft = gasAT ∧ post3T.output = [] ∧ post3T.error = none :=
  let ⟨k3, a3, g3, o3, e4T'⟩ := frame4_child
  callback_of_child post4T k3 a3 g3 o3 e4T'


end Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Tx
