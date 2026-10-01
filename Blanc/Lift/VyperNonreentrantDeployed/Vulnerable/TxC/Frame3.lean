import Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.TxC.Frame4
import Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.TxTopC
import Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Tx.Frame3

/-!
V- as an admitted transaction, frame 3: `A'` re-entered by frame 2's `CALL` at step 339 with value
100.  Its lifted certificate (`Attacker2`: the dispatcher falls through on the empty calldata)
runs 32 nodes to its `CALL` of `P`, resumes from the proxy frame (`frame4C_child`, as data with
its gas and output as literals), `POP`s and `STOP`s.  The settled callback machine `post3C` is
frame 2's `CALL` child: `ChildOk` at `cfg339C`, with the shadows `keysAT`/`adrsAC`/`storAT`/`acsAT`
and the gas, output and success frame 2 takes.
-/

namespace Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.TxC

open Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Tx

open Jaune Blanc.Lift Blanc.Lift.Witness Blanc.ConcreteRun Blanc.ForkUniform Blanc.Lift.NodeWalk
open Blanc.Lift.VyperNonreentrantDeployed Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Frame1
open Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.TxTop
open Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Subtree (haltedOf)

attribute [local irreducible] callCfgC cp0C e1C cp2C e2C cfg339C e3C cc3C aCallC cp4C e4C cp5C e5C post5C post4C

variable {g : Fork}

/-- `A'`'s (callback) settled gas (the EELS Prague trace's `STOP` at the transaction's gas). -/
def gasAC : Nat := 15127669

def adrsAC : List Adr :=
  [proxyAddress, a2Address, (4 : Adr), implementationAddress, proxyAddress] ++ warmC ++ [implementationAddress, proxyAddress, a2Address, (4 : Adr), implementationAddress, proxyAddress] ++ warmC ++ [implementationAddress, proxyAddress, a2Address, (4 : Adr), implementationAddress, proxyAddress] ++ warmC

/-- The proxy frame's settled machine as the attacker's child, its observed parts as
literals. -/
abbrev obsChild4C (d : Devm) : Devm := childObsX gas4C (word 106) refund4 d

/-- The attacker frame after its `CALL`, from a settled proxy frame `d3`. -/
def run3C (d3 : Devm) : Res :=
  match callResume e3C.sta aCallC d3 keysH4C adrsH4C storAT acsAT with
  | some c => wrun fs3 e3C.sta 2 c
  | none => .stuck

/-- The attacker's halt: gas, output, and success with the shadows `keysAT`/`adrsAC`/
`storAT`/`acsAT` and the refund counter; its accounts and set of accounts to delete as terms. -/
def obs3C : Res → Option (Nat × List Nat × Bool × AcctShadow × AdrSet)
  | .done (.halted d) cl => some (d.gasLeft, d.output.map UInt8.toNat, d.error.isNone &&
      decide (cl.keys = keysAT) && decide (cl.adrs = adrsAC) && decide (cl.stor = storAT) &&
      decide (d.refundCounter = refund3), cl.acs, d.accountsToDelete)
  | _ => none

theorem frame3C_kernel : ∀ d : Devm,
    obs3C (run3C (obsChild4C d)) = some (gasAC, [], true, acsAT, .emptyWithCapacity) := by
  kernel_forall_rfl

theorem fs3C_zero : fs3[0]? = some Attacker2.t_0000_c0 := by kernel_rfl

theorem e3C_code : e3C.sta.code = Attacker2.code := byteArray_eq_of_toList (by decide +kernel)

/-- The attacker frame's settled machine. -/
def post3C : Devm := haltedOf (run3C post4C)

/-- The attacker's frame from any settled proxy frame `d3` that is the `CALL`'s child with
the proxy frame's gas, output, success and shadows, under any covered fork. -/
theorem callbackC_of_child_at (hg : CoveredFork g) (d3 : Devm)
    (k3 : ChildOk (e3C.withFork g).sta aCallC d3)
    (a3 : ChildAgree d3 keysH4C adrsH4C storAT acsAT) (g3 : d3.gasLeft = gas4C)
    (o3 : d3.output = word 106) (e4T' : d3.error = none) (r3 : d3.refundCounter = refund4)
    (t3 : d3.accountsToDelete = .emptyWithCapacity) :
    ChildOk (e2C.withFork g).sta cfg339C (haltedOf (run3C d3)) ∧
      ChildAgree (haltedOf (run3C d3)) keysAT adrsAC storAT acsAT ∧
      (haltedOf (run3C d3)).gasLeft = gasAC ∧ (haltedOf (run3C d3)).output = [] ∧
      (haltedOf (run3C d3)).error = none ∧ (haltedOf (run3C d3)).refundCounter = refund3 ∧
      (haltedOf (run3C d3)).accountsToDelete = .emptyWithCapacity := by
  have hk := frame3C_kernel d3
  rw [show obsChild4C d3 = d3 from childObsX_eq g3 o3 e4T' r3 t3] at hk
  have hf3 : CoveredFork e3C.sta.benvStat.fork := by rw [e3C_block.1]; exact CoveredFork.prague
  unfold run3C at hk ⊢
  split at hk
  · rename_i c hc
    have hcg : callResume (e3C.withFork g).sta aCallC d3 keysH4C adrsH4C storAT acsAT = some c :=
      (callResume_withFork hf3 hg _ _ _ _ _ _).trans hc
    generalize hr : wrun fs3 e3C.sta 2 c = r at hk ⊢
    rcases r with c' | ⟨d | d, cl⟩ | _
    · simp only [obs3C, reduceCtorEq] at hk
    · simp only [obs3C, Option.some.injEq, Prod.mk.injEq, Bool.and_eq_true,
        decide_eq_true_eq] at hk
      obtain ⟨hgas, ho, ⟨⟨⟨⟨he, hkk⟩, hka⟩, hks⟩, hrf⟩, hkc, hatd⟩ := hk
      have herr : d.error = none := Option.isNone_iff_eq_none.mp he
      have hstep := (wrun_cont (aCallC_at hg)).trans (callResume_cont hcg k3 a3)
      have hrg : wrun fs3 (e3C.withFork g).sta 2 c = .done (.halted d) cl :=
        (wrun_withFork hf3 hg e3C_block.2 fs3 2 c).trans hr
      obtain ⟨hok, hag⟩ := childOk_of_start
        (fun hcode hfork hr' => lift_exact Attacker2.cert_check Attacker2.cert_jumpsOk hcode hfork hr')
        agree_cfg339C fs3C_zero (start3C_at hg) (hg : CoveredFork g) e3C_code hstep hrg herr
      rw [hkk, hka, hks, hkc] at hag
      exact ⟨hok, hag, hgas, List.map_injective_iff.mpr (fun _ _ h => UInt8.toNat_inj.mp h) ho,
        herr, hrf, hatd⟩
    · simp only [obs3C, reduceCtorEq] at hk
    · simp only [obs3C, reduceCtorEq] at hk
  · simp only [obs3C, reduceCtorEq] at hk

/-- **The callback subtree as frame 2's child** (tx frames 3-5), under any covered fork. -/
theorem callbackC_child_at (hg : CoveredFork g) :
    ChildOk (e2C.withFork g).sta cfg339C post3C ∧ ChildAgree post3C keysAT adrsAC storAT acsAT ∧
      post3C.gasLeft = gasAC ∧ post3C.output = [] ∧ post3C.error = none ∧
      post3C.refundCounter = refund3 ∧ post3C.accountsToDelete = .emptyWithCapacity :=
  let ⟨k3, a3, g3, o3, e4T', r4, t4⟩ := frame4C_child_at hg
  callbackC_of_child_at hg post4C k3 a3 g3 o3 e4T' r4 t4

end Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.TxC
