import Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Frame3

/-!
V- witness, frame 2: the attacker `A` called by frame 1 at step 339 with value 100.  Its
lifted certificate runs 24 nodes to its `CALL` of `P`, resumes from the proxy frame
(`frame3_child`, as data with its gas and output as literals), `POP`s and `STOP`s.  The
settled attacker machine `post2` is frame 1's attacker child: `ChildOk` at `cfg339`, with
the shadows `keysA`/`adrsA`/`storA`/`acsA` and the gas, output and success frame 1 takes.
With it, `frame1_closed` is frame 1 with no hypothesis left.
-/

namespace Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Subtree

open Jaune Blanc.Lift Blanc.Lift.Witness Blanc.ConcreteRun
open Blanc.Lift.VyperNonreentrantDeployed Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Frame1

attribute [local irreducible] cfg339 e2 cc2 aCall cp3 e3 cp4 e4 post4 post3

/-- The proxy frame's settled machine as the attacker's child, its observed parts as
literals. -/
abbrev obsChild3 (d : Devm) : Devm := childObs gas3 (word 106) d

/-- The attacker frame after its `CALL`, from a settled proxy frame `d3`. -/
def run2 (d3 : Devm) : Res :=
  match callResume e2.sta aCall d3 keys3 adrs3' storA acsA with
  | some c => wrun fs2 e2.sta 2 c
  | none => .stuck

/-- The attacker's halt: gas, output, and success with the shadows `keysA`/`adrsA`/
`storA`/`acsA`. -/
def obs2 : Res → Option (Nat × List Nat × Bool × AcctShadow)
  | .done (.halted d) cl => some (d.gasLeft, d.output.map UInt8.toNat, d.error.isNone &&
      decide (cl.keys = keysA) && decide (cl.adrs = adrsA) && decide (cl.stor = storA), cl.acs)
  | _ => none

theorem frame2_kernel : ∀ d : Devm, obs2 (run2 (obsChild3 d)) = some (gasA, [], true, acsA) := by
  kernel_forall_rfl

theorem fs2_zero : fs2[0]? = some Attacker.t_0000_c0 := by kernel_rfl

theorem e2_code : e2.sta.code = Attacker.code := byteArray_eq_of_toList (by decide +kernel)

theorem e2_fork : CoveredFork e2.sta.benvStat.fork := of_decide_eq_true (by decide +kernel)

/-- The attacker frame's settled machine. -/
def post2 : Devm := haltedOf (run2 post3)

/-- The attacker's frame from any settled proxy frame `d3` that is the `CALL`'s child with
the proxy frame's gas, output, success and shadows. -/
theorem attacker_of_child (d3 : Devm) (k3 : ChildOk e2.sta aCall d3)
    (a3 : ChildAgree d3 keys3 adrs3' storA acsA) (g3 : d3.gasLeft = gas3)
    (o3 : d3.output = word 106) (e3' : d3.error = none) :
    ChildOk sevm1 cfg339 (haltedOf (run2 d3)) ∧
      ChildAgree (haltedOf (run2 d3)) keysA adrsA storA acsA ∧
      (haltedOf (run2 d3)).gasLeft = gasA ∧ (haltedOf (run2 d3)).output = [] ∧
      (haltedOf (run2 d3)).error = none := by
  have hk := frame2_kernel d3
  rw [show obsChild3 d3 = d3 from childObs_eq g3 o3 e3'] at hk
  unfold run2 at hk ⊢
  split at hk
  · rename_i c hc
    generalize hr : wrun fs2 e2.sta 2 c = r at hk ⊢
    rcases r with c' | ⟨d | d, cl⟩ | _
    · simp [obs2] at hk
    · simp only [obs2, Option.some.injEq, Prod.mk.injEq, Bool.and_eq_true,
        decide_eq_true_eq] at hk
      obtain ⟨hg, ho, ⟨⟨⟨he, hkk⟩, hka⟩, hks⟩, hkc⟩ := hk
      have herr : d.error = none := Option.isNone_iff_eq_none.mp he
      have hstep := (wrun_cont aCall_eq).trans (callResume_cont hc k3 a3)
      obtain ⟨hok, hag⟩ := childOk_of_start
        (fun hcode hfork hr' => lift_exact Attacker.cert_check Attacker.cert_jumpsOk hcode hfork hr')
        agree_cfg339 fs2_zero start2_eq e2_fork e2_code hstep hr herr
      rw [hkk, hka, hks, hkc] at hag
      exact ⟨hok, hag, hg, List.map_injective_iff.mpr (fun _ _ h => UInt8.toNat_inj.mp h) ho,
        herr⟩
    · simp [obs2] at hk
    · simp [obs2] at hk
  · simp [obs2] at hk

/-- **The attacker's subtree as frame 1's child** (EELS frames 2-4). -/
theorem attacker_child : ChildOk sevm1 cfg339 post2 ∧ ChildAgree post2 keysA adrsA storA acsA ∧
    post2.gasLeft = gasA ∧ post2.output = [] ∧ post2.error = none :=
  let ⟨k3, a3, g3, o3, e3'⟩ := frame3_child
  attacker_of_child post3 k3 a3 g3 o3 e3'

/-- **Frame 1 of the V- witness, closed.**  `remove_liquidity(200, [0, 0], A)` on the
deployed 0x6326 certificate, with its attacker subtree (the reentrant `add_liquidity`
through the proxy) and its token child both run, is a gas-exact run from `pre1` to a
halted machine with the EELS gas and return data `[100, 100]`, whose world has
`totalSupply = 1800 < 1906 = balanceOf[A]` and the remove-lock released, with no error. -/
theorem frame1_closed :
    ∃ post, SProg.RunExact fs1 sevm1 pre1 post ∧ post.gasLeft = 29372882 ∧
      post.output = word 100 ++ word 100 ∧
      (storOf post.state proxyAddress (26 : Nat).toB256).toNat = 1800 ∧
      (storOf post.state proxyAddress balanceOfASlot.toB256).toNat = 1906 ∧
      (storOf post.state proxyAddress (2 : Nat).toB256).toNat = 0 ∧ post.error = none :=
  let ⟨k, a, g, o, e⟩ := attacker_child
  frame1_full post2 g o e k a

end Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Subtree
