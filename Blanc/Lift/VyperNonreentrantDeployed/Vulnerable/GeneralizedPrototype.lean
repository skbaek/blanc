import Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Frame1
import Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Reach.ViolBoundary
import Blanc.Lift.ExactWalkCutOps
import Blanc.Lift.NodeWalk

/-! A bounded rehearsal of the shared Vyper ETH-payout boundary. No headline is retired. -/
namespace Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.GeneralizedPrototype

open Jaune Blanc Blanc.Lift Blanc.Lift.Witness Blanc.Lift.NodeWalk

def payoutCall : SFunc :=
  .next (.exec .call) (.next (.reg .iszero) (.next (.push [0x44, 0x7a] (by decide))
    (.branch t_1c73_c23 t_447a_c23)))

def payoutEntry (b : Devm) (M : Mem) (G : Nat) (x y : B256) (S : List B256)
    (keys : List (Adr × B256)) (adrs : List Adr) (stor : StorShadow) (acs : AcctShadow) : Cfg :=
  ⟨St b (x :: y :: S) M (G + 33), t_1c57_c23, [], keys, adrs, stor, acs⟩

def payoutBoundary (b : Devm) (M : Mem) (G : Nat) (A : Adr) (S : List B256)
    (keys : List (Adr × B256)) (adrs : List Adr) (stor : StorShadow) (acs : AcctShadow) : Cfg :=
  ⟨St b (G.toB256 :: A.toB256 :: 100 :: 640 :: 0 :: 0 :: 0 :: S) M G,
    payoutCall, [], keys, adrs, stor, acs⟩

/-- The twelve real Vyper instructions prepare the ETH CALL with arbitrary remaining gas
and recipient. Memory and stack hypotheses are entry facts, not a successful-run premise. -/
theorem payout_suffix (s : Sevm) (b : Devm) (M : Mem) (G : Nat) (A : Adr)
    (x y : B256) (S : List B256) (keys : List (Adr × B256)) (adrs : List Adr)
    (stor : StorShadow) (acs : AcctShadow)
    (hroom : S.length + 7 < 1024)
    (hread0 : Bytes.toB256 (M.read 608 32).1 = 0)
    (hread100 : Bytes.toB256 (M.read 512 32).1 = 100)
    (hreadA : Bytes.toB256 (M.read 320 32).1 = A.toB256)
    (hmem : ∀ i ∈ [608, 512, 320], (M.read i 32).2 = M)
    (hcost : ∀ i ∈ [608, 512, 320], (St b [] M 0).extCost [⟨i, 32⟩] = 0) :
    wrun (Cert.prog cert) s 12 (payoutEntry b M G x y S keys adrs stor acs) =
      .cont (payoutBoundary b M G A S keys adrs stor acs) := by
  unfold payoutEntry payoutBoundary
  have hm0 := hmem 608 (by decide)
  have hm1 := hmem 512 (by decide)
  have hm2 := hmem 320 (by decide)
  have hc0 := hcost 608 (by decide)
  have hc1 := hcost 512 (by decide)
  have hc2 := hcost 320 (by decide)
  have hw0 : Bytes.toB256 [0] = 0 := rfl
  have hw608 : Bytes.toB256 [2, 96] = 608 := rfl
  have hw640 : Bytes.toB256 [2, 128] = 640 := rfl
  have hw512 : Bytes.toB256 [2, 0] = 512 := rfl
  have hw320 : Bytes.toB256 [1, 64] = 320 := rfl
  have hn608 : (608 : B256).toNat = 608 := rfl
  have hn512 : (512 : B256).toNat = 512 := rfl
  have hn320 : (320 : B256).toNat = 320 := rfl
  simp only [St, Devm.extCost, Devm.memory_setMach] at hc0 hc1 hc2
  change M.extend 608 32 = M at hm0
  change M.extend 512 32 = M at hm1
  change M.extend 320 32 = M at hm2
  simp only [Mem.read, array_sliceD_eq_list] at hread0 hread100 hreadA
  have hl0 : 3 ≤ G + 33 - 2 - 2 - 3 - 3 - 3 ∧ S.length + 1 + 1 < 1024 := by
    constructor <;> omega
  have hl1 : 3 ≤ G + 33 - 2 - 2 - 3 - 3 - 3 - 3 - 3 - 3 ∧
      S.length + 1 + 1 + 1 + 1 < 1024 := by constructor <;> omega
  have hl2 : 3 ≤ G + 33 - 2 - 2 - 3 - 3 - 3 - 3 - 3 - 3 - 3 - 3 ∧
      S.length + 1 + 1 + 1 + 1 + 1 < 1024 := by constructor <;> omega
  have hgas : G + 33 - 2 - 2 - 3 - 3 - 3 - 3 - 3 - 3 - 3 - 3 - 3 - 2 = G := by omega
  simp (disch := simp only [Devm.gasLeft, Devm.stack, Devm.setMach, List.length_cons]; first | omega | constructor <;> omega) only [wrun, wstep, t_1c57_c23, ninstAccKeeps, rinstAccKeeps,
    ite_true, and_true, Ninst.step_reg, Ninst.step_push, Rinst.run, Rinst.runCore,
    St, Devm.setMach, Devm.gasLeft, Devm.stack, Devm.memory, Devm.stateGas,
    Devm.pop_def, chargeGas_eq_ok,
    Devm.push_eq_ok, gBase, gVerylow, bind, Except.bind, Except.map_ok,
    Step.ofExecution, Nat.reduceAdd, List.cons_ne_nil, ite_false, List.length_cons, List.length_nil,
    Nat.zero_add, hw0, hw608, hw640, hw512, hw320, mloadStep, Devm.extCost,
    hn608, hn512, hn320, hc0, hc1, hc2, hm0, hm1, hm2, hread0, hread100, hreadA, hl0, hl1, hl2, hgas, payoutCall]

/-- The recipient code and environments remain parameters; the EIP-150 split is explicit. -/
def payoutPrepared (s : Sevm) (b : Devm) (M : Mem) (G : Nat) (A : Adr) (S : List B256)
    (adrs : List Adr) (acs : AcctShadow) : CallPrep :=
  let extra := accessCostL A adrs + gasCallValue
  let sent := except64th (G - extra)
  let p := callSpawnParent (addAccessedAddress (St b S M G) A) (sent + extra) 640 0 0 0
  ⟨Frame.ofCall (valueCallSpawnMsg s p (sent + gCallStipend) 100 A A 640 0
    (lookupA acs A).code false), p, 0, 0, A :: adrs⟩

theorem payout_prepare (s : Sevm) (b : Devm) (M : Mem) (G : Nat) (A : Adr)
    (S : List B256) (keys : List (Adr × B256)) (adrs : List Adr)
    (stor : StorShadow) (acs : AcctShadow)
    (hfork : CoveredFork s.benvStat.fork) (hdepth : s.depth ≠ 0)
    (hstatic : s.isStatic = false) (hbound : G < 2 ^ 256) (hgas : 11600 ≤ G)
    (hacc : accessCostL A adrs ≤ 2600) (hcreate : createCostS acs A = 0)
    (hcode : getDelegatedCodeAddress (lookupA acs A).code = none)
    (hbal : ¬ (lookupA acs s.currentTarget).bal < (100 : B256))
    (hext : (St b S M G).extCost [⟨640, 0⟩, ⟨0, 0⟩] = 0) :
    callPrep s (payoutBoundary b M G A S keys adrs stor acs) =
      some (payoutPrepared s b M G A S adrs acs) := by
  have hn0 : (0 : B256).toNat = 0 := rfl
  have hn100 : (100 : B256).toNat = 100 := rfl
  have hn640 : (640 : B256).toNat = 640 := rfl
  have hnonzero : (100 : B256) ≠ 0 := by decide
  have hng := B256.toNat_toB256_of_lt hbound
  have hlow : ¬ G < accessCostL A adrs + 9000 + 0 := by omega
  have hsent : except64th (G - (accessCostL A adrs + 9000)) ≤ G := by
    unfold except64th
    omega
  have hafford : except64th (G - (accessCostL A adrs + 9000)) +
      (accessCostL A adrs + 9000) ≤ G := by
    unfold except64th
    calc
      _ ≤ (G - (accessCostL A adrs + 9000)) + (accessCostL A adrs + 9000) :=
        Nat.add_le_add_right (Nat.sub_le _ _) _
      _ = G := Nat.sub_add_cancel (Nat.le_of_not_gt hlow)
  have hda : (addAccessedAddress (St b S M G) A).gasLeft = G := rfl
  simp only [St, Devm.extCost, Devm.memory_setMach] at hext
  simp only [St, Devm.stateGas, Devm.setMach, Devm.gasLeft] at hda
  simp only [Nat.add_zero] at hlow
  have hv : ¬ (100 : Nat) = 0 := by decide
  simp only [callPrep, payoutBoundary, payoutPrepared, St, Devm.stack, Devm.memory,
    Devm.gasLeft, Devm.extCost, Devm.setMach,
    toAdr_toB256, hfork, decide_true, ite_eq_left hdepth, and_self, ite_true, true_and, not_false_eq_true,
    hext, hcode, hnonzero, ite_false, hcreate, hn0, hn100, hn640, hng,
    gasCallValue, calculateMsgCallGas, hlow, Nat.add_zero, Nat.sub_zero,
    Nat.min_eq_right hsent, hafford, hstatic, hbal, hda, Devm.stateGas, hv]

open Blanc.ConcreteRun

/-- The existing old fixture's actual remove prefix, stopped before the shared suffix. -/
def old327 : Cfg :=
  match wrun (Cert.prog cert) Frame1.sevm1 327 Frame1.c0 with
  | .cont c => c
  | _ => Frame1.c0

/-- The existing reachable fixture's selected remove boundary, with its frozen shadows. -/
def new0 : Cfg := Boundary.cfgOf1 Reach.Viol.bRm0
  (Reach.Viol.rootEvm Reach.Viol.worldR).dyna.meta
  (Reach.Viol.rootEvm Reach.Viol.worldR).dyna.world

def new327 : Cfg :=
  match wrun (Cert.prog cert) Reach.Viol.sRm 327 new0 with
  | .cont c => c
  | _ => new0

theorem old327_shape : old327 =
    payoutEntry old327.devm old327.devm.memory (old327.devm.gasLeft - 33)
      (old327.devm.stack.getD 0 0) (old327.devm.stack.getD 1 0)
      (old327.devm.stack.drop 2) old327.keys old327.adrs old327.stor old327.acs := by
  kernel_rfl

theorem new327_shape : new327 =
    payoutEntry new327.devm new327.devm.memory (new327.devm.gasLeft - 33)
      (new327.devm.stack.getD 0 0) (new327.devm.stack.getD 1 0)
      (new327.devm.stack.drop 2) new327.keys new327.adrs new327.stor new327.acs := by
  kernel_rfl

/-- The finite entry reads and affordability inputs consumed by the two shared proofs. -/
def payoutInputs (s : Sevm) (c : Cfg) (A : Adr) :=
  let M := c.devm.memory
  let G := c.devm.gasLeft - 33
  let S := c.devm.stack.drop 2
  (decide (S.length + 7 < 1024), Bytes.toB256 (M.read 608 32).1,
    Bytes.toB256 (M.read 512 32).1, Bytes.toB256 (M.read 320 32).1,
    (M.read 608 32).2, (M.read 512 32).2, (M.read 320 32).2,
    (St c.devm [] M 0).extCost [⟨608, 32⟩],
    (St c.devm [] M 0).extCost [⟨512, 32⟩],
    (St c.devm [] M 0).extCost [⟨320, 32⟩],
    decide (G < 2 ^ 256), decide (11600 ≤ G), decide (accessCostL A c.adrs ≤ 2600),
    createCostS c.acs A, getDelegatedCodeAddress (lookupA c.acs A).code,
    decide (¬ (lookupA c.acs s.currentTarget).bal < (100 : B256)),
    (St c.devm S M G).extCost [⟨640, 0⟩, ⟨0, 0⟩])

private theorem old_inputs : payoutInputs Frame1.sevm1 old327 Frame1.attackerAddress =
    (true, 0, 100, Frame1.attackerAddress.toB256,
      old327.devm.memory, old327.devm.memory, old327.devm.memory,
      0, 0, 0, true, true, true, 0, none, true, 0) := by
  kernel_rfl

private theorem new_inputs : payoutInputs Reach.Viol.sRm new327 Reach.attackerAddr =
    (true, 0, 100, Reach.attackerAddr.toB256,
      new327.devm.memory, new327.devm.memory, new327.devm.memory,
      0, 0, 0, true, true, true, 0, none, true, 0) := by
  kernel_rfl

def payoutSegment (s : Sevm) (c : Cfg) (A : Adr) : Prop :=
  let G := c.devm.gasLeft - 33
  let S := c.devm.stack.drop 2
  let next := payoutBoundary c.devm c.devm.memory G A S c.keys c.adrs c.stor c.acs
  wrun (Cert.prog cert) s 12 c = .cont next ∧
    callPrep s next = some (payoutPrepared s c.devm c.devm.memory G A S c.adrs c.acs)

theorem payout_segment (s : Sevm) (c : Cfg) (A : Adr)
    (hshape : c = payoutEntry c.devm c.devm.memory (c.devm.gasLeft - 33)
      (c.devm.stack.getD 0 0) (c.devm.stack.getD 1 0)
      (c.devm.stack.drop 2) c.keys c.adrs c.stor c.acs)
    (hin : payoutInputs s c A =
      (true, 0, 100, A.toB256, c.devm.memory, c.devm.memory, c.devm.memory,
        0, 0, 0, true, true, true, 0, none, true, 0))
    (hfork : CoveredFork s.benvStat.fork) (hdepth : s.depth ≠ 0)
    (hstatic : s.isStatic = false) : payoutSegment s c A := by
  simp only [payoutInputs, Prod.mk.injEq] at hin
  rcases hin with ⟨hroom, hr0, hr100, hrA, hm0, hm1, hm2, hc0, hc1, hc2,
    hbound, hgas, hacc, hcreate, hcode, hbal, hext⟩
  have hm : ∀ i ∈ [608, 512, 320], (c.devm.memory.read i 32).2 = c.devm.memory := by
    intro i hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with h | h | h
    · subst i; exact hm0
    · subst i; exact hm1
    · subst i; exact hm2
  have hc : ∀ i ∈ [608, 512, 320],
      (St c.devm [] c.devm.memory 0).extCost [⟨i, 32⟩] = 0 := by
    intro i hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with h | h | h
    · subst i; exact hc0
    · subst i; exact hc1
    · subst i; exact hc2
  constructor
  · calc
      wrun (Cert.prog cert) s 12 c =
        wrun (Cert.prog cert) s 12 (payoutEntry c.devm c.devm.memory (c.devm.gasLeft - 33)
          (c.devm.stack.getD 0 0) (c.devm.stack.getD 1 0)
          (c.devm.stack.drop 2) c.keys c.adrs c.stor c.acs) :=
        congrArg (wrun (Cert.prog cert) s 12) hshape
      _ = _ := payout_suffix s c.devm c.devm.memory (c.devm.gasLeft - 33) A
        (c.devm.stack.getD 0 0) (c.devm.stack.getD 1 0)
        (c.devm.stack.drop 2) c.keys c.adrs c.stor c.acs
        (of_decide_eq_true hroom) hr0 hr100 hrA hm hc
  · exact payout_prepare s c.devm c.devm.memory (c.devm.gasLeft - 33) A
      (c.devm.stack.drop 2) c.keys c.adrs c.stor c.acs hfork hdepth hstatic
      (of_decide_eq_true hbound) (of_decide_eq_true hgas) (of_decide_eq_true hacc)
      hcreate hcode (of_decide_eq_true hbal) hext

theorem old_instance : payoutSegment Frame1.sevm1 old327 Frame1.attackerAddress :=
  payout_segment Frame1.sevm1 old327 Frame1.attackerAddress old327_shape old_inputs
    (by decide) (by decide) (by rfl)

theorem new_instance : payoutSegment Reach.Viol.sRm new327 Reach.attackerAddr :=
  payout_segment Reach.Viol.sRm new327 Reach.attackerAddr new327_shape new_inputs
    (by decide) (by decide) (by rfl)

/-- Exact budgets and cold access charges at the existing fixture suffix entries. -/
theorem payout_budgets :
    (old327.devm.gasLeft, new327.devm.gasLeft,
      accessCostL Frame1.attackerAddress old327.adrs, accessCostL Reach.attackerAddr new327.adrs,
      (old327.devm.stack.drop 2).length, (new327.devm.stack.drop 2).length) =
    (29495593, 930704, 2600, 2600, 3, 3) := by
  kernel_rfl

/-- The old selected entry is obtained from its existing fixture prefix. -/
theorem old_prefix : wrun (Cert.prog cert) Frame1.sevm1 327 Frame1.c0 = .cont old327 := by
  kernel_rfl

/-- The new selected entry is obtained from its existing frozen pool boundary. -/
theorem new_prefix : wrun (Cert.prog cert) Reach.Viol.sRm 327 new0 = .cont new327 := by
  kernel_rfl

/-- The old full prefix reaches its CALL through the shared twelve-step derivation. -/
theorem old339 : wrun (Cert.prog cert) Frame1.sevm1 339 Frame1.c0 =
    .cont (payoutBoundary old327.devm old327.devm.memory (old327.devm.gasLeft - 33)
      Frame1.attackerAddress (old327.devm.stack.drop 2)
      old327.keys old327.adrs old327.stor old327.acs) := by
  rw [show 339 = 327 + 12 from rfl, wrun_add, old_prefix]
  exact old_instance.1

/-- The new full pool prefix uses the same derivation at its CALL boundary. -/
theorem new339 : wrun (Cert.prog cert) Reach.Viol.sRm 339 new0 =
    .cont (payoutBoundary new327.devm new327.devm.memory (new327.devm.gasLeft - 33)
      Reach.attackerAddr (new327.devm.stack.drop 2)
      new327.keys new327.adrs new327.stor new327.acs) := by
  rw [show 339 = 327 + 12 from rfl, wrun_add, new_prefix]
  exact new_instance.1

end Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.GeneralizedPrototype
