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
    ite_true, ite_eq_left, and_true, Ninst.step_reg, Ninst.step_push, Rinst.run, Rinst.runCore,
    St, Devm.setMach, Devm.gasLeft, Devm.stack, Devm.memory, Devm.stateGas, Devm.stack_setMach, Devm.memory_setMach, Devm.gasLeft_setMach,
    Devm.stateGas_setMach, Devm.setMach_setMach, Devm.pop_def, chargeGas_eq_ok,
    Devm.push_eq_ok, gBase, gVerylow, bind, Except.bind, Except.map, Except.map_ok,
    ExceptT.stM_eq, Functor.map, Step.ofExecution, Nat.reduceAdd, Nat.add_sub_cancel, List.cons_ne_nil, if_false, List.length_cons, List.length_nil,
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
    omega
  simp only [callPrep, payoutBoundary, payoutPrepared, St, Devm.stack_setMach,
    Adr.toAdr_toB256, hfork, decide_true, hdepth, and_self, ite_true,
    Devm.setMach_setMach, Devm.memory_setMach, Devm.gasLeft_setMach, Devm.stateGas_setMach,
    hext, hcode, hnonzero, ite_false, hcreate, hn0, hn100, hn640, hng,
    gasCallValue, calculateMsgCallGas, hlow, Nat.add_zero, Nat.sub_zero,
    Nat.min_eq_right hsent, hafford, hstatic, hbal, and_true]

end Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.GeneralizedPrototype
