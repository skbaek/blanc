import Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Reach.AddSetup
import Blanc.Lift.VyperNonreentrantDeployed.Token20.Frame
import Blanc.Lift.VyperNonreentrantDeployed.Fixed.Init.Proxy
import Blanc.Lift.KernelBatchForall

/-! # V− setup, message 6: `T.approve(proxy, 1000)` from the creator

The sixth root message: the code-free `creator` calls the token `tokenAddr` with
`approve(address,uint256)` (selector `0x095ea7b3`) for `(proxyAddr, 1000)`, value 0, 100,000
gas, over any world the shadows `acs6`/`stor5` describe (the world the funding creations settle
to is one: the initialized pool, the implementation's sentinel and the token's
`balanceOf[creator] = 10^6`).  The token runs by its own certificate (`Token20.approve_child`);
the `SSTORE` of the allowance is charged cold and from an original value of zero (the
original state is the input world, whose allowance slot is empty), 22,100, so the call
succeeds with 77,697 gas left and settles to a world `acs6`/`stor6` describe. -/

namespace Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Reach

open Jaune Blanc.Lift Blanc.Lift.Witness Blanc.Lift.NodeWalk Blanc.ConcreteRun Blanc.ForkUniform
open Blanc.Lift.VyperNonreentrantDeployed.Fixed.Init (WorldIs mem_emptyWithCapacity_keys
  mem_emptyWithCapacity_adrs)

/-- The storage shadow of the world the funding creations settle to: the token's mint, the
initialized pool, the implementation's sentinel. -/
def stor5 : StorShadow := ((tokenAddr, creator.toB256), 1000000) :: initWrites ++ stor2

theorem stor6_eq : stor6 = ((tokenAddr, allowCPSlot), 1000) :: stor5 := rfl

/-- The ABI-encoded `approve(proxyAddr, 1000)`. -/
def approveCall : Bytes := [0x09, 0x5e, 0xa7, 0xb3] ++ abiWord proxyAddr.toNat ++ abiWord 1000

/-- Message 6: `creator` calls the token with `approve`, over world `W`. -/
def approveMsg (fork : Fork) (W : State) : Msg :=
  callMsg fork W tokenAddr Token20.code approveCall 100000

def frameP (W : State) : Frame := Frame.ofCall (approveMsg .prague W)

/-- The token frame's entry machine (Prague). -/
def eP (W : State) : Evm := match frameEnterS (frameP W) acs6 with | .run e => e | .done _ => default

/-- The account shadow after the message's (zero) value transfer. -/
def acsP : AcctShadow := acsTransfer (approveMsg .prague world6) acs6

/-- The entry and the static facts of the token frame (kernel evaluations over any `W`). -/
theorem approveFacts : ∀ W : State,
    frameEnterS (frameP W) acs6 = .run (eP W) ∧
    ((eP W).pc, (eP W).sta.code, (eP W).sta.currentTarget, (eP W).sta.isStatic,
      (eP W).dyna.stack, (eP W).dyna.memory.data.toList, (eP W).dyna.memory.size,
      (eP W).dyna.gasLeft) = (0, Token20.code, tokenAddr, false, [], [], 0, 100000) ∧
    (decide (Sevm.selector (eP W).sta = 0x095ea7b3) &&
      decide (Token20.apSlot (eP W).sta = allowCPSlot) &&
      decide (Token20.apVal (eP W).sta = 1000)) = true ∧
    (eP W).dyna.error = none := by
  kernel_forall_rfl_and

theorem acsP_lookup (a : Adr) : lookupA acsP a = lookupA acs6 a := by
  refine lookupA_eq_of_keys (fun b hb => ?_) a
  have hk : acsP.map Prod.fst ++ acs6.map Prod.fst =
      [tokenAddr, creator, attackerAddr, tokenAddr, proxyAddr, implAddr, creator, attackerAddr,
        tokenAddr, proxyAddr, implAddr, creator] := by kernel_rfl
  rw [hk] at hb
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

/-- The allowance slot is not the creator's balance slot (one hash evaluated). -/
theorem allowCPSlot_ne : allowCPSlot ≠ creator.toB256 := by decide +kernel

theorem lookup_stor5_allow : lookupS stor5 tokenAddr allowCPSlot = 0 := by decide +kernel

variable {g : Fork} {W : State}

theorem eP_stat (W : State) : (eP W).sta.benvStat = (frameP W).inner.benv.stat :=
  frameEnterS_stat (approveFacts W).1

theorem frameP_neutral (W : State) : (frameP W).PrecompNeutral :=
  Frame.precompNeutral_of_codeAddress (a := tokenAddr) rfl (by decide) (by decide)

theorem approveMsg_withFork (g : Fork) (W : State) :
    approveMsg g W = (approveMsg .prague W).withFork g := rfl

theorem eP_at (hg : CoveredFork g) :
    frameEnterS ((frameP W).withFork g) acs6 = .run ((eP W).withFork g) := by
  rw [frameEnterS_withFork CoveredFork.prague CoveredFork.prague hg (frameP_neutral W),
    (approveFacts W).1]
  rfl

/-- **Message 6, `approve(proxyAddr, 1000)`, under any covered fork, from any world the shadows
`acs6`/`stor5` describe.** The root call succeeds with 77,697 of its 100,000 gas left (the
allowance `SSTORE` charged 22,100: cold, original and current value zero) and settles to a world
`acs6`/`stor6` describe. -/
theorem approve_message_at (hg : CoveredFork g) (hW : WorldIs W acs6 stor5) :
    ∃ post : Devm, processMessage (approveMsg g W) = .ok post ∧ post.error = none ∧
      post.gasLeft = 77697 ∧ WorldIs post.state acs6 stor6 := by
  obtain ⟨-, hst, hdec, herr⟩ := approveFacts W
  simp only [Prod.mk.injEq] at hst
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hdec
  obtain ⟨⟨hsel, hslot⟩, hval⟩ := hdec
  obtain ⟨hpc, hcode, hct, hstatic, hstack, hmemd, hmems, hgas⟩ := hst
  set sevm := (eP W).sta.withFork g with hsevm
  set c : PCfg := childCfg ((eP W).withFork g) ((frameP W).withFork g) [] [] stor5 acs6 with hc
  have hag : PAgree c := frameStart_agree .undefined (eP_at hg) mem_emptyWithCapacity_keys
    mem_emptyWithCapacity_adrs hW.2 hW.1
  have horig : getOrigStorVal sevm tokenAddr allowCPSlot = 0 := by
    show ((eP W).sta.benvStat.origState.get tokenAddr).stor.get allowCPSlot = 0
    rw [eP_stat]
    exact (hW.2 tokenAddr allowCPSlot).trans lookup_stor5_allow
  have hmem : c.devm.memory = Mem.empty := by
    show (eP W).dyna.memory = _
    rcases hm : (eP W).dyna.memory with ⟨data, size⟩
    rw [hm] at hmemd hmems
    simp only at hmemd hmems
    subst hmems
    rw [Array.toList_eq_nil_iff.mp hmemd]
    rfl
  have hgasS : c.devm.gasLeft = 77697 + Token20.approveGasS sevm c.keys c.stor := by
    show (eP W).dyna.gasLeft = 77697 + (203 + sstoreCostS sevm [] stor5 (Token20.apSlot sevm)
      (Token20.apVal sevm))
    have hs : Token20.apSlot sevm = allowCPSlot := hslot
    have hv : Token20.apVal sevm = 1000 := hval
    have hct' : sevm.currentTarget = tokenAddr := hct
    rw [hgas, hs, hv]
    unfold sstoreCostS
    rw [hct', horig, lookup_stor5_allow]
    decide
  obtain ⟨hca, hall⟩ := Token20.approve_child (sevm := sevm) (c := c) (G := 77697) hcode hg
    hstatic hsel hpc hstack hmem hag hgasS (by decide)
  -- the frame's execution
  obtain ⟨R⟩ := (exec_iff_exec_eq 0 sevm (eP W).dyna _).mpr rfl
  have hn : NodeAt sevm c ⟨0, sevm, (eP W).dyna, _, R⟩ := ⟨hpc.symm, rfl, rfl⟩
  have hex := (hall _ hn).1
  have hpost_err : (Token20.approvePostS sevm c 77697).error = none := herr
  have hent : (Frame.ofCall (approveMsg g W)).enter = .run ((eP W).withFork g) := by
    rw [approveMsg_withFork]
    show ((frameP W).withFork g).enter = _
    rw [frame_enter_eq_B, frameEnterB_eq_S (acs := acs6) hW.1]
    exact eP_at hg
  refine ⟨Token20.approvePostS sevm c 77697, ?_, hpost_err, rfl, fun a => ?_, fun a k => ?_⟩
  · rw [MessageExecution.processMessage_eq_settle_exec_of_enter _ _ hent]
    have hexec : exec ((eP W).withFork g) = .ok (Token20.approvePostS sevm c 77697) := by
      have h0 : (eP W).withFork g = ⟨0, sevm, (eP W).dyna⟩ := by
        show (⟨(eP W).pc, sevm, (eP W).dyna⟩ : Evm) = _
        rw [hpc]
      rw [h0]; exact hex
    rw [hexec]
    exact frame_settle_ok rfl (CoveredFork.rules_stateGas_none (s := (rootBenv g W).stat) hg)
      hpost_err
  · rw [hca.2.2.2 a]
    exact acsP_lookup a
  · rw [hca.2.2.1 a k, stor6_eq]
    show lookupS (((sevm.currentTarget, Token20.apSlot sevm), Token20.apVal sevm) :: stor5) a k = _
    rw [show sevm.currentTarget = tokenAddr from hct, show Token20.apSlot sevm = allowCPSlot from hslot,
      show Token20.apVal sevm = 1000 from hval]

end Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Reach
