import Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Locks
import Blanc.Lift.WitnessSpawn

/-!
# V-: the deployed Vyper 0.2.15 pool's cross-function reentrancy, executed

The final theorem of the V- witness (`vminus_witness`).  Prague semantics: a constructed
execution of Jaune's interpreter from an explicit pre-state, not a replay of a historical
transaction.

The frame-level form (master decision `vminus-statement-form-20260928`, option B): every
frame of the nested execution is named by the machine it enters with, each spawn is a Jaune
step (`SpawnedBy`: `Xinst.step` spawns a frame whose `Frame.enter` is that machine), and each
frame whose code is lifted runs by its certificate, whose run is an `Exec` of the real bytes
(`lift_exactM`).  Points inside a lifted frame (frame 1 at its `CALL`, frame 4 in its body)
are named by the certificate interpreter's configuration (`wrun`), whose shadows agree with
the real machine (`Agree`).  The node-quantified form (a counterexample to the literal V+
exclusion over `Exec.Deriv` nodes) needs a node-exposing lift and is not attempted here.

Limits: the top-level caller `A` holds code (`attackerCode`), so under EIP-3607 this exact
message is a valid `processMessage` witness but not the first frame of a valid transaction
(a transaction from an account with code is rejected); the witness is about message
execution, not transaction admission.
-/

namespace Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Top

open Jaune Blanc.Lift Blanc.Lift.Witness Blanc.Lift.Witness.Boundary Blanc.ConcreteRun
open Blanc.Lift.VyperNonreentrantDeployed Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Frame1
open Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Subtree

attribute [local irreducible] e0 cp1 cfg339 e2 cc2 aCall cp3 e3 cp4 e4 post4

/-! ### Frame 0 -/

theorem acctAgree_world0 : AcctAgree world0 acs0 := c0_agree.2.2.2

theorem f0_enter : f0.enter = .run e0 := by
  rw [frame_enter_eq_B, frameEnterB_eq_S (acs := acs0) acctAgree_world0]; exact e0_eq

theorem e0_meta : ∃ benv, benvAfterTransferS msg0 acs0 = .ok benv ∧
    e0 = initEvm (msg0.withBenv benv) :=
  frameEnterS_run e0_eq

theorem e0_adrs : ∀ a, a ∈ e0_31.dyna.accessedAddresses ↔ a ∈ ([] : List Adr) := by
  obtain ⟨benv, -, he⟩ := e0_meta
  intro a
  show a ∈ e0.dyna.accessedAddresses ↔ _
  rw [he]
  show a ∈ (Std.HashSet.emptyWithCapacity : AdrSet) ↔ _
  simp only [Std.HashSet.not_mem_emptyWithCapacity, List.not_mem_nil]

theorem e0_world : AcctAgree e0_31.dyna.state acs00 := by
  obtain ⟨benv, hb, he⟩ := e0_meta
  show AcctAgree e0.dyna.state _
  rw [he]
  exact acctAgree_transfer acctAgree_world0 hb

theorem e0_code : e0.sta.code = proxyCode := by
  have h := e0_facts
  simp only [Prod.mk.injEq] at h
  exact h.2.1

theorem cp1_spec :
    Xinst.step e0_31.sta e0_31.dyna .delegatecall = .spawn cp1.f (.call cp1.p cp1.oi cp1.os) ∧
      (∀ a, a ∈ cp1.p.accessedAddresses ↔ a ∈ cp1.adrs) ∧
      cp1.p.accessedStorageKeys = e0_31.dyna.accessedStorageKeys ∧
      cp1.f.isCreate = false ∧ cp1.f.inner.accessedAddresses = cp1.p.accessedAddresses ∧
      cp1.f.inner.accessedStorageKeys = cp1.p.accessedStorageKeys ∧
      cp1.f.inner.benv.stat.rules.stateGas = none ∧ cp1.f.inner.benv.state = e0_31.dyna.state ∧
      cp1.p.state = e0_31.dyna.state :=
  dcallPrep_spec cp1_eq e0_adrs e0_world

theorem spawn0 : Evm.step e0_31 = .spawn cp1.f (.call cp1.p cp1.oi cp1.os) 32 := by
  have hat : Ninst.At e0_31.sta.code 31 (.exec .delegatecall) := by
    rw [show e0_31.sta = e0.sta from rfl, e0_code]; exact proxy_at_delegatecall
  show Evm.step ⟨31, e0_31.sta, e0_31.dyna⟩ = _
  rw [Evm.step_next hat, Ninst.step_exec, cp1_spec.1]
  rfl

theorem enter1 : cp1.f.enter = .run ⟨0, sevm1, pre1⟩ := by
  rw [frame_enter_eq_B, frameEnterB_eq_S (by rw [cp1_spec.2.2.2.2.2.2.2.1]; exact e0_world)]
  exact e1_eq

theorem spawnedBy1 : SpawnedBy e0_31.sta e0_31.dyna .delegatecall ⟨0, sevm1, pre1⟩ :=
  spawnedBy_of_dcallPrep cp1_eq e0_adrs e0_world e1_eq

/-- **The top-level message call.**  From any settled frame 1 with its observed gas, return
data and success, the top-level frame is an `Exec` from the machine the message enters with,
Jaune's `processMessage` returns its settled machine, and that machine has frame 1's world. -/
theorem frame0_of_child (post1 : Devm) (hx1 : Nonempty (Exec 0 sevm1 pre1 (.ok post1)))
    (hg1 : post1.gasLeft = 29372882) (ho1 : post1.output = word 100 ++ word 100)
    (he1 : post1.error = none) :
    Nonempty (Exec e0.pc e0.sta e0.dyna (.ok (post0F post1))) ∧
      processMessage msg0 = .ok (post0F post1) ∧ (post0F post1).error = none ∧
      (post0F post1).gasLeft = 29841551 ∧ (post0F post1).output = word 100 ++ word 100 ∧
      (post0F post1).state = post1.state := by
  have hobs : obsChild1 post1 = post1 := childObs_eq hg1 ho1 he1
  have hr := resume0_eq post1
  have ht := tail0_eq post1
  have hh := return0_eq post1
  have hob := post0_obs post1
  have hk := post0_keep post1
  rw [hobs] at hr ht hh hob hk
  simp only [Prod.mk.injEq] at hob
  obtain ⟨hg0, ho0, he0⟩ := hob
  have he0' : (post0F post1).error = none := Option.isNone_iff_eq_none.mp he0
  obtain ⟨-, -, -, hcr, -, -, hsg, -, -⟩ := cp1_spec
  have hsettle : Resume.run (.call cp1.p cp1.oi cp1.os) (cp1.f.settle (.ok post1)) =
      .ok (d02 post1) := by
    rw [frame_settle_ok hcr hsg he1]; exact resumeCallB_sound hr
  have hx0 : Nonempty (Exec e0.pc e0.sta e0.dyna (.ok (post0F post1))) :=
    exec_of_stepN_spawn_runOk prefix0 spawn0 enter1 hx1 hsettle (exec_of_stepN_halt ht hh)
  have hex := (exec_iff_exec_eq _ _ _ _).mp hx0
  refine ⟨hx0, ?_, he0', hg0,
    List.map_injective_iff.mpr (fun _ _ h => UInt8.toNat_inj.mp h) ho0,
    hk.trans (resumeCallB_state hr)⟩
  have hsg0 : f0.inner.benv.stat.rules.stateGas = none := rfl
  show runFrame f0 = _
  unfold runFrame
  rw [f0_enter]
  show f0.settle (exec ⟨e0.pc, e0.sta, e0.dyna⟩) = _
  rw [hex]
  exact frame_settle_ok rfl hsg0 he0'

/-! ### The final theorem -/

/-- **V- (Prague semantics): the deployed Vyper 0.2.15 pool admits `add_liquidity` reentered
from inside `remove_liquidity`, and the reentry breaks its LP ledger.**

The explicit pre-state (`msg0`, `world0`; nothing about the outcome is assumed): the pool
`P` is the 45-byte proxy (`proxyCode`) with 1000 wei and the storage of the preflight table
(both locks 0, `balances = [1000, 1000]`, `totalSupply = balanceOf[A] = 2000`, coin 1 the
token `T`); the implementation account holds the deployed 17,535-byte runtime (`code`); the
attacker `A` and the token `T` hold the explicit bytes `attackerCode` (85 bytes) and
`tokenCode` (30 bytes); `A` sends `P` the top-level message `remove_liquidity(200, [0, 0], A)`
with value 0 and 30,000,000 gas, under Prague (`CoveredFork`).

Then:
* the top-level message call succeeds: its frame is an `Exec` from the machine the message
  enters with (`Frame.enter`), and Jaune's `processMessage` returns that settled machine;
* (a) frame 1, spawned by the proxy's `DELEGATECALL`, is `P` (storage owner) running the
  implementation's `remove_liquidity`; it takes the remove-lock (slot 2 goes from 0 to 1)
  and, holding it, `CALL`s `A`; `A`'s frame `CALL`s `P`; that proxy frame's `DELEGATECALL`
  spawns frame 4, which is again `P` running the implementation, now with the calldata of
  `add_liquidity([100, 0], 0, A)`, entered while slot 2 = 1; frame 4 is an `Exec` of the
  real bytes, and its certificate run reaches the body of `add_liquidity` (node
  `t_0370_c63`, pc 0x370, past its guard) with its own lock taken (slot 0 = 1) while slot 2
  is still 1; it mints to `A` (`balanceOf[A] = 2106`) and releases slot 0;
* (b) the two guards are on different slots: `remove_liquidity`'s bytes guard slot 2
  (pcs 6900-6911, released at 7788-7792) and `add_liquidity`'s guard slot 0 (pcs 88-99,
  released at 2017-2021), so the held remove-lock never stops the reentry (the defect);
  frame 1 releases slot 2 at its exit;
* (c) the final state breaks the ledger: `totalSupply = 1800 < 1906 = balanceOf[A]`. -/
theorem vminus_witness :
    ∃ post0 post1 : Devm,
      -- the top-level message call, Prague
      msg0.benv.stat.fork = .prague ∧ CoveredFork msg0.benv.stat.fork ∧
      f0.enter = .run e0 ∧ Nonempty (Exec e0.pc e0.sta e0.dyna (.ok post0)) ∧
      processMessage msg0 = .ok post0 ∧ post0.error = none ∧
      post0.output = word 100 ++ word 100 ∧
      -- (a) frame 1: `P` running the implementation's `remove_liquidity`, spawned by the proxy
      stepN 11 e0 = some e0_31 ∧ SpawnedBy e0_31.sta e0_31.dyna .delegatecall ⟨0, sevm1, pre1⟩ ∧
      sevm1.currentTarget = proxyAddress ∧ sevm1.code = code ∧ sevm1.data = removeCalldata ∧
      Nonempty (Exec 0 sevm1 pre1 (.ok post1)) ∧ post1.error = none ∧
      -- frame 1 takes slot 2 and calls `A` holding it
      storOf pre1.state proxyAddress (2 : Nat).toB256 = 0 ∧
      wrun fs1 sevm1 339 c0 = .cont cfg339 ∧ Agree cfg339 ∧
      storOf cfg339.devm.state proxyAddress (2 : Nat).toB256 = (1 : Nat).toB256 ∧
      SpawnedBy sevm1 cfg339.devm .call e2 ∧
      e2.sta.currentTarget = attackerAddress ∧ e2.sta.code = attackerCode ∧
      -- `A` calls `P`; the proxy delegates to the implementation: frame 4
      wrun fs2 e2.sta 24 cc2 = .cont aCall ∧ SpawnedBy e2.sta aCall.devm .call e3 ∧
      e3.sta.currentTarget = proxyAddress ∧ e3.sta.code = proxyCode ∧
      stepN 11 e3 = some e31 ∧ SpawnedBy e31.sta e31.dyna .delegatecall e4 ∧
      e4.sta.currentTarget = proxyAddress ∧ e4.sta.code = code ∧ e4.sta.data = addCalldata ∧
      -- frame 4 is entered while slot 2 = 1, its own lock (slot 0) free
      storOf e4.dyna.state proxyAddress (2 : Nat).toB256 = (1 : Nat).toB256 ∧
      storOf e4.dyna.state proxyAddress (0 : Nat).toB256 = 0 ∧
      Nonempty (Exec e4.pc e4.sta e4.dyna (.ok post4)) ∧
      -- frame 4 reaches `add_liquidity`'s body with slot 0 taken and slot 2 still held
      (∃ cB : Cfg, wrun fs1 e4.sta 2625 c4 = .cont cB ∧ Agree cB ∧ cB.f = t_0370_c63 ∧
        storOf cB.devm.state proxyAddress (0 : Nat).toB256 = (1 : Nat).toB256 ∧
        storOf cB.devm.state proxyAddress (2 : Nat).toB256 = (1 : Nat).toB256) ∧
      (storOf post4.state proxyAddress balanceOfASlot.toB256).toNat = 2106 ∧
      storOf post4.state proxyAddress (0 : Nat).toB256 = 0 ∧
      -- (b) the two guards in the deployed bytes: slot 2 and slot 0
      (code.getInst 6900 = some (.next (.push [0x02] (by decide))) ∧
        code.getInst 6902 = some (.next (.reg .sload)) ∧
        code.getInst 6911 = some (.next (.reg .sstore))) ∧
      (code.getInst 88 = some (.next (.push [0x00] (by decide))) ∧
        code.getInst 90 = some (.next (.reg .sload)) ∧
        code.getInst 99 = some (.next (.reg .sstore))) ∧
      (storOf post1.state proxyAddress (2 : Nat).toB256).toNat = 0 ∧
      -- (c) the harm
      (storOf post0.state proxyAddress (26 : Nat).toB256).toNat = 1800 ∧
      (storOf post0.state proxyAddress balanceOfASlot.toB256).toNat = 1906 ∧
      (storOf post0.state proxyAddress (26 : Nat).toB256).toNat <
        (storOf post0.state proxyAddress balanceOfASlot.toB256).toNat := by
  obtain ⟨post1, hrun1, hg1, ho1, h26, hA, h2, he1⟩ := frame1_closed
  have hx1 : Nonempty (Exec 0 sevm1 pre1 (.ok post1)) :=
    lift_exactM cert_checkM cert_jumpsOkM rfl CoveredFork.prague hrun1
  obtain ⟨hx0, hpm, he0, -, ho0, hst0⟩ := frame0_of_child post1 hx1 hg1 ho1 he1
  -- frame 4's entry agreement
  obtain ⟨-, hpa, hpk, -, hia, hik, -, hst, -⟩ := cp4_spec
  have hag4 : Agree c4 := frameStart_agree t_0000_c0 e4_eq
    (fun x => by rw [hik, hpk, e31_keys]; exact e3_keys x) (fun a => by rw [hia]; exact hpa a)
    (fun a k => by rw [hst, e31_state]; exact e3_world.1 a k)
    (by rw [hst, e31_state]; exact e3_world.2)
  obtain ⟨hx4, -, ha4⟩ := frame4_child
  have hsub := subtree_facts
  simp only [Prod.mk.injEq] at hsub
  obtain ⟨h2t, h2c, -, h3t, -, -, -, h4t, -, h4d, hl2, hl0⟩ := hsub
  have hrg := remove_guard_bytes
  have hag := add_guard_bytes
  simp only [Prod.mk.injEq] at hrg hag
  -- the body boundary
  have hB : ∃ cB : Cfg, wrun fs1 e4.sta 2625 c4 = .cont cB ∧ Agree cB ∧ cB.f = t_0370_c63 ∧
      storOf cB.devm.state proxyAddress (0 : Nat).toB256 = (1 : Nat).toB256 ∧
      storOf cB.devm.state proxyAddress (2 : Nat).toB256 = (1 : Nat).toB256 := by
    have hA' := chunkA.1
    have hT := chunkA.2
    generalize hr : wrun fs1 e4.sta 2625 c4 = r at hA' hT
    rcases r with c | _ | _
    · have hc : c = cfgB c.devm.meta c.devm.world := cfg_of_obsB hA' rfl (atdClean_cont.mp hT)
      have hagc : Agree c := (wrun_cont hr).1 hag4
      refine ⟨c, rfl, hagc, (congrArg Cfg.f hc).trans rfl, ?_, ?_⟩
      · rw [hagc.2.2.1, congrArg Cfg.stor hc]; rfl
      · rw [hagc.2.2.1, congrArg Cfg.stor hc]; rfl
    all_goals simp [obsB, obsBEELS] at hA'
  refine ⟨post0F post1, post1, rfl, CoveredFork.prague, f0_enter, hx0, hpm, he0, ho0,
    prefix0, spawnedBy1, rfl, rfl, rfl, hx1, he1, ?_, cfg339_eq, agree_cfg339, ?_,
    spawnedBy_of_childStart agree_cfg339 start2_eq, h2t, h2c,
    aCall_eq, spawnedBy_of_callPrep agree_aCall cp3_eq e3_eq, h3t, e3_code,
    prefix3, spawnedBy_of_dcallPrep cp4_eq (fun a => by rw [e31_acc]; exact e3_adrs a)
      (by rw [e31_state]; exact e3_world.2) e4_eq,
    h4t, e4_code, h4d, ?_, ?_, hx4, hB, ?_, ?_,
    ⟨hrg.1, hrg.2.1, hrg.2.2.2.2.2⟩, ⟨hag.1, hag.2.1, hag.2.2.2.2.2⟩, h2, ?_, ?_, ?_⟩
  · exact (c0_agree.2.2.1 _ _).trans (by kernel_rfl)
  · rw [agree_cfg339.2.2.1]; exact lock_cfg339
  · exact (hag4.2.2.1 _ _).trans hl2
  · exact (hag4.2.2.1 _ _).trans hl0
  · rw [ha4.2.2.1]; kernel_rfl
  · rw [ha4.2.2.1]; kernel_rfl
  · rw [hst0]; exact h26
  · rw [hst0]; exact hA
  · rw [hst0, h26, hA]; decide

end Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Top
