import Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Top
import Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.ForkFrames

/-!
# V- under every covered fork

`vminus_witness_covered g` is `vminus_witness` for the same nested execution under any covered
fork `g` (Prague, Osaka, BPO1, BPO2): every machine of the run is the Prague machine with its
fork changed to `g` (`withFork`), and every conjunct is kept, so the deployed Vyper 0.2.15
pool's cross-function reentrancy and its broken LP ledger hold under every fork the
verified semantics covers.  The run never executes `CLZ`, reads no blob price, and none of its
frames enters `MODEXP` or `P256VERIFY`: the kernel facts of the Prague run transport
(`Blanc/Lift/NodeWalkFork.lean`, `Blanc/Lift/WitnessFork.lean`, `ForkFrames.lean`); nothing is
re-evaluated.  `vminus_witness` (Prague) is unchanged.
-/

namespace Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Top

open Jaune Blanc.Lift Blanc.Lift.Witness Blanc.Lift.Witness.Boundary Blanc.ConcreteRun
  Blanc.ForkUniform Blanc.Lift.NodeWalk
open Blanc.Lift.VyperNonreentrantDeployed Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Frame1
open Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Subtree

attribute [local irreducible] e0 cp1 cfg339 e2 cc2 aCall cp3 e3 cp4 e4 post4

variable {g : Fork}

/-! ### Frame 0 -/

theorem e0_stat : e0.sta.benvStat = benvStat0 := (frameEnterS_stat e0_eq).trans rfl

theorem e0_block : e0.sta.benvStat.fork = .prague ∧ e0.sta.benvStat.excessBlobGas = 0 := by
  rw [e0_stat]; exact ⟨rfl, rfl⟩

theorem cp1_neutral : cp1.f.PrecompNeutral :=
  Frame.precompNeutral_of_codeAddress (congrArg (·.2.1) spawned_codeAddresses) (by decide)
    (by decide)

theorem f0_neutral : f0.PrecompNeutral :=
  Frame.precompNeutral_of_codeAddress (congrArg (·.1) spawned_codeAddresses) (by decide)
    (by decide)

theorem f0_enter_at (hg : CoveredFork g) : (f0.withFork g).enter = .run (e0.withFork g) := by
  rw [frame_enter_withFork CoveredFork.prague CoveredFork.prague hg f0_neutral, f0_enter]; rfl

theorem prefix0_at (hg : CoveredFork g) : stepN 11 (e0.withFork g) = some (e0_31.withFork g) :=
  stepN_withFork hg e0_block.1 e0_block.2 prefix0

theorem cp1_at (hg : CoveredFork g) :
    dcallPrep (e0_31.withFork g).sta e0_31.dyna [] acs00 = some (cp1.withFork g) := by
  have hf : CoveredFork e0_31.sta.benvStat.fork := by
    show CoveredFork e0.sta.benvStat.fork
    rw [e0_block.1]; exact CoveredFork.prague
  have h := dcallPrep_withFork hf hg e0_31.dyna [] acs00
  show dcallPrep (e0_31.sta.withFork g) e0_31.dyna [] acs00 = _
  rw [h, cp1_eq]; rfl

theorem e1_at (hg : CoveredFork g) :
    frameEnterS (cp1.withFork g).f acs00 = .run ⟨0, sevm1.withFork g, pre1⟩ := by
  show frameEnterS (cp1.f.withFork g) acs00 = _
  rw [frameEnterS_withFork_of_stat (s := e0.sta) (by rw [e0_block.1]; exact CoveredFork.prague) hg
    (dcallPrep_stat cp1_eq) cp1_neutral, e1_eq]
  rfl

theorem cp1_spec_at (hg : CoveredFork g) :
    Xinst.step (e0_31.withFork g).sta e0_31.dyna .delegatecall =
        .spawn (cp1.withFork g).f (.call cp1.p cp1.oi cp1.os) ∧
      (∀ a, a ∈ cp1.p.accessedAddresses ↔ a ∈ cp1.adrs) ∧
      cp1.p.accessedStorageKeys = e0_31.dyna.accessedStorageKeys ∧
      (cp1.withFork g).f.isCreate = false ∧
      (cp1.withFork g).f.inner.accessedAddresses = cp1.p.accessedAddresses ∧
      (cp1.withFork g).f.inner.accessedStorageKeys = cp1.p.accessedStorageKeys ∧
      (cp1.withFork g).f.inner.benv.stat.rules.stateGas = none ∧
      (cp1.withFork g).f.inner.benv.state = e0_31.dyna.state ∧ cp1.p.state = e0_31.dyna.state :=
  dcallPrep_spec (cp1_at hg) e0_adrs e0_world

theorem spawn0_at (hg : CoveredFork g) :
    Evm.step (e0_31.withFork g) = .spawn (cp1.withFork g).f (.call cp1.p cp1.oi cp1.os) 32 := by
  have hat : Ninst.At (e0_31.withFork g).sta.code 31 (.exec .delegatecall) := by
    show Ninst.At e0.sta.code 31 (.exec .delegatecall)
    rw [e0_code]; exact proxy_at_delegatecall
  show Evm.step ⟨31, (e0_31.withFork g).sta, e0_31.dyna⟩ = _
  rw [Evm.step_next hat, Ninst.step_exec, (cp1_spec_at hg).1]
  rfl

theorem enter1_at (hg : CoveredFork g) :
    (cp1.withFork g).f.enter = .run ⟨0, sevm1.withFork g, pre1⟩ := by
  rw [frame_enter_eq_B, frameEnterB_eq_S (by rw [(cp1_spec_at hg).2.2.2.2.2.2.2.1]; exact e0_world)]
  exact e1_at hg

theorem spawnedBy1_at (hg : CoveredFork g) :
    SpawnedBy (e0_31.withFork g).sta e0_31.dyna .delegatecall ⟨0, sevm1.withFork g, pre1⟩ :=
  spawnedBy_of_dcallPrep (cp1_at hg) e0_adrs e0_world (e1_at hg)

/-- **The top-level message call, under any covered fork.**  From any settled frame 1 with its
observed gas, return data and success, the top-level frame is an `Exec` from the machine the
message enters with, Jaune's `processMessage` returns its settled machine, and that machine has
frame 1's world. -/
theorem frame0_of_child_at (hg : CoveredFork g) (post1 : Devm)
    (hx1 : Nonempty (Exec 0 (sevm1.withFork g) pre1 (.ok post1)))
    (hg1 : post1.gasLeft = 29372882) (ho1 : post1.output = word 100 ++ word 100)
    (he1 : post1.error = none) :
    Nonempty (Exec (e0.withFork g).pc (e0.withFork g).sta (e0.withFork g).dyna
        (.ok (post0F post1))) ∧
      processMessage (msg0.withFork g) = .ok (post0F post1) ∧ (post0F post1).error = none ∧
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
  obtain ⟨-, -, -, hcr, -, -, hsg, -, -⟩ := cp1_spec_at hg
  have hsettle : Resume.run (.call cp1.p cp1.oi cp1.os) ((cp1.withFork g).f.settle (.ok post1)) =
      .ok (d02 post1) := by
    rw [frame_settle_ok hcr hsg he1]; exact resumeCallB_sound hr
  have hsta : (e0_44 post1).sta = e0.sta := stepN_sta (evm := ⟨32, e0.sta, d02 post1⟩) ht
  have hstep_halt : Evm.step ((e0_44 post1).withFork g) = .halt (.ok (post0F post1)) := by
    have hp : (e0_44 post1).sta.benvStat.fork = .prague := by rw [hsta]; exact e0_block.1
    have hx : (e0_44 post1).sta.benvStat.excessBlobGas = 0 := by rw [hsta]; exact e0_block.2
    rw [show Evm.step ((e0_44 post1).withFork g) = (Evm.step (e0_44 post1)).withFork g from
      evm_step_withFork_prague hp hx hg (by rw [hh]; intro ee; nofun), hh]
    rfl
  have hx0 : Nonempty (Exec (e0.withFork g).pc (e0.withFork g).sta (e0.withFork g).dyna
      (.ok (post0F post1))) :=
    exec_of_stepN_spawn_runOk (prefix0_at hg) (spawn0_at hg) (enter1_at hg) hx1 hsettle
      (exec_of_stepN_halt (stepN_withFork hg (e := ⟨32, e0.sta, d02 post1⟩) e0_block.1
        e0_block.2 ht) hstep_halt)
  have hex := (exec_iff_exec_eq _ _ _ _).mp hx0
  refine ⟨hx0, ?_, he0', hg0,
    List.map_injective_iff.mpr (fun _ _ h => UInt8.toNat_inj.mp h) ho0,
    hk.trans (resumeCallB_state hr)⟩
  have hsg0 : (f0.withFork g).inner.benv.stat.rules.stateGas = none :=
    CoveredFork.rules_stateGas_none (s := (f0.withFork g).inner.benv.stat) hg
  show runFrame (f0.withFork g) = _
  unfold runFrame
  rw [f0_enter_at hg]
  show (f0.withFork g).settle (exec ⟨(e0.withFork g).pc, (e0.withFork g).sta,
    (e0.withFork g).dyna⟩) = _
  rw [hex]
  exact frame_settle_ok rfl hsg0 he0'

/-! ### The final theorem -/

/-- **V- under every covered fork: the deployed Vyper 0.2.15 pool admits `add_liquidity`
reentered from inside `remove_liquidity`, and the reentry breaks its LP ledger.**

This is `vminus_witness` for the same nested execution with every machine's fork changed to
any covered fork `g` (Prague, Osaka, BPO1 or BPO2): the pre-state, the calldata, the gas, the
frames, the lock slots and the harm are those of `vminus_witness`, and every conjunct is kept.
Only the fork of the block environment differs (`(msg0.withFork g).benv.stat.fork = g`); the
run never executes `CLZ`, reads no blob price, and none of its frames enters `MODEXP` or
`P256VERIFY`, so the same gas and the same states result. -/
theorem vminus_witness_covered (g : Fork) (hg : CoveredFork g) :
    ∃ post0 post1 : Devm,
      -- the top-level message call, under `g`
      (msg0.withFork g).benv.stat.fork = g ∧ CoveredFork (msg0.withFork g).benv.stat.fork ∧
      (f0.withFork g).enter = .run (e0.withFork g) ∧
      Nonempty (Exec (e0.withFork g).pc (e0.withFork g).sta (e0.withFork g).dyna (.ok post0)) ∧
      processMessage (msg0.withFork g) = .ok post0 ∧ post0.error = none ∧
      post0.output = word 100 ++ word 100 ∧
      -- (a) frame 1: `P` running the implementation's `remove_liquidity`, spawned by the proxy
      stepN 11 (e0.withFork g) = some (e0_31.withFork g) ∧
      SpawnedBy (e0_31.withFork g).sta (e0_31.withFork g).dyna .delegatecall
        ⟨0, sevm1.withFork g, pre1⟩ ∧
      (sevm1.withFork g).currentTarget = proxyAddress ∧ (sevm1.withFork g).code = code ∧
      (sevm1.withFork g).data = removeCalldata ∧
      Nonempty (Exec 0 (sevm1.withFork g) pre1 (.ok post1)) ∧ post1.error = none ∧
      -- frame 1 takes slot 2 and calls `A` holding it
      storOf pre1.state proxyAddress (2 : Nat).toB256 = 0 ∧
      wrun fs1 (sevm1.withFork g) 339 c0 = .cont cfg339 ∧ Agree cfg339 ∧
      storOf cfg339.devm.state proxyAddress (2 : Nat).toB256 = (1 : Nat).toB256 ∧
      SpawnedBy (sevm1.withFork g) cfg339.devm .call (e2.withFork g) ∧
      (e2.withFork g).sta.currentTarget = attackerAddress ∧
      (e2.withFork g).sta.code = attackerCode ∧
      -- `A` calls `P`; the proxy delegates to the implementation: frame 4
      wrun fs2 (e2.withFork g).sta 24 cc2 = .cont aCall ∧
      SpawnedBy (e2.withFork g).sta aCall.devm .call (e3.withFork g) ∧
      (e3.withFork g).sta.currentTarget = proxyAddress ∧
      (e3.withFork g).sta.code = proxyCode ∧
      stepN 11 (e3.withFork g) = some (e31.withFork g) ∧
      SpawnedBy (e31.withFork g).sta (e31.withFork g).dyna .delegatecall (e4.withFork g) ∧
      (e4.withFork g).sta.currentTarget = proxyAddress ∧ (e4.withFork g).sta.code = code ∧
      (e4.withFork g).sta.data = addCalldata ∧
      -- frame 4 is entered while slot 2 = 1, its own lock (slot 0) free
      storOf e4.dyna.state proxyAddress (2 : Nat).toB256 = (1 : Nat).toB256 ∧
      storOf e4.dyna.state proxyAddress (0 : Nat).toB256 = 0 ∧
      Nonempty (Exec (e4.withFork g).pc (e4.withFork g).sta (e4.withFork g).dyna (.ok post4)) ∧
      -- frame 4 reaches `add_liquidity`'s body with slot 0 taken and slot 2 still held
      (∃ cB : Cfg, wrun fs1 (e4.withFork g).sta 2625 c4 = .cont cB ∧ Agree cB ∧
        cB.f = t_0370_c63 ∧
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
  obtain ⟨post1, hrun1, hg1, ho1, h26, hA, h2, he1⟩ := frame1_closed_at hg
  have hx1 : Nonempty (Exec 0 (sevm1.withFork g) pre1 (.ok post1)) :=
    lift_exactM cert_checkM cert_jumpsOkM rfl hg hrun1
  obtain ⟨hx0, hpm, he0, -, ho0, hst0⟩ := frame0_of_child_at hg post1 hx1 hg1 ho1 he1
  -- frame 4's entry agreement
  obtain ⟨-, hpa, hpk, -, hia, hik, -, hst, -⟩ := cp4_spec
  have hag4 : Agree c4 := frameStart_agree t_0000_c0 e4_eq
    (fun x => by rw [hik, hpk, e31_keys]; exact e3_keys x) (fun a => by rw [hia]; exact hpa a)
    (fun a k => by rw [hst, e31_state]; exact e3_world.1 a k)
    (by rw [hst, e31_state]; exact e3_world.2)
  obtain ⟨hx4, -, ha4⟩ := frame4_child_at hg
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
    all_goals simp only [obsB, obsBEELS, reduceCtorEq] at hA'
  obtain ⟨cB, hcB, hagB, hfB, hlB0, hlB2⟩ := hB
  have hcBg : wrun fs1 (e4.withFork g).sta 2625 c4 = .cont cB :=
    (wrun_withFork (by rw [e4_block.1]; exact CoveredFork.prague) hg e4_block.2 fs1 2625 c4).trans
      hcB
  refine ⟨post0F post1, post1, rfl, hg, f0_enter_at hg, hx0, hpm, he0, ho0,
    prefix0_at hg, spawnedBy1_at hg, rfl, rfl, rfl, hx1, he1, ?_, cfg339_at hg, agree_cfg339, ?_,
    spawnedBy_of_childStart agree_cfg339 (start2_at hg), h2t, h2c,
    aCall_at hg, spawnedBy_of_callPrep agree_aCall (cp3_at hg) (e3_at hg), h3t, e3_code,
    prefix3_at hg, spawnedBy_of_dcallPrep (cp4_at hg)
      (fun a => by show a ∈ e31.dyna.accessedAddresses ↔ _; rw [e31_acc]; exact e3_adrs a)
      (by show AcctAgree e31.dyna.state acs3; rw [e31_state]; exact e3_world.2) (e4_at hg),
    h4t, e4_code, h4d, ?_, ?_, hx4, ⟨cB, hcBg, hagB, hfB, hlB0, hlB2⟩, ?_, ?_,
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
