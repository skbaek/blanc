import Blanc.Lift.Usdc.OldInitializerV1Callee
import Blanc.Lift.Usdc.ImplV1.Check
import Blanc.Lift.Usdc.ProxyForward
import Blanc.Lift.WriteSiteZero
import Blanc.HistoricalFork

/-!
# Actual V1 `initialize` from the original successful run

Source-bound leaf composing `OldInitializerV1Callee.initialize_observed` with
the original successful fresh PC0 execution of the registered V1
implementation, as `OldInitializerEffects` does for V2. The lift is
`lift_sound_in_noStateGas` (so the result serves historical forks through
`HistFork.stateGas_none`, and covered forks through
`CoveredFork.rules_stateGas_none`), then `FreePtr.SFunc.RunP.withPot` from
the initial potential. The actual dispatcher (`t_0000_c0`: solc free-pointer
store `mstore(0x40, 0x80)`, short-calldata revert, `div`/`and` selector
extraction, the linear comparison chain to table entry `60`, the nonpayable
check of `t_0404_c60`) is walked on the same run, which derives the
wrapper-entry seams `memWord M0 64 = 0x80` and `96 ≤ 0x80` and the entry stack
`callvalue :: selector`. Every store is classified by
`V1InitializerWriteClass` and no external instruction executes.

Explicit local premises: `stateGas = none`, the initial potential
`pre.gasMeasure < 2 ^ 256`, fresh empty stack/memory, the registered code and
the actual selector `0x3357162b`. No historical producer of the potential, no
seed, no hash separation of payload keys from protected rows is asserted here.
-/

namespace Blanc.Lift.Usdc

open Jaune Blanc Blanc.Lift Blanc.Lift.WriteSite
open OldInitializerV1Callee OldInitializerV1Staging

namespace OldInitializerV1Root

variable {sevm : Sevm} {P : Sevm → Devm → Ninst → Devm → Prop}

set_option hygiene false in
/-- One state-silent observed step: invert with `t` and rebuild. -/
local macro "qs " t:term : tactic => `(tactic| (
  have step := rpw_next run
  clear run
  obtain ⟨_, w, run⟩ := step
  refine .next ⟨w, silentClass rfl, silentNoExec rfl⟩ ?_
  obtain ⟨_, rfl⟩ := $t (erase w.1)
  clear w))

/-- One dispatcher comparison `dup; push σ; eq; push dest; branchTo next k`
whose selector `σ` does not match: the taken arm is refuted and the
fall-through run is observed by `cont`. -/
theorem miss_obs
    (erase : ∀ {s d n d'}, P s d n d' → Ninst.Run s d n d')
    {σ dd : Bytes} {hσ : σ.length ≤ 32} {hd : dd.length ≤ 32} {k : Nat} {next : SFunc}
    {b : Devm} {sel : B256} {M : Mem} {G : Nat} {out : Outcome}
    (miss : B256.eqCheck (Bytes.toB256 σ) sel = 0)
    (cont : ∀ G', SFunc.RunP (FreePtr.PotStep P) ImplV1.cert.prog sevm
      (St b [sel] M G') next out →
      SFunc.RunP (Obs (FreePtr.PotStep P) sevm) ImplV1.cert.prog sevm
        (St b [sel] M G') next out)
    (run : SFunc.RunP (FreePtr.PotStep P) ImplV1.cert.prog sevm (St b [sel] M G)
      (.next (.reg (.dup 0)) (.next (.push σ hσ) (.next (.reg .eq)
        (.next (.push dd hd) (.branchTo next k))))) out) :
    SFunc.RunP (Obs (FreePtr.PotStep P) sevm) ImplV1.cert.prog sevm (St b [sel] M G)
      (.next (.reg (.dup 0)) (.next (.push σ hσ) (.next (.reg .eq)
        (.next (.push dd hd) (.branchTo next k))))) out := by
  qs (ri_dup rfl)
  qs ri_push
  qs ri_eq
  qs ri_push
  cases run with
  | toSucc dest word nonzero lookup pop run =>
    exact (nonzero ((St.of_pop2 pop).2.1.symm.trans miss)).elim
  | toZero dest pop run =>
    refine .toZero dest pop ?_
    rw [(St.of_pop2 pop).2.2] at run ⊢
    exact cont _ run

/-- The actual nonpayable entry `t_0404_c60` of table entry `60`, from the
dispatcher's selector word and the solc free pointer `0x80`, reaches
`t_0410_c60` with the derived wrapper-entry seams. -/
theorem entry60_obs
    (erase : ∀ {s d n d'}, P s d n d' → Ninst.Run s d n d')
    {b : Devm} {sel : B256} {G : Nat} {out : Outcome}
    (run : SFunc.RunP (FreePtr.PotStep P) ImplV1.cert.prog sevm
      (St b [sel] (Mem.empty.write (Bytes.toB256 [0x40]).toNat
        (Bytes.toB256 [0x80]).toBytes) G) ImplV1.t_0404_c60 out) :
    SFunc.RunP (Obs (FreePtr.PotStep P) sevm) ImplV1.cert.prog sevm
      (St b [sel] (Mem.empty.write (Bytes.toB256 [0x40]).toNat
        (Bytes.toB256 [0x80]).toBytes) G) ImplV1.t_0404_c60 out := by
  have hfp : memWord (Mem.empty.write (Bytes.toB256 [0x40]).toNat
      (Bytes.toB256 [0x80]).toBytes) 64 = Bytes.toB256 [0x80] := by
    rw [show (Bytes.toB256 [0x40]).toNat = 64 by decide]
    exact (Mem.memWord_write_word _ 64 _).1
  have hp96 : 96 ≤ (Bytes.toB256 [0x80]).toNat := by decide
  unfold ImplV1.t_0404_c60 at run ⊢
  cases run with
  | dest burn run =>
    refine .dest burn ?_
    rw [St.of_burn burn] at run ⊢
    qs ri_callvalue
    qs (ri_dup rfl)
    qs ri_iszero
    qs ri_push
    cases run with
    | zero dest pop run =>
      unfold ImplV1.t_040c_c60 at run
      iterate 2
        obtain ⟨_, _, run⟩ := rpw_next run
      exact (rpw_revert run).elim
    | succ dest word nonzero pop run =>
      refine .succ dest word nonzero pop ?_
      rw [(St.of_pop2 pop).2.2] at run ⊢
      exact initialize_observed erase hfp hp96 run

/-- **The actual V1 dispatcher route to `initialize`.** Every `PotStep P` run
of the whole V1 implementation program from a fresh frame, with calldata
selector `0x3357162b`, is the same run with every store classified and no
external instruction. -/
theorem dispatch_obs
    (erase : ∀ {s d n d'}, P s d n d' → Ninst.Run s d n d')
    (selector : Blanc.Sevm.selector sevm = 0x3357162b)
    {b : Devm} {G : Nat} {out : Outcome}
    (run : SFunc.RunP (FreePtr.PotStep P) ImplV1.cert.prog sevm
      (St b [] Mem.empty G) ImplV1.t_0000_c0 out) :
    SFunc.RunP (Obs (FreePtr.PotStep P) sevm) ImplV1.cert.prog sevm
      (St b [] Mem.empty G) ImplV1.t_0000_c0 out := by
  have word := (dispatchWord_eq_selector sevm).trans selector
  unfold Proxy.dispatchWord at word
  unfold ImplV1.t_0000_c0 at run ⊢
  qs ri_push
  qs ri_push
  qs ri_mstore
  qs ri_push
  qs ri_calldatasize
  qs ri_lt
  qs ri_push
  cases run with
  | succ dest w nonzero pop run =>
    unfold ImplV1.t_018b_c0 at run
    cases run with
    | dest burn run =>
      iterate 2
        obtain ⟨_, _, run⟩ := rpw_next run
      exact (rpw_revert run).elim
  | zero dest pop run =>
    refine .zero dest pop ?_
    rw [(St.of_pop2 pop).2.2] at run ⊢
    unfold ImplV1.t_000d_c0 at run ⊢
    qs ri_push
    qs ri_calldataload
    qs ri_push
    qs (ri_swap rfl)
    qs ri_div
    qs ri_push
    qs ri_and
    rw [word] at run ⊢
    refine miss_obs erase (by decide) (fun _ run => ?_) run
    unfold ImplV1.t_0041_c0 at run ⊢
    refine miss_obs erase (by decide) (fun _ run => ?_) run
    unfold ImplV1.t_004c_c0 at run ⊢
    refine miss_obs erase (by decide) (fun _ run => ?_) run
    unfold ImplV1.t_0057_c0 at run ⊢
    refine miss_obs erase (by decide) (fun _ run => ?_) run
    unfold ImplV1.t_0062_c0 at run ⊢
    refine miss_obs erase (by decide) (fun _ run => ?_) run
    unfold ImplV1.t_006d_c0 at run ⊢
    refine miss_obs erase (by decide) (fun _ run => ?_) run
    unfold ImplV1.t_0078_c0 at run ⊢
    refine miss_obs erase (by decide) (fun _ run => ?_) run
    unfold ImplV1.t_0083_c0 at run ⊢
    qs (ri_dup rfl)
    qs ri_push
    qs ri_eq
    qs ri_push
    cases run with
    | toZero dest pop run =>
      exact ((by decide : B256.eqCheck (Bytes.toB256 [0x33, 0x57, 0x16, 0x2b])
        (0x3357162b : B256) ≠ 0) (St.of_pop2 pop).2.1).elim
    | toSucc dest w nonzero lookup pop run =>
      rw [show ImplV1.cert.prog[60]? = some ImplV1.t_0404_c60 from rfl] at lookup
      cases lookup
      refine .toSucc dest w nonzero rfl pop ?_
      rw [(St.of_pop2 pop).2.2] at run ⊢
      exact entry60_obs erase run

end OldInitializerV1Root

open OldInitializerV1Root

/-- **Whole actual V1 `initialize` from the original successful run.** The
original successful fresh PC0 execution of the registered V1 implementation
with selector `0x3357162b` is, on its own `StepIn` derivation, a run whose
every store writes a fixed slot `0/1/2/4/5/6/7/8`, literal zero, or a bounded
modular payload word of an actual long decoded string, and which executes no
external instruction. Local premises: `stateGas = none` and the initial
potential `pre.gasMeasure < 2 ^ 256`. -/
theorem implV1_initialize_observed
    {sevm : Sevm} {pre post : Devm}
    (run : Exec 0 sevm pre (.ok post)) (code : sevm.code = ImplV1.code)
    (hsg : sevm.benvStat.rules.stateGas = none)
    (stack : pre.stack = []) (memory : pre.memory = Mem.empty)
    (gas : pre.gasMeasure < 2 ^ 256)
    (selector : Blanc.Sevm.selector sevm = 0x3357162b) :
    SProg.RunP (fun s d n d' => StepIn ⟨0, sevm, pre, .ok post, run⟩ s d n d' ∧
      V1InitializerWriteClass sevm d n ∧ ∀ x, n ≠ .exec x) ImplV1.cert.prog sevm pre post := by
  let R : Exec.Deriv := ⟨0, sevm, pre, .ok post, run⟩
  obtain ⟨entry, lookup, lifted⟩ := lift_sound_in_noStateGas ImplV1.cert_check code hsg run
  rw [show ImplV1.cert.prog[0]? = some ImplV1.t_0000_c0 from rfl] at lookup
  cases lookup
  have pot : FreePtr.Pot pre := by
    unfold FreePtr.Pot
    rw [memory]
    exact gas
  obtain ⟨potRun, -⟩ := FreePtr.SFunc.RunP.withPot (fun h => StepIn.toRun h) hsg lifted pot
  have stateEq : St pre [] Mem.empty pre.gasLeft = pre := (St.self stack memory).symm
  have framed : SFunc.RunP (FreePtr.PotStep (StepIn R)) ImplV1.cert.prog sevm
      (St pre [] Mem.empty pre.gasLeft) ImplV1.t_0000_c0 (.halted post) :=
    stateEq.symm ▸ potRun
  have classified := dispatch_obs (fun h => StepIn.toRun h) selector framed
  have unframed : SFunc.RunP (Obs (FreePtr.PotStep (StepIn R)) sevm) ImplV1.cert.prog sevm
      pre ImplV1.t_0000_c0 (.halted post) :=
    Eq.mp (congrArg (fun d => SFunc.RunP (Obs (FreePtr.PotStep (StepIn R)) sevm)
      ImplV1.cert.prog sevm d ImplV1.t_0000_c0 (.halted post)) stateEq) classified
  exact ⟨_, rfl, SFunc.RunP.mono (fun h => ⟨h.1.1, h.2.1, h.2.2⟩) unframed⟩

/-- The requested write classifier, projected from the same actual source run. -/
theorem implV1_initialize_writeClass
    {sevm : Sevm} {pre post : Devm}
    (run : Exec 0 sevm pre (.ok post)) (code : sevm.code = ImplV1.code)
    (hsg : sevm.benvStat.rules.stateGas = none)
    (stack : pre.stack = []) (memory : pre.memory = Mem.empty)
    (gas : pre.gasMeasure < 2 ^ 256)
    (selector : Blanc.Sevm.selector sevm = 0x3357162b) :
    SProg.RunP (fun s d n d' => StepIn ⟨0, sevm, pre, .ok post, run⟩ s d n d' ∧
      V1InitializerWriteClass sevm d n) ImplV1.cert.prog sevm pre post :=
  SProg.RunP.mono (fun step => ⟨step.1, step.2.1⟩)
    (implV1_initialize_observed run code hsg stack memory gas selector)

/-- The historical-fork form: `HistFork` discharges `stateGas = none`. -/
theorem implV1_initialize_observed_hist
    {sevm : Sevm} {pre post : Devm}
    (run : Exec 0 sevm pre (.ok post)) (code : sevm.code = ImplV1.code)
    (fork : HistFork sevm.benvStat.fork)
    (stack : pre.stack = []) (memory : pre.memory = Mem.empty)
    (gas : pre.gasMeasure < 2 ^ 256)
    (selector : Blanc.Sevm.selector sevm = 0x3357162b) :
    SProg.RunP (fun s d n d' => StepIn ⟨0, sevm, pre, .ok post, run⟩ s d n d' ∧
      V1InitializerWriteClass sevm d n ∧ ∀ x, n ≠ .exec x) ImplV1.cert.prog sevm pre post :=
  implV1_initialize_observed run code (HistFork.stateGas_none fork) stack memory gas selector

/-- All three actual decoded strings are short (at most 31 bytes). -/
def V1InitializerShort (sevm : Sevm) : Prop :=
  ∀ slot head, (slot, head) ∈ stringSlots → (lenAt sevm head).toNat ≤ 31

private theorem v1Short_observation
    {K : B256 → Prop} {sevm frame : Sevm} {d : Devm} {n : Ninst}
    (observed : V1InitializerWriteClass sevm d n)
    (short : V1InitializerShort sevm)
    (separate : ∀ key, K key → key ∉ fixedSlots) :
    GuardObs K False frame d n := by
  intro store key value rest shape tracked
  rcases observed store key value rest shape with fixed | zero | payload
  · exact (separate key tracked fixed).elim
  · rw [zero]
    exact Or.inr (Nat.zero_le _)
  · obtain ⟨slot, head, member, long, -⟩ := payload
    have bound := short slot head member
    exact absurd long (by omega)

/-- Short actual decoded strings have no payload-word stores. Fixed-slot
separation therefore gives demanded-row nonincrease. -/
theorem implV1_initialize_short_nonInc
    {K : B256 → Prop} {sevm : Sevm} {pre post : Devm}
    (run : Exec 0 sevm pre (.ok post)) (code : sevm.code = ImplV1.code)
    (hsg : sevm.benvStat.rules.stateGas = none)
    (stack : pre.stack = []) (memory : pre.memory = Mem.empty)
    (gas : pre.gasMeasure < 2 ^ 256)
    (selector : Blanc.Sevm.selector sevm = 0x3357162b)
    (short : V1InitializerShort sevm)
    (separate : ∀ key, K key → key ∉ fixedSlots) :
    SProg.RunP (fun s d n d' => StepIn ⟨0, sevm, pre, .ok post, run⟩ s d n d' ∧
      GuardObs K False s d n) ImplV1.cert.prog sevm pre post := by
  refine SProg.RunP.mono ?_
    (implV1_initialize_writeClass run code hsg stack memory gas selector)
  intro s d n d' step
  exact ⟨step.1, v1Short_observation step.2 short separate⟩

/-- The actual short-string V1 initializer preserves an explicitly supplied
zero-row seed. The same route has no external instruction, so no child
effect is assumed and no fork beyond `stateGas = none` is needed. -/
theorem implV1_initialize_short_zero
    {K : B256 → Prop} {sevm : Sevm} {pre post : Devm}
    (run : Exec 0 sevm pre (.ok post)) (code : sevm.code = ImplV1.code)
    (hsg : sevm.benvStat.rules.stateGas = none)
    (stack : pre.stack = []) (memory : pre.memory = Mem.empty)
    (gas : pre.gasMeasure < 2 ^ 256)
    (selector : Blanc.Sevm.selector sevm = 0x3357162b)
    (short : V1InitializerShort sevm)
    (separate : ∀ key, K key → key ∉ fixedSlots)
    (zero : ZeroSlots K sevm.currentTarget pre) :
    ZeroSlots K sevm.currentTarget post :=
  progRunP_zero_noExec (fun step => StepIn.toRun step.1)
    (fun step => v1Short_observation step.2.1 short separate) (fun step => step.2.2)
    (implV1_initialize_observed run code hsg stack memory gas selector) zero

end Blanc.Lift.Usdc
