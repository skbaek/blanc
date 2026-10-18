import Blanc.Lift.Basic
import Blanc.Lift.Silent
import Jaune.MemoryAccounting

/-!
# The memory potential along synthetic runs (free-pointer checker, unit F2)

Goal `usdc-neversigner-freepointer-v1`, design `fp-checker.md` §1 points 5 and 8. Contract-neutral.

`Pot d` says the frame's gas plus the memory cost already paid is below one word. Jaune's public
`Exec.memory_accounting_output` shows a complete derivation never raises it; `Ninst.Run.pot`
brings that to one lifted step, and `SFunc.RunP.withPot` records it at every step of a synthetic
run. The tree-level checker (F3) reads the window bounds of every executed write off `Pot`.

## Route

`Ninst.Run sevm d n d'` quantifies the program counter away, so the step relation carries no
code at all, and Jaune's per-instruction accounting is private. The derivation is rebuilt
instead: under the static environment whose code is `n`'s own encoding at `pc` (`codeAt`), the
step is `Evm.step`, the next counter sits past the end of that code and decodes to the implicit
`STOP`, and the two nodes are a derivation of `.ok d'` to which the public frame-level theorem
applies. `Ninst.step` reads the static code only in `CODESIZE` and `CODECOPY`
(`Ninst.step_withCode`); those two are accounted directly from the public charge lemmas.
-/

namespace Blanc.Lift.FreePtr

open Jaune

/-- What a word size the memory potential allows (`Pot`, F2): every touched window ends below. -/
def memCap : Nat := 2 ^ 160

/-- The memory/gas potential of a machine state is below one word: every window an executed
instruction touches then ends below `memCap`. -/
def Pot (d : Devm) : Prop := d.gasMeasure + calculateMemoryGasCost d.memory.size < 2 ^ 256

/-- A step relation that also records the potential before and after the step. -/
def PotStep (P : Sevm → Devm → Ninst → Devm → Prop) : Sevm → Devm → Ninst → Devm → Prop :=
  fun s d n d' => P s d n d' ∧ Pot d ∧ Pot d'

/-- The potential bounds the memory size. -/
theorem Pot.size_lt {d : Devm} (h : Pot d) : d.memory.size < memCap := by
  by_contra hn
  have hmono := calculateMemoryGasCost_mono (Nat.le_of_not_gt hn)
  have hcap : 2 ^ 256 ≤ calculateMemoryGasCost memCap := by decide
  unfold Pot at h
  omega

/-! ## The static code is read by two instructions only -/

/-- `Ninst.step` reads the static code only in `CODESIZE` and `CODECOPY`. -/
theorem Ninst.step_withCode {pc : Nat} {sevm : Sevm} {d : Devm} {n : Ninst} (code : ByteArray)
    (h1 : n ≠ .reg .codesize) (h2 : n ≠ .reg .codecopy) :
    Ninst.step ⟨pc, { sevm with code := code }, d⟩ n = Ninst.step ⟨pc, sevm, d⟩ n := by
  cases n with
  | reg r =>
    cases r with
    | codesize => exact absurd rfl h1
    | codecopy => exact absurd rfl h2
    | _ => rfl
  | exec x => cases x <;> rfl
  | push bs le => rfl
  | dupn a => rfl
  | swapn a => rfl
  | exchange a => rfl

/-! ## A code that decodes to one instruction -/

/-- `pc` zero bytes, then `n`'s encoding: the code that decodes to `n` at `pc` and to the implicit
`STOP` right after it. -/
def codeAt (pc : Nat) (n : Ninst) : ByteArray := ⟨(List.replicate pc 0 ++ Ninst.toBytes n).toArray⟩

theorem List.drop?_replicate_append {ξ : Type} (x : ξ) (ys : List ξ) :
    ∀ m : Nat, List.drop? m (List.replicate m x ++ ys) = some ys
  | 0 => rfl
  | m + 1 => by
    simp only [List.replicate, List.cons_append, List.drop?]
    exact List.drop?_replicate_append x ys m

theorem codeAt_at (pc : Nat) (n : Ninst) : Ninst.At (codeAt pc n) pc n := by
  apply Ninst.at_of_slice
  refine ⟨(Ninst.toBytes n).length, ?_⟩
  rw [codeAt, ByteArray.toList_eq_toList_data]
  simp only [List.slice?, List.drop?_replicate_append, Bind.bind, Option.bind, List.take?_length]

theorem codeAt_size (pc : Nat) (n : Ninst) : (codeAt pc n).size = pc + n.size := by
  simp only [codeAt, ByteArray.size, List.size_toArray, List.length_append, List.length_replicate,
    Ninst.size_eq_length_toBytes]

/-- Past the end of the code the decoder yields the implicit `STOP`. -/
theorem getInst_of_size_le {code : ByteArray} {pc : Nat} (h : code.size ≤ pc) :
    code.getInst pc = some (.last .stop) := by
  unfold ByteArray.getInst
  rw [dite_eq_right (Nat.not_lt.mpr h)]

/-- The implicit `STOP` halts with the machine unchanged. -/
theorem Evm.step_stop_of_size_le {pc : Nat} {sevm : Sevm} {d : Devm} (h : sevm.code.size ≤ pc) :
    Evm.step ⟨pc, sevm, d⟩ = .halt (.ok d) :=
  Evm.step_last (getInst_of_size_le h)

/-! ## One lifted step as a complete derivation -/

/-- A lifted step of `n` that is not `CODESIZE`/`CODECOPY` is, under the code `codeAt pc n`, a
complete derivation: the step itself, then the implicit `STOP`. -/
theorem Ninst.StepRun.exec_codeAt {pc : Nat} {sevm : Sevm} {d d' : Devm} {n : Ninst} {xl : Xlot}
    (hfill : xl.Filled) (hstep : Ninst.StepRun pc sevm d n xl (.ok d'))
    (h1 : n ≠ .reg .codesize) (h2 : n ≠ .reg .codecopy) :
    Nonempty (Exec pc { sevm with code := codeAt pc n } d (.ok d')) := by
  have hat : Ninst.At ({ sevm with code := codeAt pc n } : Sevm).code pc n := codeAt_at pc n
  have hev : Evm.step ⟨pc, { sevm with code := codeAt pc n }, d⟩ = Ninst.step ⟨pc, sevm, d⟩ n :=
    (Evm.step_next hat).trans (Ninst.step_withCode _ h1 h2)
  have hstop : ∀ {d₁ : Devm},
      Evm.step ⟨pc + n.size, { sevm with code := codeAt pc n }, d₁⟩ = .halt (.ok d₁) :=
    fun {d₁} => Evm.step_stop_of_size_le (by rw [codeAt_size])
  unfold Ninst.StepRun at hstep
  rw [← hev] at hstep
  cases hs : Evm.step ⟨pc, { sevm with code := codeAt pc n }, d⟩ with
  | halt ex =>
    rw [hs] at hstep
    obtain ⟨-, rfl⟩ := hstep
    exact ⟨Exec.halt hs⟩
  | cont pc' d'' =>
    rw [hs] at hstep
    obtain ⟨-, hd⟩ := hstep
    cases hd
    have hpc : pc' = pc + n.size := Ninst.step_cont_pc (hev ▸ hs)
    subst hpc
    exact ⟨Exec.cont hs (Exec.halt hstop)⟩
  | spawn f rsm pc' =>
    rw [hs] at hstep
    obtain ⟨r, hrf, hr⟩ := hstep
    have hpc : pc' = pc + n.size := Ninst.step_spawn_pc (hev ▸ hs)
    subst hpc
    unfold RunFrame at hrf
    split at hrf
    · rename_i r' henter
      obtain ⟨-, rfl⟩ := hrf
      exact ⟨Exec.doneOk hs henter hr.symm (Exec.halt hstop)⟩
    · rename_i cevm henter
      obtain ⟨raw, rfl, rfl⟩ := hrf
      obtain ⟨child⟩ := hfill
      exact ⟨Exec.runOk hs henter child hr.symm (Exec.halt hstop)⟩

/-- The accounting a complete derivation of `.ok d'` gives. -/
theorem Exec.pot_le {pc : Nat} {sevm : Sevm} {d d' : Devm}
    (hsg : sevm.benvStat.rules.stateGas = none) (exc : Exec pc sevm d (.ok d')) :
    d'.gasMeasure + calculateMemoryGasCost d'.memory.size ≤
      d.gasMeasure + calculateMemoryGasCost d.memory.size :=
  (Exec.memory_accounting_output exc hsg).1

/-! ## The two code-reading instructions -/

theorem Devm.popToNat_memory {devm : Devm} {n : Nat} {devm' : Devm}
    (h : devm.popToNat = .ok (n, devm')) : devm'.memory = devm.memory := by
  rcases devm with ⟨⟨stack, memory, gasLeft, stateGas⟩, view, world⟩
  cases stack with
  | nil =>
    simp only [Devm.popToNat, liftMach, Mach.popToNat, Mach.pop, Footprint.liftOutcome,
      reduceCtorEq] at h
  | cons x xs =>
    simp only [Devm.popToNat, liftMach, Mach.popToNat, Mach.pop,
      Footprint.liftOutcome, Devm.setMach, Except.ok.injEq, Prod.mk.injEq] at h
    rw [← h.2]
    rfl

/-- A write never grows the memory past the extension it was charged for. -/
theorem Mem.write_size_le_ext (μ : Mem) (index : Nat) (bytes : Bytes) :
    (μ.write index bytes).size ≤ memExtSize μ.size index bytes.length := by
  cases bytes with
  | nil => exact Nat.le_refl _
  | cons byte bytes =>
    simp only [Mem.write]
    split
    · split <;> exact memExtSize_ge μ.size index (byte :: bytes).length
    · change ceil32 (index + (byte :: bytes).length) ≤
        memExtSize μ.size index (byte :: bytes).length
      have hn : (byte :: bytes).length ≠ 0 := by
        simp only [List.length_cons]
        omega
      simp only [memExtSize, ite_eq_right hn]
      have hceil : ∀ x : Nat, ceil32 x ≤ 32 * ceilDiv x 32 := by
        intro x
        unfold ceil32 ceilDiv
        split <;> split <;> omega
      exact Nat.le_trans (hceil _) (Nat.mul_le_mul_left 32 (Nat.le_max_right _ _))

theorem pot_codesize {pc : Nat} {sevm : Sevm} {d d' : Devm} {xl : Xlot}
    (hstep : Ninst.StepRun pc sevm d (.reg .codesize) xl (.ok d')) :
    d'.gasMeasure + calculateMemoryGasCost d'.memory.size ≤
      d.gasMeasure + calculateMemoryGasCost d.memory.size := by
  unfold Ninst.StepRun at hstep
  rw [Ninst.step_reg, Step.run_ofExecution] at hstep
  have h : pushItem sevm.code.size.toB256 gBase d = .ok d' := hstep.2.symm
  rw [pushItem_def] at h
  obtain ⟨d₁, hc, hp⟩ := Except.bind_eq_ok h
  have hg₁ := chargeGas_gasMeasure hc
  have hm₁ := chargeGas_memory_size hc
  have hg₂ := Devm.push_gasMeasure hp
  have hm₂ := Devm.push_memory hp
  rw [hm₂, hm₁]
  omega

theorem pot_codecopy {pc : Nat} {sevm : Sevm} {d d' : Devm} {xl : Xlot}
    (hstep : Ninst.StepRun pc sevm d (.reg .codecopy) xl (.ok d')) :
    d'.gasMeasure + calculateMemoryGasCost d'.memory.size ≤
      d.gasMeasure + calculateMemoryGasCost d.memory.size := by
  unfold Ninst.StepRun at hstep
  rw [Ninst.step_reg, Step.run_ofExecution] at hstep
  have h : Rinst.runCore pc d sevm .codecopy = .ok d' := hstep.2.symm
  simp only [Rinst.runCore] at h
  obtain ⟨⟨msi, d₁⟩, hp₁, h⟩ := Except.bind_eq_ok h
  dsimp only at h
  obtain ⟨⟨csi, d₂⟩, hp₂, h⟩ := Except.bind_eq_ok h
  dsimp only at h
  obtain ⟨⟨size, d₃⟩, hp₃, h⟩ := Except.bind_eq_ok h
  dsimp only at h
  obtain ⟨d₄, hc, h⟩ := Except.bind_eq_ok h
  simp only [Except.ok.injEq] at h
  subst h
  have hacc := charged_memExtends_accounting [(msi, size)] (gVerylow + gasCopy * ceilDiv size 32) hc
  have hw := Mem.write_size_le_ext d₄.memory msi (sevm.code.sliceD csi size (Linst.toUInt8 .stop))
  rw [ByteArray.length_sliceD] at hw
  have hmono := calculateMemoryGasCost_mono hw
  have hg₁ := Devm.popToNat_gasMeasure hp₁
  have hg₂ := Devm.popToNat_gasMeasure hp₂
  have hg₃ := Devm.popToNat_gasMeasure hp₃
  have hm₁ := Devm.popToNat_memory hp₁
  have hm₂ := Devm.popToNat_memory hp₂
  have hm₃ := Devm.popToNat_memory hp₃
  have hext : (d₄.memExtends [(msi, size)]).memory.size = memExtSize d₄.memory.size msi size := rfl
  have hextg : (d₄.memExtends [(msi, size)]).gasMeasure = d₄.gasMeasure := rfl
  have hwg : (d₄.memWrite msi (sevm.code.sliceD csi size (Linst.toUInt8 .stop))).gasMeasure =
      d₄.gasMeasure := rfl
  have hwm : (d₄.memWrite msi (sevm.code.sliceD csi size (Linst.toUInt8 .stop))).memory =
      d₄.memory.write msi (sevm.code.sliceD csi size (Linst.toUInt8 .stop)) := rfl
  rw [hwg, hwm]
  rw [hm₃, hm₂, hm₁] at hacc
  rw [hext, hextg] at hacc
  omega

/-! ## The headline: potential never grows along one lifted step -/

/-- **Potential never grows along one instruction step** (Jaune's `Evm.step_memory_accounting_output`
for non-spawning steps; the spawn case from `Frame.enter_done_gasLe`/`Frame.settle_gasLe`). -/
theorem Ninst.Run.pot {sevm : Sevm} {d d' : Devm} {n : Ninst}
    (hsg : sevm.benvStat.rules.stateGas = none) (run : Ninst.Run sevm d n d') :
    d'.gasMeasure + calculateMemoryGasCost d'.memory.size ≤
      d.gasMeasure + calculateMemoryGasCost d.memory.size := by
  obtain ⟨xl, hfill, pc, hstep⟩ := run
  by_cases h1 : n = .reg .codesize
  · subst h1; exact pot_codesize hstep
  by_cases h2 : n = .reg .codecopy
  · subst h2; exact pot_codecopy hstep
  obtain ⟨exc⟩ := Ninst.StepRun.exec_codeAt hfill hstep h1 h2
  exact Exec.pot_le (sevm := { sevm with code := codeAt pc n }) hsg exc

theorem Pot.step {sevm : Sevm} {d d' : Devm} {n : Ninst}
    (hsg : sevm.benvStat.rules.stateGas = none) (run : Ninst.Run sevm d n d') (pot : Pot d) :
    Pot d' :=
  Nat.lt_of_le_of_lt (Ninst.Run.pot hsg run) pot

/-! ## Along a synthetic run -/

theorem Pot.popBurn {xs : List B256} {d d' : Devm} (h : Devm.PopBurn xs d d') (pot : Pot d) :
    Pot d' := by
  unfold Pot at pot ⊢
  have hm : d.memory = d'.memory := h.memory
  have hg : d.gasLeft ≥ d'.gasLeft := h.gasLeft
  have hs : d.mach.stateGas = d'.mach.stateGas := h.stateGas
  rw [Devm.gasMeasure_def] at pot ⊢
  rw [← hs, ← hm]
  omega

theorem Pot.burn {d d' : Devm} (h : Devm.Burn d d') (pot : Pot d) : Pot d' := by
  unfold Pot at pot ⊢
  have hm : d.memory = d'.memory := h.memory
  have hg : d.gasLeft ≥ d'.gasLeft := h.gasLeft
  have hs : d.mach.stateGas = d'.mach.stateGas := h.stateGas
  rw [Devm.gasMeasure_def] at pot ⊢
  rw [← hs, ← hm]
  omega

theorem Pot.linst {sevm : Sevm} {d d' : Devm} {l : Linst}
    (hsg : sevm.benvStat.rules.stateGas = none) (h : Linst.Run sevm d l (.ok d')) (pot : Pot d) :
    Pot d' := by
  have hacc := Linst.run_memory_accounting_output sevm d l hsg
  have hl : l.run sevm d = .ok d' := h
  rw [hl] at hacc
  exact Nat.lt_of_le_of_lt hacc.1 pot

/-- **A run from a state of bounded potential records it at every step.** -/
theorem SFunc.RunP.withPot {P : Sevm → Devm → Ninst → Devm → Prop}
    (hP : ∀ {s d n d'}, P s d n d' → Ninst.Run s d n d')
    {fs : List SFunc} {sevm : Sevm} (hsg : sevm.benvStat.rules.stateGas = none)
    {d : Devm} {f : SFunc} {o : Outcome} (run : SFunc.RunP P fs sevm d f o) (pot : Pot d) :
    SFunc.RunP (PotStep P) fs sevm d f o ∧ Pot o.devm := by
  induction run with
  | zero w hpop _ ih =>
    obtain ⟨r, p⟩ := ih (Pot.popBurn hpop pot)
    exact ⟨.zero w hpop r, p⟩
  | succ w v hv hpop _ ih =>
    obtain ⟨r, p⟩ := ih (Pot.popBurn hpop pot)
    exact ⟨.succ w v hv hpop r, p⟩
  | toZero w hpop _ ih =>
    obtain ⟨r, p⟩ := ih (Pot.popBurn hpop pot)
    exact ⟨.toZero w hpop r, p⟩
  | toSucc w v hv hk hpop _ ih =>
    obtain ⟨r, p⟩ := ih (Pot.popBurn hpop pot)
    exact ⟨.toSucc w v hv hk hpop r, p⟩
  | last hl => exact ⟨.last hl, Pot.linst hsg hl pot⟩
  | next hp _ ih =>
    have pot' := Pot.step hsg (hP hp) pot
    obtain ⟨r, p⟩ := ih pot'
    exact ⟨.next ⟨hp, pot, pot'⟩ r, p⟩
  | dest hb _ ih =>
    obtain ⟨r, p⟩ := ih (Pot.burn hb pot)
    exact ⟨.dest hb r, p⟩
  | jump w hk hpop _ ih =>
    obtain ⟨r, p⟩ := ih (Pot.popBurn hpop pot)
    exact ⟨.jump w hk hpop r, p⟩
  | ret w hpop => exact ⟨.ret w hpop, Pot.popBurn hpop pot⟩
  | callHalt w hk hpop _ ih =>
    obtain ⟨r, p⟩ := ih (Pot.popBurn hpop pot)
    exact ⟨.callHalt w hk hpop r, p⟩
  | callRet w hk hpop _ _ ihg ihf =>
    obtain ⟨rg, pg⟩ := ihg (Pot.popBurn hpop pot)
    obtain ⟨rf, pf⟩ := ihf pg
    exact ⟨.callRet w hk hpop rg rf, pf⟩
  | pcAt hp hsr _ ih =>
    have pot' := Pot.step hsg (hP hp) pot
    obtain ⟨r, p⟩ := ih pot'
    exact ⟨.pcAt ⟨hp, pot, pot'⟩ hsr r, p⟩

end Blanc.Lift.FreePtr
