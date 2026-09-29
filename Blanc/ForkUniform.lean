import Blanc.Semantics

/-!
# Fork uniformity between covered forks

Jaune's machines carry a fork identity and read rule data only through
`BenvStat.rules = Fork.ruleSet fork`.  Between the covered forks (Prague, Osaka, BPO1, BPO2)
the rule records differ only in the fork label, the blob schedule, transaction and block
limits, the `MODEXP` rules, `op.clz` and the precompile set (Osaka adds `P256VERIFY` at
0x100).  At message level exactly four reads see a difference: `CLZ` (`op.clz`),
`BLOBBASEFEE` (the blob schedule), frame entry (`isPrecomp`) and `MODEXP` (`rules.modexp`).

`withFork g` replaces the fork and nothing else.  Under covered forks:

* `evm_step_withFork`: one driver step commutes with the change at a node whose instruction
  is not `CLZ` (and is `BLOBBASEFEE` only at zero excess blob gas): same outcome, the spawned
  frame with its fork changed;
* `frame_enter_withFork`, `settle_withFork`: entry commutes for a frame that avoids `MODEXP`
  and `P256VERIFY`; settlement is unchanged;
* `Exec.withFork`: a derivation satisfying `ExecNeutral` is, node for node, a derivation under
  the other fork with the same outcome; `exec_withFork`, `exec_out_withFork`,
  `runFrame_withFork`, `processMessage_withFork`, `processCreateMessage_withFork` state the
  consequences for the total interpreter and for messages.

The walk-engine counterpart that transports closed witnesses is
`Blanc/Lift/NodeWalkFork.lean`.
-/

namespace Jaune

/-- Replace the fork, nothing else. -/
def BenvStat.withFork (s : BenvStat) (g : Fork) : BenvStat := { s with fork := g }
def Benv.withFork (b : Benv) (g : Fork) : Benv := { b with stat := b.stat.withFork g }
def Sevm.withFork (s : Sevm) (g : Fork) : Sevm := { s with benvStat := s.benvStat.withFork g }
def Evm.withFork (e : Evm) (g : Fork) : Evm := { e with sta := e.sta.withFork g }
def Msg.withFork (m : Msg) (g : Fork) : Msg := { m with benv := m.benv.withFork g }
def Frame.withFork (f : Frame) (g : Fork) : Frame :=
  ⟨f.outer.withFork g, f.inner.withFork g, f.isCreate⟩

def Step.withFork (g : Fork) : Step → Step
  | .halt ex => .halt ex
  | .cont pc d => .cont pc d
  | .spawn f rsm pc => .spawn (f.withFork g) rsm pc

def XStep.withFork (g : Fork) : XStep → XStep
  | .done ex => .done ex
  | .spawn f rsm => .spawn (f.withFork g) rsm

/-- A frame whose entry does not reach a fork-sensitive precompile: precompiles are
disabled, or its code address is neither `MODEXP` (0x05, EIP-7823/7883) nor `P256VERIFY`
(0x100, EIP-7951). -/
def Frame.PrecompNeutral (f : Frame) : Prop :=
  f.inner.disablePrecompiles = true ∨ ∀ a, f.inner.codeAddress = some a → a ≠ 5 ∧ a ≠ 0x100

theorem Frame.precompNeutral_of_codeAddress {f : Frame} {a : Adr}
    (h : f.inner.codeAddress = some a) (h5 : a ≠ 5) (h100 : a ≠ 0x100) : f.PrecompNeutral :=
  Or.inr fun b hb => by
    rw [h] at hb
    cases hb
    exact ⟨h5, h100⟩

def FrameEntry.withFork (g : Fork) : FrameEntry → FrameEntry
  | .done r => .done r
  | .run e => .run (e.withFork g)

end Jaune

namespace Blanc.ForkUniform
open Jaune

section withFork
variable (s : Sevm) (g : Fork)
@[simp] theorem Sevm.withFork_caller : (s.withFork g).caller = s.caller := rfl
@[simp] theorem Sevm.withFork_target : (s.withFork g).target = s.target := rfl
@[simp] theorem Sevm.withFork_currentTarget : (s.withFork g).currentTarget = s.currentTarget := rfl
@[simp] theorem Sevm.withFork_gas : (s.withFork g).gas = s.gas := rfl
@[simp] theorem Sevm.withFork_value : (s.withFork g).value = s.value := rfl
@[simp] theorem Sevm.withFork_data : (s.withFork g).data = s.data := rfl
@[simp] theorem Sevm.withFork_codeAddress : (s.withFork g).codeAddress = s.codeAddress := rfl
@[simp] theorem Sevm.withFork_code : (s.withFork g).code = s.code := rfl
@[simp] theorem Sevm.withFork_depth : (s.withFork g).depth = s.depth := rfl
@[simp] theorem Sevm.withFork_isStatic : (s.withFork g).isStatic = s.isStatic := rfl
@[simp] theorem Sevm.withFork_tenvStat : (s.withFork g).tenvStat = s.tenvStat := rfl
@[simp] theorem Sevm.withFork_fork : (s.withFork g).benvStat.fork = g := rfl
theorem Sevm.withFork_self : s.withFork s.benvStat.fork = s := rfl
end withFork

/-- A function of the static machine that agrees with its Prague reading under every
covered fork agrees under any two covered forks. -/
theorem eq_of_prague {α : Sort _} (F : Sevm → α) {s : Sevm} {g : Fork}
    (hf : CoveredFork s.benvStat.fork) (hg : CoveredFork g)
    (h : ∀ g, CoveredFork g → F (s.withFork g) = F (s.withFork .prague)) :
    F (s.withFork g) = F s :=
  (h g hg).trans (h _ hf).symm

/-- `BLOBBASEFEE` with no excess blob gas is `1` under every valid blob schedule. -/
theorem calculateBlobGasPrice_zero (b : BlobSchedule) (h : 0 < b.baseFeeUpdateFraction) :
    calculateBlobGasPrice b 0 = 1 := by
  have h0 : b.baseFeeUpdateFraction ≠ 0 := by omega
  rw [calculateBlobGasPrice_eq, fakeExpAux]
  simp [h0, Nat.div_self h]

/-- Every instruction but `CLZ` (EIP-7939, defined from Osaka) and `BLOBBASEFEE` (it reads the
blob schedule BPO1/BPO2 move) runs identically under covered forks; `BLOBBASEFEE` too when the
block carries no excess blob gas. -/
theorem rinst_runCore_withFork {s : Sevm} {g : Fork} (hf : CoveredFork s.benvStat.fork)
    (hg : CoveredFork g) (pc : Nat) (d : Devm) (r : Rinst)
    (h1 : r ≠ .clz) (h2 : r = .blobbasefee → s.benvStat.excessBlobGas = 0) :
    Rinst.runCore pc d (s.withFork g) r = Rinst.runCore pc d s r := by
  by_cases hb : r = .blobbasefee
  · subst hb
    have hx := h2 rfl
    show pushItem (calculateBlobGasPrice (Fork.ruleSet g).blob s.benvStat.excessBlobGas).toB256
        gBase d = pushItem (calculateBlobGasPrice s.benvStat.rules.blob
          s.benvStat.excessBlobGas).toB256 gBase d
    rw [hx, calculateBlobGasPrice_zero (Fork.ruleSet g).blob (BenvStat.rules_valid (s.withFork g).benvStat).1.1,
      calculateBlobGasPrice_zero _ (BenvStat.rules_valid s.benvStat).1.1]
  refine eq_of_prague (fun s => Rinst.runCore pc d s r) hf hg fun g hg => ?_
  refine hg.cases (motive := fun g => Rinst.runCore pc d (s.withFork g) r =
    Rinst.runCore pc d (s.withFork .prague) r) rfl ?_ ?_ ?_ <;>
  cases r <;> first | exact absurd rfl h1 | exact absurd rfl hb | rfl

theorem linst_run_withFork {s : Sevm} {g : Fork} (hf : CoveredFork s.benvStat.fork)
    (hg : CoveredFork g) (d : Devm) (l : Linst) :
    Linst.run (s.withFork g) d l = Linst.run s d l := by
  refine eq_of_prague (fun s => Linst.run s d l) hf hg fun g hg => ?_
  refine hg.cases (motive := fun g => Linst.run (s.withFork g) d l =
    Linst.run (s.withFork .prague) d l) rfl ?_ ?_ ?_ <;>
  cases l <;> rfl

/-! ### Call-family and create steps -/

theorem except_map_bind {ε α β γ : Type} (m : Except ε α) (k : α → Except ε β) (f : β → γ) :
    Except.map f (m >>= k) = m >>= fun a => Except.map f (k a) := by
  cases m <;> rfl

theorem except_map_pure {ε α β : Type} (f : α → β) (a : α) :
    Except.map f (pure a : Except ε α) = pure (f a) := rfl

theorem except_map_ok {ε α β : Type} (f : α → β) (a : α) :
    Except.map f (Except.ok a : Except ε α) = Except.ok (f a) := rfl

theorem except_map_error {ε α β : Type} (f : α → β) (e : ε) :
    Except.map f (Except.error e : Except ε α) = Except.error e := rfl

theorem XStep.withFork_ofExcept (g : Fork) (m : Except (EvmError × Devm) XStep) :
    (XStep.ofExcept m).withFork g = XStep.ofExcept (m.map (XStep.withFork g)) := by
  cases m <;> rfl

@[simp] theorem XStep.withFork_done (g : Fork) (ex : Execution) :
    (XStep.done ex).withFork g = .done ex := rfl

theorem genericCall_step_withFork (s : Sevm) (g : Fork) (d : Devm) (gas : Nat) (value : B256)
    (caller target codeAddress : Adr) (stv isStaticcall : Bool)
    (ii is oi os : Nat) (code : ByteArray) (dp : Bool) :
    genericCall.step (s.withFork g) d gas value caller target codeAddress stv isStaticcall
        ii is oi os code dp =
      (genericCall.step s d gas value caller target codeAddress stv isStaticcall
        ii is oi os code dp).withFork g := by
  unfold genericCall.step
  simp only [Sevm.withFork_depth]
  by_cases h : s.depth = 0
  · simp only [h, ↓reduceIte, XStep.withFork_ofExcept, except_map_bind, except_map_pure,
      XStep.withFork_done]
  · simp only [h, ↓reduceIte]
    rfl

theorem assertDynamic_withFork (s : Sevm) (g : Fork) (d : Devm) :
    assertDynamic (s.withFork g) d = assertDynamic s d := rfl

theorem spawn_ofCreate_withFork (s : Sevm) (g : Fork) (d : Devm) (cg : Nat) (e : B256)
    (a : Adr) (cd : Bytes) (r : Resume) :
    (XStep.spawn (Frame.ofCreate (createMsg s d cg e a cd)) r).withFork g =
      .spawn (Frame.ofCreate (createMsg (s.withFork g) d cg e a cd)) r := rfl

theorem genericCreate_step_withFork {s : Sevm} {g : Fork} (hf : CoveredFork s.benvStat.fork)
    (hg : CoveredFork g) (d : Devm) (endowment : B256) (newAddress : Adr) (mi ms : Nat) :
    genericCreate.step (s.withFork g) d endowment newAddress mi ms =
      (genericCreate.step s d endowment newAddress mi ms).withFork g := by
  have hcode : (s.withFork g).benvStat.rules.code = s.benvStat.rules.code :=
    eq_of_prague (fun s => s.benvStat.rules.code) hf hg fun _ hg =>
      hg.cases (motive := fun g => (s.withFork g).benvStat.rules.code =
        (s.withFork .prague).benvStat.rules.code) rfl rfl rfl rfl
  unfold genericCreate.step
  rw [XStep.withFork_ofExcept]
  simp only [hcode, except_map_bind, except_map_pure, XStep.withFork_done,
    apply_ite (Except.map _), assertDynamic_withFork, Sevm.withFork_currentTarget,
    Sevm.withFork_depth, spawn_ofCreate_withFork]
  rfl

theorem rules_gas_withFork {s : Sevm} {g : Fork} (hf : CoveredFork s.benvStat.fork)
    (hg : CoveredFork g) : (s.withFork g).benvStat.rules.gas = s.benvStat.rules.gas :=
  eq_of_prague (fun s => s.benvStat.rules.gas) hf hg fun _ hg =>
    hg.cases (motive := fun g => (s.withFork g).benvStat.rules.gas =
      (s.withFork .prague).benvStat.rules.gas) rfl rfl rfl rfl

theorem xinst_step_withFork {s : Sevm} {g : Fork} (hf : CoveredFork s.benvStat.fork)
    (hg : CoveredFork g) (d : Devm) (x : Xinst) :
    Xinst.step (s.withFork g) d x = (Xinst.step s d x).withFork g := by
  have hsg : (s.withFork g).benvStat.rules.stateGas = none :=
    CoveredFork.rules_stateGas_none (s := (s.withFork g).benvStat) hg
  have hsf : s.benvStat.rules.stateGas = none := hf.rules_stateGas_none
  have hgas := rules_gas_withFork hf hg
  cases x <;> simp only [Xinst.step, hsg, hsf] <;> rw [XStep.withFork_ofExcept] <;>
    simp only [hgas, except_map_bind, except_map_pure, XStep.withFork_done,
      apply_ite (Except.map _), Sevm.withFork_currentTarget, Sevm.withFork_isStatic,
      genericCall_step_withFork, genericCreate_step_withFork hf hg] <;> rfl

/-! ### One driver step -/

/-- The instruction at `pc` in `s` runs identically under every covered fork: it is not
`CLZ`, and if it is `BLOBBASEFEE` the block carries no excess blob gas. -/
def InstNeutralAt (s : Sevm) (pc : Nat) : Prop :=
  s.code.getInst pc ≠ some (.next (.reg .clz)) ∧
    (s.code.getInst pc = some (.next (.reg .blobbasefee)) → s.benvStat.excessBlobGas = 0)

theorem Step.withFork_ofExecution (g : Fork) (pc : Nat) (ex : Execution) :
    (Step.ofExecution pc ex).withFork g = Step.ofExecution pc ex := by
  cases ex <;> rfl

theorem Step.withFork_ofJump (g : Fork) (r : Except (EvmError × Devm) (Nat × Devm)) :
    (Step.ofJump r).withFork g = Step.ofJump r := by
  cases r <;> rfl

theorem Step.withFork_toStep (g : Fork) (pc : Nat) (x : XStep) :
    (XStep.toStep pc x).withFork g = XStep.toStep pc (x.withFork g) := by
  cases x with
  | done ex => exact Step.withFork_ofExecution g pc ex
  | spawn f r => rfl

theorem stackAccess_withFork {s : Sevm} {g : Fork} (hf : CoveredFork s.benvStat.fork)
    (hg : CoveredFork g) :
    (s.withFork g).benvStat.rules.op.stackAccess = s.benvStat.rules.op.stackAccess :=
  eq_of_prague (fun s => s.benvStat.rules.op.stackAccess) hf hg fun _ hg =>
    hg.cases (motive := fun g => (s.withFork g).benvStat.rules.op.stackAccess =
      (s.withFork .prague).benvStat.rules.op.stackAccess) rfl rfl rfl rfl

/-- **One driver step commutes with the fork change**, at a node whose instruction is
neither `CLZ` nor `BLOBBASEFEE`, between covered forks: the outcome is the same and a
spawned frame is the same frame with its fork changed. -/
theorem evm_step_withFork {e : Evm} {g : Fork} (hf : CoveredFork e.sta.benvStat.fork)
    (hg : CoveredFork g) (hn : InstNeutralAt e.sta e.pc) :
    (e.withFork g).step = e.step.withFork g := by
  have hi : (e.withFork g).getInst = e.getInst := rfl
  unfold Evm.step
  rw [hi]
  rcases hget : e.getInst with _ | i
  · rfl
  have hget' : e.sta.code.getInst e.pc = some i := hget
  cases i with
  | next n =>
    simp only
    cases n with
    | push xs h => exact (Step.withFork_ofExecution g _ _).symm
    | reg r =>
      show Step.ofExecution _ (Rinst.runCore e.pc e.dyna (e.sta.withFork g) r) = _
      rw [rinst_runCore_withFork hf hg e.pc e.dyna r (by rintro rfl; exact hn.1 hget')
        (by rintro rfl; exact hn.2 hget')]
      exact (Step.withFork_ofExecution g _ _).symm
    | exec x =>
      show XStep.toStep _ (Xinst.step (e.sta.withFork g) e.dyna x) = _
      rw [xinst_step_withFork hf hg]
      exact (Step.withFork_toStep g _ _).symm
    | dupn imm =>
      show Step.ofExecution _ _ = _
      simp only [Ninst.step, Evm.withFork, stackAccess_withFork hf hg]
      exact (Step.withFork_ofExecution g _ _).symm
    | swapn imm =>
      show Step.ofExecution _ _ = _
      simp only [Ninst.step, Evm.withFork, stackAccess_withFork hf hg]
      exact (Step.withFork_ofExecution g _ _).symm
    | exchange imm =>
      show Step.ofExecution _ _ = _
      simp only [Ninst.step, Evm.withFork, stackAccess_withFork hf hg]
      exact (Step.withFork_ofExecution g _ _).symm
  | jump j => exact (Step.withFork_ofJump g _).symm
  | last l =>
    show Step.halt (Linst.run (e.sta.withFork g) e.dyna l) = _
    rw [linst_run_withFork hf hg]
    rfl

/-! ### Frame entry and settlement -/

theorem executePrecomp_withFork (e : Evm) (g : Fork) (adr : Adr) (h5 : adr ≠ 5) :
    executePrecomp (e.withFork g) adr = executePrecomp e adr := by
  have hrun : precompileRun (e.withFork g) adr = precompileRun e adr := by
    unfold precompileRun
    split <;> first | exact absurd rfl h5 | rfl
  unfold executePrecomp
  rw [hrun]
  rfl

theorem isPrecomp_withFork {f g : Fork} (hf : CoveredFork f) (hg : CoveredFork g) {adr : Adr}
    (h : adr ≠ 0x100) : (Fork.ruleSet g).isPrecomp adr ↔ (Fork.ruleSet f).isPrecomp adr := by
  have key : ∀ g, CoveredFork g → ((Fork.ruleSet g).isPrecomp adr ↔ adr ∈ praguePrecompiles) :=
    fun _ hg => hg.cases (motive := fun g => (Fork.ruleSet g).isPrecomp adr ↔ adr ∈ praguePrecompiles)
      Iff.rfl
      (by simp [ForkRules.isPrecomp, Fork.ruleSet, osakaRules, osakaPrecompiles, h])
      (by simp [ForkRules.isPrecomp, Fork.ruleSet, bpo1Rules, osakaRules, osakaPrecompiles, h])
      (by simp [ForkRules.isPrecomp, Fork.ruleSet, bpo2Rules, osakaRules, osakaPrecompiles, h])
  exact (key g hg).trans (key f hf).symm

theorem msg_eq_of_prague {α : Sort _} (F : Msg → α) {m : Msg} {g : Fork}
    (hf : CoveredFork m.benv.stat.fork) (hg : CoveredFork g)
    (h : ∀ g, CoveredFork g → F (m.withFork g) = F (m.withFork .prague)) :
    F (m.withFork g) = F m :=
  (h g hg).trans (h _ hf).symm

theorem processCreateMessage_settle_withFork {m : Msg} {g : Fork}
    (hf : CoveredFork m.benv.stat.fork) (hg : CoveredFork g)
    (r : Except (EvmError × State × AdrSet × Tra) Devm) :
    processCreateMessage.settle (m.withFork g) r = processCreateMessage.settle m r :=
  msg_eq_of_prague (fun m => processCreateMessage.settle m r) hf hg fun _ hg =>
    hg.cases (motive := fun g => processCreateMessage.settle (m.withFork g) r =
      processCreateMessage.settle (m.withFork .prague) r) rfl rfl rfl rfl

theorem settleMsg_withFork {f : Frame} {g : Fork} (ho : CoveredFork f.outer.benv.stat.fork)
    (hg : CoveredFork g) (r : Except (EvmError × State × AdrSet × Tra) Devm) :
    (f.withFork g).settleMsg r = f.settleMsg r := by
  unfold Frame.settleMsg
  show (if f.isCreate then processCreateMessage.settle (f.outer.withFork g)
      (processMessage.settle f.inner r) else processMessage.settle f.inner r) = _
  rw [processCreateMessage_settle_withFork ho hg]

/-- **Settlement is fork-insensitive** between covered forks. -/
theorem settle_withFork {f : Frame} {g : Fork} (ho : CoveredFork f.outer.benv.stat.fork)
    (hi : CoveredFork f.inner.benv.stat.fork) (hg : CoveredFork g) (raw : Execution) :
    (f.withFork g).settle raw = f.settle raw := by
  unfold Frame.settle
  have h1 : (f.withFork g).inner.benv.stat.rules.stateGas = none :=
    CoveredFork.rules_stateGas_none (s := (f.withFork g).inner.benv.stat) hg
  rw [h1, hi.rules_stateGas_none, settleMsg_withFork ho hg]

section msgWithFork
variable (m : Msg) (g : Fork)
@[simp] theorem Msg.withFork_codeAddress : (m.withFork g).codeAddress = m.codeAddress := rfl
@[simp] theorem Msg.withFork_disablePrecompiles :
    (m.withFork g).disablePrecompiles = m.disablePrecompiles := rfl
@[simp] theorem Msg.withFork_shouldTransferValue :
    (m.withFork g).shouldTransferValue = m.shouldTransferValue := rfl
@[simp] theorem Msg.withFork_caller : (m.withFork g).caller = m.caller := rfl
@[simp] theorem Msg.withFork_value : (m.withFork g).value = m.value := rfl
@[simp] theorem Msg.withFork_currentTarget : (m.withFork g).currentTarget = m.currentTarget := rfl
@[simp] theorem Msg.withFork_benv_state : (m.withFork g).benv.state = m.benv.state := rfl
@[simp] theorem Msg.withFork_rules : (m.withFork g).benv.stat.rules = Fork.ruleSet g := rfl
end msgWithFork

theorem initEvm_withFork {m : Msg} {g : Fork} (hf : CoveredFork m.benv.stat.fork)
    (hg : CoveredFork g) : initEvm (m.withFork g) = (initEvm m).withFork g := by
  have h : ∀ g, CoveredFork g → initEvm (m.withFork g) = (initEvm (m.withFork .prague)).withFork g :=
    fun _ hg => hg.cases (motive := fun g => initEvm (m.withFork g) =
      (initEvm (m.withFork .prague)).withFork g) rfl rfl rfl rfl
  have h2 : (initEvm (m.withFork m.benv.stat.fork)).withFork g =
      ((initEvm (m.withFork .prague)).withFork m.benv.stat.fork).withFork g := by
    rw [h _ hf]
  exact (h g hg).trans h2.symm

theorem benvAfterTransfer_withFork (m : Msg) (g : Fork) :
    (m.withFork g).benvAfterTransfer = m.benvAfterTransfer.map (·.withFork g) := by
  unfold Msg.benvAfterTransfer Benv.subBal
  simp only [Msg.withFork_shouldTransferValue, Msg.withFork_benv_state, Msg.withFork_caller,
    Msg.withFork_value]
  by_cases h : m.shouldTransferValue = true <;> simp only [h, ↓reduceIte, Bool.false_eq_true]
  · cases m.benv.state.subBal m.caller m.value <;> rfl
  · rfl

theorem executeCode_enter_withFork {m : Msg} {g : Fork} (hf : CoveredFork m.benv.stat.fork)
    (hg : CoveredFork g)
    (hp : m.disablePrecompiles = true ∨ ∀ a, m.codeAddress = some a → a ≠ 5 ∧ a ≠ 0x100) :
    executeCode.enter (m.withFork g) = (executeCode.enter m).map (·.withFork g) id := by
  unfold executeCode.enter
  simp only [initEvm_withFork hf hg, Msg.withFork_codeAddress, Msg.withFork_disablePrecompiles,
    Msg.withFork_rules]
  cases hc : m.codeAddress with
  | none => rfl
  | some adr =>
    rcases hp with hdp | hn
    · simp [hdp]
    · obtain ⟨h5, h100⟩ := hn adr hc
      have hiff := isPrecomp_withFork (adr := adr) hf hg h100
      by_cases hpre : (Fork.ruleSet m.benv.stat.fork).isPrecomp adr
      · have hpre' := hiff.mpr hpre
        by_cases hdp : m.disablePrecompiles = true
        · simp [hdp]
        · have hr : m.benv.stat.rules.isPrecomp adr := hpre
          simp [hdp, hr, hpre', executePrecomp_withFork _ _ _ h5]
      · have hpre' : ¬ (Fork.ruleSet g).isPrecomp adr := fun h => hpre (hiff.mp h)
        have hr : ¬ m.benv.stat.rules.isPrecomp adr := hpre
        simp [hr, hpre']

/-- Frame entry through any value-transfer function that commutes with the fork change and
keeps the block environment's static part: the shape shared by `Frame.enter` and the
witness engine's shadow entries. -/
theorem enterVia_withFork {T : Msg → Except (EvmError × State × AdrSet × Tra) Benv}
    {f : Frame} {g : Fork}
    (hT : T (f.inner.withFork g) = (T f.inner).map (·.withFork g))
    (hstat : ∀ b, T f.inner = .ok b → b.stat = f.inner.benv.stat)
    (ho : CoveredFork f.outer.benv.stat.fork) (hi : CoveredFork f.inner.benv.stat.fork)
    (hg : CoveredFork g) (hp : f.PrecompNeutral) :
    (match T (f.inner.withFork g) with
      | .error e => FrameEntry.done ((f.withFork g).settleMsg (.error e))
      | .ok benv =>
        match executeCode.enter ((f.inner.withFork g).withBenv benv) with
        | .inl evm => .run evm
        | .inr raw => .done ((f.withFork g).settle raw)) =
    (match T f.inner with
      | .error e => FrameEntry.done (f.settleMsg (.error e))
      | .ok benv =>
        match executeCode.enter (f.inner.withBenv benv) with
        | .inl evm => .run evm
        | .inr raw => .done (f.settle raw)).withFork g := by
  rw [hT]
  cases hb : T f.inner with
  | error e =>
    show FrameEntry.done ((f.withFork g).settleMsg (.error e)) = _
    rw [settleMsg_withFork ho hg]
    rfl
  | ok benv =>
    have hstat := hstat benv hb
    have hm : (f.inner.withFork g).withBenv (benv.withFork g) = (f.inner.withBenv benv).withFork g :=
      rfl
    have hcov : CoveredFork (f.inner.withBenv benv).benv.stat.fork := by
      show CoveredFork benv.stat.fork
      rw [hstat]; exact hi
    show (match executeCode.enter ((f.inner.withFork g).withBenv (benv.withFork g)) with
      | .inl evm => FrameEntry.run evm
      | .inr raw => .done ((f.withFork g).settle raw)) = _
    rw [hm, executeCode_enter_withFork hcov hg hp]
    rcases he : executeCode.enter (f.inner.withBenv benv) with e | raw
    · simp only [he, Sum.map_inl]
      rfl
    · simp only [he, Sum.map_inr, id, settle_withFork ho hi hg]
      rfl

/-- **Frame entry commutes with the fork change** between covered forks, for a frame that
does not enter `MODEXP` or `P256VERIFY`. -/
theorem frame_enter_withFork {f : Frame} {g : Fork} (ho : CoveredFork f.outer.benv.stat.fork)
    (hi : CoveredFork f.inner.benv.stat.fork) (hg : CoveredFork g) (hp : f.PrecompNeutral) :
    (f.withFork g).enter = f.enter.withFork g :=
  enterVia_withFork (T := Msg.benvAfterTransfer) (benvAfterTransfer_withFork _ _)
    (fun _ hb => benvAfterTransfer_stat hb) ho hi hg hp

/-! ### Complete derivations -/


/-- Every node of the derivation executes a fork-neutral instruction and every frame it
spawns is precompile-neutral (its children recursively so). -/
def ExecNeutral : {pc : Nat} → {s : Sevm} → {d : Devm} → {ex : Execution} →
    Exec pc s d ex → Prop
  | pc, s, _, _, .halt _ => InstNeutralAt s pc
  | pc, s, _, _, .cont _ R => InstNeutralAt s pc ∧ ExecNeutral R
  | pc, s, _, _, @Exec.doneErr _ _ _ f _ _ _ _ _ _ _ => InstNeutralAt s pc ∧ f.PrecompNeutral
  | pc, s, _, _, @Exec.doneOk _ _ _ f _ _ _ _ _ _ _ _ R =>
    InstNeutralAt s pc ∧ f.PrecompNeutral ∧ ExecNeutral R
  | pc, s, _, _, @Exec.runErr _ _ _ f _ _ _ _ _ _ _ C _ =>
    InstNeutralAt s pc ∧ f.PrecompNeutral ∧ ExecNeutral C
  | pc, s, _, _, @Exec.runOk _ _ _ f _ _ _ _ _ _ _ _ C _ R =>
    InstNeutralAt s pc ∧ f.PrecompNeutral ∧ ExecNeutral C ∧ ExecNeutral R

theorem step_withFork_at {pc : Nat} {s : Sevm} {d : Devm} {g : Fork}
    (hf : CoveredFork s.benvStat.fork) (hg : CoveredFork g) (hn : InstNeutralAt s pc) :
    Evm.step ⟨pc, s.withFork g, d⟩ = (Evm.step ⟨pc, s, d⟩).withFork g :=
  evm_step_withFork (e := ⟨pc, s, d⟩) hf hg hn

/-- A spawned frame carries the parent's fork in both of its messages. -/
theorem spawn_fork {pc : Nat} {s : Sevm} {d : Devm} {f : Frame} {rsm : Resume} {pc' : Nat}
    (hf : CoveredFork s.benvStat.fork) (hn : InstNeutralAt s pc)
    (h : Evm.step ⟨pc, s, d⟩ = .spawn f rsm pc') : f.withFork s.benvStat.fork = f := by
  have := step_withFork_at (d := d) hf hf hn
  rw [Sevm.withFork_self, h] at this
  simp only [Step.withFork, Step.spawn.injEq] at this
  exact this.1.symm

theorem frame_self_forks {f : Frame} {f0 : Fork} (h : f.withFork f0 = f) :
    f.outer.benv.stat.fork = f0 ∧ f.inner.benv.stat.fork = f0 := by
  rw [← h]; exact ⟨rfl, rfl⟩

/-- The entered machine carries the frame's fork. -/
theorem enter_fork {f : Frame} {f0 : Fork} {cevm : Evm} (hf0 : CoveredFork f0)
    (hself : f.withFork f0 = f) (hp : f.PrecompNeutral) (he : f.enter = .run cevm) :
    cevm.sta.benvStat.fork = f0 := by
  obtain ⟨ho, hi⟩ := frame_self_forks hself
  have := frame_enter_withFork (g := f0) (ho ▸ hf0) (hi ▸ hf0) hf0 hp
  rw [hself, he] at this
  simp only [FrameEntry.withFork, FrameEntry.run.injEq] at this
  rw [this]; rfl

/-- **Transport of a complete derivation** between covered forks: a fork-neutral
derivation from `s` is, node for node, a derivation from `s.withFork g` with the same
outcome. -/
def Exec.withFork {g : Fork} (hg : CoveredFork g) :
    {pc : Nat} → {s : Sevm} → {d : Devm} → {ex : Execution} →
    (R : Exec pc s d ex) → CoveredFork s.benvStat.fork → ExecNeutral R →
    Exec pc (s.withFork g) d ex
  | pc, s, d, _, .halt h, hf, hn =>
    have hn : InstNeutralAt s pc := hn
    .halt (by rw [step_withFork_at (d := d) hf hg hn, h]; rfl)
  | pc, s, d, _, .cont h R, hf, hn =>
    have hn : InstNeutralAt s pc ∧ ExecNeutral R := hn
    .cont (by rw [step_withFork_at (d := d) hf hg hn.1, h]; rfl) (Exec.withFork hg R hf hn.2)
  | pc, s, d, _, @Exec.doneErr _ _ _ f _ _ _ _ h he hr, hf, hn =>
    have hn : InstNeutralAt s pc ∧ f.PrecompNeutral := hn
    have hself := spawn_fork hf hn.1 h
    have hfs := frame_self_forks hself
    .doneErr (f := f.withFork g) (by rw [step_withFork_at (d := d) hf hg hn.1, h]; rfl)
      (by rw [frame_enter_withFork (hfs.1 ▸ hf) (hfs.2 ▸ hf) hg hn.2, he]; rfl) hr
  | pc, s, d, _, @Exec.doneOk _ _ _ f _ _ _ _ _ h he hr R, hf, hn =>
    have hn : InstNeutralAt s pc ∧ f.PrecompNeutral ∧ ExecNeutral R := hn
    have hself := spawn_fork hf hn.1 h
    have hfs := frame_self_forks hself
    .doneOk (f := f.withFork g) (by rw [step_withFork_at (d := d) hf hg hn.1, h]; rfl)
      (by rw [frame_enter_withFork (hfs.1 ▸ hf) (hfs.2 ▸ hf) hg hn.2.1, he]; rfl) hr
      (Exec.withFork hg R hf hn.2.2)
  | pc, s, d, _, @Exec.runErr _ _ _ f _ _ cevm _ _ h he C hr, hf, hn =>
    have hn : InstNeutralAt s pc ∧ f.PrecompNeutral ∧ ExecNeutral C := hn
    have hself := spawn_fork hf hn.1 h
    have hfs := frame_self_forks hself
    have hc := enter_fork hf hself hn.2.1 he
    .runErr (f := f.withFork g) (cevm := cevm.withFork g)
      (by rw [step_withFork_at (d := d) hf hg hn.1, h]; rfl)
      (by rw [frame_enter_withFork (hfs.1 ▸ hf) (hfs.2 ▸ hf) hg hn.2.1, he]; rfl)
      (Exec.withFork hg C (hc ▸ hf) hn.2.2)
      (by rw [settle_withFork (hfs.1 ▸ hf) (hfs.2 ▸ hf) hg]; exact hr)
  | pc, s, d, _, @Exec.runOk _ _ _ f _ _ cevm _ _ _ h he C hr R, hf, hn =>
    have hn : InstNeutralAt s pc ∧ f.PrecompNeutral ∧ ExecNeutral C ∧ ExecNeutral R := hn
    have hself := spawn_fork hf hn.1 h
    have hfs := frame_self_forks hself
    have hc := enter_fork hf hself hn.2.1 he
    .runOk (f := f.withFork g) (cevm := cevm.withFork g)
      (by rw [step_withFork_at (d := d) hf hg hn.1, h]; rfl)
      (by rw [frame_enter_withFork (hfs.1 ▸ hf) (hfs.2 ▸ hf) hg hn.2.1, he]; rfl)
      (Exec.withFork hg C (hc ▸ hf) hn.2.2.1)
      (by rw [settle_withFork (hfs.1 ▸ hf) (hfs.2 ▸ hf) hg]; exact hr)
      (Exec.withFork hg R hf hn.2.2.2)

/-- **The total interpreter is fork-insensitive** on a machine with a fork-neutral
derivation: `exec` returns the same outcome under any covered fork. -/
theorem exec_withFork {e : Evm} {g : Fork} (hf : CoveredFork e.sta.benvStat.fork)
    (hg : CoveredFork g) {ex : Execution} (R : Exec e.pc e.sta e.dyna ex) (hn : ExecNeutral R) :
    exec (e.withFork g) = exec e :=
  ((exec_iff_exec_eq _ _ _ _).mp ⟨Exec.withFork hg R hf hn⟩).trans
    ((exec_iff_exec_eq _ _ _ _).mp ⟨R⟩).symm

/-- Every derivation under the new fork has the transported outcome. -/
theorem exec_out_withFork {e : Evm} {g : Fork} (hf : CoveredFork e.sta.benvStat.fork)
    (hg : CoveredFork g) {ex : Execution} (R : Exec e.pc e.sta e.dyna ex) (hn : ExecNeutral R)
    {out : Execution} (R' : Exec e.pc (e.sta.withFork g) e.dyna out) : out = ex :=
  ((exec_iff_exec_eq _ _ _ _).mp ⟨R'⟩).symm.trans
    ((exec_iff_exec_eq _ _ _ _).mp ⟨Exec.withFork hg R hf hn⟩)

/-- A frame whose entered machine (if any) has a fork-neutral derivation. -/
def RunNeutral (f : Frame) : Prop :=
  ∀ cevm, f.enter = .run cevm → ∃ ex, ∃ R : Exec cevm.pc cevm.sta cevm.dyna ex, ExecNeutral R

/-- **A frame runs to the same result under any two covered forks** when its entry avoids
`MODEXP`/`P256VERIFY` and its derivation is fork-neutral. -/
theorem runFrame_withFork {f : Frame} {g : Fork}
    (hoi : f.outer.benv.stat.fork = f.inner.benv.stat.fork)
    (hi : CoveredFork f.inner.benv.stat.fork) (hg : CoveredFork g) (hp : f.PrecompNeutral)
    (hN : RunNeutral f) : runFrame (f.withFork g) = runFrame f := by
  have ho : CoveredFork f.outer.benv.stat.fork := hoi ▸ hi
  unfold runFrame
  rw [frame_enter_withFork ho hi hg hp]
  rcases he : f.enter with r | cevm
  · rfl
  · obtain ⟨ex, R, hn⟩ := hN cevm he
    have hself : f.withFork f.inner.benv.stat.fork = f := by
      have h1 : f.withFork f.inner.benv.stat.fork =
          ⟨f.outer.withFork f.inner.benv.stat.fork, f.inner, f.isCreate⟩ := rfl
      rw [h1, ← hoi]
      rfl
    have hc := enter_fork hi hself hp he
    show (f.withFork g).settle (exec (cevm.withFork g)) = f.settle (exec cevm)
    rw [exec_withFork (hc ▸ hi) hg R hn, settle_withFork ho hi hg]

/-- **Message calls are fork-uniform** between covered forks (see `runFrame_withFork`). -/
theorem processMessage_withFork {msg : Msg} {g : Fork} (hf : CoveredFork msg.benv.stat.fork)
    (hg : CoveredFork g) (hp : (Frame.ofCall msg).PrecompNeutral)
    (hN : RunNeutral (Frame.ofCall msg)) :
    processMessage (msg.withFork g) = processMessage msg :=
  runFrame_withFork (f := Frame.ofCall msg) rfl hf hg hp hN

theorem ofCreate_withFork (msg : Msg) (g : Fork) :
    Frame.ofCreate (msg.withFork g) = (Frame.ofCreate msg).withFork g := rfl

/-- **Creation messages are fork-uniform** between covered forks. -/
theorem processCreateMessage_withFork {msg : Msg} {g : Fork}
    (hf : CoveredFork msg.benv.stat.fork) (hg : CoveredFork g)
    (hp : (Frame.ofCreate msg).PrecompNeutral) (hN : RunNeutral (Frame.ofCreate msg)) :
    processCreateMessage (msg.withFork g) = processCreateMessage msg := by
  unfold processCreateMessage
  rw [ofCreate_withFork]
  exact runFrame_withFork rfl hf hg hp hN

end Blanc.ForkUniform
