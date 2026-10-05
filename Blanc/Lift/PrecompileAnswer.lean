import Blanc.Lift.TargetLogEvents

/-!
# Precompile answers

A precompile's successful output is a function of its calldata and the fork's `MODEXP` pricing
alone: the remaining gas only gates success (`precompileRun_gas_mono`). So every successful
precompile answer to a fixed request is one entry of the finite list
`precompileRunAddresses.filterMap (precompileAnswer data rules)`, and a successful call
message's output is either such an answer or the result of its entered code frame
(`ProcessMessage.ok_output`). Contract-neutral.
-/

namespace Blanc.Lift

open Jaune

/-- The addresses at which `precompileRun` can succeed. -/
def precompileRunAddresses : List Adr := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16,
  17, 256]

private theorem chargeGas_mono {cost : Nat} {e e' : Evm} {pr pr' : Unit → PrecompResult}
    (gas : e.dyna.gasLeft ≤ e'.dyna.gasLeft) (same : pr () = pr' ()) {c : Nat} {o : Bytes}
    (h : PrecompResult.chargeGas cost e pr = .ok c o) :
    PrecompResult.chargeGas cost e' pr' = .ok c o := by
  unfold PrecompResult.chargeGas at h ⊢
  split at h
  · rw [ite_eq_left (Nat.le_trans (by assumption) gas), ← same]
    exact h
  · cases h

/-- More gas never changes a successful precompile result; only the calldata and the `MODEXP`
pricing are read. -/
theorem precompileRun_gas_mono {e e' : Evm} (data : e'.sta.data = e.sta.data)
    (rules : e'.sta.benvStat.rules.modexp = e.sta.benvStat.rules.modexp)
    (gas : e.dyna.gasLeft ≤ e'.dyna.gasLeft) {adr : Adr} {c : Nat} {o : Bytes}
    (h : precompileRun e adr = .ok c o) : precompileRun e' adr = .ok c o := by
  unfold precompileRun at h ⊢
  split at h
  · unfold executeEcrecover at h ⊢
    rw [data]
    exact chargeGas_mono gas rfl h
  · unfold executeSha256 at h ⊢
    rw [data]
    exact chargeGas_mono gas rfl h
  · unfold executeRipemd160 at h ⊢
    rw [data]
    exact chargeGas_mono gas rfl h
  · unfold executeId at h ⊢
    rw [data]
    exact chargeGas_mono gas rfl h
  · unfold executeModexp at h ⊢
    rw [data, rules]
    dsimp only at h ⊢
    split at h
    · cases h
    · simp only [‹¬_›, ite_false]
      exact chargeGas_mono gas rfl h
  · unfold executeEcadd at h ⊢
    rw [data]
    exact chargeGas_mono gas rfl h
  · unfold executeEcmul at h ⊢
    rw [data]
    exact chargeGas_mono gas rfl h
  · unfold executePairingCheck at h ⊢
    rw [data]
    exact chargeGas_mono gas rfl h
  · unfold executeBlake2F at h ⊢
    rw [data]
    dsimp only at h ⊢
    split at h
    · cases h
    · simp only [‹¬_›, ite_false]
      exact chargeGas_mono gas rfl h
  · unfold executePointEval at h ⊢
    rw [data]
    dsimp only at h ⊢
    split at h
    · cases h
    · simp only [‹¬_›, ite_false]
      exact chargeGas_mono gas rfl h
  · unfold executeBls12G1Add at h ⊢
    rw [data]
    dsimp only at h ⊢
    split at h
    · cases h
    · simp only [‹¬_›, ite_false]
      exact chargeGas_mono gas rfl h
  · unfold executeBls12G1Msm at h ⊢
    rw [data]
    dsimp only at h ⊢
    split at h
    · cases h
    · simp only [‹¬_›, ite_false]
      exact chargeGas_mono gas rfl h
  · unfold executeBls12G2Add at h ⊢
    rw [data]
    dsimp only at h ⊢
    split at h
    · cases h
    · simp only [‹¬_›, ite_false]
      exact chargeGas_mono gas rfl h
  · unfold executeBls12G2Msm at h ⊢
    rw [data]
    dsimp only at h ⊢
    split at h
    · cases h
    · simp only [‹¬_›, ite_false]
      exact chargeGas_mono gas rfl h
  · unfold executeBls12Pairing at h ⊢
    rw [data]
    dsimp only at h ⊢
    split at h
    · cases h
    · simp only [‹¬_›, ite_false]
      exact chargeGas_mono gas rfl h
  · unfold executeBls12MapFpToG1 at h ⊢
    rw [data]
    dsimp only at h ⊢
    split at h
    · cases h
    · simp only [‹¬_›, ite_false]
      exact chargeGas_mono gas rfl h
  · unfold executeBls12MapFp2ToG2 at h ⊢
    rw [data]
    dsimp only at h ⊢
    split at h
    · cases h
    · simp only [‹¬_›, ite_false]
      exact chargeGas_mono gas rfl h
  · unfold executeP256Verify at h ⊢
    rw [data]
    exact chargeGas_mono gas rfl h
  · cases h

/-- `precompileRun` succeeds only at the listed addresses. -/
theorem precompileRun_ok_mem {e : Evm} {adr : Adr} {c : Nat} {o : Bytes}
    (h : precompileRun e adr = .ok c o) : adr ∈ precompileRunAddresses := by
  unfold precompileRun at h
  split at h <;> first
    | cases h
    | (unfold precompileRunAddresses
       repeat (first | exact List.Mem.head _ | apply List.Mem.tail))

/-- Two successful precompile runs on the same calldata and `MODEXP` pricing return the same
output, whatever their gas. -/
theorem precompileRun_ok_output_unique {e e' : Evm} (data : e'.sta.data = e.sta.data)
    (rules : e'.sta.benvStat.rules.modexp = e.sta.benvStat.rules.modexp) {adr : Adr}
    {c c' : Nat} {o o' : Bytes} (h : precompileRun e adr = .ok c o)
    (h' : precompileRun e' adr = .ok c' o') : o = o' := by
  let big : Evm := { e with dyna := e.dyna.withGasLeft (max e.dyna.gasLeft e'.dyna.gasLeft) }
  have up : precompileRun big adr = .ok c o :=
    precompileRun_gas_mono (e := e) (e' := big) rfl rfl (Nat.le_max_left _ _) h
  have up' : precompileRun big adr = .ok c' o' :=
    precompileRun_gas_mono (e := e') (e' := big) data.symm rules.symm (Nat.le_max_right _ _) h'
  rw [up] at up'
  injection up'

/-- The successful answer of the precompile at `adr` to calldata `data` under `MODEXP` pricing
`rules`, if it has one (unique by `precompileRun_ok_output_unique`). -/
noncomputable def precompileAnswer (data : Bytes) (rules : ModexpRules) (adr : Adr) :
    Option Bytes :=
  open Classical in
  if h : ∃ o : Bytes, ∃ (e : Evm) (c : Nat), e.sta.data = data ∧
      e.sta.benvStat.rules.modexp = rules ∧ precompileRun e adr = .ok c o
  then some (Classical.choose h) else none

theorem precompileAnswer_of_ok {e : Evm} {adr : Adr} {c : Nat} {o : Bytes}
    (h : precompileRun e adr = .ok c o) :
    precompileAnswer e.sta.data e.sta.benvStat.rules.modexp adr = some o := by
  have ex : ∃ o : Bytes, ∃ (e' : Evm) (c' : Nat), e'.sta.data = e.sta.data ∧
      e'.sta.benvStat.rules.modexp = e.sta.benvStat.rules.modexp ∧
      precompileRun e' adr = .ok c' o := ⟨o, e, c, rfl, rfl, h⟩
  unfold precompileAnswer
  rw [dite_eq_left_of_eq_true (eq_true ex)]
  obtain ⟨_, _, data, rules, chosen⟩ := Classical.choose_spec ex
  rw [precompileRun_ok_output_unique data rules h chosen]

/-- A settled call frame whose result carries no error is its raw execution's success. -/
theorem callFrame_settle_ok {msg : Msg} {raw : Execution} {child : Devm}
    (settled : (Frame.ofCall msg).settle raw = .ok child) (clean : child.error.isSome = false) :
    raw = .ok child := by
  unfold Frame.settle Frame.settleMsg processMessage.settle at settled
  dsimp only [Frame.ofCall] at settled
  simp only [Bool.false_eq_true, ite_false] at settled
  cases handled : executeCode.handleErrorWith msg.benv.stat.rules.stateGas raw with
  | error e =>
    rw [handled] at settled
    cases settled
  | ok evm =>
    rw [handled] at settled
    simp only [bind, Except.bind] at settled
    split at settled
    · injection settled with same
      subst same
      rename_i dirty
      have kept : evm.error.isSome = false := clean
      rw [kept] at dirty
      cases dirty
    · injection settled with same
      subst same
      unfold executeCode.handleErrorWith at handled
      split at handled <;>
      · first
          | unfold executeCode.handleError at handled
          | unfold executeCode.handleErrorAmsterdam at handled
        split at handled
        · injection handled with same
          rw [same]
        all_goals
          cases handled
          try exact Bool.noConfusion clean

/-- A successful, error-free call message's output is either the answer of the precompile its
code address names to its calldata (no frame entered), or the success of its entered code
frame's raw execution. -/
theorem ProcessMessage.ok_output {msg : Msg} {xl : Xlot} {child : Devm}
    (process : ProcessMessage msg xl (.ok child)) (clean : child.error.isSome = false) :
    (xl = .none ∧ ∃ adr ∈ precompileRunAddresses,
      precompileAnswer msg.data msg.benv.stat.rules.modexp adr = some child.output) ∨
    ∃ evm raw, xl = .some (evm, raw) ∧ raw = .ok child := by
  unfold ProcessMessage RunFrame at process
  cases entered : (Frame.ofCall msg).enter with
  | run evm =>
    rw [entered] at process
    obtain ⟨raw, slot, settled⟩ := process
    exact Or.inr ⟨evm, raw, slot, callFrame_settle_ok settled.symm clean⟩
  | done result =>
    rw [entered] at process
    obtain ⟨slot, resultEq⟩ := process
    refine Or.inl ⟨slot, ?_⟩
    unfold Frame.enter at entered
    split at entered
    · cases entered
      unfold Frame.settleMsg processMessage.settle at resultEq
      dsimp only [Frame.ofCall] at resultEq
      simp only [Bool.false_eq_true, ite_false] at resultEq
      cases resultEq
    · rename_i benv transfer
      split at entered
      · cases entered
      · rename_i raw entry
        cases entered
        have settled := callFrame_settle_ok resultEq.symm clean
        subst settled
        have stat := benvAfterTransfer_stat transfer
        unfold executeCode.enter at entry
        split at entry
        · cases entry
        · rename_i adr _
          split at entry
          · injection entry with rawEq
            unfold executePrecomp applyPrecompResult at rawEq
            split at rawEq
            · cases rawEq
            · rename_i c o run
              injection rawEq with childEq
              refine ⟨adr, precompileRun_ok_mem run, ?_⟩
              have answer := precompileAnswer_of_ok run
              rw [← childEq]
              change precompileAnswer msg.data benv.stat.rules.modexp adr = some o at answer
              rw [stat] at answer
              exact answer
          · cases entry

end Blanc.Lift
