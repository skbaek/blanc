import Blanc.NewCommon

lemma Ninst.pc_eq_of_run' {evm n xl evm'}
    (run : Ninst.Run' evm n xl (.ok evm')) :
    evm'.pc = evm.pc + n.toB8L.length := by
  cases n
  case reg => exact Rinst.pc_eq_of_run run
  case push xs le =>
    simp [Ninst.Run'] at run
    rename' run => temp
    rcases of_bind_eq_ok temp with ⟨evm1, temp_eq, run⟩; clear temp
    rw [chargeGas_inv_pc temp_eq]; clear temp_eq
    rename' run => temp
    rcases of_bind_eq_ok temp with ⟨evm2, temp_eq, run⟩; clear temp
    rw [Evm.push_inv_pc temp_eq]; clear temp_eq
    injection run with rw; rw [← rw]
    simp only [toB8L, pushToB8L, List.length_cons]; omega
  case exec x =>
    cases x
    case create =>
      simp only [Ninst.Run', exists_eq_left] at run
      inv_step_split run Evm.pop_inv_pc ⟨foo, evm1⟩
      inv_step_split run Evm.pop_mapFst_inv_pc ⟨memIndex, evm2⟩
      inv_step_split run Evm.pop_mapFst_inv_pc ⟨memSize, evm3⟩
      inv_step_split run chargeGas_inv_pc evm4
      rcases run with ⟨exn, gc, run⟩
      rename' run => temp
      rcases of_split_eq_ok temp with ⟨evm5, rw, run⟩; clear temp
      rw [rw] at gc; clear rw
      have rw : evm4.pc = evm5.pc := by
        rw [← genericCreate_inv_pc gc]; rfl
      rw [rw, ← pc_eq_of_incrPc run]; rfl
    case call =>
      simp only [Ninst.Run'] at run
      inv_step_split run Evm.pop_inv_pc ⟨_, evm1⟩
      inv_step_split run Evm.pop_mapFst_inv_pc ⟨adr, evm2⟩
      inv_step_split run Evm.pop_inv_pc ⟨_, evm3⟩
      inv_step_split run Evm.pop_mapFst_inv_pc ⟨_, evm4⟩
      inv_step_split run Evm.pop_mapFst_inv_pc ⟨_, evm5⟩
      inv_step_split run Evm.pop_mapFst_inv_pc ⟨_, evm6⟩
      inv_step_split run Evm.pop_mapFst_inv_pc ⟨_, evm7⟩
      rcases run with ⟨extendCost, temp, run⟩; clear temp
      rcases run with ⟨preAccessCost, temp, run⟩; clear temp
      rcases run with ⟨evm8, temp, run⟩
      have rw1 : evm7.pc = evm8.pc := by
        rw [temp, addAccessedAddress_inv_pc]
      rw [rw1]; clear rw1 temp
      rcases run with ⟨_, _, _, _, evm9, temp, run⟩
      have rw2 : evm8.pc = evm9.pc := by
        rw [← @accessDelegation_inv_pc evm8 adr, ← temp]
      rw [rw2]; clear rw2 temp
      rcases run with ⟨accessCost, temp, run⟩; clear temp
      rcases run with ⟨createCost, temp, run⟩; clear temp
      rcases run with ⟨transferCost, temp, run⟩; clear temp
      rcases run with ⟨msgCallCost, msgCallStipend, temp, run⟩; clear temp
      inv_step_split run chargeGas_inv_pc evm10
      rename' run => temp
      rcases of_split_eq_ok temp with ⟨_, temp', run⟩;
      clear temp temp'
      rcases run with ⟨evm11, temp_eq, run⟩
      have rw : evm10.pc = evm11.pc := by
        rw [temp_eq]; apply Evm.memExtends_inv_pc
      rw [rw]; clear rw temp_eq
      rcases run with ⟨senderBal, temp, run⟩; clear temp
      split at run
      · inv_step_split run Evm.push_inv_pc evm12
        rw [← incrPc_incr_pc run]; clear run; rfl
      · rcases run with ⟨exn, gc, run⟩
        rcases of_split_eq_ok run with ⟨evm12, rw, eq⟩
        rw [rw] at gc
        rw [genericCall_inv_pc gc, ← incrPc_incr_pc eq]; rfl
    case callcode => sorry
    case delcall => sorry
    case create2 => sorry
    case statcall => sorry
