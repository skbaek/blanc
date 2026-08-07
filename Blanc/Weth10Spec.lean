-- WETH10's abstract ladder adapter. The runtime builder remains a parameter.

import Blanc.Weth10Backed

namespace Blanc

open Jaune

namespace Weth10

/-- The existing generic ladder instantiated with WETH10's backing invariant.
The later runtime supplies `mkProg`; this module defines no callable program. -/
def backedSpec
    (mkProg : Weth10.DeployParams → Prog) (dp : Weth10.DeployParams) :
    ContractSpec where
  prog := mkProg dp
  Inv := Stor.Weth10Inv
  Side := SumNof
  inv_forget := by
    intro s v b h
    unfold Stor.Weth10Inv at h ⊢
    rw [B256.toNat_zero]
    omega
  inv_mono := by
    intro s v b b' h hle
    unfold Stor.Weth10Inv at h ⊢
    omega
  inv_recv := by
    intro s v b b' h heq
    unfold Stor.Weth10Inv at h ⊢
    rw [B256.toNat_zero] at h
    omega
  side_le := by
    intro f g h hle
    unfold SumNof at h ⊢
    omega
  side_transfer := by
    intro st st' caller callee wad h_sub h_side
    have h_nof : sum st.bal < 2 ^ 256 := h_side
    rcases of_state_transfer (callee := callee) h_sub h_nof with
      ⟨-, -, h_sum, -, -, -⟩
    show sum _ < 2 ^ 256
    rw [h_sum]
    exact h_nof
  side_addBal := by
    intro w a val h_bound _
    show sum _ < 2 ^ 256
    rw [sum_addBal_eq w a val h_bound]
    omega
  inv_transfer := by
    intro st st' caller callee ca wad v h_sub h_ne h_side h_inv
    have h_nof : sum st.bal < 2 ^ 256 := h_side
    rcases of_state_transfer (callee := callee) h_sub h_nof with
      ⟨h_t_stor, -, -, h_t_le, -, -⟩
    have h_mid : st'.bal ca = st.bal ca := by
      rcases State.of_subBal h_sub with ⟨-, h_st'⟩
      rw [h_st']
      show ((st.setBal caller _).get ca).bal = (st.get ca).bal
      rw [State.setBal_get_ne h_ne]
    have h_stor : (st'.addBal callee wad).getStor ca = st.getStor ca := h_t_stor ca
    have h_ge : (st.bal ca).toNat ≤ ((st'.addBal callee wad).bal ca).toNat := by
      by_cases h_eq : callee = ca
      · have h_add : (st'.addBal callee wad).bal ca = st.bal ca + wad := by
          rw [h_eq]
          show ((st'.setBal ca (st'.bal ca + wad)).get ca).bal = _
          rw [State.setBal_get_self]
          show st'.bal ca + wad = _
          rw [h_mid]
        rw [h_add]
        have h_le_wad : wad.toNat ≤ (st.bal caller).toNat :=
          B256.toNat_le_toNat h_t_le
        have h_two : (st.bal ca).toNat + (st.bal caller).toNat ≤ sum st.bal :=
          add_le_sum_of_ne st.bal (fun hc => h_ne hc.symm)
        have h_nof' : B256.Nof (st.bal ca) wad := by
          unfold B256.Nof
          omega
        rw [B256.toNat_add_eq_of_nof _ _ h_nof']
        omega
      · have h_other : (st'.addBal callee wad).bal ca = st.bal ca := by
          show ((st'.setBal callee _).get ca).bal = _
          rw [State.setBal_get_ne h_eq]
          exact h_mid
        rw [h_other]
    rw [h_stor]
    unfold Stor.Weth10Inv at h_inv ⊢
    omega
  inv_recv_transfer := by
    intro st st' caller ca wad h_sub h_ne h_side h_inv
    have h_nof : sum st.bal < 2 ^ 256 := h_side
    rcases of_state_transfer (callee := ca) h_sub h_nof with
      ⟨h_t_stor, -, -, -, -, -⟩
    have h_stor : (st'.addBal ca wad).getStor ca = st.getStor ca := h_t_stor ca
    have h_bal : ((st'.addBal ca wad).bal ca).toNat =
        (st.bal ca).toNat + wad.toNat :=
      of_transfer_bal_target h_sub h_ne h_nof
    rw [h_stor]
    unfold Stor.Weth10Inv at h_inv ⊢
    rw [B256.toNat_zero] at h_inv
    omega
  inv_addBal := by
    intro w ca a val v h_bound _ h_inv
    have h_nof_a : B256.Nof (w.bal a) val := by
      unfold B256.Nof
      have := @le_sum w.bal a
      omega
    have h_stor : (w.addBal a val).getStor ca = w.getStor ca := by
      show ((w.setBal a _).get ca).stor = (w.get ca).stor
      rw [State.setBal_get_stor]
    have h_ge : (w.bal ca).toNat ≤ ((w.addBal a val).bal ca).toNat := by
      by_cases h_eq : a = ca
      · subst h_eq
        show (w.bal a).toNat ≤ ((w.setBal a (w.bal a + val)).get a).bal.toNat
        rw [State.setBal_get_self]
        change (w.bal a).toNat ≤ (w.bal a + val).toNat
        rw [B256.toNat_add_eq_of_nof _ _ h_nof_a]
        omega
      · show (w.bal ca).toNat ≤ ((w.setBal a _).get ca).bal.toNat
        rw [State.setBal_get_ne h_eq]
        exact Nat.le_refl _
    rw [h_stor]
    unfold Stor.Weth10Inv at h_inv ⊢
    omega

/-! Statement bridges make the adapter's exact parameterization and ladder
meanings explicit without starting any selector-level soundness proof. -/

theorem backedSpec_prog_eq
    (mkProg : Weth10.DeployParams → Prog) (dp : Weth10.DeployParams) :
    (backedSpec mkProg dp).prog = mkProg dp := rfl

theorem backedSpec_inv_eq
    (mkProg : Weth10.DeployParams → Prog) (dp : Weth10.DeployParams) :
    (backedSpec mkProg dp).Inv = Stor.Weth10Inv := rfl

theorem backedSpec_side_eq
    (mkProg : Weth10.DeployParams → Prog) (dp : Weth10.DeployParams) :
    (backedSpec mkProg dp).Side = SumNof := rfl

theorem backedSpec_preInv_iff
    (mkProg : Weth10.DeployParams → Prog) (dp : Weth10.DeployParams)
    {ca : Adr} {sevm : Sevm} {devm : Devm} :
    (backedSpec mkProg dp).PreInv devm ca sevm ↔
      (sevm.currentTarget = ca →
        Stor.Weth10Inv (Devm.getStor devm ca) sevm.value (devm.getBal ca)) ∧
      (sevm.currentTarget ≠ ca →
        Stor.Weth10Inv (Devm.getStor devm ca) 0 (devm.getBal ca)) := Iff.rfl

theorem backedSpec_postInv_iff
    (mkProg : Weth10.DeployParams → Prog) (dp : Weth10.DeployParams)
    {ca : Adr} {devm : Devm} :
    (backedSpec mkProg dp).PostInv devm ca ↔
      Stor.Weth10Inv (Devm.getStor devm ca) 0 (devm.getBal ca) := Iff.rfl

theorem backedSpec_empty
    (mkProg : Weth10.DeployParams → Prog) (dp : Weth10.DeployParams) :
    (backedSpec mkProg dp).Inv Stor.empty 0 0 :=
  Stor.Weth10Inv.of_empty

end Weth10

end Blanc
