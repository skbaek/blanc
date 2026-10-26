import Blanc.Lift.Usdc.HistoryAnchorBodyGeneratedC00
import Blanc.Lift.Usdc.HistoryAnchorBodyGeneratedC01
import Blanc.Lift.Usdc.HistoryAnchorBodyGeneratedC02
import Blanc.Lift.Usdc.HistoryAnchorBodyGeneratedC03
import Blanc.Lift.Usdc.HistoryAnchorBodyGeneratedC04
import Blanc.Lift.Usdc.HistoryAnchorBodyGeneratedC05
import Blanc.Lift.Usdc.HistoryAnchorBodyGeneratedC06
import Blanc.Lift.Usdc.HistoryAnchorBodyGeneratedC07
import Blanc.Lift.Usdc.HistoryAnchorBodyGeneratedC08
import Blanc.Lift.Usdc.HistoryAnchorBodyGeneratedC09
import Blanc.Lift.Usdc.HistoryAnchorBodyGeneratedD00
import Blanc.Lift.Usdc.HistoryAnchorBodyGeneratedD01
import Blanc.Lift.Usdc.HistoryAnchorBodyGeneratedD02
import Blanc.Lift.Usdc.HistoryAnchorBodyGeneratedD03
import Blanc.Lift.Usdc.HistoryAnchorBodyGeneratedD04
import Blanc.Lift.Usdc.HistoryAnchorBodyGeneratedD05
import Blanc.Lift.Usdc.HistoryAnchorBodyGeneratedD06

/-! Generated only by scripts/history-anchor-body-generate.py.
Exact frozen packet bytes; historical observation adoption remains unresolved. -/

namespace Blanc.Lift.Usdc.HistoryAnchorBody

open Jaune

def cSigned : List Bytes := [c00Signed, c01Signed, c02Signed, c03Signed, c04Signed, c05Signed, c06Signed, c07Signed, c08Signed, c09Signed, c10Signed, c11Signed, c12Signed, c13Signed, c14Signed, c15Signed, c16Signed, c17Signed, c18Signed, c19Signed, c20Signed, c21Signed, c22Signed, c23Signed, c24Signed, c25Signed, c26Signed, c27Signed, c28Signed, c29Signed, c30Signed, c31Signed, c32Signed, c33Signed, c34Signed, c35Signed, c36Signed, c37Signed, c38Signed, c39Signed, c40Signed, c41Signed, c42Signed, c43Signed, c44Signed, c45Signed, c46Signed, c47Signed, c48Signed, c49Signed, c50Signed, c51Signed, c52Signed, c53Signed, c54Signed, c55Signed, c56Signed, c57Signed, c58Signed, c59Signed, c60Signed, c61Signed, c62Signed, c63Signed, c64Signed, c65Signed, c66Signed, c67Signed, c68Signed, c69Signed, c70Signed, c71Signed, c72Signed, c73Signed]

def cTxs : List Tx := [c00Tx, c01Tx, c02Tx, c03Tx, c04Tx, c05Tx, c06Tx, c07Tx, c08Tx, c09Tx, c10Tx, c11Tx, c12Tx, c13Tx, c14Tx, c15Tx, c16Tx, c17Tx, c18Tx, c19Tx, c20Tx, c21Tx, c22Tx, c23Tx, c24Tx, c25Tx, c26Tx, c27Tx, c28Tx, c29Tx, c30Tx, c31Tx, c32Tx, c33Tx, c34Tx, c35Tx, c36Tx, c37Tx, c38Tx, c39Tx, c40Tx, c41Tx, c42Tx, c43Tx, c44Tx, c45Tx, c46Tx, c47Tx, c48Tx, c49Tx, c50Tx, c51Tx, c52Tx, c53Tx, c54Tx, c55Tx, c56Tx, c57Tx, c58Tx, c59Tx, c60Tx, c61Tx, c62Tx, c63Tx, c64Tx, c65Tx, c66Tx, c67Tx, c68Tx, c69Tx, c70Tx, c71Tx, c72Tx, c73Tx]

def cBody : List (Bytes ⊕ Tx) := cTxs.map Sum.inr

theorem c_count : cSigned.length = 74 ∧ cTxs.length = 74 := by
  exact ⟨rfl, rfl⟩

/-- Strict decoding and canonical encoding for both complete ordered arrays. -/
theorem c_strict :
    cSigned.map (fun bs => bs.toBLT?.bind (fun blt => blt.toExTx.toOption)) = cTxs.map some ∧
    cTxs.map (fun tx => tx.toBLT.toBytes) = cSigned := by
  simp only [cSigned, cTxs, List.map_cons, List.map_nil,
    c00_decode, c00_canonical, c01_decode, c01_canonical, c02_decode, c02_canonical,
    c03_decode, c03_canonical, c04_decode, c04_canonical, c05_decode, c05_canonical,
    c06_decode, c06_canonical, c07_decode, c07_canonical, c08_decode, c08_canonical,
    c09_decode, c09_canonical, c10_decode, c10_canonical, c11_decode, c11_canonical,
    c12_decode, c12_canonical, c13_decode, c13_canonical, c14_decode, c14_canonical,
    c15_decode, c15_canonical, c16_decode, c16_canonical, c17_decode, c17_canonical,
    c18_decode, c18_canonical, c19_decode, c19_canonical, c20_decode, c20_canonical,
    c21_decode, c21_canonical, c22_decode, c22_canonical, c23_decode, c23_canonical,
    c24_decode, c24_canonical, c25_decode, c25_canonical, c26_decode, c26_canonical,
    c27_decode, c27_canonical, c28_decode, c28_canonical, c29_decode, c29_canonical,
    c30_decode, c30_canonical, c31_decode, c31_canonical, c32_decode, c32_canonical,
    c33_decode, c33_canonical, c34_decode, c34_canonical, c35_decode, c35_canonical,
    c36_decode, c36_canonical, c37_decode, c37_canonical, c38_decode, c38_canonical,
    c39_decode, c39_canonical, c40_decode, c40_canonical, c41_decode, c41_canonical,
    c42_decode, c42_canonical, c43_decode, c43_canonical, c44_decode, c44_canonical,
    c45_decode, c45_canonical, c46_decode, c46_canonical, c47_decode, c47_canonical,
    c48_decode, c48_canonical, c49_decode, c49_canonical, c50_decode, c50_canonical,
    c51_decode, c51_canonical, c52_decode, c52_canonical, c53_decode, c53_canonical,
    c54_decode, c54_canonical, c55_decode, c55_canonical, c56_decode, c56_canonical,
    c57_decode, c57_canonical, c58_decode, c58_canonical, c59_decode, c59_canonical,
    c60_decode, c60_canonical, c61_decode, c61_canonical, c62_decode, c62_canonical,
    c63_decode, c63_canonical, c64_decode, c64_canonical, c65_decode, c65_canonical,
    c66_decode, c66_canonical, c67_decode, c67_canonical, c68_decode, c68_canonical,
    c69_decode, c69_canonical, c70_decode, c70_canonical, c71_decode, c71_canonical,
    c72_decode, c72_canonical, c73_decode, c73_canonical, and_self]

theorem c_selected : cTxs[22]? = some c22Tx := by
  rfl

def dSigned : List Bytes := [d00Signed, d01Signed, d02Signed, d03Signed, d04Signed, d05Signed, d06Signed, d07Signed, d08Signed, d09Signed, d10Signed, d11Signed, d12Signed, d13Signed, d14Signed, d15Signed, d16Signed, d17Signed, d18Signed, d19Signed, d20Signed, d21Signed, d22Signed, d23Signed, d24Signed, d25Signed, d26Signed, d27Signed, d28Signed, d29Signed, d30Signed, d31Signed, d32Signed, d33Signed, d34Signed, d35Signed, d36Signed, d37Signed, d38Signed, d39Signed, d40Signed, d41Signed, d42Signed, d43Signed, d44Signed, d45Signed, d46Signed, d47Signed, d48Signed, d49Signed, d50Signed, d51Signed, d52Signed]

def dTxs : List Tx := [d00Tx, d01Tx, d02Tx, d03Tx, d04Tx, d05Tx, d06Tx, d07Tx, d08Tx, d09Tx, d10Tx, d11Tx, d12Tx, d13Tx, d14Tx, d15Tx, d16Tx, d17Tx, d18Tx, d19Tx, d20Tx, d21Tx, d22Tx, d23Tx, d24Tx, d25Tx, d26Tx, d27Tx, d28Tx, d29Tx, d30Tx, d31Tx, d32Tx, d33Tx, d34Tx, d35Tx, d36Tx, d37Tx, d38Tx, d39Tx, d40Tx, d41Tx, d42Tx, d43Tx, d44Tx, d45Tx, d46Tx, d47Tx, d48Tx, d49Tx, d50Tx, d51Tx, d52Tx]

def dBody : List (Bytes ⊕ Tx) := dTxs.map Sum.inr

theorem d_count : dSigned.length = 53 ∧ dTxs.length = 53 := by
  exact ⟨rfl, rfl⟩

/-- Strict decoding and canonical encoding for both complete ordered arrays. -/
theorem d_strict :
    dSigned.map (fun bs => bs.toBLT?.bind (fun blt => blt.toExTx.toOption)) = dTxs.map some ∧
    dTxs.map (fun tx => tx.toBLT.toBytes) = dSigned := by
  simp only [dSigned, dTxs, List.map_cons, List.map_nil,
    d00_decode, d00_canonical, d01_decode, d01_canonical, d02_decode, d02_canonical,
    d03_decode, d03_canonical, d04_decode, d04_canonical, d05_decode, d05_canonical,
    d06_decode, d06_canonical, d07_decode, d07_canonical, d08_decode, d08_canonical,
    d09_decode, d09_canonical, d10_decode, d10_canonical, d11_decode, d11_canonical,
    d12_decode, d12_canonical, d13_decode, d13_canonical, d14_decode, d14_canonical,
    d15_decode, d15_canonical, d16_decode, d16_canonical, d17_decode, d17_canonical,
    d18_decode, d18_canonical, d19_decode, d19_canonical, d20_decode, d20_canonical,
    d21_decode, d21_canonical, d22_decode, d22_canonical, d23_decode, d23_canonical,
    d24_decode, d24_canonical, d25_decode, d25_canonical, d26_decode, d26_canonical,
    d27_decode, d27_canonical, d28_decode, d28_canonical, d29_decode, d29_canonical,
    d30_decode, d30_canonical, d31_decode, d31_canonical, d32_decode, d32_canonical,
    d33_decode, d33_canonical, d34_decode, d34_canonical, d35_decode, d35_canonical,
    d36_decode, d36_canonical, d37_decode, d37_canonical, d38_decode, d38_canonical,
    d39_decode, d39_canonical, d40_decode, d40_canonical, d41_decode, d41_canonical,
    d42_decode, d42_canonical, d43_decode, d43_canonical, d44_decode, d44_canonical,
    d45_decode, d45_canonical, d46_decode, d46_canonical, d47_decode, d47_canonical,
    d48_decode, d48_canonical, d49_decode, d49_canonical, d50_decode, d50_canonical,
    d51_decode, d51_canonical, d52_decode, d52_canonical, and_self]

theorem d_selected : dTxs[38]? = some d38Tx := by
  rfl

end Blanc.Lift.Usdc.HistoryAnchorBody
