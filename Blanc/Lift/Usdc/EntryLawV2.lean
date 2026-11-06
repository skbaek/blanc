import Blanc.Lift.Usdc.EntryLawWord
import Blanc.Lift.Usdc.EntryLawV2_1Walks
import Blanc.Lift.CurveCoins.UsdcV2

/-!
# FiatTokenV2 and V2_1 as word-reading versions

`v2`, `v2_1`: the instances of `WordVersion`. The site lists and tables are decided by the kernel, so a wrong table fails the
build.
-/

namespace Blanc.Lift.Usdc

open Jaune Blanc Blanc.Lift Blanc.Lift.WriteSite

section V2
open ImplV2

theorem v2_sites_callers : ∀ c ∈ selV2.callers, ¬ CurveCoins.PoolCoinSel c := by
  intro c hc p
  simp only [selV2, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> rcases p with p | p | p <;> exact absurd p (by decide)

/-- **FiatTokenV2.** -/
def v2 : WordVersion where
  code := code
  cert := cert
  ann := ImplV2Ws.implWsAnn
  f0 := t_0000_c0
  checked := cert_check
  ws := implV2_wsCert
  root := rfl
  notV22 := by decide +kernel
  notDelegation := by decide +kernel
  noCall := fun run hcode hsg sel => v2_noCall run hcode hsg sel
  table := selV2
  tableSel := rfl
  rowsOk := implV2_allowSitesOk
  callers := v2_sites_callers
  owners := by decide +kernel
  inits := by decide +kernel
  auths := [0xe3ee160e]
  authSigned := by decide +kernel
  burnRows := by decide +kernel
  balRows := by decide +kernel
  t_caller := by decide +kernel
  t_cd4 := by decide +kernel
  f_cd4 := by decide +kernel
  f_cd36 := by decide +kernel
  f_row := by decide +kernel
  m_supply := by decide +kernel
  m_minter := by decide +kernel
  a_flag := by decide +kernel
  a_cd4 := by decide +kernel
  a_cd36 := by decide +kernel
  frameTransfer := fun fork wf sel run =>
    let ⟨_, _, _, d4, d5, st⟩ := ImplV2.frame_transfer fork wf sel run
    ⟨d4, d5, st⟩
  frameFrom := fun fork wf sel run =>
    let ⟨_, _, _, _, a1, d6, d7, st⟩ := ImplV2.frame_transferFrom fork wf sel run
    ⟨a1, d6, d7, _, st⟩
  frameMint := fun fork wf sel run => ImplV2.frame_mint fork wf sel run
  frameAuth := fun fork wf sel run =>
    ImplV2.frame_twa fork wf (List.mem_singleton.mp sel) run

end V2

section V2_1
open ImplV2_1

theorem v2_1_sites_callers : ∀ c ∈ selV2_1.callers, ¬ CurveCoins.PoolCoinSel c := by
  intro c hc p
  simp only [selV2_1, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> rcases p with p | p | p <;> exact absurd p (by decide)

/-- **FiatTokenV2_1.** -/
def v2_1 : WordVersion where
  code := code
  cert := cert
  ann := ImplV2_1Ws.implWsAnn
  f0 := t_0000_c0
  checked := cert_check
  ws := implV2_1_wsCert
  root := rfl
  notV22 := by decide +kernel
  notDelegation := by decide +kernel
  noCall := fun run hcode hsg sel => v2_1_noCall run hcode hsg sel
  table := selV2_1
  tableSel := rfl
  rowsOk := implV2_1_allowSitesOk
  callers := v2_1_sites_callers
  owners := by decide +kernel
  inits := by decide +kernel
  auths := [0xe3ee160e, 0xef55bec6]
  authSigned := by decide +kernel
  burnRows := by decide +kernel
  balRows := by decide +kernel
  t_caller := by decide +kernel
  t_cd4 := by decide +kernel
  f_cd4 := by decide +kernel
  f_cd36 := by decide +kernel
  f_row := by decide +kernel
  m_supply := by decide +kernel
  m_minter := by decide +kernel
  a_flag := by decide +kernel
  a_cd4 := by decide +kernel
  a_cd36 := by decide +kernel
  frameTransfer := fun fork wf sel run =>
    let ⟨_, _, _, d4, d5, st⟩ := ImplV2_1.frame_transfer fork wf sel run
    ⟨d4, d5, st⟩
  frameFrom := fun fork wf sel run =>
    let ⟨_, _, _, _, a1, d6, d7, st⟩ := ImplV2_1.frame_transferFrom fork wf sel run
    ⟨a1, d6, d7, _, st⟩
  frameMint := fun fork wf sel run => ImplV2_1.frame_mint fork wf sel run
  frameAuth := fun fork wf sel run => by
    rcases List.mem_cons.mp sel with s | s
    · exact ImplV2_1.frame_twa fork wf s run
    · exact ImplV2_1.frame_rwa fork wf (List.mem_singleton.mp s) run

end V2_1

end Blanc.Lift.Usdc
