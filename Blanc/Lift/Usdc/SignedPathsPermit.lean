import Blanc.Lift.Usdc.SignedPathsKit
import Blanc.Lift.HistAccessWalkFacts

/-!
# F7b: the permit and cancellation paths reach a library call site

`permit` (wrappers 132/149, bodies 24/41, adapter 88, entry 94 with its goto into entry 8) is
re-walked under a `SiteStep` relation to `t_47d3_c8`, right after `_hashTypedDataV4` in entry 8,
with the owner as the signer, where `site9_false` closes it; `cancelAuthorization` (wrappers
159/136, bodies 52/28, adapter 97, entry 89) to the `callNext 111` with the authorizer as the
signer, where `site111_call_false` closes it.
-/

namespace Blanc.Lift.Usdc

open Jaune Blanc Blanc.Lift Blanc.Lift.FreePtr

set_option hygiene false in
/-- The permit walk's nonstorage steps, including its literal shift, copy and timestamp. -/
macro "sxx_permit_nonstorage " h:ident : tactic => `(tactic| first
  | sx_nonstorage $h
  | sop $h => ri_shl
  | sop $h => ri_mul
  | sop $h => ri_calldatacopy
  | sop $h => ri_timestamp)

variable {P : Sevm → Devm → Ninst → Devm → Prop} {sevm : Sevm} {b : Devm}
  {S : List B256} {M : Mem} {G : Nat} {r : Seg}

/-- `_cancelAuthorization` (entry 89) reaches `_requireValidSignature` with its authorizer `z2` as
the signer. -/
theorem walk89 (hP : SiteStep P) (hfork : CoveredFork sevm.benvStat.fork) {pair : Adr}
    (rejects : LibRejects pair) (notPre : ¬ sevm.benvStat.rules.isPrecomp pair)
    (hlib : b.getCode usdcLib = Lib.code) (hpair : b.getCode pair = UniswapV2Pair.code)
    {z0 z1 z2 ret : B256} (hsg : z2.toAdr = pair)
    (run : SFunc.RunCutP P Impl.cert.prog sevm [] (St b (z0 :: z1 :: z2 :: ret :: S) M G)
      Impl.t_4a3f_c89 r) : False := by
  repeat sx run
  obtain ⟨b1, M1, G1, hs1, run⟩ := skipP_110 hP hfork run
  obtain ⟨b2, u0, M2, G2, hs2, run⟩ := ric_seg_e89 (fun h => (hP h).1) hfork run
  have hgc : ∀ a, b2.getCode a = b.getCode a := fun a => by
    rw [getCode_of_state hs2, getCode_of_state hs1]
  exact site111_call_false hP hfork rejects notPre (by rw [hgc]; exact hlib)
    (by rw [hgc]; exact hpair) hsg run

/-- `_permit`'s body (entry 8, from its deadline flag) reaches the library call site with its
owner `x4` as the signer. -/
theorem walk8H (hP : SiteStep P) (hstateGas : sevm.benvStat.rules.stateGas = none)
    (hbal : sevm.benvStat.rules.bal = none) {pair : Adr}
    (rejects : LibRejectsAt pair sevm) (notPre : ¬ sevm.benvStat.rules.isPrecomp pair)
    (hlib : b.getCode usdcLib = Lib.code) (hpair : b.getCode pair = UniswapV2Pair.code)
    {fl x0 x1 x2 x3 x4 ret : B256} (hsg : x4.toAdr = pair)
    (run : SFunc.RunCutP P Impl.cert.prog sevm []
      (St b (fl :: x0 :: x1 :: x2 :: x3 :: x4 :: ret :: S) M G) Impl.t_46c0_c8 r) : False := by
  repeat sx_nonstorage run
  brP run
  repeat sx_nonstorage run
  obtain ⟨b1, y1, M1, G1, hs1, run⟩ := skipP_78_noStateGas hP hstateGas run
  iterate 20 sx_nonstorage run
  sop run => (ri_sloadH hbal)
  iterate 5 sx_nonstorage run
  sop run => (ri_sstoreH hstateGas hbal)
  obtain ⟨b2, u0, M2, G2, hs2, run⟩ := ric_seg_e8digest_noStateGas (fun h => (hP h).1) hstateGas run
  obtain ⟨b3, z, M3, G3, hs3, run⟩ := skipP_79_noStateGas hP hstateGas run
  have hgc : ∀ a, b3.getCode a = b.getCode a := fun a => by
    rw [getCode_of_state hs3, getCode_of_state hs2, afterSstoreH_getCode, afterSloadH_getCode,
      getCode_of_state hs1]
  exact site9_falseH hP hstateGas hbal rejects notPre List.not_mem_nil List.not_mem_nil
    (by rw [hgc]; exact hlib) (by rw [hgc]; exact hpair) hsg run

/-- The original covered-fork entry8 interface. -/
theorem walk8 (hP : SiteStep P) (hfork : CoveredFork sevm.benvStat.fork) {pair : Adr}
    (rejects : LibRejects pair) (notPre : ¬ sevm.benvStat.rules.isPrecomp pair)
    (hlib : b.getCode usdcLib = Lib.code) (hpair : b.getCode pair = UniswapV2Pair.code)
    {fl x0 x1 x2 x3 x4 ret : B256} (hsg : x4.toAdr = pair)
    (run : SFunc.RunCutP P Impl.cert.prog sevm []
      (St b (fl :: x0 :: x1 :: x2 :: x3 :: x4 :: ret :: S) M G) Impl.t_46c0_c8 r) : False :=
  walk8H hP hfork.rules_stateGas_none hfork.rules_bal_none
    (rejects.at_of_covered hfork) notPre hlib hpair hsg run

/-- `_permit(owner, spender, value, deadline, signature)` (entry 94, with its goto into entry 8). -/
theorem walk94H (hP : SiteStep P) (hstateGas : sevm.benvStat.rules.stateGas = none)
    (hbal : sevm.benvStat.rules.bal = none) {pair : Adr}
    (rejects : LibRejectsAt pair sevm) (notPre : ¬ sevm.benvStat.rules.isPrecomp pair)
    (hlib : b.getCode usdcLib = Lib.code) (hpair : b.getCode pair = UniswapV2Pair.code)
    {x0 x1 x2 x3 x4 ret : B256} (hsg : x4.toAdr = pair)
    (run : SFunc.RunCutP P Impl.cert.prog sevm []
      (St b (x0 :: x1 :: x2 :: x3 :: x4 :: ret :: S) M G) Impl.t_4692_c94 r) : False := by
  repeat sx_nonstorage run
  rcases ric_branchToP (k := 8) List.not_mem_nil rfl run with ⟨-, _, run⟩ | ⟨-, _, run⟩
  · repeat sx_nonstorage run
    sop run => ri_timestamp
    iterate 3 sx_nonstorage run
    exact walk8H hP hstateGas hbal rejects notPre hlib hpair hsg run
  · exact walk8H hP hstateGas hbal rejects notPre hlib hpair hsg run

/-- The original covered-fork entry94 interface. -/
theorem walk94 (hP : SiteStep P) (hfork : CoveredFork sevm.benvStat.fork) {pair : Adr}
    (rejects : LibRejects pair) (notPre : ¬ sevm.benvStat.rules.isPrecomp pair)
    (hlib : b.getCode usdcLib = Lib.code) (hpair : b.getCode pair = UniswapV2Pair.code)
    {x0 x1 x2 x3 x4 ret : B256} (hsg : x4.toAdr = pair)
    (run : SFunc.RunCutP P Impl.cert.prog sevm []
      (St b (x0 :: x1 :: x2 :: x3 :: x4 :: ret :: S) M G) Impl.t_4692_c94 r) : False :=
  walk94H hP hfork.rules_stateGas_none hfork.rules_bal_none
    (rejects.at_of_covered hfork) notPre hlib hpair hsg run

theorem path_cancelVrs (hP : SiteStep P) (hfork : CoveredFork sevm.benvStat.fork) {pair : Adr}
    (rejects : LibRejects pair) (notPre : ¬ sevm.benvStat.rules.isPrecomp pair)
    (hlib : b.getCode usdcLib = Lib.code) (hpair : b.getCode pair = UniswapV2Pair.code)
    (sel : Blanc.Sevm.selector sevm = 0x5a049a70) (hsg : (Sevm.dataWord sevm 4).toAdr = pair)
    (run : SFunc.RunCutP P Impl.cert.prog sevm [] (St b (Blanc.Sevm.selector sevm :: S) M G)
      dispTree r) : False := by
  rw [sel] at run
  repeat dispP run
  repeat sx run
  brP run
  repeat sx run
  enterP run 52
  repeat sx run
  brP run
  repeat sx run
  enterP run 97
  repeat sxx run
  enterP run 89
  exact walk89 hP hfork rejects notPre (by rw [afterSload_getCode]; exact hlib)
    (by rw [afterSload_getCode]; exact hpair) (by rw [word_ff20, toAdr_toB256, lit4]; exact hsg) run

theorem path_cancelBytes (hP : SiteStep P) (hfork : CoveredFork sevm.benvStat.fork) {pair : Adr}
    (rejects : LibRejects pair) (notPre : ¬ sevm.benvStat.rules.isPrecomp pair)
    (hlib : b.getCode usdcLib = Lib.code) (hpair : b.getCode pair = UniswapV2Pair.code)
    (sel : Blanc.Sevm.selector sevm = 0xb7b72899) (hsg : (Sevm.dataWord sevm 4).toAdr = pair)
    (run : SFunc.RunCutP P Impl.cert.prog sevm [] (St b (Blanc.Sevm.selector sevm :: S) M G)
      dispTree r) : False := by
  rw [sel] at run
  repeat dispP run
  repeat sx run
  brP run
  repeat sx run
  brP run
  obtain ⟨b1, u0, M1, G1, hs1, run⟩ := ric_seg_w136 (fun h => (hP h).1) hfork run
  enterP run 28
  repeat sx run
  brP run
  repeat sx run
  enterP run 89
  exact walk89 hP hfork rejects notPre
    (by rw [afterSload_getCode, getCode_of_state hs1]; exact hlib)
    (by rw [afterSload_getCode, getCode_of_state hs1]; exact hpair)
    (by rw [word_ff20, toAdr_toB256, lit4]; exact hsg) run

theorem path_permitVrsH (hP : SiteStep P) (hstateGas : sevm.benvStat.rules.stateGas = none)
    (hbal : sevm.benvStat.rules.bal = none) {pair : Adr}
    (rejects : LibRejectsAt pair sevm) (notPre : ¬ sevm.benvStat.rules.isPrecomp pair)
    (hlib : b.getCode usdcLib = Lib.code) (hpair : b.getCode pair = UniswapV2Pair.code)
    (sel : Blanc.Sevm.selector sevm = 0xd505accf) (hsg : (Sevm.dataWord sevm 4).toAdr = pair)
    (run : SFunc.RunCutP P Impl.cert.prog sevm [] (St b (Blanc.Sevm.selector sevm :: S) M G)
      dispTree r) : False := by
  rw [sel] at run
  repeat dispP run
  repeat sx_nonstorage run
  brP run
  repeat sx_nonstorage run
  enterP run 24
  iterate 2 sx_nonstorage run
  sop run => (ri_sloadH hbal)
  repeat sx_nonstorage run
  brP run
  repeat sx_nonstorage run
  enterP run 88
  repeat sxx_permit_nonstorage run
  enterP run 94
  exact walk94H hP hstateGas hbal rejects notPre (by rw [afterSloadH_getCode]; exact hlib)
    (by rw [afterSloadH_getCode]; exact hpair) (by rw [ff20_word, toAdr_toB256, lit4]; exact hsg) run

/-- The original covered-fork permitVrs interface. -/
theorem path_permitVrs (hP : SiteStep P) (hfork : CoveredFork sevm.benvStat.fork) {pair : Adr}
    (rejects : LibRejects pair) (notPre : ¬ sevm.benvStat.rules.isPrecomp pair)
    (hlib : b.getCode usdcLib = Lib.code) (hpair : b.getCode pair = UniswapV2Pair.code)
    (sel : Blanc.Sevm.selector sevm = 0xd505accf) (hsg : (Sevm.dataWord sevm 4).toAdr = pair)
    (run : SFunc.RunCutP P Impl.cert.prog sevm [] (St b (Blanc.Sevm.selector sevm :: S) M G)
      dispTree r) : False :=
  path_permitVrsH hP hfork.rules_stateGas_none hfork.rules_bal_none
    (rejects.at_of_covered hfork) notPre hlib hpair sel hsg run

theorem path_permitBytesH (hP : SiteStep P) (hstateGas : sevm.benvStat.rules.stateGas = none)
    (hbal : sevm.benvStat.rules.bal = none) {pair : Adr}
    (rejects : LibRejectsAt pair sevm) (notPre : ¬ sevm.benvStat.rules.isPrecomp pair)
    (hlib : b.getCode usdcLib = Lib.code) (hpair : b.getCode pair = UniswapV2Pair.code)
    (sel : Blanc.Sevm.selector sevm = 0x9fd5a6cf) (hsg : (Sevm.dataWord sevm 4).toAdr = pair)
    (run : SFunc.RunCutP P Impl.cert.prog sevm [] (St b (Blanc.Sevm.selector sevm :: S) M G)
      dispTree r) : False := by
  rw [sel] at run
  repeat dispP run
  repeat sxx_permit_nonstorage run
  brP run
  repeat sxx_permit_nonstorage run
  brP run
  obtain ⟨b1, u0, M1, G1, hs1, run⟩ := ric_seg_w149_noStateGas (fun h => (hP h).1) hstateGas run
  enterP run 41
  iterate 2 sx_nonstorage run
  sop run => (ri_sloadH hbal)
  repeat sx_nonstorage run
  brP run
  repeat sx_nonstorage run
  enterP run 94
  exact walk94H hP hstateGas hbal rejects notPre
    (by rw [afterSloadH_getCode, getCode_of_state hs1]; exact hlib)
    (by rw [afterSloadH_getCode, getCode_of_state hs1]; exact hpair)
    (by rw [ff20_word, toAdr_toB256, lit4]; exact hsg) run

/-- The original covered-fork permitBytes interface. -/
theorem path_permitBytes (hP : SiteStep P) (hfork : CoveredFork sevm.benvStat.fork) {pair : Adr}
    (rejects : LibRejects pair) (notPre : ¬ sevm.benvStat.rules.isPrecomp pair)
    (hlib : b.getCode usdcLib = Lib.code) (hpair : b.getCode pair = UniswapV2Pair.code)
    (sel : Blanc.Sevm.selector sevm = 0x9fd5a6cf) (hsg : (Sevm.dataWord sevm 4).toAdr = pair)
    (run : SFunc.RunCutP P Impl.cert.prog sevm [] (St b (Blanc.Sevm.selector sevm :: S) M G)
      dispTree r) : False :=
  path_permitBytesH hP hfork.rules_stateGas_none hfork.rules_bal_none
    (rejects.at_of_covered hfork) notPre hlib hpair sel hsg run

end Blanc.Lift.Usdc
