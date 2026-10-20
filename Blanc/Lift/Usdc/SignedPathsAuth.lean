import Blanc.Lift.Usdc.SignedPathsKit

/-!
# F7b: the four authorization paths reach `_requireValidSignature`

`transferWithAuthorization` and `receiveWithAuthorization`, both ABI overloads (wrappers 129/138 and
125/151, bodies 20/30 and 15/43, adapters 87 and 84, internals 90 and 95), re-walked from the
dispatcher under a `SiteStep` relation to the `callNext 111` with the authorization's `from` as the
signer, where `site111_call_false` closes them.
-/

namespace Blanc.Lift.Usdc

open Jaune Blanc Blanc.Lift Blanc.Lift.FreePtr

variable {P : Sevm → Devm → Ninst → Devm → Prop} {sevm : Sevm} {b : Devm}
  {S : List B256} {M : Mem} {G : Nat} {r : Seg}

section Walks

variable (hP : SiteStep P) (hfork : CoveredFork sevm.benvStat.fork) {pair : Adr}
  (rejects : LibRejects pair) (notPre : ¬ sevm.benvStat.rules.isPrecomp pair)
  (hlib : b.getCode usdcLib = Lib.code) (hpair : b.getCode pair = UniswapV2Pair.code)
include hP hfork rejects notPre hlib hpair

/-- `_transferWithAuthorization` (entry 90) reaches entry 111 with `from` (`x6`) as the signer. -/
theorem walk90 {x0 x1 x2 x3 x4 x5 x6 ret : B256} (hsg : x6.toAdr = pair)
    (run : SFunc.RunCutP P Impl.cert.prog sevm []
      (St b (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: ret :: S) M G) Impl.t_4b49_c90 r) :
    False := by
  repeat sx run
  obtain ⟨b1, M1, G1, hs1, run⟩ := skipP_112 hP hfork run
  obtain ⟨b2, u0, M2, G2, hs2, run⟩ := ric_seg_e90 (fun h => (hP h).1) hfork run
  have hgc : ∀ a, b2.getCode a = b.getCode a := fun a => by
    rw [getCode_of_state hs2, getCode_of_state hs1]
  exact site111_call_false hP hfork rejects notPre (by rw [hgc]; exact hlib)
    (by rw [hgc]; exact hpair) hsg run

/-- `_receiveWithAuthorization` (entry 95) reaches entry 111 with `from` (`x6`) as the signer. -/
theorem walk95 {x0 x1 x2 x3 x4 x5 x6 ret : B256} (hsg : x6.toAdr = pair)
    (run : SFunc.RunCutP P Impl.cert.prog sevm []
      (St b (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: ret :: S) M G) Impl.t_4571_c95 r) :
    False := by
  repeat sx run
  brP run
  repeat sx run
  obtain ⟨b1, M1, G1, hs1, run⟩ := skipP_112 hP hfork run
  obtain ⟨b2, u0, M2, G2, hs2, run⟩ := ric_seg_e95 (fun h => (hP h).1) hfork run
  have hgc : ∀ a, b2.getCode a = b.getCode a := fun a => by
    rw [getCode_of_state hs2, getCode_of_state hs1]
  exact site111_call_false hP hfork rejects notPre (by rw [hgc]; exact hlib)
    (by rw [hgc]; exact hpair) hsg run

/-- The `(v, r, s)` adapter of `transferWithAuthorization` (entry 87), into entry 90. -/
theorem walk87 {x0 x1 x2 x3 x4 x5 x6 x7 x8 ret : B256} (hsg : x8.toAdr = pair)
    (run : SFunc.RunCutP P Impl.cert.prog sevm []
      (St b (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: ret :: S) M G) Impl.t_4c3f_c87 r) :
    False := by
  obtain ⟨b1, u0, M1, G1, hs1, run⟩ := ric_seg_e87 (fun h => (hP h).1) hfork run
  enterP run 90
  exact walk90 hP hfork rejects notPre (by rw [getCode_of_state hs1]; exact hlib)
    (by rw [getCode_of_state hs1]; exact hpair) hsg run

/-- The `(v, r, s)` adapter of `receiveWithAuthorization` (entry 84), into entry 95. -/
theorem walk84 {x0 x1 x2 x3 x4 x5 x6 x7 x8 ret : B256} (hsg : x8.toAdr = pair)
    (run : SFunc.RunCutP P Impl.cert.prog sevm []
      (St b (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: ret :: S) M G) Impl.t_4c83_c84 r) :
    False := by
  obtain ⟨b1, u0, M1, G1, hs1, run⟩ := ric_seg_e84 (fun h => (hP h).1) hfork run
  enterP run 95
  exact walk95 hP hfork rejects notPre (by rw [getCode_of_state hs1]; exact hlib)
    (by rw [getCode_of_state hs1]; exact hpair) hsg run

/-- The body of `transferWithAuthorization(…, v, r, s)` (entry 20), into entry 87. -/
theorem walk20 {x0 x1 x2 x3 x4 x5 x6 x7 x8 ret : B256} (hsg : x8.toAdr = pair)
    (run : SFunc.RunCutP P Impl.cert.prog sevm []
      (St b (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: ret :: S) M G) Impl.t_3889_c20 r) :
    False := by
  repeat sx run
  brP run
  repeat sx run
  obtain ⟨b1, y1, M1, G1, hs1, run⟩ := skipP_83 hP hfork run
  repeat sx run
  brP run
  repeat sx run
  obtain ⟨b2, y2, M2, G2, hs2, run⟩ := skipP_83 hP hfork run
  repeat sx run
  brP run
  repeat sx run
  enterP run 87
  exact walk87 hP hfork rejects notPre
    (by simp only [afterSload_getCode, getCode_of_state hs1, getCode_of_state hs2]; exact hlib)
    (by simp only [afterSload_getCode, getCode_of_state hs1, getCode_of_state hs2]; exact hpair)
    hsg run

/-- The body of `receiveWithAuthorization(…, v, r, s)` (entry 15), into entry 84. -/
theorem walk15 {x0 x1 x2 x3 x4 x5 x6 x7 x8 ret : B256} (hsg : x8.toAdr = pair)
    (run : SFunc.RunCutP P Impl.cert.prog sevm []
      (St b (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: ret :: S) M G) Impl.t_3aa2_c15 r) :
    False := by
  repeat sx run
  brP run
  repeat sx run
  obtain ⟨b1, y1, M1, G1, hs1, run⟩ := skipP_83 hP hfork run
  repeat sx run
  brP run
  repeat sx run
  obtain ⟨b2, y2, M2, G2, hs2, run⟩ := skipP_83 hP hfork run
  repeat sx run
  brP run
  repeat sx run
  enterP run 84
  exact walk84 hP hfork rejects notPre
    (by simp only [afterSload_getCode, getCode_of_state hs1, getCode_of_state hs2]; exact hlib)
    (by simp only [afterSload_getCode, getCode_of_state hs1, getCode_of_state hs2]; exact hpair)
    hsg run

/-- The body of `transferWithAuthorization(…, signature)` (entry 30), into entry 90. -/
theorem walk30 {x0 x1 x2 x3 x4 x5 x6 ret : B256} (hsg : x6.toAdr = pair)
    (run : SFunc.RunCutP P Impl.cert.prog sevm []
      (St b (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: ret :: S) M G) Impl.t_3549_c30 r) :
    False := by
  repeat sx run
  brP run
  repeat sx run
  obtain ⟨b1, y1, M1, G1, hs1, run⟩ := skipP_83 hP hfork run
  repeat sx run
  brP run
  repeat sx run
  obtain ⟨b2, y2, M2, G2, hs2, run⟩ := skipP_83 hP hfork run
  repeat sx run
  brP run
  repeat sx run
  enterP run 90
  exact walk90 hP hfork rejects notPre
    (by simp only [afterSload_getCode, getCode_of_state hs1, getCode_of_state hs2]; exact hlib)
    (by simp only [afterSload_getCode, getCode_of_state hs1, getCode_of_state hs2]; exact hpair)
    hsg run

/-- The body of `receiveWithAuthorization(…, signature)` (entry 43), into entry 95. -/
theorem walk43 {x0 x1 x2 x3 x4 x5 x6 ret : B256} (hsg : x6.toAdr = pair)
    (run : SFunc.RunCutP P Impl.cert.prog sevm []
      (St b (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: ret :: S) M G) Impl.t_2c16_c43 r) :
    False := by
  repeat sx run
  brP run
  repeat sx run
  obtain ⟨b1, y1, M1, G1, hs1, run⟩ := skipP_83 hP hfork run
  repeat sx run
  brP run
  repeat sx run
  obtain ⟨b2, y2, M2, G2, hs2, run⟩ := skipP_83 hP hfork run
  repeat sx run
  brP run
  repeat sx run
  enterP run 95
  exact walk95 hP hfork rejects notPre
    (by simp only [afterSload_getCode, getCode_of_state hs1, getCode_of_state hs2]; exact hlib)
    (by simp only [afterSload_getCode, getCode_of_state hs1, getCode_of_state hs2]; exact hpair)
    hsg run

end Walks

variable (hP : SiteStep P) (hfork : CoveredFork sevm.benvStat.fork) {pair : Adr}
  (rejects : LibRejects pair) (notPre : ¬ sevm.benvStat.rules.isPrecomp pair)
  (hlib : b.getCode usdcLib = Lib.code) (hpair : b.getCode pair = UniswapV2Pair.code)
  (hsg : (Sevm.dataWord sevm 4).toAdr = pair)
include hP hfork rejects notPre hlib hpair hsg

theorem path_twaVrs (sel : Blanc.Sevm.selector sevm = 0xe3ee160e)
    (run : SFunc.RunCutP P Impl.cert.prog sevm [] (St b (Blanc.Sevm.selector sevm :: S) M G)
      dispTree r) : False := by
  rw [sel] at run
  repeat dispP run
  repeat sx run
  brP run
  repeat sx run
  enterP run 20
  exact walk20 hP hfork rejects notPre hlib hpair (by rw [ff20_word, toAdr_toB256, lit4]; exact hsg) run

theorem path_rwaVrs (sel : Blanc.Sevm.selector sevm = 0xef55bec6)
    (run : SFunc.RunCutP P Impl.cert.prog sevm [] (St b (Blanc.Sevm.selector sevm :: S) M G)
      dispTree r) : False := by
  rw [sel] at run
  repeat dispP run
  repeat sx run
  brP run
  repeat sx run
  enterP run 15
  exact walk15 hP hfork rejects notPre hlib hpair (by rw [ff20_word, toAdr_toB256, lit4]; exact hsg) run

theorem path_twaBytes (sel : Blanc.Sevm.selector sevm = 0xcf092995)
    (run : SFunc.RunCutP P Impl.cert.prog sevm [] (St b (Blanc.Sevm.selector sevm :: S) M G)
      dispTree r) : False := by
  rw [sel] at run
  repeat dispP run
  repeat sx run
  brP run
  repeat sx run
  brP run
  repeat sx run
  brP run
  obtain ⟨b1, u0, M1, G1, hs1, run⟩ := ric_seg_w138 (fun h => (hP h).1) hfork run
  enterP run 30
  exact walk30 hP hfork rejects notPre (by rw [getCode_of_state hs1]; exact hlib)
    (by rw [getCode_of_state hs1]; exact hpair) (by rw [ff20_word, toAdr_toB256, lit4]; exact hsg) run

theorem path_rwaBytes (sel : Blanc.Sevm.selector sevm = 0x88b7ab63)
    (run : SFunc.RunCutP P Impl.cert.prog sevm [] (St b (Blanc.Sevm.selector sevm :: S) M G)
      dispTree r) : False := by
  rw [sel] at run
  repeat dispP run
  repeat sx run
  brP run
  repeat sx run
  brP run
  repeat sx run
  brP run
  obtain ⟨b1, u0, M1, G1, hs1, run⟩ := ric_seg_w151 (fun h => (hP h).1) hfork run
  enterP run 43
  exact walk43 hP hfork rejects notPre (by rw [getCode_of_state hs1]; exact hlib)
    (by rw [getCode_of_state hs1]; exact hpair) (by rw [ff20_word, toAdr_toB256, lit4]; exact hsg) run

end Blanc.Lift.Usdc
