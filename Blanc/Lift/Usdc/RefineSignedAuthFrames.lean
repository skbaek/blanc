import Blanc.Lift.Usdc.RefineSignedAuthWalk
import Blanc.Lift.Usdc.RefineDispatch

/-!
# The frames of `transferWithAuthorization` and `receiveWithAuthorization` (U6e3)

From a successful implementation frame whose selector is one of the four authorization
overloads, through the preamble and the dispatcher (`impl_preamble_cut`, `SFunc.selWalk`), the
wrapper's ABI decoding (walked; the `bytes` tail by `ric_seg_w138`/`ric_seg_w151`) and the body
(`RefineSignedAuthWalk.lean`): the guards the frame passed and the storage it leaves.
-/

namespace Blanc.Lift.Usdc

open Jaune Blanc Blanc.Lift Impl

/-- The library account holds the library runtime when its image is the library's. -/
theorem lib_code_of_image {c : ByteArray} (h : some c.toList = libSem.image) : c = Lib.code := by
  apply ByteArray.ext
  apply Array.toList_inj.mp
  simpa only [ByteArray.toList_eq_toList_data] using Option.some.inj h

theorem route_twa_vrs : dispTree.selWalk 0xe3ee160e = .inl (0xe3ee160e, 129) := rfl
theorem route_rwa_vrs : dispTree.selWalk 0xef55bec6 = .inl (0xef55bec6, 125) := rfl
theorem route_twa_bytes : dispTree.selWalk 0xcf092995 = .inl (0xcf092995, 138) := rfl
theorem route_rwa_bytes : dispTree.selWalk 0x88b7ab63 = .inl (0x88b7ab63, 151) := rfl

/-- The guards an authorization frame passed and the storage it leaves, over the calldata words
`from` (4), `to` (36), `value` (68), `validAfter` (100), `validBefore` (132), `nonce` (164). -/
def AuthFrame (sevm : Sevm) (σ σ' : Stor) : Prop :=
  flag20 (σ.get 1) = false ∧ frozenBit (σ.get (balSlot (Sevm.dataWord sevm 4).toAdr)) = false ∧
    frozenBit (σ.get (balSlot (Sevm.dataWord sevm 36).toAdr)) = false ∧
    AuthPost sevm σ (Sevm.dataWord sevm 4).toAdr (Sevm.dataWord sevm 36).toAdr
      (Sevm.dataWord sevm 68) (Sevm.dataWord sevm 100) (Sevm.dataWord sevm 132)
      (Sevm.dataWord sevm 164) σ'

theorem lits_auth : Bytes.toB256 [4] = 4 ∧ Bytes.toB256 [4] + Bytes.toB256 [32] = 36 ∧
    Bytes.toB256 [4] + Bytes.toB256 [64] = 68 ∧ Bytes.toB256 [4] + Bytes.toB256 [96] = 100 ∧
    Bytes.toB256 [4] + Bytes.toB256 [128] = 132 ∧ Bytes.toB256 [4] + Bytes.toB256 [160] = 164 := by
  decide

variable {sevm : Sevm} {pre post : Devm}

theorem frame_twa_vrs (run : Exec 0 sevm pre (.ok post)) (code : sevm.code = Impl.code)
    (fork : CoveredFork sevm.benvStat.fork) (hcode : pre.getCode usdcLib = Lib.code)
    (sel : Blanc.Sevm.selector sevm = 0xe3ee160e) :
    AuthFrame sevm (pre.getStor sevm.currentTarget) (post.getStor sevm.currentTarget) := by
  obtain ⟨-, -, M, G, h⟩ := impl_preamble_cut (impl_run_cut run code fork)
  rw [sel] at h
  clear run
  obtain ⟨-, g, G', hg, h⟩ := SFunc.RunCut.selWalk_inl route_twa_vrs h
  cases hg
  unfold t_1075_c129 at h
  repeat istep h
  ibranch h c1
  repeat istep h
  icallA h hc 20 t_3889_c20
  obtain ⟨p0, f1, f2, b1, M1, G1, e, post1⟩ := e20_inv fork hcode hc
  cases e
  clear hc
  repeat istep h
  have sp := ric_stop_getStor h
  clear h
  obtain ⟨l4, l36, l68, l100, l132, l164⟩ := lits_auth
  simp only [l36, l68, l100, l132, l164] at f1 f2 post1
  simp only [ff20_word, toAdr_toB256, l4] at f1 f2 post1
  exact ⟨p0, f1, f2, by rw [congrFun sp]; exact post1⟩

theorem frame_rwa_vrs (run : Exec 0 sevm pre (.ok post)) (code : sevm.code = Impl.code)
    (fork : CoveredFork sevm.benvStat.fork) (hcode : pre.getCode usdcLib = Lib.code)
    (sel : Blanc.Sevm.selector sevm = 0xef55bec6) :
    sevm.caller = (Sevm.dataWord sevm 36).toAdr ∧ AuthFrame sevm (pre.getStor sevm.currentTarget) (post.getStor sevm.currentTarget) := by
  obtain ⟨-, -, M, G, h⟩ := impl_preamble_cut (impl_run_cut run code fork)
  rw [sel] at h
  clear run
  obtain ⟨-, g, G', hg, h⟩ := SFunc.RunCut.selWalk_inl route_rwa_vrs h
  cases hg
  unfold t_1122_c125 at h
  repeat istep h
  ibranch h c1
  repeat istep h
  icallA h hc 15 t_3aa2_c15
  obtain ⟨p0, f1, f2, cl, b1, M1, G1, e, post1⟩ := e15_inv fork hcode hc
  cases e
  clear hc
  repeat istep h
  have sp := ric_stop_getStor h
  clear h
  obtain ⟨l4, l36, l68, l100, l132, l164⟩ := lits_auth
  simp only [l36, l68, l100, l132, l164] at f1 f2 cl post1
  simp only [ff20_word, toAdr_toB256, l4] at f1 f2 cl post1
  exact ⟨cl, p0, f1, f2, by rw [congrFun sp]; exact post1⟩

theorem frame_twa_bytes (run : Exec 0 sevm pre (.ok post)) (code : sevm.code = Impl.code)
    (fork : CoveredFork sevm.benvStat.fork) (hcode : pre.getCode usdcLib = Lib.code)
    (sel : Blanc.Sevm.selector sevm = 0xcf092995) :
    AuthFrame sevm (pre.getStor sevm.currentTarget) (post.getStor sevm.currentTarget) := by
  obtain ⟨-, -, M, G, h⟩ := impl_preamble_cut (impl_run_cut run code fork)
  rw [sel] at h
  clear run
  obtain ⟨-, g, G', hg, h⟩ := SFunc.RunCut.selWalk_inl route_twa_bytes h
  cases hg
  unfold t_0e80_c138 at h
  repeat istep h
  ibranch h c1
  repeat istep h
  ibranch h c2
  repeat istep h
  ibranch h c3
  obtain ⟨b0, u0, M0, G0, st0, h⟩ := ric_seg_w138 fork h
  icallA h hc 30 t_3549_c30
  obtain ⟨p0, f1, f2, b1, M1, G1, e, post1⟩ := e30_inv fork ((getCode_eq_of_state_eq st0 _).trans hcode) hc
  cases e
  clear hc
  repeat istep h
  have sp := ric_stop_getStor h
  clear h
  rw [getStor_eq_of_state_eq st0] at p0 f1 f2 post1
  obtain ⟨l4, l36, l68, l100, l132, l164⟩ := lits_auth
  simp only [l36, l68, l100, l132, l164] at f1 f2 post1
  simp only [ff20_word, toAdr_toB256, l4] at f1 f2 post1
  exact ⟨p0, f1, f2, by rw [congrFun sp]; exact post1⟩

theorem frame_rwa_bytes (run : Exec 0 sevm pre (.ok post)) (code : sevm.code = Impl.code)
    (fork : CoveredFork sevm.benvStat.fork) (hcode : pre.getCode usdcLib = Lib.code)
    (sel : Blanc.Sevm.selector sevm = 0x88b7ab63) :
    sevm.caller = (Sevm.dataWord sevm 36).toAdr ∧ AuthFrame sevm (pre.getStor sevm.currentTarget) (post.getStor sevm.currentTarget) := by
  obtain ⟨-, -, M, G, h⟩ := impl_preamble_cut (impl_run_cut run code fork)
  rw [sel] at h
  clear run
  obtain ⟨-, g, G', hg, h⟩ := SFunc.RunCut.selWalk_inl route_rwa_bytes h
  cases hg
  unfold t_0a53_c151 at h
  repeat istep h
  ibranch h c1
  repeat istep h
  ibranch h c2
  repeat istep h
  ibranch h c3
  obtain ⟨b0, u0, M0, G0, st0, h⟩ := ric_seg_w151 fork h
  icallA h hc 43 t_2c16_c43
  obtain ⟨p0, f1, f2, cl, b1, M1, G1, e, post1⟩ := e43_inv fork ((getCode_eq_of_state_eq st0 _).trans hcode) hc
  cases e
  clear hc
  repeat istep h
  have sp := ric_stop_getStor h
  clear h
  rw [getStor_eq_of_state_eq st0] at p0 f1 f2 post1
  obtain ⟨l4, l36, l68, l100, l132, l164⟩ := lits_auth
  simp only [l36, l68, l100, l132, l164] at f1 f2 cl post1
  simp only [ff20_word, toAdr_toB256, l4] at f1 f2 cl post1
  exact ⟨cl, p0, f1, f2, by rw [congrFun sp]; exact post1⟩

end Blanc.Lift.Usdc
