-- DeploymentCompiled.lean : compiled execution against a creation-code prefix.
--
-- Creation code commonly appends runtime bytes and ABI data after the Blanc
-- program that executes them.  The compiler table still occupies the exact
-- prefix, while EVM instructions such as CODESIZE and CODECOPY must observe the
-- complete code image.  The bridge below keeps those two facts separate.

import Blanc.Compiled

namespace Blanc

open Jaune

/-! ## Compiler-table layout inside an appended code image -/

/-- A compiler-table entry remains an exact executable slice when arbitrary
data follows the compiled `Prog`. -/
lemma subcode_of_get?_eq_some_appended
    {f fs} {code : ByteArray} {pfxCode sfxData : Bytes} {k loc : Nat} {p : Func}
    (h_compile : some pfxCode = Prog.compile ⟨f, fs⟩)
    (h_code : code.toList = pfxCode ++ sfxData)
    (h_get : getElem? (table 0 (f :: fs)) k = some ⟨loc, p⟩) :
    Jinst.At code loc Jinst.jumpdest ∧
      subcode code.toList (loc + 1)
        (Func.compile (table 0 (f :: fs)) (loc + 1) p) := by
  rcases of_get?_table_eq_some h_compile h_get with
    ⟨lft, rgt, _, _, pfx, sfx, h_pfx, h_split, h_sfx⟩
  rcases Table.compile_cons_eq_some h_sfx.symm with
    ⟨bs, bs', h_bs, _, h_sfx'⟩
  have h_slice : List.Slice code.toList loc sfx := by
    rw [h_code, h_split, ← h_pfx, List.append_assoc]
    exact List.slice_prefix
      (List.append_slice_suffix (xs := pfx) (ys := sfx ++ sfxData))
  rw [h_sfx', List.append_assoc] at h_slice
  constructor
  · apply Jinst.at_of_slice
    exact List.slice_prefix h_slice
  · rw [h_bs]
    simp only [subcode]
    exact List.slice_prefix (List.slice_suffix h_slice)

/-- Every compiler-table target is jumpable inside a code image whose compiled
program is only a prefix. -/
theorem Prog.jumpable_of_get?_table_appended
    {f fs} {code : ByteArray} {pfxCode sfxData : Bytes}
    {n loc : Nat} {r : Func}
    (h_compile : some pfxCode = Prog.compile ⟨f, fs⟩)
    (h_code : code.toList = pfxCode ++ sfxData)
    (h_get : (table 0 (f :: fs))[n]? = some (loc, r)) :
    jumpable code loc = true ∧ noPushBefore code (loc + 1) 32 = true := by
  have hcmp :
      Table.compile (table 0 (f :: fs)) (table 0 (f :: fs)) = some pfxCode :=
    h_compile.symm
  have h_prefix : List.Slice code.toList 0 pfxCode := by
    rw [h_code]
    exact List.slice_prefix (List.slice_refl (pfxCode ++ sfxData))
  have hw := @Table.noPushBefore_compile code (table 0 (f :: fs))
    (f :: fs) 0 pfxCode hcmp h_prefix rfl n loc r h_get
  have hlt := ByteArray.lt_size_of_getElem?_eq_some hw.right
  have hbyte := ByteArray.getElem_of_getElem?_eq_some hw.right hlt
  refine ⟨?_, noPushBefore_succ_of_getElem? hw.right
    (by rw [Jinst.toInstType_toUInt8]; simp) hw.left⟩
  unfold jumpable
  rw [dif_pos hlt, hbyte, if_pos rfl]
  exact hw.left

/-! ## Appended-code liveness -/

/-- The compiled liveness bridge with compiler-table evidence restricted to an
exact prefix.  Individual EVM steps continue to read the full `sevm.code`. -/
theorem Func.exec_of_runCompiled_appended_core :
    ∀ {f₀ : Func} {fs' : List Func} {sevm : Sevm} {FS : List Func}
      {devm : Devm} {p : Func} {devm' : Devm} {pfxCode sfxData : Bytes},
      Func.RunCompiled FS sevm devm p devm' →
      some pfxCode = Prog.compile ⟨f₀, fs'⟩ →
      sevm.code.toList = pfxCode ++ sfxData →
      FS = f₀ :: fs' →
      ∀ pc,
        subcode sevm.code.toList pc
          (Func.compile (table 0 (f₀ :: fs')) pc p) →
        noPushBefore sevm.code pc 32 = true →
        Nonempty (Exec pc sevm devm (.ok devm')) := by
  intro f₀ fs' sevm FS devm p devm' pfxCode sfxData h_run
  induction h_run with
  | zero h_room h_pop h_f ih =>
    intro h_compile h_code hFS pc sub hb
    rcases subcode_compile_branch_jumpable sub hb with
      ⟨loc, h_loc_eq, h_loc, h_push, h_jumpi, h_subp, h_bp, h_jd, h_jp,
        h_subq, h_bq⟩
    rcases Evm.branch_zero_steps h_push h_jumpi h_loc h_room h_pop with ⟨h1, h2⟩
    obtain ⟨excf⟩ := ih h_compile h_code hFS (pc + 4) h_subp h_bp
    exact ⟨Exec.cont h1 (Exec.cont h2 excf)⟩
  | succ h_ne h_room h_pop h_g ih =>
    intro h_compile h_code hFS pc sub hb
    rcases subcode_compile_branch_jumpable sub hb with
      ⟨loc, h_loc_eq, h_loc, h_push, h_jumpi, h_subp, h_bp, h_jd, h_jp,
        h_subq, h_bq⟩
    rcases Evm.branch_succ_steps h_push h_jumpi h_jd h_jp h_loc h_ne h_room h_pop
      with ⟨h1, h2, h3⟩
    obtain ⟨excg⟩ := ih h_compile h_code hFS (loc + 1) h_subq h_bq
    exact ⟨Exec.cont h1 (Exec.cont h2 (Exec.cont h3 excg))⟩
  | last h_lin =>
    intro h_compile h_code hFS pc sub hb
    refine ⟨Exec.halt ?_⟩
    rw [Evm.step_last (Linst.at_of_slice sub)]
    exact congrArg Step.halt h_lin
  | next h_n h_f ih =>
    intro h_compile h_code hFS pc sub hb
    rcases Func.noPushBefore_next sub hb with ⟨hb', sub'⟩
    rcases of_subcode sub with ⟨cd, h_eq', h_slice⟩
    rcases of_bind_eq_some h_eq' with ⟨cd', h_eq'', h_rw⟩
    simp [pure] at h_rw
    rw [← h_rw] at h_slice
    rcases h_n with ⟨xl, h_filled, h_step⟩
    exact Ninst.exec_of_stepRun (Ninst.at_of_slice (List.slice_prefix h_slice))
      h_filled (h_step pc) (ih h_compile h_code hFS _ sub' hb')
  | call h_get h_room h_burn h_f ih =>
    intro h_compile h_code hFS pc sub hb
    subst hFS
    rcases subcode_compile_call sub with
      ⟨loc, p₁, h_get_tab, h_loc, h_pushAt, h_jump⟩
    have h_pf := (Prog.get?_table (m := 0)).symm.trans
      (congrArg (Prod.snd <$> ·) h_get_tab)
    rw [h_get] at h_pf
    simp only [Option.map_eq_map, Option.map_some, Option.some.injEq] at h_pf
    subst h_pf
    rcases subcode_of_get?_eq_some_appended h_compile h_code h_get_tab with
      ⟨h_jd, h_subf⟩
    have h_jpb :=
      Prog.jumpable_of_get?_table_appended h_compile h_code h_get_tab
    rcases h_pushAt with ⟨le, h_push⟩
    rcases Evm.call_steps (le := le) h_push h_jump h_jd h_jpb.1 h_loc h_room h_burn
      with ⟨h1, h2, h3⟩
    obtain ⟨excf⟩ := ih h_compile h_code rfl (loc + 1) h_subf h_jpb.2
    exact ⟨Exec.cont h1 (Exec.cont h2 (Exec.cont h3 excf))⟩

/-- A gas-exact run of a compiled program executes successfully when the
compiled bytes are an exact prefix of the full EVM code image. -/
theorem Prog.exec_of_runCompiled_appended
    {sevm : Sevm} {pre : Devm} {p : Prog} {post : Devm}
    {pfxCode sfxData : Bytes}
    (h : Prog.RunCompiled sevm pre p post)
    (h_compile : some pfxCode = p.compile)
    (h_code : sevm.code.toList = pfxCode ++ sfxData) :
    exec ⟨0, sevm, pre⟩ = .ok post := by
  rcases h with ⟨mid, h_burn, h_run⟩
  have h_compile' : some pfxCode = Prog.compile ⟨p.main, p.aux⟩ := h_compile
  have h_get : (table 0 (p.main :: p.aux))[0]? = some (0, p.main) := rfl
  rcases subcode_of_get?_eq_some_appended h_compile' h_code h_get with
    ⟨h_jd, h_sub⟩
  have h_npb : noPushBefore sevm.code 1 32 = true :=
    (Prog.jumpable_of_get?_table_appended h_compile' h_code h_get).2
  have h1 : Evm.step ⟨0, sevm, pre⟩ = .cont 1 mid :=
    Evm.jumpdest_cont h_jd h_burn
  obtain ⟨exc⟩ := Func.exec_of_runCompiled_appended_core
    h_run h_compile' h_code rfl 1 h_sub h_npb
  rw [← exec_iff_exec_eq]
  exact ⟨Exec.cont h1 exc⟩

end Blanc
