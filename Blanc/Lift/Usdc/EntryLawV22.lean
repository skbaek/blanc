import Blanc.Lift.Usdc.EntryLawV2
import Blanc.Lift.Usdc.AllowLocalityV2_2
import Blanc.Lift.Usdc.V22BalanceLaws
import Blanc.Lift.Usdc.RefineAdminRun
import Blanc.Lift.Usdc.RefineAdminLedger
import Blanc.Lift.Usdc.RefineSignedAuthFrames
import Blanc.Lift.ChainStatic
import Blanc.Lift.Usdc.AllowanceRawHistory

/-!
# FiatTokenV2_2's entry law, on balance bits, and the family theorem

`v22_certFrame`: off the rescue path V2_2's descendants are the library, which never stores, and below it static frames.
`move_bits_cell`: what a move does to the holder's bits. `v22_frame_law`, per selector, and `v22_entry_law` at the proxy
frame. `usdc_entry_law`: one law over the three versions, selected by the code the implementation word finds.
Blacklisting writes the holder's whole word and keeps its bits, so it is not a holder action and needs no premise.
-/

namespace Blanc.Lift.Usdc

open Jaune Blanc Blanc.Lift Blanc.Lift.WriteSite Blanc.ExecutionTrace Impl

/-! ## The chain -/

/-- **Off rescue, V2_2's writes lie on its chain.** -/
theorem v22_certFrame {G : Exec.Frame} {T : Adr} (pc : G.pc = 0) (hcode : G.sevm.code = Impl.code)
    (hsg : G.sevm.benvStat.rules.stateGas = none) (target : G.sevm.currentTarget = T)
    (hasCode : (G.pre.getCode T).toList ≠ []) (libCode : G.pre.getCode usdcLib = Lib.code)
    (notRescue : Blanc.Sevm.selector G.sevm ≠ rescueSelector) : CertFrame G Impl.code T := by
  obtain ⟨gpc, sevm, pre, out, run, committed⟩ := G
  dsimp only at pc hcode hsg target hasCode libCode notRescue
  subst pc
  refine ⟨rfl, hcode, hsg, target, hasCode, fun {_} member {_} found => write_onChain_of run ?_ member found⟩
  refine Exec.rawFrameDescendants_of_chain (root := ⟨0, sevm, pre, out, run⟩) ?_ run (.refl _)
  intro nodePc nextPc nodeSevm nodePre nout raw frame rsm cevm nrun chain step enter child D member
  obtain ⟨x, hat, spawn, -⟩ := Evm.step_spawn_inv step
  have hx : x = .delegatecall := by
    have := v22_noCall run hcode hsg notRescue _ chain x hat
    simpa only [onlyDelegate, beq_iff_eq] using this
  subst hx
  have ccode : cevm.sta.code = Lib.code := by
    rw [Frame.enter_run_code enter]
    exact impl_delegate_lib run hcode hsg libCode chain hat spawn
  have sevmEq : nodeSevm = sevm := Blanc.Exec.Deriv.ParentPrefix.sevm_eq chain
  have csg : cevm.sta.benvStat.rules.stateGas = none := by
    rw [Blanc.Evm.step_spawn_child_benvStat step enter, sevmEq]
    exact hsg
  obtain ⟨pcZero, -, -⟩ := Blanc.Evm.step_spawn_child step enter
  obtain ⟨cpc, csevm, cdyna⟩ := cevm
  dsimp only at pcZero ccode csg child member
  subst pcZero
  simp only [Exec.rawFrameRoots, List.mem_cons] at member
  rcases member with rfl | member
  · exact .inr fun m same w found => lib_no_sstore_node rfl csg same ccode found
  · exact .inl (chain_static_descendants (root := ⟨0, csevm, cdyna, raw, child⟩)
      (fun M ch y hatM => by
        obtain ⟨κ, reach, ok⟩ := cursor_of_parentPrefix_noStateGas Lib.cert_check
          (F := ⟨0, csevm, cdyna, raw, child⟩) rfl ccode csg ch
        exact isStaticcall_eq (ok.execsSatisfy (Cursor.execsSatisfy_of_reachable lib_staticOnly reach) hatM))
      child (.refl _) D member)

/-! ## Bits -/

section Bits

variable {σ σ' : Stor} {a d h : Adr} {v : Nat}

/-- **What a move does to the holder's bits.** -/
theorem move_bits_cell (le : v ≤ balanceBits (σ.get (balSlot a)))
    (hb : balanceBits ((debitStor σ a v).get (balSlot d)) + v ≤ 2 ^ 255 - 1)
    (st : σ' = creditStor (debitStor σ a v) d v)
    (ea : balSlot a = balSlot h → a = h) (ed : balSlot d = balSlot h → d = h) :
    MoveCell (balanceBits (σ.get (balSlot h))) (balanceBits (σ'.get (balSlot h))) a d h v := by
  subst st
  have lt : ∀ w, balanceBits w < 2 ^ 255 := fun w => Nat.mod_lt _ (Nat.two_pow_pos 255)
  refine ⟨fun ha hd => ?_, fun ha hd => ?_, fun ha hd => ?_, fun ha hd => ?_⟩
  · unfold creditStor debitStor
    rw [Stor.get_set_ne _ (fun e => hd (ed e)), Stor.get_set_ne _ (fun e => ha (ea e))]
  · subst hd
    have ne : balSlot a ≠ balSlot d := fun e => ha (ea e)
    unfold creditStor
    rw [Stor.get_set_self, bits_toB256_of_le hb]
    unfold debitStor
    rw [Stor.get_set_ne _ ne]
  · subst ha
    exact move_bits_source (fun e => hd (ed e.symm)) le
  · subst ha
    subst hd
    unfold creditStor
    rw [Stor.get_set_self, bits_toB256_of_le hb]
    unfold debitStor at hb ⊢
    rw [Stor.get_set_self] at hb ⊢
    have := lt (σ.get (balSlot d))
    rw [balanceBits_toB256 (by omega)]
    omega

/-- A write keeping a word's bits keeps every slot's bits. -/
theorem set_bits_keep {K W : B256} (hw : balanceBits W = balanceBits (σ.get K)) (k : B256) :
    balanceBits ((σ.set K W).get k) = balanceBits (σ.get k) := by
  by_cases e : K = k
  · subst e
    rw [Stor.get_set_self, hw]
  · rw [Stor.get_set_ne _ e]

end Bits

/-! ## The operators' frames -/

section Frames

variable {sevm : Sevm} {b D : Devm} {S : List B256} {M : Mem} {G : Nat}

/-- `blacklist` keeps every slot's bits. -/
theorem frame_blacklist_bits (fork : HistFork sevm.benvStat.fork) (hsel : Blanc.Sevm.selector sevm = 0xf9f92be4)
    (run : SFunc.RunCut cert.prog sevm [] (St b S M G) t_0000_c0 (.done (.halted D))) (k : B256) :
    balanceBits ((D.getStor sevm.currentTarget).get k) = balanceBits ((b.getStor sevm.currentTarget).get k) := by
  obtain ⟨-, -, hs⟩ := blacklist_run fork hsel run
  rw [hs]
  exact set_bits_keep (balanceBits_blacklistWord _) k

/-- `unBlacklist` keeps every slot's bits. -/
theorem frame_unBlacklist_bits (fork : HistFork sevm.benvStat.fork) (hsel : Blanc.Sevm.selector sevm = 0x1a895266)
    (run : SFunc.RunCut cert.prog sevm [] (St b S M G) t_0000_c0 (.done (.halted D))) (k : B256) :
    balanceBits ((D.getStor sevm.currentTarget).get k) = balanceBits ((b.getStor sevm.currentTarget).get k) := by
  obtain ⟨-, -, hs⟩ := unBlacklist_run fork hsel run
  simp only [ff20_and_word, and_ff20_word, toAdr_toB256] at hs
  rw [hs]
  exact set_bits_keep (balanceBits_unBlacklistWord _) k

/-- `mint`: credit only, on bits. -/
theorem frame_mint_bits (fork : HistFork sevm.benvStat.fork) (hsel : Blanc.Sevm.selector sevm = 0x40c10f19)
    (run : SFunc.RunCut cert.prog sevm [] (St b S M G) t_0000_c0 (.done (.halted D))) :
    ∃ A W m, let σ := (b.getStor sevm.currentTarget).set 11 A
      balanceBits (σ.get (balSlot (Sevm.dataWord sevm 4).toAdr)) ≤ balanceBits W ∧
      D.getStor sevm.currentTarget = (σ.set (balSlot (Sevm.dataWord sevm 4).toAdr) W).set (minterAllowanceSlot sevm.caller) m := by
  obtain ⟨-, -, -, -, -, -, -, -, -, f9, f10, -, -, hs⟩ := mint_run fork hsel run
  simp only [ff20_and_word, and_ff20_word, toAdr_toB256, b4, b9, b11, b13, b36'] at f9 f10 hs
  have hbal := add_noWrap f9
  rw [lo255_and_toNat] at hbal
  refine ⟨_, _, _, ?_, hs⟩
  rw [balanceBits_of_le f10, hbal.1]
  exact Nat.le_add_left _ _

/-- `burn` writes the caller's entry and the supply. -/
theorem frame_burn_shape (fork : HistFork sevm.benvStat.fork) (hsel : Blanc.Sevm.selector sevm = 0x42966c68)
    (run : SFunc.RunCut cert.prog sevm [] (St b S M G) t_0000_c0 (.done (.halted D))) :
    ∃ A W, D.getStor sevm.currentTarget = ((b.getStor sevm.currentTarget).set 11 A).set (balSlot sevm.caller) W := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hs⟩ := burn_run fork hsel run
  simp only [ff20_and_word, and_ff20_word, toAdr_toB256, b4, b9, b11] at hs
  exact ⟨_, _, hs⟩

end Frames

/-- A committed frame's run, in the cut form. -/
theorem run_cut_of_frame {F : Exec.Frame} (pc : F.pc = 0) (hcode : F.sevm.code = Impl.code)
    (hsg : F.sevm.benvStat.rules.stateGas = none) :
    SFunc.RunCut cert.prog F.sevm [] (St F.pre F.pre.stack F.pre.memory F.pre.gasLeft) t_0000_c0
      (.done (.halted F.post)) :=
  SFunc.Run.cut (run_of_frame Impl.cert_check rfl pc hcode hsg)

/-- The four signed moves of V2_2, in the signed walks' form. -/
def v22Auths : List B256 := [0xe3ee160e, 0xef55bec6, 0xcf092995, 0x88b7ab63]

theorem auth_of_frame {F : Exec.Frame} (pc : F.pc = 0) (hcode : F.sevm.code = Impl.code)
    (fork : HistFork F.sevm.benvStat.fork) (lib : F.pre.getCode usdcLib = Lib.code)
    (sel : Blanc.Sevm.selector F.sevm ∈ v22Auths) :
    AuthFrame F.sevm (F.pre.getStor F.sevm.currentTarget) (F.post.getStor F.sevm.currentTarget) := by
  obtain ⟨fpc, sevm, pre, out, run, committed⟩ := F
  dsimp only at pc hcode fork lib sel ⊢
  subst pc
  cases out with
  | error e => simp only [Execution.commits, Bool.false_eq_true] at committed
  | ok post =>
    simp only [v22Auths, List.mem_cons, List.not_mem_nil, or_false] at sel
    rcases sel with s | s | s | s
    · exact (frame_twa_vrs run hcode fork lib s).1
    · exact (frame_rwa_vrs run hcode fork lib s).2.1
    · exact (frame_twa_bytes run hcode fork lib s).1
    · exact (frame_rwa_bytes run hcode fork lib s).2.1

/-! ## One frame -/

section Law

variable {T h : Adr} {frames : List Exec.Frame} {F G : Exec.Frame}

section Sites
theorem s_t_caller : (⟨.kecc (.op2 .and .caller addrMaskT) (.const 9), [(selV2T, 0xa9059cbb)], false⟩ : Site) ∈ wsRoot ImplWs.implWsAnn := by
  decide +kernel
theorem s_t_cd4 : (⟨.kecc (.op2 .and (.cd (.const 4)) addrMaskT) (.const 9), [(selV2T, 0xa9059cbb)], false⟩ : Site) ∈ wsRoot ImplWs.implWsAnn := by
  decide +kernel
theorem s_f_cd4 : (⟨.kecc (.op2 .and (.cd (.const 4)) addrMaskT) (.const 9), [(selV2T, 0x23b872dd)], false⟩ : Site) ∈ wsRoot ImplWs.implWsAnn := by
  decide +kernel
theorem s_f_cd36 : (⟨.kecc (.op2 .and (.cd (.const 0x24)) addrMaskT) (.const 9), [(selV2T, 0x23b872dd)], false⟩ : Site) ∈ wsRoot ImplWs.implWsAnn := by
  decide +kernel
theorem s_f_row : (⟨.kecc .caller (.kecc (.op2 .and (.cd (.const 4)) addrMaskT) (.const 10)), [(selV2T, 0x23b872dd)], true⟩ : Site) ∈ wsRoot ImplWs.implWsAnn := by
  decide +kernel
theorem s_m_supply : (⟨.const 0xb, [(selV2T, 0x40c10f19)], false⟩ : Site) ∈ wsRoot ImplWs.implWsAnn := by
  decide +kernel
theorem s_m_minter : (⟨.kecc .caller (.const 13), [(selV2T, 0x40c10f19)], false⟩ : Site) ∈ wsRoot ImplWs.implWsAnn := by
  decide +kernel
theorem s_b_supply : (⟨.const 0xb, [(selV2T, 0x42966c68)], true⟩ : Site) ∈ wsRoot ImplWs.implWsAnn := by
  decide +kernel
theorem s_b_caller : (⟨.kecc (.op2 .and .caller addrMaskT) (.const 9), [(selV2T, 0x42966c68)], false⟩ : Site) ∈ wsRoot ImplWs.implWsAnn := by
  decide +kernel
end Sites

abbrev v22Keys (h : Adr) (frames : List Exec.Frame) : Prop := CoinKeysFresh (wsRoot ImplWs.implWsAnn) 9 10 h frames

theorem v22_callers : ∀ c ∈ selV2_2.callers, ¬ CurveCoins.PoolCoinSel c := by
  intro c hc p
  simp only [selV2_2, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> rcases p with p | p | p <;> exact absurd p (by decide)

theorem v22_transfer_case (hF : F ∈ frames) (pc : G.pc = 0) (hcode : G.sevm.code = Impl.code)
    (fork : HistFork G.sevm.benvStat.fork) (same : SameMessage F G) (keys : v22Keys h frames)
    (s : Blanc.Sevm.selector F.sevm = 0xa9059cbb) :
    balanceBits ((Devm.getStor G.pre G.sevm.currentTarget).get (balSlot h)) + ownCredit h G.sevm ≤
      balanceBits ((Devm.getStor G.post G.sevm.currentTarget).get (balSlot h)) + ownDebit h G.sevm := by
  have sel : Blanc.Sevm.selector G.sevm = 0xa9059cbb := by rw [same.sel]; exact s
  obtain ⟨-, -, -, -, le, -, -, hb, st⟩ :=
    frame_transfer fork sel (run_of_frame Impl.cert_check rfl pc hcode fork.stateGas_none)
  refine transfer_cell sel (move_bits_cell le hb st ?_ ?_)
  · rw [same.caller]
    exact bal_caller_eq selV2T_eval keys hF s_t_caller s
  · rw [same.word]
    exact bal_cd_eq selV2T_eval keys hF s_t_cd4 s

theorem v22_from_case (hF : F ∈ frames) (pc : G.pc = 0) (hcode : G.sevm.code = Impl.code)
    (fork : HistFork G.sevm.benvStat.fork) (same : SameMessage F G) (keys : v22Keys h frames)
    (s : Blanc.Sevm.selector F.sevm = 0x23b872dd)
    (rows : RowsEmpty h frames (Devm.getStor G.pre G.sevm.currentTarget)) :
    balanceBits ((Devm.getStor G.pre G.sevm.currentTarget).get (balSlot h)) + ownCredit h G.sevm ≤
      balanceBits ((Devm.getStor G.post G.sevm.currentTarget).get (balSlot h)) + ownDebit h G.sevm := by
  have sel : Blanc.Sevm.selector G.sevm = 0x23b872dd := by rw [same.sel]; exact s
  obtain ⟨-, -, -, -, allow, -, -, le, -, hb, -, st⟩ :=
    frame_transferFrom fork sel (run_of_frame Impl.cert_check rfl pc hcode fork.stateGas_none)
  have apart : allowSlot (Sevm.dataWord G.sevm 4).toAdr G.sevm.caller ≠ balSlot h := by
    rw [same.caller, same.word]
    have mem := site_key_mem (extra := []) (balBase := 9) (allowBase := 10) (h := h) (sel := 0x23b872dd)
      (slot := .kecc .caller (.kecc (.op2 .and (.cd (.const 4)) addrMaskT) (.const 10))) (ni := true)
      selV2T_eval hF s_f_row rfl s
    simp only [termKey, addrMaskT_eval, cd_eval] at mem
    exact fun e => map_ne_row keys (held_mem (extra := [])) mem e.symm
  rw [st, Stor.get_set_ne _ apart]
  refine from_cell sel (fun _ hf => ?_) (move_bits_cell le hb rfl ?_ ?_)
  · rw [hf, rows G.sevm.caller ⟨F, hF, same.caller.symm⟩] at allow
    exact Nat.le_zero.mp allow
  · rw [same.word]
    exact bal_cd_eq selV2T_eval keys hF s_f_cd4 s
  · rw [same.word]
    exact bal_cd_eq selV2T_eval keys hF s_f_cd36 s

theorem v22_mint_case (hF : F ∈ frames) (pc : G.pc = 0) (hcode : G.sevm.code = Impl.code)
    (fork : HistFork G.sevm.benvStat.fork) (same : SameMessage F G) (keys : v22Keys h frames)
    (s : Blanc.Sevm.selector F.sevm = 0x40c10f19) :
    balanceBits ((Devm.getStor G.pre G.sevm.currentTarget).get (balSlot h)) ≤
      balanceBits ((Devm.getStor G.post G.sevm.currentTarget).get (balSlot h)) := by
  obtain ⟨A, W, m, le, st⟩ := frame_mint_bits fork (by rw [same.sel]; exact s)
    (run_cut_of_frame pc hcode fork.stateGas_none)
  have a11 : (11 : B256) ≠ balSlot h := slot_apart selV2T_eval keys hF s_m_supply rfl rfl s
  have am : minterAllowanceSlot G.sevm.caller ≠ balSlot h := by
    have := slot_apart selV2T_eval keys hF s_m_minter rfl rfl s
    rw [same.caller]
    exact this
  rw [st, Stor.get_set_ne _ am]
  by_cases hd : balSlot (Sevm.dataWord G.sevm 4).toAdr = balSlot h
  · rw [hd] at le ⊢
    rw [Stor.get_set_self]
    rwa [Stor.get_set_ne _ a11] at le
  · rw [Stor.get_set_ne _ hd, Stor.get_set_ne _ a11]

theorem v22_burn_keep (hF : F ∈ frames) (pc : G.pc = 0) (hcode : G.sevm.code = Impl.code)
    (fork : HistFork G.sevm.benvStat.fork) (same : SameMessage F G) (keys : v22Keys h frames)
    (s : Blanc.Sevm.selector F.sevm = 0x42966c68) (other : F.sevm.caller ≠ h) :
    (Devm.getStor G.post G.sevm.currentTarget).get (balSlot h) = (Devm.getStor G.pre G.sevm.currentTarget).get (balSlot h) := by
  obtain ⟨A, W, st⟩ := frame_burn_shape fork (by rw [same.sel]; exact s) (run_cut_of_frame pc hcode fork.stateGas_none)
  have a11 : (11 : B256) ≠ balSlot h := slot_apart selV2T_eval keys hF s_b_supply rfl rfl s
  have ac : balSlot G.sevm.caller ≠ balSlot h := by
    rw [same.caller]
    exact fun e => other (bal_caller_eq selV2T_eval keys hF s_b_caller s e)
  rw [st, Stor.get_set_ne _ ac, Stor.get_set_ne _ a11]

theorem v22_auth_case (hF : F ∈ frames) (pc : G.pc = 0) (hcode : G.sevm.code = Impl.code)
    (fork : HistFork G.sevm.benvStat.fork) (lib : G.pre.getCode usdcLib = Lib.code) (same : SameMessage F G)
    (keys : v22Keys h frames) (s : Blanc.Sevm.selector F.sevm ∈ v22Auths) (signed : Blanc.Sevm.selector F.sevm ∈ signedSelectors)
    (unsigned : ¬ SignedAs h F.sevm) :
    balanceBits ((Devm.getStor G.pre G.sevm.currentTarget).get (balSlot h)) ≤
      balanceBits ((Devm.getStor G.post G.sevm.currentTarget).get (balSlot h)) := by
  obtain ⟨-, -, -, -, -, -, -, -, le, -, -, hb, st⟩ := auth_of_frame pc hcode fork lib (by rw [same.sel]; exact s)
  have sites : ∀ c ∈ v22Auths,
      (⟨.kecc (.cd (.const 0xa4)) (.kecc (.op2 .and (.cd (.const 4)) addrMaskT) (.const 0x10)), [(selV2T, c)], false⟩ : Site) ∈
        wsRoot ImplWs.implWsAnn ∧
      (⟨.kecc (.op2 .and (.cd (.const 4)) addrMaskT) (.const 9), [(selV2T, c)], false⟩ : Site) ∈ wsRoot ImplWs.implWsAnn ∧
      (⟨.kecc (.op2 .and (.cd (.const 0x24)) addrMaskT) (.const 9), [(selV2T, c)], false⟩ : Site) ∈ wsRoot ImplWs.implWsAnn := by
    decide +kernel
  obtain ⟨sFlag, sFrom, sTo⟩ := sites _ s
  have flag : authSlot (Sevm.dataWord G.sevm 4).toAdr (Sevm.dataWord G.sevm 164) ≠ balSlot h := by
    have := slot_apart selV2T_eval keys hF sFlag rfl rfl rfl
    rw [WordVersion.flag_eval] at this
    rw [same.word, same.word]
    exact this
  have notSigner : (Sevm.dataWord G.sevm 4).toAdr ≠ h := by
    rw [same.word]
    exact fun e => unsigned ⟨signed, e⟩
  have cell := move_bits_cell (h := h) le hb st (by
      rw [same.word]; exact bal_cd_eq selV2T_eval keys hF sFrom rfl) (by
      rw [same.word]; exact bal_cd_eq selV2T_eval keys hF sTo rfl)
  have ge := cell.ge notSigner
  have mark : (markStor (Devm.getStor G.pre G.sevm.currentTarget) (Sevm.dataWord G.sevm 4).toAdr
      (Sevm.dataWord G.sevm 164)).get (balSlot h) = (Devm.getStor G.pre G.sevm.currentTarget).get (balSlot h) :=
    Stor.get_set_ne _ flag _
  rwa [mark] at ge

/-- The balance sites' selectors. -/
def v22BalSelectors : List B256 :=
  [0x42966c68, 0xa9059cbb, 0x23b872dd, 0x40c10f19, 0xf9f92be4, 0x1a895266] ++ v22Auths ++ usdcInitializers

theorem v22_balRows : (mappingSites 9 (wsRoot ImplWs.implWsAnn)).all (hasSel selV2T v22BalSelectors) = true := by
  decide +kernel

/-- **One frame of V2_2: the rows stay empty, and only the holder's own `transfer` or `transferFrom` lowers its bits.** -/
theorem v22_frame_law (hF : F ∈ frames) (pc : G.pc = 0) (hcode : G.sevm.code = Impl.code)
    (fork : HistFork G.sevm.benvStat.fork) (target : G.sevm.currentTarget = T)
    (hasCode : (G.pre.getCode T).toList ≠ []) (lib : G.pre.getCode usdcLib = Lib.code)
    (env : Env.root G.sevm = Env.root F.sevm) (same : SameMessage F G)
    (notRescue : Blanc.Sevm.selector F.sevm ≠ rescueSelector)
    (notInit : Blanc.Sevm.selector F.sevm ∉ usdcInitializers)
    (own : F.sevm.caller = h → CurveCoins.PoolCoinSel (Blanc.Sevm.selector F.sevm))
    (unsigned : ¬ SignedAs h F.sevm) (keys : v22Keys h frames)
    (rows : RowsEmpty h frames (Devm.getStor G.pre T)) :
    RowsEmpty h frames (Devm.getStor G.post T) ∧
      balanceBits ((Devm.getStor G.pre T).get (balSlot h)) + ownCredit h G.sevm ≤
        balanceBits ((Devm.getStor G.post T).get (balSlot h)) + ownDebit h G.sevm := by
  subst target
  have C : CertFrame G Impl.code G.sevm.currentTarget :=
    v22_certFrame pc hcode fork.stateGas_none rfl hasCode lib (by rw [same.sel]; exact notRescue)
  refine ⟨rows_after_of C Impl.cert_check impl_wsCert (t := selV2_2) rfl implV2_2_allowSitesOk v22_callers
    (by decide +kernel) (by decide +kernel) hF env same notInit own unsigned keys rows, ?_⟩
  by_cases s1 : Blanc.Sevm.selector F.sevm = 0xa9059cbb
  · exact v22_transfer_case hF pc hcode fork same keys s1
  by_cases s2 : Blanc.Sevm.selector F.sevm = 0x23b872dd
  · exact v22_from_case hF pc hcode fork same keys s2 rows
  have credit0 : Blanc.Sevm.selector G.sevm ≠ 0x23b872dd := by rw [same.sel]; exact s2
  refine keep_read ?_ credit0
  by_cases s3 : Blanc.Sevm.selector F.sevm = 0x40c10f19
  · exact v22_mint_case hF pc hcode fork same keys s3
  by_cases s4 : Blanc.Sevm.selector F.sevm ∈ v22Auths
  · exact v22_auth_case hF pc hcode fork lib same keys s4
      ((by decide : ∀ c ∈ v22Auths, c ∈ signedSelectors) _ s4) unsigned
  by_cases s5 : Blanc.Sevm.selector F.sevm = 0xf9f92be4
  · exact le_of_eq (frame_blacklist_bits fork (by rw [same.sel]; exact s5)
      (run_cut_of_frame pc hcode fork.stateGas_none) _).symm
  by_cases s6 : Blanc.Sevm.selector F.sevm = 0x1a895266
  · exact le_of_eq (frame_unBlacklist_bits fork (by rw [same.sel]; exact s6)
      (run_cut_of_frame pc hcode fork.stateGas_none) _).symm
  by_cases s7 : Blanc.Sevm.selector F.sevm = 0x42966c68
  · have other : F.sevm.caller ≠ h := fun c => by
      rcases own c with p | p | p <;> rw [p] at s7 <;> exact absurd s7 (by decide)
    rw [v22_burn_keep hF pc hcode fork same keys s7 other]
  have sG : selV2T.eval (Env.root G.sevm) = Blanc.Sevm.selector F.sevm := by rw [selV2T_eval, same.sel]
  have keep := frame_cell_keep C Impl.cert_check impl_wsCert (selT := selV2T) (R := v22BalSelectors)
    (k := balSlot h) rfl v22_balRows (by
      rw [sG]
      simp only [v22BalSelectors, List.mem_cons, List.mem_append, List.not_mem_nil, or_false, not_or]
      exact ⟨⟨⟨s7, s1, s2, s3, s5, s6⟩, s4⟩, notInit⟩)
    (fun s hs hg hk none => by
      rw [env] at hg ⊢
      exact slot_ne_of_keys keys hF hs hg hk none)
  rw [keep]

/-- **FiatTokenV2_2's law at a proxy frame**, on balance bits: every selector but the rescue selector and the initializers. -/
theorem v22_entry_law (keys : UsdcKeysFresh h frames)
    (hF : F ∈ frames) (pc : F.pc = 0) (hcode : F.sevm.code = Proxy.code)
    (fork : HistFork F.sevm.benvStat.fork) (target : F.sevm.currentTarget = T)
    (hasCode : (F.pre.getCode T).toList ≠ []) (notAdmin : F.sevm.caller ≠ adminOf F.pre.state T)
    (version : F.pre.getCode (F.pre.getStorVal T implSlot).toAdr = Impl.code)
    (lib : F.pre.getCode usdcLib = Lib.code)
    (notPrecompile : ¬ F.sevm.benvStat.rules.isPrecomp (F.pre.getStorVal T implSlot).toAdr)
    (hsize : F.sevm.data.length < 2 ^ 256)
    (notRescue : Blanc.Sevm.selector F.sevm ≠ rescueSelector)
    (notInit : Blanc.Sevm.selector F.sevm ∉ usdcInitializers)
    (own : F.sevm.caller = h → CurveCoins.PoolCoinSel (Blanc.Sevm.selector F.sevm))
    (unsigned : ¬ SignedAs h F.sevm)
    (rows : RowsView h frames (ledgerView (wordsAt T F.pre.state))) :
    RowsView h frames (ledgerView (wordsAt T F.post.state)) ∧
      heldAt T h F (ledgerView (wordsAt T F.pre.state)) + ownCredit h F.sevm ≤
        heldAt T h F (ledgerView (wordsAt T F.post.state)) + ownDebit h F.sevm := by
  have v22 : V22At T F := version
  rw [heldAt_bits v22 keys.bal_ne_impl keys.bal_ne_admin, heldAt_bits v22 keys.bal_ne_impl keys.bal_ne_admin,
    rowsView_iff keys]
  rw [rowsView_iff keys] at rows
  exact proxy_law balanceBits pc hcode fork target hasCode notAdmin version (by decide +kernel) notPrecompile hsize
    (fun G gpc gcode gfork gtarget ghas gkeep env same _ grows =>
      v22_frame_law hF gpc gcode gfork gtarget ghas
        ((gkeep usdcLib (by rw [lib]; exact lib_toList_ne_nil)).trans lib) env same notRescue notInit own unsigned
        keys.v2_2 grows)
    rows

/-- **The family theorem**: the entry law across FiatToken's versions, read by the code the implementation word finds, at a
frame the certificate restrains. The rescue selector and the initializers are outside it. -/
theorem usdc_entry_law (keys : UsdcKeysFresh h frames)
    (hF : F ∈ frames) (pc : F.pc = 0) (hcode : F.sevm.code = Proxy.code)
    (fork : HistFork F.sevm.benvStat.fork) (target : F.sevm.currentTarget = T)
    (hasCode : (F.pre.getCode T).toList ≠ []) (notAdmin : F.sevm.caller ≠ adminOf F.pre.state T)
    (certified : UsdcCertified F.pre T)
    (hsize : F.sevm.data.length < 2 ^ 256)
    (notRescue : Blanc.Sevm.selector F.sevm ≠ rescueSelector)
    (notInit : Blanc.Sevm.selector F.sevm ∉ usdcInitializers)
    (own : F.sevm.caller = h → CurveCoins.PoolCoinSel (Blanc.Sevm.selector F.sevm))
    (unsigned : ¬ SignedAs h F.sevm)
    (rows : RowsView h frames (ledgerView (wordsAt T F.pre.state))) :
    RowsView h frames (ledgerView (wordsAt T F.post.state)) ∧
      heldAt T h F (ledgerView (wordsAt T F.pre.state)) + ownCredit h F.sevm ≤
        heldAt T h F (ledgerView (wordsAt T F.post.state)) + ownDebit h F.sevm := by
  obtain ⟨version, lib, notPrecompile⟩ := certified
  have np := notPrecompile F.sevm.benvStat.fork
  rcases version with c | c | c
  · exact v2.entry_law keys keys.v2 (by decide +kernel) hF pc hcode fork target hasCode notAdmin c np hsize notRescue
      notInit own unsigned rows
  · exact v2_1.entry_law keys keys.v2_1 (by decide +kernel) hF pc hcode fork target hasCode notAdmin c np hsize notRescue
      notInit own unsigned rows
  · exact v22_entry_law keys hF pc hcode fork target hasCode notAdmin c (lib c) np hsize notRescue notInit own unsigned rows

end Law

end Blanc.Lift.Usdc
