import Blanc.Lift.Usdc.EntryLaw
import Blanc.Lift.CurveCoins.UsdcV2

/-!
# FiatTokenV2: the entry law

`frame_law`: a committed implementation frame on any selector but `rescueERC20` and the two initializers keeps the holder's
tracked rows empty, and satisfies `held pre + ownCredit ≤ held post + ownDebit`. Its premises: the holder sends only the
pool's selectors, no message claims the holder's signature, hash freshness. `mint` and a signed transfer to the holder
only credit it, by their walks. `burn` debits only its caller. Nothing else has a balance row.
-/

namespace Blanc.Lift.Usdc.EntryLawV2

open Jaune Blanc Blanc.Lift Blanc.Lift.WriteSite Blanc.ExecutionTrace ImplV2

variable {T h : Adr} {frames : List Exec.Frame}

/-- The sites. -/
abbrev sites : List Site := wsRoot ImplV2Ws.implWsAnn

/-- A frame of the code, off rescue, is a `CertFrame`. -/
theorem certFrame {G : Exec.Frame} (pc : G.pc = 0) (hcode : G.sevm.code = code)
    (hsg : G.sevm.benvStat.rules.stateGas = none) (target : G.sevm.currentTarget = T)
    (hasCode : (G.pre.getCode T).toList ≠ []) (notRescue : Blanc.Sevm.selector G.sevm ≠ rescueSelector) :
    CertFrame G code T := by
  obtain ⟨gpc, sevm, pre, out, run, committed⟩ := G
  dsimp only at pc hcode hsg target hasCode notRescue
  subst pc
  refine ⟨rfl, hcode, hsg, target, hasCode, chain_static_descendants (root := ⟨0, sevm, pre, out, run⟩) ?_ run (.refl _)⟩
  intro N chain x hat
  exact isStaticcall_eq (v2_noCall run hcode hsg notRescue N chain x hat)

/-- The selectors with a balance row: the frame laws' and `burn`, and the initializers. -/
def balSelectors : List B256 := [0x23b872dd, 0xe3ee160e, 0x40c10f19, 0xa9059cbb, 0x42966c68, 0x3357162b, 0xd608ea64]

theorem balRows_ok : (mappingSites 9 sites).all (hasSel selV2T balSelectors) = true := by decide +kernel

/-- `burn`'s one balance site, the caller's. -/
def burnSlot : Term := .kecc .caller (.const 9)

/-- The balance sites other than `burn`'s. -/
def notBurn : List B256 := [0x23b872dd, 0xe3ee160e, 0x40c10f19, 0xa9059cbb, 0x3357162b, 0xd608ea64]

theorem burnRows_ok :
    (mappingSites 9 sites).all (fun s => hasSel selV2T notBurn s || s.slot == burnSlot) = true := by decide +kernel

section Frame

variable {F G : Exec.Frame}

/-- **`burn` on another account's frame keeps the holder's entry.** -/
theorem burn_keep (hF : F ∈ frames) (C : CertFrame G code T) (env : Env.root G.sevm = Env.root F.sevm)
    (keys : CoinKeysFresh sites 9 10 h frames) (s : selV2T.eval (Env.root G.sevm) = 0x42966c68)
    (other : F.sevm.caller ≠ h) :
    (G.post.getStor T).get (balSlot h) = (G.pre.getStor T).get (balSlot h) := by
  refine frame_cellInv G C.stateGas C.hasCode _ (Inv := fun v => v = (G.pre.getStor T).get (balSlot h)) rfl ?_
  intro m member w found _ key _
  obtain ⟨site, inRoot, guards, -, cases⟩ := successfulSstore_mappingSite 9 cert_check implV2_wsCert C.pc C.code
    C.stateGas (C.chain member found) found
  rcases cases with ⟨inMap, den⟩ | ⟨known, none, keyEq⟩
  · have row := List.all_eq_true.mp burnRows_ok site inMap
    rcases Bool.or_eq_true _ _ ▸ row with top | slot
    · have hsel := hasSel_sound top rfl guards
      rw [show (Blanc.Exec.Frame.rootDeriv G).sevm = G.sevm from rfl, s] at hsel
      exact absurd hsel (by decide)
    · have eq : site.slot = burnSlot := beq_iff_eq.mp slot
      rw [eq] at den
      have keyEq := den rfl
      rw [show (Blanc.Exec.Frame.rootDeriv G).sevm = G.sevm from rfl, env] at keyEq guards
      have mem := CoinKeysFresh.site_mem (balBase := 9) (allowBase := 10) (h := h) hF inRoot guards
        (by rw [eq]; rfl)
      rw [eq] at mem
      have fresh := keys.2 _ mem _ (CoinKeysFresh.held_mem (sites := sites) (frames := frames)
        (balBase := 9) (allowBase := 10) (h := h)) (by
          have : w.key = balSlot h := key
          exact keyEq.symm.trans this)
      injection fresh with _ e
      exact absurd (Adr.toB256_inj e) other
  · refine absurd (keyEq.symm.trans key) ?_
    rw [show (Blanc.Exec.Frame.rootDeriv G).sevm = G.sevm from rfl, env]
    rw [show (Blanc.Exec.Frame.rootDeriv G).sevm = G.sevm from rfl, env] at guards
    exact slot_ne_of_keys keys hF inRoot guards known none

/-! Each case its own declaration: the walks' kernel checks and the ledger together pass one declaration's budget. -/

theorem site_t_caller : (⟨.kecc (.op2 .and .caller addrMaskT) (.const 9), [(selV2T, 0xa9059cbb)], true⟩ : Site) ∈ sites := by
  decide +kernel
theorem site_t_cd4 : (⟨.kecc (.op2 .and (.cd (.const 4)) addrMaskT) (.const 9), [(selV2T, 0xa9059cbb)], false⟩ : Site) ∈ sites := by
  decide +kernel
theorem site_f_cd4 : (⟨.kecc (.op2 .and (.cd (.const 4)) addrMaskT) (.const 9), [(selV2T, 0x23b872dd)], true⟩ : Site) ∈ sites := by
  decide +kernel
theorem site_f_cd36 : (⟨.kecc (.op2 .and (.cd (.const 0x24)) addrMaskT) (.const 9), [(selV2T, 0x23b872dd)], false⟩ : Site) ∈ sites := by
  decide +kernel
theorem site_f_row : (⟨.kecc .caller (.kecc (.op2 .and (.cd (.const 4)) addrMaskT) (.const 10)),
    [(selV2T, 0x23b872dd)], true⟩ : Site) ∈ sites := by
  decide +kernel
theorem site_m_supply : (⟨.const 0xb, [(selV2T, 0x40c10f19)], false⟩ : Site) ∈ sites := by
  decide +kernel
theorem site_m_minter : (⟨.kecc .caller (.const 13), [(selV2T, 0x40c10f19)], false⟩ : Site) ∈ sites := by
  decide +kernel
theorem site_a_flag : (⟨.kecc (.cd (.const 0xa4)) (.kecc (.op2 .and (.cd (.const 4)) addrMaskT) (.const 0x10)),
    [(selV2T, 0xe3ee160e)], false⟩ : Site) ∈ sites := by
  decide +kernel
theorem site_a_cd4 : (⟨.kecc (.op2 .and (.cd (.const 4)) addrMaskT) (.const 9), [(selV2T, 0xe3ee160e)], true⟩ : Site) ∈ sites := by
  decide +kernel
theorem site_a_cd36 : (⟨.kecc (.op2 .and (.cd (.const 0x24)) addrMaskT) (.const 9), [(selV2T, 0xe3ee160e)], false⟩ : Site) ∈ sites := by
  decide +kernel

/-- The authorization flag's site, read. -/
theorem flag_eval (e : Sevm) :
    (Term.kecc (.cd (.const 0xa4)) (.kecc (.op2 .and (.cd (.const 4)) addrMaskT) (.const 0x10))).eval (Env.root e) =
      ImplV2.authSlot (Sevm.dataWord e 4).toAdr (Sevm.dataWord e 164) := by
  change mapSlot (Sevm.dataWord e 164) (mapSlot ((Term.op2 .and (.cd (.const 4)) addrMaskT).eval (Env.root e)) 16) = _
  rw [addrMaskT_eval]
  rfl

/-- What a proxy frame's implementation child reads of its message. -/
structure SameMessage (F G : Exec.Frame) : Prop where
  caller : G.sevm.caller = F.sevm.caller
  data : G.sevm.data = F.sevm.data

theorem SameMessage.sel {F G : Exec.Frame} (h : SameMessage F G) :
    Blanc.Sevm.selector G.sevm = Blanc.Sevm.selector F.sevm := by
  unfold Blanc.Sevm.selector Sevm.dataWord
  rw [h.data]

theorem SameMessage.word {F G : Exec.Frame} (h : SameMessage F G) (i : B256) :
    Sevm.dataWord G.sevm i = Sevm.dataWord F.sevm i := by
  unfold Sevm.dataWord
  rw [h.data]

/-- The rows. -/
theorem rows_after (hF : F ∈ frames) (C : CertFrame G code G.sevm.currentTarget)
    (env : Env.root G.sevm = Env.root F.sevm) (same : SameMessage F G)
    (notInit : Blanc.Sevm.selector F.sevm ∉ [(0x3357162b : B256), 0xd608ea64])
    (own : F.sevm.caller = h → CurveCoins.PoolCoinSel (Blanc.Sevm.selector F.sevm))
    (unsigned : ¬ SignedAs h F.sevm) (keys : CoinKeysFresh sites 9 10 h frames)
    (rows : RowsEmpty h frames (Devm.getStor G.pre G.sevm.currentTarget)) :
    RowsEmpty h frames (Devm.getStor G.post G.sevm.currentTarget) := by
  refine frame_rows_zero C cert_check implV2_wsCert (t := selV2) (b := 10) (pair := h) (Tr := CallerOf frames)
    rfl implV2_allowSitesOk (by rw [env]; exact rowSep_of_keys keys hF) ?_ rows
  have ev := selV2T_eval G.sevm
  rintro (⟨hs, caller⟩ | ⟨hs, owner⟩ | hs)
  · change selV2T.eval (Env.root G.sevm) ∈ [(0x095ea7b3 : B256), 0x39509351, 0xa457c2d7] at hs
    rw [ev, same.sel] at hs
    have hc : F.sevm.caller = h := by
      have e : (Env.root G.sevm).caller = G.sevm.caller.toB256 := rfl
      rw [e, toAdr_toB256, same.caller] at caller
      exact caller
    rcases own hc with p | p | p <;> rw [p] at hs <;> exact absurd hs (by decide)
  · change selV2T.eval (Env.root G.sevm) ∈ [(0xd505accf : B256), 0xe1560fd3, 0xc237108f, 0xb0086095] at hs
    rw [ev, same.sel] at hs
    refine unsigned ⟨?_, ?_⟩
    · simp only [signedSelectors, List.mem_cons, List.not_mem_nil, or_false] at hs ⊢
      rcases hs with p | p | p | p <;> simp only [p, true_or, or_true]
    · have e : (Term.cd (.const 4)).eval (Env.root G.sevm) = Sevm.dataWord G.sevm 4 := rfl
      rw [e, same.word] at owner
      exact owner
  · change selV2T.eval (Env.root G.sevm) ∈ [(0x3357162b : B256), 0xd608ea64] at hs
    rw [ev, same.sel] at hs
    exact notInit hs

theorem transfer_case (hF : F ∈ frames) (pc : G.pc = 0) (hcode : G.sevm.code = code)
    (fork : HistFork G.sevm.benvStat.fork) (same : SameMessage F G) (wf : Mem.Wf G.pre.memory)
    (keys : CoinKeysFresh sites 9 10 h frames) (s : Blanc.Sevm.selector F.sevm = 0xa9059cbb) :
    ((Devm.getStor G.pre G.sevm.currentTarget).get (balSlot h)).toNat + ownCredit h G.sevm ≤
      ((Devm.getStor G.post G.sevm.currentTarget).get (balSlot h)).toNat + ownDebit h G.sevm := by
  have run := run_of_frame cert_check (f0 := t_0000_c0) (F := G) rfl pc hcode fork.stateGas_none
  obtain ⟨-, -, -, d4, d5, st⟩ := ImplV2.frame_transfer fork wf (by rw [same.sel]; exact s) run
  refine transfer_ledger (by rw [same.sel]; exact s) d4 d5 st ?_ ?_
  · rw [same.caller]
    exact bal_caller_eq selV2T_eval keys hF site_t_caller s
  · rw [same.word]
    exact bal_cd_eq selV2T_eval keys hF site_t_cd4 s

theorem from_case (hF : F ∈ frames) (pc : G.pc = 0) (hcode : G.sevm.code = code)
    (fork : HistFork G.sevm.benvStat.fork) (same : SameMessage F G) (wf : Mem.Wf G.pre.memory)
    (keys : CoinKeysFresh sites 9 10 h frames) (s : Blanc.Sevm.selector F.sevm = 0x23b872dd)
    (rows : RowsEmpty h frames (Devm.getStor G.pre G.sevm.currentTarget)) :
    ((Devm.getStor G.pre G.sevm.currentTarget).get (balSlot h)).toNat + ownCredit h G.sevm ≤
      ((Devm.getStor G.post G.sevm.currentTarget).get (balSlot h)).toNat + ownDebit h G.sevm := by
  have run := run_of_frame cert_check (f0 := t_0000_c0) (F := G) rfl pc hcode fork.stateGas_none
  obtain ⟨-, -, -, -, a1, d6, d7, st⟩ := ImplV2.frame_transferFrom fork wf (by rw [same.sel]; exact s) run
  refine from_ledger (by rw [same.sel]; exact s) a1 d6 d7 st ?_ ?_ ?_ ?_
  · rw [same.word]
    exact bal_cd_eq selV2T_eval keys hF site_f_cd4 s
  · rw [same.word]
    exact bal_cd_eq selV2T_eval keys hF site_f_cd36 s
  · rw [same.caller, same.word]
    have mem := site_key_mem (extra := []) (balBase := 9) (allowBase := 10) (h := h) selV2T_eval hF site_f_row rfl s
    simp only [termKey, addrMaskT_eval, cd_eval] at mem
    exact fun e => map_ne_row keys (held_mem (extra := [])) mem e.symm
  · rw [same.caller]
    exact rows _ ⟨F, hF, rfl⟩

theorem mint_case (hF : F ∈ frames) (pc : G.pc = 0) (hcode : G.sevm.code = code)
    (fork : HistFork G.sevm.benvStat.fork) (same : SameMessage F G) (wf : Mem.Wf G.pre.memory)
    (keys : CoinKeysFresh sites 9 10 h frames) (s : Blanc.Sevm.selector F.sevm = 0x40c10f19) :
    ((Devm.getStor G.pre G.sevm.currentTarget).get (balSlot h)).toNat ≤
      ((Devm.getStor G.post G.sevm.currentTarget).get (balSlot h)).toNat := by
  have run := run_of_frame cert_check (f0 := t_0000_c0) (F := G) rfl pc hcode fork.stateGas_none
  obtain ⟨m, nof, st⟩ := ImplV2.frame_mint fork wf (by rw [same.sel]; exact s) run
  refine mint_ge nof st ?_ ?_
  · exact slot_apart selV2T_eval keys hF site_m_supply rfl rfl s
  · have := slot_apart selV2T_eval keys hF site_m_minter rfl rfl s
    rw [same.caller]
    exact this

theorem auth_case (hF : F ∈ frames) (pc : G.pc = 0) (hcode : G.sevm.code = code)
    (fork : HistFork G.sevm.benvStat.fork) (same : SameMessage F G) (wf : Mem.Wf G.pre.memory)
    (keys : CoinKeysFresh sites 9 10 h frames) (s : Blanc.Sevm.selector F.sevm = 0xe3ee160e)
    (unsigned : ¬ SignedAs h F.sevm) :
    ((Devm.getStor G.pre G.sevm.currentTarget).get (balSlot h)).toNat ≤
      ((Devm.getStor G.post G.sevm.currentTarget).get (balSlot h)).toNat := by
  have run := run_of_frame cert_check (f0 := t_0000_c0) (F := G) rfl pc hcode fork.stateGas_none
  obtain ⟨x, le, nof, st⟩ := ImplV2.frame_twa fork wf (by rw [same.sel]; exact s) run
  refine auth_ge rfl le nof st ?_ ?_ ?_ ?_
  · have := slot_apart selV2T_eval keys hF site_a_flag rfl rfl s
    rw [flag_eval] at this
    rw [same.word, same.word]
    exact this
  · rw [same.word]
    intro e
    exact unsigned ⟨by rw [s]; decide, e⟩
  · rw [same.word]
    exact bal_cd_eq selV2T_eval keys hF site_a_cd4 s
  · rw [same.word]
    exact bal_cd_eq selV2T_eval keys hF site_a_cd36 s

/-- **One frame: the rows stay empty, and only the holder's own `transfer` or `transferFrom` lowers its entry.** -/
theorem frame_law (hF : F ∈ frames) (pc : G.pc = 0) (hcode : G.sevm.code = code)
    (fork : HistFork G.sevm.benvStat.fork) (target : G.sevm.currentTarget = T)
    (hasCode : (G.pre.getCode T).toList ≠ []) (env : Env.root G.sevm = Env.root F.sevm)
    (same : SameMessage F G) (wf : Mem.Wf G.pre.memory)
    (notRescue : Blanc.Sevm.selector F.sevm ≠ rescueSelector)
    (notInit : Blanc.Sevm.selector F.sevm ∉ [(0x3357162b : B256), 0xd608ea64])
    (own : F.sevm.caller = h → CurveCoins.PoolCoinSel (Blanc.Sevm.selector F.sevm))
    (unsigned : ¬ SignedAs h F.sevm) (keys : CoinKeysFresh sites 9 10 h frames)
    (rows : RowsEmpty h frames (Devm.getStor G.pre T)) :
    RowsEmpty h frames (Devm.getStor G.post T) ∧
      ((Devm.getStor G.pre T).get (balSlot h)).toNat + ownCredit h G.sevm ≤
        ((Devm.getStor G.post T).get (balSlot h)).toNat + ownDebit h G.sevm := by
  subst target
  have C : CertFrame G code G.sevm.currentTarget :=
    certFrame pc hcode fork.stateGas_none rfl hasCode (by rw [same.sel]; exact notRescue)
  refine ⟨rows_after hF C env same notInit own unsigned keys rows, ?_⟩
  by_cases s1 : Blanc.Sevm.selector F.sevm = 0xa9059cbb
  · exact transfer_case hF pc hcode fork same wf keys s1
  by_cases s2 : Blanc.Sevm.selector F.sevm = 0x23b872dd
  · exact from_case hF pc hcode fork same wf keys s2 rows
  have credit0 : Blanc.Sevm.selector G.sevm ≠ 0x23b872dd := by rw [same.sel]; exact s2
  refine keep_ledger ?_ credit0
  by_cases s3 : Blanc.Sevm.selector F.sevm = 0x40c10f19
  · exact mint_case hF pc hcode fork same wf keys s3
  by_cases s4 : Blanc.Sevm.selector F.sevm = 0xe3ee160e
  · exact auth_case hF pc hcode fork same wf keys s4 unsigned
  have sG : selV2T.eval (Env.root G.sevm) = Blanc.Sevm.selector F.sevm := by rw [selV2T_eval, same.sel]
  by_cases s5 : Blanc.Sevm.selector F.sevm = 0x42966c68
  · have other : F.sevm.caller ≠ h := fun c => by
      rcases own c with p | p | p <;> rw [p] at s5 <;> exact absurd s5 (by decide)
    exact le_of_eq (congrArg B256.toNat (burn_keep hF C env keys (sG.trans s5) other).symm)
  · have keep := frame_cell_keep C cert_check implV2_wsCert (selT := selV2T) (R := balSelectors)
      (k := balSlot h) rfl balRows_ok (by
        rw [sG]
        simp only [balSelectors, List.mem_cons, List.not_mem_nil, or_false, not_or]
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at notInit
        exact ⟨s2, s4, s3, s1, s5, notInit.1, notInit.2⟩)
      (fun s hs hg hk none => by
        rw [env] at hg ⊢
        exact slot_ne_of_keys keys hF hs hg hk none)
    exact le_of_eq (congrArg B256.toNat keep.symm)

end Frame

end Blanc.Lift.Usdc.EntryLawV2
