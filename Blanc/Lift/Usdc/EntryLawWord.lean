import Blanc.Lift.Usdc.EntryLaw

/-!
# The entry law of a version that reads whole words

FiatTokenV2 and V2_1 have the same slots and differ in trees. `WordVersion` is what a version supplies: its certificate,
its census of external instructions, its site tables decided by the kernel, and its frame walks in one form. `frame_law` and
`entry_law` are the law from those, so each version is an instance, not a copy.

`entry_law` covers every selector but `rescueERC20`, which the chain takes out of its frames, and the four initializers,
which `InitializerKeeps` and `InitializerRowsKeep` state.
-/

namespace Blanc.Lift.Usdc

open Jaune Blanc Blanc.Lift Blanc.Lift.WriteSite Blanc.ExecutionTrace

/-- **The initializers keep the holder's tracked rows empty**, as the chain reads them. The companion of
`InitializerKeeps`: an initializer's unknown sites speak for rows as well as entries. -/
def InitializerRowsKeep (T h : Adr) (frames settled : List Exec.Frame) : Prop :=
  ∀ F ∈ settled, F.sevm.currentTarget = T → F.sevm.isStatic = false → EntryObs T F →
    Blanc.Sevm.selector F.sevm ∈ usdcInitializers →
    RowsView h frames (ledgerView (wordsAt T F.pre.state)) → RowsView h frames (ledgerView (wordsAt T F.post.state))

/-- `burn`'s one balance site, the caller's. -/
def burnSlot : Term := .kecc .caller (.const 9)

/-- The selectors with a balance row but `burn`. -/
def moveSelectors (auths : List B256) : List B256 :=
  [0x23b872dd, 0xa9059cbb, 0x40c10f19] ++ auths ++ usdcInitializers

open ImplV2 (moveStor) in
/-- **What a word-reading version supplies.** -/
structure WordVersion where
  code : ByteArray
  cert : Cert
  ann : List WAnn
  f0 : SFunc
  checked : Cert.check code cert = true
  ws : wsCert cert ann = true
  root : cert.prog[0]? = some f0
  notV22 : code ≠ Impl.code
  notDelegation : ¬ isValidDelegation code
  noCall : ∀ {sevm : Sevm} {pre : Devm} {out : Execution} (run : Exec 0 sevm pre out), sevm.code = code →
    sevm.benvStat.rules.stateGas = none → Blanc.Sevm.selector sevm ≠ rescueSelector →
    ∀ N, Exec.Deriv.ParentPrefix ⟨0, sevm, pre, out, run⟩ N →
      ∀ x, Ninst.At N.sevm.code N.pc (.exec x) → Xinst.isStaticcall x = true
  /-- The rows. -/
  table : SelTable
  tableSel : table.selT = selV2T
  rowsOk : (wsRoot ann).all (rowSiteOk 10 table) = true
  callers : ∀ c ∈ table.callers, ¬ CurveCoins.PoolCoinSel c
  owners : ∀ c ∈ table.owners, c ∈ signedSelectors
  inits : ∀ c ∈ table.inits, c ∈ usdcInitializers
  /-- The signed moves. -/
  auths : List B256
  authSigned : ∀ c ∈ auths, c ∈ signedSelectors
  /-- The entries. -/
  burnRows : (mappingSites 9 (wsRoot ann)).all (fun s => hasSel selV2T (moveSelectors auths) s || s.slot == burnSlot) = true
  balRows : (mappingSites 9 (wsRoot ann)).all (hasSel selV2T (0x42966c68 :: moveSelectors auths)) = true
  /-- The sites the moves name. -/
  t_caller : (⟨.kecc (.op2 .and .caller addrMaskT) (.const 9), [(selV2T, 0xa9059cbb)], true⟩ : Site) ∈ wsRoot ann
  t_cd4 : (⟨.kecc (.op2 .and (.cd (.const 4)) addrMaskT) (.const 9), [(selV2T, 0xa9059cbb)], false⟩ : Site) ∈ wsRoot ann
  f_cd4 : (⟨.kecc (.op2 .and (.cd (.const 4)) addrMaskT) (.const 9), [(selV2T, 0x23b872dd)], true⟩ : Site) ∈ wsRoot ann
  f_cd36 : (⟨.kecc (.op2 .and (.cd (.const 0x24)) addrMaskT) (.const 9), [(selV2T, 0x23b872dd)], false⟩ : Site) ∈ wsRoot ann
  f_row : (⟨.kecc .caller (.kecc (.op2 .and (.cd (.const 4)) addrMaskT) (.const 10)), [(selV2T, 0x23b872dd)], true⟩ : Site) ∈
    wsRoot ann
  m_supply : (⟨.const 0xb, [(selV2T, 0x40c10f19)], false⟩ : Site) ∈ wsRoot ann
  m_minter : (⟨.kecc .caller (.const 13), [(selV2T, 0x40c10f19)], false⟩ : Site) ∈ wsRoot ann
  a_flag : ∀ c ∈ auths, (⟨.kecc (.cd (.const 0xa4)) (.kecc (.op2 .and (.cd (.const 4)) addrMaskT) (.const 0x10)),
    [(selV2T, c)], false⟩ : Site) ∈ wsRoot ann
  a_cd4 : ∀ c ∈ auths, (⟨.kecc (.op2 .and (.cd (.const 4)) addrMaskT) (.const 9), [(selV2T, c)], true⟩ : Site) ∈ wsRoot ann
  a_cd36 : ∀ c ∈ auths, (⟨.kecc (.op2 .and (.cd (.const 0x24)) addrMaskT) (.const 9), [(selV2T, c)], false⟩ : Site) ∈ wsRoot ann
  /-- The walks. -/
  frameTransfer : ∀ {sevm : Sevm} {b : Devm} {S : List B256} {M : Mem} {G : Nat} {post : Devm},
    HistFork sevm.benvStat.fork → Mem.Wf M → Blanc.Sevm.selector sevm = 0xa9059cbb →
    SFunc.Run cert.prog sevm (St b S M G) f0 (.halted post) →
    (Sevm.dataWord sevm 36).toNat ≤ ((Devm.getStor b sevm.currentTarget).get (balSlot sevm.caller)).toNat ∧
    (Sevm.dataWord sevm 36).toNat + (((Devm.getStor b sevm.currentTarget).set (balSlot sevm.caller)
      ((Devm.getStor b sevm.currentTarget).get (balSlot sevm.caller) - Sevm.dataWord sevm 36)).get
        (balSlot (Sevm.dataWord sevm 4).toAdr)).toNat < 2 ^ 256 ∧
    Devm.getStor post sevm.currentTarget =
      moveStor (Devm.getStor b sevm.currentTarget) sevm.caller (Sevm.dataWord sevm 4).toAdr (Sevm.dataWord sevm 36)
  frameFrom : ∀ {sevm : Sevm} {b : Devm} {S : List B256} {M : Mem} {G : Nat} {post : Devm},
    HistFork sevm.benvStat.fork → Mem.Wf M → Blanc.Sevm.selector sevm = 0x23b872dd →
    SFunc.Run cert.prog sevm (St b S M G) f0 (.halted post) →
    (Sevm.dataWord sevm 68).toNat ≤
      ((Devm.getStor b sevm.currentTarget).get (allowSlot (Sevm.dataWord sevm 4).toAdr sevm.caller)).toNat ∧
    (Sevm.dataWord sevm 68).toNat ≤ ((Devm.getStor b sevm.currentTarget).get (balSlot (Sevm.dataWord sevm 4).toAdr)).toNat ∧
    (Sevm.dataWord sevm 68).toNat + (((Devm.getStor b sevm.currentTarget).set (balSlot (Sevm.dataWord sevm 4).toAdr)
      ((Devm.getStor b sevm.currentTarget).get (balSlot (Sevm.dataWord sevm 4).toAdr) - Sevm.dataWord sevm 68)).get
        (balSlot (Sevm.dataWord sevm 36).toAdr)).toNat < 2 ^ 256 ∧
    ∃ x, Devm.getStor post sevm.currentTarget =
      (moveStor (Devm.getStor b sevm.currentTarget) (Sevm.dataWord sevm 4).toAdr (Sevm.dataWord sevm 36).toAdr
        (Sevm.dataWord sevm 68)).set (allowSlot (Sevm.dataWord sevm 4).toAdr sevm.caller) x
  frameMint : ∀ {sevm : Sevm} {b : Devm} {S : List B256} {M : Mem} {G : Nat} {post : Devm},
    HistFork sevm.benvStat.fork → Mem.Wf M → Blanc.Sevm.selector sevm = 0x40c10f19 →
    SFunc.Run cert.prog sevm (St b S M G) f0 (.halted post) →
    ∃ m, let σ := Stor.set (Devm.getStor b sevm.currentTarget) 11 (Sevm.dataWord sevm 36 + (Devm.getStor b sevm.currentTarget).get 11)
      (Sevm.dataWord sevm 36).toNat + (σ.get (balSlot (Sevm.dataWord sevm 4).toAdr)).toNat < 2 ^ 256 ∧
      Devm.getStor post sevm.currentTarget =
        (σ.set (balSlot (Sevm.dataWord sevm 4).toAdr)
          (Sevm.dataWord sevm 36 + σ.get (balSlot (Sevm.dataWord sevm 4).toAdr))).set (ImplV2.minterSlot sevm.caller) m
  frameAuth : ∀ {sevm : Sevm} {b : Devm} {S : List B256} {M : Mem} {G : Nat} {post : Devm},
    HistFork sevm.benvStat.fork → Mem.Wf M → Blanc.Sevm.selector sevm ∈ auths →
    SFunc.Run cert.prog sevm (St b S M G) f0 (.halted post) →
    ∃ x, let σ := Stor.set (Devm.getStor b sevm.currentTarget) (ImplV2.authSlot (Sevm.dataWord sevm 4).toAdr (Sevm.dataWord sevm 164)) x
      (Sevm.dataWord sevm 68).toNat ≤ (σ.get (balSlot (Sevm.dataWord sevm 4).toAdr)).toNat ∧
      (Sevm.dataWord sevm 68).toNat + ((σ.set (balSlot (Sevm.dataWord sevm 4).toAdr)
        (σ.get (balSlot (Sevm.dataWord sevm 4).toAdr) - Sevm.dataWord sevm 68)).get
          (balSlot (Sevm.dataWord sevm 36).toAdr)).toNat < 2 ^ 256 ∧
      Devm.getStor post sevm.currentTarget =
        moveStor σ (Sevm.dataWord sevm 4).toAdr (Sevm.dataWord sevm 36).toAdr (Sevm.dataWord sevm 68)

namespace WordVersion

variable (W : WordVersion) {T h : Adr} {frames : List Exec.Frame} {F G : Exec.Frame}

include W in
/-- A frame of the code, off rescue, is a `CertFrame`. -/
theorem certFrame (pc : G.pc = 0) (hcode : G.sevm.code = W.code)
    (hsg : G.sevm.benvStat.rules.stateGas = none) (target : G.sevm.currentTarget = T)
    (hasCode : (G.pre.getCode T).toList ≠ []) (notRescue : Blanc.Sevm.selector G.sevm ≠ rescueSelector) :
    CertFrame G W.code T := by
  obtain ⟨gpc, sevm, pre, out, run, committed⟩ := G
  dsimp only at pc hcode hsg target hasCode notRescue
  subst pc
  refine ⟨rfl, hcode, hsg, target, hasCode, chain_static_descendants (root := ⟨0, sevm, pre, out, run⟩) ?_ run (.refl _)⟩
  intro N chain x hat
  exact isStaticcall_eq (W.noCall run hcode hsg notRescue N chain x hat)

/-- **`burn` on another account's frame keeps the holder's entry.** -/
theorem burn_keep (hF : F ∈ frames) (C : CertFrame G W.code T) (env : Env.root G.sevm = Env.root F.sevm)
    (keys : CoinKeysFresh (wsRoot W.ann) 9 10 h frames) (s : selV2T.eval (Env.root G.sevm) = 0x42966c68)
    (notMove : (0x42966c68 : B256) ∉ moveSelectors W.auths) (other : F.sevm.caller ≠ h) :
    (G.post.getStor T).get (balSlot h) = (G.pre.getStor T).get (balSlot h) := by
  refine frame_cellInv G C.stateGas C.hasCode _ (Inv := fun v => v = (G.pre.getStor T).get (balSlot h)) rfl ?_
  intro m member w found _ key _
  obtain ⟨site, inRoot, guards, -, cases⟩ := successfulSstore_mappingSite 9 W.checked W.ws C.pc C.code
    C.stateGas (C.chain member found) found
  rcases cases with ⟨inMap, den⟩ | ⟨known, none, keyEq⟩
  · have row := List.all_eq_true.mp W.burnRows site inMap
    rcases Bool.or_eq_true _ _ ▸ row with top | slot
    · have hsel := hasSel_sound top rfl guards
      rw [show (Blanc.Exec.Frame.rootDeriv G).sevm = G.sevm from rfl, s] at hsel
      exact absurd hsel notMove
    · have eq : site.slot = burnSlot := beq_iff_eq.mp slot
      rw [eq] at den
      have keyEq := den rfl
      rw [show (Blanc.Exec.Frame.rootDeriv G).sevm = G.sevm from rfl, env] at keyEq guards
      have mem := CoinKeysFresh.site_mem (balBase := 9) (allowBase := 10) (h := h) hF inRoot guards
        (by rw [eq]; rfl)
      rw [eq] at mem
      have fresh := keys.2 _ mem _ (CoinKeysFresh.held_mem (sites := wsRoot W.ann) (frames := frames)
        (balBase := 9) (allowBase := 10) (h := h)) (by
          have : w.key = balSlot h := key
          exact keyEq.symm.trans this)
      injection fresh with _ e
      exact absurd (Adr.toB256_inj e) other
  · refine absurd (keyEq.symm.trans key) ?_
    rw [show (Blanc.Exec.Frame.rootDeriv G).sevm = G.sevm from rfl, env]
    rw [show (Blanc.Exec.Frame.rootDeriv G).sevm = G.sevm from rfl, env] at guards
    exact slot_ne_of_keys keys hF inRoot guards known none

/-- The authorization flag's site, read. -/
theorem flag_eval (e : Sevm) :
    (Term.kecc (.cd (.const 0xa4)) (.kecc (.op2 .and (.cd (.const 4)) addrMaskT) (.const 0x10))).eval (Env.root e) =
      ImplV2.authSlot (Sevm.dataWord e 4).toAdr (Sevm.dataWord e 164) := by
  change mapSlot (Sevm.dataWord e 164) (mapSlot ((Term.op2 .and (.cd (.const 4)) addrMaskT).eval (Env.root e)) 16) = _
  rw [addrMaskT_eval]
  rfl

/-- The rows. -/
theorem rows_after (hF : F ∈ frames) (C : CertFrame G W.code G.sevm.currentTarget)
    (env : Env.root G.sevm = Env.root F.sevm) (same : SameMessage F G)
    (notInit : Blanc.Sevm.selector F.sevm ∉ usdcInitializers)
    (own : F.sevm.caller = h → CurveCoins.PoolCoinSel (Blanc.Sevm.selector F.sevm))
    (unsigned : ¬ SignedAs h F.sevm) (keys : CoinKeysFresh (wsRoot W.ann) 9 10 h frames)
    (rows : RowsEmpty h frames (Devm.getStor G.pre G.sevm.currentTarget)) :
    RowsEmpty h frames (Devm.getStor G.post G.sevm.currentTarget) := by
  refine frame_rows_zero C W.checked W.ws (t := W.table) (b := 10) (pair := h) (Tr := CallerOf frames)
    (by rw [W.tableSel]; rfl) W.rowsOk (by rw [env]; exact rowSep_of_keys keys hF) ?_ rows
  have ev : W.table.selT.eval (Env.root G.sevm) = Blanc.Sevm.selector F.sevm := by
    rw [W.tableSel, selV2T_eval, same.sel]
  rintro (⟨hs, caller⟩ | ⟨hs, owner⟩ | hs)
  · rw [ev] at hs
    have hc : F.sevm.caller = h := by
      have e : (Env.root G.sevm).caller = G.sevm.caller.toB256 := rfl
      rw [e, toAdr_toB256, same.caller] at caller
      exact caller
    exact W.callers _ hs (own hc)
  · rw [ev] at hs
    refine unsigned ⟨W.owners _ hs, ?_⟩
    have e : (Term.cd (.const 4)).eval (Env.root G.sevm) = Sevm.dataWord G.sevm 4 := rfl
    rw [e, same.word] at owner
    exact owner
  · rw [ev] at hs
    exact notInit (W.inits _ hs)

theorem transfer_case (hF : F ∈ frames) (pc : G.pc = 0) (hcode : G.sevm.code = W.code)
    (fork : HistFork G.sevm.benvStat.fork) (same : SameMessage F G) (wf : Mem.Wf G.pre.memory)
    (keys : CoinKeysFresh (wsRoot W.ann) 9 10 h frames) (s : Blanc.Sevm.selector F.sevm = 0xa9059cbb) :
    ((Devm.getStor G.pre G.sevm.currentTarget).get (balSlot h)).toNat + ownCredit h G.sevm ≤
      ((Devm.getStor G.post G.sevm.currentTarget).get (balSlot h)).toNat + ownDebit h G.sevm := by
  have run := run_of_frame W.checked W.root pc hcode fork.stateGas_none
  obtain ⟨d4, d5, st⟩ := W.frameTransfer fork wf (by rw [same.sel]; exact s) run
  refine transfer_ledger (by rw [same.sel]; exact s) d4 d5 st ?_ ?_
  · rw [same.caller]
    exact bal_caller_eq selV2T_eval keys hF W.t_caller s
  · rw [same.word]
    exact bal_cd_eq selV2T_eval keys hF W.t_cd4 s

theorem from_case (hF : F ∈ frames) (pc : G.pc = 0) (hcode : G.sevm.code = W.code)
    (fork : HistFork G.sevm.benvStat.fork) (same : SameMessage F G) (wf : Mem.Wf G.pre.memory)
    (keys : CoinKeysFresh (wsRoot W.ann) 9 10 h frames) (s : Blanc.Sevm.selector F.sevm = 0x23b872dd)
    (rows : RowsEmpty h frames (Devm.getStor G.pre G.sevm.currentTarget)) :
    ((Devm.getStor G.pre G.sevm.currentTarget).get (balSlot h)).toNat + ownCredit h G.sevm ≤
      ((Devm.getStor G.post G.sevm.currentTarget).get (balSlot h)).toNat + ownDebit h G.sevm := by
  have run := run_of_frame W.checked W.root pc hcode fork.stateGas_none
  obtain ⟨a1, d6, d7, x, st⟩ := W.frameFrom fork wf (by rw [same.sel]; exact s) run
  refine from_ledger (by rw [same.sel]; exact s) a1 d6 d7 st ?_ ?_ ?_ ?_
  · rw [same.word]
    exact bal_cd_eq selV2T_eval keys hF W.f_cd4 s
  · rw [same.word]
    exact bal_cd_eq selV2T_eval keys hF W.f_cd36 s
  · rw [same.caller, same.word]
    have mem := site_key_mem (extra := []) (balBase := 9) (allowBase := 10) (h := h) selV2T_eval hF W.f_row rfl s
    simp only [termKey, addrMaskT_eval, cd_eval] at mem
    exact fun e => map_ne_row keys (held_mem (extra := [])) mem e.symm
  · rw [same.caller]
    exact rows _ ⟨F, hF, rfl⟩

theorem mint_case (hF : F ∈ frames) (pc : G.pc = 0) (hcode : G.sevm.code = W.code)
    (fork : HistFork G.sevm.benvStat.fork) (same : SameMessage F G) (wf : Mem.Wf G.pre.memory)
    (keys : CoinKeysFresh (wsRoot W.ann) 9 10 h frames) (s : Blanc.Sevm.selector F.sevm = 0x40c10f19) :
    ((Devm.getStor G.pre G.sevm.currentTarget).get (balSlot h)).toNat ≤
      ((Devm.getStor G.post G.sevm.currentTarget).get (balSlot h)).toNat := by
  have run := run_of_frame W.checked W.root pc hcode fork.stateGas_none
  obtain ⟨m, nof, st⟩ := W.frameMint fork wf (by rw [same.sel]; exact s) run
  refine mint_ge nof st ?_ ?_
  · exact slot_apart selV2T_eval keys hF W.m_supply rfl rfl s
  · have := slot_apart selV2T_eval keys hF W.m_minter rfl rfl s
    rw [same.caller]
    exact this

theorem auth_case (hF : F ∈ frames) (pc : G.pc = 0) (hcode : G.sevm.code = W.code)
    (fork : HistFork G.sevm.benvStat.fork) (same : SameMessage F G) (wf : Mem.Wf G.pre.memory)
    (keys : CoinKeysFresh (wsRoot W.ann) 9 10 h frames) (s : Blanc.Sevm.selector F.sevm ∈ W.auths)
    (unsigned : ¬ SignedAs h F.sevm) :
    ((Devm.getStor G.pre G.sevm.currentTarget).get (balSlot h)).toNat ≤
      ((Devm.getStor G.post G.sevm.currentTarget).get (balSlot h)).toNat := by
  have run := run_of_frame W.checked W.root pc hcode fork.stateGas_none
  obtain ⟨x, le, nof, st⟩ := W.frameAuth fork wf (by rw [same.sel]; exact s) run
  refine auth_ge rfl le nof st ?_ ?_ ?_ ?_
  · have := slot_apart selV2T_eval keys hF (W.a_flag _ s) rfl rfl rfl
    rw [flag_eval] at this
    rw [same.word, same.word]
    exact this
  · rw [same.word]
    intro e
    exact unsigned ⟨W.authSigned _ s, e⟩
  · rw [same.word]
    exact bal_cd_eq selV2T_eval keys hF (W.a_cd4 _ s) rfl
  · rw [same.word]
    exact bal_cd_eq selV2T_eval keys hF (W.a_cd36 _ s) rfl

/-- **One frame: the rows stay empty, and only the holder's own `transfer` or `transferFrom` lowers its entry.** -/
theorem frame_law (hF : F ∈ frames) (pc : G.pc = 0) (hcode : G.sevm.code = W.code)
    (fork : HistFork G.sevm.benvStat.fork) (target : G.sevm.currentTarget = T)
    (hasCode : (G.pre.getCode T).toList ≠ []) (env : Env.root G.sevm = Env.root F.sevm)
    (same : SameMessage F G) (wf : Mem.Wf G.pre.memory)
    (notBurnMove : (0x42966c68 : B256) ∉ moveSelectors W.auths)
    (notRescue : Blanc.Sevm.selector F.sevm ≠ rescueSelector)
    (notInit : Blanc.Sevm.selector F.sevm ∉ usdcInitializers)
    (own : F.sevm.caller = h → CurveCoins.PoolCoinSel (Blanc.Sevm.selector F.sevm))
    (unsigned : ¬ SignedAs h F.sevm) (keys : CoinKeysFresh (wsRoot W.ann) 9 10 h frames)
    (rows : RowsEmpty h frames (Devm.getStor G.pre T)) :
    RowsEmpty h frames (Devm.getStor G.post T) ∧
      ((Devm.getStor G.pre T).get (balSlot h)).toNat + ownCredit h G.sevm ≤
        ((Devm.getStor G.post T).get (balSlot h)).toNat + ownDebit h G.sevm := by
  subst target
  have C : CertFrame G W.code G.sevm.currentTarget :=
    W.certFrame pc hcode fork.stateGas_none rfl hasCode (by rw [same.sel]; exact notRescue)
  refine ⟨W.rows_after hF C env same notInit own unsigned keys rows, ?_⟩
  by_cases s1 : Blanc.Sevm.selector F.sevm = 0xa9059cbb
  · exact W.transfer_case hF pc hcode fork same wf keys s1
  by_cases s2 : Blanc.Sevm.selector F.sevm = 0x23b872dd
  · exact W.from_case hF pc hcode fork same wf keys s2 rows
  have credit0 : Blanc.Sevm.selector G.sevm ≠ 0x23b872dd := by rw [same.sel]; exact s2
  refine keep_ledger ?_ credit0
  by_cases s3 : Blanc.Sevm.selector F.sevm = 0x40c10f19
  · exact W.mint_case hF pc hcode fork same wf keys s3
  by_cases s4 : Blanc.Sevm.selector F.sevm ∈ W.auths
  · exact W.auth_case hF pc hcode fork same wf keys s4 unsigned
  have sG : selV2T.eval (Env.root G.sevm) = Blanc.Sevm.selector F.sevm := by rw [selV2T_eval, same.sel]
  by_cases s5 : Blanc.Sevm.selector F.sevm = 0x42966c68
  · have other : F.sevm.caller ≠ h := fun c => by
      rcases own c with p | p | p <;> rw [p] at s5 <;> exact absurd s5 (by decide)
    exact le_of_eq (congrArg B256.toNat (W.burn_keep hF C env keys (sG.trans s5) notBurnMove other).symm)
  · have keep := frame_cell_keep C W.checked W.ws (selT := selV2T) (R := 0x42966c68 :: moveSelectors W.auths)
      (k := balSlot h) rfl W.balRows (by
        rw [sG]
        simp only [moveSelectors, List.mem_cons, List.mem_append, List.not_mem_nil, or_false, not_or]
        refine ⟨s5, ⟨⟨s2, s1, s3⟩, s4⟩, notInit⟩)
      (fun s hs hg hk none => by
        rw [env] at hg ⊢
        exact slot_ne_of_keys keys hF hs hg hk none)
    exact le_of_eq (congrArg B256.toNat keep.symm)

/-- **A word-reading version's law at a proxy frame**, as the chain's `heldAt` reads it: every selector but
the rescue selector, which the chain removes, and the initializers. -/
theorem entry_law (keys : UsdcKeysFresh h frames) (siteKeys : CoinKeysFresh (wsRoot W.ann) 9 10 h frames)
    (notBurnMove : (0x42966c68 : B256) ∉ moveSelectors W.auths)
    (hF : F ∈ frames) (pc : F.pc = 0) (hcode : F.sevm.code = Proxy.code)
    (fork : HistFork F.sevm.benvStat.fork) (target : F.sevm.currentTarget = T)
    (hasCode : (F.pre.getCode T).toList ≠ []) (notAdmin : F.sevm.caller ≠ adminOf F.pre.state T)
    (version : F.pre.getCode (F.pre.getStorVal T implSlot).toAdr = W.code)
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
  have notV22 : ¬ V22At T F := fun c => by
    have e : F.pre.getCode (F.pre.getStorVal T implSlot).toAdr = Impl.code := c
    rw [version] at e
    exact W.notV22 e
  rw [heldAt_word notV22 keys.bal_ne_impl keys.bal_ne_admin, heldAt_word notV22 keys.bal_ne_impl keys.bal_ne_admin,
    rowsView_iff keys]
  rw [rowsView_iff keys] at rows
  exact proxy_law pc hcode fork target hasCode notAdmin version W.notDelegation notPrecompile hsize
    (fun G gpc gcode gfork gtarget ghas env same wf grows =>
      W.frame_law hF gpc gcode gfork gtarget ghas env same wf notBurnMove notRescue notInit own unsigned siteKeys grows)
    rows

end WordVersion

end Blanc.Lift.Usdc
