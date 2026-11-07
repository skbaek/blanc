import Blanc.Lift.CoinKeys
import Blanc.Lift.CurveCoins.Dai
import Blanc.Lift.PoolCoinSel
import Blanc.Lift.CurveCoins.DaiPermit
import Blanc.Lift.DaiFrames
import Blanc.Lift.LinearRuntimeSafety

/-!
# DAI: the locality of a holder's balance entry over a mid history

`dai_entry_local`: from a state with DAI's code at `T`, the settled non-static frames at `T` carry its storage,
and each one satisfies `held pre + ownCredit ≤ held post + ownDebit`. So only the holder's own `transfer` or
`transferFrom` from itself lowers the holder's entry, by at most the amount it names. No operator power
appears: a ward's `mint` only credits, and `burn` has no ward path.

Its premises: `PoolAuthorityEmpty` (the holder's allowance is empty at the cut, no settled `permit` names the
holder, and the holder sends only the selectors `OwnSel` allows) and `CoinKeysFresh`.

* Rows: the certificate alone, through `frame_rows_zero`.
* An entry under a selector with no balance row: the certificate, through `frame_cell_keep`.
* An entry under a selector with a balance row: the frame laws of `DaiFrames`.
-/

namespace Blanc.Lift.CurveCoins.Dai

open Jaune Blanc Blanc.Lift Blanc.Lift.Dai Blanc.Lift.WriteSite Blanc.ExecutionTrace

/-! ## What the holder's authority is -/

/-- **A message that claims the holder's signature**: `permit` naming the holder, syntactically. The code
checks the signature; a committed frame passed that check. -/
def SignedAs (h : Adr) (e : Sevm) : Prop :=
  Blanc.Sevm.selector e = 0x8fcbaf0c ∧ (Sevm.dataWord e 4).toAdr = h

/-- A frame's logs hold `Approval` with the holder as owner, at `T`. -/
def LogsApprovalAs (T h : Adr) (F : Exec.Frame) : Prop :=
  ∃ l ∈ F.post.logs, l.address = T ∧ l.topics.take 2 = [approvalTopic, h.toB256]

/-- DAI's dispatcher word. -/
def selTerm : Term := .op2 .shr (.const 0xe0) (.cd (.const 0))

/-- The allowance writers of DAI's table: `approve` is caller-keyed, `permit` owner-keyed. -/
def rowTable : SelTable := ⟨selTerm, [0x095ea7b3], [0x8fcbaf0c], []⟩

theorem rowTable_ok : (wsRoot DaiWs.implWsAnn).all (rowSiteOk 3 rowTable) = true := by
  decide +kernel

/-- The selectors with a balance row. -/
def balSelectors : List B256 :=
  [0xa9059cbb, 0x23b872dd, 0xb753a98c, 0xf2d5d56b, 0xbb35783b, 0x40c10f19, 0x9dc29fac]

theorem balRows_ok :
    (mappingSites 2 (wsRoot DaiWs.implWsAnn)).all (hasSel selTerm balSelectors) = true := by
  decide +kernel

theorem selTerm_eval (e : Sevm) : selTerm.eval (Env.root e) = Blanc.Sevm.selector e := by
  have shift : (0xe0 : B256).toNat = 224 := by decide
  change Sevm.dataWord e 0 >>> (0xe0 : B256).toNat = Sevm.dataWord e 0 >>> 224
  rw [shift]

theorem staticOnly : ∀ f ∈ cert.prog, f.execsSatisfy Xinst.isStaticcall = true := by
  have all : cert.prog.all (fun f => f.execsSatisfy Xinst.isStaticcall) = true := by
    decide +kernel
  exact fun f member => List.all_eq_true.mp all f member

theorem code_ne : code.size ≠ 0 := by decide +kernel

theorem code_notDelegated : code.size ≠ eoaDelegatedCodeLength := by decide +kernel

theorem runtimeSafety : InstalledRuntimeSafety code :=
  InstalledRuntimeSafety.of_linearCheck (by decide +kernel) (by decide +kernel)
    (fun h => code_notDelegated h.1)
    (fun h => code_ne (by
      show code.data.size = 0
      rw [← Array.length_toList, ← ByteArray.toList_eq_toList_data, h, List.length_nil]))

/-! ## The pure law of a move -/

section Move

variable {σ σ' : Stor} {src sp dst h u : Adr} {v : B256}

/-- The slots a move writes against the holder's entry, from the hash premise. -/
structure MoveApart (src sp dst h : Adr) : Prop where
  hsrc : balSlot src = balSlot h → src = h
  hdst : balSlot dst = balSlot h → dst = h
  hallow : src ≠ sp → allowSlot src sp ≠ balSlot h

theorem spend_get_bal (ap : MoveApart src sp dst h) (σ : Stor) (v : B256) :
    (spendStor σ src sp v).get (balSlot h) = σ.get (balSlot h) := by
  unfold spendStor
  split
  · rename_i c
    exact Stor.get_set_ne _ (ap.hallow c.1) _
  · rfl

/-- A move from someone else does not lower the entry. -/
theorem fromLaw_other (law : FromLaw σ σ' src sp dst v) (ap : MoveApart src sp dst h) (ne : src ≠ h) :
    (σ.get (balSlot h)).toNat ≤ (σ'.get (balSlot h)).toNat := by
  rw [law.stor, ← spend_get_bal ap σ v]
  exact moveStor_ge law.fits fun e => ne (ap.hsrc e.symm)

/-- A move from someone else to the holder credits it by the amount. -/
theorem fromLaw_credit (law : FromLaw σ σ' src sp dst v) (ap : MoveApart src sp dst h) (ne : src ≠ h)
    (hto : dst = h) : (σ.get (balSlot h)).toNat + v.toNat ≤ (σ'.get (balSlot h)).toNat := by
  subst hto
  have hsrc : balSlot src ≠ balSlot dst := fun e => ne (ap.hsrc e)
  have fits := law.fits
  rw [Stor.get_set_ne _ hsrc, spend_get_bal ap] at fits
  rw [law.stor]
  unfold moveStor
  have hn : (σ.get (balSlot dst)).toNat + v.toNat < 2 ^ 256 := by omega
  rw [Stor.get_set_self, Stor.get_set_ne _ hsrc, spend_get_bal ap, B256.toNat_add_eq_of_nof _ _ hn]

/-- A move from the holder lowers its entry by at most the amount. -/
theorem fromLaw_debit (law : FromLaw σ σ' src sp dst v) (ap : MoveApart src sp dst h) (from_ : src = h)
    (ne : dst ≠ h) : (σ.get (balSlot h)).toNat ≤ (σ'.get (balSlot h)).toNat + v.toNat := by
  subst from_
  have hdst : balSlot dst ≠ balSlot src := fun e => ne (ap.hdst e)
  have cov := law.covered
  rw [law.stor]
  unfold moveStor
  rw [Stor.get_set_ne _ hdst, Stor.get_set_self, spend_get_bal ap, B256.toNat_sub_of_le cov]
  omega

/-- A self-move leaves the entry. -/
theorem fromLaw_self (law : FromLaw σ σ' src sp dst v) (ap : MoveApart src sp dst h) (from_ : src = h)
    (hto : dst = h) : (σ.get (balSlot h)).toNat ≤ (σ'.get (balSlot h)).toNat := by
  subst from_
  subst hto
  have cov := law.covered
  have fits := law.fits
  rw [Stor.get_set_self, spend_get_bal ap, B256.toNat_sub_of_le cov] at fits
  rw [law.stor]
  unfold moveStor
  have hn : (σ.get (balSlot dst) - v).toNat + v.toNat < 2 ^ 256 := by
    rw [B256.toNat_sub_of_le cov]
    omega
  rw [Stor.get_set_self, Stor.get_set_self, spend_get_bal ap, B256.toNat_add_eq_of_nof _ _ hn,
    B256.toNat_sub_of_le cov]
  omega

/-- A spender other than the holder with an empty row moves nothing out of it. -/
theorem fromLaw_empty (law : FromLaw σ σ' src sp dst v) (ap : MoveApart src sp dst h) (from_ : src = h)
    (ne : sp ≠ h) (zero : σ.get (allowSlot h sp) = 0) :
    (σ.get (balSlot h)).toNat ≤ (σ'.get (balSlot h)).toNat := by
  subst from_
  by_cases hto : dst = src
  · exact fromLaw_self law ap rfl hto
  · have vz := law.allowed (Ne.symm ne) (by rw [zero]; decide)
    rw [zero] at vz
    have := fromLaw_debit law ap rfl hto
    have z : (0 : B256).toNat = 0 := rfl
    omega

/-- A burn elsewhere leaves the entry. -/
theorem burn_other (ap : MoveApart src sp dst h) (hsup : (1 : B256) ≠ balSlot h)
    (ne : balSlot src ≠ balSlot h) (σ : Stor) (v : B256) :
    (burnStor (spendStor σ src sp v) src v).get (balSlot h) = σ.get (balSlot h) := by
  unfold burnStor
  rw [Stor.get_set_ne _ hsup, Stor.get_set_ne _ ne, spend_get_bal ap]

/-- A burn of nothing from the holder leaves the entry. -/
theorem burn_zero (ap : MoveApart h sp dst h) (hsup : (1 : B256) ≠ balSlot h) (σ : Stor) {v : B256}
    (vz : v.toNat = 0) :
    (burnStor (spendStor σ h sp v) h v).get (balSlot h) = σ.get (balSlot h) := by
  have v0 : v = 0 := B256.eq_zero_of_toNat vz
  subst v0
  unfold burnStor
  rw [Stor.get_set_ne _ hsup, Stor.get_set_self, spend_get_bal ap]
  exact B256.toNat_inj _ _ (by
    rw [B256.toNat_sub_of_le (by omega)]
    omega)

/-- A mint does not lower the entry. -/
theorem mint_ge (hsup : (1 : B256) ≠ balSlot h) (hu : balSlot u = balSlot h → u = h) (σ : Stor) {v : B256}
    (fits : v.toNat + (σ.get (balSlot u)).toNat < 2 ^ 256) :
    (σ.get (balSlot h)).toNat ≤ ((mintStor σ u v).get (balSlot h)).toNat := by
  unfold mintStor
  rw [Stor.get_set_ne _ hsup]
  by_cases e : u = h
  · subst e
    have hn : (σ.get (balSlot u)).toNat + v.toNat < 2 ^ 256 := by omega
    rw [Stor.get_set_self, B256.toNat_add_eq_of_nof _ _ hn]
    omega
  · rw [Stor.get_set_ne _ (fun x => e (hu x))]

end Move

/-- `transfer`'s frame is a `FromLaw` with the caller as source and spender. -/
theorem frame_transfer_law {sevm : Sevm} {b : Devm} {S : List B256} {M : Mem} {G : Nat} {post : Devm}
    (fork : HistFork sevm.benvStat.fork) (sel : Blanc.Sevm.selector sevm = 0xa9059cbb)
    (run : SFunc.Run cert.prog sevm (St b S M G) t_0000_c0 (.halted post)) :
    FromLaw (Devm.getStor b sevm.currentTarget) (Devm.getStor post sevm.currentTarget)
      sevm.caller sevm.caller (Sevm.dataWord sevm 4).toAdr (Sevm.dataWord sevm 36) := by
  obtain ⟨d1, d2, st⟩ := frame_transfer fork sel run
  have hs : ∀ (σ : Stor) (v : B256), spendStor σ sevm.caller sevm.caller v = σ := fun σ v => by
    unfold spendStor
    rw [ite_eq_right fun hh => hh.1 rfl]
  exact ⟨d1, fun ne => absurd rfl ne, by rw [hs]; exact d2, by rw [hs]; exact st⟩

/-- `transferFrom`'s frame is a `FromLaw`. -/
theorem frame_transferFrom_law {sevm : Sevm} {b : Devm} {S : List B256} {M : Mem} {G : Nat} {post : Devm}
    (fork : HistFork sevm.benvStat.fork) (sel : Blanc.Sevm.selector sevm = 0x23b872dd)
    (run : SFunc.Run cert.prog sevm (St b S M G) t_0000_c0 (.halted post)) :
    FromLaw (Devm.getStor b sevm.currentTarget) (Devm.getStor post sevm.currentTarget)
      (Sevm.dataWord sevm 4).toAdr sevm.caller (Sevm.dataWord sevm 36).toAdr (Sevm.dataWord sevm 68) := by
  obtain ⟨d1, d0, d2, st⟩ := frame_transferFrom fork sel run
  exact ⟨d1, d0, d2, st⟩

/-! ## The hash premise, at a frame -/

section Keys

variable {h : Adr} {frames : List Exec.Frame}

/-- The list the hash premise speaks of. -/
noncomputable abbrev keyList (h : Adr) (frames : List Exec.Frame) : List CoinKey :=
  heldKeys 2 3 h frames ++ frames.flatMap fun F => frameSiteKeys (wsRoot DaiWs.implWsAnn) (Env.root F.sevm)

/-- A balance site of the frame's selector names its key. -/
theorem map_key_mem {F : Exec.Frame} (hF : F ∈ frames) {key : Term} {sel : B256} {ni : Bool}
    (hs : (⟨.kecc (.op2 .and key addrMaskT) (.const 2), [(selTerm, sel)], ni⟩ : Site) ∈ wsRoot DaiWs.implWsAnn)
    (hk : key.known = true) (hsel : Blanc.Sevm.selector F.sevm = sel) :
    CoinKey.map 2 (key.eval (Env.root F.sevm)).toAdr.toB256 ∈ keyList h frames :=
  Blanc.Lift.map_key_mem (extra := []) selTerm_eval hF hs hk hsel

/-- A row site of the frame's selector names its key. -/
theorem row_key_mem {F : Exec.Frame} (hF : F ∈ frames) {o k : Term} {sel : B256} {ni : Bool}
    (hs : (⟨.kecc (.op2 .and k addrMaskT) (.kecc (.op2 .and o addrMaskT) (.const 3)), [(selTerm, sel)], ni⟩ :
      Site) ∈ wsRoot DaiWs.implWsAnn)
    (ho : o.known = true) (hk : k.known = true) (hsel : Blanc.Sevm.selector F.sevm = sel) :
    CoinKey.row 3 (o.eval (Env.root F.sevm)).toAdr.toB256 (k.eval (Env.root F.sevm)).toAdr.toB256 ∈
      keyList h frames :=
  Blanc.Lift.row_key_mem (extra := []) selTerm_eval hF hs ho hk hsel

/-- A named balance slot equal to the holder's is the holder's. -/
theorem bal_eq (keys : CoinKeysFresh (wsRoot DaiWs.implWsAnn) 2 3 h frames) {a : Adr}
    (mem : CoinKey.map 2 a.toB256 ∈ keyList h frames) (eq : balSlot a = balSlot h) : a = h :=
  map_inj keys mem (Blanc.Lift.held_mem (extra := [])) eq

/-- A named row is apart from the holder's entry. -/
theorem allow_ne (keys : CoinKeysFresh (wsRoot DaiWs.implWsAnn) 2 3 h frames) {o s : Adr}
    (mem : CoinKey.row 3 o.toB256 s.toB256 ∈ keyList h frames) : allowSlot o s ≠ balSlot h := fun eq => by
  have := keys.2 _ mem _ (CoinKeysFresh.held_mem (sites := wsRoot DaiWs.implWsAnn) (frames := frames)
    (balBase := 2) (allowBase := 3) (h := h)) eq
  cases this

/-- The supply word is apart from the holder's entry. -/
theorem supply_ne (keys : CoinKeysFresh (wsRoot DaiWs.implWsAnn) 2 3 h frames) {F : Exec.Frame}
    (hF : F ∈ frames) {sel : B256} {ni : Bool}
    (hs : (⟨.const 1, [(selTerm, sel)], ni⟩ : Site) ∈ wsRoot DaiWs.implWsAnn)
    (hsel : Blanc.Sevm.selector F.sevm = sel) : (1 : B256) ≠ balSlot h :=
  slot_ne_of_keys keys hF hs (by
    intro g hg known
    simp only [List.mem_singleton] at hg
    subst hg
    exact hsel.symm.trans (selTerm_eval _).symm) rfl rfl

end Keys

/-! ## One frame -/

/-- A good frame's run through the certificate. -/
theorem codeFrame_run {T : Adr} {F : Exec.Frame} (good : CodeFrame T HistFork code F) :
    ∃ S M G, SFunc.Run cert.prog F.sevm (St F.pre S M G) t_0000_c0 (.halted F.post) :=
  ⟨_, _, _, run_of_frame cert_check rfl good.1 good.2.1 good.2.2.1.stateGas_none⟩

section Frame

variable {T h : Adr} {frames : List Exec.Frame}

/-- The holder's tracked rows are empty. -/
def RowsEmpty (h : Adr) (frames : List Exec.Frame) (σ : StorWords) : Prop :=
  ∀ g, CallerOf frames g → σ (allowSlot h g) = 0

theorem bal_caller (keys : CoinKeysFresh (wsRoot DaiWs.implWsAnn) 2 3 h frames) {F : Exec.Frame}
    (hF : F ∈ frames) {sel : B256} {ni : Bool}
    (hs : (⟨.kecc (.op2 .and .caller addrMaskT) (.const 2), [(selTerm, sel)], ni⟩ : Site) ∈
      wsRoot DaiWs.implWsAnn) (hsel : Blanc.Sevm.selector F.sevm = sel) :
    balSlot F.sevm.caller = balSlot h → F.sevm.caller = h := by
  have mem := map_key_mem (h := h) hF hs rfl hsel
  have e : (Term.caller.eval (Env.root F.sevm)).toAdr.toB256 = F.sevm.caller.toB256 := by
    change (F.sevm.caller.toB256).toAdr.toB256 = _
    rw [toAdr_toB256]
  rw [e] at mem
  exact bal_eq keys mem

theorem bal_cd (keys : CoinKeysFresh (wsRoot DaiWs.implWsAnn) 2 3 h frames) {F : Exec.Frame}
    (hF : F ∈ frames) {i sel : B256} {ni : Bool}
    (hs : (⟨.kecc (.op2 .and (.cd (.const i)) addrMaskT) (.const 2), [(selTerm, sel)], ni⟩ : Site) ∈
      wsRoot DaiWs.implWsAnn) (hsel : Blanc.Sevm.selector F.sevm = sel) :
    balSlot (Sevm.dataWord F.sevm i).toAdr = balSlot h → (Sevm.dataWord F.sevm i).toAdr = h := by
  have mem := map_key_mem (h := h) hF hs rfl hsel
  rw [cd_eval] at mem
  exact bal_eq keys mem

theorem allow_cd_caller (keys : CoinKeysFresh (wsRoot DaiWs.implWsAnn) 2 3 h frames) {F : Exec.Frame}
    (hF : F ∈ frames) {sel : B256} {ni : Bool}
    (hs : (⟨.kecc (.op2 .and .caller addrMaskT)
      (.kecc (.op2 .and (.cd (.const 4)) addrMaskT) (.const 3)), [(selTerm, sel)], ni⟩ : Site) ∈
      wsRoot DaiWs.implWsAnn) (hsel : Blanc.Sevm.selector F.sevm = sel) :
    allowSlot (Sevm.dataWord F.sevm 4).toAdr F.sevm.caller ≠ balSlot h := by
  have mem := row_key_mem (h := h) hF hs rfl rfl hsel
  have e : (Term.caller.eval (Env.root F.sevm)).toAdr.toB256 = F.sevm.caller.toB256 := by
    change (F.sevm.caller.toB256).toAdr.toB256 = _
    rw [toAdr_toB256]
  rw [e, cd_eval] at mem
  exact allow_ne keys mem

/-- **The rows stay empty across one frame**, from the certificate alone. -/
theorem frame_rows {F : Exec.Frame} (hF : F ∈ frames) (C : CertFrame F code T)
    (unsigned : ¬ SignedAs h F.sevm)
    (own : F.sevm.caller = h → PoolCoinSel (Blanc.Sevm.selector F.sevm))
    (keys : CoinKeysFresh (wsRoot DaiWs.implWsAnn) 2 3 h frames)
    (rows : RowsEmpty h frames (wordsAt T F.pre.state)) :
    RowsEmpty h frames (wordsAt T F.post.state) := by
  refine frame_rows_zero C cert_check dai_wsCert (t := rowTable) (b := 3) rfl rowTable_ok
    (rowSep_of_keys keys hF) ?_ rows
  rintro (⟨sel, caller⟩ | ⟨sel, named⟩ | sel)
  · have hsel : Blanc.Sevm.selector F.sevm = 0x095ea7b3 := by
      have := List.mem_singleton.mp sel
      rwa [show rowTable.selT = selTerm from rfl, selTerm_eval] at this
    have hc : F.sevm.caller = h := by
      have e : (Env.root F.sevm).caller = F.sevm.caller.toB256 := rfl
      rw [e, toAdr_toB256] at caller
      exact caller
    have ps := own hc
    rw [hsel] at ps
    rcases ps with p | p | p <;> exact absurd p (by decide)
  · have hsel : Blanc.Sevm.selector F.sevm = 0x8fcbaf0c := by
      have := List.mem_singleton.mp sel
      rwa [show rowTable.selT = selTerm from rfl, selTerm_eval] at this
    exact unsigned ⟨hsel, named⟩
  · exact absurd sel List.not_mem_nil

theorem not_poolSel {s : B256} (hs : s ≠ 0xa9059cbb ∧ s ≠ 0x23b872dd ∧ s ≠ 0x70a08231) : ¬ PoolCoinSel s := by
  rintro (p | p | p)
  · exact hs.1 p
  · exact hs.2.1 p
  · exact hs.2.2 p

theorem ownDebit_ne {e : Sevm} (hc : e.caller ≠ h) : ownDebit h e = 0 := ite_eq_left hc

theorem ownCredit_ne {e : Sevm} (hc : e.caller ≠ h) : ownCredit h e = 0 :=
  ite_eq_right fun x => hc x.1

theorem ownDebit_other {e : Sevm} (h1 : Blanc.Sevm.selector e ≠ 0xa9059cbb)
    (h2 : Blanc.Sevm.selector e ≠ 0x23b872dd) : ownDebit h e = 0 := by
  unfold ownDebit
  split
  · rfl
  · rw [ite_eq_right fun x => h1 x.1, ite_eq_right fun x => h2 x.1]

theorem ownCredit_other {e : Sevm} (h2 : Blanc.Sevm.selector e ≠ 0x23b872dd) : ownCredit h e = 0 :=
  ite_eq_right fun x => h2 x.2.1

/-- **The entry across one frame.** -/
theorem frame_held {F : Exec.Frame} (hF : F ∈ frames) (good : CodeFrame T HistFork code F)
    (target : F.sevm.currentTarget = T) (C : CertFrame F code T)
    (own : F.sevm.caller = h → PoolCoinSel (Blanc.Sevm.selector F.sevm))
    (keys : CoinKeysFresh (wsRoot DaiWs.implWsAnn) 2 3 h frames)
    (rows : RowsEmpty h frames (wordsAt T F.pre.state)) :
    ((Devm.getStor F.pre T).get (balSlot h)).toNat + ownCredit h F.sevm ≤
      ((Devm.getStor F.post T).get (balSlot h)).toNat + ownDebit h F.sevm := by
  obtain ⟨S, M, G, run⟩ := codeFrame_run good
  have fork : HistFork F.sevm.benvStat.fork := good.2.2.1
  have zero : (Devm.getStor F.pre T).get (allowSlot h F.sevm.caller) = 0 :=
    rows _ ⟨F, hF, rfl⟩
  subst target
  by_cases s1 : Blanc.Sevm.selector F.sevm = 0xa9059cbb
  · have law := frame_transfer_law fork s1 run
    have ap : MoveApart F.sevm.caller F.sevm.caller (Sevm.dataWord F.sevm 4).toAdr h :=
      ⟨bal_caller keys hF (ni := true) (by decide +kernel) s1,
        bal_cd keys hF (ni := false) (by decide +kernel) s1, fun ne => absurd rfl ne⟩
    have hcr : ownCredit h F.sevm = 0 := ownCredit_other (by rw [s1]; decide)
    rw [hcr]
    by_cases hc : F.sevm.caller = h
    · by_cases hd : (Sevm.dataWord F.sevm 4).toAdr = h
      · have := fromLaw_self law ap hc hd
        omega
      · have hdb : ownDebit h F.sevm = (Sevm.dataWord F.sevm 36).toNat := by
          unfold ownDebit
          rw [ite_eq_right (not_not.mpr hc), ite_eq_left ⟨s1, hd⟩]
        rw [hdb]
        have := fromLaw_debit law ap hc hd
        omega
    · have := fromLaw_other law ap hc
      omega
  · by_cases s2 : Blanc.Sevm.selector F.sevm = 0x23b872dd
    · have law := frame_transferFrom_law fork s2 run
      have ap : MoveApart (Sevm.dataWord F.sevm 4).toAdr F.sevm.caller (Sevm.dataWord F.sevm 36).toAdr h :=
        ⟨bal_cd keys hF (ni := true) (by decide +kernel) s2,
          bal_cd keys hF (ni := false) (by decide +kernel) s2,
          fun _ => allow_cd_caller keys hF (ni := true) (by decide +kernel) s2⟩
      by_cases hc : F.sevm.caller = h
      · by_cases hs : (Sevm.dataWord F.sevm 4).toAdr = h
        · have hcr : ownCredit h F.sevm = 0 := ite_eq_right fun x => x.2.2.1 hs
          rw [hcr]
          by_cases hd : (Sevm.dataWord F.sevm 36).toAdr = h
          · have := fromLaw_self law ap hs hd
            omega
          · have hdb : ownDebit h F.sevm = (Sevm.dataWord F.sevm 68).toNat := by
              unfold ownDebit
              rw [ite_eq_right (not_not.mpr hc), ite_eq_right (fun x => by rw [s2] at x; exact absurd x.1 (by decide)),
                ite_eq_left ⟨s2, hs, hd⟩]
            rw [hdb]
            have := fromLaw_debit law ap hs hd
            omega
        · have hdb : ownDebit h F.sevm = 0 := by
            unfold ownDebit
            rw [ite_eq_right (not_not.mpr hc), ite_eq_right (fun x => by rw [s2] at x; exact absurd x.1 (by decide)),
              ite_eq_right fun x => hs x.2.1]
          rw [hdb]
          by_cases hd : (Sevm.dataWord F.sevm 36).toAdr = h
          · have hcr : ownCredit h F.sevm = (Sevm.dataWord F.sevm 68).toNat :=
              ite_eq_left ⟨hc, s2, hs, hd⟩
            rw [hcr]
            have := fromLaw_credit law ap hs hd
            omega
          · have hcr : ownCredit h F.sevm = 0 := ite_eq_right fun x => hd x.2.2.2
            rw [hcr]
            have := fromLaw_other law ap hs
            omega
      · rw [ownDebit_ne hc, ownCredit_ne hc]
        by_cases hs : (Sevm.dataWord F.sevm 4).toAdr = h
        · have := fromLaw_empty law ap hs hc zero
          omega
        · have := fromLaw_other law ap hs
          omega
    · have hcr : ownCredit h F.sevm = 0 := ownCredit_other s2
      have hdb : ownDebit h F.sevm = 0 := ownDebit_other s1 s2
      rw [hcr, hdb]
      -- the other selectors: none of them may be the holder's own unless it only reads
      have notOwn : ∀ s : B256, Blanc.Sevm.selector F.sevm = s → s ≠ 0xa9059cbb → s ≠ 0x23b872dd →
          s ≠ 0x70a08231 → F.sevm.caller ≠ h := by
        intro s hs n1 n2 n3 hc
        have := own hc
        rw [hs] at this
        exact not_poolSel ⟨n1, n2, n3⟩ this
      by_cases s3 : Blanc.Sevm.selector F.sevm = 0xb753a98c
      · have law := frame_push fork s3 run
        have hc := notOwn _ s3 (by decide) (by decide) (by decide)
        have ap : MoveApart F.sevm.caller F.sevm.caller (Sevm.dataWord F.sevm 4).toAdr h :=
          ⟨bal_caller keys hF (ni := true) (by decide +kernel) s3,
            bal_cd keys hF (ni := false) (by decide +kernel) s3, fun ne => absurd rfl ne⟩
        have := fromLaw_other law ap hc
        omega
      · by_cases s4 : Blanc.Sevm.selector F.sevm = 0xf2d5d56b
        · have law := frame_pull fork s4 run
          have hc := notOwn _ s4 (by decide) (by decide) (by decide)
          have ap : MoveApart (Sevm.dataWord F.sevm 4).toAdr F.sevm.caller F.sevm.caller h :=
            ⟨bal_cd keys hF (ni := true) (by decide +kernel) s4,
              bal_caller keys hF (ni := false) (by decide +kernel) s4,
              fun _ => allow_cd_caller keys hF (ni := true) (by decide +kernel) s4⟩
          by_cases hs : (Sevm.dataWord F.sevm 4).toAdr = h
          · have := fromLaw_empty law ap hs hc zero
            omega
          · have := fromLaw_other law ap hs
            omega
        · by_cases s5 : Blanc.Sevm.selector F.sevm = 0xbb35783b
          · have law := frame_move fork s5 run
            have hc := notOwn _ s5 (by decide) (by decide) (by decide)
            have ap : MoveApart (Sevm.dataWord F.sevm 4).toAdr F.sevm.caller
                (Sevm.dataWord F.sevm 36).toAdr h :=
              ⟨bal_cd keys hF (ni := true) (by decide +kernel) s5,
                bal_cd keys hF (ni := false) (by decide +kernel) s5,
                fun _ => allow_cd_caller keys hF (ni := true) (by decide +kernel) s5⟩
            by_cases hs : (Sevm.dataWord F.sevm 4).toAdr = h
            · have := fromLaw_empty law ap hs hc zero
              omega
            · have := fromLaw_other law ap hs
              omega
          · by_cases s6 : Blanc.Sevm.selector F.sevm = 0x40c10f19
            · obtain ⟨fits, st⟩ := frame_mint fork s6 run
              rw [st]
              have := mint_ge (supply_ne keys hF (ni := false) (by decide +kernel) s6)
                (bal_cd keys hF (ni := false) (by decide +kernel) s6) _ fits
              omega
            · by_cases s7 : Blanc.Sevm.selector F.sevm = 0x9dc29fac
              · obtain ⟨-, allowed, st⟩ := frame_burn fork s7 run
                have hc := notOwn _ s7 (by decide) (by decide) (by decide)
                have hsup := supply_ne keys hF (ni := true) (by decide +kernel) s7
                have hu := bal_cd (i := 4) keys hF (ni := true) (by decide +kernel) s7
                have ap : MoveApart (Sevm.dataWord F.sevm 4).toAdr F.sevm.caller
                    (Sevm.dataWord F.sevm 4).toAdr h :=
                  ⟨hu, hu, fun _ => allow_cd_caller keys hF (ni := true) (by decide +kernel) s7⟩
                rw [st]
                by_cases hs : (Sevm.dataWord F.sevm 4).toAdr = h
                · have vz := allowed (fun e => hc (e.symm.trans hs))
                    (by rw [hs, zero]; decide)
                  rw [hs, zero] at vz
                  have v0 : (Sevm.dataWord F.sevm 36).toNat = 0 := by
                    have z : (0 : B256).toNat = 0 := rfl
                    omega
                  rw [hs] at ap ⊢
                  rw [burn_zero ap hsup _ v0]
                · rw [burn_other ap hsup (fun e => hs (hu e))]
              · have notRow : selTerm.eval (Env.root F.sevm) ∉ balSelectors := by
                  rw [selTerm_eval]
                  simp only [balSelectors, List.mem_cons, List.not_mem_nil, or_false, not_or]
                  exact ⟨s1, s2, s3, s4, s5, s6, s7⟩
                have keep := frame_cell_keep C cert_check dai_wsCert (selT := selTerm) (b := 2)
                  (k := balSlot h) rfl balRows_ok notRow
                  (fun _ hs hg hk none => slot_ne_of_keys keys hF hs hg hk none)
                rw [keep]

end Frame

/-! ## What a reader checks for `noSignature` -/

/-- **A committed `permit` naming the holder logs `Approval` with that owner.** -/
theorem signedAs_logs {T h : Adr} {F : Exec.Frame} (good : CodeFrame T HistFork code F)
    (target : F.sevm.currentTarget = T) (signed : SignedAs h F.sevm) : LogsApprovalAs T h F := by
  obtain ⟨S, M, G, run⟩ := codeFrame_run good
  obtain ⟨l, mem, addr, topics⟩ := frame_permit_logs good.2.2.1 signed.1 run
  refine ⟨l, mem, addr.trans target, ?_⟩
  rw [topics, signed.2]

/-! ## The history -/

/-- DAI's storage moves through its settled frames. -/
theorem dai_chain {cfg : ChainConfig} {start : Benv} {future : BlockChain} {T : Adr}
    (trace : MidHistoryTraceIn HistFork cfg start future)
    (installed : start.state.getCode T = code) :
    SettledChain T (fun _ => True) (CodeFrame T HistFork code) (fun _ => True)
      (wordsAt T start.state) (wordsAt T future.state) trace.settledFrames :=
  mid_frameChain HistFork.stateGas_none BodyStageCapabilities.historical code_ne code_notDelegated
    runtimeSafety
    (fun run _ hcode fork _ _ _ =>
      staticOnly_quiet cert_check staticOnly T _ run hcode fork.stateGas_none)
    trace installed

/-- **`noSignature` from the logs**: if no settled frame at `T` logs `Approval` with the holder as owner,
no settled frame at `T` is a `permit` naming the holder. A reader checks the logs with `eth_getLogs`. -/
theorem dai_noSignature_of_logs {cfg : ChainConfig} {start : Benv} {future : BlockChain} {T h : Adr}
    (trace : MidHistoryTraceIn HistFork cfg start future)
    (installed : start.state.getCode T = code)
    (noLog : ∀ F ∈ coinFrames T (fun _ => True) trace.settledFrames, ¬ LogsApprovalAs T h F) :
    ∀ F ∈ coinFrames T (fun _ => True) trace.settledFrames, ¬ SignedAs h F.sevm := fun F hF signed =>
  noLog F hF (signedAs_logs (((dai_chain trace installed).1 fun _ _ => trivial).good F hF)
    (mem_coinFrames.mp hF).2.1 signed)

/-- **DAI's balance locality.** From a state with DAI's code at `T`, over a mid history, the settled non-static
frames at `T` carry its storage, and each moves the holder `h`'s entry by at most what its message
names: a third party's frame never lowers it, and `h`'s own lowers it only as `transfer` or `transferFrom`
from itself, by at most the amount. The premises are `PoolAuthorityEmpty` and `CoinKeysFresh`; no operator
premise appears. -/
theorem dai_entry_local {cfg : ChainConfig} {start : Benv} {future : BlockChain} {T h : Adr}
    (trace : MidHistoryTraceIn HistFork cfg start future)
    (installed : start.state.getCode T = code)
    (authority : PoolAuthorityEmpty SignedAs allowSlot PoolCoinSel h (wordsAt T start.state)
      (coinFrames T (fun _ => True) trace.settledFrames))
    (keys : CoinKeysFresh (wsRoot DaiWs.implWsAnn) 2 3 h
      (coinFrames T (fun _ => True) trace.settledFrames)) :
    EntryLocal T (fun _ => True) (CodeFrame T HistFork code) (fun σ => (σ (balSlot h)).toNat)
      (ownDebit h) (ownCredit h) (wordsAt T start.state) (wordsAt T future.state)
      trace.settledFrames := by
  have chain := dai_chain trace installed
  refine entryLocal_of_frames (I := RowsEmpty h (coinFrames T (fun _ => True) trace.settledFrames)) chain
    (fun _ _ => trivial) authority.rowsAtCut ?_
  intro F hF good rows
  obtain ⟨-, target, -, -⟩ := mem_coinFrames.mp hF
  have C := CertFrame.of_staticOnly cert_check staticOnly HistFork.stateGas_none good target
  have own := authority.ownCalls F hF
  exact ⟨frame_rows hF C (authority.noSignature F hF) own keys rows,
    frame_held hF good target C own keys rows⟩

end Blanc.Lift.CurveCoins.Dai
