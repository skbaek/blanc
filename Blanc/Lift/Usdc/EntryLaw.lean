import Blanc.Lift.CoinKeys
import Blanc.Lift.ChainStatic
import Blanc.Lift.Usdc.EntryQuiet
import Blanc.Lift.Usdc.EntryLawProxy
import Blanc.Lift.Usdc.EntryLawV2Walks
import Blanc.Lift.Usdc.AllowLocality
import Blanc.Lift.Usdc.ImplWs

/-!
# USDC's entry laws: what the word-reading versions share

`SignedAs` names every message that claims another account's signature, the one definition `noSignature` reads. The
ledger lemmas read a frame's storage equation at the holder's entry: `transfer_ledger`, `from_ledger`, `mint_ledger`,
`auth_ledger`. FiatTokenV2 and V2_1 have the same slots and the same equations, so these state both.
-/

namespace Blanc.Lift.Usdc

open Jaune Blanc Blanc.Lift Blanc.Lift.WriteSite Blanc.ExecutionTrace

/-- The messages that claim the signature of calldata word 4: `permit` (both forms), the three
`*AllowanceWithAuthorization`, `transferWithAuthorization` and `receiveWithAuthorization` (both forms). `cancelAuthorization`
moves no entry and no row, so it is not here. -/
def signedSelectors : List B256 :=
  [0xd505accf, 0x9fd5a6cf, 0xe1560fd3, 0xc237108f, 0xb0086095, 0xe3ee160e, 0xcf092995, 0xef55bec6, 0x88b7ab63]

/-- **The frame's message claims `h`'s signature.** The one definition `noSignature` reads. -/
def SignedAs (h : Adr) (e : Sevm) : Prop :=
  Blanc.Sevm.selector e ∈ signedSelectors ∧ (Sevm.dataWord e 4).toAdr = h

/-- The holder's tracked rows are empty. -/
def RowsEmpty (h : Adr) (frames : List Exec.Frame) (σ : Stor) : Prop :=
  ∀ g, CallerOf frames g → σ.get (allowSlot h g) = 0

theorem selV2T_eval : SelEval selV2T := fun e => by
  have shift : (0xe0 : B256).toNat = 224 := by decide
  change Sevm.dataWord e 0 >>> (0xe0 : B256).toNat = Sevm.dataWord e 0 >>> 224
  rw [shift]

/-- The certified sites of the three versions. -/
abbrev usdcSites : List Site := wsRoot ImplV2Ws.implWsAnn ++ wsRoot ImplV2_1Ws.implWsAnn ++ wsRoot ImplWs.implWsAnn

/-- **Hash freshness at USDC** (HASH-T): `CoinKeysFresh` over the three versions' sites, and the proxy's two slots. -/
def UsdcKeysFresh (h : Adr) (frames : List Exec.Frame) : Prop :=
  CoinKeysFreshWith [.raw implSlot, .raw adminSlot] usdcSites 9 10 h frames

section UsdcKeys

variable {h : Adr} {frames : List Exec.Frame}

theorem UsdcKeysFresh.v2 (keys : UsdcKeysFresh h frames) :
    CoinKeysFresh (wsRoot ImplV2Ws.implWsAnn) 9 10 h frames :=
  CoinKeysFreshWith.restrict keys fun _ hs => List.mem_append_left _ (List.mem_append_left _ hs)

theorem UsdcKeysFresh.v2_1 (keys : UsdcKeysFresh h frames) :
    CoinKeysFresh (wsRoot ImplV2_1Ws.implWsAnn) 9 10 h frames :=
  CoinKeysFreshWith.restrict keys fun _ hs => List.mem_append_left _ (List.mem_append_right _ hs)

theorem UsdcKeysFresh.v2_2 (keys : UsdcKeysFresh h frames) :
    CoinKeysFresh (wsRoot ImplWs.implWsAnn) 9 10 h frames :=
  CoinKeysFreshWith.restrict keys fun _ hs => List.mem_append_right _ hs

theorem UsdcKeysFresh.bal_ne_impl (keys : UsdcKeysFresh h frames) : balSlot h ≠ implSlot :=
  map_ne_raw keys (held_mem) (List.mem_append_left _ List.mem_cons_self)

theorem UsdcKeysFresh.bal_ne_admin (keys : UsdcKeysFresh h frames) : balSlot h ≠ adminSlot :=
  map_ne_raw keys (held_mem) (List.mem_append_left _ (List.mem_cons_of_mem _ List.mem_cons_self))

theorem UsdcKeysFresh.row_ne_impl (keys : UsdcKeysFresh h frames) {g : Adr} (hg : CallerOf frames g) :
    allowSlot h g ≠ implSlot := by
  obtain ⟨G, hG, rfl⟩ := hg
  exact fun e => raw_ne_row keys (List.mem_append_left _ List.mem_cons_self) (frame_row_mem hG) e.symm

theorem UsdcKeysFresh.row_ne_admin (keys : UsdcKeysFresh h frames) {g : Adr} (hg : CallerOf frames g) :
    allowSlot h g ≠ adminSlot := by
  obtain ⟨G, hG, rfl⟩ := hg
  exact fun e => raw_ne_row keys (List.mem_append_left _ (List.mem_cons_of_mem _ List.mem_cons_self))
    (frame_row_mem hG) e.symm

end UsdcKeys

/-- The rows as the chain reads them. -/
def RowsView (h : Adr) (frames : List Exec.Frame) (w : StorWords) : Prop :=
  ∀ g, CallerOf frames g → w (allowSlot h g) = 0

theorem rowsView_iff {h : Adr} {frames : List Exec.Frame} (keys : UsdcKeysFresh h frames) (T : Adr) (d : State) :
    RowsView h frames (ledgerView (wordsAt T d)) ↔ RowsEmpty h frames (d.getStor T) := by
  refine forall_congr' fun g => forall_congr' fun hg => ?_
  have e : ledgerView (wordsAt T d) (allowSlot h g) = (d.getStor T).get (allowSlot h g) := by
    unfold ledgerView
    exact ite_eq_right fun c => c.elim (fun x => (keys.row_ne_impl hg x).elim) fun x => (keys.row_ne_admin hg x).elim
  rw [e]

/-- A frame not reading bits reads the word, through the view. -/
theorem heldAt_word {T h : Adr} {F : Exec.Frame} (notV22 : ¬ V22At T F) (hi : balSlot h ≠ implSlot)
    (ha : balSlot h ≠ adminSlot) (w : StorWords) :
    heldAt T h F (ledgerView w) = (w (balSlot h)).toNat := by
  unfold heldAt
  rw [ite_eq_right fun c => (notV22 c).elim, ledgerView_bal hi ha]

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

theorem SameMessage.credit {F G : Exec.Frame} (s : SameMessage F G) (h : Adr) :
    ownCredit h G.sevm = ownCredit h F.sevm := by
  unfold ownCredit
  rw [s.caller, s.sel, s.word, s.word, s.word]

theorem SameMessage.debit {F G : Exec.Frame} (s : SameMessage F G) (h : Adr) :
    ownDebit h G.sevm = ownDebit h F.sevm := by
  unfold ownDebit
  rw [s.caller, s.sel, s.word, s.word, s.word]

/-- **A word-reading version's implementation law is its proxy frame's.** -/
theorem proxy_law {T h : Adr} {frames : List Exec.Frame} {F : Exec.Frame} {C : ByteArray} (pc : F.pc = 0)
    (code : F.sevm.code = Proxy.code) (fork : HistFork F.sevm.benvStat.fork) (target : F.sevm.currentTarget = T)
    (hasCode : (F.pre.getCode T).toList ≠ []) (notAdmin : F.sevm.caller ≠ adminOf F.pre.state T)
    (version : F.pre.getCode (F.pre.getStorVal T implSlot).toAdr = C) (notDelegation : ¬ isValidDelegation C)
    (notPrecompile : ¬ F.sevm.benvStat.rules.isPrecomp (F.pre.getStorVal T implSlot).toAdr)
    (hsize : F.sevm.data.length < 2 ^ 256)
    (law : ∀ G : Exec.Frame, G.pc = 0 → G.sevm.code = C → HistFork G.sevm.benvStat.fork →
      G.sevm.currentTarget = T → (G.pre.getCode T).toList ≠ [] → Env.root G.sevm = Env.root F.sevm →
      SameMessage F G → Mem.Wf G.pre.memory →
      RowsEmpty h frames (Devm.getStor G.pre T) →
      RowsEmpty h frames (Devm.getStor G.post T) ∧
        ((Devm.getStor G.pre T).get (balSlot h)).toNat + ownCredit h G.sevm ≤
          ((Devm.getStor G.post T).get (balSlot h)).toNat + ownDebit h G.sevm)
    (rows : RowsEmpty h frames (Devm.getStor F.pre T)) :
    RowsEmpty h frames (Devm.getStor F.post T) ∧
      ((Devm.getStor F.pre T).get (balSlot h)).toNat + ownCredit h F.sevm ≤
        ((Devm.getStor F.post T).get (balSlot h)).toNat + ownDebit h F.sevm := by
  obtain ⟨fpc, sevm, pre, out, run, committed⟩ := F
  dsimp only at pc code fork target hasCode notAdmin version notPrecompile hsize law rows ⊢
  subst pc
  subst target
  cases out with
  | error e => simp only [Execution.commits, Bool.false_eq_true] at committed
  | ok post =>
    subst version
    obtain ⟨G, child⟩ := proxy_entry_child run code fork.stateGas_none fork.bal_none hasCode notAdmin notDelegation
      notPrecompile hsize
    have same : SameMessage ⟨0, sevm, pre, .ok post, run, committed⟩ G := ⟨child.caller, child.data⟩
    have forkG : HistFork G.sevm.benvStat.fork := by rw [child.stat]; exact fork
    have rowsG : RowsEmpty h frames (Devm.getStor G.pre sevm.currentTarget) := by
      rw [child.preStor]
      exact rows
    have result := law G child.pc child.code forkG child.target (by
      have e := child.codeLib sevm.currentTarget hasCode
      rw [e]
      exact hasCode) child.env same child.wf rowsG
    rw [same.credit, same.debit, child.preStor, ← child.postStor] at result
    exact result

section Ledger

open ImplV2 (moveStor)

variable {σ σ' : Stor} {a d h : Adr} {v : B256}

/-- What a move does to the holder's entry, by whether it is the source and the recipient. -/
theorem move_cell (le : v.toNat ≤ (σ.get (balSlot a)).toNat)
    (nof : v.toNat + ((σ.set (balSlot a) (σ.get (balSlot a) - v)).get (balSlot d)).toNat < 2 ^ 256)
    (ea : balSlot a = balSlot h → a = h) (ed : balSlot d = balSlot h → d = h) :
    (a ≠ h → d ≠ h → ((moveStor σ a d v).get (balSlot h)).toNat = (σ.get (balSlot h)).toNat) ∧
    (a ≠ h → d = h → (σ.get (balSlot h)).toNat + v.toNat = ((moveStor σ a d v).get (balSlot h)).toNat) ∧
    (a = h → d ≠ h → ((moveStor σ a d v).get (balSlot h)).toNat + v.toNat = (σ.get (balSlot h)).toNat) ∧
    (a = h → d = h → ((moveStor σ a d v).get (balSlot h)).toNat = (σ.get (balSlot h)).toNat) := by
  change v.toNat ≤ (σ.get (ImplV2.balSlot a)).toNat at le
  change v.toNat + ((σ.set (ImplV2.balSlot a) (σ.get (ImplV2.balSlot a) - v)).get (ImplV2.balSlot d)).toNat < 2 ^ 256 at nof
  change ImplV2.balSlot a = ImplV2.balSlot h → a = h at ea
  change ImplV2.balSlot d = ImplV2.balSlot h → d = h at ed
  change ((a ≠ h → d ≠ h → ((moveStor σ a d v).get (ImplV2.balSlot h)).toNat = (σ.get (ImplV2.balSlot h)).toNat) ∧
    (a ≠ h → d = h → (σ.get (ImplV2.balSlot h)).toNat + v.toNat = ((moveStor σ a d v).get (ImplV2.balSlot h)).toNat) ∧
    (a = h → d ≠ h → ((moveStor σ a d v).get (ImplV2.balSlot h)).toNat + v.toNat = (σ.get (ImplV2.balSlot h)).toNat) ∧
    (a = h → d = h → ((moveStor σ a d v).get (ImplV2.balSlot h)).toNat = (σ.get (ImplV2.balSlot h)).toNat))
  unfold moveStor
  refine ⟨fun ha hd => ?_, fun ha hd => ?_, fun ha hd => ?_, fun ha hd => ?_⟩
  · rw [Stor.get_set_ne _ (fun e => hd (ed e)), Stor.get_set_ne _ (fun e => ha (ea e))]
  · subst hd
    have ne : ImplV2.balSlot a ≠ ImplV2.balSlot d := fun e => ha (ea e)
    rw [Stor.get_set_self, Stor.get_set_ne _ ne] at *
    rw [B256.toNat_add_eq_of_nof _ _ nof]
    omega
  · subst ha
    rw [Stor.get_set_ne _ (fun e => hd (ed e)), Stor.get_set_self, WriteSite.B256.toNat_sub_of_le le]
    omega
  · subst ha
    subst hd
    rw [Stor.get_set_self] at nof
    rw [Stor.get_set_self, Stor.get_set_self, B256.toNat_add_eq_of_nof _ _ nof, WriteSite.B256.toNat_sub_of_le le]
    omega

/-- **`transfer`'s frame at the holder's entry.** -/
theorem transfer_ledger {e : Sevm} (sel : Blanc.Sevm.selector e = 0xa9059cbb)
    (le : (Sevm.dataWord e 36).toNat ≤ (σ.get (balSlot e.caller)).toNat)
    (nof : (Sevm.dataWord e 36).toNat + ((σ.set (balSlot e.caller) (σ.get (balSlot e.caller) - Sevm.dataWord e 36)).get
      (balSlot (Sevm.dataWord e 4).toAdr)).toNat < 2 ^ 256)
    (st : σ' = moveStor σ e.caller (Sevm.dataWord e 4).toAdr (Sevm.dataWord e 36))
    (ea : balSlot e.caller = balSlot h → e.caller = h)
    (ed : balSlot (Sevm.dataWord e 4).toAdr = balSlot h → (Sevm.dataWord e 4).toAdr = h) :
    (σ.get (balSlot h)).toNat + ownCredit h e ≤ (σ'.get (balSlot h)).toNat + ownDebit h e := by
  subst st
  obtain ⟨c1, c2, c3, c4⟩ := move_cell (h := h) le nof ea ed
  have credit : ownCredit h e = 0 := ite_eq_right fun c => absurd (c.2.1.symm.trans sel) (by decide)
  rw [credit]
  by_cases hc : e.caller = h <;> by_cases hd : (Sevm.dataWord e 4).toAdr = h
  · have := c4 hc hd
    omega
  · have debit : ownDebit h e = (Sevm.dataWord e 36).toNat := by
      simp only [ownDebit, ne_eq, hc, not_true_eq_false, ↓reduceIte, sel, hd, not_false_eq_true, and_self]
    have := c3 hc hd
    omega
  · have := c2 hc hd
    omega
  · have := c1 hc hd
    omega

/-- **`transferFrom`'s frame at the holder's entry**, the holder's tracked rows empty. -/
theorem from_ledger {e : Sevm} (sel : Blanc.Sevm.selector e = 0x23b872dd)
    (allow : (Sevm.dataWord e 68).toNat ≤ (σ.get (allowSlot (Sevm.dataWord e 4).toAdr e.caller)).toNat)
    (le : (Sevm.dataWord e 68).toNat ≤ (σ.get (balSlot (Sevm.dataWord e 4).toAdr)).toNat)
    (nof : (Sevm.dataWord e 68).toNat + ((σ.set (balSlot (Sevm.dataWord e 4).toAdr)
      (σ.get (balSlot (Sevm.dataWord e 4).toAdr) - Sevm.dataWord e 68)).get
        (balSlot (Sevm.dataWord e 36).toAdr)).toNat < 2 ^ 256)
    {x : B256} (st : σ' = (moveStor σ (Sevm.dataWord e 4).toAdr (Sevm.dataWord e 36).toAdr (Sevm.dataWord e 68)).set
      (allowSlot (Sevm.dataWord e 4).toAdr e.caller) x)
    (ea : balSlot (Sevm.dataWord e 4).toAdr = balSlot h → (Sevm.dataWord e 4).toAdr = h)
    (ed : balSlot (Sevm.dataWord e 36).toAdr = balSlot h → (Sevm.dataWord e 36).toAdr = h)
    (apart : allowSlot (Sevm.dataWord e 4).toAdr e.caller ≠ balSlot h)
    (row : σ.get (allowSlot h e.caller) = 0) :
    (σ.get (balSlot h)).toNat + ownCredit h e ≤ (σ'.get (balSlot h)).toNat + ownDebit h e := by
  subst st
  rw [Stor.get_set_ne _ apart]
  obtain ⟨c1, c2, c3, c4⟩ := move_cell (h := h) le nof ea ed
  by_cases hc : e.caller = h <;> by_cases hf : (Sevm.dataWord e 4).toAdr = h <;>
    by_cases hd : (Sevm.dataWord e 36).toAdr = h
  · have := c4 hf hd
    have credit : ownCredit h e = 0 := ite_eq_right fun c => absurd hf c.2.2.1
    omega
  · have := c3 hf hd
    have credit : ownCredit h e = 0 := ite_eq_right fun c => absurd hf c.2.2.1
    have debit : ownDebit h e = (Sevm.dataWord e 68).toNat := by
      simp only [ownDebit, ne_eq, hc, not_true_eq_false, ↓reduceIte, sel, hf, hd, not_false_eq_true, and_self,
        show (0x23b872dd : B256) ≠ 0xa9059cbb by decide, false_and, true_and]
    omega
  · have := c2 hf hd
    have credit : ownCredit h e = (Sevm.dataWord e 68).toNat := ite_eq_left ⟨hc, sel, hf, hd⟩
    omega
  · have := c1 hf hd
    have credit : ownCredit h e = 0 := ite_eq_right fun c => absurd c.2.2.2 hd
    omega
  · have zero : (Sevm.dataWord e 68).toNat = 0 := by
      rw [hf, row] at allow
      exact Nat.le_zero.mp allow
    have := c4 hf hd
    have credit : ownCredit h e = 0 := ite_eq_right fun c => absurd c.1 hc
    omega
  · have zero : (Sevm.dataWord e 68).toNat = 0 := by
      rw [hf, row] at allow
      exact Nat.le_zero.mp allow
    have := c3 hf hd
    have credit : ownCredit h e = 0 := ite_eq_right fun c => absurd c.1 hc
    omega
  · have := c2 hf hd
    have credit : ownCredit h e = 0 := ite_eq_right fun c => absurd c.1 hc
    omega
  · have := c1 hf hd
    have credit : ownCredit h e = 0 := ite_eq_right fun c => absurd c.1 hc
    omega

/-- A frame on a selector with no `ownCredit` that credits or keeps the entry. -/
theorem keep_ledger {e : Sevm} (hle : (σ.get (balSlot h)).toNat ≤ (σ'.get (balSlot h)).toNat)
    (sel : Blanc.Sevm.selector e ≠ 0x23b872dd) :
    (σ.get (balSlot h)).toNat + ownCredit h e ≤ (σ'.get (balSlot h)).toNat + ownDebit h e := by
  have credit : ownCredit h e = 0 := ite_eq_right fun c => absurd c.2.1 sel
  omega

/-- **`transferWithAuthorization`'s frame at the holder's entry**, the holder not its signer: credit only. -/
theorem auth_ge {σ₁ : Stor} {k x : B256} (hσ : σ₁ = σ.set k x)
    (le : v.toNat ≤ (σ₁.get (balSlot a)).toNat)
    (nof : v.toNat + ((σ₁.set (balSlot a) (σ₁.get (balSlot a) - v)).get (balSlot d)).toNat < 2 ^ 256)
    (st : σ' = moveStor σ₁ a d v) (apart : k ≠ balSlot h) (notSigner : a ≠ h)
    (ea : balSlot a = balSlot h → a = h) (ed : balSlot d = balSlot h → d = h) :
    (σ.get (balSlot h)).toNat ≤ (σ'.get (balSlot h)).toNat := by
  subst st
  subst hσ
  obtain ⟨c1, c2, -, -⟩ := move_cell (h := h) le nof ea ed
  have keep := Stor.get_set_ne σ apart x
  rw [keep] at c1 c2
  by_cases hd : d = h
  · have := c2 notSigner hd
    omega
  · exact le_of_eq (c1 notSigner hd).symm

/-- **`mint`'s frame at the holder's entry**: credit only. -/
theorem mint_ge {a₁ m : B256} {j : B256}
    (nof : v.toNat + ((σ.set 11 a₁).get (balSlot d)).toNat < 2 ^ 256)
    (st : σ' = ((σ.set 11 a₁).set (balSlot d) (v + (σ.set 11 a₁).get (balSlot d))).set j m)
    (apart11 : (11 : B256) ≠ balSlot h) (apartJ : j ≠ balSlot h) :
    (σ.get (balSlot h)).toNat ≤ (σ'.get (balSlot h)).toNat := by
  subst st
  rw [Stor.get_set_ne _ apartJ]
  by_cases hd : balSlot d = balSlot h
  · rw [hd] at nof ⊢
    rw [Stor.get_set_self, B256.toNat_add_eq_of_nof _ _ nof, Stor.get_set_ne _ apart11]
    omega
  · rw [Stor.get_set_ne _ hd, Stor.get_set_ne _ apart11]

end Ledger

end Blanc.Lift.Usdc
