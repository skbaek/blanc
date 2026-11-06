import Blanc.Lift.BalanceLocality
import Blanc.Lift.CurveCoins.Usdt
import Blanc.Lift.CurveCoins.Sel
import Blanc.Lift.CurveCoins.UsdtQuiet
import Blanc.Lift.LinearRuntimeSafety
import Blanc.Lift.UsdtOwnerFrames

/-!
# USDT: the locality of a holder's balance entry over a mid history

`usdt_entry_local`: from a state with TetherToken's code at `T`, the settled non-static frames at `T` carry its
storage, and each one satisfies `held pre ≤ held post + usdtDebit`. So only the holder's own `transfer` lowers
the holder's entry, by at most the amount it names. No credit is claimed: a fee may reduce what arrives, and the
pool measures its credit by `balanceOf` (`frame_balanceOf_output`).

Two premises constrain Tether's owner, each named after the power:

* `NotDeprecated`: at each such frame, `deprecate` has not been used, so the frame forwards nothing and enters no
  frame (`usdt_descendants_nil`);
* `Confiscates`: no settled `destroyBlackFunds` names the holder.

The owner's other balance powers need no premise. `issue` credits only the owner, and `redeem` debits only the
owner, and both require the owner as caller. So if the owner is not the holder they miss the holder's entry, and if
it is, `ownCalls` says the holder never sends them.

The others: `PoolAuthorityEmpty` (the holder's allowance is empty at the cut, the holder sends only
`PoolCoinSel`; USDT has no signed writer), and `UsdtKeysFresh`.
-/

namespace Blanc.Lift.CurveCoins.Usdt

open Jaune Blanc Blanc.Lift Blanc.Lift.Usdt Blanc.Lift.WriteSite Blanc.ExecutionTrace

/-- USDT has no message that claims another account's signature. -/
def NoSigned (_ : Adr) (_ : Sevm) : Prop := False

/-- **Tether owner's power `destroyBlackFunds`:** the frame's message confiscates the holder's entry. -/
def Confiscates (h : Adr) (e : Sevm) : Prop :=
  Blanc.Sevm.selector e = 0xf3bdc228 ∧ (Sevm.dataWord e 4).toAdr = h

/-- **Tether owner's power `deprecate`:** at this frame's entry the flag is clear. -/
def NotDeprecated (T : Adr) (F : Exec.Frame) : Prop := flag20 ((Devm.getStor F.pre T).get 10) = 0

/-- What the holder's own message takes out of its entry: `transfer`'s amount, whatever the fee and whoever
it pays. A self-transfer with a fee lowers the entry, so unlike `ownDebit` this does not exclude it. -/
def usdtDebit (h : Adr) (e : Sevm) : Nat :=
  if e.caller = h ∧ Blanc.Sevm.selector e = 0xa9059cbb then (Sevm.dataWord e 36).toNat else 0

/-- USDT's dispatcher word. -/
def selTerm : Term :=
  .op2 .and (.op2 .div (.cd (.const 0)) (.const 0x100000000000000000000000000000000000000000000000000000000))
    (.const 0xffffffff)

theorem selTerm_eval (e : Sevm) : selTerm.eval (Env.root e) = Blanc.Sevm.selector e := by
  rw [← legacy_selector_word e, B256.and_comm, show (Bytes.toB256 [0x00] : B256) = 0 by decide]
  rfl

theorem cd_eval (e : Sevm) (i : B256) : (Term.cd (.const i)).eval (Env.root e) = Sevm.dataWord e i := rfl

/-- The selectors with a `top` balance site, which frame laws cover: `transfer`, `transferFrom`, `issue`, `redeem`. -/
def topSelectors : List B256 := [0xa9059cbb, 0x23b872dd, 0xcc872b66, 0xdb006a75]

/-- USDT's allowance table: `approve` is caller-keyed. `rowSiteOk`'s initializer list takes the `top` selectors, since
it is the list of frames the table does not speak for; those frames are the frame laws'. -/
def rowTable : SelTable := ⟨selTerm, [0x095ea7b3], [], topSelectors⟩

theorem rowTable_ok : (wsRoot UsdtWs.implWsAnn).all (rowSiteOk 5 rowTable) = true := by
  decide +kernel

/-- The selectors with a balance row. -/
def balSelectors : List B256 := 0xf3bdc228 :: topSelectors

theorem balRows_ok :
    (mappingSites 2 (wsRoot UsdtWs.implWsAnn)).all (hasSel selTerm balSelectors) = true := by
  decide +kernel

/-- `destroyBlackFunds`' one balance site. -/
def destroySlot : Term := .kecc (.op2 .and (.cd (.const 4)) addrMaskT) (.const 2)

/-- A balance site is on a `top` selector, or it is `destroyBlackFunds`'. -/
theorem destroyRows_ok :
    (mappingSites 2 (wsRoot UsdtWs.implWsAnn)).all
      (fun s => hasSel selTerm topSelectors s || s.slot == destroySlot) = true := by
  decide +kernel

theorem code_ne : code.size ≠ 0 := by decide +kernel

theorem code_notDelegated : code.size ≠ eoaDelegatedCodeLength := by decide +kernel

theorem runtimeSafety : InstalledRuntimeSafety code :=
  InstalledRuntimeSafety.of_linearCheck (by decide +kernel) (by decide +kernel)
    (fun h => code_notDelegated h.1)
    (fun h => code_ne (by
      show code.data.size = 0
      rw [← Array.length_toList, ← ByteArray.toList_eq_toList_data, h, List.length_nil]))

/-! ## The hash premise -/

section Keys

variable {h : Adr} {frames : List Exec.Frame}

/-- The owner's entry at a frame's entry, the slot of its `top` sites. -/
def ownerKey (F : Exec.Frame) : CoinKey :=
  .map 2 (ownerOf (Devm.getStor F.pre F.sevm.currentTarget)).toB256

/-- The keys the certificate's terms cannot name: the owner's and supply words, and each frame's owner's entry. -/
def topKeys (frames : List Exec.Frame) : List CoinKey := .raw 0 :: .raw 1 :: frames.map ownerKey

/-- What the hash premise speaks of. -/
noncomputable abbrev coinKeyList (h : Adr) (frames : List Exec.Frame) : List CoinKey :=
  heldKeys 2 5 h frames ++ frames.flatMap fun F => frameSiteKeys (wsRoot UsdtWs.implWsAnn) (Env.root F.sevm)

/-- **Hash freshness at USDT**: `CoinKeysFresh`, over those keys and `topKeys` too. -/
def UsdtKeysFresh (h : Adr) (frames : List Exec.Frame) : Prop :=
  SlotFootprint.FreshKeys CoinKey.slot [] (fun _ => False) (topKeys frames ++ coinKeyList h frames)

theorem UsdtKeysFresh.coin (keys : UsdtKeysFresh h frames) :
    CoinKeysFresh (wsRoot UsdtWs.implWsAnn) 2 5 h frames :=
  ⟨fun k hk => keys.1 k (List.mem_append_right _ hk), fun a ha b hb =>
    keys.2 a (List.mem_append_right _ ha) b (List.mem_append_right _ hb)⟩

/-- Two listed keys on one slot are one key. -/
theorem UsdtKeysFresh.inj (keys : UsdtKeysFresh h frames) {a b : CoinKey}
    (ha : a ∈ topKeys frames ++ coinKeyList h frames) (hb : b ∈ topKeys frames ++ coinKeyList h frames)
    (eq : a.slot = b.slot) : a = b := keys.2 a ha b hb eq

noncomputable abbrev KeyList (h : Adr) (frames : List Exec.Frame) : List CoinKey := topKeys frames ++ coinKeyList h frames

theorem zero_mem : CoinKey.raw 0 ∈ KeyList h frames := List.mem_append_left _ List.mem_cons_self

theorem one_mem : CoinKey.raw 1 ∈ KeyList h frames :=
  List.mem_append_left _ (List.mem_cons_of_mem _ List.mem_cons_self)

theorem owner_mem {F : Exec.Frame} (hF : F ∈ frames) : ownerKey F ∈ KeyList h frames :=
  List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨F, hF, rfl⟩)))

theorem held_mem : CoinKey.map 2 h.toB256 ∈ KeyList h frames :=
  List.mem_append_right _ (CoinKeysFresh.held_mem (sites := wsRoot UsdtWs.implWsAnn) (frames := frames))

theorem row_mem {F : Exec.Frame} (hF : F ∈ frames) :
    CoinKey.row 5 h.toB256 F.sevm.caller.toB256 ∈ KeyList h frames :=
  List.mem_append_right _ (CoinKeysFresh.row_mem (sites := wsRoot UsdtWs.implWsAnn) hF)

/-- A site of the frame's selector names its key. -/
theorem site_mem {F : Exec.Frame} (hF : F ∈ frames) {slot : Term} {sel : B256} {ni : Bool}
    (hs : (⟨slot, [(selTerm, sel)], ni⟩ : Site) ∈ wsRoot UsdtWs.implWsAnn) (hk : slot.known = true)
    (hsel : Blanc.Sevm.selector F.sevm = sel) : termKey (Env.root F.sevm) slot ∈ KeyList h frames :=
  List.mem_append_right _ (CoinKeysFresh.site_mem (sites := wsRoot UsdtWs.implWsAnn) hF hs (by
    intro g hg known
    simp only [List.mem_singleton] at hg
    subst hg
    exact hsel.symm.trans (selTerm_eval _).symm) hk)

theorem map_key_mem {F : Exec.Frame} (hF : F ∈ frames) {key : Term} {sel : B256} {ni : Bool}
    (hs : (⟨.kecc (.op2 .and key addrMaskT) (.const 2), [(selTerm, sel)], ni⟩ : Site) ∈ wsRoot UsdtWs.implWsAnn)
    (hk : key.known = true) (hsel : Blanc.Sevm.selector F.sevm = sel) :
    CoinKey.map 2 (key.eval (Env.root F.sevm)).toAdr.toB256 ∈ KeyList h frames := by
  have := site_mem (h := h) hF hs (by simp only [Term.known, hk, Bool.and_self, addrMaskT]) hsel
  simpa only [termKey, addrMaskT_eval] using this

theorem caller_eval (e : Sevm) : (Term.caller.eval (Env.root e)).toAdr.toB256 = e.caller.toB256 := by
  change (e.caller.toB256).toAdr.toB256 = _
  rw [toAdr_toB256]

/-- A balance slot of a listed key equal to the holder's is the holder's. -/
theorem bal_eq (keys : UsdtKeysFresh h frames) {a : Adr} (mem : CoinKey.map 2 a.toB256 ∈ KeyList h frames)
    (eq : balSlot a = balSlot h) : a = h := by
  have := keys.2 _ mem _ (held_mem (h := h) (frames := frames)) eq
  injection this with _ e
  exact Adr.toB256_inj e

/-- The owner word's slot is no listed balance slot. -/
theorem bal_ne_zero (keys : UsdtKeysFresh h frames) {a : Adr} (mem : CoinKey.map 2 a.toB256 ∈ KeyList h frames) :
    balSlot a ≠ 0 := fun eq => by
  have := keys.2 _ mem _ (zero_mem (h := h) (frames := frames)) eq
  cases this

/-- A listed balance slot is none of the holder's tracked rows. -/
theorem bal_ne_row (keys : UsdtKeysFresh h frames) {a g : Adr} {G : Exec.Frame} (hG : G ∈ frames)
    (hg : G.sevm.caller = g) (mem : CoinKey.map 2 a.toB256 ∈ KeyList h frames) :
    balSlot a ≠ allowSlot h g := fun eq => by
  subst hg
  have := keys.2 _ mem _ (row_mem (h := h) hG) eq
  cases this

/-- The supply word is none of the holder's tracked rows. -/
theorem one_ne_row (keys : UsdtKeysFresh h frames) {g : Adr} {G : Exec.Frame} (hG : G ∈ frames)
    (hg : G.sevm.caller = g) : (1 : B256) ≠ allowSlot h g := fun eq => by
  subst hg
  have := keys.2 _ (one_mem (h := h) (frames := frames)) _ (row_mem (h := h) hG) eq
  cases this

/-- The supply word is not the holder's entry. -/
theorem one_ne_bal (keys : UsdtKeysFresh h frames) : (1 : B256) ≠ balSlot h := fun eq => by
  have := keys.2 _ (one_mem (h := h) (frames := frames)) _ (held_mem (h := h) (frames := frames)) eq
  cases this

end Keys

/-! ## One frame -/

/-- A good frame's run through the certificate. -/
theorem codeFrame_run {T : Adr} {F : Exec.Frame} (good : CodeFrame T HistFork code F) :
    ∃ S M G, SFunc.Run cert.prog F.sevm (St F.pre S M G) t_0000_c0 (.halted F.post) := by
  obtain ⟨pc, sevm, pre, out, run, committed⟩ := F
  obtain ⟨hpc, hcode, fork, -⟩ := good
  dsimp only at hpc hcode fork
  subst hpc
  cases out with
  | error e => simp only [Execution.commits, Bool.false_eq_true] at committed
  | ok post =>
    obtain ⟨f, hf0, hrun⟩ := lift_sound_noStateGas cert_check hcode fork.stateGas_none run
    obtain rfl : f = t_0000_c0 := Option.some.inj (hf0.symm.trans rfl)
    rw [St.self' pre] at hrun
    exact ⟨_, _, _, hrun⟩

/-- A good frame, not deprecated, is a `CertFrame`: it has no descendant, static or not. -/
theorem certFrame {T : Adr} {G : Exec.Frame} (good : CodeFrame T HistFork code G)
    (target : G.sevm.currentTarget = T) (live : NotDeprecated T G) : CertFrame G code T := by
  obtain ⟨gpc, sevm, pre, out, run, committed⟩ := G
  obtain ⟨pc, hcode, fork, hasCode⟩ := good
  dsimp only [NotDeprecated] at pc hcode fork target hasCode live
  subst pc
  subst target
  refine ⟨rfl, hcode, fork.stateGas_none, rfl, hasCode, ?_⟩
  rw [usdt_descendants_nil run hcode fork.stateGas_none fork.bal_none live]
  exact fun _ h => absurd h List.not_mem_nil

section Frame

variable {T h : Adr} {frames : List Exec.Frame}

/-- The holder's tracked rows are empty. -/
def RowsEmpty (h : Adr) (frames : List Exec.Frame) (σ : StorWords) : Prop :=
  ∀ g, CallerOf frames g → σ (allowSlot h g) = 0

/-- The keys of a `transfer` frame's writes. -/
structure TransferKeys (h : Adr) (frames : List Exec.Frame) (F : Exec.Frame) : Prop where
  caller : CoinKey.map 2 F.sevm.caller.toB256 ∈ KeyList h frames
  dst : CoinKey.map 2 (Sevm.dataWord F.sevm 4).toAdr.toB256 ∈ KeyList h frames

theorem transferKeys {F : Exec.Frame} (hF : F ∈ frames) (s : Blanc.Sevm.selector F.sevm = 0xa9059cbb) :
    TransferKeys h frames F := by
  refine ⟨?_, ?_⟩
  · have mem := map_key_mem (h := h) hF (key := .caller) (ni := true) (by decide +kernel) rfl s
    rwa [caller_eval] at mem
  · have mem := map_key_mem (h := h) hF (key := .cd (.const 4)) (ni := false) (by decide +kernel) rfl s
    rwa [cd_eval] at mem

/-- The keys of a `transferFrom` frame's writes. -/
structure FromKeys (h : Adr) (frames : List Exec.Frame) (F : Exec.Frame) : Prop where
  src : CoinKey.map 2 (Sevm.dataWord F.sevm 4).toAdr.toB256 ∈ KeyList h frames
  dst : CoinKey.map 2 (Sevm.dataWord F.sevm 36).toAdr.toB256 ∈ KeyList h frames
  row : CoinKey.row 5 (Sevm.dataWord F.sevm 4).toAdr.toB256 F.sevm.caller.toB256 ∈ KeyList h frames

theorem fromKeys {F : Exec.Frame} (hF : F ∈ frames) (s : Blanc.Sevm.selector F.sevm = 0x23b872dd) :
    FromKeys h frames F := by
  refine ⟨?_, ?_, ?_⟩
  · have mem := map_key_mem (h := h) hF (key := .cd (.const 4)) (ni := true) (by decide +kernel) rfl s
    rwa [cd_eval] at mem
  · have mem := map_key_mem (h := h) hF (key := .cd (.const 0x24)) (ni := false) (by decide +kernel) rfl s
    rwa [cd_eval] at mem
  · have mem := site_mem (h := h) hF
      (slot := .kecc (.op2 .and .caller addrMaskT) (.kecc (.op2 .and (.cd (.const 4)) addrMaskT) (.const 5)))
      (ni := true) (by decide +kernel) rfl s
    simp only [termKey, addrMaskT_eval, caller_eval, cd_eval] at mem
    exact mem

/-- **The holder's tracked rows, and its entry, across a move's frame law.** -/
theorem transfer_law {F : Exec.Frame} (hF : F ∈ frames) (keys : UsdtKeysFresh h frames)
    (target : F.sevm.currentTarget = T) (K : TransferKeys h frames F)
    {σ σ' : Stor} (hσ : σ = Devm.getStor F.pre T) {f : B256}
    (ok : MoveOk σ F.sevm.caller (Sevm.dataWord F.sevm 4).toAdr (Sevm.dataWord F.sevm 36) f)
    (st : σ' = moveStor σ F.sevm.caller (Sevm.dataWord F.sevm 4).toAdr (Sevm.dataWord F.sevm 36) f)
    (s : Blanc.Sevm.selector F.sevm = 0xa9059cbb)
    (rows : ∀ g, CallerOf frames g → σ.get (allowSlot h g) = 0) :
    (∀ g, CallerOf frames g → σ'.get (allowSlot h g) = 0) ∧
      (σ.get (balSlot h)).toNat ≤ (σ'.get (balSlot h)).toNat + usdtDebit h F.sevm := by
  subst st
  refine ⟨?_, ?_⟩
  · rintro g ⟨G, hG, hg⟩
    have owner : ownerKey F = CoinKey.map 2 (ownerOf σ).toB256 := by
      unfold ownerKey
      rw [target, hσ]
    have ko := owner_mem (h := h) hF
    rw [owner] at ko
    rw [moveStor_get_ne (bal_ne_zero keys K.caller) (bal_ne_zero keys K.dst) (bal_ne_row keys hG hg K.caller)
      (bal_ne_row keys hG hg K.dst) (bal_ne_row keys hG hg ko)]
    exact rows g ⟨G, hG, hg⟩
  · by_cases hc : F.sevm.caller = h
    · have hd : usdtDebit h F.sevm = (Sevm.dataWord F.sevm 36).toNat := ite_eq_left ⟨hc, s⟩
      rw [hd]
      rw [← hc]
      exact moveStor_source ok
    · have := moveStor_ge ok (k := balSlot h) (fun e => hc (bal_eq keys K.caller e.symm))
      omega

/-- A `transferFrom` naming the holder as source moves nothing, its row being empty. -/
theorem from_amount_zero {σ : Stor} {src sp : Adr} {v : B256} (zero : σ.get (allowSlot src sp) = 0)
    (allow : σ.get (allowSlot src sp) ≠ maxUint → v.toNat ≤ (σ.get (allowSlot src sp)).toNat) : v = 0 := by
  have := allow (by rw [zero]; decide +kernel)
  rw [zero] at this
  exact B256.eq_zero_of_toNat (Nat.le_zero.mp this)

/-- **The holder's tracked rows, and its entry, across `transferFrom`'s frame law.** A source other than the
holder misses the entry; the holder as source moves nothing. -/
theorem from_law {F : Exec.Frame} (hF : F ∈ frames) (keys : UsdtKeysFresh h frames)
    (target : F.sevm.currentTarget = T) (K : FromKeys h frames F)
    {σ σ' : Stor} (hσ : σ = Devm.getStor F.pre T) {f : B256}
    (allow : σ.get (allowSlot (Sevm.dataWord F.sevm 4).toAdr F.sevm.caller) ≠ maxUint →
      (Sevm.dataWord F.sevm 68).toNat ≤ (σ.get (allowSlot (Sevm.dataWord F.sevm 4).toAdr F.sevm.caller)).toNat)
    (ok : MoveOk (spendStor σ (Sevm.dataWord F.sevm 4).toAdr F.sevm.caller (Sevm.dataWord F.sevm 68))
      (Sevm.dataWord F.sevm 4).toAdr (Sevm.dataWord F.sevm 36).toAdr (Sevm.dataWord F.sevm 68) f)
    (st : σ' = moveStor (spendStor σ (Sevm.dataWord F.sevm 4).toAdr F.sevm.caller (Sevm.dataWord F.sevm 68))
      (Sevm.dataWord F.sevm 4).toAdr (Sevm.dataWord F.sevm 36).toAdr (Sevm.dataWord F.sevm 68) f)
    (rows : ∀ g, CallerOf frames g → σ.get (allowSlot h g) = 0) :
    (∀ g, CallerOf frames g → σ'.get (allowSlot h g) = 0) ∧
      (σ.get (balSlot h)).toNat ≤ (σ'.get (balSlot h)).toNat := by
  subst st
  obtain ⟨ks, kd, kr⟩ := K
  generalize hsrc : (Sevm.dataWord F.sevm 4).toAdr = src at *
  generalize hdst : (Sevm.dataWord F.sevm 36).toAdr = dst at *
  generalize hv : Sevm.dataWord F.sevm 68 = v at *
  have row0 : allowSlot src F.sevm.caller ≠ 0 := fun eq => by
    have := keys.2 _ kr _ (zero_mem (h := h) (frames := frames)) eq
    cases this
  have ownerSpend : ownerOf (spendStor σ src F.sevm.caller v) = ownerOf σ := by
    unfold spendStor
    split
    · rfl
    · exact ownerOf_set row0
  have ko : CoinKey.map 2 (ownerOf (spendStor σ src F.sevm.caller v)).toB256 ∈ KeyList h frames := by
    have m := owner_mem (h := h) hF
    unfold ownerKey at m
    rwa [target, ← hσ, ← ownerSpend] at m
  have callerRow : σ.get (allowSlot src F.sevm.caller) = 0 → v = 0 := fun z => from_amount_zero z allow
  refine ⟨?_, ?_⟩
  · rintro g ⟨G, hG, hg⟩
    rw [moveStor_get_ne (bal_ne_zero keys ks) (bal_ne_zero keys kd) (bal_ne_row keys hG hg ks)
      (bal_ne_row keys hG hg kd) (bal_ne_row keys hG hg ko)]
    by_cases same : allowSlot src F.sevm.caller = allowSlot h g
    · have e := keys.2 _ kr _ (row_mem (h := h) hG) (by rw [hg]; exact same)
      injection e with _ e1 e2
      have es : src = h := Adr.toB256_inj e1
      have eg : F.sevm.caller = g := by rw [hg] at e2; exact Adr.toB256_inj e2
      subst es
      subst eg
      have z := rows _ ⟨G, hG, hg⟩
      have vz := callerRow z
      subst vz
      unfold spendStor
      rw [if_neg (by rw [z]; decide +kernel), Stor.get_set_self, z]
      decide +kernel
    · rw [spendStor_get_ne same]
      exact rows g ⟨G, hG, hg⟩
  · have keep : (spendStor σ src F.sevm.caller v).get (balSlot h) = σ.get (balSlot h) :=
      spendStor_get_ne fun eq => by
        have := keys.2 _ kr _ (held_mem (h := h) (frames := frames)) eq
        cases this
    by_cases hs : src = h
    · subst hs
      have vz := callerRow (rows _ ⟨F, hF, rfl⟩)
      subst vz
      have := moveStor_source ok
      rw [keep, show (0 : B256).toNat = 0 from rfl] at this
      omega
    · have := moveStor_ge ok (k := balSlot h) (fun e => hs (bal_eq keys ks e.symm))
      rwa [keep] at this

theorem not_poolSel {s : B256} (hs : s ≠ 0xa9059cbb ∧ s ≠ 0x23b872dd ∧ s ≠ 0x70a08231) : ¬ PoolCoinSel s := by
  rintro (p | p | p)
  · exact hs.1 p
  · exact hs.2.1 p
  · exact hs.2.2 p

/-- The owner as caller of `issue` or `redeem`, not the holder: its entry and the supply word miss the holder's cells. -/
theorem owner_apart {F : Exec.Frame} (hF : F ∈ frames) (keys : UsdtKeysFresh h frames)
    (target : F.sevm.currentTarget = T) {σ : Stor} (hσ : σ = Devm.getStor F.pre T)
    (own : F.sevm.caller = ownerOf σ) (other : F.sevm.caller ≠ h) :
    balSlot (ownerOf σ) ≠ balSlot h ∧ ∀ g, CallerOf frames g → balSlot (ownerOf σ) ≠ allowSlot h g := by
  have ko : CoinKey.map 2 (ownerOf σ).toB256 ∈ KeyList h frames := by
    have m := owner_mem (h := h) hF
    unfold ownerKey at m
    rwa [target, ← hσ] at m
  refine ⟨fun e => other (own.trans (bal_eq keys ko e)), ?_⟩
  rintro g ⟨G, hG, hg⟩
  exact bal_ne_row keys hG hg ko

/-- **`destroyBlackFunds` naming another account keeps the holder's entry.** The certificate gives its one
balance site. -/
theorem frame_destroy_keep {F : Exec.Frame} (hF : F ∈ frames) (C : CertFrame F code T)
    (keys : UsdtKeysFresh h frames) (s : Blanc.Sevm.selector F.sevm = 0xf3bdc228) (named : ¬ Confiscates h F.sevm) :
    (F.post.getStor T).get (balSlot h) = (F.pre.getStor T).get (balSlot h) := by
  refine frame_cellInv F C.stateGas C.hasCode _ (Inv := fun v => v = (F.pre.getStor T).get (balSlot h)) rfl ?_
  intro m member w found _ key _
  obtain ⟨site, inRoot, guards, -, cases⟩ := successfulSstore_mappingSite 2 cert_check usdt_wsCert C.pc C.code
    C.stateGas (C.chain member found) found
  rcases cases with ⟨inMap, den⟩ | ⟨known, none, keyEq⟩
  · have row := List.all_eq_true.mp destroyRows_ok site inMap
    rcases Bool.or_eq_true _ _ ▸ row with top | slot
    · have hsel := hasSel_sound top rfl guards
      rw [selTerm_eval, show (Blanc.Exec.Frame.rootDeriv F).sevm = F.sevm from rfl, s] at hsel
      exact absurd hsel (by decide)
    · have eq : site.slot = destroySlot := beq_iff_eq.mp slot
      rw [eq] at den
      have keyEq := den rfl
      have mem := map_key_mem (h := h) hF (key := .cd (.const 4)) (ni := false) (by decide +kernel) rfl s
      rw [cd_eval] at mem
      have e : balSlot (Sevm.dataWord F.sevm 4).toAdr = balSlot h := by
        have slotEq : destroySlot.eval (Env.root F.sevm) = balSlot (Sevm.dataWord F.sevm 4).toAdr := by
          rw [← termKey_slot]
          simp only [destroySlot, termKey, addrMaskT_eval, cd_eval, balSlot, CoinKey.slot]
        rw [← slotEq, ← key]
        exact keyEq.symm
      exact absurd ⟨s, bal_eq keys mem e⟩ named
  · exact absurd (keyEq.symm.trans key) (slot_ne_of_keys keys.coin hF inRoot guards known none)

/-- **One frame: the rows stay empty, and only the holder's own `transfer` lowers its entry.** -/
theorem frame_law {F : Exec.Frame} (hF : F ∈ frames) (good : CodeFrame T HistFork code F)
    (target : F.sevm.currentTarget = T) (live : NotDeprecated T F)
    (own : F.sevm.caller = h → PoolCoinSel (Blanc.Sevm.selector F.sevm))
    (named : ¬ Confiscates h F.sevm) (keys : UsdtKeysFresh h frames)
    (rows : RowsEmpty h frames (wordsAt T F.pre.state)) :
    RowsEmpty h frames (wordsAt T F.post.state) ∧
      ((wordsAt T F.pre.state) (balSlot h)).toNat ≤ ((wordsAt T F.post.state) (balSlot h)).toNat + usdtDebit h F.sevm := by
  obtain ⟨S, M, G, run⟩ := codeFrame_run good
  have fork : HistFork F.sevm.benvStat.fork := good.2.2.1
  have C := certFrame good target live
  have hdep : flag20 ((Devm.getStor (St F.pre S M G) F.sevm.currentTarget).get 10) = 0 := by
    simp only [St_getStor, target]
    exact live
  change (∀ g, CallerOf frames g → (Devm.getStor F.post T).get (allowSlot h g) = 0) ∧
    ((Devm.getStor F.pre T).get (balSlot h)).toNat ≤ ((Devm.getStor F.post T).get (balSlot h)).toNat + usdtDebit h F.sevm
  change ∀ g, CallerOf frames g → (Devm.getStor F.pre T).get (allowSlot h g) = 0 at rows
  by_cases s1 : Blanc.Sevm.selector F.sevm = 0xa9059cbb
  · obtain ⟨-, -, ok, st⟩ := frame_transfer fork s1 hdep run
    simp only [St_getStor, target] at ok st
    exact transfer_law hF keys target (transferKeys hF s1) rfl ok st s1 rows
  by_cases s2 : Blanc.Sevm.selector F.sevm = 0x23b872dd
  · obtain ⟨-, -, allow, ok, st⟩ := frame_transferFrom fork s2 hdep run
    simp only [St_getStor, target] at allow ok st
    obtain ⟨r, e⟩ := from_law hF keys target (fromKeys hF s2) rfl allow ok st rows
    exact ⟨r, by omega⟩
  have other : Blanc.Sevm.selector F.sevm = 0xcc872b66 ∨ Blanc.Sevm.selector F.sevm = 0xdb006a75 →
      F.sevm.caller ≠ h := by
    rintro (s | s) hc
    all_goals
      have ps := own hc
      rw [s] at ps
      exact not_poolSel (by decide) ps
  by_cases s3 : Blanc.Sevm.selector F.sevm = 0xcc872b66
  · obtain ⟨o, st⟩ := frame_issue fork s3 run
    simp only [St_getStor, target] at o st
    obtain ⟨a1, a2⟩ := owner_apart hF keys target rfl o (other (.inl s3))
    rw [st]
    refine ⟨?_, ?_⟩
    · rintro g ⟨G', hG, hg⟩
      rw [issueStor_get_ne (one_ne_row keys hG hg) (a2 g ⟨G', hG, hg⟩)]
      exact rows g ⟨G', hG, hg⟩
    · rw [issueStor_get_ne (one_ne_bal keys) a1]
      omega
  by_cases s4 : Blanc.Sevm.selector F.sevm = 0xdb006a75
  · obtain ⟨o, st⟩ := frame_redeem fork s4 run
    simp only [St_getStor, target] at o st
    obtain ⟨a1, a2⟩ := owner_apart hF keys target rfl o (other (.inr s4))
    rw [st]
    refine ⟨?_, ?_⟩
    · rintro g ⟨G', hG, hg⟩
      rw [redeemStor_get_ne (one_ne_row keys hG hg) (a2 g ⟨G', hG, hg⟩)]
      exact rows g ⟨G', hG, hg⟩
    · rw [redeemStor_get_ne (one_ne_bal keys) a1]
      omega
  have notTop : selTerm.eval (Env.root F.sevm) ∉ topSelectors := by
    rw [selTerm_eval]
    simp only [topSelectors, List.mem_cons, List.not_mem_nil, or_false, not_or]
    exact ⟨s1, s2, s3, s4⟩
  refine ⟨?_, ?_⟩
  · refine frame_rows_zero C cert_check usdt_wsCert (t := rowTable) (b := 5) rfl rowTable_ok
      (rowSep_of_keys keys.coin hF) ?_ rows
    rintro (⟨sel, caller⟩ | ⟨sel, -⟩ | sel)
    · have hsel : Blanc.Sevm.selector F.sevm = 0x095ea7b3 := by
        have := List.mem_singleton.mp sel
        rwa [show rowTable.selT = selTerm from rfl, selTerm_eval] at this
      have hc : F.sevm.caller = h := by
        have e : (Env.root F.sevm).caller = F.sevm.caller.toB256 := rfl
        rw [e, toAdr_toB256] at caller
        exact caller
      have ps := own hc
      rw [hsel] at ps
      exact not_poolSel (by decide) ps
    · exact absurd sel List.not_mem_nil
    · exact notTop sel
  · by_cases s5 : Blanc.Sevm.selector F.sevm = 0xf3bdc228
    · rw [show Devm.getStor F.post T = F.post.getStor T from rfl,
        frame_destroy_keep hF C keys s5 named]
      exact Nat.le_add_right _ _
    · have keep := frame_cell_keep C cert_check usdt_wsCert (selT := selTerm) (R := balSelectors)
        (k := balSlot h) rfl balRows_ok (by
          rw [selTerm_eval]
          simp only [balSelectors, topSelectors, List.mem_cons, List.not_mem_nil, or_false, not_or]
          exact ⟨s5, s1, s2, s3, s4⟩)
        (fun s hs hg hk none => slot_ne_of_keys keys.coin hF hs hg hk none)
      rw [show Devm.getStor F.post T = F.post.getStor T from rfl, keep]
      exact Nat.le_add_right _ _

end Frame

/-! ## The history -/

section History

variable {T h : Adr} {cfg : ChainConfig} {start : Benv} {future : BlockChain}

/-- **USDT's storage moves frame by frame**, while it is not deprecated. A deprecated frame's forward, and what it
re-enters, leaves the claim vacuous rather than assumed away. -/
theorem usdt_chain (capabilities : BodyStageCapabilities HistFork)
    (trace : MidHistoryTraceIn HistFork cfg start future) (installed : start.state.getCode T = code) :
    SettledChain T (fun _ => True) (CodeFrame T HistFork code) (NotDeprecated T)
      (wordsAt T start.state) (wordsAt T future.state) trace.settledFrames :=
  mid_frameChain HistFork.stateGas_none capabilities code_ne code_notDelegated runtimeSafety
    (fun {sevm pre post} run committed hcode fork target _ live => by
      have raw := usdt_descendants_nil run hcode fork.stateGas_none fork.bal_none (by
        rw [target]
        exact live)
      refine List.flatMap_eq_nil_iff.mpr fun D member => ?_
      have := Exec.mem_rawFrameDescendants_of_mem_descendantFrames run D member
      rw [raw] at this
      exact absurd this List.not_mem_nil)
    trace installed

/-- **The locality of the holder's USDT entry**, over a mid history from a state with TetherToken's code. -/
theorem usdt_entry_local (capabilities : BodyStageCapabilities HistFork)
    (trace : MidHistoryTraceIn HistFork cfg start future) (installed : start.state.getCode T = code)
    (authority : PoolAuthorityEmpty NoSigned allowSlot PoolCoinSel h (wordsAt T start.state)
      (coinFrames T (fun _ => True) trace.settledFrames))
    (notDeprecated : ∀ F ∈ coinFrames T (fun _ => True) trace.settledFrames, NotDeprecated T F)
    (noConfiscation : ∀ F ∈ coinFrames T (fun _ => True) trace.settledFrames, ¬ Confiscates h F.sevm)
    (keys : UsdtKeysFresh h (coinFrames T (fun _ => True) trace.settledFrames)) :
    EntryLocal T (fun _ => True) (CodeFrame T HistFork code) (fun σ => (σ (balSlot h)).toNat) (usdtDebit h)
      (fun _ => 0) (wordsAt T start.state) (wordsAt T future.state) trace.settledFrames :=
  entryLocal_of_frames (I := RowsEmpty h (coinFrames T (fun _ => True) trace.settledFrames))
    (usdt_chain capabilities trace installed) notDeprecated (fun g _ => authority.rowsAtCut g)
    (fun F hF good rows => by
      have target := (mem_coinFrames.mp hF).2.1
      obtain ⟨r, e⟩ := frame_law hF good target (notDeprecated F hF)
        (authority.ownCalls F hF) (noConfiscation F hF) keys rows
      exact ⟨r, by simpa only [Nat.add_zero] using e⟩)

/-- A third party's frame does not lower the entry. -/
theorem usdt_third_party {a b : StorWords} {settled : List Exec.Frame} {Good : Exec.Frame → Prop}
    (L : EntryLocal T (fun _ => True) Good (fun σ => (σ (balSlot h)).toNat) (usdtDebit h) (fun _ => 0) a b settled)
    {F : Exec.Frame} (hF : F ∈ coinFrames T (fun _ => True) settled) (caller : F.sevm.caller ≠ h) :
    (wordsAt T F.pre.state (balSlot h)).toNat ≤ (wordsAt T F.post.state (balSlot h)).toNat := by
  have law := L.law F hF
  have hd : usdtDebit h F.sevm = 0 := ite_eq_right fun x => caller x.1
  simpa only [hd, Nat.add_zero] using law

/-- A frame that lowers the entry is the holder's own `transfer`, and lowers it by at most the amount. -/
theorem usdt_lowered {a b : StorWords} {settled : List Exec.Frame} {Good : Exec.Frame → Prop}
    (L : EntryLocal T (fun _ => True) Good (fun σ => (σ (balSlot h)).toNat) (usdtDebit h) (fun _ => 0) a b settled)
    {F : Exec.Frame} (hF : F ∈ coinFrames T (fun _ => True) settled)
    (lower : (wordsAt T F.post.state (balSlot h)).toNat < (wordsAt T F.pre.state (balSlot h)).toNat) :
    F.sevm.caller = h ∧ Blanc.Sevm.selector F.sevm = 0xa9059cbb ∧
      (wordsAt T F.pre.state (balSlot h)).toNat ≤
        (wordsAt T F.post.state (balSlot h)).toNat + (Sevm.dataWord F.sevm 36).toNat := by
  have law := L.law F hF
  by_cases c : F.sevm.caller = h ∧ Blanc.Sevm.selector F.sevm = 0xa9059cbb
  · have hd : usdtDebit h F.sevm = (Sevm.dataWord F.sevm 36).toNat := ite_eq_left c
    simp only [hd, Nat.add_zero] at law
    exact ⟨c.1, c.2, law⟩
  · have hd : usdtDebit h F.sevm = 0 := ite_eq_right c
    simp only [hd, Nat.add_zero] at law
    omega

end History

end Blanc.Lift.CurveCoins.Usdt
