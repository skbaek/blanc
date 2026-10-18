import Blanc.Lift.WriteSiteRows
import Blanc.AddressSlotProofs
import Blanc.Lift.Usdc.Slots
import Blanc.Lift.Usdc.ImplV1Ws
import Blanc.Lift.Usdc.ImplV2Ws
import Blanc.Lift.Usdc.ImplV2_1Ws

/-! # The allowance-locality law for USDC FiatTokenV1, V2 and V2_1 (unit H3)

`ws_row_locality` at the allowance mapping (slot 10) of the Pair, over each version's certified
root write sites (`implV*Run_ws`).  The frame facts are what the write-site checker certifies: an
allowance write's owner word is `caller` or calldata word 4 (masked to an address), and every root
site carries the dispatcher's selector guard.  `AllowedFrame` reads them: the frame's selector is a
caller-keyed writer and its caller is the Pair, or an owner-word writer and its calldata word 4 is
the Pair, or an initializer.

Per version, `SelTable` lists the selectors; the structural check `allowSiteOk` over the root list
is decided by the kernel, so a wrong table fails the build.

- **V1** (`0x3357162b` initialize only): `approve` is caller-keyed.  Its `transferFrom` write
  `allowed[cd4][caller]` is *not* certified non-increasing: solc 0.4.24's `SafeMath.sub` guard is
  `ISZERO ISZERO ISZERO (GT b a)`, one comparison level deeper than `WSt.prune` (two closures) and
  `refineFacts` (three rounds) follow, so the summary carries no order fact.  It therefore stands in
  V1's owner-word row, where the never-signer argument does not apply: the consumer must exclude
  it (or the checker must follow the chain; the H3 report has the change).
- **V2**: caller-keyed `approve`, `increaseAllowance`, `decreaseAllowance`; owner-word (signed)
  `permit` and `approve`/`increase`/`decreaseAllowanceWithAuthorization`; initializers
  `initialize`, `initializeV2`; `transferFrom` is certified non-increasing.
- **V2_1**: as V2 with `permit` the only owner-word writer.

The initializer rows hold the `top` sites (string-copy slots after an `SLOAD`); the consumer
excludes them by the initialized flags (V1 `initialized`, slot 8 byte 20; V2 `_initializedVersion`,
slot 18, for `initializeV2`), under which those entries revert.

`RowSep` is the frame-local collision premise (`WriteSiteRows`). -/

namespace Blanc.Lift.Usdc

open Jaune Blanc Blanc.Lift Blanc.Lift.WriteSite

/-- solc's address mask. -/
def addrMaskT : Term := .const 0xffffffffffffffffffffffffffffffffffffffff

/-- The masked caller word, a caller-keyed row's owner. -/
def callerWordT : Term := .op2 .and .caller addrMaskT

/-- The masked calldata word 4, an owner-word row's owner (the signer of a signed write). -/
def ownerWordT : Term := .op2 .and (.cd (.const 4)) addrMaskT

/-- A version's selector table: the dispatcher's selector term and the selectors whose allowance
writes are caller-keyed, owner-word keyed, and the initializers. -/
structure SelTable where
  selT : Term
  callers : List B256
  owners : List B256
  inits : List B256

/-- The site carries a guard `selT = c` with `c ∈ cs`. -/
def hasSel (selT : Term) (cs : List B256) (s : Site) : Bool :=
  s.guards.any fun g => g.1 == selT && cs.contains g.2

/-- A root site is allowed by the table: non-increasing, a non-allowance known slot, an allowance
row whose owner word fits its selector, or an initializer's. -/
def allowSiteOk (t : SelTable) (s : Site) : Bool :=
  s.nonInc ||
    if s.slot.known then
      match rowOf 10 s.slot with
      | some (o, _) => (o == callerWordT && hasSel t.selT t.callers s) ||
          (o == ownerWordT && hasSel t.selT t.owners s) || hasSel t.selT t.inits s
      | none => true
    else hasSel t.selT t.inits s

/-- What the law allows a protected allowance write in frame `ε`. -/
def AllowedFrame (t : SelTable) (pair : Adr) (ε : Env) : Prop :=
  (t.selT.eval ε ∈ t.callers ∧ ε.caller.toAdr = pair) ∨
  (t.selT.eval ε ∈ t.owners ∧ ((Term.cd (.const 4)).eval ε).toAdr = pair) ∨
  t.selT.eval ε ∈ t.inits

/-- The tracked spender words of the Pair's rows. -/
def AllowKey (Tr : Adr → Prop) (w : B256) : Prop := ∃ g, Tr g ∧ g.toB256 = w

theorem hasSel_sound {selT : Term} {cs : List B256} {s : Site} {ε : Env}
    (h : hasSel selT cs s = true) (hk : selT.known = true) (hg : s.GuardsHold ε) :
    selT.eval ε ∈ cs := by
  simp only [hasSel, List.any_eq_true, Bool.and_eq_true, beq_iff_eq,
    List.contains_iff_mem] at h
  obtain ⟨g, hmem, rfl, hc⟩ := h
  rw [← hg g hmem hk]
  exact hc

theorem addrMaskT_eval (t : Term) (ε : Env) :
    (Term.op2 .and t addrMaskT).eval ε = (t.eval ε).toAdr.toB256 := by
  have hm : (0xffffffffffffffffffffffffffffffffffffffff : B256) = ~~~ addressMask := by decide
  show B256.and (t.eval ε) 0xffffffffffffffffffffffffffffffffffffffff = _
  rw [hm]
  exact and_mask_word (t.eval ε)

/-- **The allowance law over a checked site list.** -/
theorem allow_locality {t : SelTable} {pair : Adr} {Tr : Adr → Prop} {sites : List Site}
    {ε : Env} (hsel : t.selT.known = true) (hok : sites.all (allowSiteOk t) = true)
    (sep : RowSep 10 pair.toB256 (AllowKey Tr) sites ε)
    {P : Sevm → Devm → Ninst → Devm → Prop} {fs : List SFunc} {sevm : Sevm} {pre post : Devm}
    (run : SProg.RunP (WsStep sites ε P) fs sevm pre post) :
    SProg.RunP (fun s d n d' => P s d n d' ∧
        GuardObs (fun x => ∃ g, Tr g ∧ allowSlot pair g = x) (AllowedFrame t pair ε) s d n)
      fs sevm pre post := by
  have hloc := ws_row_locality (allowed := AllowedFrame t pair ε) sep ?hown ?htop run
  case hown =>
    intro s hs hni hg hk o k hr ho
    have h1 := List.all_eq_true.mp hok s hs
    simp only [allowSiteOk, hni, hk, hr, Bool.false_or, ↓reduceIte, Bool.or_eq_true,
      Bool.and_eq_true, beq_iff_eq] at h1
    rcases h1 with (⟨rfl, hc⟩ | ⟨rfl, hc⟩) | hc
    · rw [callerWordT, addrMaskT_eval] at ho
      exact Or.inl ⟨hasSel_sound hc hsel hg, Adr.toB256_inj ho⟩
    · rw [ownerWordT, addrMaskT_eval] at ho
      exact Or.inr (Or.inl ⟨hasSel_sound hc hsel hg, Adr.toB256_inj ho⟩)
    · exact Or.inr (Or.inr (hasSel_sound hc hsel hg))
  case htop =>
    intro s hs hni hg hk
    have h1 := List.all_eq_true.mp hok s hs
    simp only [allowSiteOk, hni, hk, Bool.false_or, Bool.false_eq_true, ↓reduceIte] at h1
    exact Or.inr (Or.inr (hasSel_sound h1 hsel hg))
  refine SProg.RunP.mono ?_ hloc
  intro s d n d' h
  refine ⟨h.1, GuardObs.mono ?_ h.2⟩
  rintro x ⟨g, hTg, rfl⟩
  exact ⟨g.toB256, ⟨g, hTg, rfl⟩, rfl⟩

/-! ## The three versions -/

/-- solc 0.4.24's selector word: `and(div(cd0, 2^224), 0xffffffff)`. -/
def selV1T : Term :=
  .op2 .and (.op2 .div (.cd (.const 0x0))
    (.const 0x100000000000000000000000000000000000000000000000000000000)) (.const 0xffffffff)

/-- solc 0.6.12's selector word: `shr(0xe0, cd0)`. -/
def selV2T : Term := .op2 .shr (.const 0xe0) (.cd (.const 0x0))

/-- FiatTokenV1: `approve` caller-keyed; `transferFrom` (`allowed[cd4][caller]`, not certified
non-increasing) owner-word keyed; `initialize`. -/
def selV1 : SelTable := ⟨selV1T, [0x095ea7b3], [0x23b872dd], [0x3357162b]⟩

/-- FiatTokenV2: `approve`, `increaseAllowance`, `decreaseAllowance`; `permit` and the three
`*AllowanceWithAuthorization`; `initialize`, `initializeV2`. -/
def selV2 : SelTable :=
  ⟨selV2T, [0x095ea7b3, 0x39509351, 0xa457c2d7], [0xd505accf, 0xe1560fd3, 0xc237108f, 0xb0086095],
    [0x3357162b, 0xd608ea64]⟩

/-- FiatTokenV2_1: as V2, with `permit` the only owner-word writer. -/
def selV2_1 : SelTable :=
  ⟨selV2T, [0x095ea7b3, 0x39509351, 0xa457c2d7], [0xd505accf], [0x3357162b, 0xd608ea64]⟩

theorem implV1_allowSitesOk : (wsRoot ImplV1Ws.implWsAnn).all (allowSiteOk selV1) = true := by
  decide +kernel

theorem implV2_allowSitesOk : (wsRoot ImplV2Ws.implWsAnn).all (allowSiteOk selV2) = true := by
  decide +kernel

theorem implV2_1_allowSitesOk :
    (wsRoot ImplV2_1Ws.implWsAnn).all (allowSiteOk selV2_1) = true := by
  decide +kernel

/-- **Allowance locality, FiatTokenV1**: in an ok run of V1's code, every `SSTORE` to a tracked
allowance row `allowSlot pair g` is non-increasing, or its frame is `approve` called by the Pair,
`transferFrom` with owner word the Pair, or `initialize`. -/
theorem implV1_allowLocality {pair : Adr} {Tr : Adr → Prop} {sevm : Sevm} {pre post : Devm}
    (run : Exec 0 sevm pre (.ok post)) (code : sevm.code = ImplV1.code)
    (fork : CoveredFork sevm.benvStat.fork)
    (sep : RowSep 10 pair.toB256 (AllowKey Tr) (wsRoot ImplV1Ws.implWsAnn)
      (WriteSite.Env.root sevm)) :
    SProg.RunP (fun s d n d' => StepIn ⟨0, sevm, pre, .ok post, run⟩ s d n d' ∧
        GuardObs (fun x => ∃ g, Tr g ∧ allowSlot pair g = x)
          (AllowedFrame selV1 pair (WriteSite.Env.root sevm)) s d n)
      ImplV1.cert.prog sevm pre post :=
  allow_locality (by decide) implV1_allowSitesOk sep (implV1Run_ws run code fork)

/-- **Allowance locality, FiatTokenV2**: in an ok run of V2's code, every `SSTORE` to a tracked
allowance row `allowSlot pair g` is non-increasing, or its frame is a caller-keyed allowance writer
called by the Pair, a signed allowance writer whose owner word is the Pair, or an initializer. -/
theorem implV2_allowLocality {pair : Adr} {Tr : Adr → Prop} {sevm : Sevm} {pre post : Devm}
    (run : Exec 0 sevm pre (.ok post)) (code : sevm.code = ImplV2.code)
    (fork : CoveredFork sevm.benvStat.fork)
    (sep : RowSep 10 pair.toB256 (AllowKey Tr) (wsRoot ImplV2Ws.implWsAnn)
      (WriteSite.Env.root sevm)) :
    SProg.RunP (fun s d n d' => StepIn ⟨0, sevm, pre, .ok post, run⟩ s d n d' ∧
        GuardObs (fun x => ∃ g, Tr g ∧ allowSlot pair g = x)
          (AllowedFrame selV2 pair (WriteSite.Env.root sevm)) s d n)
      ImplV2.cert.prog sevm pre post :=
  allow_locality (by decide) implV2_allowSitesOk sep (implV2Run_ws run code fork)

/-- **Allowance locality, FiatTokenV2_1**: as V2, with `permit` the only signed writer. -/
theorem implV2_1_allowLocality {pair : Adr} {Tr : Adr → Prop} {sevm : Sevm} {pre post : Devm}
    (run : Exec 0 sevm pre (.ok post)) (code : sevm.code = ImplV2_1.code)
    (fork : CoveredFork sevm.benvStat.fork)
    (sep : RowSep 10 pair.toB256 (AllowKey Tr) (wsRoot ImplV2_1Ws.implWsAnn)
      (WriteSite.Env.root sevm)) :
    SProg.RunP (fun s d n d' => StepIn ⟨0, sevm, pre, .ok post, run⟩ s d n d' ∧
        GuardObs (fun x => ∃ g, Tr g ∧ allowSlot pair g = x)
          (AllowedFrame selV2_1 pair (WriteSite.Env.root sevm)) s d n)
      ImplV2_1.cert.prog sevm pre post :=
  allow_locality (by decide) implV2_1_allowSitesOk sep (implV2_1Run_ws run code fork)

end Blanc.Lift.Usdc
