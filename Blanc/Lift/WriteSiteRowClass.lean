import Blanc.Lift.WriteSiteRows
import Blanc.Lift.WriteSiteReachHistory
import Blanc.AddressSlotProofs

/-!
# Classifying a write at one owner's rows of a two-level mapping

`ws_row_locality` read through a selector table: every root site of a certified code is non-increasing,
a known slot outside the mapping, a row whose owner word fits its selector, or an initializer's
(`rowSiteOk`, decided per code). So a write at a tracked row of `pair` is non-increasing or its frame is
one the table names (`AllowedFrame`): `pair` as caller of a caller-keyed entry, `pair` in calldata word 4
of an owner-word entry, or an initializer.

* `row_locality`: over a run;
* `row_class_of_wsObs`: at one `SSTORE`;
* `rawWrite_rowClass`: at a raw `SSTORE` of a frame, for any eventual outcome.

Hoisted from the USDC allowance programme, whose base-10 names are instances. Contract-neutral.
-/

namespace Blanc.Lift.WriteSite

open Jaune Blanc Blanc.Lift

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

/-- A root site is allowed by the table at the two-level mapping at base `b`: non-increasing, a known
slot outside it, a row whose owner word fits its selector, or an initializer's. -/
def rowSiteOk (b : B256) (t : SelTable) (s : Site) : Bool :=
  s.nonInc ||
    if s.slot.known then
      match rowOf b s.slot with
      | some (o, _) => (o == callerWordT && hasSel t.selT t.callers s) ||
          (o == ownerWordT && hasSel t.selT t.owners s) || hasSel t.selT t.inits s
      | none => true
    else hasSel t.selT t.inits s

/-- What the law allows a protected row write in frame `ε`. -/
def AllowedFrame (t : SelTable) (pair : Adr) (ε : Env) : Prop :=
  (t.selT.eval ε ∈ t.callers ∧ ε.caller.toAdr = pair) ∨
  (t.selT.eval ε ∈ t.owners ∧ ((Term.cd (.const 4)).eval ε).toAdr = pair) ∨
  t.selT.eval ε ∈ t.inits

/-- The tracked spender words of an owner's rows. -/
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

/-- **The row law over a checked site list**, at the two-level mapping at base `b`. -/
theorem row_locality {b : B256} {t : SelTable} {pair : Adr} {Tr : Adr → Prop} {sites : List Site}
    {ε : Env} (hsel : t.selT.known = true) (hok : sites.all (rowSiteOk b t) = true)
    (sep : RowSep b pair.toB256 (AllowKey Tr) sites ε)
    {P : Sevm → Devm → Ninst → Devm → Prop} {fs : List SFunc} {sevm : Sevm} {pre post : Devm}
    (run : SProg.RunP (WsStep sites ε P) fs sevm pre post) :
    SProg.RunP (fun s d n d' => P s d n d' ∧
        GuardObs (fun x => ∃ g, Tr g ∧ rowSlot b pair.toB256 g.toB256 = x)
          (AllowedFrame t pair ε) s d n)
      fs sevm pre post := by
  have hloc := ws_row_locality (allowed := AllowedFrame t pair ε) sep ?hown ?htop run
  case hown =>
    intro s hs hni hg hk o k hr ho
    have h1 := List.all_eq_true.mp hok s hs
    simp only [rowSiteOk, hni, hk, hr, Bool.false_or, ↓reduceIte, Bool.or_eq_true,
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
    simp only [rowSiteOk, hni, hk, Bool.false_or, Bool.false_eq_true, ↓reduceIte] at h1
    exact Or.inr (Or.inr (hasSel_sound h1 hsel hg))
  refine SProg.RunP.mono ?_ hloc
  intro s d n d' h
  refine ⟨h.1, GuardObs.mono ?_ h.2⟩
  rintro x ⟨g, hTg, rfl⟩
  exact ⟨g.toB256, ⟨g, hTg, rfl⟩, rfl⟩

/-- **The row law at one `SSTORE`.** -/
theorem row_class_of_wsObs {b : B256} {t : SelTable} {pair : Adr} {Tr : Adr → Prop}
    {sites : List Site} {ε : Env} (hsel : t.selT.known = true)
    (hok : sites.all (rowSiteOk b t) = true) (sep : RowSep b pair.toB256 (AllowKey Tr) sites ε)
    {sevm : Sevm} {d : Devm} (obs : WsObs sites ε sevm d (.reg .sstore)) {x v : B256}
    {rest : List B256} (stack : d.stack = x :: v :: rest)
    (tracked : ∃ g, Tr g ∧ rowSlot b pair.toB256 g.toB256 = x) :
    AllowedFrame t pair ε ∨ v.toNat ≤ (d.getStorVal sevm.currentTarget x).toNat :=
  (SProg.RunP.point (P := WsStep sites ε fun _ _ _ _ => True) (d' := d)
    (fun r => row_locality hsel hok sep r) ⟨trivial, obs⟩).2 rfl x v rest stack tracked

/-- **The row law at a raw `SSTORE`.** At a node of a frame entered at pc `0` without state gas and
running a certified code with a write-site annotation whose root sites the table accepts, a write at
a tracked row of `pair` is non-increasing or in an allowed frame, whatever the frame's eventual
outcome. -/
theorem rawWrite_rowClass {b : B256} {G m : Exec.Deriv} (hpc : G.pc = 0)
    (hsg : G.sevm.benvStat.rules.stateGas = none) (chain : Exec.Deriv.ParentPrefix G m)
    {code : ByteArray} {c : Cert} {ann : List WAnn} {t : SelTable} {pair : Adr} {Tr : Adr → Prop}
    (hc : Cert.check code c = true) (hw : wsCert c ann = true) (hcode : G.sevm.code = code)
    (hsel : t.selT.known = true) (hok : (wsRoot ann).all (rowSiteOk b t) = true)
    (sep : RowSep b pair.toB256 (AllowKey Tr) (wsRoot ann) (Env.root G.sevm))
    {w : Exec.StorageWrite} (found : Exec.Deriv.successfulSstore? m = some w)
    (tracked : ∃ g, Tr g ∧ rowSlot b pair.toB256 g.toB256 = w.key) :
    AllowedFrame t pair (Env.root G.sevm) ∨
      w.value.toNat ≤ (m.devm.getStorVal m.sevm.currentTarget w.key).toNat := by
  obtain ⟨site, member, den, guards, nonInc⟩ :=
    successfulSstore_site hc hw hpc hcode hsg chain found
  obtain ⟨-, rest, stack⟩ := Exec.Deriv.successfulSstore?_decoded found
  have obs : WsObs (wsRoot ann) (Env.root G.sevm) m.sevm m.devm (.reg .sstore) := by
    intro _ key value tail actualStack
    obtain ⟨rfl, tailEq⟩ := List.cons.inj (stack.symm.trans actualStack)
    obtain ⟨rfl, -⟩ := List.cons.inj tailEq
    exact ⟨site, member, den, guards, nonInc⟩
  exact row_class_of_wsObs hsel hok sep obs stack tracked

end Blanc.Lift.WriteSite
