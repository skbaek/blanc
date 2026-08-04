-- Conserved.lean : the ERC-3156 flash-mint contract as a `ContractSpec`
-- instance, statements only.  This module is to `Blanc/Fmint.lean` what
-- `Blanc/Solvent.lean` is to `Blanc/Weth.lean` — the property layer over the
-- program layer — and, like that pair, it is named for the property proved
-- rather than for the contract.
--
-- From `~/plans/flashmint-proposal.md`, produced by `~/plans/solvent-split.md`
-- as the second instance the `ContractSpec` record is validated against.  Its
-- invariant is a storage-only *equality* — no callvalue term, no ETH-balance
-- term and no `nof`-class side condition — which is what makes it the useful
-- counterweight to WETH's.
--
-- It imports `Blanc.Ladder` (for `ContractSpec`) and `Blanc.Fmint` (for the
-- program and `supplySlot`), and deliberately NOT `Blanc.Solvent`: fmint and
-- WETH are siblings, so nothing on this side may depend on the other
-- contract's property layer.  The notion both invariants are built from,
-- `balSum`, lives upstream of both in `Blanc/CommonCore.lean`.
--
-- STATE OF THE PROOF.  Arc B of `~/plans/flashmint-proposal.md`
-- (`~/plans/fmint-conserved.md`) is filling this module in.  Landed so far:
-- the `Stor.Conserved` algebra — the two invisibility lemmas, `Stor.Silent`,
-- the four preservation combinators and the `balance ≤ supply` bound corollary
-- — the `fmintSpec` bridges, and eleven of the twelve `FuncSound` inputs plus
-- the reverting fallback (the eight read-only targets and the three ERC-20
-- writers).  Still open: `flashLoan`, the twelfth (Step 4), and the
-- assembly through `ContractSpec.sound_of_dispatch` that turns
-- `FmintPreservesConserved` and `FmintChainPreservesConserved` from
-- `Prop`-valued definitions into theorems (Step 5).  Those two are still
-- asserted of nothing.  The `flashLoan` success specification is Arc C.
--
-- CLAIM HYGIENE.  What this module works towards is *conservation* — an
-- equality about storage, `totalSupply = Σ balances`, at every observable
-- point.  It is not solvency and not liveness.  During a flash loan the minted
-- supply is unbacked by construction; that is the design, not a gap.

import Blanc.Ladder
import Blanc.Fmint

namespace Blanc

open Jaune

/-! ## Instance 2 — `fmint` (ERC-3156 flash mint)

From `~/plans/flashmint-proposal.md`, whose open decision D1 resolved to the
pure token: fmint is an ERC-20 with the ERC-3156 triple and no wrap/unwrap
surface.  The contract is `Blanc.Fmint.fmint`, and `Blanc/FmintCode.lean`
carries the witness that Blanc's compiler really produces its bytes.

The two headline results at the foot of this module are still `Prop`-valued
definitions — statements that elaborate — rather than `theorem`s; see *State of
the proof* above for what has landed and what has not. -/

/-- The conservation invariant: total supply equals the sum of balances.  A
storage-only equality — no callvalue term, no ETH-balance term.

`Fmint.supplySlot` is never address-shaped and `balSum` sums over address-shaped
keys only, so the supply slot self-excludes from the right-hand side. -/
def Stor.Conserved (s : Stor) : Prop :=
  (s.get Fmint.supplySlot).toNat = balSum s

/-! ## The `Stor.Conserved` algebra

Everything below is about the invariant alone — no `Func`, no `Devm`, no
dispatch.  It is what the per-function obligations of Steps 3 and 4 compose
with once a walk has characterized a target's storage effect.

The layer rests on one bit fact: `Fmint.supplySlot` is not address-shaped.
`balSum` sums over address-shaped keys only, so that fact is simultaneously why
the supply slot self-excludes from Σ, why a supply write cannot move Σ, and why
a balance write cannot move the supply. -/

namespace Fmint

/-- `supplySlot` is never address-shaped.  `supplySlot = B256.max` has all
ninety-six high bits set, and `validAdr_iff` says an address-shaped word meets
`addressMask` in nothing.

This is the Lean form of `Blanc/Fmint.lean`'s second collision-guard `example`,
which states the same fact about the six bytes `checkAddress` emits.  `decide`
rather than `decide +kernel`: `B256`'s tactic-built comparison instances stall
in the kernel evaluator (`~/plans/kernel-decidable.md`). -/
theorem supplySlot_not_validAdr : ¬ ValidAdr supplySlot := by
  rw [validAdr_iff]
  decide

/-- The same fact in the form the storage lemmas want. -/
theorem toB256_ne_supplySlot (a : Adr) : a.toB256 ≠ supplySlot :=
  fun h => supplySlot_not_validAdr ⟨a, h⟩

end Fmint

/-- Supply writes are invisible to `balSum`: the supply slot is not an
address-shaped key, so `Stor.rest` — and therefore Σ — cannot see it. -/
theorem Stor.rest_set_supplySlot (s : Stor) (v : B256) :
    Stor.rest (s.set Fmint.supplySlot v) = Stor.rest s := by
  funext a
  simp only [Stor.rest, Function.comp_apply]
  exact Stor.get_set_ne _ (Fmint.toB256_ne_supplySlot a).symm _

/-- Balance writes are invisible to the supply slot, which is the converse
direction and the reason the two storage regions never interfere. -/
theorem Stor.get_supplySlot_set {s : Stor} {k v : B256} (h : ValidAdr k) :
    (s.set k v).get Fmint.supplySlot = s.get Fmint.supplySlot := by
  rcases h with ⟨a, rfl⟩
  exact Stor.get_set_ne _ (Fmint.toB256_ne_supplySlot a) _

/-! ### Storage changes conservation cannot see

`approve`, and both allowance-writing arms of `transferFrom`, move a key that is
in neither of the two regions the invariant mentions.  That is not
whole-storage equality, so the no-op combinator cannot state it; `Stor.Silent`
can, and it is what the extended guard buys at the proof layer. -/

/-- A storage change the conservation invariant cannot see: no address-shaped
key moves, and the supply slot does not move either. -/
def Stor.Silent (s s' : Stor) : Prop :=
  Stor.rest s = Stor.rest s' ∧ s'.get Fmint.supplySlot = s.get Fmint.supplySlot

theorem Stor.Silent.rfl {s : Stor} : Stor.Silent s s := ⟨Eq.refl _, Eq.refl _⟩

theorem Stor.Silent.of_eq {s s' : Stor} (h : s = s') : Stor.Silent s s' :=
  h ▸ Stor.Silent.rfl

theorem Stor.Silent.trans {s s' s'' : Stor}
    (h : Stor.Silent s s') (h' : Stor.Silent s' s'') : Stor.Silent s s'' :=
  ⟨h.1.trans h'.1, h'.2.trans h.2⟩

/-- The guarded allowance write.  `checkSlotCollides` yields exactly these two
hypotheses, and they are exactly what silence needs. -/
theorem Stor.Silent.set {s : Stor} {k v : B256}
    (h_nva : ¬ ValidAdr k) (h_ns : k ≠ Fmint.supplySlot) : Stor.Silent s (s.set k v) := by
  refine ⟨?_, Stor.get_set_ne _ h_ns _⟩
  funext a
  simp only [Stor.rest, Function.comp_apply]
  exact (Stor.get_set_ne _ (fun hc => h_nva ⟨a, hc.symm⟩) _).symm

/-- Σ does not overflow, for free, because the invariant equates it to a
256-bit word.  WETH has to carry this as the `nof` side condition; fmint's
instance declines it precisely because of this lemma. -/
theorem Stor.Conserved.sumNof {s : Stor} (h : Stor.Conserved s) :
    SumNof (Stor.rest s) := by
  show balSum s < 2 ^ 256
  rw [← h]
  exact B256.toNat_lt _

/-- **The bound corollary.**  Every booked balance is at most the supply —
immediately from `le_sum`, once the invariant has identified the supply with Σ.

This is the invariant-dependent argument `Blanc/Fmint.lean`'s `burnAndReturn`
docstring defers to this arc.  Step 4 consumes it twice: it discharges the
mint's balance-side overflow obligation and the burn's underflow obligation,
and it is why the contract carries no supply-underflow guard. -/
theorem Stor.Conserved.le_supply {s : Stor} (h : Stor.Conserved s) (a : Adr) :
    (Stor.rest s a).toNat ≤ (s.get Fmint.supplySlot).toNat := by
  rw [h]; exact le_sum

/-! ### The four preservation combinators

Each takes a characterization of a target's storage effect and returns
`Conserved`.  Together they cover every write fmint performs: a view writes
nothing, `transfer`/`transferFrom` move value between two address-shaped keys,
`flashLoan` mints, and `burnAndReturn` burns.  `approve`'s allowance write is
the no-op case as far as *this* layer is concerned — it touches neither Σ nor
the supply slot — but that is a fact its own walk must supply. -/

/-- **No-op**: storage unchanged. -/
theorem Stor.Conserved.of_eq {s s' : Stor} (h : Stor.Conserved s) (h_eq : s = s') :
    Stor.Conserved s' := h_eq ▸ h

/-- **No-op, in the form a guarded allowance write actually delivers.**  A write
whose key is neither address-shaped nor the supply slot leaves both sides of the
invariant alone, but it does *not* leave storage equal, so `of_eq` cannot see
it.  This is the composite the third storage region needs. -/
theorem Stor.Conserved.of_rest_eq {s s' : Stor} (h : Stor.Conserved s)
    (h_rest : Stor.rest s = Stor.rest s')
    (h_sup : s'.get Fmint.supplySlot = s.get Fmint.supplySlot) :
    Stor.Conserved s' := by
  show _ = balSum s'
  rw [h_sup, h]
  simp only [balSum, h_rest]

/-- The same, packaged: a silent change preserves the invariant. -/
theorem Stor.Conserved.of_silent {s s' : Stor} (h : Stor.Conserved s)
    (h_sil : Stor.Silent s s') : Stor.Conserved s' :=
  h.of_rest_eq h_sil.1 h_sil.2

/-- **Transfer**: value moves between two address-shaped keys and the supply
slot is untouched.  `transfer_preserves_sum` wants Σ not to overflow, and the
invariant itself supplies that (`sumNof`) — there is no side condition to
thread. -/
theorem Stor.Conserved.transfer {s s' : Stor} {a a' : Adr} {x : B256}
    (h : Stor.Conserved s)
    (h_tr : Transfer (Stor.rest s) a x a' (Stor.rest s'))
    (h_sup : s'.get Fmint.supplySlot = s.get Fmint.supplySlot) :
    Stor.Conserved s' := by
  show _ = balSum s'
  rw [h_sup, h]
  exact transfer_preserves_sum h.sumNof h_tr

/-- **Paired mint**: one balance rises by `v` and the supply rises by the same
`v`.  The caller owes only the *supply*-side overflow bound — fmint's
`amount ≤ maxFlashLoan` guard — because the balance-side bound follows from it
through the bound corollary. -/
theorem Stor.Conserved.mint {s s' : Stor} {a : Adr} {v : B256}
    (h : Stor.Conserved s)
    (h_inc : Increase a v (Stor.rest s) (Stor.rest s'))
    (h_nof : B256.Nof (s.get Fmint.supplySlot) v)
    (h_sup : s'.get Fmint.supplySlot = s.get Fmint.supplySlot + v) :
    Stor.Conserved s' := by
  have h_bal : B256.Nof (Stor.rest s a) v := by
    have h_le := h.le_supply a
    unfold B256.Nof at h_nof ⊢
    omega
  show _ = balSum s'
  rw [h_sup, B256.toNat_add_eq_of_nof _ _ h_nof, h]
  exact sum_add_assoc h_inc h_bal

/-- **Paired burn**: one balance falls by `v` and the supply falls by the same
`v`.  The caller owes only `v ≤ balance` — fmint's explicit balance check — and
the bound corollary turns that into `v ≤ supply`, which is why no
supply-underflow guard exists in the contract. -/
theorem Stor.Conserved.burn {s s' : Stor} {a : Adr} {v : B256}
    (h : Stor.Conserved s)
    (h_dec : Decrease a v (Stor.rest s) (Stor.rest s'))
    (h_le : v ≤ Stor.rest s a)
    (h_sup : s'.get Fmint.supplySlot = s.get Fmint.supplySlot - v) :
    Stor.Conserved s' := by
  have h_le_sup : v ≤ s.get Fmint.supplySlot :=
    B256.le_of_toNat_le_toNat
      (le_trans (B256.toNat_le_toNat h_le) (h.le_supply a))
  show _ = balSum s'
  rw [h_sup, B256.toNat_sub_eq_of_le _ _ h_le_sup, h]
  exact sum_sub_assoc h_dec h_le

/-- **The mint pair, in the exact `set` form the walked `SSTORE`s deliver**: a
balance write of `v + bal` at an address-shaped key, then a supply write of
`v + supply` read *after* the balance write.  The caller owes only the
supply-side bound — fmint's `amount ≤ maxFlashLoan` guard — exactly as in the
underlying combinator. -/
theorem Stor.Conserved.mint_set {s : Stor} {a : Adr} {v : B256}
    (h : Stor.Conserved s)
    (h_nof : B256.Nof (s.get Fmint.supplySlot) v) :
    Stor.Conserved
      ((s.set a.toB256 (v + s.get a.toB256)).set Fmint.supplySlot
        (v + (s.set a.toB256 (v + s.get a.toB256)).get Fmint.supplySlot)) := by
  have h_va : ValidAdr a.toB256 := ⟨a, rfl⟩
  have h_sup_mid : (s.set a.toB256 (v + s.get a.toB256)).get Fmint.supplySlot
      = s.get Fmint.supplySlot := Stor.get_supplySlot_set h_va
  refine h.mint (a := a) (v := v) ?_ h_nof ?_
  · rw [Stor.rest_set_supplySlot]
    exact Stor.increase_set s a v
  · rw [Stor.get_set_self, h_sup_mid, B256.add_comm]

/-- **The burn pair, same form**: a balance write of `bal − v` at an
address-shaped key, then a supply write of `supply − v`.  The caller owes only
the balance-side bound `v ≤ bal` — fmint's explicit balance check in
`burnAndReturn` — and the invariant supplies the supply-side bound itself,
which is why the contract carries no supply-underflow guard. -/
theorem Stor.Conserved.burn_set {s : Stor} {a : Adr} {v : B256}
    (h : Stor.Conserved s)
    (h_le : v ≤ s.get a.toB256) :
    Stor.Conserved
      ((s.set a.toB256 (s.get a.toB256 - v)).set Fmint.supplySlot
        ((s.set a.toB256 (s.get a.toB256 - v)).get Fmint.supplySlot - v)) := by
  have h_va : ValidAdr a.toB256 := ⟨a, rfl⟩
  have h_sup_mid : (s.set a.toB256 (s.get a.toB256 - v)).get Fmint.supplySlot
      = s.get Fmint.supplySlot := Stor.get_supplySlot_set h_va
  refine h.burn (a := a) (v := v) ?_ ?_ ?_
  · rw [Stor.rest_set_supplySlot]
    exact Stor.decrease_set s a v
  · exact h_le
  · rw [Stor.get_set_self, h_sup_mid]

/-- The flash-mint instance.  `Inv` ignores both the callvalue and the ETH
balance, and `Side` is trivial: this contract declines the `nof`-class side
condition, which is precisely why every balance-movement slot carries `Side`
in hypothesis position rather than demanding a concrete bound. -/
def fmintSpec : ContractSpec where
  prog := Fmint.fmint
  Inv := fun s _ _ => Stor.Conserved s
  Side := fun _ => True
  inv_forget := id
  inv_mono := fun h _ => h
  inv_recv := fun h _ => h
  side_le := fun _ _ => trivial
  side_transfer := fun _ _ => trivial
  side_addBal := fun _ _ => trivial
  inv_transfer := by
    intro st st' caller callee ca wad v h_sub h_ne _ h_inv
    show Stor.Conserved _
    have h_stor : (st'.addBal callee wad).getStor ca = st.getStor ca := by
      rcases State.of_subBal h_sub with ⟨-, h_st'⟩
      show ((st'.setBal callee _).get ca).stor = (st.get ca).stor
      rw [State.setBal_get_stor, h_st', State.setBal_get_stor]
    rw [h_stor]; exact h_inv
  inv_recv_transfer := by
    intro st st' caller ca wad h_sub h_ne _ h_inv
    show Stor.Conserved _
    have h_stor : (st'.addBal ca wad).getStor ca = st.getStor ca := by
      rcases State.of_subBal h_sub with ⟨-, h_st'⟩
      show ((st'.setBal ca _).get ca).stor = (st.get ca).stor
      rw [State.setBal_get_stor, h_st', State.setBal_get_stor]
    rw [h_stor]; exact h_inv
  inv_addBal := by
    intro w ca a val v _ _ h_inv
    show Stor.Conserved _
    have h_stor : (w.addBal a val).getStor ca = w.getStor ca := by
      show ((w.setBal a _).get ca).stor = (w.get ca).stor
      rw [State.setBal_get_stor]
    rw [h_stor]; exact h_inv

/-- `PrecondC` of the proposal, as the record's frame-entry bundle.  Its
`side` field is `True`: the `nof` hypothesis WETH carries is absent. -/
def PrecondC (fa : Adr) (sevm : Sevm) (devm : Devm) : Prop :=
  fmintSpec.Pre fa sevm devm

/-- `PostcondC` of the proposal. -/
def PostcondC (fa : Adr) (sevm : Sevm) (devm : Devm) : Prop :=
  fmintSpec.Post fa sevm devm

/-- The `State.Inv` counterpart, for the chain-level rungs. -/
def StateInvC (fa : Adr) (w : Jaune.State) : Prop :=
  fmintSpec.StateInv fa w

/-! ## The `fmintSpec` bridges

The counterparts of `wethSpec_pre_iff` / `post_iff` / `prog_eq` / `pre_eq` /
`post_eq`.  They are cheaper here than at WETH for a structural reason worth
stating once: `Precond`/`Postcond`/`State.Inv` are WETH-specific *structures*
that predate the record and have to be shown interderivable with it field by
field, whereas `PrecondC`/`PostcondC`/`StateInvC` were introduced by
`solvent-split` as the record's own bundles under a local name.  So each bridge
is `Iff.rfl` — which is the evidence that this instance adds no restatement. -/

theorem fmintSpec_prog_eq : fmintSpec.prog = Fmint.fmint := rfl

theorem fmintSpec_pre_iff {ca : Adr} {sevm : Sevm} {devm : Devm} :
    fmintSpec.Pre ca sevm devm ↔ PrecondC ca sevm devm := Iff.rfl

theorem fmintSpec_post_iff {ca : Adr} {sevm : Sevm} {devm : Devm} :
    fmintSpec.Post ca sevm devm ↔ PostcondC ca sevm devm := Iff.rfl

theorem fmintSpec_stateInv_iff {ca : Adr} {w : Jaune.State} :
    fmintSpec.StateInv ca w ↔ StateInvC ca w := Iff.rfl

theorem fmintSpec_pre_eq : fmintSpec.Pre = PrecondC := rfl

theorem fmintSpec_post_eq : fmintSpec.Post = PostcondC := rfl

theorem fmintSpec_stateInv_eq : fmintSpec.StateInv = StateInvC := rfl

/-- The frame-entry bundle collapses.  `fmintSpec.Inv` ignores both the
callvalue and the ETH balance, so `PreInv`'s two branches — target and
non-target — are the same proposition, and the whole bundle is just
`Conserved` at the contract's storage.  WETH cannot do this: its `Inv` carries
the callvalue, which is exactly what makes `Devm.PreSolvent` a genuine
conjunction. -/
theorem fmintSpec_preInv_iff {ca : Adr} {sevm : Sevm} {devm : Devm} :
    fmintSpec.PreInv devm ca sevm ↔ Stor.Conserved (Devm.getStor devm ca) := by
  constructor
  · intro h
    by_cases h_ct : sevm.currentTarget = ca
    · exact h.1 h_ct
    · exact h.2 h_ct
  · exact fun h => ⟨fun _ => h, fun _ => h⟩

theorem fmintSpec_postInv_iff {ca : Adr} {devm : Devm} :
    fmintSpec.PostInv devm ca ↔ Stor.Conserved (Devm.getStor devm ca) := Iff.rfl

/-- fmint's dispatch targets, in the form `ContractSpec.sound_of_dispatch`
consumes — the counterpart of `wethSpec_funcSound`, and simpler than it in
exactly one way.  fmint's `Side` is `True`, so there is no `nof` conjunct to
thread through `Func.preserves_nof`: the obligation *is* "this target preserves
`Stor.Conserved` at the frame's own target", with nothing else attached.  That
simplification is the whole point of the instance having declined the side
condition.

Per-function lemmas are stated at `sevm.currentTarget` (`dispatch-generic`'s
design correction): `FuncSound` carries `sevm.currentTarget = ca` in entry
position and this helper is where that equation is discharged.  The
deeper-frame induction hypothesis is discarded here; `flashLoan` is the only
target that consumes it. -/
theorem fmintSpec_funcSound {fa : Adr} (f : Func)
    ( h_cons :
      ∀ {sevm : Sevm} {s r : Devm},
        Func.Run (Fmint.fmint.main :: Fmint.fmintAux) sevm s f r →
        Stor.Conserved (Devm.getStor s sevm.currentTarget) →
        Stor.Conserved (Devm.getStor r sevm.currentTarget) ) :
    fmintSpec.FuncSound fa Fmint.fmintAux f := by
  intro sevm s r h_ct h_pre _ h_run
  subst h_ct
  exact ⟨trivial, h_cons h_run (fmintSpec_preInv_iff.mp h_pre.inv)⟩

/-! ## The effect-free nine

The fallback and the eight read-only dispatch targets: everything fmint can be
asked to do that writes no storage.

**Decision gate (`~/plans/fmint-conserved.md`, Step 2c), resolved NO-GO.**  The
proposal offered a narrowed *syntactic* discharge lemma — a `Bool`-valued
"no `sstore` and no `Xinst` whatsoever" predicate over `Func` plus a soundness
theorem — as an alternative to running the existing invariance automation eight
times.  Both routes were measured on `name` and `maxFlashLoan` before either
was committed to.  The lemma is provable, but it costs **47 code lines against
3** for those two targets and elaborates no faster (both routes sit inside the
noise of the bare-import baseline, ~1.14 s on this host).  The predeclared rule
required *strictly cheaper in both*, so it is dropped and the walks stand.  The
measurement is recorded in `~/plans/reports/fmint-conserved-step-2.md`; do not
re-open it without new evidence. -/

/-- Discharge an effect-free target: `func_inv` shows the run leaves
`Devm.getStor` alone, and the no-op combinator does the rest.  The counterpart
of `Blanc/Solvent.lean`'s `simple_solvent`, and shorter than it because there
is no callvalue to forget. -/
syntax "simple_conserved" : tactic
set_option hygiene false in
macro_rules
| `(tactic| simple_conserved) =>
  `(tactic| exact h.of_eq
              (congr_fun (Func.of_inv Devm.getStor Devm.getStor (by func_inv) run)
                sevm.currentTarget))

/-- The fallback, free.  fmint's fallback is `Func.rev` and `Blanc.not_run_rev`
says no `Func.Run` witnesses it, so the obligation is vacuous — which is what
"an unrecognized selector reverts" buys at the proof layer. -/
theorem fmintSpec_funcSound_rev {fa : Adr} :
    fmintSpec.FuncSound fa Fmint.fmintAux Func.rev := by
  intro _ _ _ _ _ _ h_run
  exact absurd h_run not_run_rev

/-! ### The eight read-only targets

`name`, `symbol` and `totalSupply` are fmint's own; `decimals`, `balanceOf` and
`allowance` are the shared `Blanc.*` definitions hoisted in Step 1, so these
three lemmas are about the same terms WETH's are about; `maxFlashLoan` and
`flashFee` are the ERC-3156 views. -/

theorem name_preserves_conserved {sevm : Sevm} {s r : Devm}
    (run : Func.Run (Fmint.fmint.main :: Fmint.fmintAux) sevm s Fmint.name r)
    (h : Stor.Conserved (Devm.getStor s sevm.currentTarget)) :
    Stor.Conserved (Devm.getStor r sevm.currentTarget) := by simple_conserved

theorem symbol_preserves_conserved {sevm : Sevm} {s r : Devm}
    (run : Func.Run (Fmint.fmint.main :: Fmint.fmintAux) sevm s Fmint.symbol r)
    (h : Stor.Conserved (Devm.getStor s sevm.currentTarget)) :
    Stor.Conserved (Devm.getStor r sevm.currentTarget) := by simple_conserved

theorem decimals_preserves_conserved {sevm : Sevm} {s r : Devm}
    (run : Func.Run (Fmint.fmint.main :: Fmint.fmintAux) sevm s decimals r)
    (h : Stor.Conserved (Devm.getStor s sevm.currentTarget)) :
    Stor.Conserved (Devm.getStor r sevm.currentTarget) := by simple_conserved

theorem totalSupply_preserves_conserved {sevm : Sevm} {s r : Devm}
    (run : Func.Run (Fmint.fmint.main :: Fmint.fmintAux) sevm s Fmint.totalSupply r)
    (h : Stor.Conserved (Devm.getStor s sevm.currentTarget)) :
    Stor.Conserved (Devm.getStor r sevm.currentTarget) := by simple_conserved

theorem balanceOf_preserves_conserved {sevm : Sevm} {s r : Devm}
    (run : Func.Run (Fmint.fmint.main :: Fmint.fmintAux) sevm s balanceOf r)
    (h : Stor.Conserved (Devm.getStor s sevm.currentTarget)) :
    Stor.Conserved (Devm.getStor r sevm.currentTarget) := by simple_conserved

theorem allowance_preserves_conserved {sevm : Sevm} {s r : Devm}
    (run : Func.Run (Fmint.fmint.main :: Fmint.fmintAux) sevm s allowance r)
    (h : Stor.Conserved (Devm.getStor s sevm.currentTarget)) :
    Stor.Conserved (Devm.getStor r sevm.currentTarget) := by simple_conserved

theorem maxFlashLoan_preserves_conserved {sevm : Sevm} {s r : Devm}
    (run : Func.Run (Fmint.fmint.main :: Fmint.fmintAux) sevm s Fmint.maxFlashLoan r)
    (h : Stor.Conserved (Devm.getStor s sevm.currentTarget)) :
    Stor.Conserved (Devm.getStor r sevm.currentTarget) := by simple_conserved

theorem flashFee_preserves_conserved {sevm : Sevm} {s r : Devm}
    (run : Func.Run (Fmint.fmint.main :: Fmint.fmintAux) sevm s Fmint.flashFee r)
    (h : Stor.Conserved (Devm.getStor s sevm.currentTarget)) :
    Stor.Conserved (Devm.getStor r sevm.currentTarget) := by simple_conserved

/-! ## The three ERC-20 writers

`transfer`, `approve` and `transferFrom`: everything fmint can be asked to do
that writes storage without transferring control out of the frame.
(`flashLoan`, which does, is the twelfth obligation and is proved separately.)

Two storage regions are in play and the invariant is an *equality*, so each walk
owes two facts rather than WETH's one: what happened to Σ, and that the supply
slot did not move.  The second is `Stor.AgreeOffAdr` (`Blanc/Ladder.lean`) at
`Fmint.supplySlot`, which is available because `supplySlot` is not
address-shaped — the same bit fact the whole layer rests on. -/

/-- `transfer` moves value between two address-shaped keys and touches nothing
else, so Σ is preserved and the supply slot is untouched.

This is Step 1's hoist paying for itself: `transfer` is the shared
`Blanc.transfer`, `transfer_of_transfer` is `fs`-quantified and lives in
`Blanc/Ladder.lean`, and nothing about fmint has to be re-walked. -/
theorem transfer_preserves_conserved {sevm : Sevm} {s r : Devm}
    (run : Func.Run (Fmint.fmint.main :: Fmint.fmintAux) sevm s transfer r)
    (h : Stor.Conserved (Devm.getStor s sevm.currentTarget)) :
    Stor.Conserved (Devm.getStor r sevm.currentTarget) := by
  rcases transfer_of_transfer run with ⟨⟨_, _, _, h_tr⟩, h_off⟩
  exact h.transfer h_tr (h_off _ Fmint.supplySlot_not_validAdr).symm

section

open Jaune.Ninst Ninst

namespace Fmint

/-- **The extended allowance-slot guard, at the proof layer.**  The fmint
analogue of the hoisted `of_check_address`, and the reason fmint's third storage
region is safe: one flag on the stack yields *both* conjuncts.

`checkSlotCollides` is `checkAddress` or-ed with `isMax`, and an `or` is zero
only when both operands are (`B256.of_or_eq_zero`), so a passing guard says the
key is neither address-shaped nor the supply slot.  `isMax` **is** the
`supplySlot` comparison — `supplySlot = B256.max`, so "all ones" and "the supply
slot" are the same test — which is why the clause costs two bytes;
`Blanc/Fmint.lean` states that identity and its two `example`s prove it. -/
lemma of_checkSlotCollides {e : Sevm} {s s' : Devm} {x xs} :
    (x :: xs <<+ s.stack) →
    Line.Run e s checkSlotCollides s' →
    ∃ y, (y :: x :: xs <<+ s'.stack) ∧
      (y = 0 → ¬ ValidAdr x ∧ x ≠ supplySlot) := by
  intro h_pfx h_run
  simp only [checkSlotCollides] at h_run
  rcases of_run_append _ h_run with ⟨s₂, hAB, hOr⟩; clear h_run
  rcases of_run_append _ hAB with ⟨s₁, hA, hB⟩; clear hAB
  -- (A) dup 0 :: checkAddress  ( x -- va(x) :: x )
  rcases Line.of_run_cons hA with ⟨sd, r_dup, hCA⟩
  rcases of_run_dup r_dup with ⟨w, hw, pb⟩
  have hw_x : w = x := by
    have h_get : s.stack[(0 : Fin 16).val]? = some x :=
      Stack.nth_getElem (Stack.Nth.head x xs) h_pfx
    rw [h_get] at hw; injection hw with hw; exact hw.symm
  subst w
  have hpd : x :: x :: xs <<+ sd.stack := prefix_of_push pb h_pfx
  rcases of_check_address hpd hCA with ⟨va, hs₁, h_iff⟩
  clear hA hCA r_dup pb hpd
  -- (B) dup 1 :: isMax  ( va :: x -- (x =? max) :: va :: x )
  rcases Line.of_run_cons hB with ⟨se, r_dup', hMax⟩
  rcases of_run_dup r_dup' with ⟨w, hw', pb'⟩
  have hw_x' : w = x := by
    have h_get : s₁.stack[(1 : Fin 16).val]? = some x :=
      Stack.nth_getElem (Stack.Nth.tail 0 x va (x :: xs) (Stack.Nth.head x xs)) hs₁
    rw [h_get] at hw'; injection hw' with hw'; exact hw'.symm
  subst w
  have hpe : x :: va :: x :: xs <<+ se.stack := prefix_of_push pb' hs₁
  simp only [isMax] at hMax
  rcases Line.of_run_cons hMax with ⟨sn, r_not, hMax'⟩
  rcases Line.of_run_cons hMax' with ⟨si, r_isz, hnil⟩
  cases hnil
  have hpn : (~~~ x) :: va :: x :: xs <<+ sn.stack := prefix_of_not r_not hpe
  have hps₂ : ((~~~ x) =? 0) :: va :: x :: xs <<+ s₂.stack := prefix_of_iszero r_isz hpn
  -- (C) or : the two clauses collapse into one flag
  refine ⟨((~~~ x) =? 0) ||| va, prefix_of_or (of_run_singleton hOr) hps₂, ?_⟩
  intro h_zero
  rcases Blanc.B256.of_or_eq_zero h_zero with ⟨h_max, h_va⟩
  refine ⟨h_iff.mp h_va, ?_⟩
  intro h_eq
  rw [h_eq] at h_max
  have h_one : B256.eqCheck (~~~ supplySlot) 0 = 1 := by decide
  rw [h_one] at h_max
  exact B256.zero_ne_one h_max.symm

/-- fmint's `prepApprove`, which is WETH's with `checkSlotCollides` in place of
`dup 0 :: checkAddress`.  The guard already duplicates the hash, so the walk is
one instruction shorter and the payload is one conjunct richer. -/
lemma of_prepApprove {sevm : Sevm} {s s' : Devm} :
    Line.Run sevm s prepApprove s' →
    ∃ vx x y, ([vx, x, y] <<+ s'.stack) ∧
      (vx = 0 → ¬ ValidAdr x ∧ x ≠ supplySlot) := by
  line_execute 7
  have hp₀ : [] <<+ s₁.stack := nil_pref
  clear_state s
  line_execute 2
  rcases prefix_of_cdl hp₀ h₂ with ⟨wad, hp₁⟩
  clear_state s₁
  line_execute 2
  have hp₂ : [0, 64, wad] <<+ s₃.stack := by generalize_line_prefix
  clear_state s₂
  line_execute 1
  rcases prefix_of_kec (of_run_singleton h₄) hp₂ with ⟨hash, hp₃⟩
  clear_state s₃
  intro h
  rcases of_checkSlotCollides hp₃ h with ⟨vx, h_vx, h_iff⟩
  exact ⟨vx, hash, wad, h_vx, h_iff⟩

/-- `approve`'s whole storage effect: one write, at a key the guard has shown to
be neither address-shaped nor the supply slot.

Stated as the `set` rather than as two invariance facts because that is what the
walk actually establishes, and because both halves of the conservation
invariant then read off it. -/
lemma of_approve {sevm : Sevm} {s r : Devm}
    (run : Func.Run (fmint.main :: fmintAux) sevm s approve r) :
    ∃ k v, ¬ ValidAdr k ∧ k ≠ supplySlot ∧
      Devm.getStor r sevm.currentTarget = (Devm.getStor s sevm.currentTarget).set k v := by
  simp only [approve] at run
  -- arg 0 ++ checkNonAddress, then the rev-branch on `guy`
  rcases of_run_prepend (arg 0 ++ checkNonAddress) _ run with ⟨s0, h_s0, h_run'⟩; clear run
  have hg0 : Devm.getStor s sevm.currentTarget = Devm.getStor s0 sevm.currentTarget :=
    congr_fun (by invariance : Devm.getStor s = Devm.getStor s0) sevm.currentTarget
  rcases of_run_branch_rev h_run' with ⟨s1, h_pop, h_run⟩; clear h_run'
  have hg1 : Devm.getStor s0 sevm.currentTarget = Devm.getStor s1 sevm.currentTarget :=
    (Devm.PopBurn.getStor h_pop sevm.currentTarget).symm
  clear h_pop
  -- prepApprove : the hash and the guard flag
  rcases of_run_prepend prepApprove _ h_run with ⟨s2, h_s2, h_run'⟩; clear h_run
  rcases of_prepApprove h_s2 with ⟨collides, hash, wad, h_s2_stk, h_iff⟩
  have hg2 : Devm.getStor s1 sevm.currentTarget = Devm.getStor s2 sevm.currentTarget :=
    congr_fun (by invariance : Devm.getStor s1 = Devm.getStor s2) sevm.currentTarget
  clear h_s2
  -- rev-branch : the guard passed, so the flag is 0 and both conjuncts hold
  rcases of_run_branch_rev h_run' with ⟨s3, h_pop', h_run⟩; clear h_run'
  have h_pop_stk := h_pop'.stack
  simp only [Stack.Pop, Split, List.nil_append, List.cons_append] at h_pop_stk
  rw [h_pop_stk] at h_s2_stk
  have h_zero : collides = 0 := pref_head_unique h_s2_stk (pref_append [0] s3.stack)
  rcases h_iff h_zero with ⟨h_nva, h_nsup⟩
  rw [h_zero] at h_s2_stk
  have h_s3_stk : [hash, wad] <<+ s3.stack := cons_pref_cons_inv h_s2_stk
  have hg3 : Devm.getStor s2 sevm.currentTarget = Devm.getStor s3 sevm.currentTarget :=
    (Devm.PopBurn.getStor h_pop' sevm.currentTarget).symm
  clear h_pop' h_pop_stk h_s2_stk h_iff
  -- the single sstore, then a storage-silent tail
  rcases of_run_next h_run with ⟨s4, h_sstore, h_run'⟩; clear h_run
  rcases sstore_getStor_setStorVal h_sstore h_s3_stk with ⟨v, h_set⟩
  have hg4 : Devm.getStor s4 sevm.currentTarget = Devm.getStor r sevm.currentTarget :=
    congr_fun (Func.of_inv Devm.getStor Devm.getStor (by func_inv) h_run') sevm.currentTarget
  exact ⟨hash, v, h_nva, h_nsup, by rw [← hg4, h_set, ← hg3, ← hg2, ← hg1, ← hg0]⟩

/-- **fmint's `updateAllowance` is silent.**  The re-proof the arc's move table
predicted: WETH's `updateAllowance_preserves_stor_rest` names WETH's forked
`updateAllowance`, so it does not transport.

Two things change with the fork.  The guard is `checkSlotCollides` rather than
`checkAddress`, and it runs *before* the `swap 0` rather than after, so three of
WETH's segments become two.  And the conclusion is stronger: because the guard
excludes the supply slot too, the walk delivers `Stor.Silent` rather than bare
`Stor.rest` invariance — which is exactly why fmint can carry a third storage
region under an equality invariant.  Everything else follows WETH's structure
segment for segment.

The `src = caller` bypass is deliberate and scoped to the ERC-20 surface
(`FMINT_DEVIATIONS.md` row 16).  At this layer it is one more early return that
writes nothing, so it costs the proof a branch and nothing else. -/
lemma of_updateAllowance {fs : List Func} {sevm : Sevm} {s r : Devm} {wad dst}
    (hs : [wad, dst] <<+ s.stack)
    (h_run : Func.Run fs sevm s updateAllowance r) :
    Stor.Silent (Devm.getStor s sevm.currentTarget) (Devm.getStor r sevm.currentTarget) := by
  rcases of_run_prepend [caller, dup 2, eq] _ h_run with ⟨s0, h_s0, h_run0⟩
  clear h_run
  rw [congr_fun (Line.of_inv Devm.getStor (by line_inv) h_s0) sevm.currentTarget]
  rcases of_run_branch h_run0 with
    ⟨s1, h_pop, h_runP⟩ | ⟨w, s1, s2, h_ne, h_pop, h_burn, h_runQ⟩
  · -- update path
    -- pop the `(dst =? caller)` flag (= 0, since this is the update branch)
    have hs0 : [dst =? Adr.toB256 sevm.caller, wad, dst] <<+ s0.stack := by generalize_line_prefix
    have hp0 := h_pop.stack
    simp only [Stack.Pop, Split, List.nil_append, List.cons_append] at hp0
    rw [hp0] at hs0
    have hs1 : [wad, dst] <<+ s1.stack := by
      have hflag : (dst =? Adr.toB256 sevm.caller) = 0 :=
        pref_head_unique hs0 (pref_append [0] s1.stack)
      rw [hflag] at hs0; exact cons_pref_cons_inv hs0
    rw [(Devm.PopBurn.getStor h_pop sevm.currentTarget).symm]
    clear hs0 hp0 h_pop h_s0 h_run0 hs
    -- segment 1 : swap 0 :: mstoreAt 0  ( wad dst -- wad )
    rcases of_run_prepend (swap 0 :: mstoreAt 0) _ h_runP with ⟨sA, hA, h_runP⟩
    have hsA : [wad] <<+ sA.stack := by generalize_line_prefix
    rw [congr_fun (Line.of_inv Devm.getStor (by line_inv) hA) sevm.currentTarget]
    clear hA hs1
    -- segment 2 : caller  ( wad -- caller wad )
    rcases of_run_next h_runP with ⟨sB, rB, h_runP⟩
    have hsB : [Adr.toB256 sevm.caller, wad] <<+ sB.stack :=
      prefix_of_push (of_run_caller rB) hsA
    rw [congr_fun (Line.of_inv Devm.getStor (by line_inv)
      (Line.Run.cons rB Line.Run.nil)) sevm.currentTarget]
    clear rB hsA
    -- segment 3 : mstoreAt 1  ( caller wad -- wad )
    rcases of_run_prepend (mstoreAt 1) _ h_runP with ⟨sC, hC, h_runP⟩
    have hsC : [wad] <<+ sC.stack := by generalize_line_prefix
    rw [congr_fun (Line.of_inv Devm.getStor (by line_inv) hC) sevm.currentTarget]
    clear hC hsB
    -- segment 4 : pushList [64, 0]  ( wad -- 0 64 wad )
    rcases of_run_prepend (pushList [64, 0]) _ h_runP with ⟨sD, hD, h_runP⟩
    have hsD : [0, 64, wad] <<+ sD.stack := by generalize_line_prefix
    rw [congr_fun (Line.of_inv Devm.getStor (by line_inv) hD) sevm.currentTarget]
    clear hD hsC
    -- segment 5 : kec  ( 0 64 wad -- hash wad )
    rcases of_run_next h_runP with ⟨sE, rE, h_runP⟩
    rcases prefix_of_kec rE hsD with ⟨hash, hsE⟩
    rw [congr_fun (Line.of_inv Devm.getStor (by line_inv)
      (Line.Run.cons rE Line.Run.nil)) sevm.currentTarget]
    clear rE hsD
    -- segment 6 : checkSlotCollides  ( hash wad -- collides? hash wad )
    -- WETH needs three segments here — swap, dup, checkAddress — because its
    -- guard tests the copy the `swap` left behind.  fmint's guard duplicates
    -- the hash itself and runs first, so the swap moves to the far side.
    rcases of_run_prepend checkSlotCollides _ h_runP with ⟨sG, hG, h_runP⟩
    rcases of_checkSlotCollides hsE hG with ⟨coll, hsG, h_guard⟩
    rw [congr_fun (Line.of_inv Devm.getStor (by line_inv) hG) sevm.currentTarget]
    clear hG hsE
    -- rev-branch : the guard passed, so the key is neither address-shaped nor
    -- the supply slot
    rcases of_run_branch_rev h_runP with ⟨sH, h_popH, h_runP⟩
    have hpH := h_popH.stack
    simp only [Stack.Pop, Split, List.nil_append, List.cons_append] at hpH
    rw [hpH] at hsG
    have hcoll : coll = 0 := pref_head_unique hsG (pref_append [0] sH.stack)
    obtain ⟨hnva, hnsup⟩ := h_guard hcoll
    rw [hcoll] at hsG
    have hsH : [hash, wad] <<+ sH.stack := cons_pref_cons_inv hsG
    rw [(Devm.PopBurn.getStor h_popH sevm.currentTarget).symm]
    clear hsG hpH h_popH h_guard hcoll
    -- segment 7 : swap 0  ( hash wad -- wad hash )
    rcases of_run_next h_runP with ⟨sF, rF, h_runP⟩
    have h_swapF : Stack.Swap (0 : Fin 16).val [hash, wad] [wad, hash] :=
      Stack.swapCore_zero
    have hsF : [wad, hash] <<+ sF.stack :=
      Stack.prefix_of_swap h_swapF (of_run_swap rF) hsH
    rw [congr_fun (Line.of_inv Devm.getStor (by line_inv)
      (Line.Run.cons rF Line.Run.nil)) sevm.currentTarget]
    clear rF hsH
    -- dup 1  ( wad hash -- hash wad hash )
    rcases of_run_next h_runP with ⟨sI, rI, h_runP⟩
    rcases of_run_dup rI with ⟨y, hyI, pbI⟩
    have hyI' : y = hash := by
      have h_nth : Stack.Nth 1 hash [wad, hash] :=
        Stack.Nth.tail 0 hash wad [hash] (Stack.Nth.head hash [])
      have h_get : sF.stack[(1 : Fin 16).val]? = some hash := Stack.nth_getElem h_nth hsF
      rw [h_get] at hyI; injection hyI with hyI; exact hyI.symm
    subst y
    have hsI : [hash, wad, hash] <<+ sI.stack := prefix_of_push pbI hsF
    rw [congr_fun (Line.of_inv Devm.getStor (by line_inv)
      (Line.Run.cons rI Line.Run.nil)) sevm.currentTarget]
    clear rI pbI hsF
    -- sload  ( hash wad hash -- amnt wad hash )
    rcases of_run_next h_runP with ⟨sJ, rJ, h_runP⟩
    rcases prefix_of_sload rJ hsI with ⟨amnt, hsJ, _⟩
    rw [congr_fun (Line.of_inv Devm.getStor (by line_inv)
      (Line.Run.cons rJ Line.Run.nil)) sevm.currentTarget]
    clear rJ hsI
    -- dup 0  ( amnt wad hash -- amnt amnt wad hash )
    rcases of_run_next h_runP with ⟨sK, rK, h_runP⟩
    rcases of_run_dup rK with ⟨y, hyK, pbK⟩
    have hyK' : y = amnt := by
      have h_nth : Stack.Nth 0 amnt [amnt, wad, hash] := Stack.Nth.head amnt [wad, hash]
      have h_get : sJ.stack[(0 : Fin 16).val]? = some amnt := Stack.nth_getElem h_nth hsJ
      rw [h_get] at hyK; injection hyK with hyK; exact hyK.symm
    subst y
    have hsK : [amnt, amnt, wad, hash] <<+ sK.stack := prefix_of_push pbK hsJ
    rw [congr_fun (Line.of_inv Devm.getStor (by line_inv)
      (Line.Run.cons rK Line.Run.nil)) sevm.currentTarget]
    clear rK pbK hsJ
    -- isMax = [not, iszero]  ( amnt amnt wad hash -- flag amnt wad hash )
    rcases of_run_prepend isMax _ h_runP with ⟨sL, hL, h_runP⟩
    rcases Line.of_run_cons hL with ⟨sK', rNot, hL'⟩
    rcases Line.of_run_cons hL' with ⟨sK'', rIsz, hLnil⟩
    cases hLnil
    have hsL0 : (~~~ amnt) :: [amnt, wad, hash] <<+ sK'.stack := prefix_of_not rNot hsK
    have hsL : ((~~~ amnt) =? 0) :: [amnt, wad, hash] <<+ sL.stack := prefix_of_iszero rIsz hsL0
    rw [congr_fun (Line.of_inv Devm.getStor (by line_inv) hL) sevm.currentTarget]
    clear hL rNot rIsz hsK hsL0
    -- returnTrue-branch : early-return when the allowance is infinite
    rcases of_run_branch h_runP with
      ⟨sM, h_popM, h_runP⟩ | ⟨w2, sM, sM2, h_ne2, h_popM, h_burnM, h_runQ2⟩
    · -- continue path
      have hpM := h_popM.stack
      simp only [Stack.Pop, Split, List.nil_append, List.cons_append] at hpM
      rw [hpM] at hsL
      have hflagM : ((~~~ amnt) =? 0) = 0 := pref_head_unique hsL (pref_append [0] sM.stack)
      rw [hflagM] at hsL
      have hsM : [amnt, wad, hash] <<+ sM.stack := cons_pref_cons_inv hsL
      rw [(Devm.PopBurn.getStor h_popM sevm.currentTarget).symm]
      clear hsL hpM h_popM hflagM
      -- dup 1  ( amnt wad hash -- wad amnt wad hash )
      rcases of_run_next h_runP with ⟨sN1, rN1, h_runP⟩
      rcases of_run_dup rN1 with ⟨y, hyN1, pbN1⟩
      have hyN1' : y = wad := by
        have h_nth : Stack.Nth 1 wad [amnt, wad, hash] :=
          Stack.Nth.tail 0 wad amnt [wad, hash] (Stack.Nth.head wad [hash])
        have h_get : sM.stack[(1 : Fin 16).val]? = some wad := Stack.nth_getElem h_nth hsM
        rw [h_get] at hyN1; injection hyN1 with hyN1; exact hyN1.symm
      subst y
      have hsN1 : [wad, amnt, wad, hash] <<+ sN1.stack := prefix_of_push pbN1 hsM
      rw [congr_fun (Line.of_inv Devm.getStor (by line_inv)
        (Line.Run.cons rN1 Line.Run.nil)) sevm.currentTarget]
      clear rN1 pbN1 hsM
      -- dup 1  ( wad amnt wad hash -- amnt wad amnt wad hash )
      rcases of_run_next h_runP with ⟨sN2, rN2, h_runP⟩
      rcases of_run_dup rN2 with ⟨y, hyN2, pbN2⟩
      have hyN2' : y = amnt := by
        have h_nth : Stack.Nth 1 amnt [wad, amnt, wad, hash] :=
          Stack.Nth.tail 0 amnt wad [amnt, wad, hash] (Stack.Nth.head amnt [wad, hash])
        have h_get : sN1.stack[(1 : Fin 16).val]? = some amnt := Stack.nth_getElem h_nth hsN1
        rw [h_get] at hyN2; injection hyN2 with hyN2; exact hyN2.symm
      subst y
      have hsN2 : [amnt, wad, amnt, wad, hash] <<+ sN2.stack := prefix_of_push pbN2 hsN1
      rw [congr_fun (Line.of_inv Devm.getStor (by line_inv)
        (Line.Run.cons rN2 Line.Run.nil)) sevm.currentTarget]
      clear rN2 pbN2 hsN1
      -- lt  ( amnt wad amnt wad hash -- (amnt<?wad) amnt wad hash )
      rcases of_run_next h_runP with ⟨sN, rN, h_runP⟩
      have hsN : (amnt <? wad) :: [amnt, wad, hash] <<+ sN.stack := prefix_of_lt rN hsN2
      rw [congr_fun (Line.of_inv Devm.getStor (by line_inv)
        (Line.Run.cons rN Line.Run.nil)) sevm.currentTarget]
      clear rN hsN2
      -- rev-branch : guarantees allowance ≥ wad
      rcases of_run_branch_rev h_runP with ⟨sO, h_popO, h_runP⟩
      have hpO := h_popO.stack
      simp only [Stack.Pop, Split, List.nil_append, List.cons_append] at hpO
      rw [hpO] at hsN
      have hflagO : (amnt <? wad) = 0 := pref_head_unique hsN (pref_append [0] sO.stack)
      rw [hflagO] at hsN
      have hsO : [amnt, wad, hash] <<+ sO.stack := cons_pref_cons_inv hsN
      rw [(Devm.PopBurn.getStor h_popO sevm.currentTarget).symm]
      clear hsN hpO h_popO hflagO
      -- sub  ( amnt wad hash -- (amnt-wad) hash )
      rcases of_run_next h_runP with ⟨sP, rP, h_runP⟩
      have hsP : (amnt - wad) :: [hash] <<+ sP.stack := prefix_of_sub rP hsO
      rw [congr_fun (Line.of_inv Devm.getStor (by line_inv)
        (Line.Run.cons rP Line.Run.nil)) sevm.currentTarget]
      clear rP hsO
      -- swap 0  ( (amnt-wad) hash -- hash (amnt-wad) )
      rcases of_run_next h_runP with ⟨sQ, rQ, h_runP⟩
      have h_swapQ : Stack.Swap (0 : Fin 16).val [amnt - wad, hash] [hash, amnt - wad] :=
        Stack.swapCore_zero
      have hsQ : [hash, amnt - wad] <<+ sQ.stack :=
        Stack.prefix_of_swap h_swapQ (of_run_swap rQ) hsP
      rw [congr_fun (Line.of_inv Devm.getStor (by line_inv)
        (Line.Run.cons rQ Line.Run.nil)) sevm.currentTarget]
      clear rQ hsP
      -- sstore : the one write, at the guarded key
      rcases of_run_next h_runP with ⟨sR, rR, h_runP⟩
      have h_set : Devm.getStor sR sevm.currentTarget
          = (Devm.getStor sQ sevm.currentTarget).set hash (amnt - wad) :=
        sstore_getStor_set rR hsQ
      -- returnTrue
      rw [← congr_fun (Func.of_inv Devm.getStor Devm.getStor (by func_inv) h_runP)
        sevm.currentTarget, h_set]
      exact Stor.Silent.set hnva hnsup
    · -- early return (allowance infinite) : `returnTrue` preserves storage
      rw [← Devm.PopBurn.getStor h_popM sevm.currentTarget,
          ← Devm.Burn.getStor h_burnM sevm.currentTarget,
          congr_fun (Func.of_inv Devm.getStor Devm.getStor (by func_inv) h_runQ2)
            sevm.currentTarget]
      exact Stor.Silent.rfl
  · -- early return (`src = caller`) : `returnTrue` preserves storage
    have h_eq : Devm.getStor s0 sevm.currentTarget = Devm.getStor r sevm.currentTarget := by
      rw [← Devm.PopBurn.getStor h_pop sevm.currentTarget,
          ← Devm.Burn.getStor h_burn sevm.currentTarget,
          congr_fun (Func.of_inv Devm.getStor Devm.getStor (by func_inv) h_runQ)
            sevm.currentTarget]
    rw [h_eq]
    exact Stor.Silent.rfl

/-- **`transferFrom`'s whole storage effect.**  The two balance writes are a
`Transfer` between address-shaped keys, and the allowance tail is silent, so the
supply slot comes out of the walk untouched.

fmint's `transferFrom` is textually WETH's — the fork is entirely in the
`updateAllowance` it ends with — so this follows WETH's
`transfer_of_transferFrom` segment for segment, with the supply-slot conjunct
threaded alongside.  That conjunct costs nothing new: the two balance writes
report `Stor.AgreeOffAdr` (`Blanc/Ladder.lean`) and the tail reports
`Stor.Silent`, and `supplySlot` is not address-shaped. -/
lemma of_transferFrom {fs : List Func} {sevm : Sevm} {s r : Devm} :
    Func.Run fs sevm s transferFrom r →
    (∃ (x : B256) (a a' : Adr),
      Transfer (Stor.rest (Devm.getStor s sevm.currentTarget)) a x a'
        (Stor.rest (Devm.getStor r sevm.currentTarget))) ∧
    (Devm.getStor r sevm.currentTarget).get supplySlot
      = (Devm.getStor s sevm.currentTarget).get supplySlot := by
  intro h_run
  simp only [transferFrom] at h_run
  -- arg 0 : push src
  rcases of_run_prepend (arg 0) _ h_run with ⟨a1, h1, h_run⟩
  rcases prefix_of_cdl nil_pref h1 with ⟨src, hs1⟩
  have hg : Devm.getStor s = Devm.getStor a1 := Line.of_inv Devm.getStor (by line_inv) h1
  clear h1
  -- dup 0 : [src, src]
  rcases of_run_next h_run with ⟨a2, r2, h_run⟩
  rcases of_run_dup r2 with ⟨y, hy2, pb2⟩
  have hy2' : y = src := by
    have h_get : a1.stack[(0 : Fin 16).val]? = some src :=
      Stack.nth_getElem (Stack.Nth.head src []) hs1
    rw [h_get] at hy2; injection hy2 with hy2; exact hy2.symm
  subst y
  have hs2 : [src, src] <<+ a2.stack := prefix_of_push pb2 hs1
  have hg := hg.trans (Line.of_inv Devm.getStor (by line_inv) (Line.Run.cons r2 Line.Run.nil))
  clear r2 pb2 hs1
  -- checkNonAddress
  rcases of_run_prepend checkNonAddress _ h_run with ⟨a3, h3, h_run⟩
  rcases of_check_non_address hs2 h3 with ⟨na_src, hs3, h_src_iff⟩
  have hg := hg.trans (Line.of_inv Devm.getStor (by line_inv) h3)
  clear h3 hs2
  -- rev-branch : src is a valid address
  rcases of_run_branch_rev h_run with ⟨a4, hp4, h_run⟩
  have hp4s := hp4.stack
  simp only [Stack.Pop, Split, List.nil_append, List.cons_append] at hp4s
  rw [hp4s] at hs3
  have h_src : ValidAdr src := h_src_iff.mp (pref_head_unique hs3 (pref_append [0] a4.stack))
  rw [pref_head_unique hs3 (pref_append [0] a4.stack)] at hs3
  have hs4 : [src] <<+ a4.stack := cons_pref_cons_inv hs3
  have hg := hg.trans (funext (fun a => (Devm.PopBurn.getStor hp4 a).symm))
  clear hs3 hp4s hp4 h_src_iff
  -- arg 2 : push wad
  rcases of_run_prepend (arg 2) _ h_run with ⟨a5, h5, h_run⟩
  rcases prefix_of_cdl hs4 h5 with ⟨wad, hs5⟩
  have hg := hg.trans (Line.of_inv Devm.getStor (by line_inv) h5)
  clear h5 hs4
  -- dup 0 : [wad, wad, src]
  rcases of_run_next h_run with ⟨a6, r6, h_run⟩
  rcases of_run_dup r6 with ⟨y, hy6, pb6⟩
  have hy6' : y = wad := by
    have h_get : a5.stack[(0 : Fin 16).val]? = some wad :=
      Stack.nth_getElem (Stack.Nth.head wad [src]) hs5
    rw [h_get] at hy6; injection hy6 with hy6; exact hy6.symm
  subst y
  have hs6 : [wad, wad, src] <<+ a6.stack := prefix_of_push pb6 hs5
  have hg := hg.trans (Line.of_inv Devm.getStor (by line_inv) (Line.Run.cons r6 Line.Run.nil))
  clear r6 pb6 hs5
  -- dup 2 : [src, wad, wad, src]
  rcases of_run_next h_run with ⟨a7, r7, h_run⟩
  rcases of_run_dup r7 with ⟨y, hy7, pb7⟩
  have hy7' : y = src := by
    have h_get : a6.stack[(2 : Fin 16).val]? = some src :=
      Stack.nth_getElem
        (Stack.Nth.tail 1 src wad [wad, src]
          (Stack.Nth.tail 0 src wad [src] (Stack.Nth.head src []))) hs6
    rw [h_get] at hy7; injection hy7 with hy7; exact hy7.symm
  subst y
  have hs7 : [src, wad, wad, src] <<+ a7.stack := prefix_of_push pb7 hs6
  have hg7 : Devm.getStor s = Devm.getStor a7 :=
    hg.trans (Line.of_inv Devm.getStor (by line_inv) (Line.Run.cons r7 Line.Run.nil))
  clear r7 pb7 hs6
  -- sload : [sbal, wad, wad, src]
  rcases of_run_next h_run with ⟨a8, r8, h_run⟩
  rcases prefix_of_sload r8 hs7 with ⟨sbal, hs8, h_sbal⟩
  have hg := hg7.trans (Line.of_inv Devm.getStor (by line_inv) (Line.Run.cons r8 Line.Run.nil))
  clear r8 hs7
  -- dup 1 : [wad, sbal, wad, wad, src]
  rcases of_run_next h_run with ⟨a9, r9, h_run⟩
  rcases of_run_dup r9 with ⟨y, hy9, pb9⟩
  have hy9' : y = wad := by
    have h_get : a8.stack[(1 : Fin 16).val]? = some wad :=
      Stack.nth_getElem
        (Stack.Nth.tail 0 wad sbal [wad, wad, src] (Stack.Nth.head wad [wad, src])) hs8
    rw [h_get] at hy9; injection hy9 with hy9; exact hy9.symm
  subst y
  have hs9 : [wad, sbal, wad, wad, src] <<+ a9.stack := prefix_of_push pb9 hs8
  have hg := hg.trans (Line.of_inv Devm.getStor (by line_inv) (Line.Run.cons r9 Line.Run.nil))
  clear r9 pb9 hs8
  -- dup 1 : [sbal, wad, sbal, wad, wad, src]
  rcases of_run_next h_run with ⟨a10, r10, h_run⟩
  rcases of_run_dup r10 with ⟨y, hy10, pb10⟩
  have hy10' : y = sbal := by
    have h_get : a9.stack[(1 : Fin 16).val]? = some sbal :=
      Stack.nth_getElem
        (Stack.Nth.tail 0 sbal wad [sbal, wad, wad, src] (Stack.Nth.head sbal [wad, wad, src])) hs9
    rw [h_get] at hy10; injection hy10 with hy10; exact hy10.symm
  subst y
  have hs10 : [sbal, wad, sbal, wad, wad, src] <<+ a10.stack := prefix_of_push pb10 hs9
  have hg := hg.trans (Line.of_inv Devm.getStor (by line_inv) (Line.Run.cons r10 Line.Run.nil))
  clear r10 pb10 hs9
  -- lt : [(sbal <? wad), sbal, wad, wad, src]
  rcases of_run_next h_run with ⟨a11, r11, h_run⟩
  have hs11 : (sbal <? wad) :: [sbal, wad, wad, src] <<+ a11.stack := prefix_of_lt r11 hs10
  have hg := hg.trans (Line.of_inv Devm.getStor (by line_inv) (Line.Run.cons r11 Line.Run.nil))
  clear r11 hs10
  -- rev-branch : source balance ≥ wad
  rcases of_run_branch_rev h_run with ⟨a12, hp12, h_run⟩
  have hp12s := hp12.stack
  simp only [Stack.Pop, Split, List.nil_append, List.cons_append] at hp12s
  rw [hp12s] at hs11
  have h_ltflag : (sbal <? wad) = 0 := pref_head_unique hs11 (pref_append [0] a12.stack)
  have h_le : wad ≤ sbal := by
    rw [← B256.not_lt]; intro hlt
    rw [B256.ltCheck, if_pos hlt] at h_ltflag
    exact B256.zero_ne_one h_ltflag.symm
  rw [h_ltflag] at hs11
  have hs12 : [sbal, wad, wad, src] <<+ a12.stack := cons_pref_cons_inv hs11
  have hg12 : Devm.getStor s = Devm.getStor a12 :=
    hg.trans (funext (fun a => (Devm.PopBurn.getStor hp12 a).symm))
  clear hs11 hp12s hp12 h_ltflag
  -- transferFromUpdateSbal : decrease source balance
  rcases of_run_prepend transferFromUpdateSbal _ h_run with ⟨a13, h13, h_run⟩
  have h_sbal' : sbal = (Devm.getStor a12 sevm.currentTarget).get src := by
    rw [h_sbal]
    show (Devm.getStor a7 sevm.currentTarget).get src = _
    rw [congr_fun (hg7.symm.trans hg12) sevm.currentTarget]
  rcases of_transferFromUpdateSbal h_src h_sbal' h_le hs12 h13 with ⟨h_dec, h_le', h_off13⟩
  have hs13 : [wad, src] <<+ a13.stack := by generalize_line_prefix
  clear h13 hs12 h_sbal h_sbal' h_le
  -- arg 1 : push dst
  rcases of_run_prepend (arg 1) _ h_run with ⟨a14, h14, h_run⟩
  rcases prefix_of_cdl hs13 h14 with ⟨dst, hs14⟩
  have hg' : Devm.getStor a13 = Devm.getStor a14 := Line.of_inv Devm.getStor (by line_inv) h14
  clear h14 hs13
  -- dup 0 : [dst, dst, wad, src]
  rcases of_run_next h_run with ⟨a15, r15, h_run⟩
  rcases of_run_dup r15 with ⟨y, hy15, pb15⟩
  have hy15' : y = dst := by
    have h_get : a14.stack[(0 : Fin 16).val]? = some dst :=
      Stack.nth_getElem (Stack.Nth.head dst [wad, src]) hs14
    rw [h_get] at hy15; injection hy15 with hy15; exact hy15.symm
  subst y
  have hs15 : [dst, dst, wad, src] <<+ a15.stack := prefix_of_push pb15 hs14
  have hg' := hg'.trans (Line.of_inv Devm.getStor (by line_inv) (Line.Run.cons r15 Line.Run.nil))
  clear r15 pb15 hs14
  -- checkNonAddress
  rcases of_run_prepend checkNonAddress _ h_run with ⟨a16, h16, h_run⟩
  rcases of_check_non_address hs15 h16 with ⟨na_dst, hs16, h_dst_iff⟩
  have hg' := hg'.trans (Line.of_inv Devm.getStor (by line_inv) h16)
  clear h16 hs15
  -- rev-branch : dst is a valid address
  rcases of_run_branch_rev h_run with ⟨a17, hp17, h_run⟩
  have hp17s := hp17.stack
  simp only [Stack.Pop, Split, List.nil_append, List.cons_append] at hp17s
  rw [hp17s] at hs16
  have h_dst : ValidAdr dst := h_dst_iff.mp (pref_head_unique hs16 (pref_append [0] a17.stack))
  rw [pref_head_unique hs16 (pref_append [0] a17.stack)] at hs16
  have hs17 : [dst, wad, src] <<+ a17.stack := cons_pref_cons_inv hs16
  have hg' := hg'.trans (funext (fun a => (Devm.PopBurn.getStor hp17 a).symm))
  clear hs16 hp17s hp17 h_dst_iff
  -- dup 0 : [dst, dst, wad, src]
  rcases of_run_next h_run with ⟨a18, r18, h_run⟩
  rcases of_run_dup r18 with ⟨y, hy18, pb18⟩
  have hy18' : y = dst := by
    have h_get : a17.stack[(0 : Fin 16).val]? = some dst :=
      Stack.nth_getElem (Stack.Nth.head dst [wad, src]) hs17
    rw [h_get] at hy18; injection hy18 with hy18; exact hy18.symm
  subst y
  have hs18 : [dst, dst, wad, src] <<+ a18.stack := prefix_of_push pb18 hs17
  have hg' := hg'.trans (Line.of_inv Devm.getStor (by line_inv) (Line.Run.cons r18 Line.Run.nil))
  clear r18 pb18 hs17
  -- dup 2 : [wad, dst, dst, wad, src]
  rcases of_run_next h_run with ⟨a19, r19, h_run⟩
  rcases of_run_dup r19 with ⟨y, hy19, pb19⟩
  have hy19' : y = wad := by
    have h_get : a18.stack[(2 : Fin 16).val]? = some wad :=
      Stack.nth_getElem
        (Stack.Nth.tail 1 wad dst [dst, wad, src]
          (Stack.Nth.tail 0 wad dst [wad, src] (Stack.Nth.head wad [src]))) hs18
    rw [h_get] at hy19; injection hy19 with hy19; exact hy19.symm
  subst y
  have hs19 : [wad, dst, dst, wad, src] <<+ a19.stack := prefix_of_push pb19 hs18
  have hg19 : Devm.getStor a13 = Devm.getStor a19 :=
    hg'.trans (Line.of_inv Devm.getStor (by line_inv) (Line.Run.cons r19 Line.Run.nil))
  clear r19 pb19 hs18
  -- incrWbal : increase destination balance
  rcases of_run_prepend incrWbal _ h_run with ⟨a20, h20, h_run⟩
  rcases incrAt_of_incrWbal h_dst h20 (pref_trans ⟨[dst, wad, src], rfl⟩ hs19)
    with ⟨h_incr, h_off20⟩
  have hs20 : [dst, wad, src] <<+ a20.stack := by
    rcases of_run_append [dup 1, sload, add, swap 0] h20 with ⟨am, ham, hend⟩
    rcases Line.of_run_cons ham with ⟨b1, rd1, ham⟩
    rcases Line.of_run_cons ham with ⟨b2, rsl, ham⟩
    rcases Line.of_run_cons ham with ⟨b3, radd, ham⟩
    rcases Line.of_run_cons ham with ⟨b4, rsw, ham⟩
    cases ham
    rcases Line.of_run_cons hend with ⟨a20', r_sstore, hend⟩
    cases hend
    rcases of_run_dup rd1 with ⟨y, hy, pb⟩
    have hyd : y = dst := by
      have h_get : a19.stack[(1 : Fin 16).val]? = some dst :=
        Stack.nth_getElem
          (Stack.Nth.tail 0 dst wad [dst, dst, wad, src] (Stack.Nth.head dst [dst, wad, src])) hs19
      rw [h_get] at hy; injection hy with hy; exact hy.symm
    subst y
    have hb1 : [dst, wad, dst, dst, wad, src] <<+ b1.stack := prefix_of_push pb hs19
    rcases prefix_of_sload rsl hb1 with ⟨dbal, hb2, _⟩
    have hb3 : (dbal + wad) :: [dst, dst, wad, src] <<+ b3.stack := prefix_of_add radd hb2
    have h_swap : Stack.Swap (0 : Fin 16).val
        [dbal + wad, dst, dst, wad, src] [dst, dbal + wad, dst, wad, src] := Stack.swapCore_zero
    have hb4 : [dst, dbal + wad, dst, wad, src] <<+ am.stack :=
      Stack.prefix_of_swap h_swap (of_run_swap rsw) hb3
    exact prefix_of_sstore r_sstore hb4
  clear h20 hs19
  -- transferFromLog : does not touch storage
  rcases of_run_prepend transferFromLog _ h_run with ⟨a21, h21, h_run⟩
  have hs21 : [wad, src] <<+ a21.stack := by generalize_line_prefix
  have hg_log : Devm.getStor a20 = Devm.getStor a21 := Line.of_inv Devm.getStor (by line_inv) h21
  clear h21
  -- updateAllowance : silent, so it moves neither Σ nor the supply slot
  have h_ua : Stor.Silent (Devm.getStor a21 sevm.currentTarget)
      (Devm.getStor r sevm.currentTarget) := of_updateAllowance hs21 h_run
  -- the supply slot, carried through the two balance writes and the tail
  have h_sup_s13 : (Devm.getStor s sevm.currentTarget).get supplySlot
      = (Devm.getStor a13 sevm.currentTarget).get supplySlot := by
    rw [congr_fun hg12 sevm.currentTarget]
    exact h_off13 supplySlot supplySlot_not_validAdr
  have h_sup_1321 : (Devm.getStor a13 sevm.currentTarget).get supplySlot
      = (Devm.getStor a21 sevm.currentTarget).get supplySlot := by
    rw [congr_fun hg19 sevm.currentTarget, h_off20 supplySlot supplySlot_not_validAdr,
      congr_fun hg_log sevm.currentTarget]
  refine ⟨⟨wad, src.toAdr, dst.toAdr, ?_,
    (Stor.rest (Devm.getStor a13 sevm.currentTarget)), ?_, ?_⟩,
    h_ua.2.trans (h_sup_s13.trans h_sup_1321).symm⟩
  · rw [congr_fun hg12 sevm.currentTarget]; exact h_le'
  · rw [congr_fun hg12 sevm.currentTarget]; exact h_dec
  · rw [congr_fun hg19 sevm.currentTarget, ← h_ua.1, ← congr_fun hg_log sevm.currentTarget]
    exact h_incr

end Fmint

/-- `approve` writes one allowance slot and nothing else.  WETH needed only that
the key is not address-shaped, so that Σ cannot see the write; fmint's invariant
is an *equality*, so it needs the second conjunct too — and that is exactly what
the `isMax` clause of `checkSlotCollides` buys.  This is the reason the third
storage region is safe. -/
theorem approve_preserves_conserved {sevm : Sevm} {s r : Devm}
    (run : Func.Run (Fmint.fmint.main :: Fmint.fmintAux) sevm s Fmint.approve r)
    (h : Stor.Conserved (Devm.getStor s sevm.currentTarget)) :
    Stor.Conserved (Devm.getStor r sevm.currentTarget) := by
  rcases Fmint.of_approve run with ⟨k, v, h_nva, h_nsup, h_set⟩
  exact h.of_silent (h_set ▸ Stor.Silent.set h_nva h_nsup)

/-- `transferFrom` is a `transfer` with an allowance tail.  The tail is silent —
`Fmint.of_updateAllowance`, the arc's one substantial re-proof — so the two
balance writes are the whole storage story and the transfer combinator closes
it. -/
theorem transferFrom_preserves_conserved {sevm : Sevm} {s r : Devm}
    (run : Func.Run (Fmint.fmint.main :: Fmint.fmintAux) sevm s Fmint.transferFrom r)
    (h : Stor.Conserved (Devm.getStor s sevm.currentTarget)) :
    Stor.Conserved (Devm.getStor r sevm.currentTarget) := by
  rcases Fmint.of_transferFrom run with ⟨⟨_, _, _, h_tr⟩, h_sup⟩
  exact h.transfer h_tr h_sup

end

/-- Headline 1 of `flashmint-proposal.md`, as a statement.  This is the shape
`weth_preserves_solvent` has, with the record substituted; it is asserted of
nothing and proved nowhere. -/
def FmintPreservesConserved (fa : Adr) : Prop :=
  ∀ sevm pre post,
    Exec 0 sevm pre (.ok post) →
    (sevm.currentTarget = fa → some sevm.code.toList = Prog.compile Fmint.fmint) →
    PrecondC fa sevm pre →
    PostcondC fa sevm post

/-- The chain-level rung, same substitution.  The `wdsum` bound survives as a
hypothesis about the world rather than about the contract, so it is unaffected
by the instance. -/
def FmintChainPreservesConserved (fa : Adr) : Prop :=
  ∀ ch ch' : BlockChain,
    BlockChain.Reach ch ch' →
    StateInvC fa ch.state →
    StateInvC fa ch'.state


end Blanc
