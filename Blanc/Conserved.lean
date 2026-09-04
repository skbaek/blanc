-- Conserved.lean : supply conservation for the ERC-3156 flash-mint contract,
-- as a `ContractSpec` instance.  This module is to `Blanc/Fmint.lean` what
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
-- (`~/plans/fmint-conserved.md`) is complete: the `Stor.Conserved` algebra —
-- the two invisibility lemmas, `Stor.Silent`, the four preservation
-- combinators and the `balance ≤ supply` bound corollary — the `fmintSpec`
-- bridges, all twelve `FuncSoundNoMem` obligations plus the reverting fallback,
-- and
-- the assembly through `ContractSpec.soundNoMem_of_dispatch` and
-- `ContractSpec.preserves_noMem`.  `fmint_preserves_conserved` and
-- `chain_preserves_conserved` carry the statements this module used to hold as
-- `Prop`-valued definitions asserted of nothing.  The arc's conditional Step 6
-- added the quantified open-contract layer: `fmintSpec_preservesNoMem` is now
-- the instantiation of `ContractSpec.preservesNoMem_of_dispatch`
-- (`Blanc/Ladder.lean`),
-- and context stability across program extension is settled at the foot of
-- this module (`fmint_core_stable`, `fmint_funcSound_stable`) — eleven of the
-- twelve obligations transport verbatim; `flashLoan` is re-discharge.  The
-- `flashLoan` *success* specification is Arc C, and it landed in
-- `Blanc/FlashSpec.lean` (`Fmint.fmint_flashLoan_spec` and its seven
-- `no_success_of_*` corollaries), downstream of this module.  Note what it is
-- and is not: partial correctness about a successful run given as a
-- hypothesis, NOT a state-restoration claim and not liveness.  Nothing in
-- *this* module claims any of it.
--
-- CLAIM HYGIENE.  What this module works towards is *conservation* — an
-- equality about storage, `totalSupply = Σ balances`, at every observable
-- point.  It is not solvency and not liveness.  During a flash loan the minted
-- supply is unbacked by construction; that is the design, not a gap.

import Blanc.BalanceAlgebra
import Blanc.Fmint

namespace Blanc

open Jaune

/-! ## Instance 2 — `fmint` (ERC-3156 flash mint)

From `~/plans/flashmint-proposal.md`, whose open decision D1 resolved to the
pure token: fmint is an ERC-20 with the ERC-3156 triple and no wrap/unwrap
surface.  The contract is `Blanc.Fmint.fmint`, and `Blanc/FmintCode.lean`
carries the witness that Blanc's compiler really produces its bytes.

The two headline results near the foot of this module are theorems
(`fmint_preserves_conserved`, `chain_preserves_conserved`); see *State of the
proof* above for what is in and out of scope. -/

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

/-! ### Genesis: storage that reads zero everywhere is conserved

`fmint_preserves_conserved` is a *preservation* theorem: it takes the invariant
at the start of an execution and returns it at the end.  Something has to
establish the hypothesis once, and for a contract installed at genesis that
something is this lemma — both sides of the equality are `0`, because the supply
slot reads `0` like every other key and `balSum` then sums the constant-`0`
function.

Read its scope honestly.  It says nothing about *deployment*: Blanc compiles one
runtime and has no constructor (`FMINT_DEVIATIONS.md` row 23), so no
initcode/`CREATE` theorem connects this to an on-chain deployment transaction.
It closes exactly one gap — the genesis-installed case — and leaves that one
open. -/

/-- **Genesis.**  Storage reading `0` at every key is conserved. -/
theorem Stor.Conserved.of_get_eq_zero {s : Stor} (h : ∀ k, s.get k = 0) :
    Stor.Conserved s := by
  show (s.get Fmint.supplySlot).toNat = balSum s
  have h_rest : Stor.rest s = fun _ => (0 : B256) := funext fun a => h _
  rw [h, balSum, sum, h_rest, sumBelow_zero]
  rfl

/-- **Genesis, at the canonical empty map.**  An account created with no storage
entries at all satisfies the invariant before it has run. -/
theorem Stor.Conserved.of_empty : Stor.Conserved Stor.empty :=
  Stor.Conserved.of_get_eq_zero fun _ => rfl

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

/-- fmint's dispatch targets, in the form
`ContractSpec.soundNoMem_of_dispatch` consumes — the counterpart of
`wethSpec_funcSound`, and simpler than it in
exactly one way.  fmint's `Side` is `True`, so there is no `nof` conjunct to
thread through `Func.preserves_nof`: the obligation *is* "this target preserves
`Stor.Conserved` at the frame's own target", with nothing else attached.  That
simplification is the whole point of the instance having declined the side
condition.

Per-function lemmas are stated at `sevm.currentTarget` (`dispatch-generic`'s
design correction): `FuncSoundNoMem` carries `sevm.currentTarget = ca` in entry
position and this helper is where that equation is discharged.  The
deeper-frame induction hypothesis is discarded here; `flashLoan` is the only
target that consumes it. -/
theorem fmintSpec_funcSound {fa : Adr} (f : Func)
    ( h_cons :
      ∀ {sevm : Sevm} {s r : Devm},
        Func.Run (Fmint.fmint.main :: Fmint.fmintAux) sevm s f r →
        Stor.Conserved (Devm.getStor s sevm.currentTarget) →
        Stor.Conserved (Devm.getStor r sevm.currentTarget) ) :
    fmintSpec.FuncSoundNoMem fa Fmint.fmintAux f := by
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

/-- The fallback, free.  fmint's fallback is `Func.revert` and `Blanc.not_run_revert`
says no `Func.Run` witnesses it, so the obligation is vacuous — which is what
"an unrecognized selector reverts" buys at the proof layer. -/
theorem fmintSpec_funcSound_revert {fa : Adr} :
    fmintSpec.FuncSoundNoMem fa Fmint.fmintAux Func.revert := by
  intro _ _ _ _ _ _ h_run
  exact absurd h_run not_run_revert

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
  rcases prefix_of_keccak256 (of_run_singleton h₄) hp₂ with ⟨hash, hp₃⟩
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
  -- arg 0 ++ checkNonAddress, then the revert-branch on `guy`
  rcases of_run_prepend (arg 0 ++ checkNonAddress) _ run with ⟨s0, h_s0, h_run'⟩; clear run
  have hg0 : Devm.getStor s sevm.currentTarget = Devm.getStor s0 sevm.currentTarget :=
    congr_fun (by invariance : Devm.getStor s = Devm.getStor s0) sevm.currentTarget
  rcases of_run_branch_revert h_run' with ⟨s1, h_pop, h_run⟩; clear h_run'
  have hg1 : Devm.getStor s0 sevm.currentTarget = Devm.getStor s1 sevm.currentTarget :=
    (Devm.PopBurn.getStor h_pop sevm.currentTarget).symm
  clear h_pop
  -- prepApprove : the hash and the guard flag
  rcases of_run_prepend prepApprove _ h_run with ⟨s2, h_s2, h_run'⟩; clear h_run
  rcases of_prepApprove h_s2 with ⟨collides, hash, wad, h_s2_stk, h_iff⟩
  have hg2 : Devm.getStor s1 sevm.currentTarget = Devm.getStor s2 sevm.currentTarget :=
    congr_fun (by invariance : Devm.getStor s1 = Devm.getStor s2) sevm.currentTarget
  clear h_s2
  -- revert-branch : the guard passed, so the flag is 0 and both conjuncts hold
  rcases of_run_branch_revert h_run' with ⟨s3, h_pop', h_run⟩; clear h_run'
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
    -- segment 5 : keccak256  ( 0 64 wad -- hash wad )
    rcases of_run_next h_runP with ⟨sE, rE, h_runP⟩
    rcases prefix_of_keccak256 rE hsD with ⟨hash, hsE⟩
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
    -- revert-branch : the guard passed, so the key is neither address-shaped nor
    -- the supply slot
    rcases of_run_branch_revert h_runP with ⟨sH, h_popH, h_runP⟩
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
      -- revert-branch : guarantees allowance ≥ wad
      rcases of_run_branch_revert h_runP with ⟨sO, h_popO, h_runP⟩
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
  -- revert-branch : src is a valid address
  rcases of_run_branch_revert h_run with ⟨a4, hp4, h_run⟩
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
  -- revert-branch : source balance ≥ wad
  rcases of_run_branch_revert h_run with ⟨a12, hp12, h_run⟩
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
  -- revert-branch : dst is a valid address
  rcases of_run_branch_revert h_run with ⟨a17, hp17, h_run⟩
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

/-- **The callback, and the induction hypothesis.**  Any successful `call` made
from the contract's own frame preserves conservation, provided every deeper
frame does — which is exactly what `Exec.InvDepth` supplies, and `flashLoan`
is the only target that consumes it.

The operands are arbitrary: fmint passes `value = 0`, but conservation is
storage-only, so even the value transfer is invisible and the lemma does not
need to know.  This is the counterpart of WETH's `of_send_to_caller`
(`Blanc/Solvent.lean`), which cannot transport because its conclusion is
balance arithmetic; the storage-only walk keeps the frame plumbing — the seven
pops, delegation resolution, the four ways the call can fail without entering
a frame, rollback, the precompile case, and the resumed parent — and drops
every solvency segment.  Unlike WETH's, it also returns the parent's stack
shape, because fmint keeps executing after the call returns and the repayment
needs `amount` and `receiver` back.

The induction hypothesis is applied at the child's initial machine: the value
transfer touches only balances, so the child enters with the parent's storage
and code at the contract address, and `Prog.At` needs exactly the delegation
argument WETH's proof makes — a compiled program is never a delegation
designator, so `accessDelegation` resolves to the code itself. -/
lemma conserved_of_call {sevm : Sevm} {s sf : Devm} {g w v ii is oi os : B256} {xs : Stack}
    (ih : Exec.InvDepth sevm.depth sevm.currentTarget Fmint.fmint
      (fmintSpec.PreWf sevm.currentTarget) (fmintSpec.Post sevm.currentTarget))
    (hp : (g :: w :: v :: ii :: is :: oi :: os :: xs) <<+ s.stack)
    (h_code : some (s.getCode sevm.currentTarget).toList = Prog.compile Fmint.fmint)
    (h_cons : Stor.Conserved (Devm.getStor s sevm.currentTarget))
    (h_run : Ninst.Run sevm s call sf) :
    Stor.Conserved (Devm.getStor sf sevm.currentTarget) ∧ ∃ b, ((b :: xs) <<+ sf.stack) := by
  rcases h_run with ⟨xl, h_fill, pc, h_run⟩
  simp only [Ninst.StepRun, Ninst.step_exec, XStep.run_toStep, Xinst.step,
    Bind.bind, Except.bind, Except.assert] at h_run
  -- pop gas
  rcases eq1 : Devm.pop s with _ | ⟨gas1, devm1⟩ <;> simp only [eq1] at h_run
  · cases XStep.run_ofExcept_error h_run
  have e1 := (Devm.pop_of_pop eq1).stack
  simp only [Stack.Pop, Split, List.nil_append, List.cons_append] at e1
  rw [e1] at hp
  rw [pref_head_unique hp (pref_append [gas1] devm1.stack)] at hp
  replace hp := cons_pref_cons_inv hp
  -- pop callee
  rcases eq2 : Devm.popToAdr devm1 with _ | ⟨callee, devm2⟩ <;> simp only [eq2] at h_run
  · cases XStep.run_ofExcept_error h_run
  rcases Devm.pop_of_popToAdr eq2 with ⟨x2, hx2, h_pop2⟩
  have e2 := (Devm.pop_of_pop h_pop2).stack
  simp only [Stack.Pop, Split, List.nil_append, List.cons_append] at e2
  rw [e2] at hp
  rw [pref_head_unique hp (pref_append [x2] devm2.stack)] at hp
  replace hp := cons_pref_cons_inv hp
  -- pop value
  rcases eq3 : Devm.pop devm2 with _ | ⟨value, devm3⟩ <;> simp only [eq3] at h_run
  · cases XStep.run_ofExcept_error h_run
  have e3 := (Devm.pop_of_pop eq3).stack
  simp only [Stack.Pop, Split, List.nil_append, List.cons_append] at e3
  rw [e3] at hp
  rw [pref_head_unique hp (pref_append [value] devm3.stack)] at hp
  replace hp := cons_pref_cons_inv hp
  -- pop the four indices/sizes
  rcases eq4 : Devm.popToNat devm3 with _ | ⟨inputIndex, devm4⟩ <;> simp only [eq4] at h_run
  · cases XStep.run_ofExcept_error h_run
  rcases Devm.pop_of_popToNat eq4 with ⟨x4, h_pop4⟩
  have e4 := h_pop4.stack
  simp only [Stack.Pop, Split, List.nil_append, List.cons_append] at e4
  rw [e4] at hp
  rw [pref_head_unique hp (pref_append [x4] devm4.stack)] at hp
  replace hp := cons_pref_cons_inv hp
  rcases eq5 : Devm.popToNat devm4 with _ | ⟨inputSize, devm5⟩ <;> simp only [eq5] at h_run
  · cases XStep.run_ofExcept_error h_run
  rcases Devm.pop_of_popToNat eq5 with ⟨x5, h_pop5⟩
  have e5 := h_pop5.stack
  simp only [Stack.Pop, Split, List.nil_append, List.cons_append] at e5
  rw [e5] at hp
  rw [pref_head_unique hp (pref_append [x5] devm5.stack)] at hp
  replace hp := cons_pref_cons_inv hp
  rcases eq6 : Devm.popToNat devm5 with _ | ⟨outputIndex, devm6⟩ <;> simp only [eq6] at h_run
  · cases XStep.run_ofExcept_error h_run
  rcases Devm.pop_of_popToNat eq6 with ⟨x6, h_pop6⟩
  have e6 := h_pop6.stack
  simp only [Stack.Pop, Split, List.nil_append, List.cons_append] at e6
  rw [e6] at hp
  rw [pref_head_unique hp (pref_append [x6] devm6.stack)] at hp
  replace hp := cons_pref_cons_inv hp
  rcases eq7 : Devm.popToNat devm6 with _ | ⟨outputSize, devm7⟩ <;> simp only [eq7] at h_run
  · cases XStep.run_ofExcept_error h_run
  rcases Devm.pop_of_popToNat eq7 with ⟨x7, h_pop7⟩
  have e7 := h_pop7.stack
  simp only [Stack.Pop, Split, List.nil_append, List.cons_append] at e7
  rw [e7] at hp
  rw [pref_head_unique hp (pref_append [x7] devm7.stack)] at hp
  replace hp := cons_pref_cons_inv hp
  -- state is unchanged by the seven pops
  have h_st7 : s.state = devm7.state :=
    ((Devm.pop_of_pop eq1).state).trans
      (((Devm.pop_of_pop h_pop2).state).trans
        (((Devm.pop_of_pop eq3).state).trans
          ((h_pop4.state).trans
            ((h_pop5.state).trans ((h_pop6.state).trans h_pop7.state)))))
  clear e1 e2 e3 e4 e5 e6 e7 eq1 eq2 eq3 eq4 eq5 eq6 eq7 h_pop2 h_pop4 h_pop5 h_pop6 h_pop7
  -- delegation resolution
  rcases hp11 : accessDelegation (addAccessedAddress devm7 callee) callee with
    ⟨dp, na, code0, dagc, devm9⟩
  simp only [hp11] at h_run
  have h_code0 :
      code0 = (accessDelegation (addAccessedAddress devm7 callee) callee).2.2.1 := by
    rw [hp11]
  have h_st9 : devm9.state = devm7.state := by
    have h := congrArg (fun q => (q.2.2.2.2 : Devm).state) hp11
    dsimp at h
    rw [← h, accessDelegation_state]
    rfl
  have h_stk9 : devm9.stack = devm7.stack := by
    have h := congrArg (fun q => (q.2.2.2.2 : Devm).stack) hp11
    dsimp at h
    rw [← h, accessDelegation_stack]
    rfl
  -- charge the call gas
  split at h_run
  · cases XStep.run_ofExcept_error h_run
  rename_i devm10 eq16
  have h_st10 : devm9.state = devm10.state := (Devm.burn_of_chargeGas eq16).state
  have h_stk10 : devm9.stack = devm10.stack := (Devm.burn_of_chargeGas eq16).stack
  have h_st11 :
      (devm10.memExtends [(inputIndex, inputSize), (outputIndex, outputSize)]).state
        = s.state := by
    show devm10.state = s.state
    rw [← h_st10, h_st9, ← h_st7]
  have h_stk11 :
      (devm10.memExtends [(inputIndex, inputSize), (outputIndex, outputSize)]).stack
        = devm7.stack := by
    show devm10.stack = devm7.stack
    rw [← h_stk10, h_stk9]
  have h_st_devm7 : devm7.state = s.state := h_st7.symm
  clear h_st10 h_st9 h_stk10 h_stk9 eq16 h_st7
  -- static-context assertion
  split at h_run
  case h_1 => cases XStep.run_ofExcept_error h_run
  case h_2 =>
  split at h_run
  · -- insufficient balance : call fails, state unchanged
    split at h_run
    case h_1 => cases XStep.run_ofExcept_error h_run
    case h_2 =>
    rename_i devm12 eq20
    have h_ex := Except.ok.inj h_run.2
    rw [h_ex]
    constructor
    · rw [getStor_eq_of_state_eq (show ((devm12.withReturnData []).withGasLeft _).state
        = s.state by
          show devm12.state = s.state
          rw [← (Devm.push_of_push eq20).state]; exact h_st11)]
      exact h_cons
    · refine ⟨0, ?_⟩
      have h_stk := (Devm.push_of_push eq20).stack
      show (0 :: xs) <<+ ((devm12.withReturnData []).withGasLeft _).stack
      show (0 :: xs) <<+ devm12.stack
      rw [h_stk, h_stk11]
      exact pref_cons hp
  · -- balance is sufficient : the call goes through
    simp only [genericCall.step] at h_run
    split at h_run
    · -- depth limit reached : call fails, state unchanged
      simp only [Bind.bind, Except.bind] at h_run
      split at h_run
      case h_1 => cases XStep.run_ofExcept_error h_run
      case h_2 =>
      rename_i devm12 h_push
      have h_ex := Except.ok.inj h_run.2
      rw [h_ex]
      constructor
      · rw [getStor_eq_of_state_eq (show devm12.state = s.state by
          rw [← (Devm.push_of_push h_push).state]; exact h_st11)]
        exact h_cons
      · refine ⟨0, ?_⟩
        have h_stk := (Devm.push_of_push h_push).stack
        show (0 :: xs) <<+ devm12.stack
        rw [h_stk]
        show (0 :: xs) <<+ 0 ::
          ((devm10.memExtends [(inputIndex, inputSize), (outputIndex, outputSize)]).withReturnData
            []).stack
        rw [show ((devm10.memExtends [(inputIndex, inputSize),
          (outputIndex, outputSize)]).withReturnData []).stack
          = devm7.stack from h_stk11]
        exact pref_cons hp
    · -- the call is executed
      rename_i h_depth_ne
      simp only [XStep.Run] at h_run
      rcases h_run with ⟨ex', run_pm₀, h_split⟩
      -- name the child message and keep only the projections we need
      obtain ⟨childMsg, run_pm, hc_stv, hc_state, hc_caller, hc_value, hc_ct,
          hc_ca, hc_code, hc_depth⟩ :
          ∃ m : Msg, ProcessMessage m xl ex' ∧
            m.shouldTransferValue = true ∧ m.benv.state = s.state ∧
            m.caller = sevm.currentTarget ∧ m.value = value ∧
            m.currentTarget = callee ∧ m.codeAddress = some na ∧
            m.code = code0 ∧ m.depth = sevm.depth - 1 :=
        ⟨_, run_pm₀, rfl, h_st11, rfl, rfl, rfl, rfl, rfl, rfl⟩
      clear run_pm₀
      -- the sub-message result must be ok
      rcases ex' with err' | child
      · cases Resume.call_run_error h_split.symm
      have h_sf_state : sf.state = child.state := Resume.call_state h_split.symm
      rcases Resume.call_stack h_split.symm with ⟨b, h_sf_stack⟩
      -- the stack conclusion, once and for all: the resume pushes one flag on
      -- the parent's stack, which still carries `xs`
      have h_stack_out : ∃ b', (b' :: xs) <<+ sf.stack := by
        refine ⟨b, ?_⟩
        rw [h_sf_stack]
        show (b :: xs) <<+ b ::
          ((devm10.memExtends [(inputIndex, inputSize), (outputIndex, outputSize)]).withReturnData
            []).stack
        rw [show ((devm10.memExtends [(inputIndex, inputSize),
          (outputIndex, outputSize)]).withReturnData []).stack
          = devm7.stack from h_stk11]
        exact pref_cons hp
      refine ⟨?_, h_stack_out⟩
      -- unpack the process-message run
      obtain ⟨r0, hbody, hset⟩ := ProcessMessage.iff_body.mp run_pm
      unfold FrameBody at hbody
      rcases eq_bt : childMsg.benvAfterTransfer with e | benv' <;>
        rw [eq_bt] at hbody
      · rw [hbody.2, processMessage.settle_error] at hset
        cases hset
      have run_ec : ExecuteCode (childMsg.withBenv benv') xl r0 := hbody
      -- the value transfer performed before the sub-message run
      rcases of_benvAfterTransfer hc_stv eq_bt with ⟨st_mid, h_sub, hB⟩
      rw [hc_state, hc_caller, hc_value] at h_sub
      rcases of_state_transfer_fields (callee := callee) h_sub with
        ⟨h_t_stor, h_t_code, -, -, -⟩
      have hBs : benv'.state = st_mid.addBal callee value := by
        rw [hB, hc_ct, hc_value]; rfl
      -- resolve the inner split : either rollback or a clean sub-message result
      obtain ⟨evm2, h_r0, h_settle⟩ := processMessage.settle_ok_cases hset.symm
      subst h_r0
      rcases h_settle with ⟨h_err2, h_if⟩ | ⟨h_err2, h_if⟩
      · -- sub-message failed : state rolled back to the pre-transfer state
        rw [getStor_eq_of_state_eq (show sf.state = s.state by
          rw [h_sf_state, ← h_if]; exact hc_state)]
        exact h_cons
      -- sub-message succeeded
      have h_if' := h_if.symm
      subst h_if'
      have h_wb_ca : (childMsg.withBenv benv').codeAddress = some na := hc_ca
      rcases of_executeCode_someCode h_wb_ca run_ec with
        ⟨h_prec, h_xl_none, h_he⟩ | ⟨h_prec, ex''', h_xl_some, h_he⟩
      · -- callee is a precompile : no sub-execution, only the transfer
        have h_child_state : child.state = benv'.state := by
          have h := state_of_executePrecomp_ok h_he h_err2
          rw [h]; rfl
        have h_stor_eq : Devm.getStor sf sevm.currentTarget
            = Devm.getStor s sevm.currentTarget := by
          show (sf.state.get sevm.currentTarget).stor = (s.state.get sevm.currentTarget).stor
          rw [h_sf_state, h_child_state, hBs]
          exact h_t_stor sevm.currentTarget
        rw [h_stor_eq]
        exact h_cons
      · -- callee is a regular account : a sub-execution takes place
        rw [h_xl_some] at h_fill
        dsimp only [Xlot.Filled] at h_fill
        rcases ex''' with ⟨err3, d3⟩ | child3
        · -- sub-execution error : contradicts the clean sub-message result
          rcases of_handleError_err h_he with ⟨evm4, h_ok4, h_some4, -⟩ | ⟨e, h_err4⟩
          · have h_ok4 := Except.ok.inj h_ok4
            rw [← h_ok4] at h_some4
            exact absurd h_some4 h_err2
          · cases h_err4
        -- clean sub-execution : apply the induction hypothesis
        simp only [executeCode.handleError] at h_he
        have h_he := (Except.ok.inj h_he).symm
        subst h_he
        obtain ⟨ex_sub⟩ := h_fill
        -- projections of the sub-message's initial sevm/devm
        have h_sd_state : (initDevm (childMsg.withBenv benv')).state = benv'.state := rfl
        have h_ss_ct : (initSevm (childMsg.withBenv benv')).currentTarget = callee := hc_ct
        -- code at the contract's address is the fmint code
        have h_code_at :
            some ((initDevm (childMsg.withBenv benv')).getCode sevm.currentTarget).toList
              = Prog.compile Fmint.fmint := by
          show some ((initDevm (childMsg.withBenv benv')).state.get sevm.currentTarget).code.toList
            = Prog.compile Fmint.fmint
          rw [h_sd_state, hBs, h_t_code sevm.currentTarget]
          exact h_code
        -- the target program invariant for the sub-execution
        have h_at : Prog.At Fmint.fmint sevm.currentTarget 0
            (initSevm (childMsg.withBenv benv')) (initDevm (childMsg.withBenv benv')) := by
          refine ⟨h_code_at, ?_⟩
          intro h_eq_ct
          rw [h_ss_ct] at h_eq_ct
          refine ⟨?_, rfl⟩
          show some (initSevm (childMsg.withBenv benv')).code.toList = Prog.compile Fmint.fmint
          have h_code_c : (initSevm (childMsg.withBenv benv')).code = code0 := hc_code
          rw [h_code_c, h_code0]
          have h_ad : (addAccessedAddress devm7 callee).state.getCode callee
              = s.getCode sevm.currentTarget := by
            show devm7.state.getCode callee = s.getCode sevm.currentTarget
            rw [h_st_devm7, h_eq_ct]; rfl
          have h_notdel : ¬ isValidDelegation
              ((addAccessedAddress devm7 callee).state.getCode callee) := by
            rw [h_ad]; exact not_delegation_of_compile h_code
          rw [accessDelegation_code_of_not h_notdel, h_ad]
          exact h_code
        -- the depth of the sub-execution is strictly smaller
        have h_depth_lt : (initSevm (childMsg.withBenv benv')).depth < sevm.depth := by
          have h_dep : (initSevm (childMsg.withBenv benv')).depth = sevm.depth - 1 := hc_depth
          rw [h_dep]; omega
        -- the precondition holds for the sub-message
        have h_gs : Devm.getStor (initDevm (childMsg.withBenv benv')) sevm.currentTarget
            = Devm.getStor s sevm.currentTarget := by
          show ((initDevm (childMsg.withBenv benv')).state.get sevm.currentTarget).stor
            = (s.state.get sevm.currentTarget).stor
          rw [h_sd_state, hBs]
          exact h_t_stor sevm.currentTarget
        have h_precond : fmintSpec.Pre sevm.currentTarget
            (initSevm (childMsg.withBenv benv')) (initDevm (childMsg.withBenv benv')) := by
          refine ⟨h_code_at, trivial, ?_⟩
          apply fmintSpec_preInv_iff.mpr
          rw [h_gs]
          exact h_cons
        -- apply the induction hypothesis
        have hpost : fmintSpec.Post sevm.currentTarget
            (initSevm (childMsg.withBenv benv')) child :=
          ih 0 (initSevm (childMsg.withBenv benv')) (initDevm (childMsg.withBenv benv'))
            (.ok child) ex_sub h_depth_lt h_at ⟨h_precond, fun _ => Mem.wf_empty⟩
        have h_post_cons : Stor.Conserved (Devm.getStor child sevm.currentTarget) :=
          fmintSpec_postInv_iff.mp hpost.inv
        rw [getStor_eq_of_state_eq h_sf_state sevm.currentTarget]
        exact h_post_cons

lemma supplySlot_eq_not_zero : (~~~ (0 : B256)) = supplySlot := by decide

/-- **The burn pair.**  `burnAndReturn` decreases the receiver's balance by
`wad` and the supply by the same `wad`, with the balance check as its only
guard; the supply-side bound comes from the invariant itself. -/
lemma of_burnAndReturn {fs : List Func} {sevm : Sevm} {s r : Devm} {wad receiver : B256}
    (h_va : ValidAdr receiver)
    (hs : [wad, receiver] <<+ s.stack)
    (h : Stor.Conserved (Devm.getStor s sevm.currentTarget))
    (h_run : Func.Run fs sevm s burnAndReturn r) :
    Stor.Conserved (Devm.getStor r sevm.currentTarget) := by
  rcases h_va with ⟨a, rfl⟩
  simp only [burnAndReturn] at h_run
  -- dup 1 : [a.toB256, wad, a.toB256]
  rcases of_run_next h_run with ⟨s1, r1, h_run⟩
  rcases of_run_dup r1 with ⟨y, hy1, pb1⟩
  have hy1' : y = a.toB256 := by
    have h_get : s.stack[(1 : Fin 16).val]? = some a.toB256 :=
      Stack.nth_getElem (Stack.Nth.tail 0 a.toB256 wad [a.toB256]
        (Stack.Nth.head a.toB256 [])) hs
    rw [h_get] at hy1; injection hy1 with hy1; exact hy1.symm
  subst y
  have hs1 : [a.toB256, wad, a.toB256] <<+ s1.stack := prefix_of_push pb1 hs
  have hg : Devm.getStor s = Devm.getStor s1 :=
    Line.of_inv Devm.getStor (by line_inv) (Line.Run.cons r1 Line.Run.nil)
  clear r1 pb1 hs
  -- sload : [rbal, wad, a.toB256]
  rcases of_run_next h_run with ⟨s2, r2, h_run⟩
  rcases prefix_of_sload r2 hs1 with ⟨rbal, hs2, h_rbal⟩
  have h_rbal' : rbal = (Devm.getStor s sevm.currentTarget).get a.toB256 := by
    rw [h_rbal]
    show (Devm.getStor s1 sevm.currentTarget).get a.toB256 = _
    rw [← congr_fun hg sevm.currentTarget]
  clear h_rbal
  have hg := hg.trans (Line.of_inv Devm.getStor (by line_inv) (Line.Run.cons r2 Line.Run.nil))
  clear r2 hs1
  -- dup 1 : [wad, rbal, wad, a.toB256]
  rcases of_run_next h_run with ⟨s3, r3, h_run⟩
  rcases of_run_dup r3 with ⟨y, hy3, pb3⟩
  have hy3' : y = wad := by
    have h_get : s2.stack[(1 : Fin 16).val]? = some wad :=
      Stack.nth_getElem (Stack.Nth.tail 0 wad rbal [wad, a.toB256]
        (Stack.Nth.head wad [a.toB256])) hs2
    rw [h_get] at hy3; injection hy3 with hy3; exact hy3.symm
  subst y
  have hs3 : [wad, rbal, wad, a.toB256] <<+ s3.stack := prefix_of_push pb3 hs2
  have hg := hg.trans (Line.of_inv Devm.getStor (by line_inv) (Line.Run.cons r3 Line.Run.nil))
  clear r3 pb3
  -- dup 1 : [rbal, wad, rbal, wad, a.toB256]
  rcases of_run_next h_run with ⟨s4, r4, h_run⟩
  rcases of_run_dup r4 with ⟨y, hy4, pb4⟩
  have hy4' : y = rbal := by
    have h_get : s3.stack[(1 : Fin 16).val]? = some rbal :=
      Stack.nth_getElem (Stack.Nth.tail 0 rbal wad [rbal, wad, a.toB256]
        (Stack.Nth.head rbal [wad, a.toB256])) hs3
    rw [h_get] at hy4; injection hy4 with hy4; exact hy4.symm
  subst y
  have hs4 : [rbal, wad, rbal, wad, a.toB256] <<+ s4.stack := prefix_of_push pb4 hs3
  have hg := hg.trans (Line.of_inv Devm.getStor (by line_inv) (Line.Run.cons r4 Line.Run.nil))
  clear r4 pb4 hs3
  -- lt : [(rbal <? wad), wad... wait: lt pops rbal, wad → rbal <? wad
  rcases of_run_next h_run with ⟨s5, r5, h_run⟩
  have hs5 : (rbal <? wad) :: [rbal, wad, a.toB256] <<+ s5.stack := prefix_of_lt r5 hs4
  have hg := hg.trans (Line.of_inv Devm.getStor (by line_inv) (Line.Run.cons r5 Line.Run.nil))
  clear r5 hs4
  -- revert-branch : a.toB256 balance covers the burn
  rcases of_run_branch_revert h_run with ⟨s6, hp6, h_run⟩
  have hp6s := hp6.stack
  simp only [Stack.Pop, Split, List.nil_append, List.cons_append] at hp6s
  rw [hp6s] at hs5
  have h_ltflag : (rbal <? wad) = 0 := pref_head_unique hs5 (pref_append [0] s6.stack)
  have h_le : wad ≤ rbal := by
    rw [← B256.not_lt]; intro hlt
    rw [B256.ltCheck, if_pos hlt] at h_ltflag
    exact B256.zero_ne_one h_ltflag.symm
  rw [h_ltflag] at hs5
  have hs6 : [rbal, wad, a.toB256] <<+ s6.stack := cons_pref_cons_inv hs5
  have hg := hg.trans (funext (fun a => (Devm.PopBurn.getStor hp6 a).symm))
  clear hs5 hp6s hp6 h_ltflag
  -- dup 1 : [wad, rbal, wad, a.toB256]
  rcases of_run_next h_run with ⟨s7, r7, h_run⟩
  rcases of_run_dup r7 with ⟨y, hy7, pb7⟩
  have hy7' : y = wad := by
    have h_get : s6.stack[(1 : Fin 16).val]? = some wad :=
      Stack.nth_getElem (Stack.Nth.tail 0 wad rbal [wad, a.toB256]
        (Stack.Nth.head wad [a.toB256])) hs6
    rw [h_get] at hy7; injection hy7 with hy7; exact hy7.symm
  subst y
  have hs7 : [wad, rbal, wad, a.toB256] <<+ s7.stack := prefix_of_push pb7 hs6
  have hg := hg.trans (Line.of_inv Devm.getStor (by line_inv) (Line.Run.cons r7 Line.Run.nil))
  clear r7 pb7 hs6
  -- swap 0 : [rbal, wad, wad, a.toB256]
  rcases of_run_next h_run with ⟨s8, r8, h_run⟩
  have h_swap8 : Stack.Swap (0 : Fin 16).val [wad, rbal] [rbal, wad] := Stack.swapCore_zero
  have hs8 : [rbal, wad, wad, a.toB256] <<+ s8.stack := by
    have h_swap8' : Stack.Swap (0 : Fin 16).val [wad, rbal, wad, a.toB256]
        [rbal, wad, wad, a.toB256] := Stack.swapCore_zero
    exact Stack.prefix_of_swap h_swap8' (of_run_swap r8) hs7
  have hg := hg.trans (Line.of_inv Devm.getStor (by line_inv) (Line.Run.cons r8 Line.Run.nil))
  clear r8 hs7
  -- sub : [(rbal - wad), wad, a.toB256]
  rcases of_run_next h_run with ⟨s9, r9, h_run⟩
  have hs9 : (rbal - wad) :: [wad, a.toB256] <<+ s9.stack := prefix_of_sub r9 hs8
  have hg := hg.trans (Line.of_inv Devm.getStor (by line_inv) (Line.Run.cons r9 Line.Run.nil))
  clear r9 hs8
  -- dup 2 : [a.toB256, (rbal - wad), wad, a.toB256]
  rcases of_run_next h_run with ⟨s10, r10, h_run⟩
  rcases of_run_dup r10 with ⟨y, hy10, pb10⟩
  have hy10' : y = a.toB256 := by
    have h_get : s9.stack[(2 : Fin 16).val]? = some a.toB256 :=
      Stack.nth_getElem
        (Stack.Nth.tail 1 a.toB256 (rbal - wad) [wad, a.toB256]
          (Stack.Nth.tail 0 a.toB256 wad [a.toB256] (Stack.Nth.head a.toB256 []))) hs9
    rw [h_get] at hy10; injection hy10 with hy10; exact hy10.symm
  subst y
  have hs10 : [a.toB256, rbal - wad, wad, a.toB256] <<+ s10.stack := prefix_of_push pb10 hs9
  have hg := hg.trans (Line.of_inv Devm.getStor (by line_inv) (Line.Run.cons r10 Line.Run.nil))
  clear r10 pb10 hs9
  -- sstore : the balance write
  rcases of_run_next h_run with ⟨s11, r11, h_run⟩
  have h_set1 : Devm.getStor s11 sevm.currentTarget
      = (Devm.getStor s10 sevm.currentTarget).set a.toB256 (rbal - wad) :=
    sstore_getStor_set r11 hs10
  have hs11 : [wad, a.toB256] <<+ s11.stack := prefix_of_sstore r11 hs10
  clear r11 hs10
  -- pushSupplySlot = [pushB256 0, not] : [supplySlot, wad, a.toB256]
  rcases of_run_prepend pushSupplySlot _ h_run with ⟨s12, h12, h_run⟩
  have hs12 : Fmint.supplySlot :: [wad, a.toB256] <<+ s12.stack := by
    simp only [pushSupplySlot] at h12
    rcases Line.of_run_cons h12 with ⟨sa, ra, h12'⟩
    rcases Line.of_run_cons h12' with ⟨sb, rb, hnil⟩
    cases hnil
    have hpa : (0 : B256) :: [wad, a.toB256] <<+ sa.stack :=
      prefix_of_push (of_run_pushB256 ra) hs11
    have hpb := prefix_of_not rb hpa
    rw [supplySlot_eq_not_zero] at hpb
    exact hpb
  have hg2 : Devm.getStor s11 = Devm.getStor s12 :=
    Line.of_inv Devm.getStor (by line_inv) h12
  clear h12 hs11
  -- sload : [supply, wad, a.toB256]
  rcases of_run_next h_run with ⟨s13, r13, h_run⟩
  rcases prefix_of_sload r13 hs12 with ⟨supply, hs13, h_supply⟩
  have h_supply' : supply
      = ((Devm.getStor s sevm.currentTarget).set a.toB256 (rbal - wad)).get
          Fmint.supplySlot := by
    rw [h_supply]
    show (Devm.getStor s12 sevm.currentTarget).get Fmint.supplySlot = _
    rw [← congr_fun hg2 sevm.currentTarget, h_set1, ← congr_fun hg sevm.currentTarget]
  clear h_supply
  have hg2 := hg2.trans (Line.of_inv Devm.getStor (by line_inv) (Line.Run.cons r13 Line.Run.nil))
  clear r13 hs12
  -- dup 1 : [wad, supply, wad, a.toB256]
  rcases of_run_next h_run with ⟨s14, r14, h_run⟩
  rcases of_run_dup r14 with ⟨y, hy14, pb14⟩
  have hy14' : y = wad := by
    have h_get : s13.stack[(1 : Fin 16).val]? = some wad :=
      Stack.nth_getElem (Stack.Nth.tail 0 wad supply [wad, a.toB256]
        (Stack.Nth.head wad [a.toB256])) hs13
    rw [h_get] at hy14; injection hy14 with hy14; exact hy14.symm
  subst y
  have hs14 : [wad, supply, wad, a.toB256] <<+ s14.stack := prefix_of_push pb14 hs13
  have hg2 := hg2.trans (Line.of_inv Devm.getStor (by line_inv) (Line.Run.cons r14 Line.Run.nil))
  clear r14 pb14 hs13
  -- swap 0 : [supply, wad, wad, a.toB256]
  rcases of_run_next h_run with ⟨s15, r15, h_run⟩
  have hs15 : [supply, wad, wad, a.toB256] <<+ s15.stack := by
    have h_swap15 : Stack.Swap (0 : Fin 16).val [wad, supply, wad, a.toB256]
        [supply, wad, wad, a.toB256] := Stack.swapCore_zero
    exact Stack.prefix_of_swap h_swap15 (of_run_swap r15) hs14
  have hg2 := hg2.trans (Line.of_inv Devm.getStor (by line_inv) (Line.Run.cons r15 Line.Run.nil))
  clear r15 hs14
  -- sub : [(supply - wad), wad, a.toB256]
  rcases of_run_next h_run with ⟨s16, r16, h_run⟩
  have hs16 : (supply - wad) :: [wad, a.toB256] <<+ s16.stack := prefix_of_sub r16 hs15
  have hg2 := hg2.trans (Line.of_inv Devm.getStor (by line_inv) (Line.Run.cons r16 Line.Run.nil))
  clear r16 hs15
  -- pushSupplySlot : [supplySlot, (supply - wad), wad, a.toB256]
  rcases of_run_prepend pushSupplySlot _ h_run with ⟨s17, h17, h_run⟩
  have hs17 : Fmint.supplySlot :: (supply - wad) :: [wad, a.toB256] <<+ s17.stack := by
    simp only [pushSupplySlot] at h17
    rcases Line.of_run_cons h17 with ⟨sa, ra, h17'⟩
    rcases Line.of_run_cons h17' with ⟨sb, rb, hnil⟩
    cases hnil
    have hpa : (0 : B256) :: (supply - wad) :: [wad, a.toB256] <<+ sa.stack :=
      prefix_of_push (of_run_pushB256 ra) hs16
    have hpb := prefix_of_not rb hpa
    rw [supplySlot_eq_not_zero] at hpb
    exact hpb
  have hg2 := hg2.trans (Line.of_inv Devm.getStor (by line_inv) h17)
  clear h17 hs16
  -- sstore : the supply write, completing the pair
  rcases of_run_next h_run with ⟨s18, r18, h_run⟩
  have h_set2 : Devm.getStor s18 sevm.currentTarget
      = (Devm.getStor s17 sevm.currentTarget).set Fmint.supplySlot (supply - wad) :=
    sstore_getStor_set r18 hs17
  clear r18 hs17
  -- the tail is storage-silent
  have hg3 : Devm.getStor s18 sevm.currentTarget = Devm.getStor r sevm.currentTarget :=
    congr_fun (Func.of_inv Devm.getStor Devm.getStor (by func_inv) h_run) sevm.currentTarget
  -- assemble the burn
  rw [← hg3, h_set2, ← congr_fun hg2 sevm.currentTarget, h_set1,
    ← congr_fun hg sevm.currentTarget]
  rw [h_supply', h_rbal']
  rw [h_rbal'] at h_le
  exact h.burn_set h_le

/-- The aux table locates the burn epilogue where `Func.call burnSlot` points:
`burnSlot = 2` in `fmint.main :: fmintAux`, skipping `main` and the reverting
fallback.  The lookup never inspects `main`, so nothing heavy unfolds. -/
lemma get_burnSlot :
    (fmint.main :: fmintAux)[burnSlot]? = some burnAndReturn := by
  show (fmint.main :: fmintAux)[(2 : Nat)]? = some burnAndReturn
  simp only [fmintAux, List.getElem?_cons_succ, List.getElem?_cons_zero]

/-- `storeCallbackHead` writes the selector and five head words to memory,
consuming the `amount` it was handed. -/
lemma of_storeCallbackHead {e : Sevm} {s s' : Devm} {x xs}
    (hp : x :: xs <<+ s.stack) (h : Line.Run e s storeCallbackHead s') :
    xs <<+ s'.stack := by
  simp only [storeCallbackHead] at h
  rcases Line.of_run_cons h with ⟨t1, q1, h⟩
  have hp1 : onFlashLoanSelector :: x :: xs <<+ t1.stack :=
    prefix_of_push (of_run_pushB256 q1) hp
  rcases of_run_append (mstoreAt 0) h with ⟨t2, q2, h⟩
  have hp2 : x :: xs <<+ t2.stack := prefix_of_mstoreAt q2 hp1
  rcases Line.of_run_cons h with ⟨t3, q3, h⟩
  have hp3 : e.caller.toB256 :: x :: xs <<+ t3.stack :=
    prefix_of_push (of_run_caller q3) hp2
  rcases of_run_append (mstoreAt 1) h with ⟨t4, q4, h⟩
  have hp4 : x :: xs <<+ t4.stack := prefix_of_mstoreAt q4 hp3
  rcases Line.of_run_cons h with ⟨t5, q5, h⟩
  have hp5 : e.currentTarget.toB256 :: x :: xs <<+ t5.stack :=
    prefix_of_push (of_run_address q5) hp4
  rcases of_run_append (mstoreAt 2) h with ⟨t6, q6, h⟩
  have hp6 : x :: xs <<+ t6.stack := prefix_of_mstoreAt q6 hp5
  rcases of_run_append (mstoreAt 3) h with ⟨t7, q7, h⟩
  have hp7 : xs <<+ t7.stack := prefix_of_mstoreAt q7 hp6
  rcases Line.of_run_cons h with ⟨t8, q8, h⟩
  have hp8 : (0 : B256) :: xs <<+ t8.stack := prefix_of_push (of_run_pushB256 q8) hp7
  rcases of_run_append (mstoreAt 4) h with ⟨t9, q9, h⟩
  have hp9 : xs <<+ t9.stack := prefix_of_mstoreAt q9 hp8
  rcases Line.of_run_cons h with ⟨t10, q10, h⟩
  have hp10 : (0xa0 : B256) :: xs <<+ t10.stack := prefix_of_push (of_run_pushB256 q10) hp9
  exact prefix_of_mstoreAt h hp10

/-- `forwardCallbackData` pushes the forwarded tail's length. -/
lemma of_forwardCallbackData {e : Sevm} {s s' : Devm} {xs}
    (hp : xs <<+ s.stack) (h : Line.Run e s forwardCallbackData s') :
    ∃ len, len :: xs <<+ s'.stack := by
  simp only [forwardCallbackData, forwardArgTail] at h
  rcases of_run_append (arg 3) h with ⟨t1, q1, h⟩
  rcases prefix_of_cdl hp q1 with ⟨off, hp1⟩
  rcases Line.of_run_cons h with ⟨t2, q2, h⟩
  have hp2 : (4 : B256) :: off :: xs <<+ t2.stack := prefix_of_push (of_run_pushB256 q2) hp1
  rcases Line.of_run_cons h with ⟨t3, q3, h⟩
  have hp3 := prefix_of_add q3 hp2
  rcases Line.of_run_cons h with ⟨t4, q4, h⟩
  rcases of_run_dup q4 with ⟨y4, hy4, pb4⟩
  have hp4 := prefix_of_push pb4 hp3
  rcases Line.of_run_cons h with ⟨t5, q5, h⟩
  rcases prefix_of_calldataload q5 hp4 with ⟨len, hp5⟩
  rcases Line.of_run_cons h with ⟨t6, q6, h⟩
  rcases of_run_dup q6 with ⟨y6, hy6, pb6⟩
  have hp6 := prefix_of_push pb6 hp5
  rcases of_run_append (mstoreAt 6) h with ⟨t7, q7, h⟩
  have hp7 : len :: (4 + off) :: xs <<+ t7.stack := prefix_of_mstoreAt q7 hp6
  rcases Line.of_run_cons h with ⟨t8, q8, h⟩
  rcases of_run_dup q8 with ⟨y8, hy8, pb8⟩
  have hp8 : y8 :: len :: (4 + off) :: xs <<+ t8.stack := prefix_of_push pb8 hp7
  rcases Line.of_run_cons h with ⟨t9, q9, h⟩
  have hp9 : (4 + off) :: len :: y8 :: xs <<+ t9.stack := by
    have h_swap : Stack.Swap (1 : Fin 16).val
        (y8 :: len :: (4 + off) :: xs) ((4 + off) :: len :: y8 :: xs) := by
      apply Stack.swapCore_succ
      apply Stack.swapCore_zero
    exact Stack.prefix_of_swap h_swap (of_run_swap q9) hp8
  rcases Line.of_run_cons h with ⟨t10, q10, h⟩
  have hp10 : (32 : B256) :: (4 + off) :: len :: y8 :: xs <<+ t10.stack :=
    prefix_of_push (of_run_pushB256 q10) hp9
  rcases Line.of_run_cons h with ⟨t11, q11, h⟩
  have hp11 := prefix_of_add q11 hp10
  rcases Line.of_run_cons h with ⟨t12, q12, h⟩
  have hp12 : ((6 + 1) * 32 : B256) :: (32 + (4 + off)) :: len :: y8 :: xs <<+ t12.stack :=
    prefix_of_push (of_run_pushB256 q12) hp11
  rcases Line.of_run_cons h with ⟨t13, q13, hnil⟩
  cases hnil
  exact ⟨y8, prefix_of_calldatacopy q13 hp12⟩

/-- `callbackArgsSize` turns the length into the `CALL`'s `argsSize`. -/
lemma of_callbackArgsSize {e : Sevm} {s s' : Devm} {x xs}
    (hp : x :: xs <<+ s.stack) (h : Line.Run e s callbackArgsSize s') :
    ∃ y, y :: xs <<+ s'.stack := by
  simp only [callbackArgsSize] at h
  rcases Line.of_run_cons h with ⟨u1, q1, h⟩
  have hp1 : (31 : B256) :: x :: xs <<+ u1.stack := prefix_of_push (of_run_pushB256 q1) hp
  rcases Line.of_run_cons h with ⟨u2, q2, h⟩
  have hp2 := prefix_of_add q2 hp1
  rcases Line.of_run_cons h with ⟨u3, q3, h⟩
  have hp3 : (31 : B256) :: (31 + x) :: xs <<+ u3.stack :=
    prefix_of_push (of_run_pushB256 q3) hp2
  rcases Line.of_run_cons h with ⟨u4, q4, h⟩
  have hp4 := prefix_of_not q4 hp3
  rcases Line.of_run_cons h with ⟨u5, q5, h⟩
  have hp5 := prefix_of_and q5 hp4
  rcases Line.of_run_cons h with ⟨u6, q6, h⟩
  have hp6 : (0xc4 : B256) :: ((~~~ (31 : B256)) &&& (31 + x)) :: xs <<+ u6.stack :=
    prefix_of_push (of_run_pushB256 q6) hp5
  rcases Line.of_run_cons h with ⟨u7, q7, hnil⟩
  cases hnil
  exact ⟨_, prefix_of_add q7 hp6⟩

/-- **The repayment.**  `spendAllowanceThenBurn` spends the allowance
`receiver → address(this)` — writing at most one guarded slot — and both arms
converge on `burnAndReturn`.  The infinite (`isMax`) arm writes nothing; the
finite arm writes one slot `checkSlotCollides` has shown to be in neither
storage region the invariant reads. -/
lemma of_spendAllowanceThenBurn {sevm : Sevm} {s r : Devm} {wad receiver : B256}
    (h_va : ValidAdr receiver)
    (hs : [wad, receiver] <<+ s.stack)
    (h : Stor.Conserved (Devm.getStor s sevm.currentTarget))
    (h_run : Func.Run (fmint.main :: fmintAux) sevm s spendAllowanceThenBurn r) :
    Stor.Conserved (Devm.getStor r sevm.currentTarget) := by
  simp only [spendAllowanceThenBurn] at h_run
  -- dup 1 : [receiver, wad, receiver]
  rcases of_run_next h_run with ⟨s1, r1, h_run⟩
  rcases of_run_dup r1 with ⟨y, hy1, pb1⟩
  have hy1' : y = receiver := by
    have h_get : s.stack[(1 : Fin 16).val]? = some receiver :=
      Stack.nth_getElem (Stack.Nth.tail 0 receiver wad [receiver]
        (Stack.Nth.head receiver [])) hs
    rw [h_get] at hy1; injection hy1 with hy1; exact hy1.symm
  subst y
  have hs1 : [receiver, wad, receiver] <<+ s1.stack := prefix_of_push pb1 hs
  have hg : Devm.getStor s = Devm.getStor s1 :=
    Line.of_inv Devm.getStor (by line_inv) (Line.Run.cons r1 Line.Run.nil)
  clear r1 pb1 hs
  -- mstoreAt 0 : [wad, receiver]
  rcases of_run_prepend (mstoreAt 0) _ h_run with ⟨s2, h2, h_run⟩
  have hs2 : [wad, receiver] <<+ s2.stack := by generalize_line_prefix
  have hg := hg.trans (Line.of_inv Devm.getStor (by line_inv) h2)
  clear h2 hs1
  -- address : [self, wad, receiver]
  rcases of_run_next h_run with ⟨s3, r3, h_run⟩
  have hs3 : sevm.currentTarget.toB256 :: [wad, receiver] <<+ s3.stack :=
    prefix_of_push (of_run_address r3) hs2
  have hg := hg.trans (Line.of_inv Devm.getStor (by line_inv) (Line.Run.cons r3 Line.Run.nil))
  clear r3 hs2
  -- mstoreAt 1 : [wad, receiver]
  rcases of_run_prepend (mstoreAt 1) _ h_run with ⟨s4, h4, h_run⟩
  have hs4 : [wad, receiver] <<+ s4.stack := by generalize_line_prefix
  have hg := hg.trans (Line.of_inv Devm.getStor (by line_inv) h4)
  clear h4 hs3
  -- pushList [64, 0] : [0, 64, wad, receiver]
  rcases of_run_prepend (pushList [64, 0]) _ h_run with ⟨s5, h5, h_run⟩
  have hs5 : [0, 64, wad, receiver] <<+ s5.stack := by generalize_line_prefix
  have hg := hg.trans (Line.of_inv Devm.getStor (by line_inv) h5)
  clear h5 hs4
  -- keccak256 : [hash, wad, receiver]
  rcases of_run_next h_run with ⟨s6, r6, h_run⟩
  rcases prefix_of_keccak256 r6 hs5 with ⟨hash, hs6⟩
  have hg := hg.trans (Line.of_inv Devm.getStor (by line_inv) (Line.Run.cons r6 Line.Run.nil))
  clear r6 hs5
  -- checkSlotCollides : [collides?, hash, wad, receiver]
  rcases of_run_prepend checkSlotCollides _ h_run with ⟨s7, h7, h_run⟩
  rcases of_checkSlotCollides hs6 h7 with ⟨coll, hs7, h_guard⟩
  have hg := hg.trans (Line.of_inv Devm.getStor (by line_inv) h7)
  clear h7 hs6
  -- revert-branch : the slot aliases neither region
  rcases of_run_branch_revert h_run with ⟨s8, hp8, h_run⟩
  have hp8s := hp8.stack
  simp only [Stack.Pop, Split, List.nil_append, List.cons_append] at hp8s
  rw [hp8s] at hs7
  have h_coll : coll = 0 := pref_head_unique hs7 (pref_append [0] s8.stack)
  obtain ⟨h_nva, h_nsup⟩ := h_guard h_coll
  rw [h_coll] at hs7
  have hs8 : [hash, wad, receiver] <<+ s8.stack := cons_pref_cons_inv hs7
  have hg := hg.trans (funext (fun a => (Devm.PopBurn.getStor hp8 a).symm))
  clear hs7 hp8s hp8 h_guard h_coll
  -- dup 0 : [hash, hash, wad, receiver]
  rcases of_run_next h_run with ⟨s9, r9, h_run⟩
  rcases of_run_dup r9 with ⟨y, hy9, pb9⟩
  have hy9' : y = hash := by
    have h_get : s8.stack[(0 : Fin 16).val]? = some hash :=
      Stack.nth_getElem (Stack.Nth.head hash [wad, receiver]) hs8
    rw [h_get] at hy9; injection hy9 with hy9; exact hy9.symm
  subst y
  have hs9 : [hash, hash, wad, receiver] <<+ s9.stack := prefix_of_push pb9 hs8
  have hg := hg.trans (Line.of_inv Devm.getStor (by line_inv) (Line.Run.cons r9 Line.Run.nil))
  clear r9 pb9 hs8
  -- sload : [amnt, hash, wad, receiver]
  rcases of_run_next h_run with ⟨s10, r10, h_run⟩
  rcases prefix_of_sload r10 hs9 with ⟨amnt, hs10, -⟩
  have hg := hg.trans (Line.of_inv Devm.getStor (by line_inv) (Line.Run.cons r10 Line.Run.nil))
  clear r10 hs9
  -- dup 0 : [amnt, amnt, hash, wad, receiver]
  rcases of_run_next h_run with ⟨s11, r11, h_run⟩
  rcases of_run_dup r11 with ⟨y, hy11, pb11⟩
  have hy11' : y = amnt := by
    have h_get : s10.stack[(0 : Fin 16).val]? = some amnt :=
      Stack.nth_getElem (Stack.Nth.head amnt [hash, wad, receiver]) hs10
    rw [h_get] at hy11; injection hy11 with hy11; exact hy11.symm
  subst y
  have hs11 : [amnt, amnt, hash, wad, receiver] <<+ s11.stack := prefix_of_push pb11 hs10
  have hg := hg.trans (Line.of_inv Devm.getStor (by line_inv) (Line.Run.cons r11 Line.Run.nil))
  clear r11 pb11 hs10
  -- isMax = [not, iszero] : [(amnt =? max), amnt, hash, wad, receiver]
  rcases of_run_prepend isMax _ h_run with ⟨s12, h12, h_run⟩
  rcases Line.of_run_cons h12 with ⟨sa, rNot, h12'⟩
  rcases Line.of_run_cons h12' with ⟨sb, rIsz, hnil⟩
  cases hnil
  have hsa : (~~~ amnt) :: [amnt, hash, wad, receiver] <<+ sa.stack := prefix_of_not rNot hs11
  have hs12 : ((~~~ amnt) =? 0) :: [amnt, hash, wad, receiver] <<+ s12.stack :=
    prefix_of_iszero rIsz hsa
  have hg := hg.trans (Line.of_inv Devm.getStor (by line_inv) h12)
  clear h12 rNot rIsz hsa hs11
  -- the isMax branch : infinite arm keeps the allowance, finite arm decrements
  rcases of_run_branch h_run with
    ⟨s13, hp13, h_run⟩ | ⟨w13, s13, s14, h_ne13, hp13, hb13, h_run⟩
  · -- FINITE ARM : the flag is 0
    have hp13s := hp13.stack
    simp only [Stack.Pop, Split, List.nil_append, List.cons_append] at hp13s
    rw [hp13s] at hs12
    have h_flag : ((~~~ amnt) =? 0) = 0 := pref_head_unique hs12 (pref_append [0] s13.stack)
    rw [h_flag] at hs12
    have hs13 : [amnt, hash, wad, receiver] <<+ s13.stack := cons_pref_cons_inv hs12
    have hg := hg.trans (funext (fun a => (Devm.PopBurn.getStor hp13 a).symm))
    clear hs12 hp13s hp13 h_flag
    -- dup 2 : [wad, amnt, hash, wad, receiver]
    rcases of_run_next h_run with ⟨s14, r14, h_run⟩
    rcases of_run_dup r14 with ⟨y, hy14, pb14⟩
    have hy14' : y = wad := by
      have h_get : s13.stack[(2 : Fin 16).val]? = some wad :=
        Stack.nth_getElem
          (Stack.Nth.tail 1 wad amnt [hash, wad, receiver]
            (Stack.Nth.tail 0 wad hash [wad, receiver]
              (Stack.Nth.head wad [receiver]))) hs13
      rw [h_get] at hy14; injection hy14 with hy14; exact hy14.symm
    subst y
    have hs14 : [wad, amnt, hash, wad, receiver] <<+ s14.stack := prefix_of_push pb14 hs13
    have hg := hg.trans (Line.of_inv Devm.getStor (by line_inv) (Line.Run.cons r14 Line.Run.nil))
    clear r14 pb14 hs13
    -- dup 1 : [amnt, wad, amnt, hash, wad, receiver]
    rcases of_run_next h_run with ⟨s15, r15, h_run⟩
    rcases of_run_dup r15 with ⟨y, hy15, pb15⟩
    have hy15' : y = amnt := by
      have h_get : s14.stack[(1 : Fin 16).val]? = some amnt :=
        Stack.nth_getElem
          (Stack.Nth.tail 0 amnt wad [amnt, hash, wad, receiver]
            (Stack.Nth.head amnt [hash, wad, receiver])) hs14
      rw [h_get] at hy15; injection hy15 with hy15; exact hy15.symm
    subst y
    have hs15 : [amnt, wad, amnt, hash, wad, receiver] <<+ s15.stack := prefix_of_push pb15 hs14
    have hg := hg.trans (Line.of_inv Devm.getStor (by line_inv) (Line.Run.cons r15 Line.Run.nil))
    clear r15 pb15 hs14
    -- lt : [(amnt <? wad), amnt, hash, wad, receiver]
    rcases of_run_next h_run with ⟨s16, r16, h_run⟩
    have hs16 : (amnt <? wad) :: [amnt, hash, wad, receiver] <<+ s16.stack :=
      prefix_of_lt r16 hs15
    have hg := hg.trans (Line.of_inv Devm.getStor (by line_inv) (Line.Run.cons r16 Line.Run.nil))
    clear r16 hs15
    -- revert-branch : the allowance covers the amount owed
    rcases of_run_branch_revert h_run with ⟨s17, hp17, h_run⟩
    have hp17s := hp17.stack
    simp only [Stack.Pop, Split, List.nil_append, List.cons_append] at hp17s
    rw [hp17s] at hs16
    have h_flag17 : (amnt <? wad) = 0 := pref_head_unique hs16 (pref_append [0] s17.stack)
    rw [h_flag17] at hs16
    have hs17 : [amnt, hash, wad, receiver] <<+ s17.stack := cons_pref_cons_inv hs16
    have hg := hg.trans (funext (fun a => (Devm.PopBurn.getStor hp17 a).symm))
    clear hs16 hp17s hp17 h_flag17
    -- dup 2 : [wad, amnt, hash, wad, receiver]
    rcases of_run_next h_run with ⟨s18, r18, h_run⟩
    rcases of_run_dup r18 with ⟨y, hy18, pb18⟩
    have hy18' : y = wad := by
      have h_get : s17.stack[(2 : Fin 16).val]? = some wad :=
        Stack.nth_getElem
          (Stack.Nth.tail 1 wad amnt [hash, wad, receiver]
            (Stack.Nth.tail 0 wad hash [wad, receiver]
              (Stack.Nth.head wad [receiver]))) hs17
      rw [h_get] at hy18; injection hy18 with hy18; exact hy18.symm
    subst y
    have hs18 : [wad, amnt, hash, wad, receiver] <<+ s18.stack := prefix_of_push pb18 hs17
    have hg := hg.trans (Line.of_inv Devm.getStor (by line_inv) (Line.Run.cons r18 Line.Run.nil))
    clear r18 pb18 hs17
    -- swap 0 : [amnt, wad, hash, wad, receiver]
    rcases of_run_next h_run with ⟨s19, r19, h_run⟩
    have hs19 : [amnt, wad, hash, wad, receiver] <<+ s19.stack := by
      have h_swap : Stack.Swap (0 : Fin 16).val [wad, amnt, hash, wad, receiver]
          [amnt, wad, hash, wad, receiver] := Stack.swapCore_zero
      exact Stack.prefix_of_swap h_swap (of_run_swap r19) hs18
    have hg := hg.trans (Line.of_inv Devm.getStor (by line_inv) (Line.Run.cons r19 Line.Run.nil))
    clear r19 hs18
    -- sub : [(amnt - wad), hash, wad, receiver]
    rcases of_run_next h_run with ⟨s20, r20, h_run⟩
    have hs20 : (amnt - wad) :: [hash, wad, receiver] <<+ s20.stack := prefix_of_sub r20 hs19
    have hg := hg.trans (Line.of_inv Devm.getStor (by line_inv) (Line.Run.cons r20 Line.Run.nil))
    clear r20 hs19
    -- swap 0 : [hash, (amnt - wad), wad, receiver]
    rcases of_run_next h_run with ⟨s21, r21, h_run⟩
    have hs21 : [hash, amnt - wad, wad, receiver] <<+ s21.stack := by
      have h_swap : Stack.Swap (0 : Fin 16).val [amnt - wad, hash, wad, receiver]
          [hash, amnt - wad, wad, receiver] := Stack.swapCore_zero
      exact Stack.prefix_of_swap h_swap (of_run_swap r21) hs20
    have hg := hg.trans (Line.of_inv Devm.getStor (by line_inv) (Line.Run.cons r21 Line.Run.nil))
    clear r21 hs20
    -- sstore : the guarded allowance write
    rcases of_run_next h_run with ⟨s22, r22, h_run⟩
    have h_set : Devm.getStor s22 sevm.currentTarget
        = (Devm.getStor s21 sevm.currentTarget).set hash (amnt - wad) :=
      sstore_getStor_set r22 hs21
    have hs22 : [wad, receiver] <<+ s22.stack := prefix_of_sstore r22 hs21
    clear r22 hs21
    -- the write is silent, so the invariant survives to the burn's entry
    have h22 : Stor.Conserved (Devm.getStor s22 sevm.currentTarget) := by
      apply Stor.Conserved.of_silent _ (h_set ▸ Stor.Silent.set h_nva h_nsup)
      rw [← congr_fun hg sevm.currentTarget]
      exact h
    -- Func.call burnSlot : the shared epilogue
    rcases of_run_call h_run with ⟨f, s23, h_get, h_burn, h_run⟩
    rw [get_burnSlot] at h_get
    exact of_burnAndReturn h_va
      (by rcases hs22 with ⟨t, hsplit⟩
          exact ⟨t, by rw [← h_burn.stack]; exact hsplit⟩)
      (by rw [← congr_fun (funext (fun a => (Devm.Burn.getStor h_burn a).symm) :
            Devm.getStor s22 = Devm.getStor _) sevm.currentTarget]
          exact h22)
      (by rw [← Option.some.inj h_get] at h_run; exact h_run)
  · -- INFINITE ARM : the flag is nonzero, nothing is written
    have hp13s := hp13.stack
    simp only [Stack.Pop, Split, List.nil_append, List.cons_append] at hp13s
    rw [hp13s] at hs12
    have h_w13 : ((~~~ amnt) =? 0) = w13 := pref_head_unique hs12 (pref_append [w13] s13.stack)
    rw [h_w13] at hs12
    have hs13 : [amnt, hash, wad, receiver] <<+ s13.stack := cons_pref_cons_inv hs12
    have hg := hg.trans (funext (fun a => (Devm.PopBurn.getStor hp13 a).symm))
    have hg := hg.trans (funext (fun a => (Devm.Burn.getStor hb13 a).symm))
    have hs14 : [amnt, hash, wad, receiver] <<+ s14.stack := by
      rcases hs13 with ⟨t, hsplit⟩
      refine ⟨t, ?_⟩
      rw [← hb13.stack]
      exact hsplit
    clear hs12 hp13s hp13 hb13 h_w13 hs13
    -- pop : [hash, wad, receiver]
    rcases of_run_next h_run with ⟨s15, r15, h_run⟩
    have hs15 : [hash, wad, receiver] <<+ s15.stack :=
      prefix_of_pop (of_run_pop r15) hs14
    have hg := hg.trans (Line.of_inv Devm.getStor (by line_inv) (Line.Run.cons r15 Line.Run.nil))
    clear r15 hs14
    -- pop : [wad, receiver]
    rcases of_run_next h_run with ⟨s16, r16, h_run⟩
    have hs16 : [wad, receiver] <<+ s16.stack :=
      prefix_of_pop (of_run_pop r16) hs15
    have hg := hg.trans (Line.of_inv Devm.getStor (by line_inv) (Line.Run.cons r16 Line.Run.nil))
    clear r16 hs15
    -- Func.call burnSlot
    rcases of_run_call h_run with ⟨f, s17, h_get, h_burn, h_run⟩
    rw [get_burnSlot] at h_get
    exact of_burnAndReturn h_va
      (by rcases hs16 with ⟨t, hsplit⟩
          exact ⟨t, by rw [← h_burn.stack]; exact hsplit⟩)
      (by rw [← congr_fun (funext (fun a => (Devm.Burn.getStor h_burn a).symm) :
            Devm.getStor s16 = Devm.getStor _) sevm.currentTarget]
          rw [← congr_fun hg sevm.currentTarget]
          exact h)
      (by rw [← Option.some.inj h_get] at h_run; exact h_run)

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

/-- **The twelfth `FuncSoundNoMem` input.**  `flashLoan` preserves
conservation.
Walked in the program's own order: the three guards, the mint pair completing
before the `CALL`, the callback under the deeper-frame induction hypothesis,
the returndata checks, and the repayment converging on the burn pair. -/
theorem flashLoan_preserves_conserved {sevm : Sevm} {s r : Devm}
    (cond : fmintSpec.Pre sevm.currentTarget sevm s)
    (ih : Exec.InvDepth sevm.depth sevm.currentTarget Fmint.fmint
      (fmintSpec.PreWf sevm.currentTarget) (fmintSpec.Post sevm.currentTarget))
    (h_run : Func.Run (Fmint.fmint.main :: Fmint.fmintAux) sevm s Fmint.flashLoan r) :
    Stor.Conserved (Devm.getStor r sevm.currentTarget) := by
  have h_code : some (s.getCode sevm.currentTarget).toList = Prog.compile Fmint.fmint :=
    cond.code
  have h_cons : Stor.Conserved (Devm.getStor s sevm.currentTarget) :=
    fmintSpec_preInv_iff.mp cond.inv
  clear cond
  simp only [Fmint.flashLoan] at h_run
  -- (0) `token = self` guard : storage-silent
  rcases of_run_prepend (arg 1) _ h_run with ⟨s1, h1, h_run⟩
  rcases prefix_of_cdl nil_pref h1 with ⟨token, hs1⟩
  have hg : Devm.getStor s = Devm.getStor s1 := Line.of_inv Devm.getStor (by line_inv) h1
  have hgc : Devm.getCode s = Devm.getCode s1 := Line.of_inv Devm.getCode (by line_inv) h1
  clear h1
  rcases of_run_next h_run with ⟨s2, r2, h_run⟩
  have hs2 : sevm.currentTarget.toB256 :: token :: [] <<+ s2.stack :=
    prefix_of_push (of_run_address r2) hs1
  have hg := hg.trans (Line.of_inv Devm.getStor (by line_inv) (Line.Run.cons r2 Line.Run.nil))
  have hgc := hgc.trans (Line.of_inv Devm.getCode (by line_inv) (Line.Run.cons r2 Line.Run.nil))
  clear r2 hs1
  rcases of_run_next h_run with ⟨s3, r3, h_run⟩
  have hs3 := prefix_of_eq r3 hs2
  have hg := hg.trans (Line.of_inv Devm.getStor (by line_inv) (Line.Run.cons r3 Line.Run.nil))
  have hgc := hgc.trans (Line.of_inv Devm.getCode (by line_inv) (Line.Run.cons r3 Line.Run.nil))
  clear r3 hs2
  rcases of_run_next h_run with ⟨s4, r4, h_run⟩
  have hs4 := prefix_of_iszero r4 hs3
  have hg := hg.trans (Line.of_inv Devm.getStor (by line_inv) (Line.Run.cons r4 Line.Run.nil))
  have hgc := hgc.trans (Line.of_inv Devm.getCode (by line_inv) (Line.Run.cons r4 Line.Run.nil))
  clear r4 hs3
  rcases of_run_branch_revert h_run with ⟨s5, hp5, h_run⟩
  have hg := hg.trans (funext (fun x => (Devm.PopBurn.getStor hp5 x).symm))
  have hgc := hgc.trans (funext (fun x => getCode_eq_of_state_eq hp5.state x))
  clear hp5 hs4
  -- (1) the receiver guard : conservation-critical, not hygiene
  rcases of_run_prepend (arg 0) _ h_run with ⟨s6, h6, h_run⟩
  rcases prefix_of_cdl nil_pref h6 with ⟨receiver, hs6⟩
  have hg := hg.trans (Line.of_inv Devm.getStor (by line_inv) h6)
  have hgc := hgc.trans (Line.of_inv Devm.getCode (by line_inv) h6)
  clear h6
  rcases of_run_next h_run with ⟨s7, r7, h_run⟩
  rcases of_run_dup r7 with ⟨y, hy7, pb7⟩
  have hy7' : y = receiver := by
    have h_get : s6.stack[(0 : Fin 16).val]? = some receiver :=
      Stack.nth_getElem (Stack.Nth.head receiver []) hs6
    rw [h_get] at hy7; injection hy7 with hy7; exact hy7.symm
  subst y
  have hs7 : [receiver, receiver] <<+ s7.stack := prefix_of_push pb7 hs6
  have hg := hg.trans (Line.of_inv Devm.getStor (by line_inv) (Line.Run.cons r7 Line.Run.nil))
  have hgc := hgc.trans (Line.of_inv Devm.getCode (by line_inv) (Line.Run.cons r7 Line.Run.nil))
  clear r7 pb7 hs6
  rcases of_run_prepend checkNonAddress _ h_run with ⟨s8, h8, h_run⟩
  rcases of_check_non_address hs7 h8 with ⟨na, hs8, h_va_iff⟩
  have hg := hg.trans (Line.of_inv Devm.getStor (by line_inv) h8)
  have hgc := hgc.trans (Line.of_inv Devm.getCode (by line_inv) h8)
  clear h8 hs7
  rcases of_run_branch_revert h_run with ⟨s9, hp9, h_run⟩
  have hp9s := hp9.stack
  simp only [Stack.Pop, Split, List.nil_append, List.cons_append] at hp9s
  rw [hp9s] at hs8
  have h_va : ValidAdr receiver :=
    h_va_iff.mp (pref_head_unique hs8 (pref_append [0] s9.stack))
  rw [pref_head_unique hs8 (pref_append [0] s9.stack)] at hs8
  have hs9 : [receiver] <<+ s9.stack := cons_pref_cons_inv hs8
  have hg := hg.trans (funext (fun x => (Devm.PopBurn.getStor hp9 x).symm))
  have hgc := hgc.trans (funext (fun x => getCode_eq_of_state_eq hp9.state x))
  clear hs8 hp9s hp9 h_va_iff
  rcases h_va with ⟨a, h_recv⟩
  subst h_recv
  -- (2) `amount ≤ maxFlashLoan` : the whole overflow argument for the mint
  rcases of_run_prepend (arg 2) _ h_run with ⟨s10, h10, h_run⟩
  rcases prefix_of_cdl hs9 h10 with ⟨amount, hs10⟩
  have hg := hg.trans (Line.of_inv Devm.getStor (by line_inv) h10)
  have hgc := hgc.trans (Line.of_inv Devm.getCode (by line_inv) h10)
  clear h10 hs9
  rcases of_run_next h_run with ⟨s11, r11, h_run⟩
  rcases of_run_dup r11 with ⟨y, hy11, pb11⟩
  have hy11' : y = amount := by
    have h_get : s10.stack[(0 : Fin 16).val]? = some amount :=
      Stack.nth_getElem (Stack.Nth.head amount [a.toB256]) hs10
    rw [h_get] at hy11; injection hy11 with hy11; exact hy11.symm
  subst y
  have hs11 : [amount, amount, a.toB256] <<+ s11.stack := prefix_of_push pb11 hs10
  have hg := hg.trans (Line.of_inv Devm.getStor (by line_inv) (Line.Run.cons r11 Line.Run.nil))
  have hgc := hgc.trans (Line.of_inv Devm.getCode (by line_inv) (Line.Run.cons r11 Line.Run.nil))
  clear r11 pb11 hs10
  rcases of_run_prepend Fmint.pushSupplySlot _ h_run with ⟨s12, h12, h_run⟩
  have hs12 : Fmint.supplySlot :: [amount, amount, a.toB256] <<+ s12.stack := by
    simp only [Fmint.pushSupplySlot] at h12
    rcases Line.of_run_cons h12 with ⟨sa, ra, h12'⟩
    rcases Line.of_run_cons h12' with ⟨sb, rb, hnil⟩
    cases hnil
    have hpa : (0 : B256) :: [amount, amount, a.toB256] <<+ sa.stack :=
      prefix_of_push (of_run_pushB256 ra) hs11
    have hpb := prefix_of_not rb hpa
    rw [Fmint.supplySlot_eq_not_zero] at hpb
    exact hpb
  have hg := hg.trans (Line.of_inv Devm.getStor (by line_inv) h12)
  have hgc := hgc.trans (Line.of_inv Devm.getCode (by line_inv) h12)
  clear h12 hs11
  rcases of_run_next h_run with ⟨s13, r13, h_run⟩
  rcases prefix_of_sload r13 hs12 with ⟨supply, hs13, h_supply⟩
  have h_supply' : supply
      = (Devm.getStor s sevm.currentTarget).get Fmint.supplySlot := by
    rw [h_supply]
    show (Devm.getStor s12 sevm.currentTarget).get Fmint.supplySlot = _
    rw [← congr_fun hg sevm.currentTarget]
  clear h_supply
  have hg := hg.trans (Line.of_inv Devm.getStor (by line_inv) (Line.Run.cons r13 Line.Run.nil))
  have hgc := hgc.trans (Line.of_inv Devm.getCode (by line_inv) (Line.Run.cons r13 Line.Run.nil))
  clear r13 hs12
  rcases of_run_next h_run with ⟨s14, r14, h_run⟩
  have hs14 := prefix_of_not r14 hs13
  have hg := hg.trans (Line.of_inv Devm.getStor (by line_inv) (Line.Run.cons r14 Line.Run.nil))
  have hgc := hgc.trans (Line.of_inv Devm.getCode (by line_inv) (Line.Run.cons r14 Line.Run.nil))
  clear r14 hs13
  rcases of_run_next h_run with ⟨s15, r15, h_run⟩
  have hs15 := prefix_of_lt r15 hs14
  have hg := hg.trans (Line.of_inv Devm.getStor (by line_inv) (Line.Run.cons r15 Line.Run.nil))
  have hgc := hgc.trans (Line.of_inv Devm.getCode (by line_inv) (Line.Run.cons r15 Line.Run.nil))
  clear r15 hs14
  rcases of_run_branch_revert h_run with ⟨s16, hp16, h_run⟩
  have hp16s := hp16.stack
  simp only [Stack.Pop, Split, List.nil_append, List.cons_append] at hp16s
  rw [hp16s] at hs15
  have h_boundflag : ((~~~ supply) <? amount) = 0 :=
    pref_head_unique hs15 (pref_append [0] s16.stack)
  have h_bound : amount ≤ ~~~ supply := by
    rw [← B256.not_lt]; intro hlt
    rw [B256.ltCheck, if_pos hlt] at h_boundflag
    exact B256.zero_ne_one h_boundflag.symm
  have h_nof : B256.Nof ((Devm.getStor s sevm.currentTarget).get Fmint.supplySlot) amount := by
    rw [← h_supply']
    exact B256.nof_of_le_not h_bound
  rw [h_boundflag] at hs15
  have hs16 : [amount, a.toB256] <<+ s16.stack := cons_pref_cons_inv hs15
  have hg := hg.trans (funext (fun x => (Devm.PopBurn.getStor hp16 x).symm))
  have hgc := hgc.trans (funext (fun x => getCode_eq_of_state_eq hp16.state x))
  clear hs15 hp16s hp16 h_boundflag h_bound h_supply'
  -- (3) the mint pair : both SSTOREs complete before the CALL
  rcases of_run_next h_run with ⟨s17, r17, h_run⟩
  rcases of_run_dup r17 with ⟨y, hy17, pb17⟩
  have hy17' : y = a.toB256 := by
    have h_get : s16.stack[(1 : Fin 16).val]? = some a.toB256 :=
      Stack.nth_getElem (Stack.Nth.tail 0 a.toB256 amount [a.toB256]
        (Stack.Nth.head a.toB256 [])) hs16
    rw [h_get] at hy17; injection hy17 with hy17; exact hy17.symm
  subst y
  have hs17 : [a.toB256, amount, a.toB256] <<+ s17.stack := prefix_of_push pb17 hs16
  have hg := hg.trans (Line.of_inv Devm.getStor (by line_inv) (Line.Run.cons r17 Line.Run.nil))
  have hgc := hgc.trans (Line.of_inv Devm.getCode (by line_inv) (Line.Run.cons r17 Line.Run.nil))
  clear r17 pb17 hs16
  rcases of_run_next h_run with ⟨s18, r18, h_run⟩
  rcases prefix_of_sload r18 hs17 with ⟨rbal, hs18, h_rbal⟩
  have h_rbal' : rbal = (Devm.getStor s sevm.currentTarget).get a.toB256 := by
    rw [h_rbal]
    show (Devm.getStor s17 sevm.currentTarget).get a.toB256 = _
    rw [← congr_fun hg sevm.currentTarget]
  clear h_rbal
  have hg := hg.trans (Line.of_inv Devm.getStor (by line_inv) (Line.Run.cons r18 Line.Run.nil))
  have hgc := hgc.trans (Line.of_inv Devm.getCode (by line_inv) (Line.Run.cons r18 Line.Run.nil))
  clear r18 hs17
  rcases of_run_next h_run with ⟨s19, r19, h_run⟩
  rcases of_run_dup r19 with ⟨y, hy19, pb19⟩
  have hy19' : y = amount := by
    have h_get : s18.stack[(1 : Fin 16).val]? = some amount :=
      Stack.nth_getElem (Stack.Nth.tail 0 amount rbal [amount, a.toB256]
        (Stack.Nth.head amount [a.toB256])) hs18
    rw [h_get] at hy19; injection hy19 with hy19; exact hy19.symm
  subst y
  have hs19 : [amount, rbal, amount, a.toB256] <<+ s19.stack := prefix_of_push pb19 hs18
  have hg := hg.trans (Line.of_inv Devm.getStor (by line_inv) (Line.Run.cons r19 Line.Run.nil))
  have hgc := hgc.trans (Line.of_inv Devm.getCode (by line_inv) (Line.Run.cons r19 Line.Run.nil))
  clear r19 pb19 hs18
  rcases of_run_next h_run with ⟨s20, r20, h_run⟩
  have hs20 : (amount + rbal) :: [amount, a.toB256] <<+ s20.stack := prefix_of_add r20 hs19
  have hg := hg.trans (Line.of_inv Devm.getStor (by line_inv) (Line.Run.cons r20 Line.Run.nil))
  have hgc := hgc.trans (Line.of_inv Devm.getCode (by line_inv) (Line.Run.cons r20 Line.Run.nil))
  clear r20 hs19
  rcases of_run_next h_run with ⟨s21, r21, h_run⟩
  rcases of_run_dup r21 with ⟨y, hy21, pb21⟩
  have hy21' : y = a.toB256 := by
    have h_get : s20.stack[(2 : Fin 16).val]? = some a.toB256 :=
      Stack.nth_getElem
        (Stack.Nth.tail 1 a.toB256 (amount + rbal) [amount, a.toB256]
          (Stack.Nth.tail 0 a.toB256 amount [a.toB256]
            (Stack.Nth.head a.toB256 []))) hs20
    rw [h_get] at hy21; injection hy21 with hy21; exact hy21.symm
  subst y
  have hs21 : [a.toB256, amount + rbal, amount, a.toB256] <<+ s21.stack :=
    prefix_of_push pb21 hs20
  have hg := hg.trans (Line.of_inv Devm.getStor (by line_inv) (Line.Run.cons r21 Line.Run.nil))
  have hgc := hgc.trans (Line.of_inv Devm.getCode (by line_inv) (Line.Run.cons r21 Line.Run.nil))
  clear r21 pb21 hs20
  -- the balance-side SSTORE
  rcases of_run_next h_run with ⟨s22, r22, h_run⟩
  have h_set1 : Devm.getStor s22 sevm.currentTarget
      = (Devm.getStor s21 sevm.currentTarget).set a.toB256 (amount + rbal) :=
    sstore_getStor_set r22 hs21
  have hgc := hgc.trans (Line.of_inv Devm.getCode (by line_inv) (Line.Run.cons r22 Line.Run.nil))
  have hs22 : [amount, a.toB256] <<+ s22.stack := prefix_of_sstore r22 hs21
  clear r22 hs21
  rcases of_run_prepend Fmint.pushSupplySlot _ h_run with ⟨s23, h23, h_run⟩
  have hs23 : Fmint.supplySlot :: [amount, a.toB256] <<+ s23.stack := by
    simp only [Fmint.pushSupplySlot] at h23
    rcases Line.of_run_cons h23 with ⟨sa, ra, h23'⟩
    rcases Line.of_run_cons h23' with ⟨sb, rb, hnil⟩
    cases hnil
    have hpa : (0 : B256) :: [amount, a.toB256] <<+ sa.stack :=
      prefix_of_push (of_run_pushB256 ra) hs22
    have hpb := prefix_of_not rb hpa
    rw [Fmint.supplySlot_eq_not_zero] at hpb
    exact hpb
  have hg2 : Devm.getStor s22 = Devm.getStor s23 :=
    Line.of_inv Devm.getStor (by line_inv) h23
  have hgc := hgc.trans (Line.of_inv Devm.getCode (by line_inv) h23)
  clear h23 hs22
  rcases of_run_next h_run with ⟨s24, r24, h_run⟩
  rcases prefix_of_sload r24 hs23 with ⟨supply2, hs24, h_supply2⟩
  have h_supply2' : supply2
      = ((Devm.getStor s sevm.currentTarget).set a.toB256
          (amount + (Devm.getStor s sevm.currentTarget).get a.toB256)).get
            Fmint.supplySlot := by
    rw [h_supply2]
    show (Devm.getStor s23 sevm.currentTarget).get Fmint.supplySlot = _
    rw [← congr_fun hg2 sevm.currentTarget, h_set1, ← congr_fun hg sevm.currentTarget,
      h_rbal']
  clear h_supply2
  have hg2 := hg2.trans (Line.of_inv Devm.getStor (by line_inv) (Line.Run.cons r24 Line.Run.nil))
  have hgc := hgc.trans (Line.of_inv Devm.getCode (by line_inv) (Line.Run.cons r24 Line.Run.nil))
  clear r24 hs23
  rcases of_run_next h_run with ⟨s25, r25, h_run⟩
  rcases of_run_dup r25 with ⟨y, hy25, pb25⟩
  have hy25' : y = amount := by
    have h_get : s24.stack[(1 : Fin 16).val]? = some amount :=
      Stack.nth_getElem (Stack.Nth.tail 0 amount supply2 [amount, a.toB256]
        (Stack.Nth.head amount [a.toB256])) hs24
    rw [h_get] at hy25; injection hy25 with hy25; exact hy25.symm
  subst y
  have hs25 : [amount, supply2, amount, a.toB256] <<+ s25.stack := prefix_of_push pb25 hs24
  have hg2 := hg2.trans (Line.of_inv Devm.getStor (by line_inv) (Line.Run.cons r25 Line.Run.nil))
  have hgc := hgc.trans (Line.of_inv Devm.getCode (by line_inv) (Line.Run.cons r25 Line.Run.nil))
  clear r25 pb25 hs24
  rcases of_run_next h_run with ⟨s26, r26, h_run⟩
  have hs26 : (amount + supply2) :: [amount, a.toB256] <<+ s26.stack := prefix_of_add r26 hs25
  have hg2 := hg2.trans (Line.of_inv Devm.getStor (by line_inv) (Line.Run.cons r26 Line.Run.nil))
  have hgc := hgc.trans (Line.of_inv Devm.getCode (by line_inv) (Line.Run.cons r26 Line.Run.nil))
  clear r26 hs25
  rcases of_run_prepend Fmint.pushSupplySlot _ h_run with ⟨s27, h27, h_run⟩
  have hs27 : Fmint.supplySlot :: (amount + supply2) :: [amount, a.toB256] <<+ s27.stack := by
    simp only [Fmint.pushSupplySlot] at h27
    rcases Line.of_run_cons h27 with ⟨sa, ra, h27'⟩
    rcases Line.of_run_cons h27' with ⟨sb, rb, hnil⟩
    cases hnil
    have hpa : (0 : B256) :: (amount + supply2) :: [amount, a.toB256] <<+ sa.stack :=
      prefix_of_push (of_run_pushB256 ra) hs26
    have hpb := prefix_of_not rb hpa
    rw [Fmint.supplySlot_eq_not_zero] at hpb
    exact hpb
  have hg2 := hg2.trans (Line.of_inv Devm.getStor (by line_inv) h27)
  have hgc := hgc.trans (Line.of_inv Devm.getCode (by line_inv) h27)
  clear h27 hs26
  -- the supply-side SSTORE : the pair is complete, conservation holds at the CALL
  rcases of_run_next h_run with ⟨s28, r28, h_run⟩
  have h_set2 : Devm.getStor s28 sevm.currentTarget
      = (Devm.getStor s27 sevm.currentTarget).set Fmint.supplySlot (amount + supply2) :=
    sstore_getStor_set r28 hs27
  have hgc := hgc.trans (Line.of_inv Devm.getCode (by line_inv) (Line.Run.cons r28 Line.Run.nil))
  have hs28 : [amount, a.toB256] <<+ s28.stack := prefix_of_sstore r28 hs27
  clear r28 hs27
  have h_cons28 : Stor.Conserved (Devm.getStor s28 sevm.currentTarget) := by
    rw [h_set2, ← congr_fun hg2 sevm.currentTarget, h_set1,
      ← congr_fun hg sevm.currentTarget, h_rbal', h_supply2']
    exact h_cons.mint_set h_nof
  clear h_set1 h_set2 h_supply2' h_rbal' h_nof hg hg2 h_cons
  -- (4) the mint `Transfer` log : storage-silent
  rcases of_run_next h_run with ⟨s29, r29, h_run⟩
  rcases of_run_dup r29 with ⟨y29, hy29, pb29⟩
  have hs29 : y29 :: [amount, a.toB256] <<+ s29.stack := prefix_of_push pb29 hs28
  have hg3 : Devm.getStor s28 = Devm.getStor s29 :=
    Line.of_inv Devm.getStor (by line_inv) (Line.Run.cons r29 Line.Run.nil)
  have hgc := hgc.trans (Line.of_inv Devm.getCode (by line_inv) (Line.Run.cons r29 Line.Run.nil))
  clear r29 pb29 hy29 hs28
  rcases of_run_prepend (mstoreAt 0) _ h_run with ⟨s30, h30, h_run⟩
  have hs30 : [amount, a.toB256] <<+ s30.stack := prefix_of_mstoreAt h30 hs29
  have hg3 := hg3.trans (Line.of_inv Devm.getStor (by line_inv) h30)
  have hgc := hgc.trans (Line.of_inv Devm.getCode (by line_inv) h30)
  clear h30 hs29
  rcases of_run_next h_run with ⟨s31, r31, h_run⟩
  rcases of_run_dup r31 with ⟨y31, hy31, pb31⟩
  have hs31 : y31 :: [amount, a.toB256] <<+ s31.stack := prefix_of_push pb31 hs30
  have hg3 := hg3.trans (Line.of_inv Devm.getStor (by line_inv) (Line.Run.cons r31 Line.Run.nil))
  have hgc := hgc.trans (Line.of_inv Devm.getCode (by line_inv) (Line.Run.cons r31 Line.Run.nil))
  clear r31 pb31 hy31 hs30
  rcases of_run_next h_run with ⟨s32, r32, h_run⟩
  have hs32 : (0 : B256) :: y31 :: [amount, a.toB256] <<+ s32.stack :=
    prefix_of_push (of_run_pushB256 r32) hs31
  have hg3 := hg3.trans (Line.of_inv Devm.getStor (by line_inv) (Line.Run.cons r32 Line.Run.nil))
  have hgc := hgc.trans (Line.of_inv Devm.getCode (by line_inv) (Line.Run.cons r32 Line.Run.nil))
  clear r32 hs31
  rcases of_run_next h_run with ⟨s33, r33, h_run⟩
  have hs33 : transferEvent :: (0 : B256) :: y31 :: [amount, a.toB256] <<+ s33.stack :=
    prefix_of_push (of_run_pushB256 r33) hs32
  have hg3 := hg3.trans (Line.of_inv Devm.getStor (by line_inv) (Line.Run.cons r33 Line.Run.nil))
  have hgc := hgc.trans (Line.of_inv Devm.getCode (by line_inv) (Line.Run.cons r33 Line.Run.nil))
  clear r33 hs32
  rcases of_run_prepend (logWith 2 0 1) _ h_run with ⟨s34, h34, h_run⟩
  have hs34 : [amount, a.toB256] <<+ s34.stack := of_logWith201 hs33 h34
  have hg3 := hg3.trans (Line.of_inv Devm.getStor (by line_inv) h34)
  have hgc := hgc.trans (Line.of_inv Devm.getCode (by line_inv) h34)
  clear h34 hs33
  -- (5) assemble the callback frame
  rcases of_run_next h_run with ⟨s35, r35, h_run⟩
  rcases of_run_dup r35 with ⟨y35, hy35, pb35⟩
  have hs35 : y35 :: [amount, a.toB256] <<+ s35.stack := prefix_of_push pb35 hs34
  have hg3 := hg3.trans (Line.of_inv Devm.getStor (by line_inv) (Line.Run.cons r35 Line.Run.nil))
  have hgc := hgc.trans (Line.of_inv Devm.getCode (by line_inv) (Line.Run.cons r35 Line.Run.nil))
  clear r35 pb35 hy35 hs34
  rcases of_run_prepend Fmint.storeCallbackHead _ h_run with ⟨s36, h36, h_run⟩
  have hs36 : [amount, a.toB256] <<+ s36.stack := Fmint.of_storeCallbackHead hs35 h36
  have hg3 := hg3.trans (Line.of_inv Devm.getStor (by line_inv) h36)
  have hgc := hgc.trans (Line.of_inv Devm.getCode (by line_inv) h36)
  clear h36 hs35
  rcases of_run_prepend (pushList [0, 0]) _ h_run with ⟨s37, h37, h_run⟩
  have hs37 : (0 : B256) :: (0 : B256) :: [amount, a.toB256] <<+ s37.stack := by
    simp only [pushList, List.map] at h37
    rcases Line.of_run_cons h37 with ⟨u1, q1, h37'⟩
    rcases Line.of_run_cons h37' with ⟨u2, q2, hnil⟩
    cases hnil
    exact prefix_of_push (of_run_pushB256 q2)
      (prefix_of_push (of_run_pushB256 q1) hs36)
  have hg3 := hg3.trans (Line.of_inv Devm.getStor (by line_inv) h37)
  have hgc := hgc.trans (Line.of_inv Devm.getCode (by line_inv) h37)
  clear h37 hs36
  rcases of_run_prepend Fmint.forwardCallbackData _ h_run with ⟨s38, h38, h_run⟩
  rcases Fmint.of_forwardCallbackData hs37 h38 with ⟨len, hs38⟩
  have hg3 := hg3.trans (Line.of_inv Devm.getStor (by line_inv) h38)
  have hgc := hgc.trans (Line.of_inv Devm.getCode (by line_inv) h38)
  clear h38 hs37
  rcases of_run_prepend Fmint.callbackArgsSize _ h_run with ⟨s39, h39, h_run⟩
  rcases Fmint.of_callbackArgsSize hs38 h39 with ⟨asz, hs39⟩
  have hg3 := hg3.trans (Line.of_inv Devm.getStor (by line_inv) h39)
  have hgc := hgc.trans (Line.of_inv Devm.getCode (by line_inv) h39)
  clear h39 hs38
  rcases of_run_next h_run with ⟨s40, r40, h_run⟩
  have hs40 : Fmint.callbackArgsOffset :: asz :: (0 : B256) :: (0 : B256) ::
      [amount, a.toB256] <<+ s40.stack := prefix_of_push (of_run_pushB256 r40) hs39
  have hg3 := hg3.trans (Line.of_inv Devm.getStor (by line_inv) (Line.Run.cons r40 Line.Run.nil))
  have hgc := hgc.trans (Line.of_inv Devm.getCode (by line_inv) (Line.Run.cons r40 Line.Run.nil))
  clear r40 hs39
  rcases of_run_next h_run with ⟨s41, r41, h_run⟩
  have hs41 : (0 : B256) :: Fmint.callbackArgsOffset :: asz :: (0 : B256) :: (0 : B256) ::
      [amount, a.toB256] <<+ s41.stack := prefix_of_push (of_run_pushB256 r41) hs40
  have hg3 := hg3.trans (Line.of_inv Devm.getStor (by line_inv) (Line.Run.cons r41 Line.Run.nil))
  have hgc := hgc.trans (Line.of_inv Devm.getCode (by line_inv) (Line.Run.cons r41 Line.Run.nil))
  clear r41 hs40
  rcases of_run_next h_run with ⟨s42, r42, h_run⟩
  rcases of_run_dup r42 with ⟨y42, hy42, pb42⟩
  have hs42 : y42 :: (0 : B256) :: Fmint.callbackArgsOffset :: asz :: (0 : B256) ::
      (0 : B256) :: [amount, a.toB256] <<+ s42.stack := prefix_of_push pb42 hs41
  have hg3 := hg3.trans (Line.of_inv Devm.getStor (by line_inv) (Line.Run.cons r42 Line.Run.nil))
  have hgc := hgc.trans (Line.of_inv Devm.getCode (by line_inv) (Line.Run.cons r42 Line.Run.nil))
  clear r42 pb42 hy42 hs41
  rcases of_run_next h_run with ⟨s43, r43, h_run⟩
  rcases of_run_gas r43 with ⟨g43, pb43⟩
  have hs43 : g43 :: y42 :: (0 : B256) :: Fmint.callbackArgsOffset :: asz :: (0 : B256) ::
      (0 : B256) :: [amount, a.toB256] <<+ s43.stack := prefix_of_push pb43 hs42
  have hg3 := hg3.trans (Line.of_inv Devm.getStor (by line_inv) (Line.Run.cons r43 Line.Run.nil))
  have hgc := hgc.trans (Line.of_inv Devm.getCode (by line_inv) (Line.Run.cons r43 Line.Run.nil))
  clear r43 pb43 hs42
  -- (6) the callback, and the induction hypothesis
  rcases of_run_next h_run with ⟨s44, r44, h_run⟩
  have h_code43 : some (s43.getCode sevm.currentTarget).toList = Prog.compile Fmint.fmint := by
    rw [← congr_fun hgc sevm.currentTarget]
    exact h_code
  have h_cons43 : Stor.Conserved (Devm.getStor s43 sevm.currentTarget) := by
    rw [← congr_fun hg3 sevm.currentTarget]
    exact h_cons28
  rcases Fmint.conserved_of_call ih hs43 h_code43 h_cons43 r44 with ⟨h_cons44, b, hs44⟩
  clear h_cons43 h_code43 hs43 r44 hg3 hgc h_cons28 h_code
  -- (7) the returndata checks : storage-silent
  rcases of_run_next h_run with ⟨s45, r45, h_run⟩
  have hs45 := prefix_of_iszero r45 hs44
  have hg4 : Devm.getStor s44 = Devm.getStor s45 :=
    Line.of_inv Devm.getStor (by line_inv) (Line.Run.cons r45 Line.Run.nil)
  clear r45 hs44
  rcases of_run_branch_revert h_run with ⟨s46, hp46, h_run⟩
  have hp46s := hp46.stack
  simp only [Stack.Pop, Split, List.nil_append, List.cons_append] at hp46s
  rw [hp46s] at hs45
  rw [pref_head_unique hs45 (pref_append [0] s46.stack)] at hs45
  have hs46 : [amount, a.toB256] <<+ s46.stack := cons_pref_cons_inv hs45
  have hg4 := hg4.trans (funext (fun x => (Devm.PopBurn.getStor hp46 x).symm))
  clear hs45 hp46s hp46
  rcases of_run_prepend (returnDataShorterThan 32) _ h_run with ⟨s47, h47, h_run⟩
  rcases of_returnDataShorterThan hs46 h47 with ⟨f47, hs47⟩
  have hg4 := hg4.trans (Line.of_inv Devm.getStor (by line_inv) h47)
  clear h47 hs46
  rcases of_run_branch_revert h_run with ⟨s48, hp48, h_run⟩
  have hp48s := hp48.stack
  simp only [Stack.Pop, Split, List.nil_append, List.cons_append] at hp48s
  rw [hp48s] at hs47
  rw [pref_head_unique hs47 (pref_append [0] s48.stack)] at hs47
  have hs48 : [amount, a.toB256] <<+ s48.stack := cons_pref_cons_inv hs47
  have hg4 := hg4.trans (funext (fun x => (Devm.PopBurn.getStor hp48 x).symm))
  clear hs47 hp48s hp48
  rcases of_run_prepend (checkReturnDataHead Fmint.erc3156Magic 0) _ h_run with ⟨s49, h49, h_run⟩
  rcases of_checkReturnDataHead hs48 h49 with ⟨f49, hs49⟩
  have hg4 := hg4.trans (Line.of_inv Devm.getStor (by line_inv) h49)
  clear h49 hs48
  rcases of_run_next h_run with ⟨s50, r50, h_run⟩
  have hs50 := prefix_of_iszero r50 hs49
  have hg4 := hg4.trans (Line.of_inv Devm.getStor (by line_inv) (Line.Run.cons r50 Line.Run.nil))
  clear r50 hs49
  rcases of_run_branch_revert h_run with ⟨s51, hp51, h_run⟩
  have hp51s := hp51.stack
  simp only [Stack.Pop, Split, List.nil_append, List.cons_append] at hp51s
  rw [hp51s] at hs50
  rw [pref_head_unique hs50 (pref_append [0] s51.stack)] at hs50
  have hs51 : [amount, a.toB256] <<+ s51.stack := cons_pref_cons_inv hs50
  have hg4 := hg4.trans (funext (fun x => (Devm.PopBurn.getStor hp51 x).symm))
  clear hs50 hp51s hp51
  -- (8) the repayment, and the burn pair
  apply Fmint.of_spendAllowanceThenBurn ⟨a, rfl⟩ hs51 _ h_run
  rw [← congr_fun hg4 sevm.currentTarget]
  exact h_cons44

/-- `flashLoan` is the one target that consumes `FuncSoundNoMem`'s deeper-frame
induction hypothesis — the mirror of WETH's `wethSpec_funcSound_withdraw`. -/
theorem fmintSpec_funcSound_flashLoan {fa : Adr} :
    fmintSpec.FuncSoundNoMem fa Fmint.fmintAux Fmint.flashLoan := by
  intro sevm s r h_ct h_pre ih h_run
  subst h_ct
  refine ⟨trivial, ?_⟩
  exact flashLoan_preserves_conserved h_pre ih h_run

end

/-! ## Assembly

The twelve `FuncSoundNoMem` obligations above, plus the reverting fallback, are
the
whole input to the generic dispatcher argument.  Everything from here down is
instantiation: no walk, no invariant reasoning, and nothing that names the
program's shape beyond reading it off `fmintSpec.prog` by unification. -/

/-- The twelve per-target obligations, packaged in the form both
`ContractSpec.soundNoMem_of_dispatch` and
`ContractSpec.preservesNoMem_of_dispatch` consume.  They are stated at
`FuncSoundNoMem` because no fmint target reads the machine's memory, which is
what keeps the frame theorem below premise-free. -/
theorem fmintSpec_funcSound_all (fa : Adr) :
    ∀ p ∈ Fmint.fmintFuncs, fmintSpec.FuncSoundNoMem fa Fmint.fmintAux p.2 := by
  intro f h_mem
  -- Drive the membership unfolding with `List.mem_cons`, never with `decide`:
  -- deciding anything about these leaves forces the `String.keccak` behind
  -- every `selector` and blows `maxRecDepth`.  Twelve entries here, ten at
  -- WETH, and the failure mode is the same.
  simp only [Fmint.fmintFuncs, List.mem_cons, List.not_mem_nil, or_false] at h_mem
  rcases h_mem with h | h | h | h | h | h | h | h | h | h | h | h <;> (cases h)
  · exact fmintSpec_funcSound Fmint.name name_preserves_conserved
  · exact fmintSpec_funcSound Fmint.approve approve_preserves_conserved
  · exact fmintSpec_funcSound Fmint.totalSupply totalSupply_preserves_conserved
  · exact fmintSpec_funcSound Fmint.transferFrom transferFrom_preserves_conserved
  · exact fmintSpec_funcSound decimals decimals_preserves_conserved
  · exact fmintSpec_funcSound_flashLoan
  · exact fmintSpec_funcSound Fmint.maxFlashLoan maxFlashLoan_preserves_conserved
  · exact fmintSpec_funcSound balanceOf balanceOf_preserves_conserved
  · exact fmintSpec_funcSound Fmint.symbol symbol_preserves_conserved
  · exact fmintSpec_funcSound transfer transfer_preserves_conserved
  · exact fmintSpec_funcSound Fmint.flashFee flashFee_preserves_conserved
  · exact fmintSpec_funcSound allowance allowance_preserves_conserved

/-- fmint's frame-level obligation, the one input
`ContractSpec.preserves_noMem` cannot supply.  The proof is
`wethSpec_soundNoMem`'s, with twelve dispatch targets where WETH has ten and a
*reverting* fallback where WETH has `deposit`, so the fallback obligation is
vacuous rather than a walk.

Both shape side conditions are `rfl`: `k`, the function list and the aux context
are read off `fmintSpec.prog` by unification.  The fallback lookup at index 1
reduces — unlike `burnSlot`'s at index 2, which needs `get_burnSlot`'s explicit
`List.getElem?` route. -/
theorem fmintSpec_soundNoMem (fa : Adr) : fmintSpec.SoundNoMem fa :=
  ContractSpec.soundNoMem_of_dispatch (k := Fmint.fallbackSlot)
    (funcs := Fmint.fmintFuncs) (aux := Fmint.fmintAux) (fallback := Func.revert)
    rfl (List.cons_ne_nil _ _) rfl (fmintSpec_funcSound_all fa)
    fmintSpec_funcSound_revert

/-- The memory-carrying obligation, for any consumer that wants it: dropping a
premise fmint never used. -/
theorem fmintSpec_sound (fa : Adr) : fmintSpec.Sound fa :=
  ContractSpec.SoundNoMem.sound (fmintSpec_soundNoMem fa)

/-- fmint's own result, as the instantiation of the quantified open-contract
statement (`ContractSpec.preservesNoMem_of_dispatch`, `Blanc/Ladder.lean`): the
same twelve obligations and the same vacuous fallback, consumed by the named
theorem rather than by its proof pattern. -/
theorem fmintSpec_preservesNoMem (fa : Adr) : fmintSpec.PreservesNoMem fa :=
  ContractSpec.preservesNoMem_of_dispatch (k := Fmint.fallbackSlot)
    (funcs := Fmint.fmintFuncs) (aux := Fmint.fmintAux) (fallback := Func.revert)
    rfl (List.cons_ne_nil _ _) rfl (fmintSpec_funcSound_all fa)
    fmintSpec_funcSound_revert

/-- The memory-carrying form the message-, transaction- and block-level rungs
consume. -/
theorem fmintSpec_preserves (fa : Adr) : fmintSpec.Preserves fa :=
  ContractSpec.PreservesNoMem.preserves (fmintSpec_preservesNoMem fa)

/-- **Headline 1 of `flashmint-proposal.md`**, now a theorem: an arbitrary
execution that starts in an fmint frame with the supply conserved ends with the
supply conserved.  Arbitrary includes reentrant — `flashLoan` hands control to
borrower code that may call back in through any entrypoint at any depth, and
the invariant re-established on resumption is this same one.

The statement is the one this module carried as a `Prop`-valued definition
before Arc B; nothing about it was adjusted to fit the proof.  Read it as
**conservation, an equality about storage**: `totalSupply = Σ balances` at every
observable point.  It is not solvency and it is not liveness.  During a flash
loan the minted supply is unbacked by construction — that is the design, and the
claim here is precisely that the books balance at every point an observer can
reach. -/
theorem fmint_preserves_conserved (fa : Adr) :
    ∀ sevm pre post,
      Exec 0 sevm pre (.ok post) →
      (sevm.currentTarget = fa → some sevm.code.toList = Prog.compile Fmint.fmint) →
      PrecondC fa sevm pre →
      PostcondC fa sevm post := by
  simpa only [ContractSpec.PreservesNoMem, fmintSpec_prog_eq, fmintSpec_pre_eq,
    fmintSpec_post_eq] using fmintSpec_preservesNoMem fa

/-! ### The chain rungs

The descent from the message-call layer to the frame is contract-generic and
lives in `Blanc/Ladder.lean`; each rung consumes the frame-level result as a
`c.Preserves ca` hypothesis, and `fmintSpec_preserves` is what feeds it in.  So
every theorem below is an instantiation of its generic parent — the mirror of
`Blanc/Solvent.lean`'s audited family, and no new proof.

The `wdsum` bound on the transition rungs is a hypothesis about the world, not
about the contract: it is what the generic ladder asks of the block, and it
survives the instance unchanged even though fmint's invariant never mentions an
ETH balance. -/

/-- The block-level state transition, at fmint.  Prague is the
`rules := pragueRules` instance of the generic parent, which never asks which
rules it is running. -/
theorem stateTransition_preserves_conserved (fa : Adr)
    (ch ch' : BlockChain) (block : Block)
    (h_run : stateTransition ch block = .ok ch')
    (h_wds : sum ch.state.bal + wdsum block.wds < 2 ^ 256)
    (h_inv : StateInvC fa ch.state) : StateInvC fa ch'.state :=
  fmintSpec_stateInv_iff.mp
    (ContractSpec.stateTransition_preserves_inv fa (fmintSpec_preserves fa)
      ch ch' block h_run h_wds (fmintSpec_stateInv_iff.mpr h_inv))

/-- On a configured chain the block's own timestamp picks the rules, and the
result holds whichever ones it picks: a chain that crosses an activation is not
a new case. -/
theorem stateTransitionUsing_preserves_conserved (fa : Adr) (cfg : ChainConfig)
    (ch ch' : BlockChain) (block : Block)
    (h_run : stateTransitionUsing cfg ch block = .ok ch')
    (h_wds : sum ch.state.bal + wdsum block.wds < 2 ^ 256)
    (h_inv : StateInvC fa ch.state) : StateInvC fa ch'.state :=
  fmintSpec_stateInv_iff.mp
    (ContractSpec.stateTransitionUsing_preserves_inv fa (fmintSpec_preserves fa)
      cfg ch ch' block h_run h_wds (fmintSpec_stateInv_iff.mpr h_inv))

/-- **The chain-level rung**, the second statement this module carried as a
`Prop`-valued definition: no sequence of valid blocks can break fmint's supply
conservation.  Statement unchanged. -/
theorem chain_preserves_conserved (fa : Adr) (ch ch' : BlockChain)
    (h_reach : BlockChain.Reach ch ch')
    (h_inv : StateInvC fa ch.state) : StateInvC fa ch'.state :=
  fmintSpec_stateInv_iff.mp
    (ContractSpec.chain_preserves_inv fa (fmintSpec_preserves fa)
      ch ch' h_reach (fmintSpec_stateInv_iff.mpr h_inv))

/-- Chain-level induction over a configured chain, whatever schedule it follows
and whichever activations the sequence crosses. -/
theorem chainUsing_preserves_conserved (fa : Adr) (cfg : ChainConfig)
    (ch ch' : BlockChain) (h_reach : BlockChain.ReachUsing cfg ch ch')
    (h_inv : StateInvC fa ch.state) : StateInvC fa ch'.state :=
  fmintSpec_stateInv_iff.mp
    (ContractSpec.chainUsing_preserves_inv fa (fmintSpec_preserves fa)
      cfg ch ch' h_reach (fmintSpec_stateInv_iff.mpr h_inv))

/-- Ethereum mainnet's configured schedule is the published specialization of
the chain-level rung.  It is a statement over that schedule, not executable
evidence that any mainnet block was run. -/
theorem chainUsing_preserves_conserved_mainnet (fa : Adr)
    (ch ch' : BlockChain)
    (h_reach : BlockChain.ReachUsing mainnetChainConfig ch ch')
    (h_inv : StateInvC fa ch.state) : StateInvC fa ch'.state :=
  chainUsing_preserves_conserved fa mainnetChainConfig ch ch' h_reach h_inv

/-- The Prague-only schedule is the retained fixed-fork instance of the same
rung; it says nothing the configured statement does not already say. -/
theorem chainUsing_preserves_conserved_prague (fa : Adr) (chainId : UInt64)
    (ch ch' : BlockChain)
    (h_reach : BlockChain.ReachUsing (ChainConfig.pragueOnly chainId) ch ch')
    (h_inv : StateInvC fa ch.state) : StateInvC fa ch'.state :=
  chainUsing_preserves_conserved fa (ChainConfig.pragueOnly chainId) ch ch'
    h_reach h_inv

/-- Preservation through RLP decoding and the block-hash checks. -/
theorem addBlockToChain_preserves_conserved (fa : Adr)
    (ch ch' : BlockChain) (rlp : Bytes)
    (h_run : addBlockToChain ch rlp = .ok (.inl ch'))
    (h_wds : ∀ block hash, rlpToBlock rlp = .ok ⟨block, hash⟩ →
      sum ch.state.bal + wdsum block.wds < 2 ^ 256)
    (h_inv : StateInvC fa ch.state) : StateInvC fa ch'.state :=
  fmintSpec_stateInv_iff.mp
    (ContractSpec.addBlockToChain_preserves_inv fa (fmintSpec_preserves fa)
      ch ch' rlp h_run h_wds (fmintSpec_stateInv_iff.mpr h_inv))

/-- Block import on a configured chain: the schedule and chain identity are
validated before decoding, and the decoded timestamp then selects the rules. -/
theorem addBlockToChainUsing_preserves_conserved (fa : Adr) (cfg : ChainConfig)
    (ch ch' : BlockChain) (rlp : Bytes)
    (h_run : addBlockToChainUsing cfg ch rlp = .ok (.inl ch'))
    (h_wds : ∀ block hash, rlpToBlock rlp = .ok ⟨block, hash⟩ →
      sum ch.state.bal + wdsum block.wds < 2 ^ 256)
    (h_inv : StateInvC fa ch.state) : StateInvC fa ch'.state :=
  fmintSpec_stateInv_iff.mp
    (ContractSpec.addBlockToChainUsing_preserves_inv fa (fmintSpec_preserves fa)
      cfg ch ch' rlp h_run h_wds (fmintSpec_stateInv_iff.mpr h_inv))

/-! ### Context stability, demonstrated at fmint

The quantified layer's second half (`~/plans/fmint-conserved.md` Step 6): the
extent to which fmint's discharged obligations survive a program extension,
stated over the program-free core (`Func.Core`, `Blanc/Ladder.lean`) because
`FuncSound` itself cannot transport — its `Pre` pins the exact program bytes.

Eleven of the twelve dispatch targets are call-free — their bodies contain no
`Func.call`, so their run derivations never consult the context at all — and
their cores are therefore *context-universal*: they hold at every `List Func`
whatsoever, extension shapes included, with no side condition.  The proofs
below consume the original walk lemmas (`name_preserves_conserved` …
`transferFrom_preserves_conserved`) verbatim; nothing is re-walked.

The twelfth, `flashLoan`, is the predicted exception twice over: its body
carries the two `Func.call burnSlot` tail jumps, and its obligation is not
core-shaped in the first place — it consumes `Pre`'s code equation and the
program-indexed `Exec.InvDepth` through `conserved_of_call`.  Under an
extension, `flashLoan` (and any new call-bearing target) is mechanical
re-discharge territory, per the plan's honest fallback. -/

/-- Each non-reentrant fmint target's core holds in **every** context: the
target is call-free, so its derivation never performs a lookup. -/
theorem fmint_core_stable (fs : List Func) :
    ∀ p ∈ Fmint.fmintFuncs, p.2 ≠ Fmint.flashLoan →
      Func.Core fs Stor.Conserved p.2 := by
  intro p h_mem h_ne
  -- `List.mem_cons`, never `decide` (see `fmintSpec_funcSound_all`).
  simp only [Fmint.fmintFuncs, List.mem_cons, List.not_mem_nil, or_false] at h_mem
  rcases h_mem with h | h | h | h | h | h | h | h | h | h | h | h <;> (cases h)
  · exact Func.Core.of_callFree rfl name_preserves_conserved
  · exact Func.Core.of_callFree rfl approve_preserves_conserved
  · exact Func.Core.of_callFree rfl totalSupply_preserves_conserved
  · exact Func.Core.of_callFree rfl transferFrom_preserves_conserved
  · exact Func.Core.of_callFree rfl decimals_preserves_conserved
  · exact absurd rfl h_ne
  · exact Func.Core.of_callFree rfl maxFlashLoan_preserves_conserved
  · exact Func.Core.of_callFree rfl balanceOf_preserves_conserved
  · exact Func.Core.of_callFree rfl symbol_preserves_conserved
  · exact Func.Core.of_callFree rfl transfer_preserves_conserved
  · exact Func.Core.of_callFree rfl flashFee_preserves_conserved
  · exact Func.Core.of_callFree rfl allowance_preserves_conserved

/-- The reuse path an extension arc takes, closed generically: any
storage-only spec whose invariant is `Stor.Conserved` — in particular, an
extended fmint with a new `main`, an appended aux, and the same invariant —
inherits fmint's eleven non-reentrant `FuncSound` obligations verbatim,
whatever its program and aux context.  No re-walk; the original walk lemmas
are consumed as they stand.  `flashLoan` and any new target remain that
spec's own obligations. -/
theorem fmint_funcSound_stable (c' : ContractSpec) (fa : Adr) (aux' : List Func)
    (h_side : ∀ bal, c'.Side bal)
    (h_inv : ∀ s v b, c'.Inv s v b ↔ Stor.Conserved s) :
    ∀ p ∈ Fmint.fmintFuncs, p.2 ≠ Fmint.flashLoan →
      c'.FuncSound fa aux' p.2 := by
  intro p h_mem h_ne
  apply ContractSpec.funcSound_of_core h_side
    (fun h => (h_inv _ _ _).mpr ((h_inv _ _ _).mp h))
  intro sevm s r h_run h
  exact (h_inv _ _ _).mpr
    (fmint_core_stable _ p h_mem h_ne h_run ((h_inv _ _ _).mp h))

end Blanc
