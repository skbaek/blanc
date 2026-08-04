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
-- the `Stor.Conserved` algebra — the two invisibility lemmas, the four
-- preservation combinators and the `balance ≤ supply` bound corollary — the
-- `fmintSpec` bridges, and nine of the twelve-plus-one `FuncSound` inputs (the
-- reverting fallback and the eight read-only targets).  Still open: `transfer`,
-- `approve` and `transferFrom` (Step 3), `flashLoan` (Step 4), and the
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
