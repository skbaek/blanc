-- Flashmint.lean : the ERC-3156 flash-mint contract as a `ContractSpec`
-- instance, statements only.
--
-- From `~/plans/flashmint-proposal.md`, produced by `~/plans/solvent-split.md`
-- as the second instance the `ContractSpec` record is validated against.  Its
-- invariant is a storage-only *equality* — no callvalue term, no ETH-balance
-- term and no `nof`-class side condition — which is what makes it the useful
-- counterweight to WETH's.
--
-- This module lives above `Blanc.Solvent` because `Stor.Conserved` is stated
-- with `wbsum`, which stays in `Solvent.lean`, and above `Blanc.Fmint` because
-- `supplySlot` now lives with the contract that generates it.
--
-- Nothing here is proved, and the program is still a parameter: the contract's
-- dispatch targets arrive with Step 1 of `~/plans/fmint-code.md`, which
-- replaces the parameter with `Fmint.fmint`.  The headline results appear as
-- `Prop`-valued definitions asserted of nothing.

import Blanc.Solvent
import Blanc.Fmint

namespace Blanc

open Jaune

/-! ## Instance 2 — `fmint` (ERC-3156 flash mint), statements only

From `~/plans/flashmint-proposal.md`, whose open decision D1 resolved to the
pure token: fmint is an ERC-20 with the ERC-3156 triple and no wrap/unwrap
surface.  The contract itself does not exist yet — Arc A's Step 1 owns it — so
the program is a parameter and everything below holds for whichever `Prog` that
step produces.

Nothing here is proved.  The headline theorem appears as a `Prop`-valued
definition — a statement that elaborates — not as a `theorem` with a proof.
Conservation is unproven pending Arc B. -/

/-- The conservation invariant: total supply equals the sum of balances.  A
storage-only equality — no callvalue term, no ETH-balance term.

`Fmint.supplySlot` is never address-shaped and `wbsum` sums over address-shaped
keys only, so the supply slot self-excludes from the right-hand side. -/
def Stor.Conserved (s : Stor) : Prop :=
  (s.get Fmint.supplySlot).toNat = wbsum s

/-- The flash-mint instance.  `Inv` ignores both the callvalue and the ETH
balance, and `Side` is trivial: this contract declines the `nof`-class side
condition, which is precisely why every balance-movement slot carries `Side`
in hypothesis position rather than demanding a concrete bound. -/
def fmintSpec (fmintProg : Prog) : ContractSpec where
  prog := fmintProg
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
def PrecondC (fmintProg : Prog) (fa : Adr) (sevm : Sevm) (devm : Devm) : Prop :=
  (fmintSpec fmintProg).Pre fa sevm devm

/-- `PostcondC` of the proposal. -/
def PostcondC (fmintProg : Prog) (fa : Adr) (sevm : Sevm) (devm : Devm) : Prop :=
  (fmintSpec fmintProg).Post fa sevm devm

/-- The `State.Inv` counterpart, for the chain-level rungs. -/
def StateInvC (fmintProg : Prog) (fa : Adr) (w : Jaune.State) : Prop :=
  (fmintSpec fmintProg).StateInv fa w

/-- Headline 1 of `flashmint-proposal.md`, as a statement.  This is the shape
`weth_preserves_solvent` has, with the record substituted; it is asserted of
nothing and proved nowhere. -/
def FmintPreservesConserved (fmintProg : Prog) (fa : Adr) : Prop :=
  ∀ sevm pre post,
    Exec 0 sevm pre (.ok post) →
    (sevm.currentTarget = fa → some sevm.code.toList = Prog.compile fmintProg) →
    PrecondC fmintProg fa sevm pre →
    PostcondC fmintProg fa sevm post

/-- The chain-level rung, same substitution.  The `wdsum` bound survives as a
hypothesis about the world rather than about the contract, so it is unaffected
by the instance. -/
def FmintChainPreservesConserved (fmintProg : Prog) (fa : Adr) : Prop :=
  ∀ ch ch' : BlockChain,
    BlockChain.Reach ch ch' →
    StateInvC fmintProg fa ch.state →
    StateInvC fmintProg fa ch'.state


end Blanc
