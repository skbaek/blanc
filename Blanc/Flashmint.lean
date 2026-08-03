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
-- with `wbsum`, which stays in `Solvent.lean`.  Nothing here is proved: the
-- contract itself does not exist yet (`flashmint-proposal.md` Arc A owns it),
-- so the program is a parameter, and the headline results appear as
-- `Prop`-valued definitions asserted of nothing.

import Blanc.Solvent

namespace Blanc

open Jaune

/-! ## Instance 2 — `fweth` (ERC-3156 flash mint), statements only

From `~/plans/flashmint-proposal.md`.  The contract itself does not exist yet
(its Arc A owns it), so the program is a parameter: everything below holds for
whichever `Prog` that arc produces, and equally for the pure-token resolution
of the proposal's open decision D1, whose invariant is identical.

Nothing here is proved.  The headline theorem appears as a `Prop`-valued
definition — a statement that elaborates — not as a `theorem` with a proof. -/

/-- The supply slot: `B256.max`, which is never address-shaped, so `wbsum`
(which sums over address-shaped keys only) excludes it. -/
def supplySlot : B256 := B256.max

/-- The conservation invariant: total supply equals the sum of balances.  A
storage-only equality — no callvalue term, no ETH-balance term. -/
def Stor.Conserved (s : Stor) : Prop :=
  (s.get supplySlot).toNat = wbsum s

/-- The flash-mint instance.  `Inv` ignores both the callvalue and the ETH
balance, and `Side` is trivial: this contract declines the `nof`-class side
condition, which is precisely why every balance-movement slot carries `Side`
in hypothesis position rather than demanding a concrete bound. -/
def fwethSpec (fwethProg : Prog) : ContractSpec where
  prog := fwethProg
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
def PrecondC (fwethProg : Prog) (fa : Adr) (sevm : Sevm) (devm : Devm) : Prop :=
  (fwethSpec fwethProg).Pre fa sevm devm

/-- `PostcondC` of the proposal. -/
def PostcondC (fwethProg : Prog) (fa : Adr) (sevm : Sevm) (devm : Devm) : Prop :=
  (fwethSpec fwethProg).Post fa sevm devm

/-- The `State.Inv` counterpart, for the chain-level rungs. -/
def StateInvC (fwethProg : Prog) (fa : Adr) (w : Jaune.State) : Prop :=
  (fwethSpec fwethProg).StateInv fa w

/-- Headline 1 of `flashmint-proposal.md`, as a statement.  This is the shape
`weth_preserves_solvent` has, with the record substituted; it is asserted of
nothing and proved nowhere. -/
def FwethPreservesConserved (fwethProg : Prog) (fa : Adr) : Prop :=
  ∀ sevm pre post,
    Exec 0 sevm pre (.ok post) →
    (sevm.currentTarget = fa → some sevm.code.toList = Prog.compile fwethProg) →
    PrecondC fwethProg fa sevm pre →
    PostcondC fwethProg fa sevm post

/-- The chain-level rung, same substitution.  The `wdsum` bound survives as a
hypothesis about the world rather than about the contract, so it is unaffected
by the instance. -/
def FwethChainPreservesConserved (fwethProg : Prog) (fa : Adr) : Prop :=
  ∀ ch ch' : BlockChain,
    BlockChain.Reach ch ch' →
    StateInvC fwethProg fa ch.state →
    StateInvC fwethProg fa ch'.state


end Blanc
