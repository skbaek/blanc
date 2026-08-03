-- Ladder.lean : the contract-spec record for the axis-2 cut of Solvent.lean.
--
-- STEP 1 DRAFT (`~/plans/solvent-split.md`).  This module currently sits
-- *above* `Blanc.Solvent` so that the WETH instance can be discharged from the
-- lemmas that already exist there.  Step 2 inverts that dependency: the record
-- and the contract-generic band move below `Solvent.lean`, and `Solvent.lean`
-- becomes the WETH instance.  Nothing here is imported by the audited
-- theorems, and nothing here changes an existing definition.
--
-- What the record is for.  The band of `Solvent.lean` from the
-- sub-execution-carryover tier upwards is contract-generic in substance but
-- WETH-monomorphic in statement: every theorem names `weth`, `Stor.Solvent`,
-- `SumNof`, `Precond`, `Postcond` or `State.Inv`.  `ContractSpec` is the
-- interface those statements actually consume — a program, an invariant, a
-- global balance side condition, and the handful of closure properties the
-- ladder's proofs use.  Two instances are given below: `wethSpec`, which is
-- the shipped contract and is shown to reproduce the existing `Precond` /
-- `Postcond` / `State.Inv` bundles exactly, and `fwethSpec`, the ERC-3156
-- flash-mint contract of `~/plans/flashmint-proposal.md`, whose invariant is a
-- storage-only *equality* with no callvalue term, no ETH-balance term and no
-- `nof`-class side condition.  `fwethSpec` is a statement-level instance only:
-- its program is a parameter (the contract does not exist yet, and its arc
-- owns it) and nothing is proved about the resulting statements.

import Blanc.Solvent

namespace Blanc

open Jaune

/-! ## The record -/

/-- The interface the contract-generic band of the solvency ladder consumes.

`Inv` is the contract-level invariant, applied to the contract's storage, the
callvalue in flight into the current frame, and the contract's ETH balance.
`Side` is the global side condition on the world's balance map — WETH's
`SumNof`; a balance-independent contract declines it with `fun _ => True`.

The remaining fields are the *slots*: the closure properties the ladder's
proofs use.  They come in two tiers.  The first three are the invariant's own
algebra and mention nothing outside it.  The last four are the
balance-movement tier (`subBal`/`addBal` at the world-state level, which is
what `Xinst`'s value transfers, `processMessageCall` and `processTransaction`
all reduce to); they carry `Side` in hypothesis position, which is exactly how
a contract that declines the `nof` condition also declines the obligation to
reason about wrap-around. -/
structure ContractSpec where
  /-- The contract's source program.  The ladder consumes it only through
  `Prog.compile` — code preservation across sub-executions, code
  non-emptiness (`Prog.compile_ne_nil`) and non-delegation
  (`not_delegation_of_compile`), all three of which are already generic in
  the program and therefore need no slot. -/
  prog : Prog
  /-- storage at the contract address → callvalue in flight → the contract's
  ETH balance → Prop. -/
  Inv : Stor → B256 → B256 → Prop
  /-- The global side condition on the world's balance map. -/
  Side : (Adr → B256) → Prop
  /-- Once a frame has terminated there is no callvalue in flight.
  (WETH: `solvent_zero_of_solvent`.) -/
  inv_forget : ∀ {s : Stor} {v b : B256}, Inv s v b → Inv s 0 b
  /-- The invariant survives a rise in the contract's own balance. -/
  inv_mono : ∀ {s : Stor} {v b b' : B256}, Inv s v b → b.toNat ≤ b'.toNat → Inv s v b'
  /-- A callvalue that has already been credited to the contract's balance may
  be taken into flight. -/
  inv_recv : ∀ {s : Stor} {v b b' : B256}, Inv s 0 b → b'.toNat = b.toNat + v.toNat → Inv s v b'
  /-- The side condition survives any change that does not raise the total. -/
  side_le : ∀ {f g : Adr → B256}, Side f → sum g ≤ sum f → Side g
  /-- The side condition survives a value transfer. -/
  side_transfer : ∀ {st st' : Jaune.State} {caller callee : Adr} {wad : B256},
    st.subBal caller wad = some st' → Side st.bal → Side (st'.addBal callee wad).bal
  /-- The side condition survives a credit that stays under the bound.  The
  bound is supplied by the caller's wei-conservation argument, exactly as in
  `State.Inv.addBal`. -/
  side_addBal : ∀ {w : Jaune.State} {a : Adr} {val : B256},
    sum w.bal + val.toNat < 2 ^ 256 → Side w.bal → Side (w.addBal a val).bal
  /-- The invariant survives a value transfer that does not debit the
  contract.  The callee may be the contract itself, in which case its balance
  rises; `Side` is what rules out a wrap. -/
  inv_transfer : ∀ {st st' : Jaune.State} {caller callee ca : Adr} {wad v : B256},
    st.subBal caller wad = some st' → caller ≠ ca → Side st.bal →
    Inv (st.getStor ca) v (st.bal ca) →
    Inv ((st'.addBal callee wad).getStor ca) v ((st'.addBal callee wad).bal ca)
  /-- Entering a frame *at* the contract with callvalue `wad`: the transfer has
  already credited `wad` to the contract's balance, and the child frame carries
  it in flight. -/
  inv_recv_transfer : ∀ {st st' : Jaune.State} {caller ca : Adr} {wad : B256},
    st.subBal caller wad = some st' → caller ≠ ca → Side st.bal →
    Inv (st.getStor ca) 0 (st.bal ca) →
    Inv ((st'.addBal ca wad).getStor ca) wad ((st'.addBal ca wad).bal ca)
  /-- The invariant survives a bare credit under the wei-conservation bound
  (`State.Inv.addBal`: gas refunds, the coinbase fee, withdrawals). -/
  inv_addBal : ∀ {w : Jaune.State} {ca a : Adr} {val v : B256},
    sum w.bal + val.toNat < 2 ^ 256 → Side w.bal →
    Inv (w.getStor ca) v (w.bal ca) →
    Inv ((w.addBal a val).getStor ca) v ((w.addBal a val).bal ca)

namespace ContractSpec

variable (c : ContractSpec)

/-- The frame-entry form of the invariant: the callvalue is in flight exactly
when the current frame is executing the contract itself. -/
def PreInv (devm : Devm) (ca : Adr) (sevm : Sevm) : Prop :=
  (sevm.currentTarget = ca → c.Inv (Devm.getStor devm ca) sevm.value (devm.getBal ca)) ∧
  (sevm.currentTarget ≠ ca → c.Inv (Devm.getStor devm ca) 0 (devm.getBal ca))

/-- The frame-exit form of the invariant. -/
def PostInv (devm : Devm) (ca : Adr) : Prop :=
  c.Inv (Devm.getStor devm ca) 0 (devm.getBal ca)

/-- The generic counterpart of `Blanc.Precond`. -/
structure Pre (ca : Adr) (sevm : Sevm) (devm : Devm) : Prop where
  (code : some (devm.getCode ca).toList = Prog.compile c.prog)
  (side : c.Side devm.getBal)
  (inv : c.PreInv devm ca sevm)

/-- The generic counterpart of `Blanc.Postcond`. -/
structure Post (ca : Adr) (_sevm : Sevm) (devm : Devm) : Prop where
  (side : c.Side devm.getBal)
  (inv : c.PostInv devm ca)

/-- The generic counterpart of `Blanc.State.Inv`. -/
structure StateInv (ca : Adr) (w : Jaune.State) : Prop where
  (code : some (w.getCode ca).toList = Prog.compile c.prog)
  (side : c.Side w.bal)
  (inv : c.Inv (w.getStor ca) 0 (w.bal ca))

end ContractSpec

/-! ## Instance 1 — WETH

Every slot is discharged from a lemma that already exists in `Solvent.lean`,
or from the arithmetic those lemmas' own proofs already perform.  No new proof
content: this is repackaging. -/

/-- `Stor.Solvent` in the record's argument order — it already is. -/
def wethSpec : ContractSpec where
  prog := weth
  Inv := Stor.Solvent
  Side := SumNof
  inv_forget := solvent_zero_of_solvent
  inv_mono := by
    intro s v b b' h hle
    unfold Stor.Solvent at h ⊢; omega
  inv_recv := by
    intro s v b b' h heq
    unfold Stor.Solvent at h ⊢
    rw [B256.toNat_zero] at h; omega
  side_le := by
    intro f g h hle
    unfold SumNof at h ⊢; omega
  side_transfer := by
    intro st st' caller callee wad h_sub h_side
    have h_nof : sum st.bal < 2 ^ 256 := h_side
    rcases of_state_transfer (callee := callee) h_sub h_nof with ⟨-, -, h_sum, -, -, -⟩
    show sum _ < 2 ^ 256
    rw [h_sum]; exact h_nof
  side_addBal := by
    intro w a val h_bound _
    show sum _ < 2 ^ 256
    rw [sum_addBal_eq w a val h_bound]; omega
  inv_transfer := by
    intro st st' caller callee ca wad v h_sub h_ne h_side h_inv
    have h_nof : sum st.bal < 2 ^ 256 := h_side
    rcases of_state_transfer (callee := callee) h_sub h_nof with
      ⟨h_t_stor, -, -, h_t_le, -, -⟩
    have h_mid : st'.bal ca = st.bal ca := by
      rcases State.of_subBal h_sub with ⟨-, h_st'⟩
      rw [h_st']
      show ((st.setBal caller _).get ca).bal = (st.get ca).bal
      rw [State.setBal_get_ne h_ne]
    have h_stor : (st'.addBal callee wad).getStor ca = st.getStor ca := h_t_stor ca
    have h_ge : (st.bal ca).toNat ≤ ((st'.addBal callee wad).bal ca).toNat := by
      by_cases h_eq : callee = ca
      · have h_add : (st'.addBal callee wad).bal ca = st.bal ca + wad := by
          rw [h_eq]
          show ((st'.setBal ca (st'.bal ca + wad)).get ca).bal = _
          rw [State.setBal_get_self]
          show st'.bal ca + wad = _
          rw [h_mid]
        rw [h_add]
        have h_le_wad : wad.toNat ≤ (st.bal caller).toNat := B256.toNat_le_toNat h_t_le
        have h_two : (st.bal ca).toNat + (st.bal caller).toNat ≤ sum st.bal :=
          add_le_sum_of_ne st.bal (fun hc => h_ne hc.symm)
        have h_nof' : B256.Nof (st.bal ca) wad := by unfold B256.Nof; omega
        rw [B256.toNat_add_eq_of_nof _ _ h_nof']
        omega
      · have h_other : (st'.addBal callee wad).bal ca = st.bal ca := by
          show ((st'.setBal callee _).get ca).bal = _
          rw [State.setBal_get_ne h_eq]
          exact h_mid
        rw [h_other]
    rw [h_stor]
    unfold Stor.Solvent at h_inv ⊢
    omega
  inv_recv_transfer := by
    intro st st' caller ca wad h_sub h_ne h_side h_inv
    have h_nof : sum st.bal < 2 ^ 256 := h_side
    rcases of_state_transfer (callee := ca) h_sub h_nof with ⟨h_t_stor, -, -, -, -, -⟩
    have h_stor : (st'.addBal ca wad).getStor ca = st.getStor ca := h_t_stor ca
    have h_bal : ((st'.addBal ca wad).bal ca).toNat = (st.bal ca).toNat + wad.toNat :=
      of_transfer_bal_target h_sub h_ne h_nof
    rw [h_stor]
    unfold Stor.Solvent at h_inv ⊢
    rw [B256.toNat_zero] at h_inv
    omega
  inv_addBal := by
    intro w ca a val v h_bound _ h_inv
    have h_nof_a : B256.Nof (w.bal a) val := by
      unfold B256.Nof; have := @le_sum w.bal a; omega
    have h_stor : (w.addBal a val).getStor ca = w.getStor ca := by
      show ((w.setBal a _).get ca).stor = (w.get ca).stor
      rw [State.setBal_get_stor]
    have h_ge : (w.bal ca).toNat ≤ ((w.addBal a val).bal ca).toNat := by
      by_cases h_eq : a = ca
      · subst h_eq
        show (w.bal a).toNat ≤ ((w.setBal a (w.bal a + val)).get a).bal.toNat
        rw [State.setBal_get_self]
        change (w.bal a).toNat ≤ (w.bal a + val).toNat
        rw [B256.toNat_add_eq_of_nof _ _ h_nof_a]; omega
      · show (w.bal ca).toNat ≤ ((w.setBal a _).get ca).bal.toNat
        rw [State.setBal_get_ne h_eq]; exact Nat.le_refl _
    rw [h_stor]
    unfold Stor.Solvent at h_inv ⊢
    omega

/-! ### The record reproduces the WETH bundles exactly

These three bridges are the evidence that `ContractSpec` is the interface the
existing statements consume: each generic bundle is interderivable with the
WETH-specific one it is meant to replace, field by field, with no side
conditions. -/

theorem wethSpec_pre_iff {ca : Adr} {sevm : Sevm} {devm : Devm} :
    wethSpec.Pre ca sevm devm ↔ Precond ca sevm devm :=
  ⟨fun h => ⟨h.code, h.side, h.inv⟩, fun h => ⟨h.code, h.nof, h.solvent⟩⟩

theorem wethSpec_post_iff {ca : Adr} {sevm : Sevm} {devm : Devm} :
    wethSpec.Post ca sevm devm ↔ Postcond ca sevm devm :=
  ⟨fun h => ⟨h.side, h.inv⟩, fun h => ⟨h.nof, h.solvent⟩⟩

theorem wethSpec_stateInv_iff {ca : Adr} {w : Jaune.State} :
    wethSpec.StateInv ca w ↔ State.Inv ca w :=
  ⟨fun h => ⟨h.code, h.side, h.inv⟩, fun h => ⟨h.code, h.nof, h.solvent⟩⟩

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
