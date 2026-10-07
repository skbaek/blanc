import Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Reach.Checkpoint
import Blanc.Lift.ShadowTail

/-! # V4: the `Checkpoint` predicate — the finite read-set the violation depends on

`SoundCheckpoint` (in `Reach/Checkpoint.lean`) is the sound funded ledger that the V3 setup
*reaches*.  `Checkpoint W` below is what the **violation** needs of its pre-state `W`, and no
more: a finite agreement with the concrete reached shadow on exactly the keys the violating
execution reads, plus the accounts it reads (the four codes it runs, the code-free root caller
and the identity precompile's account), plus the code-free root caller.  It is a genuine
finite read-set agreement (a prefix of entries), not `WorldIs` with the whole checkpoint tables;
every world agreeing on these entries — and differing arbitrarily elsewhere — satisfies it.

The read set was measured by running the whole violation (EOA → `AttackerR` →
`remove_liquidity` → ETH callback → re-entrant `add_liquidity` → settle) over a closed world and
collecting the certificate interpreter's accessed storage keys at the settled root.  The twelve
proxy slots and two token slots in `readStor` are exactly that set; the values are the reached
world's (`lookupS storAdd`, proved by `readStor_storAdd`).  `ShadowTail.storOf_prefix_tail` turns
the agreement into a full engine shadow `readStor ++ storTailOf W`, so the universal violation
walk runs over any `W` with `Checkpoint W` (`ViolFinal.vminus_reach_violation`).

The keys, and why each is read:
* proxy slot `0` — `add_liquidity`'s reentrancy lock (read free, taken during the reentry);
* proxy slot `2` — `remove_liquidity`'s reentrancy lock (taken by the outer call, read free by
  the reentry: the cross-function-lock defect);
* proxy slots `7, 10, 12, 14, 15, 16` — the pool configuration the two functions read
  (`coins[1] = T` at 7, fee/admin-fee and the price-scale/packed config);
* proxy slots `8, 9` — `balances[0]`, `balances[1]` (the reserves, both 1000);
* proxy slot `26` — `totalSupply` (2000 before the violation, read for the stale cached supply);
* proxy slot `lpSlotA` — `balanceOf[attacker]` (2000 before, the LP ledger entry the mint grows);
* token `balanceOf[attacker]`, `balanceOf[proxy]` — read by the `transfer(attacker, 100)` the
  outer `remove_liquidity` makes after the callback.
-/

namespace Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Reach

open Blanc.Lift.VyperNonreentrantDeployed.Fixed.Reach (creator creatorFunds initialWorld rootBenv rootTenv)

open Jaune Blanc.Lift Blanc.Lift.Witness
open Blanc.Lift.VyperNonreentrantDeployed

/-- The twelve proxy slots and two token slots the violation reads, with the reached world's
values (the pre-violation checkpoint). Newest-first order is irrelevant: the keys are distinct. -/
def readStor : StorShadow :=
  [((proxyAddr, (0 : B256)), 0),
   ((proxyAddr, (2 : B256)), 0),
   ((proxyAddr, (7 : B256)), 292300327466180583640736966543256603931186508595),
   ((proxyAddr, (8 : B256)), 1000),
   ((proxyAddr, (9 : B256)), 1000),
   ((proxyAddr, (10 : B256)), 0),
   ((proxyAddr, (12 : B256)), 10000),
   ((proxyAddr, (14 : B256)), 0),
   ((proxyAddr, (15 : B256)), 1000000000000000000),
   ((proxyAddr, (16 : B256)), 1000000000000000000),
   ((proxyAddr, (26 : B256)), 2000),
   ((proxyAddr, lpSlotA), 2000),
   ((tokenAddr, Token20.balSlot attackerAddr), 0),
   ((tokenAddr, Token20.balSlot proxyAddr), 1000)]

/-- The accounts the violation reads (`AcctShadow` entries drop storage; the storage is
`readStor`): the four codes it runs, with the pool's 1000 wei; the root caller `creator`, whose
balance the root message's value transfer reads (`benvAfterTransferS`) and restates into the
shadow; and the identity precompile `0x04`, whose code every `CALL` preparation reads (the
EIP-7702 delegation check, `callPrep`) and whose view the four zero-value identity calls of
`remove_liquidity` restate.  The last two were measured by running the violation with a
poisoned tail after this prefix (V4 freeze probe): they are the only accounts read outside the
four codes, and with them in the prefix no lookup reaches the tail. -/
def readAcct : AcctShadow :=
  [(implAddr, ⟨1, 0, .empty, Vulnerable.code⟩),
   (proxyAddr, ⟨1, 1000, .empty, fwdCode⟩),
   (tokenAddr, ⟨1, 0, .empty, Token20.code⟩),
   (attackerAddr, ⟨1, 0, .empty, AttackerR.code⟩),
   (creator, ⟨0, creatorFunds - 1000, .empty, .empty⟩),
   ((4 : Adr), ⟨0, 0, .empty, .empty⟩)]

/-- **The checkpoint predicate the V4 violation depends on.** `W` agrees with the reached
world on exactly the fourteen storage slots the violation reads (`readStor`) and carries the
accounts it reads (`readAcct`: the four codes it runs, with the pool holding 1000 wei, the
code-free root caller with its balance, and the empty identity-precompile account); the root
caller `creator` is code-free.  Everything else about `W` is free. -/
def Checkpoint (W : State) : Prop :=
  (∀ e ∈ readStor, storOf W e.1.1 e.1.2 = e.2) ∧
    (∀ e ∈ readAcct, acctView (W.get e.1) = e.2) ∧
    (W.get creator).code = (default : ByteArray)

/-! ### The reached world satisfies `Checkpoint` -/

theorem readStor_storAdd : ∀ e ∈ readStor, lookupS storAdd e.1.1 e.1.2 = e.2 := by
  intro e he
  simp only [readStor, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    (first
      | (show lookupS storAdd proxyAddr _ = _; rw [lpSlot_attacker.symm] <;> decide +kernel)
      | decide +kernel)

theorem readAcct_acsB : ∀ e ∈ readAcct, lookupA acsB e.1 = e.2 := by
  intro e he
  simp only [readAcct, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl <;> kernel_rfl

/-- **The reached checkpoint world satisfies `Checkpoint`.** Discharged from the reached
world's description (`storAdd`/`acsB`), specialized to the finite read set. -/
theorem checkpoint_of_reached {W : State}
    (hs : ∀ a k, storOf W a k = lookupS storAdd a k) (ha : AcctAgree W acsB) : Checkpoint W := by
  refine ⟨fun e he => (hs e.1.1 e.1.2).trans (readStor_storAdd e he), fun e he => ?_, ?_⟩
  · exact (ha e.1).trans (readAcct_acsB e he)
  · have h := congrArg Acct.code (ha creator)
    exact h.trans (by kernel_rfl)

/-! ### The predicate reconstructs a full engine shadow

A world with `Checkpoint W` is described, at every address and key, by the finite read prefix
followed by `W`'s own tail — the shape the certificate interpreter's `Agree` needs.  The
interpreter reads only the prefix keys, so the free tail is never consulted; this is what makes
the finite agreement sufficient to run the universal violation walk over `W`. -/
theorem checkpoint_worldShadow {W : State} (h : Checkpoint W) :
    (∀ a k, storOf W a k = lookupS (readStor ++ storTailOf W) a k) ∧
      AcctAgree W (readAcct ++ acctTailOf W) :=
  ⟨storOf_prefix_tail h.1, acctAgree_prefix_tail h.2.1⟩

/-! ### Discharge at the V3 reached world, and the standalone pre-state

The world the seven-message V3 setup reaches (`setup_checkpoint`'s `addPost.state`, every
covered fork) satisfies `Checkpoint`.  This is the pre-state of the standalone violation
instance and the point at which the reachable capstone hands off to the violating call. -/
theorem setup_reaches_checkpoint (fork : Fork) (hfork : CoveredFork fork) :
    ∃ postI postP postC tokenPost attackerPost approvePost addPost : Devm,
      processCreateMessage (implCreateMsg fork initialWorld) = .ok postI ∧ postI.error = none ∧
      processCreateMessage (cloneCreateMsg fork postI.state) = .ok postP ∧ postP.error = none ∧
      processMessage (initMsg fork postP.state) = .ok postC ∧ postC.error = none ∧
      processCreateMessage (tokenCreateMsg fork postC.state) = .ok tokenPost ∧
      tokenPost.error = none ∧
      processCreateMessage (attackerCreateMsg fork tokenPost.state) = .ok attackerPost ∧
      attackerPost.error = none ∧
      processMessage (approveMsg fork attackerPost.state) = .ok approvePost ∧
      approvePost.error = none ∧
      processMessage (addMsg fork approvePost.state) = .ok addPost ∧ addPost.error = none ∧
      SoundCheckpoint addPost.state ∧ Checkpoint addPost.state := by
  obtain ⟨postI, postP, postC, tokenPost, attackerPost, approvePost, addPost,
    h1, e1, h2, e2, h3, e3, -, h4, e4, h5, e5, -, h6, e6, -, -, h7, e7, -, -, hsound, hstor,
    hacs⟩ := setup_checkpoint fork hfork
  exact ⟨postI, postP, postC, tokenPost, attackerPost, approvePost, addPost, h1, e1, h2, e2, h3,
    e3, h4, e4, h5, e5, h6, e6, h7, e7, hsound, checkpoint_of_reached hstor hacs⟩

end Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Reach
