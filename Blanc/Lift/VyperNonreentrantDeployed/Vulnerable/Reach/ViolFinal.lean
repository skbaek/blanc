import Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Reach.ViolReAdd
import Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Reach.ViolRemove
import Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Reach.ViolTop
import Blanc.Lift.RootMessages

/-!
# V−: the reachable ledger violation

The public headline is `vminus_attack`: on every covered fork, seven setup messages from the
disclosed initial world reach a pool whose LP ledger is sound (`totalSupply = balanceOf[attacker]
= 2000`), and the one attack message then settles with `totalSupply = 1800` below the attacker's
`balanceOf = 1906`. It is stated over the message fold `runMessages` and the storage observers
`supply`/`lpBalance`. These are **synthetic worlds** (synthetic clone, token and attacker code,
supplied CREATE targets, a creator-only start world): there is no live contract, so no deployment
root applies. The statement is an existence claim over a fixed scenario, so it is not vacuous:
the fold is computed and its two intermediate worlds exhibited.

The detailed results it is derived from, each composed from the frame theorems against the
frozen statements of `ViolBoundary`:

* `vminus_reach_violation : ViolationStmt` — for every covered fork and every world agreeing with
  `Checkpoint`'s finite read set, the violating message settles with `totalSupply = 1800 < 1906 =
  balanceOf[attacker]`, and the same execution's frames show the cross-function reentry;
* `vminus_reachable_capstone : CapstoneStmt` — eight root messages from the disclosed initial world,
  each from the previous settled world and each settling without error: implementation and clone
  creation, `initialize`, token and attacker creation, `approve`, `add_liquidity` (reaching the
  sound LP ledger), then the violation.

Frames: F5 `reAdd_frame` (re-entrant `add_liquidity`), F3/F4 `callback_frame`, F2 `remove_frame`,
F0/F1 `root_frame`.
-/

namespace Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Reach.Viol

/-- **The universal reachable V− violation.** -/
theorem vminus_reach_violation : ViolationStmt :=
  root_frame (remove_frame (callback_frame reAdd_frame))

/-- **The reachable V− capstone**: deployment, initialization and liquidity, then the violation. -/
theorem vminus_reachable_capstone : CapstoneStmt :=
  capstone_of_violation vminus_reach_violation

open Blanc.Lift.VyperNonreentrantDeployed.Fixed.Reach (initialWorld)
open Jaune Blanc.Lift Blanc.Lift.Witness

/-! ### The headline: the attack over the message fold -/

/-- The pool's `totalSupply` word (storage slot 26 of the clone `proxyAddr`). -/
def supply (W : State) : B256 := storOf W proxyAddr 26

/-- The pool's `balanceOf[h]` word. -/
def lpBalance (W : State) (h : Adr) : B256 := storOf W proxyAddr (lpSlot h)

/-- The seven setup messages, all from the code-free `creator`: implementation and clone creation,
`initialize` through the clone, token and attacker creation, `approve`, and `add_liquidity([1000,
1000], 0, attackerAddr)` with 1000 wei. -/
def vminusSetup : List RootMsg :=
  [.create implCreateMsg, .create cloneCreateMsg, .call initMsg, .create tokenCreateMsg,
    .create attackerCreateMsg, .call approveMsg, .call addMsg]

/-- The LP ledger before the attack: the supply equals the attacker's LP balance, 2000 (the
setup's only LP mint is to the attacker). -/
def LedgerSound (W : State) : Prop :=
  supply W = 2000 ∧ lpBalance W attackerAddr = 2000

/-- The LP ledger after the attack: the supply, 1800, is below the attacker's LP balance, 1906, so
one holder owns more LP than exists. -/
def LedgerBroken (W : State) : Prop :=
  supply W = 1800 ∧ lpBalance W attackerAddr = 1906

/-- **V−: the cross-function reentrancy attack breaks the LP ledger.** On every covered fork, the
setup messages run from the disclosed `initialWorld` to a world `W₀` with a sound ledger, and the
attack message `violMsg` (the creator calls the attacker contract, which calls
`remove_liquidity`; its ETH callback re-enters `add_liquidity` through the clone while
`remove_liquidity`'s lock is held, the two guards being on different slots) then settles to a
world `W` with the ledger broken. Synthetic worlds: no live contract, so no deployment root; the
reentry frame chain is in `vminus_reach_violation`. -/
theorem vminus_attack (fork : Fork) (hfork : CoveredFork fork) :
    ∃ W₀ W, runMessages fork initialWorld vminusSetup = some W₀ ∧ LedgerSound W₀ ∧
      runMessages fork W₀ [.call violMsg] = some W ∧ LedgerBroken W := by
  obtain ⟨postI, postP, postC, tokenPost, attackerPost, approvePost, addPost, post,
    h1, e1, h2, e2, h3, e3, h4, e4, h5, e5, h6, e6, h7, e7, hsound, -, hv⟩ :=
    vminus_reachable_capstone fork hfork
  obtain ⟨hm, he, -, hs, hl, -⟩ := hv
  obtain ⟨-, s0, l0, -⟩ := hsound
  refine ⟨addPost.state, post.state, ?_, ⟨s0, l0⟩, ?_, hs, ?_⟩
  · rw [vminusSetup, runMessages_cons_of_ok (m := .create implCreateMsg) h1 e1,
      runMessages_cons_of_ok (m := .create cloneCreateMsg) h2 e2,
      runMessages_cons_of_ok (m := .call initMsg) h3 e3,
      runMessages_cons_of_ok (m := .create tokenCreateMsg) h4 e4,
      runMessages_cons_of_ok (m := .create attackerCreateMsg) h5 e5,
      runMessages_cons_of_ok (m := .call approveMsg) h6 e6,
      runMessages_cons_of_ok (m := .call addMsg) h7 e7]
    rfl
  · rw [runMessages_cons_of_ok (m := .call violMsg) hm he]
    rfl
  · rw [lpBalance, lpSlot_attacker]
    exact hl

end Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Reach.Viol
