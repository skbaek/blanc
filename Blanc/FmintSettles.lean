-- FmintSettles.lean : fmint's `flashLoan`, walked forward to the callback.
--
-- Everything Blanc has said about `flashLoan` so far stops short of the `CALL`.
-- `Blanc/FlashSpec.lean` reads facts *off* a run that is given; `Blanc/
-- FmintReverts.lean` constructs the two guard-failure walks, neither of which
-- reaches the mint.  This module is the first construction that runs the
-- contract's state-changing half: three guards passed, a storage read priced
-- without knowing whether the key was warm, the mint pair written, and the
-- frame handed on to the callback-argument build.
--
-- Two things make the walk possible at all, and both are `Blanc/
-- ForwardCall.lean`'s:
--
-- * **`func_run`'s budget.**  A `Func` is concrete all the way down, so a
--   caller cannot abstract its tail and stop the walk that way.  `func_run (n)`
--   walks `n` nodes and hands the residual walk back, which is what lets a
--   trunk interleave tactic segments with rules the tactic has no arm for.
-- * **The two storage steps in continuation-passing form.**  A rule that hands
--   back a successor *term* is unusable four steps later: each state would
--   carry the previous one inside it.  `Func.runCompiledTo_sload_step` and
--   `_sstore_warm_step` hand the successor's base, charge and gas account to a
--   continuation as **variables with equations**, so the walk's states stay the
--   size of one instruction no matter how many storage operations precede them.
--
-- **No warmth premise, anywhere.**  The `SLOAD` step's charge is an `if` on the
-- frame's own accessed set, bounded by the schedule rather than decided, which
-- is A3 of `~/plans/adversarial-progress.md`: the statements this serves have no
-- premise about the frame's history, so the trunk may not buy exactness with
-- one.  The same goes for the two `SSTORE`s, whose EIP-2200 value cases are
-- bounded by `gasStorageSet`.
--
-- Scope, as everywhere in this genre: **message-call altitude, one selector,
-- construction direction only.**  Nothing here is an exhaustiveness claim, and
-- nothing here crosses the `CALL`.

import Blanc.ForwardCall
import Blanc.FmintReverts

namespace Blanc
namespace Fmint

open Jaune

set_option maxRecDepth 40000

/-- `Devm.logs` through `setMach`, the log-list analogue of
`Blanc/Forward.lean`'s `Devm.stack_setMach`.  Local to this module: the walk is
the only consumer, and the fact is one `rfl`. -/
lemma Devm.logs_setMach {devm : Devm} {m : Mach} :
    (devm.setMach m).logs = devm.logs := rfl

/-- The accessed storage keys through `setMach`, on the same footing. -/
lemma Devm.accessedStorageKeys_setMach {devm : Devm} {m : Mach} :
    (devm.setMach m).accessedStorageKeys = devm.accessedStorageKeys := rfl

/-- `Sevm.argWord` at its own definition, as a rewrite in the direction the walk
produces.  `arg k` compiles to `CALLDATALOAD (32 * k + 4)`, so a walk's stack
carries `Sevm.dataWord` where a statement carries `Sevm.argWord`; the two are
definitionally equal and this is the bridge `simp only` needs. -/
lemma Sevm.argWord_eq_dataWord {e : Sevm} {k : B256} :
    Sevm.argWord e k = Sevm.dataWord e ((32 * k) + 4) := rfl

/-! ## The two sub-terms of `flashLoan` this walk hands on to

`Blanc/FlashSpec.lean`'s `flashLoanFromCall` names the body from the `CALL`
onward.  These two name the two nodes before it, on the same principle and for
the same reason: each is *literally* the sub-term of `flashLoan` at that point,
so a walk that stops there hands back a goal stated in the contract's own
vocabulary, and the definition stops type-checking if the contract changes. -/

/-- `flashLoan`'s body from the callback-argument build onward: the memory
layout of spike 2, the seven `CALL` operands, and then `flashLoanFromCall`. -/
def flashLoanFromCallbackArgs : Func :=
  Ninst.dup 0 ::: storeCallbackHead +++
  pushList [0, 0] +++
  forwardCallbackData +++
  callbackArgsSize +++
  Ninst.pushB256 callbackArgsOffset :::
  Ninst.pushB256 0 :::
  Ninst.dup 6 :::
  Ninst.gas :::
  flashLoanFromCall

/-- `flashLoan`'s body from the mint's `Transfer` log onward. -/
def flashLoanFromMintLog : Func :=
  Ninst.dup 0 ::: mstoreAt 0 +++
  Ninst.dup 1 :::
  Ninst.pushB256 0 :::
  Ninst.pushB256 transferEvent :::
  logWith 2 0 1 +++
  flashLoanFromCallbackArgs

/-! ## The gas the trunk's first half can charge

Worst case, per **A3**: `gasColdSload` at both reads whose warmth is open, and
`gasStorageSet` at both stores.  The figure is a *bound* the frame must be able
to pay, not the frame's spend — the walk carries the slack as the difference
between the two `SSTORE` charges' bound and their value.

Written in Jaune's schedule symbols and never in numerals, in
`Blanc/FmintGas.lean`'s mold, with `flashLoanMintGas_eq` as the numeral. -/

/-- Every gas constant `flashLoan` can charge from the program entry to the end
of the mint pair, in the order it charges them: the entry `JUMPDEST`; `fsig`;
three dispatch forks, the first jumping and the other two falling through; the
leaf's `PUSH`/`EQ` and its taken arm; guard (0) passing; guard (1) passing;
guard (2) passing, with its `SLOAD` at the cold price; and the mint — the
receiver's balance read (cold price) and written (`gasStorageSet`), then the
supply read (warm, the guard already touched it) and written
(`gasStorageSet`). -/
def flashLoanMintGas : Nat :=
  gJumpdest
    + (gBase + gVerylow + gVerylow + gVerylow)
    + (gVerylow + gVerylow + gVerylow + (gVerylow + gHigh + gJumpdest))
    + (gVerylow + gVerylow + gVerylow + (gVerylow + gHigh))
    + (gVerylow + gVerylow + gVerylow + (gVerylow + gHigh))
    + (gVerylow + gVerylow + (gVerylow + gHigh + gJumpdest))
    + (gVerylow + gVerylow + gBase + gVerylow + gVerylow + (gVerylow + gHigh))
    + (gVerylow + gVerylow + gVerylow
        + (gBase + gVerylow + gVerylow + gVerylow + gVerylow)
        + (gVerylow + gHigh))
    + (gVerylow + gVerylow + gVerylow + (gBase + gVerylow) + gasColdSload
        + gVerylow + gVerylow + (gVerylow + gHigh))
    + (gVerylow + gasColdSload + gVerylow + gVerylow + gVerylow + gasStorageSet
        + (gBase + gVerylow) + gasWarmAccess + gVerylow + gVerylow
        + (gBase + gVerylow) + gasStorageSet)

/-- 44 523 gas, of which 40 000 is the two `SSTORE`s at their worst case and
4 200 the two reads at the cold price.  The control flow — dispatcher, three
guards and the stack work — is 323. -/
theorem flashLoanMintGas_eq : flashLoanMintGas = 44523 := by decide

/-! ## The supply slot is not a balance slot

The mint writes two keys and the statement below says what each holds
afterwards, which needs them to be *different* keys.  They are, and the reason
is the one `supplySlot`'s docstring gives: `B256.max` has all ninety-six high
bits set, so it is never address-shaped, while a `receiver` that passed guard
(1) is. -/

/-- `supplySlot` is not the image of an address. -/
theorem not_validAdr_supplySlot : ¬ ValidAdr supplySlot := by
  rw [validAdr_iff]
  decide

/-- …so a guard-(1)-passing `receiver` is a different storage key. -/
theorem supplySlot_ne_of_validAdr {w : B256} (h : ValidAdr w) : supplySlot ≠ w :=
  fun h_eq => not_validAdr_supplySlot (h_eq ▸ h)

/-! ## The trunk, as far as the mint pair

The walk is stated in continuation-passing form for the reason the module
banner gives: the state at the mint's end is a base the *rules* produced, not
one a caller can write, so the caller receives it as a variable together with
everything a later instruction needs to know about it.

What the continuation is handed, and why each clause is there:

* **the mint pair, as two storage equations** — proposal D5's pairing is
  complete *before* the `CALL`, so this is a fact about the state the callback
  is entered in and not merely about the state it is left in;
* **the untouched keys** — everything the mint did not write still reads what
  it read on entry, which is what a conservation argument downstream needs;
* **both keys warm, and warmth monotone** — the continuation's own `SSTORE`s
  (the burn, after the callback) are priced against this;
* **no log yet** — the mint's `Transfer` is the *next* node, so the frame's log
  list is still the caller's;
* **the gas account, two-sided** — bounded below by the worst case this
  statement's premise pays for, and above by the frame's own account.

There is no premise about the frame's accessed set and none about the `SSTORE`
value cases; both are bounded inside. -/

/-- **`fmint`'s `flashLoan` reaches its callback's argument build**, on a call
whose three guards pass, with the mint pair written and priced at worst case.

The premises are the pinned headline's, minus the ones only the post-`CALL`
half needs (`h_size`) and plus `h_static`, which every `SSTORE` and `LOG`
carries at this altitude.

What it does **not** say: nothing about the callee, nothing about what the
frame settles at — the outcome `out` is whatever the continuation produces —
and nothing about exhaustiveness. -/
theorem flashLoan_runCompiledTo_mint {sevm : Sevm} {pre : Devm}
    {receiver token amount : B256} {data : Bytes} {out : Execution}
    (h_sel : Sevm.selector sevm = flashLoanSelector)
    (h_dec : Sevm.DecodesCallWithTail sevm flashLoanSelector
      [receiver, token, amount] data)
    (h_token : token = sevm.currentTarget.toB256)
    (h_addr : ValidAdr receiver)
    (h_nof : B256.Nof (Devm.getStorVal pre sevm.currentTarget supplySlot) amount)
    (h_static : sevm.isStatic = false)
    (h_stack : pre.stack = [])
    (h_mem : pre.memory = Mem.empty)
    (h_gas : flashLoanMintGas ≤ pre.gasLeft)
    (h_cont : ∀ (b : Devm) (G : Nat),
      b.getStorVal sevm.currentTarget receiver
        = amount + pre.getStorVal sevm.currentTarget receiver →
      b.getStorVal sevm.currentTarget supplySlot
        = amount + pre.getStorVal sevm.currentTarget supplySlot →
      (∀ (a : Adr) (k : B256), (a, k) ≠ (sevm.currentTarget, receiver) →
        (a, k) ≠ (sevm.currentTarget, supplySlot) →
        b.getStorVal a k = pre.getStorVal a k) →
      (⟨sevm.currentTarget, receiver⟩ : Adr × B256) ∈ b.accessedStorageKeys →
      (⟨sevm.currentTarget, supplySlot⟩ : Adr × B256) ∈ b.accessedStorageKeys →
      (∀ p : Adr × B256, p ∈ pre.accessedStorageKeys →
        p ∈ b.accessedStorageKeys) →
      b.logs = pre.logs →
      pre.gasLeft - flashLoanMintGas ≤ G → G ≤ pre.gasLeft →
      Func.RunCompiledTo (fmint.main :: fmint.aux) sevm
        (b.setMach ⟨[amount, receiver], Mem.empty, G⟩) flashLoanFromMintLog out) :
    Prog.RunCompiledTo sevm pre fmint out := by
  have h_arg0 : Sevm.argWord sevm 0 = receiver := argWord_zero_of_decodes h_dec
  have h_arg2 : Sevm.argWord sevm 2 = amount := argWord_two_of_decodes h_dec
  have h_d0 : Sevm.dataWord sevm (32 * 0 + 4) = receiver := h_arg0
  have h_d2 : Sevm.dataWord sevm (32 * 2 + 4) = amount := h_arg2
  have h_slot : supplySlot ≠ receiver := supplySlot_ne_of_validAdr h_addr
  rw [flashLoanMintGas_eq] at h_gas h_cont
  set g := pre.gasLeft with hg
  refine
    Prog.runCompiledTo_intro (G := g - 1)
      (mid := pre.setMach ⟨[], Mem.empty, g - 1⟩)
      (by simp only [gJumpdest]; omega)
      (by rw [h_stack, h_mem])
      ?_
  -- the dispatcher, guard (0) and guard (1)
  func_run (39) [flashLoanSelector, 1, 0, 0, 1, 1, 0,
    ~~~ (0 : B256), (~~~ (0 : B256)) <<< (Nat.toB256 160).toNat, 0, supplySlot]
  · show sevm.currentTarget.toB256 =? Sevm.argWord sevm 1 = 1
    rw [argWord_one_of_decodes h_dec, h_token]
    show (if sevm.currentTarget.toB256 = sevm.currentTarget.toB256
      then (1 : B256) else 0) = 1
    rw [if_pos rfl]
  · show ((~~~ (0 : B256)) <<< (Nat.toB256 160).toNat).and
      (Sevm.argWord sevm 0) = 0
    rw [h_arg0, ← addressMask_eq_shl]
    exact validAdr_iff.mp h_addr
  -- guard (2): the supply read, priced without deciding warmth
  refine Func.runCompiledTo_sload_step rfl (by simp)
    (v := Devm.getStorVal pre sevm.currentTarget supplySlot) rfl
    (M := Mem.empty) rfl
    (by simp only [Devm.gasLeft_setMach, gasColdSload]; omega) ?_
  intro b₁ c₁ G₁ hw₁ hacc₁ hstor₁ hrc₁ hlog₁ hlo₁ hhi₁ hG₁
  simp only [Devm.gasLeft_setMach, gasWarmAccess, gasColdSload] at hG₁ hlo₁ hhi₁
  func_run (4) [~~~ (Devm.getStorVal pre sevm.currentTarget supplySlot), 0]
  · show ~~~ (Devm.getStorVal pre sevm.currentTarget supplySlot) <?
      Sevm.argWord sevm 2 = 0
    rw [h_arg2]
    show (if ~~~ (Devm.getStorVal pre sevm.currentTarget supplySlot) < amount
      then (1 : B256) else 0) = 0
    rw [if_neg (not_lt_of_ge (B256.le_not_of_nof h_nof))]
  -- (3) the mint: the receiver's balance, read then written
  refine Func.runCompiledTo_sload_step rfl (by simp)
    (v := Devm.getStorVal b₁ sevm.currentTarget (Sevm.argWord sevm 0)) rfl
    (M := Mem.empty) rfl
    (by simp only [Devm.gasLeft_setMach, gasColdSload]; omega) ?_
  intro b₂ c₂ G₂ hw₂ hacc₂ hstor₂ hrc₂ hlog₂ hlo₂ hhi₂ hG₂
  simp only [Devm.gasLeft_setMach, gasWarmAccess, gasColdSload] at hG₂ hlo₂ hhi₂
  func_run (3)
  refine Func.runCompiledTo_sstore_warm_step rfl hw₂ h_static
    (M := Mem.empty) rfl
    (by simp only [Devm.gasLeft_setMach, gasStorageSet]; omega) ?_
  intro b₃ c₃ G₃ hkey₃ hoth₃ hacc₃ hlog₃ hc₃ hG₃
  simp only [Devm.gasLeft_setMach, gasStorageSet] at hG₃ hc₃
  have hws₃ : (⟨sevm.currentTarget, supplySlot⟩ : Adr × B256)
      ∈ b₃.accessedStorageKeys := by
    rw [hacc₃]; exact hacc₂ _ hw₁
  -- the supply, read warm and written
  func_run (7) [supplySlot,
    Sevm.argWord sevm 2 + Devm.getStorVal b₃ sevm.currentTarget supplySlot,
    supplySlot]
  refine Func.runCompiledTo_sstore_warm_step (k := supplySlot)
    (v := Sevm.argWord sevm 2 + Devm.getStorVal b₃ sevm.currentTarget supplySlot)
    (s := [Sevm.argWord sevm 2, Sevm.argWord sevm 0]) ?_ ?_ h_static
    (M := Mem.empty) ?_ ?_ ?_
  · rfl
  · exact hws₃
  · rfl
  · simp only [Devm.gasLeft_setMach, gasStorageSet]; omega
  intro b₄ c₄ G₄ hkey₄ hoth₄ hacc₄ hlog₄ hc₄ hG₄
  simp only [Devm.gasLeft_setMach, gasStorageSet] at hG₄ hc₄
  -- the state the mint leaves, read off the four steps
  have h_ne_rs : ((sevm.currentTarget, Sevm.dataWord sevm (32 * 0 + 4))
      : Adr × B256) ≠ (sevm.currentTarget, supplySlot) := by
    simp only [ne_eq, Prod.mk.injEq, not_and]
    exact fun _ h => h_slot (h_d0 ▸ h.symm)
  have h_ne_sr : ((sevm.currentTarget, supplySlot) : Adr × B256)
      ≠ (sevm.currentTarget, Sevm.dataWord sevm (32 * 0 + 4)) :=
    fun h => h_ne_rs h.symm
  have h_sup₃ : b₃.getStorVal sevm.currentTarget supplySlot
      = pre.getStorVal sevm.currentTarget supplySlot := by
    simp only [hoth₃ _ _ h_ne_sr, Devm.getStorVal_setMach, hstor₂, hstor₁]
  have h_rcv : b₄.getStorVal sevm.currentTarget receiver
      = amount + pre.getStorVal sevm.currentTarget receiver := by
    rw [← h_d0, ← h_d2]
    simp only [hoth₄ _ _ h_ne_rs, Devm.getStorVal_setMach, hkey₃, hstor₁,
      Sevm.argWord_eq_dataWord]
  have h_sup : b₄.getStorVal sevm.currentTarget supplySlot
      = amount + pre.getStorVal sevm.currentTarget supplySlot := by
    rw [← h_d2]
    simp only [hkey₄, Sevm.argWord_eq_dataWord, h_sup₃]
  rw [h_arg0, h_arg2]
  refine h_cont b₄ G₄ h_rcv h_sup (fun a k h_ne_r h_ne_s => ?_) ?_ ?_
    (fun p hp => ?_)
    (by simp only [hlog₄, Devm.logs_setMach, hlog₃, hlog₂, hlog₁])
    (by omega) (by omega)
  · have h_nr : (a, k) ≠ (sevm.currentTarget, Sevm.dataWord sevm (32 * 0 + 4)) := by
      rw [h_d0]; exact h_ne_r
    simp only [hoth₄ _ _ h_ne_s, Devm.getStorVal_setMach, hoth₃ _ _ h_nr,
      hstor₂, hstor₁]
  · rw [hacc₄, ← h_d0]
    simp only [Devm.accessedStorageKeys_setMach, hacc₃]
    exact hw₂
  · rw [hacc₄]
    simp only [Devm.accessedStorageKeys_setMach]
    exact hws₃
  · rw [hacc₄]
    simp only [Devm.accessedStorageKeys_setMach, hacc₃]
    exact hacc₂ _ (hacc₁ _ hp)

end Fmint
end Blanc
