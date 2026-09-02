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

/-! ## The gas the trunk's second half can charge

The mint's `Transfer` log, then the callback's argument build.  Only one charge
here is not a constant: the `CALLDATACOPY` that forwards the caller's own
`bytes` payload. -/

/-- The mint's `Transfer(0, receiver, amount)`: the word stored at `0x00`, the
three topics pushed, and `LOG3` over a one-word window that memory already
covers.  1 780 gas, of which 1 756 is the log itself. -/
def flashLoanLogGas : Nat :=
  (gVerylow + gBase + (gVerylow + gMemory))
    + (gVerylow + gBase + gVerylow + gVerylow + gBase)
    + (gLog + gLogdata * 32 + gLogtopic * 3)

/-- The `CALLDATACOPY` of `forwardArgTail`, the only charge on this whole path
that depends on the caller's input.

**The affine part costs `gasCopy + gMemory = 6` per 32-byte word** — three for
the copy and three for the linear share of the expansion — on top of
`gVerylow`; the memory term's quadratic share adds
`(7 + dataLen / 32)² / 512 − 7² / 512` beyond that, the only superlinear term in
the trunk.  The window's base is memory byte `224`, which is where
`forwardCallbackData` puts the payload. -/
def flashLoanCopyGas (dataLen : Nat) : Nat :=
  gVerylow + gasCopy * ceilDiv dataLen 32
    + (calculateMemoryGasCost (memExtSize 224 224 dataLen)
        - calculateMemoryGasCost 224)

/-- The callback's argument build: the six head words of the spike-2 layout, the
forwarded tail, the `argsSize` arithmetic, and the seven `CALL` operands down to
the `GAS` push.  145 gas plus the copy. -/
def flashLoanCallbackGas (dataLen : Nat) : Nat :=
  (gVerylow + gVerylow + gBase + gVerylow)
    + (gBase + gVerylow + (gVerylow + gMemory))
    + (gBase + gVerylow + (gVerylow + gMemory))
    + (gVerylow + (gVerylow + gMemory))
    + (gBase + gVerylow + (gVerylow + gMemory))
    + (gVerylow + gVerylow + (gVerylow + gMemory))
    + (gBase + gBase + gVerylow + gVerylow + gVerylow + gVerylow
        + gVerylow + gVerylow + gVerylow + gVerylow)
    + (gVerylow + gMemory)
    + (gVerylow + gVerylow + gVerylow + gVerylow + gVerylow)
    + flashLoanCopyGas dataLen
    + (gVerylow + gVerylow + gVerylow + gVerylow + gVerylow + gVerylow + gVerylow)
    + (gVerylow + gBase + gVerylow + gBase)

/-- **The trunk's whole charge**, from the program entry to the instant before
the `CALL`: the dispatcher, three guards and the mint pair
(`flashLoanMintGas`), the `Transfer` log (`flashLoanLogGas`), and the callback
build (`flashLoanCallbackGas`).

Worst case per **A3** — cold at both reads whose warmth is open, `gasStorageSet`
at both stores — and exact everywhere else. -/
def flashLoanPreCallGas (dataLen : Nat) : Nat :=
  flashLoanMintGas + flashLoanLogGas + flashLoanCallbackGas dataLen

/-- 46 451 gas on an empty payload: 44 523 to the end of the mint, 1 780 for the
log, and 148 for the argument build. -/
theorem flashLoanPreCallGas_zero : flashLoanPreCallGas 0 = 46451 := by decide

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

set_option maxRecDepth 733 in
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
  intro b₁ c₁ G₁ hw₁ hacc₁ hstor₁ _hbal₁ _hcode₁ hrc₁ hlog₁ hlo₁ hhi₁ hG₁
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
  intro b₂ c₂ G₂ hw₂ hacc₂ hstor₂ _hbal₂ _hcode₂ hrc₂ hlog₂ hlo₂ hhi₂ hG₂
  simp only [Devm.gasLeft_setMach, gasWarmAccess, gasColdSload] at hG₂ hlo₂ hhi₂
  func_run (3)
  refine Func.runCompiledTo_sstore_warm_step rfl hw₂ h_static
    (M := Mem.empty) rfl
    (by simp only [Devm.gasLeft_setMach, gasStorageSet]; omega) ?_
  intro b₃ c₃ G₃ hkey₃ hoth₃ _hbal₃ _hcode₃ hacc₃ hlog₃ hc₃ hG₃
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
  intro b₄ c₄ G₄ hkey₄ hoth₄ _hbal₄ _hcode₄ hacc₄ hlog₄ hc₄ hG₄
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
    (by simp only [hlog₄, Devm.setMach_logs, hlog₃, hlog₂, hlog₁])
    (by omega) (by omega)
  · have h_nr : (a, k) ≠ (sevm.currentTarget, Sevm.dataWord sevm (32 * 0 + 4)) := by
      rw [h_d0]; exact h_ne_r
    simp only [hoth₄ _ _ h_ne_s, Devm.getStorVal_setMach, hoth₃ _ _ h_nr,
      hstor₂, hstor₁]
  · rw [hacc₄, ← h_d0]
    simp only [Devm.setMach_accessedStorageKeys, hacc₃]
    exact hw₂
  · rw [hacc₄]
    simp only [Devm.setMach_accessedStorageKeys]
    exact hws₃
  · rw [hacc₄]
    simp only [Devm.setMach_accessedStorageKeys, hacc₃]
    exact hacc₂ _ (hacc₁ _ hp)

/-! ## What the frame holds when the callback is about to run

Three names, so that the state-at-`CALL` lemma below and everything downstream
say the same things the same way.

The memory image is written as the chain of writes it *is*, over the empty image
the frame entered with, rather than as a `Mem.Reads` predicate: the `CALL` reads
a window out of it and the crossing needs its `size`, and both are questions
about the chain. `Blanc/FlashSpec.lean`'s `callbackImage_nil` already says what
the same chain looks like as a byte list, which is the readable form; this is
the constructive one. -/

/-- **The callback's memory**, exactly as `flashLoan` builds it: the mint's
`Transfer` word at `0x00`, then the spike-2 layout of `Blanc/Fmint.lean` —
selector (overwriting that word), initiator, token, amount, fee `0`, the tail
offset `0xa0`, the tail's length at `0xc0` and its payload at `0xe0`. -/
def flashLoanCallMem (sevm : Sevm) (amount : B256) (payload : Bytes) : Mem :=
  ((((((((Mem.empty.write 0 amount.toBytes).write 0 onFlashLoanSelector.toBytes).write
    32 sevm.caller.toB256.toBytes).write
    64 sevm.currentTarget.toB256.toBytes).write
    96 amount.toBytes).write
    128 (0 : B256).toBytes).write
    160 (160 : B256).toBytes).write
    192 (Nat.toB256 payload.length).toBytes).write
    224 payload

/-- The `CALL`'s `argsSize` operand: four selector bytes, six head words and the
padded payload. `Blanc/FlashSpec.lean`'s `toNat_callbackArgsSize` reads it as
`196 + ceil32 dataLen`. -/
def flashLoanArgsSize (dataLen : Nat) : B256 :=
  0xc4 + ((~~~ (31 : B256)) &&& (31 + Nat.toB256 dataLen))

/-- The mint's `Transfer(0, receiver, amount)` entry. -/
def flashLoanMintLog (sevm : Sevm) (receiver amount : B256) : Log :=
  ⟨sevm.currentTarget, [transferEvent, 0, receiver], amount.toBytes⟩

/-! ## The spawned frame, named (A5)

`Blanc/ForwardCall.lean`'s `callSpawnParent`/`callSpawnMsg` name what *a*
`value = 0` `CALL` spawns. The two below name what **fmint's callback** spawns,
by fixing the four operands the trunk determines: `argsOffset = 0x1c`,
`argsSize = flashLoanArgsSize dataLen`, and an empty `(0, 0)` return window.

What they do **not** fix is what the crossing itself produces — the
delegation-resolved parent `d1`, the forwarded stipend `mcs`, the callee's code
and code address, and the delegation flag — because those are functions of the
*world*, not of `flashLoan`'s construction. That is the honest boundary: A5
requires the success form's callback premises to be stated over named
definitions rather than an existential, and these are the names; the arguments
they still take are the ones a caller has to bind anyway. -/

/-- The parent state fmint's callback `CALL` suspends on. -/
def flashLoanSpawnParent (d1 : Devm) (charge dataLen : Nat) : Devm :=
  callSpawnParent d1 charge callbackArgsOffset.toNat
    (flashLoanArgsSize dataLen).toNat 0 0

/-- The message fmint's callback `CALL` builds: `onFlashLoan(...)` read out of
the parent's own memory, sent to `receiver` with no value.  `receiver` owns the
storage and `cadr` is the account whose code runs; they differ exactly when the
borrower carries a delegation designator, so `cadr` joins `code` and `dp` among
the operands the world supplies rather than `flashLoan`'s construction. -/
def flashLoanSpawnMsg (sevm : Sevm) (p : Devm) (mcs : Nat) (receiver : B256)
    (cadr : Adr) (dataLen : Nat) (code : ByteArray) (dp : Bool) : Msg :=
  callSpawnMsg sevm p mcs receiver.toAdr cadr callbackArgsOffset.toNat
    (flashLoanArgsSize dataLen).toNat code dp

/-! ## The trunk, all the way to the `CALL`

The walk continues `flashLoan_runCompiledTo_mint` through the `Transfer` log and
the callback's argument build, and stops on the `CALL` instruction itself.

Two mechanisms carry the second half, both `Blanc/ForwardCall.lean`'s and both
measured rather than guessed:

* **every `MSTORE` names its image.** `func_run`'s own `MSTORE` arm builds the
  image as a term, and eight of them in a row make each later state carry a
  chain whose payloads are concrete — a `keccak`-derived selector among them —
  so every `whnf` the walk performs runs that chain. Measured: ≈ 0.1 s per node
  before the layout and ≈ 1.5 s per node after it, against ≈ 0.1 s throughout
  with `Func.runCompiledTo_mstore_step`.
* **the `CALLDATACOPY` is applied by hand.** Its charge is affine in the
  caller's `data.length`, and `func_run` requires numeral charges (**F10**).

The conclusion is the exact state the crossing starts from: the seven `CALL`
operands with `gw` the frame's own remaining gas, the memory image as a named
chain, the mint pair, the log, and a two-sided gas account. -/

set_option maxRecDepth 796 in
/-- **`fmint`'s `flashLoan` reaches its `CALL`**, on a call whose three guards
pass.

Everything the continuation is handed is a fact about the state the *callback*
is entered in, which is the point: the mint pair is complete, the `Transfer` is
emitted, and the memory window the callee will read is fully written, all before
any of the borrower's code runs.

`gw`, the first operand, is `Nat.toB256 G` — the `GAS` push is the frame's own
account, so the amount offered to the callback is pinned by the same arithmetic
that bounds `G`. No premise about the borrower appears anywhere. -/
theorem flashLoan_runCompiledTo_call {sevm : Sevm} {pre : Devm}
    {receiver token amount : B256} {data : Bytes} {out : Execution}
    (h_sel : Sevm.selector sevm = flashLoanSelector)
    (h_dec : Sevm.DecodesCallWithTail sevm flashLoanSelector
      [receiver, token, amount] data)
    (h_size : 196 + ceil32 data.length < 2 ^ 256)
    (h_token : token = sevm.currentTarget.toB256)
    (h_addr : ValidAdr receiver)
    (h_nof : B256.Nof (Devm.getStorVal pre sevm.currentTarget supplySlot) amount)
    (h_static : sevm.isStatic = false)
    (h_stack : pre.stack = [])
    (h_mem : pre.memory = Mem.empty)
    (h_gas : flashLoanPreCallGas data.length ≤ pre.gasLeft)
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
      b.logs = pre.logs ++ [flashLoanMintLog sevm receiver amount] →
      pre.gasLeft - flashLoanPreCallGas data.length ≤ G → G ≤ pre.gasLeft →
      Func.RunCompiledTo (fmint.main :: fmint.aux) sevm
        (b.setMach ⟨[Nat.toB256 G, receiver, 0, callbackArgsOffset,
            flashLoanArgsSize data.length, 0, 0, amount, receiver],
          flashLoanCallMem sevm amount data, G⟩) flashLoanFromCall out) :
    Prog.RunCompiledTo sevm pre fmint out := by
  have h_len_lt : data.length < 2 ^ 256 := by
    have := Nat.le_ceil32 data.length; omega
  have h_pre : flashLoanMintGas + flashLoanLogGas + flashLoanCallbackGas data.length
      ≤ pre.gasLeft := h_gas
  refine flashLoan_runCompiledTo_mint h_sel h_dec h_token h_addr h_nof h_static
    h_stack h_mem (by
      simp only [flashLoanLogGas, flashLoanCallbackGas, flashLoanCopyGas,
        gVerylow, gBase, gMemory, gLog, gLogdata, gLogtopic] at h_pre; omega) ?_
  intro b₀ G₀ h_rcv h_sup h_oth hw_r hw_s hw_mono h_log h_lo h_hi
  rw [flashLoanMintGas_eq] at h_lo
  -- the mint's `Transfer`, then the callback's argument build
  have hG₀ : flashLoanLogGas + flashLoanCallbackGas data.length ≤ G₀ := by
    simp only [flashLoanMintGas_eq] at h_pre; omega
  have hN : flashLoanLogGas + 145 ≤ G₀ := by
    simp only [flashLoanLogGas, flashLoanCallbackGas, flashLoanCopyGas, gVerylow,
      gBase, gMemory, gLog, gLogdata, gLogtopic] at hG₀ ⊢
    omega
  func_run (8) [gMemory]
  · exact Devm.extCost_empty_word
  refine Func.runCompiledTo_log_step (topics := [transferEvent, 0, receiver])
    (s := [amount, receiver]) rfl rfl h_static
    (M := Mem.empty.write 0 amount.toBytes) rfl
    (c := 1756) (payload := amount.toBytes)
    (M' := Mem.empty.write 0 amount.toBytes) ?_ ?_ ?_
    (by simp only [Devm.gasLeft_setMach, flashLoanLogGas, gVerylow, gBase,
      gMemory, gLog, gLogdata, gLogtopic] at hN ⊢; omega) ?_
  · exact Devm.extCost_add_of_size Mem.size_write_word (by decide)
  · exact Mem.read_write_word
  · exact Mem.read_snd_eq_self (by rw [Mem.size_write_word]; decide)
  intro b G hlogb hstorb _hbalb _hcodeb haccb hGb
  simp only [Devm.gasLeft_setMach, flashLoanLogGas, gVerylow, gBase, gMemory,
    gLog, gLogdata, gLogtopic] at hGb hN
  have h_gas' : flashLoanCallbackGas data.length ≤ G := by
    simp only [flashLoanLogGas, gVerylow, gBase, gMemory, gLog, gLogdata,
      gLogtopic] at hG₀; omega
  have hG : 145 ≤ G := by
    simp only [flashLoanCallbackGas, gVerylow, gBase, gMemory] at h_gas'
    omega
  have h_ptr : (4 : B256) + Sevm.dataWord sevm (32 * 3 + 4) = 132 := by
    rw [show Sevm.dataWord sevm (32 * 3 + 4) = Nat.toB256 128 from
      argWord_three_of_decodes h_dec]
    decide
  have h_len : Sevm.dataWord sevm 132 = Nat.toB256 data.length := by
    rw [show (132 : B256) = Nat.toB256 132 from rfl,
      ← tailPtr_three_of_decodes h_dec]
    exact tailLen_three_of_decodes h_dec
  func_run (3)
  refine Func.runCompiledTo_mstore_step
    (M := Mem.empty.write 0 amount.toBytes) (c := 3) rfl rfl ?_ ?_ ?_
  · exact Devm.extCost_add_of_size Mem.size_write_word (by decide)
  · simp only [Devm.gasLeft_setMach]; omega
  intro M₁ G₁ hM₁ hg₁
  simp only [Devm.gasLeft_setMach] at hg₁
  have s₁ : M₁.size = 32 := by
    rw [← hM₁, Mem.size_write_word_at, Mem.size_write_word]; decide
  func_run (2)
  refine Func.runCompiledTo_mstore_step (M := M₁) (c := 6) rfl rfl ?_ ?_ ?_
  · exact Devm.extCost_add_of_size s₁ (by decide)
  · simp only [Devm.gasLeft_setMach]; omega
  intro M₂ G₂ hM₂ hg₂
  simp only [Devm.gasLeft_setMach] at hg₂
  have s₂ : M₂.size = 64 := by
    rw [← hM₂, Mem.size_write_word_at, s₁]; decide
  func_run (2)
  refine Func.runCompiledTo_mstore_step (M := M₂) (c := 6) rfl rfl ?_ ?_ ?_
  · exact Devm.extCost_add_of_size s₂ (by decide)
  · simp only [Devm.gasLeft_setMach]; omega
  intro M₃ G₃ hM₃ hg₃
  simp only [Devm.gasLeft_setMach] at hg₃
  have s₃ : M₃.size = 96 := by
    rw [← hM₃, Mem.size_write_word_at, s₂]; decide
  func_run (1)
  refine Func.runCompiledTo_mstore_step (M := M₃) (c := 6) rfl rfl ?_ ?_ ?_
  · exact Devm.extCost_add_of_size s₃ (by decide)
  · simp only [Devm.gasLeft_setMach]; omega
  intro M₄ G₄ hM₄ hg₄
  simp only [Devm.gasLeft_setMach] at hg₄
  have s₄ : M₄.size = 128 := by
    rw [← hM₄, Mem.size_write_word_at, s₃]; decide
  func_run (2)
  refine Func.runCompiledTo_mstore_step (M := M₄) (c := 6) rfl rfl ?_ ?_ ?_
  · exact Devm.extCost_add_of_size s₄ (by decide)
  · simp only [Devm.gasLeft_setMach]; omega
  intro M₅ G₅ hM₅ hg₅
  simp only [Devm.gasLeft_setMach] at hg₅
  have s₅ : M₅.size = 160 := by
    rw [← hM₅, Mem.size_write_word_at, s₄]; decide
  func_run (2)
  refine Func.runCompiledTo_mstore_step (M := M₅) (c := 6) rfl rfl ?_ ?_ ?_
  · exact Devm.extCost_add_of_size s₅ (by decide)
  · simp only [Devm.gasLeft_setMach]; omega
  intro M₆ G₆ hM₆ hg₆
  simp only [Devm.gasLeft_setMach] at hg₆
  have s₆ : M₆.size = 192 := by
    rw [← hM₆, Mem.size_write_word_at, s₅]; decide
  func_run (10) [(132 : B256)]
  rw [h_len]
  refine Func.runCompiledTo_mstore_step (M := M₆) (c := 6) rfl rfl ?_ ?_ ?_
  · exact Devm.extCost_add_of_size s₆ (by decide)
  · simp only [Devm.gasLeft_setMach]; omega
  intro M₇ G₇ hM₇ hg₇
  simp only [Devm.gasLeft_setMach] at hg₇
  have s₇ : M₇.size = 224 := by
    rw [← hM₇, Mem.size_write_word_at, s₆]; decide
  func_run (5) [(164 : B256)]
  have h_dl : (Nat.toB256 data.length).toNat = data.length := by
    rw [B256.toNat_toB256]; exact Nat.mod_eq_of_lt h_len_lt
  have h164 : (Nat.toB256 132 + 32 : B256).toNat = (164 : B256).toNat := by decide
  have h_bytes : sevm.data.sliceD (164 : B256).toNat
      (Nat.toB256 data.length).toNat 0 = data := by
    have h_tb : Sevm.tailBytes sevm 3 = data :=
      tailBytes_three_of_decodes h_len_lt h_dec
    refine Eq.trans ?_ h_tb
    simp only [Sevm.tailBytes, tailPtr_three_of_decodes h_dec,
      tailLen_three_of_decodes h_dec, h164]
  refine Func.runCompiledTo_calldatacopy_step (M := M₇)
    (c := flashLoanCopyGas data.length) rfl rfl ?_ ?_ ?_
  · refine Devm.extCost_add_of_size s₇ ?_
    simp only [h_dl, flashLoanCopyGas,
      show ((6 + 1 : B256) * 32).toNat = 224 from rfl]
  · simp only [Devm.gasLeft_setMach, flashLoanCallbackGas, gVerylow, gBase,
      gMemory] at h_gas' ⊢
    omega
  intro M₈ G₈ hM₈ hg₈
  simp only [Devm.gasLeft_setMach, h_bytes] at hM₈ hg₈
  have hG₈ : 31 ≤ G₈ := by
    simp only [flashLoanCallbackGas, gVerylow, gBase, gMemory] at h_gas'
    omega
  func_run (11)
  -- the state at the `CALL`, read off the eight named images
  have i0 : ((0 : B256) * 32).toNat = 0 := rfl
  have i1 : ((1 : B256) * 32).toNat = 32 := rfl
  have i2 : ((2 : B256) * 32).toNat = 64 := rfl
  have i3 : ((3 : B256) * 32).toNat = 96 := rfl
  have i4 : ((4 : B256) * 32).toNat = 128 := rfl
  have i5 : ((5 : B256) * 32).toNat = 160 := rfl
  have i6 : ((6 : B256) * 32).toNat = 192 := rfl
  have i7 : ((6 + 1 : B256) * 32).toNat = 224 := rfl
  simp only [i0, i1, i2, i3, i4, i5, i6, i7] at hM₁ hM₂ hM₃ hM₄ hM₅ hM₆ hM₇ hM₈
  have h_img : M₈ = flashLoanCallMem sevm amount data := by
    rw [← hM₈, ← hM₇, ← hM₆, ← hM₅, ← hM₄, ← hM₃, ← hM₂, ← hM₁]
    rfl
  rw [h_img]
  refine h_cont b (G₈ - 31) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [hstorb]; exact h_rcv
  · rw [hstorb]; exact h_sup
  · intro a k hk₁ hk₂; rw [hstorb]; exact h_oth a k hk₁ hk₂
  · rw [haccb]; exact hw_r
  · rw [haccb]; exact hw_s
  · intro p hp; rw [haccb]; exact hw_mono p hp
  · rw [hlogb]
    simp only [Devm.setMach_logs, h_log, flashLoanMintLog]
  · simp only [flashLoanPreCallGas, flashLoanMintGas_eq, flashLoanLogGas,
      flashLoanCallbackGas, gVerylow, gBase, gMemory, gLog, gLogdata,
      gLogtopic] at *
    omega
  · omega

/-! ## The trunk again, existential in the outcome

The two lemmas above fix their outcome `out` before the walk begins, which is
the right shape for a statement that knows where it ends — and the wrong one
for the settlement trichotomy, whose outcome is *decided by a case analysis on
the callback's settle*, inside the continuation, over states the walk itself
introduced.  `Blanc/ForwardCall.lean`'s `ExecSat` carries exactly that: the
outcome is existential, constrained by a predicate, and the fatal arm — a
`CALL` whose child settles on the non-consensus channel, which
`Func.RunCompiledTo` cannot even express — has a terminal of its own.

The two walks below are the two above, re-run over `ExecSat`.  Same premises,
same hints, same charges, same handed-on facts; the `func_run` segments run
inside `Func.execSat_segment`'s transformer and the storage/memory steps use
the `execSat_*` siblings.  The fixed-outcome forms stay: they are checkpoint
2b's landed surface, and their exact-state conclusions are what a *known*
outcome composes against. -/

set_option maxRecDepth 736 in
/-- `flashLoan_runCompiledTo_mint`, existential in the outcome. -/
theorem flashLoan_execSat_mint {sevm : Sevm} {pre : Devm}
    {receiver token amount : B256} {data : Bytes} {P : Execution → Prop}
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
      b.error = pre.error →
      pre.gasLeft - flashLoanMintGas ≤ G → G ≤ pre.gasLeft →
      Func.ExecSat (fmint.main :: fmint.aux) sevm
        (b.setMach ⟨[amount, receiver], Mem.empty, G⟩) flashLoanFromMintLog P) :
    Prog.ExecSat sevm pre fmint P := by
  have h_arg0 : Sevm.argWord sevm 0 = receiver := argWord_zero_of_decodes h_dec
  have h_arg2 : Sevm.argWord sevm 2 = amount := argWord_two_of_decodes h_dec
  have h_d0 : Sevm.dataWord sevm (32 * 0 + 4) = receiver := h_arg0
  have h_d2 : Sevm.dataWord sevm (32 * 2 + 4) = amount := h_arg2
  have h_slot : supplySlot ≠ receiver := supplySlot_ne_of_validAdr h_addr
  rw [flashLoanMintGas_eq] at h_gas h_cont
  set g := pre.gasLeft with hg
  refine Prog.execSat_intro (G := g - 1)
    (mid := pre.setMach ⟨[], Mem.empty, g - 1⟩)
    (by simp only [gJumpdest]; omega)
    (by rw [h_stack, h_mem])
    ?_
  apply Func.execSat_segment
  · intro ex hex
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
    exact hex
  refine Func.execSat_sload_step rfl (by simp)
    (v := Devm.getStorVal pre sevm.currentTarget supplySlot) rfl
    (M := Mem.empty) rfl
    (by simp only [Devm.gasLeft_setMach, gasColdSload]; omega) ?_
  intro b₁ c₁ G₁ hw₁ hacc₁ hstor₁ _hbal₁ _hcode₁ hrc₁ hlog₁ _hout₁ herr₁
    _hdelete₁ hlo₁ hhi₁ hG₁
  simp only [Devm.gasLeft_setMach, gasWarmAccess, gasColdSload] at hG₁ hlo₁ hhi₁
  apply Func.execSat_segment
  · intro ex hex
    func_run (4) [~~~ (Devm.getStorVal pre sevm.currentTarget supplySlot), 0]
    · show ~~~ (Devm.getStorVal pre sevm.currentTarget supplySlot) <?
        Sevm.argWord sevm 2 = 0
      rw [h_arg2]
      show (if ~~~ (Devm.getStorVal pre sevm.currentTarget supplySlot) < amount
        then (1 : B256) else 0) = 0
      rw [if_neg (not_lt_of_ge (B256.le_not_of_nof h_nof))]
    exact hex
  refine Func.execSat_sload_step rfl (by simp)
    (v := Devm.getStorVal b₁ sevm.currentTarget (Sevm.argWord sevm 0)) rfl
    (M := Mem.empty) rfl
    (by simp only [Devm.gasLeft_setMach, gasColdSload]; omega) ?_
  intro b₂ c₂ G₂ hw₂ hacc₂ hstor₂ _hbal₂ _hcode₂ hrc₂ hlog₂ _hout₂ herr₂
    _hdelete₂ hlo₂ hhi₂ hG₂
  simp only [Devm.gasLeft_setMach, gasWarmAccess, gasColdSload] at hG₂ hlo₂ hhi₂
  apply Func.execSat_segment
  · intro ex hex
    func_run (3)
    exact hex
  refine Func.execSat_sstore_warm_step rfl hw₂ h_static
    (M := Mem.empty) rfl
    (by simp only [Devm.gasLeft_setMach, gasStorageSet]; omega) ?_
  intro b₃ c₃ G₃ hkey₃ hoth₃ _hbal₃ _hcode₃ hacc₃ hlog₃ _hout₃ herr₃
    _hdelete₃ _hrefund₃ hc₃ hG₃
  simp only [Devm.gasLeft_setMach, gasStorageSet] at hG₃ hc₃
  have hws₃ : (⟨sevm.currentTarget, supplySlot⟩ : Adr × B256)
      ∈ b₃.accessedStorageKeys := by
    rw [hacc₃]; exact hacc₂ _ hw₁
  apply Func.execSat_segment
  · intro ex hex
    func_run (7) [supplySlot,
      Sevm.argWord sevm 2 + Devm.getStorVal b₃ sevm.currentTarget supplySlot,
      supplySlot]
    exact hex
  refine Func.execSat_sstore_warm_step (k := supplySlot)
    (v := Sevm.argWord sevm 2 + Devm.getStorVal b₃ sevm.currentTarget supplySlot)
    (s := [Sevm.argWord sevm 2, Sevm.argWord sevm 0]) ?_ ?_ h_static
    (M := Mem.empty) ?_ ?_ ?_
  · rfl
  · exact hws₃
  · rfl
  · simp only [Devm.gasLeft_setMach, gasStorageSet]; omega
  intro b₄ c₄ G₄ hkey₄ hoth₄ _hbal₄ _hcode₄ hacc₄ hlog₄ _hout₄ herr₄
    _hdelete₄ _hrefund₄ hc₄ hG₄
  simp only [Devm.gasLeft_setMach, gasStorageSet] at hG₄ hc₄
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
    (by simp only [hlog₄, Devm.setMach_logs, hlog₃, hlog₂, hlog₁])
    (by simp only [herr₄, Devm.setMach_error, herr₃, herr₂, herr₁])
    (by omega) (by omega)
  · have h_nr : (a, k) ≠ (sevm.currentTarget, Sevm.dataWord sevm (32 * 0 + 4)) := by
      rw [h_d0]; exact h_ne_r
    simp only [hoth₄ _ _ h_ne_s, Devm.getStorVal_setMach, hoth₃ _ _ h_nr,
      hstor₂, hstor₁]
  · rw [hacc₄, ← h_d0]
    simp only [Devm.setMach_accessedStorageKeys, hacc₃]
    exact hw₂
  · rw [hacc₄]
    simp only [Devm.setMach_accessedStorageKeys]
    exact hws₃
  · rw [hacc₄]
    simp only [Devm.setMach_accessedStorageKeys, hacc₃]
    exact hacc₂ _ (hacc₁ _ hp)

set_option maxRecDepth 799 in
/-- `flashLoan_runCompiledTo_call`, existential in the outcome: the exact state
at the `CALL`, handed to a continuation that will decide the outcome by case
analysis on the callback's settle. -/
theorem flashLoan_execSat_call {sevm : Sevm} {pre : Devm}
    {receiver token amount : B256} {data : Bytes} {P : Execution → Prop}
    (h_sel : Sevm.selector sevm = flashLoanSelector)
    (h_dec : Sevm.DecodesCallWithTail sevm flashLoanSelector
      [receiver, token, amount] data)
    (h_size : 196 + ceil32 data.length < 2 ^ 256)
    (h_token : token = sevm.currentTarget.toB256)
    (h_addr : ValidAdr receiver)
    (h_nof : B256.Nof (Devm.getStorVal pre sevm.currentTarget supplySlot) amount)
    (h_static : sevm.isStatic = false)
    (h_stack : pre.stack = [])
    (h_mem : pre.memory = Mem.empty)
    (h_gas : flashLoanPreCallGas data.length ≤ pre.gasLeft)
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
      b.logs = pre.logs ++ [flashLoanMintLog sevm receiver amount] →
      b.error = pre.error →
      pre.gasLeft - flashLoanPreCallGas data.length ≤ G → G ≤ pre.gasLeft →
      Func.ExecSat (fmint.main :: fmint.aux) sevm
        (b.setMach ⟨[Nat.toB256 G, receiver, 0, callbackArgsOffset,
            flashLoanArgsSize data.length, 0, 0, amount, receiver],
          flashLoanCallMem sevm amount data, G⟩) flashLoanFromCall P) :
    Prog.ExecSat sevm pre fmint P := by
  have h_len_lt : data.length < 2 ^ 256 := by
    have := Nat.le_ceil32 data.length; omega
  have h_pre : flashLoanMintGas + flashLoanLogGas + flashLoanCallbackGas data.length
      ≤ pre.gasLeft := h_gas
  refine flashLoan_execSat_mint h_sel h_dec h_token h_addr h_nof h_static
    h_stack h_mem (by
      simp only [flashLoanLogGas, flashLoanCallbackGas, flashLoanCopyGas,
        gVerylow, gBase, gMemory, gLog, gLogdata, gLogtopic] at h_pre; omega) ?_
  intro b₀ G₀ h_rcv h_sup h_oth hw_r hw_s hw_mono h_log h_err h_lo h_hi
  rw [flashLoanMintGas_eq] at h_lo
  -- the mint's `Transfer`, then the callback's argument build
  have hG₀ : flashLoanLogGas + flashLoanCallbackGas data.length ≤ G₀ := by
    simp only [flashLoanMintGas_eq] at h_pre; omega
  have hN : flashLoanLogGas + 145 ≤ G₀ := by
    simp only [flashLoanLogGas, flashLoanCallbackGas, flashLoanCopyGas, gVerylow,
      gBase, gMemory, gLog, gLogdata, gLogtopic] at hG₀ ⊢
    omega
  apply Func.execSat_segment
  · intro ex hex
    func_run (8) [gMemory]
    · exact Devm.extCost_empty_word
    exact hex
  refine Func.execSat_log_step (topics := [transferEvent, 0, receiver])
    (s := [amount, receiver]) rfl rfl h_static
    (M := Mem.empty.write 0 amount.toBytes) rfl
    (c := 1756) (payload := amount.toBytes)
    (M' := Mem.empty.write 0 amount.toBytes) ?_ ?_ ?_
    (by simp only [Devm.gasLeft_setMach, flashLoanLogGas, gVerylow, gBase,
      gMemory, gLog, gLogdata, gLogtopic] at hN ⊢; omega) ?_
  · exact Devm.extCost_add_of_size Mem.size_write_word (by decide)
  · exact Mem.read_write_word
  · exact Mem.read_snd_eq_self (by rw [Mem.size_write_word]; decide)
  intro b G hlogb hstorb _hbalb _hcodeb haccb _hrefundb _houtb herrb
    _hdeleteb hGb
  simp only [Devm.gasLeft_setMach, flashLoanLogGas, gVerylow, gBase, gMemory,
    gLog, gLogdata, gLogtopic] at hGb hN
  have h_gas' : flashLoanCallbackGas data.length ≤ G := by
    simp only [flashLoanLogGas, gVerylow, gBase, gMemory, gLog, gLogdata,
      gLogtopic] at hG₀; omega
  have hG : 145 ≤ G := by
    simp only [flashLoanCallbackGas, gVerylow, gBase, gMemory] at h_gas'
    omega
  have h_ptr : (4 : B256) + Sevm.dataWord sevm (32 * 3 + 4) = 132 := by
    rw [show Sevm.dataWord sevm (32 * 3 + 4) = Nat.toB256 128 from
      argWord_three_of_decodes h_dec]
    decide
  have h_len : Sevm.dataWord sevm 132 = Nat.toB256 data.length := by
    rw [show (132 : B256) = Nat.toB256 132 from rfl,
      ← tailPtr_three_of_decodes h_dec]
    exact tailLen_three_of_decodes h_dec
  apply Func.execSat_segment
  · intro ex hex
    func_run (3)
    exact hex
  refine Func.execSat_mstore_step
    (M := Mem.empty.write 0 amount.toBytes) (c := 3) rfl rfl ?_ ?_ ?_
  · exact Devm.extCost_add_of_size Mem.size_write_word (by decide)
  · simp only [Devm.gasLeft_setMach]; omega
  intro M₁ G₁ hM₁ hg₁
  simp only [Devm.gasLeft_setMach] at hg₁
  have s₁ : M₁.size = 32 := by
    rw [← hM₁, Mem.size_write_word_at, Mem.size_write_word]; decide
  apply Func.execSat_segment
  · intro ex hex
    func_run (2)
    exact hex
  refine Func.execSat_mstore_step (M := M₁) (c := 6) rfl rfl ?_ ?_ ?_
  · exact Devm.extCost_add_of_size s₁ (by decide)
  · simp only [Devm.gasLeft_setMach]; omega
  intro M₂ G₂ hM₂ hg₂
  simp only [Devm.gasLeft_setMach] at hg₂
  have s₂ : M₂.size = 64 := by
    rw [← hM₂, Mem.size_write_word_at, s₁]; decide
  apply Func.execSat_segment
  · intro ex hex
    func_run (2)
    exact hex
  refine Func.execSat_mstore_step (M := M₂) (c := 6) rfl rfl ?_ ?_ ?_
  · exact Devm.extCost_add_of_size s₂ (by decide)
  · simp only [Devm.gasLeft_setMach]; omega
  intro M₃ G₃ hM₃ hg₃
  simp only [Devm.gasLeft_setMach] at hg₃
  have s₃ : M₃.size = 96 := by
    rw [← hM₃, Mem.size_write_word_at, s₂]; decide
  apply Func.execSat_segment
  · intro ex hex
    func_run (1)
    exact hex
  refine Func.execSat_mstore_step (M := M₃) (c := 6) rfl rfl ?_ ?_ ?_
  · exact Devm.extCost_add_of_size s₃ (by decide)
  · simp only [Devm.gasLeft_setMach]; omega
  intro M₄ G₄ hM₄ hg₄
  simp only [Devm.gasLeft_setMach] at hg₄
  have s₄ : M₄.size = 128 := by
    rw [← hM₄, Mem.size_write_word_at, s₃]; decide
  apply Func.execSat_segment
  · intro ex hex
    func_run (2)
    exact hex
  refine Func.execSat_mstore_step (M := M₄) (c := 6) rfl rfl ?_ ?_ ?_
  · exact Devm.extCost_add_of_size s₄ (by decide)
  · simp only [Devm.gasLeft_setMach]; omega
  intro M₅ G₅ hM₅ hg₅
  simp only [Devm.gasLeft_setMach] at hg₅
  have s₅ : M₅.size = 160 := by
    rw [← hM₅, Mem.size_write_word_at, s₄]; decide
  apply Func.execSat_segment
  · intro ex hex
    func_run (2)
    exact hex
  refine Func.execSat_mstore_step (M := M₅) (c := 6) rfl rfl ?_ ?_ ?_
  · exact Devm.extCost_add_of_size s₅ (by decide)
  · simp only [Devm.gasLeft_setMach]; omega
  intro M₆ G₆ hM₆ hg₆
  simp only [Devm.gasLeft_setMach] at hg₆
  have s₆ : M₆.size = 192 := by
    rw [← hM₆, Mem.size_write_word_at, s₅]; decide
  apply Func.execSat_segment
  · intro ex hex
    func_run (10) [(132 : B256)]
    exact hex
  rw [h_len]
  refine Func.execSat_mstore_step (M := M₆) (c := 6) rfl rfl ?_ ?_ ?_
  · exact Devm.extCost_add_of_size s₆ (by decide)
  · simp only [Devm.gasLeft_setMach]; omega
  intro M₇ G₇ hM₇ hg₇
  simp only [Devm.gasLeft_setMach] at hg₇
  have s₇ : M₇.size = 224 := by
    rw [← hM₇, Mem.size_write_word_at, s₆]; decide
  apply Func.execSat_segment
  · intro ex hex
    func_run (5) [(164 : B256)]
    exact hex
  have h_dl : (Nat.toB256 data.length).toNat = data.length := by
    rw [B256.toNat_toB256]; exact Nat.mod_eq_of_lt h_len_lt
  have h164 : (Nat.toB256 132 + 32 : B256).toNat = (164 : B256).toNat := by decide
  have h_bytes : sevm.data.sliceD (164 : B256).toNat
      (Nat.toB256 data.length).toNat 0 = data := by
    have h_tb : Sevm.tailBytes sevm 3 = data :=
      tailBytes_three_of_decodes h_len_lt h_dec
    refine Eq.trans ?_ h_tb
    simp only [Sevm.tailBytes, tailPtr_three_of_decodes h_dec,
      tailLen_three_of_decodes h_dec, h164]
  refine Func.execSat_calldatacopy_step (M := M₇)
    (c := flashLoanCopyGas data.length) rfl rfl ?_ ?_ ?_
  · refine Devm.extCost_add_of_size s₇ ?_
    simp only [h_dl, flashLoanCopyGas,
      show ((6 + 1 : B256) * 32).toNat = 224 from rfl]
  · simp only [Devm.gasLeft_setMach, flashLoanCallbackGas, gVerylow, gBase,
      gMemory] at h_gas' ⊢
    omega
  intro M₈ G₈ hM₈ hg₈
  simp only [Devm.gasLeft_setMach, h_bytes] at hM₈ hg₈
  have hG₈ : 31 ≤ G₈ := by
    simp only [flashLoanCallbackGas, gVerylow, gBase, gMemory] at h_gas'
    omega
  apply Func.execSat_segment
  · intro ex hex
    func_run (11)
    exact hex
  -- the state at the `CALL`, read off the eight named images
  have i0 : ((0 : B256) * 32).toNat = 0 := rfl
  have i1 : ((1 : B256) * 32).toNat = 32 := rfl
  have i2 : ((2 : B256) * 32).toNat = 64 := rfl
  have i3 : ((3 : B256) * 32).toNat = 96 := rfl
  have i4 : ((4 : B256) * 32).toNat = 128 := rfl
  have i5 : ((5 : B256) * 32).toNat = 160 := rfl
  have i6 : ((6 : B256) * 32).toNat = 192 := rfl
  have i7 : ((6 + 1 : B256) * 32).toNat = 224 := rfl
  simp only [i0, i1, i2, i3, i4, i5, i6, i7] at hM₁ hM₂ hM₃ hM₄ hM₅ hM₆ hM₇ hM₈
  have h_img : M₈ = flashLoanCallMem sevm amount data := by
    rw [← hM₈, ← hM₇, ← hM₆, ← hM₅, ← hM₄, ← hM₃, ← hM₂, ← hM₁]
    rfl
  rw [h_img]
  refine h_cont b (G₈ - 31) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [hstorb]; exact h_rcv
  · rw [hstorb]; exact h_sup
  · intro a k hk₁ hk₂; rw [hstorb]; exact h_oth a k hk₁ hk₂
  · rw [haccb]; exact hw_r
  · rw [haccb]; exact hw_s
  · intro p hp; rw [haccb]; exact hw_mono p hp
  · rw [hlogb]
    simp only [Devm.setMach_logs, h_log, flashLoanMintLog]
  · rw [herrb]
    simp only [Devm.setMach_error]
    exact h_err
  · simp only [flashLoanPreCallGas, flashLoanMintGas_eq, flashLoanLogGas,
      flashLoanCallbackGas, gVerylow, gBase, gMemory, gLog, gLogdata,
      gLogtopic] at *
    omega
  · omega

/-! ## Across the `CALL`

Everything below this line is on the far side of the callback.  The names and
facts here follow the plan's checkpoint 3a: the sub-term of `flashLoan` after
the `CALL` node, the callback memory's size, and the crossing itself. -/

/-- `flashLoanFromCall`'s tail after the `CALL` node: the flag test, the two
returndata checks, and the repayment.  `flashLoanFromCall` is definitionally
`Ninst.call ::: flashLoanFromFlag`, which the `example` below pins. -/
def flashLoanFromFlag : Func :=
  Ninst.iszero :::
  .revert <?>
  returnDataShorterThan 32 +++
  .revert <?>
  checkReturnDataHead erc3156Magic 0 +++
  Ninst.iszero :::
  .revert <?>
  spendAllowanceThenBurn

example : flashLoanFromCall = Ninst.call ::: flashLoanFromFlag := rfl

/-- The callback memory's size: seven words of head material and the padded
payload.  At an empty payload the final write is the identity and the figure is
the head's 224. -/
lemma flashLoanCallMem_size {sevm : Sevm} {amount : B256} {payload : Bytes} :
    (flashLoanCallMem sevm amount payload).size = 224 + ceil32 payload.length := by
  have h7 : ((((((((Mem.empty.write 0 amount.toBytes).write 0
      onFlashLoanSelector.toBytes).write 32 sevm.caller.toB256.toBytes).write
      64 sevm.currentTarget.toB256.toBytes).write 96 amount.toBytes).write
      128 (0 : B256).toBytes).write 160 (160 : B256).toBytes).write
      192 (Nat.toB256 payload.length).toBytes).size = 224 := by
    rw [Mem.size_write_word_at, Mem.size_write_word_at, Mem.size_write_word_at,
      Mem.size_write_word_at, Mem.size_write_word_at, Mem.size_write_word_at,
      Mem.size_write_word_at, Mem.size_write_word]
    decide
  show (Mem.write _ 224 payload).size = _
  rcases payload with _ | ⟨x, xs⟩
  · rw [show ∀ μ : Mem, Mem.write μ 224 [] = μ from fun _ => rfl, h7]
    decide
  · rw [Mem.size_write_cons, h7,
      if_neg (by simp only [List.length_cons]; omega),
      ceil32_eq_mul, ceil32_eq_mul]
    omega

/-- The `CALL`'s two access windows — the argument window and the empty return
window — are covered by the callback memory the trunk built. -/
lemma flashLoanCallMem_covered {sevm : Sevm} {amount : B256} {data : Bytes}
    (h_size : 196 + ceil32 data.length < 2 ^ 256) :
    memExtsSize (flashLoanCallMem sevm amount data).size
      [⟨callbackArgsOffset.toNat, (flashLoanArgsSize data.length).toNat⟩,
        ⟨(0 : B256).toNat, (0 : B256).toNat⟩]
      = (flashLoanCallMem sevm amount data).size := by
  have h_asz : (flashLoanArgsSize data.length).toNat = 196 + ceil32 data.length :=
    toNat_callbackArgsSize h_size
  simp only [memExtsSize]
  rw [flashLoanCallMem_size, h_asz, ceil32_eq_mul,
    show callbackArgsOffset.toNat = 28 from rfl,
    show ((0 : B256)).toNat = 0 from rfl]
  set q := (31 + data.length) / 32 with hq
  have h1 : memExtSize (224 + 32 * q) 28 (196 + 32 * q) = 224 + 32 * q := by
    unfold memExtSize
    rw [if_neg (by omega)]
    simp only [ceilDiv]
    rw [show (224 + 32 * q) % 32 = 0 from by omega,
      show (28 + (196 + 32 * q)) % 32 = 0 from by omega,
      show (224 + 32 * q) / 32 = 7 + q from by omega,
      show (28 + (196 + 32 * q)) / 32 = 7 + q from by omega]
    simp only [if_true, Nat.add_zero, Nat.max_self]
    omega
  rw [h1]
  show memExtSize (224 + 32 * q) 0 0 = 224 + 32 * q
  rfl

/-- **The crossing.**  From the trunk's premises the walk reaches the `CALL`;
the callee — arbitrary code resolved from the *world*, its derivation supplied
by totality (`Xlot.filled_exec`, through the landed crossing lemmas) — either
settles, and the frame continues at the flag the resume pushed, or dies on the
non-consensus channel, and the frame dies with it, which is `hP_fatal`'s arm.

The case analysis is exactly A2's: over `f.settle (exec cevm)` for the entered
frame, plus the two arms no settle reaches — the frame that never enters (a
precompile callee, or the transfer assertion) and the depth-limit arm that
never spawns.  **No premise about the callee appears anywhere.**

`K` is whatever gas floor the caller wants threaded through EIP-150 to the
continuations: the frame retains at least a sixty-fourth of what it had after
the call's own access charges, and `2 * gasColdAccountAccess` bounds those
(the account access plus EIP-7702's delegation resolution, at `value = 0`). -/
theorem flashLoan_execSat_flag {sevm : Sevm} {pre : Devm}
    {receiver token amount : B256} {data : Bytes} {K : Nat}
    {P : Execution → Prop}
    (h_sel : Sevm.selector sevm = flashLoanSelector)
    (h_dec : Sevm.DecodesCallWithTail sevm flashLoanSelector
      [receiver, token, amount] data)
    (h_size : 196 + ceil32 data.length < 2 ^ 256)
    (h_token : token = sevm.currentTarget.toB256)
    (h_addr : ValidAdr receiver)
    (h_nof : B256.Nof (Devm.getStorVal pre sevm.currentTarget supplySlot) amount)
    (h_static : sevm.isStatic = false)
    (h_stack : pre.stack = [])
    (h_mem : pre.memory = Mem.empty)
    (h_gas : flashLoanPreCallGas data.length + 2 * gasColdAccountAccess + 64 * K
      ≤ pre.gasLeft)
    (hP_fatal : ∀ (e : EvmError) (d : Devm), NonConsensus e → P (.error (e, d)))
    (h_flag0 : ∀ (d : Devm) (Gc : Nat), K ≤ Gc →
      Func.ExecSat (fmint.main :: fmint.aux) sevm
        (d.setMach ⟨0 :: [amount, receiver],
          flashLoanCallMem sevm amount data, Gc⟩) flashLoanFromFlag P)
    (h_flag1 : ∀ (d : Devm) (Gc : Nat), K ≤ Gc → d.error = pre.error →
      Func.ExecSat (fmint.main :: fmint.aux) sevm
        (d.setMach ⟨1 :: [amount, receiver],
          flashLoanCallMem sevm amount data, Gc⟩) flashLoanFromFlag P) :
    Prog.ExecSat sevm pre fmint P := by
  refine flashLoan_execSat_call h_sel h_dec h_size h_token h_addr h_nof h_static
    h_stack h_mem (by omega) ?_
  intro b G h_rcv h_sup h_oth hw_r hw_s hw_mono h_log h_err h_lo h_hi
  have hKG : 2 * gasColdAccountAccess + 64 * K ≤ G := by omega
  rw [show flashLoanFromCall = Ninst.call ::: flashLoanFromFlag from rfl]
  have h_cov := flashLoanCallMem_covered (sevm := sevm) (amount := amount)
    (data := data) h_size
  set st := b.setMach ⟨[Nat.toB256 G, receiver, 0, callbackArgsOffset,
    flashLoanArgsSize data.length, 0, 0, amount, receiver],
    flashLoanCallMem sevm amount data, G⟩ with hst
  rcases hdel : accessDelegation (addAccessedAddress
      (st.setMach ⟨[amount, receiver], st.memory, st.gasLeft⟩) receiver.toAdr)
      receiver.toAdr with ⟨dp, dadr, dcode, dgc, d1⟩
  obtain ⟨hd1s, hd1m, hd1g, hdgc⟩ := accessDelegation_inv hdel
  have hd1e : d1.error = pre.error := by
    rw [accessDelegation_error hdel]
    show st.error = pre.error
    simp only [hst, Devm.setMach_error]
    exact h_err
  have hd1s' : d1.stack = [amount, receiver] := hd1s
  have hd1m' : d1.memory = flashLoanCallMem sevm amount data := hd1m
  have hd1g' : d1.gasLeft = G := hd1g
  have h_ext : (st.setMach ⟨[amount, receiver], st.memory, st.gasLeft⟩).extCost
      [⟨callbackArgsOffset.toNat, (flashLoanArgsSize data.length).toNat⟩,
        ⟨(0 : B256).toNat, (0 : B256).toNat⟩] = 0 :=
    Devm.extCost_covered h_cov
  set acc := accessCost receiver.toAdr
    (st.setMach ⟨[amount, receiver], st.memory, st.gasLeft⟩).accessedAddresses
    + dgc with hacc
  have h_acc_le : acc ≤ 2 * gasColdAccountAccess := by
    have h1 := accessCost_le (x := receiver.toAdr)
      (a := (st.setMach
        ⟨[amount, receiver], st.memory, st.gasLeft⟩).accessedAddresses)
    omega
  have h_afford : acc + 0 ≤ d1.gasLeft := by rw [hd1g']; omega
  have h_split := calculateMsgCallGas_zero (gas := (Nat.toB256 G).toNat) h_afford
  set mcs := min (Nat.toB256 G).toNat (except64th (d1.gasLeft - 0 - acc))
    with hmcs
  have h_mcs_le : mcs ≤ d1.gasLeft - 0 - acc := by
    rw [hmcs, show except64th (d1.gasLeft - 0 - acc)
      = (d1.gasLeft - 0 - acc) - (d1.gasLeft - 0 - acc) / 64 from rfl]
    exact le_trans (Nat.min_le_right _ _) (by omega)
  have h_gcross : (mcs + acc) + 0 ≤ d1.gasLeft := by omega
  have h_return := le_retained_of_calculateMsgCallGas_zero h_afford h_split
  have h_K_return : K ≤ d1.gasLeft - (mcs + acc + 0) := by
    rw [hd1g'] at h_return ⊢
    have h64 : 64 * K ≤ G - 0 - acc := by omega
    have h2 : K ≤ (G - 0 - acc) / 64 := by omega
    omega
  by_cases hd : sevm.depth = 0
  · -- the depth-limit arm: no child is spawned, the flag is `0`
    refine Func.execSat_next
      (Ninst.runCompiled_call_zero_value_zero_depth rfl h_ext hdel hacc.symm
        h_split h_gcross hd (by simp [hd1s'])) ?_
    rw [hd1s', hd1m', Mem.extends_covered h_cov]
    exact h_flag0 _ _ (by omega)
  · -- the spawn
    have h_step := Xinst.step_call_zero_value_spawn (sevm := sevm) rfl h_ext hdel
      hacc.symm h_split h_gcross hd
    set P' := callSpawnParent d1 (mcs + acc + 0) callbackArgsOffset.toNat
      (flashLoanArgsSize data.length).toNat (0 : B256).toNat (0 : B256).toNat
      with hP'
    set msg' := callSpawnMsg sevm P' mcs receiver.toAdr dadr
      callbackArgsOffset.toNat (flashLoanArgsSize data.length).toNat dcode dp
      with hmsg'
    have hP's : P'.stack = [amount, receiver] := by
      rw [hP', callSpawnParent_stack, hd1s']
    have hP'm : P'.memory = flashLoanCallMem sevm amount data := by
      rw [hP', callSpawnParent_memory, hd1m', Mem.extends_covered h_cov]
    have hP'g : P'.gasLeft = d1.gasLeft - (mcs + acc + 0) := by
      rw [hP', callSpawnParent_gasLeft]
    have hP'K : K ≤ P'.gasLeft := by rw [hP'g]; exact h_K_return
    have hroom : P'.stack.length < 1024 := by simp [hP's]
    rcases henter : (Frame.ofCall msg').enter with r | cevm
    · -- the frame resolves without entering: a precompile, or the transfer
      rcases r with ⟨e, st', ca, tra⟩ | child
      · -- ...fatally: the error is non-consensus by construction
        exact Func.execSat_next_error
          (Ninst.stepRun_exec_doneFrame_error h_step henter Resume.run_call_fatal)
          (hP_fatal e _ (Frame.enter_done_error_inv rfl henter))
      · by_cases hce : child.error.isSome = true
        · have hres : Resume.run (.call P' ((0 : B256)).toNat ((0 : B256)).toNat)
              (.ok child)
              = .ok ((incorporateChildOnError P' child child.output).setMach
                  ⟨0 :: [amount, receiver], flashLoanCallMem sevm amount data,
                    P'.gasLeft + child.gasLeft⟩) := by
            rw [Resume.run_call_err hce hroom]
            simp only [show ((0 : B256)).toNat = 0 from rfl, List.take_zero]
            rw [Devm.memWrite_nil, hP's, hP'm]
          exact Func.execSat_next
            (Ninst.runCompiled_exec_doneFrame h_step henter hres)
            (h_flag0 (incorporateChildOnError P' child child.output)
              (P'.gasLeft + child.gasLeft) (by omega))
        · have hce' : child.error.isSome = false := by
            revert hce; cases child.error.isSome <;> simp
          have hres : Resume.run (.call P' ((0 : B256)).toNat ((0 : B256)).toNat)
              (.ok child)
              = .ok ((incorporateChildOnSuccess P' child child.output).setMach
                  ⟨1 :: [amount, receiver], flashLoanCallMem sevm amount data,
                    P'.gasLeft + child.gasLeft⟩) := by
            rw [Resume.run_call_ok hce' hroom]
            simp only [show ((0 : B256)).toNat = 0 from rfl, List.take_zero]
            rw [Devm.memWrite_nil, hP's, hP'm]
          exact Func.execSat_next
            (Ninst.runCompiled_exec_doneFrame h_step henter hres)
            (h_flag1 (incorporateChildOnSuccess P' child child.output)
              (P'.gasLeft + child.gasLeft) (by omega)
              (by show P'.error = pre.error
                  simp only [hP', callSpawnParent_error]
                  exact hd1e))
    · -- the entered frame: the child's derivation is `exec cevm`, by totality
      rcases hsettle : (Frame.ofCall msg').settle (exec cevm)
        with ⟨e, st', ca, tra⟩ | child
      · -- fatal settle: the non-consensus channel propagates
        exact Func.execSat_next_error
          (Ninst.stepRun_exec_run_error h_step henter
            (by rw [hsettle]; exact Resume.run_call_fatal))
          (hP_fatal e _ (handleError_error_inv (Frame.settle_error_inv rfl hsettle)))
      · by_cases hce : child.error.isSome = true
        · -- the borrower reverted or halted: the resume pushes `0`
          have hres : Resume.run (.call P' ((0 : B256)).toNat ((0 : B256)).toNat)
              ((Frame.ofCall msg').settle (exec cevm))
              = .ok ((incorporateChildOnError P' child child.output).setMach
                  ⟨0 :: [amount, receiver], flashLoanCallMem sevm amount data,
                    P'.gasLeft + child.gasLeft⟩) := by
            rw [hsettle, Resume.run_call_err hce hroom]
            simp only [show ((0 : B256)).toNat = 0 from rfl, List.take_zero]
            rw [Devm.memWrite_nil, hP's, hP'm]
          exact Func.execSat_next
            (Ninst.runCompiled_call_zero_value rfl h_ext hdel hacc.symm h_split
              h_gcross hd henter hres)
            (h_flag0 (incorporateChildOnError P' child child.output)
              (P'.gasLeft + child.gasLeft) (by omega))
        · -- the borrower settled clean: the resume pushes `1`
          have hce' : child.error.isSome = false := by
            revert hce; cases child.error.isSome <;> simp
          have hres : Resume.run (.call P' ((0 : B256)).toNat ((0 : B256)).toNat)
              ((Frame.ofCall msg').settle (exec cevm))
              = .ok ((incorporateChildOnSuccess P' child child.output).setMach
                  ⟨1 :: [amount, receiver], flashLoanCallMem sevm amount data,
                    P'.gasLeft + child.gasLeft⟩) := by
            rw [hsettle, Resume.run_call_ok hce' hroom]
            simp only [show ((0 : B256)).toNat = 0 from rfl, List.take_zero]
            rw [Devm.memWrite_nil, hP's, hP'm]
          exact Func.execSat_next
            (Ninst.runCompiled_call_zero_value rfl h_ext hdel hacc.symm h_split
              h_gcross hd henter hres)
            (h_flag1 (incorporateChildOnSuccess P' child child.output)
              (P'.gasLeft + child.gasLeft) (by omega)
              (by show P'.error = pre.error
                  simp only [hP', callSpawnParent_error]
                  exact hd1e))

/-- **The callback-failed leaf.**  Whatever pushed the `0` — a reverting or
halting borrower, a failed precompile, or the depth limit — `flashLoan` tests
the flag and deliberately reverts.  The walk runs from a symbolic gas lower
bound, which is the plan's A7 capability check: `func_run` needed no change. -/
lemma execSat_flagZero_leaf {sevm : Sevm} {d : Devm} {amount receiver : B256}
    {M : Mem} {Gc : Nat} {P : Execution → Prop}
    (h_gas : 21 ≤ Gc)
    (hP : ∀ post : Devm, P (.error (.revert, post))) :
    Func.ExecSat (fmint.main :: fmint.aux) sevm
      (d.setMach ⟨0 :: [amount, receiver], M, Gc⟩) flashLoanFromFlag P := by
  apply Func.execSat_of_runCompiledTo
  · func_run (2) [1]
    exact Func.runCompiledTo_revert_func (G := Gc - 21)
      (by simp only [Devm.gasLeft_setMach, gBase]; omega)
      (by simp only [Devm.stack_setMach, List.length_cons, List.length_nil]; omega)
  · exact hP _

/-- **The returndata-short leaf.**  The callback settled clean but answered
fewer than 32 bytes: `returnDataShorterThan 32` fires before any word is read —
`returndatacopy` would abort the frame rather than fail a test — and `flashLoan`
deliberately reverts. -/
lemma execSat_returnDataShort_leaf {sevm : Sevm} {d : Devm}
    {amount receiver : B256} {M : Mem} {Gc : Nat} {P : Execution → Prop}
    (h_rd : d.returnData.length < 32)
    (h_gas : 42 ≤ Gc)
    (hP : ∀ post : Devm, P (.error (.revert, post))) :
    Func.ExecSat (fmint.main :: fmint.aux) sevm
      (d.setMach ⟨1 :: [amount, receiver], M, Gc⟩) flashLoanFromFlag P := by
  have h_lt : (Nat.toB256 d.returnData.length <? (32 : B256)) = 1 := by
    show (if Nat.toB256 d.returnData.length < 32 then (1 : B256) else 0) = 1
    refine if_pos ?_
    rw [B256.lt_iff_toNat_lt_toNat, B256.toNat_toB256,
      show ((32 : B256)).toNat = 32 from rfl,
      Nat.lo_eq_of_lt (show d.returnData.length < 2 ^ 256 from
        Nat.lt_of_lt_of_le h_rd (by norm_num))]
    exact h_rd
  apply Func.execSat_of_runCompiledTo
  · func_run (6) [0, 1]
    exact Func.runCompiledTo_revert_func (G := Gc - 42)
      (by simp only [Devm.gasLeft_setMach, gBase]; omega)
      (by simp only [Devm.stack_setMach, List.length_cons, List.length_nil]; omega)
  · exact hP _

/-- The word `checkReturnDataHead erc3156Magic 0` reads back: the head word of the
returndata, through the image `returndatacopy` wrote into memory word `0`.  Named
so the magic-mismatch premise and the assembly's case split are stated over the
same term. -/
def flashLoanReturnDataHead (d : Devm) (M : Mem) : B256 :=
  ((M.write ((0 * 32 : B256)).toNat
    (List.sliceD d.returnData (B256.toNat 0) (B256.toNat 32) (0 : UInt8))).read
      ((0 * 32 : B256)).toNat 32).1.toB256

set_option maxRecDepth 608 in
/-- **The magic-mismatch leaf.**  The callback settled clean with a full word
of returndata, but the head word is not `erc3156Magic`: `flashLoan` reads the
word back through `returndatacopy`/`mload` and deliberately reverts. -/
lemma execSat_magicMismatch_leaf {sevm : Sevm} {d : Devm}
    {amount receiver : B256} {M : Mem} {Gc : Nat} {P : Execution → Prop}
    (h_ge : (Nat.toB256 d.returnData.length <? (32 : B256)) = 0)
    (h_neq : (erc3156Magic =? flashLoanReturnDataHead d M) = 0)
    (h32 : M.size % 32 = 0)
    (h_msz : 64 ≤ M.size)
    (h_gas : 82 ≤ Gc)
    (hP : ∀ post : Devm, P (.error (.revert, post))) :
    Func.ExecSat (fmint.main :: fmint.aux) sevm
      (d.setMach ⟨1 :: [amount, receiver], M, Gc⟩) flashLoanFromFlag P := by
  have h_len : B256.toNat 0 + B256.toNat 32 ≤ d.returnData.length := by
    have h1 : ¬ Nat.toB256 d.returnData.length < (32 : B256) := by
      intro hc
      rw [show (Nat.toB256 d.returnData.length <? (32 : B256))
        = if Nat.toB256 d.returnData.length < 32 then (1 : B256) else 0 from rfl,
        if_pos hc] at h_ge
      exact (by decide : (1 : B256) ≠ 0) h_ge
    rw [B256.lt_iff_toNat_lt_toNat, B256.toNat_toB256,
      show ((32 : B256)).toNat = 32 from rfl, Nat.lo_eq] at h1
    have h2 := Nat.mod_le d.returnData.length (2 ^ 256)
    rw [show B256.toNat 0 + B256.toNat 32 = 32 from by decide]
    omega
  have h_neq' : (erc3156Magic =?
      ((M.write ((0 * 32 : B256)).toNat
        (List.sliceD d.returnData (B256.toNat 0) (B256.toNat 32)
          (0 : UInt8))).read ((0 * 32 : B256)).toNat 32).1.toB256) = 0 := h_neq
  apply Func.execSat_of_runCompiledTo
  · func_run (16) [0, 0, 6, 3, 0, 1]
    · rw [Devm.extCost_zero_of_le h32 (by
        rw [show ((0 * 32 : B256)).toNat + B256.toNat 32 = 32 from by decide]
        omega)]
      decide
    · have hs1 : (M.write ((0 * 32 : B256)).toNat
          (List.sliceD d.returnData (B256.toNat 0) (B256.toNat 32)
            (0 : UInt8))).size = M.size := by
        apply Mem.size_write_of_le
        rw [show (List.sliceD d.returnData (B256.toNat 0) (B256.toNat 32)
            (0 : UInt8)).length = B256.toNat 32 from List.takeD_length _ _ _,
          show ((0 * 32 : B256)).toNat + B256.toNat 32 = 32 from by decide]
        omega
      simp only [Devm.returnData_setMach]
      rw [Devm.extCost_zero_of_le (by rw [hs1]; exact h32) (by
        rw [hs1, show ((0 * 32 : B256)).toNat + 32 = 32 from by decide]
        omega)]
      decide
    · exact Func.runCompiledTo_revert_func (G := Gc - 82)
        (by simp only [Devm.gasLeft_setMach, gBase]; omega)
        (by simp only [Devm.stack_setMach, List.length_cons, List.length_nil]
            omega)
  · exact hP _

/-- The lower bound `returnDataShorterThan 32` establishes in the negative
direction, in the shape the `returndatacopy` arm's guard wants. -/
lemma returnData_bound_of_not_short {d : Devm}
    (h_ge : (Nat.toB256 d.returnData.length <? (32 : B256)) = 0) :
    B256.toNat 0 + B256.toNat 32 ≤ d.returnData.length := by
  have h1 : ¬ Nat.toB256 d.returnData.length < (32 : B256) := by
    intro hc
    rw [show (Nat.toB256 d.returnData.length <? (32 : B256))
      = if Nat.toB256 d.returnData.length < 32 then (1 : B256) else 0 from rfl,
      if_pos hc] at h_ge
    exact (by decide : (1 : B256) ≠ 0) h_ge
  rw [B256.lt_iff_toNat_lt_toNat, B256.toNat_toB256,
    show ((32 : B256)).toNat = 32 from rfl, Nat.lo_eq] at h1
  have h2 := Nat.mod_le d.returnData.length (2 ^ 256)
  rw [show B256.toNat 0 + B256.toNat 32 = 32 from by decide]
  omega

/-- The `returndatacopy` of `checkReturnDataHead` keeps the size of the image it
writes into. -/
lemma flashLoanReturnDataImage_size {d : Devm} {M : Mem} (h_msz : 64 ≤ M.size) :
    (M.write ((0 * 32 : B256)).toNat
      (List.sliceD d.returnData (B256.toNat 0) (B256.toNat 32)
        (0 : UInt8))).size = M.size := by
  apply Mem.size_write_of_le
  rw [show (List.sliceD d.returnData (B256.toNat 0) (B256.toNat 32)
      (0 : UInt8)).length = B256.toNat 32 from List.takeD_length _ _ _,
    show ((0 * 32 : B256)).toNat + B256.toNat 32 = 32 from by decide]
  omega

set_option maxRecDepth 605 in
/-- **Into the repayment.**  The flag is `1` and both returndata checks pass:
the walk crosses `returnDataShorterThan 32` and `checkReturnDataHead erc3156Magic 0`
and hands the continuation the state entering `spendAllowanceThenBurn` — the
memory image a variable with only its size pinned (F8), the gas account
exact. -/
lemma execSat_spend_step {sevm : Sevm} {d : Devm}
    {amount receiver : B256} {M : Mem} {Gc : Nat} {P : Execution → Prop}
    (h_ge : (Nat.toB256 d.returnData.length <? (32 : B256)) = 0)
    (h_eq : (erc3156Magic =? flashLoanReturnDataHead d M) = 1)
    (h32 : M.size % 32 = 0)
    (h_msz : 64 ≤ M.size)
    (h_gas : 77 ≤ Gc)
    (h_next : ∀ M' : Mem, M'.size = M.size →
      Func.ExecSat (fmint.main :: fmint.aux) sevm
        (d.setMach ⟨[amount, receiver], M', Gc - 77⟩)
          spendAllowanceThenBurn P) :
    Func.ExecSat (fmint.main :: fmint.aux) sevm
      (d.setMach ⟨1 :: [amount, receiver], M, Gc⟩) flashLoanFromFlag P := by
  have h_len := returnData_bound_of_not_short h_ge
  have h_eq' : (erc3156Magic =?
      ((M.write ((0 * 32 : B256)).toNat
        (List.sliceD d.returnData (B256.toNat 0) (B256.toNat 32)
          (0 : UInt8))).read ((0 * 32 : B256)).toNat 32).1.toB256) = 1 := h_eq
  have hs1 := flashLoanReturnDataImage_size (d := d) (M := M) h_msz
  have hs' : (((M.write ((0 * 32 : B256)).toNat
      (List.sliceD d.returnData (B256.toNat 0) (B256.toNat 32)
        (0 : UInt8))).read ((0 * 32 : B256)).toNat 32).2).size = M.size := by
    rw [Mem.size_read_snd_of_le (by rw [hs1]; exact h32)
      (by rw [hs1, show ((0 * 32 : B256)).toNat + 32 = 32 from by decide]
          omega),
      hs1]
  refine Func.execSat_segment ?_ (h_next _ hs')
  intro ex hex
  func_run (16) [0, 0, 6, 3, 1, 0]
  · rw [Devm.extCost_zero_of_le h32 (by
      rw [show ((0 * 32 : B256)).toNat + B256.toNat 32 = 32 from by decide]
      omega)]
    decide
  · simp only [Devm.returnData_setMach]
    rw [Devm.extCost_zero_of_le (by rw [hs1]; exact h32) (by
      rw [hs1, show ((0 * 32 : B256)).toNat + 32 = 32 from by decide]
      omega)]
    decide
  · exact hex

open Jaune.Ninst Ninst in
/-- `spendAllowanceThenBurn`'s tail after the collision guard: the allowance
read and the two arms of the infinite-allowance test, both converging on
`burnAndReturn` in aux slot `burnSlot`.  The `example` below pins it as the
sub-term it is. -/
def spendFromHash : Func :=
  dup 0 ::: sload :::
  dup 0 ::: isMax +++
  ( pop ::: pop :::
    .call burnSlot ) <?>
  ( dup 2 ::: dup 1 ::: lt :::
    .revert <?>
    dup 2 ::: swap 0 ::: sub :::
    swap 0 ::: sstore :::
    .call burnSlot )

open Jaune.Ninst Ninst in
example : spendAllowanceThenBurn =
    dup 1 ::: mstoreAt 0 +++
    address ::: mstoreAt 1 +++
    pushList [64, 0] +++
    keccak256 :::
    checkSlotCollides +++
    .revert <?>
    spendFromHash := rfl

/-- **Through the collision guard.**  The allowance key is hashed and collides
with neither storage region: the walk hands the continuation the state
entering `spendFromHash`, with the hash a variable named by `h_hash`. -/
lemma execSat_spendGuard_step {sevm : Sevm} {d : Devm}
    {wad receiver h : B256} {M : Mem} {Gc : Nat} {P : Execution → Prop}
    (h_hash : Bytes.keccak ((((M.write ((0 * 32 : B256)).toNat
      receiver.toBytes).write ((1 * 32 : B256)).toNat
        sevm.currentTarget.toB256.toBytes).read (B256.toNat 0)
          (B256.toNat 64)).1) = h)
    (h_nva : B256.eqCheck
      (((~~~ (0 : B256)) <<< (Nat.toB256 160).toNat) &&& h) 0 = 0)
    (h_nmax : B256.eqCheck (~~~ h) 0 = 0)
    (h32 : M.size % 32 = 0)
    (h_msz : 64 ≤ M.size)
    (h_gas : 108 ≤ Gc)
    (h_next : ∀ M'' : Mem, M''.size = M.size →
      Func.ExecSat (fmint.main :: fmint.aux) sevm
        (d.setMach ⟨[h, wad, receiver], M'', Gc - 108⟩) spendFromHash P) :
    Func.ExecSat (fmint.main :: fmint.aux) sevm
      (d.setMach ⟨[wad, receiver], M, Gc⟩) spendAllowanceThenBurn P := by
  have hw1 : (M.write ((0 * 32 : B256)).toNat receiver.toBytes).size
      = M.size := by
    apply Mem.size_write_of_le
    rw [B256.length_toBytes,
      show ((0 * 32 : B256)).toNat + 32 = 32 from by decide]
    omega
  have hw2 : ((M.write ((0 * 32 : B256)).toNat receiver.toBytes).write
      ((1 * 32 : B256)).toNat sevm.currentTarget.toB256.toBytes).size
      = M.size := by
    rw [Mem.size_write_of_le, hw1]
    rw [hw1, B256.length_toBytes,
      show ((1 * 32 : B256)).toNat + 32 = 64 from by decide]
    omega
  have hs'' : ((((M.write ((0 * 32 : B256)).toNat receiver.toBytes).write
      ((1 * 32 : B256)).toNat sevm.currentTarget.toB256.toBytes).read
        (B256.toNat 0) (B256.toNat 64)).2).size = M.size := by
    rw [Mem.size_read_snd_of_le (by rw [hw2]; exact h32)
      (by rw [hw2, show B256.toNat 0 + B256.toNat 64 = 64 from by decide]
          omega),
      hw2]
  refine Func.execSat_segment ?_ (h_next _ hs'')
  intro ex hex
  func_run (21) [0, 0, 42, h, ~~~ (0 : B256),
    (~~~ (0 : B256)) <<< (Nat.toB256 160).toNat,
    ((~~~ (0 : B256)) <<< (Nat.toB256 160).toNat) &&& h, 0, ~~~ h, 0, 0]
  · exact Devm.extCost_zero_of_le h32 (by
      rw [show ((0 * 32 : B256)).toNat + 32 = 32 from by decide]
      omega)
  · exact Devm.extCost_zero_of_le (by rw [hw1]; exact h32) (by
      rw [hw1, show ((1 * 32 : B256)).toNat + 32 = 64 from by decide]
      omega)
  · rw [Devm.extCost_zero_of_le (by rw [hw2]; exact h32) (by
      rw [hw2, show B256.toNat 0 + B256.toNat 64 = 64 from by decide]
      omega)]
    decide
  · exact hex

/-- **The slot-collision leaf.**  The allowance key hashes into one of the two
guarded storage regions — it is address-shaped (`va = 1`) or it is
`supplySlot` (`mx = 1`) — and `flashLoan` deliberately reverts rather than
write through the alias.  The two clause values are threaded as variables so
one statement serves all three colliding combinations. -/
lemma execSat_slotCollision_leaf {sevm : Sevm} {d : Devm}
    {wad receiver h va mx : B256} {M : Mem} {Gc : Nat} {P : Execution → Prop}
    (h_hash : Bytes.keccak ((((M.write ((0 * 32 : B256)).toNat
      receiver.toBytes).write ((1 * 32 : B256)).toNat
        sevm.currentTarget.toB256.toBytes).read (B256.toNat 0)
          (B256.toNat 64)).1) = h)
    (h_va : B256.eqCheck
      (((~~~ (0 : B256)) <<< (Nat.toB256 160).toNat) &&& h) 0 = va)
    (h_mx : B256.eqCheck (~~~ h) 0 = mx)
    (h_col : (mx ||| va) = 1)
    (h32 : M.size % 32 = 0)
    (h_msz : 64 ≤ M.size)
    (h_gas : 113 ≤ Gc)
    (hP : ∀ post : Devm, P (.error (.revert, post))) :
    Func.ExecSat (fmint.main :: fmint.aux) sevm
      (d.setMach ⟨[wad, receiver], M, Gc⟩) spendAllowanceThenBurn P := by
  have hw1 : (M.write ((0 * 32 : B256)).toNat receiver.toBytes).size
      = M.size := by
    apply Mem.size_write_of_le
    rw [B256.length_toBytes,
      show ((0 * 32 : B256)).toNat + 32 = 32 from by decide]
    omega
  have hw2 : ((M.write ((0 * 32 : B256)).toNat receiver.toBytes).write
      ((1 * 32 : B256)).toNat sevm.currentTarget.toB256.toBytes).size
      = M.size := by
    rw [Mem.size_write_of_le, hw1]
    rw [hw1, B256.length_toBytes,
      show ((1 * 32 : B256)).toNat + 32 = 64 from by decide]
    omega
  apply Func.execSat_of_runCompiledTo
  · func_run (21) [0, 0, 42, h, ~~~ (0 : B256),
      (~~~ (0 : B256)) <<< (Nat.toB256 160).toNat,
      ((~~~ (0 : B256)) <<< (Nat.toB256 160).toNat) &&& h, va, ~~~ h, mx, 1]
    · exact Devm.extCost_zero_of_le h32 (by
        rw [show ((0 * 32 : B256)).toNat + 32 = 32 from by decide]
        omega)
    · exact Devm.extCost_zero_of_le (by rw [hw1]; exact h32) (by
        rw [hw1, show ((1 * 32 : B256)).toNat + 32 = 64 from by decide]
        omega)
    · rw [Devm.extCost_zero_of_le (by rw [hw2]; exact h32) (by
        rw [hw2, show B256.toNat 0 + B256.toNat 64 = 64 from by decide]
        omega)]
      decide
    · exact Func.runCompiledTo_revert_func (G := Gc - 113)
        (by simp only [Devm.gasLeft_setMach, gBase]; omega)
        (by simp only [Devm.stack_setMach, List.length_cons, List.length_nil]
            omega)
  · exact hP _

/-- **The allowance-low leaf.**  The allowance `receiver → address(this)` is
finite and below the amount owed: `flashLoan` deliberately reverts.  The
allowance value is read through the warmth-open `SLOAD` step, so the statement
needs no warm-set premise (F28). -/
lemma execSat_allowanceLow_leaf {sevm : Sevm} {d : Devm}
    {wad receiver h amnt : B256} {M : Mem} {Gc : Nat} {P : Execution → Prop}
    (h_amnt : d.getStorVal sevm.currentTarget h = amnt)
    (h_nmax : B256.eqCheck (~~~ amnt) 0 = 0)
    (h_low : (amnt <? wad) = 1)
    (h_gas : 2152 ≤ Gc)
    (hP : ∀ post : Devm, P (.error (.revert, post))) :
    Func.ExecSat (fmint.main :: fmint.aux) sevm
      (d.setMach ⟨[h, wad, receiver], M, Gc⟩) spendFromHash P := by
  refine Func.execSat_next
    (Ninst.runCompiled_dup (n := 0) (G := Gc - gVerylow) rfl
      (by simp only [Devm.gasLeft_setMach, gVerylow]; omega)
      (by simp only [Devm.stack_setMach, List.length_cons, List.length_nil]
          omega)) ?_
  apply Func.execSat_sload_step (k := h) (v := amnt)
    (s := [h, wad, receiver]) (M := M)
  · rfl
  · simp only [List.length_cons, List.length_nil]; omega
  · exact h_amnt
  · rfl
  · simp only [Devm.gasLeft_setMach, gasColdSload, gVerylow]; omega
  · intro base c G h_in h_mono h_stor _h_bal _h_code h_rc h_logs _h_output h_er
      _h_delete h_lo h_hi h_geq
    have hG : 49 ≤ G := by
      simp only [Devm.gasLeft_setMach, gVerylow] at h_geq
      simp only [gasColdSload] at h_hi
      omega
    apply Func.execSat_of_runCompiledTo
    · func_run (8) [~~~ amnt, 0, 1]
      exact Func.runCompiledTo_revert_func (G := G - 49)
        (by simp only [Devm.gasLeft_setMach, gBase]; omega)
        (by simp only [Devm.stack_setMach, List.length_cons, List.length_nil]
            omega)
    · exact hP _

/-- **Through the infinite-allowance arm.**  The allowance is `2^256 - 1`, so
it is preserved rather than decremented: nothing is written, and the walk
hands the continuation the state entering `burnAndReturn` with storage exactly
`d`'s. -/
lemma execSat_spendInf_step {sevm : Sevm} {d : Devm}
    {wad receiver h amnt : B256} {M : Mem} {Gc : Nat} {P : Execution → Prop}
    (h_amnt : d.getStorVal sevm.currentTarget h = amnt)
    (h_max : B256.eqCheck (~~~ amnt) 0 = 1)
    (h_gas : 2142 ≤ Gc)
    (h_next : ∀ (b : Devm) (G : Nat),
      (∀ (a : Adr) (k : B256), b.getStorVal a k = d.getStorVal a k) →
      b.error = d.error →
      Gc - 2142 ≤ G →
      Func.ExecSat (fmint.main :: fmint.aux) sevm
        (b.setMach ⟨[wad, receiver], M, G⟩) burnAndReturn P) :
    Func.ExecSat (fmint.main :: fmint.aux) sevm
      (d.setMach ⟨[h, wad, receiver], M, Gc⟩) spendFromHash P := by
  refine Func.execSat_next
    (Ninst.runCompiled_dup (n := 0) (G := Gc - gVerylow) rfl
      (by simp only [Devm.gasLeft_setMach, gVerylow]; omega)
      (by simp only [Devm.stack_setMach, List.length_cons, List.length_nil]
          omega)) ?_
  apply Func.execSat_sload_step (k := h) (v := amnt)
    (s := [h, wad, receiver]) (M := M)
  · rfl
  · simp only [List.length_cons, List.length_nil]; omega
  · exact h_amnt
  · rfl
  · simp only [Devm.gasLeft_setMach, gasColdSload, gVerylow]; omega
  · intro base c G h_in h_mono h_stor _h_bal _h_code h_rc h_logs _h_output h_er
      _h_delete h_lo h_hi h_geq
    simp only [Devm.gasLeft_setMach, gVerylow] at h_geq
    simp only [gasColdSload] at h_hi
    have hG : 39 ≤ G := by omega
    refine Func.execSat_segment ?_ (h_next base (G - 39) ?_ ?_ (by omega))
    · intro ex hex
      func_run (7) [~~~ amnt, 1]
      exact hex
    · intro a k
      exact h_stor a k
    · simpa only [Devm.setMach_error] using h_er

/-- **Through the finite-allowance arm.**  The allowance covers the amount
owed: it is decremented and written back — the one `SSTORE` of the arm, warm
because the walk read the same key three instructions earlier (F28) — and the
walk hands the continuation the state entering `burnAndReturn`, with exactly
one storage cell moved against `d`. -/
lemma execSat_spendFin_step {sevm : Sevm} {d : Devm}
    {wad receiver h amnt : B256} {M : Mem} {Gc : Nat} {P : Execution → Prop}
    (h_amnt : d.getStorVal sevm.currentTarget h = amnt)
    (h_nmax : B256.eqCheck (~~~ amnt) 0 = 0)
    (h_ge : (amnt <? wad) = 0)
    (h_static : sevm.isStatic = false)
    (h_gas : 22171 ≤ Gc)
    (h_next : ∀ (b : Devm) (G : Nat),
      b.getStorVal sevm.currentTarget h = amnt - wad →
      (∀ (a : Adr) (k : B256), (a, k) ≠ (sevm.currentTarget, h) →
        b.getStorVal a k = d.getStorVal a k) →
      b.error = d.error →
      Gc - 22171 ≤ G →
      Func.ExecSat (fmint.main :: fmint.aux) sevm
        (b.setMach ⟨[wad, receiver], M, G⟩) burnAndReturn P) :
    Func.ExecSat (fmint.main :: fmint.aux) sevm
      (d.setMach ⟨[h, wad, receiver], M, Gc⟩) spendFromHash P := by
  refine Func.execSat_next
    (Ninst.runCompiled_dup (n := 0) (G := Gc - gVerylow) rfl
      (by simp only [Devm.gasLeft_setMach, gVerylow]; omega)
      (by simp only [Devm.stack_setMach, List.length_cons, List.length_nil]
          omega)) ?_
  apply Func.execSat_sload_step (k := h) (v := amnt)
    (s := [h, wad, receiver]) (M := M)
  · rfl
  · simp only [List.length_cons, List.length_nil]; omega
  · exact h_amnt
  · rfl
  · simp only [Devm.gasLeft_setMach, gasColdSload, gVerylow]; omega
  · intro base c G h_in h_mono h_stor _h_bal _h_code h_rc h_logs _h_output h_er
      _h_delete h_lo h_hi h_geq
    simp only [Devm.gasLeft_setMach, gVerylow] at h_geq
    simp only [gasColdSload] at h_hi
    have hG : 20068 ≤ G := by omega
    apply Func.execSat_segment
    · intro ex hex
      func_run (12) [~~~ amnt, 0, 0, amnt - wad]
      exact hex
    · apply Func.execSat_sstore_warm_step (k := h) (v := amnt - wad)
        (s := [wad, receiver]) (M := M)
      · rfl
      · exact h_in
      · exact h_static
      · rfl
      · simp only [Devm.gasLeft_setMach, gasStorageSet]; omega
      · intro base2 c2 G2 hkey hoth _h_bal2 _h_code2 hacc hlogs2 _hout2
          her2 _h_delete2 _hrefund2 hle2 hgeq2
        simp only [Devm.gasLeft_setMach] at hgeq2
        simp only [gasStorageSet] at hle2
        refine Func.execSat_segment ?_
          (h_next base2 (G2 - 12) hkey ?_ ?_ (by omega))
        · intro ex hex
          func_run (1) []
          exact hex
        · intro a k hne
          rw [hoth a k hne]
          exact h_stor a k
        · rw [her2]
          simpa only [Devm.setMach_error] using h_er

/-- **The balance-low leaf.**  The receiver's balance cannot cover the burn:
`burnAndReturn` deliberately reverts before writing anything. -/
lemma execSat_burnLow_leaf {sevm : Sevm} {b : Devm}
    {wad receiver rbal : B256} {M : Mem} {G : Nat} {P : Execution → Prop}
    (h_rbal : b.getStorVal sevm.currentTarget receiver = rbal)
    (h_low : (rbal <? wad) = 1)
    (h_gas : 2130 ≤ G)
    (hP : ∀ post : Devm, P (.error (.revert, post))) :
    Func.ExecSat (fmint.main :: fmint.aux) sevm
      (b.setMach ⟨[wad, receiver], M, G⟩) burnAndReturn P := by
  refine Func.execSat_next
    (Ninst.runCompiled_dup (n := 1) (G := G - gVerylow) rfl
      (by simp only [Devm.gasLeft_setMach, gVerylow]; omega)
      (by simp only [Devm.stack_setMach, List.length_cons, List.length_nil]
          omega)) ?_
  apply Func.execSat_sload_step (k := receiver) (v := rbal)
    (s := [wad, receiver]) (M := M)
  · rfl
  · simp only [List.length_cons, List.length_nil]; omega
  · exact h_rbal
  · rfl
  · simp only [Devm.gasLeft_setMach, gasColdSload, gVerylow]; omega
  · intro base c G1 h_in h_mono h_stor _h_bal _h_code h_rc h_logs _h_output h_er
      _h_delete h_lo h_hi h_geq
    simp only [Devm.gasLeft_setMach, gVerylow] at h_geq
    simp only [gasColdSload] at h_hi
    have hG : 27 ≤ G1 := by omega
    apply Func.execSat_of_runCompiledTo
    · func_run (4) [1]
      exact Func.runCompiledTo_revert_func (G := G1 - 27)
        (by simp only [Devm.gasLeft_setMach, gBase]; omega)
        (by simp only [Devm.stack_setMach, List.length_cons, List.length_nil]
            omega)
    · exact hP _

set_option maxRecDepth 629 in
/-- **The success leaf.**  The balance covers the burn: the pair is written —
each `SSTORE` warm behind its own `SLOAD` (F28), each clearing the EIP-2200
sentry because `gasStorageSet ≤ gasLeft` subsumes it — the burn `Transfer` is
logged, and the frame returns `true`.  The `.ok` arm of the trichotomy. -/
lemma execSat_burnOk_leaf {sevm : Sevm} {b : Devm}
    {wad receiver rbal : B256} {M : Mem} {G : Nat} {P : Execution → Prop}
    (h_rbal : b.getStorVal sevm.currentTarget receiver = rbal)
    (h_ge : (rbal <? wad) = 0)
    (h_static : sevm.isStatic = false)
    (h32 : M.size % 32 = 0)
    (h_msz : 64 ≤ M.size)
    (h_gas : 46046 ≤ G)
    (hP : ∀ post : Devm, post.error = b.error → P (.ok post)) :
    Func.ExecSat (fmint.main :: fmint.aux) sevm
      (b.setMach ⟨[wad, receiver], M, G⟩) burnAndReturn P := by
  have hs1 : (M.write ((0 * 32 : B256)).toNat wad.toBytes).size = M.size := by
    apply Mem.size_write_of_le
    rw [B256.length_toBytes,
      show ((0 * 32 : B256)).toNat + 32 = 32 from by decide]
    omega
  have hs2 : (((M.write ((0 * 32 : B256)).toNat wad.toBytes).read
      ((0 * 32 : B256)).toNat ((1 * 32 : B256)).toNat).2).size = M.size := by
    rw [Mem.size_read_snd_of_le (by rw [hs1]; exact h32)
      (by rw [hs1,
            show ((0 * 32 : B256)).toNat + ((1 * 32 : B256)).toNat = 32 from
              by decide]
          omega),
      hs1]
  have hs3 : ((((M.write ((0 * 32 : B256)).toNat wad.toBytes).read
      ((0 * 32 : B256)).toNat ((1 * 32 : B256)).toNat).2).write
        ((0 * 32 : B256)).toNat (1 : B256).toBytes).size = M.size := by
    rw [Mem.size_write_of_le, hs2]
    rw [hs2, B256.length_toBytes,
      show ((0 * 32 : B256)).toNat + 32 = 32 from by decide]
    omega
  refine Func.execSat_next
    (Ninst.runCompiled_dup (n := 1) (G := G - gVerylow) rfl
      (by simp only [Devm.gasLeft_setMach, gVerylow]; omega)
      (by simp only [Devm.stack_setMach, List.length_cons, List.length_nil]
          omega)) ?_
  apply Func.execSat_sload_step (k := receiver) (v := rbal)
    (s := [wad, receiver]) (M := M)
  · rfl
  · simp only [List.length_cons, List.length_nil]; omega
  · exact h_rbal
  · rfl
  · simp only [Devm.gasLeft_setMach, gasColdSload, gVerylow]; omega
  · intro base c G1 h_in h_mono h_stor _h_bal _h_code h_rc h_logs _h_output h_er
      _h_delete h_lo h_hi h_geq
    simp only [Devm.gasLeft_setMach, gVerylow] at h_geq
    simp only [gasColdSload] at h_hi
    have hG1 : 43943 ≤ G1 := by omega
    apply Func.execSat_segment
    · intro ex hex
      func_run (8) [0, rbal - wad]
      exact hex
    · apply Func.execSat_sstore_warm_step (k := receiver) (v := rbal - wad)
        (s := [wad, receiver]) (M := M)
      · rfl
      · exact h_in
      · exact h_static
      · rfl
      · simp only [Devm.gasLeft_setMach, gasStorageSet]; omega
      · intro base2 c2 G2 hkey2 hoth2 _h_bal2 _h_code2 hacc2 hlogs2 _hout2
          her2 _h_delete2 _hrefund2 hle2 hgeq2
        simp only [Devm.gasLeft_setMach] at hgeq2
        simp only [gasStorageSet] at hle2
        have hG2 : 23909 ≤ G2 := by omega
        apply Func.execSat_segment
        · intro ex hex
          func_run (2) [supplySlot]
          exact hex
        · apply Func.execSat_sload_step (k := supplySlot)
            (v := base2.getStorVal sevm.currentTarget supplySlot)
            (s := [wad, receiver]) (M := M)
          · rfl
          · simp only [List.length_cons, List.length_nil]; omega
          · rfl
          · rfl
          · simp only [Devm.gasLeft_setMach, gasColdSload]; omega
          · intro base3 c3 G3 h_in3 h_mono3 h_stor3 _h_bal3 _h_code3 h_rc3 h_logs3 _hout3 h_er3
              _h_delete3 h_lo3 h_hi3 h_geq3
            simp only [Devm.gasLeft_setMach] at h_geq3
            simp only [gasColdSload] at h_hi3
            have hG3 : 21804 ≤ G3 := by omega
            apply Func.execSat_segment
            · intro ex hex
              func_run (5)
                [base2.getStorVal sevm.currentTarget supplySlot - wad,
                  supplySlot]
              exact hex
            · apply Func.execSat_sstore_warm_step (k := supplySlot)
                (v := base2.getStorVal sevm.currentTarget supplySlot - wad)
                (s := [wad, receiver]) (M := M)
              · rfl
              · exact h_in3
              · exact h_static
              · rfl
              · simp only [Devm.gasLeft_setMach, gasStorageSet]; omega
              · intro base4 c4 G4 hkey4 hoth4 _h_bal4 _h_code4 hacc4 hlogs4
                  _hout4 her4 _h_delete4 _hrefund4 hle4 hgeq4
                simp only [Devm.gasLeft_setMach] at hgeq4
                simp only [gasStorageSet] at hle4
                have hG4 : 1790 ≤ G4 := by omega
                apply Func.execSat_of_runCompiledTo
                · func_run (14) [0, 1756, 0]
                  · exact Devm.extCost_zero_of_le h32 (by
                      rw [show ((0 * 32 : B256)).toNat + 32 = 32 from by decide]
                      omega)
                  · rw [Devm.extCost_zero_of_le (by rw [hs1]; exact h32) (by
                      rw [hs1, show ((0 * 32 : B256)).toNat
                        + ((1 * 32 : B256)).toNat = 32 from by decide]
                      omega)]
                    decide
                  · exact Devm.extCost_zero_of_le (by rw [hs2]; exact h32) (by
                      rw [hs2,
                        show ((0 * 32 : B256)).toNat + 32 = 32 from by decide]
                      omega)
                  · exact Func.runCompiledTo_return_word rfl
                      (Devm.extCost_zero_of_le (by rw [hs3]; exact h32) (by
                        rw [hs3, show ((0 : B256)).toNat + ((32 : B256)).toNat
                          = 32 from by decide]
                        omega))
                      (Nat.add_zero _).symm rfl
                · refine hP _ ?_
                  simp only [Devm.addLog_error, Devm.setMach_error,
                    Devm.withOutput_error, Devm.memRead_error,
                    her4, h_er3, her2, h_er]

/-! ## The continuation bound

`flashLoanContGasMax` bounds what *any* post-`CALL` leaf can spend, in Jaune's
schedule symbols per **A3**: worst case at every warmth-open read (cold price)
and every value-open store (`gasStorageSet`), exact everywhere else.  The
worst path is flag `1` → both returndata checks pass → collision guard passes
→ the finite-allowance arm's decrement → `burnAndReturn`'s full success
epilogue; every other leaf stops strictly earlier and cheaper (the landed
floors: 21, 42, 82, 113 after the guard, 2 152, 2 130).  `gasStorageSet ≤
gasLeft` at each of the two burn-side `SSTORE`s is what the walk demands, and
it subsumes the EIP-2200 `gCallStipend < gasLeft` sentry — `gCallStipend =
2300 < 20000` — so clearing the sentry costs the bound nothing extra. -/

/-- The flag test and both returndata checks, flag `1`, both passing: the
`ISZERO`/branch, `returnDataShorterThan 32`, and `checkReturnDataHead` with its
`RETURNDATACOPY` of one covered word.  77 gas. -/
def flashLoanFlagCheckGas : Nat :=
  gVerylow + (gVerylow + gHigh)
    + (gVerylow + gBase + gVerylow + (gVerylow + gHigh))
    + (gVerylow + gBase + gBase + (gVerylow + gasCopy) + gBase + gVerylow
        + gVerylow + gVerylow + gVerylow + (gVerylow + gHigh))

/-- The repayment key's hash and collision guard, passing: the two head-word
stores, the two-word `KECCAK256`, `checkSlotCollides`, and the untaken revert
branch.  108 gas. -/
def flashLoanSpendGuardGas : Nat :=
  (gVerylow + gBase + gVerylow)
    + (gBase + gVerylow + gVerylow)
    + (gVerylow + gBase)
    + (gKeccak256 + gasKeccak256Word * 2)
    + (gVerylow + (gBase + gVerylow + gVerylow + gVerylow) + gVerylow
        + gVerylow + gVerylow + gVerylow + gVerylow + gVerylow)
    + (gVerylow + gHigh)

/-- The finite-allowance arm — the dearer of the two, and the only one that
writes: the allowance read at the cold price, the `isMax` and bound tests both
falling through, the decrement's `SSTORE` at `gasStorageSet`, and the tail
call into `burnSlot`.  22 171 gas. -/
def flashLoanSpendFinGas : Nat :=
  gVerylow + gasColdSload
    + (gVerylow + gVerylow + gVerylow + (gVerylow + gHigh))
    + (gVerylow + gVerylow + gVerylow + (gVerylow + gHigh))
    + (gVerylow + gVerylow + gVerylow + gVerylow + gasStorageSet)
    + (gVerylow + gMid + gJumpdest)

/-- `burnAndReturn`'s success path: the balance read (cold price) and the
bound test falling through, the burn pair at `gasStorageSet` each with the
supply read between them at the cold price, the burn `Transfer` log over a
covered one-word window, and `returnTrue`.  46 046 gas. -/
def flashLoanBurnGas : Nat :=
  gVerylow + gasColdSload
    + (gVerylow + gVerylow + gVerylow + (gVerylow + gHigh))
    + (gVerylow + gVerylow + gVerylow + gVerylow + gasStorageSet)
    + (gBase + gVerylow + gasColdSload)
    + (gVerylow + gVerylow + gVerylow + (gBase + gVerylow) + gasStorageSet)
    + (gVerylow + (gBase + gVerylow) + gBase + gVerylow + gVerylow)
    + (gVerylow + gBase + (gLog + gLogdata * 32 + gLogtopic * 3))
    + (gVerylow + (gBase + gVerylow) + gVerylow + gBase)

/-- **The bound on every post-`CALL` leaf's spend** (A3's `contMax`): the
worst path's four segments, in order.  Every leaf's landed floor premise is at
most this, which is what the 3d assembly consumes. -/
def flashLoanContGasMax : Nat :=
  flashLoanFlagCheckGas + flashLoanSpendGuardGas + flashLoanSpendFinGas
    + flashLoanBurnGas

/-- 68 402 gas: 77 + 108 + 22 171 + 46 046.  Read it as the three value-open
`SSTORE`s at 20 000 each, the three warmth-open `SLOAD`s at 2 100 each, 1 756
of `LOG3`, 42 of `KECCAK256`, and 304 of control flow. -/
theorem flashLoanContGasMax_eq : flashLoanContGasMax = 68402 := by decide

/-- Term-keyed sibling of `execSat_returnDataShort_leaf`, for the assembly's
case split: the machine compares `Nat.toB256 d.returnData.length` — the
*wrapped* length — against 32, so exhaustive coverage splits on that
comparison and not on the bare `Nat` bound, which the model does not cap. -/
lemma execSat_returnDataShort_leaf' {sevm : Sevm} {d : Devm}
    {amount receiver : B256} {M : Mem} {Gc : Nat} {P : Execution → Prop}
    (h_lt : (Nat.toB256 d.returnData.length <? (32 : B256)) = 1)
    (h_gas : 42 ≤ Gc)
    (hP : ∀ post : Devm, P (.error (.revert, post))) :
    Func.ExecSat (fmint.main :: fmint.aux) sevm
      (d.setMach ⟨1 :: [amount, receiver], M, Gc⟩) flashLoanFromFlag P := by
  apply Func.execSat_of_runCompiledTo
  · func_run (6) [0, 1]
    exact Func.runCompiledTo_revert_func (G := Gc - 42)
      (by simp only [Devm.gasLeft_setMach, gBase]; omega)
      (by simp only [Devm.stack_setMach, List.length_cons, List.length_nil]
          omega)
  · exact hP _

/-- **The assembled bound** (A3): the trunk's exact worst case, the `CALL`'s
own extras — the account access and the EIP-7702 delegation resolution, at
most `2 * gasColdAccountAccess` because the argument and return windows are
covered by the trunk's own memory (F27) — and EIP-150's sixty-fourfold of the
continuation bound, which is what the frame provably retains after forwarding
everything it has. -/
def flashLoanGas (dataLen : Nat) : Nat :=
  flashLoanPreCallGas dataLen + 2 * gasColdAccountAccess
    + 64 * flashLoanContGasMax

/-- 4 429 379 gas on an empty payload: 46 451 for the trunk, 5 200 for the
call's extras, and 64 × 68 402 for the retained sixty-fourth.  Well under a
block: the borrower may burn, bomb, or squander everything it is offered and
the caller still cannot be starved. -/
theorem flashLoanGas_zero : flashLoanGas 0 = 4429379 := by decide

/-- **The trichotomy, with the settled-error field carried on the `.ok` arm.**

This is the assembled case tree, and `fmint_flashLoan_settles` below is its
pinned corollary.  The extra conjunct — the successful outcome's
`Devm.error` is the one the frame started with — is what the *frame* altitude
needs and cannot recover afterwards: `processMessage.settle` decides between
`out.error = none` and a rollback by reading that field, and no lemma in the
repository transports it across an arbitrary `Exec`.  So it is threaded down
the walk instead, one handed-back equation per continuation-passing step, and
discharged at the `.ok` terminal through Jaune's matching update-first
projection lemmas.

It says nothing new about the borrower: the field is untouched by
`incorporateChildOnSuccess`/`OnError`, so a callback cannot write it. -/
theorem flashLoan_settles_error {sevm : Sevm} {pre : Devm}
    {receiver token amount : B256} {data : Bytes}
    (h_code : some sevm.code.toList = Prog.compile fmint)
    (h_sel : Sevm.selector sevm = flashLoanSelector)
    (h_static : sevm.isStatic = false)
    (h_dec : Sevm.DecodesCallWithTail sevm flashLoanSelector
      [receiver, token, amount] data)
    (h_size : 196 + ceil32 data.length < 2 ^ 256)
    (h_token : token = sevm.currentTarget.toB256)
    (h_addr : ValidAdr receiver)
    (h_nof : B256.Nof ((Devm.getStor pre sevm.currentTarget).get supplySlot)
      amount)
    (h_stack : pre.stack = [])
    (h_mem : pre.memory = Mem.empty)
    (h_gas : flashLoanGas data.length ≤ pre.gasLeft) :
    (∃ post, exec ⟨0, sevm, pre⟩ = .ok post ∧ post.error = pre.error) ∨
    (∃ post, exec ⟨0, sevm, pre⟩ = .error (.revert, post)) ∨
    (∃ e post, exec ⟨0, sevm, pre⟩ = .error (e, post) ∧ NonConsensus e) := by
  refine Prog.execSat_out (P := fun ex =>
      (∃ post, ex = .ok post ∧ post.error = pre.error) ∨
      (∃ post, ex = .error (.revert, post)) ∨
      (∃ e post, ex = .error (e, post) ∧ NonConsensus e)) ?_ h_code
  refine flashLoan_execSat_flag (K := flashLoanContGasMax) h_sel h_dec h_size
    h_token h_addr h_nof h_static h_stack h_mem h_gas ?_ ?_ ?_
  · intro e dd hnc
    exact Or.inr (Or.inr ⟨e, dd, rfl, hnc⟩)
  · intro dd Gc hK
    rw [flashLoanContGasMax_eq] at hK
    exact execSat_flagZero_leaf (by omega)
      (fun post => Or.inr (Or.inl ⟨post, rfl⟩))
  · intro dd Gc hK hEr
    rw [flashLoanContGasMax_eq] at hK
    by_cases hLen : Nat.toB256 dd.returnData.length < (32 : B256)
    · refine execSat_returnDataShort_leaf' ?_ (by omega)
        (fun post => Or.inr (Or.inl ⟨post, rfl⟩))
      rw [show (Nat.toB256 dd.returnData.length <? (32 : B256))
        = if Nat.toB256 dd.returnData.length < 32 then (1 : B256) else 0
        from rfl, if_pos hLen]
    · have h_ge : (Nat.toB256 dd.returnData.length <? (32 : B256)) = 0 := by
        rw [show (Nat.toB256 dd.returnData.length <? (32 : B256))
          = if Nat.toB256 dd.returnData.length < 32 then (1 : B256) else 0
          from rfl, if_neg hLen]
      have h32c : (flashLoanCallMem sevm amount data).size % 32 = 0 := by
        rw [flashLoanCallMem_size, ceil32_eq_mul]; omega
      have hmszc : 64 ≤ (flashLoanCallMem sevm amount data).size := by
        rw [flashLoanCallMem_size]; omega
      by_cases hMagic : erc3156Magic
          = flashLoanReturnDataHead dd (flashLoanCallMem sevm amount data)
      case neg =>
        refine execSat_magicMismatch_leaf h_ge ?_ h32c hmszc (by omega)
          (fun post => Or.inr (Or.inl ⟨post, rfl⟩))
        rw [show (erc3156Magic =? flashLoanReturnDataHead dd
            (flashLoanCallMem sevm amount data))
          = if erc3156Magic = flashLoanReturnDataHead dd
              (flashLoanCallMem sevm amount data) then (1 : B256) else 0
          from rfl, if_neg hMagic]
      case pos =>
        have h_eq : (erc3156Magic =? flashLoanReturnDataHead dd
            (flashLoanCallMem sevm amount data)) = 1 := by
          rw [show (erc3156Magic =? flashLoanReturnDataHead dd
              (flashLoanCallMem sevm amount data))
            = if erc3156Magic = flashLoanReturnDataHead dd
                (flashLoanCallMem sevm amount data) then (1 : B256) else 0
            from rfl, if_pos hMagic]
        refine execSat_spend_step h_ge h_eq h32c hmszc (by omega) ?_
        intro M' hsM'
        have h32' : M'.size % 32 = 0 := by rw [hsM']; exact h32c
        have hmsz' : 64 ≤ M'.size := by rw [hsM']; exact hmszc
        set hh : B256 := Bytes.keccak ((((M'.write ((0 * 32 : B256)).toNat
          receiver.toBytes).write ((1 * 32 : B256)).toNat
            sevm.currentTarget.toB256.toBytes).read (B256.toNat 0)
              (B256.toNat 64)).1) with hhash
        by_cases hA : ((~~~ (0 : B256)) <<< (Nat.toB256 160).toNat) &&& hh = 0
        · by_cases hB : ~~~ hh = 0
          · exact execSat_slotCollision_leaf (va := 1) (mx := 1) hhash.symm
              (by rw [show B256.eqCheck
                    (((~~~ (0 : B256)) <<< (Nat.toB256 160).toNat) &&& hh) 0
                  = if ((~~~ (0 : B256)) <<< (Nat.toB256 160).toNat) &&& hh = 0
                    then (1 : B256) else 0 from rfl, if_pos hA])
              (by rw [show B256.eqCheck (~~~ hh) 0
                  = if ~~~ hh = 0 then (1 : B256) else 0 from rfl, if_pos hB])
              (by decide) h32' hmsz' (by omega)
              (fun post => Or.inr (Or.inl ⟨post, rfl⟩))
          · exact execSat_slotCollision_leaf (va := 1) (mx := 0) hhash.symm
              (by rw [show B256.eqCheck
                    (((~~~ (0 : B256)) <<< (Nat.toB256 160).toNat) &&& hh) 0
                  = if ((~~~ (0 : B256)) <<< (Nat.toB256 160).toNat) &&& hh = 0
                    then (1 : B256) else 0 from rfl, if_pos hA])
              (by rw [show B256.eqCheck (~~~ hh) 0
                  = if ~~~ hh = 0 then (1 : B256) else 0 from rfl, if_neg hB])
              (by decide) h32' hmsz' (by omega)
              (fun post => Or.inr (Or.inl ⟨post, rfl⟩))
        · by_cases hB : ~~~ hh = 0
          · exact execSat_slotCollision_leaf (va := 0) (mx := 1) hhash.symm
              (by rw [show B256.eqCheck
                    (((~~~ (0 : B256)) <<< (Nat.toB256 160).toNat) &&& hh) 0
                  = if ((~~~ (0 : B256)) <<< (Nat.toB256 160).toNat) &&& hh = 0
                    then (1 : B256) else 0 from rfl, if_neg hA])
              (by rw [show B256.eqCheck (~~~ hh) 0
                  = if ~~~ hh = 0 then (1 : B256) else 0 from rfl, if_pos hB])
              (by decide) h32' hmsz' (by omega)
              (fun post => Or.inr (Or.inl ⟨post, rfl⟩))
          · refine execSat_spendGuard_step hhash.symm
              (by rw [show B256.eqCheck
                    (((~~~ (0 : B256)) <<< (Nat.toB256 160).toNat) &&& hh) 0
                  = if ((~~~ (0 : B256)) <<< (Nat.toB256 160).toNat) &&& hh = 0
                    then (1 : B256) else 0 from rfl, if_neg hA])
              (by rw [show B256.eqCheck (~~~ hh) 0
                  = if ~~~ hh = 0 then (1 : B256) else 0 from rfl, if_neg hB])
              h32' hmsz' (by omega) ?_
            intro M'' hsM''
            have h32'' : M''.size % 32 = 0 := by rw [hsM'']; exact h32'
            have hmsz'' : 64 ≤ M''.size := by rw [hsM'']; exact hmsz'
            by_cases hMax : ~~~ (dd.getStorVal sevm.currentTarget hh) = 0
            · refine execSat_spendInf_step rfl
                (by rw [show B256.eqCheck
                      (~~~ dd.getStorVal sevm.currentTarget hh) 0
                    = if ~~~ dd.getStorVal sevm.currentTarget hh = 0
                      then (1 : B256) else 0 from rfl, if_pos hMax])
                (by omega) ?_
              intro b G hstor hEb hG
              by_cases hBal : b.getStorVal sevm.currentTarget receiver < amount
              · exact execSat_burnLow_leaf rfl
                  (by rw [show (b.getStorVal sevm.currentTarget receiver
                      <? amount)
                    = if b.getStorVal sevm.currentTarget receiver < amount
                      then (1 : B256) else 0 from rfl, if_pos hBal])
                  (by omega) (fun post => Or.inr (Or.inl ⟨post, rfl⟩))
              · exact execSat_burnOk_leaf rfl
                  (by rw [show (b.getStorVal sevm.currentTarget receiver
                      <? amount)
                    = if b.getStorVal sevm.currentTarget receiver < amount
                      then (1 : B256) else 0 from rfl, if_neg hBal])
                  h_static h32'' hmsz'' (by omega)
                  (fun post hp => Or.inl ⟨post, rfl, hp.trans (hEb.trans hEr)⟩)
            · by_cases hAlw : dd.getStorVal sevm.currentTarget hh < amount
              · exact execSat_allowanceLow_leaf rfl
                  (by rw [show B256.eqCheck
                        (~~~ dd.getStorVal sevm.currentTarget hh) 0
                      = if ~~~ dd.getStorVal sevm.currentTarget hh = 0
                        then (1 : B256) else 0 from rfl, if_neg hMax])
                  (by rw [show (dd.getStorVal sevm.currentTarget hh <? amount)
                    = if dd.getStorVal sevm.currentTarget hh < amount
                      then (1 : B256) else 0 from rfl, if_pos hAlw])
                  (by omega) (fun post => Or.inr (Or.inl ⟨post, rfl⟩))
              · refine execSat_spendFin_step rfl
                  (by rw [show B256.eqCheck
                        (~~~ dd.getStorVal sevm.currentTarget hh) 0
                      = if ~~~ dd.getStorVal sevm.currentTarget hh = 0
                        then (1 : B256) else 0 from rfl, if_neg hMax])
                  (by rw [show (dd.getStorVal sevm.currentTarget hh <? amount)
                    = if dd.getStorVal sevm.currentTarget hh < amount
                      then (1 : B256) else 0 from rfl, if_neg hAlw])
                  h_static (by omega) ?_
                intro b G hkey hoth hEb hG
                by_cases hBal :
                    b.getStorVal sevm.currentTarget receiver < amount
                · exact execSat_burnLow_leaf rfl
                    (by rw [show (b.getStorVal sevm.currentTarget receiver
                        <? amount)
                      = if b.getStorVal sevm.currentTarget receiver < amount
                        then (1 : B256) else 0 from rfl, if_pos hBal])
                    (by omega) (fun post => Or.inr (Or.inl ⟨post, rfl⟩))
                · exact execSat_burnOk_leaf rfl
                    (by rw [show (b.getStorVal sevm.currentTarget receiver
                        <? amount)
                      = if b.getStorVal sevm.currentTarget receiver < amount
                        then (1 : B256) else 0 from rfl, if_neg hBal])
                    h_static h32'' hmsz'' (by omega)
                    (fun post hp =>
                      Or.inl ⟨post, rfl, hp.trans (hEb.trans hEr)⟩)

/-- **The headline: `flashLoan` cannot be griefed into an exceptional halt.**

Under fmint's own entry conditions — and with **no premise about the
borrower**, whose code, behaviour, gas use and settlement are all quantified
by `pre` itself — every outcome of the frame is one of: a success, a
deliberate `revert`, or the non-consensus machine-fault channel that
`SettledHalt` cannot even store.  In particular no borrower behaviour reaches
an `ExceptionalHalt`: `outOfGas` is unreachable however the callback burns,
because `h_gas` funds the worst leaf through EIP-150's retained sixty-fourth.

`h_static` is a premise about the *caller's* frame, not the borrower: a
caller who `STATICCALL`s `flashLoan` halts at the mint's first `SSTORE` by
its own doing (the F21 amendment, user-adjudicated 2026-08-07). -/
theorem fmint_flashLoan_settles {sevm : Sevm} {pre : Devm}
    {receiver token amount : B256} {data : Bytes}
    (h_code : some sevm.code.toList = Prog.compile fmint)
    (h_sel : Sevm.selector sevm = flashLoanSelector)
    (h_static : sevm.isStatic = false)
    (h_dec : Sevm.DecodesCallWithTail sevm flashLoanSelector
      [receiver, token, amount] data)
    (h_size : 196 + ceil32 data.length < 2 ^ 256)
    (h_token : token = sevm.currentTarget.toB256)
    (h_addr : ValidAdr receiver)
    (h_nof : B256.Nof ((Devm.getStor pre sevm.currentTarget).get supplySlot)
      amount)
    (h_stack : pre.stack = [])
    (h_mem : pre.memory = Mem.empty)
    (h_gas : flashLoanGas data.length ≤ pre.gasLeft) :
    (∃ post, exec ⟨0, sevm, pre⟩ = .ok post) ∨
    (∃ post, exec ⟨0, sevm, pre⟩ = .error (.revert, post)) ∨
    (∃ e post, exec ⟨0, sevm, pre⟩ = .error (e, post) ∧ NonConsensus e) := by
  rcases flashLoan_settles_error h_code h_sel h_static h_dec h_size h_token
    h_addr h_nof h_stack h_mem h_gas with
    ⟨post, h_ok, -⟩ | h | h
  · exact Or.inl ⟨post, h_ok⟩
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)

/-! ## The two guard-failure walks the strengthening needs

`Blanc/FmintReverts.lean` walks guard (0) — `token ≠ self` — to `Func.revert`.
The unguarded form of the headline needs the other two pre-`CALL` guards
walked the same way, so that a call which fails any of them is *still* inside
the trichotomy (a deliberate revert), and the three guard premises can be
dropped from the statement.

Both walks pass every earlier guard, so each carries the earlier guards'
conditions as premises.  Neither crosses the `CALL`. -/

/-- Guard (1)'s revert path: the dispatcher, guard (0) passing, and
`checkNonAddress` firing on a `receiver` word with bits above 160. -/
def receiverNotAddressGas : Nat :=
  gJumpdest
    + (gBase + gVerylow + gVerylow + gVerylow)
    + (gVerylow + gVerylow + gVerylow + (gVerylow + gHigh + gJumpdest))
    + (gVerylow + gVerylow + gVerylow + (gVerylow + gHigh))
    + (gVerylow + gVerylow + gVerylow + (gVerylow + gHigh))
    + (gVerylow + gVerylow + (gVerylow + gHigh + gJumpdest))
    + (gVerylow + gVerylow + gBase + gVerylow + gVerylow + (gVerylow + gHigh))
    + (gVerylow + gVerylow + gVerylow
        + (gBase + gVerylow + gVerylow + gVerylow + gVerylow)
        + (gVerylow + gHigh + gJumpdest))
    + (gBase + gBase)

theorem receiverNotAddressGas_eq : receiverNotAddressGas = 167 := by decide

set_option maxRecDepth 674 in
/-- A `flashLoan` call whose `token` is fmint but whose `receiver` word is not
address-shaped has a gas-exact walk that reverts, with empty revert data. -/
theorem receiverNotAddress_runCompiledTo {sevm : Sevm} {pre : Devm}
    {receiver token amount : B256} {data : Bytes} {w : B256}
    (h_sel : Sevm.selector sevm = flashLoanSelector)
    (h_dec : Sevm.DecodesCallWithTail sevm flashLoanSelector
      [receiver, token, amount] data)
    (h_token : token = sevm.currentTarget.toB256)
    (h_bad : ((~~~ (0 : B256)) <<< (Nat.toB256 160).toNat).and
      (Sevm.argWord sevm 0) = w)
    (h_ne : w ≠ 0)
    (h_stack : pre.stack = [])
    (h_gas : receiverNotAddressGas ≤ pre.gasLeft) :
    ∃ post, Prog.RunCompiledTo sevm pre fmint (.error (.revert, post)) ∧
      Devm.output post = [] := by
  rw [receiverNotAddressGas_eq] at h_gas
  set g := pre.gasLeft with hg
  exact
    ⟨_,
      Prog.runCompiledTo_intro (G := g - 1)
        (mid := pre.setMach ⟨[], pre.memory, g - 1⟩)
        (by simp only [gJumpdest]; omega)
        (by rw [h_stack])
        (by
          func_run (33) [flashLoanSelector, 1, 0, 0, 1, 1, 0,
            ~~~ (0 : B256), (~~~ (0 : B256)) <<< (Nat.toB256 160).toNat, w]
          · show sevm.currentTarget.toB256 =? Sevm.argWord sevm 1 = 1
            rw [argWord_one_of_decodes h_dec, h_token]
            show (if sevm.currentTarget.toB256 = sevm.currentTarget.toB256
              then (1 : B256) else 0) = 1
            rw [if_pos rfl]
          · refine Func.runCompiledTo_branch_succ (G := g - 163) h_ne rfl
              (by simp only [Devm.stack_setMach, List.length_cons,
                List.length_nil]; omega)
              (by simp only [Devm.gasLeft_setMach, gVerylow, gHigh,
                gJumpdest]; omega) ?_
            exact Func.runCompiledTo_revert_func (G := g - 167)
              (by simp only [Devm.gasLeft_setMach, gBase]; omega)
              (by simp only [Devm.stack_setMach, List.length_cons,
                List.length_nil]; omega)),
      rfl⟩

/-- **fmint's `flashLoan` reverts when `receiver` is not address-shaped.**

The `exec`-altitude sibling of `receiverNotAddress_runCompiledTo`, in the mold
of `Blanc/FmintReverts.lean`'s `fmint_token_ne_self_reverts`, and the strong
counterpart of `Blanc/FlashSpec.lean`'s `no_success_of_receiver_not_address`:
that theorem holds with **no gas premise** because "cannot succeed" is not a
claim that the frame reaches anything, and this one cannot be stated without
one.  Neither subsumes the other and both rows stand.

The walk is strictly longer than the `token ≠ self` one because it must pass
guard (0) first, which is why `h_token` is a premise here.  One selector,
message-call altitude, exact frame gas, not exhaustiveness — the frame banner
of `Blanc/FmintReverts.lean` applies verbatim. -/
theorem fmint_receiver_not_address_reverts {sevm : Sevm} {pre : Devm}
    {receiver token amount : B256} {data : Bytes}
    (h_code : some sevm.code.toList = Prog.compile fmint)
    (h_sel : Sevm.selector sevm = flashLoanSelector)
    (h_dec : Sevm.DecodesCallWithTail sevm flashLoanSelector
      [receiver, token, amount] data)
    (h_token : token = sevm.currentTarget.toB256)
    (h_addr : ¬ ValidAdr receiver)
    (h_stack : pre.stack = [])
    (h_gas : receiverNotAddressGas ≤ pre.gasLeft) :
    ∃ post, exec ⟨0, sevm, pre⟩ = .error (.revert, post) ∧
      Devm.output post = [] := by
  have h_ne : ((~~~ (0 : B256)) <<< (Nat.toB256 160).toNat).and
      (Sevm.argWord sevm 0) ≠ 0 := by
    rw [argWord_zero_of_decodes h_dec, ← addressMask_eq_shl]
    exact fun h => h_addr (validAdr_iff.mpr h)
  obtain ⟨post, h_run, h_out⟩ :=
    receiverNotAddress_runCompiledTo h_sel h_dec h_token rfl h_ne h_stack h_gas
  exact ⟨post, Prog.exec_of_runCompiledTo h_run h_code, h_out⟩

/-- Guard (2)'s revert path: the dispatcher, guards (0) and (1) passing, and
the headroom check firing.  The `SLOAD` of `supplySlot` is warmth-open, so
this is a *bound* at the cold price and not an exact figure — the only
warmth-dependent guard walk in the family. -/
def amountOverBoundGas : Nat :=
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
        + gVerylow + gVerylow + (gVerylow + gHigh + gJumpdest))
    + (gBase + gBase)

/-- 2 300 gas: 200 of walking and one cold `SLOAD`. -/
theorem amountOverBoundGas_eq : amountOverBoundGas = 2300 := by decide

set_option maxRecDepth 672 in
/-- A `flashLoan` call past the first two guards whose `amount` exceeds
`maxFlashLoan = 2^256 - 1 - totalSupply` reverts, with empty revert data. -/
theorem fmint_amount_over_bound_reverts {sevm : Sevm} {pre : Devm}
    {receiver token amount : B256} {data : Bytes}
    (h_code : some sevm.code.toList = Prog.compile fmint)
    (h_sel : Sevm.selector sevm = flashLoanSelector)
    (h_dec : Sevm.DecodesCallWithTail sevm flashLoanSelector
      [receiver, token, amount] data)
    (h_token : token = sevm.currentTarget.toB256)
    (h_addr : ValidAdr receiver)
    (h_over : ¬ B256.Nof (Devm.getStorVal pre sevm.currentTarget supplySlot)
      amount)
    (h_stack : pre.stack = [])
    (h_gas : amountOverBoundGas ≤ pre.gasLeft) :
    ∃ post, exec ⟨0, sevm, pre⟩ = .error (.revert, post) := by
  have h_arg0 : Sevm.argWord sevm 0 = receiver := argWord_zero_of_decodes h_dec
  have h_arg2 : Sevm.argWord sevm 2 = amount := argWord_two_of_decodes h_dec
  have h_lt : ~~~ (Devm.getStorVal pre sevm.currentTarget supplySlot) < amount :=
    lt_of_not_ge fun hle => h_over (B256.nof_of_le_not hle)
  rw [amountOverBoundGas_eq] at h_gas
  set g := pre.gasLeft with hg
  refine Prog.execSat_out (P := fun ex => ∃ post, ex = .error (.revert, post))
    ?_ h_code
  refine Prog.execSat_intro (G := g - 1)
    (mid := pre.setMach ⟨[], pre.memory, g - 1⟩)
    (by simp only [gJumpdest]; omega) (by rw [h_stack]) ?_
  apply Func.execSat_segment
  · intro ex hex
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
    exact hex
  refine Func.execSat_sload_step
    (v := Devm.getStorVal pre sevm.currentTarget supplySlot) rfl (by simp)
    rfl (M := pre.memory) rfl
    (by simp only [Devm.gasLeft_setMach, gasColdSload]; omega) ?_
  intro base c G h_in h_mono h_stor _h_bal _h_code h_rc h_logs _h_output h_er
    _h_delete h_lo h_hi h_geq
  simp only [Devm.gasLeft_setMach, gasColdSload] at h_geq h_hi
  have hG : 24 ≤ G := by omega
  apply Func.execSat_of_runCompiledTo
  · have h_fire : (~~~ (Devm.getStorVal pre sevm.currentTarget supplySlot)
        <? Sevm.argWord sevm 2) = 1 := by
      rw [h_arg2]
      show (if ~~~ (Devm.getStorVal pre sevm.currentTarget supplySlot) < amount
        then (1 : B256) else 0) = 1
      rw [if_pos h_lt]
    func_run (3) [~~~ (Devm.getStorVal pre sevm.currentTarget supplySlot), 1]
    exact Func.runCompiledTo_revert_func (G := G - 24)
      (by simp only [Devm.gasLeft_setMach, gBase]; omega)
      (by simp only [Devm.stack_setMach, List.length_cons, List.length_nil]
          omega)
  · exact ⟨_, rfl⟩

/-- **The unguarded headline: `flashLoan` settles on *any* call.**

`fmint_flashLoan_settles`'s three guard premises — `token = self`, `receiver`
address-shaped, `amount` within the headroom — dropped.  A call that fails a
guard does not leave the trichotomy: it takes that guard's deliberate revert,
which is the second disjunct, so the conclusion is unchanged and the
statement now holds of **every** `flashLoan` call at this gas.

What remains is what the trichotomy is really about: canonical calldata
(`h_dec`, `h_size`), a non-static caller frame (`h_static`), a frame entered
clean (`h_stack`, `h_mem`), and enough gas (`h_gas`).  There is still no
premise about the borrower.

`h_gas` is `flashLoanGas`'s worst case for all four arms: the three guard
walks are far cheaper (131, 167 and 2 300 gas), and stating them at their own
bounds is what `fmint_token_ne_self_reverts`,
`receiverNotAddress_runCompiledTo` and `fmint_amount_over_bound_reverts` do.
As everywhere in the family, this is construction and not exhaustiveness. -/
theorem fmint_flashLoan_settles_of_call {sevm : Sevm} {pre : Devm}
    {receiver token amount : B256} {data : Bytes}
    (h_code : some sevm.code.toList = Prog.compile fmint)
    (h_sel : Sevm.selector sevm = flashLoanSelector)
    (h_static : sevm.isStatic = false)
    (h_dec : Sevm.DecodesCallWithTail sevm flashLoanSelector
      [receiver, token, amount] data)
    (h_size : 196 + ceil32 data.length < 2 ^ 256)
    (h_stack : pre.stack = [])
    (h_mem : pre.memory = Mem.empty)
    (h_gas : flashLoanGas data.length ≤ pre.gasLeft) :
    (∃ post, exec ⟨0, sevm, pre⟩ = .ok post) ∨
    (∃ post, exec ⟨0, sevm, pre⟩ = .error (.revert, post)) ∨
    (∃ e post, exec ⟨0, sevm, pre⟩ = .error (e, post) ∧ NonConsensus e) := by
  have h_room : 4377728 ≤ pre.gasLeft := by
    simp only [flashLoanGas, flashLoanContGasMax_eq] at h_gas; omega
  by_cases h_tok : token = sevm.currentTarget.toB256
  · by_cases h_adr : ValidAdr receiver
    · by_cases h_nof : B256.Nof
          ((Devm.getStor pre sevm.currentTarget).get supplySlot) amount
      · exact fmint_flashLoan_settles h_code h_sel h_static h_dec h_size h_tok
          h_adr h_nof h_stack h_mem h_gas
      · exact Or.inr (Or.inl (fmint_amount_over_bound_reverts h_code h_sel
          h_dec h_tok h_adr h_nof h_stack
          (by rw [amountOverBoundGas_eq]; omega)))
    · refine Or.inr (Or.inl ?_)
      have h_ne : ((~~~ (0 : B256)) <<< (Nat.toB256 160).toNat).and
          (Sevm.argWord sevm 0) ≠ 0 := by
        rw [argWord_zero_of_decodes h_dec, ← addressMask_eq_shl]
        exact fun h => h_adr (validAdr_iff.mpr h)
      obtain ⟨post, h_run, -⟩ := receiverNotAddress_runCompiledTo h_sel h_dec
        h_tok (w := ((~~~ (0 : B256)) <<< (Nat.toB256 160).toNat).and
          (Sevm.argWord sevm 0)) rfl h_ne h_stack
        (by rw [receiverNotAddressGas_eq]; omega)
      exact ⟨post, Prog.exec_of_runCompiledTo h_run h_code⟩
  · obtain ⟨post, h_exec, -⟩ := fmint_token_ne_self_reverts h_code h_sel h_dec
      h_tok h_stack (by rw [tokenNeSelfGas_eq]; omega)
    exact Or.inr (Or.inl ⟨post, h_exec⟩)

/-! ## The frame: what fmint's caller is handed

`Blanc/FmintReverts.lean`'s `rollback_revert_of_exec_revert` composes one
`exec`-altitude *revert* into a frame settlement.  The trichotomy needs the
same composition on all three arms at once, and the arm that is new is the
`.ok` one: `processMessage.settle` decides between `out.error = none` and a
rollback by reading `Devm.error`, and the successful outcome's value of that
field is exactly what `flashLoan_settles_error` carries down the walk.

**The fatal arm needs no premise of its own.**  It is excluded by the shape of
`h_pm`: a non-consensus error propagates through `executeCode.handleError` on
the *error* channel, `processMessage.settle` passes it through, and the frame
never produces an `.ok out` at all.  That is what the standing `.ok out`
premise of the whole frame family quarantines here.

**Still one frame, and still not a transaction**, and still not
exhaustiveness — `Blanc/FmintReverts.lean`'s frame banner applies verbatim. -/

/-- **A frame whose code settles, settles at its frame too.**

The trichotomy's generic frame composition, stated once over the abstract
premise `h_exec` in the mold of `rollback_revert_of_exec_revert`, whose three
structural premises (`h_fill`, `h_bt`, `h_prec`) it takes for that theorem's
reasons.

**Contract-agnostic**; it lives in fmint's module because its consumer does. -/
theorem frame_settles_of_exec_settles {msg : Msg} {benv : Benv} {xl : Xlot}
    {out : Devm}
    (h_pm : ProcessMessage msg xl (.ok out))
    (h_fill : Xlot.Filled xl)
    (h_bt : msg.benvAfterTransfer = .ok benv)
    (h_prec : ∀ adr, msg.codeAddress = some adr →
      ¬ (!msg.disablePrecompiles && decide (benv.stat.rules.isPrecomp adr)) = true)
    (h_exec :
      (∃ post, exec ⟨0, initSevm (msg.withBenv benv),
          initDevm (msg.withBenv benv)⟩ = .ok post ∧ post.error = none) ∨
      (∃ post, exec ⟨0, initSevm (msg.withBenv benv),
          initDevm (msg.withBenv benv)⟩ = .error (.revert, post)) ∨
      (∃ e post, exec ⟨0, initSevm (msg.withBenv benv),
          initDevm (msg.withBenv benv)⟩ = .error (e, post) ∧ NonConsensus e)) :
    out.error = none ∨ out.error = some .revert := by
  obtain ⟨r0, hbody, hset⟩ := ProcessMessage.iff_body.mp h_pm
  unfold FrameBody at hbody
  rw [h_bt] at hbody
  have key : executeCode.handleError
      (exec ⟨0, initSevm (msg.withBenv benv),
        initDevm (msg.withBenv benv)⟩) = r0 := by
    rcases h_ca : (msg.withBenv benv).codeAddress with _ | adr
    · obtain ⟨ex', h_xl, h_he⟩ := of_executeCode_noneCode h_ca hbody
      subst h_xl
      obtain ⟨exc⟩ := h_fill
      have h_eq : exec ⟨0, initSevm (msg.withBenv benv),
          initDevm (msg.withBenv benv)⟩ = ex' :=
        (exec_iff_exec_eq _ _ _ _).mp ⟨exc⟩
      rw [h_eq]
      exact h_he
    · rcases of_executeCode_someCode h_ca hbody with
        ⟨h_pre, -, -⟩ | ⟨-, ex', h_xl, h_he⟩
      · exact absurd h_pre (h_prec adr h_ca)
      · subst h_xl
        obtain ⟨exc⟩ := h_fill
        have h_eq : exec ⟨0, initSevm (msg.withBenv benv),
            initDevm (msg.withBenv benv)⟩ = ex' :=
          (exec_iff_exec_eq _ _ _ _).mp ⟨exc⟩
        rw [h_eq]
        exact h_he
  rcases hr0 : r0 with p | evm
  · rw [hr0, processMessage.settle_error] at hset; cases hset
  · rw [hr0] at key hset
    rcases h_exec with ⟨post, hx, herr⟩ | ⟨post, hx⟩ | ⟨e, post, hx, hnc⟩
    · rw [hx] at key
      have h_evm : post = evm := Except.ok.inj key
      subst h_evm
      unfold processMessage.settle at hset
      dsimp only [bind, Except.bind] at hset
      rw [if_neg (by rw [herr]; simp)] at hset
      exact Or.inl (by rw [Except.ok.inj hset, herr])
    · rw [hx] at key
      have h_evm : post.withError (some .revert) = evm := Except.ok.inj key
      subst h_evm
      unfold processMessage.settle at hset
      dsimp only [bind, Except.bind] at hset
      rw [if_pos (show (post.withError (some SettledHalt.revert)).error.isSome
        = true from rfl)] at hset
      exact Or.inr (by rw [Except.ok.inj hset]; rfl)
    · rcases e with r | _ | r | r
      · exact absurd rfl (hnc (.halt r))
      · exact absurd rfl (hnc .revert)
      · rw [hx] at key; cases key
      · rw [hx] at key; cases key

/-- **fmint's `flashLoan` frame settles: `none` or `.revert`, never a stored
halt.**

The headline at fmint's own message frame.  `Blanc/FlashSpec.lean`'s
restoration family says a frame that cannot succeed comes back with
`out.error.isSome`; `Blanc/FmintReverts.lean`'s strong form names that error
for one guard.  This says that on *this* selector, under fmint's own entry
conditions and **with no premise about the borrower**, the only two errors the
frame can come back with are no error at all and the deliberate `.revert` —
whatever bytecode answers the callback.

`h_stack` and `h_mem` do not appear: `initDevm`'s stack is `[]` and its memory
is `Mem.empty` by construction, which is a fact about frame entry rather than
a premise about it.  `h_static` is inherited as `msg.isStatic`, because
`initSevm (msg.withBenv benv)`'s `isStatic` *is* `msg.isStatic` — a premise
about fmint's caller, not about the borrower.

Not exhaustiveness, one selector, one frame and not a transaction: see this
section's banner. -/
theorem fmint_flashLoan_frame_settles {msg : Msg} {benv : Benv} {xl : Xlot}
    {out : Devm} {receiver token amount : B256} {data : Bytes}
    (h_pm : ProcessMessage msg xl (.ok out))
    (h_fill : Xlot.Filled xl)
    (h_bt : msg.benvAfterTransfer = .ok benv)
    (h_prec : ∀ adr, msg.codeAddress = some adr →
      ¬ (!msg.disablePrecompiles && decide (benv.stat.rules.isPrecomp adr)) = true)
    (h_code : some (initSevm (msg.withBenv benv)).code.toList = Prog.compile fmint)
    (h_sel : Sevm.selector (initSevm (msg.withBenv benv)) = flashLoanSelector)
    (h_static : msg.isStatic = false)
    (h_dec : Sevm.DecodesCallWithTail (initSevm (msg.withBenv benv))
      flashLoanSelector [receiver, token, amount] data)
    (h_size : 196 + ceil32 data.length < 2 ^ 256)
    (h_token : token = (initSevm (msg.withBenv benv)).currentTarget.toB256)
    (h_addr : ValidAdr receiver)
    (h_nof : B256.Nof ((Devm.getStor (initDevm (msg.withBenv benv))
      (initSevm (msg.withBenv benv)).currentTarget).get supplySlot) amount)
    (h_gas : flashLoanGas data.length
      ≤ (initDevm (msg.withBenv benv)).gasLeft) :
    out.error = none ∨ out.error = some .revert := by
  refine frame_settles_of_exec_settles h_pm h_fill h_bt h_prec ?_
  rcases flashLoan_settles_error h_code h_sel h_static h_dec h_size h_token
    h_addr h_nof rfl rfl h_gas with
    ⟨post, h_ok, h_err⟩ | h | h
  · exact Or.inl ⟨post, h_ok, h_err⟩
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)

end Fmint
end Blanc
