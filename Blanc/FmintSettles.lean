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
and the delegation flag — because those are functions of the *world*, not of
`flashLoan`'s construction. That is the honest boundary: A5 requires the success
form's callback premises to be stated over named definitions rather than an
existential, and these are the names; the arguments they still take are the ones
a caller has to bind anyway. -/

/-- The parent state fmint's callback `CALL` suspends on. -/
def flashLoanSpawnParent (d1 : Devm) (charge dataLen : Nat) : Devm :=
  callSpawnParent d1 charge callbackArgsOffset.toNat
    (flashLoanArgsSize dataLen).toNat 0 0

/-- The message fmint's callback `CALL` builds: `onFlashLoan(...)` read out of
the parent's own memory, sent to `receiver` with no value. -/
def flashLoanSpawnMsg (sevm : Sevm) (p : Devm) (mcs : Nat) (receiver : B256)
    (dataLen : Nat) (code : ByteArray) (dp : Bool) : Msg :=
  callSpawnMsg sevm p mcs receiver.toAdr callbackArgsOffset.toNat
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
  intro b G hlogb hstorb haccb hGb
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
    simp only [Devm.logs_setMach, h_log, flashLoanMintLog]
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
  intro b₁ c₁ G₁ hw₁ hacc₁ hstor₁ hrc₁ hlog₁ hlo₁ hhi₁ hG₁
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
  intro b₂ c₂ G₂ hw₂ hacc₂ hstor₂ hrc₂ hlog₂ hlo₂ hhi₂ hG₂
  simp only [Devm.gasLeft_setMach, gasWarmAccess, gasColdSload] at hG₂ hlo₂ hhi₂
  apply Func.execSat_segment
  · intro ex hex
    func_run (3)
    exact hex
  refine Func.execSat_sstore_warm_step rfl hw₂ h_static
    (M := Mem.empty) rfl
    (by simp only [Devm.gasLeft_setMach, gasStorageSet]; omega) ?_
  intro b₃ c₃ G₃ hkey₃ hoth₃ hacc₃ hlog₃ hc₃ hG₃
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
  intro b₄ c₄ G₄ hkey₄ hoth₄ hacc₄ hlog₄ hc₄ hG₄
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
  intro b₀ G₀ h_rcv h_sup h_oth hw_r hw_s hw_mono h_log h_lo h_hi
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
  intro b G hlogb hstorb haccb hGb
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
  refine h_cont b (G₈ - 31) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [hstorb]; exact h_rcv
  · rw [hstorb]; exact h_sup
  · intro a k hk₁ hk₂; rw [hstorb]; exact h_oth a k hk₁ hk₂
  · rw [haccb]; exact hw_r
  · rw [haccb]; exact hw_s
  · intro p hp; rw [haccb]; exact hw_mono p hp
  · rw [hlogb]
    simp only [Devm.logs_setMach, h_log, flashLoanMintLog]
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
  .rev <?>
  retdataShorterThan 32 +++
  .rev <?>
  checkRetdataHead erc3156Magic 0 +++
  Ninst.iszero :::
  .rev <?>
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
    (h_flag1 : ∀ (d : Devm) (Gc : Nat), K ≤ Gc →
      Func.ExecSat (fmint.main :: fmint.aux) sevm
        (d.setMach ⟨1 :: [amount, receiver],
          flashLoanCallMem sevm amount data, Gc⟩) flashLoanFromFlag P) :
    Prog.ExecSat sevm pre fmint P := by
  refine flashLoan_execSat_call h_sel h_dec h_size h_token h_addr h_nof h_static
    h_stack h_mem (by omega) ?_
  intro b G h_rcv h_sup h_oth hw_r hw_s hw_mono h_log h_lo h_hi
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
  have h_ret := le_retained_of_calculateMsgCallGas_zero h_afford h_split
  have h_K_ret : K ≤ d1.gasLeft - (mcs + acc + 0) := by
    rw [hd1g'] at h_ret ⊢
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
    set msg' := callSpawnMsg sevm P' mcs receiver.toAdr callbackArgsOffset.toNat
      (flashLoanArgsSize data.length).toNat dcode dp with hmsg'
    have hP's : P'.stack = [amount, receiver] := by
      rw [hP', callSpawnParent_stack, hd1s']
    have hP'm : P'.memory = flashLoanCallMem sevm amount data := by
      rw [hP', callSpawnParent_memory, hd1m', Mem.extends_covered h_cov]
    have hP'g : P'.gasLeft = d1.gasLeft - (mcs + acc + 0) := by
      rw [hP', callSpawnParent_gasLeft]
    have hP'K : K ≤ P'.gasLeft := by rw [hP'g]; exact h_K_ret
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
              (P'.gasLeft + child.gasLeft) (by omega))
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
              (P'.gasLeft + child.gasLeft) (by omega))

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
    exact Func.runCompiledTo_rev_func (G := Gc - 21)
      (by simp only [Devm.gasLeft_setMach, gBase]; omega)
      (by simp only [Devm.stack_setMach, List.length_cons, List.length_nil]; omega)
  · exact hP _

/-- **The returndata-short leaf.**  The callback settled clean but answered
fewer than 32 bytes: `retdataShorterThan 32` fires before any word is read —
`retdatacopy` would abort the frame rather than fail a test — and `flashLoan`
deliberately reverts. -/
lemma execSat_retdataShort_leaf {sevm : Sevm} {d : Devm}
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
    exact Func.runCompiledTo_rev_func (G := Gc - 42)
      (by simp only [Devm.gasLeft_setMach, gBase]; omega)
      (by simp only [Devm.stack_setMach, List.length_cons, List.length_nil]; omega)
  · exact hP _

end Fmint
end Blanc
