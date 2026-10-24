import Blanc.Lift.ExactWalkCallChild
import Blanc.Lift.HistCreate

/-!
# A zero-value `CALL` under a flat access schedule, forward

`Ninst.runCompiled_call_zero_child` (`ExactWalkCallChild.lean`) takes `CoveredFork`: it charges
the EIP-2929 warm/cold account access, resolves EIP-7702 delegation, and settles the child without
the EIP-161 touched sweep. This module states the same crossing from the rule facts a pre-Berlin
schedule gives:

* `Xinst.step_call_zero_flat`: under `rules.stateGas = none`, a flat access schedule (the call
  base `fa.call`, no warm set) and delegation disabled, a zero-value `CALL` from `St b … M X`
  spawns the frame of `callSpawnMsg` over `callSpawnParent`, running the callee's own code;
* `Ninst.runCompiled_call_zero_child_flat`: when that child's raw execution halts cleanly, the
  `CALL` is a compiled step to `callChildPost` over the child's machine with its target's EIP-161
  touch recorded (`Devm.recordTouch`, the identity when the rules do not sweep);
* `processMessage_call_of_execH`: a top-level call message settles from its raw execution;
* `checkTransaction_sender_code_emptyH`: with delegation disabled, the admitted sender has no
  code.

Nothing here mentions a contract.
-/

namespace Blanc.Lift

open Jaune

/-- **The zero-value `CALL` arm under a flat access schedule.**  With `rules.stateGas = none`, a
flat access schedule and delegation disabled, a zero-value `CALL` whose split and charge fit spawns
the callee's own code over the charged, extended parent. -/
theorem Xinst.step_call_zero_flat {sevm : Sevm} {b : Devm} {g c ii is oi os : B256}
    {S : List B256} {M : Mem} {X ext mcc mcs : Nat} {fa : FlatAccessGas}
    (hsg : sevm.benvStat.rules.stateGas = none)
    (hacc : sevm.benvStat.rules.access = .flat fa)
    (hdel : sevm.benvStat.rules.delegationEnabled = false)
    (hext : (St b S M X).extCost [⟨ii.toNat, is.toNat⟩, ⟨oi.toNat, os.toNat⟩] = ext)
    (hsplit : calculateMsgCallGas 0 g.toNat X ext fa.call = ⟨mcc, mcs⟩)
    (hgas : mcc + ext ≤ X) (hdepth : sevm.depth ≠ 0) :
    Xinst.step sevm (St b (g :: c :: 0 :: ii :: is :: oi :: os :: S) M X) .call =
      .spawn
        (Frame.ofCall (callSpawnMsg sevm
          (callSpawnParent (St b S M X) (mcc + ext) ii.toNat is.toNat oi.toNat os.toNat)
          mcs c.toAdr c.toAdr ii.toNat is.toNat (b.state.getCode c.toAdr) false))
        (.call (callSpawnParent (St b S M X) (mcc + ext) ii.toNat is.toNat oi.toNat os.toNat)
          oi.toNat os.toNat) := by
  subst hext
  simp only [Xinst.step, hsg, hacc, ForkRules.accessDelegation, hdel, Bool.false_eq_true,
    ↓reduceIte]
  rw [show (St b (g :: c :: 0 :: ii :: is :: oi :: os :: S) M X).pop =
    .ok (g, St b (c :: 0 :: ii :: is :: oi :: os :: S) M X) from rfl]
  simp only [Except.bind_ok]
  rw [show (St b (c :: 0 :: ii :: is :: oi :: os :: S) M X).popToAdr =
    .ok (c.toAdr, St b (0 :: ii :: is :: oi :: os :: S) M X) from rfl]
  simp only [Except.bind_ok]
  rw [show (St b (0 :: ii :: is :: oi :: os :: S) M X).pop =
    .ok (0, St b (ii :: is :: oi :: os :: S) M X) from rfl]
  simp only [Except.bind_ok]
  rw [show (St b (ii :: is :: oi :: os :: S) M X).popToNat =
    .ok (ii.toNat, St b (is :: oi :: os :: S) M X) from rfl]
  simp only [Except.bind_ok]
  rw [show (St b (is :: oi :: os :: S) M X).popToNat =
    .ok (is.toNat, St b (oi :: os :: S) M X) from rfl]
  simp only [Except.bind_ok]
  rw [show (St b (oi :: os :: S) M X).popToNat =
    .ok (oi.toNat, St b (os :: S) M X) from rfl]
  simp only [Except.bind_ok]
  rw [show (St b (os :: S) M X).popToNat = .ok (os.toNat, St b S M X) from rfl]
  simp only [Except.bind_ok, B256.toNat_zero, ↓reduceIte, or_true, Nat.add_zero,
    St.gasLeft, hsplit]
  rw [chargeGas_eq_ok (devm := St b S M X) hgas]
  simp only [Except.bind_ok, Except.assert, ↓reduceIte, Except.bind_ok,
    show ∀ x : B256, ¬ x < 0 from fun x => not_lt_of_ge (B256.zero_le x)]
  rw [genericCall.step_spawn hdepth]
  rfl

/-- **The zero-value `CALL` into a known child, under a flat access schedule.**  As
`Ninst.runCompiled_call_zero_child`, from `rules.stateGas = none`, a flat schedule and delegation
disabled: the child runs the callee's own code over the message `callSpawnMsg` builds, and when its
raw execution halts cleanly the parent resumes in `callChildPost` over the child's machine with
the callee's EIP-161 touch recorded. -/
theorem Ninst.runCompiled_call_zero_child_flat {sevm : Sevm} {b : Devm} {g c ii is oi os : B256}
    {S : List B256} {M : Mem} {X ext mcc mcs : Nat} {fa : FlatAccessGas} {cpost : Devm}
    (hsg : sevm.benvStat.rules.stateGas = none)
    (hacc : sevm.benvStat.rules.access = .flat fa)
    (hdel : sevm.benvStat.rules.delegationEnabled = false)
    (hext : (St b S M X).extCost [⟨ii.toNat, is.toNat⟩, ⟨oi.toNat, os.toNat⟩] = ext)
    (hsplit : calculateMsgCallGas 0 g.toNat X ext fa.call = ⟨mcc, mcs⟩)
    (hgas : mcc + ext ≤ X) (hdepth : sevm.depth ≠ 0)
    (hprec : sevm.benvStat.rules.isPrecomp c.toAdr = false) (hroom : S.length < 1024)
    (hexec : exec (initEvm (callSpawnMsg sevm
      (callSpawnParent (St b S M X) (mcc + ext) ii.toNat is.toNat oi.toNat os.toNat)
      mcs c.toAdr c.toAdr ii.toNat is.toNat (b.state.getCode c.toAdr) false)) = .ok cpost)
    (herror : cpost.error = none) :
    Ninst.RunCompiled sevm (St b (g :: c :: 0 :: ii :: is :: oi :: os :: S) M X) (.exec .call)
      (callChildPost (callSpawnParent (St b S M X) (mcc + ext) ii.toNat is.toNat oi.toNat os.toNat)
        (cpost.recordTouch sevm.benvStat.rules true c.toAdr) oi.toNat os.toNat) := by
  let p := callSpawnParent (St b S M X) (mcc + ext) ii.toNat is.toNat oi.toNat os.toNat
  let msg := callSpawnMsg sevm p mcs c.toAdr c.toAdr ii.toNat is.toNat (b.state.getCode c.toAdr)
    false
  have hbt : msg.benvAfterTransfer = .ok msg.benv := Msg.benvAfterTransfer_of_value_zero rfl
  have henter : (Frame.ofCall msg).enter = .run (initEvm (msg.withBenv msg.benv)) :=
    Frame.enter_run_of_nonprecompile hbt rfl hprec
  have hwith : msg.withBenv msg.benv = msg := rfl
  rw [hwith] at henter
  have hsettle : (Frame.ofCall msg).settle (exec (initEvm msg)) =
      .ok (cpost.recordTouch sevm.benvStat.rules true c.toAdr) := by
    rw [hexec, Frame.settle_eq_settleMsg_handleErrorWith, executeCode.handleErrorWith_ok]
    simp only [Frame.ofCall, Frame.settleMsg, processMessage.settle, herror,
      Option.isSome_none, Bool.false_eq_true, ite_false, bind, Except.bind]
    rfl
  have hres : Resume.run (.call p oi.toNat os.toNat) ((Frame.ofCall msg).settle (exec (initEvm msg))) =
      .ok (callChildPost p (cpost.recordTouch sevm.benvStat.rules true c.toAdr) oi.toNat
        os.toNat) := by
    rw [hsettle, Resume.run_call_ok (by rw [Devm.recordTouch_error, herror]; rfl)
      (by exact hroom)]
    rfl
  exact Ninst.runCompiled_exec_run
    (Xinst.step_call_zero_flat hsg hacc hdel hext hsplit hgas hdepth) henter hres

/-- **A call message settles as its raw execution, from no rule fact.**  A message whose code
address is no precompile, whose value transfer yields `benv`, and whose raw execution from that
entry halts with no frame error settles as that machine with its target's EIP-161 touch recorded
(the identity when the rules do not sweep). -/
theorem processMessage_call_of_execH {msg : Msg} {benv : Benv} {post : Devm} {t : Adr}
    (hentry : msg.benvAfterTransfer = .ok benv) (hcodeAddress : msg.codeAddress = some t)
    (hprec : msg.benv.stat.rules.isPrecomp t = false)
    (hexec : exec (initEvm (msg.withBenv benv)) = .ok post) (herror : post.error = none) :
    processMessage msg = .ok (post.recordTouch msg.benv.stat.rules true msg.currentTarget) := by
  have hstat : (msg.withBenv benv).benv.stat = msg.benv.stat := benvAfterTransfer_stat hentry
  have henter : (Frame.ofCall msg).enter = .run (initEvm (msg.withBenv benv)) :=
    Frame.enter_run_of_nonprecompile hentry hcodeAddress
      (by rw [show ((Frame.ofCall msg).inner.withBenv benv).benv.stat = msg.benv.stat from hstat]
          exact hprec)
  unfold processMessage runFrame
  rw [henter]
  dsimp only
  rw [hexec, Frame.settle_eq_settleMsg_handleErrorWith, executeCode.handleErrorWith_ok]
  simp only [Frame.ofCall, Frame.settleMsg, processMessage.settle, herror,
    Option.isSome_none, Bool.false_eq_true, ite_false, bind, Except.bind]

/-- **A historical admission check finds a sender without code.**  With delegation disabled,
`checkTransaction` admits a transaction only from an account whose code is empty. -/
theorem checkTransaction_sender_code_emptyH {benv : Benv} {bout : BlockOutput} {tx : Tx}
    {sender : Adr} {price : Nat} {hashes : List B256} {blobGas : Nat}
    (hdel : benv.stat.rules.delegationEnabled = false)
    (checked : checkTransaction benv bout tx = .ok (sender, price, hashes, blobGas)) :
    (benv.state.get sender).code.isEmpty = true := by
  unfold checkTransaction at checked
  rcases Except.bind_eq_ok checked with ⟨_, _, checked⟩
  rcases Except.bind_eq_ok checked with ⟨_, _, checked⟩
  rcases Except.bind_eq_ok checked with ⟨recovered, _, checked⟩
  rcases Except.bind_eq_ok checked with ⟨_, _, checked⟩
  rcases Except.bind_eq_ok checked with ⟨_, _, checked⟩
  rcases Except.bind_eq_ok checked with ⟨_, _, checked⟩
  rcases Except.bind_eq_ok checked with ⟨_, _, checked⟩
  rcases Except.bind_eq_ok checked with ⟨_, account, checked⟩
  have senderEq : recovered = sender := congrArg Prod.fst (Except.ok.inj checked)
  rw [senderEq, Except.mapError_eq_ok_iff] at account
  unfold checkTransactionSenderAccountFor at account
  rcases Except.bind_eq_ok account with ⟨_, _, account⟩
  rw [checkTransactionSenderCodeFor_disabled hdel] at account
  split at account
  · assumption
  · cases account

end Blanc.Lift
