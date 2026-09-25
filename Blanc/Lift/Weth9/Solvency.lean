import Blanc.Lift.Weth9.Frame
import Blanc.ContractAdmissionSem
import Blanc.ExecutionHistoryAdmission

/-!
# WETH9 solvency at frame, message, transaction, block and history altitude

The P1 parity rows for the pinned solc 0.4.19 WETH9 runtime, over the lifted
code semantics `weth9Sem` and the booked-sum frame contract `weth9Spec`
(`Inv = Solvent`, `Side = SumNof`), against Blanc-WETH's `Blanc/Solvent.lean`:

| Blanc-WETH (`Blanc/Solvent.lean`)       | WETH9 (this file)                              |
|-----------------------------------------|------------------------------------------------|
| `wethSpec_sound`                        | `weth9Spec_soundAdmitted`                      |
| `wethSpec_preserves`                    | `weth9Spec_preservesAdmitted`                  |
| `weth_preserves_solvent`                | `weth9_preserves_solvent`                      |
| `exec_preserves_solvent`                | `weth9_exec_preserves_solvent`                 |
| (message call, via the ladder)          | `weth9_messageCall_preserves_solvent`          |
| (transaction list, via the ladder)      | `weth9_applyTransactions_preserves_solvent`    |
| (block body, via the ladder)            | `weth9_appliedBody_preserves_solvent`          |
| `stateTransition_preserves_solvent`     | `weth9_block_preserves_solvent`                |
| `chain_preserves_solvent`               | `weth9_history_preserves_solvent`              |
| `addBlockToChain_preserves_solvent`     | not reached (see below)                        |

**The one qualification.**  Every row carries the trace-local admission
`Exec.FrameAdmitted ca weth9Entry …` (or its trace form): every WETH9 frame the
execution actually enters satisfies `AllowAdmitted`, i.e. the two allowance
slots that frame's `approve`/`transferFrom` could write are off the balance
image.  No global keccak assumption appears anywhere.  Its necessity is the O4
control `approve_collision_control` (`Approve.lean`): with an admitted
collision an approve run ends insolvent.  (`TransferFrom.lean` has no control
lemma of its own.)

**Block and chain rows.**  The admission chain's block and history rungs are
stated over retained traces (`ConfiguredBlockTrace`, `ConfiguredHistoryTrace`),
which carry the frame roots the admission talks about; Blanc-WETH's
`stateTransition`/`BlockChain.Reach` rows are over the executable functions,
where no derivation — hence no admitted root — is available.  The trace rows
are the counterparts.  `addBlockToChain_preserves_solvent` (RLP decoding and
hash checks in front of `stateTransition`) has no admission-chain rung at all,
so it is not reached.
-/

namespace Blanc.Lift.Weth9

open Jaune
open Blanc
open Blanc.Lift
open Blanc.ExecutionTrace

/-- The WETH9 entry condition: the frame's local collision premise. -/
def weth9Entry : Sevm → Devm → Prop := fun sevm _ => AllowAdmitted sevm

/-- **WETH9 frame soundness, trace-admitted.**  Counterpart of `wethSpec_sound`. -/
theorem weth9Spec_soundAdmitted (ca : Adr) : weth9Spec.SoundAdmitted ca weth9Entry := by
  intro sevm pre post hfork execution hrun hca admitted ih _ hpre
  subst hca
  have hin := lift_sound_in cert_check hrun.1 hfork execution
  exact frame_post_in (R := ⟨0, sevm, pre, .ok post, execution⟩) hfork hin
    (admitted.root rfl) admitted ih hpre

/-- **WETH9 frame preservation, trace-admitted.**  Counterpart of
`wethSpec_preserves`; the form the message, transaction and block rungs
consume. -/
theorem weth9Spec_preservesAdmitted (ca : Adr) :
    weth9Spec.PreservesAdmitted ca weth9Entry :=
  weth9Spec.preserves_inv_admitted ca weth9Entry (weth9Spec_soundAdmitted ca)

/-- Counterpart of `weth_preserves_solvent`: every successful execution whose
entered WETH9 frames are admitted takes the frame precondition to the frame
postcondition. -/
theorem weth9_preserves_solvent (ca : Adr) (sevm : Sevm) (pre post : Devm)
    (hfork : CoveredFork sevm.benvStat.fork)
    (execution : Exec 0 sevm pre (.ok post))
    (admitted : Exec.FrameAdmitted ca weth9Entry execution)
    (hcode : sevm.currentTarget = ca → some sevm.code.toList = weth9Sem.image)
    (hwf : sevm.currentTarget = ca → Mem.Wf pre.memory)
    (hpre : weth9Spec.Pre ca sevm pre) : weth9Spec.Post ca sevm post :=
  weth9Spec_preservesAdmitted ca sevm pre post hfork execution admitted hcode hwf hpre

/-- Counterpart of `exec_preserves_solvent`, for the total executable `exec`.
The admission is stated for the execution's derivation (unique up to
`Exec.unique`). -/
theorem weth9_exec_preserves_solvent (ca : Adr) (sevm : Sevm) (pre post : Devm)
    (hfork : CoveredFork sevm.benvStat.fork)
    (hrun : exec ⟨0, sevm, pre⟩ = .ok post)
    (admitted : ∀ execution : Exec 0 sevm pre (.ok post),
      Exec.FrameAdmitted ca weth9Entry execution)
    (hcode : sevm.currentTarget = ca → some sevm.code.toList = weth9Sem.image)
    (hwf : sevm.currentTarget = ca → Mem.Wf pre.memory)
    (hpre : weth9Spec.Pre ca sevm pre) : weth9Spec.Post ca sevm post := by
  obtain ⟨execution⟩ := (exec_iff_exec_eq 0 sevm pre (.ok post)).mpr hrun
  exact weth9_preserves_solvent ca sevm pre post hfork execution (admitted execution)
    hcode hwf hpre

/-- Message-call rung: an admitted message call preserves the WETH9 state
invariant (and deletes no WETH9 account). -/
theorem weth9_messageCall_preserves_solvent {ca : Adr} {msg : Msg} {state : State}
    {out : MsgCallOutput} (trace : MessageCallTrace msg state out)
    (hfork : CoveredFork msg.benv.stat.fork)
    (admitted : trace.FrameAdmitted ca weth9Entry)
    (ready : weth9Spec.MsgInv ca msg) :
    weth9Spec.StateInv ca state ∧
      (∀ address ∈ out.accountsToDelete.toList, address ≠ ca) :=
  trace.stateInv_admitted_sem (weth9Spec_preservesAdmitted ca) hfork admitted ready

/-- Transaction-list rung. -/
theorem weth9_applyTransactions_preserves_solvent {ca : Adr}
    {txs : List (Nat × Tx)} {benv finalBenv : Benv} {bout finalBout : BlockOutput}
    (trace : ApplyTransactionsTrace txs benv bout finalBenv finalBout)
    (hfork : CoveredFork benv.stat.fork)
    (admitted : trace.FrameAdmitted ca weth9Entry)
    (sumNof : sum benv.state.bal < 2 ^ 256)
    (inv : weth9Spec.BenvInv ca benv) :
    weth9Spec.BenvInv ca finalBenv :=
  trace.benvInv_admitted_sem (weth9Spec_preservesAdmitted ca) hfork admitted sumNof inv

/-- Block-body rung: system messages, transactions, withdrawals and requests. -/
theorem weth9_appliedBody_preserves_solvent {ca : Adr}
    {benv : Benv} {txs : List (Bytes ⊕ Tx)} {wds : List Withdrawal}
    {state : State} {bout : BlockOutput}
    (trace : AppliedBodyTrace benv txs wds state bout)
    (hfork : CoveredFork benv.stat.fork)
    (admitted : trace.FrameAdmitted ca weth9Entry)
    (bound : sum benv.state.bal + wdsum wds < 2 ^ 256)
    (inv : weth9Spec.BenvInv ca benv) :
    weth9Spec.StateInv ca state :=
  trace.stateInv_admitted_sem (weth9Spec_preservesAdmitted ca) hfork admitted bound inv

/-- Block rung, counterpart of `stateTransition_preserves_solvent`: one
configured block whose entered WETH9 frames are admitted preserves the WETH9
state invariant. -/
theorem weth9_block_preserves_solvent {ca : Adr} {cfg : ChainConfig}
    {pre post : BlockChain} (trace : ConfiguredBlockTrace cfg pre post)
    (admitted : trace.FrameAdmitted ca weth9Entry)
    (inv : weth9Spec.StateInv ca pre.state) :
    weth9Spec.StateInv ca post.state :=
  trace.stateInv_admitted_sem (weth9Spec_preservesAdmitted ca) admitted inv

/-- History rung, counterpart of `chain_preserves_solvent`: a configured
history of blocks whose entered WETH9 frames are admitted preserves the WETH9
state invariant. -/
theorem weth9_history_preserves_solvent {ca : Adr} {cfg : ChainConfig}
    {checkpoint future : BlockChain}
    (trace : ConfiguredHistoryTrace cfg checkpoint future)
    (admitted : trace.FrameAdmitted ca weth9Entry)
    (inv : weth9Spec.StateInv ca checkpoint.state) :
    weth9Spec.StateInv ca future.state :=
  trace.stateInv_admitted_sem (weth9Spec_preservesAdmitted ca) admitted inv

/-- The state invariant is WETH9 solvency, the side condition, and the pinned
code. -/
theorem weth9Spec_stateInv_iff {ca : Adr} {w : State} :
    weth9Spec.StateInv ca w ↔
      (some (w.getCode ca).toList = some code.toList ∧ SumNof w.bal ∧
        Solvent (w.getStor ca) 0 (w.bal ca)) :=
  ⟨fun h => ⟨h.code, h.side, h.inv⟩, fun h => ⟨h.1, h.2.1, h.2.2⟩⟩

end Blanc.Lift.Weth9
