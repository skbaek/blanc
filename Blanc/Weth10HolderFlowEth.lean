import Blanc.ExecutionMessageEffects
import Blanc.ExecutionTransactionEffects
import Blanc.ExecutionBodyEffects
import Blanc.Weth10HolderFlowAuthenticity

/-!
Execution-side ETH accounting for the committed WETH10 flow ledger.

The primitive relation below is an inequality, not an input ledger predicate:
it is derived from concrete state transfers and then composed through the
retained trace hierarchy.  Ordinary mints count on the left and actual
redemptions on the right.  Unclassified inward ETH is permitted as slack;
there is deliberately no constructor for an unclassified outward transfer
from the WETH10 account.
-/

namespace Blanc

open Jaune

namespace Weth10

/-- ETH entering WETH10 and represented by an ordinary mint action. -/
def FlowAtom.ethMint : FlowAtom → Nat
  | .ordinaryMint _ _ amount => amount
  | _ => 0

/-- ETH delivered by an actual redemption action. -/
def FlowAtom.ethRedemption : FlowAtom → Nat
  | .redemption _ _ _ amount => amount
  | _ => 0

def flowActionsEthMint (actions : List FlowAction) : Nat :=
  (actions.map fun action => action.atom.ethMint).sum

def flowActionsEthRedemption (actions : List FlowAction) : Nat :=
  (actions.map fun action => action.atom.ethRedemption).sum

/-- The ETH-side inequality needed by committed credit no-wrap. -/
def EthBound (ca : Adr) (pre post : State)
    (actions : List FlowAction) : Prop :=
  (pre.bal ca).toNat + flowActionsEthMint actions ≤
    (post.bal ca).toNat + flowActionsEthRedemption actions

theorem flowActionsEthMint_append (left right : List FlowAction) :
    flowActionsEthMint (left ++ right) =
      flowActionsEthMint left + flowActionsEthMint right := by
  simp [flowActionsEthMint]

theorem flowActionsEthRedemption_append (left right : List FlowAction) :
    flowActionsEthRedemption (left ++ right) =
      flowActionsEthRedemption left + flowActionsEthRedemption right := by
  simp [flowActionsEthRedemption]

/-! ## Frame-entry/body partition

An ordinary mint is funded by the message value transfer that precedes the
callee's raw `Exec`; counting it again in the callee body would double-count
that ETH.  Every other root action belongs to the body.  Proper-descendant
actions always belong to the enclosing body, because their own entry transfers
occur during that execution. -/

def FlowAction.entryEthActions (action : FlowAction) : List FlowAction :=
  match action.atom with
  | .ordinaryMint .. => [action]
  | _ => []

def FlowAction.bodyEthActions (action : FlowAction) : List FlowAction :=
  match action.atom with
  | .ordinaryMint .. => []
  | _ => [action]

theorem FlowAction.entryEthActions_append_bodyEthActions
    (action : FlowAction) :
    action.entryEthActions ++ action.bodyEthActions = [action] := by
  rcases action with
    ⟨atom, credit, debit, actualCaller, currentTarget, codeAddress, depth⟩
  cases atom <;> rfl

def flowActionEntryEthActions : Option FlowAction → List FlowAction
  | none => []
  | some action => action.entryEthActions

def flowActionBodyEthActions : Option FlowAction → List FlowAction
  | none => []
  | some action => action.bodyEthActions

theorem flowActionEntryEthActions_append_bodyEthActions
    (action : Option FlowAction) :
    flowActionEntryEthActions action ++ flowActionBodyEthActions action =
      action.toList := by
  cases action with
  | none => rfl
  | some action => exact action.entryEthActions_append_bodyEthActions

theorem flowActionsEthRedemption_entryEthActions_eq_zero
    (action : Option FlowAction) :
    flowActionsEthRedemption (flowActionEntryEthActions action) = 0 := by
  cases action with
  | none => rfl
  | some action =>
      rcases action with
        ⟨atom, credit, debit, actualCaller, currentTarget, codeAddress, depth⟩
      cases atom <;> rfl

private theorem FlowAtom.ethMint_le_value_of_primaryFlowAtom_eq_some
    {e : Sevm} {atom : FlowAtom}
    (h : primaryFlowAtom e = some atom) :
    atom.ethMint ≤ e.value.toNat := by
  unfold primaryFlowAtom at h
  split at h
  · cases Option.some.inj h
    rfl
  · split at h
    · cases Option.some.inj h
      rfl
    · split at h
      · cases Option.some.inj h
        rfl
      · split at h
        · dsimp only at h
          split at h <;> cases Option.some.inj h <;>
            simp [FlowAtom.ethMint]
        · split at h
          · dsimp only at h
            split at h <;> cases Option.some.inj h <;>
              simp [FlowAtom.ethMint]
          · split at h
            · cases Option.some.inj h
              simp [FlowAtom.ethMint]
            · split at h
              · cases Option.some.inj h
                simp [FlowAtom.ethMint]
              · split at h
                · cases Option.some.inj h
                  simp [FlowAtom.ethMint]
                · split at h
                  · cases Option.some.inj h
                    simp [FlowAtom.ethMint]
                  · simp at h

theorem Exec.Frame.flowActionsEthMint_entryEthActions_le_value
    {dp : DeployParams} {ca : Adr} (frame : Exec.Frame) :
    flowActionsEthMint
        (flowActionEntryEthActions
          (Blanc.Weth10.Exec.Frame.flowAction? dp ca frame)) ≤
      frame.sevm.value.toNat := by
  unfold Exec.Frame.flowAction?
  split
  · cases hprimary : primaryFlowAtom frame.sevm with
    | none =>
        simp [flowActionEntryEthActions, flowActionsEthMint]
    | some atom =>
        have hle :=
          FlowAtom.ethMint_le_value_of_primaryFlowAtom_eq_some hprimary
        cases atom <;>
          simp_all [flowActionEntryEthActions,
            FlowAction.entryEthActions, flowActionsEthMint,
            FlowAtom.ethMint]
  · simp [flowActionEntryEthActions, flowActionsEthMint]

/-- The root ordinary-mint action, if any.  This is the part funded by the
actual value transfer into the entered frame. -/
def Exec.entryEthActions (dp : DeployParams) (ca : Adr)
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out)
    (hcommit : Execution.commits out = true) : List FlowAction :=
  flowActionEntryEthActions
    (Exec.Frame.flowAction? dp ca (Exec.Frame.ofRun run hcommit))

/-- Root non-mint action followed by every proper committed descendant. -/
def Exec.bodyEthActions (dp : DeployParams) (ca : Adr)
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out)
    (hcommit : Execution.commits out = true) : List FlowAction :=
  flowActionBodyEthActions
      (Exec.Frame.flowAction? dp ca (Exec.Frame.ofRun run hcommit)) ++
    (Exec.descendantFrames run).filterMap
      (Exec.Frame.flowAction? dp ca)

/-- Exact partition of a committed frame's public action traversal into its
message-entry-funded root mint and its execution-body actions. -/
theorem Exec.flowActions_eq_entry_append_body
    {dp : DeployParams} {ca : Adr}
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out)
    (hcommit : Execution.commits out = true) :
    Exec.flowActions dp ca run =
      Exec.entryEthActions dp ca run hcommit ++
        Exec.bodyEthActions dp ca run hcommit := by
  unfold Exec.flowActions Exec.committedFrames Exec.entryEthActions
    Exec.bodyEthActions
  simp only [dif_pos hcommit, List.filterMap_cons]
  generalize hroot :
      Exec.Frame.flowAction? dp ca (Exec.Frame.ofRun run hcommit) = root
  cases root with
  | none => rfl
  | some action =>
      rcases action with
        ⟨atom, credit, debit, actualCaller, currentTarget, codeAddress, depth⟩
      cases atom <;> rfl

theorem EthBound.refl (ca : Adr) (state : State) :
    EthBound ca state state [] := by
  simp [EthBound, flowActionsEthMint, flowActionsEthRedemption]

theorem EthBound.trans
    {ca : Adr} {first middle last : State}
    {left right : List FlowAction}
    (hleft : EthBound ca first middle left)
    (hright : EthBound ca middle last right) :
    EthBound ca first last (left ++ right) := by
  unfold EthBound at hleft hright ⊢
  rw [flowActionsEthMint_append, flowActionsEthRedemption_append]
  omega

/-! ## Concrete, non-circular ETH movements -/

/-- One concrete ETH movement contributing zero, one, or two classified
actions.  Every value-transfer constructor retains the actual successful
`subBal` and `addBal` state.  The global sum bound prevents recipient wrap.
The self-call constructor pairs the enclosing redemption with the nested
ordinary mint, which is the only sound local treatment of WETH calling itself
with value. -/
inductive EthStep (ca : Adr) : State → List FlowAction → State → Prop
  | silent {pre post}
      (balance_eq : post.bal ca = pre.bal ca) :
      EthStep ca pre [] post
  | unrelatedTransfer {pre debit post caller target value}
      (caller_ne : caller ≠ ca) (target_ne : target ≠ ca)
      (sub : pre.subBal caller value = some debit)
      (post_eq : post = debit.addBal target value) :
      EthStep ca pre [] post
  | unclassifiedInward {pre debit post caller value}
      (caller_ne : caller ≠ ca)
      (sub : pre.subBal caller value = some debit)
      (post_eq : post = debit.addBal ca value)
      (sum_nof : sum pre.bal < 2 ^ 256) :
      EthStep ca pre [] post
  | ordinaryMint {pre debit post caller value action rawRecipient recipient}
      (caller_ne : caller ≠ ca)
      (sub : pre.subBal caller value = some debit)
      (post_eq : post = debit.addBal ca value)
      (sum_nof : sum pre.bal < 2 ^ 256)
      (atom_eq : action.atom =
        .ordinaryMint rawRecipient recipient value.toNat) :
      EthStep ca pre [action] post
  | redemption {pre debit post target value action rawSource source ethRecipient}
      (target_ne : target ≠ ca)
      (sub : pre.subBal ca value = some debit)
      (post_eq : post = debit.addBal target value)
      (atom_eq : action.atom =
        .redemption rawSource source ethRecipient value.toNat) :
      EthStep ca pre [action] post
  | selfRedemptionMint {pre debit post value redemption mint
      rawSource source ethRecipient rawRecipient recipient}
      (sub : pre.subBal ca value = some debit)
      (post_eq : post = debit.addBal ca value)
      (redemption_eq : redemption.atom =
        .redemption rawSource source ethRecipient value.toNat)
      (mint_eq : mint.atom =
        .ordinaryMint rawRecipient recipient value.toNat) :
      EthStep ca pre [redemption, mint] post
  | externalCredit {pre post recipient value}
      (post_eq : post = pre.addBal recipient value)
      (sum_nof : sum pre.bal + value.toNat < 2 ^ 256) :
      EthStep ca pre [] post

theorem EthStep.bound
    {ca : Adr} {pre post : State} {actions : List FlowAction}
    (step : EthStep ca pre actions post) :
    EthBound ca pre post actions := by
  cases step with
  | silent balance_eq =>
      simp [EthBound, flowActionsEthMint, flowActionsEthRedemption,
        balance_eq]
  | unrelatedTransfer caller_ne target_ne sub post_eq =>
      subst post
      have hbal := of_transfer_bal_other sub caller_ne target_ne
      simp [EthBound, flowActionsEthMint, flowActionsEthRedemption, hbal]
  | unclassifiedInward caller_ne sub post_eq sum_nof =>
      subst post
      have hbal := of_transfer_bal_target sub caller_ne sum_nof
      simp [EthBound, flowActionsEthMint, flowActionsEthRedemption]
      omega
  | ordinaryMint caller_ne sub post_eq sum_nof atom_eq =>
      subst post
      have hbal := of_transfer_bal_target sub caller_ne sum_nof
      simp [EthBound, flowActionsEthMint, flowActionsEthRedemption,
        atom_eq, FlowAtom.ethMint, FlowAtom.ethRedemption, hbal]
  | redemption target_ne sub post_eq atom_eq =>
      rename_i debit target value action rawSource source ethRecipient
      subst post
      rcases State.of_subBal sub with ⟨hle, rfl⟩
      have htarget :
          ((pre.setBal ca (pre.bal ca - value)).addBal target value).bal ca =
            pre.bal ca - value := by
        simp only [State.addBal, State.bal,
          State.setBal_get_ne target_ne, State.setBal_get_self]
        rfl
      have hnat := B256.toNat_sub_eq_of_le (pre.bal ca) value hle
      simp [EthBound, flowActionsEthMint, flowActionsEthRedemption,
        atom_eq, FlowAtom.ethMint, FlowAtom.ethRedemption, htarget]
      omega
  | selfRedemptionMint sub post_eq redemption_eq mint_eq =>
      subst post
      rcases of_state_transfer_fields (callee := ca) sub with
        ⟨_, _, _, hself, _⟩
      have hbal := hself rfl
      simp [EthBound, flowActionsEthMint, flowActionsEthRedemption,
        redemption_eq, mint_eq, FlowAtom.ethMint,
        FlowAtom.ethRedemption, hbal]
  | externalCredit post_eq sum_nof =>
      rename_i recipient value
      subst post
      by_cases hrecipient : recipient = ca
      · subst recipient
        have hnof : B256.Nof (pre.bal ca) value := by
          unfold B256.Nof
          have hle : (pre.bal ca).toNat ≤ sum pre.bal := le_sum
          omega
        have hbal : (pre.addBal ca value).bal ca = pre.bal ca + value := by
          show ((pre.setBal ca (pre.bal ca + value)).get ca).bal = _
          rw [State.setBal_get_self]
          rfl
        simp [EthBound, flowActionsEthMint, flowActionsEthRedemption,
          hbal, B256.toNat_add_eq_of_nof _ _ hnof]
      · have hbal : (pre.addBal recipient value).bal ca = pre.bal ca := by
          show ((pre.setBal recipient _).get ca).bal = _
          rw [State.setBal_get_ne hrecipient]
          rfl
        simp [EthBound, flowActionsEthMint, flowActionsEthRedemption, hbal]

/-- A contiguous sequence of concrete ETH movements. -/
inductive EthChain (ca : Adr) :
    List FlowAction → State → State → Prop
  | nil (state : State) : EthChain ca [] state state
  | cons {head tail first middle last}
      (step : EthStep ca first head middle)
      (rest : EthChain ca tail middle last) :
      EthChain ca (head ++ tail) first last

theorem EthChain.bound
    {ca : Adr} {actions : List FlowAction} {pre post : State}
    (chain : EthChain ca actions pre post) :
    EthBound ca pre post actions := by
  induction chain with
  | nil state => exact EthBound.refl ca state
  | cons step rest ih => exact step.bound.trans ih

/-! ## Message-entry constructors -/

theorem EthStep.of_benvAfterTransfer_unrelated
    {ca : Adr} {msg : Msg} {post : Benv}
    (htransfer : msg.shouldTransferValue = true)
    (hcaller : msg.caller ≠ ca) (htarget : msg.currentTarget ≠ ca)
    (hrun : msg.benvAfterTransfer = .ok post) :
    EthStep ca msg.benv.state [] post.state := by
  rcases of_benvAfterTransfer htransfer hrun with ⟨debit, hsub, rfl⟩
  exact .unrelatedTransfer hcaller htarget hsub rfl

theorem EthStep.of_benvAfterTransfer_unclassifiedInward
    {ca : Adr} {msg : Msg} {post : Benv}
    (htransfer : msg.shouldTransferValue = true)
    (hcaller : msg.caller ≠ ca) (htarget : msg.currentTarget = ca)
    (hsum : sum msg.benv.state.bal < 2 ^ 256)
    (hrun : msg.benvAfterTransfer = .ok post) :
    EthStep ca msg.benv.state [] post.state := by
  rcases of_benvAfterTransfer htransfer hrun with ⟨debit, hsub, rfl⟩
  subst ca
  exact .unclassifiedInward hcaller hsub rfl hsum

theorem EthStep.of_benvAfterTransfer_ordinaryMint
    {ca : Adr} {msg : Msg} {post : Benv} {action : FlowAction}
    {rawRecipient : B256} {recipient : Adr}
    (htransfer : msg.shouldTransferValue = true)
    (hcaller : msg.caller ≠ ca) (htarget : msg.currentTarget = ca)
    (hsum : sum msg.benv.state.bal < 2 ^ 256)
    (hatom : action.atom =
      .ordinaryMint rawRecipient recipient msg.value.toNat)
    (hrun : msg.benvAfterTransfer = .ok post) :
    EthStep ca msg.benv.state [action] post.state := by
  rcases of_benvAfterTransfer htransfer hrun with ⟨debit, hsub, rfl⟩
  subst ca
  exact .ordinaryMint hcaller hsub rfl hsum hatom

theorem EthStep.of_benvAfterTransfer_redemption
    {ca : Adr} {msg : Msg} {post : Benv} {action : FlowAction}
    {rawSource : B256} {source ethRecipient : Adr}
    (htransfer : msg.shouldTransferValue = true)
    (hcaller : msg.caller = ca) (htarget : msg.currentTarget ≠ ca)
    (hatom : action.atom =
      .redemption rawSource source ethRecipient msg.value.toNat)
    (hrun : msg.benvAfterTransfer = .ok post) :
    EthStep ca msg.benv.state [action] post.state := by
  rcases of_benvAfterTransfer htransfer hrun with ⟨debit, hsub, rfl⟩
  subst ca
  exact .redemption htarget hsub rfl hatom

theorem EthStep.of_benvAfterTransfer_selfRedemptionMint
    {ca : Adr} {msg : Msg} {post : Benv}
    {redemption mint : FlowAction}
    {rawSource : B256} {source ethRecipient : Adr}
    {rawRecipient : B256} {recipient : Adr}
    (htransfer : msg.shouldTransferValue = true)
    (hcaller : msg.caller = ca) (htarget : msg.currentTarget = ca)
    (hredemption : redemption.atom =
      .redemption rawSource source ethRecipient msg.value.toNat)
    (hmint : mint.atom =
      .ordinaryMint rawRecipient recipient msg.value.toNat)
    (hrun : msg.benvAfterTransfer = .ok post) :
    EthStep ca msg.benv.state [redemption, mint] post.state := by
  rcases of_benvAfterTransfer htransfer hrun with ⟨debit, hsub, rfl⟩
  subst ca
  exact .selfRedemptionMint hsub (by rw [htarget]; rfl)
    hredemption hmint

theorem EthStep.of_benvAfterTransfer_noTransfer
    {ca : Adr} {msg : Msg} {post : Benv}
    (htransfer : msg.shouldTransferValue = false)
    (hrun : msg.benvAfterTransfer = .ok post) :
    EthStep ca msg.benv.state [] post.state := by
  unfold Msg.benvAfterTransfer at hrun
  rw [htransfer] at hrun
  cases hrun
  exact .silent rfl

/-- Contract-neutral entry accounting for the root action of an interpreted
frame.  A selected ordinary mint is bounded by the frame's actual call value;
the full `MsgInv` boundary later supplies `hcaller`, `hval0`, and `hsum`.
No compiled body theorem is used here. -/
theorem Exec.entryEthBound
    {dp : DeployParams} {ca : Adr} {msg : Msg} {benv : Benv}
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out)
    (htransfer : msg.benvAfterTransfer = .ok benv)
    (hinit : (⟨pc, sevm, pre⟩ : Evm) =
      initEvm (msg.withBenv benv))
    (hcommit : Execution.commits out = true)
    (hcaller : msg.shouldTransferValue = true → msg.caller ≠ ca)
    (hval0 : msg.shouldTransferValue = false →
      msg.currentTarget = ca → msg.value = 0)
    (hsum : sum msg.benv.state.bal < 2 ^ 256) :
    EthBound ca msg.benv.state pre.state
      (Exec.entryEthActions dp ca run hcommit) := by
  have hpc := congrArg Evm.pc hinit
  have hsevm := congrArg Evm.sta hinit
  have hpre := congrArg Evm.dyna hinit
  dsimp only [initEvm] at hpc hsevm hpre
  subst pc
  subst sevm
  subst pre
  let root : Exec.Frame := Exec.Frame.ofRun run hcommit
  have hmint :
      flowActionsEthMint
          (Exec.entryEthActions dp ca run hcommit) ≤ msg.value.toNat := by
    have h := Blanc.Weth10.Exec.Frame.flowActionsEthMint_entryEthActions_le_value
      (dp := dp) (ca := ca) root
    simpa [root, Exec.entryEthActions, Exec.Frame.ofRun,
      initSevm, Msg.withBenv] using h
  have hredeem :
      flowActionsEthRedemption
          (Exec.entryEthActions dp ca run hcommit) = 0 :=
    flowActionsEthRedemption_entryEthActions_eq_zero _
  by_cases hstv : msg.shouldTransferValue = true
  · rcases of_benvAfterTransfer hstv htransfer with
      ⟨debit, hsub, hbenv⟩
    by_cases htarget : msg.currentTarget = ca
    · have hbal := of_transfer_bal_target hsub (hcaller hstv) hsum
      have hbenvState :
          benv.state = debit.addBal msg.currentTarget msg.value := by
        rw [hbenv]
        rfl
      have hbenvBal :
          (benv.state.bal ca).toNat =
            (msg.benv.state.bal ca).toNat + msg.value.toNat := by
        rw [hbenvState, htarget]
        exact hbal
      unfold EthBound
      rw [hredeem, Nat.add_zero]
      change (msg.benv.state.bal ca).toNat +
          flowActionsEthMint (Exec.entryEthActions dp ca run hcommit) ≤
        (benv.state.bal ca).toNat
      rw [hbenvBal]
      omega
    · have hbal := of_transfer_bal_other hsub (hcaller hstv) htarget
      have hentry : Exec.entryEthActions dp ca run hcommit = [] := by
        simp [Exec.entryEthActions, Exec.Frame.flowAction?,
          Exec.Frame.exactInvocation, Exec.Frame.ofRun, exactInvocation,
          flowActionEntryEthActions, initSevm, Msg.withBenv, htarget]
      have hbenvState :
          benv.state = debit.addBal msg.currentTarget msg.value := by
        rw [hbenv]
        rfl
      have hbenvBal : benv.state.bal ca = msg.benv.state.bal ca := by
        rw [hbenvState]
        exact hbal
      unfold EthBound
      rw [hentry]
      simp only [flowActionsEthMint, List.map_nil, List.sum_nil,
        flowActionsEthRedemption, Nat.add_zero]
      change (msg.benv.state.bal ca).toNat ≤ (benv.state.bal ca).toNat
      rw [hbenvBal]
  · have hbenv := of_benvAfterTransfer_no hstv htransfer
    subst benv
    by_cases htarget : msg.currentTarget = ca
    · have hfalse : msg.shouldTransferValue = false := by
        cases hbool : msg.shouldTransferValue with
        | false => rfl
        | true => exact (hstv hbool).elim
      have hvalue := hval0 hfalse htarget
      have hvalueNat : msg.value.toNat = 0 := by
        rw [hvalue]
        rfl
      rw [hvalueNat] at hmint
      have hmintZero :
          flowActionsEthMint
              (Exec.entryEthActions dp ca run hcommit) = 0 :=
        Nat.eq_zero_of_le_zero hmint
      unfold EthBound
      rw [hredeem, Nat.add_zero]
      change (msg.benv.state.bal ca).toNat +
          flowActionsEthMint (Exec.entryEthActions dp ca run hcommit) ≤
        (msg.benv.state.bal ca).toNat
      rw [hmintZero]
      simp
    · have hentry : Exec.entryEthActions dp ca run hcommit = [] := by
        simp [Exec.entryEthActions, Exec.Frame.flowAction?,
          Exec.Frame.exactInvocation, Exec.Frame.ofRun, exactInvocation,
          flowActionEntryEthActions, initSevm, Msg.withBenv, htarget]
      rw [hentry]
      exact EthBound.refl ca msg.benv.state

/-- Entry accounting for the successful value child of a concrete WETH10
redemption.  When the recipient is foreign, the parent redemption pays for
the debit.  When WETH calls itself, the same parent redemption also pays for
the child's possible root ordinary mint; the actual self-transfer leaves the
contract ETH balance unchanged. -/
theorem Exec.redemptionEntryEthBound
    {dp : DeployParams} {ca : Adr} {msg : Msg} {benv : Benv}
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out)
    (htransfer : msg.benvAfterTransfer = .ok benv)
    (hinit : (⟨pc, sevm, pre⟩ : Evm) =
      initEvm (msg.withBenv benv))
    (hcommit : Execution.commits out = true)
    (hstv : msg.shouldTransferValue = true)
    (hcaller : msg.caller = ca)
    {action : FlowAction} {rawSource : B256}
    {source ethRecipient : Adr}
    (hatom : action.atom =
      .redemption rawSource source ethRecipient msg.value.toNat) :
    EthBound ca msg.benv.state pre.state
      (action :: Exec.entryEthActions dp ca run hcommit) := by
  have hpc := congrArg Evm.pc hinit
  have hsevm := congrArg Evm.sta hinit
  have hpre := congrArg Evm.dyna hinit
  dsimp only [initEvm] at hpc hsevm hpre
  subst pc
  subst sevm
  subst pre
  let root : Exec.Frame := Exec.Frame.ofRun run hcommit
  have hmint :
      flowActionsEthMint
          (Exec.entryEthActions dp ca run hcommit) ≤ msg.value.toNat := by
    have h := Blanc.Weth10.Exec.Frame.flowActionsEthMint_entryEthActions_le_value
      (dp := dp) (ca := ca) root
    simpa [root, Exec.entryEthActions, Exec.Frame.ofRun,
      initSevm, Msg.withBenv] using h
  have hredeem :
      flowActionsEthRedemption
          (Exec.entryEthActions dp ca run hcommit) = 0 :=
    flowActionsEthRedemption_entryEthActions_eq_zero _
  by_cases htarget : msg.currentTarget = ca
  · rcases of_benvAfterTransfer hstv htransfer with
      ⟨debit, hsub, hbenv⟩
    have hbalTransfer :
        (debit.addBal msg.currentTarget msg.value).bal ca =
          msg.benv.state.bal ca := by
      rcases of_state_transfer_fields
          (callee := msg.currentTarget) hsub with
        ⟨_, _, _, hself, _⟩
      rw [← hcaller]
      exact hself (htarget.trans hcaller.symm)
    have hbenvBal : benv.state.bal ca = msg.benv.state.bal ca := by
      rw [hbenv]
      exact hbalTransfer
    unfold EthBound
    rw [flowActionsEthMint, flowActionsEthRedemption]
    simp only [List.map_cons, List.sum_cons, hatom,
      FlowAtom.ethMint, FlowAtom.ethRedemption]
    change (msg.benv.state.bal ca).toNat +
        (0 + flowActionsEthMint
          (Exec.entryEthActions dp ca run hcommit)) ≤
      (benv.state.bal ca).toNat +
        (msg.value.toNat + flowActionsEthRedemption
          (Exec.entryEthActions dp ca run hcommit))
    rw [hbenvBal, hredeem]
    omega
  · have hentry : Exec.entryEthActions dp ca run hcommit = [] := by
      simp [Exec.entryEthActions, Exec.Frame.flowAction?,
        Exec.Frame.exactInvocation, Exec.Frame.ofRun, exactInvocation,
        flowActionEntryEthActions, initSevm, Msg.withBenv, htarget]
    rw [hentry]
    exact (EthStep.of_benvAfterTransfer_redemption hstv hcaller
      htarget hatom htransfer).bound

/-! ## Actual successful value-call evidence -/

/-- The committed child behind a value `CALL` whose success flag passed the
WETH10 guard.  This is stronger than a log or endpoint observation: it retains
the exact child message and its recursive execution trace. -/
structure AcceptedValueCallTrace
    (e : Sevm) (target value : B256)
    (callPre guardPost : Devm) : Type where
  gasWord : B256
  callPost : Devm
  parent : Devm
  child : Devm
  slot : Xlot
  pc : Nat
  step : Ninst.StepRun pc e callPre Ninst.call slot (.ok callPost)
  depth_pos : 0 < e.depth
  delegated : Bool
  code : ByteArray
  availableGas : Nat
  parent_state : parent.state = callPre.state
  delegation_resolution :
    ((getDelegatedCodeAddress (callPre.getCode target.toAdr) = none ∧
        code = callPre.getCode target.toAdr ∧ delegated = false) ∨
      (∃ delegatedTarget,
        getDelegatedCodeAddress (callPre.getCode target.toAdr) =
          some delegatedTarget ∧
        code = callPre.getCode delegatedTarget ∧ delegated = true))
  childMessage : Msg
  childMessage_eq : childMessage =
    callMsg e parent
      (min gasWord.toNat (except64th availableGas) +
        (if value.toNat = 0 then 0 else gCallStipend))
      value e.currentTarget target.toAdr
      ((getDelegatedCodeAddress (callPre.getCode target.toAdr)).getD
        target.toAdr)
      true false
      ((callPre.memory.read (0 : B256).toNat (0 : B256).toNat).1)
      code delegated
  retained : ProcessMessageTrace childMessage (.ok child)
  child_clean : child.error.isSome = false
  guard_state : guardPost.state = child.state

theorem exists_acceptedValueCallTrace
    {e : Sevm} {target value : B256} {callPre guardPost : Devm}
    (accepted : AcceptedValueCall e target value callPre guardPost) :
    Nonempty (AcceptedValueCallTrace e target value callPre guardPost) := by
  rcases accepted with
    ⟨g, callPost, testPost, hstack, hcall, hiszero, hpop⟩
  rcases of_run_call_val_with_depth_frame hstack hcall with
      hfailed | hsuccess
  · exfalso
    have htest := prefix_of_iszero hiszero hfailed.1
    have hpopStack := hpop.stack
    simp only [Stack.Pop, Split, List.nil_append,
      List.cons_append] at hpopStack
    rw [hpopStack] at htest
    have hzero : ((0 : B256) =? 0) = 0 :=
      pref_head_unique htest (pref_append [(0 : B256)] guardPost.stack)
    rw [show ((0 : B256) =? 0) = 1 from by
      simp [B256.eqCheck]] at hzero
    exact B256.zero_ne_one hzero.symm
  · rcases hsuccess with
      ⟨parent, child, slot, delegated, na, code, availableGas, pc, hstep,
        hdepth, _, hparentState, _, _, _, hdelegation, hfilled, hmessage,
        hclean, hresume, hcallPostState, _, _, _⟩
    rcases exists_retainedXlot_of_filled hfilled with ⟨retained⟩
    have hresolution :
        (getDelegatedCodeAddress (callPre.getCode target.toAdr) = none ∧
            code = callPre.getCode target.toAdr ∧ delegated = false) ∨
          (∃ delegatedTarget,
            getDelegatedCodeAddress (callPre.getCode target.toAdr) =
              some delegatedTarget ∧
            code = callPre.getCode delegatedTarget ∧ delegated = true) := by
      rcases hdelegation with
        ⟨hnone, _, hcode, hdp⟩ | ⟨d, hsome, _, hcode, hdp⟩
      · exact Or.inl ⟨hnone, hcode, hdp⟩
      · exact Or.inr ⟨d, hsome, hcode, hdp⟩
    have hna : na =
        (getDelegatedCodeAddress (callPre.getCode target.toAdr)).getD
          target.toAdr := by
      rcases hdelegation with
        ⟨hnone, heq, _, _⟩ | ⟨d, hsome, heq, _, _⟩
      · rw [heq, hnone]; rfl
      · rw [heq, hsome]; rfl
    rw [hna] at hmessage
    let childMessage :=
      callMsg e parent
        (min g.toNat (except64th availableGas) +
          (if value.toNat = 0 then 0 else gCallStipend))
        value e.currentTarget target.toAdr
        ((getDelegatedCodeAddress (callPre.getCode target.toAdr)).getD
          target.toAdr)
        true false
        ((callPre.memory.read (0 : B256).toNat (0 : B256).toNat).1)
        code delegated
    have hguardState : guardPost.state = child.state := by
      calc
        guardPost.state = testPost.state := hpop.state.symm
        _ = callPost.state :=
          (Ninst.Hinv.inv (f := Devm.state) hiszero).symm
        _ = child.state := hcallPostState
    exact ⟨⟨g, callPost, parent, child, slot, pc, hstep, hdepth,
      delegated, code, availableGas,
      hparentState, hresolution, childMessage, rfl,
      ⟨slot, retained, by simpa only [childMessage] using hmessage⟩,
      hclean, hguardState⟩⟩

theorem exists_burnCallPrefixTrace
    {e : Sevm} {pre callPre guardPost : Devm}
    {owner : Adr} {amount target : B256}
    (burn : BurnCallPrefix e pre callPre guardPost owner amount target) :
    Nonempty (AcceptedValueCallTrace e target amount callPre guardPost) :=
  exists_acceptedValueCallTrace burn.2.2.2.2.2.2.2

/-! ## Withdrawal credits -/

/-- Consensus withdrawals are arbitrary inward ETH for this accounting
purpose.  The block bound makes each `addBal` exact, so they can only improve
the WETH10 ETH inequality, including when `ca` is the recipient. -/
theorem processWithdrawalsState_ethBound
    (ca : Adr) (state : State) (withdrawals : List Withdrawal)
    (hbound : sum state.bal + wdsum withdrawals < 2 ^ 256) :
    EthBound ca state (processWithdrawalsState state withdrawals) [] := by
  induction withdrawals generalizing state with
  | nil => exact EthBound.refl ca state
  | cons withdrawal withdrawals ih =>
      obtain ⟨hheadBound, htailBound⟩ :=
        ExecutionTrace.withdrawalCredit_bounds hbound
      let value := withdrawal.amount * (10 ^ 9).toB256
      let next := state.addBal withdrawal.recipient value
      have hhead : EthBound ca state next [] :=
        (EthStep.externalCredit (ca := ca) (post := next)
          rfl hheadBound).bound
      have htail := ih next htailBound
      have hcombined := hhead.trans htail
      simpa [processWithdrawalsState, next, value] using hcombined

theorem processWithdrawalsState_stable
    {dp : DeployParams} {ca : Adr}
    (state : State) (withdrawals : List Withdrawal)
    (hbound : sum state.bal + wdsum withdrawals < 2 ^ 256)
    (hstable : Stable dp ca state) :
    Stable dp ca (processWithdrawalsState state withdrawals) := by
  have hbacked :=
    ContractSpec.processWithdrawalsState_preserves_inv
      (c := backedSpec weth10 dp) ca state withdrawals hbound
      (show (backedSpec weth10 dp).StateInv ca state from
        ⟨hstable.code, hstable.sumNof, hstable.backed⟩)
  have hflash :=
    ContractSpec.processWithdrawalsState_preserves_inv
      (c := flashExactSpec dp 0) ca state withdrawals hbound
      (show (flashExactSpec dp 0).StateInv ca state from
        ⟨hstable.code, trivial, hstable.flashZero⟩)
  exact ⟨hbacked.code, hbacked.side, hbacked.inv, hflash.inv⟩

/-! ## Transaction envelope facts -/

theorem TransactionTrace.sender_ne_ca
    {dp : DeployParams} {ca : Adr}
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    {state : State} {bout' : BlockOutput}
    (trace : TransactionTrace benv bout tx index state bout')
    (hstable : Stable dp ca benv.state)
    (hnotCreated : ca ∉ benv.createdAccounts) :
    trace.sender ≠ ca :=
  ExecutionTrace.TransactionTrace.sender_ne (c := backedSpec weth10 dp) trace
    ⟨hstable.code, hstable.sumNof, hstable.backed⟩ hnotCreated

theorem TransactionTrace.debitState_bal_ca
    {dp : DeployParams} {ca : Adr}
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    {state : State} {bout' : BlockOutput}
    (trace : TransactionTrace benv bout tx index state bout')
    (hstable : Stable dp ca benv.state)
    (hnotCreated : ca ∉ benv.createdAccounts) :
    trace.debitState.bal ca = benv.state.bal ca :=
  ExecutionTrace.TransactionTrace.debitState_bal_eq trace
    (TransactionTrace.sender_ne_ca trace hstable hnotCreated)

theorem TransactionTrace.accountsToDelete_ne_ca
    {dp : DeployParams} {ca : Adr}
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    {state : State} {bout' : BlockOutput}
    (trace : TransactionTrace benv bout tx index state bout')
    (hstable : Stable dp ca benv.state)
    (hnotCreated : ca ∉ benv.createdAccounts) :
    ∀ address ∈ trace.messageOut.accountsToDelete.toList,
      address ≠ ca :=
  ExecutionTrace.TransactionTrace.accountsToDelete_ne trace
    (backedSpec_preserves dp ca)
    ⟨hstable.code, hstable.sumNof, hstable.backed⟩ hnotCreated

theorem foldl_destroyAccount_bal_eq
    {ca : Adr} {state : State} {addresses : List Adr}
    (hne : ∀ address ∈ addresses, address ≠ ca) :
    (addresses.foldl destroyAccount state).bal ca = state.bal ca :=
  congrArg Acct.bal (ExecutionTrace.foldl_destroyAccount_get_eq hne)

/-- Refund and priority-fee settlement, followed by the transaction's account
deletions, cannot lower the installed WETH10 account.  This is proved from
the checked up-front debit and the actual message result, so it also covers a
coinbase equal to `ca` without assuming that either `addBal` cannot wrap. -/
theorem TransactionTrace.postMessage_ethBound
    {dp : DeployParams} {ca : Adr}
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    {state : State} {bout' : BlockOutput}
    (trace : TransactionTrace benv bout tx index state bout')
    (hstable : Stable dp ca benv.state)
    (hnotCreated : ca ∉ benv.createdAccounts) :
    EthBound ca trace.messageState state [] := by
  rcases ExecutionTrace.TransactionTrace.exists_stateChronology trace with
    ⟨chronology⟩
  obtain ⟨hrefundBound, htipBound⟩ :=
    ExecutionTrace.TransactionTrace.settlement_sum_bounds trace
      chronology.refundCounter hstable.sumNof
  have hrefundStep :
      EthBound ca trace.messageState
        (trace.refundedState chronology.refundCounter) [] :=
    (EthStep.externalCredit (ca := ca) (pre := trace.messageState)
      (post := trace.refundedState chronology.refundCounter)
      (recipient := trace.sender)
      (value := trace.refundValue chronology.refundCounter)
      rfl hrefundBound).bound
  have htipStep :
      EthBound ca (trace.refundedState chronology.refundCounter)
        (trace.coinbaseState chronology.refundCounter) [] :=
    (EthStep.externalCredit (ca := ca)
      (pre := trace.refundedState chronology.refundCounter)
      (post := trace.coinbaseState chronology.refundCounter)
      (recipient := benv.stat.coinbase)
      (value := trace.coinbaseValue chronology.refundCounter)
      rfl htipBound).bound
  have hcredits :
      EthBound ca trace.messageState
        (trace.coinbaseState chronology.refundCounter) [] := by
    simpa using hrefundStep.trans htipStep
  have hdelete := TransactionTrace.accountsToDelete_ne_ca trace
    hstable hnotCreated
  have hdeleteBal :
      (trace.messageOut.accountsToDelete.toList.foldl destroyAccount
        (trace.coinbaseState chronology.refundCounter)).bal ca =
        (trace.coinbaseState chronology.refundCounter).bal ca :=
    foldl_destroyAccount_bal_eq hdelete
  have hstateBal :
      state.bal ca = (trace.coinbaseState chronology.refundCounter).bal ca :=
    (congrArg (fun w : State => w.bal ca) chronology.finalState_eq).trans
      hdeleteBal
  simpa [EthBound, flowActionsEthMint, flowActionsEthRedemption,
    hstateBal] using hcredits

/-! ## The recursive execution seam -/

/-- The two message invariants that actual transaction and system-message
wrappers establish before entering the raw recursive core.  Keeping the full
`MsgInv`s (rather than only their state fields) records code provenance,
non-deletion, transfer direction, and the zero-value non-transfer case. -/
structure MessageReady (dp : DeployParams) (ca : Adr) (msg : Msg) : Prop where
  backed : (backedSpec weth10 dp).MsgInv ca msg
  flash : (flashExactSpec dp 0).MsgInv ca msg

/-- The additional provenance fact needed at the raw interpreter boundary.
For a call message, `target.isNone = false` activates `MsgInv.code`; for a
create message, the wrapper proves that its fresh current target is not the
installed WETH10 address.  Quantifying raw `Exec` over `MessageReady` alone
would be unsound because a synthetic create-style message may otherwise run
arbitrary initialization code with `currentTarget = ca`. -/
structure MessageRunReady
    (dp : DeployParams) (ca : Adr) (msg : Msg) : Prop where
  ready : MessageReady dp ca msg
  codeOrForeign :
    msg.target.isNone = false ∨ msg.currentTarget ≠ ca

theorem MessageReady.stable
    {dp : DeployParams} {ca : Adr} {msg : Msg}
    (ready : MessageReady dp ca msg) :
    Stable dp ca msg.benv.state :=
  ⟨ready.backed.state.code, ready.backed.state.side,
    ready.backed.state.inv, ready.flash.state.inv⟩

theorem MessageReady.runReady_of_call
    {dp : DeployParams} {ca : Adr} {msg : Msg}
    (ready : MessageReady dp ca msg)
    (htarget : msg.target.isNone = false) :
    MessageRunReady dp ca msg :=
  ⟨ready, Or.inl htarget⟩

theorem MessageReady.runReady_of_foreign
    {dp : DeployParams} {ca : Adr} {msg : Msg}
    (ready : MessageReady dp ca msg)
    (htarget : msg.currentTarget ≠ ca) :
    MessageRunReady dp ca msg :=
  ⟨ready, Or.inr htarget⟩

/-- The exact remaining installed-body theorem.  Message-entry funding is
handled independently by `Exec.entryEthBound`, so an implementation must
account only for the root non-mint action and committed descendant frames.
Its `Prog.At` and concrete `Pre` premises pin the execution to the installed
WETH10 program and its backed invariant; no endpoint conservation equation is
assumed. -/
def ExecBodyEthSound (dp : DeployParams) (ca : Adr) : Prop :=
  ∀ {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out)
    (hcommit : Execution.commits out = true),
    Prog.At (weth10 dp) ca pc sevm pre →
    Exec.Frame.IsRoot (Exec.Frame.ofRun run hcommit) →
    (sevm.currentTarget = ca → sevm.codeAddress = some ca) →
    (backedSpec weth10 dp).Pre ca sevm pre →
    EthBound ca pre.state
      (Execution.committedPost out hcommit).state
      (Exec.bodyEthActions dp ca run hcommit)

/-- Complete committed-message accounting at the exact raw interpreter
boundary.  `MessageRunReady` excludes synthetic create-style executions of
foreign code at `ca`; actual call and create wrappers establish it below. -/
def CommittedExecEthSound (dp : DeployParams) (ca : Adr) : Prop :=
  ∀ {msg : Msg} {benv : Benv} {pc : Nat} {sevm : Sevm}
    {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out)
    (_htransfer : msg.benvAfterTransfer = .ok benv)
    (_hinit : (⟨pc, sevm, pre⟩ : Evm) =
      initEvm (msg.withBenv benv))
    (hcommit : Execution.commits out = true),
    MessageRunReady dp ca msg →
    EthBound ca msg.benv.state
      (Execution.committedPost out hcommit).state
      (Exec.flowActions dp ca run)

/-- Entry transfer accounting plus the installed-body theorem discharge the
full raw message theorem. -/
theorem ExecBodyEthSound.committedExecEthSound
    {dp : DeployParams} {ca : Adr}
    (sound : ExecBodyEthSound dp ca) :
    CommittedExecEthSound dp ca := by
  intro msg benv pc sevm pre out run htransfer hinit hcommit runReady
  have hentry := Exec.entryEthBound (dp := dp) (ca := ca)
    run htransfer hinit hcommit
    runReady.ready.backed.ne runReady.ready.backed.val0
    runReady.ready.stable.sumNof
  have hprecond :=
    ContractSpec.Pre.of_inv_benvAfterTransfer
      runReady.ready.backed.ne runReady.ready.backed.val0
      htransfer runReady.ready.backed.state
  have hpc := congrArg Evm.pc hinit
  have hsevm := congrArg Evm.sta hinit
  have hpre := congrArg Evm.dyna hinit
  dsimp only [initEvm] at hpc hsevm hpre
  subst pc
  subst sevm
  subst pre
  have hat : Prog.At (weth10 dp) ca 0
      (initSevm (msg.withBenv benv))
      (initDevm (msg.withBenv benv)) := by
    refine ⟨hprecond.code, ?_⟩
    intro htarget
    refine ⟨?_, rfl⟩
    rcases runReady.codeOrForeign with hcall | hforeign
    · exact runReady.ready.backed.code hcall
        (by simpa [initSevm, Msg.withBenv] using htarget)
    · exact False.elim (hforeign
        (by simpa [initSevm, Msg.withBenv] using htarget))
  have hroot : Exec.Frame.IsRoot (Exec.Frame.ofRun run hcommit) := by
    exact ⟨rfl, rfl⟩
  have hdirect :
      (initSevm (msg.withBenv benv)).currentTarget = ca →
        (initSevm (msg.withBenv benv)).codeAddress = some ca := by
    intro htarget
    rcases runReady.codeOrForeign with hcall | hforeign
    · exact runReady.ready.backed.codeAddress hcall
        (by simpa [initSevm, Msg.withBenv] using htarget)
    · exact False.elim (hforeign
        (by simpa [initSevm, Msg.withBenv] using htarget))
  have hbody := sound run hcommit hat hroot hdirect hprecond
  simpa only [Exec.flowActions_eq_entry_append_body
      (dp := dp) (ca := ca) run hcommit] using
    hentry.trans hbody

theorem Exec.flowActions_eq_nil_of_not_commits
    {dp : DeployParams} {ca : Adr}
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out)
    (hnot : Execution.commits out ≠ true) :
    Exec.flowActions dp ca run = [] := by
  simp [Exec.flowActions, Exec.committedFrames, hnot]

theorem ProcessMessage.ethBound_of_none_conditions
    {ca : Adr} {msg : Msg} {post : Devm}
    (hprocess : ProcessMessage msg .none (.ok post))
    (hcaller : msg.shouldTransferValue = true → msg.caller ≠ ca)
    (hsum : sum msg.benv.state.bal < 2 ^ 256) :
    EthBound ca msg.benv.state post.state [] := by
  simpa [EthBound, flowActionsEthMint, flowActionsEthRedemption] using
    (_root_.Blanc.ProcessMessage.targetBalanceMono_of_none
      hprocess hcaller hsum)

theorem ProcessMessage.ethBound_of_none
    {dp : DeployParams} {ca : Adr} {msg : Msg} {post : Devm}
    (hprocess : ProcessMessage msg .none (.ok post))
    (ready : MessageReady dp ca msg) :
    EthBound ca msg.benv.state post.state [] :=
  ProcessMessage.ethBound_of_none_conditions hprocess
    ready.backed.ne ready.stable.sumNof

/-- Generic successful interpreter-slot accounting from an independently
proved body bound.  This is the child-frame composition rule used by the
proof-indexed recursive ETH traversal; it performs actual message entry and
failed rollback rather than assuming an endpoint equation. -/
theorem ProcessMessage.ethBound_of_bodyBound
    {dp : DeployParams} {ca : Adr}
    {msg : Msg} {post : Devm} {pc : Nat} {sevm : Sevm}
    {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out)
    (hprocess :
      ProcessMessage msg (.some ⟨⟨pc, sevm, pre⟩, out⟩) (.ok post))
    (hcaller : msg.shouldTransferValue = true → msg.caller ≠ ca)
    (hval0 : msg.shouldTransferValue = false →
      msg.currentTarget = ca → msg.value = 0)
    (hsum : sum msg.benv.state.bal < 2 ^ 256)
    (hbody : ∀ (hcommit : Execution.commits out = true),
      EthBound ca pre.state
        (Execution.committedPost out hcommit).state
        (Exec.bodyEthActions dp ca run hcommit)) :
    EthBound ca msg.benv.state post.state
      (Exec.flowActions dp ca run) := by
  have henter := (RunFrame.some_inv hprocess).1
  rcases Frame.enter_run_inv henter with ⟨benv, htransfer, hinit⟩
  by_cases hcommit : Execution.commits out = true
  · have hentry := Exec.entryEthBound (dp := dp) (ca := ca)
      run htransfer hinit hcommit hcaller hval0 hsum
    have hbound := hentry.trans (hbody hcommit)
    rw [ProcessMessage.ok_state_eq_committedPost hprocess hcommit]
    simpa only [Frame.ofCall,
      Exec.flowActions_eq_entry_append_body
        (dp := dp) (ca := ca) run hcommit] using hbound
  · have hstate :=
      ProcessMessage.ok_state_eq_of_not_commits hprocess hcommit
    rw [Exec.flowActions_eq_nil_of_not_commits run hcommit, hstate]
    exact EthBound.refl ca msg.benv.state

/-- Value-child counterpart of `ethBound_of_bodyBound`.  Clean settlement
forces the retained raw execution to commit.  The parent's concrete
redemption action pays for the actual transfer, including the self-call case
where a nested root ordinary mint may also be selected. -/
theorem ProcessMessage.ethBound_of_redemptionBodyBound
    {dp : DeployParams} {ca : Adr}
    {msg : Msg} {post : Devm} {pc : Nat} {sevm : Sevm}
    {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out)
    (hprocess :
      ProcessMessage msg (.some ⟨⟨pc, sevm, pre⟩, out⟩) (.ok post))
    (hclean : post.error.isSome = false)
    (hstv : msg.shouldTransferValue = true)
    (hcaller : msg.caller = ca)
    {action : FlowAction} {rawSource : B256}
    {source ethRecipient : Adr}
    (hatom : action.atom =
      .redemption rawSource source ethRecipient msg.value.toNat)
    (hbody : ∀ (hcommit : Execution.commits out = true),
      EthBound ca pre.state
        (Execution.committedPost out hcommit).state
        (Exec.bodyEthActions dp ca run hcommit)) :
    EthBound ca msg.benv.state post.state
      (action :: Exec.flowActions dp ca run) := by
  have henter := (RunFrame.some_inv hprocess).1
  rcases Frame.enter_run_inv henter with ⟨benv, htransfer, hinit⟩
  have hsettle := (RunFrame.some_inv hprocess).2
  have hsettleCommit :
      Blanc.Frame.settlementCommits (Frame.ofCall msg) out = true := by
    have hclean' : post.error.isNone = true := by
      cases herror : post.error <;> simp_all
    unfold Blanc.Frame.settlementCommits
    rw [← hsettle]
    exact hclean'
  have hcommit : Execution.commits out = true :=
    Frame.raw_commits_of_settlementCommits hsettleCommit
  have hentry := Exec.redemptionEntryEthBound (dp := dp) (ca := ca)
    run htransfer hinit hcommit hstv hcaller hatom
  have hbound := hentry.trans (hbody hcommit)
  rw [ProcessMessage.ok_state_eq_committedPost hprocess hcommit]
  have hflow := Exec.flowActions_eq_entry_append_body
    (dp := dp) (ca := ca) run hcommit
  rw [hflow]
  simpa only [Frame.ofCall, List.cons_append] using hbound

theorem ProcessMessage.ethBound_of_committedExecSound
    {dp : DeployParams} {ca : Adr}
    {msg : Msg} {post : Devm} {pc : Nat} {sevm : Sevm}
    {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out)
    (hprocess :
      ProcessMessage msg (.some ⟨⟨pc, sevm, pre⟩, out⟩) (.ok post))
    (hsound : CommittedExecEthSound dp ca)
    (runReady : MessageRunReady dp ca msg) :
    EthBound ca msg.benv.state post.state
      (Exec.flowActions dp ca run) := by
  have henter := (RunFrame.some_inv hprocess).1
  rcases Frame.enter_run_inv henter with ⟨benv, htransfer, hinit⟩
  by_cases hcommit : Execution.commits out = true
  · have hbound := hsound run htransfer hinit hcommit runReady
    rw [ProcessMessage.ok_state_eq_committedPost hprocess hcommit]
    exact hbound
  · have hstate :=
      ProcessMessage.ok_state_eq_of_not_commits hprocess hcommit
    rw [Exec.flowActions_eq_nil_of_not_commits run hcommit, hstate]
    exact EthBound.refl ca msg.benv.state

/-- Complete raw `ProcessMessage` accounting from the one committed-`Exec`
lemma.  This theorem discharges both failed interpreter rollback and the
precompile/no-slot path. -/
theorem ProcessMessageTrace.ethBound_of_committedExecSound
    {dp : DeployParams} {ca : Adr} {msg : Msg} {post : Devm}
    (trace : ProcessMessageTrace msg (.ok post))
    (hsound : CommittedExecEthSound dp ca)
    (runReady : MessageRunReady dp ca msg) :
    EthBound ca msg.benv.state post.state
      (Blanc.Weth10.RetainedXlot.flowActions dp ca trace.retained) := by
  rcases trace with ⟨slot, retained, hprocess⟩
  cases retained with
  | none =>
      exact ProcessMessage.ethBound_of_none hprocess runReady.ready
  | some run =>
      exact ProcessMessage.ethBound_of_committedExecSound
        run hprocess hsound runReady

theorem processCreateMessage_msg_bal_eq (msg : Msg) :
    (processCreateMessage.msg msg).benv.state.bal =
      msg.benv.state.bal :=
  Blanc.processCreateMessage_msg_bal_eq msg

theorem MessageReady.processCreateMessage_msg
    {dp : DeployParams} {ca : Adr} {msg : Msg}
    (ready : MessageReady dp ca msg)
    (htargetNone : msg.target.isNone = true)
    (htargetNe : msg.currentTarget ≠ ca) :
    MessageReady dp ca (processCreateMessage.msg msg) := by
  have one :
      ∀ (spec : ContractSpec),
        spec.MsgInv ca msg →
        spec.MsgInv ca (processCreateMessage.msg msg) := by
    intro spec hinv
    have hstate : spec.StateInv ca
        (processCreateMessage.msg msg).benv.state := by
      simpa [processCreateMessage.msg, Msg.withBenv,
        addCreatedAccount, Benv.setStor, Benv.incrNonce] using
        (ContractSpec.StateInv.incrNonce
          (ContractSpec.StateInv.setStor_ne htargetNe hinv.state))
    refine ⟨hstate, ?_, ?_, ?_, ?_, ?_⟩
    · refine ⟨?_, ?_⟩
      · simpa [processCreateMessage.msg, Msg.withBenv,
          addCreatedAccount, Benv.setStor, Benv.incrNonce,
          htargetNe] using hinv.nodel.ca
      · exact fun hempty => Prog.compile_ne_nil
          (hstate.code.symm.trans (congrArg some hempty))
    · intro htarget
      simp [processCreateMessage.msg, Msg.withBenv,
        htargetNone] at htarget
    · intro htarget
      simp [processCreateMessage.msg, Msg.withBenv,
        htargetNone] at htarget
    · simpa [processCreateMessage.msg, Msg.withBenv] using hinv.ne
    · intro _ hcurrent
      exact False.elim (htargetNe (by
        simpa [processCreateMessage.msg, Msg.withBenv] using hcurrent))
  exact ⟨one _ ready.backed, one _ ready.flash⟩

theorem ne_ca_of_messageCreateCollision_false
    {dp : DeployParams} {ca : Adr} {msg : Msg}
    (ready : MessageReady dp ca msg)
    (hcollision : messageCreateCollision msg = false) :
    msg.currentTarget ≠ ca :=
  ContractSpec.StateInv.ne_of_messageCreateCollision_false
    ready.backed.state hcollision

theorem processCreateMessage.chargeCodeGas_bal_eq
    {rules : ForkRules} {pre post : Devm}
    (h : processCreateMessage.chargeCodeGas rules pre = .ok post) :
    post.state.bal = pre.state.bal :=
  _root_.Blanc.processCreateMessage.chargeCodeGas_bal_eq h

theorem ProcessCreateMessage.ok_state_eq_inner_of_no_error
    {msg : Msg} {slot : Xlot} {post : Devm}
    (hprocess : ProcessCreateMessage msg slot (.ok post))
    (herror : post.error.isSome = false) :
    ∃ inner : Devm,
      ProcessMessage (processCreateMessage.msg msg) slot (.ok inner) ∧
      post.state.bal = inner.state.bal :=
  _root_.Blanc.ProcessCreateMessage.ok_state_eq_inner_of_no_error
    hprocess herror

/-- CREATE settlement around a no-interpreter-slot constructor is also ETH
sound under the explicit foreign-caller entry conditions.  Code-deposit
failure and errored constructor settlement roll back; successful code deposit
does not alter balances. -/
theorem ProcessCreateMessage.ethBound_of_none_conditions
    {ca : Adr} {msg : Msg} {post : Devm}
    (hprocess : ProcessCreateMessage msg .none (.ok post))
    (hcaller : msg.shouldTransferValue = true → msg.caller ≠ ca)
    (hsum : sum msg.benv.state.bal < 2 ^ 256) :
    EthBound ca msg.benv.state post.state [] := by
  simpa [EthBound, flowActionsEthMint, flowActionsEthRedemption] using
    (_root_.Blanc.ProcessCreateMessage.targetBalanceMono_of_none
      hprocess hcaller hsum)

/-- Create settlement contributes retained raw actions only when code-deposit
settlement also commits.  The error arm proves the outer rollback exactly. -/
theorem ProcessCreateMessageTrace.ethBound_of_committedExecSound
    {dp : DeployParams} {ca : Adr} {msg : Msg} {post : Devm}
    (trace : ProcessCreateMessageTrace msg (.ok post))
    (hsound : CommittedExecEthSound dp ca)
    (ready : MessageReady dp ca msg)
    (htargetNone : msg.target.isNone = true)
    (htargetNe : msg.currentTarget ≠ ca) :
    EthBound ca msg.benv.state post.state
      (if post.error.isSome then []
       else Blanc.Weth10.RetainedXlot.flowActions dp ca
         trace.retained) := by
  cases herror : post.error.isSome with
  | true =>
      simp only [↓reduceIte]
      rw [ProcessCreateMessage.rollback_of_error trace.run herror]
      exact EthBound.refl ca msg.benv.state
  | false =>
      simp
      rcases ProcessCreateMessage.ok_state_eq_inner_of_no_error
        trace.run herror with ⟨inner, hinner, hpost⟩
      let innerTrace : ProcessMessageTrace
          (processCreateMessage.msg msg) (.ok inner) :=
        ⟨trace.slot, trace.retained, hinner⟩
      have hprepared :=
        ready.processCreateMessage_msg htargetNone htargetNe
      have hrunPrepared := hprepared.runReady_of_foreign htargetNe
      have hbound := innerTrace.ethBound_of_committedExecSound
        hsound hrunPrepared
      unfold EthBound at hbound ⊢
      rw [hpost, ← congrFun (processCreateMessage_msg_bal_eq msg) ca]
      simpa only [Bool.true_eq_false, if_false] using hbound

theorem MessageReady.of_messageCallDelegation
    {dp : DeployParams} {ca : Adr} {msg delegated : Msg} {refund : Nat}
    (ready : MessageReady dp ca msg)
    (hrun : messageCallDelegation msg = .ok ⟨delegated, refund⟩) :
    MessageReady dp ca delegated := by
  unfold messageCallDelegation at hrun
  split at hrun
  · simp only [Except.ok.injEq, Prod.mk.injEq] at hrun
    rcases hrun with ⟨rfl, rfl⟩
    exact ready
  · rcases Except.bind_eq_ok hrun with
      ⟨⟨delegated', refundWord⟩, hset, hrest⟩
    simp only [Except.ok.injEq, Prod.mk.injEq] at hrest
    rcases hrest with ⟨rfl, rfl⟩
    exact ⟨ContractSpec.setDelegation_preserves_msgInv hset ready.backed,
      ContractSpec.setDelegation_preserves_msgInv hset ready.flash⟩

theorem MessageReady.messageCallExecutionMessage
    {dp : DeployParams} {ca : Adr} {msg : Msg}
    (ready : MessageReady dp ca msg) :
    MessageReady dp ca (messageCallExecutionMessage msg) := by
  exact ⟨ContractSpec.MsgInv.pc
      (codeSrc := fun dca => msg.benv.state.getCode dca) ready.backed,
    ContractSpec.MsgInv.pc
      (codeSrc := fun dca => msg.benv.state.getCode dca) ready.flash⟩

theorem setDelegation_bal_eq
    {msg delegated : Msg} {refund : B256}
    (hrun : setDelegation msg = .ok ⟨delegated, refund⟩) :
    delegated.benv.state.bal = msg.benv.state.bal := by
  unfold setDelegation at hrun
  rcases Except.bind_eq_ok hrun with
    ⟨⟨loopMsg, loopRefund⟩, hloop, hrest⟩
  have hbal := setDelegationLoop_bal_eq hloop
  cases hcode : loopMsg.codeAddress with
  | none => simp [hcode] at hrest
  | some address =>
    simp [hcode] at hrest
    rcases hrest with ⟨rfl, rfl⟩
    exact hbal

theorem messageCallDelegation_bal_eq
    {msg delegated : Msg} {refund : Nat}
    (hrun : messageCallDelegation msg = .ok ⟨delegated, refund⟩) :
    delegated.benv.state.bal = msg.benv.state.bal := by
  unfold messageCallDelegation at hrun
  split at hrun
  · simp only [Except.ok.injEq, Prod.mk.injEq] at hrun
    rcases hrun with ⟨rfl, rfl⟩
    rfl
  · rcases Except.bind_eq_ok hrun with
      ⟨⟨delegated', refundWord⟩, hset, hrest⟩
    simp only [Except.ok.injEq, Prod.mk.injEq] at hrest
    rcases hrest with ⟨rfl, rfl⟩
    exact setDelegation_bal_eq hset

theorem messageCallDelegation_target_eq
    {msg delegated : Msg} {refund : Nat}
    (hrun : messageCallDelegation msg = .ok ⟨delegated, refund⟩) :
    delegated.target = msg.target := by
  unfold messageCallDelegation at hrun
  split at hrun
  · simp only [Except.ok.injEq, Prod.mk.injEq] at hrun
    rcases hrun with ⟨rfl, rfl⟩
    rfl
  · rcases Except.bind_eq_ok hrun with
      ⟨⟨delegated', refundWord⟩, hset, hrest⟩
    simp only [Except.ok.injEq, Prod.mk.injEq] at hrest
    rcases hrest with ⟨rfl, rfl⟩
    exact (setDelegation_fields hset).2.1

theorem messageCallExecutionMessage_target_eq (msg : Msg) :
    (messageCallExecutionMessage msg).target = msg.target := by
  unfold messageCallExecutionMessage
  split <;> rfl

theorem processMessageCall_createCollision_state_eq
    {msg : Msg} {state : State} {out : MsgCallOutput}
    (htarget : msg.target.isNone = true)
    (hcollision : messageCreateCollision msg = true)
    (hresult : processMessageCall msg = .ok ⟨state, out⟩) :
    state = msg.benv.state := by
  unfold processMessageCall at hresult
  simp only [htarget, ↓reduceIte] at hresult
  unfold processMessageCall.create at hresult
  unfold messageCreateCollision at hcollision
  simp only [hcollision, ↓reduceIte, pure] at hresult
  exact (Prod.mk.inj (Except.ok.inj hresult)).1.symm

theorem processMessageCall_createRun_state_eq
    {msg : Msg} {evm : Devm} {state : State} {out : MsgCallOutput}
    (htarget : msg.target.isNone = true)
    (hcollision : messageCreateCollision msg = false)
    (hcore : processCreateMessage msg = .ok evm)
    (hresult : processMessageCall msg = .ok ⟨state, out⟩) :
    state = evm.state := by
  unfold processMessageCall at hresult
  simp only [htarget, ↓reduceIte] at hresult
  unfold processMessageCall.create at hresult
  unfold messageCreateCollision at hcollision
  simp only [hcollision, Bool.false_eq_true, ↓reduceIte,
    bind, Except.bind] at hresult
  rcases Except.bind_eq_ok hresult with
    ⟨actual, hactualMap, htail⟩
  have hactualCore := Except.bimap_id_eq_ok hactualMap
  have hactualEq : actual = evm := Except.ok.inj
    (hactualCore.symm.trans hcore)
  subst actual
  split at htail
  · rcases Except.bind_eq_ok htail with
      ⟨refundActual, _hrefund, hout⟩
    exact (Prod.mk.inj (Except.ok.inj hout)).1.symm
  · exact (Prod.mk.inj (Except.ok.inj htail)).1.symm

theorem processMessageCall_callRun_state_eq
    {msg delegated execMsg : Msg} {refund : Nat}
    {evm : Devm} {state : State} {out : MsgCallOutput}
    (htarget : msg.target.isNone = false)
    (hdelegation :
      messageCallDelegation msg = .ok ⟨delegated, refund⟩)
    (hexecMsg : execMsg = messageCallExecutionMessage delegated)
    (hcore : processMessage execMsg = .ok evm)
    (hresult : processMessageCall msg = .ok ⟨state, out⟩) :
    state = evm.state := by
  unfold processMessageCall at hresult
  simp only [htarget, Bool.false_eq_true, ↓reduceIte] at hresult
  cases hauth : msg.tenv.stat.auths.isEmpty with
  | false =>
      unfold messageCallDelegation at hdelegation
      simp only [hauth, Bool.false_eq_true, ↓reduceIte] at hdelegation
      rcases Except.bind_eq_ok hdelegation with
        ⟨⟨delegated', refundWord⟩, hset, hrest⟩
      simp only [Except.ok.injEq, Prod.mk.injEq] at hrest
      rcases hrest with ⟨rfl, rfl⟩
      unfold processMessageCall.call at hresult
      simp only [hauth, Bool.false_eq_true, ↓reduceIte,
        hset, bind, Except.bind] at hresult
      have hcoreExec :
          processMessage (messageCallExecutionMessage delegated') =
            .ok evm :=
        (congrArg processMessage hexecMsg).symm.trans hcore
      rcases Except.bind_eq_ok hresult with
        ⟨actual, hactualMap, htail⟩
      have hactualCore := Except.bimap_id_eq_ok hactualMap
      have hactualEq : actual = evm := Except.ok.inj
        (hactualCore.symm.trans hcoreExec)
      subst actual
      split at htail
      · rcases Except.bind_eq_ok htail with
          ⟨refundActual, _hrefund, hout⟩
        exact (Prod.mk.inj (Except.ok.inj hout)).1.symm
      · exact (Prod.mk.inj (Except.ok.inj htail)).1.symm
  | true =>
      unfold messageCallDelegation at hdelegation
      simp only [hauth, ↓reduceIte,
        Except.ok.injEq, Prod.mk.injEq] at hdelegation
      rcases hdelegation with ⟨rfl, rfl⟩
      unfold processMessageCall.call at hresult
      simp only [hauth, ↓reduceIte,
        bind, Except.bind] at hresult
      have hcoreExec :
          processMessage (messageCallExecutionMessage msg) = .ok evm :=
        (congrArg processMessage hexecMsg).symm.trans hcore
      rcases Except.bind_eq_ok hresult with
        ⟨actual, hactualMap, htail⟩
      have hactualCore := Except.bimap_id_eq_ok hactualMap
      have hactualEq : actual = evm := Except.ok.inj
        (hactualCore.symm.trans hcoreExec)
      subst actual
      split at htail
      · rcases Except.bind_eq_ok htail with
          ⟨refundActual, _hrefund, hout⟩
        exact (Prod.mk.inj (Except.ok.inj hout)).1.symm
      · exact (Prod.mk.inj (Except.ok.inj htail)).1.symm

/-- ETH accounting for one exact settled message trace.  Proving this
predicate from the retained recursive execution is the sole semantic seam
left by the wrapper/body/history lifts below. -/
def MessageCallTrace.EthAccounted
    (dp : DeployParams) (ca : Adr)
    {msg : Msg} {state : State} {out : MsgCallOutput}
    (trace : MessageCallTrace msg state out) : Prop :=
  EthBound ca msg.benv.state state (trace.flowActions dp ca)

/-- A uniform discharge of the retained-message seam.  It is deliberately
phrased over exact `MessageCallTrace`s rather than endpoint executions. -/
def MessageEthSound (dp : DeployParams) (ca : Adr) : Prop :=
  ∀ {msg : Msg} {state : State} {out : MsgCallOutput}
    (trace : MessageCallTrace msg state out),
    MessageReady dp ca msg →
    trace.EthAccounted dp ca

/-- The exact raw committed-execution theorem discharges every settled
message shape, including collision, EIP-7702 delegation, precompiles, failed
rollback, and create code-deposit rollback. -/
theorem CommittedExecEthSound.messageEthSound
    {dp : DeployParams} {ca : Adr}
    (hsound : CommittedExecEthSound dp ca) :
    MessageEthSound dp ca := by
  intro msg state out trace ready
  cases trace with
  | createCollision htarget hcollision hresult =>
      unfold MessageCallTrace.EthAccounted
      change EthBound ca msg.benv.state state []
      have hstate := processMessageCall_createCollision_state_eq
        htarget hcollision hresult
      simpa only [hstate] using EthBound.refl ca msg.benv.state
  | createRun htarget hcollision evm hcore trace hresult =>
      unfold MessageCallTrace.EthAccounted
      have htargetNe := ne_ca_of_messageCreateCollision_false
        ready hcollision
      have hbound :=
        ProcessCreateMessageTrace.ethBound_of_committedExecSound trace
          hsound ready htarget htargetNe
      have hstate := processMessageCall_createRun_state_eq
        htarget hcollision hcore hresult
      change EthBound ca msg.benv.state state
        (if evm.error.isSome then []
         else Blanc.Weth10.RetainedXlot.flowActions dp ca trace.retained)
      unfold EthBound at hbound ⊢
      rw [hstate]
      exact hbound
  | callRun htarget delegated refund hdelegation execMsg hexecMsg evm
      hcore trace hresult =>
      unfold MessageCallTrace.EthAccounted
      have readyDelegated := ready.of_messageCallDelegation hdelegation
      have readyExec := readyDelegated.messageCallExecutionMessage
      have readyExecMsg : MessageReady dp ca execMsg := by
        simpa only [hexecMsg] using readyExec
      have htargetExec : execMsg.target.isNone = false := by
        rw [hexecMsg, messageCallExecutionMessage_target_eq,
          messageCallDelegation_target_eq hdelegation]
        exact htarget
      have runReadyExec := readyExecMsg.runReady_of_call htargetExec
      have hbound : EthBound ca execMsg.benv.state evm.state
          (Blanc.Weth10.RetainedXlot.flowActions dp ca trace.retained) :=
        ProcessMessageTrace.ethBound_of_committedExecSound trace hsound
          runReadyExec
      have hstate := processMessageCall_callRun_state_eq
        htarget hdelegation hexecMsg hcore hresult
      have hpre : execMsg.benv.state.bal = msg.benv.state.bal := by
        rw [hexecMsg, ExecutionTrace.messageCallExecutionMessage_bal_eq,
          messageCallDelegation_bal_eq hdelegation]
      change EthBound ca msg.benv.state state
        (Blanc.Weth10.RetainedXlot.flowActions dp ca trace.retained)
      unfold EthBound at hbound ⊢
      rw [hstate, ← congrFun hpre ca]
      exact hbound

theorem TransactionTrace.messageReady
    {dp : DeployParams} {ca : Adr}
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    {state : State} {bout' : BlockOutput}
    (trace : TransactionTrace benv bout tx index state bout')
    (hstable : Stable dp ca benv.state)
    (hnotCreated : ca ∉ benv.createdAccounts) :
    MessageReady dp ca trace.msg :=
  ⟨ExecutionTrace.TransactionTrace.msgInv (c := backedSpec weth10 dp) trace
      ⟨hstable.code, hstable.sumNof, hstable.backed⟩ hnotCreated,
    ExecutionTrace.TransactionTrace.msgInv (c := flashExactSpec dp 0) trace
      ⟨hstable.code, trivial, hstable.flashZero⟩ hnotCreated⟩

theorem TransactionTrace.message_stable_and_safe
    {dp : DeployParams} {ca : Adr}
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    {state : State} {bout' : BlockOutput}
    (trace : TransactionTrace benv bout tx index state bout')
    (hstable : Stable dp ca benv.state)
    (hnotCreated : ca ∉ benv.createdAccounts) :
    Stable dp ca trace.msg.benv.state ∧
      ca ∉ trace.msg.benv.createdAccounts ∧
      (trace.msg.shouldTransferValue = true → trace.msg.caller ≠ ca) := by
  have ready := TransactionTrace.messageReady trace hstable hnotCreated
  exact ⟨ready.stable, ready.backed.nodel.ca, ready.backed.ne⟩

/-- The actual transaction wrapper contributes only its exact message
actions.  Its up-front debit is from a non-contract sender; refund, fee-tip,
and deletion settlement are handled by `postMessage_ethBound`. -/
theorem TransactionTrace.ethBound
    {dp : DeployParams} {ca : Adr}
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    {state : State} {bout' : BlockOutput}
    (trace : TransactionTrace benv bout tx index state bout')
    (hmessage : MessageEthSound dp ca)
    (hstable : Stable dp ca benv.state)
    (hnotCreated : ca ∉ benv.createdAccounts) :
    EthBound ca benv.state state
      (Blanc.Weth10.TransactionTrace.flowActions dp ca trace) := by
  have hdebit : EthBound ca benv.state trace.debitState [] :=
    (EthStep.silent (ca := ca)
      (TransactionTrace.debitState_bal_ca trace hstable hnotCreated)).bound
  have hready := TransactionTrace.messageReady trace hstable hnotCreated
  have hmsg := hmessage trace.message hready
  unfold MessageCallTrace.EthAccounted at hmsg
  rw [prepareMessage_benv trace.prepared] at hmsg
  change EthBound ca trace.debitState trace.messageState
    (Blanc.Weth10.MessageCallTrace.flowActions dp ca trace.message) at hmsg
  have hsettled :=
    TransactionTrace.postMessage_ethBound trace hstable hnotCreated
  have htotal := (hdebit.trans hmsg).trans hsettled
  simpa [TransactionTrace.flowActions] using htotal

theorem SystemMessageTrace.messageReady
    {dp : DeployParams} {ca : Adr}
    {benv : Benv} {target : Adr} {data : Bytes}
    {state : State} {out : MsgCallOutput}
    (_trace : SystemMessageTrace benv target data state out)
    (hstable : Stable dp ca benv.state)
    (hnotCreated : ca ∉ benv.createdAccounts) :
    MessageReady dp ca (systemTransactionMessage benv target data) :=
  ⟨ExecutionTrace.systemTransactionMessage_msgInv
      ⟨hstable.code, hstable.sumNof, hstable.backed⟩ hnotCreated,
    ExecutionTrace.systemTransactionMessage_msgInv
      ⟨hstable.code, trivial, hstable.flashZero⟩ hnotCreated⟩

theorem SystemMessageTrace.ethBound
    {dp : DeployParams} {ca : Adr}
    {benv : Benv} {target : Adr} {data : Bytes}
    {state : State} {out : MsgCallOutput}
    (trace : SystemMessageTrace benv target data state out)
    (hmessage : MessageEthSound dp ca)
    (hstable : Stable dp ca benv.state)
    (hnotCreated : ca ∉ benv.createdAccounts) :
    EthBound ca benv.state state
      (Blanc.Weth10.SystemMessageTrace.flowActions dp ca trace) := by
  have hready := SystemMessageTrace.messageReady trace hstable hnotCreated
  have hmsg := hmessage trace.message hready
  unfold MessageCallTrace.EthAccounted at hmsg
  simpa [SystemMessageTrace.flowActions, systemTransactionMessage,
    processSystemTransactionMsg, Benv.beginTransaction] using hmsg

/-- Stability and total-balance monotonicity transported across an actual
unchecked system-message trace. -/
theorem SystemMessageTrace.stable_and_sum_le
    {dp : DeployParams} {ca : Adr}
    {benv : Benv} {target : Adr} {data : Bytes}
    {state : State} {out : MsgCallOutput}
    (trace : SystemMessageTrace benv target data state out)
    (hstable : Stable dp ca benv.state)
    (hnotCreated : ca ∉ benv.createdAccounts) :
    Stable dp ca state ∧ sum state.bal ≤ sum benv.state.bal := by
  have hbacked := trace.stateInv_and_sum_le (backedSpec_preserves dp ca)
    ⟨⟨hstable.code, hstable.sumNof, hstable.backed⟩, hnotCreated⟩
  have hflash := trace.stateInv_and_sum_le (flashExactSpec_preserves dp ca 0)
    ⟨⟨hstable.code, trivial, hstable.flashZero⟩, hnotCreated⟩
  exact ⟨⟨hbacked.1.code, hbacked.1.side, hbacked.1.inv,
    hflash.1.inv⟩, hbacked.2⟩

theorem TransactionTrace.stable
    {dp : DeployParams} {ca : Adr}
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    {state : State} {bout' : BlockOutput}
    (trace : TransactionTrace benv bout tx index state bout')
    (hstable : Stable dp ca benv.state)
    (hnotCreated : ca ∉ benv.createdAccounts) :
    Stable dp ca state :=
  processTransaction_preserves_stable dp ca benv bout bout' tx index state
    trace.result hstable.sumNof hnotCreated hstable

theorem ApplyTransactionsTrace.sum_le
    {txs : List (Nat × Tx)} {benv finalBenv : Benv}
    {bout finalBout : BlockOutput}
    (trace : ApplyTransactionsTrace txs benv bout finalBenv finalBout) :
    sum finalBenv.state.bal ≤ sum benv.state.bal :=
  ExecutionTrace.ApplyTransactionsTrace.sum_le trace

theorem ApplyTransactionsTrace.createdAccounts_eq
    {txs : List (Nat × Tx)} {benv finalBenv : Benv}
    {bout finalBout : BlockOutput}
    (trace : ApplyTransactionsTrace txs benv bout finalBenv finalBout) :
    finalBenv.createdAccounts = benv.createdAccounts :=
  ExecutionTrace.ApplyTransactionsTrace.createdAccounts_eq trace

theorem ApplyTransactionsTrace.stable
    {dp : DeployParams} {ca : Adr}
    {txs : List (Nat × Tx)} {benv finalBenv : Benv}
    {bout finalBout : BlockOutput}
    (trace : ApplyTransactionsTrace txs benv bout finalBenv finalBout)
    (hstable : Stable dp ca benv.state)
    (hnotCreated : ca ∉ benv.createdAccounts) :
    Stable dp ca finalBenv.state := by
  have hbacked := trace.benvInv (backedSpec_preserves dp ca) hstable.sumNof
    ⟨⟨hstable.code, hstable.sumNof, hstable.backed⟩, hnotCreated⟩
  have hflash := trace.benvInv (flashExactSpec_preserves dp ca 0)
    hstable.sumNof ⟨⟨hstable.code, trivial, hstable.flashZero⟩, hnotCreated⟩
  exact ⟨hbacked.state.code, hbacked.state.side, hbacked.state.inv,
    hflash.state.inv⟩

theorem ApplyTransactionsTrace.ethBound
    (dp : DeployParams) (ca : Adr)
    (hmessage : MessageEthSound dp ca) :
    {txs : List (Nat × Tx)} → {benv : Benv} → {bout : BlockOutput} →
    {finalBenv : Benv} → {finalBout : BlockOutput} →
    (trace : ApplyTransactionsTrace txs benv bout finalBenv finalBout) →
    Stable dp ca benv.state →
    ca ∉ benv.createdAccounts →
    EthBound ca benv.state finalBenv.state
      (Blanc.Weth10.ApplyTransactionsTrace.flowActions dp ca trace)
  | _, _, _, _, _, .nil benv _bout, _, _ =>
      EthBound.refl ca benv.state
  | _, _, _, _, _, .cons head tail, hstable, hnotCreated =>
      EthBound.trans
        (TransactionTrace.ethBound head hmessage hstable hnotCreated)
        (ApplyTransactionsTrace.ethBound dp ca hmessage tail
          (TransactionTrace.stable head hstable hnotCreated)
          (by simpa [Benv.withState] using hnotCreated))

theorem RequestsTrace.ethBound
    {dp : DeployParams} {ca : Adr}
    {benv : Benv} {bout : BlockOutput}
    {state : State} {bout' : BlockOutput}
    (trace : RequestsTrace benv bout state bout')
    (hmessage : MessageEthSound dp ca)
    (hstable : Stable dp ca benv.state)
    (hnotCreated : ca ∉ benv.createdAccounts) :
    EthBound ca benv.state state
      (Blanc.Weth10.RequestsTrace.flowActions dp ca trace) := by
  have hwithdrawal :=
    SystemMessageTrace.ethBound trace.withdrawal hmessage hstable hnotCreated
  have hwithdrawalMeta :=
    SystemMessageTrace.stable_and_sum_le trace.withdrawal hstable hnotCreated
  have hconsolidation :=
    SystemMessageTrace.ethBound trace.consolidation hmessage
      hwithdrawalMeta.1
      (by simpa [Benv.withState] using hnotCreated)
  have hboth := hwithdrawal.trans hconsolidation
  simpa [RequestsTrace.flowActions, Benv.withState,
    ExecutionTrace.RequestsTrace.state_eq_consolidationState trace] using hboth

theorem RequestsTrace.stable_and_sum_le
    {dp : DeployParams} {ca : Adr}
    {benv : Benv} {bout : BlockOutput}
    {state : State} {bout' : BlockOutput}
    (trace : RequestsTrace benv bout state bout')
    (hstable : Stable dp ca benv.state)
    (hnotCreated : ca ∉ benv.createdAccounts) :
    Stable dp ca state ∧ sum state.bal ≤ sum benv.state.bal := by
  have hbacked := trace.stateInv_and_sum_le (backedSpec_preserves dp ca)
    ⟨⟨hstable.code, hstable.sumNof, hstable.backed⟩, hnotCreated⟩
  have hflash := trace.stateInv_and_sum_le (flashExactSpec_preserves dp ca 0)
    ⟨⟨hstable.code, trivial, hstable.flashZero⟩, hnotCreated⟩
  exact ⟨⟨hbacked.1.code, hbacked.1.side, hbacked.1.inv,
    hflash.1.inv⟩, hbacked.2⟩

/-! ## Block-body and history lifts -/

/-- Complete ETH accounting for an actual retained block-body trace,
conditional only on the uniform retained-message seam.  The withdrawal bound
is transported through the balance-nonincreasing system and transaction
prefix before the exact withdrawal credits are added. -/
theorem AppliedBodyTrace.ethBound
    {dp : DeployParams} {ca : Adr}
    {benv : Benv} {txs : List (Bytes ⊕ Tx)}
    {wds : List Withdrawal} {state : State} {bout : BlockOutput}
    (trace : AppliedBodyTrace benv txs wds state bout)
    (hmessage : MessageEthSound dp ca)
    (hstable : Stable dp ca benv.state)
    (hnotCreated : ca ∉ benv.createdAccounts)
    (hbound : sum benv.state.bal + wdsum wds < 2 ^ 256) :
    EthBound ca benv.state state
      (Blanc.Weth10.AppliedBodyTrace.flowActions dp ca trace) := by
  have hbeacon :=
    SystemMessageTrace.ethBound trace.beacon hmessage hstable hnotCreated
  have hbeaconMeta :=
    SystemMessageTrace.stable_and_sum_le trace.beacon hstable hnotCreated
  have hhistoryMeta :=
    SystemMessageTrace.stable_and_sum_le trace.history hbeaconMeta.1
      (by simpa [Benv.withState] using hnotCreated)
  have hhistory :=
    SystemMessageTrace.ethBound trace.history hmessage hbeaconMeta.1
      (by simpa [Benv.withState] using hnotCreated)
  have htransactions :=
    ApplyTransactionsTrace.ethBound dp ca hmessage trace.transactions
      hhistoryMeta.1
      (by simpa [Benv.withState] using hnotCreated)
  have htxSum := ApplyTransactionsTrace.sum_le trace.transactions
  have htxSum' :
      sum trace.transactionBenv.state.bal ≤
        sum trace.historyState.bal := by
    simpa [Benv.withState] using htxSum
  have hhistorySum :
      sum trace.historyState.bal ≤ sum benv.state.bal :=
    le_trans (by simpa [Benv.withState] using hhistoryMeta.2)
      hbeaconMeta.2
  have hwithdrawalBound :
      sum trace.transactionBenv.state.bal + wdsum wds < 2 ^ 256 := by
    omega
  have hwithdrawals :=
    processWithdrawalsState_ethBound ca trace.transactionBenv.state wds
      hwithdrawalBound
  have htransactionsStable :=
    ApplyTransactionsTrace.stable trace.transactions hhistoryMeta.1
      (by simpa [Benv.withState] using hnotCreated)
  have hwithdrawalsStable :=
    processWithdrawalsState_stable trace.transactionBenv.state wds
      hwithdrawalBound htransactionsStable
  have htransactionNotCreated :
      ca ∉ trace.transactionBenv.createdAccounts := by
    rw [ApplyTransactionsTrace.createdAccounts_eq trace.transactions]
    simpa [Benv.withState] using hnotCreated
  have hrequests := RequestsTrace.ethBound trace.requests hmessage
    hwithdrawalsStable
    (by simpa [Benv.withState] using htransactionNotCreated)
  have htotal :=
    (((hbeacon.trans hhistory).trans htransactions).trans hwithdrawals).trans
      hrequests
  simpa [AppliedBodyTrace.flowActions, Benv.withState,
    List.append_assoc] using htotal

theorem AccountedBlock.ethBound
    {chainId : UInt64} {dp : DeployParams} {ca : Adr}
    {pre post : BlockChain}
    (accounted : AccountedBlock chainId dp ca pre post)
    (hmessage : MessageEthSound dp ca)
    (hstable : Stable dp ca pre.state) :
    EthBound ca pre.state post.state accounted.actions := by
  have hbody :=
    AppliedBodyTrace.ethBound accounted.bodyTrace hmessage hstable
      (by simp [initBenv]) accounted.bound
  have hpost := congrArg (fun chain : BlockChain => chain.state)
    accounted.postEq
  simpa [initBenv, accounted.actions_eq, hpost] using hbody

/-- Global contract-ETH accounting across a proof-carrying committed Prague
history.  Once `MessageEthSound` is discharged from retained recursive
execution, this is the unconditional execution-side inequality needed for
credit no-wrap. -/
theorem AccountedHistory.ethBound
    (chainId : UInt64) (dp : DeployParams) (ca : Adr)
    (hmessage : MessageEthSound dp ca) :
    {checkpoint : BlockChain} → {future : BlockChain} →
    (history : AccountedHistory chainId dp ca checkpoint future) →
    Stable dp ca checkpoint.state →
    EthBound ca checkpoint.state future.state history.flowActions
  | _, _, .refl _ _ _, _ =>
      EthBound.refl ca _
  | _, _, .step prior accounted, hstable =>
      EthBound.trans
        (AccountedHistory.ethBound chainId dp ca hmessage prior hstable)
        (AccountedBlock.ethBound accounted hmessage
          (prior.future_stable hstable))

/-- Full history accounting with all settlement/wrapper premises discharged;
only the concrete committed raw-`Exec` theorem remains to be supplied. -/
theorem AccountedHistory.ethBound_of_committedExecSound
    (chainId : UInt64) (dp : DeployParams) (ca : Adr)
    (hsound : CommittedExecEthSound dp ca) :
    {checkpoint : BlockChain} → {future : BlockChain} →
    (history : AccountedHistory chainId dp ca checkpoint future) →
    Stable dp ca checkpoint.state →
    EthBound ca checkpoint.state future.state history.flowActions :=
  AccountedHistory.ethBound chainId dp ca hsound.messageEthSound

end Weth10

end Blanc
