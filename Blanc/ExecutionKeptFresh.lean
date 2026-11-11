import Blanc.ExecutionKeptConfigured
import Blanc.ExecutionFrameEntry

/-! # Exact fresh machines in the settlement-retained kept carrier -/

namespace Blanc

open Jaune

/-- A kept target frame is either the fresh root or a genuinely entered fresh descendant. -/
theorem Root.keptAt_fresh {root : Root}
    (fresh : Exec.FreshEntry root.evm.sta root.evm.dyna) (a : Adr)
    {frame : Exec.Frame} (member : frame ∈ root.keptAt a) :
    Exec.FreshEntry frame.sevm frame.pre := by
  unfold Root.keptAt at member
  split at member
  next committed =>
    split at member
    next target =>
      rw [List.mem_singleton] at member
      subst frame
      exact fresh
    next foreign =>
      exact Exec.rawFrameDescendants_fresh root.run _
        (Exec.mem_rawFrameDescendants_of_mem_descendantFrames root.run frame
          (Exec.mem_descendantFrames_of_mem_keptAt root.run member))
  next rolled => exact False.elim (List.not_mem_nil member)

private def RootsFresh (roots : List Root) : Prop :=
  ∀ root ∈ roots, Exec.FreshEntry root.evm.sta root.evm.dyna

private theorem message_roots_fresh {msg : Msg} {state : State} {out : MsgCallOutput}
    {roots : List Root} (run : MessageRoots msg state out roots) : RootsFresh roots := by
  intro root member
  have entry := run.entry_machine member
  exact ⟨entry.2.1, entry.2.2.1⟩

private theorem transaction_roots_fresh {benv : Benv} {bout : BlockOutput} {tx : Tx}
    {index : Nat} {state : State} {bout' : BlockOutput} {sender : Adr} {roots : List Root}
    (run : TransactionRoots benv bout tx index state bout' sender roots) : RootsFresh roots := by
  obtain ⟨msg, _, _, _, message⟩ := run.2
  exact message_roots_fresh message

private theorem transactions_roots_fresh {txs : List (Nat × Tx)} {benv final : Benv}
    {bout out : BlockOutput} {senders : List (Adr × Tx)} {roots : List Root}
    (run : TransactionsRoots txs benv bout final out senders roots) : RootsFresh roots := by
  induction run with
  | nil => exact fun _ member => False.elim (List.not_mem_nil member)
  | cons head _ ih =>
      intro root member
      rcases List.mem_append.mp member with first | later
      · exact transaction_roots_fresh head root first
      · exact ih root later

private theorem pre_call_fresh {on : Bool} {benv : Benv} {target : Adr} {data : Bytes}
    {state : State} {roots : List Root} (run : PreCall on benv target data state roots) :
    RootsFresh roots := by
  unfold PreCall at run
  split at run
  · obtain ⟨out, message⟩ := run
    exact message_roots_fresh message
  · obtain ⟨_, rfl⟩ := run
    exact fun _ member => False.elim (List.not_mem_nil member)

private theorem pre_roots_fresh {benv : Benv} {state : State} {bal : BalBuilder}
    {roots : List Root} (run : PreRoots benv state bal roots) : RootsFresh roots := by
  obtain ⟨_, _, _, _, _, beacon, _, history, rfl⟩ := run
  intro root member
  rcases List.mem_append.mp member with first | later
  · exact pre_call_fresh beacon root first
  · exact pre_call_fresh history root later

private theorem request_roots_fresh {idx : Nat} {contracts : List (UInt8 × Adr)}
    {benv : Benv} {acc acc' : List Bytes} {bal bal' : BalBuilder} {state : State}
    {steps : List RequestStep}
    (run : RequestRoots idx contracts benv acc bal state acc' bal' steps) :
    RootsFresh (requestRootsOf steps) := by
  induction run with
  | nil => exact fun _ member => False.elim (List.not_mem_nil member)
  | cons _ message _ ih =>
      intro root member
      change root ∈ _ ++ requestRootsOf _ at member
      rcases List.mem_append.mp member with first | later
      · exact message_roots_fresh message root first
      · exact ih root later

private theorem request_pass_fresh {benv : Benv} {bout out : BlockOutput} {state : State}
    {steps : List RequestStep} (run : RequestPass benv bout state out steps) :
    RootsFresh (requestRootsOf steps) := by
  unfold RequestPass at run
  split at run
  · obtain ⟨_, _, _, _, requests, _⟩ := run
    exact request_roots_fresh requests
  · obtain ⟨_, _, rfl⟩ := run
    exact fun _ member => False.elim (List.not_mem_nil member)

/-- Every body root comes from an actual message entry with an empty stack and memory. -/
theorem BodyRoots.roots_fresh {benv : Benv} {txs : List (Bytes ⊕ Tx)} {ommers : List Header}
    {wds : List Withdrawal} {state : State} {bout : BlockOutput} {body : BodyRun}
    (run : BodyRoots benv txs ommers wds state bout body) :
    ∀ root ∈ body.roots, Exec.FreshEntry root.evm.sta root.evm.dyna := by
  obtain ⟨_, _, transactions⟩ := run.transactions
  obtain ⟨_, _, requests⟩ := run.requests
  intro root member
  change root ∈ _ ++ _ ++ _ at member
  rcases List.mem_append.mp member with before | request
  · rcases List.mem_append.mp before with pre | transaction
    · exact pre_roots_fresh run.pre root pre
    · exact transactions_roots_fresh transactions root transaction
  · exact request_pass_fresh requests root request

/-- Fresh entry is derived on the original kept history, with no code, fork or budget premise. -/
theorem KeptHistory.fresh {cfg : ChainConfig} {start stop : BlockChain} {blocks : List KeptBlock}
    (run : KeptHistory cfg start blocks stop) (a : Adr) :
    ∀ block ∈ blocks, ∀ frame ∈ block.keptAt a, Exec.FreshEntry frame.sevm frame.pre := by
  intro block blockMember frame frameMember
  obtain ⟨_, step⟩ := run.mem_step block blockMember
  obtain ⟨root, rootMember, kept⟩ := List.mem_flatMap.mp frameMember
  exact Root.keptAt_fresh (step.body.roots_fresh root rootMember) a kept

end Blanc
