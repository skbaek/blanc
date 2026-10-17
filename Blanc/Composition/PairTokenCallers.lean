import Blanc.Lift.UniswapV2Pair.PairHistoryShape
import Blanc.Lift.UniswapV2Pair.PropertiesSides
import Blanc.Lift.Token.Abi

import Blanc.Lift.Token.Along
import Blanc.Lift.Token.SelfCaller
import Blanc.ExecutionTraceRootCallers

/-!
# The Pair's booked calls on a token, and its allowances, along a configured history

Against the token core only (no token storage layout), under the C3 hypotheses (A8):

* `pair_token_entry_transfer`: every non-static entry frame of the token `T` called by the Pair is
  one of the Pair's own `transfer` requests (caller fold `settledFrames_callerTarget_of_children`:
  Pair frames call `T` only by `transfer`, `T` never forwards a foreign caller into its own entries
  (`SelfCaller`), and the Pair originates no settled root (EIP-3607, `pair ≠ systemAddress`));
* `Core.good_along`: every ledger along the replay of a settled prefix is good;
* `pair_token_segment`: along any contiguous run of settled frames, the Pair loses at most the
  amounts of its own `transfer` entries and keeps a zero allowance (`BookLaws.run_holder`, A5 form).
-/

namespace Blanc.Composition.PairTokenJoint

open Jaune Blanc Blanc.ExecutionTrace Blanc.Lift Blanc.Lift.Token Blanc.Lift.UniswapV2Pair

/-- The Pair originates no settled message root of a history from an installed checkpoint. -/
theorem pair_history_settledRoots_caller_ne {pair : Adr} {cfg : ChainConfig}
    {checkpoint future : BlockChain} {K₀ : WriterKey → Prop} {st₀ : UniswapV2Pair.State}
    (trace : ConfiguredHistoryTrace cfg checkpoint future)
    (installed : some (checkpoint.state.getCode pair).toList = pairSem.image)
    (initial : WriterRep K₀ (checkpoint.state.getStor pair) st₀)
    (fresh : WriterFreshKeys K₀ (pairHistoryTouchedKeys pair trace))
    (notSystem : pair ≠ systemAddress) :
    ∀ R ∈ trace.settledRoots, R.sevm.caller ≠ pair := by
  let U := WriterExtend K₀ (pairHistoryTouchedKeys pair trace)
  have extended : WriterRep U (checkpoint.state.getStor pair) st₀ := initial.extend fresh
  have admitted : trace.FrameAdmitted pair (pairEntry U) :=
    pair_trace_admitted trace (fun k row => Or.inr row)
  have start : (pairSpec U).StateInv pair checkpoint.state :=
    ⟨installed, trivial, ⟨st₀, K₀, fun _ h => Or.inl h, initial⟩⟩
  exact trace.settledRoots_caller_ne
    (pairSpec_preservesAdmittedWith pair
      (pairAdmittedSupply extended.inj extended.apart pairSem pairSem_image))
    admitted start notSystem

/-- What a token entry called by the Pair is: one of the Pair's `transfer` requests. -/
def PairTransferAsk (T : Adr) (s : Sevm) : Prop :=
  s.isStatic = false → s.codeAddress = some T →
    ∃ recipient value, s.data = (ExternalOperation.transfer recipient value).encode

/-- **Every non-static entry of the token called by the Pair is one of the Pair's own `transfer`
requests**, and the book reads it as that transfer. -/
theorem pair_token_entry_transfer {pair T : Adr} {B : Book} (C : Core T B) (abi : Erc20Abi B)
    (self : SelfCaller C) (side : TokenSide) {cfg : ChainConfig} {checkpoint future : BlockChain}
    {K₀ : WriterKey → Prop} {st₀ : UniswapV2Pair.State}
    (trace : ConfiguredHistoryTrace cfg checkpoint future)
    (installed : some (checkpoint.state.getCode pair).toList = pairSem.image)
    (initial : WriterRep K₀ (checkpoint.state.getStor pair) st₀)
    (fresh : WriterFreshKeys K₀ (pairHistoryTouchedKeys pair trace))
    (hist : C.Hist trace) (token : st₀.tokenOn side = T) (unlocked : st₀.unlocked = 1)
    (apart : pair ≠ T) (notSystem : pair ≠ systemAddress)
    (factoryQuiet : ∀ G ∈ trace.settledFrames, G.sevm.currentTarget = pair →
      G.sevm.isStatic = false → G.sevm.caller ≠ st₀.factory) :
    ∀ F ∈ trace.settledFrames, IsEntry T F → F.sevm.isStatic = false → F.sevm.caller = pair →
      ∃ recipient value, F.sevm.data = (ExternalOperation.transfer recipient value).encode ∧
        B.op F.sevm = .transfer recipient value.toNat := by
  have tokens : T = st₀.token0 ∨ T = st₀.token1 := by
    cases side
    · exact Or.inl token.symm
    · exact Or.inr token.symm
  have fold := trace.settledFrames_callerTarget_of_children (p := pair) (ca := T)
    (Q := PairTransferAsk T)
    (fun R member _ caller =>
      absurd caller (pair_history_settledRoots_caller_ne trace installed initial fresh notSystem
        R member))
    (by
      intro G member which c child target caller static codeAddress
      rcases which with atPair | atToken
      · cases staticG : G.sevm.isStatic
        · obtain ⟨-, shape⟩ := (pair_history_mutable_children trace installed initial fresh
            unlocked factoryQuiet G member atPair staticG c child static).cases
          rcases shape with ⟨-, recipient, value, data⟩ | ⟨-, apart0, apart1⟩
          · exact ⟨recipient, value, data⟩
          · rcases tokens with h | h
            · exact absurd (target.trans h) apart0
            · exact absurd (target.trans h) apart1
        · rw [Exec.childFrames_isStatic G.run staticG c child] at static
          cases static
      · cases staticG : G.sevm.isStatic
        · have selfCaller := self.child_caller trace hist G member atToken staticG c child
            ⟨target, codeAddress⟩
          exact absurd (caller.symm.trans selfCaller) apart
        · rw [Exec.childFrames_isStatic G.run staticG c child] at static
          cases static)
  intro F member entry static caller
  obtain ⟨recipient, value, data⟩ := fold F member entry.1 caller static entry.2
  refine ⟨recipient, value, data, ?_⟩
  have length := transfer_encode_length recipient value
  have words := transfer_encode_words data
  have selector : Blanc.Sevm.selector F.sevm = 0xa9059cbb := by
    rw [Blanc.Sevm.selector_eq_toB256_takeD_four, data]
    simp only [ExternalOperation.encode, List.cons_append, List.takeD, List.headD_cons,
      List.tail_cons]
    rfl
  rw [abi.transfer F.sevm (by rw [data, length]) (by rw [data, length]; decide)
    selector, words.1, words.2, toAdr_toB256]

open Classical in
/-- A message among the entry messages of a list is the message of one of its non-static
entries. -/
theorem mem_entryAsks {T : Adr} {frames : List Exec.Frame} {a : Sevm}
    (member : a ∈ entryAsks T frames) :
    ∃ F ∈ frames, IsEntry T F ∧ F.sevm.isStatic = false ∧ F.sevm = a := by
  obtain ⟨F, inFilter, rfl⟩ := List.mem_map.mp member
  obtain ⟨inFrames, picked⟩ := List.mem_filter.mp inFilter
  obtain ⟨entry, static⟩ := of_decide_eq_true picked
  exact ⟨F, inFrames, entry, static, rfl⟩

/-- **Pair segment.**  Along a contiguous run of settled frames, the Pair loses at most the amounts
of its own `transfer` entries and keeps a zero allowance (under the C3 hypotheses). -/
theorem pair_token_segment {pair T : Adr} {B : Book} (C : Core T B) (laws : BookLaws B)
    (abi : Erc20Abi B) (self : SelfCaller C) (side : TokenSide) {cfg : ChainConfig}
    {checkpoint future : BlockChain} {K₀ : WriterKey → Prop} {st₀ : UniswapV2Pair.State}
    (trace : ConfiguredHistoryTrace cfg checkpoint future)
    (installed : some (checkpoint.state.getCode pair).toList = pairSem.image)
    (initial : WriterRep K₀ (checkpoint.state.getStor pair) st₀)
    (fresh : WriterFreshKeys K₀ (pairHistoryTouchedKeys pair trace))
    (hist : C.Hist trace) (token : st₀.tokenOn side = T) (unlocked : st₀.unlocked = 1)
    (apart : pair ≠ T) (notSystem : pair ≠ systemAddress)
    (factoryQuiet : ∀ G ∈ trace.settledFrames, G.sevm.currentTarget = pair →
      G.sevm.isStatic = false → G.sevm.caller ≠ st₀.factory)
    {pre mid post : List Exec.Frame} (split : trace.settledFrames = pre ++ mid ++ post)
    {l l' : B.Ledger} (atPre : B.run (C.ledgerOf trace checkpoint.state) (entryAsks T pre) = some l)
    (step : B.run l (entryAsks T mid) = some l') (zero : ∀ g, B.allow l pair g = 0) :
    B.bal l pair ≤ B.bal l' pair + (((entryAsks T mid).filter fun a => decide (a.caller = pair)).map
      fun a => (B.op a).debit pair).sum ∧ ∀ g, B.allow l' pair g = 0 := by
  refine C.run_holder_segment laws trace hist split atPre step zero ?_
  intro a member caller
  obtain ⟨F, inMid, entry, static, rfl⟩ := mem_entryAsks member
  have settled : F ∈ trace.settledFrames := by
    rw [split]
    exact List.mem_append_left _ (List.mem_append_right _ inMid)
  obtain ⟨recipient, value, -, op⟩ := pair_token_entry_transfer C abi self side trace installed
    initial fresh hist token unlocked apart notSystem factoryQuiet F settled entry static caller
  rw [op]
  trivial

end Blanc.Composition.PairTokenJoint
