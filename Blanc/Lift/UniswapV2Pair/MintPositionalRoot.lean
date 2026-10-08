import Blanc.Lift.UniswapV2Pair.MintPositionalThree
import Blanc.Lift.UniswapV2Pair.MintPositionalSuffix

/-! Three actual Mint instructions selected by the original public root. -/
namespace Blanc.Lift.UniswapV2Pair
open Jaune

def mintRootReserves (root : Exec.Deriv) (b : Devm) : Devm :=
  afterSload root.sevm (mintLockedWorld root.sevm b) 8

def mintRootToken0 (root : Exec.Deriv) (b : Devm) : B256 :=
  ((mintRootReserves root b).getStorVal root.sevm.currentTarget 6).toAdr.toB256

def mintRootReserve0 (root : Exec.Deriv) (b : Devm) : B256 :=
  reserve0Read ((mintLockedWorld root.sevm b).getStorVal root.sevm.currentTarget 8)

def mintRootReserve1 (root : Exec.Deriv) (b : Devm) : B256 :=
  reserve1Read ((mintLockedWorld root.sevm b).getStorVal root.sevm.currentTarget 8)

def mintRootFirstWorld (root : Exec.Deriv) (b : Devm) : Devm :=
  temporalAccountAccessBase (afterSload root.sevm (mintRootReserves root b) 6)
    (mintRootToken0 root b).toAdr

abbrev MintRootFirst (root : Exec.Deriv) (b : Devm) :=
  MintBalanceOccurrence root root .first (mintRootFirstWorld root b) (mintRootToken0 root b)
    (164 :: 0x70a08231 :: mintRootToken0 root b :: 0 :: mintRootReserve1 root b ::
      mintRootReserve0 root b :: 0 :: (Sevm.dataWord root.sevm 4).toAdr.toB256 ::
      0x039b :: [0x6a627842])
    (balanceRequestMemory getterInitMemory root.sevm.currentTarget) [t_039b_c86]

def mintRootToken1 {root : Exec.Deriv} {b : Devm} (first : MintRootFirst root b) : B256 :=
  (first.call.returned.devm.getStorVal first.call.returned.sevm.currentTarget 7).toAdr.toB256

def mintRootSecondWorld {root : Exec.Deriv} {b : Devm} (first : MintRootFirst root b) : Devm :=
  temporalAccountAccessBase (afterSload first.call.returned.sevm first.call.returned.devm 7)
    (mintRootToken1 first).toAdr

abbrev MintRootSecond {root : Exec.Deriv} {b : Devm} (first : MintRootFirst root b)
    (out0 : Bytes) :=
  MintBalanceOccurrence root first.call.returned .second (mintRootSecondWorld first)
    (mintRootToken1 first)
    (164 :: 0x70a08231 :: mintRootToken1 first :: 0 :: Bytes.toB256 (out0.take 32) ::
      mintRootReserve1 root b :: mintRootReserve0 root b :: 0 ::
      (Sevm.dataWord root.sevm 4).toAdr.toB256 :: 0x039b :: [0x6a627842])
    (balanceRequestMemory (balanceReplyMemory getterInitMemory root.sevm.currentTarget out0)
      first.call.returned.sevm.currentTarget) [t_039b_c86]

/-- All three original slots are selected in order. The two complete physical
balance replies feed the operands at the following actual instructions. -/
structure MintRootCallPositions (root : Exec.Deriv) (b : Devm) where
  first : MintRootFirst root b
  guarded0 : ((mintRootFirstWorld root b).getCode (mintRootToken0 root b).toAdr).size.toB256 ≠ 0
  out0 : Bytes
  post0 : StaticCallPost (mintRootFirstWorld root b) first.call.returned.devm
    (164 :: 0x70a08231 :: mintRootToken0 root b :: 0 :: mintRootReserve1 root b ::
      mintRootReserve0 root b :: 0 :: (Sevm.dataWord root.sevm 4).toAdr.toB256 ::
      0x039b :: [0x6a627842])
    (balanceRequestMemory getterInitMemory root.sevm.currentTarget) 128 36 128 32 1 out0
  bound0 : out0.length < 2 ^ 256
  width0 : 32 ≤ out0.length
  answer0 : StaticAnswered root.sevm (mintRootFirstWorld root b) (mintRootToken0 root b).toAdr
    (ExternalOperation.encode (.balanceOf root.sevm.currentTarget)) out0
  second : MintRootSecond first out0
  guarded1 : ((mintRootSecondWorld first).getCode (mintRootToken1 first).toAdr).size.toB256 ≠ 0
  out1 : Bytes
  post1 : StaticCallPost (mintRootSecondWorld first) second.call.returned.devm
    (164 :: 0x70a08231 :: mintRootToken1 first :: 0 :: Bytes.toB256 (out0.take 32) ::
      mintRootReserve1 root b :: mintRootReserve0 root b :: 0 ::
      (Sevm.dataWord root.sevm 4).toAdr.toB256 :: 0x039b :: [0x6a627842])
    (balanceRequestMemory (balanceReplyMemory getterInitMemory root.sevm.currentTarget out0)
      first.call.returned.sevm.currentTarget) 128 36 128 32 1 out1
  bound1 : out1.length < 2 ^ 256
  width1 : 32 ≤ out1.length
  answer1 : StaticAnswered first.call.returned.sevm (mintRootSecondWorld first)
    (mintRootToken1 first).toAdr
    (ExternalOperation.encode (.balanceOf first.call.returned.sevm.currentTarget)) out1
  cover0 : mintRootReserve0 root b ≤ Bytes.toB256 (out0.take 32)
  cover1 : mintRootReserve1 root b ≤ Bytes.toB256 (out1.take 32)
  fee : PairFeeObservation root second.call.returned second.call.returned.devm
    (balanceReplyMemory (balanceReplyMemory getterInitMemory root.sevm.currentTarget out0)
      first.call.returned.sevm.currentTarget out1)
    (mintRootReserve1 root b) (mintRootReserve0 root b) 0x1233
    (mintFeeLocals (Bytes.toB256 (out1.take 32) - mintRootReserve1 root b)
      (Bytes.toB256 (out0.take 32) - mintRootReserve0 root b)
      (Bytes.toB256 (out1.take 32)) (Bytes.toB256 (out0.take 32))
      (mintRootReserve1 root b) (mintRootReserve0 root b)
      (Sevm.dataWord root.sevm 4).toAdr.toB256 0x039b [0x6a627842])
    [t_1233_c41, t_039b_c86]

/-- The successful public root retains the actual first code guard as well as
the original first slot; neither fact is inferred from a later reply. -/
theorem mint_first_guarded_occurrence_of_success {sevm : Sevm} {b post : Devm} {G : Nat}
    (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (selector : Blanc.Sevm.selector sevm = 0x6a627842)
    (run : Exec 0 sevm (St b [] Mem.empty G) (.ok post)) :
    let root : Exec.Deriv := ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩
    ((mintRootFirstWorld root b).getCode (mintRootToken0 root b).toAdr).size.toB256 ≠ 0 ∧
      Nonempty (MintRootFirst root b) := by
  obtain ⟨_, _, abi, unlocked, _⟩ := mint_prefix_guards_of_success codeEq fork selector run
  obtain ⟨entry⟩ := mint_public_cursor_state codeEq fork selector run
  obtain ⟨internal⟩ := mint_abi_cursor_state entry rfl fork abi
  obtain ⟨reserves⟩ := mint_lock_cursor_state internal rfl fork unlocked
  obtain ⟨requestEntry⟩ := pair_reserves_cursor_state reserves rfl fork
  have guarded := mint_first_code_guard requestEntry rfl fork getterInitMemory_ptr
  obtain ⟨request⟩ := mint_first_guard_cursor_state requestEntry rfl fork getterInitMemory_ptr
  refine ⟨?_, mint_balance_occurrence_of_request_cursor .first request (.refl _) rfl fork⟩
  simpa only [mintRootFirstWorld, mintRootReserves, mintRootToken0,
    Devm.getCode, Devm.getAcct, temporalAccountAccessBase_state] using guarded

/-- All three occurrences and physical replies are derived from the supplied
public execution; code and arithmetic guards are retained without new premises. -/
theorem mint_three_occurrences_of_success {sevm : Sevm} {b post : Devm} {G : Nat}
    (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (selector : Blanc.Sevm.selector sevm = 0x6a627842)
    (run : Exec 0 sevm (St b [] Mem.empty G) (.ok post)) :
    Nonempty (MintRootCallPositions ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩ b) := by
  let root : Exec.Deriv := ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩
  obtain ⟨guarded0, ⟨first⟩⟩ := mint_first_guarded_occurrence_of_success codeEq fork selector run
  have firstPtr : PtrMem 128 192 (balanceRequestMemory getterInitMemory sevm.currentTarget) :=
    balanceRequestMemory_ptr getterInitMemory_ptr sevm.currentTarget
  obtain ⟨out0, reply0, bound0, width0, answer0, guarded1, ⟨second⟩⟩ :=
    mint_second_occurrence_of_first first rfl fork getterInitMemory_ptr.wf firstPtr
  have replyPtr := balanceReplyMemory_ptr out0 firstPtr
  have secondPtr : PtrMem 128 192
      (balanceRequestMemory (balanceReplyMemory getterInitMemory sevm.currentTarget out0)
        first.call.returned.sevm.currentTarget) :=
    balanceRequestMemory_ptr replyPtr first.call.returned.sevm.currentTarget
  have returnedSuccess : first.call.returned.exn = .ok post := first.returned_exn
  have returnedFork : CoveredFork first.call.returned.sevm.benvStat.fork := by
    rw [first.returned_sevm]; exact fork
  have low (word : B256) : (word &&& reserveMask112).toNat < 2 ^ 112 := by
    rw [show reserveMask112 = (2 ^ 112 - 1 : Nat).toB256 from rfl,
      PackedWord.lowMask_toNat word (by decide : 112 ≤ 256)]
    exact Nat.mod_lt _ (by decide)
  have reserve0Bound : (mintRootReserve0 root b).toNat < 2 ^ 112 := low _
  have reserve1Bound : (mintRootReserve1 root b).toNat < 2 ^ 112 := low _
  obtain ⟨out1, reply1, bound1, width1, answer1, cover0, cover1, ⟨fee⟩⟩ :=
    mint_fee_observation_of_second second returnedSuccess returnedFork replyPtr.wf
      secondPtr reserve0Bound reserve1Bound
  exact ⟨⟨first, guarded0, out0, reply0, bound0, width0, answer0,
    second, guarded1, out1, reply1, bound1, width1, answer1, cover0, cover1, fee⟩⟩

/-- The final no-exec fact uses this certificate's own fee occurrence and
continuations, rather than an independently selected terminal cursor. -/
theorem MintRootCallPositions.final_no_exec {root : Exec.Deriv} {b : Devm}
    (r : MintRootCallPositions root b) (fork : CoveredFork root.sevm.benvStat.fork) :
    ∀ N, Exec.Deriv.ParentPrefix r.fee.occurrence.call.returned N → ∀ x,
      ¬ Ninst.At N.sevm.code N.pc (.exec x) := by
  have returnedEnv : r.fee.occurrence.call.returned.sevm = root.sevm :=
    (Cursor.parentStep_sevm r.fee.occurrence.call.edge).trans
      (r.fee.occurrence.sevm_eq.trans (r.second.returned_sevm.trans r.first.returned_sevm))
  exact mint_fee_suffix_no_exec r.fee.occurrence.placed r.fee.occurrence.tree
    r.fee.occurrence.continuations (by rw [returnedEnv]; exact fork)

end Blanc.Lift.UniswapV2Pair
