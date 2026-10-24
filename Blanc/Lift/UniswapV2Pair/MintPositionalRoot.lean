import Blanc.Lift.UniswapV2Pair.MintPositionalThree
import Blanc.Lift.UniswapV2Pair.MintPositionalSuffix

/-! Three actual Mint instructions selected by the original public root. -/
namespace Blanc.Lift.UniswapV2Pair
open Jaune

def mintRootReserves (root : Exec.Deriv) (b : Devm) : Devm :=
  afterSload root.sevm (mintLockedWorld root.sevm b) 8

def mintRootReservesH (root : Exec.Deriv) (b : Devm) : Devm :=
  afterSloadH root.sevm (mintLockedWorldH root.sevm b) 8

theorem mintRootReservesH_of_covered {root : Exec.Deriv} {b : Devm}
    (fork : CoveredFork root.sevm.benvStat.fork) :
    mintRootReservesH root b = mintRootReserves root b := by
  unfold mintRootReservesH mintRootReserves
  simp only [mintLockedWorldH_of_covered fork, afterSloadH_of_eip2929 fork.rules_access]

def mintRootToken0 (root : Exec.Deriv) (b : Devm) : B256 :=
  ((mintRootReserves root b).getStorVal root.sevm.currentTarget 6).toAdr.toB256

def mintRootReserve0 (root : Exec.Deriv) (b : Devm) : B256 :=
  reserve0Read ((mintLockedWorld root.sevm b).getStorVal root.sevm.currentTarget 8)

def mintRootReserve1 (root : Exec.Deriv) (b : Devm) : B256 :=
  reserve1Read ((mintLockedWorld root.sevm b).getStorVal root.sevm.currentTarget 8)

def mintRootFirstWorld (root : Exec.Deriv) (b : Devm) : Devm :=
  temporalAccountAccessBase (afterSload root.sevm (mintRootReserves root b) 6)
    (mintRootToken0 root b).toAdr

def mintRootFirstWorldH (root : Exec.Deriv) (b : Devm) : Devm :=
  accountAccessH root.sevm (afterSloadH root.sevm (mintRootReservesH root b) 6)
    (mintRootToken0 root b).toAdr

theorem mintRootFirstWorldH_of_covered {root : Exec.Deriv} {b : Devm}
    (fork : CoveredFork root.sevm.benvStat.fork) :
    mintRootFirstWorldH root b = mintRootFirstWorld root b := by
  unfold mintRootFirstWorldH mintRootFirstWorld
  simp only [mintRootReservesH_of_covered fork, afterSloadH_of_eip2929 fork.rules_access, accountAccessH_of_eip2929 fork.rules_access]

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

/-- The cached token1 word read from an actual returned node. -/
def mintToken1Of (d : Exec.Deriv) : B256 :=
  (d.devm.getStorVal d.sevm.currentTarget 7).toAdr.toB256

/-- The second balance call's world as a function of the returned node's environment
and world, before the access schedule is fixed. `mintRootSecondWorld first` is this at
`first.call.returned`. -/
def mintSecondWorldOf (s : Sevm) (d : Devm) : Devm :=
  temporalAccountAccessBase (afterSload s d 7) ((d.getStorVal s.currentTarget 7).toAdr.toB256).toAdr

def mintSecondWorldOfH (s : Sevm) (d : Devm) : Devm :=
  accountAccessH s (afterSloadH s d 7) ((d.getStorVal s.currentTarget 7).toAdr.toB256).toAdr

theorem mintSecondWorldOfH_of_covered {s : Sevm} {d : Devm} (fork : CoveredFork s.benvStat.fork) :
    mintSecondWorldOfH s d = mintSecondWorldOf s d := by
  unfold mintSecondWorldOfH mintSecondWorldOf
  simp only [afterSloadH_of_eip2929 fork.rules_access, accountAccessH_of_eip2929 fork.rules_access]

/-- The three call worlds of the Mint root under the historical access schedule. -/
def MintRootWorldsH (root : Exec.Deriv) (b W1 : Devm) (A2 F : Sevm → Devm → Devm) : Prop :=
  W1 = mintRootFirstWorldH root b ∧
    (∀ s d, s = root.sevm → A2 s d = mintSecondWorldOfH s d) ∧
    (∀ s d, s = root.sevm → F s d = feeFactoryCallWorldH s d)

theorem MintRootWorldsH.historical (root : Exec.Deriv) (b : Devm) :
    MintRootWorldsH root b (mintRootFirstWorldH root b) mintSecondWorldOfH feeFactoryCallWorldH :=
  ⟨rfl, fun _ _ _ => rfl, fun _ _ _ => rfl⟩

theorem MintRootWorldsH.of_covered {root : Exec.Deriv} {b : Devm}
    (fork : CoveredFork root.sevm.benvStat.fork) :
    MintRootWorldsH root b (mintRootFirstWorld root b) mintSecondWorldOf feeFactoryCallWorld :=
  ⟨(mintRootFirstWorldH_of_covered fork).symm,
    fun s d same => by subst same; exact (mintSecondWorldOfH_of_covered fork).symm,
    fun s d same => by subst same; exact (feeFactoryCallWorldH_of_covered fork).symm⟩

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

/-- `MintRootCallPositions` with its three call worlds as parameters: the first world `W1`,
and the second-call and fee-call worlds as functions `A2`, `F` of the returned node's
environment and world. `worlds` fixes them to the historical schedule; at the modern worlds
the call fields are the modern ones field for field. -/
structure MintRootCallPositionsH (root : Exec.Deriv) (b W1 : Devm) (A2 F : Sevm → Devm → Devm) where
  worlds : MintRootWorldsH root b W1 A2 F
  first : MintBalanceOccurrence root root .first W1 (mintRootToken0 root b)
    (164 :: 0x70a08231 :: mintRootToken0 root b :: 0 :: mintRootReserve1 root b ::
      mintRootReserve0 root b :: 0 :: (Sevm.dataWord root.sevm 4).toAdr.toB256 ::
      0x039b :: [0x6a627842])
    (balanceRequestMemory getterInitMemory root.sevm.currentTarget) [t_039b_c86]
  guarded0 : (W1.getCode (mintRootToken0 root b).toAdr).size.toB256 ≠ 0
  out0 : Bytes
  post0 : StaticCallPost W1 first.call.returned.devm
    (164 :: 0x70a08231 :: mintRootToken0 root b :: 0 :: mintRootReserve1 root b ::
      mintRootReserve0 root b :: 0 :: (Sevm.dataWord root.sevm 4).toAdr.toB256 ::
      0x039b :: [0x6a627842])
    (balanceRequestMemory getterInitMemory root.sevm.currentTarget) 128 36 128 32 1 out0
  bound0 : out0.length < 2 ^ 256
  width0 : 32 ≤ out0.length
  answer0 : StaticAnsweredH root.sevm W1 (mintRootToken0 root b).toAdr
    (ExternalOperation.encode (.balanceOf root.sevm.currentTarget)) out0
  second : MintBalanceOccurrence root first.call.returned .second
    (A2 first.call.returned.sevm first.call.returned.devm) (mintToken1Of first.call.returned)
    (164 :: 0x70a08231 :: mintToken1Of first.call.returned :: 0 :: Bytes.toB256 (out0.take 32) ::
      mintRootReserve1 root b :: mintRootReserve0 root b :: 0 ::
      (Sevm.dataWord root.sevm 4).toAdr.toB256 :: 0x039b :: [0x6a627842])
    (balanceRequestMemory (balanceReplyMemory getterInitMemory root.sevm.currentTarget out0)
      first.call.returned.sevm.currentTarget) [t_039b_c86]
  guarded1 : ((A2 first.call.returned.sevm first.call.returned.devm).getCode
    (mintToken1Of first.call.returned).toAdr).size.toB256 ≠ 0
  out1 : Bytes
  post1 : StaticCallPost (A2 first.call.returned.sevm first.call.returned.devm)
    second.call.returned.devm
    (164 :: 0x70a08231 :: mintToken1Of first.call.returned :: 0 :: Bytes.toB256 (out0.take 32) ::
      mintRootReserve1 root b :: mintRootReserve0 root b :: 0 ::
      (Sevm.dataWord root.sevm 4).toAdr.toB256 :: 0x039b :: [0x6a627842])
    (balanceRequestMemory (balanceReplyMemory getterInitMemory root.sevm.currentTarget out0)
      first.call.returned.sevm.currentTarget) 128 36 128 32 1 out1
  bound1 : out1.length < 2 ^ 256
  width1 : 32 ≤ out1.length
  answer1 : StaticAnsweredH first.call.returned.sevm (A2 first.call.returned.sevm first.call.returned.devm)
    (mintToken1Of first.call.returned).toAdr
    (ExternalOperation.encode (.balanceOf first.call.returned.sevm.currentTarget)) out1
  cover0 : mintRootReserve0 root b ≤ Bytes.toB256 (out0.take 32)
  cover1 : mintRootReserve1 root b ≤ Bytes.toB256 (out1.take 32)
  fee : PairFeeObservationH root second.call.returned second.call.returned.devm
    (F second.call.returned.sevm second.call.returned.devm)
    (balanceReplyMemory (balanceReplyMemory getterInitMemory root.sevm.currentTarget out0)
      first.call.returned.sevm.currentTarget out1)
    (mintRootReserve1 root b) (mintRootReserve0 root b) 0x1233
    (mintFeeLocals (Bytes.toB256 (out1.take 32) - mintRootReserve1 root b)
      (Bytes.toB256 (out0.take 32) - mintRootReserve0 root b)
      (Bytes.toB256 (out1.take 32)) (Bytes.toB256 (out0.take 32))
      (mintRootReserve1 root b) (mintRootReserve0 root b)
      (Sevm.dataWord root.sevm 4).toAdr.toB256 0x039b [0x6a627842])
    [t_1233_c41, t_039b_c86]

/-- The modern positions' worlds, at the modern call worlds. -/
abbrev MintRootCallPositionsM (root : Exec.Deriv) (b : Devm) :=
  MintRootCallPositionsH root b (mintRootFirstWorld root b) mintSecondWorldOf feeFactoryCallWorld

theorem MintRootCallPositionsH.firstFork {root : Exec.Deriv} {b W1 : Devm} {A2 F : Sevm → Devm → Devm}
    (h : MintRootCallPositionsH root b W1 A2 F) (fork : CoveredFork root.sevm.benvStat.fork) :
    CoveredFork h.first.call.returned.sevm.benvStat.fork := by
  rw [h.first.returned_sevm]; exact fork

theorem MintRootCallPositionsH.secondFork {root : Exec.Deriv} {b W1 : Devm} {A2 F : Sevm → Devm → Devm}
    (h : MintRootCallPositionsH root b W1 A2 F) (fork : CoveredFork root.sevm.benvStat.fork) :
    CoveredFork h.second.call.returned.sevm.benvStat.fork := by
  rw [h.second.returned_sevm, h.first.returned_sevm]; exact fork

/-- At the modern call worlds and on a covered fork, `MintRootCallPositionsH` gives the modern
`MintRootCallPositions` field for field. -/
def MintRootCallPositionsH.toCovered {root : Exec.Deriv} {b : Devm}
    (fork : CoveredFork root.sevm.benvStat.fork) (h : MintRootCallPositionsM root b) :
    MintRootCallPositions root b :=
  ⟨h.first, h.guarded0, h.out0, h.post0, h.bound0, h.width0,
    (StaticAnsweredH_iff_of_covered fork).mp h.answer0, h.second, h.guarded1, h.out1, h.post1,
    h.bound1, h.width1, (StaticAnsweredH_iff_of_covered (h.firstFork fork)).mp h.answer1,
    h.cover0, h.cover1, h.fee.toCovered (h.secondFork fork)⟩

/-- On a covered fork, the modern `MintRootCallPositions` is `MintRootCallPositionsH` at the
modern call worlds. -/
def MintRootCallPositions.toH {root : Exec.Deriv} {b : Devm}
    (fork : CoveredFork root.sevm.benvStat.fork) (h : MintRootCallPositions root b) :
    MintRootCallPositionsM root b :=
  have firstFork : CoveredFork h.first.call.returned.sevm.benvStat.fork := by
    rw [h.first.returned_sevm]; exact fork
  have secondFork : CoveredFork h.second.call.returned.sevm.benvStat.fork := by
    rw [h.second.returned_sevm, h.first.returned_sevm]; exact fork
  ⟨MintRootWorldsH.of_covered fork, h.first, h.guarded0, h.out0, h.post0, h.bound0, h.width0,
    (StaticAnsweredH_iff_of_covered fork).mpr h.answer0, h.second, h.guarded1, h.out1, h.post1,
    h.bound1, h.width1, (StaticAnsweredH_iff_of_covered firstFork).mpr h.answer1,
    h.cover0, h.cover1, h.fee.toH secondFork⟩

theorem mint_first_guarded_occurrence_of_successH {sevm : Sevm} {b post : Devm} {G : Nat}
    (codeEq : sevm.code = code) (stateGas : sevm.benvStat.rules.stateGas = none)
    (bal : sevm.benvStat.rules.bal = none)
    (selector : Blanc.Sevm.selector sevm = 0x6a627842)
    (run : Exec 0 sevm (St b [] Mem.empty G) (.ok post)) :
    let root : Exec.Deriv := ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩
    ((mintRootFirstWorldH root b).getCode (mintRootToken0 root b).toAdr).size.toB256 ≠ 0 ∧
      Nonempty (MintBalanceOccurrence root root .first (mintRootFirstWorldH root b)
        (mintRootToken0 root b)
        (164 :: 0x70a08231 :: mintRootToken0 root b :: 0 :: mintRootReserve1 root b ::
          mintRootReserve0 root b :: 0 :: (Sevm.dataWord root.sevm 4).toAdr.toB256 ::
          0x039b :: [0x6a627842])
        (balanceRequestMemory getterInitMemory root.sevm.currentTarget) [t_039b_c86]) := by
  obtain ⟨_, _, abi, unlocked, _⟩ := mint_prefix_guards_of_successH codeEq stateGas bal selector run
  obtain ⟨entry⟩ := mint_public_cursor_stateH codeEq stateGas selector run
  obtain ⟨internal⟩ := mint_abi_cursor_stateH entry rfl stateGas abi
  obtain ⟨reserves⟩ := mint_lock_cursor_stateH internal rfl stateGas bal unlocked
  obtain ⟨requestEntry⟩ := pair_reserves_cursor_stateH reserves rfl stateGas bal
  have guarded := mint_first_code_guardH requestEntry rfl stateGas bal getterInitMemory_ptr
  obtain ⟨request⟩ := mint_first_guard_cursor_stateH requestEntry rfl stateGas bal getterInitMemory_ptr
  -- The cached words are storage reads, equal under either access schedule.
  have token : ((afterSloadH sevm (mintLockedWorldH sevm b) 8).getStorVal sevm.currentTarget 6).toAdr.toB256 =
      mintRootToken0 ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩ b := by
    simp only [mintRootToken0, mintRootReserves, getStorVal_afterSloadH, getStorVal_afterSload,
      mintLockedWorldH_getStorVal]
  have reserve0 : reserve0Read ((mintLockedWorldH sevm b).getStorVal sevm.currentTarget 8) =
      mintRootReserve0 ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩ b := by
    rw [mintLockedWorldH_getStorVal]; rfl
  have reserve1 : reserve1Read ((mintLockedWorldH sevm b).getStorVal sevm.currentTarget 8) =
      mintRootReserve1 ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩ b := by
    rw [mintLockedWorldH_getStorVal]; rfl
  simp only [token, reserve0, reserve1] at request guarded
  refine ⟨?_, mint_balance_occurrence_of_request_cursorH .first request (.refl _) rfl stateGas⟩
  have keep : ∀ x, (mintRootFirstWorldH ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩ b).getCode x =
      (afterSloadH sevm (afterSloadH sevm (mintLockedWorldH sevm b) 8) 6).getCode x := fun x => by
    simp only [mintRootFirstWorldH, mintRootReservesH, Devm.getCode, Devm.getAcct, accountAccessH_state]
  rw [keep]
  exact guarded


theorem mint_three_occurrences_of_successH {sevm : Sevm} {b post W1 : Devm} {G : Nat}
    {A2 F : Sevm → Devm → Devm} (codeEq : sevm.code = code) (stateGas : sevm.benvStat.rules.stateGas = none)
    (bal : sevm.benvStat.rules.bal = none)
    (selector : Blanc.Sevm.selector sevm = 0x6a627842)
    (run : Exec 0 sevm (St b [] Mem.empty G) (.ok post))
    (worlds : MintRootWorldsH ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩ b W1 A2 F) :
    Nonempty (MintRootCallPositionsH ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩ b W1 A2 F) := by
  let root : Exec.Deriv := ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩
  obtain ⟨hW1, hA2, hF⟩ := worlds
  subst hW1
  obtain ⟨guarded0, ⟨first⟩⟩ := mint_first_guarded_occurrence_of_successH codeEq stateGas bal selector run
  have firstPtr : PtrMem 128 192 (balanceRequestMemory getterInitMemory sevm.currentTarget) :=
    balanceRequestMemory_ptr getterInitMemory_ptr sevm.currentTarget
  obtain ⟨out0, reply0, bound0, width0, answer0, guarded1, ⟨second⟩⟩ :=
    mint_second_occurrence_of_firstH first rfl stateGas bal getterInitMemory_ptr.wf firstPtr
  have secondWorld : A2 first.call.returned.sevm first.call.returned.devm =
      mintSecondWorldOfH first.call.returned.sevm first.call.returned.devm :=
    hA2 _ _ first.returned_sevm
  change ((mintSecondWorldOfH first.call.returned.sevm first.call.returned.devm).getCode _).size.toB256 ≠ 0
    at guarded1
  change MintBalanceOccurrence _ _ _ (mintSecondWorldOfH first.call.returned.sevm first.call.returned.devm)
    _ _ _ _ at second
  rw [← secondWorld] at guarded1 second
  have replyPtr := balanceReplyMemory_ptr out0 firstPtr
  have secondPtr : PtrMem 128 192
      (balanceRequestMemory (balanceReplyMemory getterInitMemory sevm.currentTarget out0)
        first.call.returned.sevm.currentTarget) :=
    balanceRequestMemory_ptr replyPtr first.call.returned.sevm.currentTarget
  have returnedSuccess : first.call.returned.exn = .ok post := first.returned_exn
  have returnedFork : first.call.returned.sevm.benvStat.rules.stateGas = none ∧ first.call.returned.sevm.benvStat.rules.bal = none := by
    rw [first.returned_sevm]; exact ⟨stateGas, bal⟩
  have low (word : B256) : (word &&& reserveMask112).toNat < 2 ^ 112 := by
    rw [show reserveMask112 = (2 ^ 112 - 1 : Nat).toB256 from rfl,
      PackedWord.lowMask_toNat word (by decide : 112 ≤ 256)]
    exact Nat.mod_lt _ (by decide)
  have reserve0Bound : (mintRootReserve0 root b).toNat < 2 ^ 112 := low _
  have reserve1Bound : (mintRootReserve1 root b).toNat < 2 ^ 112 := low _
  obtain ⟨out1, reply1, bound1, width1, answer1, cover0, cover1, ⟨fee⟩⟩ :=
    mint_fee_observation_of_secondH (F := F) (fun s d same => hF s d (same.trans first.returned_sevm))
      second returnedSuccess returnedFork.1 returnedFork.2 replyPtr.wf
      secondPtr reserve0Bound reserve1Bound
  exact ⟨⟨⟨rfl, hA2, hF⟩, first, guarded0, out0, reply0, bound0, width0, answer0,
    second, guarded1, out1, reply1, bound1, width1, answer1, cover0, cover1, fee⟩⟩


theorem MintRootCallPositionsH.final_no_exec {root : Exec.Deriv} {b W1 : Devm}
    {A2 F : Sevm → Devm → Devm}
    (r : MintRootCallPositionsH root b W1 A2 F) (stateGas : root.sevm.benvStat.rules.stateGas = none) :
    ∀ N, Exec.Deriv.ParentPrefix r.fee.occurrence.call.returned N → ∀ x,
      ¬ Ninst.At N.sevm.code N.pc (.exec x) := by
  have returnedEnv : r.fee.occurrence.call.returned.sevm = root.sevm :=
    (Cursor.parentStep_sevm r.fee.occurrence.call.edge).trans
      (r.fee.occurrence.sevm_eq.trans (r.second.returned_sevm.trans r.first.returned_sevm))
  exact mint_fee_suffix_no_execH r.fee.occurrence.placed r.fee.occurrence.tree
    r.fee.occurrence.continuations (by rw [returnedEnv]; exact stateGas)


end Blanc.Lift.UniswapV2Pair
