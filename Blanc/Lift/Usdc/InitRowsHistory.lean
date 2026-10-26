import Blanc.Lift.Usdc.InitReachV1
import Blanc.Lift.Usdc.ProxyWritesHistory

/-!
# Initializer writes at the Pair's rows, from the prefix walks

Every raw `SSTORE` node of an initializer frame (`UsdcInitFrame`) is the end of a reach of its
implementation code from entry `0` (`Reach.sstoreNode_pot`), so the prefix walks classify its
key: `KeysInit06` under `initialize` (V1 `InitReachV1.initV1_reach`, V2-line
`Init06.init_reach_V2`/`V2_1`/`V2_2`), `KeysInitV2` under `initializeV2`
(`InitReachV2.initV2_reach` and its V2_1/V2_2 twins), `KeysInitV2_2` under `initializeV2_2`
(`InitReachV2_2.initV2_2_reach`), or the stored word is zero. The classification holds at
every node of the frame, whatever its outcome.

`InitRowsApart` states, per initializer frame at `P`, that no tracked Pair row is a key of
these classes for that frame's own calldata: fixed slots, payload keys `keccak(slot) + j`
below the frame's decoded lengths, and `initializeV2_2`'s blacklist mapping keys. From it,
`ConfiguredHistoryTraceIn.initRowWritesNonInc` gives `InitRowWritesNonInc`, and
`usdc_pairAllowance_noIncrease_deployed_apart` is `usdc_pairAllowance_noIncrease_deployed`
with that premise in place of `InitRowWritesNonInc`.
-/

namespace Blanc.Lift.Usdc

open Jaune Blanc Blanc.Lift Blanc.ExecutionTrace

/-- The keys an initializer frame's code writes under its selector, read from the frame's
own calldata: `initialize`'s fixed slots and string payload keys, `initializeV2`'s, and
`initializeV2_2`'s (with its blacklist mapping keys), each under its own selector. Each decoded
length is capped at a bound the walks prove for any reached store: `2 ^ 32` from the solc 0.6
ABI decoders, `2 ^ 160` for `initialize` from V1's memory potential. -/
def InitKeys (sevm : Sevm) (key : B256) : Prop :=
  (initSelWord sevm = 0x3357162b ∧ Init06.KeysInit06 sevm key) ∨
    (initSelWord sevm = 0xd608ea64 ∧ KeysInitV2 sevm key) ∨
    (initSelWord sevm = 0x430239b4 ∧ InitReachV2_2.KeysInitV2_2 sevm key)

/-- **Initializer keys apart from the tracked rows (stated, frame-local).** For every raw
initializer frame at `P`, no tracked Pair row is one of the frame's `InitKeys`.

It is meant for a finite, explicit `Tr`. The fixed slots and mapping keys are apart from a
tracked row unless Keccak collides. The payload keys `keccak(s) + j` (`s ∈ {4, 5, 7}`) form
intervals from three constant bases, of at most `2 ^ 155` words under `initialize` and
`2 ^ 27` under the solc 0.6 decoders; keeping a tracked row out of them is interval
avoidance, decidable by arithmetic for an explicit `Tr`, not a hash-collision fact. -/
def InitRowsApart (P pair : Adr) (Tr : Adr → Prop) (frames : List Exec.Deriv) : Prop :=
  ∀ G ∈ frames, G.sevm.currentTarget = P → UsdcInitFrame G →
    ∀ g, Tr g → ¬ InitKeys G.sevm (allowSlot pair g)

theorem selV1T_root (sevm : Sevm) :
    selV1T.eval (WriteSite.Env.root sevm) = Blanc.Sevm.selector sevm := by
  rw [← dispatchWord_eq_selector]
  unfold Proxy.dispatchWord
  rw [B256.and_comm]
  simp only [selV1T, WriteSite.Term.eval, WriteSite.Op2.eval, WriteSite.Env.root, Sevm.dataWord]
  rfl

theorem selWord_eq_selector (sevm : Sevm) : initSelWord sevm = Blanc.Sevm.selector sevm := by
  unfold initSelWord Blanc.Sevm.selector
  rw [show Bytes.toB256 [0] = (0 : B256) from by decide,
    show (Bytes.toB256 [0xe0]).toNat = 224 from by decide]

theorem selV2T_root_selWord (sevm : Sevm) :
    selV2T.eval (WriteSite.Env.root sevm) = initSelWord sevm := by
  simp only [selV2T, WriteSite.Term.eval, WriteSite.Op2.eval, WriteSite.Env.root, initSelWord,
    Sevm.dataWord]
  rfl

/-- **Every `SSTORE` node of an initializer frame, classified.** At a node under a raw
initializer frame entered at pc `0` without state gas, with empty stack and memory and gas
below `2 ^ 256`, a successful `SSTORE` writes one of the frame's `InitKeys` or zero. -/
theorem initFrame_sstore {G N : Exec.Deriv} (hpc : G.pc = 0)
    (hsg : G.sevm.benvStat.rules.stateGas = none) (fresh : Exec.FreshEntry G.sevm G.devm)
    (gas : G.devm.gasMeasure < 2 ^ 256) (init : UsdcInitFrame G)
    (chain : Exec.Deriv.ParentPrefix G N) {w : Exec.StorageWrite}
    (found : Exec.Deriv.successfulSstore? N = some w) :
    InitKeys G.sevm w.key ∨ w.value = 0 := by
  obtain ⟨hat, rest, hstack⟩ := successfulSstore?_decoded found
  obtain ⟨stack, memory⟩ := fresh
  have erase : ∀ {s d n d'}, StepIn G s d n d' → Ninst.Run s d n d' := fun h => StepIn.toRun h
  have eraseP : ∀ {s d n d'}, FreePtr.PotStep (StepIn G) s d n d' → Ninst.Run s d n d' :=
    fun h => StepIn.toRun h.1
  have use : ∀ {K : B256 → Prop} {T : Conf}, InitStore K T → T.d = N.devm →
      ∀ {L : B256 → Prop}, (∀ k, K k → L k) → L w.key ∨ w.value = 0 := by
    intro K T h e L hL
    rw [← e] at hstack
    exact (h _ _ _ hstack).imp_left (hL _)
  rcases init with ⟨code, sel⟩ | ⟨code, sel⟩ | ⟨code, sel⟩ | ⟨code, sel⟩
  · obtain ⟨T, run, hT, e⟩ := Reach.sstoreNode_pot ImplV1.cert_check hpc code hsg stack memory
      gas chain hat
    have hs : Blanc.Sevm.selector G.sevm = 0x3357162b := by
      rw [← selV1T_root]
      exact List.mem_singleton.mp sel
    exact use (InitReachV1.initV1_reach erase hs run hT) e
      fun _ h => .inl ⟨(selWord_eq_selector _).trans hs, h⟩
  · obtain ⟨T, run, hT, e⟩ := Reach.sstoreNode_pot ImplV2.cert_check hpc code hsg stack memory
      gas chain hat
    change selV2T.eval _ ∈ [0x3357162b, 0xd608ea64] at sel
    rw [selV2T_root_selWord] at sel
    rcases List.mem_cons.mp sel with hs | hs
    · exact use (Init06.init_reach_V2 erase hs run hT) e fun _ h => .inl ⟨hs, h⟩
    · rw [List.mem_singleton] at hs
      exact use (InitReachV2.initV2_reach eraseP hs run hT) e fun _ h => .inr (.inl ⟨hs, h⟩)
  · obtain ⟨T, run, hT, e⟩ := Reach.sstoreNode_pot ImplV2_1.cert_check hpc code hsg stack
      memory gas chain hat
    change selV2T.eval _ ∈ [0x3357162b, 0xd608ea64] at sel
    rw [selV2T_root_selWord] at sel
    rcases List.mem_cons.mp sel with hs | hs
    · exact use (Init06.init_reach_V2_1 erase hs run hT) e fun _ h => .inl ⟨hs, h⟩
    · rw [List.mem_singleton] at hs
      exact use (InitReachV2_1.initV2_reach eraseP hs run hT) e fun _ h => .inr (.inl ⟨hs, h⟩)
  · obtain ⟨T, run, hT, e⟩ := Reach.sstoreNode_pot Impl.cert_check hpc code hsg stack memory
      gas chain hat
    change selV2T.eval _ ∈ [0x3357162b, 0x430239b4, 0xd608ea64] at sel
    rw [selV2T_root_selWord] at sel
    rcases List.mem_cons.mp sel with hs | hs
    · exact use (Init06.init_reach_V2_2 erase hs run hT) e fun _ h => .inl ⟨hs, h⟩
    rcases List.mem_cons.mp hs with hs | hs
    · exact use (InitReachV2_2.initV2_2_reach eraseP hs run hT) e
        fun _ h => .inr (.inr ⟨hs, h⟩)
    · rw [List.mem_singleton] at hs
      exact use (InitReachV2_2.initV2_reach eraseP hs run hT) e fun _ h => .inr (.inl ⟨hs, h⟩)

section History

variable {F : Fork → Prop} {cfg : ChainConfig} {checkpoint future : BlockChain}
  {P : Adr} {W : List UsdcDeployedEntry} {pair : Adr} {Tr : Adr → Prop}

/-- **`InitRowWritesNonInc` from the frame-local key separation.** -/
theorem ConfiguredHistoryTraceIn.initRowWritesNonInc
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F)
    (apart : InitRowsApart P pair Tr history.rawFrames) :
    InitRowWritesNonInc P pair Tr history.rawFrames := by
  intro G hG target init m chain w found tracked
  obtain ⟨hpc, -, hsg, fresh, gas⟩ := history.rawFrame_entryFacts capabilities G hG
  rcases initFrame_sstore hpc hsg fresh gas init chain found with keys | zero
  · obtain ⟨g, hg, hk⟩ := tracked
    exact (apart G hG target init g hg (hk ▸ keys)).elim
  · rw [zero]
    exact Nat.zero_le _

/-- **P1 with the initializers' writes discharged.** `usdc_pairAllowance_noIncrease_deployed`
with `InitRowsApart` (frame-local key separation of the initializer frames) in place of
`InitRowWritesNonInc`; every other premise is the same. -/
theorem ConfiguredHistoryTraceIn.usdc_pairAllowance_noIncrease_deployed_apart
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F) (bal : ∀ {fork}, F fork → fork.ruleSet.bal = none)
    (world : UsdcDeployedWorld history.BoundaryAt P W checkpoint.state)
    (admin : AdminUpgradesWithinFrom P W history.rawFrames history.rawNodes)
    (apartSlot : ImplSlotApart P history.rawNodes)
    (slotsApart : ProxySlotsApart pair Tr)
    (rowSep : UsdcRowSep P pair Tr history.rawFrames)
    (noPairException : NoPairExceptionWrites P pair Tr history.rawFrames history.rawNodes)
    (initApart : InitRowsApart P pair Tr history.rawFrames)
    {k : B256} (tracked : ∃ g, Tr g ∧ allowSlot pair g = k) :
    (∀ n ∈ history.rawNodes,
        ((n.devm.getStor P).get k).toNat ≤ ((checkpoint.state.getStor P).get k).toNat) ∧
      ((future.state.getStor P).get k).toNat ≤ ((checkpoint.state.getStor P).get k).toNat :=
  ConfiguredHistoryTraceIn.usdc_pairAllowance_noIncrease_deployed history capabilities bal world
    admin apartSlot slotsApart rowSep noPairException
    (ConfiguredHistoryTraceIn.initRowWritesNonInc history capabilities initApart) tracked

end History

end Blanc.Lift.Usdc
