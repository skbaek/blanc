import Blanc.Composition.Curve3Pool3CrvCapstoneTx
import Blanc.Composition.Curve3Pool3CrvWorldAgrees
import Blanc.Composition.Curve3Pool3CrvTraceEnv
import Blanc.Composition.Curve3Pool3CrvU3
import Blanc.ExecutionHistoryFrameTime

/-!
# U9(b): the closed 3pool–3Crv instance — one signed `exchange` in one configured BPO2 block

`curve3pool_closed_agreeing` (universal form): for every canonical world `st` with representable
total ether that agrees with `P0` on the touched accounts (`AgreesP0`), the configured BPO2 block
with the signed type-2 `exchange(0, 1, 100, 0)` (`signedExchangeTx`) is a valid state transition
from the checkpoint at `st`, and on a configured history of it the composed U3 headline
(`pool_3crv_u3`) applies with every hypothesis discharged — the code premises, the joint
pool–3Crv checkpoint (U9(a)'s checker), the fresh 3Crv keys (no frame runs at 3Crv), the pool's
trace premises (`ex_poolTraceEnv`) — and its first replayed invocation is the swap:

* the decoded call is `exchange(0, 1, 100, 0)` at `poolState`, the model's step leaves
  `poolState1` (balances `[1100, 1868, 3000]`) and pulls 100 of coin 0, pushes `a > 0` of coin 1
  (the swap moves a positive amount);
* the U3 bounds hold at 3Crv's ledger supplies, the supply is unchanged (`exchange` makes no 3Crv
  call), and `get_virtual_price`'s `D` rises strictly (22177905188247 → 22178770202300): `D/T`
  strictly increases from the fee.

The coins' answers are `Token20`'s code (`token20_coinPullOkAt`, `token20_coinPushOkAt`), not
premises; the frame is `exchange_live` instantiated (`ex_frame_live`).
`curve3pool_closed_instance` is the concrete world `P0`.
-/

namespace Blanc.Composition.Curve3Pool3CrvInstance

open Jaune Blanc Blanc.Lift Blanc.ExecutionTrace Blanc.BlockForward
open Blanc.Composition.Curve3Pool3CrvJoint
open Blanc.Composition.Curve3PoolSupply (supplyAt pool_3crv_u3)
open Blanc.Lift.Curve3Pool (PoolInvocation PoolRun poolSubtreeFrames)
open Blanc.Lift.Weth9.ClosedInstance (config checkpoint input systemAddresses SystemCodes
  systemCode)

/-- A settled frame of a configured history is one of its raw frames. -/
theorem history_rawFrames_of_settled {cfg : ChainConfig} {pre post : BlockChain}
    (trace : ConfiguredHistoryTrace cfg pre post) (f : Exec.Frame)
    (h : f ∈ trace.settledFrames) : Exec.Frame.rootDeriv f ∈ trace.rawFrames := by
  induction trace with
  | refl => simp only [ConfiguredHistoryTrace.settledFrames, List.not_mem_nil] at h
  | step prior block ih =>
    simp only [ConfiguredHistoryTrace.settledFrames, ConfiguredHistoryTrace.rawFrames,
      List.mem_append] at h ⊢
    rcases h with h | h
    · exact .inl (ih h)
    · exact .inr (block.mem_rawFrames_of_settled f h)

/-- The model's `exchange(0, 1, 100, 0)` step is its `exchange`. -/
theorem step_exchange {s : Curve3Pool.State} {e : Curve3Pool.Env} {o : Curve3Pool.Out}
    (h : Curve3Pool.step s e (.exchange 0 1 100 0) = some o) :
    Curve3Pool.exchange s e 0 1 100 0 = some o := by
  have h' : (if e.value = 0 then Curve3Pool.body s e (.exchange 0 1 100 0) else none) = some o := h
  split_ifs at h' with hv
  simp only [Curve3Pool.body, Curve3Pool.idx, show (0 : Nat) < 3 from by decide,
    show (1 : Nat) < 3 from by decide, ↓reduceDIte, Option.bind_eq_bind, Option.bind_some] at h'
  exact h'

theorem systemAddresses_ne_coin : ∀ a ∈ systemAddresses, ∀ k : Fin 3, exCoinAdr k ≠ a := by
  decide +kernel

theorem systemCode_ne_nil : systemCode.toList ≠ [] := by decide +kernel

theorem systemCode_not_delegation : ¬ isValidDelegation systemCode := by
  intro h
  have h1 := h.1
  revert h1
  decide +kernel

/-- **What the closed block does on `st`** (see the module note). -/
def ClosedExchangeOutcome (st : Jaune.State) : Prop :=
  ∃ (s1 : Jaune.State) (bout : BlockOutput),
    stateTransitionUsing config (checkpoint st)
        (oneTxBlock signedExchangeTx st s1 (requestsOutput bout [] [])) =
      .ok (oneTxChain signedExchangeTx st s1 (requestsOutput bout [] [])) ∧
    ∃ (trace : ConfiguredHistoryTrace config (checkpoint st)
        (oneTxChain signedExchangeTx st s1 (requestsOutput bout [] [])))
      (i : PoolInvocation) (rest : List PoolInvocation),
      (i :: rest).flatMap (fun j => poolSubtreeFrames poolAddr j.frame) =
        Curve3Pool.committedPoolFrames poolAddr trace ∧
      (∀ j ∈ i :: rest, j.Authentic poolAddr) ∧
      Curve3Pool.decodeCall i.frame.sevm = .exchange 0 1 100 0 ∧
      ∃ o, Curve3Pool.step poolState i.env (Curve3Pool.decodeCall i.frame.sevm) = some o ∧
        Curve3Pool.RawEffect (Exec.Frame.rootDeriv i.frame) i.frame.post i.env o ∧
        Curve3Pool.U3Ledger poolState i.env (Curve3Pool.decodeCall i.frame.sevm) o
          (supplyAt c3crvAddr i.frame.pre.state) (supplyAt c3crvAddr i.frame.post.state) ∧
        o.state = poolState1 ∧
        (∃ a, o.calls = [.pull 0 i.env.caller 100, .push 1 i.env.caller a] ∧ 0 < a) ∧
        supplyAt c3crvAddr i.frame.post.state = supplyAt c3crvAddr i.frame.pre.state ∧
        ∃ D D', Curve3Pool.vDChk poolState i.env.time = some D ∧
          Curve3Pool.vDChk o.state i.env.time = some D' ∧ D < D'

/-- **U9(b), universal form**: every canonical world with representable total ether agreeing with
`P0` on the touched accounts. -/
theorem curve3pool_closed_agreeing {st : Jaune.State} (canonical : st.Canonical)
    (bound : SumNof st.bal) (ag : AgreesP0 st) : ClosedExchangeOutcome st := by
  have ctx := exTxContext_of_agrees ag
  have fork := ex_fork ctx
  obtain ⟨s1, bout, run, requests, gas⟩ := ex_transaction ctx
  -- the system fixture after the block
  obtain ⟨t0⟩ := exists_transactionTrace run fork
  obtain ⟨sevm0, b0, post0, hf0, exc0, hraw0, -⟩ := ex_trace_raw ctx t0
  have afterCodes : SystemCodes s1 := by
    intro a ha
    have keep := (t0.codeAt_keep fork (a := a)
      (fun auth hm => absurd hm (by
        rw [show signedExchangeTx.auths = [] from rfl]; exact List.not_mem_nil))
      (by
        intro root member _
        rw [hraw0] at member
        rcases List.mem_cons.mp member with rfl | hd
        · show sevm0.currentTarget ≠ a
          rw [hf0.target]
          exact Ne.symm (systemAddresses_ne a ha).1
        · obtain ⟨c, -, ⟨k, hk⟩, hrs, -, -⟩ := exFrame_raw hf0 exc0 root hd
          rw [hrs, hk]
          show exCoin sevm0 b0 k ≠ a
          rw [exFrame_coin hf0 k]
          exact systemAddresses_ne_coin a ha k)
      (by change (st.getCode a).toList ≠ []
          rw [systemCodes_of_agrees ag a ha]; exact systemCode_ne_nil)
      (by change ¬ isValidDelegation (st.getCode a)
          rw [systemCodes_of_agrees ag a ha]; exact systemCode_not_delegation)
      Std.HashSet.not_mem_emptyWithCapacity).2
    rw [keep]
    exact systemCodes_of_agrees ag a ha
  -- the configured history
  obtain ⟨transition, trace, t1, sysRaw, sysRaw', hraw, hsysEq, hnoAuth, hsys, hset⟩ :=
    oneTx_history canonical bound (systemCodes_of_agrees ag) afterCodes run requests gas
  obtain ⟨sevm, b, post, hf, exc, hraw1, f, hfm, hfs, -, -⟩ := ex_trace_raw ctx t1
  have hrawFull : trace.rawFrames = sysRaw ++ Exec.rawFrameRoots exc ++ sysRaw' := by
    rw [hraw, hraw1]
  -- the headline's premises
  have env := ex_poolTraceEnv trace exc hf hrawFull hsys hsysEq (code4_of_agrees ag)
    (hnoAuth rfl 4)
  have fresh : Lift.Curve3Crv.FreshKeys (c3Keys c3Rows) (Lift.Curve3Crv.historyTouchedKeys c3crvAddr trace) := by
    rw [ex_touched_c3crv trace exc hf hrawFull hsys]
    exact ⟨fun k h => absurd h List.not_mem_nil, fun k h => absurd h List.not_mem_nil⟩
  obtain ⟨invs, obs, auth, -, per⟩ := pool_3crv_u3 trace (poolInstalled_of_agrees ag)
    (c3crvInstalled_of_agrees ag) (joint_of_agrees ag) fresh env (by decide +kernel)
  -- the exchange frame is a committed pool frame, so there is an invocation
  have hfS : f ∈ trace.settledFrames := hset f hfm
  have hobsf : f ∈ Curve3Pool.committedPoolFrames poolAddr trace := by
    unfold Curve3Pool.committedPoolFrames
    refine List.mem_flatMap.mpr ⟨f, hfS, ?_⟩
    unfold Curve3Pool.poolFrameObs
    rw [ite_eq_left ⟨by rw [hfs]; exact hf.target, by rw [hfs]; exact hf.static⟩]
    exact List.mem_singleton_self f
  cases invs with
  | nil =>
    rw [← obs, List.flatMap_nil] at hobsf
    exact absurd hobsf List.not_mem_nil
  | cons i rest =>
  -- the first invocation is the exchange frame
  have hi : i ∈ i :: rest := List.mem_cons_self
  obtain ⟨blk, hblk, -⟩ := Curve3Pool.pool_invocation_time obs hi (auth i hi)
  have hiS : i.frame ∈ trace.settledFrames := by
    rw [← trace.blockFrames_map_snd]
    exact List.mem_map.mpr ⟨_, hblk, rfl⟩
  have hiR := history_rawFrames_of_settled trace _ hiS
  have htgt : (Exec.Frame.rootDeriv i.frame).sevm.currentTarget = poolAddr := (auth i hi).2.2.1
  have hroot : Exec.Frame.rootDeriv i.frame = ⟨0, sevm, b, .ok post, exc⟩ := by
    rcases ex_trace_targets trace exc hf hrawFull hsys _ hiR with h | h | ⟨k, hk, -⟩
    · rw [htgt] at h
      exact absurd rfl (systemAddresses_ne _ h).1
    · exact h
    · rw [htgt] at hk
      exact absurd hk.symm (exCoinAdr_ne k).1
  have hsv : i.frame.sevm = sevm := congrArg Exec.Deriv.sevm hroot
  have hdec : Curve3Pool.decodeCall i.frame.sevm = .exchange 0 1 100 0 := by
    rw [hsv]; exact exFrame_decode hf
  obtain ⟨-, -, o, hstep, hraweff, -, hafter, hledger⟩ :=
    per [] i rest poolState rfl (PoolRun.nil _)
  have hex : Curve3Pool.exchange poolState i.env 0 1 100 0 = some o := by
    rw [hdec] at hstep; exact step_exchange hstep
  obtain ⟨hstate, hcalls⟩ := ex_model_step hex
  refine ⟨s1, bout, transition, trace, i, rest, obs, auth, hdec, o, hstep, hraweff, hledger, hstate,
    ⟨132, hcalls, by decide⟩, ?_, ?_⟩
  · rw [hcalls] at hafter
    exact hafter.symm
  · rw [hstate]
    exact ex_model_D i.env.time

/-- **U9(b), the concrete instance**: the synthetic world `P0`. -/
theorem curve3pool_closed_instance : ClosedExchangeOutcome P0 :=
  curve3pool_closed_agreeing p0_canonical p0_sumNof p0_agrees

end Blanc.Composition.Curve3Pool3CrvInstance
