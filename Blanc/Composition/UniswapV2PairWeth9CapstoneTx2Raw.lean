import Blanc.Composition.UniswapV2PairWeth9CapstoneSwapRaw
import Blanc.Composition.UniswapV2PairWeth9Tx2
import Blanc.Composition.Weth9TokenOutputsTransfer
import Blanc.LockExclusion

/-!
# The raw frames of `tx2`'s swap frame

`tx2_swap_raw`: every raw frame the Pair's swap frame of the closed instance's second transaction
enters is WETH9's `transfer(trader, 996)`, `X.balanceOf(pair)` or `WETH9.balanceOf(pair)`, each called
by the Pair, each entering nothing further, each answering successfully (`true`, `1001000`,
`999004`).  The frame's own outcome is U10b's success.  This is what the trace-local HASH-T rows of
the closed history are computed from.
-/

namespace Blanc.Composition.UniswapV2PairWeth9Capstone

open Jaune Blanc Blanc.Lift Blanc.Lift.UniswapV2Pair Blanc.Composition.UniswapV2PairWeth9Instance

/-- WETH9's `transfer(trader, 996)` calldata, as the Pair stages it. -/
def tx2TransferData : Bytes :=
  abiSelectorBytes 0xa9059cbb ++
    ((0xffffffffffffffffffffffffffffffffffffffff : B256) &&& trader.toB256).toBytes ++
    (swapOut : B256).toBytes

/-- `balanceOf(pair)` calldata. -/
def tx2BalanceData : Bytes := ExternalOperation.encode (.balanceOf pair)

section Tokens

variable {sevm : Sevm} {b : Devm} {S : List B256} {M : Mem} {G : Nat}
  (h : Tx2Frame sevm (St b S M G))
include h

theorem tx2_tokenSlot {k : B256} (hk : k ≠ 12) :
    (afterSload sevm (mintLockedWorld sevm b) 8).getStorVal sevm.currentTarget k = w0PairStor.get k := by
  unfold mintLockedWorld
  rw [getStorVal_eq', getStor_eq', NodeWalk.afterSload_state, NodeWalk.afterSstore_state,
    NodeWalk.afterSload_state, h.target, State.setStorVal_getStor_self, Stor.get_set_ne _ (Ne.symm hk)]
  exact congrArg (fun s : Stor => s.get k) h.pairStor

theorem tx2_token0 : swapInitialToken0 sevm b = tokenX.toB256 := by
  unfold swapInitialToken0
  rw [tx2_tokenSlot h (by decide), w0PairStor_6]
  decide +kernel

theorem tx2_token1 : swapInitialToken1 sevm b = weth.toB256 := by
  unfold swapInitialToken1
  rw [tx2_tokenSlot h (by decide), w0PairStor_7]
  decide +kernel

end Tokens


/-- The raw roots of a run that enters nothing are the run itself. -/
theorem eq_root_of_rawFrameDescendants_nil {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out) (nil : Exec.rawFrameDescendants run = []) {d : Exec.Deriv}
    (mem : d ∈ Exec.rawFrameRoots run) : d.pc = pc ∧ d.sevm = sevm ∧ d.exn = out := by
  simp only [Exec.rawFrameRoots, nil, List.mem_singleton] at mem
  subst mem
  exact ⟨rfl, rfl, rfl⟩

theorem selector_of_data {s : Sevm} {data : Bytes} (h : s.data = data) :
    Sevm.selector s = Bytes.toB256 (data.sliceD 0 32 0) >>> 224 := by
  unfold Sevm.selector Sevm.dataWord
  rw [h]
  rfl

theorem shortCall_of_data {s : Sevm} {data : Bytes} (h : s.data = data) :
    Weth9.shortCall s ↔ data.length.toB256 < 4 := by
  unfold Weth9.shortCall
  rw [h]


/-- An entered call child at a callee whose code enters nothing (given the child's code and
fork) is its own only raw root. -/
theorem CallChild.root {node : Exec.Deriv} {target : Adr} {data rd : Bytes} {d : Exec.Deriv}
    {C : ByteArray} (c : CallChild node target data 0 rd d)
    (undelegated : getDelegatedCodeAddress (node.devm.getCode target) = none)
    (codeNode : node.devm.getCode target = C)
    (quiet : ∀ (m : Msg) (cd : Devm),
      m.code = C → m.data = data → m.benv.stat = node.sevm.benvStat →
      ∀ child : Exec 0 (initSevm (m.withBenv m.benv)) (initDevm (m.withBenv m.benv)) (.ok cd),
        Exec.rawFrameDescendants child = []) :
    ∃ (m : Msg) (cd : Devm)
      (_child : Exec 0 (initSevm (m.withBenv m.benv)) (initDevm (m.withBenv m.benv)) (.ok cd)),
      d.pc = 0 ∧ d.sevm = initSevm (m.withBenv m.benv) ∧ d.exn = .ok cd ∧
        m.currentTarget = target ∧ m.caller = node.sevm.currentTarget ∧ m.data = data ∧
        m.code = C ∧ m.benv.stat = node.sevm.benvStat ∧ cd.output = rd := by
  obtain ⟨m, cd, benv, tgt, caller, hdata, value, stat, code, out, after, child, mem⟩ := c
  rw [Msg.benvAfterTransfer_of_value_zero value] at after
  obtain rfl := (Except.ok.inj after).symm
  have hcode := (code undelegated).trans codeNode
  obtain ⟨dpc, dsevm, dexn⟩ :=
    eq_root_of_rawFrameDescendants_nil child (quiet m cd hcode hdata stat child) mem
  exact ⟨m, cd, child, dpc, dsevm, dexn, tgt, caller, hdata, hcode, stat, out⟩

theorem token20_code_ne_nil : VyperNonreentrantDeployed.Token20.code.toList ≠ [] := by
  rw [ByteArray.toList_eq_toList_data]
  exact List.cons_ne_nil _ _

/-- What a raw frame entered below `tx2`'s swap root is: one of the three callees, called by the
Pair at pc `0`, answering successfully. -/
def Tx2Callee (d : Exec.Deriv) : Prop :=
  d.pc = 0 ∧ d.sevm.caller = pair ∧
    ((d.sevm.currentTarget = weth ∧ d.sevm.data = tx2TransferData ∧
        ∃ cd, d.exn = .ok cd ∧ cd.output = (Nat.toB256 1).toBytes) ∨
      (d.sevm.currentTarget = tokenX ∧
        ∃ cd, d.exn = .ok cd ∧ Bytes.toB256 (cd.output.take 32) = 1001000) ∨
      (d.sevm.currentTarget = weth ∧ d.sevm.data = tx2BalanceData ∧
        ∃ cd, d.exn = .ok cd ∧ Bytes.toB256 (cd.output.take 32) = 999004))

section Swap

variable {sevm : Sevm} {b : Devm} {G : Nat} (h : Tx2Frame sevm (St b [] Mem.empty G))
include h

/-- The decoded balances of the swap's two queries are `1001000` and `999004`: the frame's `Sync`
log carries them, and U10b's run fixes the frame's logs. -/
theorem tx2_balances {post : Devm}
    (run : Exec 0 sevm (St b [] Mem.empty G) (.ok post))
    (r : SwapPhysicalResult ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩ b post) :
    r.balances.balance0 = 1001000 ∧ r.balances.balance1 = 999004 := by
  obtain ⟨P, execEq, -, -, -, -, logs, -⟩ := tx2_frame_success h
  have same : post = P :=
    Except.ok.inj (((exec_iff_exec_eq 0 sevm _ _).mp ⟨run⟩).symm.trans execEq)
  subst same
  obtain ⟨M, gas, image⟩ := r.image
  have postLogs : post.logs = r.balances.finalWorld.logs := by
    simpa only [St, Devm.setMach_logs] using congrArg (fun d : Devm => d.logs) image
  rw [SwapBalances.finalWorld, afterSstore_logs, logs_addLog,
    updateWorld_logs r.facts.bound0 r.facts.bound1, logs] at postLogs
  have split1 := List.append_inj'
    ((show [wethTransferLog, tx2SyncLog, tx2SwapLog] = [wethTransferLog, tx2SyncLog] ++ [tx2SwapLog]
      from rfl).symm.trans postLogs) rfl
  have split2 := List.append_inj'
    ((show [wethTransferLog, tx2SyncLog] = [wethTransferLog] ++ [tx2SyncLog] from rfl).symm.trans
      split1.1) rfl
  have syncEq := List.singleton_inj.mp split2.2
  have dataEq := congrArg Log.data syncEq
  simp only [tx2SyncLog, encodeWords, List.flatMap_cons, List.flatMap_nil, List.append_nil] at dataEq
  rw [show reserve0Read tx2Packed1 = 1001000 by decide +kernel,
    show reserve1Read tx2Packed1 = 999004 by decide +kernel] at dataEq
  have parts := List.append_inj dataEq (by rw [B256.length_toBytes, B256.length_toBytes])
  refine ⟨?_, ?_⟩
  · have e := congrArg Bytes.toB256 parts.1
    rw [B256.toB256_toBytes, B256.toB256_toBytes] at e
    exact e.symm
  · have e := congrArg Bytes.toB256 parts.2
    rw [B256.toB256_toBytes, B256.toB256_toBytes] at e
    exact e.symm

/-- **The raw frames of `tx2`'s swap frame.** -/
theorem tx2_swap_raw {out : Execution} (run : Exec 0 sevm (St b [] Mem.empty G) out) :
    (∃ post, out = .ok post ∧ post.output = []) ∧
      ∀ d ∈ Exec.rawFrameDescendants run, Tx2Callee d := by
  obtain ⟨P, execEq, -, -, -, -, -, -⟩ := tx2_frame_success h
  have outEq : out = .ok P := ((exec_iff_exec_eq 0 sevm _ out).mp ⟨run⟩).symm.trans execEq
  subst outEq
  obtain ⟨r⟩ := swap_physical_result h.code (tx2_fork h) (tx2_selector h.data) run
  refine ⟨⟨P, rfl, r.output.trans h.output⟩, ?_⟩
  have bals := tx2_balances h run r
  have fork := tx2_fork h
  have rootCode {N : Exec.Deriv}
      (chain : Exec.Deriv.ParentPrefix ⟨0, sevm, St b [] Mem.empty G, .ok P, run⟩ N)
      {a : Adr} {c : ByteArray} (hc : (St b [] Mem.empty G).state.getCode a = c)
      (ne : c.toList ≠ []) : N.devm.getCode a = c := by
    have cp := Blanc.Exec.Deriv.ParentPrefix.codePreserve chain a
      (by change ((St b [] Mem.empty G).state.getCode a).toList ≠ []; rw [hc]; exact ne)
    exact cp.trans hc
  intro d member
  rcases swap_rawFrameDescendants r.balances fork (tx2_amount0 h.data) (tx2_dataLength h.data)
      d member with ⟨actual, -, occ⟩ | occ | occ
  · -- WETH9's `transfer(trader, 996)`
    have nodeSevm : actual.step.occurrence.node.sevm = sevm :=
      actual.sevmEq.trans r.balances.optional.transfers.first.sevmEq
    have nodeFork : CoveredFork actual.step.occurrence.node.sevm.benvStat.fork := by
      rw [nodeSevm]; exact fork
    have occ' :=
      call_occChild actual.step (by rw [actual.input]; exact pref_append [_, _, _, _, _, _, _] _)
        actual.stack nodeFork occ
    have tok : (swapInitialToken1 sevm b &&& 0xffffffffffffffffffffffffffffffffffffffff).toAdr =
        weth := by
      rw [tx2_token1 h]; decide +kernel
    have codeNode : actual.step.occurrence.node.devm.getCode weth = Weth9.code :=
      rootCode actual.step.sameFrame h.wethCode (Weth9.weth9Sem.ne_nil rfl)
    have hdata : (actual.step.occurrence.node.devm.memory.read
        (r.balances.optional.transfers.first.ptr + 164).toNat (B256.toNat 68)).1 =
          tx2TransferData := by
      rw [actual.input, St.memory]
      refine actual.calldata.trans ?_
      show abiSelectorBytes 0xa9059cbb ++
        ((0xffffffffffffffffffffffffffffffffffffffff : B256) &&& swapRecipientWord sevm).toBytes ++
          (swapAmount1Out sevm).toBytes = _
      rw [tx2_recipientWord h.data, tx2_amount1 h.data]
      rfl
    rw [tok, hdata] at occ'
    obtain ⟨m, cd, child, dpc, dsevm, dexn, tgt, caller, mdata, mcode, mstat, out⟩ :=
      occ'.root (by rw [codeNode]; exact Weth9.getDelegatedCodeAddress_code) codeNode
        (fun m cd mcode mdata mstat child => weth9_rawFrameDescendants_nil child mcode
          (by change CoveredFork m.benv.stat.fork; rw [mstat]; exact nodeFork)
          (by rw [selector_of_data mdata]; decide +kernel))
    refine ⟨dpc, ?_, Or.inl ⟨?_, ?_, cd, dexn, ?_⟩⟩
    · rw [dsevm]
      change m.caller = pair
      rw [caller, nodeSevm]; exact h.target
    · rw [dsevm]; exact tgt
    · rw [dsevm]; exact mdata
    · exact Weth9Token.weth9_transfer_output (sevm := initSevm (m.withBenv m.benv))
        (pre := initDevm (m.withBenv m.benv)) (G := (m.withBenv m.benv).gas) mcode
        (by change CoveredFork m.benv.stat.fork; rw [mstat]; exact nodeFork)
        (by rw [shortCall_of_data (s := initSevm (m.withBenv m.benv)) mdata]; decide +kernel)
        (by rw [selector_of_data (s := initSevm (m.withBenv m.benv)) mdata]; decide +kernel) child
  · -- `X.balanceOf(pair)`
    have startSevm : r.balances.optional.callback.next.sevm = sevm :=
      r.balances.optional.callback.sevmEq.trans (r.balances.optional.transfers.second.sevmEq.trans
        r.balances.optional.transfers.first.sevmEq)
    have nodeSevm : r.balances.first.step.occurrence.node.sevm = sevm :=
      r.balances.first.sevmEq.trans startSevm
    have nodeFork : CoveredFork r.balances.first.step.occurrence.node.sevm.benvStat.fork := by
      rw [nodeSevm]; exact fork
    have occ' := staticcall_occChild r.balances.first.step
      (by rw [r.balances.first.input]; exact pref_append [_, _, _, _, _, _] _)
      r.balances.first.reply.stack nodeFork occ
    have tok : (swapTokenWord (swapInitialToken0 sevm b)).toAdr = tokenX := by
      rw [tx2_token0 h]; decide +kernel
    have codeNode : r.balances.first.step.occurrence.node.devm.getCode tokenX =
        VyperNonreentrantDeployed.Token20.code :=
      rootCode r.balances.first.step.sameFrame h.xCode token20_code_ne_nil
    have hdata : (r.balances.first.step.occurrence.node.devm.memory.read
        r.balances.optional.transfers.second.ptr.toNat (B256.toNat 36)).1 = tx2BalanceData := by
      rw [r.balances.first.input, St.memory]
      refine r.balances.first.calldata.trans ?_
      rw [startSevm, h.target]
      rfl
    rw [tok, hdata, r.balances.first.reply.returnData] at occ'
    obtain ⟨m, cd, child, dpc, dsevm, dexn, tgt, caller, mdata, mcode, mstat, out⟩ :=
      occ'.root (by rw [codeNode]; exact getDelegatedCodeAddress_token20) codeNode
        (fun m cd mcode mdata mstat child => token20_rawFrameDescendants_nil child mcode)
    refine ⟨dpc, ?_, Or.inr (Or.inl ⟨?_, cd, dexn, ?_⟩)⟩
    · rw [dsevm]
      change m.caller = pair
      rw [caller, nodeSevm]; exact h.target
    · rw [dsevm]; exact tgt
    · rw [out]; exact bals.1
  · -- `WETH9.balanceOf(pair)`
    have startSevm : r.balances.first.step.returned.sevm = sevm :=
      (Cursor.parentStep_sevm r.balances.first.step.edge).trans (r.balances.first.sevmEq.trans
        (r.balances.optional.callback.sevmEq.trans (r.balances.optional.transfers.second.sevmEq.trans
          r.balances.optional.transfers.first.sevmEq)))
    have nodeSevm : r.balances.second.step.occurrence.node.sevm = sevm :=
      r.balances.second.sevmEq.trans startSevm
    have nodeFork : CoveredFork r.balances.second.step.occurrence.node.sevm.benvStat.fork := by
      rw [nodeSevm]; exact fork
    have occ' := staticcall_occChild r.balances.second.step
      (by rw [r.balances.second.input]; exact pref_append [_, _, _, _, _, _] _)
      r.balances.second.reply.stack nodeFork occ
    have tok : (swapTokenWord (swapInitialToken1 sevm b)).toAdr = weth := by
      rw [tx2_token1 h]; decide +kernel
    have codeNode : r.balances.second.step.occurrence.node.devm.getCode weth = Weth9.code :=
      rootCode r.balances.second.step.sameFrame h.wethCode (Weth9.weth9Sem.ne_nil rfl)
    have hdata : (r.balances.second.step.occurrence.node.devm.memory.read
        r.balances.optional.transfers.second.ptr.toNat (B256.toNat 36)).1 = tx2BalanceData := by
      rw [r.balances.second.input, St.memory]
      refine r.balances.second.calldata.trans ?_
      rw [startSevm, h.target]
      rfl
    rw [tok, hdata, r.balances.second.reply.returnData] at occ'
    obtain ⟨m, cd, child, dpc, dsevm, dexn, tgt, caller, mdata, mcode, mstat, out⟩ :=
      occ'.root (by rw [codeNode]; exact Weth9.getDelegatedCodeAddress_code) codeNode
        (fun m cd mcode mdata mstat child => weth9_rawFrameDescendants_nil child mcode
          (by change CoveredFork m.benv.stat.fork; rw [mstat]; exact nodeFork)
          (by rw [selector_of_data (s := initSevm (m.withBenv m.benv)) mdata]; decide +kernel))
    refine ⟨dpc, ?_, Or.inr (Or.inr ⟨?_, ?_, cd, dexn, ?_⟩)⟩
    · rw [dsevm]
      change m.caller = pair
      rw [caller, nodeSevm]; exact h.target
    · rw [dsevm]; exact tgt
    · rw [dsevm]; exact mdata
    · rw [out]; exact bals.2

end Swap

end Blanc.Composition.UniswapV2PairWeth9Capstone
