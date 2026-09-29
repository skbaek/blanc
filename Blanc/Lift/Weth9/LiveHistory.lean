import Blanc.Lift.Weth9.LiveModel
import Blanc.Lift.Weth9.FootHistory

/-!
# Liveness at reachable states of the deployed WETH9

After **any** configured history from a checkpoint with a footprint (or from a deployment-shaped
checkpoint, `metadata` only), the future state carries the footprint `FootInv U` over the trace's
tracked keys (`weth9_history_footprint_universe`).  A fresh frame at that state then has everything the
frame-level liveness of `LiveWriters.lean` needs:

* `weth9_history_withdraw_live`: a holder with tracked balance `≥ wad` can `withdraw(wad)` to an
  externally owned account, at exactly `withdrawAnyGas`, ending in the storage with the balance debited —
  the footprint backs the ether the send needs;
* `weth9_history_deposit_live`, `weth9_history_transfer_live`: likewise `deposit()` (any value) and
  `transfer` of a tracked balance;
* `weth9_history_withdraw_live_deployed`: the withdraw case from a deployment-shaped checkpoint.

No history-level wrapper is stated for the model-accepted writers (`approve`, `transferFrom`): the
frame-level `weth9_*_model_live` (`LiveModel.lean`) apply at the future state with the footprint
`weth9_history_footprint_universe` supplies.

The frame is a fresh entry at the future state (`pre.state = future.state`), executing the deployed code
of the contract (`sevm.code` is the code at `ca`).
-/

namespace Blanc.Lift.Weth9

open Jaune Blanc Blanc.Lift
open Blanc.ExecutionTrace

theorem code_eq_of_toList {a : ByteArray} (h : a.toList = code.toList) : a = code := by
  rw [ByteArray.toList_eq_toList_data, ByteArray.toList_eq_toList_data] at h
  cases a with
  | mk d =>
    cases hk : code with
    | mk d' =>
      rw [hk] at h
      exact congrArg ByteArray.mk (Array.toList_inj.mp h)

/-- **A fresh frame at a reachable state**: it runs the deployed code, and the footprint of the future
state is a footprint of its world. -/
theorem history_frame {ca : Adr} {cfg : ChainConfig} {checkpoint future : BlockChain}
    {K₀ : Key → Prop}
    (trace : ConfiguredHistoryTrace cfg checkpoint future)
    (installed : some (checkpoint.state.getCode ca).toList = weth9Sem.image)
    (sumNof : SumNof checkpoint.state.bal)
    (initial : FootInv K₀ (checkpoint.state.getStor ca) (checkpoint.state.bal ca))
    (fresh : KeysFresh K₀ (historyTouchedKeys ca trace))
    {sevm : Sevm} {pre : Devm} (hca : sevm.currentTarget = ca) (hpre : pre.state = future.state)
    (hcode : sevm.code = future.state.getCode ca) :
    sevm.code = code ∧
      FootInv (historyKeyUniverse ca trace K₀) (Devm.getStor pre sevm.currentTarget)
        (pre.getBal sevm.currentTarget) := by
  obtain ⟨hc, -, hfoot⟩ := weth9_history_footprint_universe trace installed sumNof initial fresh
  subst hca
  refine ⟨?_, ?_⟩
  · have h : (future.state.getCode sevm.currentTarget).toList = code.toList :=
      (Option.some.inj hc)
    rw [hcode]
    exact code_eq_of_toList h
  · have e1 : Devm.getStor pre sevm.currentTarget = future.state.getStor sevm.currentTarget := by
      show pre.state.getStor _ = _
      rw [hpre]
    have e2 : pre.getBal sevm.currentTarget = future.state.bal sevm.currentTarget := by
      show (pre.state.get _).bal = (future.state.get _).bal
      rw [hpre]
    rw [e1, e2]
    exact hfoot

/-- **After any configured history, a holder can withdraw to an externally owned account, gas-exact.**
The caller is a tracked holder of the trace's universe whose stored balance covers `wad`; it has no code
and is no precompile.  At gas `G + withdrawAnyGas` with `811 ≤ G` the deployed code executes
`withdraw(wad)` successfully ending at gas `G`, debiting the caller's balance slot and no other. -/
theorem weth9_history_withdraw_live {ca : Adr} {cfg : ChainConfig} {checkpoint future : BlockChain}
    {K₀ : Key → Prop}
    (trace : ConfiguredHistoryTrace cfg checkpoint future)
    (installed : some (checkpoint.state.getCode ca).toList = weth9Sem.image)
    (sumNof : SumNof checkpoint.state.bal)
    (initial : FootInv K₀ (checkpoint.state.getStor ca) (checkpoint.state.bal ca))
    (fresh : KeysFresh K₀ (historyTouchedKeys ca trace))
    {sevm : Sevm} {pre : Devm} {G : Nat}
    (hca : sevm.currentTarget = ca) (hpre : pre.state = future.state)
    (hcode : sevm.code = future.state.getCode ca)
    (hfork : CoveredFork sevm.benvStat.fork)
    (h_static : sevm.isStatic = false) (h_value : sevm.value = 0)
    (h_sel : Sevm.selector sevm = wdSel)
    (h_len : 4 ≤ sevm.data.length) (h_len' : sevm.data.length < 2 ^ 256)
    (h_stack : pre.stack = []) (h_mem : pre.memory = Mem.empty) (h_depth : sevm.depth ≠ 0)
    (hholder : historyKeyUniverse ca trace K₀ (.bal sevm.caller))
    (hbal : Sevm.dataWord sevm 4 ≤ (future.state.getStor ca).get (balSlot sevm.caller))
    (h_eoa : (pre.getCode sevm.caller).size = 0)
    (h_prec : sevm.benvStat.rules.isPrecomp sevm.caller = false)
    (h_gas : pre.gasLeft = G + withdrawAnyGas sevm pre) (hG : 811 ≤ G) :
    ∃ post, exec ⟨0, sevm, pre⟩ = .ok post ∧ post.gasLeft = G ∧ post.output = pre.output ∧
      Devm.getStor post ca = (future.state.getStor ca).set (balSlot sevm.caller)
        ((future.state.getStor ca).get (balSlot sevm.caller) - Sevm.dataWord sevm 4) ∧
      ∀ a, a ≠ ca → Devm.getStor post a = future.state.getStor a := by
  obtain ⟨hc, hinv⟩ := history_frame trace installed sumNof initial fresh hca hpre hcode
  have e1 : ∀ a, Devm.getStor pre a = future.state.getStor a := fun a => by
    show pre.state.getStor a = _
    rw [hpre]
  have hle : Sevm.dataWord sevm 4 ≤ pre.getStorVal sevm.currentTarget (balSlot sevm.caller) := by
    subst hca
    show Sevm.dataWord sevm 4 ≤ (Devm.getStor pre sevm.currentTarget).get (balSlot sevm.caller)
    rw [e1]; exact hbal
  have h_eth : ¬ (pre.getAcct sevm.currentTarget).bal < Sevm.dataWord sevm 4 := by
    intro hlt
    have h1 := B256.toNat_lt_toNat hlt
    have h2 := B256.toNat_le_toNat hle
    have hb := hinv.balance_le (by subst hca; exact hholder)
    have h3 : (pre.getStorVal sevm.currentTarget (balSlot sevm.caller)).toNat ≤
        (pre.getAcct sevm.currentTarget).bal.toNat := hb
    omega
  obtain ⟨post, hex, hg, ho, hst, hother⟩ := weth9_withdraw_any_live hc hfork h_static h_value h_sel
    h_len h_len' h_stack h_mem h_depth hle h_eoa h_prec h_eth h_gas hG
  subst hca
  refine ⟨post, hex, hg, ho, ?_, ?_⟩
  · rw [hst, e1]
    have e3 : pre.getStorVal sevm.currentTarget (balSlot sevm.caller) =
        (future.state.getStor sevm.currentTarget).get (balSlot sevm.caller) := by
      show (Devm.getStor pre sevm.currentTarget).get _ = _
      rw [e1]
    rw [e3]
  · intro a ha
    rw [hother a ha, e1]


/-- **After any configured history, `deposit()` is live, gas-exact, at the future state.** -/
theorem weth9_history_deposit_live {ca : Adr} {cfg : ChainConfig} {checkpoint future : BlockChain}
    {K₀ : Key → Prop}
    (trace : ConfiguredHistoryTrace cfg checkpoint future)
    (installed : some (checkpoint.state.getCode ca).toList = weth9Sem.image)
    (sumNof : SumNof checkpoint.state.bal)
    (initial : FootInv K₀ (checkpoint.state.getStor ca) (checkpoint.state.bal ca))
    (fresh : KeysFresh K₀ (historyTouchedKeys ca trace))
    {sevm : Sevm} {pre : Devm} {G : Nat}
    (hca : sevm.currentTarget = ca) (hpre : pre.state = future.state)
    (hcode : sevm.code = future.state.getCode ca)
    (hfork : CoveredFork sevm.benvStat.fork) (h_static : sevm.isStatic = false)
    (h_sel : Sevm.selector sevm = dpSel)
    (h_len : 4 ≤ sevm.data.length) (h_len' : sevm.data.length < 2 ^ 256)
    (h_stack : pre.stack = []) (h_mem : pre.memory = Mem.empty)
    (h_gas : pre.gasLeft = G + depositGas sevm pre) (hG : 844 ≤ G) :
    ∃ post, exec ⟨0, sevm, pre⟩ = .ok post ∧ post.gasLeft = G ∧ post.output = pre.output ∧
      Devm.getStor post ca = (future.state.getStor ca).set (balSlot sevm.caller)
        ((future.state.getStor ca).get (balSlot sevm.caller) + sevm.value) := by
  obtain ⟨hc, -⟩ := history_frame trace installed sumNof initial fresh hca hpre hcode
  have e1 : ∀ a, Devm.getStor pre a = future.state.getStor a := fun a => by
    show pre.state.getStor a = _
    rw [hpre]
  obtain ⟨post, hex, hg, ho, hst⟩ := weth9_deposit_live hc hfork h_static h_sel h_len h_len'
    h_stack h_mem h_gas hG
  subst hca
  exact ⟨post, hex, hg, ho, by rw [hst, e1]⟩

/-- **After any configured history, a holder can `transfer` a tracked balance, gas-exact.** -/
theorem weth9_history_transfer_live {ca : Adr} {cfg : ChainConfig} {checkpoint future : BlockChain}
    {K₀ : Key → Prop}
    (trace : ConfiguredHistoryTrace cfg checkpoint future)
    (installed : some (checkpoint.state.getCode ca).toList = weth9Sem.image)
    (sumNof : SumNof checkpoint.state.bal)
    (initial : FootInv K₀ (checkpoint.state.getStor ca) (checkpoint.state.bal ca))
    (fresh : KeysFresh K₀ (historyTouchedKeys ca trace))
    {sevm : Sevm} {pre : Devm} {G : Nat}
    (hca : sevm.currentTarget = ca) (hpre : pre.state = future.state)
    (hcode : sevm.code = future.state.getCode ca)
    (hfork : CoveredFork sevm.benvStat.fork)
    (h_static : sevm.isStatic = false) (h_value : sevm.value = 0)
    (h_sel : Sevm.selector sevm = trSel)
    (h_len : 4 ≤ sevm.data.length) (h_len' : sevm.data.length < 2 ^ 256)
    (h_stack : pre.stack = []) (h_mem : pre.memory = Mem.empty)
    (hbal : Sevm.dataWord sevm 36 ≤ (future.state.getStor ca).get (balSlot sevm.caller))
    (h_gas : pre.gasLeft = G + transferGas sevm pre) (hG : 353 ≤ G) :
    ∃ post, exec ⟨0, sevm, pre⟩ = .ok post ∧ post.gasLeft = G ∧
      post.output = (1 : B256).toBytes ∧
      xferStorStep (future.state.getStor ca) sevm.caller sevm.caller (Sevm.dataWord sevm 4).toAdr
        (Sevm.dataWord sevm 36) = some (Devm.getStor post ca) := by
  obtain ⟨hc, -⟩ := history_frame trace installed sumNof initial fresh hca hpre hcode
  have e1 : ∀ a, Devm.getStor pre a = future.state.getStor a := fun a => by
    show pre.state.getStor a = _
    rw [hpre]
  have hle : Sevm.dataWord sevm 36 ≤ pre.getStorVal sevm.currentTarget (balSlot sevm.caller) := by
    subst hca
    show Sevm.dataWord sevm 36 ≤ (Devm.getStor pre sevm.currentTarget).get (balSlot sevm.caller)
    rw [e1]; exact hbal
  obtain ⟨post, hex, hg, ho, hst⟩ := weth9_transfer_live hc hfork h_static h_value h_sel h_len
    h_len' h_stack h_mem hle h_gas hG
  subst hca
  exact ⟨post, hex, hg, ho, by rw [← e1]; exact hst⟩

end Blanc.Lift.Weth9
