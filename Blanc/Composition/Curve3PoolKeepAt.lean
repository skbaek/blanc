import Blanc.Composition.Curve3PoolCoinKeep
import Blanc.Lift.Curve3Crv.CommittedExec
import Blanc.Lift.Curve3Pool.Safe
import Blanc.Lift.Curve3Pool.Walk.ChildrenSel
import Blanc.Lift.Curve3Pool.HistoryMid

/-!
# The pool's keep premises at a frame whose coins and token are their bytes

* `tok_keeps`: a child at 3Crv keeps the foreign world, from 3Crv's bytes: its certificate executes only
  `STATICCALL`, to the identity precompile;
* `keepSel_of_world`: every child a walk can name keeps the pool (`KeepSel`), from `PoolWorld`;
* `children_static_of_callFree`: a non-static frame on a call-free selector enters only static children, so
  they keep the world whatever they run;
* `pool_keeps_of_world`: the two keep premises at a committed non-static pool frame. The six calling entries
  read their children off their walks; the other 32 enter only static ones.
-/

namespace Blanc.Composition.Curve3PoolCoinKeep

open Jaune Blanc Blanc.Lift Blanc.Lift.Curve3Pool Blanc.Lift.CurveCoins
open Blanc.Composition.Curve3Pool3CrvInstance

variable {sevm : Sevm} {b post : Devm}

/-- How a frame's parties enter its keep premises: the coins' world, and 3Crv's deployed bytes at entry. -/
structure PoolWorld (exc : Exec 0 sevm b (.ok post)) (dai usdc usdt tok : Adr) : Prop
    extends PoolCoinWorld exc dai usdc usdt where
  tokCode : b.getCode tok = Curve3Crv.code

theorem c3crv_code_ne : Curve3Crv.code.toList ≠ [] := by decide +kernel

theorem c3crv_not_delegation : ¬ isValidDelegation Curve3Crv.code := by decide +kernel

variable {exc : Exec 0 sevm b (.ok post)} {dai usdc usdt tok : Adr}

/-- **Every child at 3Crv keeps the foreign world**, on any selector. -/
theorem PoolWorld.tok_keeps (w : PoolWorld exc dai usdc usdt tok)
    (hcode : sevm.code = Curve3Pool.code) (hfork : HistFork sevm.benvStat.fork) :
    ∀ c ∈ Exec.childFrames exc, c.sevm.currentTarget = tok → ∀ a, tok ≠ a →
      ((b.getCode a).toList ≠ [] → ∀ x, (c.post.getStor a).get x = (c.pre.getStor a).get x) ∧
        c.post.getCode a = c.pre.getCode a := by
  intro c hc ht a hne
  obtain ⟨pc0, stat, -, cpre, ccode⟩ := poolChild_facts hcode hfork.stateGas_none exc c hc
  have code : c.sevm.code = Curve3Crv.code := by
    rw [ccode tok (by rw [w.tokCode]; exact c3crv_code_ne) (by rw [w.tokCode]; exact c3crv_not_delegation) ht,
      w.tokCode]
  obtain ⟨hst, hcd⟩ := frameKeepsForeign_of_staticOnly Curve3Crv.cert_check Curve3Crv.cert_onlyStaticcall c pc0
    code (by rw [stat]; exact hfork.stateGas_none) (a := a) (by rw [ht]; exact hne.symm)
  exact ⟨fun hna => hst (by rw [cpre a hna]; exact hna), hcd⟩

/-- The parties a frame's storage names: each coin is one of the three, the token is `tok`, and none of them
is the pool or `4`. -/
structure PartiesAt (σ : Stor) (pool dai usdc usdt tok : Adr) : Prop where
  coin : ∀ k : Fin 3, (σ.get (coinSlot k)).toAdr = dai ∨ (σ.get (coinSlot k)).toAdr = usdc ∨
    (σ.get (coinSlot k)).toAdr = usdt
  token : (σ.get tokenSlot).toAdr = tok
  coinNe : ∀ k : Fin 3, (σ.get (coinSlot k)).toAdr ≠ pool ∧ (σ.get (coinSlot k)).toAdr ≠ 4
  tokNe : tok ≠ pool ∧ tok ≠ 4
  apart : ∀ k : Fin 3, (σ.get (coinSlot k)).toAdr ≠ tok

/-- Each coin the storage names keeps the foreign world on the pool's selectors. -/
theorem PoolWorld.coin_keeps (w : PoolWorld exc dai usdc usdt tok) {σ : Stor}
    {pool : Adr} (hp : PartiesAt σ pool dai usdc usdt tok)
    (hcode : sevm.code = Curve3Pool.code) (hfork : HistFork sevm.benvStat.fork) (k : Fin 3) :
    ChildKeepsSel exc (σ.get (coinSlot k)).toAdr := by
  rcases hp.coin k with e | e | e <;> rw [e]
  · exact w.dai_keeps hcode hfork
  · exact w.usdc_keeps hcode hfork
  · exact w.usdt_keeps hcode hfork

/-- **Every child a walk can name keeps the pool.** -/
theorem keepSel_of_world (w : PoolWorld exc dai usdc usdt tok)
    (hp : PartiesAt (b.getStor sevm.currentTarget) sevm.currentTarget dai usdc usdt tok)
    (hcode : sevm.code = Curve3Pool.code) (hfork : HistFork sevm.benvStat.fork)
    (hpne : (b.getCode sevm.currentTarget).toList ≠ []) :
    KeepSel sevm (b.getStor sevm.currentTarget) (Exec.childFrames exc) := by
  rintro c hc (ht | ⟨⟨i, hi, ht⟩, sel⟩)
  · rw [hp.token] at ht
    have k := w.tok_keeps hcode hfork c hc ht
    exact ⟨(k _ hp.tokNe.1).1 hpne, (k _ hp.tokNe.2).2⟩
  · have k := w.coin_keeps hp hcode hfork ⟨i, hi⟩ c hc ht sel
    exact ⟨(k _ (hp.coinNe ⟨i, hi⟩).1).1 hpne, (k _ (hp.coinNe ⟨i, hi⟩).2).2⟩

/-- The two keep premises, when every child is one the walk can name. -/
theorem keeps_of_children_sel (w : PoolWorld exc dai usdc usdt tok)
    (hp : PartiesAt (b.getStor sevm.currentTarget) sevm.currentTarget dai usdc usdt tok)
    (hcode : sevm.code = Curve3Pool.code) (hfork : HistFork sevm.benvStat.fork)
    (hpne : (b.getCode sevm.currentTarget).toList ≠ [])
    (hall : ∀ c ∈ Exec.childFrames exc, PoolChildSel (b.getStor sevm.currentTarget) c) :
    PoolCallsKeep ⟨0, sevm, b, .ok post, exc⟩ ∧ PoolCoinCallsKeepToken ⟨0, sevm, b, .ok post, exc⟩ := by
  have K := keepSel_of_world w hp hcode hfork hpne
  refine ⟨fun c hc => (K c hc (hall c hc)).1, ?_⟩
  rintro c hc ⟨k, hk⟩ hct x
  have htokA : tokenAdr ⟨0, sevm, b, .ok post, exc⟩ = tok := hp.token
  rw [htokA] at hct ⊢
  rcases hall c hc with ht | ⟨-, sel⟩
  · exact absurd (ht.trans hp.token) hct
  · have hk' : c.sevm.currentTarget = ((b.getStor sevm.currentTarget).get (coinSlot k)).toAdr := hk
    exact ((w.coin_keeps hp hcode hfork k) c hc hk' sel tok (fun e => hct (hk'.trans e))).1
      (by rw [w.tokCode]; exact c3crv_code_ne) x

/-- A child of a pool frame that is static has a code address. -/
theorem poolChild_codeAddress (hsg : sevm.benvStat.rules.stateGas = none) :
    ∀ c ∈ Exec.childFrames exc, c.sevm.isStatic = true → c.sevm.codeAddress ≠ none := by
  intro c hc hs
  obtain ⟨N, f, rsm, pc', cevm, pp, hstep, henter, hsevm, -⟩ :=
    Exec.childFrames_spawnedAt_entry exc (.refl _) c hc
  have hNs : N.sevm = sevm := Blanc.Exec.Deriv.ParentPrefix.sevm_eq pp
  obtain ⟨x, -, hxs, -⟩ := Evm.step_spawn_inv hstep
  have hst : f.inner.isStatic = true := by
    rw [← Frame.enter_run_isStatic henter, ← hsevm]
    exact hs
  have hca := Xinst.step_spawn_codeAddress_of_static_noStateGas (by rw [hNs]; exact hsg) hxs hst
  obtain ⟨_, _, hcev⟩ := Frame.enter_run_inv henter
  rw [hsevm, hcev]
  exact hca

/-- The two keep premises, when every child is static. -/
theorem keeps_of_children_static (hfork : HistFork sevm.benvStat.fork)
    (hcode : sevm.code = Curve3Pool.code)
    (hpne : (b.getCode sevm.currentTarget).toList ≠ [])
    (htok : (b.getCode (tokenAdr ⟨0, sevm, b, .ok post, exc⟩)).toList ≠ [])
    (hall : ∀ c ∈ Exec.childFrames exc, c.sevm.isStatic = true) :
    PoolCallsKeep ⟨0, sevm, b, .ok post, exc⟩ ∧ PoolCoinCallsKeepToken ⟨0, sevm, b, .ok post, exc⟩ := by
  have keep : ∀ c ∈ Exec.childFrames exc, ∀ a, (b.getCode a).toList ≠ [] → ∀ x,
      (c.post.getStor a).get x = (c.pre.getStor a).get x := by
    intro c hc a hne x
    obtain ⟨-, stat, -, cpre, -⟩ := poolChild_facts hcode hfork.stateGas_none exc c hc
    exact (frameKeeps_of_static c (by rw [stat]; exact hfork.stateGas_none) (hall c hc)
      (poolChild_codeAddress hfork.stateGas_none c hc (hall c hc)) a).1 (by rw [cpre a hne]; exact hne) x
  exact ⟨fun c hc => keep c hc _ hpne, fun c hc _ _ => keep c hc _ htok⟩

/-- **A non-static frame on a call-free selector enters only static children**: its raw effect names no call. -/
theorem children_static_of_callFree {s : Curve3Pool.State} {e : Env} {o : Out}
    (hlen : 4 ≤ sevm.data.length) (hin : Sevm.selector sevm ∈ callFreeSels)
    (hstatic : sevm.isStatic = false)
    (hstep : step s e (decodeCall sevm) = some o)
    (hraw : RawEffect ⟨0, sevm, b, .ok post, exc⟩ post e o) :
    ∀ c ∈ Exec.childFrames exc, c.sevm.isStatic = true := by
  have hnil : o.calls = [] := step_calls_nil (decodeCall_free hlen hin) hstep
  have hcalls := hraw.calls hstatic
  rw [hnil] at hcalls
  have empty : CallsOf ⟨0, sevm, b, .ok post, exc⟩ = [] := by
    rw [hcalls]
    rfl
  intro c hc
  cases hs : c.sevm.isStatic with
  | true => rfl
  | false =>
    have := List.filterMap_eq_nil_iff.mp empty c hc
    simp only [hs, Bool.false_eq_true, ↓reduceIte, reduceCtorEq] at this

/-- **The keep premises at a committed non-static pool frame whose parties are their bytes.** -/
theorem pool_keeps_of_world {s : Curve3Pool.State}
    (hcode : sevm.code = Curve3Pool.code) (hfork : HistFork sevm.benvStat.fork)
    (hcd : sevm.data.length < 2 ^ 256) (hstack : b.stack = []) (hmem : b.memory = Mem.empty)
    (hgas : b.gasMeasure < 2 ^ 256) (hstatic : sevm.isStatic = false)
    (hpc : b.getCode sevm.currentTarget ≠ .empty)
    (hck : Checkpoint (b.getStor sevm.currentTarget) s) (hid : IdReadyH sevm b)
    (htok : ¬ sevm.benvStat.rules.isPrecomp ((b.getStor sevm.currentTarget).get tokenSlot).toAdr)
    (hcoin : ∀ k : Fin 3, ¬ sevm.benvStat.rules.isPrecomp ((b.getStor sevm.currentTarget).get (coinSlot k)).toAdr)
    (w : PoolWorld exc dai usdc usdt tok)
    (hp : PartiesAt (b.getStor sevm.currentTarget) sevm.currentTarget dai usdc usdt tok) :
    PoolCallsKeep ⟨0, sevm, b, .ok post, exc⟩ ∧ PoolCoinCallsKeepToken ⟨0, sevm, b, .ok post, exc⟩ := by
  have hpne : (b.getCode sevm.currentTarget).toList ≠ [] := ByteArray.toList_ne_nil_of_ne_empty hpc
  have K := keepSel_of_world w hp hcode hfork hpne
  have hx : XAt sevm post 0 (St b [] Mem.empty b.gasLeft) (Exec.childFrames exc) :=
    XAt.of_eq (St.self hstack hmem) (XAt.of_exec exc hgas)
  have ofAll := keeps_of_children_sel w hp hcode hfork hpne
  have hcoinN : ∀ i, i < 3 → ¬ sevm.benvStat.rules.isPrecomp
      (coinAt (b.getStor sevm.currentTarget) i).toAdr := fun i hi => hcoin ⟨i, hi⟩
  by_cases hlen : 4 ≤ sevm.data.length
  · by_cases hin : Sevm.selector sevm ∈ sels
    · rcases sels_split hin with h | h | h | h | h | h | h
      · obtain ⟨e, o, hstep, hraw⟩ := pool_frame_refines_callFree exc hcode hfork hlen hcd h hstack hmem hgas
          hck htok hcoin
        exact keeps_of_children_static hfork hcode hpne
          (by rw [show tokenAdr ⟨0, sevm, b, .ok post, exc⟩ = tok from hp.token, w.tokCode]; exact c3crv_code_ne)
          (children_static_of_callFree hlen h hstatic hstep hraw)
      · exact ofAll (al_children_sel checkedM hcode hfork hlen hcd h hck.abs htok hcoinN hpc hid K hx)
      · exact ofAll (ex_children_sel hcode hfork hlen hcd h hck.abs hcoin hpc hid K hx)
      · exact ofAll (rl_children_sel hcode hfork hlen hcd h htok hcoinN hpc hid K hx)
      · exact ofAll (rli_children_sel checkedM hcode hfork hlen hcd h hck.abs htok hcoinN hpc hid K hx)
      · exact ofAll (oc_children_sel checkedM hcode hfork hlen hcd h hck.abs htok
          (fun hj => by simpa only [coinSlot, toB256_toNat] using hcoin ⟨_, hj⟩) hpc hid K hx)
      · exact ofAll (wd_children_sel hcode hfork hlen hcd h hid hpc K hcoin hx)
    · exact absurd (decodeCall_miss fun s hs he => hin (he ▸ hs))
        (pool_other_fails exc hcode hcd hstack hmem hgas)
  · exact absurd (decodeCall_short (by omega))
      (pool_other_fails exc hcode hcd hstack hmem hgas)

end Blanc.Composition.Curve3PoolCoinKeep
