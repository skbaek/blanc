import Blanc.Composition.Curve3PoolKeepAt
import Blanc.ExecutionMidHistoryInOwnCode
import Blanc.ExecutionInCodeImage
import Blanc.Lift.RetainedTargetCompleteness
import Blanc.Lift.Usdc.EntryChainSettled

/-!
# `PoolKeepAt` over a history in which the coins are their bytes

* `PartyWords`: the words a pool's coins and token hold name the three coins and the token, apart;
* `settledFrames_children`: a settled frame's committed children are settled;
* `FramesHold`: what the proof reads at each settled frame: the four codes, and the two operator premises;
* `pool_keepAt_of_frames`: `PoolKeepAt` at every settled pool frame, from `FramesHold`;
* `CoinsHold`: `FramesHold`'s premises as stated of the history: DAI's and USDT's code at its start, USDC's code
  at every settled frame, and the operators' `usdcImpl` and `usdtLive`, each at the settled frames it reaches.
  A frame inside a reverted parent is not settled, so a rolled-back upgrade is not read: a scan of the logs
  sees what these premises range over;
* `framesHold_of_coins`: `FramesHold`, certified bytes staying installed: `InstalledCert` for DAI, USDT and 3Crv.
-/

namespace Blanc.Composition.Curve3PoolCoinKeep

open Jaune Blanc Blanc.ExecutionTrace Blanc.Lift Blanc.Lift.Curve3Pool Blanc.Lift.CurveCoins

/-- The words of a pool's coins and token name the three coins and the token, none the pool or `4`. -/
structure PartyWords (cs : V3) (tokw : Nat) (pool dai usdc usdt tok : Adr) : Prop where
  coin : ∀ k : Fin 3, adrOf (cs.get k) = dai ∨ adrOf (cs.get k) = usdc ∨ adrOf (cs.get k) = usdt
  token : adrOf tokw = tok
  coinNe : ∀ k : Fin 3, adrOf (cs.get k) ≠ pool ∧ adrOf (cs.get k) ≠ 4
  tokNe : tok ≠ pool ∧ tok ≠ 4
  apart : ∀ k : Fin 3, adrOf (cs.get k) ≠ tok

section

variable {cfg : ChainConfig} {start : Benv} {future : BlockChain}

/-- **A settled frame's committed children are settled.** -/
theorem settledFrames_children (trace : MidHistoryTraceIn HistFork cfg start future) {f c : Exec.Frame}
    (member : f ∈ trace.settledFrames) (hc : c ∈ Exec.childFrames f.run) : c ∈ trace.settledFrames := by
  obtain ⟨b, a, split⟩ := List.append_of_mem member
  have split' := split
  rw [trace.settledFrames_eq] at split'
  obtain ⟨r, rest⟩ := (rootFrames_forest split').1
  rw [split, rest]
  exact List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_append_left _
    (Exec.mem_descendantFrames_of_mem_childFrames f.run c hc)))

/-- **A committed proxy frame on the pool's selectors has a caller other than the admin word.** -/
theorem usdc_child_notAdmin (c : Exec.Frame) (pc0 : c.pc = 0) (code : c.sevm.code = Usdc.Proxy.code)
    (hsg : c.sevm.benvStat.rules.stateGas = none) (bal : c.sevm.benvStat.rules.bal = none)
    (sel : PoolCoinSel (Blanc.Sevm.selector c.sevm)) :
    c.sevm.caller ≠ Usdc.adminOf c.pre.state c.sevm.currentTarget := by
  obtain ⟨cpc, sevm, pre, out, run, committed⟩ := c
  dsimp only at pc0 code hsg bal sel ⊢
  subst pc0
  cases out with
  | error e => simp only [Execution.commits, Bool.false_eq_true] at committed
  | ok post =>
    refine Usdc.proxy_notAdmin run code hsg bal fun hin => ?_
    rcases sel with h | h | h <;> rw [h] at hin <;> exact absurd hin (by decide)

/-- What the proof reads at each settled frame of the history. -/
structure FramesHold (trace : MidHistoryTraceIn HistFork cfg start future) (dai usdc usdt tok : Adr) : Prop where
  code : ∀ f ∈ trace.settledFrames, f.pre.getCode dai = Dai.code ∧ f.pre.getCode usdc = Usdc.Proxy.code ∧
    f.pre.getCode usdt = Usdt.code ∧ f.pre.getCode tok = Curve3Crv.code
  /-- Circle's proxy admin: at every settled proxy frame not called by the admin word, the implementation word is
  certified. -/
  usdcImpl : Usdc.CertifiedSettled usdc trace.settledFrames
  /-- Tether's owner: at every settled non-static frame at USDT, USDT is not deprecated. -/
  usdtLive : ∀ f ∈ trace.settledFrames, f.sevm.currentTarget = usdt → f.sevm.isStatic = false →
    Usdt.flag20 ((Devm.getStor f.pre usdt).get 10) = 0

/-- **`PoolKeepAt` at every settled pool frame of a history in which the coins and the token are their bytes.** -/
theorem pool_keepAt_of_frames {checkpoint : BlockChain} {pool dai usdc usdt tok : Adr} {cs : V3} {tokw : Nat}
    {full : ConfiguredHistoryTraceIn HistFork cfg checkpoint future}
    {trace : MidHistoryTraceIn HistFork cfg start future}
    (facts : PoolMidFacts full trace pool cs tokw) (words : PartyWords cs tokw pool dai usdc usdt tok)
    (frames : FramesHold trace dai usdc usdt tok) :
    ∀ f ∈ trace.settledFrames, f.sevm.currentTarget = pool → PoolKeepAt cs tokw f := by
  intro f member target s hcode hpc hstatic hck hq
  have raw : Exec.Frame.rootDeriv f ∈ trace.rawFrames := trace.mem_rawFrames_of_mem_settledFrames f member
  obtain ⟨⟨hstack, hmem⟩, hcd, hgas, hid, hcs, htk, -⟩ := facts.entry raw target
  obtain ⟨hpc0, hfork⟩ := trace.rootEntryIn _ raw
  obtain ⟨cdai, cusdc, cusdt, ctok⟩ := frames.code f member
  have kids : ∀ c ∈ Exec.childFrames f.run, c ∈ trace.settledFrames := fun _ hc =>
    settledFrames_children trace member hc
  obtain ⟨pc, sevm, pre, out, run, committed⟩ := f
  dsimp only at hpc0 hfork target hcode hpc hstatic hck hstack hmem hcd hgas hid hcs htk cdai cusdc cusdt ctok kids
  subst hpc0
  cases out with
  | error e => simp only [Execution.commits, Bool.false_eq_true] at committed
  | ok post =>
    have habs : Abstracts (entryStor ⟨0, sevm, pre, .ok post, run⟩) s := hck.abs
    have hcw : ∀ k : Fin 3, ((pre.getStor sevm.currentTarget).get (coinSlot k)).toAdr = adrOf (cs.get k) := by
      intro k
      have := coinAdr_eq habs k
      rw [hq.1] at this
      exact this
    have htw : ((pre.getStor sevm.currentTarget).get tokenSlot).toAdr = adrOf tokw := by
      have := tokenAdr_eq habs
      rw [hq.2] at this
      exact this
    have hp : PartiesAt (pre.getStor sevm.currentTarget) sevm.currentTarget dai usdc usdt tok :=
      { coin := fun k => by rw [hcw k]; exact words.coin k
        token := by rw [htw]; exact words.token
        coinNe := fun k => by rw [hcw k, target]; exact words.coinNe k
        tokNe := by rw [target]; exact words.tokNe
        apart := fun k => by rw [hcw k]; exact words.apart k }
    have w : PoolWorld run dai usdc usdt tok :=
      { daiCode := cdai
        usdcCode := cusdc
        usdtCode := cusdt
        tokCode := ctok
        usdcImpl := fun c hc ht _ sel => by
          obtain ⟨pc0, stat, -, -, ccode⟩ := poolChild_facts hcode hfork.stateGas_none run c hc
          have code : c.sevm.code = Usdc.Proxy.code := by
            rw [ccode usdc (by rw [cusdc]; exact Usdc.proxy_toList_ne_nil)
              (by rw [cusdc]; exact Usdc.proxy_not_delegation) ht, cusdc]
          exact (frames.usdcImpl c (kids c hc) ht code (ht ▸ usdc_child_notAdmin c pc0 code
            (by rw [stat]; exact hfork.stateGas_none) (by rw [stat]; exact hfork.bal_none) sel)).1
        usdtLive := fun c hc ht hs => frames.usdtLive c (kids c hc) ht hs }
    exact pool_keeps_of_world hcode hfork hcd hstack hmem hgas hstatic hpc hck hid
      (by rw [htw]; exact htk) (fun k => by rw [hcw k]; exact hcs k) w hp

/-- Installed certified bytes as a code semantics with no run content. -/
def certSem {C : ByteArray} (K : InstalledCert C) : CodeSem where
  image := some C.toList
  Run := fun _ _ _ => True
  correct := fun _ _ => trivial
  ne_nil := by
    intro l image
    exact (Option.some.inj image) ▸ K.nonempty
  not_delegation := by
    intro actual image
    exact bytes_eq_of_image image ▸ K.notDelegation

/-- **Certified bytes installed at a mid history's start stay at every raw frame.** -/
theorem midCode_of_cert {C : ByteArray} (K : InstalledCert C) {a : Adr}
    (trace : MidHistoryTraceIn HistFork cfg start future)
    (installed : start.state.getCode a = C) :
    ∀ R ∈ trace.rawFrames, R.devm.getCode a = C := by
  have capabilities := BodyStageCapabilities.historical
  have inv : (ContractSpecSem.ofStorageOnly (certSem K) (fun _ => True)).StateInv a start.state :=
    ⟨by rw [installed]; rfl, trivial, trivial⟩
  intro R member
  exact bytes_eq_of_image (trace.rawFrames_codeImageIn
    (c := ContractSpecSem.ofStorageOnly (certSem K) (fun _ => True))
    (entry := fun _ _ => True) (fun _ _ _ _ _ _ _ _ _ => ⟨trivial, trivial⟩) capabilities
    ((trace.frameAdmitted_iff_rawFrames a _).2 fun _ _ _ => trivial)
    (trace.rewardCreditsFunded capabilities) inv K.runtimeSafety rfl R member)

theorem daiInstalledCert : InstalledCert Dai.code where
  exists_cert := ⟨Dai.cert, Dai.cert_check, by decide +kernel, by decide +kernel⟩
  notDelegation := by decide +kernel
  nonempty := by decide +kernel

theorem usdtInstalledCert : InstalledCert Usdt.code where
  exists_cert := ⟨Usdt.cert, Usdt.cert_check, by decide +kernel, by decide +kernel⟩
  notDelegation := by decide +kernel
  nonempty := by decide +kernel

/-- **The coins' premises, of the history.** What is stated of the coins: DAI's and USDT's code at its start, and
the operators' two powers restrained, each at the settled non-static frames it reaches. `usdcCode` is USDC's code at every
settled frame: the proxy delegates, so `InstalledCert` does not give it. -/
structure CoinsHold (trace : MidHistoryTraceIn HistFork cfg start future) (dai usdc usdt : Adr) : Prop where
  daiCode : start.state.getCode dai = Dai.code
  usdtCode : start.state.getCode usdt = Usdt.code
  usdcCode : ∀ f ∈ trace.settledFrames, f.pre.getCode usdc = Usdc.Proxy.code
  usdcImpl : Usdc.CertifiedSettled usdc trace.settledFrames
  usdtLive : ∀ f ∈ trace.settledFrames, f.sevm.currentTarget = usdt → f.sevm.isStatic = false →
    Usdt.flag20 ((Devm.getStor f.pre usdt).get 10) = 0

theorem framesHold_of_coins {trace : MidHistoryTraceIn HistFork cfg start future} {dai usdc usdt tok : Adr}
    (coins : CoinsHold trace dai usdc usdt)
    (tokCode : ∀ R ∈ trace.rawFrames, R.devm.getCode tok = Curve3Crv.code) :
    FramesHold trace dai usdc usdt tok where
  code := fun f member =>
    have raw := trace.mem_rawFrames_of_mem_settledFrames f member
    ⟨midCode_of_cert daiInstalledCert trace coins.daiCode _ raw, coins.usdcCode f member,
      midCode_of_cert usdtInstalledCert trace coins.usdtCode _ raw, tokCode _ raw⟩
  usdcImpl := coins.usdcImpl
  usdtLive := coins.usdtLive

/-- **The pool's whole mid-history environment from the coins' premises.** -/
theorem poolMidEnv_of_coins {checkpoint : BlockChain} {pool dai usdc usdt tok : Adr} {cs : V3} {tokw : Nat}
    {full : ConfiguredHistoryTraceIn HistFork cfg checkpoint future}
    {trace : MidHistoryTraceIn HistFork cfg start future}
    (facts : PoolMidFacts full trace pool cs tokw) (words : PartyWords cs tokw pool dai usdc usdt tok)
    (coins : CoinsHold trace dai usdc usdt)
    (tokCode : ∀ R ∈ trace.rawFrames, R.devm.getCode tok = Curve3Crv.code) :
    PoolMidEnv full trace pool cs tokw :=
  { facts with callbacks := pool_keepAt_of_frames facts words (framesHold_of_coins coins tokCode) }

end

end Blanc.Composition.Curve3PoolCoinKeep
