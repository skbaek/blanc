import Blanc.Composition.Curve3PoolKeepAt
import Blanc.ExecutionMidHistoryInOwnCode
import Blanc.ExecutionInCodeImage
import Blanc.Lift.RetainedTargetCompleteness

/-!
# `PoolKeepAt` over a history in which the coins are their bytes

* `PartyWords`: the words a pool's coins and token hold name the three coins and the token, apart;
* `FramesHold`: what the proof reads at each raw frame: the four codes, and the two operator premises;
* `pool_keepAt_of_frames`: `PoolKeepAt` at every raw pool frame, from `FramesHold`;
* `CoinsHold`: `FramesHold`'s premises as stated of the history: DAI's and USDT's code at its start, USDC's code
  at every raw frame, and the operators' `usdcImpl` and `usdtLive`;
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

/-- What the proof reads at each raw frame of the history. -/
structure FramesHold (trace : MidHistoryTraceIn HistFork cfg start future) (dai usdc usdt tok : Adr) : Prop where
  code : ∀ R ∈ trace.rawFrames, R.devm.getCode dai = Dai.code ∧ R.devm.getCode usdc = Usdc.Proxy.code ∧
    R.devm.getCode usdt = Usdt.code ∧ R.devm.getCode tok = Curve3Crv.code
  /-- Circle's proxy admin: at every frame at USDC, the implementation word names one of the three versions. -/
  usdcImpl : ∀ R ∈ trace.rawFrames, R.sevm.currentTarget = usdc → UsdcImplAt R.devm usdc
  /-- Tether's owner: at every frame at USDT, USDT is not deprecated. -/
  usdtLive : ∀ R ∈ trace.rawFrames, R.sevm.currentTarget = usdt →
    Usdt.flag20 ((Devm.getStor R.devm usdt).get 10) = 0

/-- **`PoolKeepAt` at every raw pool frame of a history in which the coins and the token are their bytes.** -/
theorem pool_keepAt_of_frames {checkpoint : BlockChain} {pool dai usdc usdt tok : Adr} {cs : V3} {tokw : Nat}
    {full : ConfiguredHistoryTraceIn HistFork cfg checkpoint future}
    {trace : MidHistoryTraceIn HistFork cfg start future}
    (facts : PoolMidFacts full trace pool cs tokw) (words : PartyWords cs tokw pool dai usdc usdt tok)
    (frames : FramesHold trace dai usdc usdt tok) :
    trace.FrameAdmitted pool (PoolKeepAt cs tokw) := by
  apply (trace.frameAdmitted_iff_rawFrames pool _).2
  intro root member target post exc s hcode hpc hstatic herr hck hq
  obtain ⟨⟨hstack, hmem⟩, hcd, hgas, hid, hcs, htk, -⟩ := facts.entry member target
  obtain ⟨hpc0, hfork⟩ := trace.rootEntryIn root member
  obtain ⟨cdai, cusdc, cusdt, ctok⟩ := frames.code root member
  have kids : Exec.derivEntry (fun D => Execution.commits D.exn = true → ∀ c ∈ children D,
      Exec.Frame.rootDeriv c ∈ trace.rawFrames) root.sevm root.devm :=
    Exec.derivEntry_of_deriv hpc0 fun committed c hc =>
      trace.rawFrames_closed root member _ (Exec.mem_rawFrameRoots_of_mem_committedFrames root.exc c
        (by
          rw [Exec.committedFrames, dite_eq_left committed]
          exact List.mem_cons_of_mem _ (Exec.mem_descendantFrames_of_mem_childFrames root.exc c hc)))
  have hkids := kids _ exc (by
    change Execution.commits (.ok post) = true
    simp only [Execution.commits, herr, Option.isNone_none])
  have habs : Abstracts (entryStor ⟨0, root.sevm, root.devm, .ok post, exc⟩) s := hck.abs
  have hcw : ∀ k : Fin 3, ((root.devm.getStor root.sevm.currentTarget).get (coinSlot k)).toAdr = adrOf (cs.get k) := by
    intro k
    have := coinAdr_eq habs k
    rw [hq.1] at this
    exact this
  have htw : ((root.devm.getStor root.sevm.currentTarget).get tokenSlot).toAdr = adrOf tokw := by
    have := tokenAdr_eq habs
    rw [hq.2] at this
    exact this
  have hp : PartiesAt (root.devm.getStor root.sevm.currentTarget) root.sevm.currentTarget dai usdc usdt tok :=
    { coin := fun k => by rw [hcw k]; exact words.coin k
      token := by rw [htw]; exact words.token
      coinNe := fun k => by rw [hcw k, target]; exact words.coinNe k
      tokNe := by rw [target]; exact words.tokNe
      apart := fun k => by rw [hcw k]; exact words.apart k }
  have w : PoolWorld exc dai usdc usdt tok :=
    { daiCode := cdai
      usdcCode := cusdc
      usdtCode := cusdt
      tokCode := ctok
      usdcImpl := fun c hc ht => frames.usdcImpl (Exec.Frame.rootDeriv c) (hkids c hc) ht
      usdtLive := fun c hc ht => frames.usdtLive (Exec.Frame.rootDeriv c) (hkids c hc) ht }
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
the operators' two powers restrained, each at the frames it reaches. `usdcCode` is USDC's code at every raw frame:
the proxy delegates, so `InstalledCert` does not give it. -/
structure CoinsHold (trace : MidHistoryTraceIn HistFork cfg start future) (dai usdc usdt : Adr) : Prop where
  daiCode : start.state.getCode dai = Dai.code
  usdtCode : start.state.getCode usdt = Usdt.code
  usdcCode : ∀ R ∈ trace.rawFrames, R.devm.getCode usdc = Usdc.Proxy.code
  usdcImpl : ∀ R ∈ trace.rawFrames, R.sevm.currentTarget = usdc → UsdcImplAt R.devm usdc
  usdtLive : ∀ R ∈ trace.rawFrames, R.sevm.currentTarget = usdt →
    Usdt.flag20 ((Devm.getStor R.devm usdt).get 10) = 0

theorem framesHold_of_coins {trace : MidHistoryTraceIn HistFork cfg start future} {dai usdc usdt tok : Adr}
    (coins : CoinsHold trace dai usdc usdt)
    (tokCode : ∀ R ∈ trace.rawFrames, R.devm.getCode tok = Curve3Crv.code) :
    FramesHold trace dai usdc usdt tok where
  code := fun R member => ⟨midCode_of_cert daiInstalledCert trace coins.daiCode R member,
    coins.usdcCode R member, midCode_of_cert usdtInstalledCert trace coins.usdtCode R member, tokCode R member⟩
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
