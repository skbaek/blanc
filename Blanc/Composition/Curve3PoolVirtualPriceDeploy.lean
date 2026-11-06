import Blanc.Composition.Curve3PoolPublicBridge
import Blanc.Composition.Curve3Pool3CrvU3Mid

/-!
# `Assumes` gives the deployment's facts and the history's environment

`Assumes` states its premises over the whole history, from the pool's creation on. Here they become what
`joint_mid_u3` asks for:

* `Assumes.facts`: `AnchoredDeployment.Facts`, over the part of the history up to the minter assignment;
* `Assumes.env`: `PoolMidEnv` over the history since the minter assignment;
* `Assumes.fresh`: 3Crv's collision premise at the keys tracked at that cut.

`cutCode_of_cert` carries certified bytes from a block boundary to right after a later transaction.
-/

namespace Blanc.Composition.Curve3PoolPublic

open Jaune Blanc Blanc.Lift Blanc.ExecutionTrace
open Blanc.Composition.Curve3PoolCoinKeep (CoinsHold certSem midCode_of_cert daiInstalledCert
  usdtInstalledCert poolMidEnv_of_coins)
open Blanc.Composition.Curve3PoolJointRoot (parties_not_precompile party_words)

/-- **Certified bytes at a block boundary are there right after any later transaction.** -/
theorem cutCode_of_cert {C : ByteArray} (K : InstalledCert C) {cfg : ChainConfig} {a0 pre post : BlockChain}
    (hist : ConfiguredHistoryTraceIn HistFork cfg a0 pre)
    (block : ConfiguredBlockTraceIn HistFork cfg pre post) {i : Nat}
    (cut : block.bodyTrace.transactions.TxSplit i) {a : Adr} (installed : a0.state.getCode a = C) :
    cut.afterBenv.state.getCode a = C := by
  let c := ContractSpecSem.ofStorageOnly (certSem K) (fun _ => True)
  have preserves : c.PreservesAdmittedIn HistFork a (fun _ _ => True) :=
    ContractSpecSem.preserves_inv_admittedIn HistFork HistFork.stateGas_none c a _
      (fun _ _ _ _ _ _ _ _ => ⟨trivial, trivial⟩)
  have capabilities := BodyStageCapabilities.historical
  have inv0 : c.StateInv a a0.state := ⟨by rw [installed]; rfl, trivial, trivial⟩
  have inv := hist.stateInv_admitted_semIn preserves capabilities
    ((hist.frameAdmitted_iff_rawFrames a _).2 fun _ _ _ => trivial)
    (hist.rewardCreditsFunded capabilities) inv0 K.runtimeSafety rfl
  have admitted : block.FrameAdmitted a (fun _ _ => True) :=
    (block.frameAdmitted_iff_rawFrames a _).2 fun _ _ _ => trivial
  have hF : HistFork (initBenv block.fork pre block.block.header).stat.fork := block.forkIn
  have hsg : (initBenv block.fork pre block.block.header).stat.rules.stateGas = none :=
    capabilities.stateGas_none block.forkIn
  have bound : sum pre.state.bal + wdsum block.block.wds < 2 ^ 256 := block.withdrawalsBound
  have startInv : c.BenvInv a (initBenv block.fork pre block.block.header) := ⟨inv, AdrSet.not_mem_empty⟩
  have openSum : sum (initBenv block.fork pre block.block.header).state.bal < 2 ^ 256 := by
    change sum pre.state.bal < 2 ^ 256
    omega
  have beaconMeta := block.bodyTrace.beacon.stateInv_and_sum_le_admitted_semIn preserves hF hsg
    admitted.beacon startInv K.runtimeSafety rfl
  have beaconInv : c.BenvInv a
      ((initBenv block.fork pre block.block.header).withState block.bodyTrace.beaconState) :=
    ⟨beaconMeta.1, by simpa only [Benv.withState] using startInv.ca⟩
  have beaconSum : sum block.bodyTrace.beaconState.bal < 2 ^ 256 :=
    Nat.lt_of_le_of_lt beaconMeta.2 openSum
  have historyMeta := block.bodyTrace.history.stateInv_and_sum_le_admitted_semIn preserves
    (by simpa only [Benv.withState] using hF) (by simpa only [Benv.withState] using hsg)
    admitted.history beaconInv K.runtimeSafety rfl
  have historyInv : c.BenvInv a
      (((initBenv block.fork pre block.block.header).withState
        block.bodyTrace.beaconState).withState block.bodyTrace.historyState) :=
    ⟨historyMeta.1, by simpa only [Benv.withState] using beaconInv.ca⟩
  have historySum : sum block.bodyTrace.historyState.bal < 2 ^ 256 := by
    have le := historyMeta.2
    simp only [Benv.withState] at le
    exact Nat.lt_of_le_of_lt le beaconSum
  have hFhist : HistFork (((initBenv block.fork pre block.block.header).withState
      block.bodyTrace.beaconState).withState block.bodyTrace.historyState).stat.fork := by
    simpa only [Benv.withState] using hF
  have hsgHist : (((initBenv block.fork pre block.block.header).withState
      block.bodyTrace.beaconState).withState block.bodyTrace.historyState).stat.rules.stateGas =
      none := by
    simpa only [Benv.withState] using hsg
  have whole := (block.bodyTrace.transactions.frameAdmitted_iff_rawFrames a _).1 admitted.transactions
  have admittedBefore : cut.before.FrameAdmitted a (fun _ _ => True) :=
    (cut.before.frameAdmitted_iff_rawFrames a _).2 fun _ _ _ => trivial
  have admittedHead : cut.head.FrameAdmitted a (fun _ _ => True) :=
    (cut.head.frameAdmitted_iff_rawFrames a _).2 fun _ _ _ => trivial
  have benvInv : c.BenvInv a cut.benv :=
    cut.before.benvInv_admitted_semIn preserves hFhist hsgHist admittedBefore historySum
      historyInv K.runtimeSafety rfl
  have stat : cut.benv.stat = (initBenv block.fork pre block.block.header).stat :=
    block.txSplit_stat cut
  have hFcut : HistFork cut.benv.stat.fork := by rw [stat]; exact hF
  have hsgCut : cut.benv.stat.rules.stateGas = none := by rw [stat]; exact hsg
  have cutSum : sum cut.benv.state.bal < 2 ^ 256 :=
    Nat.lt_of_le_of_lt (cut.before.sum_le_noStateGas hsgHist) historySum
  have afterInv := cut.head.benvInv_admitted_semIn preserves hFcut hsgCut admittedHead cutSum
    benvInv K.runtimeSafety rfl
  exact bytes_eq_of_image afterInv.state.1

/-! ## Keys -/

section Keys

variable {κ : Type} {slot : κ → B256} {fixed : List B256}

/-- Collision freedom over a list holds over any list inside it. -/
theorem freshKeys_mono {K : κ → Prop} {ks ks' : List κ} (hk : ∀ k ∈ ks, k ∈ ks')
    (fresh : SlotFootprint.FreshKeys slot fixed K ks') : SlotFootprint.FreshKeys slot fixed K ks :=
  ⟨fun k h => fresh.1 k (hk k h), fun a ha b hb e => fresh.2 a (hk a ha) b (hk b hb) e⟩

/-- Collision freedom over all keys, none tracked, holds at any tracked keys among them. -/
theorem freshKeys_tracked {K : κ → Prop} {ks all : List κ}
    (fresh : SlotFootprint.FreshKeys slot fixed (fun _ => False) all)
    (hk : ∀ k ∈ ks, k ∈ all) (hK : ∀ k, K k → k ∈ all) : SlotFootprint.FreshKeys slot fixed K ks := by
  classical
  refine ⟨fun k h => ?_, fun a ha b hb e => fresh.2 a (hk a ha) b (hk b hb) e⟩
  by_cases tracked : K k
  · exact .inl tracked
  · exact .inr ⟨(fresh.1 k (hk k h)).resolve_left id |>.1, fun k' hk' e => tracked (by
      rwa [fresh.2 k' (hK k' hk') k (hk k h) e] at hk')⟩

end Keys

/-- The keys touched over a sublist of raw roots are among the wider list's. -/
theorem midTouched_mono {cfg : ChainConfig} {s s' : Benv} {f f' : BlockChain} {ca : Adr}
    {t : MidHistoryTraceIn HistFork cfg s f} {t' : MidHistoryTraceIn HistFork cfg s' f'}
    (sub : ∀ r ∈ t.rawFrames, r ∈ t'.rawFrames) :
    ∀ k ∈ Curve3Crv.midTouchedKeysIn ca t, k ∈ Curve3Crv.midTouchedKeysIn ca t' := by
  intro k hk
  obtain ⟨r, hr, hk⟩ := List.mem_flatMap.mp hk
  exact List.mem_flatMap.mpr ⟨r, sub r hr, hk⟩

section Assumes

variable {d : Deployment} {future : BlockChain} {h : MainnetHistory d.minter.post future}

/-! ## The history's parts -/

theorem sincePool_settled : (d.sincePool h).settledFrames =
    (MidHistoryTraceIn.tail d.pool.trace d.poolCut).settledFrames ++ d.toMinter.settledFrames ++
      d.minter.trace.settledFrames ++ h.settledFrames := by
  simp only [Deployment.sincePool, MidHistoryTraceIn.append_settledFrames,
    ConfiguredHistoryTraceIn.settledFrames_append, ConfiguredHistoryTraceIn.settledFrames,
    List.append_assoc]

theorem sinceMinter_settled_sub :
    ∀ F ∈ (d.sinceMinter h).settledFrames, F ∈ (d.sincePool h).settledFrames := by
  intro F member
  rw [sincePool_settled]
  simp only [Deployment.sinceMinter, MidHistoryTraceIn.append_settledFrames, List.mem_append] at member ⊢
  rcases member with m | m
  · refine .inl (.inr ?_)
    rw [d.minter.trace.settledFrames_throughCut d.minterCut]
    exact List.mem_append_right _ m
  · exact .inr m

/-- The history up to the end of the minter assignment's block, from the pool's creation. -/
noncomputable abbrev spanOf (d : Deployment) :
    MidHistoryTraceIn HistFork mainnetChainConfig d.poolCut.afterBenv d.minter.post :=
  ((MidHistoryTraceIn.tail d.pool.trace d.poolCut).append d.toMinter).step d.minter.trace

theorem span_settled_sub : ∀ F ∈ (spanOf d).settledFrames, F ∈ (d.sincePool h).settledFrames := by
  intro F member
  rw [sincePool_settled]
  simp only [MidHistoryTraceIn.settledFrames, MidHistoryTraceIn.append_settledFrames,
    List.mem_append] at member ⊢
  rcases member with (m | m) | m
  · exact .inl (.inl (.inl m))
  · exact .inl (.inl (.inr m))
  · exact .inl (.inr m)

theorem sinceC3Block_raw : (d.sinceC3Block h).rawFrames =
    d.toPool.rawFrames ++ d.pool.trace.rawFrames ++ d.toMinter.rawFrames ++ d.minter.trace.rawFrames ++
      h.rawFrames := by
  simp only [Deployment.sinceC3Block, ConfiguredHistoryTraceIn.rawFrames_append,
    ConfiguredHistoryTraceIn.rawFrames, List.append_assoc]

theorem tail_raw_sub {pre post : BlockChain} (block : ConfiguredBlockTraceIn HistFork mainnetChainConfig pre post)
    {i : Nat} (cut : block.bodyTrace.transactions.TxSplit i) :
    ∀ r ∈ (MidHistoryTraceIn.tail block cut).rawFrames, r ∈ block.rawFrames := by
  intro r hr
  rw [block.rawFrames_txSplit cut]
  exact List.mem_append_right _ hr

theorem sinceMinter_raw_sub :
    ∀ r ∈ (d.sinceMinter h).rawFrames, r ∈ (d.sinceC3Block h).rawFrames := by
  intro r member
  rw [sinceC3Block_raw]
  simp only [Deployment.sinceMinter, MidHistoryTraceIn.append_rawFrames, List.mem_append] at member ⊢
  rcases member with m | m
  · exact .inl (.inr (tail_raw_sub _ _ r m))
  · exact .inr m

/-! ## The coins -/

/-- `Assumes` gives `CoinsHold` over any part of the history from the pool's creation, given the two codes at its start. -/
theorem Assumes.coinsHold (A : Assumes d h) {s : Benv} {f : BlockChain}
    (trace : MidHistoryTraceIn HistFork mainnetChainConfig s f)
    (sub : ∀ F ∈ trace.settledFrames, F ∈ (d.sincePool h).settledFrames)
    (daiCode : s.state.getCode dai = Lift.Dai.code) (usdtCode : s.state.getCode usdt = Lift.Usdt.code) :
    CoinsHold trace dai usdc usdt where
  daiCode := daiCode
  usdtCode := usdtCode
  usdcCode := fun F m => A.circle.proxyStays F (sub F m)
  usdcImpl := fun F m t _ => (A.circle.usdcCertified F (sub F m) t).1
  usdtLive := fun F m t st => A.tether.notDeprecated F (mem_coinFrames.mpr ⟨sub F m, t, st, trivial⟩)

theorem coin0_eq : Curve3Pool.adrOf (Curve3Pool.Creation.coinsN.get 0) = dai := by decide +kernel
theorem coin1_eq : Curve3Pool.adrOf (Curve3Pool.Creation.coinsN.get 1) = usdc := by decide +kernel
theorem coin2_eq : Curve3Pool.adrOf (Curve3Pool.Creation.coinsN.get 2) = usdt := by decide +kernel

/-- **`Assumes` gives `AnchoredDeployment.Facts`.** -/
theorem Assumes.facts (A : Assumes d h) : d.Facts where
  fresh := by
    refine freshKeys_mono (midTouched_mono fun r hr => ?_) A.hashes.c3Keys
    simp only [Deployment.sinceCreation, Deployment.sinceC3Block, MidHistoryTraceIn.append_rawFrames,
      ConfiguredHistoryTraceIn.rawFrames_append, List.mem_append] at hr ⊢
    rcases hr with m | m
    · exact .inl m
    · exact .inr (.inl m)
  coins := by
    rw [coin0_eq, coin1_eq, coin2_eq]
    exact A.coinsHold (spanOf d) span_settled_sub
      (cutCode_of_cert daiInstalledCert d.toPool d.pool.trace d.poolCut A.code.daiCode)
      (cutCode_of_cert usdtInstalledCert d.toPool d.pool.trace d.poolCut A.code.usdtCode)
  idEmpty := A.code.idEmpty
  idNoFrame := fun r hr => A.hashes.noCreateAt4 r (by
    change r ∈ _ at hr
    rw [Deployment.sinceC3Block, ConfiguredHistoryTraceIn.rawFrames_append]
    exact List.mem_append_left _ hr)

/-- 3Crv's runtime stays at every raw frame since the minter assignment. -/
theorem Assumes.c3Code (A : Assumes d h) :
    ∀ R ∈ (d.sinceMinter h).rawFrames, R.devm.getCode c3 = Curve3Crv.code := by
  obtain ⟨hcode, -, -⟩ := (Deployment.toJoint d A.facts).c3Created
  intro R member
  refine midCode_of_cert Curve3Crv.c3crvInstalledCert (d.sinceCreation h)
    (Curve3Crv.code_of_image ((congrArg some hcode).trans rfl)) R ?_
  simp only [Deployment.sinceCreation, MidHistoryTraceIn.append_rawFrames, List.mem_append]
  exact .inr (sinceMinter_raw_sub R member)

/-- **3Crv's collision premise at the keys tracked at the minter assignment.** -/
theorem Assumes.fresh (A : Assumes d h) :
    Curve3Crv.FreshKeys (Deployment.toJoint d A.facts).c3Keys
      (Curve3Crv.midTouchedKeysIn Curve3Crv.Creation.tokenAddress (d.sinceMinter h)) := by
  refine freshKeys_tracked A.hashes.c3Keys (midTouched_mono fun r hr => ?_) ?_
  · simp only [Deployment.sinceCreation, MidHistoryTraceIn.append_rawFrames, List.mem_append]
    exact .inr (sinceMinter_raw_sub r hr)
  · rintro k (hk | hk)
    · exact hk.elim
    · obtain ⟨inv, hinv, hk⟩ := List.mem_flatMap.mp hk
      obtain ⟨F, hF, hinv⟩ := List.mem_flatMap.mp hinv
      unfold Curve3Crv.committedFrameInvocations at hinv
      split at hinv
      · rename_i hw
        rw [List.mem_singleton] at hinv
        subst hinv
        refine List.mem_flatMap.mpr ⟨Exec.Frame.rootDeriv F, ?_, ?_⟩
        · have raw := MidHistoryTraceIn.mem_rawFrames_of_mem_settledFrames
            ((Deployment.toJoint d A.facts).c3Mid.step d.minter.trace) F (by
              simp only [MidHistoryTraceIn.settledFrames, List.mem_append]
              rcases List.mem_append.mp hF with m | m
              · exact .inl m
              · have m' : F ∈ d.minter.trace.settledThroughCut d.minterCut := m
                have inB : F ∈ d.minter.trace.settledFrames := by
                  rw [d.minter.trace.settledFrames_throughCut d.minterCut]
                  exact List.mem_append_left _ m'
                exact .inr inB)
          have raw' : Exec.Frame.rootDeriv F ∈ (((MidHistoryTraceIn.tail d.c3.trace d.c3Cut).append
              ((d.toPool.step d.pool.trace).append d.toMinter)).step d.minter.trace).rawFrames := raw
          simp only [Deployment.sinceCreation, Deployment.sinceC3Block, MidHistoryTraceIn.append_rawFrames,
            MidHistoryTraceIn.rawFrames, ConfiguredHistoryTraceIn.rawFrames_append,
            ConfiguredHistoryTraceIn.rawFrames, List.mem_append] at raw' ⊢
          rcases raw' with (m | m) | m
          · exact .inl m
          · exact .inr (.inl (.inl m))
          · exact .inr (.inl (.inr m))
        · rw [ite_eq_left (show (Exec.Frame.rootDeriv F).sevm.currentTarget = c3 from hw.1)]
          exact hk
      · exact absurd hinv List.not_mem_nil

/-- The history's facts since the minter assignment, from `Assumes`. -/
theorem Assumes.midFacts (A : Assumes d h) :
    Curve3Pool.PoolMidFacts (d.sinceC3Block h) (d.sinceMinter h) pool Curve3Pool.Creation.coinsN
      Curve3Pool.Creation.tokenN where
  subset := sinceMinter_raw_sub
  parties := fun root member _ => parties_not_precompile ((d.sinceMinter h).rootEntryIn root member).2
  idEmpty := A.code.idEmpty
  idNoAuthority := A.keys.idNoAuthority
  idNoFrame := A.hashes.noCreateAt4
  sysNe := d.system_ne A.system Curve3PoolBlockAnchor.AnchoredDeployment.pool_not_system

/-- `CoinsHold` since the minter assignment. -/
theorem Assumes.coinsSince (A : Assumes d h) : CoinsHold (d.sinceMinter h) dai usdc usdt :=
  A.coinsHold (d.sinceMinter h) sinceMinter_settled_sub
    (cutCode_of_cert daiInstalledCert ((d.toPool.step d.pool.trace).append d.toMinter) d.minter.trace
      d.minterCut A.code.daiCode)
    (cutCode_of_cert usdtInstalledCert ((d.toPool.step d.pool.trace).append d.toMinter) d.minter.trace
      d.minterCut A.code.usdtCode)

/-- The recorded coins and token are the public names. -/
theorem party_words' : Curve3PoolCoinKeep.PartyWords Curve3Pool.Creation.coinsN Curve3Pool.Creation.tokenN pool
    dai usdc usdt c3 := by
  have := party_words
  rwa [coin0_eq, coin1_eq, coin2_eq] at this

/-- **`Assumes` gives the pool's environment since the minter assignment.** -/
theorem Assumes.env (A : Assumes d h) :
    Curve3Pool.PoolMidEnv (d.sinceC3Block h) (d.sinceMinter h) pool Curve3Pool.Creation.coinsN
      Curve3Pool.Creation.tokenN :=
  poolMidEnv_of_coins A.midFacts party_words' A.coinsSince A.c3Code

end Assumes

end Blanc.Composition.Curve3PoolPublic
