import Blanc.Composition.Curve3PoolVirtualPriceFallsChain
import Blanc.Composition.Curve3PoolPublic

/-!
# The returned virtual price falls on the deployed bytes, from the deployment state

`virtual_price_falls` proves the public statement `Curve3PoolPublic.virtual_price_falls`.  All four calls,
with every child frame, are kernel evaluations of the bytes (`Curve3PoolVirtualPriceFallsFacts*`), composed
in `Curve3PoolVirtualPriceFallsChain`; no pool or coin model enters.

The witness: the deposit is `[540712138941758899472585, 1160326029455, 1949013540497]`, the call
`remove_liquidity_one_coin(8, 0, 0)`, the word goes from `10^18` to `10^18 - 1` (`falls_at_witness`).
The public statement's docstring says what this does not claim.
-/

namespace Blanc.Composition.Curve3PoolVirtualPriceFalls

open Jaune Blanc Blanc.Lift Blanc.Lift.Witness Blanc.Lift.NodeWalk
open Blanc.Lift.Curve3Pool.VirtualPriceFalls
open Blanc.Lift.Curve3Pool (coinSlot balanceSlot feeSlot adminFeeSlot ownerSlot tokenSlot initialASlot futureASlot initialATimeSlot futureATimeSlot killDeadlineSlot answerWord selGetVirtualPrice selAddLiquidity)

open Curve3PoolPublic (ReturnsPrice AtPoolBlock CallCommits AtDeployment rampWords)

/-! ## One top-level call -/

theorem acctAgree_get_code {W : Jaune.State} (h : AcctAgree W acsW) (a : Adr) :
    W.getCode a = (lookupA acsW a).code := by
  have e := congrArg Acct.code (h a)
  exact e

/-- A top-level call from its start boundary. -/
theorem stage {W O : Jaune.State} {stat : BenvStat} {d : Bytes} {st : Bool} {x z : XB}
    (hO : OrigAgree O stat.origState) (hx : x.pc = 0) (hk : x.keys = []) (ha : x.adrs = [])
    (hst : ∀ a k, storOf W a k = lookupS x.stor a k) (hac : AcctAgree W acsW)
    (hob : xObs x ⟨0, initDevm (msgOf W (stat.withOrig O) d st), x.keys, x.adrs, x.stor, acsW⟩ =
      xOk acsW)
    (r : RunsB (sevmOf stat d st) acsW x z) :
    ∃ m' w', exec (initEvm (msgOf W (stat.withOrig O) d st)) = .ok (z.cfg acsW m' w').devm ∧
      PAgree (z.cfg acsW m' w') := by
  refine exec_of_runsB (O := O) rfl hO hx hob ?_ r
  refine ⟨fun y => ?_, fun a => ?_, fun a k => hst a k, hac⟩
  · show y ∈ (Std.HashSet.emptyWithCapacity : Std.HashSet (Adr × B256)) ↔ y ∈ x.keys
    rw [hk]
    simp only [Std.HashSet.not_mem_emptyWithCapacity, List.not_mem_nil]
  · show a ∈ (Std.HashSet.emptyWithCapacity : AdrSet) ↔ a ∈ x.adrs
    rw [ha]
    simp only [Std.HashSet.not_mem_emptyWithCapacity, List.not_mem_nil]

/-! ## The world's facts -/

theorem storW_eq : storW = storShadowOf worldWrites := by kernel_rfl

theorem storOf_acct_zero (a : Adr) (k : B256) : storOf (stateFoldAcct default acctsW) a k = 0 :=
  storOf_stateFoldAcct acctsW a k

theorem world_stor (a : Adr) (k : B256) : storOf worldW a k = lookupS storW a k := by
  rw [storW_eq]
  exact storOf_stateFoldStor worldWrites storOf_acct_zero a k

theorem world_acct : AcctAgree worldW acsW :=
  acctAgree_stateFoldStor worldWrites (acctAgree_stateFoldAcct acctsW)

theorem world_at : AtDeployment worldW where
  poolAt :=
    { code := by rw [acctAgree_get_code world_acct]; kernel_rfl
      stor := by kernel_rfl }
  tokenAt :=
    { code := by rw [acctAgree_get_code world_acct]; kernel_rfl
      stor := by kernel_rfl }
  coins :=
    { daiCode := by rw [acctAgree_get_code world_acct]; kernel_rfl
      usdtCode := by rw [acctAgree_get_code world_acct]; kernel_rfl
      idEmpty := by rw [acctAgree_get_code world_acct]; kernel_rfl }
  usdcAt :=
    { proxy := by rw [acctAgree_get_code world_acct]; kernel_rfl
      v2 := by
        have h : (worldW.getStor usdcA).get Usdc.implSlot = implA.toB256 :=
          (world_stor usdcA Usdc.implSlot).trans (by kernel_rfl)
        have hi : implA.toB256.toAdr = implA := by decide +kernel
        show worldW.getCode ((worldW.getStor usdcA).get Usdc.implSlot).toAdr = _
        rw [h, hi]
        exact (acctAgree_get_code world_acct implA).trans (by kernel_rfl) }
  empty := by
    have h : ∀ k, lookupS storW (Curve3PoolPublic.coinAt k) (Curve3PoolPublic.coinEntry poolA k) = 0 := by
      decide +kernel
    intro k
    exact (congrArg B256.toNat ((world_stor _ _).trans (h k))).trans rfl

/-! ## The four calls' boundary decisions -/

theorem statOf_orig (l : StorShadow) : (statOf l).origState = origOf l := rfl

theorem statOf_block (l : StorShadow) : AtPoolBlock (statOf l) := ⟨rfl, rfl, rfl⟩

theorem stat1_eq : stat1 = statOf storW := by kernel_rfl

theorem stat2_eq : stat2 = statOf endDeposit.stor := by kernel_rfl

theorem origAgree_world : OrigAgree worldW stat1.origState := by
  rw [stat1_eq, statOf_orig]
  exact origAgree_origOf world_stor

theorem obsDeposit : xObs startDeposit
    ⟨0, initDevm (msgOf worldW (stat1.withOrig worldW) data1 false), startDeposit.keys,
      startDeposit.adrs, startDeposit.stor, acsW⟩ = xOk acsW := by kernel_rfl

theorem obsPrice1 : ∀ W O, xObs startPrice1
    ⟨0, initDevm (msgOf W (stat2.withOrig O) dataP true), startPrice1.keys,
      startPrice1.adrs, startPrice1.stor, acsW⟩ = xOk acsW := by kernel_forall_rfl

theorem obsCall : ∀ W O, xObs startCall
    ⟨0, initDevm (msgOf W (stat2.withOrig O) data2 false), startCall.keys,
      startCall.adrs, startCall.stor, acsW⟩ = xOk acsW := by kernel_forall_rfl

theorem obsPrice2 : ∀ W O, xObs startPrice2
    ⟨0, initDevm (msgOf W (stat2.withOrig O) dataP true), startPrice2.keys,
      startPrice2.adrs, startPrice2.stor, acsW⟩ = xOk acsW := by kernel_forall_rfl

/-- What the four calls' end boundaries say: the deposit and the call end without error, the ramp
words are unchanged, and the two words returned. -/
theorem endFacts :
    answerWord endPrice1.out = 10 ^ 18 ∧ answerWord endPrice2.out = 10 ^ 18 - 1 ∧
      [initialASlot, futureASlot, initialATimeSlot, futureATimeSlot].map (lookupS endDeposit.stor poolA) =
        [initialASlot, futureASlot, initialATimeSlot, futureATimeSlot].map (lookupS endCall.stor poolA) := by
  decide +kernel

/-! ## The fall -/

theorem cfg_error (z : XB) (A : AcctShadow) (m : Meta) (w : Jaune.World) :
    (z.cfg A m w).devm.error = none := rfl

theorem cfg_output (z : XB) (A : AcctShadow) (m : Meta) (w : Jaune.World) :
    (z.cfg A m w).devm.output = z.out := rfl

/-- The depositor's call commits. -/
theorem commits {W : Jaune.State} {stat : BenvStat} {d : Bytes} {st : Bool} {post : Devm}
    (hcode : AcctAgree W acsW) (hf : AtPoolBlock stat)
    (hr : exec (initEvm (msgOf W (stat.withOrig W) d st)) = .ok post) (he : post.error = none) :
    CallCommits (msgOf W (stat.withOrig W) d st) W post where
  target := rfl
  state := rfl
  orig := rfl
  code := by rw [acctAgree_get_code hcode]; show Curve3Pool.code = _; kernel_rfl
  gas := rfl
  block := ⟨hf.fork, hf.number, hf.time⟩
  ran := hr
  ok := he

/-- A price question gets its word. -/
theorem returns {W O : Jaune.State} {stat : BenvStat} {post : Devm} {p : Nat}
    (hcode : AcctAgree W acsW)
    (hr : exec (initEvm (msgOf W (stat.withOrig O) priceData true)) = .ok post)
    (he : post.error = none) (hp : answerWord post.output = p) :
    ReturnsPrice (stat.withOrig O) W p :=
  ⟨msgOf W (stat.withOrig O) priceData true, post,
    ⟨rfl, rfl, by rw [acctAgree_get_code hcode]; show Curve3Pool.code = _; kernel_rfl, rfl, rfl,
      by show priceData = _; decide +kernel⟩, rfl, hr, he, hp⟩

theorem data1_eq : data1 = depositData amt0 amt1 amt2 := by kernel_rfl
theorem data2_eq : data2 = oneCoinData 8 := by kernel_rfl
theorem dataP_eq : dataP = priceData := by kernel_rfl

/-- `rampWords` from a state's storage shadow. -/
theorem rampWords_of_shadow {W : Jaune.State} {l : StorShadow}
    (h : ∀ k, (W.getStor Curve3PoolPublic.pool).get k = lookupS l poolA k) :
    rampWords W = ([initialASlot, futureASlot, initialATimeSlot, futureATimeSlot].map
      (lookupS l poolA)).map B256.toNat := by
  simp only [rampWords, Curve3PoolPublic.word, List.map_cons, List.map_nil, h]

/-- **The fall at the witness**: the exact deposit, the exact call, the exact words. -/
theorem falls_at_witness :
    ∃ (dep m : Msg) (mid post : Devm),
      AtDeployment worldW ∧ dep.data = depositData amt0 amt1 amt2 ∧ m.data = oneCoinData 8 ∧
      CallCommits dep worldW mid ∧ CallCommits m mid.state post ∧
      rampWords mid.state = rampWords post.state ∧
      ReturnsPrice m.benv.stat mid.state (10 ^ 18) ∧
      ReturnsPrice m.benv.stat post.state (10 ^ 18 - 1) := by
  obtain ⟨m1, w1, hex1, hag1⟩ := stage (W := worldW) (O := worldW) (stat := stat1) (d := data1)
    (st := false) (x := startDeposit) (z := endDeposit) origAgree_world (by kernel_rfl)
    (by kernel_rfl) (by kernel_rfl) (by
      have e : startDeposit.stor = storW := by kernel_rfl
      rw [e]; exact world_stor) world_acct obsDeposit runDeposit
  have hO : OrigAgree (endDeposit.cfg acsW m1 w1).devm.state stat2.origState := by
    rw [stat2_eq, statOf_orig]
    exact origAgree_origOf hag1.2.2.1
  obtain ⟨mc, wc, hexc, hagc⟩ := stage (O := (endDeposit.cfg acsW m1 w1).devm.state) (stat := stat2)
    (d := data2) (st := false) (x := startCall) (z := endCall) hO (by kernel_rfl) (by kernel_rfl)
    (by kernel_rfl) (by
      have e : startCall.stor = endDeposit.stor := by kernel_rfl
      rw [e]; exact hag1.2.2.1) hag1.2.2.2 (obsCall _ _) runCall
  obtain ⟨mp, wp, hexp, -⟩ := stage (O := (endDeposit.cfg acsW m1 w1).devm.state) (stat := stat2)
    (d := dataP) (st := true) (x := startPrice1) (z := endPrice1) hO (by kernel_rfl)
    (by kernel_rfl) (by kernel_rfl) (by
      have e : startPrice1.stor = endDeposit.stor := by kernel_rfl
      rw [e]; exact hag1.2.2.1) hag1.2.2.2 (obsPrice1 _ _) runPrice1
  obtain ⟨mq, wq, hexq, -⟩ := stage (O := (endDeposit.cfg acsW m1 w1).devm.state) (stat := stat2)
    (d := dataP) (st := true) (x := startPrice2) (z := endPrice2) hO (by kernel_rfl)
    (by kernel_rfl) (by kernel_rfl) (by
      have e : startPrice2.stor = endCall.stor := by kernel_rfl
      rw [e]; exact hagc.2.2.1) hagc.2.2.2 (obsPrice2 _ _) runPrice2
  obtain ⟨hw1, hw2, hramp⟩ := endFacts
  rw [dataP_eq] at hexp hexq
  refine ⟨_, _, _, _, world_at, data1_eq, data2_eq,
    commits world_acct (by rw [stat1_eq]; exact statOf_block _) hex1 (cfg_error _ _ _ _),
    commits hag1.2.2.2 (by rw [stat2_eq]; exact statOf_block _) hexc (cfg_error _ _ _ _), ?_,
    returns hag1.2.2.2 hexp (cfg_error _ _ _ _) ((congrArg answerWord (cfg_output _ _ _ _)).trans hw1),
    returns hagc.2.2.2 hexq (cfg_error _ _ _ _) ((congrArg answerWord (cfg_output _ _ _ _)).trans hw2)⟩
  rw [rampWords_of_shadow (W := (endDeposit.cfg acsW m1 w1).devm.state) (l := endDeposit.stor) (hag1.2.2.1 poolA),
    rampWords_of_shadow (W := (endCall.cfg acsW mc wc).devm.state) (l := endCall.stor) (hagc.2.2.1 poolA), hramp]

/-- **The word `get_virtual_price()` returns falls on the deployed bytes, from the deployment state.** -/
theorem virtual_price_falls : Curve3PoolPublic.virtual_price_falls := by
  obtain ⟨dep, m, mid, post, hat, hd, -, hc1, hc2, hr, hp, hp'⟩ := falls_at_witness
  have hsel : depositData amt0 amt1 amt2 = abiSelectorBytes selAddLiquidity ++
      (wordB amt0 ++ wordB amt1 ++ wordB amt2 ++ wordB 0) := by decide +kernel
  exact ⟨worldW, dep, m, mid, post, 10 ^ 18, 10 ^ 18 - 1, hat, ⟨_, hd.trans hsel⟩, hc1, hc2, hr,
    hp, hp', by decide⟩

end Blanc.Composition.Curve3PoolVirtualPriceFalls
