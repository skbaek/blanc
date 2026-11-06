import Blanc.Composition.Curve3PoolVirtualPriceFallsChain
import Blanc.Lift.Curve3Pool.Decode

/-!
# The returned virtual price falls on the deployed bytes, from the deployment state

`virtual_price_falls`: starting from the storage the recorded creation left (the pool's
`Curve3Pool.Creation.deployedStor` at its recorded timestamp, 3Crv's for its recorded deployer with the minter
set to the pool), with DAI, USDC's proxy over `FiatTokenV2` and USDT holding their deployed bytes,
there is a first deposit and then a call after which the word `get_virtual_price()` returns is
lower, the amplification words unchanged.  All four calls, with every child frame, are kernel
evaluations of the bytes (`Curve3PoolVirtualPriceFallsFacts*`), composed in `Curve3PoolVirtualPriceFallsChain`; no pool or
coin model enters.

**What this does not claim.**  The deposit is a path the chain could have taken, not one it took: no
reachability from a real history is stated, and the depositor's coin balances and allowances are a
choice of the witness.  The calls run under Muir Glacier, the fork of the recorded creation blocks, at
the pool's creation block number and timestamp.  They are message calls with 10,000,000 gas, not
validated transactions in a block.  Nothing here speaks of any chain state after the creation.

The deposit is `[540712138941758899472585, 1160326029455, 1949013540497]`, the call
`remove_liquidity_one_coin(8, 0, 0)`, the word goes from `10^18` to `10^18 - 1`.
-/

namespace Blanc.Composition.Curve3PoolVirtualPriceFalls

open Jaune Blanc Blanc.Lift Blanc.Lift.Witness Blanc.Lift.NodeWalk
open Blanc.Lift.Curve3Pool.VirtualPriceFalls
open Blanc.Lift.Curve3Pool (coinSlot balanceSlot feeSlot adminFeeSlot ownerSlot tokenSlot initialASlot futureASlot initialATimeSlot futureATimeSlot killDeadlineSlot answerWord selGetVirtualPrice selAddLiquidity)

/-! ## The statement -/

/-- A message asks the pool for `get_virtual_price()` at `w`, statically. -/
structure AsksPrice (m : Msg) (w : Jaune.State) : Prop where
  target : m.currentTarget = poolA
  state : m.benv.state = w
  code : m.code = w.getCode poolA
  data : m.data = abiSelectorBytes selGetVirtualPrice

/-- `get_virtual_price()` at `w`, asked in the environment `env`, returns `p`. -/
def ReturnsPrice (env : BenvStat) (w : Jaune.State) (p : Nat) : Prop :=
  ∃ m post, AsksPrice m w ∧ m.benv.stat = env ∧ exec (initEvm m) = .ok post ∧ post.error = none ∧
    answerWord post.output = p

/-- A top-level message to the pool at `w`, under Muir Glacier, with `w` as its original state, commits
and ends in `post`. -/
structure CallCommits (m : Msg) (w : Jaune.State) (post : Devm) : Prop where
  target : m.currentTarget = poolA
  state : m.benv.state = w
  orig : m.benv.stat.origState = w
  code : m.code = w.getCode poolA
  fork : m.benv.stat.fork = .muirGlacier
  ran : exec (initEvm m) = .ok post
  ok : post.error = none

/-- **The world the recorded creations and the minter assignment leave**: the contracts' storage
exactly, each coin its deployed bytes, USDC's proxy over the version it served then, and the pool
holding none of any coin.  Who else holds coins is free. -/
structure AtDeployment (w : Jaune.State) : Prop where
  poolCode : w.getCode poolA = Curve3Pool.code
  poolStor : w.getStor poolA = Curve3Pool.Creation.deployedStor Curve3Pool.Creation.deployTime
  c3Code : w.getCode c3A = Curve3Crv.code
  c3Stor : w.getStor c3A =
    (Curve3Crv.Creation.deployedStor Curve3Crv.Creation.deployer.toB256).set 6 poolA.toB256
  daiCode : w.getCode daiA = Dai.code
  usdtCode : w.getCode usdtA = Usdt.code
  idEmpty : w.getCode 4 = ByteArray.empty
  usdcCode : w.getCode usdcA = Usdc.Proxy.code
  usdcV2 : w.getCode ((w.getStor usdcA).get Usdc.implSlot).toAdr = Usdc.ImplV2.code
  emptyDai : (w.getStor daiA).get (mapSlot poolA.toB256 2) = 0
  emptyUsdc : (w.getStor usdcA).get (mapSlot poolA.toB256 9) = 0
  emptyUsdt : (w.getStor usdtA).get (mapSlot poolA.toB256 2) = 0

/-- The pool's four amplification words. -/
def rampWords (w : Jaune.State) : List B256 :=
  [initialASlot, futureASlot, initialATimeSlot, futureATimeSlot].map (w.getStor poolA).get

/-- The message is a call of `add_liquidity`. -/
def IsDeposit (m : Msg) : Prop := ∃ rest, m.data = abiSelectorBytes selAddLiquidity ++ rest

/-- **The word `get_virtual_price()` returns falls across one call at fixed amplification**, from the
world the recorded deployment leaves plus one first deposit.  A claim about the bytes: the deposit is
a path the chain could have taken, not one it took. -/
def VirtualPriceFalls : Prop :=
  ∃ (w : Jaune.State) (dep m : Msg) (mid post : Devm) (p p' : Nat),
    AtDeployment w ∧ IsDeposit dep ∧ CallCommits dep w mid ∧ CallCommits m mid.state post ∧
    rampWords mid.state = rampWords post.state ∧
    ReturnsPrice m.benv.stat mid.state p ∧ ReturnsPrice m.benv.stat post.state p' ∧ p' < p

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
  poolCode := by rw [acctAgree_get_code world_acct]; kernel_rfl
  poolStor := by kernel_rfl
  c3Code := by rw [acctAgree_get_code world_acct]; kernel_rfl
  c3Stor := by kernel_rfl
  daiCode := by rw [acctAgree_get_code world_acct]; kernel_rfl
  usdtCode := by rw [acctAgree_get_code world_acct]; kernel_rfl
  idEmpty := by rw [acctAgree_get_code world_acct]; kernel_rfl
  usdcCode := by rw [acctAgree_get_code world_acct]; kernel_rfl
  usdcV2 := by
    have h : (worldW.getStor usdcA).get Usdc.implSlot = implA.toB256 :=
      (world_stor usdcA Usdc.implSlot).trans (by kernel_rfl)
    have hi : implA.toB256.toAdr = implA := by decide +kernel
    rw [h, hi]
    exact (acctAgree_get_code world_acct implA).trans (by kernel_rfl)
  emptyDai := (world_stor daiA _).trans (by kernel_rfl)
  emptyUsdc := (world_stor usdcA _).trans (by kernel_rfl)
  emptyUsdt := (world_stor usdtA _).trans (by kernel_rfl)

/-! ## The four calls' boundary decisions -/

theorem statOf_orig (l : StorShadow) : (statOf l).origState = origOf l := rfl

theorem statOf_fork (l : StorShadow) : (statOf l).fork = .muirGlacier := rfl

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
    (hcode : AcctAgree W acsW) (hf : stat.fork = .muirGlacier)
    (hr : exec (initEvm (msgOf W (stat.withOrig W) d st)) = .ok post) (he : post.error = none) :
    CallCommits (msgOf W (stat.withOrig W) d st) W post where
  target := rfl
  state := rfl
  orig := rfl
  code := by rw [acctAgree_get_code hcode]; show Curve3Pool.code = _; kernel_rfl
  fork := hf
  ran := hr
  ok := he

/-- A price question gets its word. -/
theorem returns {W O : Jaune.State} {stat : BenvStat} {post : Devm} {p : Nat}
    (hcode : AcctAgree W acsW)
    (hr : exec (initEvm (msgOf W (stat.withOrig O) priceData true)) = .ok post)
    (he : post.error = none) (hp : answerWord post.output = p) :
    ReturnsPrice (stat.withOrig O) W p :=
  ⟨msgOf W (stat.withOrig O) priceData true, post,
    ⟨rfl, rfl, by rw [acctAgree_get_code hcode]; show Curve3Pool.code = _; kernel_rfl,
      by show priceData = _; decide +kernel⟩, rfl, hr, he, hp⟩

theorem data1_eq : data1 = depositData amt0 amt1 amt2 := by kernel_rfl
theorem data2_eq : data2 = oneCoinData 8 := by kernel_rfl
theorem dataP_eq : dataP = priceData := by kernel_rfl

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
    commits world_acct (by rw [stat1_eq]; exact statOf_fork _) hex1 (cfg_error _ _ _ _),
    commits hag1.2.2.2 (by rw [stat2_eq]; exact statOf_fork _) hexc (cfg_error _ _ _ _), ?_,
    returns hag1.2.2.2 hexp (cfg_error _ _ _ _) ((congrArg answerWord (cfg_output _ _ _ _)).trans hw1),
    returns hagc.2.2.2 hexq (cfg_error _ _ _ _) ((congrArg answerWord (cfg_output _ _ _ _)).trans hw2)⟩
  have e1 : ∀ k, ((endDeposit.cfg acsW m1 w1).devm.state.getStor poolA).get k =
      lookupS endDeposit.stor poolA k := hag1.2.2.1 poolA
  have e2 : ∀ k, ((endCall.cfg acsW mc wc).devm.state.getStor poolA).get k =
      lookupS endCall.stor poolA k := hagc.2.2.1 poolA
  simp only [List.map_cons, List.map_nil] at hramp
  simp only [rampWords, List.map_cons, List.map_nil]
  rw [e1, e1, e1, e1, e2, e2, e2, e2]
  exact hramp

/-- **The word `get_virtual_price()` returns falls on the deployed bytes, from the deployment state.** -/
theorem virtual_price_falls : VirtualPriceFalls := by
  obtain ⟨dep, m, mid, post, hat, hd, -, hc1, hc2, hr, hp, hp'⟩ := falls_at_witness
  have hsel : depositData amt0 amt1 amt2 = abiSelectorBytes selAddLiquidity ++
      (wordB amt0 ++ wordB amt1 ++ wordB amt2 ++ wordB 0) := by decide +kernel
  exact ⟨worldW, dep, m, mid, post, 10 ^ 18, 10 ^ 18 - 1, hat, ⟨_, hd.trans hsel⟩, hc1, hc2, hr,
    hp, hp', by decide⟩

end Blanc.Composition.Curve3PoolVirtualPriceFalls
