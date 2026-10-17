import Blanc.Lift.Curve3Pool.Creation.Check
import Blanc.Lift.Curve3Pool.Creation.Jumps
import Blanc.Lift.Curve3Pool.Creation.Walk
import Blanc.Lift.Deploy
import Blanc.BalanceAlgebra
import Blanc.ForkUniform
import Mathlib.Tactic.FinCases

/-!
# U7: INIT by deployment of the 3pool's recorded creation input

* `pool_create`: executing the 3pool's recorded creation input (21,967 bytes with its ABI
  arguments: owner `0x6e8f…3eb7`, coins DAI/USDC/USDT, pool token 3Crv, `A = 100`,
  `fee = 4,000,000`, `admin_fee = 0`; `Creation/Cert.lean`, registered as
  `curve-3pool-creation`) as a zero-value CREATE message under a covered fork, at a block
  timestamp `t` whose kill deadline `t + KILL_DEADLINE_DT` does not wrap, succeeds, installs the
  creation input's runtime window `[488, 21687)` (`runtimeWindow`), and leaves the storage
  `deployedStor t`.
* `deployedStor_checkpoint`: that storage satisfies U2's checkpoint predicate
  (`Layout.lean`'s `Checkpoint`) at the model state `poolInitState t`, which is exactly the
  model constructor's output on the recorded arguments (`init_recorded`); and
  `deployedStor_off`: every slot outside the pool's slots is zero, so the storage is the model
  state's encoding and nothing else.
* `pool_deploy_covered`: the recorded deployment message (deployer `0xbabe…9f67` at nonce 43,
  the recorded block timestamp) under every covered fork.
* `deployedStor_wrong_fee`: the statement control: the model state of a constructor call with any
  other `_fee` is not abstracted by the deployed storage.

No hash premise (M5): the only digest, `keccak(0)`, is a kernel evaluation (`coinsBase_eq`), and
the pool's slots are pairwise distinct by a kernel decision (`poolSlots_nodup`).

**Scope.** The runtime window is the creation input's bytes; that they equal the certified deployed
runtime `Blanc.Lift.Curve3Pool.code` is the one-line kernel fact
`runtimeWindow = Blanc.Lift.Curve3Pool.code.toList` (U0 §1.2 confirms the bytes), added once the
runtime certificate lands. Modeled deployment under the covered forks' rules (the historical block
10,809,473 predates them), not historical inclusion. Gas: any message gas in
`[4,500,000, 2^64)` suffices (the code deposit alone is 4,239,800).
-/

namespace Blanc.Lift.Curve3Pool.Creation

open Jaune Blanc.Lift Blanc.Lift.Curve3Pool Blanc.ForkUniform Blanc.StableSwapNewton

/-! ## The deployed storage -/

/-- The kill deadline word at timestamp `t`. -/
def killWord (t : B256) : B256 := t + 0x4f1a00

/-- The constructor's stores before the kill deadline (concrete). -/
def coreStor0 : Stor :=
  ((((((((Stor.empty.set (coinSlot 0) coin0W).set (coinSlot 1) coin1W).set (coinSlot 2) coin2W).set
    initialASlot ampW).set futureASlot ampW).set feeSlot feeW).set adminFeeSlot adminFeeW).set
    ownerSlot ownerW)

/-- The constructor's stores without the kill deadline (concrete). -/
def coreStor : Stor := coreStor0.set tokenSlot tokenW

/-- **The storage the constructor leaves** at block timestamp `t`, in store order. -/
def deployedStor (t : B256) : Stor :=
  (coreStor0.set killDeadlineSlot (killWord t)).set tokenSlot tokenW

theorem deployedStor_get (t x : B256) :
    (deployedStor t).get x = if killDeadlineSlot = x then killWord t else coreStor.get x := by
  unfold deployedStor coreStor
  rw [Stor.get_set_ite, Stor.get_set_ite, Stor.get_set_ite]
  by_cases h1 : tokenSlot = x
  · rw [ite_eq_left h1, ite_eq_left h1, ite_eq_right (by rw [← h1]; decide)]
  · rw [ite_eq_right h1, ite_eq_right h1]

theorem ctor_stor (sevm : Sevm) (b : Devm)
    (hempty : Devm.getStor b sevm.currentTarget = Stor.empty) :
    Devm.getStor (tw10 sevm b) sevm.currentTarget = deployedStor sevm.benvStat.time := by
  simp only [tw10, tw9, tw8, tw7, tw6, tw5, tw4, tw3, tw2, tw1, afterSstore_getStor_self, hempty,
    deployedStor, coreStor0, killWord]

/-! ## The model's constructor on the recorded arguments -/

def ownerN : Nat := 0x6e8f6d1da6232d5e40b0b8758a0145d6c5123eb7
def coinsN : V3 := ⟨0x6b175474e89094c44da98b954eedeac495271d0f,
  0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48, 0xdac17f958d2ee523a2206206994597c13d831ec7⟩
def tokenN : Nat := 0x6c3f90f043a72fa612cbac8115ee7e52bde6e490

/-- The model state the constructor produces at timestamp `t` from the recorded arguments. -/
def poolInitState (t : Nat) : State where
  coins := coinsN
  balances := V3.zero
  fee := 4000000
  adminFee := 0
  owner := ownerN
  token := tokenN
  initialA := 100
  futureA := 100
  initialATime := 0
  futureATime := 0
  adminActionsDeadline := 0
  transferOwnershipDeadline := 0
  futureFee := 0
  futureAdminFee := 0
  futureOwner := 0
  isKilled := false
  killDeadline := t + killDeadlineDt

/-- **The model's `init` on the recorded arguments** (no call value) is `poolInitState t`. -/
theorem init_recorded {t : Nat} (ht : t + killDeadlineDt < 2 ^ 256) :
    init ownerN coinsN tokenN 100 4000000 0 t 0 = some (poolInitState t) := by
  have hreq : (0 = 0 ∧ ownerN < 2 ^ 160 ∧ coinsN.v0 < 2 ^ 160 ∧ coinsN.v1 < 2 ^ 160 ∧
      coinsN.v2 < 2 ^ 160 ∧ tokenN < 2 ^ 160) ∧ (coinsN.v0 ≠ 0 ∧ coinsN.v1 ≠ 0 ∧ coinsN.v2 ≠ 0) :=
    by decide
  unfold init req
  rw [ite_eq_left hreq.1.1, ite_eq_left hreq.1.2, ite_eq_left hreq.2]
  unfold chkAdd
  rw [ite_eq_left (show t + killDeadlineDt < wordSize from ht)]
  rfl

/-! ## The checkpoint predicate at deployment -/

/-- **The deployed storage satisfies U2's checkpoint predicate** at the model's constructor
output. -/
theorem deployedStor_checkpoint {t : B256} (ht : t.toNat + killDeadlineDt < 2 ^ 256) :
    Checkpoint (deployedStor t) (poolInitState t.toNat) := by
  have hk : ∀ x, killDeadlineSlot ≠ x → (deployedStor t).get x = coreStor.get x :=
    fun x h => by rw [deployedStor_get, ite_eq_right h]
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · intro i
    fin_cases i
    · rw [hk _ (by decide +kernel)]; dsimp only [poolInitState]; decide +kernel
    · rw [hk _ (by decide +kernel)]; dsimp only [poolInitState]; decide +kernel
    · rw [hk _ (by decide +kernel)]; dsimp only [poolInitState]; decide +kernel
  · intro i
    fin_cases i
    · rw [hk _ (by decide +kernel)]; dsimp only [poolInitState]; decide +kernel
    · rw [hk _ (by decide +kernel)]; dsimp only [poolInitState]; decide +kernel
    · rw [hk _ (by decide +kernel)]; dsimp only [poolInitState]; decide +kernel
  · rw [hk _ (by decide)]; dsimp only [poolInitState]; decide +kernel
  · rw [hk _ (by decide)]; dsimp only [poolInitState]; decide +kernel
  · rw [hk _ (by decide)]; dsimp only [poolInitState]; decide +kernel
  · rw [hk _ (by decide)]; dsimp only [poolInitState]; decide +kernel
  · rw [hk _ (by decide)]; dsimp only [poolInitState]; decide +kernel
  · rw [hk _ (by decide)]; dsimp only [poolInitState]; decide +kernel
  · rw [hk _ (by decide)]; dsimp only [poolInitState]; decide +kernel
  · rw [hk _ (by decide)]; dsimp only [poolInitState]; decide +kernel
  · rw [hk _ (by decide)]; dsimp only [poolInitState]; decide +kernel
  · rw [hk _ (by decide)]; dsimp only [poolInitState]; decide +kernel
  · rw [hk _ (by decide)]; dsimp only [poolInitState]; decide +kernel
  · rw [hk _ (by decide)]; dsimp only [poolInitState]; decide +kernel
  · rw [hk _ (by decide)]; dsimp only [poolInitState]; decide +kernel
  · rw [hk _ (by decide)]; dsimp only [poolInitState]; decide +kernel
  · rw [deployedStor_get, ite_eq_left rfl]
    exact kill_toNat ht
  · rw [hk _ (by decide)]; decide +kernel
  · show ownerN < 2 ^ 160 ∧ coinsN.v0 < 2 ^ 160 ∧ coinsN.v1 < 2 ^ 160 ∧ coinsN.v2 < 2 ^ 160 ∧
      tokenN < 2 ^ 160 ∧ 0 < 2 ^ 160
    decide

/-- **Exactness**: every slot outside the pool's slots is zero in the deployed storage. -/
theorem deployedStor_off (t x : B256) (hx : x ∉ poolSlots) : (deployedStor t).get x = 0 := by
  simp only [poolSlots, List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
  obtain ⟨h0, h1, h2, -, -, -, h6, h7, h8, h9, h10, h11, -, -, -, -, -, -, -, -, h20, -⟩ := hx
  rw [deployedStor_get, ite_eq_right (Ne.symm h20)]
  unfold coreStor coreStor0
  simp only [Stor.get_set_ite, Ne.symm h0, Ne.symm h1, Ne.symm h2, Ne.symm h6, Ne.symm h7,
    Ne.symm h8, Ne.symm h9, Ne.symm h10, Ne.symm h11, ↓reduceIte]
  simp only [Stor.get, Stor.empty, Std.TreeMap.empty_eq_emptyc, Std.TreeMap.getD_emptyc]

/-- **Statement control**: the model state of a constructor call with any other `_fee` is not
abstracted by the deployed storage (its slot 2 holds the recorded `4,000,000`). -/
theorem deployedStor_wrong_fee {t fee' : Nat} {s : State} (hfee : fee' ≠ 4000000) (u : B256)
    (hs : init ownerN coinsN tokenN 100 fee' 0 t 0 = some s) :
    ¬ Abstracts (deployedStor u) s := by
  intro h
  have h2 : (deployedStor u).get feeSlot = feeW := by
    rw [deployedStor_get, ite_eq_right (by decide)]; decide +kernel
  have hsfee : s.fee = fee' := by
    have hreq : (0 = 0 ∧ ownerN < 2 ^ 160 ∧ coinsN.v0 < 2 ^ 160 ∧ coinsN.v1 < 2 ^ 160 ∧
        coinsN.v2 < 2 ^ 160 ∧ tokenN < 2 ^ 160) ∧
        (coinsN.v0 ≠ 0 ∧ coinsN.v1 ≠ 0 ∧ coinsN.v2 ≠ 0) := by decide
    unfold init req at hs
    rw [ite_eq_left hreq.1.1, ite_eq_left hreq.1.2, ite_eq_left hreq.2] at hs
    cases hk : chkAdd t killDeadlineDt with
    | none => rw [hk] at hs; cases hs
    | some kd =>
      rw [hk] at hs
      rw [← Option.some.inj hs]
  have := h.fee
  rw [h2, hsfee] at this
  exact hfee (this.symm.trans (by decide))

/-! ## Deployment -/

/-- **Deploying the 3pool.** The recorded creation input, executed as a zero-value CREATE message
with enough gas under a covered fork, at a timestamp whose kill deadline does not wrap, succeeds;
the new account's code is the creation input's runtime window and its storage is
`deployedStor` of the block timestamp. -/
theorem pool_create (msg : Msg) (hvalue : msg.value = 0)
    (hcodeAddress : msg.codeAddress = .none) (hcode : msg.code = code)
    (hgas : 4500000 ≤ msg.gas) (hfork : CoveredFork msg.benv.stat.fork)
    (hstatic : msg.isStatic = false)
    (hmax : 0x52cf ≤ msg.benv.stat.rules.code.maxCodeSize)
    (ht : msg.benv.stat.time.toNat + killDeadlineDt < 2 ^ 256) :
    ∃ post, processCreateMessage msg = .ok post ∧
      (post.getCode msg.currentTarget).toList = runtimeWindow ∧
      Devm.getStor post msg.currentTarget = deployedStor msg.benv.stat.time ∧
      post.error = .none := by
  obtain ⟨benv, htransfer⟩ :=
    benvAfterTransfer_exists_zero (msg := processCreateMessage.msg msg) hvalue
  set sevm := initSevm (createSeed msg benv) with hsevm
  set b := initDevm (createSeed msg benv) with hb
  have hstat : sevm.benvStat = msg.benv.stat := by
    show benv.stat = (processCreateMessage.msg msg).benv.stat
    exact benvAfterTransfer_stat htransfer
  have fr : CtorFrame sevm := ⟨by rw [hstat]; exact hfork, hstatic⟩
  have hempty : Devm.getStor b sevm.currentTarget = Stor.empty := by
    show benv.state.getStor msg.currentTarget = _
    rw [benvAfterTransfer_ok_getStor htransfer msg.currentTarget (Or.inl hvalue),
      processCreateMessage_msg_getStor_currentTarget]
  have ht' : sevm.benvStat.time.toNat + killDeadlineDt < 2 ^ 256 := by rw [hstat]; exact ht
  have hle := ctorCost_le sevm b
  obtain ⟨raw, hrun, hout, herr, hst, hgasLeft⟩ :=
    ctor_run_facts fr hcode hvalue ht' (b := b) (G := msg.gas - ctorCost sevm b)
      (by unfold gCallStipend; omega)
  have hpre0 : St b [] Mem.empty (msg.gas - ctorCost sevm b + ctorCost sevm b) = b :=
    pre_eq_St rfl rfl (by show _ = msg.gas; omega)
  rw [hpre0] at hrun
  have hlen : raw.output.length = 0x52cf := by rw [hout]; exact runtimeWindow_length
  obtain ⟨post, hpost, hcodePost, hstorPost, herrPost⟩ := liftCreate_ok cert_check jumps_ok msg
    hcodeAddress hcode hfork htransfer hrun (by rw [herr]; rfl)
    (by rw [hout]; exact runtimeWindow_head)
    (by rw [hlen, hgasLeft]; unfold gasCodeDeposit; omega)
    (by rw [hlen]; exact hmax)
  refine ⟨post, hpost, hcodePost.trans hout, ?_, herrPost⟩
  have hnonempty : ¬ ({ raw.state.get msg.currentTarget with
      code := ⟨⟨raw.output⟩⟩ } : Acct).Empty := by
    intro empty
    have zero : raw.output.length = 0 := empty.1
    omega
  simp only [hstorPost, Acct.clearIfEmpty_stor, hnonempty, ↓reduceIte]
  show Devm.getStor raw sevm.currentTarget = _
  rw [hst, ctor_stor sevm b hempty, hstat]

/-! ## The recorded deployment, closed -/

/-- The recorded deployer of the 3pool (creation transaction `0x20793bbf…22f3ac6`, block
10,809,473, sender nonce 43). -/
def deployer : Adr := 0xbabe61887f1de2713c6f97e567623453d3c79f67

/-- The 3pool's address. -/
def poolAddress : Adr := 0xbebc44782c7db0a1a60cb6fe97d0b483032ff1c7

/-- The recorded block timestamp. -/
def deployTime : B256 := 1599414978

/-- The pool's address is the CREATE address of the deployer at nonce 43. -/
theorem poolAddress_eq : poolAddress = computeContractAddress deployer 43 := by
  have hsender : deployer.toBytes = [0xba, 0xbe, 0x61, 0x88, 0x7f, 0x1d, 0xe2, 0x71, 0x3c, 0x6f, 0x97, 0xe5, 0x67, 0x62, 0x34, 0x53, 0xd3, 0xc7, 0x9f, 0x67] := by decide +kernel
  have hnonce : (UInt64.toBytes 43).sig = [0x2b] := by decide +kernel
  have hrlp : BLT.toBytes (.list [.bytes [0xba, 0xbe, 0x61, 0x88, 0x7f, 0x1d, 0xe2, 0x71, 0x3c, 0x6f, 0x97, 0xe5, 0x67, 0x62, 0x34, 0x53, 0xd3, 0xc7, 0x9f, 0x67], .bytes [0x2b]]) =
      [0xd6, 0x94, 0xba, 0xbe, 0x61, 0x88, 0x7f, 0x1d, 0xe2, 0x71, 0x3c, 0x6f, 0x97, 0xe5, 0x67, 0x62, 0x34, 0x53, 0xd3, 0xc7, 0x9f, 0x67, 0x2b] := by
    simp only [BLT.toBytes, BLTs.toBytes, BLTs.toBytesJoin, List.length_cons, List.length_nil,
      zero_add, Nat.reduceAdd, Nat.reduceLT, ↓reduceIte, Nat.toUInt8_eq, UInt8.reduceOfNat,
      UInt8.reduceAdd, UInt8.reduceLT, List.append_nil, List.cons_append, List.nil_append]
  unfold computeContractAddress
  simp only [hsender, hnonce, hrlp]
  decide +kernel

/-- The recorded creation message: from the recorded deployer, the recorded creation input with
its arguments, to the pool's address, zero value, 5,000,000 gas, empty call data, Jaune's default
environment (empty world) at the recorded block timestamp. A message, not a validated
transaction. -/
def deployMsg : Msg where
  benv := { (default : Benv) with stat := { (default : Benv).stat with time := deployTime } }
  tenv := default
  caller := deployer
  target := none
  currentTarget := poolAddress
  gas := 5000000
  value := 0
  data := []
  codeAddress := none
  code := code
  depth := 1024
  shouldTransferValue := true
  isStatic := false
  accessedAddresses := .emptyWithCapacity
  accessedStorageKeys := .emptyWithCapacity
  disablePrecompiles := false

/-- **U7: the recorded 3pool deployment under every covered fork.** The pool's address is the
deployer's CREATE address at nonce 43; the recorded creation message succeeds, installs the
runtime window, leaves `deployedStor deployTime`, which satisfies U2's checkpoint predicate at the
model constructor's output on the recorded arguments, and is zero off the pool's slots. -/
theorem pool_deploy_covered (f : Fork) (hf : CoveredFork f) :
    poolAddress = computeContractAddress deployer 43 ∧
    init ownerN coinsN tokenN 100 4000000 0 deployTime.toNat 0 =
      some (poolInitState deployTime.toNat) ∧
    ∃ post, processCreateMessage (deployMsg.withFork f) = .ok post ∧
      (post.getCode poolAddress).toList = runtimeWindow ∧
      Devm.getStor post poolAddress = deployedStor deployTime ∧
      Checkpoint (Devm.getStor post poolAddress) (poolInitState deployTime.toNat) ∧
      (∀ x, x ∉ poolSlots → (Devm.getStor post poolAddress).get x = 0) := by
  have ht : deployTime.toNat + killDeadlineDt < 2 ^ 256 := by decide
  refine ⟨poolAddress_eq, init_recorded ht, ?_⟩
  obtain ⟨post, h1, h2, h3, -⟩ := pool_create (deployMsg.withFork f) rfl rfl rfl
    (by dsimp only [Msg.withFork, Benv.withFork, BenvStat.withFork]; decide) hf rfl
    (hf.cases (motive := fun f =>
      0x52cf ≤ (deployMsg.withFork f).benv.stat.rules.code.maxCodeSize)
      (by dsimp only [Msg.withFork, Benv.withFork, BenvStat.withFork]; decide)
      (by dsimp only [Msg.withFork, Benv.withFork, BenvStat.withFork]; decide)
      (by dsimp only [Msg.withFork, Benv.withFork, BenvStat.withFork]; decide)
      (by dsimp only [Msg.withFork, Benv.withFork, BenvStat.withFork]; decide)) ht
  have h3' : Devm.getStor post poolAddress = deployedStor deployTime := h3
  refine ⟨post, h1, h2, h3', ?_, ?_⟩
  · rw [h3']; exact deployedStor_checkpoint ht
  · intro x hx; rw [h3']; exact deployedStor_off deployTime x hx

end Blanc.Lift.Curve3Pool.Creation
