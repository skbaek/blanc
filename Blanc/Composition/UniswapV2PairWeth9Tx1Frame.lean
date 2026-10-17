import Blanc.Lift.VyperNonreentrantDeployed.Token20.RunTransfer
import Blanc.ForwardStorageAccess

/-!
# The closed instance's first transaction: data and the token frame

The closed minimal instance of the Uniswap V2 Pair / WETH9 composition (goal C6(b)) runs two
signed type-2 transactions from the trader.  The first, `tx1`, is `X.transfer(pair, amountIn)` on
the synthetic 299-byte Token20 `X`.  This file fixes the instance's addresses, the amount and the
unsigned fields of `tx1` (the signature is a parameter, supplied with its recovery by the signing
unit), and proves the exact token frame: from a frame entry with the two balance slots cold and
holding `xT` (trader) and `xP` (pair), the frame returns `1` with exactly the two slot writes, at
exactly 10173 gas.
-/

namespace Blanc.Composition.UniswapV2PairWeth9Instance

open Jaune Blanc Blanc.Lift
open Blanc.Lift.VyperNonreentrantDeployed.Token20 (trTo trVal transferGas transferPost
  transfer_runExact mvFrom mvTo mv1 mv2 mv3 mv4 mvCost transferBase retPost okMem balSlot code
  cert_check cert_jumpsOk)

/-- The trader: the address of the published secp256k1 test key `1`. -/
def trader : Adr := 0x7e5f4552091a69125d5dfcb7b8c2659029395bdf

/-- The synthetic token `X` (Token20's runtime), the pair's `token0`. -/
def tokenX : Adr := 0x1111111111111111111111111111111111111111

/-- The Uniswap V2 Pair of the instance (`token0 = X`, `token1 = WETH9`). -/
def pair : Adr := 0x2222222222222222222222222222222222222222

/-- The amount of `X` the trader sends to the pair in `tx1`. -/
def amountIn : B256 := 1000

/-- `transfer(pair, amountIn)` calldata: selector `0xa9059cbb`, the pair word, the amount. -/
def tx1Data : Bytes :=
  abiSelectorBytes 0xa9059cbb ++ pair.toB256.toBytes ++ amountIn.toBytes

/-- **The first transaction**: type 2, chain 1, priority fee 1, fee cap 8, gas 50000, nonce 0,
value 0, to `X`, calldata `transfer(pair, amountIn)`, signed by `(v, r, s)`. -/
def tx1 (v : Nat) (r s : Bytes) : Tx :=
  { nonce := 0, gas := 50000, value := 0, data := tx1Data, v := v, r := r, s := s
    type := .two 1 1 8 (some tokenX) [] }

/-- The token frame's world: `X`'s trader slot debited, then its pair slot credited. -/
def tx1FrameWrites (st : Jaune.State) (xT xP : B256) : Jaune.State :=
  (st.setStorVal tokenX (balSlot trader) (xT - amountIn)).setStorVal tokenX (balSlot pair)
    (amountIn + xP)

theorem trader_ne_tokenX : trader ≠ tokenX := by decide +kernel
theorem trader_ne_pair : trader ≠ pair := by decide +kernel
theorem tokenX_ne_pair : tokenX ≠ pair := by decide +kernel

theorem balSlot_trader_ne_pair : balSlot trader ≠ balSlot pair := by decide +kernel

/-- An `SSTORE` that changes a nonzero, not yet rewritten slot to another nonzero value costs
`2900` beyond the access charge. -/
theorem sstoreValueCost_update {x y : B256} (hx : x ≠ 0) (hxy : x ≠ y) :
    sstoreValueCost x x y = 2900 := by
  unfold sstoreValueCost
  rw [ite_eq_left ⟨rfl, hxy⟩, ite_eq_right hx]
  rfl

/-- Such an `SSTORE` leaves the refund counter alone. -/
theorem sstoreNewRefundCounter_update (gas : GasSchedule) {x y : B256} (rc : Int)
    (hx : x ≠ 0) (hy : y ≠ 0) (hxy : x ≠ y) :
    sstoreNewRefundCounter gas y x x rc = rc := by
  unfold sstoreNewRefundCounter
  simp only [ne_eq, hxy, not_false_eq_true, ↓reduceIte, hx, hy, and_false]

/-- Membership after a selected warm-or-cold access: the key, or an earlier member. -/
theorem mem_sloadAccessedStorageKeys_iff {t : Adr} {K : KeySet} {k : B256} {x : Adr × B256} :
    x ∈ sloadAccessedStorageKeys t K k ↔ x = (t, k) ∨ x ∈ K := by
  unfold sloadAccessedStorageKeys
  split
  · rename_i hm
    constructor
    · exact Or.inr
    · rintro (rfl | h)
      · exact hm
      · exact h
  · rw [Std.HashSet.mem_insert, beq_iff_eq]
    constructor
    · rintro (h | h)
      · exact Or.inl h.symm
      · exact Or.inr h
    · rintro (h | h)
      · exact Or.inl h.symm
      · exact Or.inr h

/-- A returning tail keeps the base's error, refund, deletions, logs and world. -/
theorem retPost_keeps (b : Devm) (S : List B256) (M : Mem) (G : Nat) (w : B256) :
    (retPost b S M G w).error = b.error ∧ (retPost b S M G w).refundCounter = b.refundCounter ∧
      (retPost b S M G w).accountsToDelete = b.accountsToDelete ∧
      (retPost b S M G w).logs = b.logs ∧ (retPost b S M G w).state = b.state :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

section Frame

variable {sevm : Sevm} {pre : Devm} {xT xP : B256}

/-- The values, charges and refund of `transfer(pair, amountIn)` from `trader` at `X`. -/
theorem tx1_move_facts
    (hcaller : sevm.caller = trader) (htarget : sevm.currentTarget = tokenX)
    (hto : trTo sevm = pair) (hval : trVal sevm = amountIn)
    (hT : pre.getStorVal tokenX (balSlot trader) = xT)
    (hTo : pre.getOrigStorVal sevm tokenX (balSlot trader) = xT)
    (hP : pre.getStorVal tokenX (balSlot pair) = xP)
    (hPo : pre.getOrigStorVal sevm tokenX (balSlot pair) = xP)
    (hcoldT : (tokenX, balSlot trader) ∉ pre.accessedStorageKeys)
    (hcoldP : (tokenX, balSlot pair) ∉ pre.accessedStorageKeys)
    (hcov : amountIn < xT) (hP0 : xP ≠ 0) (hnof : B256.Nof amountIn xP) :
    mvFrom sevm pre sevm.caller = xT ∧
      mvTo sevm pre sevm.caller (trTo sevm) (trVal sevm) = xP ∧
      transferGas sevm pre = 10173 ∧
      (transferBase sevm pre).refundCounter = pre.refundCounter ∧
      (transferBase sevm pre).state = tx1FrameWrites pre.state xT xP := by
  rw [hcaller, hto, hval]
  rw [← htarget] at hT hTo hP hPo hcoldT hcoldP
  have hTnat := B256.toNat_lt_toNat hcov
  have ha : amountIn.toNat = 1000 := rfl
  have hxT0 : xT ≠ 0 := by
    rintro rfl; rw [B256.toNat_zero] at hTnat; omega
  have hsubNat : (xT - amountIn).toNat = xT.toNat - 1000 := by
    rw [B256.toNat_sub_eq_of_le _ _ (B256.le_of_lt hcov), ha]
  have hsub0 : xT - amountIn ≠ 0 := by
    intro h; rw [h, B256.toNat_zero] at hsubNat; omega
  have hsubne : xT ≠ xT - amountIn := by
    intro h; rw [← h] at hsubNat; omega
  have haddNat : (amountIn + xP).toNat = 1000 + xP.toNat := by
    rw [B256.toNat_add_eq_of_nof _ _ hnof, ha]
  have hxP0' : xP.toNat ≠ 0 := by
    intro h; exact hP0 (B256.toNat_inj _ _ (by rw [h, B256.toNat_zero]))
  have hadd0 : amountIn + xP ≠ 0 := by
    intro h; rw [h, B256.toNat_zero] at haddNat; omega
  have haddne : xP ≠ amountIn + xP := by
    intro h; rw [← h] at haddNat; omega
  have hkey : (sevm.currentTarget, balSlot pair) ≠ (sevm.currentTarget, balSlot trader) := by
    intro h; exact balSlot_trader_ne_pair (Prod.mk.inj h).2.symm
  -- the trader read and write
  have from_ : mvFrom sevm pre trader = xT := hT
  have warm1 : (sevm.currentTarget, balSlot trader) ∈
      (mv1 sevm pre trader).accessedStorageKeys := by
    unfold mv1; rw [afterSload_accessedStorageKeys, mem_sloadAccessedStorageKeys_iff]; exact Or.inl rfl
  have created1 : (mv1 sevm pre trader).createdAccounts = pre.createdAccounts :=
    afterSload_createdAccounts sevm pre (balSlot trader)
  have load1 : sloadCost sevm pre (balSlot trader) = 2100 := by
    unfold sloadCost; rw [ite_eq_right hcoldT]; rfl
  have orig1 : (mv1 sevm pre trader).getOrigStorVal sevm sevm.currentTarget (balSlot trader) = xT :=
    (getOrigStorVal_congr_created _ _ created1).trans hTo
  have cur1 : (mv1 sevm pre trader).getStorVal sevm.currentTarget (balSlot trader) = xT :=
    getStorVal_afterSload.trans hT
  have store1 : sstoreCost sevm (mv1 sevm pre trader) (balSlot trader) (xT - amountIn) = 2900 := by
    unfold sstoreCost
    rw [ite_eq_left warm1, orig1, cur1, sstoreValueCost_update hxT0 hsubne]
  -- the pair read
  have created2 : (mv2 sevm pre trader amountIn).createdAccounts = pre.createdAccounts := by
    unfold mv2; rw [afterSstore_createdAccounts, created1]
  have cold2 : (sevm.currentTarget, balSlot pair) ∉ (mv2 sevm pre trader amountIn).accessedStorageKeys := by
    unfold mv2 mv1
    rw [afterSstore_accessedStorageKeys, afterSload_accessedStorageKeys]
    rw [mem_sloadAccessedStorageKeys_iff, mem_sloadAccessedStorageKeys_iff]
    rintro (h | h | h)
    · exact hkey h
    · exact hkey h
    · exact hcoldP h
  have load2 : sloadCost sevm (mv2 sevm pre trader amountIn) (balSlot pair) = 2100 := by
    unfold sloadCost; rw [ite_eq_right cold2]; rfl
  have to_ : mvTo sevm pre trader pair amountIn = xP := by
    unfold mvTo mv2
    show (Devm.getStor _ _).get _ = _
    rw [afterSstore_getStor_self, Stor.get_set_ne _ balSlot_trader_ne_pair]
    unfold mv1
    rw [afterSload_getStor]
    exact hP
  -- the pair write
  have warm3 : (sevm.currentTarget, balSlot pair) ∈
      (mv3 sevm pre trader pair amountIn).accessedStorageKeys := by
    unfold mv3; rw [afterSload_accessedStorageKeys, mem_sloadAccessedStorageKeys_iff]; exact Or.inl rfl
  have orig3 : (mv3 sevm pre trader pair amountIn).getOrigStorVal sevm sevm.currentTarget
      (balSlot pair) = xP := by
    refine (getOrigStorVal_congr_created _ _ ?_).trans hPo
    unfold mv3; rw [afterSload_createdAccounts, created2]
  have cur3 : (mv3 sevm pre trader pair amountIn).getStorVal sevm.currentTarget (balSlot pair) =
      xP := getStorVal_afterSload.trans to_
  have store3 : sstoreCost sevm (mv3 sevm pre trader pair amountIn) (balSlot pair)
      (amountIn + xP) = 2900 := by
    unfold sstoreCost
    rw [ite_eq_left warm3, orig3, cur3, sstoreValueCost_update hP0 haddne]
  refine ⟨from_, to_, ?_, ?_, ?_⟩
  · unfold transferGas mvCost
    rw [hcaller, hto, hval, to_, store3, load2, from_, store1, load1]
  · unfold transferBase mv4
    rw [hcaller, hto, hval, afterSstore_refundCounter, orig3, cur3, to_,
      sstoreNewRefundCounter_update _ _ hP0 hadd0 haddne]
    unfold mv3 mv2
    rw [afterSload_refundCounter, afterSstore_refundCounter, from_, orig1, cur1,
      sstoreNewRefundCounter_update _ _ hxT0 hsub0 hsubne]
    exact afterSload_refundCounter
  · unfold transferBase mv4
    rw [hcaller, hto, hval, to_, NodeWalk.afterSstore_state]
    unfold mv3 mv2
    rw [NodeWalk.afterSload_state, NodeWalk.afterSstore_state, from_]
    unfold mv1
    rw [NodeWalk.afterSload_state, htarget]
    rfl

/-- **The token frame of `tx1`**: from a frame entry at `X` running Token20's code, called by the
trader with `transfer(pair, amountIn)` calldata, 28416 gas, the two balance slots cold and holding
`xT` and `xP` (also at transaction start), the frame succeeds with 18243 gas left, no refund, no
log, the word `1` returned, and exactly the two balance writes. -/
theorem tx1_frame_success
    (hcode : sevm.code = code) (hfork : CoveredFork sevm.benvStat.fork)
    (hcaller : sevm.caller = trader) (htarget : sevm.currentTarget = tokenX)
    (hstatic : sevm.isStatic = false) (hdata : sevm.data = tx1Data)
    (hstack : pre.stack = []) (hmem : pre.memory = Mem.empty) (hgas : pre.gasLeft = 28416)
    (hT : pre.getStorVal tokenX (balSlot trader) = xT)
    (hTo : pre.getOrigStorVal sevm tokenX (balSlot trader) = xT)
    (hP : pre.getStorVal tokenX (balSlot pair) = xP)
    (hPo : pre.getOrigStorVal sevm tokenX (balSlot pair) = xP)
    (hcoldT : (tokenX, balSlot trader) ∉ pre.accessedStorageKeys)
    (hcoldP : (tokenX, balSlot pair) ∉ pre.accessedStorageKeys)
    (hcov : amountIn < xT) (hP0 : xP ≠ 0) (hnof : B256.Nof amountIn xP)
    (herror : pre.error = none) (hrefund : pre.refundCounter = 0) :
    ∃ post, exec ⟨0, sevm, pre⟩ = .ok post ∧ post.gasLeft = 18243 ∧ post.error = none ∧
      post.refundCounter = 0 ∧ post.accountsToDelete = pre.accountsToDelete ∧
      post.logs = pre.logs ∧ post.state = tx1FrameWrites pre.state xT xP ∧
      post.output = (1 : B256).toBytes := by
  have hsel : Sevm.selector sevm = 0xa9059cbb := by
    simp only [Sevm.selector, Sevm.dataWord, hdata, tx1Data]
    decide +kernel
  have hto : trTo sevm = pair := by
    simp only [trTo, Sevm.dataWord, hdata, tx1Data]
    decide +kernel
  have hval : trVal sevm = amountIn := by
    simp only [trVal, Sevm.dataWord, hdata, tx1Data]
    decide +kernel
  obtain ⟨from_, to_, gas, refund, state⟩ := tx1_move_facts hcaller htarget hto hval hT hTo hP hPo
    hcoldT hcoldP hcov hP0 hnof
  have hle : trVal sevm ≤ mvFrom sevm pre sevm.caller := by
    rw [hval, from_]; exact B256.le_of_lt hcov
  have hnof' : trVal sevm ≤ trVal sevm + mvTo sevm pre sevm.caller (trTo sevm) (trVal sevm) := by
    rw [to_, hval, B256.le_iff_toNat_le_toNat, B256.toNat_add_eq_of_nof _ _ hnof]
    omega
  have run := transfer_runExact (G := 18243) hfork hstatic hsel hstack hmem
    (by rw [hgas, gas]) (by decide) hle hnof'
  refine ⟨_, (exec_iff_exec_eq 0 sevm pre (.ok _)).mp
    (lift_exact cert_check cert_jumpsOk hcode hfork run), rfl, ?_, ?_, ?_, ?_, ?_, rfl⟩
  all_goals
    rw [show transferPost sevm pre 18243 = retPost (transferBase sevm pre)
      [trVal sevm, (trTo sevm).toB256, sevm.caller.toB256, Sevm.selector sevm]
      (okMem Mem.empty) 18243 1 from rfl]
  all_goals
    obtain ⟨kE, kR, kD, kL, kS⟩ := retPost_keeps (transferBase sevm pre)
      [trVal sevm, (trTo sevm).toB256, sevm.caller.toB256, Sevm.selector sevm]
      (okMem Mem.empty) 18243 1
  · rw [kE]
    unfold transferBase mv4 mv3 mv2 mv1
    rw [afterSstore_error, afterSload_error, afterSstore_error, afterSload_error]
    exact herror
  · rw [kR]
    rw [refund, hrefund]
  · rw [kD]
    unfold transferBase mv4 mv3 mv2 mv1
    rw [afterSstore_accountsToDelete, afterSload_accountsToDelete, afterSstore_accountsToDelete,
      afterSload_accountsToDelete]
  · rw [kL]
    unfold transferBase mv4 mv3 mv2 mv1
    rw [afterSstore_logs, afterSload_logs, afterSstore_logs, afterSload_logs]
  · rw [kS]
    exact state

end Frame

end Blanc.Composition.UniswapV2PairWeth9Instance
