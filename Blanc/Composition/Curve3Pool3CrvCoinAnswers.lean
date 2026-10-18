import Blanc.Composition.Curve3Pool3CrvCoinCalls
import Blanc.Composition.UniswapV2PairWeth9SwapLegsCall
import Blanc.StorageAccessGas
import Blanc.CodeDelegation
import Blanc.Lift.Curve3Pool.Walk.LiveKit

/-!
# U9(b): the coins' answers at the pool's `CALL` sites, from `Token20`'s code

A value-`0` `CALL` from a pool call site into a coin running the synthetic token resumes in
`ccPost` (`cc_cross`); here the resumed parent is read back (`cc_answer`: the caller-visible post,
the reply, the gas, the world) and the child is `Token20`'s gas-exact run, lifted to an execution of
its code (`lift_exact`), so the coins' replies are their code's, not premises.

* `ccExt_le`: the call's two windows inside `[0, 0xc20)` cost at most 309 gas of expansion,
  whatever the memory;
* `ccMsg_data`: the child's calldata is the input window of the caller's memory.
-/

namespace Blanc.Composition.Curve3Pool3CrvInstance

open Jaune Blanc Blanc.Lift Blanc.Composition.Curve3Pool3CrvJoint
open Blanc.Composition.UniswapV2PairWeth9Joint (vcsm_benvStat vcsm_caller vcsm_currentTarget
  vcsm_value vcsm_isStatic vcsm_code vcsm_state vcsm_gasLeft vcsm_stack vcsm_memory vcsm_error
  mem_read_fst callSpawnParent_memory_data addAccessedAddress_setMach_memory)

/-! ## The expansion charge -/

theorem ceilDiv_32_mul (k : Nat) : ceilDiv (32 * k) 32 = k := by
  unfold ceilDiv
  rw [Nat.mul_div_cancel_left _ (by decide), Nat.mul_mod_right, if_pos rfl, Nat.add_zero]

theorem ceilDiv_32_le {n : Nat} (h : n ≤ 3104) : ceilDiv n 32 ≤ 97 := by
  unfold ceilDiv
  split <;> omega

theorem memoryGas_32_mul (k : Nat) :
    calculateMemoryGasCost (32 * k) = 3 * k + k ^ 2 / 512 := by
  unfold calculateMemoryGasCost gMemory
  rw [ceilDiv_32_mul]

/-- **The call's expansion charge is at most 309** when both windows end by `0xc20`. -/
theorem ccExt_le {b : Devm} {S : List B256} {M : Mem} {G : Nat} {ii is oi : B256}
    (his : is.toNat ≠ 0) (hA : ii.toNat + is.toNat ≤ 3104) (hB : oi.toNat + 32 ≤ 3104) :
    ccExt b S M G ii is oi ≤ 309 := by
  unfold ccExt Devm.extCost
  rw [St.memory, show (0x20 : B256).toNat = 32 from rfl]
  simp only [memExtsSize, memExtSize, his, show (32 : Nat) ≠ 0 from by decide, ↓reduceIte,
    ceilDiv_32_mul, memoryGas_32_mul]
  have hw : calculateMemoryGasCost M.size =
      3 * ceilDiv M.size 32 + ceilDiv M.size 32 ^ 2 / 512 := by
    unfold calculateMemoryGasCost gMemory
    rfl
  rw [hw]
  have ha := ceilDiv_32_le hA
  have hb := ceilDiv_32_le hB
  generalize ceilDiv M.size 32 = w at *
  generalize ceilDiv (ii.toNat + is.toNat) 32 = a at *
  generalize ceilDiv (oi.toNat + 32) 32 = c at *
  by_cases hk : max (max w a) c = w
  · rw [hk]
    omega
  · have hle : max (max w a) c ≤ 97 := by omega
    have hsq : max (max w a) c ^ 2 ≤ 9409 :=
      (Nat.pow_le_pow_left hle 2).trans (by decide)
    generalize max (max w a) c = k at *
    generalize k ^ 2 = q at *
    omega

/-! ## The child message -/

/-- The child's calldata is the caller's input window. -/
theorem ccMsg_data (sevm : Sevm) (b : Devm) (S : List B256) (M : Mem) (G : Nat)
    (t ii is oi : B256) :
    (initSevm (ccMsg sevm b S M G t ii is oi)).data = (M.read ii.toNat is.toNat).1 := by
  rw [mem_read_fst]
  unfold ccMsg
  change (ccParent b S M G t ii is oi).memory.data.sliceD ii.toNat is.toNat 0 = _
  unfold ccParent ccWarm St
  rw [callSpawnParent_memory_data, addAccessedAddress_setMach_memory]

theorem ccMsg_state (sevm : Sevm) (b : Devm) (S : List B256) (M : Mem) (G : Nat)
    (t ii is oi : B256) :
    (initDevm (ccMsg sevm b S M G t ii is oi)).state = b.state := rfl

/-! ## The resumed parent -/

/-- **The resumed parent of a clean child, read back**: the caller-visible post with flag `1`, the
child's output as reply, the gas, the child's world, the warm addresses kept. -/
theorem cc_answer {sevm : Sevm} {b : Devm} {S : List B256} {M : Mem} {G : Nat}
    {t ii is oi : B256} {cpost : Devm}
    (hfork : CoveredFork sevm.benvStat.fork)
    (hdel : getDelegatedCodeAddress (b.state.getCode t.toAdr) = none)
    (hdepth : sevm.depth ≠ 0) (hprec : sevm.benvStat.rules.isPrecomp t.toAdr = false)
    (hroom : S.length < 1024) (hG : G < 2 ^ 256)
    (hcharge : ccAcc b S M G t + ccExt b S M G ii is oi ≤ G)
    (hexec : exec (initEvm (ccMsg sevm b S M G t ii is oi)) = .ok cpost)
    (herr : cpost.error = none) :
    Ninst.RunCompiled sevm (St b (Nat.toB256 G :: t :: 0 :: ii :: is :: oi :: 0x20 :: S) M G)
        (.exec .call) (ccPost b S M G t ii is oi cpost) ∧
      MutableCallPost b (ccPost b S M G t ii is oi cpost) S M ii is oi 0x20 1 ∧
      (ccPost b S M G t ii is oi cpost).returnData = cpost.output ∧
      (ccPost b S M G t ii is oi cpost).gasLeft =
        G - (ccFwd b S M G t ii is oi + ccAcc b S M G t + ccExt b S M G ii is oi) +
          cpost.gasLeft ∧
      (ccPost b S M G t ii is oi cpost).state = cpost.state ∧
      (∀ a ∈ b.accessedAddresses, a ∈ (ccPost b S M G t ii is oi cpost).accessedAddresses) := by
  have hrun := cc_cross hfork hdel hdepth hprec hroom hG hcharge hexec herr
  have raw : Ninst.Run sevm (St b (Nat.toB256 G :: t :: 0 :: ii :: is :: oi :: 0x20 :: S) M G)
      (.exec .call) (ccPost b S M G t ii is oi cpost) := by
    obtain ⟨xl, filled, step⟩ := hrun
    exact ⟨xl, filled, 0, step 0⟩
  obtain ⟨flag, post⟩ := ri_call_post hfork raw
  have hstack : (ccPost b S M G t ii is oi cpost).stack = 1 :: S := rfl
  have flagOne : flag = 1 := (List.cons.inj (post.stack.symm.trans hstack)).1
  subst flagOne
  refine ⟨hrun, post, rfl, ?_, rfl, ?_⟩
  · change (ccParent b S M G t ii is oi).gasLeft + cpost.gasLeft = _
    rfl
  · intro a ha
    exact Std.HashSet.mem_union_of_left (Std.HashSet.mem_insert.mpr (Or.inr ha))

/-! ## Gas -/

theorem ccAcc_le (b : Devm) (S : List B256) (M : Mem) (G : Nat) (t : B256) :
    ccAcc b S M G t ≤ 2600 := by
  unfold ccAcc accessCost
  split <;> decide

/-- With `80000` gas at the call and an expansion of at most `309`, the child gets at least
`75300`. -/
theorem ccFwd_ge {b : Devm} {S : List B256} {M : Mem} {G : Nat} {t ii is oi : B256}
    (hU : 80000 ≤ G) (hext : ccExt b S M G ii is oi ≤ 309) :
    75300 ≤ ccFwd b S M G t ii is oi := by
  have ha := ccAcc_le b S M G t
  unfold ccFwd except64th
  omega

/-! ## A clean `true` reply at a pool call site -/

/-- `true` passes the pool's reply test. -/
theorem rawCallOk_one : RawCallOk (1 : B256).toBytes := Or.inr (by decide +kernel)

/-- **A coin child that halts cleanly with `true`, charging at most `72918`, answers the pool's
`CALL` within `80000` gas** (`MutCallOkAt`'s conclusion, the world aside). -/
theorem cc_answer_true {sevm : Sevm} {b : Devm} {S : List B256} {M : Mem} {G : Nat}
    {t ii is oi : B256} {cpost : Devm} {used : Nat}
    (hfork : CoveredFork sevm.benvStat.fork)
    (hdel : getDelegatedCodeAddress (b.state.getCode t.toAdr) = none)
    (hdepth : sevm.depth ≠ 0) (hprec : sevm.benvStat.rules.isPrecomp t.toAdr = false)
    (hroom : S.length < 1024) (hG : G < 2 ^ 256) (hU : 80000 ≤ G)
    (hext : ccExt b S M G ii is oi ≤ 309) (hused : used ≤ 72918)
    (hexec : exec (initEvm (ccMsg sevm b S M G t ii is oi)) = .ok cpost)
    (herr : cpost.error = none) (hout : cpost.output = (1 : B256).toBytes)
    (hgas : cpost.gasLeft = ccFwd b S M G t ii is oi - used) :
    Ninst.RunCompiled sevm (St b (Nat.toB256 G :: t :: 0 :: ii :: is :: oi :: 0x20 :: S) M G)
        (.exec .call) (ccPost b S M G t ii is oi cpost) ∧
      MutableCallPost b (ccPost b S M G t ii is oi cpost) S M ii is oi 0x20 1 ∧
      RawCallOk (ccPost b S M G t ii is oi cpost).returnData ∧
      (ccPost b S M G t ii is oi cpost).returnData.length < 2 ^ 256 ∧
      G ≤ (ccPost b S M G t ii is oi cpost).gasLeft + 80000 ∧
      (ccPost b S M G t ii is oi cpost).gasLeft ≤ G ∧
      (ccPost b S M G t ii is oi cpost).state = cpost.state ∧
      (∀ a ∈ b.accessedAddresses, a ∈ (ccPost b S M G t ii is oi cpost).accessedAddresses) := by
  have ha := ccAcc_le b S M G t
  have hf := ccFwd_ge (t := t) hU hext
  have hfle := cc_fwd_le b S M G t ii is oi
  obtain ⟨hrun, hpost, hret, hgl, hst, hacc⟩ := cc_answer hfork hdel hdepth hprec hroom hG
    (by omega) hexec herr
  rw [hout] at hret
  refine ⟨hrun, hpost, by rw [hret]; exact rawCallOk_one, by rw [hret]; decide +kernel, ?_, ?_, hst,
    hacc⟩
  · rw [hgl, hgas]; omega
  · rw [hgl, hgas]; omega

/-- What a returning tail keeps of its base. -/
theorem retPost_facts (b : Devm) (S : List B256) (M : Mem) (G : Nat) (w : B256) :
    (VyperNonreentrantDeployed.Token20.retPost b S M G w).error = b.error ∧
      (VyperNonreentrantDeployed.Token20.retPost b S M G w).output = w.toBytes ∧
      (VyperNonreentrantDeployed.Token20.retPost b S M G w).gasLeft = G ∧
      (VyperNonreentrantDeployed.Token20.retPost b S M G w).state = b.state :=
  ⟨rfl, rfl, rfl, rfl⟩

/-! ## Coin 0's `transferFrom(trader, pool, 100)` -/

/-- The pull's calldata. -/
def pullData : Bytes :=
  Curve3Pool.transferFromSel ++ trader.toB256.toBytes ++ poolAddr.toB256.toBytes ++
    (Nat.toB256 exchangeDx).toBytes

section Pull

open VyperNonreentrantDeployed.Token20 (tfFrom tfTo tfVal tfAllow tf1 tf2 mvFrom mvTo mv1 mv2 mv3 mv4
  mvCost transferFromGas transferFromBase transferFromPost transferFrom_runExact cert_check
  cert_jumpsOk)

/-- What `transferFrom`'s halting machine keeps of its base. -/
theorem tfPost_facts (s : Sevm) (p : Devm) (G : Nat) :
    (transferFromPost s p G).error = (transferFromBase s p).error ∧
      (transferFromPost s p G).output = (1 : B256).toBytes ∧
      (transferFromPost s p G).gasLeft = G ∧
      (transferFromPost s p G).state = (transferFromBase s p).state := by
  unfold transferFromPost
  exact retPost_facts _ _ _ _ _

variable {sevm : Sevm} {b : Devm} {S : List B256} {M : Mem} {G : Nat} {t ii oi : B256}

/-- **Coin 0 runs `transferFrom(trader, pool, 100)` cleanly**: from a pool call site whose input
window holds the pull's calldata, at a coin holding `Token20` over `coin0Stor`, the child halts
with `true`, charging at most `72918`, writing only coin 0's storage. -/
theorem pull_child (hfork : CoveredFork sevm.benvStat.fork) (hstatic : sevm.isStatic = false)
    (htarget : sevm.currentTarget = poolAddr) (ht : t.toAdr = coin0Addr)
    (hcode : b.state.getCode coin0Addr = VyperNonreentrantDeployed.Token20.code)
    (hstor : b.getStor coin0Addr = coin0Stor)
    (hdata : (M.read ii.toNat (0x64 : B256).toNat).1 = pullData)
    (hfwd : 75300 ≤ ccFwd b S M G t ii 0x64 oi) :
    ∃ cpost used, exec (initEvm (ccMsg sevm b S M G t ii 0x64 oi)) = .ok cpost ∧
      cpost.error = none ∧ cpost.output = (1 : B256).toBytes ∧
      cpost.gasLeft = ccFwd b S M G t ii 0x64 oi - used ∧ used ≤ 72918 ∧
      (∀ a, cpost.getCode a = b.getCode a) ∧
      (∀ a, a ≠ coin0Addr → cpost.getStor a = b.getStor a) := by
  generalize hmsg : ccMsg sevm b S M G t ii 0x64 oi = msg
  have hcC : (initSevm msg).code = VyperNonreentrantDeployed.Token20.code := by
    rw [← hmsg, ← hcode, ← ht]; rfl
  have hfC : CoveredFork (initSevm msg).benvStat.fork := by rw [← hmsg]; exact hfork
  have hsC : (initSevm msg).isStatic = false := by
    rw [← hmsg]; show (false || sevm.isStatic) = false; rw [hstatic]; rfl
  have hct : (initSevm msg).currentTarget = coin0Addr := by rw [← hmsg, ← ht]; rfl
  have hcl : (initSevm msg).caller = poolAddr := by rw [← hmsg, ← htarget]; rfl
  have hd : (initSevm msg).data = pullData := by rw [← hmsg, ccMsg_data, hdata]
  have hgl : (initDevm msg).gasLeft = ccFwd b S M G t ii 0x64 oi := by rw [← hmsg]; rfl
  have hget : ∀ k, (initDevm msg).getStorVal coin0Addr k = coin0Stor.get k := by
    intro k
    rw [← hmsg, ← hstor]
    rfl
  have hsel : Sevm.selector (initSevm msg) = 0x23b872dd := by
    unfold Sevm.selector Sevm.dataWord; rw [hd]; decide +kernel
  have hfrom : tfFrom (initSevm msg) = trader := by
    unfold tfFrom Sevm.dataWord; rw [hd]; decide +kernel
  have hto : tfTo (initSevm msg) = poolAddr := by
    unfold tfTo Sevm.dataWord; rw [hd]; decide +kernel
  have hval : tfVal (initSevm msg) = 100 := by
    unfold tfVal Sevm.dataWord; rw [hd]; decide +kernel
  -- the reads
  have hal : tfAllow (initSevm msg) (initDevm msg) = 100 := by
    unfold tfAllow; rw [hct, hget, hfrom, hcl]; decide +kernel
  have hfromBal : mvFrom (initSevm msg) (tf2 (initSevm msg) (initDevm msg))
      (tfFrom (initSevm msg)) = 1000 := by
    unfold mvFrom tf2
    show (Devm.getStor (afterSstore _ _ _ _) (initSevm msg).currentTarget).get _ = _
    rw [afterSstore_getStor_self, hfrom, hcl, Stor.get_set_ne _ (by decide +kernel)]
    unfold tf1
    rw [afterSload_getStor, hct]
    exact (hget _).trans (by decide +kernel)
  have htoBal : mvTo (initSevm msg) (tf2 (initSevm msg) (initDevm msg)) (tfFrom (initSevm msg))
      (tfTo (initSevm msg)) (tfVal (initSevm msg)) = 1000 := by
    unfold mvTo mv2
    show (Devm.getStor (afterSstore _ _ _ _) (initSevm msg).currentTarget).get _ = _
    rw [afterSstore_getStor_self, hfrom, hto, Stor.get_set_ne _ (by decide +kernel)]
    unfold mv1 tf2
    rw [afterSload_getStor, afterSstore_getStor_self, hcl, hfrom,
      Stor.get_set_ne _ (by decide +kernel)]
    unfold tf1
    rw [afterSload_getStor, hct]
    exact (hget _).trans (by decide +kernel)
  -- the charge
  have hused : transferFromGas (initSevm msg) (initDevm msg) ≤ 72918 := by
    unfold transferFromGas mvCost
    have := Lift.Curve3Pool.sstoreCost_le_22100 (initSevm msg) (mv3 (initSevm msg)
      (tf2 (initSevm msg) (initDevm msg)) (tfFrom (initSevm msg)) (tfTo (initSevm msg))
      (tfVal (initSevm msg))) (VyperNonreentrantDeployed.Token20.balSlot (tfTo (initSevm msg)))
      (tfVal (initSevm msg) + mvTo (initSevm msg) (tf2 (initSevm msg) (initDevm msg))
        (tfFrom (initSevm msg)) (tfTo (initSevm msg)) (tfVal (initSevm msg)))
    have := Lift.Curve3Pool.sstoreCost_le_22100 (initSevm msg) (mv1 (initSevm msg)
      (tf2 (initSevm msg) (initDevm msg)) (tfFrom (initSevm msg)))
      (VyperNonreentrantDeployed.Token20.balSlot (tfFrom (initSevm msg)))
      (mvFrom (initSevm msg) (tf2 (initSevm msg) (initDevm msg)) (tfFrom (initSevm msg)) -
        tfVal (initSevm msg))
    have := Lift.Curve3Pool.sstoreCost_le_22100 (initSevm msg) (tf1 (initSevm msg) (initDevm msg))
      (VyperNonreentrantDeployed.Token20.allowSlot (tfFrom (initSevm msg)) (initSevm msg).caller)
      (tfAllow (initSevm msg) (initDevm msg) - tfVal (initSevm msg))
    have := sloadCost_le (initSevm msg) (mv2 (initSevm msg) (tf2 (initSevm msg) (initDevm msg))
      (tfFrom (initSevm msg)) (tfVal (initSevm msg)))
      (VyperNonreentrantDeployed.Token20.balSlot (tfTo (initSevm msg)))
    have := sloadCost_le (initSevm msg) (tf2 (initSevm msg) (initDevm msg))
      (VyperNonreentrantDeployed.Token20.balSlot (tfFrom (initSevm msg)))
    have := sloadCost_le (initSevm msg) (initDevm msg)
      (VyperNonreentrantDeployed.Token20.allowSlot (tfFrom (initSevm msg)) (initSevm msg).caller)
    unfold gasColdSload at *
    omega
  have run := transferFrom_runExact (pre := initDevm msg) (G := ccFwd b S M G t ii 0x64 oi -
      transferFromGas (initSevm msg) (initDevm msg)) hfC hsC hsel (by rw [← hmsg]; rfl)
    (by rw [← hmsg]; rfl) (by rw [hgl]; omega) (by unfold gCallStipend; omega)
    (by rw [hal, hval]) (by rw [hfromBal, hval]; decide)
    (by rw [htoBal, hval]; decide)
  have hexec := (exec_iff_exec_eq 0 (initSevm msg) (initDevm msg) (.ok _)).mp
    (lift_exact cert_check cert_jumpsOk hcC hfC run)
  obtain ⟨pe, po, pg, ps⟩ := tfPost_facts (initSevm msg) (initDevm msg)
    (ccFwd b S M G t ii 0x64 oi - transferFromGas (initSevm msg) (initDevm msg))
  refine ⟨transferFromPost (initSevm msg) (initDevm msg)
      (ccFwd b S M G t ii 0x64 oi - transferFromGas (initSevm msg) (initDevm msg)),
    transferFromGas (initSevm msg) (initDevm msg), hexec, ?_, po, pg, hused, ?_, ?_⟩
  · rw [pe]
    unfold transferFromBase mv4 mv3 mv2 mv1 tf2 tf1
    rw [afterSstore_error, afterSload_error, afterSstore_error, afterSload_error, afterSstore_error,
      afterSload_error, ← hmsg]
    rfl
  · intro a
    unfold Devm.getCode Devm.getAcct
    rw [ps]
    change (transferFromBase (initSevm msg) (initDevm msg)).getCode a = _
    unfold transferFromBase mv4 mv3 mv2 mv1 tf2 tf1
    rw [afterSstore_getCode, afterSload_getCode, afterSstore_getCode, afterSload_getCode,
      afterSstore_getCode, afterSload_getCode, ← hmsg]
    rfl
  · intro a ha
    have hne : (initSevm msg).currentTarget ≠ a := by rw [hct]; exact Ne.symm ha
    unfold Devm.getStor Devm.getAcct
    rw [ps]
    change Devm.getStor (transferFromBase (initSevm msg) (initDevm msg)) a = _
    unfold transferFromBase mv4 mv3 mv2 mv1 tf2 tf1
    rw [afterSstore_getStor_ne _ _ _ _ _ hne, afterSload_getStor, afterSstore_getStor_ne _ _ _ _ _ hne,
      afterSload_getStor, afterSstore_getStor_ne _ _ _ _ _ hne, afterSload_getStor, ← hmsg]
    rfl

end Pull

/-! ## Coin 1's `transfer(trader, 132)` -/

/-- The push's calldata. -/
def pushData : Bytes :=
  Curve3Pool.transferSel ++ trader.toB256.toBytes ++ (132 : B256).toBytes

section Push

open VyperNonreentrantDeployed.Token20 (trTo trVal mvFrom mvTo mv1 mv2 mv3 mv4 mvCost transferGas
  transferBase transferPost transfer_runExact cert_check cert_jumpsOk)

/-- What `transfer`'s halting machine keeps of its base. -/
theorem trPost_facts (s : Sevm) (p : Devm) (G : Nat) :
    (transferPost s p G).error = (transferBase s p).error ∧
      (transferPost s p G).output = (1 : B256).toBytes ∧
      (transferPost s p G).gasLeft = G ∧
      (transferPost s p G).state = (transferBase s p).state := by
  unfold transferPost
  exact retPost_facts _ _ _ _ _

variable {sevm : Sevm} {b : Devm} {S : List B256} {M : Mem} {G : Nat} {t ii oi : B256}

/-- **Coin 1 runs `transfer(trader, 132)` from the pool cleanly**: at a coin holding `Token20`
over `coin1Stor`, the child halts with `true`, charging at most `48573`, writing only coin 1's
storage. -/
theorem push_child (hfork : CoveredFork sevm.benvStat.fork) (hstatic : sevm.isStatic = false)
    (htarget : sevm.currentTarget = poolAddr) (ht : t.toAdr = coin1Addr)
    (hcode : b.state.getCode coin1Addr = VyperNonreentrantDeployed.Token20.code)
    (hstor : b.getStor coin1Addr = coin1Stor)
    (hdata : (M.read ii.toNat (0x44 : B256).toNat).1 = pushData)
    (hfwd : 75300 ≤ ccFwd b S M G t ii 0x44 oi) :
    ∃ cpost used, exec (initEvm (ccMsg sevm b S M G t ii 0x44 oi)) = .ok cpost ∧
      cpost.error = none ∧ cpost.output = (1 : B256).toBytes ∧
      cpost.gasLeft = ccFwd b S M G t ii 0x44 oi - used ∧ used ≤ 72918 ∧
      (∀ a, cpost.getCode a = b.getCode a) ∧
      (∀ a, a ≠ coin1Addr → cpost.getStor a = b.getStor a) := by
  generalize hmsg : ccMsg sevm b S M G t ii 0x44 oi = msg
  have hcC : (initSevm msg).code = VyperNonreentrantDeployed.Token20.code := by
    rw [← hmsg, ← hcode, ← ht]; rfl
  have hfC : CoveredFork (initSevm msg).benvStat.fork := by rw [← hmsg]; exact hfork
  have hsC : (initSevm msg).isStatic = false := by
    rw [← hmsg]; show (false || sevm.isStatic) = false; rw [hstatic]; rfl
  have hct : (initSevm msg).currentTarget = coin1Addr := by rw [← hmsg, ← ht]; rfl
  have hcl : (initSevm msg).caller = poolAddr := by rw [← hmsg, ← htarget]; rfl
  have hd : (initSevm msg).data = pushData := by rw [← hmsg, ccMsg_data, hdata]
  have hgl : (initDevm msg).gasLeft = ccFwd b S M G t ii 0x44 oi := by rw [← hmsg]; rfl
  have hget : ∀ k, (initDevm msg).getStorVal coin1Addr k = coin1Stor.get k := by
    intro k
    rw [← hmsg, ← hstor]
    rfl
  have hsel : Sevm.selector (initSevm msg) = 0xa9059cbb := by
    unfold Sevm.selector Sevm.dataWord; rw [hd]; decide +kernel
  have hto : trTo (initSevm msg) = trader := by
    unfold trTo Sevm.dataWord; rw [hd]; decide +kernel
  have hval : trVal (initSevm msg) = 132 := by
    unfold trVal Sevm.dataWord; rw [hd]; decide +kernel
  have hfromBal : mvFrom (initSevm msg) (initDevm msg) (initSevm msg).caller = 2000 := by
    unfold mvFrom
    rw [hct, hget, hcl]
    decide +kernel
  have htoBal : mvTo (initSevm msg) (initDevm msg) (initSevm msg).caller (trTo (initSevm msg))
      (trVal (initSevm msg)) = 0 := by
    unfold mvTo mv2
    show (Devm.getStor (afterSstore _ _ _ _) (initSevm msg).currentTarget).get _ = _
    rw [afterSstore_getStor_self, hto, hcl, Stor.get_set_ne _ (by decide +kernel)]
    unfold mv1
    rw [afterSload_getStor, hct]
    exact (hget _).trans (by decide +kernel)
  have hused : transferGas (initSevm msg) (initDevm msg) ≤ 72918 := by
    unfold transferGas mvCost
    have := Lift.Curve3Pool.sstoreCost_le_22100 (initSevm msg) (mv3 (initSevm msg) (initDevm msg)
      (initSevm msg).caller (trTo (initSevm msg)) (trVal (initSevm msg)))
      (VyperNonreentrantDeployed.Token20.balSlot (trTo (initSevm msg)))
      (trVal (initSevm msg) + mvTo (initSevm msg) (initDevm msg) (initSevm msg).caller
        (trTo (initSevm msg)) (trVal (initSevm msg)))
    have := Lift.Curve3Pool.sstoreCost_le_22100 (initSevm msg) (mv1 (initSevm msg) (initDevm msg)
      (initSevm msg).caller) (VyperNonreentrantDeployed.Token20.balSlot (initSevm msg).caller)
      (mvFrom (initSevm msg) (initDevm msg) (initSevm msg).caller - trVal (initSevm msg))
    have := sloadCost_le (initSevm msg) (mv2 (initSevm msg) (initDevm msg) (initSevm msg).caller
      (trVal (initSevm msg))) (VyperNonreentrantDeployed.Token20.balSlot (trTo (initSevm msg)))
    have := sloadCost_le (initSevm msg) (initDevm msg)
      (VyperNonreentrantDeployed.Token20.balSlot (initSevm msg).caller)
    unfold gasColdSload at *
    omega
  have run := transfer_runExact (pre := initDevm msg) (G := ccFwd b S M G t ii 0x44 oi -
      transferGas (initSevm msg) (initDevm msg)) hfC hsC hsel (by rw [← hmsg]; rfl)
    (by rw [← hmsg]; rfl) (by rw [hgl]; omega) (by unfold gCallStipend; omega)
    (by rw [hfromBal, hval]; decide) (by rw [htoBal, hval]; decide)
  have hexec := (exec_iff_exec_eq 0 (initSevm msg) (initDevm msg) (.ok _)).mp
    (lift_exact cert_check cert_jumpsOk hcC hfC run)
  obtain ⟨pe, po, pg, ps⟩ := trPost_facts (initSevm msg) (initDevm msg)
    (ccFwd b S M G t ii 0x44 oi - transferGas (initSevm msg) (initDevm msg))
  refine ⟨transferPost (initSevm msg) (initDevm msg)
      (ccFwd b S M G t ii 0x44 oi - transferGas (initSevm msg) (initDevm msg)),
    transferGas (initSevm msg) (initDevm msg), hexec, ?_, po, pg, hused, ?_, ?_⟩
  · rw [pe]
    unfold transferBase mv4 mv3 mv2 mv1
    rw [afterSstore_error, afterSload_error, afterSstore_error, afterSload_error, ← hmsg]
    rfl
  · intro a
    unfold Devm.getCode Devm.getAcct
    rw [ps]
    change (transferBase (initSevm msg) (initDevm msg)).getCode a = _
    unfold transferBase mv4 mv3 mv2 mv1
    rw [afterSstore_getCode, afterSload_getCode, afterSstore_getCode, afterSload_getCode, ← hmsg]
    rfl
  · intro a ha
    have hne : (initSevm msg).currentTarget ≠ a := by rw [hct]; exact Ne.symm ha
    unfold Devm.getStor Devm.getAcct
    rw [ps]
    change Devm.getStor (transferBase (initSevm msg) (initDevm msg)) a = _
    unfold transferBase mv4 mv3 mv2 mv1
    rw [afterSstore_getStor_ne _ _ _ _ _ hne, afterSload_getStor, afterSstore_getStor_ne _ _ _ _ _ hne,
      afterSload_getStor, ← hmsg]
    rfl

end Push

/-! ## The coins' premises for `exchange(0, 1, 100, 0)`

The world invariants: before the pull (`WPull`) both coins hold `Token20` over their synthetic
ledgers; after it (`WPush`) coin 1 still does; after the push nothing more is needed. -/

/-- The world before the pull. -/
def WPull (b : Devm) : Prop :=
  b.getCode coin0Addr = VyperNonreentrantDeployed.Token20.code ∧
    b.getCode coin1Addr = VyperNonreentrantDeployed.Token20.code ∧
    b.getStor coin0Addr = coin0Stor ∧ b.getStor coin1Addr = coin1Stor

/-- The world after the pull. -/
def WPush (b : Devm) : Prop :=
  b.getCode coin1Addr = VyperNonreentrantDeployed.Token20.code ∧ b.getStor coin1Addr = coin1Stor

theorem token20_undelegated :
    getDelegatedCodeAddress VyperNonreentrantDeployed.Token20.code = none :=
  getDelegatedCodeAddress_eq_none_of_size_ne (by decide +kernel)

theorem getStor_of_state {d c : Devm} (h : d.state = c.state) (a : Adr) :
    d.getStor a = c.getStor a := by
  unfold Devm.getStor Devm.getAcct
  rw [h]

theorem getCode_of_state {d c : Devm} (h : d.state = c.state) (a : Adr) :
    d.getCode a = c.getCode a := by
  unfold Devm.getCode Devm.getAcct
  rw [h]

/-- A non-precompile, as the crossing states it. -/
theorem prec_false {p : Prop} (h : ¬ p) : p = (false = true) :=
  propext ⟨fun hp => absurd hp h, fun hf => absurd hf Bool.false_ne_true⟩

theorem idReady_of_child {sevm : Sevm} {b d : Devm} (hcode : d.getCode 4 = b.getCode 4)
    (hacc : ∀ a ∈ b.accessedAddresses, a ∈ d.accessedAddresses) (h : IdReady sevm b) :
    IdReady sevm d :=
  ⟨by rw [hcode]; exact h.nodeleg, hacc _ h.warm, h.pre, h.fork⟩

section Premises

variable {sevm : Sevm} {t amt : B256}

/-- **Coin 0 answers the pull** (`CoinPullOkAt` at `exchange`'s window, from `Token20`'s code). -/
theorem coin_pullOk (hfork : CoveredFork sevm.benvStat.fork) (hstatic : sevm.isStatic = false)
    (hdepth : sevm.depth ≠ 0) (hcaller : sevm.caller = trader)
    (htarget : sevm.currentTarget = poolAddr)
    (hprec : ¬ sevm.benvStat.rules.isPrecomp coin0Addr) (ht : t.toAdr = coin0Addr)
    (hamt : amt = Nat.toB256 exchangeDx) :
    Curve3Pool.CoinPullOkAt sevm WPull WPush t amt 80000 0x600 0x6c0 := by
  intro b S M G hW hU hG hin hS
  obtain ⟨hc0, hc1, hs0, hs1⟩ := hW
  have hext : ccExt b S M G 0x600 0x64 0x6c0 ≤ 309 := ccExt_le (by decide) (by decide) (by decide)
  have hfwd := ccFwd_ge (t := t) hU hext
  have hc0' : b.state.getCode coin0Addr = VyperNonreentrantDeployed.Token20.code := hc0
  obtain ⟨cpost, used, hexec, herr, hout, hgas, hused, hcode, hstor⟩ := pull_child hfork hstatic
    htarget ht hc0' hs0 (by rw [hin, hcaller, htarget, hamt]; rfl) hfwd
  obtain ⟨hrun, hpost, hok, hlen, hg1, hg2, hst, hacc⟩ := cc_answer_true hfork
    (by rw [ht, hc0']; exact token20_undelegated) hdepth (by rw [ht]; exact prec_false hprec) hS hG
    hU hext hused hexec herr hout hgas
  refine ⟨_, hrun, hpost, hok, hlen, hg1, hg2, ?_, ⟨?_, ?_⟩, ?_⟩
  · rw [htarget, getStor_of_state hst, hstor _ (by decide +kernel)]
  · rw [getCode_of_state hst, hcode]; exact hc1
  · rw [getStor_of_state hst, hstor _ (by decide +kernel)]; exact hs1
  · exact idReady_of_child (by rw [getCode_of_state hst, hcode]) hacc

/-- **Coin 1 answers the push** (`CoinPushOkAt` at `exchange`'s window, from `Token20`'s code). -/
theorem coin_pushOk (hfork : CoveredFork sevm.benvStat.fork) (hstatic : sevm.isStatic = false)
    (hdepth : sevm.depth ≠ 0) (hcaller : sevm.caller = trader)
    (htarget : sevm.currentTarget = poolAddr)
    (hprec : ¬ sevm.benvStat.rules.isPrecomp coin1Addr) (ht : t.toAdr = coin1Addr)
    (hamt : amt = 132) :
    Curve3Pool.CoinPushOkAt sevm WPush (fun _ => True) t amt 80000 0xb60 0xc00 := by
  intro b S M G hW hU hG hin hS
  obtain ⟨hc1, hs1⟩ := hW
  have hext : ccExt b S M G 0xb60 0x44 0xc00 ≤ 309 := ccExt_le (by decide) (by decide) (by decide)
  have hfwd := ccFwd_ge (t := t) hU hext
  have hc1' : b.state.getCode coin1Addr = VyperNonreentrantDeployed.Token20.code := hc1
  obtain ⟨cpost, used, hexec, herr, hout, hgas, hused, hcode, hstor⟩ := push_child hfork hstatic
    htarget ht hc1' hs1 (by rw [hin, hcaller, hamt]; rfl) hfwd
  obtain ⟨hrun, hpost, hok, hlen, hg1, hg2, hst, hacc⟩ := cc_answer_true hfork
    (by rw [ht, hc1']; exact token20_undelegated) hdepth (by rw [ht]; exact prec_false hprec) hS hG
    hU hext hused hexec herr hout hgas
  refine ⟨_, hrun, hpost, hok, hlen, hg1, hg2, ?_, trivial, ?_⟩
  · rw [htarget, getStor_of_state hst, hstor _ (by decide +kernel)]
  · exact idReady_of_child (by rw [getCode_of_state hst, hcode]) hacc

/-- `WPull` survives the pool's own steps. -/
theorem wPull_closed (htarget : sevm.currentTarget = poolAddr) : Curve3Pool.WClosed sevm WPull where
  st _ _ _ _ h := h
  sload b k h := by
    unfold WPull
    rw [afterSload_getCode, afterSload_getCode, afterSload_getStor, afterSload_getStor]
    exact h
  sstore b k v h := by
    unfold WPull
    rw [afterSstore_getCode, afterSstore_getCode,
      afterSstore_getStor_ne _ _ _ _ _ (by rw [htarget]; decide +kernel),
      afterSstore_getStor_ne _ _ _ _ _ (by rw [htarget]; decide +kernel)]
    exact h
  sha b b' rd hp h := by
    unfold WPull
    rw [hp.code, hp.code, hp.stor, hp.stor]
    exact h
  log _ _ h := h

/-- `WPush` survives the pool's own steps. -/
theorem wPush_closed (htarget : sevm.currentTarget = poolAddr) : Curve3Pool.WClosed sevm WPush where
  st _ _ _ _ h := h
  sload b k h := by
    unfold WPush
    rw [afterSload_getCode, afterSload_getStor]
    exact h
  sstore b k v h := by
    unfold WPush
    rw [afterSstore_getCode, afterSstore_getStor_ne _ _ _ _ _ (by rw [htarget]; decide +kernel)]
    exact h
  sha b b' rd hp h := by
    unfold WPush
    rw [hp.code, hp.stor]
    exact h
  log _ _ h := h

theorem wTrue_closed : Curve3Pool.WClosed sevm (fun _ => True) where
  st _ _ _ _ _ := trivial
  sload _ _ _ := trivial
  sstore _ _ _ _ := trivial
  sha _ _ _ _ _ := trivial
  log _ _ _ := trivial

end Premises

end Blanc.Composition.Curve3Pool3CrvInstance
