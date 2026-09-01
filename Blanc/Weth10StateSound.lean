-- WETH10's exact call-free state-changing selector proofs.

import Blanc.Weth10Sound

namespace Blanc

open Jaune
open Jaune.Ninst Ninst
open scoped LogOutputHinv

namespace Weth10

/-! ## Runtime key normalization -/

/-- Clearing the high 96 bits always produces an address-shaped storage key,
including for dirty ABI words. -/
theorem normalizedAddress_valid (w : B256) :
    ValidAdr ((~~~ addressMask) &&& w) := by
  rw [validAdr_iff]
  have hand_not (x y : UInt64) : x &&& ((~~~ x) &&& y) = 0 := by
    apply UInt64.toBitVec_inj.mp
    simp only [UInt64.toBitVec_and]
    rw [← BitVec.and_assoc]
    simp
  rcases w with ⟨⟨whh, whl⟩, ⟨wlh, wll⟩⟩
  simp only [addressMask, B256.and_eq_and_prod_and,
    B128.and_eq_and_prod_and]
  apply Prod.ext
  · apply Prod.ext
    · exact hand_not _ _
    · exact hand_not _ _
  · apply Prod.ext
    · exact hand_not _ _
    · exact hand_not _ _

/-- Tagging a normalized address word as a nonce key cannot alias the
all-ones flash-counter slot, even for dirty ABI input words. -/
theorem runtimeNonceKey_ne_flash (w : B256) :
    nonceTagWord ||| ((~~~ addressMask) &&& w) ≠ flashMintedSlot := by
  let owner := ((~~~ addressMask) &&& w).toAdr
  have hvalid : ValidAdr ((~~~ addressMask) &&& w) :=
    normalizedAddress_valid w
  have howner : owner.toB256 = (~~~ addressMask) &&& w :=
    toB256_toAdr hvalid
  rw [← howner]
  simpa only [nonceTagWord, ← nonceKey_formula] using
    nonceKey_ne_flashMintedSlot owner

/-- Tagging a normalized address word as a nonce key also keeps it outside
the address-shaped balance region. -/
theorem runtimeNonceKey_not_valid (w : B256) :
    ¬ ValidAdr (nonceTagWord ||| ((~~~ addressMask) &&& w)) := by
  let owner := ((~~~ addressMask) &&& w).toAdr
  have hvalid : ValidAdr ((~~~ addressMask) &&& w) :=
    normalizedAddress_valid w
  have howner : owner.toB256 = (~~~ addressMask) &&& w :=
    toB256_toAdr hvalid
  rw [← howner]
  simpa only [nonceTagWord, ← nonceKey_formula] using
    nonceKey_not_valid owner

/-- The exact `addressArg` walk: load a raw ABI word and retain only its low
160 bits. -/
theorem prefix_of_addressArg {e : Sevm} {k : B256} {xs : Stack}
    {s s' : Devm} (hp : xs <<+ s.stack)
    (run : Line.Run e s (addressArg k) s') :
    ((~~~ addressMask) &&& Sevm.argWord e k) :: xs <<+ s'.stack := by
  unfold addressArg normalizeAddress at run
  rcases of_run_append (arg k) run with ⟨s1, harg, run1⟩
  have hp1 : Sevm.argWord e k :: xs <<+ s1.stack :=
    prefix_of_arg hp harg
  rcases of_run_append pushAddressMask run1 with ⟨s2, hmask, run2⟩
  have hp2 : addressMask :: Sevm.argWord e k :: xs <<+ s2.stack :=
    of_push_addressMask hp1 hmask
  rcases Line.of_run_cons run2 with ⟨s3, hnot, run3⟩
  have hp3 : (~~~ addressMask) :: Sevm.argWord e k :: xs <<+ s3.stack :=
    prefix_of_not hnot hp2
  rcases Line.of_run_cons run3 with ⟨s4, hand, hnil⟩
  cases hnil
  exact prefix_of_and hand hp3

/-! ## Tagged allowance keys -/

/-- The exact key emitted by `allowanceKeyFromMemory` is in the tagged
allowance region for every keccak result. -/
theorem runtimeAllowanceKey_region (w : B256) :
    InRegion .allowance
      (allowanceTagWord ||| (allowancePayloadMask &&& w)) := by
  change (0xc000000000000000 : UInt64) &&&
    ((0x8000000000000000 : UInt64) |||
      ((0x3fffffffffffffff : UInt64) &&& w.1.1)) =
    (0x8000000000000000 : UInt64)
  apply UInt64.toBitVec_inj.mp
  rw [UInt64.toBitVec_and, UInt64.toBitVec_or,
    BitVec.and_or_distrib_left]
  simp only [UInt64.toBitVec_and]
  have htags :
      (0xc000000000000000 : UInt64).toBitVec &&&
          (0x8000000000000000 : UInt64).toBitVec =
        (0x8000000000000000 : UInt64).toBitVec := by
    rfl
  have hmask :
      (0xc000000000000000 : UInt64).toBitVec &&&
          (0x3fffffffffffffff : UInt64).toBitVec = 0 := by
    rfl
  rw [htags, ← BitVec.and_assoc, hmask]
  simp

theorem runtimeAllowanceKey_not_valid (w : B256) :
    ¬ ValidAdr (allowanceTagWord ||| (allowancePayloadMask &&& w)) := by
  intro h
  rcases h with ⟨a, ha⟩
  apply regions_disjoint (x := .balance) (y := .allowance)
    (by decide) (allowanceTagWord ||| (allowancePayloadMask &&& w))
  · rw [← ha]
    simpa only [balanceKey] using balanceKey_region a
  · exact runtimeAllowanceKey_region w

theorem runtimeAllowanceKey_ne_flash (w : B256) :
    allowanceTagWord ||| (allowancePayloadMask &&& w) ≠ flashMintedSlot := by
  intro h
  apply regions_disjoint (x := .allowance) (y := .flash)
    (by decide) (allowanceTagWord ||| (allowancePayloadMask &&& w))
  · exact runtimeAllowanceKey_region w
  · rw [h]
    exact flashMintedSlot_region

/-- The value-level stack effect of the exact allowance-key fragment. -/
theorem prefix_of_allowanceKeyFromMemory {e : Sevm} {xs : Stack}
    {s s' : Devm} (hp : xs <<+ s.stack)
    (run : Line.Run e s allowanceKeyFromMemory s') :
    ∃ hash,
      (allowanceTagWord ||| (allowancePayloadMask &&& hash)) :: xs <<+
        s'.stack := by
  unfold allowanceKeyFromMemory pushList at run
  simp only [List.map] at run
  rcases Line.of_run_cons run with ⟨s1, hpush64, run1⟩
  have hp1 : (64 : B256) :: xs <<+ s1.stack :=
    prefix_of_push (of_run_pushB256 hpush64) hp
  rcases Line.of_run_cons run1 with ⟨s2, hpush0, run2⟩
  have hp2 : (0 : B256) :: 64 :: xs <<+ s2.stack :=
    prefix_of_push (of_run_pushB256 hpush0) hp1
  rcases Line.of_run_cons run2 with ⟨s3, hkec, run3⟩
  rcases prefix_of_kec hkec hp2 with ⟨hash, hp3⟩
  rcases Line.of_run_cons run3 with ⟨s4, hpushMask, run4⟩
  have hp4 : allowancePayloadMask :: hash :: xs <<+ s4.stack :=
    prefix_of_push (of_run_pushB256 hpushMask) hp3
  rcases Line.of_run_cons run4 with ⟨s5, hand, run5⟩
  have hp5 : (allowancePayloadMask &&& hash) :: xs <<+ s5.stack :=
    prefix_of_and hand hp4
  rcases Line.of_run_cons run5 with ⟨s6, hpushTag, run6⟩
  have hp6 :
      allowanceTagWord :: (allowancePayloadMask &&& hash) :: xs <<+
        s6.stack :=
    prefix_of_push (of_run_pushB256 hpushTag) hp5
  rcases Line.of_run_cons run6 with ⟨s7, hor, hnil⟩
  cases hnil
  exact ⟨hash, prefix_of_or hor hp6⟩

/-- The exact caller-allowance loader exposes the tagged runtime key, loaded
allowance, and max-allowance flag while preserving an arbitrary stack tail. -/
theorem prefix_of_callerAllowanceIsMax (owner : B256)
    {e : Sevm} {s r : Devm} {xs : Stack}
    (hp : xs <<+ s.stack)
    (run : Line.Run e s
      (arg owner ++ mstoreAt 0 ++ [caller] ++ mstoreAt 1 ++
        allowanceKeyFromMemory ++ [dup 0, sload, dup 0] ++ isMax) r) :
    ∃ hash allowance,
      allowance =
        (Devm.getStor s e.currentTarget).get
          (allowanceTagWord ||| (allowancePayloadMask &&& hash)) ∧
      (((~~~ allowance) =? 0) :: allowance ::
        (allowanceTagWord ||| (allowancePayloadMask &&& hash)) :: xs) <<+
          r.stack := by
  let pre : Line :=
    arg owner ++ mstoreAt 0 ++ [caller] ++ mstoreAt 1
  rcases of_run_append pre run with ⟨s1, hpre, run1⟩
  have hp1 : xs <<+ s1.stack := by
    unfold pre at hpre
    rcases of_run_append (arg owner) hpre with
      ⟨p1, howner, hpre1⟩
    have hpp1 : Sevm.argWord e owner :: xs <<+ p1.stack :=
      prefix_of_arg hp howner
    rcases of_run_append (mstoreAt 0) hpre1 with
      ⟨p2, hmstore0, hpre2⟩
    have hpp2 : xs <<+ p2.stack :=
      prefix_of_mstoreAt hmstore0 hpp1
    rcases Line.of_run_cons hpre2 with
      ⟨p3, hcaller, hpre3⟩
    have hpp3 : e.caller.toB256 :: xs <<+ p3.stack :=
      prefix_of_push (of_run_caller hcaller) hpp2
    exact prefix_of_mstoreAt hpre3 hpp3
  rcases of_run_append allowanceKeyFromMemory run1 with
    ⟨s2, hkey, run2⟩
  rcases prefix_of_allowanceKeyFromMemory hp1 hkey with
    ⟨hash, hp2⟩
  let key := allowanceTagWord ||| (allowancePayloadMask &&& hash)
  rcases Line.of_run_cons run2 with ⟨s3, hdup1, run3⟩
  have hp3 : key :: key :: xs <<+ s3.stack :=
    prefix_of_dup_val hdup1 (by show_nth) hp2
  rcases Line.of_run_cons run3 with ⟨s4, hload, run4⟩
  rcases prefix_of_sload hload hp3 with
    ⟨allowance, hp4, hallowance⟩
  rcases Line.of_run_cons run4 with ⟨s5, hdup2, run5⟩
  have hp5 : allowance :: allowance :: key :: xs <<+ s5.stack :=
    prefix_of_dup_val hdup2 (by show_nth) hp4
  unfold isMax at run5
  rcases Line.of_run_cons run5 with ⟨s6, hnot, run6⟩
  have hp6 : (~~~ allowance) :: allowance :: key :: xs <<+ s6.stack :=
    prefix_of_not hnot hp5
  rcases Line.of_run_cons run6 with ⟨s7, hiszero, hnil⟩
  cases hnil
  have hp7 : ((~~~ allowance) =? 0) :: allowance :: key :: xs <<+
      r.stack := prefix_of_iszero hiszero hp6
  have hs : Devm.getStor s = Devm.getStor s3 := by
    rw [Line.of_inv Devm.getStor (by line_inv) hpre,
      Line.of_inv Devm.getStor (by line_inv) hkey,
      Line.of_inv Devm.getStor (by line_inv)
        (Line.Run.cons hdup1 Line.Run.nil)]
  change allowance = (Devm.getStor s3 e.currentTarget).get key at hallowance
  refine ⟨hash, allowance, ?_, hp7⟩
  rw [hallowance, ← congrFun hs e.currentTarget]

/-- The exact self-allowance loader used by flash settlement. -/
theorem prefix_of_selfAllowanceIsMax (owner : B256)
    {e : Sevm} {s r : Devm} {xs : Stack}
    (hp : xs <<+ s.stack)
    (run : Line.Run e s
      (addressArg owner ++ mstoreAt 0 ++ [address] ++ mstoreAt 1 ++
        allowanceKeyFromMemory ++ [dup 0, sload, dup 0] ++ isMax) r) :
    ∃ hash allowance,
      allowance =
        (Devm.getStor s e.currentTarget).get
          (allowanceTagWord ||| (allowancePayloadMask &&& hash)) ∧
      (((~~~ allowance) =? 0) :: allowance ::
        (allowanceTagWord ||| (allowancePayloadMask &&& hash)) :: xs) <<+
          r.stack := by
  let pre : Line :=
    addressArg owner ++ mstoreAt 0 ++ [address] ++ mstoreAt 1
  rcases of_run_append pre run with ⟨s1, hpre, run1⟩
  have hp1 : xs <<+ s1.stack := by
    unfold pre at hpre
    rcases of_run_append (addressArg owner) hpre with
      ⟨p1, howner, hpre1⟩
    have hpp1 : ((~~~ addressMask) &&& Sevm.argWord e owner) :: xs <<+
        p1.stack := prefix_of_addressArg hp howner
    rcases of_run_append (mstoreAt 0) hpre1 with
      ⟨p2, hmstore0, hpre2⟩
    have hpp2 : xs <<+ p2.stack :=
      prefix_of_mstoreAt hmstore0 hpp1
    rcases Line.of_run_cons hpre2 with
      ⟨p3, haddress, hpre3⟩
    have hpp3 : e.currentTarget.toB256 :: xs <<+ p3.stack :=
      prefix_of_push (of_run_address haddress) hpp2
    exact prefix_of_mstoreAt hpre3 hpp3
  rcases of_run_append allowanceKeyFromMemory run1 with
    ⟨s2, hkey, run2⟩
  rcases prefix_of_allowanceKeyFromMemory hp1 hkey with
    ⟨hash, hp2⟩
  let key := allowanceTagWord ||| (allowancePayloadMask &&& hash)
  rcases Line.of_run_cons run2 with ⟨s3, hdup1, run3⟩
  have hp3 : key :: key :: xs <<+ s3.stack :=
    prefix_of_dup_val hdup1 (by show_nth) hp2
  rcases Line.of_run_cons run3 with ⟨s4, hload, run4⟩
  rcases prefix_of_sload hload hp3 with
    ⟨allowance, hp4, hallowance⟩
  rcases Line.of_run_cons run4 with ⟨s5, hdup2, run5⟩
  have hp5 : allowance :: allowance :: key :: xs <<+ s5.stack :=
    prefix_of_dup_val hdup2 (by show_nth) hp4
  unfold isMax at run5
  rcases Line.of_run_cons run5 with ⟨s6, hnot, run6⟩
  have hp6 : (~~~ allowance) :: allowance :: key :: xs <<+ s6.stack :=
    prefix_of_not hnot hp5
  rcases Line.of_run_cons run6 with ⟨s7, hiszero, hnil⟩
  cases hnil
  have hp7 : ((~~~ allowance) =? 0) :: allowance :: key :: xs <<+
      r.stack := prefix_of_iszero hiszero hp6
  have hs : Devm.getStor s = Devm.getStor s3 := by
    rw [Line.of_inv Devm.getStor (by line_inv) hpre,
      Line.of_inv Devm.getStor (by line_inv) hkey,
      Line.of_inv Devm.getStor (by line_inv)
        (Line.Run.cons hdup1 Line.Run.nil)]
  change allowance = (Devm.getStor s3 e.currentTarget).get key at hallowance
  refine ⟨hash, allowance, ?_, hp7⟩
  rw [hallowance, ← congrFun hs e.currentTarget]

/-- The balance guard duplicates its inputs and exposes exactly the EVM
less-than flag used by the following reverting branch. -/
theorem prefix_of_balanceTooSmall
    {e : Sevm} {s r : Devm} {balance value owner : B256} {xs : Stack}
    (hp : balance :: value :: owner :: xs <<+ s.stack)
    (run : Line.Run e s balanceTooSmall r) :
    (balance <? value) :: balance :: value :: owner :: xs <<+
      r.stack := by
  unfold balanceTooSmall at run
  rcases Line.of_run_cons run with ⟨s1, hdup1, run1⟩
  have hp1 : value :: balance :: value :: owner :: xs <<+ s1.stack :=
    prefix_of_dup_val hdup1 (by show_nth) hp
  rcases Line.of_run_cons run1 with ⟨s2, hdup2, run2⟩
  have hp2 : balance :: value :: balance :: value :: owner :: xs <<+
      s2.stack := prefix_of_dup_val hdup2 (by show_nth) hp1
  rcases Line.of_run_cons run2 with ⟨s3, hlt, hnil⟩
  cases hnil
  exact prefix_of_lt hlt hp2

/-- A successful conditional whose selected error arm is an exact `revWith`
must have taken the zero/continuation arm. -/
theorem of_run_branch_call_revWith
    {fs : List Func} {e : Sevm} {s r : Devm} {k : Nat}
    {payload : String} {next : Func}
    (hget : fs[k]? = some (Func.revWith payload))
    (run : Func.Run fs e s ((.call k) <?> next) r) :
    ∃ s', Devm.PopBurn [0] s s' ∧ Func.Run fs e s' next r := by
  exact Blanc.of_run_branch_call_revWith hget run

/-- Spending a caller allowance is backing-silent before its tail jump.  The
self-owner and infinite-allowance paths leave storage unchanged; the finite
path writes only the runtime-tagged allowance key. -/
theorem of_run_spendCallerAllowanceThen
    (dp : DeployParams) (amount : B256) (nextSlot : Nat)
    (core : Func)
    (hnext : ((weth10 dp).main :: weth10Aux)[nextSlot]? = some core)
    {e : Sevm} {s r : Devm}
    (run : Func.Run ((weth10 dp).main :: weth10Aux) e s
      (spendCallerAllowanceThen amount nextSlot) r) :
    ∃ sc,
      Func.Run ((weth10 dp).main :: weth10Aux) e sc core r ∧
      Stor.Weth10Silent
        (Devm.getStor s e.currentTarget)
        (Devm.getStor sc e.currentTarget) ∧
      Devm.getBal s = Devm.getBal sc ∧
      Devm.getCode s e.currentTarget = Devm.getCode sc e.currentTarget := by
  unfold spendCallerAllowanceThen at run
  rcases of_run_prepend (arg 0 ++ [caller, eq]) _ run with
    ⟨s1, hownerEq, run1⟩
  have hp1 :
      (e.caller.toB256 =? Sevm.argWord e 0) :: [] <<+ s1.stack := by
    rcases of_run_append (arg 0) hownerEq with
      ⟨p1, harg, hownerEq1⟩
    have hpArg : Sevm.argWord e 0 :: [] <<+ p1.stack :=
      prefix_of_arg nil_pref harg
    rcases Line.of_run_cons hownerEq1 with
      ⟨p2, hcaller, hownerEq2⟩
    have hpCaller :
        e.caller.toB256 :: Sevm.argWord e 0 :: [] <<+ p2.stack :=
      prefix_of_push (of_run_caller hcaller) hpArg
    rcases Line.of_run_cons hownerEq2 with
      ⟨p3, heq, hnil⟩
    cases hnil
    exact prefix_of_eq heq hpCaller
  rcases of_run_branch run1 with
      ⟨s2, houterPop, hnonself⟩ |
      ⟨w, s2, s3, hnz, houterPop, houterBurn, hself⟩
  · let loadLine : Line :=
      arg 0 ++ mstoreAt 0 ++ [caller] ++ mstoreAt 1 ++
        allowanceKeyFromMemory ++ [dup 0, sload, dup 0] ++ isMax
    rcases of_run_prepend loadLine _ hnonself with
      ⟨sl, hload, runLoad⟩
    have h_stor_s_sl : Devm.getStor s = Devm.getStor sl :=
      (Line.of_inv Devm.getStor (by line_inv) hownerEq).trans
        ((PopBurn.Inv.inv houterPop).trans
          (Line.of_inv Devm.getStor (by line_inv) hload))
    have h_bal_s_sl : Devm.getBal s = Devm.getBal sl :=
      (Line.of_inv Devm.getBal (by line_inv) hownerEq).trans
        ((PopBurn.Inv.inv houterPop).trans
          (Line.of_inv Devm.getBal (by line_inv) hload))
    have h_code_s_sl :
        Devm.getCode s e.currentTarget =
          Devm.getCode sl e.currentTarget :=
      (congrFun (Line.of_inv Devm.getCode (by line_inv) hownerEq)
          e.currentTarget).trans
        ((getCode_eq_of_state_eq houterPop.state e.currentTarget).trans
          (congrFun (Line.of_inv Devm.getCode (by line_inv) hload)
            e.currentTarget))
    obtain ⟨hash, allowance, hallowance, hpLoad⟩ :=
      prefix_of_callerAllowanceIsMax 0 nil_pref (by
        simpa only [loadLine] using hload)
    let key := allowanceTagWord ||| (allowancePayloadMask &&& hash)
    rcases of_run_branch runLoad with
        ⟨sf, hfinitePop, hfinite⟩ |
        ⟨wmax, sm1, sm2, hnzmax, hmaxPop, hmaxBurn, hmax⟩
    · have hfiniteStack := hfinitePop.stack
      simp only [Stack.Pop, Split, List.nil_append, List.cons_append] at hfiniteStack
      rw [hfiniteStack] at hpLoad
      have hmaxFlag : ((~~~ allowance) =? 0) = 0 :=
        pref_head_unique hpLoad (pref_append [0] sf.stack)
      rw [hmaxFlag] at hpLoad
      have hpFinite : allowance :: key :: [] <<+ sf.stack :=
        cons_pref_cons_inv hpLoad
      let guardLine : Line := arg amount ++ [swap 0] ++ balanceTooSmall
      rcases of_run_prepend guardLine _ hfinite with
        ⟨sg, hguardLine, runGuard⟩
      have hpGuard :
          (allowance <? Sevm.argWord e amount) :: allowance ::
            Sevm.argWord e amount :: key :: [] <<+ sg.stack := by
        unfold guardLine at hguardLine
        rcases of_run_append (arg amount) hguardLine with
          ⟨sa, hamount, hguard1⟩
        have hpa :
            Sevm.argWord e amount :: allowance :: key :: [] <<+
              sa.stack := prefix_of_arg hpFinite hamount
        rcases Line.of_run_cons hguard1 with
          ⟨ss, hswap, htooSmall⟩
        have hswapCore : Stack.Swap (0 : Fin 16).val
            (Sevm.argWord e amount :: allowance :: key :: [])
            (allowance :: Sevm.argWord e amount :: key :: []) :=
          Stack.swapCore_zero
        have hps :
            allowance :: Sevm.argWord e amount :: key :: [] <<+
              ss.stack :=
          Stack.prefix_of_swap hswapCore (of_run_swap hswap) hpa
        exact prefix_of_balanceTooSmall hps htooSmall
      have h_allowance_lookup :
          ((weth10 dp).main :: weth10Aux)[allowanceErrorSlot]? =
            some (Func.revWith "WETH: request exceeds allowance") := by
        simp [weth10, weth10Aux, allowanceErrorSlot, allowanceError]
      rcases of_run_branch_call_revWith h_allowance_lookup runGuard with
        ⟨sb, hguardPop, runMutate⟩
      have hguardStack := hguardPop.stack
      simp only [Stack.Pop, Split, List.nil_append, List.cons_append] at hguardStack
      rw [hguardStack] at hpGuard
      have hguardFlag : (allowance <? Sevm.argWord e amount) = 0 :=
        pref_head_unique hpGuard (pref_append [0] sb.stack)
      rw [hguardFlag] at hpGuard
      have hpBeforeMutate :
          allowance :: Sevm.argWord e amount :: key :: [] <<+ sb.stack :=
        cons_pref_cons_inv hpGuard
      let mutateLine : Line :=
        [sub, dup 0, swap 1, sstore] ++
          arg 0 ++ [swap 0, caller] ++ emitApproval ++ [pop, pop]
      rcases of_run_prepend mutateLine _ runMutate with
        ⟨scall, hmutate, hcallRun⟩
      unfold mutateLine at hmutate
      rcases Line.of_run_cons hmutate with
        ⟨ms1, hsub, hmutate1⟩
      have hpSub :
          (allowance - Sevm.argWord e amount) :: key :: [] <<+
            ms1.stack := prefix_of_sub hsub hpBeforeMutate
      rcases Line.of_run_cons hmutate1 with
        ⟨ms2, hdup, hmutate2⟩
      have hpDup :
          (allowance - Sevm.argWord e amount) ::
            (allowance - Sevm.argWord e amount) :: key :: [] <<+
              ms2.stack :=
        prefix_of_dup_val hdup (by show_nth) hpSub
      rcases Line.of_run_cons hmutate2 with
        ⟨ms3, hswap, hmutate3⟩
      have hswapCore : Stack.Swap (1 : Fin 16).val
          ((allowance - Sevm.argWord e amount) ::
            (allowance - Sevm.argWord e amount) :: key :: [])
          (key :: (allowance - Sevm.argWord e amount) ::
            (allowance - Sevm.argWord e amount) :: []) :=
        Stack.swapCore_succ Stack.swapCore_zero
      have hpStore :
          key :: (allowance - Sevm.argWord e amount) ::
            (allowance - Sevm.argWord e amount) :: [] <<+ ms3.stack :=
        Stack.prefix_of_swap hswapCore (of_run_swap hswap) hpDup
      rcases Line.of_run_cons hmutate3 with
        ⟨ms4, hstore, happroval⟩
      have hset :
          Devm.getStor ms4 e.currentTarget =
            (Devm.getStor ms3 e.currentTarget).set key
              (allowance - Sevm.argWord e amount) :=
        sstore_getStor_set hstore hpStore
      rcases of_run_call hcallRun with
        ⟨f, sc, hget, hcallBurn, hcore⟩
      have hf : f = core := by
        rw [hnext] at hget
        exact Option.some.inj hget.symm
      subst f
      have h_stor_s_ms3 : Devm.getStor s = Devm.getStor ms3 :=
        h_stor_s_sl.trans
          ((PopBurn.Inv.inv hfinitePop).trans
            ((Line.of_inv Devm.getStor (by line_inv) hguardLine).trans
              ((PopBurn.Inv.inv hguardPop).trans
                ((Line.of_inv Devm.getStor (by line_inv)
                  (Line.Run.cons hsub Line.Run.nil)).trans
                  ((Line.of_inv Devm.getStor (by line_inv)
                    (Line.Run.cons hdup Line.Run.nil)).trans
                    (Line.of_inv Devm.getStor (by line_inv)
                      (Line.Run.cons hswap Line.Run.nil)))))))
      have h_stor_scall_sc : Devm.getStor scall = Devm.getStor sc :=
        Burn.Inv.inv hcallBurn
      have h_stor_ms4_scall : Devm.getStor ms4 = Devm.getStor scall :=
        Line.of_inv Devm.getStor (by line_inv) happroval
      have h_stor_sc :
          Devm.getStor sc e.currentTarget =
            (Devm.getStor s e.currentTarget).set key
              (allowance - Sevm.argWord e amount) := by
        rw [← congrFun h_stor_scall_sc e.currentTarget,
          ← congrFun h_stor_ms4_scall e.currentTarget,
          hset,
          ← congrFun h_stor_s_ms3 e.currentTarget]
      have h_bal_s_sc : Devm.getBal s = Devm.getBal sc :=
        h_bal_s_sl.trans
          ((PopBurn.Inv.inv hfinitePop).trans
            ((Line.of_inv Devm.getBal (by line_inv) hguardLine).trans
              ((PopBurn.Inv.inv hguardPop).trans
                ((Line.of_inv Devm.getBal (by line_inv) hmutate).trans
                  (Burn.Inv.inv hcallBurn)))))
      have h_code_s_sc :
          Devm.getCode s e.currentTarget =
            Devm.getCode sc e.currentTarget :=
        h_code_s_sl.trans
          ((getCode_eq_of_state_eq hfinitePop.state e.currentTarget).trans
            ((congrFun (Line.of_inv Devm.getCode (by line_inv) hguardLine)
                e.currentTarget).trans
              ((getCode_eq_of_state_eq hguardPop.state
                  e.currentTarget).trans
                ((congrFun (Line.of_inv Devm.getCode (by line_inv) hmutate)
                    e.currentTarget).trans
                  (getCode_eq_of_state_eq hcallBurn.state
                    e.currentTarget)))))
      refine ⟨sc, hcore, ?_, h_bal_s_sc, h_code_s_sc⟩
      rw [h_stor_sc]
      exact Stor.Weth10Silent.set
        (runtimeAllowanceKey_not_valid hash)
        (runtimeAllowanceKey_ne_flash hash)
    · rcases of_run_next hmax with ⟨sm3, hpop1, hmax1⟩
      rcases of_run_next hmax1 with ⟨sm4, hpop2, hcallRun⟩
      rcases of_run_call hcallRun with
        ⟨f, sc, hget, hcallBurn, hcore⟩
      have hf : f = core := by
        rw [hnext] at hget
        exact Option.some.inj hget.symm
      subst f
      let hpops : Line.Run e sm2 [pop, pop] sm4 :=
        Line.Run.cons hpop1 (Line.Run.cons hpop2 Line.Run.nil)
      have h_stor_s_sc : Devm.getStor s = Devm.getStor sc :=
        h_stor_s_sl.trans
          ((PopBurn.Inv.inv hmaxPop).trans
            ((Burn.Inv.inv hmaxBurn).trans
              ((Line.of_inv Devm.getStor (by line_inv) hpops).trans
                (Burn.Inv.inv hcallBurn))))
      have h_bal_s_sc : Devm.getBal s = Devm.getBal sc :=
        h_bal_s_sl.trans
          ((PopBurn.Inv.inv hmaxPop).trans
            ((Burn.Inv.inv hmaxBurn).trans
              ((Line.of_inv Devm.getBal (by line_inv) hpops).trans
                (Burn.Inv.inv hcallBurn))))
      have h_code_s_sc :
          Devm.getCode s e.currentTarget =
            Devm.getCode sc e.currentTarget :=
        h_code_s_sl.trans
          ((getCode_eq_of_state_eq hmaxPop.state e.currentTarget).trans
            ((getCode_eq_of_state_eq hmaxBurn.state e.currentTarget).trans
              ((congrFun (Line.of_inv Devm.getCode (by line_inv) hpops)
                  e.currentTarget).trans
                (getCode_eq_of_state_eq hcallBurn.state e.currentTarget))))
      exact ⟨sc, hcore,
        Stor.Weth10Silent.of_eq
          (congrFun h_stor_s_sc e.currentTarget),
        h_bal_s_sc, h_code_s_sc⟩
  · rcases of_run_call hself with
      ⟨f, sc, hget, hcallBurn, hcore⟩
    have hf : f = core := by
      rw [hnext] at hget
      exact Option.some.inj hget.symm
    subst f
    have h_stor_s_sc : Devm.getStor s = Devm.getStor sc :=
      (Line.of_inv Devm.getStor (by line_inv) hownerEq).trans
        ((PopBurn.Inv.inv houterPop).trans
          ((Burn.Inv.inv houterBurn).trans
            (Burn.Inv.inv hcallBurn)))
    have h_bal_s_sc : Devm.getBal s = Devm.getBal sc :=
      (Line.of_inv Devm.getBal (by line_inv) hownerEq).trans
        ((PopBurn.Inv.inv houterPop).trans
          ((Burn.Inv.inv houterBurn).trans
            (Burn.Inv.inv hcallBurn)))
    have h_code_s_sc :
        Devm.getCode s e.currentTarget =
          Devm.getCode sc e.currentTarget :=
      (congrFun (Line.of_inv Devm.getCode (by line_inv) hownerEq)
          e.currentTarget).trans
        ((getCode_eq_of_state_eq houterPop.state e.currentTarget).trans
          ((getCode_eq_of_state_eq houterBurn.state e.currentTarget).trans
            (getCode_eq_of_state_eq hcallBurn.state e.currentTarget)))
    exact ⟨sc, hcore,
      Stor.Weth10Silent.of_eq
        (congrFun h_stor_s_sc e.currentTarget),
      h_bal_s_sc, h_code_s_sc⟩

/-- A backing-silent storage transition, with unchanged balances and code,
transports the WETH10 frame-entry precondition. -/
theorem backedPre_of_silent (dp : DeployParams) (ca : Adr)
    {sevm : Sevm} {s sc : Devm}
    (h_pre : (backedSpec weth10 dp).Pre ca sevm s)
    (h_silent : Stor.Weth10Silent
      (Devm.getStor s ca) (Devm.getStor sc ca))
    (h_bal : Devm.getBal s = Devm.getBal sc)
    (h_code : Devm.getCode s ca = Devm.getCode sc ca) :
    (backedSpec weth10 dp).Pre ca sevm sc := by
  refine ⟨?_, ?_, ?_⟩
  · rw [← h_code]
    exact h_pre.code
  · rw [← h_bal]
    exact h_pre.side
  · constructor
    · intro h_target
      have h := h_pre.inv.1 h_target
      change Stor.Weth10Inv
        (Devm.getStor sc ca) sevm.value (Devm.getBal sc ca)
      rw [← congrFun h_bal ca]
      exact h.silent h_silent
    · intro h_target
      have h := h_pre.inv.2 h_target
      change Stor.Weth10Inv
        (Devm.getStor sc ca) 0 (Devm.getBal sc ca)
      rw [← congrFun h_bal ca]
      exact h.silent h_silent

/-- A backing-silent storage transition with unchanged balances transports an
already-established frame-exit postcondition. -/
theorem backedPost_of_silent (dp : DeployParams) (ca : Adr)
    {sevm : Sevm} {s r : Devm}
    (h_post : (backedSpec weth10 dp).Post ca sevm s)
    (h_silent : Stor.Weth10Silent
      (Devm.getStor s ca) (Devm.getStor r ca))
    (h_bal : Devm.getBal s = Devm.getBal r) :
    (backedSpec weth10 dp).Post ca sevm r := by
  refine ⟨?_, ?_⟩
  · rw [← h_bal]
    exact h_post.side
  · change Stor.Weth10Inv (Devm.getStor r ca) 0 (Devm.getBal r ca)
    rw [← congrFun h_bal ca]
    have h := h_post.inv
    change Stor.Weth10Inv (Devm.getStor s ca) 0
      (Devm.getBal s ca) at h
    exact h.silent h_silent

/-! ## Approve -/

/-- `approve` performs exactly one storage write, and its runtime-tagged key
is silent for the backing invariant. -/
theorem approve_storage_silent {fs : List Func} {sevm : Sevm}
    {s r : Devm} (run : Func.Run fs sevm s approve r) :
    Stor.Weth10Silent
      (Devm.getStor s sevm.currentTarget)
      (Devm.getStor r sevm.currentTarget) := by
  simp only [approve, approvePrefix] at run
  rcases of_run_prepend
      ([caller] ++ mstoreAt 0 ++ argCopy 1 0 1) _ run with
    ⟨s0, hpre, run0⟩
  rcases of_run_prepend allowanceKeyFromMemory _ run0 with
    ⟨s1, hkey, run1⟩
  rcases prefix_of_allowanceKeyFromMemory nil_pref hkey with
    ⟨hash, hp1⟩
  let key := allowanceTagWord ||| (allowancePayloadMask &&& hash)
  rcases of_run_prepend (arg 1) _ run1 with ⟨s2, harg, run2⟩
  have hp2 : Sevm.argWord sevm 1 :: key :: [] <<+ s2.stack :=
    prefix_of_arg hp1 harg
  rcases of_run_next run2 with ⟨s3, hswap, run3⟩
  have hswap_core : Stack.Swap (0 : Fin 16).val
      [Sevm.argWord sevm 1, key] [key, Sevm.argWord sevm 1] :=
    Stack.swapCore_zero
  have hp3 : key :: Sevm.argWord sevm 1 :: [] <<+ s3.stack :=
    Stack.prefix_of_swap hswap_core (of_run_swap hswap) hp2
  rcases of_run_next run3 with ⟨s4, hstore, run4⟩
  have hset :
      Devm.getStor s4 sevm.currentTarget =
        (Devm.getStor s3 sevm.currentTarget).set key
          (Sevm.argWord sevm 1) :=
    sstore_getStor_set hstore hp3
  have hs_before : Devm.getStor s = Devm.getStor s3 := by
    rw [Line.of_inv Devm.getStor (by line_inv) hpre,
      Line.of_inv Devm.getStor (by line_inv) hkey,
      Line.of_inv Devm.getStor (by line_inv) harg,
      Line.of_inv Devm.getStor (by line_inv)
        (Line.Run.cons hswap Line.Run.nil)]
  have hs_after : Devm.getStor s4 = Devm.getStor r :=
    Func.of_inv Devm.getStor Devm.getStor (by func_inv) run4
  rw [← congrFun hs_after sevm.currentTarget, hset,
    ← congrFun hs_before sevm.currentTarget]
  exact Stor.Weth10Silent.set
    (runtimeAllowanceKey_not_valid hash)
    (runtimeAllowanceKey_ne_flash hash)

/-- The exact `approvePrefix` line writes only its tagged allowance key, so it
is silent for the backing invariant before any callback continuation runs. -/
theorem approvePrefix_storage_silent {sevm : Sevm}
    {s r : Devm} (run : Line.Run sevm s approvePrefix r) :
    Stor.Weth10Silent
      (Devm.getStor s sevm.currentTarget)
      (Devm.getStor r sevm.currentTarget) := by
  simp only [approvePrefix] at run
  rcases of_run_append
      ([caller] ++ mstoreAt 0 ++ argCopy 1 0 1) run with
    ⟨s0, hpre, run0⟩
  rcases of_run_append allowanceKeyFromMemory run0 with
    ⟨s1, hkey, run1⟩
  rcases prefix_of_allowanceKeyFromMemory nil_pref hkey with
    ⟨hash, hp1⟩
  let key := allowanceTagWord ||| (allowancePayloadMask &&& hash)
  rcases of_run_append (arg 1) run1 with ⟨s2, harg, run2⟩
  have hp2 : Sevm.argWord sevm 1 :: key :: [] <<+ s2.stack :=
    prefix_of_arg hp1 harg
  rcases Line.of_run_cons run2 with ⟨s3, hswap, run3⟩
  have hswap_core : Stack.Swap (0 : Fin 16).val
      [Sevm.argWord sevm 1, key] [key, Sevm.argWord sevm 1] :=
    Stack.swapCore_zero
  have hp3 : key :: Sevm.argWord sevm 1 :: [] <<+ s3.stack :=
    Stack.prefix_of_swap hswap_core (of_run_swap hswap) hp2
  rcases Line.of_run_cons run3 with ⟨s4, hstore, run4⟩
  have hset :
      Devm.getStor s4 sevm.currentTarget =
        (Devm.getStor s3 sevm.currentTarget).set key
          (Sevm.argWord sevm 1) :=
    sstore_getStor_set hstore hp3
  have hs_before : Devm.getStor s = Devm.getStor s3 := by
    rw [Line.of_inv Devm.getStor (by line_inv) hpre,
      Line.of_inv Devm.getStor (by line_inv) hkey,
      Line.of_inv Devm.getStor (by line_inv) harg,
      Line.of_inv Devm.getStor (by line_inv)
        (Line.Run.cons hswap Line.Run.nil)]
  have hs_after : Devm.getStor s4 = Devm.getStor r :=
    Line.of_inv Devm.getStor (by line_inv) run4
  rw [← congrFun hs_after sevm.currentTarget, hset,
    ← congrFun hs_before sevm.currentTarget]
  exact Stor.Weth10Silent.set
    (runtimeAllowanceKey_not_valid hash)
    (runtimeAllowanceKey_ne_flash hash)

/-- The exact nonpayable `approve` selector preserves WETH10 backing. -/
theorem backedSpec_approve_funcSound (dp : DeployParams) (ca : Adr) :
    (backedSpec weth10 dp).FuncSoundNoMem ca weth10Aux
      (nonpayable approve) := by
  intro sevm s r h_target h_pre h_ih run
  subst ca
  refine ⟨Func.preserves_nof run h_pre.side, ?_⟩
  change Stor.Weth10Inv
    (Devm.getStor r sevm.currentTarget) 0
    (Devm.getBal r sevm.currentTarget)
  obtain ⟨mid, h_value, h_state_mid, h_body⟩ :=
    run_body_of_run_nonpayable run
  have h_stor_mid :
      Devm.getStor s sevm.currentTarget =
        Devm.getStor mid sevm.currentTarget := by
    change (s.state.get sevm.currentTarget).stor =
      (mid.state.get sevm.currentTarget).stor
    rw [h_state_mid]
  have h_silent :
      Stor.Weth10Silent
        (Devm.getStor s sevm.currentTarget)
        (Devm.getStor r sevm.currentTarget) :=
    (Stor.Weth10Silent.of_eq h_stor_mid).trans
      (approve_storage_silent h_body)
  have h_inv : Stor.Weth10Inv
      (Devm.getStor s sevm.currentTarget) sevm.value
      (Devm.getBal s sevm.currentTarget) :=
    h_pre.inv.1 rfl
  have h_post := h_inv.silent h_silent
  have h_bal : Devm.getBal s = Devm.getBal r :=
    Func.of_inv Devm.getBal Devm.getBal (by func_inv) run
  rw [← congrFun h_bal sevm.currentTarget]
  simpa only [h_value] using h_post

/-! ## Deposit to an address -/

/-- A successful exact `depositTo` run credits the normalized low-160-bit
address and leaves the disjoint flash counter unchanged. -/
theorem depositTo_storage {fs : List Func} {sevm : Sevm}
    {s r : Devm} (run : Func.Run fs sevm s depositTo r) :
    ∃ recipient : Adr,
      Increase recipient sevm.value
        (Stor.rest (Devm.getStor s sevm.currentTarget))
        (Stor.rest (Devm.getStor r sevm.currentTarget)) ∧
      (Devm.getStor r sevm.currentTarget).get flashMintedSlot =
        (Devm.getStor s sevm.currentTarget).get flashMintedSlot := by
  simp only [depositTo, mintToPrefix] at run
  rcases of_run_prepend (addressArg 0) _ run with
    ⟨s1, harg1, run1⟩
  let key := (~~~ addressMask) &&& Sevm.argWord sevm 0
  have hp1 : key :: [] <<+ s1.stack :=
    prefix_of_addressArg nil_pref harg1
  have hvalid : ValidAdr key :=
    normalizedAddress_valid (Sevm.argWord sevm 0)
  rcases of_run_next run1 with ⟨s2, hload, run2⟩
  rcases prefix_of_sload hload hp1 with ⟨toBal, hp2, htoBal⟩
  rcases of_run_next run2 with ⟨s3, hvalue, run3⟩
  have hp3 : sevm.value :: toBal :: [] <<+ s3.stack :=
    prefix_of_push (of_run_callvalue hvalue) hp2
  rcases of_run_next run3 with ⟨s4, hadd, run4⟩
  have hp4 : (sevm.value + toBal) :: [] <<+ s4.stack :=
    prefix_of_add hadd hp3
  rcases of_run_prepend (addressArg 0) _ run4 with
    ⟨s5, harg2, run5⟩
  have hp5 : key :: (sevm.value + toBal) :: [] <<+ s5.stack :=
    prefix_of_addressArg hp4 harg2
  rcases of_run_next run5 with ⟨s6, hstore, run6⟩
  have hset :
      Devm.getStor s6 sevm.currentTarget =
        (Devm.getStor s5 sevm.currentTarget).set key
          (sevm.value + toBal) :=
    sstore_getStor_set hstore hp5
  have hs1 : Devm.getStor s = Devm.getStor s1 :=
    Line.of_inv Devm.getStor (by line_inv) harg1
  have hs2 : Devm.getStor s1 = Devm.getStor s2 :=
    Line.of_inv Devm.getStor (by line_inv)
      (Line.Run.cons hload Line.Run.nil)
  have hs3 : Devm.getStor s2 = Devm.getStor s3 :=
    Line.of_inv Devm.getStor (by line_inv)
      (Line.Run.cons hvalue Line.Run.nil)
  have hs4 : Devm.getStor s3 = Devm.getStor s4 :=
    Line.of_inv Devm.getStor (by line_inv)
      (Line.Run.cons hadd Line.Run.nil)
  have hs5 : Devm.getStor s4 = Devm.getStor s5 :=
    Line.of_inv Devm.getStor (by line_inv) harg2
  have hs_before : Devm.getStor s = Devm.getStor s5 := by
    rw [hs1, hs2, hs3, hs4, hs5]
  have hs_after : Devm.getStor s6 = Devm.getStor r :=
    Func.of_inv Devm.getStor Devm.getStor (by func_inv) run6
  have htoBal' :
      toBal = (Devm.getStor s5 sevm.currentTarget).get key := by
    rw [htoBal]
    show (Devm.getStor s1 sevm.currentTarget).get key = _
    rw [hs2, hs3, hs4, hs5]
  have hkey : key.toAdr.toB256 = key :=
    toB256_toAdr hvalid
  have hset' :
      Devm.getStor s6 sevm.currentTarget =
        (Devm.getStor s5 sevm.currentTarget).set key.toAdr.toB256
          (sevm.value + toBal) := by
    simpa only [hkey] using hset
  refine ⟨key.toAdr, ?_, ?_⟩
  · rw [hs_before, ← hs_after]
    intro a
    constructor
    · intro h_eq
      subst h_eq
      simp only [Stor.rest, Function.comp_apply]
      rw [hset', Stor.get_set_self, hkey, ← htoBal', B256.add_comm]
    · intro h_ne
      simp only [Stor.rest, Function.comp_apply]
      rw [hset']
      exact (Stor.get_set_ne _
        (fun hc => h_ne (Adr.toB256_inj hc)) _).symm
  · have h_flash_ne : key.toAdr.toB256 ≠ flashMintedSlot := by
      simpa only [balanceKey] using
        balanceKey_ne_flashMintedSlot key.toAdr
    rw [← hs_after, hset', Stor.get_set_ne _ h_flash_ne _, ← hs_before]

/-- The exact payable `depositTo` selector preserves WETH10 backing for both
canonical and dirty address words; the runtime normalizes both to low 160 bits. -/
theorem backedSpec_depositTo_funcSound (dp : DeployParams) (ca : Adr) :
    (backedSpec weth10 dp).FuncSoundNoMem ca weth10Aux depositTo := by
  intro sevm s r h_target h_pre h_ih run
  subst ca
  refine ⟨Func.preserves_nof run h_pre.side, ?_⟩
  change Stor.Weth10Inv
    (Devm.getStor r sevm.currentTarget) 0
    (Devm.getBal r sevm.currentTarget)
  have h_inv : Stor.Weth10Inv
      (Devm.getStor s sevm.currentTarget) sevm.value
      (Devm.getBal s sevm.currentTarget) :=
    h_pre.inv.1 rfl
  have h_bal : Devm.getBal s = Devm.getBal r :=
    Func.of_inv Devm.getBal Devm.getBal (by func_inv) run
  obtain ⟨recipient, h_inc, h_flash⟩ := depositTo_storage run
  rw [← congrFun h_bal sevm.currentTarget]
  exact Stor.Weth10Inv.deposit h_inv h_inc h_flash

/-! ## Shared transfer / withdrawal effects -/

/-- The exact caller-balance loader exposes the booked balance, requested
amount, and caller key on the stack. -/
theorem prefix_of_loadCallerBalanceAmount
    {e : Sevm} {s r : Devm} {k : B256} {xs : Stack}
    (hp : xs <<+ s.stack)
    (run : Line.Run e s (loadCallerBalanceAmount k) r) :
    ∃ balance,
      balance = (Devm.getStor s e.currentTarget).get e.caller.toB256 ∧
      (balance :: Sevm.argWord e k :: e.caller.toB256 :: xs) <<+
        r.stack := by
  unfold loadCallerBalanceAmount at run
  rcases Line.of_run_cons run with ⟨s1, hcaller, run1⟩
  have hp1 : e.caller.toB256 :: xs <<+ s1.stack :=
    prefix_of_push (of_run_caller hcaller) hp
  rcases Line.of_run_cons run1 with ⟨s2, hdup, run2⟩
  have hp2 : e.caller.toB256 :: e.caller.toB256 :: xs <<+ s2.stack :=
    prefix_of_dup_val hdup (by show_nth) hp1
  rcases Line.of_run_cons run2 with ⟨s3, hload, run3⟩
  rcases prefix_of_sload hload hp2 with ⟨balance, hp3, hbalance⟩
  rcases of_run_append (arg k) run3 with ⟨s4, harg, run4⟩
  have hp4 : Sevm.argWord e k :: balance :: e.caller.toB256 :: xs <<+
      s4.stack := prefix_of_arg hp3 harg
  rcases Line.of_run_cons run4 with ⟨s5, hswap, hnil⟩
  cases hnil
  have hswap_core : Stack.Swap (0 : Fin 16).val
      (Sevm.argWord e k :: balance :: e.caller.toB256 :: xs)
      (balance :: Sevm.argWord e k :: e.caller.toB256 :: xs) :=
    Stack.swapCore_zero
  refine ⟨balance, ?_, Stack.prefix_of_swap hswap_core
    (of_run_swap hswap) hp4⟩
  rw [hbalance]
  have hs : Devm.getStor s = Devm.getStor s2 := by
    rw [Line.of_inv Devm.getStor (by line_inv)
      (Line.Run.cons hcaller Line.Run.nil),
      Line.of_inv Devm.getStor (by line_inv)
        (Line.Run.cons hdup Line.Run.nil)]
  change (Devm.getStor s2 e.currentTarget).get e.caller.toB256 =
    (Devm.getStor s e.currentTarget).get e.caller.toB256
  rw [← congrFun hs e.currentTarget]

/-- The normalized-address balance loader exposes the booked balance,
requested amount, and exact low-160-bit owner key on the stack. -/
theorem prefix_of_loadArgBalanceAmount (owner amount : B256)
    {e : Sevm} {s r : Devm} {xs : Stack}
    (hp : xs <<+ s.stack)
    (run : Line.Run e s (loadArgBalanceAmount owner amount) r) :
    ∃ balance key,
      key = (~~~ addressMask) &&& Sevm.argWord e owner ∧
      balance = (Devm.getStor s e.currentTarget).get key ∧
      (balance :: Sevm.argWord e amount :: key :: xs) <<+ r.stack := by
  unfold loadArgBalanceAmount at run
  rcases of_run_append (addressArg owner) run with
    ⟨s1, howner, run1⟩
  let key := (~~~ addressMask) &&& Sevm.argWord e owner
  have hp1 : key :: xs <<+ s1.stack :=
    prefix_of_addressArg hp howner
  rcases Line.of_run_cons run1 with ⟨s2, hdup, run2⟩
  have hp2 : key :: key :: xs <<+ s2.stack :=
    prefix_of_dup_val hdup (by show_nth) hp1
  rcases Line.of_run_cons run2 with ⟨s3, hload, run3⟩
  rcases prefix_of_sload hload hp2 with
    ⟨balance, hp3, hbalance⟩
  rcases of_run_append (arg amount) run3 with
    ⟨s4, hamount, run4⟩
  have hp4 : Sevm.argWord e amount :: balance :: key :: xs <<+
      s4.stack := prefix_of_arg hp3 hamount
  rcases Line.of_run_cons run4 with ⟨s5, hswap, hnil⟩
  cases hnil
  have hswapCore : Stack.Swap (0 : Fin 16).val
      (Sevm.argWord e amount :: balance :: key :: xs)
      (balance :: Sevm.argWord e amount :: key :: xs) :=
    Stack.swapCore_zero
  have hp5 : balance :: Sevm.argWord e amount :: key :: xs <<+ r.stack :=
    Stack.prefix_of_swap hswapCore (of_run_swap hswap) hp4
  have hs : Devm.getStor s = Devm.getStor s2 := by
    rw [Line.of_inv Devm.getStor (by line_inv) howner,
      Line.of_inv Devm.getStor (by line_inv)
        (Line.Run.cons hdup Line.Run.nil)]
  change balance = (Devm.getStor s2 e.currentTarget).get key at hbalance
  refine ⟨balance, key, rfl, ?_, hp5⟩
  rw [hbalance, ← congrFun hs e.currentTarget]

/-- The exact debit fragment decreases one normalized balance, proves that the
amount was covered, and leaves the flash counter unchanged. -/
theorem debitLoadedBalance_storage {e : Sevm} {s r : Devm}
    {balance value owner : B256}
    (h_owner : ValidAdr owner)
    (h_balance : balance = (Devm.getStor s e.currentTarget).get owner)
    (h_le : value ≤ balance)
    (hp : [balance, value, owner] <<+ s.stack)
    (run : Line.Run e s debitLoadedBalance r) :
    Decrease owner.toAdr value
        (Stor.rest (Devm.getStor s e.currentTarget))
        (Stor.rest (Devm.getStor r e.currentTarget)) ∧
      value ≤ (Stor.rest (Devm.getStor s e.currentTarget)) owner.toAdr ∧
      (Devm.getStor r e.currentTarget).get flashMintedSlot =
        (Devm.getStor s e.currentTarget).get flashMintedSlot := by
  unfold debitLoadedBalance at run
  rcases Line.of_run_cons run with ⟨s1, hsub, run1⟩
  have hp1 : (balance - value) :: owner :: [] <<+ s1.stack :=
    prefix_of_sub hsub hp
  rcases Line.of_run_cons run1 with ⟨s2, hswap, run2⟩
  have hswap_core : Stack.Swap (0 : Fin 16).val
      [balance - value, owner] [owner, balance - value] :=
    Stack.swapCore_zero
  have hp2 : owner :: (balance - value) :: [] <<+ s2.stack :=
    Stack.prefix_of_swap hswap_core (of_run_swap hswap) hp1
  rcases Line.of_run_cons run2 with ⟨s3, hstore, hnil⟩
  cases hnil
  have hset :
      Devm.getStor r e.currentTarget =
        (Devm.getStor s2 e.currentTarget).set owner (balance - value) :=
    sstore_getStor_set hstore hp2
  have hs_before : Devm.getStor s = Devm.getStor s2 := by
    rw [Line.of_inv Devm.getStor (by line_inv)
          (Line.Run.cons hsub Line.Run.nil),
      Line.of_inv Devm.getStor (by line_inv)
          (Line.Run.cons hswap Line.Run.nil)]
  have hkey : owner.toAdr.toB256 = owner := toB256_toAdr h_owner
  have hset' :
      Devm.getStor r e.currentTarget =
        (Devm.getStor s2 e.currentTarget).set owner.toAdr.toB256
          (balance - value) := by
    simpa only [hkey] using hset
  constructor
  · intro a
    constructor
    · intro h_eq
      subst h_eq
      simp only [Stor.rest, Function.comp_apply]
      rw [hset', Stor.get_set_self, hkey, ← h_balance]
    · intro h_ne
      simp only [Stor.rest, Function.comp_apply]
      rw [hset',
        Stor.get_set_ne _ (fun hc => h_ne (Adr.toB256_inj hc)) _,
        ← congrFun hs_before e.currentTarget]
  · constructor
    · simp only [Stor.rest, Function.comp_apply]
      rw [hkey, ← h_balance]
      exact h_le
    · have h_flash_ne : owner.toAdr.toB256 ≠ flashMintedSlot := by
        simpa only [balanceKey] using
          balanceKey_ne_flashMintedSlot owner.toAdr
      rw [hset', Stor.get_set_ne _ h_flash_ne _,
        ← congrFun hs_before e.currentTarget]

/-- The exact unchecked recipient-credit fragment exposes the normalized
recipient, increases that address balance, and leaves the disjoint flash
counter unchanged. -/
theorem creditAddressArg_storage_at (owner amount : B256)
    {e : Sevm} {s r : Devm}
    (run : Line.Run e s
      (addressArg owner ++ [dup 0, sload] ++ arg amount ++
        [add, swap 0, sstore]) r) :
    ∃ recipient : Adr,
      recipient.toB256 = (~~~ addressMask) &&& Sevm.argWord e owner ∧
      Increase recipient (Sevm.argWord e amount)
        (Stor.rest (Devm.getStor s e.currentTarget))
        (Stor.rest (Devm.getStor r e.currentTarget)) ∧
      (Devm.getStor r e.currentTarget).get flashMintedSlot =
        (Devm.getStor s e.currentTarget).get flashMintedSlot := by
  rcases of_run_append (addressArg owner) run with
    ⟨s1, harg, run1⟩
  let key := (~~~ addressMask) &&& Sevm.argWord e owner
  have hp1 : key :: [] <<+ s1.stack :=
    prefix_of_addressArg nil_pref harg
  have hvalid : ValidAdr key :=
    normalizedAddress_valid (Sevm.argWord e owner)
  rcases of_run_append [dup 0] run1 with
    ⟨s2, hdupLine, run2⟩
  rcases Line.of_run_cons hdupLine with ⟨s2', hdup, hnil2⟩
  cases hnil2
  have hp2 : key :: key :: [] <<+ s2.stack :=
    prefix_of_dup_val hdup (by show_nth) hp1
  rcases of_run_append [sload] run2 with
    ⟨s3, hloadLine, run3⟩
  rcases Line.of_run_cons hloadLine with ⟨s3', hload, hnil3⟩
  cases hnil3
  rcases prefix_of_sload hload hp2 with ⟨toBal, hp3, htoBal⟩
  rcases of_run_append (arg amount) run3 with
    ⟨s4, hamount, run4⟩
  have hp4 : Sevm.argWord e amount :: toBal :: key :: [] <<+ s4.stack :=
    prefix_of_arg hp3 hamount
  rcases Line.of_run_cons run4 with ⟨s5, hadd, run5⟩
  have hp5 : (Sevm.argWord e amount + toBal) :: key :: [] <<+
      s5.stack := prefix_of_add hadd hp4
  rcases Line.of_run_cons run5 with ⟨s6, hswap, run6⟩
  have hswapCore : Stack.Swap (0 : Fin 16).val
      [Sevm.argWord e amount + toBal, key]
      [key, Sevm.argWord e amount + toBal] :=
    Stack.swapCore_zero
  have hp6 : key :: (Sevm.argWord e amount + toBal) :: [] <<+ s6.stack :=
    Stack.prefix_of_swap hswapCore (of_run_swap hswap) hp5
  rcases Line.of_run_cons run6 with ⟨s7, hstore, hnil7⟩
  cases hnil7
  have hset :
      Devm.getStor r e.currentTarget =
        (Devm.getStor s6 e.currentTarget).set key
          (Sevm.argWord e amount + toBal) :=
    sstore_getStor_set hstore hp6
  have hs_start_s2 : Devm.getStor s = Devm.getStor s2 := by
    rw [Line.of_inv Devm.getStor (by line_inv) harg,
      Line.of_inv Devm.getStor (by line_inv) hdupLine]
  have hs_s2_s6 : Devm.getStor s2 = Devm.getStor s6 := by
    rw [Line.of_inv Devm.getStor (by line_inv) hloadLine,
      Line.of_inv Devm.getStor (by line_inv) hamount,
      Line.of_inv Devm.getStor (by line_inv)
        (Line.Run.cons hadd Line.Run.nil),
      Line.of_inv Devm.getStor (by line_inv)
        (Line.Run.cons hswap Line.Run.nil)]
  have hs_before : Devm.getStor s = Devm.getStor s6 :=
    hs_start_s2.trans hs_s2_s6
  change toBal = (Devm.getStor s2 e.currentTarget).get key at htoBal
  have htoBal0 :
      toBal = (Devm.getStor s e.currentTarget).get key := by
    rw [htoBal, congrFun hs_start_s2 e.currentTarget]
  have hkey : key.toAdr.toB256 = key := toB256_toAdr hvalid
  have hset' :
      Devm.getStor r e.currentTarget =
        (Devm.getStor s6 e.currentTarget).set key.toAdr.toB256
          (Sevm.argWord e amount + toBal) := by
    simpa only [hkey] using hset
  refine ⟨key.toAdr, ?_, ?_, ?_⟩
  · exact hkey
  · intro a
    constructor
    · intro h_eq
      subst h_eq
      simp only [Stor.rest, Function.comp_apply]
      rw [hset', Stor.get_set_self, hkey, ← htoBal0, B256.add_comm]
    · intro h_ne
      simp only [Stor.rest, Function.comp_apply]
      rw [hset',
        Stor.get_set_ne _ (fun hc => h_ne (Adr.toB256_inj hc)) _,
        ← congrFun hs_before e.currentTarget]
  · have h_flash_ne : key.toAdr.toB256 ≠ flashMintedSlot := by
      simpa only [balanceKey] using
        balanceKey_ne_flashMintedSlot key.toAdr
    rw [hset', Stor.get_set_ne _ h_flash_ne _,
      ← congrFun hs_before e.currentTarget]

/-- Compatibility projection retaining the original storage-only API. -/
theorem creditAddressArg_storage (owner amount : B256)
    {e : Sevm} {s r : Devm}
    (run : Line.Run e s
      (addressArg owner ++ [dup 0, sload] ++ arg amount ++
        [add, swap 0, sstore]) r) :
    ∃ recipient : Adr,
      Increase recipient (Sevm.argWord e amount)
        (Stor.rest (Devm.getStor s e.currentTarget))
        (Stor.rest (Devm.getStor r e.currentTarget)) ∧
      (Devm.getStor r e.currentTarget).get flashMintedSlot =
        (Devm.getStor s e.currentTarget).get flashMintedSlot := by
  rcases creditAddressArg_storage_at owner amount run with
    ⟨recipient, _, hinc, hflash⟩
  exact ⟨recipient, hinc, hflash⟩

/-- The exact nonzero-word transfer branch establishes a fresh backed pre-state
at its continuation boundary.  The normalized recipient may itself be zero
when the raw ABI word is dirty. -/
theorem backedPre_of_transferNonzeroThen (dp : DeployParams) (ca : Adr)
    {sevm : Sevm} {s r : Devm} {next : Func}
    (h_target : sevm.currentTarget = ca)
    (h_pre : (backedSpec weth10 dp).Pre ca sevm s)
    (h_value : sevm.value = 0)
    (run : Func.Run ((weth10 dp).main :: weth10Aux) sevm s
      (transferNonzeroThen next) r) :
    ∃ snext,
      (backedSpec weth10 dp).Pre ca sevm snext ∧
      Func.Run ((weth10 dp).main :: weth10Aux) sevm snext next r := by
  subst ca
  have h_inv0 := h_pre.inv.1 rfl
  change Stor.Weth10Inv
    (Devm.getStor s sevm.currentTarget) sevm.value
    (Devm.getBal s sevm.currentTarget) at h_inv0
  rw [h_value] at h_inv0
  simp only [transferNonzeroThen] at run
  rcases of_run_prepend (loadCallerBalanceAmount 1) _ run with
    ⟨s1, hload, run1⟩
  rcases prefix_of_loadCallerBalanceAmount nil_pref hload with
    ⟨balance, h_balance, hp1⟩
  rcases of_run_prepend balanceTooSmall _ run1 with
    ⟨s2, hguard, run2⟩
  have hp2 :
      (balance <? Sevm.argWord sevm 1) :: balance ::
        Sevm.argWord sevm 1 :: sevm.caller.toB256 :: [] <<+ s2.stack :=
    prefix_of_balanceTooSmall hp1 hguard
  have h_error_lookup :
      ((weth10 dp).main :: weth10Aux)[transferBalanceErrorSlot]? =
        some (Func.revWith "WETH: transfer amount exceeds balance") := by
    simp [weth10, weth10Aux, transferBalanceErrorSlot,
      transferBalanceError]
  rcases of_run_branch_call_revWith h_error_lookup run2 with
    ⟨s3, hpopGuard, run3⟩
  have hpopStack := hpopGuard.stack
  simp only [Stack.Pop, Split, List.nil_append, List.cons_append] at hpopStack
  rw [hpopStack] at hp2
  have h_flag : (balance <? Sevm.argWord sevm 1) = 0 :=
    pref_head_unique hp2 (pref_append [0] s3.stack)
  have h_token_le : Sevm.argWord sevm 1 ≤ balance := by
    rw [← B256.not_lt]
    intro hlt
    rw [B256.ltCheck, if_pos hlt] at h_flag
    exact B256.zero_ne_one h_flag.symm
  rw [h_flag] at hp2
  have hp3 :
      [balance, Sevm.argWord sevm 1, sevm.caller.toB256] <<+ s3.stack :=
    cons_pref_cons_inv hp2
  have h_stor_s_s3 : Devm.getStor s = Devm.getStor s3 :=
    (Line.of_inv Devm.getStor (by line_inv) hload).trans
      ((Line.of_inv Devm.getStor (by line_inv) hguard).trans
        (PopBurn.Inv.inv hpopGuard))
  have h_bal_s_s3 : Devm.getBal s = Devm.getBal s3 :=
    (Line.of_inv Devm.getBal (by line_inv) hload).trans
      ((Line.of_inv Devm.getBal (by line_inv) hguard).trans
        (PopBurn.Inv.inv hpopGuard))
  have h_code_s_s3 :
      Devm.getCode s sevm.currentTarget =
        Devm.getCode s3 sevm.currentTarget :=
    (congrFun (Line.of_inv Devm.getCode (by line_inv) hload)
        sevm.currentTarget).trans
      ((congrFun (Line.of_inv Devm.getCode (by line_inv) hguard)
          sevm.currentTarget).trans
        (getCode_eq_of_state_eq hpopGuard.state sevm.currentTarget))
  have h_inv3 : Stor.Weth10Inv
      (Devm.getStor s3 sevm.currentTarget) 0
      (Devm.getBal s3 sevm.currentTarget) := by
    rw [← congrFun h_stor_s_s3 sevm.currentTarget,
      ← congrFun h_bal_s_s3 sevm.currentTarget]
    exact h_inv0
  have h_balance3 :
      balance =
        (Devm.getStor s3 sevm.currentTarget).get sevm.caller.toB256 := by
    rw [h_balance, congrFun h_stor_s_s3 sevm.currentTarget]
  rcases of_run_prepend debitLoadedBalance _ run3 with
    ⟨s4, hdebit, run4⟩
  obtain ⟨h_dec, h_cover, h_flash_debit⟩ :=
    debitLoadedBalance_storage (validAdr_toB256 sevm.caller)
      h_balance3 h_token_le hp3 hdebit
  let creditLine : Line :=
    addressArg 0 ++ [dup 0, sload] ++ arg 1 ++ [add, swap 0, sstore]
  rcases of_run_prepend creditLine _ run4 with
    ⟨s5, hcredit, run5⟩
  obtain ⟨recipient, h_inc, h_flash_credit⟩ :=
    creditAddressArg_storage 0 1 (by
      simpa only [creditLine] using hcredit)
  have h_transfer : Transfer
      (Stor.rest (Devm.getStor s3 sevm.currentTarget))
      sevm.caller.toB256.toAdr (Sevm.argWord sevm 1) recipient
      (Stor.rest (Devm.getStor s5 sevm.currentTarget)) :=
    ⟨h_cover, Stor.rest (Devm.getStor s4 sevm.currentTarget),
      h_dec, h_inc⟩
  have h_flash :
      (Devm.getStor s5 sevm.currentTarget).get flashMintedSlot =
        (Devm.getStor s3 sevm.currentTarget).get flashMintedSlot :=
    h_flash_credit.trans h_flash_debit
  have h_inv5 : Stor.Weth10Inv
      (Devm.getStor s5 sevm.currentTarget) 0
      (Devm.getBal s3 sevm.currentTarget) :=
    Stor.Weth10Inv.transfer h_inv3 h_transfer h_flash
  let logLine : Line :=
    [caller] ++ arg 1 ++ addressArg 0 ++ emitTransfer
  rcases of_run_prepend logLine next run5 with
    ⟨s6, hlog, hnext⟩
  have h_stor_s5_s6 : Devm.getStor s5 = Devm.getStor s6 :=
    Line.of_inv Devm.getStor (by line_inv) hlog
  have h_bal_s3_s6 : Devm.getBal s3 = Devm.getBal s6 :=
    (Line.of_inv Devm.getBal (by line_inv) hdebit).trans
      ((Line.of_inv Devm.getBal (by line_inv) hcredit).trans
        (Line.of_inv Devm.getBal (by line_inv) hlog))
  have h_code_s3_s6 :
      Devm.getCode s3 sevm.currentTarget =
        Devm.getCode s6 sevm.currentTarget :=
    (congrFun (Line.of_inv Devm.getCode (by line_inv) hdebit)
        sevm.currentTarget).trans
      ((congrFun (Line.of_inv Devm.getCode (by line_inv) hcredit)
          sevm.currentTarget).trans
        (congrFun (Line.of_inv Devm.getCode (by line_inv) hlog)
          sevm.currentTarget))
  refine ⟨s6, ?_, hnext⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← h_code_s3_s6, ← h_code_s_s3]
    exact h_pre.code
  · rw [← h_bal_s3_s6, ← h_bal_s_s3]
    exact h_pre.side
  · intro _
    change Stor.Weth10Inv
      (Devm.getStor s6 sevm.currentTarget) sevm.value
      (Devm.getBal s6 sevm.currentTarget)
    rw [h_value, ← congrFun h_stor_s5_s6 sevm.currentTarget,
      ← congrFun h_bal_s3_s6 sevm.currentTarget]
    exact h_inv5
  · intro hne
    exact (hne rfl).elim

/-- The exact nonzero-word `transfer` branch preserves backing. -/
theorem backedPost_of_transferNonzero (dp : DeployParams) (ca : Adr)
    {sevm : Sevm} {s r : Devm}
    (h_target : sevm.currentTarget = ca)
    (h_pre : (backedSpec weth10 dp).Pre ca sevm s)
    (h_value : sevm.value = 0)
    (run : Func.Run ((weth10 dp).main :: weth10Aux) sevm s
      (transferNonzeroThen returnTrue) r) :
    (backedSpec weth10 dp).Post ca sevm r := by
  obtain ⟨snext, h_pre_next, hreturn⟩ :=
    backedPre_of_transferNonzeroThen dp ca
      h_target h_pre h_value run
  refine ⟨Func.preserves_nof hreturn h_pre_next.side, ?_⟩
  have h_stor : Devm.getStor snext = Devm.getStor r :=
    Func.of_inv Devm.getStor Devm.getStor (by func_inv) hreturn
  have h_bal : Devm.getBal snext = Devm.getBal r :=
    Func.of_inv Devm.getBal Devm.getBal (by func_inv) hreturn
  change Stor.Weth10Inv (Devm.getStor r ca) 0 (Devm.getBal r ca)
  rw [← congrFun h_stor ca, ← congrFun h_bal ca]
  have h := h_pre_next.inv.1 h_target
  change Stor.Weth10Inv
    (Devm.getStor snext ca) sevm.value (Devm.getBal snext ca) at h
  rw [h_value] at h
  exact h

/-- Child-frame entry after a synchronized WETH burn and ETH transfer from
the contract.  This is the value-call seam the contract-neutral ladder cannot
provide: its ordinary transfer lemma deliberately assumes that the contract
is not the debited sender. -/
theorem backedPre_of_withdraw_transfer (dp : DeployParams)
    {ca target : Adr} {sevm' : Sevm} {devm' : Devm}
    {st st_mid : Jaune.State} {value : B256}
    (h_code : some (st.getCode ca).toList = Prog.compile (weth10 dp))
    (h_side : SumNof st.bal)
    (h_inv : Stor.Weth10Inv (st.getStor ca) 0 (st.bal ca - value))
    (h_sub : st.subBal ca value = some st_mid)
    (h_state : devm'.state = st_mid.addBal target value)
    (h_ct : sevm'.currentTarget = target)
    (h_value : sevm'.value = value) :
    (backedSpec weth10 dp).Pre ca sevm' devm' := by
  rcases of_state_transfer_fields (callee := target) h_sub with
    ⟨h_t_stor, h_t_code, h_le, h_t_self, h_t_ne⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · show some (devm'.state.get ca).code.toList =
      Prog.compile (weth10 dp)
    rw [h_state, h_t_code ca]
    exact h_code
  · show SumNof devm'.state.bal
    rw [h_state]
    exact (backedSpec weth10 dp).side_transfer h_sub h_side
  · intro h_target
    have h_target' : target = ca := h_ct.symm.trans h_target
    have hbal : ((st_mid.addBal target value).get ca).bal =
        (st.get ca).bal := h_t_self h_target'
    show Stor.Weth10Inv (Devm.getStor devm' ca) sevm'.value
      (Devm.getBal devm' ca)
    change Stor.Weth10Inv (devm'.state.get ca).stor sevm'.value
      (devm'.state.get ca).bal
    rw [h_state, h_value, h_t_stor ca, hbal]
    change Stor.Weth10Inv (st.get ca).stor 0
      ((st.get ca).bal - value) at h_inv
    change value ≤ (st.get ca).bal at h_le
    have h_le_nat := B256.toNat_le_toNat h_le
    unfold Stor.Weth10Inv at h_inv ⊢
    rw [B256.toNat_zero, Nat.add_zero,
      B256.toNat_sub_eq_of_le _ _ h_le] at h_inv
    omega
  · intro h_target
    have h_target' : target ≠ ca :=
      fun h => h_target (h_ct.trans h)
    have hbal : ((st_mid.addBal target value).get ca).bal =
        (st.get ca).bal - value := h_t_ne h_target'
    show Stor.Weth10Inv (Devm.getStor devm' ca) 0
      (Devm.getBal devm' ca)
    change Stor.Weth10Inv (devm'.state.get ca).stor 0
      (devm'.state.get ca).bal
    rw [h_state, h_t_stor ca, hbal]
    change Stor.Weth10Inv (st.get ca).stor 0
      ((st.get ca).bal - value) at h_inv
    exact h_inv

/-- A zero-length value `CALL` made after a synchronized token debit restores
the ordinary WETH10 postcondition.  The child may be a precompile, delegated
code, arbitrary bytecode, or a reentrant WETH10 frame; the last case is exactly
where `FuncSoundNoMem`'s deeper-frame hypothesis is consumed. -/
theorem backedPost_of_value_call
    (dp : DeployParams) (ca : Adr)
    {sevm : Sevm} {s sf : Devm} {g c v ii is oi os : B256}
    {xs : Stack}
    (h_target : sevm.currentTarget = ca)
    (ih : Exec.InvDepth sevm.depth ca (weth10 dp)
      ((backedSpec weth10 dp).PreWf ca) ((backedSpec weth10 dp).Post ca))
    (hp : (g :: c :: v :: ii :: is :: oi :: os :: xs) <<+ s.stack)
    (h_code : some (s.getCode ca).toList = Prog.compile (weth10 dp))
    (h_side : SumNof s.getBal)
    (h_le : v ≤ s.getBal ca)
    (h_inv : Stor.Weth10Inv (Devm.getStor s ca) 0
      (s.getBal ca - v))
    (h_run : Ninst.Run sevm s call sf) :
    (backedSpec weth10 dp).Post ca sevm sf := by
  rcases of_run_call_val_with_depth hp h_run with
    ⟨_, h_world⟩ |
      ⟨parent, child, xl, delegated, na, code, avail, h_depth,
        h_stack, h_parent_state, h_parent_memory, h_delegation,
        h_fill, h_pm, h_child_clean, h_resume, h_sf_state,
        h_returnData, h_memory, h_sf_stack⟩
  · refine ⟨?_, ?_⟩
    · show SumNof sf.getBal
      have hb : s.getBal = sf.getBal :=
        funext fun a => h_world.getBal a
      rw [← hb]
      exact h_side
    · change Stor.Weth10Inv (Devm.getStor sf ca) 0 (sf.getBal ca)
      have h_inv' :
          Stor.Weth10Inv (Devm.getStor s ca) 0 (s.getBal ca) := by
        exact (backedSpec weth10 dp).inv_mono h_inv (by
          rw [B256.toNat_sub_eq_of_le _ _ h_le]
          omega)
      rw [← h_world.getStor ca, ← h_world.getBal ca]
      exact h_inv'
  · let childMsg :=
      callMsg sevm parent
        (min g.toNat (except64th avail) +
          (if v.toNat = 0 then 0 else gCallStipend))
        v sevm.currentTarget c.toAdr na true false
        ((s.memory.read ii.toNat is.toNat).1) code delegated
    change ProcessMessage childMsg xl (.ok child) at h_pm
    have hc_state : childMsg.benv.state = s.state := by
      change parent.state = s.state
      exact h_parent_state
    have hc_stv : childMsg.shouldTransferValue = true := rfl
    have hc_caller : childMsg.caller = ca := by
      change sevm.currentTarget = ca
      exact h_target
    have hc_value : childMsg.value = v := rfl
    have hc_target : childMsg.currentTarget = c.toAdr := rfl
    have hc_codeAddress : childMsg.codeAddress = some na := rfl
    obtain ⟨r0, hbody, hset⟩ := ProcessMessage.iff_body.mp h_pm
    unfold FrameBody at hbody
    rcases h_bt : childMsg.benvAfterTransfer with e | benv <;>
      rw [h_bt] at hbody
    · rw [hbody.2, processMessage.settle_error] at hset
      cases hset
    have h_exec : ExecuteCode (childMsg.withBenv benv) xl r0 := hbody
    rcases of_benvAfterTransfer hc_stv h_bt with
      ⟨st_mid, h_sub, h_benv⟩
    rw [hc_state, hc_caller, hc_value] at h_sub
    have h_benv_state :
        benv.state = st_mid.addBal c.toAdr v := by
      rw [h_benv, hc_target, hc_value]
      rfl
    have h_pre : (backedSpec weth10 dp).Pre ca
        (initSevm (childMsg.withBenv benv))
        (initDevm (childMsg.withBenv benv)) := by
      apply backedPre_of_withdraw_transfer dp
        (st := s.state) (st_mid := st_mid)
        (target := c.toAdr) (value := v)
      · exact h_code
      · exact h_side
      · exact h_inv
      · exact h_sub
      · exact h_benv_state
      · exact hc_target
      · exact hc_value
    obtain ⟨evm2, h_r0, h_settle⟩ := processMessage.settle_ok_cases hset.symm
    subst h_r0
    rcases h_settle with ⟨h_err2, h_eq⟩ | ⟨h_err2, h_eq_child⟩
    · have : child.error.isSome = true := by
        rw [← h_eq]
        exact h_err2
      simp [h_child_clean] at this
    rw [h_eq_child] at h_exec h_err2
    have h_child_post : (backedSpec weth10 dp).Post ca
        (initSevm (childMsg.withBenv benv)) child := by
      have hc_codeAddress' :
          (childMsg.withBenv benv).codeAddress = some na :=
        hc_codeAddress
      rcases of_executeCode_someCode hc_codeAddress' h_exec with
        ⟨h_precompile, h_xl_none, h_handle⟩ |
        ⟨h_precompile, exn, h_xl_some, h_handle⟩
      · have h_child_state :
            child.state = (initDevm (childMsg.withBenv benv)).state := by
          have hstate := state_of_executePrecomp_ok h_handle h_err2
          exact hstate
        exact (backedSpec weth10 dp).post_of_pre
          (h_pre.state_eq h_child_state)
      · have h_exn : exn = .ok child :=
          exec_ok_of_handleError h_handle h_err2
        rw [h_xl_some, h_exn] at h_fill
        obtain ⟨h_exec_child⟩ := h_fill
        have h_at : Prog.At (weth10 dp) ca 0
            (initSevm (childMsg.withBenv benv))
            (initDevm (childMsg.withBenv benv)) := by
          refine ⟨h_pre.code, ?_⟩
          intro h_child_target
          refine ⟨?_, rfl⟩
          have h_to_ca : c.toAdr = ca :=
            hc_target.symm.trans h_child_target
          change some code.toList = Prog.compile (weth10 dp)
          rcases h_delegation with
            ⟨h_none, _, h_code_self, h_not_delegated⟩ |
            ⟨d, h_some, _, h_code_delegated, h_delegated⟩
          · rw [h_code_self, h_to_ca]
            exact h_code
          · exfalso
            have h_not : ¬ isValidDelegation (s.getCode ca) :=
              not_delegation_of_compile h_code
            apply h_not
            unfold getDelegatedCodeAddress at h_some
            split at h_some
            · rename_i h_valid
              rw [h_to_ca] at h_valid
              exact h_valid
            · cases h_some
        have h_depth_lt :
            (initSevm (childMsg.withBenv benv)).depth < sevm.depth := by
          change sevm.depth - 1 < sevm.depth
          omega
        exact ih 0
          (initSevm (childMsg.withBenv benv))
          (initDevm (childMsg.withBenv benv))
          (.ok child) h_exec_child h_depth_lt h_at
          ⟨h_pre, fun _ => Mem.wf_empty⟩
    refine ⟨?_, ?_⟩
    · show SumNof sf.getBal
      have h_bal : sf.getBal = child.getBal :=
        funext (getBal_eq_of_state_eq h_sf_state)
      rw [h_bal]
      exact h_child_post.side
    · change Stor.Weth10Inv (Devm.getStor sf ca) 0 (sf.getBal ca)
      have h_stor : Devm.getStor sf ca = Devm.getStor child ca :=
        getStor_eq_of_state_eq h_sf_state ca
      have h_bal : sf.getBal ca = child.getBal ca :=
        getBal_eq_of_state_eq h_sf_state ca
      rw [h_stor, h_bal]
      exact h_child_post.inv

/-- A `CALL` whose result is accepted by the runtime's `iszero`/reverting
guard necessarily passed the EVM balance guard. -/
theorem value_le_balance_of_run_call_success_guard
    {sevm : Sevm} {s sc si sb : Devm}
    {g c v ii is oi os : B256} {xs : Stack}
    (hp : (g :: c :: v :: ii :: is :: oi :: os :: xs) <<+ s.stack)
    (hcall : Ninst.Run sevm s call sc)
    (hiszero : Ninst.Run sevm sc iszero si)
    (hpop : Devm.PopBurn [0] si sb) :
    v ≤ s.getBal sevm.currentTarget := by
  rcases of_run_call_val_with_depth hp hcall with
    ⟨hp0, h_world⟩ |
      ⟨parent, child, xl, delegated, na, code, avail, h_depth,
        h_stack, h_parent_state, h_parent_memory, h_delegation,
        h_fill, h_pm, h_child_clean, h_resume, h_sc_state,
        h_returnData, h_memory, h_sc_stack⟩
  · have hp1 : ((0 : B256) =? 0) :: xs <<+ si.stack :=
      prefix_of_iszero hiszero hp0
    have hpop_stack := hpop.stack
    simp only [Stack.Pop, Split, List.nil_append, List.cons_append] at hpop_stack
    rw [hpop_stack] at hp1
    have hbad : ((0 : B256) =? 0) = 0 :=
      pref_head_unique hp1 (pref_append [0] sb.stack)
    exact (B256.zero_ne_one hbad.symm).elim
  · let childMsg :=
      callMsg sevm parent
        (min g.toNat (except64th avail) +
          (if v.toNat = 0 then 0 else gCallStipend))
        v sevm.currentTarget c.toAdr na true false
        ((s.memory.read ii.toNat is.toNat).1) code delegated
    change ProcessMessage childMsg xl (.ok child) at h_pm
    obtain ⟨r0, hbody, hset⟩ := ProcessMessage.iff_body.mp h_pm
    unfold FrameBody at hbody
    rcases h_bt : childMsg.benvAfterTransfer with e | benv <;>
      rw [h_bt] at hbody
    · rw [hbody.2, processMessage.settle_error] at hset
      cases hset
    rcases of_benvAfterTransfer
        (show childMsg.shouldTransferValue = true from rfl) h_bt with
      ⟨st_mid, h_sub, h_benv⟩
    change parent.state.subBal sevm.currentTarget v = some st_mid at h_sub
    rw [h_parent_state] at h_sub
    exact (of_state_transfer_fields (callee := c.toAdr) h_sub).2.2.1

/-- The exact caller-value sender up to its final `CALL`, with the seven CALL
operands and the unchanged parent world state exposed. -/
theorem of_sendValueToCaller
    {e : Sevm} {s r : Devm} {value : B256} {xs : Stack}
    (hp : value :: xs <<+ s.stack)
    (run : Line.Run e s sendValueToCaller r) :
    ∃ sc g,
      (g :: e.caller.toB256 :: value :: 0 :: 0 :: 0 :: 0 :: xs) <<+
        sc.stack ∧
      Ninst.Run e sc call r ∧
      Devm.getStor s = Devm.getStor sc ∧
      s.getBal = sc.getBal ∧
      s.getCode = sc.getCode := by
  unfold sendValueToCaller at run
  let pre : Line := pushList [0, 0, 0, 0] ++ [swap 3, caller, gas]
  rcases of_run_append pre run with ⟨sc, hpre, hrest⟩
  rcases Line.of_run_cons hrest with ⟨r', hcall, hnil⟩
  cases hnil
  unfold pre pushList at hpre
  simp only [List.map] at hpre
  rcases Line.of_run_cons hpre with ⟨s1, hpush1, hpre1⟩
  have hp1 : (0 : B256) :: value :: xs <<+ s1.stack :=
    prefix_of_push (of_run_pushB256 hpush1) hp
  rcases Line.of_run_cons hpre1 with ⟨s2, hpush2, hpre2⟩
  have hp2 : (0 : B256) :: 0 :: value :: xs <<+ s2.stack :=
    prefix_of_push (of_run_pushB256 hpush2) hp1
  rcases Line.of_run_cons hpre2 with ⟨s3, hpush3, hpre3⟩
  have hp3 : (0 : B256) :: 0 :: 0 :: value :: xs <<+ s3.stack :=
    prefix_of_push (of_run_pushB256 hpush3) hp2
  rcases Line.of_run_cons hpre3 with ⟨s4, hpush4, hpre4⟩
  have hp4 : (0 : B256) :: 0 :: 0 :: 0 :: value :: xs <<+ s4.stack :=
    prefix_of_push (of_run_pushB256 hpush4) hp3
  rcases Line.of_run_cons hpre4 with ⟨s5, hswap, hpre5⟩
  have hswap_core : Stack.Swap (3 : Fin 16).val
      ((0 : B256) :: 0 :: 0 :: 0 :: value :: xs)
      (value :: 0 :: 0 :: 0 :: 0 :: xs) :=
    Stack.swapCore_succ
      (Stack.swapCore_succ
        (Stack.swapCore_succ Stack.swapCore_zero))
  have hp5 : value :: 0 :: 0 :: 0 :: 0 :: xs <<+ s5.stack :=
    Stack.prefix_of_swap hswap_core (of_run_swap hswap) hp4
  rcases Line.of_run_cons hpre5 with ⟨s6, hcaller, hpre6⟩
  have hp6 : e.caller.toB256 :: value :: 0 :: 0 :: 0 :: 0 :: xs <<+
      s6.stack := prefix_of_push (of_run_caller hcaller) hp5
  rcases Line.of_run_cons hpre6 with ⟨s7, hgas, hnil⟩
  cases hnil
  rcases of_run_gas hgas with ⟨g, hpushGas⟩
  have hp7 :
      g :: e.caller.toB256 :: value :: 0 :: 0 :: 0 :: 0 :: xs <<+
        sc.stack := prefix_of_push hpushGas hp6
  exact ⟨sc, g, hp7, hcall,
    Line.of_inv Devm.getStor (by line_inv) hpre,
    Line.of_inv Devm.getBal (by line_inv) hpre,
    Line.of_inv Devm.getCode (by line_inv) hpre⟩

/-- The exact address-argument value sender up to its final `CALL`, with the
seven CALL operands and unchanged parent world state exposed.  Dirty ABI words
are passed intact to `CALL`; EVM address conversion occurs at the call seam. -/
theorem of_sendValueToArg (k : B256)
    {e : Sevm} {s r : Devm} {value : B256} {xs : Stack}
    (hp : value :: xs <<+ s.stack)
    (run : Line.Run e s (sendValueToArg k) r) :
    ∃ sc g,
      (g :: Sevm.argWord e k :: value :: 0 :: 0 :: 0 :: 0 :: xs) <<+
        sc.stack ∧
      Ninst.Run e sc call r ∧
      Devm.getStor s = Devm.getStor sc ∧
      s.getBal = sc.getBal ∧
      s.getCode = sc.getCode := by
  unfold sendValueToArg at run
  let pre : Line :=
    pushList [0, 0, 0, 0] ++ [swap 3] ++ arg k ++ [gas]
  rcases of_run_append pre run with ⟨sc, hpre, hrest⟩
  rcases Line.of_run_cons hrest with ⟨r', hcall, hnil⟩
  cases hnil
  unfold pre pushList at hpre
  simp only [List.map] at hpre
  rcases Line.of_run_cons hpre with ⟨s1, hpush1, hpre1⟩
  have hp1 : (0 : B256) :: value :: xs <<+ s1.stack :=
    prefix_of_push (of_run_pushB256 hpush1) hp
  rcases Line.of_run_cons hpre1 with ⟨s2, hpush2, hpre2⟩
  have hp2 : (0 : B256) :: 0 :: value :: xs <<+ s2.stack :=
    prefix_of_push (of_run_pushB256 hpush2) hp1
  rcases Line.of_run_cons hpre2 with ⟨s3, hpush3, hpre3⟩
  have hp3 : (0 : B256) :: 0 :: 0 :: value :: xs <<+ s3.stack :=
    prefix_of_push (of_run_pushB256 hpush3) hp2
  rcases Line.of_run_cons hpre3 with ⟨s4, hpush4, hpre4⟩
  have hp4 : (0 : B256) :: 0 :: 0 :: 0 :: value :: xs <<+ s4.stack :=
    prefix_of_push (of_run_pushB256 hpush4) hp3
  rcases Line.of_run_cons hpre4 with ⟨s5, hswap, hpre5⟩
  have hswap_core : Stack.Swap (3 : Fin 16).val
      ((0 : B256) :: 0 :: 0 :: 0 :: value :: xs)
      (value :: 0 :: 0 :: 0 :: 0 :: xs) :=
    Stack.swapCore_succ
      (Stack.swapCore_succ
        (Stack.swapCore_succ Stack.swapCore_zero))
  have hp5 : value :: 0 :: 0 :: 0 :: 0 :: xs <<+ s5.stack :=
    Stack.prefix_of_swap hswap_core (of_run_swap hswap) hp4
  rcases of_run_append (arg k) hpre5 with ⟨s6, harg, hpre6⟩
  have hp6 : Sevm.argWord e k :: value :: 0 :: 0 :: 0 :: 0 :: xs <<+
      s6.stack := prefix_of_arg hp5 harg
  rcases Line.of_run_cons hpre6 with ⟨s7, hgas, hnil7⟩
  cases hnil7
  rcases of_run_gas hgas with ⟨g, hpushGas⟩
  have hp7 :
      g :: Sevm.argWord e k :: value :: 0 :: 0 :: 0 :: 0 :: xs <<+
        sc.stack := prefix_of_push hpushGas hp6
  exact ⟨sc, g, hp7, hcall,
    Line.of_inv Devm.getStor (by line_inv) hpre,
    Line.of_inv Devm.getBal (by line_inv) hpre,
    Line.of_inv Devm.getCode (by line_inv) hpre⟩

/-- The exact burn event fragment consumes the event source and leaves the
selected calldata amount ready for the value call. -/
theorem prefix_of_burnEvent (k : B256)
    {e : Sevm} {s r : Devm} {xs : Stack}
    (hp : xs <<+ s.stack)
    (run : Line.Run e s
      ([caller] ++ arg k ++ [pushB256 0] ++ emitTransfer ++
        [swap 0, pop]) r) :
    Sevm.argWord e k :: xs <<+ r.stack := by
  rcases of_run_append [caller] run with ⟨s1, hcallerLine, run1⟩
  rcases Line.of_run_cons hcallerLine with ⟨s1', hcaller, hnil1⟩
  cases hnil1
  have hp1 : e.caller.toB256 :: xs <<+ s1.stack :=
    prefix_of_push (of_run_caller hcaller) hp
  rcases of_run_append (arg k) run1 with ⟨s2, harg, run2⟩
  have hp2 : Sevm.argWord e k :: e.caller.toB256 :: xs <<+ s2.stack :=
    prefix_of_arg hp1 harg
  rcases of_run_append [pushB256 0] run2 with ⟨s3, hpushLine, run3⟩
  rcases Line.of_run_cons hpushLine with ⟨s3', hpush, hnil3⟩
  cases hnil3
  have hp3 : (0 : B256) :: Sevm.argWord e k :: e.caller.toB256 :: xs <<+
      s3.stack := prefix_of_push (of_run_pushB256 hpush) hp2
  rcases of_run_append emitTransfer run3 with ⟨s4, hlog, run4⟩
  have hp4 : Sevm.argWord e k :: e.caller.toB256 :: xs <<+
      s4.stack := by
    clear hp run hcallerLine hp1 run1 harg hp2 run2 hpushLine hpush run3 run4
    unfold emitTransfer Blanc.transferFromLog at hlog
    generalize_line_prefix
  rcases Line.of_run_cons run4 with ⟨s5, hswap, run5⟩
  have hswap_core : Stack.Swap (0 : Fin 16).val
      (Sevm.argWord e k :: e.caller.toB256 :: xs)
      (e.caller.toB256 :: Sevm.argWord e k :: xs) :=
    Stack.swapCore_zero
  have hp5 : e.caller.toB256 :: Sevm.argWord e k :: xs <<+ s5.stack :=
    Stack.prefix_of_swap hswap_core (of_run_swap hswap) hp4
  rcases Line.of_run_cons run5 with ⟨s6, hpop, hnil6⟩
  cases hnil6
  exact prefix_of_pop (of_run_pop hpop) hp5

/-- The arbitrary-owner burn event consumes the normalized source and leaves
the selected calldata amount ready for the following value call. -/
theorem prefix_of_burnEventFromArg (owner amount : B256)
    {e : Sevm} {s r : Devm} {xs : Stack}
    (hp : xs <<+ s.stack)
    (run : Line.Run e s
      (addressArg owner ++ arg amount ++ [pushB256 0] ++ emitTransfer ++
        [swap 0, pop]) r) :
    Sevm.argWord e amount :: xs <<+ r.stack := by
  rcases of_run_append (addressArg owner) run with
    ⟨s1, howner, run1⟩
  have hp1 :
      ((~~~ addressMask) &&& Sevm.argWord e owner) :: xs <<+ s1.stack :=
    prefix_of_addressArg hp howner
  rcases of_run_append (arg amount) run1 with
    ⟨s2, hamount, run2⟩
  have hp2 :
      Sevm.argWord e amount ::
        ((~~~ addressMask) &&& Sevm.argWord e owner) :: xs <<+ s2.stack :=
    prefix_of_arg hp1 hamount
  rcases of_run_append [pushB256 0] run2 with
    ⟨s3, hpushLine, run3⟩
  rcases Line.of_run_cons hpushLine with
    ⟨s3', hpush, hnil3⟩
  cases hnil3
  have hp3 :
      (0 : B256) :: Sevm.argWord e amount ::
        ((~~~ addressMask) &&& Sevm.argWord e owner) :: xs <<+ s3.stack :=
    prefix_of_push (of_run_pushB256 hpush) hp2
  rcases of_run_append emitTransfer run3 with
    ⟨s4, hlog, run4⟩
  have hp4 :
      Sevm.argWord e amount ::
        ((~~~ addressMask) &&& Sevm.argWord e owner) :: xs <<+ s4.stack := by
    clear hp run howner hp1 run1 hamount hp2 run2 hpushLine hpush run3 run4
    unfold emitTransfer Blanc.transferFromLog at hlog
    generalize_line_prefix
  rcases Line.of_run_cons run4 with
    ⟨s5, hswap, run5⟩
  have hswapCore : Stack.Swap (0 : Fin 16).val
      (Sevm.argWord e amount ::
        ((~~~ addressMask) &&& Sevm.argWord e owner) :: xs)
      (((~~~ addressMask) &&& Sevm.argWord e owner) ::
        Sevm.argWord e amount :: xs) :=
    Stack.swapCore_zero
  have hp5 :
      ((~~~ addressMask) &&& Sevm.argWord e owner) ::
        Sevm.argWord e amount :: xs <<+ s5.stack :=
    Stack.prefix_of_swap hswapCore (of_run_swap hswap) hp4
  rcases Line.of_run_cons run5 with
    ⟨s6, hpop, hnil6⟩
  cases hnil6
  exact prefix_of_pop (of_run_pop hpop) hp5

/-- The `withdraw` specialization of `prefix_of_burnEvent`. -/
theorem prefix_of_withdrawEvent
    {e : Sevm} {s r : Devm} {xs : Stack}
    (hp : xs <<+ s.stack)
    (run : Line.Run e s
      ([caller] ++ arg 0 ++ [pushB256 0] ++ emitTransfer ++
        [swap 0, pop]) r) :
    Sevm.argWord e 0 :: xs <<+ r.stack :=
  prefix_of_burnEvent 0 hp run

private theorem code_eq_of_ninst_run
    {sevm : Sevm} {s r : Devm} {n : Ninst} {a : Adr}
    (hcode : (s.getCode a).toList ≠ [])
    (run : Ninst.Run sevm s n r) :
    r.getCode a = s.getCode a := by
  exact (Ninst.effect_of_effectRec codePreserve_refl_trans.1
    codePreserve_refl_trans.2 Ninst.codePreserve_effectRec
    Jinst.codePreserve_effect Linst.codePreserve_effect n run) a hcode

/-- The exact zero-recipient transfer branch burns caller tokens, accepts only
a successful ETH value call, and establishes a fresh backed pre-state at its
continuation boundary. -/
theorem backedPre_of_transferZeroThen (dp : DeployParams) (ca : Adr)
    {sevm : Sevm} {s r : Devm} {next : Func}
    (h_target : sevm.currentTarget = ca)
    (h_pre : (backedSpec weth10 dp).Pre ca sevm s)
    (ih : Exec.InvDepth sevm.depth ca (weth10 dp)
      ((backedSpec weth10 dp).PreWf ca) ((backedSpec weth10 dp).Post ca))
    (h_value : sevm.value = 0)
    (run : Func.Run ((weth10 dp).main :: weth10Aux) sevm s
      (transferZeroThen next) r) :
    ∃ snext,
      (backedSpec weth10 dp).Pre ca sevm snext ∧
      Func.Run ((weth10 dp).main :: weth10Aux) sevm snext next r := by
  subst ca
  simp only [transferZeroThen] at run
  rcases of_run_prepend (loadCallerBalanceAmount 1) _ run with
    ⟨s1, hload, run1⟩
  rcases prefix_of_loadCallerBalanceAmount nil_pref hload with
    ⟨balance, h_balance, hp1⟩
  rcases of_run_prepend balanceTooSmall _ run1 with
    ⟨s2, hguard, run2⟩
  have hp2 :
      (balance <? Sevm.argWord sevm 1) :: balance ::
        Sevm.argWord sevm 1 :: sevm.caller.toB256 :: [] <<+ s2.stack :=
    prefix_of_balanceTooSmall hp1 hguard
  have h_burn_lookup :
      ((weth10 dp).main :: weth10Aux)[burnBalanceErrorSlot]? =
        some (Func.revWith "WETH: burn amount exceeds balance") := by
    simp [weth10, weth10Aux, burnBalanceErrorSlot, burnBalanceError]
  rcases of_run_branch_call_revWith h_burn_lookup run2 with
    ⟨s3, hpopGuard, run3⟩
  have hpopStack := hpopGuard.stack
  simp only [Stack.Pop, Split, List.nil_append, List.cons_append] at hpopStack
  rw [hpopStack] at hp2
  have h_flag : (balance <? Sevm.argWord sevm 1) = 0 :=
    pref_head_unique hp2 (pref_append [0] s3.stack)
  have h_token_le : Sevm.argWord sevm 1 ≤ balance := by
    rw [← B256.not_lt]
    intro hlt
    rw [B256.ltCheck, if_pos hlt] at h_flag
    exact B256.zero_ne_one h_flag.symm
  rw [h_flag] at hp2
  have hp3 :
      [balance, Sevm.argWord sevm 1, sevm.caller.toB256] <<+ s3.stack :=
    cons_pref_cons_inv hp2
  have h_stor_s_s3 : Devm.getStor s = Devm.getStor s3 :=
    (Line.of_inv Devm.getStor (by line_inv) hload).trans
      ((Line.of_inv Devm.getStor (by line_inv) hguard).trans
        (PopBurn.Inv.inv hpopGuard))
  have h_bal_s_s3 : Devm.getBal s = Devm.getBal s3 :=
    (Line.of_inv Devm.getBal (by line_inv) hload).trans
      ((Line.of_inv Devm.getBal (by line_inv) hguard).trans
        (PopBurn.Inv.inv hpopGuard))
  have h_code_s_s3 :
      Devm.getCode s sevm.currentTarget =
        Devm.getCode s3 sevm.currentTarget :=
    (congrFun (Line.of_inv Devm.getCode (by line_inv) hload)
        sevm.currentTarget).trans
      ((congrFun (Line.of_inv Devm.getCode (by line_inv) hguard)
          sevm.currentTarget).trans
        (getCode_eq_of_state_eq hpopGuard.state sevm.currentTarget))
  have h_inv3 : Stor.Weth10Inv
      (Devm.getStor s3 sevm.currentTarget) 0
      (Devm.getBal s3 sevm.currentTarget) := by
    have h := h_pre.inv.1 rfl
    change Stor.Weth10Inv
      (Devm.getStor s sevm.currentTarget) sevm.value
      (Devm.getBal s sevm.currentTarget) at h
    rw [h_value] at h
    rw [← congrFun h_stor_s_s3 sevm.currentTarget,
      ← congrFun h_bal_s_s3 sevm.currentTarget]
    exact h
  have h_balance3 :
      balance =
        (Devm.getStor s3 sevm.currentTarget).get sevm.caller.toB256 := by
    rw [h_balance, congrFun h_stor_s_s3 sevm.currentTarget]
  rcases of_run_prepend debitLoadedBalance _ run3 with
    ⟨s4, hdebit, run4⟩
  obtain ⟨h_dec, h_cover, h_flash⟩ :=
    debitLoadedBalance_storage (validAdr_toB256 sevm.caller)
      h_balance3 h_token_le hp3 hdebit
  let eventLine : Line :=
    [caller] ++ arg 1 ++ [pushB256 0] ++ emitTransfer ++ [swap 0, pop]
  rcases of_run_prepend eventLine _ run4 with
    ⟨s5, hevent, run5⟩
  have hp5 : Sevm.argWord sevm 1 :: [] <<+ s5.stack := by
    apply prefix_of_burnEvent 1 nil_pref
    simpa only [eventLine] using hevent
  rcases of_run_prepend sendValueToCaller _ run5 with
    ⟨s6, hsend, run6⟩
  obtain ⟨sc, g, hpCall, hcall, h_stor_s5_sc, h_bal_s5_sc,
      h_code_s5_sc⟩ :=
    of_sendValueToCaller hp5 hsend
  rcases of_run_next run6 with ⟨si, hiszero, run7⟩
  have h_eth_lookup :
      ((weth10 dp).main :: weth10Aux)[ethTransferErrorSlot]? =
        some (Func.revWith "WETH: ETH transfer failed") := by
    simp [weth10, weth10Aux, ethTransferErrorSlot, ethTransferError]
  rcases of_run_branch_call_revWith h_eth_lookup run7 with
    ⟨sb, hpopCall, hnext⟩
  have h_eth_le :
      Sevm.argWord sevm 1 ≤ sc.getBal sevm.currentTarget :=
    value_le_balance_of_run_call_success_guard
      hpCall hcall hiszero hpopCall
  have h_bal_s3_sc : Devm.getBal s3 = Devm.getBal sc :=
    (Line.of_inv Devm.getBal (by line_inv) hdebit).trans
      ((Line.of_inv Devm.getBal (by line_inv) hevent).trans h_bal_s5_sc)
  have h_stor_s4_sc : Devm.getStor s4 = Devm.getStor sc :=
    (Line.of_inv Devm.getStor (by line_inv) hevent).trans h_stor_s5_sc
  have h_code_s3_sc :
      Devm.getCode s3 sevm.currentTarget =
        Devm.getCode sc sevm.currentTarget :=
    (congrFun (Line.of_inv Devm.getCode (by line_inv) hdebit)
        sevm.currentTarget).trans
      ((congrFun (Line.of_inv Devm.getCode (by line_inv) hevent)
          sevm.currentTarget).trans
        (congrFun h_code_s5_sc sevm.currentTarget))
  have h_code_sc :
      some (sc.getCode sevm.currentTarget).toList =
        Prog.compile (weth10 dp) := by
    rw [← h_code_s3_sc, ← h_code_s_s3]
    exact h_pre.code
  have h_side_sc : SumNof sc.getBal := by
    rw [← h_bal_s3_sc, ← h_bal_s_s3]
    exact h_pre.side
  have h_eth_le3 :
      Sevm.argWord sevm 1 ≤ s3.getBal sevm.currentTarget := by
    rw [h_bal_s3_sc]
    exact h_eth_le
  have h_afterDebit : Stor.Weth10Inv
      (Devm.getStor s4 sevm.currentTarget) 0
      (Devm.getBal s3 sevm.currentTarget - Sevm.argWord sevm 1) :=
    Stor.Weth10Inv.withdraw h_inv3 h_dec h_cover h_eth_le3 h_flash
  have h_ready : Stor.Weth10Inv
      (Devm.getStor sc sevm.currentTarget) 0
      (sc.getBal sevm.currentTarget - Sevm.argWord sevm 1) := by
    rw [← congrFun h_stor_s4_sc sevm.currentTarget,
      ← congrFun h_bal_s3_sc sevm.currentTarget]
    exact h_afterDebit
  have h_post_call := backedPost_of_value_call dp sevm.currentTarget
    rfl ih hpCall h_code_sc h_side_sc h_eth_le h_ready hcall
  have h_stor_s6_si : Devm.getStor s6 = Devm.getStor si :=
    Line.of_inv Devm.getStor (by line_inv)
      (Line.Run.cons hiszero Line.Run.nil)
  have h_stor_si_sb : Devm.getStor si = Devm.getStor sb :=
    PopBurn.Inv.inv hpopCall
  have h_stor_s6_sb : Devm.getStor s6 = Devm.getStor sb :=
    h_stor_s6_si.trans h_stor_si_sb
  have h_bal_s6_si : Devm.getBal s6 = Devm.getBal si :=
    Line.of_inv Devm.getBal (by line_inv)
      (Line.Run.cons hiszero Line.Run.nil)
  have h_bal_si_sb : Devm.getBal si = Devm.getBal sb :=
    PopBurn.Inv.inv hpopCall
  have h_bal_s6_sb : Devm.getBal s6 = Devm.getBal sb :=
    h_bal_s6_si.trans h_bal_si_sb
  have h_code_nonempty :
      (sc.getCode sevm.currentTarget).toList ≠ [] := by
    intro he
    apply Prog.compile_ne_nil (p := weth10 dp)
    rw [← h_code_sc, he]
  have h_code_s6_sc :
      s6.getCode sevm.currentTarget = sc.getCode sevm.currentTarget :=
    code_eq_of_ninst_run h_code_nonempty hcall
  have h_code_s6_si :
      s6.getCode sevm.currentTarget = si.getCode sevm.currentTarget :=
    congrFun (Line.of_inv Devm.getCode (by line_inv)
      (Line.Run.cons hiszero Line.Run.nil)) sevm.currentTarget
  have h_code_si_sb :
      si.getCode sevm.currentTarget = sb.getCode sevm.currentTarget :=
    getCode_eq_of_state_eq hpopCall.state sevm.currentTarget
  have h_code_sb_sc :
      sb.getCode sevm.currentTarget = sc.getCode sevm.currentTarget :=
    (h_code_s6_si.trans h_code_si_sb).symm.trans h_code_s6_sc
  have h_inv_sb : Stor.Weth10Inv
      (Devm.getStor sb sevm.currentTarget) 0
      (Devm.getBal sb sevm.currentTarget) := by
    rw [← congrFun h_stor_s6_sb sevm.currentTarget,
      ← congrFun h_bal_s6_sb sevm.currentTarget]
    exact h_post_call.inv
  refine ⟨sb, ?_, hnext⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [h_code_sb_sc]
    exact h_code_sc
  · rw [← h_bal_s6_sb]
    exact h_post_call.side
  · intro _
    change Stor.Weth10Inv
      (Devm.getStor sb sevm.currentTarget) sevm.value
      (Devm.getBal sb sevm.currentTarget)
    simpa only [h_value] using h_inv_sb
  · intro hne
    exact (hne rfl).elim

/-- The exact zero-recipient `transfer` branch preserves backing. -/
theorem backedPost_of_transferZero (dp : DeployParams) (ca : Adr)
    {sevm : Sevm} {s r : Devm}
    (h_target : sevm.currentTarget = ca)
    (h_pre : (backedSpec weth10 dp).Pre ca sevm s)
    (ih : Exec.InvDepth sevm.depth ca (weth10 dp)
      ((backedSpec weth10 dp).PreWf ca) ((backedSpec weth10 dp).Post ca))
    (h_value : sevm.value = 0)
    (run : Func.Run ((weth10 dp).main :: weth10Aux) sevm s
      (transferZeroThen returnTrue) r) :
    (backedSpec weth10 dp).Post ca sevm r := by
  obtain ⟨snext, h_pre_next, hreturn⟩ :=
    backedPre_of_transferZeroThen dp ca
      h_target h_pre ih h_value run
  refine ⟨Func.preserves_nof hreturn h_pre_next.side, ?_⟩
  have h_stor : Devm.getStor snext = Devm.getStor r :=
    Func.of_inv Devm.getStor Devm.getStor (by func_inv) hreturn
  have h_bal : Devm.getBal snext = Devm.getBal r :=
    Func.of_inv Devm.getBal Devm.getBal (by func_inv) hreturn
  change Stor.Weth10Inv (Devm.getStor r ca) 0 (Devm.getBal r ca)
  rw [← congrFun h_stor ca, ← congrFun h_bal ca]
  have h := h_pre_next.inv.1 h_target
  change Stor.Weth10Inv
    (Devm.getStor snext ca) sevm.value (Devm.getBal snext ca) at h
  rw [h_value] at h
  exact h

/-- The exact nonpayable `withdraw` selector preserves WETH10 backing.  Its
accepted value-call result supplies the ETH cover premise, while the exact
token debit and unchanged flash counter supply the storage premises. -/
theorem backedSpec_withdraw_funcSound (dp : DeployParams) (ca : Adr) :
    (backedSpec weth10 dp).FuncSoundNoMem ca weth10Aux
      (nonpayable withdraw) := by
  intro sevm s r h_target h_pre ih run
  subst ca
  refine ⟨Func.preserves_nof run h_pre.side, ?_⟩
  change Stor.Weth10Inv
    (Devm.getStor r sevm.currentTarget) 0
    (Devm.getBal r sevm.currentTarget)
  obtain ⟨mid, h_value, h_state_mid, h_body⟩ :=
    run_body_of_run_nonpayable run
  have h_pre_mid := h_pre.state_eq h_state_mid.symm
  simp only [withdraw] at h_body
  rcases of_run_prepend (loadCallerBalanceAmount 0) _ h_body with
    ⟨s1, hload, run1⟩
  rcases prefix_of_loadCallerBalanceAmount nil_pref hload with
    ⟨balance, h_balance, hp1⟩
  rcases of_run_prepend balanceTooSmall _ run1 with
    ⟨s2, hguard, run2⟩
  have hp2 :
      (balance <? Sevm.argWord sevm 0) :: balance ::
        Sevm.argWord sevm 0 :: sevm.caller.toB256 :: [] <<+ s2.stack :=
    prefix_of_balanceTooSmall hp1 hguard
  have h_burn_lookup :
      ((weth10 dp).main :: weth10Aux)[burnBalanceErrorSlot]? =
        some (Func.revWith "WETH: burn amount exceeds balance") := by
    simp [weth10, weth10Aux, burnBalanceErrorSlot, burnBalanceError]
  rcases of_run_branch_call_revWith h_burn_lookup run2 with
    ⟨s3, hpopGuard, run3⟩
  have hpopStack := hpopGuard.stack
  simp only [Stack.Pop, Split, List.nil_append, List.cons_append] at hpopStack
  rw [hpopStack] at hp2
  have h_flag : (balance <? Sevm.argWord sevm 0) = 0 :=
    pref_head_unique hp2 (pref_append [0] s3.stack)
  have h_token_le : Sevm.argWord sevm 0 ≤ balance := by
    rw [← B256.not_lt]
    intro hlt
    rw [B256.ltCheck, if_pos hlt] at h_flag
    exact B256.zero_ne_one h_flag.symm
  rw [h_flag] at hp2
  have hp3 :
      [balance, Sevm.argWord sevm 0, sevm.caller.toB256] <<+ s3.stack :=
    cons_pref_cons_inv hp2
  have h_stor_mid_s1 : Devm.getStor mid = Devm.getStor s1 :=
    Line.of_inv Devm.getStor (by line_inv) hload
  have h_stor_s1_s2 : Devm.getStor s1 = Devm.getStor s2 :=
    Line.of_inv Devm.getStor (by line_inv) hguard
  have h_stor_mid_s3 : Devm.getStor mid = Devm.getStor s3 :=
    h_stor_mid_s1.trans
      (h_stor_s1_s2.trans
        (funext fun a => (Devm.PopBurn.getStor hpopGuard a).symm))
  have h_bal_mid_s3 : Devm.getBal mid = Devm.getBal s3 :=
    (Line.of_inv Devm.getBal (by line_inv) hload).trans
      ((Line.of_inv Devm.getBal (by line_inv) hguard).trans
        (PopBurn.Inv.inv hpopGuard))
  have h_code_mid_s3 :
      Devm.getCode mid sevm.currentTarget =
        Devm.getCode s3 sevm.currentTarget :=
    (congrFun (Line.of_inv Devm.getCode (by line_inv) hload)
        sevm.currentTarget).trans
      ((congrFun (Line.of_inv Devm.getCode (by line_inv) hguard)
          sevm.currentTarget).trans
        (getCode_eq_of_state_eq hpopGuard.state sevm.currentTarget))
  have h_pre3 := h_pre_mid.of_eqs
    h_code_mid_s3.symm
    h_bal_mid_s3.symm
    (congrFun h_stor_mid_s3.symm sevm.currentTarget)
  have h_inv3 : Stor.Weth10Inv
      (Devm.getStor s3 sevm.currentTarget) 0
      (Devm.getBal s3 sevm.currentTarget) := by
    have h := h_pre3.inv.1 rfl
    change Stor.Weth10Inv
      (Devm.getStor s3 sevm.currentTarget) sevm.value
      (Devm.getBal s3 sevm.currentTarget) at h
    simpa only [h_value] using h
  have h_balance3 :
      balance =
        (Devm.getStor s3 sevm.currentTarget).get sevm.caller.toB256 := by
    rw [h_balance, congrFun h_stor_mid_s3 sevm.currentTarget]
  rcases of_run_prepend debitLoadedBalance _ run3 with
    ⟨s4, hdebit, run4⟩
  obtain ⟨h_dec, h_cover, h_flash⟩ :=
    debitLoadedBalance_storage (validAdr_toB256 sevm.caller)
      h_balance3 h_token_le hp3 hdebit
  let eventLine : Line :=
    [caller] ++ arg 0 ++ [pushB256 0] ++ emitTransfer ++ [swap 0, pop]
  rcases of_run_prepend eventLine _ run4 with
    ⟨s5, hevent, run5⟩
  have hp5 : Sevm.argWord sevm 0 :: [] <<+ s5.stack := by
    apply prefix_of_withdrawEvent nil_pref
    simpa only [eventLine] using hevent
  rcases of_run_prepend sendValueToCaller _ run5 with
    ⟨s6, hsend, run6⟩
  obtain ⟨sc, g, hpCall, hcall, h_stor_s5_sc, h_bal_s5_sc,
      h_code_s5_sc⟩ :=
    of_sendValueToCaller hp5 hsend
  rcases of_run_next run6 with ⟨si, hiszero, run7⟩
  have h_eth_lookup :
      ((weth10 dp).main :: weth10Aux)[ethTransferErrorSlot]? =
        some (Func.revWith "WETH: ETH transfer failed") := by
    simp [weth10, weth10Aux, ethTransferErrorSlot, ethTransferError]
  rcases of_run_branch_call_revWith h_eth_lookup run7 with
    ⟨sb, hpopCall, hstop⟩
  have h_eth_le :
      Sevm.argWord sevm 0 ≤ sc.getBal sevm.currentTarget :=
    value_le_balance_of_run_call_success_guard
      hpCall hcall hiszero hpopCall
  have h_bal_s3_sc : Devm.getBal s3 = Devm.getBal sc :=
    (Line.of_inv Devm.getBal (by line_inv) hdebit).trans
      ((Line.of_inv Devm.getBal (by line_inv) hevent).trans h_bal_s5_sc)
  have h_stor_s4_sc : Devm.getStor s4 = Devm.getStor sc :=
    (Line.of_inv Devm.getStor (by line_inv) hevent).trans h_stor_s5_sc
  have h_code_s3_sc : Devm.getCode s3 = Devm.getCode sc :=
    (Line.of_inv Devm.getCode (by line_inv) hdebit).trans
      ((Line.of_inv Devm.getCode (by line_inv) hevent).trans h_code_s5_sc)
  have h_code_sc :
      some (sc.getCode sevm.currentTarget).toList =
        Prog.compile (weth10 dp) := by
    rw [← congrFun h_code_s3_sc sevm.currentTarget]
    exact h_pre3.code
  have h_side_sc : SumNof sc.getBal := by
    rw [← h_bal_s3_sc]
    exact h_pre3.side
  have h_eth_le3 :
      Sevm.argWord sevm 0 ≤ s3.getBal sevm.currentTarget := by
    rw [h_bal_s3_sc]
    exact h_eth_le
  have h_afterDebit : Stor.Weth10Inv
      (Devm.getStor s4 sevm.currentTarget) 0
      (Devm.getBal s3 sevm.currentTarget - Sevm.argWord sevm 0) :=
    Stor.Weth10Inv.withdraw h_inv3 h_dec h_cover h_eth_le3 h_flash
  have h_ready : Stor.Weth10Inv
      (Devm.getStor sc sevm.currentTarget) 0
      (sc.getBal sevm.currentTarget - Sevm.argWord sevm 0) := by
    rw [← congrFun h_stor_s4_sc sevm.currentTarget,
      ← congrFun h_bal_s3_sc sevm.currentTarget]
    exact h_afterDebit
  have h_post_call := backedPost_of_value_call dp sevm.currentTarget
    rfl ih hpCall h_code_sc h_side_sc h_eth_le h_ready hcall
  have h_stor_s6_si : Devm.getStor s6 = Devm.getStor si :=
    Line.of_inv Devm.getStor (by line_inv)
      (Line.Run.cons hiszero Line.Run.nil)
  have h_stor_si_sb : Devm.getStor si = Devm.getStor sb :=
    PopBurn.Inv.inv hpopCall
  have h_stor_sb_r : Devm.getStor sb = Devm.getStor r :=
    Func.of_inv Devm.getStor Devm.getStor (by func_inv) hstop
  have h_stor_s6_r : Devm.getStor s6 = Devm.getStor r :=
    h_stor_s6_si.trans (h_stor_si_sb.trans h_stor_sb_r)
  have h_bal_s6_si : Devm.getBal s6 = Devm.getBal si :=
    Line.of_inv Devm.getBal (by line_inv)
      (Line.Run.cons hiszero Line.Run.nil)
  have h_bal_si_sb : Devm.getBal si = Devm.getBal sb :=
    PopBurn.Inv.inv hpopCall
  have h_bal_sb_r : Devm.getBal sb = Devm.getBal r :=
    Func.of_inv Devm.getBal Devm.getBal (by func_inv) hstop
  have h_bal_s6_r : Devm.getBal s6 = Devm.getBal r :=
    h_bal_s6_si.trans (h_bal_si_sb.trans h_bal_sb_r)
  rw [← congrFun h_stor_s6_r sevm.currentTarget,
    ← congrFun h_bal_s6_r sevm.currentTarget]
  exact h_post_call.inv

/-- The exact nonpayable `transfer` selector preserves WETH10 backing.
Raw zero takes the ETH-withdrawal branch; every nonzero ABI word takes the
normalized token-credit branch, including dirty words whose low 160 bits are
zero. -/
theorem backedSpec_transfer_funcSound (dp : DeployParams) (ca : Adr) :
    (backedSpec weth10 dp).FuncSoundNoMem ca weth10Aux
      (nonpayable transfer) := by
  intro sevm s r h_target h_pre ih run
  subst ca
  obtain ⟨mid, h_value, h_state_mid, h_body⟩ :=
    run_body_of_run_nonpayable run
  have h_pre_mid := h_pre.state_eq h_state_mid.symm
  simp only [transfer, transferThen] at h_body
  rcases of_run_prepend (arg 0) _ h_body with
    ⟨s1, harg, run1⟩
  have hp1 : Sevm.argWord sevm 0 :: [] <<+ s1.stack :=
    prefix_of_arg nil_pref harg
  rcases of_run_next run1 with ⟨s2, hiszero, run2⟩
  have hp2 : (Sevm.argWord sevm 0 =? 0) :: [] <<+ s2.stack :=
    prefix_of_iszero hiszero hp1
  rcases of_run_branch run2 with
      ⟨s3, hpop, hnonzero⟩ |
      ⟨w, s3, s4, hnz, hpop, hburn, hzero⟩
  · have h_stor_mid_s3 : Devm.getStor mid = Devm.getStor s3 :=
      (Line.of_inv Devm.getStor (by line_inv) harg).trans
        ((Line.of_inv Devm.getStor (by line_inv)
          (Line.Run.cons hiszero Line.Run.nil)).trans
            (PopBurn.Inv.inv hpop))
    have h_bal_mid_s3 : Devm.getBal mid = Devm.getBal s3 :=
      (Line.of_inv Devm.getBal (by line_inv) harg).trans
        ((Line.of_inv Devm.getBal (by line_inv)
          (Line.Run.cons hiszero Line.Run.nil)).trans
            (PopBurn.Inv.inv hpop))
    have h_code_mid_s3 :
        Devm.getCode mid sevm.currentTarget =
          Devm.getCode s3 sevm.currentTarget :=
      (congrFun (Line.of_inv Devm.getCode (by line_inv) harg)
          sevm.currentTarget).trans
        ((congrFun (Line.of_inv Devm.getCode (by line_inv)
            (Line.Run.cons hiszero Line.Run.nil))
            sevm.currentTarget).trans
          (getCode_eq_of_state_eq hpop.state sevm.currentTarget))
    have h_pre3 := h_pre_mid.of_eqs h_code_mid_s3.symm
      h_bal_mid_s3.symm
      (congrFun h_stor_mid_s3.symm sevm.currentTarget)
    exact backedPost_of_transferNonzero dp sevm.currentTarget
      rfl h_pre3 h_value hnonzero
  · have h_stor_mid_s4 : Devm.getStor mid = Devm.getStor s4 :=
      (Line.of_inv Devm.getStor (by line_inv) harg).trans
        ((Line.of_inv Devm.getStor (by line_inv)
          (Line.Run.cons hiszero Line.Run.nil)).trans
            ((PopBurn.Inv.inv hpop).trans (Burn.Inv.inv hburn)))
    have h_bal_mid_s4 : Devm.getBal mid = Devm.getBal s4 :=
      (Line.of_inv Devm.getBal (by line_inv) harg).trans
        ((Line.of_inv Devm.getBal (by line_inv)
          (Line.Run.cons hiszero Line.Run.nil)).trans
            ((PopBurn.Inv.inv hpop).trans (Burn.Inv.inv hburn)))
    have h_code_mid_s4 :
        Devm.getCode mid sevm.currentTarget =
          Devm.getCode s4 sevm.currentTarget :=
      (congrFun (Line.of_inv Devm.getCode (by line_inv) harg)
          sevm.currentTarget).trans
        ((congrFun (Line.of_inv Devm.getCode (by line_inv)
            (Line.Run.cons hiszero Line.Run.nil))
            sevm.currentTarget).trans
          ((getCode_eq_of_state_eq hpop.state sevm.currentTarget).trans
            (getCode_eq_of_state_eq hburn.state sevm.currentTarget)))
    have h_pre4 := h_pre_mid.of_eqs h_code_mid_s4.symm
      h_bal_mid_s4.symm
      (congrFun h_stor_mid_s4.symm sevm.currentTarget)
    exact backedPost_of_transferZero dp sevm.currentTarget
      rfl h_pre4 ih h_value hzero

/-- The exact nonpayable `withdrawTo` selector preserves WETH10 backing for
arbitrary canonical or dirty target words. -/
theorem backedSpec_withdrawTo_funcSound (dp : DeployParams) (ca : Adr) :
    (backedSpec weth10 dp).FuncSoundNoMem ca weth10Aux
      (nonpayable withdrawTo) := by
  intro sevm s r h_target h_pre ih run
  subst ca
  refine ⟨Func.preserves_nof run h_pre.side, ?_⟩
  change Stor.Weth10Inv
    (Devm.getStor r sevm.currentTarget) 0
    (Devm.getBal r sevm.currentTarget)
  obtain ⟨mid, h_value, h_state_mid, h_body⟩ :=
    run_body_of_run_nonpayable run
  have h_pre_mid := h_pre.state_eq h_state_mid.symm
  simp only [withdrawTo] at h_body
  rcases of_run_prepend (loadCallerBalanceAmount 1) _ h_body with
    ⟨s1, hload, run1⟩
  rcases prefix_of_loadCallerBalanceAmount nil_pref hload with
    ⟨balance, h_balance, hp1⟩
  rcases of_run_prepend balanceTooSmall _ run1 with
    ⟨s2, hguard, run2⟩
  have hp2 :
      (balance <? Sevm.argWord sevm 1) :: balance ::
        Sevm.argWord sevm 1 :: sevm.caller.toB256 :: [] <<+ s2.stack :=
    prefix_of_balanceTooSmall hp1 hguard
  have h_burn_lookup :
      ((weth10 dp).main :: weth10Aux)[burnBalanceErrorSlot]? =
        some (Func.revWith "WETH: burn amount exceeds balance") := by
    simp [weth10, weth10Aux, burnBalanceErrorSlot, burnBalanceError]
  rcases of_run_branch_call_revWith h_burn_lookup run2 with
    ⟨s3, hpopGuard, run3⟩
  have hpopStack := hpopGuard.stack
  simp only [Stack.Pop, Split, List.nil_append, List.cons_append] at hpopStack
  rw [hpopStack] at hp2
  have h_flag : (balance <? Sevm.argWord sevm 1) = 0 :=
    pref_head_unique hp2 (pref_append [0] s3.stack)
  have h_token_le : Sevm.argWord sevm 1 ≤ balance := by
    rw [← B256.not_lt]
    intro hlt
    rw [B256.ltCheck, if_pos hlt] at h_flag
    exact B256.zero_ne_one h_flag.symm
  rw [h_flag] at hp2
  have hp3 :
      [balance, Sevm.argWord sevm 1, sevm.caller.toB256] <<+ s3.stack :=
    cons_pref_cons_inv hp2
  have h_stor_mid_s1 : Devm.getStor mid = Devm.getStor s1 :=
    Line.of_inv Devm.getStor (by line_inv) hload
  have h_stor_s1_s2 : Devm.getStor s1 = Devm.getStor s2 :=
    Line.of_inv Devm.getStor (by line_inv) hguard
  have h_stor_mid_s3 : Devm.getStor mid = Devm.getStor s3 :=
    h_stor_mid_s1.trans
      (h_stor_s1_s2.trans (PopBurn.Inv.inv hpopGuard))
  have h_bal_mid_s3 : Devm.getBal mid = Devm.getBal s3 :=
    (Line.of_inv Devm.getBal (by line_inv) hload).trans
      ((Line.of_inv Devm.getBal (by line_inv) hguard).trans
        (PopBurn.Inv.inv hpopGuard))
  have h_code_mid_s3 :
      Devm.getCode mid sevm.currentTarget =
        Devm.getCode s3 sevm.currentTarget :=
    (congrFun (Line.of_inv Devm.getCode (by line_inv) hload)
        sevm.currentTarget).trans
      ((congrFun (Line.of_inv Devm.getCode (by line_inv) hguard)
          sevm.currentTarget).trans
        (getCode_eq_of_state_eq hpopGuard.state sevm.currentTarget))
  have h_pre3 := h_pre_mid.of_eqs h_code_mid_s3.symm
    h_bal_mid_s3.symm
    (congrFun h_stor_mid_s3.symm sevm.currentTarget)
  have h_inv3 : Stor.Weth10Inv
      (Devm.getStor s3 sevm.currentTarget) 0
      (Devm.getBal s3 sevm.currentTarget) := by
    have h := h_pre3.inv.1 rfl
    change Stor.Weth10Inv
      (Devm.getStor s3 sevm.currentTarget) sevm.value
      (Devm.getBal s3 sevm.currentTarget) at h
    simpa only [h_value] using h
  have h_balance3 :
      balance =
        (Devm.getStor s3 sevm.currentTarget).get sevm.caller.toB256 := by
    rw [h_balance, congrFun h_stor_mid_s3 sevm.currentTarget]
  rcases of_run_prepend debitLoadedBalance _ run3 with
    ⟨s4, hdebit, run4⟩
  obtain ⟨h_dec, h_cover, h_flash⟩ :=
    debitLoadedBalance_storage (validAdr_toB256 sevm.caller)
      h_balance3 h_token_le hp3 hdebit
  let eventLine : Line :=
    [caller] ++ arg 1 ++ [pushB256 0] ++ emitTransfer ++ [swap 0, pop]
  rcases of_run_prepend eventLine _ run4 with
    ⟨s5, hevent, run5⟩
  have hp5 : Sevm.argWord sevm 1 :: [] <<+ s5.stack := by
    apply prefix_of_burnEvent 1 nil_pref
    simpa only [eventLine] using hevent
  rcases of_run_prepend (sendValueToArg 0) _ run5 with
    ⟨s6, hsend, run6⟩
  obtain ⟨sc, g, hpCall, hcall, h_stor_s5_sc, h_bal_s5_sc,
      h_code_s5_sc⟩ :=
    of_sendValueToArg 0 hp5 hsend
  rcases of_run_next run6 with ⟨si, hiszero, run7⟩
  have h_eth_lookup :
      ((weth10 dp).main :: weth10Aux)[ethTransferErrorSlot]? =
        some (Func.revWith "WETH: ETH transfer failed") := by
    simp [weth10, weth10Aux, ethTransferErrorSlot, ethTransferError]
  rcases of_run_branch_call_revWith h_eth_lookup run7 with
    ⟨sb, hpopCall, hstop⟩
  have h_eth_le :
      Sevm.argWord sevm 1 ≤ sc.getBal sevm.currentTarget :=
    value_le_balance_of_run_call_success_guard
      hpCall hcall hiszero hpopCall
  have h_bal_s3_sc : Devm.getBal s3 = Devm.getBal sc :=
    (Line.of_inv Devm.getBal (by line_inv) hdebit).trans
      ((Line.of_inv Devm.getBal (by line_inv) hevent).trans h_bal_s5_sc)
  have h_stor_s4_sc : Devm.getStor s4 = Devm.getStor sc :=
    (Line.of_inv Devm.getStor (by line_inv) hevent).trans h_stor_s5_sc
  have h_code_s3_sc : Devm.getCode s3 = Devm.getCode sc :=
    (Line.of_inv Devm.getCode (by line_inv) hdebit).trans
      ((Line.of_inv Devm.getCode (by line_inv) hevent).trans h_code_s5_sc)
  have h_code_sc :
      some (sc.getCode sevm.currentTarget).toList =
        Prog.compile (weth10 dp) := by
    rw [← congrFun h_code_s3_sc sevm.currentTarget]
    exact h_pre3.code
  have h_side_sc : SumNof sc.getBal := by
    rw [← h_bal_s3_sc]
    exact h_pre3.side
  have h_eth_le3 :
      Sevm.argWord sevm 1 ≤ s3.getBal sevm.currentTarget := by
    rw [h_bal_s3_sc]
    exact h_eth_le
  have h_afterDebit : Stor.Weth10Inv
      (Devm.getStor s4 sevm.currentTarget) 0
      (Devm.getBal s3 sevm.currentTarget - Sevm.argWord sevm 1) :=
    Stor.Weth10Inv.withdraw h_inv3 h_dec h_cover h_eth_le3 h_flash
  have h_ready : Stor.Weth10Inv
      (Devm.getStor sc sevm.currentTarget) 0
      (sc.getBal sevm.currentTarget - Sevm.argWord sevm 1) := by
    rw [← congrFun h_stor_s4_sc sevm.currentTarget,
      ← congrFun h_bal_s3_sc sevm.currentTarget]
    exact h_afterDebit
  have h_post_call := backedPost_of_value_call dp sevm.currentTarget
    rfl ih hpCall h_code_sc h_side_sc h_eth_le h_ready hcall
  have h_stor_s6_si : Devm.getStor s6 = Devm.getStor si :=
    Line.of_inv Devm.getStor (by line_inv)
      (Line.Run.cons hiszero Line.Run.nil)
  have h_stor_si_sb : Devm.getStor si = Devm.getStor sb :=
    PopBurn.Inv.inv hpopCall
  have h_stor_sb_r : Devm.getStor sb = Devm.getStor r :=
    Func.of_inv Devm.getStor Devm.getStor (by func_inv) hstop
  have h_stor_s6_r : Devm.getStor s6 = Devm.getStor r :=
    h_stor_s6_si.trans (h_stor_si_sb.trans h_stor_sb_r)
  have h_bal_s6_si : Devm.getBal s6 = Devm.getBal si :=
    Line.of_inv Devm.getBal (by line_inv)
      (Line.Run.cons hiszero Line.Run.nil)
  have h_bal_si_sb : Devm.getBal si = Devm.getBal sb :=
    PopBurn.Inv.inv hpopCall
  have h_bal_sb_r : Devm.getBal sb = Devm.getBal r :=
    Func.of_inv Devm.getBal Devm.getBal (by func_inv) hstop
  have h_bal_s6_r : Devm.getBal s6 = Devm.getBal r :=
    h_bal_s6_si.trans (h_bal_si_sb.trans h_bal_sb_r)
  rw [← congrFun h_stor_s6_r sevm.currentTarget,
    ← congrFun h_bal_s6_r sevm.currentTarget]
  exact h_post_call.inv

/-! ## Allowance-gated transfer and withdrawal cores -/

/-- The exact nonzero-recipient `transferFrom` core preserves backing by
debiting the normalized source and crediting the normalized recipient. -/
theorem backedPost_of_transferFromNonzero (dp : DeployParams) (ca : Adr)
    {sevm : Sevm} {s r : Devm}
    (h_target : sevm.currentTarget = ca)
    (h_pre : (backedSpec weth10 dp).Pre ca sevm s)
    (h_value : sevm.value = 0)
    (run : Func.Run ((weth10 dp).main :: weth10Aux) sevm s
      transferFromNonzero r) :
    (backedSpec weth10 dp).Post ca sevm r := by
  subst ca
  refine ⟨Func.preserves_nof run h_pre.side, ?_⟩
  change Stor.Weth10Inv
    (Devm.getStor r sevm.currentTarget) 0
    (Devm.getBal r sevm.currentTarget)
  have h_inv0 := h_pre.inv.1 rfl
  change Stor.Weth10Inv
    (Devm.getStor s sevm.currentTarget) sevm.value
    (Devm.getBal s sevm.currentTarget) at h_inv0
  rw [h_value] at h_inv0
  simp only [transferFromNonzero] at run
  rcases of_run_prepend (loadArgBalanceAmount 0 2) _ run with
    ⟨s1, hload, run1⟩
  rcases prefix_of_loadArgBalanceAmount 0 2 nil_pref hload with
    ⟨balance, owner, h_owner, h_balance, hp1⟩
  rcases of_run_prepend balanceTooSmall _ run1 with
    ⟨s2, hguard, run2⟩
  have hp2 :
      (balance <? Sevm.argWord sevm 2) :: balance ::
        Sevm.argWord sevm 2 :: owner :: [] <<+ s2.stack :=
    prefix_of_balanceTooSmall hp1 hguard
  have h_error_lookup :
      ((weth10 dp).main :: weth10Aux)[transferBalanceErrorSlot]? =
        some (Func.revWith "WETH: transfer amount exceeds balance") := by
    simp [weth10, weth10Aux, transferBalanceErrorSlot,
      transferBalanceError]
  rcases of_run_branch_call_revWith h_error_lookup run2 with
    ⟨s3, hpopGuard, run3⟩
  have hpopStack := hpopGuard.stack
  simp only [Stack.Pop, Split, List.nil_append, List.cons_append] at hpopStack
  rw [hpopStack] at hp2
  have h_flag : (balance <? Sevm.argWord sevm 2) = 0 :=
    pref_head_unique hp2 (pref_append [0] s3.stack)
  have h_token_le : Sevm.argWord sevm 2 ≤ balance := by
    rw [← B256.not_lt]
    intro hlt
    rw [B256.ltCheck, if_pos hlt] at h_flag
    exact B256.zero_ne_one h_flag.symm
  rw [h_flag] at hp2
  have hp3 :
      [balance, Sevm.argWord sevm 2, owner] <<+ s3.stack :=
    cons_pref_cons_inv hp2
  have h_stor_s_s3 : Devm.getStor s = Devm.getStor s3 :=
    (Line.of_inv Devm.getStor (by line_inv) hload).trans
      ((Line.of_inv Devm.getStor (by line_inv) hguard).trans
        (PopBurn.Inv.inv hpopGuard))
  have h_bal_s_s3 : Devm.getBal s = Devm.getBal s3 :=
    (Line.of_inv Devm.getBal (by line_inv) hload).trans
      ((Line.of_inv Devm.getBal (by line_inv) hguard).trans
        (PopBurn.Inv.inv hpopGuard))
  have h_inv3 : Stor.Weth10Inv
      (Devm.getStor s3 sevm.currentTarget) 0
      (Devm.getBal s3 sevm.currentTarget) := by
    rw [← congrFun h_stor_s_s3 sevm.currentTarget,
      ← congrFun h_bal_s_s3 sevm.currentTarget]
    exact h_inv0
  have h_balance3 :
      balance = (Devm.getStor s3 sevm.currentTarget).get owner := by
    rw [h_balance, congrFun h_stor_s_s3 sevm.currentTarget]
  rcases of_run_prepend debitLoadedBalance _ run3 with
    ⟨s4, hdebit, run4⟩
  obtain ⟨h_dec, h_cover, h_flash_debit⟩ :=
    debitLoadedBalance_storage
      (by
        rw [h_owner]
        exact normalizedAddress_valid (Sevm.argWord sevm 0))
      h_balance3 h_token_le hp3 hdebit
  let creditLine : Line :=
    addressArg 1 ++ [dup 0, sload] ++ arg 2 ++ [add, swap 0, sstore]
  rcases of_run_prepend creditLine _ run4 with
    ⟨s5, hcredit, run5⟩
  obtain ⟨recipient, h_inc, h_flash_credit⟩ :=
    creditAddressArg_storage 1 2 (by
      simpa only [creditLine] using hcredit)
  have h_transfer : Transfer
      (Stor.rest (Devm.getStor s3 sevm.currentTarget))
      owner.toAdr (Sevm.argWord sevm 2) recipient
      (Stor.rest (Devm.getStor s5 sevm.currentTarget)) :=
    ⟨h_cover, Stor.rest (Devm.getStor s4 sevm.currentTarget),
      h_dec, h_inc⟩
  have h_flash :
      (Devm.getStor s5 sevm.currentTarget).get flashMintedSlot =
        (Devm.getStor s3 sevm.currentTarget).get flashMintedSlot :=
    h_flash_credit.trans h_flash_debit
  have h_inv5 : Stor.Weth10Inv
      (Devm.getStor s5 sevm.currentTarget) 0
      (Devm.getBal s3 sevm.currentTarget) :=
    Stor.Weth10Inv.transfer h_inv3 h_transfer h_flash
  let logLine : Line :=
    addressArg 0 ++ arg 2 ++ addressArg 1 ++ emitTransfer
  rcases of_run_prepend logLine returnTrue run5 with
    ⟨s6, hlog, hreturn⟩
  have h_stor_s5_r : Devm.getStor s5 = Devm.getStor r :=
    (Line.of_inv Devm.getStor (by line_inv) hlog).trans
      (Func.of_inv Devm.getStor Devm.getStor (by func_inv) hreturn)
  have h_bal_s3_r : Devm.getBal s3 = Devm.getBal r :=
    (Line.of_inv Devm.getBal (by line_inv) hdebit).trans
      ((Line.of_inv Devm.getBal (by line_inv) hcredit).trans
        ((Line.of_inv Devm.getBal (by line_inv) hlog).trans
          (Func.of_inv Devm.getBal Devm.getBal (by func_inv) hreturn)))
  rw [← congrFun h_stor_s5_r sevm.currentTarget,
    ← congrFun h_bal_s3_r sevm.currentTarget]
  exact h_inv5

/-- The exact zero-recipient `transferFrom` core burns the normalized source
balance and preserves backing across the accepted ETH value call. -/
theorem backedPost_of_transferFromZero (dp : DeployParams) (ca : Adr)
    {sevm : Sevm} {s r : Devm}
    (h_target : sevm.currentTarget = ca)
    (h_pre : (backedSpec weth10 dp).Pre ca sevm s)
    (ih : Exec.InvDepth sevm.depth ca (weth10 dp)
      ((backedSpec weth10 dp).PreWf ca) ((backedSpec weth10 dp).Post ca))
    (h_value : sevm.value = 0)
    (run : Func.Run ((weth10 dp).main :: weth10Aux) sevm s
      transferFromZero r) :
    (backedSpec weth10 dp).Post ca sevm r := by
  subst ca
  refine ⟨Func.preserves_nof run h_pre.side, ?_⟩
  change Stor.Weth10Inv
    (Devm.getStor r sevm.currentTarget) 0
    (Devm.getBal r sevm.currentTarget)
  have h_inv0 := h_pre.inv.1 rfl
  change Stor.Weth10Inv
    (Devm.getStor s sevm.currentTarget) sevm.value
    (Devm.getBal s sevm.currentTarget) at h_inv0
  rw [h_value] at h_inv0
  simp only [transferFromZero] at run
  rcases of_run_prepend (loadArgBalanceAmount 0 2) _ run with
    ⟨s1, hload, run1⟩
  rcases prefix_of_loadArgBalanceAmount 0 2 nil_pref hload with
    ⟨balance, owner, h_owner, h_balance, hp1⟩
  rcases of_run_prepend balanceTooSmall _ run1 with
    ⟨s2, hguard, run2⟩
  have hp2 :
      (balance <? Sevm.argWord sevm 2) :: balance ::
        Sevm.argWord sevm 2 :: owner :: [] <<+ s2.stack :=
    prefix_of_balanceTooSmall hp1 hguard
  have h_burn_lookup :
      ((weth10 dp).main :: weth10Aux)[burnBalanceErrorSlot]? =
        some (Func.revWith "WETH: burn amount exceeds balance") := by
    simp [weth10, weth10Aux, burnBalanceErrorSlot, burnBalanceError]
  rcases of_run_branch_call_revWith h_burn_lookup run2 with
    ⟨s3, hpopGuard, run3⟩
  have hpopStack := hpopGuard.stack
  simp only [Stack.Pop, Split, List.nil_append, List.cons_append] at hpopStack
  rw [hpopStack] at hp2
  have h_flag : (balance <? Sevm.argWord sevm 2) = 0 :=
    pref_head_unique hp2 (pref_append [0] s3.stack)
  have h_token_le : Sevm.argWord sevm 2 ≤ balance := by
    rw [← B256.not_lt]
    intro hlt
    rw [B256.ltCheck, if_pos hlt] at h_flag
    exact B256.zero_ne_one h_flag.symm
  rw [h_flag] at hp2
  have hp3 : [balance, Sevm.argWord sevm 2, owner] <<+ s3.stack :=
    cons_pref_cons_inv hp2
  have h_stor_s_s3 : Devm.getStor s = Devm.getStor s3 :=
    (Line.of_inv Devm.getStor (by line_inv) hload).trans
      ((Line.of_inv Devm.getStor (by line_inv) hguard).trans
        (PopBurn.Inv.inv hpopGuard))
  have h_bal_s_s3 : Devm.getBal s = Devm.getBal s3 :=
    (Line.of_inv Devm.getBal (by line_inv) hload).trans
      ((Line.of_inv Devm.getBal (by line_inv) hguard).trans
        (PopBurn.Inv.inv hpopGuard))
  have h_code_s_s3 :
      Devm.getCode s sevm.currentTarget =
        Devm.getCode s3 sevm.currentTarget :=
    (congrFun (Line.of_inv Devm.getCode (by line_inv) hload)
        sevm.currentTarget).trans
      ((congrFun (Line.of_inv Devm.getCode (by line_inv) hguard)
          sevm.currentTarget).trans
        (getCode_eq_of_state_eq hpopGuard.state sevm.currentTarget))
  have h_inv3 : Stor.Weth10Inv
      (Devm.getStor s3 sevm.currentTarget) 0
      (Devm.getBal s3 sevm.currentTarget) := by
    rw [← congrFun h_stor_s_s3 sevm.currentTarget,
      ← congrFun h_bal_s_s3 sevm.currentTarget]
    exact h_inv0
  have h_balance3 :
      balance = (Devm.getStor s3 sevm.currentTarget).get owner := by
    rw [h_balance, congrFun h_stor_s_s3 sevm.currentTarget]
  have h_owner_valid : ValidAdr owner := by
    rw [h_owner]
    exact normalizedAddress_valid (Sevm.argWord sevm 0)
  rcases of_run_prepend debitLoadedBalance _ run3 with
    ⟨s4, hdebit, run4⟩
  obtain ⟨h_dec, h_cover, h_flash⟩ :=
    debitLoadedBalance_storage h_owner_valid
      h_balance3 h_token_le hp3 hdebit
  let eventLine : Line :=
    addressArg 0 ++ arg 2 ++ [pushB256 0] ++ emitTransfer ++
      [swap 0, pop]
  rcases of_run_prepend eventLine _ run4 with
    ⟨s5, hevent, run5⟩
  have hp5 : Sevm.argWord sevm 2 :: [] <<+ s5.stack := by
    apply prefix_of_burnEventFromArg 0 2 nil_pref
    simpa only [eventLine] using hevent
  rcases of_run_prepend sendValueToCaller _ run5 with
    ⟨s6, hsend, run6⟩
  obtain ⟨sc, g, hpCall, hcall, h_stor_s5_sc, h_bal_s5_sc,
      h_code_s5_sc⟩ :=
    of_sendValueToCaller hp5 hsend
  rcases of_run_next run6 with ⟨si, hiszero, run7⟩
  have h_eth_lookup :
      ((weth10 dp).main :: weth10Aux)[ethTransferErrorSlot]? =
        some (Func.revWith "WETH: ETH transfer failed") := by
    simp [weth10, weth10Aux, ethTransferErrorSlot, ethTransferError]
  rcases of_run_branch_call_revWith h_eth_lookup run7 with
    ⟨sb, hpopCall, hreturn⟩
  have h_eth_le :
      Sevm.argWord sevm 2 ≤ sc.getBal sevm.currentTarget :=
    value_le_balance_of_run_call_success_guard
      hpCall hcall hiszero hpopCall
  have h_bal_s3_sc : Devm.getBal s3 = Devm.getBal sc :=
    (Line.of_inv Devm.getBal (by line_inv) hdebit).trans
      ((Line.of_inv Devm.getBal (by line_inv) hevent).trans h_bal_s5_sc)
  have h_stor_s4_sc : Devm.getStor s4 = Devm.getStor sc :=
    (Line.of_inv Devm.getStor (by line_inv) hevent).trans h_stor_s5_sc
  have h_code_s3_sc :
      Devm.getCode s3 sevm.currentTarget =
        Devm.getCode sc sevm.currentTarget :=
    (congrFun (Line.of_inv Devm.getCode (by line_inv) hdebit)
        sevm.currentTarget).trans
      ((congrFun (Line.of_inv Devm.getCode (by line_inv) hevent)
          sevm.currentTarget).trans
        (congrFun h_code_s5_sc sevm.currentTarget))
  have h_code_sc :
      some (sc.getCode sevm.currentTarget).toList =
        Prog.compile (weth10 dp) := by
    rw [← h_code_s3_sc, ← h_code_s_s3]
    exact h_pre.code
  have h_side_sc : SumNof sc.getBal := by
    rw [← h_bal_s3_sc, ← h_bal_s_s3]
    exact h_pre.side
  have h_eth_le3 :
      Sevm.argWord sevm 2 ≤ s3.getBal sevm.currentTarget := by
    rw [h_bal_s3_sc]
    exact h_eth_le
  have h_afterDebit : Stor.Weth10Inv
      (Devm.getStor s4 sevm.currentTarget) 0
      (Devm.getBal s3 sevm.currentTarget - Sevm.argWord sevm 2) :=
    Stor.Weth10Inv.withdraw h_inv3 h_dec h_cover h_eth_le3 h_flash
  have h_ready : Stor.Weth10Inv
      (Devm.getStor sc sevm.currentTarget) 0
      (sc.getBal sevm.currentTarget - Sevm.argWord sevm 2) := by
    rw [← congrFun h_stor_s4_sc sevm.currentTarget,
      ← congrFun h_bal_s3_sc sevm.currentTarget]
    exact h_afterDebit
  have h_post_call := backedPost_of_value_call dp sevm.currentTarget
    rfl ih hpCall h_code_sc h_side_sc h_eth_le h_ready hcall
  have h_stor_s6_si : Devm.getStor s6 = Devm.getStor si :=
    Line.of_inv Devm.getStor (by line_inv)
      (Line.Run.cons hiszero Line.Run.nil)
  have h_stor_si_sb : Devm.getStor si = Devm.getStor sb :=
    PopBurn.Inv.inv hpopCall
  have h_stor_sb_r : Devm.getStor sb = Devm.getStor r :=
    Func.of_inv Devm.getStor Devm.getStor (by func_inv) hreturn
  have h_stor_s6_r : Devm.getStor s6 = Devm.getStor r :=
    h_stor_s6_si.trans (h_stor_si_sb.trans h_stor_sb_r)
  have h_bal_s6_si : Devm.getBal s6 = Devm.getBal si :=
    Line.of_inv Devm.getBal (by line_inv)
      (Line.Run.cons hiszero Line.Run.nil)
  have h_bal_si_sb : Devm.getBal si = Devm.getBal sb :=
    PopBurn.Inv.inv hpopCall
  have h_bal_sb_r : Devm.getBal sb = Devm.getBal r :=
    Func.of_inv Devm.getBal Devm.getBal (by func_inv) hreturn
  have h_bal_s6_r : Devm.getBal s6 = Devm.getBal r :=
    h_bal_s6_si.trans (h_bal_si_sb.trans h_bal_sb_r)
  rw [← congrFun h_stor_s6_r sevm.currentTarget,
    ← congrFun h_bal_s6_r sevm.currentTarget]
  exact h_post_call.inv

/-- The exact `transferFrom` core selects the raw-zero ETH branch or the
nonzero-word token-credit branch without changing the backing argument. -/
theorem backedPost_of_transferFromCore (dp : DeployParams) (ca : Adr)
    {sevm : Sevm} {s r : Devm}
    (h_target : sevm.currentTarget = ca)
    (h_pre : (backedSpec weth10 dp).Pre ca sevm s)
    (ih : Exec.InvDepth sevm.depth ca (weth10 dp)
      ((backedSpec weth10 dp).PreWf ca) ((backedSpec weth10 dp).Post ca))
    (h_value : sevm.value = 0)
    (run : Func.Run ((weth10 dp).main :: weth10Aux) sevm s
      transferFromCore r) :
    (backedSpec weth10 dp).Post ca sevm r := by
  subst ca
  simp only [transferFromCore] at run
  rcases of_run_prepend (arg 1) _ run with
    ⟨s1, harg, run1⟩
  have hp1 : Sevm.argWord sevm 1 :: [] <<+ s1.stack :=
    prefix_of_arg nil_pref harg
  rcases of_run_next run1 with ⟨s2, hiszero, run2⟩
  have hp2 : (Sevm.argWord sevm 1 =? 0) :: [] <<+ s2.stack :=
    prefix_of_iszero hiszero hp1
  rcases of_run_branch run2 with
      ⟨s3, hpop, hnonzero⟩ |
      ⟨w, s3, s4, hnz, hpop, hburn, hzero⟩
  · have h_stor_s_s3 : Devm.getStor s = Devm.getStor s3 :=
      (Line.of_inv Devm.getStor (by line_inv) harg).trans
        ((Line.of_inv Devm.getStor (by line_inv)
          (Line.Run.cons hiszero Line.Run.nil)).trans
            (PopBurn.Inv.inv hpop))
    have h_bal_s_s3 : Devm.getBal s = Devm.getBal s3 :=
      (Line.of_inv Devm.getBal (by line_inv) harg).trans
        ((Line.of_inv Devm.getBal (by line_inv)
          (Line.Run.cons hiszero Line.Run.nil)).trans
            (PopBurn.Inv.inv hpop))
    have h_code_s_s3 :
        Devm.getCode s sevm.currentTarget =
          Devm.getCode s3 sevm.currentTarget :=
      (congrFun (Line.of_inv Devm.getCode (by line_inv) harg)
          sevm.currentTarget).trans
        ((congrFun (Line.of_inv Devm.getCode (by line_inv)
            (Line.Run.cons hiszero Line.Run.nil))
            sevm.currentTarget).trans
          (getCode_eq_of_state_eq hpop.state sevm.currentTarget))
    have h_pre3 := h_pre.of_eqs h_code_s_s3.symm
      h_bal_s_s3.symm
      (congrFun h_stor_s_s3.symm sevm.currentTarget)
    exact backedPost_of_transferFromNonzero dp sevm.currentTarget
      rfl h_pre3 h_value hnonzero
  · have h_stor_s_s4 : Devm.getStor s = Devm.getStor s4 :=
      (Line.of_inv Devm.getStor (by line_inv) harg).trans
        ((Line.of_inv Devm.getStor (by line_inv)
          (Line.Run.cons hiszero Line.Run.nil)).trans
            ((PopBurn.Inv.inv hpop).trans (Burn.Inv.inv hburn)))
    have h_bal_s_s4 : Devm.getBal s = Devm.getBal s4 :=
      (Line.of_inv Devm.getBal (by line_inv) harg).trans
        ((Line.of_inv Devm.getBal (by line_inv)
          (Line.Run.cons hiszero Line.Run.nil)).trans
            ((PopBurn.Inv.inv hpop).trans (Burn.Inv.inv hburn)))
    have h_code_s_s4 :
        Devm.getCode s sevm.currentTarget =
          Devm.getCode s4 sevm.currentTarget :=
      (congrFun (Line.of_inv Devm.getCode (by line_inv) harg)
          sevm.currentTarget).trans
        ((congrFun (Line.of_inv Devm.getCode (by line_inv)
            (Line.Run.cons hiszero Line.Run.nil))
            sevm.currentTarget).trans
          ((getCode_eq_of_state_eq hpop.state sevm.currentTarget).trans
            (getCode_eq_of_state_eq hburn.state sevm.currentTarget)))
    have h_pre4 := h_pre.of_eqs h_code_s_s4.symm
      h_bal_s_s4.symm
      (congrFun h_stor_s_s4.symm sevm.currentTarget)
    exact backedPost_of_transferFromZero dp sevm.currentTarget
      rfl h_pre4 ih h_value hzero

/-- The exact nonpayable `transferFrom` selector preserves WETH10 backing,
including its self/infinite/finite allowance paths. -/
theorem backedSpec_transferFrom_funcSound (dp : DeployParams) (ca : Adr) :
    (backedSpec weth10 dp).FuncSoundNoMem ca weth10Aux
      (nonpayable transferFrom) := by
  intro sevm s r h_target h_pre ih run
  subst ca
  obtain ⟨mid, h_value, h_state_mid, h_body⟩ :=
    run_body_of_run_nonpayable run
  have h_pre_mid := h_pre.state_eq h_state_mid.symm
  simp only [transferFrom] at h_body
  have h_core_lookup :
      ((weth10 dp).main :: weth10Aux)[transferFromCoreSlot]? =
        some transferFromCore := by
    simp [weth10, weth10Aux, transferFromCoreSlot]
  obtain ⟨sc, hcore, h_silent, h_bal, h_code⟩ :=
    of_run_spendCallerAllowanceThen dp 2 transferFromCoreSlot
      transferFromCore h_core_lookup h_body
  have h_pre_sc := backedPre_of_silent dp sevm.currentTarget
    h_pre_mid h_silent h_bal h_code
  exact backedPost_of_transferFromCore dp sevm.currentTarget
    rfl h_pre_sc ih h_value hcore

/-- The exact `withdrawFrom` core burns the normalized source balance and
preserves backing across the accepted value call to the raw target word. -/
theorem backedPost_of_withdrawFromCore (dp : DeployParams) (ca : Adr)
    {sevm : Sevm} {s r : Devm}
    (h_target : sevm.currentTarget = ca)
    (h_pre : (backedSpec weth10 dp).Pre ca sevm s)
    (ih : Exec.InvDepth sevm.depth ca (weth10 dp)
      ((backedSpec weth10 dp).PreWf ca) ((backedSpec weth10 dp).Post ca))
    (h_value : sevm.value = 0)
    (run : Func.Run ((weth10 dp).main :: weth10Aux) sevm s
      withdrawFromCore r) :
    (backedSpec weth10 dp).Post ca sevm r := by
  subst ca
  refine ⟨Func.preserves_nof run h_pre.side, ?_⟩
  change Stor.Weth10Inv
    (Devm.getStor r sevm.currentTarget) 0
    (Devm.getBal r sevm.currentTarget)
  have h_inv0 := h_pre.inv.1 rfl
  change Stor.Weth10Inv
    (Devm.getStor s sevm.currentTarget) sevm.value
    (Devm.getBal s sevm.currentTarget) at h_inv0
  rw [h_value] at h_inv0
  simp only [withdrawFromCore] at run
  rcases of_run_prepend (loadArgBalanceAmount 0 2) _ run with
    ⟨s1, hload, run1⟩
  rcases prefix_of_loadArgBalanceAmount 0 2 nil_pref hload with
    ⟨balance, owner, h_owner, h_balance, hp1⟩
  rcases of_run_prepend balanceTooSmall _ run1 with
    ⟨s2, hguard, run2⟩
  have hp2 :
      (balance <? Sevm.argWord sevm 2) :: balance ::
        Sevm.argWord sevm 2 :: owner :: [] <<+ s2.stack :=
    prefix_of_balanceTooSmall hp1 hguard
  have h_burn_lookup :
      ((weth10 dp).main :: weth10Aux)[burnBalanceErrorSlot]? =
        some (Func.revWith "WETH: burn amount exceeds balance") := by
    simp [weth10, weth10Aux, burnBalanceErrorSlot, burnBalanceError]
  rcases of_run_branch_call_revWith h_burn_lookup run2 with
    ⟨s3, hpopGuard, run3⟩
  have hpopStack := hpopGuard.stack
  simp only [Stack.Pop, Split, List.nil_append, List.cons_append] at hpopStack
  rw [hpopStack] at hp2
  have h_flag : (balance <? Sevm.argWord sevm 2) = 0 :=
    pref_head_unique hp2 (pref_append [0] s3.stack)
  have h_token_le : Sevm.argWord sevm 2 ≤ balance := by
    rw [← B256.not_lt]
    intro hlt
    rw [B256.ltCheck, if_pos hlt] at h_flag
    exact B256.zero_ne_one h_flag.symm
  rw [h_flag] at hp2
  have hp3 : [balance, Sevm.argWord sevm 2, owner] <<+ s3.stack :=
    cons_pref_cons_inv hp2
  have h_stor_s_s3 : Devm.getStor s = Devm.getStor s3 :=
    (Line.of_inv Devm.getStor (by line_inv) hload).trans
      ((Line.of_inv Devm.getStor (by line_inv) hguard).trans
        (PopBurn.Inv.inv hpopGuard))
  have h_bal_s_s3 : Devm.getBal s = Devm.getBal s3 :=
    (Line.of_inv Devm.getBal (by line_inv) hload).trans
      ((Line.of_inv Devm.getBal (by line_inv) hguard).trans
        (PopBurn.Inv.inv hpopGuard))
  have h_code_s_s3 :
      Devm.getCode s sevm.currentTarget =
        Devm.getCode s3 sevm.currentTarget :=
    (congrFun (Line.of_inv Devm.getCode (by line_inv) hload)
        sevm.currentTarget).trans
      ((congrFun (Line.of_inv Devm.getCode (by line_inv) hguard)
          sevm.currentTarget).trans
        (getCode_eq_of_state_eq hpopGuard.state sevm.currentTarget))
  have h_inv3 : Stor.Weth10Inv
      (Devm.getStor s3 sevm.currentTarget) 0
      (Devm.getBal s3 sevm.currentTarget) := by
    rw [← congrFun h_stor_s_s3 sevm.currentTarget,
      ← congrFun h_bal_s_s3 sevm.currentTarget]
    exact h_inv0
  have h_balance3 :
      balance = (Devm.getStor s3 sevm.currentTarget).get owner := by
    rw [h_balance, congrFun h_stor_s_s3 sevm.currentTarget]
  have h_owner_valid : ValidAdr owner := by
    rw [h_owner]
    exact normalizedAddress_valid (Sevm.argWord sevm 0)
  rcases of_run_prepend debitLoadedBalance _ run3 with
    ⟨s4, hdebit, run4⟩
  obtain ⟨h_dec, h_cover, h_flash⟩ :=
    debitLoadedBalance_storage h_owner_valid
      h_balance3 h_token_le hp3 hdebit
  let eventLine : Line :=
    addressArg 0 ++ arg 2 ++ [pushB256 0] ++ emitTransfer ++
      [swap 0, pop]
  rcases of_run_prepend eventLine _ run4 with
    ⟨s5, hevent, run5⟩
  have hp5 : Sevm.argWord sevm 2 :: [] <<+ s5.stack := by
    apply prefix_of_burnEventFromArg 0 2 nil_pref
    simpa only [eventLine] using hevent
  rcases of_run_prepend (sendValueToArg 1) _ run5 with
    ⟨s6, hsend, run6⟩
  obtain ⟨sc, g, hpCall, hcall, h_stor_s5_sc, h_bal_s5_sc,
      h_code_s5_sc⟩ :=
    of_sendValueToArg 1 hp5 hsend
  rcases of_run_next run6 with ⟨si, hiszero, run7⟩
  have h_eth_lookup :
      ((weth10 dp).main :: weth10Aux)[etherTransferErrorSlot]? =
        some (Func.revWith "WETH: Ether transfer failed") := by
    simp [weth10, weth10Aux, etherTransferErrorSlot, etherTransferError]
  rcases of_run_branch_call_revWith h_eth_lookup run7 with
    ⟨sb, hpopCall, hstop⟩
  have h_eth_le :
      Sevm.argWord sevm 2 ≤ sc.getBal sevm.currentTarget :=
    value_le_balance_of_run_call_success_guard
      hpCall hcall hiszero hpopCall
  have h_bal_s3_sc : Devm.getBal s3 = Devm.getBal sc :=
    (Line.of_inv Devm.getBal (by line_inv) hdebit).trans
      ((Line.of_inv Devm.getBal (by line_inv) hevent).trans h_bal_s5_sc)
  have h_stor_s4_sc : Devm.getStor s4 = Devm.getStor sc :=
    (Line.of_inv Devm.getStor (by line_inv) hevent).trans h_stor_s5_sc
  have h_code_s3_sc :
      Devm.getCode s3 sevm.currentTarget =
        Devm.getCode sc sevm.currentTarget :=
    (congrFun (Line.of_inv Devm.getCode (by line_inv) hdebit)
        sevm.currentTarget).trans
      ((congrFun (Line.of_inv Devm.getCode (by line_inv) hevent)
          sevm.currentTarget).trans
        (congrFun h_code_s5_sc sevm.currentTarget))
  have h_code_sc :
      some (sc.getCode sevm.currentTarget).toList =
        Prog.compile (weth10 dp) := by
    rw [← h_code_s3_sc, ← h_code_s_s3]
    exact h_pre.code
  have h_side_sc : SumNof sc.getBal := by
    rw [← h_bal_s3_sc, ← h_bal_s_s3]
    exact h_pre.side
  have h_eth_le3 :
      Sevm.argWord sevm 2 ≤ s3.getBal sevm.currentTarget := by
    rw [h_bal_s3_sc]
    exact h_eth_le
  have h_afterDebit : Stor.Weth10Inv
      (Devm.getStor s4 sevm.currentTarget) 0
      (Devm.getBal s3 sevm.currentTarget - Sevm.argWord sevm 2) :=
    Stor.Weth10Inv.withdraw h_inv3 h_dec h_cover h_eth_le3 h_flash
  have h_ready : Stor.Weth10Inv
      (Devm.getStor sc sevm.currentTarget) 0
      (sc.getBal sevm.currentTarget - Sevm.argWord sevm 2) := by
    rw [← congrFun h_stor_s4_sc sevm.currentTarget,
      ← congrFun h_bal_s3_sc sevm.currentTarget]
    exact h_afterDebit
  have h_post_call := backedPost_of_value_call dp sevm.currentTarget
    rfl ih hpCall h_code_sc h_side_sc h_eth_le h_ready hcall
  have h_stor_s6_si : Devm.getStor s6 = Devm.getStor si :=
    Line.of_inv Devm.getStor (by line_inv)
      (Line.Run.cons hiszero Line.Run.nil)
  have h_stor_si_sb : Devm.getStor si = Devm.getStor sb :=
    PopBurn.Inv.inv hpopCall
  have h_stor_sb_r : Devm.getStor sb = Devm.getStor r :=
    Func.of_inv Devm.getStor Devm.getStor (by func_inv) hstop
  have h_stor_s6_r : Devm.getStor s6 = Devm.getStor r :=
    h_stor_s6_si.trans (h_stor_si_sb.trans h_stor_sb_r)
  have h_bal_s6_si : Devm.getBal s6 = Devm.getBal si :=
    Line.of_inv Devm.getBal (by line_inv)
      (Line.Run.cons hiszero Line.Run.nil)
  have h_bal_si_sb : Devm.getBal si = Devm.getBal sb :=
    PopBurn.Inv.inv hpopCall
  have h_bal_sb_r : Devm.getBal sb = Devm.getBal r :=
    Func.of_inv Devm.getBal Devm.getBal (by func_inv) hstop
  have h_bal_s6_r : Devm.getBal s6 = Devm.getBal r :=
    h_bal_s6_si.trans (h_bal_si_sb.trans h_bal_sb_r)
  rw [← congrFun h_stor_s6_r sevm.currentTarget,
    ← congrFun h_bal_s6_r sevm.currentTarget]
  exact h_post_call.inv

/-- The exact nonpayable `withdrawFrom` selector preserves WETH10 backing,
including its self/infinite/finite allowance paths and dirty target words. -/
theorem backedSpec_withdrawFrom_funcSound (dp : DeployParams) (ca : Adr) :
    (backedSpec weth10 dp).FuncSoundNoMem ca weth10Aux
      (nonpayable withdrawFrom) := by
  intro sevm s r h_target h_pre ih run
  subst ca
  obtain ⟨mid, h_value, h_state_mid, h_body⟩ :=
    run_body_of_run_nonpayable run
  have h_pre_mid := h_pre.state_eq h_state_mid.symm
  simp only [withdrawFrom] at h_body
  have h_core_lookup :
      ((weth10 dp).main :: weth10Aux)[withdrawFromCoreSlot]? =
        some withdrawFromCore := by
    simp [weth10, weth10Aux, withdrawFromCoreSlot]
  obtain ⟨sc, hcore, h_silent, h_bal, h_code⟩ :=
    of_run_spendCallerAllowanceThen dp 2 withdrawFromCoreSlot
      withdrawFromCore h_core_lookup h_body
  have h_pre_sc := backedPre_of_silent dp sevm.currentTarget
    h_pre_mid h_silent h_bal h_code
  exact backedPost_of_withdrawFromCore dp sevm.currentTarget
    rfl h_pre_sc ih h_value hcore

/-! ## Boolean-callback backing seams -/

/-- The line-level mint prefix has the same exact storage effect as the
standalone `depositTo` endpoint. -/
theorem mintToPrefix_storage {fs : List Func} {sevm : Sevm}
    {s r : Devm} (run : Line.Run sevm s mintToPrefix r) :
    ∃ recipient : Adr,
      Increase recipient sevm.value
        (Stor.rest (Devm.getStor s sevm.currentTarget))
        (Stor.rest (Devm.getStor r sevm.currentTarget)) ∧
      (Devm.getStor r sevm.currentTarget).get flashMintedSlot =
        (Devm.getStor s sevm.currentTarget).get flashMintedSlot := by
  have hstop : Func.Run fs sevm r Func.stop r := by
    apply Func.Run.last
    simp [Linst.Run, Linst.run]
  have hrun : Func.Run fs sevm s depositTo r := by
    have prepend_stop :
        ∀ {d d' : Devm} {line : Line},
          Line.Run sevm d line d' →
          Func.Run fs sevm d' Func.stop d' →
          Func.Run fs sevm d (line +++ Func.stop) d' := by
      intro d d' line hline htail
      induction hline with
      | nil => exact htail
      | cons hi hrest ih => exact Func.Run.next hi (ih htail)
    simpa only [depositTo] using prepend_stop run hstop
  exact depositTo_storage hrun

/-- Returning a memory window changes only frame-local machine fields, never
account code. -/
theorem returnMemoryRange_preserves_code {fs : List Func} {e : Sevm}
    {s r : Devm} {i n : B256}
    (run : Func.Run fs e s (returnMemoryRange i n) r) :
    Devm.getCode s = Devm.getCode r := by
  unfold returnMemoryRange at run
  rcases of_run_prepend (pushList [n, i]) Func.ret run with
    ⟨sm, hpushes, hret⟩
  have h_code_s_sm : Devm.getCode s = Devm.getCode sm :=
    Line.of_inv Devm.getCode (by line_inv) hpushes
  have h_code_sm_r : Devm.getCode sm = Devm.getCode r := by
    cases hret with
    | last h_run =>
      exact funext fun a => (Linst.run_codeFrame h_run a).symm
  exact h_code_s_sm.trans h_code_sm_r

/-- Bubbling the preceding returndata always terminates by revert, so it has
no successful function-level run. -/
theorem not_run_bubbleRevert {fs : List Func} {e : Sevm}
    {s r : Devm} : ¬ Func.Run fs e s bubbleRevert r := by
  intro run
  simp only [bubbleRevert, Func.revReturnData] at run
  rcases of_run_next run with ⟨s1, h1, run1⟩
  rcases of_run_next run1 with ⟨s2, h2, run2⟩
  rcases of_run_next run2 with ⟨s3, h3, run3⟩
  rcases of_run_next run3 with ⟨s4, h4, run4⟩
  rcases of_run_next run4 with ⟨s5, h5, run5⟩
  rcases of_run_next run5 with ⟨s6, h6, run6⟩
  cases run6 with
  | last h_run =>
    simp only [Linst.Run, Linst.run] at h_run
    rcases Except.bind_eq_ok h_run with ⟨v1, h1, h2⟩
    rcases Except.bind_eq_ok h2 with ⟨v2, h3, h4⟩
    rcases Except.bind_eq_ok h4 with ⟨v3, h5, h6⟩
    contradiction

/-- Every successful Solidity-0.7 Boolean return decoder walk is world-state
silent.  A failed callback can only select the impossible bubbling reverter. -/
theorem boolReturn_preserves_fields (dp : DeployParams)
    {e : Sevm} {s r : Devm}
    (run : Func.Run ((weth10 dp).main :: weth10Aux) e s boolReturn r) :
    Devm.getStor s = Devm.getStor r ∧
    Devm.getBal s = Devm.getBal r ∧
    Devm.getCode s e.currentTarget = Devm.getCode r e.currentTarget := by
  simp only [boolReturn] at run
  rcases of_run_next run with ⟨s1, hiszero, run1⟩
  rcases of_run_branch run1 with
      ⟨s2, hpopCall, hcontinue⟩ |
      ⟨w, s2, s3, hnz, hpopCall, hburnCall, hbubbleCall⟩
  · rcases of_run_prepend (retdataShorterThan 32) _ hcontinue with
      ⟨s3, hshort, run3⟩
    rcases of_run_branch_rev run3 with
      ⟨s4, hpopShort, htail⟩
    have h_stor : Devm.getStor s = Devm.getStor r :=
      (Line.of_inv Devm.getStor (by line_inv)
        (Line.Run.cons hiszero Line.Run.nil)).trans
        ((PopBurn.Inv.inv hpopCall).trans
          ((Line.of_inv Devm.getStor (by line_inv) hshort).trans
            ((PopBurn.Inv.inv hpopShort).trans
              (Func.of_inv Devm.getStor Devm.getStor
                (by func_inv) htail))))
    have h_bal : Devm.getBal s = Devm.getBal r :=
      (Line.of_inv Devm.getBal (by line_inv)
        (Line.Run.cons hiszero Line.Run.nil)).trans
        ((PopBurn.Inv.inv hpopCall).trans
          ((Line.of_inv Devm.getBal (by line_inv) hshort).trans
            ((PopBurn.Inv.inv hpopShort).trans
              (Func.of_inv Devm.getBal Devm.getBal
                (by func_inv) htail))))
    let decodeLine : Line :=
      pushList [32, 0, 0] ++
        [retdatacopy, pushB256 0, mload, iszero, iszero] ++ mstoreAt 0
    rcases of_run_prepend decodeLine (returnMemoryRange 0 32) htail with
      ⟨sr, hdecode, hreturn⟩
    have h_tail_code : Devm.getCode s4 = Devm.getCode r :=
      (Line.of_inv Devm.getCode (by line_inv) hdecode).trans
        (returnMemoryRange_preserves_code hreturn)
    have h_code :
        Devm.getCode s e.currentTarget = Devm.getCode r e.currentTarget :=
      (congrFun (Line.of_inv Devm.getCode (by line_inv)
        (Line.Run.cons hiszero Line.Run.nil)) e.currentTarget).trans
        ((getCode_eq_of_state_eq hpopCall.state e.currentTarget).trans
          ((congrFun (Line.of_inv Devm.getCode (by line_inv) hshort)
            e.currentTarget).trans
            ((getCode_eq_of_state_eq hpopShort.state e.currentTarget).trans
              (congrFun h_tail_code e.currentTarget))))
    exact ⟨h_stor, h_bal, h_code⟩
  · rcases of_run_call hbubbleCall with
      ⟨f, sb, hget, hburn, hbubble⟩
    have hlookup :
        ((weth10 dp).main :: weth10Aux)[bubbleRevertSlot]? =
          some bubbleRevert := by
      simp [weth10, weth10Aux, bubbleRevertSlot]
    have hf : f = bubbleRevert := by
      rw [hlookup] at hget
      exact Option.some.inj hget.symm
    subst f
    exact absurd hbubble not_run_bubbleRevert

/-- The fixed-context tail jump into `boolReturn` is world-state silent on
every successful path. -/
theorem of_run_call_boolReturn_preserves_fields (dp : DeployParams)
    {e : Sevm} {s r : Devm}
    (run : Func.Run ((weth10 dp).main :: weth10Aux) e s
      (.call boolReturnSlot) r) :
    Devm.getStor s = Devm.getStor r ∧
    Devm.getBal s = Devm.getBal r ∧
    Devm.getCode s e.currentTarget = Devm.getCode r e.currentTarget := by
  rcases of_run_call run with
    ⟨f, sb, hget, hburn, hbool⟩
  have hlookup :
      ((weth10 dp).main :: weth10Aux)[boolReturnSlot]? =
        some boolReturn := by
    simp [weth10, weth10Aux, boolReturnSlot]
  have hf : f = boolReturn := by
    rw [hlookup] at hget
    exact Option.some.inj hget.symm
  subst f
  obtain ⟨h_stor, h_bal, h_code⟩ :=
    boolReturn_preserves_fields dp hbool
  exact ⟨(Burn.Inv.inv hburn).trans h_stor,
    (Burn.Inv.inv hburn).trans h_bal,
    (getCode_eq_of_state_eq hburn.state e.currentTarget).trans h_code⟩

/-- A successful typed Boolean callback exposes its exact zero-value `CALL`
boundary and the fixed `boolReturn` continuation.  The setup is world-state
silent; `value` is abstract so the seam is shared by deposit, approval, and
transfer callbacks. -/
theorem of_run_callBoolCallback (dp : DeployParams)
    (sel target dataArg : B256) (value : Line)
    (h_value_stor : Line.Inv Devm.getStor value)
    (h_value_bal : Line.Inv Devm.getBal value)
    (h_value_code : Line.Inv Devm.getCode value)
    {e : Sevm} {s r : Devm}
    (run : Func.Run ((weth10 dp).main :: weth10Aux) e s
      (callBoolCallback sel target dataArg value) r) :
    ∃ sc sf g inputSize xs,
      (g :: Sevm.argWord e target :: 0 :: callbackArgsOffset ::
        inputSize :: 0 :: 0 :: xs) <<+ sc.stack ∧
      Ninst.Run e sc call sf ∧
      Func.Run ((weth10 dp).main :: weth10Aux) e sf
        (.call boolReturnSlot) r ∧
      Devm.getStor s = Devm.getStor sc ∧
      Devm.getBal s = Devm.getBal sc ∧
      Devm.getCode s e.currentTarget = Devm.getCode sc e.currentTarget := by
  unfold callBoolCallback at run
  let checkLine : Line := arg target ++ [dup 0, extcodesize, iszero]
  rcases of_run_prepend checkLine _ run with
    ⟨s1, hcheck, run1⟩
  rcases of_run_branch_rev run1 with
    ⟨s2, hpopCheck, run2⟩
  rcases of_run_next run2 with
    ⟨s3, hpopTarget, run3⟩
  rcases of_run_prepend value _ run3 with
    ⟨s4, hvalueLine, run4⟩
  rcases of_run_prepend (storeTokenCallbackHead sel) _ run4 with
    ⟨s5, hhead, run5⟩
  rcases of_run_prepend (pushList [0, 0]) _ run5 with
    ⟨s6, hzeros, run6⟩
  have hp6 : (0 : B256) :: 0 :: [] <<+ s6.stack := by
    unfold pushList at hzeros
    simp only [List.map] at hzeros
    rcases Line.of_run_cons hzeros with ⟨z1, hz1, hzeros1⟩
    have hpz1 : (0 : B256) :: [] <<+ z1.stack :=
      prefix_of_push (of_run_pushB256 hz1) nil_pref
    rcases Line.of_run_cons hzeros1 with ⟨z2, hz2, hnil⟩
    cases hnil
    exact prefix_of_push (of_run_pushB256 hz2) hpz1
  rcases of_run_prepend (forwardArgTail dataArg 4) _ run6 with
    ⟨s7, htailArgs, run7⟩
  have hp7 : Sevm.tailLen e dataArg :: 0 :: 0 :: [] <<+ s7.stack :=
    (of_forwardArgTail_val hp6 htailArgs).1
  rcases of_run_prepend tokenCallbackArgsSize _ run7 with
    ⟨s8, hsize, run8⟩
  let inputSize : B256 :=
    0x84 + ((~~~ (31 : B256)) &&&
      ((31 : B256) + Sevm.tailLen e dataArg))
  have hp8 : inputSize :: 0 :: 0 :: [] <<+ s8.stack := by
    unfold tokenCallbackArgsSize at hsize
    rcases Line.of_run_cons hsize with ⟨q1, hq1, hsize1⟩
    have hpq1 :
        (31 : B256) :: Sevm.tailLen e dataArg :: 0 :: 0 :: [] <<+
          q1.stack := prefix_of_push (of_run_pushB256 hq1) hp7
    rcases Line.of_run_cons hsize1 with ⟨q2, hq2, hsize2⟩
    have hpq2 :
        ((31 : B256) + Sevm.tailLen e dataArg) :: 0 :: 0 :: [] <<+
          q2.stack := prefix_of_add hq2 hpq1
    rcases Line.of_run_cons hsize2 with ⟨q3, hq3, hsize3⟩
    have hpq3 :
        (31 : B256) :: ((31 : B256) + Sevm.tailLen e dataArg) ::
          0 :: 0 :: [] <<+ q3.stack :=
      prefix_of_push (of_run_pushB256 hq3) hpq2
    rcases Line.of_run_cons hsize3 with ⟨q4, hq4, hsize4⟩
    have hpq4 :
        (~~~ (31 : B256)) ::
          ((31 : B256) + Sevm.tailLen e dataArg) :: 0 :: 0 :: [] <<+
            q4.stack := prefix_of_not hq4 hpq3
    rcases Line.of_run_cons hsize4 with ⟨q5, hq5, hsize5⟩
    have hpq5 :
        ((~~~ (31 : B256)) &&&
          ((31 : B256) + Sevm.tailLen e dataArg)) :: 0 :: 0 :: [] <<+
            q5.stack := prefix_of_and hq5 hpq4
    rcases Line.of_run_cons hsize5 with ⟨q6, hq6, hsize6⟩
    have hpq6 :
        (0x84 : B256) ::
          ((~~~ (31 : B256)) &&&
            ((31 : B256) + Sevm.tailLen e dataArg)) :: 0 :: 0 :: [] <<+
              q6.stack := prefix_of_push (of_run_pushB256 hq6) hpq5
    rcases Line.of_run_cons hsize6 with ⟨q7, hq7, hnil⟩
    cases hnil
    exact prefix_of_add hq7 hpq6
  rcases of_run_prepend
      [pushB256 callbackArgsOffset, pushB256 0] _ run8 with
    ⟨s9, hoffsets, run9⟩
  have hp9 :
      (0 : B256) :: callbackArgsOffset :: inputSize :: 0 :: 0 :: [] <<+
        s9.stack := by
    rcases Line.of_run_cons hoffsets with ⟨o1, ho1, hoffsets1⟩
    have hpo1 :
        callbackArgsOffset :: inputSize :: 0 :: 0 :: [] <<+ o1.stack :=
      prefix_of_push (of_run_pushB256 ho1) hp8
    rcases Line.of_run_cons hoffsets1 with ⟨o2, ho2, hnil⟩
    cases hnil
    exact prefix_of_push (of_run_pushB256 ho2) hpo1
  rcases of_run_prepend (arg target) _ run9 with
    ⟨s10, htarget, run10⟩
  have hp10 :
      Sevm.argWord e target :: 0 :: callbackArgsOffset :: inputSize ::
        0 :: 0 :: [] <<+ s10.stack :=
    prefix_of_arg hp9 htarget
  rcases of_run_next run10 with
    ⟨sc, hgas, run11⟩
  rcases of_run_gas hgas with ⟨g, hpushGas⟩
  have hpCall :
      g :: Sevm.argWord e target :: 0 :: callbackArgsOffset :: inputSize ::
        0 :: 0 :: [] <<+ sc.stack :=
    prefix_of_push hpushGas hp10
  rcases of_run_next run11 with
    ⟨sf, hcall, hbool⟩
  have h_stor_s3_sc : Devm.getStor s3 = Devm.getStor sc :=
    (h_value_stor hvalueLine).trans
      ((Line.of_inv Devm.getStor (by line_inv) hhead).trans
        ((Line.of_inv Devm.getStor (by line_inv) hzeros).trans
          ((Line.of_inv Devm.getStor (by line_inv) htailArgs).trans
            ((Line.of_inv Devm.getStor (by line_inv) hsize).trans
              ((Line.of_inv Devm.getStor (by line_inv) hoffsets).trans
                ((Line.of_inv Devm.getStor (by line_inv) htarget).trans
                  (Line.of_inv Devm.getStor (by line_inv)
                    (Line.Run.cons hgas Line.Run.nil))))))))
  have h_bal_s3_sc : Devm.getBal s3 = Devm.getBal sc :=
    (h_value_bal hvalueLine).trans
      ((Line.of_inv Devm.getBal (by line_inv) hhead).trans
        ((Line.of_inv Devm.getBal (by line_inv) hzeros).trans
          ((Line.of_inv Devm.getBal (by line_inv) htailArgs).trans
            ((Line.of_inv Devm.getBal (by line_inv) hsize).trans
              ((Line.of_inv Devm.getBal (by line_inv) hoffsets).trans
                ((Line.of_inv Devm.getBal (by line_inv) htarget).trans
                  (Line.of_inv Devm.getBal (by line_inv)
                    (Line.Run.cons hgas Line.Run.nil))))))))
  have h_code_s3_sc : Devm.getCode s3 = Devm.getCode sc :=
    (h_value_code hvalueLine).trans
      ((Line.of_inv Devm.getCode (by line_inv) hhead).trans
        ((Line.of_inv Devm.getCode (by line_inv) hzeros).trans
          ((Line.of_inv Devm.getCode (by line_inv) htailArgs).trans
            ((Line.of_inv Devm.getCode (by line_inv) hsize).trans
              ((Line.of_inv Devm.getCode (by line_inv) hoffsets).trans
                ((Line.of_inv Devm.getCode (by line_inv) htarget).trans
                  (Line.of_inv Devm.getCode (by line_inv)
                    (Line.Run.cons hgas Line.Run.nil))))))))
  have h_stor_s_sc : Devm.getStor s = Devm.getStor sc :=
    (Line.of_inv Devm.getStor (by line_inv) hcheck).trans
      ((PopBurn.Inv.inv hpopCheck).trans
        ((Line.of_inv Devm.getStor (by line_inv)
          (Line.Run.cons hpopTarget Line.Run.nil)).trans h_stor_s3_sc))
  have h_bal_s_sc : Devm.getBal s = Devm.getBal sc :=
    (Line.of_inv Devm.getBal (by line_inv) hcheck).trans
      ((PopBurn.Inv.inv hpopCheck).trans
        ((Line.of_inv Devm.getBal (by line_inv)
          (Line.Run.cons hpopTarget Line.Run.nil)).trans h_bal_s3_sc))
  have h_code_s_sc :
      Devm.getCode s e.currentTarget = Devm.getCode sc e.currentTarget :=
    (congrFun (Line.of_inv Devm.getCode (by line_inv) hcheck)
        e.currentTarget).trans
      ((getCode_eq_of_state_eq hpopCheck.state e.currentTarget).trans
        ((congrFun (Line.of_inv Devm.getCode (by line_inv)
          (Line.Run.cons hpopTarget Line.Run.nil)) e.currentTarget).trans
            (congrFun h_code_s3_sc e.currentTarget)))
  exact ⟨sc, sf, g, inputSize, [], hpCall, hcall, hbool,
    h_stor_s_sc, h_bal_s_sc, h_code_s_sc⟩

private theorem b256_sub_zero (x : B256) : x - 0 = x := by
  rcases x with ⟨xh, xl⟩
  change (((xh - (0 : B128)) -
    (if xl < (0 : B128) then (1 : B128) else 0),
    xl - (0 : B128))) = (xh, xl)
  have h : ¬ xl < (0 : B128) := by
    intro h
    rcases h with h | ⟨_, h⟩
    · exact UInt64.not_lt_zero h
    · exact UInt64.not_lt_zero h
  rw [if_neg h, B128.sub_zero, B128.sub_zero, B128.sub_zero]

private theorem b256_zero_le (x : B256) : (0 : B256) ≤ x := by
  rw [← B256.not_lt]
  intro h
  have hn := B256.toNat_lt_toNat h
  rw [B256.toNat_zero] at hn
  omega

/-- A successful exact Boolean callback tail preserves WETH10 backing once its
zero-value `CALL` setup state already satisfies the ordinary invariant. -/
theorem backedPost_of_run_callBoolCallback
    (dp : DeployParams) (ca : Adr)
    {sevm : Sevm} {s r : Devm} {sel target dataArg : B256}
    {value : Line}
    (h_target : sevm.currentTarget = ca)
    (ih : Exec.InvDepth sevm.depth ca (weth10 dp)
      ((backedSpec weth10 dp).PreWf ca) ((backedSpec weth10 dp).Post ca))
    (h_code : some (s.getCode ca).toList = Prog.compile (weth10 dp))
    (h_side : SumNof s.getBal)
    (h_inv : Stor.Weth10Inv (Devm.getStor s ca) 0 (s.getBal ca))
    (h_value_stor : Line.Inv Devm.getStor value)
    (h_value_bal : Line.Inv Devm.getBal value)
    (h_value_code : Line.Inv Devm.getCode value)
    (run : Func.Run ((weth10 dp).main :: weth10Aux) sevm s
      (callBoolCallback sel target dataArg value) r) :
    (backedSpec weth10 dp).Post ca sevm r := by
  obtain ⟨sc, sf, g, inputSize, xs, hpCall, hcall, hbool,
      h_stor_s_sc, h_bal_s_sc, h_code_s_sc⟩ :=
    of_run_callBoolCallback dp sel target dataArg value
      h_value_stor h_value_bal h_value_code run
  have h_inv_sc : Stor.Weth10Inv
      (Devm.getStor sc ca) 0 (sc.getBal ca) := by
    rw [← congrFun h_stor_s_sc ca, ← congrFun h_bal_s_sc ca]
    exact h_inv
  have h_code_sc :
      some (sc.getCode ca).toList = Prog.compile (weth10 dp) := by
    rw [← h_target, ← h_code_s_sc, h_target]
    exact h_code
  have h_side_sc : SumNof sc.getBal := by
    rw [← h_bal_s_sc]
    exact h_side
  have h_inv_ready : Stor.Weth10Inv
      (Devm.getStor sc ca) 0 (sc.getBal ca - 0) := by
    rw [b256_sub_zero]
    exact h_inv_sc
  have h_post_call := backedPost_of_value_call dp ca
    h_target ih hpCall h_code_sc h_side_sc (b256_zero_le _) h_inv_ready hcall
  obtain ⟨h_stor_tail, h_bal_tail, h_code_tail⟩ :=
    of_run_call_boolReturn_preserves_fields dp hbool
  refine ⟨?_, ?_⟩
  · rw [← h_bal_tail]
    exact h_post_call.side
  · change Stor.Weth10Inv
      (Devm.getStor r ca) 0 (Devm.getBal r ca)
    rw [← congrFun h_stor_tail ca, ← congrFun h_bal_tail ca]
    exact h_post_call.inv

/-- The exact payable `depositToAndCall` selector preserves WETH10 backing.
The mint prefix establishes backing before the arbitrary zero-value callback;
the fixed Boolean decoder is world-state silent on every successful path. -/
theorem backedSpec_depositToAndCall_funcSound
    (dp : DeployParams) (ca : Adr) :
    (backedSpec weth10 dp).FuncSoundNoMem ca weth10Aux depositToAndCall := by
  intro sevm s r h_target h_pre ih run
  subst ca
  simp only [depositToAndCall] at run
  rcases of_run_prepend mintToPrefix _ run with
    ⟨smint, hmint, hcallback⟩
  obtain ⟨recipient, h_inc, h_flash⟩ :=
    mintToPrefix_storage
      (fs := (weth10 dp).main :: weth10Aux) hmint
  have h_bal_s_mint : Devm.getBal s = Devm.getBal smint :=
    Line.of_inv Devm.getBal (by line_inv) hmint
  have h_code_s_mint :
      Devm.getCode s sevm.currentTarget =
        Devm.getCode smint sevm.currentTarget :=
    congrFun (Line.of_inv Devm.getCode (by line_inv) hmint)
      sevm.currentTarget
  have h_inv0 : Stor.Weth10Inv
      (Devm.getStor s sevm.currentTarget) sevm.value
      (Devm.getBal s sevm.currentTarget) :=
    h_pre.inv.1 rfl
  have h_inv_mint : Stor.Weth10Inv
      (Devm.getStor smint sevm.currentTarget) 0
      (Devm.getBal smint sevm.currentTarget) := by
    rw [← congrFun h_bal_s_mint sevm.currentTarget]
    exact Stor.Weth10Inv.deposit h_inv0 h_inc h_flash
  refine backedPost_of_run_callBoolCallback dp sevm.currentTarget
    rfl ih ?_ ?_ h_inv_mint (by line_inv) (by line_inv) (by line_inv)
      hcallback
  · rw [← h_code_s_mint]
    exact h_pre.code
  · rw [← h_bal_s_mint]
    exact h_pre.side

/-- The exact nonpayable `approveAndCall` selector preserves WETH10 backing.
Its tagged allowance write is invariant-silent before the arbitrary zero-value
callback. -/
theorem backedSpec_approveAndCall_funcSound
    (dp : DeployParams) (ca : Adr) :
    (backedSpec weth10 dp).FuncSoundNoMem ca weth10Aux
      (nonpayable approveAndCall) := by
  intro sevm s r h_target h_pre ih run
  subst ca
  obtain ⟨mid, h_value, h_state_mid, h_body⟩ :=
    run_body_of_run_nonpayable run
  have h_pre_mid := h_pre.state_eq h_state_mid.symm
  simp only [approveAndCall] at h_body
  rcases of_run_prepend approvePrefix _ h_body with
    ⟨sapprove, happrove, hcallback⟩
  have h_silent := approvePrefix_storage_silent happrove
  have h_bal_mid_approve : Devm.getBal mid = Devm.getBal sapprove :=
    Line.of_inv Devm.getBal (by line_inv) happrove
  have h_code_mid_approve :
      Devm.getCode mid sevm.currentTarget =
        Devm.getCode sapprove sevm.currentTarget :=
    congrFun (Line.of_inv Devm.getCode (by line_inv) happrove)
      sevm.currentTarget
  have h_inv_mid : Stor.Weth10Inv
      (Devm.getStor mid sevm.currentTarget) 0
      (Devm.getBal mid sevm.currentTarget) := by
    have h := h_pre_mid.inv.1 rfl
    change Stor.Weth10Inv
      (Devm.getStor mid sevm.currentTarget) sevm.value
      (Devm.getBal mid sevm.currentTarget) at h
    simpa only [h_value] using h
  have h_inv_approve : Stor.Weth10Inv
      (Devm.getStor sapprove sevm.currentTarget) 0
      (Devm.getBal sapprove sevm.currentTarget) := by
    rw [← congrFun h_bal_mid_approve sevm.currentTarget]
    exact h_inv_mid.silent h_silent
  refine backedPost_of_run_callBoolCallback dp sevm.currentTarget
    rfl ih ?_ ?_ h_inv_approve (by line_inv) (by line_inv) (by line_inv)
      hcallback
  · rw [← h_code_mid_approve]
    exact h_pre_mid.code
  · rw [← h_bal_mid_approve]
    exact h_pre_mid.side

/-- The exact nonpayable `transferAndCall` selector preserves WETH10 backing.
Both runtime transfer branches establish backing before entering the arbitrary
zero-value Boolean callback. -/
theorem backedSpec_transferAndCall_funcSound
    (dp : DeployParams) (ca : Adr) :
    (backedSpec weth10 dp).FuncSoundNoMem ca weth10Aux
      (nonpayable transferAndCall) := by
  intro sevm s r h_target h_pre ih run
  subst ca
  obtain ⟨mid, h_value, h_state_mid, h_body⟩ :=
    run_body_of_run_nonpayable run
  have h_pre_mid := h_pre.state_eq h_state_mid.symm
  simp only [transferAndCall, transferThen] at h_body
  rcases of_run_prepend (arg 0) _ h_body with
    ⟨s1, harg, run1⟩
  have hp1 : Sevm.argWord sevm 0 :: [] <<+ s1.stack :=
    prefix_of_arg nil_pref harg
  rcases of_run_next run1 with ⟨s2, hiszero, run2⟩
  have hp2 : (Sevm.argWord sevm 0 =? 0) :: [] <<+ s2.stack :=
    prefix_of_iszero hiszero hp1
  rcases of_run_branch run2 with
      ⟨s3, hpop, hnonzero⟩ |
      ⟨w, s3, s4, hnz, hpop, hburn, hzero⟩
  · have h_stor_mid_s3 : Devm.getStor mid = Devm.getStor s3 :=
      (Line.of_inv Devm.getStor (by line_inv) harg).trans
        ((Line.of_inv Devm.getStor (by line_inv)
          (Line.Run.cons hiszero Line.Run.nil)).trans
            (PopBurn.Inv.inv hpop))
    have h_bal_mid_s3 : Devm.getBal mid = Devm.getBal s3 :=
      (Line.of_inv Devm.getBal (by line_inv) harg).trans
        ((Line.of_inv Devm.getBal (by line_inv)
          (Line.Run.cons hiszero Line.Run.nil)).trans
            (PopBurn.Inv.inv hpop))
    have h_code_mid_s3 :
        Devm.getCode mid sevm.currentTarget =
          Devm.getCode s3 sevm.currentTarget :=
      (congrFun (Line.of_inv Devm.getCode (by line_inv) harg)
          sevm.currentTarget).trans
        ((congrFun (Line.of_inv Devm.getCode (by line_inv)
            (Line.Run.cons hiszero Line.Run.nil))
            sevm.currentTarget).trans
          (getCode_eq_of_state_eq hpop.state sevm.currentTarget))
    have h_pre3 := h_pre_mid.of_eqs h_code_mid_s3.symm
      h_bal_mid_s3.symm
      (congrFun h_stor_mid_s3.symm sevm.currentTarget)
    obtain ⟨snext, h_pre_next, hcallback⟩ :=
      backedPre_of_transferNonzeroThen dp sevm.currentTarget
        rfl h_pre3 h_value hnonzero
    have h_inv_next := h_pre_next.inv.1 rfl
    change Stor.Weth10Inv
      (Devm.getStor snext sevm.currentTarget) sevm.value
      (Devm.getBal snext sevm.currentTarget) at h_inv_next
    rw [h_value] at h_inv_next
    exact backedPost_of_run_callBoolCallback dp sevm.currentTarget
      rfl ih h_pre_next.code h_pre_next.side h_inv_next
      (by line_inv) (by line_inv) (by line_inv) hcallback
  · have h_stor_mid_s4 : Devm.getStor mid = Devm.getStor s4 :=
      (Line.of_inv Devm.getStor (by line_inv) harg).trans
        ((Line.of_inv Devm.getStor (by line_inv)
          (Line.Run.cons hiszero Line.Run.nil)).trans
            ((PopBurn.Inv.inv hpop).trans (Burn.Inv.inv hburn)))
    have h_bal_mid_s4 : Devm.getBal mid = Devm.getBal s4 :=
      (Line.of_inv Devm.getBal (by line_inv) harg).trans
        ((Line.of_inv Devm.getBal (by line_inv)
          (Line.Run.cons hiszero Line.Run.nil)).trans
            ((PopBurn.Inv.inv hpop).trans (Burn.Inv.inv hburn)))
    have h_code_mid_s4 :
        Devm.getCode mid sevm.currentTarget =
          Devm.getCode s4 sevm.currentTarget :=
      (congrFun (Line.of_inv Devm.getCode (by line_inv) harg)
          sevm.currentTarget).trans
        ((congrFun (Line.of_inv Devm.getCode (by line_inv)
            (Line.Run.cons hiszero Line.Run.nil))
            sevm.currentTarget).trans
          ((getCode_eq_of_state_eq hpop.state sevm.currentTarget).trans
            (getCode_eq_of_state_eq hburn.state sevm.currentTarget)))
    have h_pre4 := h_pre_mid.of_eqs h_code_mid_s4.symm
      h_bal_mid_s4.symm
      (congrFun h_stor_mid_s4.symm sevm.currentTarget)
    obtain ⟨snext, h_pre_next, hcallback⟩ :=
      backedPre_of_transferZeroThen dp sevm.currentTarget
        rfl h_pre4 ih h_value hzero
    have h_inv_next := h_pre_next.inv.1 rfl
    change Stor.Weth10Inv
      (Devm.getStor snext sevm.currentTarget) sevm.value
      (Devm.getBal snext sevm.currentTarget) at h_inv_next
    rw [h_value] at h_inv_next
    exact backedPost_of_run_callBoolCallback dp sevm.currentTarget
      rfl ih h_pre_next.code h_pre_next.side h_inv_next
      (by line_inv) (by line_inv) (by line_inv) hcallback

/-! ## Flash-counter floor closure

The backing invariant intentionally forgets the exact flash counter at a
successful callback boundary.  Flash settlement needs one more fact: the
outer loan remains included in that counter while arbitrary borrower code is
running.  The auxiliary spec below carries only that lower bound.  It does not
change `backedSpec`; it closes independently over the same exact dispatcher
and is consumed by the final backing proof for `flashLoan`. -/

/-- The runtime flash cap together with a lower bound on WETH10's outstanding
flash-minted counter.  The cap is essential: it rules out modular wrap in a
nested flash mint before the runtime's total-limit check. -/
def Stor.FlashFloor (floor : B256) (s : Stor) : Prop :=
  (s.get flashMintedSlot).toNat ≤ maxFlashMinted ∧
    floor ≤ s.get flashMintedSlot

/-- The storage-only auxiliary contract spec used to retain an outer flash
loan's amount through arbitrary reentrant WETH10 executions. -/
def flashFloorSpec (dp : DeployParams) (floor : B256) : ContractSpec where
  prog := weth10 dp
  Inv := fun s _ _ => Stor.FlashFloor floor s
  Side := fun _ => True
  inv_forget := id
  inv_mono := fun h _ => h
  inv_recv := fun h _ => h
  side_le := fun _ _ => trivial
  side_transfer := fun _ _ => trivial
  side_addBal := fun _ _ => trivial
  inv_transfer := by
    intro st st' caller callee ca wad v h_sub h_ne _ h_inv
    show Stor.FlashFloor floor _
    have h_stor : (st'.addBal callee wad).getStor ca = st.getStor ca := by
      rcases State.of_subBal h_sub with ⟨-, h_st'⟩
      show ((st'.setBal callee _).get ca).stor = (st.get ca).stor
      rw [State.setBal_get_stor, h_st', State.setBal_get_stor]
    rw [h_stor]
    exact h_inv
  inv_recv_transfer := by
    intro st st' caller ca wad h_sub h_ne _ h_inv
    show Stor.FlashFloor floor _
    have h_stor : (st'.addBal ca wad).getStor ca = st.getStor ca := by
      rcases State.of_subBal h_sub with ⟨-, h_st'⟩
      show ((st'.setBal ca _).get ca).stor = (st.get ca).stor
      rw [State.setBal_get_stor, h_st', State.setBal_get_stor]
    rw [h_stor]
    exact h_inv
  inv_addBal := by
    intro w ca a val v _ _ h_inv
    show Stor.FlashFloor floor _
    have h_stor : (w.addBal a val).getStor ca = w.getStor ca := by
      show ((w.setBal a _).get ca).stor = (w.get ca).stor
      rw [State.setBal_get_stor]
    rw [h_stor]
    exact h_inv

/-- Exact flash-slot preservation for a body in WETH10's runtime context. -/
def FlashStable (dp : DeployParams) (f : Func) : Prop :=
  ∀ {sevm : Sevm} {s r : Devm},
    Func.Run ((weth10 dp).main :: weth10Aux) sevm s f r →
    (Devm.getStor r sevm.currentTarget).get flashMintedSlot =
      (Devm.getStor s sevm.currentTarget).get flashMintedSlot

/-- A flash-stable body satisfies every flash-floor `FuncSoundNoMem`
obligation. -/
theorem flashFloor_funcSound_of_stable
    (dp : DeployParams) (floor : B256) (ca : Adr) {f : Func}
    (hstable : FlashStable dp f) :
    (flashFloorSpec dp floor).FuncSoundNoMem ca weth10Aux f := by
  intro sevm s r h_target h_pre _ run
  subst ca
  refine ⟨trivial, ?_⟩
  change Stor.FlashFloor floor (Devm.getStor r sevm.currentTarget)
  have hfloor := h_pre.inv.1 rfl
  change Stor.FlashFloor floor
    (Devm.getStor s sevm.currentTarget) at hfloor
  unfold Stor.FlashFloor at hfloor ⊢
  rw [hstable run]
  exact hfloor

/-- A whole-storage invariant is sufficient for flash-slot stability. -/
theorem FlashStable.of_inv (dp : DeployParams) {f : Func}
    (h_inv : Func.Inv Devm.getStor Devm.getStor f) :
    FlashStable dp f := by
  intro sevm s r run
  have hs : Devm.getStor s = Devm.getStor r :=
    Func.of_inv Devm.getStor Devm.getStor h_inv run
  rw [← congrFun hs sevm.currentTarget]

/-- Flash stability lifts through WETH10's nonpayable wrapper. -/
theorem FlashStable.nonpayable (dp : DeployParams) {body : Func}
    (hbody : FlashStable dp body) :
    FlashStable dp (nonpayable body) := by
  intro sevm s r run
  rcases run_body_of_run_nonpayable run with
    ⟨mid, _, h_state, hrun⟩
  have h_stor : Devm.getStor s sevm.currentTarget =
      Devm.getStor mid sevm.currentTarget := by
    change (s.state.get sevm.currentTarget).stor =
      (mid.state.get sevm.currentTarget).stor
    rw [h_state]
  exact (hbody hrun).trans (congrArg (fun st => st.get flashMintedSlot)
    h_stor).symm

/-- A body-level floor proof lifts through the state-equivalent nonpayable
entry wrapper while retaining the same deeper-frame hypothesis. -/
theorem flashFloor_nonpayable_funcSound_of_body
    (dp : DeployParams) (floor : B256) (ca : Adr) {body : Func}
    (hbody : (flashFloorSpec dp floor).FuncSoundNoMem ca weth10Aux body) :
    (flashFloorSpec dp floor).FuncSoundNoMem ca weth10Aux
      (nonpayable body) := by
  intro sevm s r h_target h_pre ih run
  rcases run_body_of_run_nonpayable run with
    ⟨mid, _, h_state, hrun⟩
  exact hbody h_target (h_pre.state_eq h_state.symm) ih hrun

/-- An arbitrary value `CALL` preserves a flash-counter floor.  Value transfer
never changes storage; if the child reenters WETH10, the auxiliary spec's
deeper-frame hypothesis supplies exactly the retained floor. -/
theorem flashFloorPost_of_value_call
    (dp : DeployParams) (floor : B256) (ca : Adr)
    {sevm : Sevm} {s sf : Devm} {g c v ii is oi os : B256}
    {xs : Stack}
    (h_target : sevm.currentTarget = ca)
    (ih : Exec.InvDepth sevm.depth ca (weth10 dp)
      ((flashFloorSpec dp floor).PreWf ca)
      ((flashFloorSpec dp floor).Post ca))
    (hp : (g :: c :: v :: ii :: is :: oi :: os :: xs) <<+ s.stack)
    (h_code : some (s.getCode ca).toList = Prog.compile (weth10 dp))
    (h_floor : Stor.FlashFloor floor (Devm.getStor s ca))
    (h_run : Ninst.Run sevm s call sf) :
    (flashFloorSpec dp floor).Post ca sevm sf := by
  rcases of_run_call_val_with_depth hp h_run with
    ⟨_, h_world⟩ |
      ⟨parent, child, xl, delegated, na, code, avail, h_depth,
        h_stack, h_parent_state, h_parent_memory, h_delegation,
        h_fill, h_pm, h_child_clean, h_resume, h_sf_state,
        h_returnData, h_memory, h_sf_stack⟩
  · refine ⟨trivial, ?_⟩
    change Stor.FlashFloor floor (Devm.getStor sf ca)
    rw [← h_world.getStor ca]
    exact h_floor
  · let childMsg :=
      callMsg sevm parent
        (min g.toNat (except64th avail) +
          (if v.toNat = 0 then 0 else gCallStipend))
        v sevm.currentTarget c.toAdr na true false
        ((s.memory.read ii.toNat is.toNat).1) code delegated
    change ProcessMessage childMsg xl (.ok child) at h_pm
    have hc_state : childMsg.benv.state = s.state := by
      change parent.state = s.state
      exact h_parent_state
    have hc_stv : childMsg.shouldTransferValue = true := rfl
    have hc_caller : childMsg.caller = ca := by
      change sevm.currentTarget = ca
      exact h_target
    have hc_value : childMsg.value = v := rfl
    have hc_target : childMsg.currentTarget = c.toAdr := rfl
    have hc_codeAddress : childMsg.codeAddress = some na := rfl
    obtain ⟨r0, hbody, hset⟩ := ProcessMessage.iff_body.mp h_pm
    unfold FrameBody at hbody
    rcases h_bt : childMsg.benvAfterTransfer with e | benv <;>
      rw [h_bt] at hbody
    · rw [hbody.2, processMessage.settle_error] at hset
      cases hset
    have h_exec : ExecuteCode (childMsg.withBenv benv) xl r0 := hbody
    rcases of_benvAfterTransfer hc_stv h_bt with
      ⟨st_mid, h_sub, h_benv⟩
    rw [hc_state, hc_caller, hc_value] at h_sub
    have h_benv_state :
        benv.state = st_mid.addBal c.toAdr v := by
      rw [h_benv, hc_target, hc_value]
      rfl
    rcases of_state_transfer_fields (callee := c.toAdr) h_sub with
      ⟨h_t_stor, h_t_code, h_le, h_t_self, h_t_ne⟩
    have h_pre : (flashFloorSpec dp floor).Pre ca
        (initSevm (childMsg.withBenv benv))
        (initDevm (childMsg.withBenv benv)) := by
      refine ⟨?_, trivial, ?_, ?_⟩
      · show some (benv.state.getCode ca).toList =
          Prog.compile (weth10 dp)
        rw [h_benv_state]
        change some ((st_mid.addBal c.toAdr v).get ca).code.toList =
          Prog.compile (weth10 dp)
        rw [h_t_code ca]
        exact h_code
      · intro _
        change Stor.FlashFloor floor (benv.state.getStor ca)
        rw [h_benv_state]
        change Stor.FlashFloor floor
          ((st_mid.addBal c.toAdr v).get ca).stor
        rw [h_t_stor ca]
        exact h_floor
      · intro _
        change Stor.FlashFloor floor (benv.state.getStor ca)
        rw [h_benv_state]
        change Stor.FlashFloor floor
          ((st_mid.addBal c.toAdr v).get ca).stor
        rw [h_t_stor ca]
        exact h_floor
    obtain ⟨evm2, h_r0, h_settle⟩ := processMessage.settle_ok_cases hset.symm
    subst h_r0
    rcases h_settle with ⟨h_err2, h_eq⟩ | ⟨h_err2, h_eq_child⟩
    · have : child.error.isSome = true := by
        rw [← h_eq]
        exact h_err2
      simp [h_child_clean] at this
    rw [h_eq_child] at h_exec h_err2
    have h_child_post : (flashFloorSpec dp floor).Post ca
        (initSevm (childMsg.withBenv benv)) child := by
      have hc_codeAddress' :
          (childMsg.withBenv benv).codeAddress = some na :=
        hc_codeAddress
      rcases of_executeCode_someCode hc_codeAddress' h_exec with
        ⟨h_precompile, h_xl_none, h_handle⟩ |
        ⟨h_precompile, exn, h_xl_some, h_handle⟩
      · have h_child_state :
            child.state = (initDevm (childMsg.withBenv benv)).state :=
          state_of_executePrecomp_ok h_handle h_err2
        exact (flashFloorSpec dp floor).post_of_pre
          (h_pre.state_eq h_child_state)
      · have h_exn : exn = .ok child :=
          exec_ok_of_handleError h_handle h_err2
        rw [h_xl_some, h_exn] at h_fill
        obtain ⟨h_exec_child⟩ := h_fill
        have h_at : Prog.At (weth10 dp) ca 0
            (initSevm (childMsg.withBenv benv))
            (initDevm (childMsg.withBenv benv)) := by
          refine ⟨h_pre.code, ?_⟩
          intro h_child_target
          refine ⟨?_, rfl⟩
          have h_to_ca : c.toAdr = ca :=
            hc_target.symm.trans h_child_target
          change some code.toList = Prog.compile (weth10 dp)
          rcases h_delegation with
            ⟨h_none, _, h_code_self, h_not_delegated⟩ |
            ⟨d, h_some, _, h_code_delegated, h_delegated⟩
          · rw [h_code_self, h_to_ca]
            exact h_code
          · exfalso
            have h_not : ¬ isValidDelegation (s.getCode ca) :=
              not_delegation_of_compile h_code
            apply h_not
            unfold getDelegatedCodeAddress at h_some
            split at h_some
            · rename_i h_valid
              rw [h_to_ca] at h_valid
              exact h_valid
            · cases h_some
        have h_depth_lt :
            (initSevm (childMsg.withBenv benv)).depth < sevm.depth := by
          change sevm.depth - 1 < sevm.depth
          omega
        exact ih 0
          (initSevm (childMsg.withBenv benv))
          (initDevm (childMsg.withBenv benv))
          (.ok child) h_exec_child h_depth_lt h_at
          ⟨h_pre, fun _ => Mem.wf_empty⟩
    refine ⟨trivial, ?_⟩
    change Stor.FlashFloor floor (Devm.getStor sf ca)
    have h_stor : Devm.getStor sf ca = Devm.getStor child ca :=
      getStor_eq_of_state_eq h_sf_state ca
    rw [h_stor]
    exact h_child_post.inv

/-! ### Flash-stable non-reentrant leaves -/

theorem flashFloorSpec_receiveEther_funcSound
    (dp : DeployParams) (floor : B256) (ca : Adr) :
    (flashFloorSpec dp floor).FuncSoundNoMem ca weth10Aux receiveEther := by
  apply flashFloor_funcSound_of_stable dp floor ca
  intro sevm s r run
  exact (mintCaller_storage (by
    simpa only [receiveEther] using run)).2

theorem flashFloorSpec_deposit_funcSound
    (dp : DeployParams) (floor : B256) (ca : Adr) :
    (flashFloorSpec dp floor).FuncSoundNoMem ca weth10Aux deposit := by
  apply flashFloor_funcSound_of_stable dp floor ca
  intro sevm s r run
  exact (mintCaller_storage (by simpa only [deposit] using run)).2

theorem flashFloorSpec_approve_funcSound
    (dp : DeployParams) (floor : B256) (ca : Adr) :
    (flashFloorSpec dp floor).FuncSoundNoMem ca weth10Aux
      (nonpayable approve) := by
  apply flashFloor_funcSound_of_stable dp floor ca
  apply FlashStable.nonpayable dp
  intro sevm s r run
  exact (approve_storage_silent run).2

theorem flashFloorSpec_depositTo_funcSound
    (dp : DeployParams) (floor : B256) (ca : Adr) :
    (flashFloorSpec dp floor).FuncSoundNoMem ca weth10Aux depositTo := by
  apply flashFloor_funcSound_of_stable dp floor ca
  intro sevm s r run
  exact (depositTo_storage run).choose_spec.2

theorem flashFloorSpec_name_funcSound
    (dp : DeployParams) (floor : B256) (ca : Adr) :
    (flashFloorSpec dp floor).FuncSoundNoMem ca weth10Aux
      (nonpayable name) :=
  flashFloor_funcSound_of_stable dp floor ca
    (FlashStable.nonpayable dp (FlashStable.of_inv dp (by func_inv)))

theorem flashFloorSpec_totalSupply_funcSound
    (dp : DeployParams) (floor : B256) (ca : Adr) :
    (flashFloorSpec dp floor).FuncSoundNoMem ca weth10Aux
      (nonpayable totalSupply) :=
  flashFloor_funcSound_of_stable dp floor ca
    (FlashStable.nonpayable dp (FlashStable.of_inv dp (by func_inv)))

theorem flashFloorSpec_permitTypehash_funcSound
    (dp : DeployParams) (floor : B256) (ca : Adr) :
    (flashFloorSpec dp floor).FuncSoundNoMem ca weth10Aux
      (nonpayable permitTypehash) :=
  flashFloor_funcSound_of_stable dp floor ca
    (FlashStable.nonpayable dp (FlashStable.of_inv dp (by func_inv)))

theorem flashFloorSpec_decimals_funcSound
    (dp : DeployParams) (floor : B256) (ca : Adr) :
    (flashFloorSpec dp floor).FuncSoundNoMem ca weth10Aux
      (nonpayable decimals) :=
  flashFloor_funcSound_of_stable dp floor ca
    (FlashStable.nonpayable dp (FlashStable.of_inv dp (by func_inv)))

theorem flashFloorSpec_domainSeparator_funcSound
    (dp : DeployParams) (floor : B256) (ca : Adr) :
    (flashFloorSpec dp floor).FuncSoundNoMem ca weth10Aux
      (nonpayable (domainSeparator dp)) := by
  apply flashFloor_funcSound_of_stable dp floor ca
  apply FlashStable.nonpayable dp
  apply FlashStable.of_inv dp
  unfold domainSeparator returnDeployWord pushDeployWord
  func_inv

theorem flashFloorSpec_maxFlashLoan_funcSound
    (dp : DeployParams) (floor : B256) (ca : Adr) :
    (flashFloorSpec dp floor).FuncSoundNoMem ca weth10Aux
      (nonpayable maxFlashLoan) :=
  flashFloor_funcSound_of_stable dp floor ca
    (FlashStable.nonpayable dp (FlashStable.of_inv dp (by func_inv)))

theorem flashFloorSpec_balanceOf_funcSound
    (dp : DeployParams) (floor : B256) (ca : Adr) :
    (flashFloorSpec dp floor).FuncSoundNoMem ca weth10Aux
      (nonpayable balanceOfEndpoint) :=
  flashFloor_funcSound_of_stable dp floor ca
    (FlashStable.nonpayable dp (FlashStable.of_inv dp (by func_inv)))

theorem flashFloorSpec_nonces_funcSound
    (dp : DeployParams) (floor : B256) (ca : Adr) :
    (flashFloorSpec dp floor).FuncSoundNoMem ca weth10Aux
      (nonpayable nonces) :=
  flashFloor_funcSound_of_stable dp floor ca
    (FlashStable.nonpayable dp (FlashStable.of_inv dp (by func_inv)))

theorem flashFloorSpec_callbackSuccess_funcSound
    (dp : DeployParams) (floor : B256) (ca : Adr) :
    (flashFloorSpec dp floor).FuncSoundNoMem ca weth10Aux
      (nonpayable callbackSuccess) :=
  flashFloor_funcSound_of_stable dp floor ca
    (FlashStable.nonpayable dp (FlashStable.of_inv dp (by func_inv)))

theorem flashFloorSpec_flashMinted_funcSound
    (dp : DeployParams) (floor : B256) (ca : Adr) :
    (flashFloorSpec dp floor).FuncSoundNoMem ca weth10Aux
      (nonpayable flashMinted) :=
  flashFloor_funcSound_of_stable dp floor ca
    (FlashStable.nonpayable dp (FlashStable.of_inv dp (by func_inv)))

theorem flashFloorSpec_symbol_funcSound
    (dp : DeployParams) (floor : B256) (ca : Adr) :
    (flashFloorSpec dp floor).FuncSoundNoMem ca weth10Aux
      (nonpayable symbol) :=
  flashFloor_funcSound_of_stable dp floor ca
    (FlashStable.nonpayable dp (FlashStable.of_inv dp (by func_inv)))

theorem flashFloorSpec_deploymentChainId_funcSound
    (dp : DeployParams) (floor : B256) (ca : Adr) :
    (flashFloorSpec dp floor).FuncSoundNoMem ca weth10Aux
      (nonpayable (deploymentChainId dp)) := by
  apply flashFloor_funcSound_of_stable dp floor ca
  apply FlashStable.nonpayable dp
  apply FlashStable.of_inv dp
  unfold deploymentChainId returnDeployWord pushDeployWord
  func_inv

theorem flashFloorSpec_allowance_funcSound
    (dp : DeployParams) (floor : B256) (ca : Adr) :
    (flashFloorSpec dp floor).FuncSoundNoMem ca weth10Aux
      (nonpayable allowance) :=
  flashFloor_funcSound_of_stable dp floor ca
    (FlashStable.nonpayable dp (FlashStable.of_inv dp (by func_inv)))

theorem flashFloorSpec_flashFee_funcSound
    (dp : DeployParams) (floor : B256) (ca : Adr) :
    (flashFloorSpec dp floor).FuncSoundNoMem ca weth10Aux
      (nonpayable flashFee) := by
  apply flashFloor_funcSound_of_stable dp floor ca
  apply FlashStable.nonpayable dp
  intro sevm s r run
  have hs := (run_flashFee_observations_eq dp run).1
  rw [← congrFun hs sevm.currentTarget]

/-! ### Reentrant callback closure -/

/-- The exact Boolean callback tail retains a flash floor across its
zero-value external call and its world-state-silent decoder. -/
theorem flashFloorPost_of_run_callBoolCallback
    (dp : DeployParams) (floor : B256) (ca : Adr)
    {sevm : Sevm} {s r : Devm} {sel target dataArg : B256}
    {value : Line}
    (h_target : sevm.currentTarget = ca)
    (ih : Exec.InvDepth sevm.depth ca (weth10 dp)
      ((flashFloorSpec dp floor).PreWf ca)
      ((flashFloorSpec dp floor).Post ca))
    (h_code : some (s.getCode ca).toList = Prog.compile (weth10 dp))
    (h_floor : Stor.FlashFloor floor (Devm.getStor s ca))
    (h_value_stor : Line.Inv Devm.getStor value)
    (h_value_bal : Line.Inv Devm.getBal value)
    (h_value_code : Line.Inv Devm.getCode value)
    (run : Func.Run ((weth10 dp).main :: weth10Aux) sevm s
      (callBoolCallback sel target dataArg value) r) :
    (flashFloorSpec dp floor).Post ca sevm r := by
  obtain ⟨sc, sf, g, inputSize, xs, hpCall, hcall, hbool,
      h_stor_s_sc, h_bal_s_sc, h_code_s_sc⟩ :=
    of_run_callBoolCallback dp sel target dataArg value
      h_value_stor h_value_bal h_value_code run
  have h_floor_sc : Stor.FlashFloor floor (Devm.getStor sc ca) := by
    rw [← congrFun h_stor_s_sc ca]
    exact h_floor
  have h_code_sc :
      some (sc.getCode ca).toList = Prog.compile (weth10 dp) := by
    rw [← h_target, ← h_code_s_sc, h_target]
    exact h_code
  have h_post_call := flashFloorPost_of_value_call dp floor ca
    h_target ih hpCall h_code_sc h_floor_sc hcall
  obtain ⟨h_stor_tail, h_bal_tail, h_code_tail⟩ :=
    of_run_call_boolReturn_preserves_fields dp hbool
  refine ⟨trivial, ?_⟩
  change Stor.FlashFloor floor (Devm.getStor r ca)
  rw [← congrFun h_stor_tail ca]
  exact h_post_call.inv

/-- An accepted `CALL` result (`iszero` followed by the successful zero-flag
branch) carries both the flash floor and the contract's compiled code to the
post-guard state. -/
theorem flashFloorCode_of_call_success_guard
    (dp : DeployParams) (floor : B256) (ca : Adr)
    {sevm : Sevm} {sc s6 si sb : Devm}
    {g c v ii is oi os : B256} {xs : Stack}
    (h_target : sevm.currentTarget = ca)
    (ih : Exec.InvDepth sevm.depth ca (weth10 dp)
      ((flashFloorSpec dp floor).PreWf ca)
      ((flashFloorSpec dp floor).Post ca))
    (hp : (g :: c :: v :: ii :: is :: oi :: os :: xs) <<+ sc.stack)
    (h_code : some (sc.getCode ca).toList = Prog.compile (weth10 dp))
    (h_floor : Stor.FlashFloor floor (Devm.getStor sc ca))
    (hcall : Ninst.Run sevm sc call s6)
    (hiszero : Ninst.Run sevm s6 iszero si)
    (hpop : Devm.PopBurn [0] si sb) :
    Stor.FlashFloor floor (Devm.getStor sb ca) ∧
      some (sb.getCode ca).toList = Prog.compile (weth10 dp) := by
  have h_post_call := flashFloorPost_of_value_call dp floor ca
    h_target ih hp h_code h_floor hcall
  have h_stor_s6_si : Devm.getStor s6 = Devm.getStor si :=
    Line.of_inv Devm.getStor (by line_inv)
      (Line.Run.cons hiszero Line.Run.nil)
  have h_stor_si_sb : Devm.getStor si = Devm.getStor sb :=
    PopBurn.Inv.inv hpop
  have h_floor_sb : Stor.FlashFloor floor (Devm.getStor sb ca) := by
    rw [← congrFun h_stor_si_sb ca, ← congrFun h_stor_s6_si ca]
    exact h_post_call.inv
  have h_code_nonempty : (sc.getCode ca).toList ≠ [] := by
    intro he
    apply Prog.compile_ne_nil (p := weth10 dp)
    rw [← h_code, he]
  have h_code_s6_sc : s6.getCode ca = sc.getCode ca :=
    code_eq_of_ninst_run h_code_nonempty hcall
  have h_code_s6_si : s6.getCode ca = si.getCode ca :=
    congrFun (Line.of_inv Devm.getCode (by line_inv)
      (Line.Run.cons hiszero Line.Run.nil)) ca
  have h_code_si_sb : si.getCode ca = sb.getCode ca :=
    getCode_eq_of_state_eq hpop.state ca
  have h_code_sb_sc : sb.getCode ca = sc.getCode ca :=
    (h_code_s6_si.trans h_code_si_sb).symm.trans h_code_s6_sc
  refine ⟨h_floor_sb, ?_⟩
  rw [h_code_sb_sc]
  exact h_code

theorem flashFloorSpec_depositToAndCall_funcSound
    (dp : DeployParams) (floor : B256) (ca : Adr) :
    (flashFloorSpec dp floor).FuncSoundNoMem ca weth10Aux
      depositToAndCall := by
  intro sevm s r h_target h_pre ih run
  subst ca
  simp only [depositToAndCall] at run
  rcases of_run_prepend mintToPrefix _ run with
    ⟨smint, hmint, hcallback⟩
  obtain ⟨recipient, h_inc, h_flash⟩ :=
    mintToPrefix_storage
      (fs := (weth10 dp).main :: weth10Aux) hmint
  have h_code :
      some (smint.getCode sevm.currentTarget).toList =
        Prog.compile (weth10 dp) := by
    rw [← congrFun (Line.of_inv Devm.getCode (by line_inv) hmint)
      sevm.currentTarget]
    exact h_pre.code
  have h_floor := h_pre.inv.1 rfl
  change Stor.FlashFloor floor
    (Devm.getStor s sevm.currentTarget) at h_floor
  have h_floor_mint : Stor.FlashFloor floor
      (Devm.getStor smint sevm.currentTarget) := by
    unfold Stor.FlashFloor at h_floor ⊢
    rw [h_flash]
    exact h_floor
  exact flashFloorPost_of_run_callBoolCallback dp floor
    sevm.currentTarget rfl ih h_code h_floor_mint
    (by line_inv) (by line_inv) (by line_inv) hcallback

theorem flashFloorSpec_approveAndCall_funcSound
    (dp : DeployParams) (floor : B256) (ca : Adr) :
    (flashFloorSpec dp floor).FuncSoundNoMem ca weth10Aux
      (nonpayable approveAndCall) := by
  apply flashFloor_nonpayable_funcSound_of_body dp floor ca
  intro sevm s r h_target h_pre ih run
  subst ca
  simp only [approveAndCall] at run
  rcases of_run_prepend approvePrefix _ run with
    ⟨sapprove, happrove, hcallback⟩
  have h_silent := approvePrefix_storage_silent happrove
  have h_code :
      some (sapprove.getCode sevm.currentTarget).toList =
        Prog.compile (weth10 dp) := by
    rw [← congrFun (Line.of_inv Devm.getCode (by line_inv) happrove)
      sevm.currentTarget]
    exact h_pre.code
  have h_floor := h_pre.inv.1 rfl
  change Stor.FlashFloor floor
    (Devm.getStor s sevm.currentTarget) at h_floor
  have h_floor_approve : Stor.FlashFloor floor
      (Devm.getStor sapprove sevm.currentTarget) := by
    unfold Stor.FlashFloor at h_floor ⊢
    rw [h_silent.2]
    exact h_floor
  exact flashFloorPost_of_run_callBoolCallback dp floor
    sevm.currentTarget rfl ih h_code h_floor_approve
    (by line_inv) (by line_inv) (by line_inv) hcallback

/-- The nonzero-recipient transfer prefix preserves the exact flash counter
and exposes its continuation state. -/
theorem of_transferNonzeroThen_flash
    (dp : DeployParams) {sevm : Sevm} {s r : Devm} {next : Func}
    (run : Func.Run ((weth10 dp).main :: weth10Aux) sevm s
      (transferNonzeroThen next) r) :
    ∃ snext,
      (Devm.getStor snext sevm.currentTarget).get flashMintedSlot =
        (Devm.getStor s sevm.currentTarget).get flashMintedSlot ∧
      snext.getCode sevm.currentTarget = s.getCode sevm.currentTarget ∧
      Func.Run ((weth10 dp).main :: weth10Aux) sevm snext next r := by
  simp only [transferNonzeroThen] at run
  rcases of_run_prepend (loadCallerBalanceAmount 1) _ run with
    ⟨s1, hload, run1⟩
  rcases prefix_of_loadCallerBalanceAmount nil_pref hload with
    ⟨balance, h_balance, hp1⟩
  rcases of_run_prepend balanceTooSmall _ run1 with
    ⟨s2, hguard, run2⟩
  have hp2 :
      (balance <? Sevm.argWord sevm 1) :: balance ::
        Sevm.argWord sevm 1 :: sevm.caller.toB256 :: [] <<+ s2.stack :=
    prefix_of_balanceTooSmall hp1 hguard
  have h_error_lookup :
      ((weth10 dp).main :: weth10Aux)[transferBalanceErrorSlot]? =
        some (Func.revWith "WETH: transfer amount exceeds balance") := by
    simp [weth10, weth10Aux, transferBalanceErrorSlot,
      transferBalanceError]
  rcases of_run_branch_call_revWith h_error_lookup run2 with
    ⟨s3, hpopGuard, run3⟩
  have hpopStack := hpopGuard.stack
  simp only [Stack.Pop, Split, List.nil_append, List.cons_append] at hpopStack
  rw [hpopStack] at hp2
  have h_flag : (balance <? Sevm.argWord sevm 1) = 0 :=
    pref_head_unique hp2 (pref_append [0] s3.stack)
  have h_token_le : Sevm.argWord sevm 1 ≤ balance := by
    rw [← B256.not_lt]
    intro hlt
    rw [B256.ltCheck, if_pos hlt] at h_flag
    exact B256.zero_ne_one h_flag.symm
  rw [h_flag] at hp2
  have hp3 :
      [balance, Sevm.argWord sevm 1, sevm.caller.toB256] <<+ s3.stack :=
    cons_pref_cons_inv hp2
  have h_stor_s_s3 : Devm.getStor s = Devm.getStor s3 :=
    (Line.of_inv Devm.getStor (by line_inv) hload).trans
      ((Line.of_inv Devm.getStor (by line_inv) hguard).trans
        (PopBurn.Inv.inv hpopGuard))
  have h_balance3 :
      balance =
        (Devm.getStor s3 sevm.currentTarget).get sevm.caller.toB256 := by
    rw [h_balance, congrFun h_stor_s_s3 sevm.currentTarget]
  rcases of_run_prepend debitLoadedBalance _ run3 with
    ⟨s4, hdebit, run4⟩
  obtain ⟨h_dec, h_cover, h_flash_debit⟩ :=
    debitLoadedBalance_storage (validAdr_toB256 sevm.caller)
      h_balance3 h_token_le hp3 hdebit
  let creditLine : Line :=
    addressArg 0 ++ [dup 0, sload] ++ arg 1 ++ [add, swap 0, sstore]
  rcases of_run_prepend creditLine _ run4 with
    ⟨s5, hcredit, run5⟩
  obtain ⟨recipient, h_inc, h_flash_credit⟩ :=
    creditAddressArg_storage 0 1 (by
      simpa only [creditLine] using hcredit)
  let logLine : Line :=
    [caller] ++ arg 1 ++ addressArg 0 ++ emitTransfer
  rcases of_run_prepend logLine next run5 with
    ⟨s6, hlog, hnext⟩
  have h_stor_s5_s6 : Devm.getStor s5 = Devm.getStor s6 :=
    Line.of_inv Devm.getStor (by line_inv) hlog
  have h_code_s_s6 :
      s.getCode sevm.currentTarget = s6.getCode sevm.currentTarget :=
    (congrFun (Line.of_inv Devm.getCode (by line_inv) hload)
      sevm.currentTarget).trans
      ((congrFun (Line.of_inv Devm.getCode (by line_inv) hguard)
        sevm.currentTarget).trans
        ((getCode_eq_of_state_eq hpopGuard.state sevm.currentTarget).trans
          ((congrFun (Line.of_inv Devm.getCode (by line_inv) hdebit)
            sevm.currentTarget).trans
            ((congrFun (Line.of_inv Devm.getCode (by line_inv) hcredit)
              sevm.currentTarget).trans
              (congrFun (Line.of_inv Devm.getCode (by line_inv) hlog)
                sevm.currentTarget)))))
  refine ⟨s6, ?_, h_code_s_s6.symm, hnext⟩
  rw [← congrFun h_stor_s5_s6 sevm.currentTarget,
    h_flash_credit, h_flash_debit,
    ← congrFun h_stor_s_s3 sevm.currentTarget]

/-- Generic caller-burn/value-send prefix used by `withdraw`, `withdrawTo`,
and the zero-recipient transfer branch.  The sender-specific line is supplied
only through its exact CALL exposure theorem. -/
theorem of_callerBurnThen_floor
    (dp : DeployParams) (floor : B256) (ca : Adr)
    (amountArg : B256) (send : Line) (sendErrorSlot : Nat)
    (sendError : String) {next : Func}
    {sevm : Sevm} {s r : Devm}
    (h_target : sevm.currentTarget = ca)
    (ih : Exec.InvDepth sevm.depth ca (weth10 dp)
      ((flashFloorSpec dp floor).PreWf ca)
      ((flashFloorSpec dp floor).Post ca))
    (h_code : some (s.getCode ca).toList = Prog.compile (weth10 dp))
    (h_floor : Stor.FlashFloor floor (Devm.getStor s ca))
    (h_send : ∀ {s0 r0 : Devm} {value : B256} {xs : Stack},
      value :: xs <<+ s0.stack → Line.Run sevm s0 send r0 →
      ∃ sc g target,
        (g :: target :: value :: 0 :: 0 :: 0 :: 0 :: xs) <<+ sc.stack ∧
        Ninst.Run sevm sc call r0 ∧
        Devm.getStor s0 = Devm.getStor sc ∧
        s0.getCode = sc.getCode)
    (h_error_lookup :
      ((weth10 dp).main :: weth10Aux)[sendErrorSlot]? =
        some (Func.revWith sendError))
    (run : Func.Run ((weth10 dp).main :: weth10Aux) sevm s
      (loadCallerBalanceAmount amountArg +++ balanceTooSmall +++
        (.call burnBalanceErrorSlot) <?>
        (debitLoadedBalance +++
          caller ::: arg amountArg +++ pushB256 0 ::: emitTransfer +++
          swap 0 ::: pop :::
          send +++ iszero :::
          (.call sendErrorSlot) <?> next)) r) :
    ∃ snext,
      Stor.FlashFloor floor (Devm.getStor snext ca) ∧
      some (snext.getCode ca).toList = Prog.compile (weth10 dp) ∧
      Func.Run ((weth10 dp).main :: weth10Aux) sevm snext next r := by
  subst ca
  rcases of_run_prepend (loadCallerBalanceAmount amountArg) _ run with
    ⟨s1, hload, run1⟩
  rcases prefix_of_loadCallerBalanceAmount nil_pref hload with
    ⟨balance, h_balance, hp1⟩
  rcases of_run_prepend balanceTooSmall _ run1 with
    ⟨s2, hguard, run2⟩
  have hp2 :
      (balance <? Sevm.argWord sevm amountArg) :: balance ::
        Sevm.argWord sevm amountArg :: sevm.caller.toB256 :: [] <<+
          s2.stack :=
    prefix_of_balanceTooSmall hp1 hguard
  have h_burn_lookup :
      ((weth10 dp).main :: weth10Aux)[burnBalanceErrorSlot]? =
        some (Func.revWith "WETH: burn amount exceeds balance") := by
    simp [weth10, weth10Aux, burnBalanceErrorSlot, burnBalanceError]
  rcases of_run_branch_call_revWith h_burn_lookup run2 with
    ⟨s3, hpopGuard, run3⟩
  have hpopStack := hpopGuard.stack
  simp only [Stack.Pop, Split, List.nil_append, List.cons_append] at hpopStack
  rw [hpopStack] at hp2
  have h_flag : (balance <? Sevm.argWord sevm amountArg) = 0 :=
    pref_head_unique hp2 (pref_append [0] s3.stack)
  have h_token_le : Sevm.argWord sevm amountArg ≤ balance := by
    rw [← B256.not_lt]
    intro hlt
    rw [B256.ltCheck, if_pos hlt] at h_flag
    exact B256.zero_ne_one h_flag.symm
  rw [h_flag] at hp2
  have hp3 :
      [balance, Sevm.argWord sevm amountArg, sevm.caller.toB256] <<+
        s3.stack := cons_pref_cons_inv hp2
  have h_stor_s_s3 : Devm.getStor s = Devm.getStor s3 :=
    (Line.of_inv Devm.getStor (by line_inv) hload).trans
      ((Line.of_inv Devm.getStor (by line_inv) hguard).trans
        (PopBurn.Inv.inv hpopGuard))
  have h_code_s_s3 :
      s.getCode sevm.currentTarget = s3.getCode sevm.currentTarget :=
    (congrFun (Line.of_inv Devm.getCode (by line_inv) hload)
      sevm.currentTarget).trans
      ((congrFun (Line.of_inv Devm.getCode (by line_inv) hguard)
        sevm.currentTarget).trans
        (getCode_eq_of_state_eq hpopGuard.state sevm.currentTarget))
  have h_balance3 :
      balance =
        (Devm.getStor s3 sevm.currentTarget).get sevm.caller.toB256 := by
    rw [h_balance, congrFun h_stor_s_s3 sevm.currentTarget]
  rcases of_run_prepend debitLoadedBalance _ run3 with
    ⟨s4, hdebit, run4⟩
  obtain ⟨h_dec, h_cover, h_flash⟩ :=
    debitLoadedBalance_storage (validAdr_toB256 sevm.caller)
      h_balance3 h_token_le hp3 hdebit
  let eventLine : Line :=
    [caller] ++ arg amountArg ++ [pushB256 0] ++ emitTransfer ++
      [swap 0, pop]
  rcases of_run_prepend eventLine _ run4 with
    ⟨s5, hevent, run5⟩
  have hp5 : Sevm.argWord sevm amountArg :: [] <<+ s5.stack := by
    apply prefix_of_burnEvent amountArg nil_pref
    simpa only [eventLine] using hevent
  rcases of_run_prepend send _ run5 with ⟨s6, hsend, run6⟩
  obtain ⟨sc, g, target, hpCall, hcall, h_stor_s5_sc,
      h_code_s5_sc⟩ := h_send hp5 hsend
  rcases of_run_next run6 with ⟨si, hiszero, run7⟩
  rcases of_run_branch_call_revWith h_error_lookup run7 with
    ⟨sb, hpopCall, hnext⟩
  have h_stor_s4_sc : Devm.getStor s4 = Devm.getStor sc :=
    (Line.of_inv Devm.getStor (by line_inv) hevent).trans h_stor_s5_sc
  have h_code_s3_sc :
      s3.getCode sevm.currentTarget = sc.getCode sevm.currentTarget :=
    (congrFun (Line.of_inv Devm.getCode (by line_inv) hdebit)
      sevm.currentTarget).trans
      ((congrFun (Line.of_inv Devm.getCode (by line_inv) hevent)
        sevm.currentTarget).trans
        (congrFun h_code_s5_sc sevm.currentTarget))
  have h_code_sc :
      some (sc.getCode sevm.currentTarget).toList =
        Prog.compile (weth10 dp) := by
    rw [← h_code_s3_sc, ← h_code_s_s3]
    exact h_code
  have h_floor_sc : Stor.FlashFloor floor
      (Devm.getStor sc sevm.currentTarget) := by
    unfold Stor.FlashFloor at h_floor ⊢
    rw [← congrFun h_stor_s4_sc sevm.currentTarget,
      h_flash, ← congrFun h_stor_s_s3 sevm.currentTarget]
    exact h_floor
  obtain ⟨h_floor_sb, h_code_sb⟩ :=
    flashFloorCode_of_call_success_guard dp floor sevm.currentTarget
      rfl ih hpCall h_code_sc h_floor_sc hcall hiszero hpopCall
  exact ⟨sb, h_floor_sb, h_code_sb, hnext⟩

/-- The normalized-source/nonzero-recipient transfer-from core preserves the
exact flash counter. -/
theorem transferFromNonzero_flashStable (dp : DeployParams) :
    FlashStable dp transferFromNonzero := by
  intro sevm s r run
  simp only [transferFromNonzero] at run
  rcases of_run_prepend (loadArgBalanceAmount 0 2) _ run with
    ⟨s1, hload, run1⟩
  rcases prefix_of_loadArgBalanceAmount 0 2 nil_pref hload with
    ⟨balance, owner, h_owner, h_balance, hp1⟩
  rcases of_run_prepend balanceTooSmall _ run1 with
    ⟨s2, hguard, run2⟩
  have hp2 :
      (balance <? Sevm.argWord sevm 2) :: balance ::
        Sevm.argWord sevm 2 :: owner :: [] <<+ s2.stack :=
    prefix_of_balanceTooSmall hp1 hguard
  have h_error_lookup :
      ((weth10 dp).main :: weth10Aux)[transferBalanceErrorSlot]? =
        some (Func.revWith "WETH: transfer amount exceeds balance") := by
    simp [weth10, weth10Aux, transferBalanceErrorSlot,
      transferBalanceError]
  rcases of_run_branch_call_revWith h_error_lookup run2 with
    ⟨s3, hpopGuard, run3⟩
  have hpopStack := hpopGuard.stack
  simp only [Stack.Pop, Split, List.nil_append, List.cons_append] at hpopStack
  rw [hpopStack] at hp2
  have h_flag : (balance <? Sevm.argWord sevm 2) = 0 :=
    pref_head_unique hp2 (pref_append [0] s3.stack)
  have h_token_le : Sevm.argWord sevm 2 ≤ balance := by
    rw [← B256.not_lt]
    intro hlt
    rw [B256.ltCheck, if_pos hlt] at h_flag
    exact B256.zero_ne_one h_flag.symm
  rw [h_flag] at hp2
  have hp3 : [balance, Sevm.argWord sevm 2, owner] <<+ s3.stack :=
    cons_pref_cons_inv hp2
  have h_stor_s_s3 : Devm.getStor s = Devm.getStor s3 :=
    (Line.of_inv Devm.getStor (by line_inv) hload).trans
      ((Line.of_inv Devm.getStor (by line_inv) hguard).trans
        (PopBurn.Inv.inv hpopGuard))
  have h_balance3 :
      balance = (Devm.getStor s3 sevm.currentTarget).get owner := by
    rw [h_balance, congrFun h_stor_s_s3 sevm.currentTarget]
  rcases of_run_prepend debitLoadedBalance _ run3 with
    ⟨s4, hdebit, run4⟩
  obtain ⟨h_dec, h_cover, h_flash_debit⟩ :=
    debitLoadedBalance_storage (by
      rw [h_owner]
      exact normalizedAddress_valid (Sevm.argWord sevm 0))
      h_balance3 h_token_le hp3 hdebit
  let creditLine : Line :=
    addressArg 1 ++ [dup 0, sload] ++ arg 2 ++ [add, swap 0, sstore]
  rcases of_run_prepend creditLine _ run4 with
    ⟨s5, hcredit, run5⟩
  obtain ⟨recipient, h_inc, h_flash_credit⟩ :=
    creditAddressArg_storage 1 2 (by
      simpa only [creditLine] using hcredit)
  let logLine : Line :=
    addressArg 0 ++ arg 2 ++ addressArg 1 ++ emitTransfer
  rcases of_run_prepend logLine returnTrue run5 with
    ⟨s6, hlog, hreturn⟩
  have h_stor_s5_r : Devm.getStor s5 = Devm.getStor r :=
    (Line.of_inv Devm.getStor (by line_inv) hlog).trans
      (Func.of_inv Devm.getStor Devm.getStor (by func_inv) hreturn)
  rw [← congrFun h_stor_s5_r sevm.currentTarget,
    h_flash_credit, h_flash_debit,
    ← congrFun h_stor_s_s3 sevm.currentTarget]

/-- Generic normalized-source burn/value-send prefix used by
`transferFromZero` and `withdrawFromCore`. -/
theorem of_argBurnThen_floor
    (dp : DeployParams) (floor : B256) (ca : Adr)
    (ownerArg amountArg : B256) (send : Line) (sendErrorSlot : Nat)
    (sendError : String) {next : Func}
    {sevm : Sevm} {s r : Devm}
    (h_target : sevm.currentTarget = ca)
    (ih : Exec.InvDepth sevm.depth ca (weth10 dp)
      ((flashFloorSpec dp floor).PreWf ca)
      ((flashFloorSpec dp floor).Post ca))
    (h_code : some (s.getCode ca).toList = Prog.compile (weth10 dp))
    (h_floor : Stor.FlashFloor floor (Devm.getStor s ca))
    (h_send : ∀ {s0 r0 : Devm} {value : B256} {xs : Stack},
      value :: xs <<+ s0.stack → Line.Run sevm s0 send r0 →
      ∃ sc g target,
        (g :: target :: value :: 0 :: 0 :: 0 :: 0 :: xs) <<+ sc.stack ∧
        Ninst.Run sevm sc call r0 ∧
        Devm.getStor s0 = Devm.getStor sc ∧
        s0.getCode = sc.getCode)
    (h_error_lookup :
      ((weth10 dp).main :: weth10Aux)[sendErrorSlot]? =
        some (Func.revWith sendError))
    (run : Func.Run ((weth10 dp).main :: weth10Aux) sevm s
      (loadArgBalanceAmount ownerArg amountArg +++ balanceTooSmall +++
        (.call burnBalanceErrorSlot) <?>
        (debitLoadedBalance +++
          addressArg ownerArg +++ arg amountArg +++ pushB256 0 :::
          emitTransfer +++ swap 0 ::: pop :::
          send +++ iszero :::
          (.call sendErrorSlot) <?> next)) r) :
    ∃ snext,
      Stor.FlashFloor floor (Devm.getStor snext ca) ∧
      some (snext.getCode ca).toList = Prog.compile (weth10 dp) ∧
      Func.Run ((weth10 dp).main :: weth10Aux) sevm snext next r := by
  subst ca
  rcases of_run_prepend (loadArgBalanceAmount ownerArg amountArg) _ run with
    ⟨s1, hload, run1⟩
  rcases prefix_of_loadArgBalanceAmount ownerArg amountArg nil_pref hload with
    ⟨balance, owner, h_owner, h_balance, hp1⟩
  rcases of_run_prepend balanceTooSmall _ run1 with
    ⟨s2, hguard, run2⟩
  have hp2 :
      (balance <? Sevm.argWord sevm amountArg) :: balance ::
        Sevm.argWord sevm amountArg :: owner :: [] <<+ s2.stack :=
    prefix_of_balanceTooSmall hp1 hguard
  have h_burn_lookup :
      ((weth10 dp).main :: weth10Aux)[burnBalanceErrorSlot]? =
        some (Func.revWith "WETH: burn amount exceeds balance") := by
    simp [weth10, weth10Aux, burnBalanceErrorSlot, burnBalanceError]
  rcases of_run_branch_call_revWith h_burn_lookup run2 with
    ⟨s3, hpopGuard, run3⟩
  have hpopStack := hpopGuard.stack
  simp only [Stack.Pop, Split, List.nil_append, List.cons_append] at hpopStack
  rw [hpopStack] at hp2
  have h_flag : (balance <? Sevm.argWord sevm amountArg) = 0 :=
    pref_head_unique hp2 (pref_append [0] s3.stack)
  have h_token_le : Sevm.argWord sevm amountArg ≤ balance := by
    rw [← B256.not_lt]
    intro hlt
    rw [B256.ltCheck, if_pos hlt] at h_flag
    exact B256.zero_ne_one h_flag.symm
  rw [h_flag] at hp2
  have hp3 : [balance, Sevm.argWord sevm amountArg, owner] <<+ s3.stack :=
    cons_pref_cons_inv hp2
  have h_stor_s_s3 : Devm.getStor s = Devm.getStor s3 :=
    (Line.of_inv Devm.getStor (by line_inv) hload).trans
      ((Line.of_inv Devm.getStor (by line_inv) hguard).trans
        (PopBurn.Inv.inv hpopGuard))
  have h_code_s_s3 :
      s.getCode sevm.currentTarget = s3.getCode sevm.currentTarget :=
    (congrFun (Line.of_inv Devm.getCode (by line_inv) hload)
      sevm.currentTarget).trans
      ((congrFun (Line.of_inv Devm.getCode (by line_inv) hguard)
        sevm.currentTarget).trans
        (getCode_eq_of_state_eq hpopGuard.state sevm.currentTarget))
  have h_balance3 : balance =
      (Devm.getStor s3 sevm.currentTarget).get owner := by
    rw [h_balance, congrFun h_stor_s_s3 sevm.currentTarget]
  rcases of_run_prepend debitLoadedBalance _ run3 with
    ⟨s4, hdebit, run4⟩
  obtain ⟨h_dec, h_cover, h_flash⟩ :=
    debitLoadedBalance_storage (by
      rw [h_owner]
      exact normalizedAddress_valid (Sevm.argWord sevm ownerArg))
      h_balance3 h_token_le hp3 hdebit
  let eventLine : Line :=
    addressArg ownerArg ++ arg amountArg ++ [pushB256 0] ++
      emitTransfer ++ [swap 0, pop]
  rcases of_run_prepend eventLine _ run4 with
    ⟨s5, hevent, run5⟩
  have hp5 : Sevm.argWord sevm amountArg :: [] <<+ s5.stack := by
    apply prefix_of_burnEventFromArg ownerArg amountArg nil_pref
    simpa only [eventLine] using hevent
  rcases of_run_prepend send _ run5 with ⟨s6, hsend, run6⟩
  obtain ⟨sc, g, target, hpCall, hcall, h_stor_s5_sc,
      h_code_s5_sc⟩ := h_send hp5 hsend
  rcases of_run_next run6 with ⟨si, hiszero, run7⟩
  rcases of_run_branch_call_revWith h_error_lookup run7 with
    ⟨sb, hpopCall, hnext⟩
  have h_stor_s4_sc : Devm.getStor s4 = Devm.getStor sc :=
    (Line.of_inv Devm.getStor (by line_inv) hevent).trans h_stor_s5_sc
  have h_code_s3_sc :
      s3.getCode sevm.currentTarget = sc.getCode sevm.currentTarget :=
    (congrFun (Line.of_inv Devm.getCode (by line_inv) hdebit)
      sevm.currentTarget).trans
      ((congrFun (Line.of_inv Devm.getCode (by line_inv) hevent)
        sevm.currentTarget).trans
        (congrFun h_code_s5_sc sevm.currentTarget))
  have h_code_sc :
      some (sc.getCode sevm.currentTarget).toList =
        Prog.compile (weth10 dp) := by
    rw [← h_code_s3_sc, ← h_code_s_s3]
    exact h_code
  have h_floor_sc : Stor.FlashFloor floor
      (Devm.getStor sc sevm.currentTarget) := by
    unfold Stor.FlashFloor at h_floor ⊢
    rw [← congrFun h_stor_s4_sc sevm.currentTarget,
      h_flash, ← congrFun h_stor_s_s3 sevm.currentTarget]
    exact h_floor
  obtain ⟨h_floor_sb, h_code_sb⟩ :=
    flashFloorCode_of_call_success_guard dp floor sevm.currentTarget
      rfl ih hpCall h_code_sc h_floor_sc hcall hiszero hpopCall
  exact ⟨sb, h_floor_sb, h_code_sb, hnext⟩

/-- The zero-recipient transfer prefix retains a flash floor across its
accepted ETH call and exposes the continuation state. -/
theorem of_transferZeroThen_floor
    (dp : DeployParams) (floor : B256) (ca : Adr)
    {sevm : Sevm} {s r : Devm} {next : Func}
    (h_target : sevm.currentTarget = ca)
    (ih : Exec.InvDepth sevm.depth ca (weth10 dp)
      ((flashFloorSpec dp floor).PreWf ca)
      ((flashFloorSpec dp floor).Post ca))
    (h_code : some (s.getCode ca).toList = Prog.compile (weth10 dp))
    (h_floor : Stor.FlashFloor floor (Devm.getStor s ca))
    (run : Func.Run ((weth10 dp).main :: weth10Aux) sevm s
      (transferZeroThen next) r) :
    ∃ snext,
      Stor.FlashFloor floor (Devm.getStor snext ca) ∧
      some (snext.getCode ca).toList = Prog.compile (weth10 dp) ∧
      Func.Run ((weth10 dp).main :: weth10Aux) sevm snext next r := by
  subst ca
  simp only [transferZeroThen] at run
  rcases of_run_prepend (loadCallerBalanceAmount 1) _ run with
    ⟨s1, hload, run1⟩
  rcases prefix_of_loadCallerBalanceAmount nil_pref hload with
    ⟨balance, h_balance, hp1⟩
  rcases of_run_prepend balanceTooSmall _ run1 with
    ⟨s2, hguard, run2⟩
  have hp2 :
      (balance <? Sevm.argWord sevm 1) :: balance ::
        Sevm.argWord sevm 1 :: sevm.caller.toB256 :: [] <<+ s2.stack :=
    prefix_of_balanceTooSmall hp1 hguard
  have h_burn_lookup :
      ((weth10 dp).main :: weth10Aux)[burnBalanceErrorSlot]? =
        some (Func.revWith "WETH: burn amount exceeds balance") := by
    simp [weth10, weth10Aux, burnBalanceErrorSlot, burnBalanceError]
  rcases of_run_branch_call_revWith h_burn_lookup run2 with
    ⟨s3, hpopGuard, run3⟩
  have hpopStack := hpopGuard.stack
  simp only [Stack.Pop, Split, List.nil_append, List.cons_append] at hpopStack
  rw [hpopStack] at hp2
  have h_flag : (balance <? Sevm.argWord sevm 1) = 0 :=
    pref_head_unique hp2 (pref_append [0] s3.stack)
  have h_token_le : Sevm.argWord sevm 1 ≤ balance := by
    rw [← B256.not_lt]
    intro hlt
    rw [B256.ltCheck, if_pos hlt] at h_flag
    exact B256.zero_ne_one h_flag.symm
  rw [h_flag] at hp2
  have hp3 :
      [balance, Sevm.argWord sevm 1, sevm.caller.toB256] <<+ s3.stack :=
    cons_pref_cons_inv hp2
  have h_stor_s_s3 : Devm.getStor s = Devm.getStor s3 :=
    (Line.of_inv Devm.getStor (by line_inv) hload).trans
      ((Line.of_inv Devm.getStor (by line_inv) hguard).trans
        (PopBurn.Inv.inv hpopGuard))
  have h_code_s_s3 :
      s.getCode sevm.currentTarget = s3.getCode sevm.currentTarget :=
    (congrFun (Line.of_inv Devm.getCode (by line_inv) hload)
      sevm.currentTarget).trans
      ((congrFun (Line.of_inv Devm.getCode (by line_inv) hguard)
        sevm.currentTarget).trans
        (getCode_eq_of_state_eq hpopGuard.state sevm.currentTarget))
  have h_balance3 :
      balance =
        (Devm.getStor s3 sevm.currentTarget).get sevm.caller.toB256 := by
    rw [h_balance, congrFun h_stor_s_s3 sevm.currentTarget]
  rcases of_run_prepend debitLoadedBalance _ run3 with
    ⟨s4, hdebit, run4⟩
  obtain ⟨h_dec, h_cover, h_flash⟩ :=
    debitLoadedBalance_storage (validAdr_toB256 sevm.caller)
      h_balance3 h_token_le hp3 hdebit
  let eventLine : Line :=
    [caller] ++ arg 1 ++ [pushB256 0] ++ emitTransfer ++ [swap 0, pop]
  rcases of_run_prepend eventLine _ run4 with
    ⟨s5, hevent, run5⟩
  have hp5 : Sevm.argWord sevm 1 :: [] <<+ s5.stack := by
    apply prefix_of_burnEvent 1 nil_pref
    simpa only [eventLine] using hevent
  rcases of_run_prepend sendValueToCaller _ run5 with
    ⟨s6, hsend, run6⟩
  obtain ⟨sc, g, hpCall, hcall, h_stor_s5_sc, h_bal_s5_sc,
      h_code_s5_sc⟩ := of_sendValueToCaller hp5 hsend
  rcases of_run_next run6 with ⟨si, hiszero, run7⟩
  have h_eth_lookup :
      ((weth10 dp).main :: weth10Aux)[ethTransferErrorSlot]? =
        some (Func.revWith "WETH: ETH transfer failed") := by
    simp [weth10, weth10Aux, ethTransferErrorSlot, ethTransferError]
  rcases of_run_branch_call_revWith h_eth_lookup run7 with
    ⟨sb, hpopCall, hnext⟩
  have h_stor_s4_sc : Devm.getStor s4 = Devm.getStor sc :=
    (Line.of_inv Devm.getStor (by line_inv) hevent).trans h_stor_s5_sc
  have h_code_s3_sc :
      s3.getCode sevm.currentTarget = sc.getCode sevm.currentTarget :=
    (congrFun (Line.of_inv Devm.getCode (by line_inv) hdebit)
      sevm.currentTarget).trans
      ((congrFun (Line.of_inv Devm.getCode (by line_inv) hevent)
        sevm.currentTarget).trans
        (congrFun h_code_s5_sc sevm.currentTarget))
  have h_code_sc :
      some (sc.getCode sevm.currentTarget).toList =
        Prog.compile (weth10 dp) := by
    rw [← h_code_s3_sc, ← h_code_s_s3]
    exact h_code
  have h_floor_sc : Stor.FlashFloor floor
      (Devm.getStor sc sevm.currentTarget) := by
    unfold Stor.FlashFloor at h_floor ⊢
    rw [← congrFun h_stor_s4_sc sevm.currentTarget,
      h_flash, ← congrFun h_stor_s_s3 sevm.currentTarget]
    exact h_floor
  have h_post_call := flashFloorPost_of_value_call dp floor
    sevm.currentTarget rfl ih hpCall h_code_sc h_floor_sc hcall
  have h_stor_s6_si : Devm.getStor s6 = Devm.getStor si :=
    Line.of_inv Devm.getStor (by line_inv)
      (Line.Run.cons hiszero Line.Run.nil)
  have h_stor_si_sb : Devm.getStor si = Devm.getStor sb :=
    PopBurn.Inv.inv hpopCall
  have h_floor_sb : Stor.FlashFloor floor
      (Devm.getStor sb sevm.currentTarget) := by
    rw [← congrFun h_stor_si_sb sevm.currentTarget,
      ← congrFun h_stor_s6_si sevm.currentTarget]
    exact h_post_call.inv
  have h_code_nonempty :
      (sc.getCode sevm.currentTarget).toList ≠ [] := by
    intro he
    apply Prog.compile_ne_nil (p := weth10 dp)
    rw [← h_code_sc, he]
  have h_code_s6_sc :
      s6.getCode sevm.currentTarget = sc.getCode sevm.currentTarget :=
    code_eq_of_ninst_run h_code_nonempty hcall
  have h_code_s6_si :
      s6.getCode sevm.currentTarget = si.getCode sevm.currentTarget :=
    congrFun (Line.of_inv Devm.getCode (by line_inv)
      (Line.Run.cons hiszero Line.Run.nil)) sevm.currentTarget
  have h_code_si_sb :
      si.getCode sevm.currentTarget = sb.getCode sevm.currentTarget :=
    getCode_eq_of_state_eq hpopCall.state sevm.currentTarget
  have h_code_sb_sc :
      sb.getCode sevm.currentTarget = sc.getCode sevm.currentTarget :=
    (h_code_s6_si.trans h_code_si_sb).symm.trans h_code_s6_sc
  refine ⟨sb, h_floor_sb, ?_, hnext⟩
  rw [h_code_sb_sc]
  exact h_code_sc

/-- `transferThen` preserves a flash floor up to its arbitrary continuation,
for both the normalized credit branch and the raw-zero ETH branch. -/
theorem of_transferThen_floor
    (dp : DeployParams) (floor : B256) (ca : Adr)
    {sevm : Sevm} {s r : Devm} {next : Func}
    (h_target : sevm.currentTarget = ca)
    (ih : Exec.InvDepth sevm.depth ca (weth10 dp)
      ((flashFloorSpec dp floor).PreWf ca)
      ((flashFloorSpec dp floor).Post ca))
    (h_code : some (s.getCode ca).toList = Prog.compile (weth10 dp))
    (h_floor : Stor.FlashFloor floor (Devm.getStor s ca))
    (run : Func.Run ((weth10 dp).main :: weth10Aux) sevm s
      (transferThen next) r) :
    ∃ snext,
      Stor.FlashFloor floor (Devm.getStor snext ca) ∧
      some (snext.getCode ca).toList = Prog.compile (weth10 dp) ∧
      Func.Run ((weth10 dp).main :: weth10Aux) sevm snext next r := by
  subst ca
  simp only [transferThen] at run
  rcases of_run_prepend (arg 0) _ run with ⟨s1, harg, run1⟩
  have hp1 : Sevm.argWord sevm 0 :: [] <<+ s1.stack :=
    prefix_of_arg nil_pref harg
  rcases of_run_next run1 with ⟨s2, hiszero, run2⟩
  have hp2 : (Sevm.argWord sevm 0 =? 0) :: [] <<+ s2.stack :=
    prefix_of_iszero hiszero hp1
  rcases of_run_branch run2 with
      ⟨s3, hpop, hnonzero⟩ |
      ⟨w, s3, s4, hnz, hpop, hburn, hzero⟩
  · have h_stor_s_s3 : Devm.getStor s = Devm.getStor s3 :=
      (Line.of_inv Devm.getStor (by line_inv) harg).trans
        ((Line.of_inv Devm.getStor (by line_inv)
          (Line.Run.cons hiszero Line.Run.nil)).trans
            (PopBurn.Inv.inv hpop))
    have h_code_s_s3 :
        s.getCode sevm.currentTarget = s3.getCode sevm.currentTarget :=
      (congrFun (Line.of_inv Devm.getCode (by line_inv) harg)
        sevm.currentTarget).trans
        ((congrFun (Line.of_inv Devm.getCode (by line_inv)
          (Line.Run.cons hiszero Line.Run.nil))
          sevm.currentTarget).trans
          (getCode_eq_of_state_eq hpop.state sevm.currentTarget))
    obtain ⟨snext, h_flash, h_code_next, hnext⟩ :=
      of_transferNonzeroThen_flash dp hnonzero
    refine ⟨snext, ?_, ?_, hnext⟩
    · unfold Stor.FlashFloor at h_floor ⊢
      rw [h_flash, ← congrFun h_stor_s_s3 sevm.currentTarget]
      exact h_floor
    · rw [h_code_next, ← h_code_s_s3]
      exact h_code
  · have h_stor_s_s4 : Devm.getStor s = Devm.getStor s4 :=
      (Line.of_inv Devm.getStor (by line_inv) harg).trans
        ((Line.of_inv Devm.getStor (by line_inv)
          (Line.Run.cons hiszero Line.Run.nil)).trans
            ((PopBurn.Inv.inv hpop).trans (Burn.Inv.inv hburn)))
    have h_code_s_s4 :
        s.getCode sevm.currentTarget = s4.getCode sevm.currentTarget :=
      (congrFun (Line.of_inv Devm.getCode (by line_inv) harg)
        sevm.currentTarget).trans
        ((congrFun (Line.of_inv Devm.getCode (by line_inv)
          (Line.Run.cons hiszero Line.Run.nil))
          sevm.currentTarget).trans
          ((getCode_eq_of_state_eq hpop.state sevm.currentTarget).trans
            (getCode_eq_of_state_eq hburn.state sevm.currentTarget)))
    have h_floor4 : Stor.FlashFloor floor
        (Devm.getStor s4 sevm.currentTarget) := by
      unfold Stor.FlashFloor at h_floor ⊢
      rw [← congrFun h_stor_s_s4 sevm.currentTarget]
      exact h_floor
    have h_code4 :
        some (s4.getCode sevm.currentTarget).toList =
          Prog.compile (weth10 dp) := by
      rw [← h_code_s_s4]
      exact h_code
    exact of_transferZeroThen_floor dp floor sevm.currentTarget
      rfl ih h_code4 h_floor4 hzero

theorem flashFloorSpec_transfer_funcSound
    (dp : DeployParams) (floor : B256) (ca : Adr) :
    (flashFloorSpec dp floor).FuncSoundNoMem ca weth10Aux
      (nonpayable transfer) := by
  apply flashFloor_nonpayable_funcSound_of_body dp floor ca
  intro sevm s r h_target h_pre ih run
  change Func.Run ((weth10 dp).main :: weth10Aux) sevm s transfer r at run
  have h_floor := h_pre.inv.1 h_target
  change Stor.FlashFloor floor (Devm.getStor s ca) at h_floor
  obtain ⟨snext, h_floor_next, h_code_next, hreturn⟩ :=
    of_transferThen_floor dp floor ca h_target ih h_pre.code h_floor
      (by simpa only [transfer] using run)
  refine ⟨trivial, ?_⟩
  change Stor.FlashFloor floor (Devm.getStor r ca)
  have hs : Devm.getStor snext = Devm.getStor r :=
    Func.of_inv Devm.getStor Devm.getStor (by func_inv) hreturn
  rw [← congrFun hs ca]
  exact h_floor_next

theorem flashFloorSpec_transferAndCall_funcSound
    (dp : DeployParams) (floor : B256) (ca : Adr) :
    (flashFloorSpec dp floor).FuncSoundNoMem ca weth10Aux
      (nonpayable transferAndCall) := by
  apply flashFloor_nonpayable_funcSound_of_body dp floor ca
  intro sevm s r h_target h_pre ih run
  change Func.Run ((weth10 dp).main :: weth10Aux) sevm s
    transferAndCall r at run
  have h_floor := h_pre.inv.1 h_target
  change Stor.FlashFloor floor (Devm.getStor s ca) at h_floor
  obtain ⟨snext, h_floor_next, h_code_next, hcallback⟩ :=
    of_transferThen_floor dp floor ca h_target ih h_pre.code h_floor
      (by simpa only [transferAndCall] using run)
  exact flashFloorPost_of_run_callBoolCallback dp floor ca
    h_target ih h_code_next h_floor_next
    (by line_inv) (by line_inv) (by line_inv) hcallback

theorem flashFloorSpec_withdraw_funcSound
    (dp : DeployParams) (floor : B256) (ca : Adr) :
    (flashFloorSpec dp floor).FuncSoundNoMem ca weth10Aux
      (nonpayable withdraw) := by
  apply flashFloor_nonpayable_funcSound_of_body dp floor ca
  intro sevm s r h_target h_pre ih run
  change Func.Run ((weth10 dp).main :: weth10Aux) sevm s withdraw r at run
  have h_floor := h_pre.inv.1 h_target
  change Stor.FlashFloor floor (Devm.getStor s ca) at h_floor
  obtain ⟨snext, h_floor_next, h_code_next, hstop⟩ :=
    of_callerBurnThen_floor dp floor ca 0 sendValueToCaller
      ethTransferErrorSlot "WETH: ETH transfer failed"
      h_target ih h_pre.code h_floor (by
        intro s0 r0 value xs hp hsend
        rcases of_sendValueToCaller hp hsend with
          ⟨sc, g, hpCall, hcall, hstor, hbal, hcode⟩
        exact ⟨sc, g, sevm.caller.toB256, hpCall, hcall, hstor, hcode⟩)
      (by
        simp [weth10, weth10Aux, ethTransferErrorSlot,
          ethTransferError])
      (by simpa only [withdraw] using run)
  refine ⟨trivial, ?_⟩
  change Stor.FlashFloor floor (Devm.getStor r ca)
  have hs : Devm.getStor snext = Devm.getStor r :=
    Func.of_inv Devm.getStor Devm.getStor (by func_inv) hstop
  rw [← congrFun hs ca]
  exact h_floor_next

theorem flashFloorSpec_withdrawTo_funcSound
    (dp : DeployParams) (floor : B256) (ca : Adr) :
    (flashFloorSpec dp floor).FuncSoundNoMem ca weth10Aux
      (nonpayable withdrawTo) := by
  apply flashFloor_nonpayable_funcSound_of_body dp floor ca
  intro sevm s r h_target h_pre ih run
  change Func.Run ((weth10 dp).main :: weth10Aux) sevm s withdrawTo r at run
  have h_floor := h_pre.inv.1 h_target
  change Stor.FlashFloor floor (Devm.getStor s ca) at h_floor
  obtain ⟨snext, h_floor_next, h_code_next, hstop⟩ :=
    of_callerBurnThen_floor dp floor ca 1 (sendValueToArg 0)
      ethTransferErrorSlot "WETH: ETH transfer failed"
      h_target ih h_pre.code h_floor (by
        intro s0 r0 value xs hp hsend
        rcases of_sendValueToArg 0 hp hsend with
          ⟨sc, g, hpCall, hcall, hstor, hbal, hcode⟩
        exact ⟨sc, g, Sevm.argWord sevm 0, hpCall, hcall,
          hstor, hcode⟩)
      (by
        simp [weth10, weth10Aux, ethTransferErrorSlot,
          ethTransferError])
      (by simpa only [withdrawTo] using run)
  refine ⟨trivial, ?_⟩
  change Stor.FlashFloor floor (Devm.getStor r ca)
  have hs : Devm.getStor snext = Devm.getStor r :=
    Func.of_inv Devm.getStor Devm.getStor (by func_inv) hstop
  rw [← congrFun hs ca]
  exact h_floor_next

theorem flashFloorSpec_transferFromNonzero_funcSound
    (dp : DeployParams) (floor : B256) (ca : Adr) :
    (flashFloorSpec dp floor).FuncSoundNoMem ca weth10Aux
      transferFromNonzero :=
  flashFloor_funcSound_of_stable dp floor ca
    (transferFromNonzero_flashStable dp)

theorem flashFloorSpec_transferFromZero_funcSound
    (dp : DeployParams) (floor : B256) (ca : Adr) :
    (flashFloorSpec dp floor).FuncSoundNoMem ca weth10Aux
      transferFromZero := by
  intro sevm s r h_target h_pre ih run
  change Func.Run ((weth10 dp).main :: weth10Aux) sevm s
    transferFromZero r at run
  have h_floor := h_pre.inv.1 h_target
  change Stor.FlashFloor floor (Devm.getStor s ca) at h_floor
  obtain ⟨snext, h_floor_next, h_code_next, hreturn⟩ :=
    of_argBurnThen_floor dp floor ca 0 2 sendValueToCaller
      ethTransferErrorSlot "WETH: ETH transfer failed"
      h_target ih h_pre.code h_floor (by
        intro s0 r0 value xs hp hsend
        rcases of_sendValueToCaller hp hsend with
          ⟨sc, g, hpCall, hcall, hstor, hbal, hcode⟩
        exact ⟨sc, g, sevm.caller.toB256, hpCall, hcall, hstor, hcode⟩)
      (by
        simp [weth10, weth10Aux, ethTransferErrorSlot,
          ethTransferError])
      (by simpa only [transferFromZero] using run)
  refine ⟨trivial, ?_⟩
  change Stor.FlashFloor floor (Devm.getStor r ca)
  have hs : Devm.getStor snext = Devm.getStor r :=
    Func.of_inv Devm.getStor Devm.getStor (by func_inv) hreturn
  rw [← congrFun hs ca]
  exact h_floor_next

/-- A floor-only counterpart of `backedPre_of_silent`. -/
theorem flashFloorPre_of_silent
    (dp : DeployParams) (floor : B256) (ca : Adr)
    {sevm : Sevm} {s sc : Devm}
    (h_pre : (flashFloorSpec dp floor).Pre ca sevm s)
    (h_silent : Stor.Weth10Silent
      (Devm.getStor s ca) (Devm.getStor sc ca))
    (h_code : Devm.getCode s ca = Devm.getCode sc ca) :
    (flashFloorSpec dp floor).Pre ca sevm sc := by
  refine ⟨?_, trivial, ?_, ?_⟩
  · rw [← h_code]
    exact h_pre.code
  · intro h_target
    have h := h_pre.inv.1 h_target
    change Stor.FlashFloor floor (Devm.getStor sc ca)
    unfold Stor.FlashFloor at h ⊢
    rw [h_silent.2]
    exact h
  · intro h_target
    have h := h_pre.inv.2 h_target
    change Stor.FlashFloor floor (Devm.getStor sc ca)
    unfold Stor.FlashFloor at h ⊢
    rw [h_silent.2]
    exact h

theorem flashFloorSpec_transferFromCore_funcSound
    (dp : DeployParams) (floor : B256) (ca : Adr) :
    (flashFloorSpec dp floor).FuncSoundNoMem ca weth10Aux
      transferFromCore := by
  intro sevm s r h_target h_pre ih run
  change Func.Run ((weth10 dp).main :: weth10Aux) sevm s
    transferFromCore r at run
  simp only [transferFromCore] at run
  rcases of_run_prepend (arg 1) _ run with ⟨s1, harg, run1⟩
  have hp1 : Sevm.argWord sevm 1 :: [] <<+ s1.stack :=
    prefix_of_arg nil_pref harg
  rcases of_run_next run1 with ⟨s2, hiszero, run2⟩
  have hp2 : (Sevm.argWord sevm 1 =? 0) :: [] <<+ s2.stack :=
    prefix_of_iszero hiszero hp1
  rcases of_run_branch run2 with
      ⟨s3, hpop, hnonzero⟩ |
      ⟨w, s3, s4, hnz, hpop, hburn, hzero⟩
  · have h_stor_s_s3 : Devm.getStor s = Devm.getStor s3 :=
      (Line.of_inv Devm.getStor (by line_inv) harg).trans
        ((Line.of_inv Devm.getStor (by line_inv)
          (Line.Run.cons hiszero Line.Run.nil)).trans
            (PopBurn.Inv.inv hpop))
    have h_code_s_s3 :
        s.getCode sevm.currentTarget = s3.getCode sevm.currentTarget :=
      (congrFun (Line.of_inv Devm.getCode (by line_inv) harg)
        sevm.currentTarget).trans
        ((congrFun (Line.of_inv Devm.getCode (by line_inv)
          (Line.Run.cons hiszero Line.Run.nil))
          sevm.currentTarget).trans
          (getCode_eq_of_state_eq hpop.state sevm.currentTarget))
    have h_pre3 := flashFloorPre_of_silent dp floor ca h_pre
      (Stor.Weth10Silent.of_eq
        (congrFun h_stor_s_s3 ca))
      (by simpa only [h_target] using h_code_s_s3)
    exact flashFloorSpec_transferFromNonzero_funcSound dp floor ca
      h_target h_pre3 ih hnonzero
  · have h_stor_s_s4 : Devm.getStor s = Devm.getStor s4 :=
      (Line.of_inv Devm.getStor (by line_inv) harg).trans
        ((Line.of_inv Devm.getStor (by line_inv)
          (Line.Run.cons hiszero Line.Run.nil)).trans
            ((PopBurn.Inv.inv hpop).trans (Burn.Inv.inv hburn)))
    have h_code_s_s4 :
        s.getCode sevm.currentTarget = s4.getCode sevm.currentTarget :=
      (congrFun (Line.of_inv Devm.getCode (by line_inv) harg)
        sevm.currentTarget).trans
        ((congrFun (Line.of_inv Devm.getCode (by line_inv)
          (Line.Run.cons hiszero Line.Run.nil))
          sevm.currentTarget).trans
          ((getCode_eq_of_state_eq hpop.state sevm.currentTarget).trans
            (getCode_eq_of_state_eq hburn.state sevm.currentTarget)))
    have h_pre4 := flashFloorPre_of_silent dp floor ca h_pre
      (Stor.Weth10Silent.of_eq
        (congrFun h_stor_s_s4 ca))
      (by simpa only [h_target] using h_code_s_s4)
    exact flashFloorSpec_transferFromZero_funcSound dp floor ca
      h_target h_pre4 ih hzero

theorem flashFloorSpec_transferFrom_funcSound
    (dp : DeployParams) (floor : B256) (ca : Adr) :
    (flashFloorSpec dp floor).FuncSoundNoMem ca weth10Aux
      (nonpayable transferFrom) := by
  apply flashFloor_nonpayable_funcSound_of_body dp floor ca
  intro sevm s r h_target h_pre ih run
  change Func.Run ((weth10 dp).main :: weth10Aux) sevm s transferFrom r at run
  have h_core_lookup :
      ((weth10 dp).main :: weth10Aux)[transferFromCoreSlot]? =
        some transferFromCore := by
    simp [weth10, weth10Aux, transferFromCoreSlot]
  obtain ⟨sc, hcore, h_silent, h_bal, h_code⟩ :=
    of_run_spendCallerAllowanceThen dp 2 transferFromCoreSlot
      transferFromCore h_core_lookup (by
        simpa only [transferFrom] using run)
  have h_silent' : Stor.Weth10Silent
      (Devm.getStor s ca) (Devm.getStor sc ca) := by
    simpa only [h_target] using h_silent
  have h_pre_sc := flashFloorPre_of_silent dp floor ca
    h_pre h_silent' (by simpa only [h_target] using h_code)
  exact flashFloorSpec_transferFromCore_funcSound dp floor ca
    h_target h_pre_sc ih hcore

theorem flashFloorSpec_withdrawFromCore_funcSound
    (dp : DeployParams) (floor : B256) (ca : Adr) :
    (flashFloorSpec dp floor).FuncSoundNoMem ca weth10Aux
      withdrawFromCore := by
  intro sevm s r h_target h_pre ih run
  change Func.Run ((weth10 dp).main :: weth10Aux) sevm s
    withdrawFromCore r at run
  have h_floor := h_pre.inv.1 h_target
  change Stor.FlashFloor floor (Devm.getStor s ca) at h_floor
  obtain ⟨snext, h_floor_next, h_code_next, hstop⟩ :=
    of_argBurnThen_floor dp floor ca 0 2 (sendValueToArg 1)
      etherTransferErrorSlot "WETH: Ether transfer failed"
      h_target ih h_pre.code h_floor (by
        intro s0 r0 value xs hp hsend
        rcases of_sendValueToArg 1 hp hsend with
          ⟨sc, g, hpCall, hcall, hstor, hbal, hcode⟩
        exact ⟨sc, g, Sevm.argWord sevm 1, hpCall, hcall,
          hstor, hcode⟩)
      (by
        simp [weth10, weth10Aux, etherTransferErrorSlot,
          etherTransferError])
      (by simpa only [withdrawFromCore] using run)
  refine ⟨trivial, ?_⟩
  change Stor.FlashFloor floor (Devm.getStor r ca)
  have hs : Devm.getStor snext = Devm.getStor r :=
    Func.of_inv Devm.getStor Devm.getStor (by func_inv) hstop
  rw [← congrFun hs ca]
  exact h_floor_next

theorem flashFloorSpec_withdrawFrom_funcSound
    (dp : DeployParams) (floor : B256) (ca : Adr) :
    (flashFloorSpec dp floor).FuncSoundNoMem ca weth10Aux
      (nonpayable withdrawFrom) := by
  apply flashFloor_nonpayable_funcSound_of_body dp floor ca
  intro sevm s r h_target h_pre ih run
  change Func.Run ((weth10 dp).main :: weth10Aux) sevm s withdrawFrom r at run
  have h_core_lookup :
      ((weth10 dp).main :: weth10Aux)[withdrawFromCoreSlot]? =
        some withdrawFromCore := by
    simp [weth10, weth10Aux, withdrawFromCoreSlot]
  obtain ⟨sc, hcore, h_silent, h_bal, h_code⟩ :=
    of_run_spendCallerAllowanceThen dp 2 withdrawFromCoreSlot
      withdrawFromCore h_core_lookup (by
        simpa only [withdrawFrom] using run)
  have h_silent' : Stor.Weth10Silent
      (Devm.getStor s ca) (Devm.getStor sc ca) := by
    simpa only [h_target] using h_silent
  have h_pre_sc := flashFloorPre_of_silent dp floor ca
    h_pre h_silent' (by simpa only [h_target] using h_code)
  exact flashFloorSpec_withdrawFromCore_funcSound dp floor ca
    h_target h_pre_sc ih hcore

/-! ### Exact flash settlement -/

theorem prefix_of_pushFlashMintedSlot
    {e : Sevm} {s r : Devm} {xs : Stack}
    (hp : xs <<+ s.stack)
    (run : Line.Run e s pushFlashMintedSlot r) :
    flashMintedSlot :: xs <<+ r.stack := by
  unfold pushFlashMintedSlot at run
  rcases Line.of_run_cons run with ⟨s1, hzero, run1⟩
  rcases Line.of_run_cons run1 with ⟨s2, hnot, hnil⟩
  cases hnil
  have hp1 : (0 : B256) :: xs <<+ s1.stack :=
    prefix_of_push (of_run_pushB256 hzero) hp
  have hp2 := prefix_of_not hnot hp1
  have h_zero : (~~~ (0 : B256)) = flashMintedSlot := rfl
  rw [h_zero] at hp2
  exact hp2

theorem rest_set_flashMintedSlot (s : Stor) (v : B256) :
    Stor.rest (s.set flashMintedSlot v) = Stor.rest s := by
  funext a
  simp only [Stor.rest, Function.comp_apply]
  exact Stor.get_set_ne _ (fun h =>
    flashMintedSlot_not_valid ⟨a, h.symm⟩) _

/-- The exact balance-debit fragment changes only its address-shaped owner
key.  Any distinct storage key is therefore preserved. -/
theorem debitLoadedBalance_storage_get_ne
    {e : Sevm} {s r : Devm} {balance value owner key : B256}
    (hkey : key ≠ owner)
    (hp : [balance, value, owner] <<+ s.stack)
    (run : Line.Run e s debitLoadedBalance r) :
    (Devm.getStor r e.currentTarget).get key =
      (Devm.getStor s e.currentTarget).get key := by
  unfold debitLoadedBalance at run
  rcases Line.of_run_cons run with ⟨s1, hsub, run1⟩
  have hp1 : (balance - value) :: owner :: [] <<+ s1.stack :=
    prefix_of_sub hsub hp
  rcases Line.of_run_cons run1 with ⟨s2, hswap, run2⟩
  have hswapCore : Stack.Swap (0 : Fin 16).val
      [balance - value, owner] [owner, balance - value] :=
    Stack.swapCore_zero
  have hp2 : owner :: (balance - value) :: [] <<+ s2.stack :=
    Stack.prefix_of_swap hswapCore (of_run_swap hswap) hp1
  rcases Line.of_run_cons run2 with ⟨s3, hstore, hnil⟩
  cases hnil
  have hset : Devm.getStor r e.currentTarget =
      (Devm.getStor s2 e.currentTarget).set owner
        (balance - value) :=
    sstore_getStor_set hstore hp2
  have hstor : Devm.getStor s = Devm.getStor s2 := by
    rw [Line.of_inv Devm.getStor (by line_inv)
          (Line.Run.cons hsub Line.Run.nil),
      Line.of_inv Devm.getStor (by line_inv)
        (Line.Run.cons hswap Line.Run.nil)]
  rw [hset, Stor.get_set_ne _ hkey.symm,
    ← congrFun hstor e.currentTarget]

/-- Exact successful `flashBurn`: debit the normalized receiver by argument 2
and subtract that same word from the flash counter. -/
theorem flashBurn_storage_at_receiver
    (dp : DeployParams) {sevm : Sevm} {s r : Devm}
    (run : Func.Run ((weth10 dp).main :: weth10Aux) sevm s
      flashBurn r) :
    Decrease (((~~~ addressMask) &&& Sevm.argWord sevm 0).toAdr)
        (Sevm.argWord sevm 2)
        (Stor.rest (Devm.getStor s sevm.currentTarget))
        (Stor.rest (Devm.getStor r sevm.currentTarget)) ∧
      Sevm.argWord sevm 2 ≤
        Stor.rest (Devm.getStor s sevm.currentTarget)
          (((~~~ addressMask) &&& Sevm.argWord sevm 0).toAdr) ∧
      (Devm.getStor r sevm.currentTarget).get flashMintedSlot =
        (Devm.getStor s sevm.currentTarget).get flashMintedSlot -
          Sevm.argWord sevm 2 ∧
      Devm.getBal s = Devm.getBal r := by
  simp only [flashBurn] at run
  rcases of_run_prepend (loadArgBalanceAmount 0 2) _ run with
    ⟨s1, hload, run1⟩
  rcases prefix_of_loadArgBalanceAmount 0 2 nil_pref hload with
    ⟨balance, ownerWord, h_owner, h_balance, hp1⟩
  rcases of_run_prepend balanceTooSmall _ run1 with
    ⟨s2, hguard, run2⟩
  have hp2 :
      (balance <? Sevm.argWord sevm 2) :: balance ::
        Sevm.argWord sevm 2 :: ownerWord :: [] <<+ s2.stack :=
    prefix_of_balanceTooSmall hp1 hguard
  have h_burn_lookup :
      ((weth10 dp).main :: weth10Aux)[burnBalanceErrorSlot]? =
        some (Func.revWith "WETH: burn amount exceeds balance") := by
    simp [weth10, weth10Aux, burnBalanceErrorSlot, burnBalanceError]
  rcases of_run_branch_call_revWith h_burn_lookup run2 with
    ⟨s3, hpopGuard, run3⟩
  have hpopStack := hpopGuard.stack
  simp only [Stack.Pop, Split, List.nil_append, List.cons_append] at hpopStack
  rw [hpopStack] at hp2
  have h_flag : (balance <? Sevm.argWord sevm 2) = 0 :=
    pref_head_unique hp2 (pref_append [0] s3.stack)
  have h_token_le : Sevm.argWord sevm 2 ≤ balance := by
    rw [← B256.not_lt]
    intro hlt
    rw [B256.ltCheck, if_pos hlt] at h_flag
    exact B256.zero_ne_one h_flag.symm
  rw [h_flag] at hp2
  have hp3 : [balance, Sevm.argWord sevm 2, ownerWord] <<+ s3.stack :=
    cons_pref_cons_inv hp2
  have h_stor_s_s3 : Devm.getStor s = Devm.getStor s3 :=
    (Line.of_inv Devm.getStor (by line_inv) hload).trans
      ((Line.of_inv Devm.getStor (by line_inv) hguard).trans
        (PopBurn.Inv.inv hpopGuard))
  have h_balance3 :
      balance = (Devm.getStor s3 sevm.currentTarget).get ownerWord := by
    rw [h_balance, congrFun h_stor_s_s3 sevm.currentTarget]
  have h_owner_valid : ValidAdr ownerWord := by
    rw [h_owner]
    exact normalizedAddress_valid (Sevm.argWord sevm 0)
  rcases of_run_prepend debitLoadedBalance _ run3 with
    ⟨s4, hdebit, run4⟩
  obtain ⟨h_dec, h_cover, h_flash_debit⟩ :=
    debitLoadedBalance_storage h_owner_valid
      h_balance3 h_token_le hp3 hdebit
  let eventLine : Line :=
    addressArg 0 ++ arg 2 ++ [pushB256 0] ++ emitTransfer ++ [pop, pop]
  rcases of_run_prepend eventLine _ run4 with
    ⟨s5, hevent, run5⟩
  have h_stor_s4_s5 : Devm.getStor s4 = Devm.getStor s5 :=
    Line.of_inv Devm.getStor (by line_inv) hevent
  rcases of_run_prepend pushFlashMintedSlot _ run5 with
    ⟨s6, hpush1, run6⟩
  have hp6 : flashMintedSlot :: [] <<+ s6.stack :=
    prefix_of_pushFlashMintedSlot nil_pref hpush1
  rcases of_run_next run6 with ⟨s7, hloadFlash, run7⟩
  rcases prefix_of_sload hloadFlash hp6 with
    ⟨flash, hp7, h_flash_read⟩
  rcases of_run_prepend (arg 2) _ run7 with
    ⟨s8, harg2, run8⟩
  have hp8 : Sevm.argWord sevm 2 :: flash :: [] <<+ s8.stack :=
    prefix_of_arg hp7 harg2
  rcases of_run_next run8 with ⟨s9, hswap, run9⟩
  have hp9 : flash :: Sevm.argWord sevm 2 :: [] <<+ s9.stack := by
    have hswapCore : Stack.Swap (0 : Fin 16).val
        [Sevm.argWord sevm 2, flash]
        [flash, Sevm.argWord sevm 2] := Stack.swapCore_zero
    exact Stack.prefix_of_swap hswapCore (of_run_swap hswap) hp8
  rcases of_run_next run9 with ⟨s10, hsub, run10⟩
  have hp10 : (flash - Sevm.argWord sevm 2) :: [] <<+ s10.stack :=
    prefix_of_sub hsub hp9
  rcases of_run_prepend pushFlashMintedSlot _ run10 with
    ⟨s11, hpush2, run11⟩
  have hp11 : flashMintedSlot ::
      (flash - Sevm.argWord sevm 2) :: [] <<+ s11.stack :=
    prefix_of_pushFlashMintedSlot hp10 hpush2
  rcases of_run_next run11 with ⟨s12, hstoreFlash, hreturn⟩
  have h_set : Devm.getStor s12 sevm.currentTarget =
      (Devm.getStor s11 sevm.currentTarget).set flashMintedSlot
        (flash - Sevm.argWord sevm 2) :=
    sstore_getStor_set hstoreFlash hp11
  have h_stor_s12_r : Devm.getStor s12 = Devm.getStor r :=
    Func.of_inv Devm.getStor Devm.getStor (by func_inv) hreturn
  have h_stor_s5_s11 : Devm.getStor s5 = Devm.getStor s11 := by
    rw [Line.of_inv Devm.getStor (by line_inv) hpush1,
      Line.of_inv Devm.getStor (by line_inv)
        (Line.Run.cons hloadFlash Line.Run.nil),
      Line.of_inv Devm.getStor (by line_inv) harg2,
      Line.of_inv Devm.getStor (by line_inv)
        (Line.Run.cons hswap Line.Run.nil),
      Line.of_inv Devm.getStor (by line_inv)
        (Line.Run.cons hsub Line.Run.nil),
      Line.of_inv Devm.getStor (by line_inv) hpush2]
  have h_flash_read' : flash =
      (Devm.getStor s5 sevm.currentTarget).get flashMintedSlot := by
    rw [h_flash_read]
    show (Devm.getStor s6 sevm.currentTarget).get flashMintedSlot = _
    rw [← congrFun (Line.of_inv Devm.getStor (by line_inv) hpush1)
      sevm.currentTarget]
  let owner := ownerWord.toAdr
  have h_owner_key : owner.toB256 = ownerWord := by
    exact toB256_toAdr h_owner_valid
  have h_rest_s_s3 :
      Stor.rest (Devm.getStor s sevm.currentTarget) =
        Stor.rest (Devm.getStor s3 sevm.currentTarget) :=
    congrArg Stor.rest (congrFun h_stor_s_s3 sevm.currentTarget)
  have h_rest_s4_r :
      Stor.rest (Devm.getStor s4 sevm.currentTarget) =
        Stor.rest (Devm.getStor r sevm.currentTarget) := by
    rw [← congrFun h_stor_s12_r sevm.currentTarget, h_set,
      rest_set_flashMintedSlot,
      ← congrFun h_stor_s5_s11 sevm.currentTarget,
      ← congrFun h_stor_s4_s5 sevm.currentTarget]
  have h_flash_s5_s :
      (Devm.getStor s5 sevm.currentTarget).get flashMintedSlot =
        (Devm.getStor s sevm.currentTarget).get flashMintedSlot := by
    rw [← congrFun h_stor_s4_s5 sevm.currentTarget,
      h_flash_debit, ← congrFun h_stor_s_s3 sevm.currentTarget]
  have h_flash_read_s : flash =
      (Devm.getStor s sevm.currentTarget).get flashMintedSlot :=
    h_flash_read'.trans h_flash_s5_s
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [h_rest_s_s3, ← h_rest_s4_r]
    simpa only [owner, h_owner] using h_dec
  · rw [h_rest_s_s3]
    simpa only [owner, h_owner] using h_cover
  · rw [← congrFun h_stor_s12_r sevm.currentTarget, h_set,
      Stor.get_set_self, h_flash_read_s]
  · have h_bal_s_s3 : Devm.getBal s = Devm.getBal s3 :=
      (Line.of_inv Devm.getBal (by line_inv) hload).trans
        ((Line.of_inv Devm.getBal (by line_inv) hguard).trans
          (PopBurn.Inv.inv hpopGuard))
    exact h_bal_s_s3.trans
      (Func.of_inv Devm.getBal Devm.getBal (by func_inv) run3)

/-- `flashBurn` changes the normalized receiver balance and the flash counter,
but preserves every key outside both the balance region and flash slot. -/
theorem flashBurn_storage_get_of_not_valid
    (dp : DeployParams) (key : B256)
    (hkeyNotValid : ¬ ValidAdr key)
    (hkeyFlash : key ≠ flashMintedSlot)
    {sevm : Sevm} {s r : Devm}
    (run : Func.Run ((weth10 dp).main :: weth10Aux) sevm s
      flashBurn r) :
    (Devm.getStor r sevm.currentTarget).get key =
      (Devm.getStor s sevm.currentTarget).get key := by
  simp only [flashBurn] at run
  rcases of_run_prepend (loadArgBalanceAmount 0 2) _ run with
    ⟨s1, hload, run1⟩
  rcases prefix_of_loadArgBalanceAmount 0 2 nil_pref hload with
    ⟨balance, ownerWord, howner, hbalance, hp1⟩
  rcases of_run_prepend balanceTooSmall _ run1 with
    ⟨s2, hguard, run2⟩
  have hp2 :
      (balance <? Sevm.argWord sevm 2) :: balance ::
        Sevm.argWord sevm 2 :: ownerWord :: [] <<+ s2.stack :=
    prefix_of_balanceTooSmall hp1 hguard
  have hlookup :
      ((weth10 dp).main :: weth10Aux)[burnBalanceErrorSlot]? =
        some (Func.revWith "WETH: burn amount exceeds balance") := by
    simp [weth10, weth10Aux, burnBalanceErrorSlot, burnBalanceError]
  rcases of_run_branch_call_revWith hlookup run2 with
    ⟨s3, hpopGuard, run3⟩
  have hpopStack := hpopGuard.stack
  simp only [Stack.Pop, Split, List.nil_append, List.cons_append] at hpopStack
  rw [hpopStack] at hp2
  have hflag : (balance <? Sevm.argWord sevm 2) = 0 :=
    pref_head_unique hp2 (pref_append [0] s3.stack)
  rw [hflag] at hp2
  have hp3 : [balance, Sevm.argWord sevm 2, ownerWord] <<+ s3.stack :=
    cons_pref_cons_inv hp2
  have hstor_s_s3 : Devm.getStor s = Devm.getStor s3 :=
    (Line.of_inv Devm.getStor (by line_inv) hload).trans
      ((Line.of_inv Devm.getStor (by line_inv) hguard).trans
        (PopBurn.Inv.inv hpopGuard))
  have hownerValid : ValidAdr ownerWord := by
    rw [howner]
    exact normalizedAddress_valid (Sevm.argWord sevm 0)
  have hkeyOwner : key ≠ ownerWord := by
    intro heq
    apply hkeyNotValid
    rw [heq]
    exact hownerValid
  rcases of_run_prepend debitLoadedBalance _ run3 with
    ⟨s4, hdebit, run4⟩
  have hdebitKey := debitLoadedBalance_storage_get_ne hkeyOwner hp3
    hdebit
  let eventLine : Line :=
    addressArg 0 ++ arg 2 ++ [pushB256 0] ++ emitTransfer ++ [pop, pop]
  rcases of_run_prepend eventLine _ run4 with
    ⟨s5, hevent, run5⟩
  have hstor_s4_s5 : Devm.getStor s4 = Devm.getStor s5 :=
    Line.of_inv Devm.getStor (by line_inv) hevent
  rcases of_run_prepend pushFlashMintedSlot _ run5 with
    ⟨s6, hpush1, run6⟩
  have hp6 : flashMintedSlot :: [] <<+ s6.stack :=
    prefix_of_pushFlashMintedSlot nil_pref hpush1
  rcases of_run_next run6 with ⟨s7, hloadFlash, run7⟩
  rcases prefix_of_sload hloadFlash hp6 with
    ⟨flash, hp7, hflashRead⟩
  rcases of_run_prepend (arg 2) _ run7 with
    ⟨s8, harg2, run8⟩
  have hp8 : Sevm.argWord sevm 2 :: flash :: [] <<+ s8.stack :=
    prefix_of_arg hp7 harg2
  rcases of_run_next run8 with ⟨s9, hswap, run9⟩
  have hp9 : flash :: Sevm.argWord sevm 2 :: [] <<+ s9.stack := by
    have hswapCore : Stack.Swap (0 : Fin 16).val
        [Sevm.argWord sevm 2, flash]
        [flash, Sevm.argWord sevm 2] := Stack.swapCore_zero
    exact Stack.prefix_of_swap hswapCore (of_run_swap hswap) hp8
  rcases of_run_next run9 with ⟨s10, hsub, run10⟩
  have hp10 : (flash - Sevm.argWord sevm 2) :: [] <<+ s10.stack :=
    prefix_of_sub hsub hp9
  rcases of_run_prepend pushFlashMintedSlot _ run10 with
    ⟨s11, hpush2, run11⟩
  have hp11 : flashMintedSlot ::
      (flash - Sevm.argWord sevm 2) :: [] <<+ s11.stack :=
    prefix_of_pushFlashMintedSlot hp10 hpush2
  rcases of_run_next run11 with ⟨s12, hstoreFlash, hreturn⟩
  have hset : Devm.getStor s12 sevm.currentTarget =
      (Devm.getStor s11 sevm.currentTarget).set flashMintedSlot
        (flash - Sevm.argWord sevm 2) :=
    sstore_getStor_set hstoreFlash hp11
  have hstor_s12_r : Devm.getStor s12 = Devm.getStor r :=
    Func.of_inv Devm.getStor Devm.getStor (by func_inv) hreturn
  have hstor_s5_s11 : Devm.getStor s5 = Devm.getStor s11 := by
    rw [Line.of_inv Devm.getStor (by line_inv) hpush1,
      Line.of_inv Devm.getStor (by line_inv)
        (Line.Run.cons hloadFlash Line.Run.nil),
      Line.of_inv Devm.getStor (by line_inv) harg2,
      Line.of_inv Devm.getStor (by line_inv)
        (Line.Run.cons hswap Line.Run.nil),
      Line.of_inv Devm.getStor (by line_inv)
        (Line.Run.cons hsub Line.Run.nil),
      Line.of_inv Devm.getStor (by line_inv) hpush2]
  calc
    (Devm.getStor r sevm.currentTarget).get key =
        (Devm.getStor s12 sevm.currentTarget).get key := by
            rw [congrFun hstor_s12_r sevm.currentTarget]
    _ = (Devm.getStor s11 sevm.currentTarget).get key := by
            rw [hset, Stor.get_set_ne _ hkeyFlash.symm]
    _ = (Devm.getStor s5 sevm.currentTarget).get key := by
            rw [congrFun hstor_s5_s11 sevm.currentTarget]
    _ = (Devm.getStor s4 sevm.currentTarget).get key := by
            rw [congrFun hstor_s4_s5 sevm.currentTarget]
    _ = (Devm.getStor s3 sevm.currentTarget).get key := hdebitKey
    _ = (Devm.getStor s sevm.currentTarget).get key := by
            rw [congrFun hstor_s_s3 sevm.currentTarget]

/-- Existential-owner projection of `flashBurn_storage_at_receiver`, retained
for the original backing-preservation consumers. -/
theorem flashBurn_storage
    (dp : DeployParams) {sevm : Sevm} {s r : Devm}
    (run : Func.Run ((weth10 dp).main :: weth10Aux) sevm s
      flashBurn r) :
    ∃ owner : Adr,
      Decrease owner (Sevm.argWord sevm 2)
        (Stor.rest (Devm.getStor s sevm.currentTarget))
        (Stor.rest (Devm.getStor r sevm.currentTarget)) ∧
      Sevm.argWord sevm 2 ≤
        Stor.rest (Devm.getStor s sevm.currentTarget) owner ∧
      (Devm.getStor r sevm.currentTarget).get flashMintedSlot =
        (Devm.getStor s sevm.currentTarget).get flashMintedSlot -
          Sevm.argWord sevm 2 ∧
      Devm.getBal s = Devm.getBal r := by
  refine ⟨((~~~ addressMask) &&& Sevm.argWord sevm 0).toAdr, ?_⟩
  exact flashBurn_storage_at_receiver dp run

/-- Flash settlement's allowance phase is WETH10-silent and tail-jumps to the
single exact burn continuation on both max and finite allowance paths. -/
theorem of_run_flashSettle
    (dp : DeployParams) {sevm : Sevm} {s r : Devm}
    (run : Func.Run ((weth10 dp).main :: weth10Aux) sevm s
      flashSettle r) :
    ∃ sc,
      Func.Run ((weth10 dp).main :: weth10Aux) sevm sc flashBurn r ∧
      Stor.Weth10Silent
        (Devm.getStor s sevm.currentTarget)
        (Devm.getStor sc sevm.currentTarget) ∧
      Devm.getBal s = Devm.getBal sc ∧
      s.getCode sevm.currentTarget = sc.getCode sevm.currentTarget := by
  unfold flashSettle at run
  let loadLine : Line :=
    addressArg 0 ++ mstoreAt 0 ++ [address] ++ mstoreAt 1 ++
      allowanceKeyFromMemory ++ [dup 0, sload, dup 0] ++ isMax
  rcases of_run_prepend loadLine _ run with ⟨sl, hload, runLoad⟩
  have h_stor_s_sl : Devm.getStor s = Devm.getStor sl :=
    Line.of_inv Devm.getStor (by line_inv) hload
  have h_bal_s_sl : Devm.getBal s = Devm.getBal sl :=
    Line.of_inv Devm.getBal (by line_inv) hload
  have h_code_s_sl :
      s.getCode sevm.currentTarget = sl.getCode sevm.currentTarget :=
    congrFun (Line.of_inv Devm.getCode (by line_inv) hload)
      sevm.currentTarget
  obtain ⟨hash, allowance, hallowance, hpLoad⟩ :=
    prefix_of_selfAllowanceIsMax 0 nil_pref (by
      simpa only [loadLine] using hload)
  let key := allowanceTagWord ||| (allowancePayloadMask &&& hash)
  have h_burn_lookup :
      ((weth10 dp).main :: weth10Aux)[flashBurnSlot]? = some flashBurn := by
    simp [weth10, weth10Aux, flashBurnSlot]
  rcases of_run_branch runLoad with
      ⟨sf, hfinitePop, hfinite⟩ |
      ⟨wmax, sm1, sm2, hnzmax, hmaxPop, hmaxBurn, hmax⟩
  · have hfiniteStack := hfinitePop.stack
    simp only [Stack.Pop, Split, List.nil_append, List.cons_append] at hfiniteStack
    rw [hfiniteStack] at hpLoad
    have hmaxFlag : ((~~~ allowance) =? 0) = 0 :=
      pref_head_unique hpLoad (pref_append [0] sf.stack)
    rw [hmaxFlag] at hpLoad
    have hpFinite : allowance :: key :: [] <<+ sf.stack :=
      cons_pref_cons_inv hpLoad
    let guardLine : Line := arg 2 ++ [swap 0] ++ balanceTooSmall
    rcases of_run_prepend guardLine _ hfinite with
      ⟨sg, hguardLine, runGuard⟩
    have hpGuard :
        (allowance <? Sevm.argWord sevm 2) :: allowance ::
          Sevm.argWord sevm 2 :: key :: [] <<+ sg.stack := by
      unfold guardLine at hguardLine
      rcases of_run_append (arg 2) hguardLine with
        ⟨sa, hamount, hguard1⟩
      have hpa : Sevm.argWord sevm 2 :: allowance :: key :: [] <<+
          sa.stack := prefix_of_arg hpFinite hamount
      rcases Line.of_run_cons hguard1 with
        ⟨ss, hswap, htooSmall⟩
      have hswapCore : Stack.Swap (0 : Fin 16).val
          [Sevm.argWord sevm 2, allowance, key]
          [allowance, Sevm.argWord sevm 2, key] := Stack.swapCore_zero
      have hps : allowance :: Sevm.argWord sevm 2 :: key :: [] <<+
          ss.stack :=
        Stack.prefix_of_swap hswapCore (of_run_swap hswap) hpa
      exact prefix_of_balanceTooSmall hps htooSmall
    have h_allowance_lookup :
        ((weth10 dp).main :: weth10Aux)[allowanceErrorSlot]? =
          some (Func.revWith "WETH: request exceeds allowance") := by
      simp [weth10, weth10Aux, allowanceErrorSlot, allowanceError]
    rcases of_run_branch_call_revWith h_allowance_lookup runGuard with
      ⟨sb, hguardPop, runMutate⟩
    have hguardStack := hguardPop.stack
    simp only [Stack.Pop, Split, List.nil_append, List.cons_append] at hguardStack
    rw [hguardStack] at hpGuard
    have hguardFlag : (allowance <? Sevm.argWord sevm 2) = 0 :=
      pref_head_unique hpGuard (pref_append [0] sb.stack)
    rw [hguardFlag] at hpGuard
    have hpBeforeMutate :
        allowance :: Sevm.argWord sevm 2 :: key :: [] <<+ sb.stack :=
      cons_pref_cons_inv hpGuard
    let mutateLine : Line :=
      [sub, dup 0, swap 1, sstore] ++ emitFlashApproval
    rcases of_run_prepend mutateLine _ runMutate with
      ⟨scall, hmutate, hcallRun⟩
    unfold mutateLine at hmutate
    rcases Line.of_run_cons hmutate with ⟨ms1, hsub, hmutate1⟩
    have hpSub :
        (allowance - Sevm.argWord sevm 2) :: key :: [] <<+ ms1.stack :=
      prefix_of_sub hsub hpBeforeMutate
    rcases Line.of_run_cons hmutate1 with ⟨ms2, hdup, hmutate2⟩
    have hpDup :
        (allowance - Sevm.argWord sevm 2) ::
          (allowance - Sevm.argWord sevm 2) :: key :: [] <<+ ms2.stack :=
      prefix_of_dup_val hdup (by show_nth) hpSub
    rcases Line.of_run_cons hmutate2 with ⟨ms3, hswap, hmutate3⟩
    have hswapCore : Stack.Swap (1 : Fin 16).val
        ((allowance - Sevm.argWord sevm 2) ::
          (allowance - Sevm.argWord sevm 2) :: key :: [])
        (key :: (allowance - Sevm.argWord sevm 2) ::
          (allowance - Sevm.argWord sevm 2) :: []) :=
      Stack.swapCore_succ Stack.swapCore_zero
    have hpStore :
        key :: (allowance - Sevm.argWord sevm 2) ::
          (allowance - Sevm.argWord sevm 2) :: [] <<+ ms3.stack :=
      Stack.prefix_of_swap hswapCore (of_run_swap hswap) hpDup
    rcases Line.of_run_cons hmutate3 with
      ⟨ms4, hstore, happroval⟩
    have hset : Devm.getStor ms4 sevm.currentTarget =
        (Devm.getStor ms3 sevm.currentTarget).set key
          (allowance - Sevm.argWord sevm 2) :=
      sstore_getStor_set hstore hpStore
    rcases of_run_call hcallRun with
      ⟨f, sc, hget, hcallBurn, hcore⟩
    have hf : f = flashBurn := by
      rw [h_burn_lookup] at hget
      exact Option.some.inj hget.symm
    subst f
    have h_stor_s_ms3 : Devm.getStor s = Devm.getStor ms3 :=
      h_stor_s_sl.trans
        ((PopBurn.Inv.inv hfinitePop).trans
          ((Line.of_inv Devm.getStor (by line_inv) hguardLine).trans
            ((PopBurn.Inv.inv hguardPop).trans
              ((Line.of_inv Devm.getStor (by line_inv)
                (Line.Run.cons hsub Line.Run.nil)).trans
                ((Line.of_inv Devm.getStor (by line_inv)
                  (Line.Run.cons hdup Line.Run.nil)).trans
                  (Line.of_inv Devm.getStor (by line_inv)
                    (Line.Run.cons hswap Line.Run.nil)))))))
    have h_stor_scall_sc : Devm.getStor scall = Devm.getStor sc :=
      Burn.Inv.inv hcallBurn
    have h_stor_ms4_scall : Devm.getStor ms4 = Devm.getStor scall :=
      Line.of_inv Devm.getStor (by line_inv) happroval
    have h_stor_sc : Devm.getStor sc sevm.currentTarget =
        (Devm.getStor s sevm.currentTarget).set key
          (allowance - Sevm.argWord sevm 2) := by
      rw [← congrFun h_stor_scall_sc sevm.currentTarget,
        ← congrFun h_stor_ms4_scall sevm.currentTarget, hset,
        ← congrFun h_stor_s_ms3 sevm.currentTarget]
    have h_bal_s_sc : Devm.getBal s = Devm.getBal sc :=
      h_bal_s_sl.trans
        ((PopBurn.Inv.inv hfinitePop).trans
          ((Line.of_inv Devm.getBal (by line_inv) hguardLine).trans
            ((PopBurn.Inv.inv hguardPop).trans
              ((Line.of_inv Devm.getBal (by line_inv) hmutate).trans
                (Burn.Inv.inv hcallBurn)))))
    have h_code_s_sc :
        s.getCode sevm.currentTarget = sc.getCode sevm.currentTarget :=
      h_code_s_sl.trans
        ((getCode_eq_of_state_eq hfinitePop.state sevm.currentTarget).trans
          ((congrFun (Line.of_inv Devm.getCode (by line_inv) hguardLine)
            sevm.currentTarget).trans
            ((getCode_eq_of_state_eq hguardPop.state
              sevm.currentTarget).trans
              ((congrFun (Line.of_inv Devm.getCode (by line_inv) hmutate)
                sevm.currentTarget).trans
                (getCode_eq_of_state_eq hcallBurn.state
                  sevm.currentTarget)))))
    refine ⟨sc, hcore, ?_, h_bal_s_sc, h_code_s_sc⟩
    rw [h_stor_sc]
    exact Stor.Weth10Silent.set
      (runtimeAllowanceKey_not_valid hash)
      (runtimeAllowanceKey_ne_flash hash)
  · rcases of_run_next hmax with ⟨sm3, hpop1, hmax1⟩
    rcases of_run_next hmax1 with ⟨sm4, hpop2, hcallRun⟩
    rcases of_run_call hcallRun with
      ⟨f, sc, hget, hcallBurn, hcore⟩
    have hf : f = flashBurn := by
      rw [h_burn_lookup] at hget
      exact Option.some.inj hget.symm
    subst f
    let hpops : Line.Run sevm sm2 [pop, pop] sm4 :=
      Line.Run.cons hpop1 (Line.Run.cons hpop2 Line.Run.nil)
    have h_stor_s_sc : Devm.getStor s = Devm.getStor sc :=
      h_stor_s_sl.trans
        ((PopBurn.Inv.inv hmaxPop).trans
          ((Burn.Inv.inv hmaxBurn).trans
            ((Line.of_inv Devm.getStor (by line_inv) hpops).trans
              (Burn.Inv.inv hcallBurn))))
    have h_bal_s_sc : Devm.getBal s = Devm.getBal sc :=
      h_bal_s_sl.trans
        ((PopBurn.Inv.inv hmaxPop).trans
          ((Burn.Inv.inv hmaxBurn).trans
            ((Line.of_inv Devm.getBal (by line_inv) hpops).trans
              (Burn.Inv.inv hcallBurn))))
    have h_code_s_sc :
        s.getCode sevm.currentTarget = sc.getCode sevm.currentTarget :=
      h_code_s_sl.trans
        ((getCode_eq_of_state_eq hmaxPop.state sevm.currentTarget).trans
          ((getCode_eq_of_state_eq hmaxBurn.state sevm.currentTarget).trans
            ((congrFun (Line.of_inv Devm.getCode (by line_inv) hpops)
              sevm.currentTarget).trans
              (getCode_eq_of_state_eq hcallBurn.state
                sevm.currentTarget))))
    exact ⟨sc, hcore,
      Stor.Weth10Silent.of_eq
        (congrFun h_stor_s_sc sevm.currentTarget),
      h_bal_s_sc, h_code_s_sc⟩

/-- Settling a callback that retained the dynamically minted floor burns the
loan amount, restores the caller's prior floor, and preserves backing. -/
theorem flashSettle_backed_floor
    (dp : DeployParams) {base : B256} {sevm : Sevm} {s r : Devm}
    (h_nof : B256.Nof base (Sevm.argWord sevm 2))
    (h_floor : Stor.FlashFloor (base + Sevm.argWord sevm 2)
      (Devm.getStor s sevm.currentTarget))
    (h_inv : Stor.Weth10Inv
      (Devm.getStor s sevm.currentTarget) sevm.value
      (Devm.getBal s sevm.currentTarget))
    (run : Func.Run ((weth10 dp).main :: weth10Aux) sevm s
      flashSettle r) :
    Stor.Weth10Inv
        (Devm.getStor r sevm.currentTarget) sevm.value
        (Devm.getBal r sevm.currentTarget) ∧
      Stor.FlashFloor base
        (Devm.getStor r sevm.currentTarget) := by
  obtain ⟨sc, hburnRun, hsilent, hbal, hcode⟩ :=
    of_run_flashSettle dp run
  have h_inv_sc : Stor.Weth10Inv
      (Devm.getStor sc sevm.currentTarget) sevm.value
      (Devm.getBal sc sevm.currentTarget) := by
    rw [← congrFun hbal sevm.currentTarget]
    exact h_inv.silent hsilent
  have h_floor_sc : Stor.FlashFloor
      (base + Sevm.argWord sevm 2)
      (Devm.getStor sc sevm.currentTarget) := by
    unfold Stor.FlashFloor at h_floor ⊢
    rw [hsilent.2]
    exact h_floor
  obtain ⟨owner, hdec, hcover, hflash, h_bal_sc_r⟩ :=
    flashBurn_storage dp hburnRun
  have h_inv_sc' : Stor.Weth10Inv
      (Devm.getStor sc sevm.currentTarget) sevm.value
      (Devm.getBal r sevm.currentTarget) := by
    rw [← congrFun h_bal_sc_r sevm.currentTarget]
    exact h_inv_sc
  have h_amount_le_minted : Sevm.argWord sevm 2 ≤
      base + Sevm.argWord sevm 2 := by
    rw [B256.add_comm]
    exact B256.le_add_right (by
      simpa only [B256.Nof, Nat.add_comm] using h_nof)
  have h_amount_le_flash : Sevm.argWord sevm 2 ≤
      (Devm.getStor sc sevm.currentTarget).get flashMintedSlot :=
    B256.le_trans h_amount_le_minted h_floor_sc.2
  constructor
  · exact Stor.Weth10Inv.flashBurn
      (s := Devm.getStor sc sevm.currentTarget)
      (s' := Devm.getStor r sevm.currentTarget)
      (a := owner) (cv := sevm.value)
      (b := Devm.getBal r sevm.currentTarget)
      (x := Sevm.argWord sevm 2)
      h_inv_sc' hdec hcover h_amount_le_flash hflash
  · unfold Stor.FlashFloor
    rw [hflash, B256.toNat_sub_eq_of_le _ _ h_amount_le_flash]
    have h_minted_nat :
        (base + Sevm.argWord sevm 2).toNat =
          base.toNat + (Sevm.argWord sevm 2).toNat :=
      B256.toNat_add_eq_of_nof _ _ h_nof
    have h_lower := B256.toNat_le_toNat h_floor_sc.2
    rw [h_minted_nat] at h_lower
    constructor
    · exact Nat.le_trans (Nat.sub_le _ _) h_floor_sc.1
    · rw [B256.le_iff_toNat_le_toNat]
      rw [B256.toNat_sub_eq_of_le _ _ h_amount_le_flash]
      omega

/-- Floor-only projection of successful flash settlement.  This is the piece
used by the recursive exact/floor dispatch closure; backing remains handled by
`flashSettle_backed_floor`. -/
theorem flashSettle_floor
    (dp : DeployParams) {base : B256} {sevm : Sevm} {s r : Devm}
    (h_nof : B256.Nof base (Sevm.argWord sevm 2))
    (h_floor : Stor.FlashFloor (base + Sevm.argWord sevm 2)
      (Devm.getStor s sevm.currentTarget))
    (run : Func.Run ((weth10 dp).main :: weth10Aux) sevm s
      flashSettle r) :
    Stor.FlashFloor base
      (Devm.getStor r sevm.currentTarget) := by
  obtain ⟨sc, hburnRun, hsilent, hbal, hcode⟩ :=
    of_run_flashSettle dp run
  have h_floor_sc : Stor.FlashFloor
      (base + Sevm.argWord sevm 2)
      (Devm.getStor sc sevm.currentTarget) := by
    unfold Stor.FlashFloor at h_floor ⊢
    rw [hsilent.2]
    exact h_floor
  obtain ⟨owner, hdec, hcover, hflash, h_bal_sc_r⟩ :=
    flashBurn_storage dp hburnRun
  have h_amount_le_minted : Sevm.argWord sevm 2 ≤
      base + Sevm.argWord sevm 2 := by
    rw [B256.add_comm]
    exact B256.le_add_right (by
      simpa only [B256.Nof, Nat.add_comm] using h_nof)
  have h_amount_le_flash : Sevm.argWord sevm 2 ≤
      (Devm.getStor sc sevm.currentTarget).get flashMintedSlot :=
    B256.le_trans h_amount_le_minted h_floor_sc.2
  unfold Stor.FlashFloor
  rw [hflash, B256.toNat_sub_eq_of_le _ _ h_amount_le_flash]
  have h_minted_nat :
      (base + Sevm.argWord sevm 2).toNat =
        base.toNat + (Sevm.argWord sevm 2).toNat :=
    B256.toNat_add_eq_of_nof _ _ h_nof
  have h_lower := B256.toNat_le_toNat h_floor_sc.2
  rw [h_minted_nat] at h_lower
  constructor
  · exact Nat.le_trans (Nat.sub_le _ _) h_floor_sc.1
  · rw [B256.le_iff_toNat_le_toNat]
    rw [B256.toNat_sub_eq_of_le _ _ h_amount_le_flash]
    omega

/-- Successful flash settlement does not change any account balance. -/
theorem flashSettle_balance
    (dp : DeployParams) {sevm : Sevm} {s r : Devm}
    (run : Func.Run ((weth10 dp).main :: weth10Aux) sevm s
      flashSettle r) :
    Devm.getBal s = Devm.getBal r := by
  obtain ⟨sc, hburnRun, hsilent, hbal, hcode⟩ :=
    of_run_flashSettle dp run
  obtain ⟨owner, hdec, hcover, hflash, h_bal_sc_r⟩ :=
    flashBurn_storage dp hburnRun
  exact hbal.trans h_bal_sc_r

/-- The exact suffix of WETH10 `flashLoan` beginning at the borrower call. -/
def flashLoanFromCall : Func :=
  call ::: iszero :::
  (.call bubbleRevertSlot) <?>
  (retdataShorterThan 32 +++
    Func.rev <?>
    (checkRetdataHead CALLBACK_SUCCESS 0 +++ iszero :::
      (.call flashFailedErrorSlot) <?>
      (pop ::: pop ::: .call flashSettleSlot)))

/-- A successful `EXTCODESIZE` replaces its address operand by one size word
and preserves every known stack-tail word. -/
theorem of_extcodesize_frame
    {e : Sevm} {s r : Devm} {x : B256} {xs : Stack}
    (hp : x :: xs <<+ s.stack)
    (run : Ninst.Run e s extcodesize r) :
    ∃ size, size :: xs <<+ r.stack ∧ s.memory = r.memory := by
  rcases of_run_reg run with ⟨pc, hrun⟩
  simp only [Rinst.run, Rinst.runCore] at hrun
  rcases Except.bind_eq_ok hrun with
    ⟨⟨adr, d1⟩, hpopAdr, hrun⟩
  rw [Devm.popToAdr_def] at hpopAdr
  dsimp [(· <&> ·), Functor.mapRev, Functor.map, Except.map] at hpopAdr
  rcases hpop : Devm.pop s with _ | ⟨word, d0⟩ <;>
    simp [hpop] at hpopAdr
  rcases hpopAdr with ⟨rfl, rfl⟩
  have hpop' := Devm.pop_of_pop hpop
  have hx : x = word :=
    (List.of_cons_pref_of_cons_pref hp
      (pref_of_split hpop'.stack)).left
  subst word
  have htail : xs <<+ d0.stack :=
    of_append_pref hpop'.stack hp
  split at hrun
  · rcases Except.bind_eq_ok hrun with
      ⟨d2, hgas, hpush⟩
    refine ⟨_, append_pref (Devm.push_of_push hpush).stack ?_, ?_⟩
    · rw [← (Devm.burn_of_chargeGas hgas).stack]
      exact htail
    · exact hpop'.memory.trans
        ((Devm.burn_of_chargeGas hgas).memory.trans
          (Devm.push_of_push hpush).memory)
  · rcases Except.bind_eq_ok hrun with
      ⟨d2, hgas, hpush⟩
    refine ⟨_, append_pref (Devm.push_of_push hpush).stack ?_, ?_⟩
    · rw [← (Devm.burn_of_chargeGas hgas).stack]
      exact htail
    · exact hpop'.memory.trans
        ((show d0.memory = (addAccessedAddress d0 x.toAdr).memory from rfl).trans
          ((Devm.burn_of_chargeGas hgas).memory.trans
            (Devm.push_of_push hpush).memory))

/-- Stack-only projection of `of_extcodesize_frame`. -/
theorem prefix_of_extcodesize
    {e : Sevm} {s r : Devm} {x : B256} {xs : Stack}
    (hp : x :: xs <<+ s.stack)
    (run : Ninst.Run e s extcodesize r) :
    ∃ size, size :: xs <<+ r.stack := by
  rcases of_extcodesize_frame hp run with ⟨size, hp', _⟩
  exact ⟨size, hp'⟩

/-- The static flash-callback ABI head consumes the duplicate amount word,
preserves the retained amount/receiver tail, and writes the six canonical ABI
head words. -/
theorem of_storeFlashCallbackHead_frame
    {e : Sevm} {s r : Devm} {amount : B256} {xs : Stack}
    (hp : amount :: amount :: xs <<+ s.stack)
    (run : Line.Run e s storeFlashCallbackHead r) :
    amount :: xs <<+ r.stack ∧
      r.memory =
        ((((((s.memory.write 0 onFlashLoanSelector.toBytes).write
          32 e.caller.toB256.toBytes).write
          64 e.currentTarget.toB256.toBytes).write
          96 amount.toBytes).write
          128 (0 : B256).toBytes).write
          160 (0xa0 : B256).toBytes) := by
  unfold storeFlashCallbackHead at run
  rcases Line.of_run_cons run with ⟨s1, hselector, run1⟩
  have hb1 := of_run_pushB256 hselector
  have hp1 := prefix_of_push hb1 hp
  rcases of_run_append (mstoreAt 0) run1 with
    ⟨s2, hstore0, run2⟩
  rcases of_run_mstoreAt_val hstore0 hp1 with ⟨hp2, hm2⟩
  have e2 : s2.memory =
      s.memory.write 0 onFlashLoanSelector.toBytes := by
    rw [hm2, ← hb1.memory]
    rfl
  rcases Line.of_run_cons run2 with ⟨s3, hcaller, run3⟩
  have hb3 := of_run_caller hcaller
  have hp3 := prefix_of_push hb3 hp2
  rcases of_run_append (mstoreAt 1) run3 with
    ⟨s4, hstore1, run4⟩
  rcases of_run_mstoreAt_val hstore1 hp3 with ⟨hp4, hm4⟩
  have e4 : s4.memory =
      (s.memory.write 0 onFlashLoanSelector.toBytes).write
        32 e.caller.toB256.toBytes := by
    rw [hm4, ← hb3.memory, e2]
    rfl
  rcases Line.of_run_cons run4 with ⟨s5, haddress, run5⟩
  have hb5 := of_run_address haddress
  have hp5 := prefix_of_push hb5 hp4
  rcases of_run_append (mstoreAt 2) run5 with
    ⟨s6, hstore2, run6⟩
  rcases of_run_mstoreAt_val hstore2 hp5 with ⟨hp6, hm6⟩
  have e6 : s6.memory =
      ((s.memory.write 0 onFlashLoanSelector.toBytes).write
        32 e.caller.toB256.toBytes).write
        64 e.currentTarget.toB256.toBytes := by
    rw [hm6, ← hb5.memory, e4]
    rfl
  rcases of_run_append (mstoreAt 3) run6 with
    ⟨s7, hstore3, run7⟩
  rcases of_run_mstoreAt_val hstore3 hp6 with ⟨hp7, hm7⟩
  have e7 : s7.memory =
      (((s.memory.write 0 onFlashLoanSelector.toBytes).write
        32 e.caller.toB256.toBytes).write
        64 e.currentTarget.toB256.toBytes).write
        96 amount.toBytes := by
    rw [hm7, e6]
    rfl
  rcases Line.of_run_cons run7 with ⟨s8, hzero, run8⟩
  have hb8 := of_run_pushB256 hzero
  have hp8 := prefix_of_push hb8 hp7
  rcases of_run_append (mstoreAt 4) run8 with
    ⟨s9, hstore4, run9⟩
  rcases of_run_mstoreAt_val hstore4 hp8 with ⟨hp9, hm9⟩
  have e9 : s9.memory =
      ((((s.memory.write 0 onFlashLoanSelector.toBytes).write
        32 e.caller.toB256.toBytes).write
        64 e.currentTarget.toB256.toBytes).write
        96 amount.toBytes).write 128 (0 : B256).toBytes := by
    rw [hm9, ← hb8.memory, e7]
    rfl
  rcases Line.of_run_cons run9 with ⟨s10, hoffset, run10⟩
  have hb10 := of_run_pushB256 hoffset
  have hp10 := prefix_of_push hb10 hp9
  rcases of_run_mstoreAt_val run10 hp10 with ⟨hp11, hm11⟩
  exact ⟨hp11, by rw [hm11, ← hb10.memory, e9]; rfl⟩

/-- Stack-only projection of `of_storeFlashCallbackHead_frame`. -/
theorem prefix_of_storeFlashCallbackHead
    {e : Sevm} {s r : Devm} {amount : B256} {xs : Stack}
    (hp : amount :: amount :: xs <<+ s.stack)
    (run : Line.Run e s storeFlashCallbackHead r) :
    amount :: xs <<+ r.stack :=
  (of_storeFlashCallbackHead_frame hp run).1

/-- The flash callback size fragment preserves the stack tail and replaces its
head length by one computed call-input size. -/
theorem prefix_of_flashCallbackArgsSize_exact
    {e : Sevm} {s r : Devm} {x : B256} {xs : Stack}
    (hp : x :: xs <<+ s.stack)
    (run : Line.Run e s flashCallbackArgsSize r) :
    (0xc4 + ((~~~ (31 : B256)) &&& (31 + x))) :: xs <<+ r.stack := by
  unfold flashCallbackArgsSize at run
  rcases Line.of_run_cons run with ⟨s1, h31a, run1⟩
  have hp1 : (31 : B256) :: x :: xs <<+ s1.stack :=
    prefix_of_push (of_run_pushB256 h31a) hp
  rcases Line.of_run_cons run1 with ⟨s2, hadd1, run2⟩
  have hp2 := prefix_of_add hadd1 hp1
  rcases Line.of_run_cons run2 with ⟨s3, h31b, run3⟩
  have hp3 : (31 : B256) :: (31 + x) :: xs <<+ s3.stack :=
    prefix_of_push (of_run_pushB256 h31b) hp2
  rcases Line.of_run_cons run3 with ⟨s4, hnot, run4⟩
  have hp4 := prefix_of_not hnot hp3
  rcases Line.of_run_cons run4 with ⟨s5, hand, run5⟩
  have hp5 := prefix_of_and hand hp4
  rcases Line.of_run_cons run5 with ⟨s6, hsize, run6⟩
  have hp6 : (0xc4 : B256) ::
      ((~~~ (31 : B256)) &&& (31 + x)) :: xs <<+ s6.stack :=
    prefix_of_push (of_run_pushB256 hsize) hp5
  rcases Line.of_run_cons run6 with ⟨s7, hadd2, hnil⟩
  cases hnil
  exact prefix_of_add hadd2 hp6

/-- Existential compatibility projection of the exact callback-size walk. -/
theorem prefix_of_flashCallbackArgsSize
    {e : Sevm} {s r : Devm} {x : B256} {xs : Stack}
    (hp : x :: xs <<+ s.stack)
    (run : Line.Run e s flashCallbackArgsSize r) :
    ∃ y, y :: xs <<+ r.stack :=
  ⟨_, prefix_of_flashCallbackArgsSize_exact hp run⟩

/-- A successful `flashLoan` reaches the borrower `CALL` only after the
bounded flash-counter write and normalized receiver credit have both
completed.  The conclusion exposes exactly the state and stack facts needed
by the relational floor proof. -/
theorem of_flashLoan_toCall_frame
    (dp : DeployParams) {sevm : Sevm} {s r : Devm}
    (run : Func.Run ((weth10 dp).main :: weth10Aux) sevm s flashLoan r) :
    ∃ (recipient : Adr) (sc : Devm) (g inputSize base : B256),
      base = (Devm.getStor s sevm.currentTarget).get flashMintedSlot ∧
      recipient.toB256 =
        ((~~~ addressMask) &&& Sevm.argWord sevm 0) ∧
      Sevm.argWord sevm 1 = sevm.currentTarget.toB256 ∧
      Sevm.argWord sevm 2 ≤ maxUint112 ∧
      base + Sevm.argWord sevm 2 ≤ maxUint112 ∧
      Increase recipient (Sevm.argWord sevm 2)
        (Stor.rest (Devm.getStor s sevm.currentTarget))
        (Stor.rest (Devm.getStor sc sevm.currentTarget)) ∧
      (Devm.getStor sc sevm.currentTarget).get flashMintedSlot =
        base + Sevm.argWord sevm 2 ∧
      Devm.getCode s = Devm.getCode sc ∧
      Devm.getBal s = Devm.getBal sc ∧
      inputSize =
        0xc4 + ((~~~ (31 : B256)) &&&
          (31 + Sevm.tailLen sevm 3)) ∧
      (g :: recipient.toB256 :: (0 : B256) :: callbackArgsOffset ::
        inputSize :: 0 :: 0 ::
        [Sevm.argWord sevm 2, recipient.toB256] <<+ sc.stack) ∧
      (∀ img, Mem.Wf s.memory → Mem.Reads s.memory img →
        Mem.Wf sc.memory ∧
          Mem.Reads sc.memory
            (Bytes.writeAt
              (Bytes.writeAt
                (Bytes.writeAt
                  (Bytes.writeAt
                    (Bytes.writeAt
                      (Bytes.writeAt
                        (Bytes.writeAt
                          (Bytes.writeAt
                            (Bytes.writeAt img 0
                              (Sevm.argWord sevm 2).toBytes)
                            0 onFlashLoanSelector.toBytes)
                          32 sevm.caller.toB256.toBytes)
                        64 sevm.currentTarget.toB256.toBytes)
                      96 (Sevm.argWord sevm 2).toBytes)
                    128 (0 : B256).toBytes)
                  160 (0xa0 : B256).toBytes)
                192 (Sevm.tailLen sevm 3).toBytes)
              224 (Sevm.tailBytes sevm 3))) ∧
      sc.logs = s.logs ++
        [⟨sevm.currentTarget,
          [Blanc.transferEvent, 0, recipient.toB256],
          (Sevm.argWord sevm 2).toBytes⟩] ∧
      sc.output = s.output ∧
      Func.Run ((weth10 dp).main :: weth10Aux) sevm sc
        flashLoanFromCall r := by
  simp only [flashLoan] at run
  let tokenLine : Line := arg 1 ++ [address, eq, iszero]
  rcases of_run_prepend tokenLine _ run with
    ⟨st0, htoken, run0⟩
  have hstor : Devm.getStor s = Devm.getStor st0 :=
    Line.of_inv Devm.getStor (by line_inv) htoken
  have hcode : Devm.getCode s = Devm.getCode st0 :=
    Line.of_inv Devm.getCode (by line_inv) htoken
  have hbal : Devm.getBal s = Devm.getBal st0 :=
    Line.of_inv Devm.getBal (by line_inv) htoken
  have hm : s.memory = st0.memory :=
    Line.of_inv Devm.memory (by line_inv) htoken
  have hlogs : s.logs = st0.logs :=
    Line.of_inv Devm.logs (by line_inv) htoken
  have hout : s.output = st0.output :=
    Line.of_inv Devm.output (by line_inv) htoken
  have hpTokenFlag :
      ((sevm.currentTarget.toB256 =? Sevm.argWord sevm 1) =? 0) :: [] <<+
        st0.stack := by
    have htoken' := htoken
    unfold tokenLine at htoken'
    rcases of_run_append (arg 1) htoken' with
      ⟨tt1, htArg, htoken'⟩
    have hp1 : Sevm.argWord sevm 1 :: [] <<+ tt1.stack :=
      prefix_of_arg nil_pref htArg
    rcases Line.of_run_cons htoken' with
      ⟨tt2, htAddress, htoken'⟩
    have hp2 : sevm.currentTarget.toB256 :: Sevm.argWord sevm 1 :: [] <<+
        tt2.stack := prefix_of_push (of_run_address htAddress) hp1
    rcases Line.of_run_cons htoken' with ⟨tt3, htEq, htoken'⟩
    have hp3 : (sevm.currentTarget.toB256 =? Sevm.argWord sevm 1) :: [] <<+
        tt3.stack := prefix_of_eq htEq hp2
    rcases Line.of_run_cons htoken' with ⟨tt4, htZero, hnil⟩
    cases hnil
    exact prefix_of_iszero htZero hp3
  have h_token_lookup :
      ((weth10 dp).main :: weth10Aux)[flashTokenErrorSlot]? =
        some (Func.revWith "WETH: flash mint only WETH10") := by
    simp [weth10, weth10Aux, flashTokenErrorSlot, flashTokenError]
  rcases of_run_branch_call_revWith h_token_lookup run0 with
    ⟨st1, htokenPop, run1⟩
  have htokenStack := htokenPop.stack
  simp only [Stack.Pop, Split, List.nil_append, List.cons_append] at htokenStack
  rw [htokenStack] at hpTokenFlag
  have h_token_flag : (0 : B256) =
      ((sevm.currentTarget.toB256 =? Sevm.argWord sevm 1) =? 0) :=
    (pref_head_unique hpTokenFlag (pref_append [0] st1.stack)).symm
  have h_token_self : Sevm.argWord sevm 1 =
      sevm.currentTarget.toB256 := by
    by_contra hne
    have hne' : sevm.currentTarget.toB256 ≠ Sevm.argWord sevm 1 :=
      Ne.symm hne
    simp [B256.eqCheck, hne'] at h_token_flag
    exact B256.zero_ne_one h_token_flag
  have hstor := hstor.trans (PopBurn.Inv.inv htokenPop)
  have hcode := hcode.trans
    (funext (fun a => getCode_eq_of_state_eq htokenPop.state a))
  have hbal := hbal.trans (PopBurn.Inv.inv htokenPop)
  have hm := hm.trans htokenPop.memory
  have hlogs := hlogs.trans htokenPop.logs
  have hout := hout.trans htokenPop.output

  let amountLine : Line := arg 2 ++ [dup 0, pushB256 maxUint112, lt]
  rcases of_run_prepend amountLine _ run1 with
    ⟨sa0, hamount, run2⟩
  have hstor := hstor.trans
    (Line.of_inv Devm.getStor (by line_inv) hamount)
  have hcode := hcode.trans
    (Line.of_inv Devm.getCode (by line_inv) hamount)
  have hbal := hbal.trans
    (Line.of_inv Devm.getBal (by line_inv) hamount)
  have hm := hm.trans
    (Line.of_inv Devm.memory (by line_inv) hamount)
  have hlogs := hlogs.trans
    (Line.of_inv Devm.logs (by line_inv) hamount)
  have hout := hout.trans
    (Line.of_inv Devm.output (by line_inv) hamount)
  have hpAmountFlag :
      (maxUint112 <? Sevm.argWord sevm 2) ::
        Sevm.argWord sevm 2 :: [] <<+ sa0.stack := by
    unfold amountLine at hamount
    rcases of_run_append (arg 2) hamount with
      ⟨sa1, harg2, hamount1⟩
    have hp1 : Sevm.argWord sevm 2 :: [] <<+ sa1.stack :=
      prefix_of_arg nil_pref harg2
    rcases Line.of_run_cons hamount1 with
      ⟨sa2, hdup, hamount2⟩
    have hp2 : Sevm.argWord sevm 2 :: Sevm.argWord sevm 2 :: [] <<+
        sa2.stack := prefix_of_dup_val hdup (by show_nth) hp1
    rcases Line.of_run_cons hamount2 with
      ⟨sa3, hmax, hamount3⟩
    have hp3 : maxUint112 :: Sevm.argWord sevm 2 ::
        Sevm.argWord sevm 2 :: [] <<+ sa3.stack :=
      prefix_of_push (of_run_pushB256 hmax) hp2
    rcases Line.of_run_cons hamount3 with
      ⟨sa4, hlt, hnil⟩
    cases hnil
    exact prefix_of_lt hlt hp3
  have h_individual_lookup :
      ((weth10 dp).main :: weth10Aux)[individualLimitErrorSlot]? =
        some (Func.revWith "WETH: individual loan limit exceeded") := by
    simp [weth10, weth10Aux, individualLimitErrorSlot,
      individualLimitError]
  rcases of_run_branch_call_revWith h_individual_lookup run2 with
    ⟨sa5, hamountPop, run3⟩
  have hpopStack := hamountPop.stack
  simp only [Stack.Pop, Split, List.nil_append, List.cons_append] at hpopStack
  rw [hpopStack] at hpAmountFlag
  have h_amount_flag : (maxUint112 <? Sevm.argWord sevm 2) = 0 :=
    pref_head_unique hpAmountFlag (pref_append [0] sa5.stack)
  have h_amount_le : Sevm.argWord sevm 2 ≤ maxUint112 := by
    rw [← B256.not_lt]
    intro hlt
    rw [B256.ltCheck, if_pos hlt] at h_amount_flag
    exact B256.zero_ne_one h_amount_flag.symm
  rw [h_amount_flag] at hpAmountFlag
  have hpAmount : [Sevm.argWord sevm 2] <<+ sa5.stack :=
    cons_pref_cons_inv hpAmountFlag
  have hstor := hstor.trans (PopBurn.Inv.inv hamountPop)
  have hcode := hcode.trans
    (funext (fun a => getCode_eq_of_state_eq hamountPop.state a))
  have hbal := hbal.trans (PopBurn.Inv.inv hamountPop)
  have hm := hm.trans hamountPop.memory
  have hlogs := hlogs.trans hamountPop.logs
  have hout := hout.trans hamountPop.output

  let flashLine : Line :=
    pushFlashMintedSlot ++ [sload, dup 1, add] ++
      pushFlashMintedSlot ++ [sstore]
  rcases of_run_prepend flashLine _ run3 with
    ⟨sf0, hflashLine, run4⟩
  unfold flashLine at hflashLine
  rcases of_run_append pushFlashMintedSlot hflashLine with
    ⟨sf1, hpushFlash1, hflash1⟩
  have hpF1 : flashMintedSlot :: Sevm.argWord sevm 2 :: [] <<+
      sf1.stack := prefix_of_pushFlashMintedSlot hpAmount hpushFlash1
  rcases Line.of_run_cons hflash1 with ⟨sf2, hloadFlash, hflash2⟩
  rcases prefix_of_sload hloadFlash hpF1 with
    ⟨flash, hpF2, hflashRead⟩
  rcases Line.of_run_cons hflash2 with ⟨sf3, hdupAmount, hflash3⟩
  have hpF3 : Sevm.argWord sevm 2 :: flash ::
      Sevm.argWord sevm 2 :: [] <<+ sf3.stack :=
    prefix_of_dup_val hdupAmount (by show_nth) hpF2
  rcases Line.of_run_cons hflash3 with ⟨sf4, haddFlash, hflash4⟩
  have hpF4 : (Sevm.argWord sevm 2 + flash) ::
      Sevm.argWord sevm 2 :: [] <<+ sf4.stack :=
    prefix_of_add haddFlash hpF3
  rcases of_run_append pushFlashMintedSlot hflash4 with
    ⟨sf5, hpushFlash2, hflash5⟩
  have hpF5 : flashMintedSlot ::
      (Sevm.argWord sevm 2 + flash) ::
      Sevm.argWord sevm 2 :: [] <<+ sf5.stack :=
    prefix_of_pushFlashMintedSlot hpF4 hpushFlash2
  rcases Line.of_run_cons hflash5 with
    ⟨sf6, hstoreFlash, hnilFlash⟩
  cases hnilFlash
  have h_set_flash : Devm.getStor sf0 sevm.currentTarget =
      (Devm.getStor sf5 sevm.currentTarget).set flashMintedSlot
        (Sevm.argWord sevm 2 + flash) :=
    sstore_getStor_set hstoreFlash hpF5
  have hpF6 : [Sevm.argWord sevm 2] <<+ sf0.stack :=
    prefix_of_sstore hstoreFlash hpF5
  have h_stor_s_sf5 : Devm.getStor s = Devm.getStor sf5 :=
    hstor.trans ((Line.of_inv Devm.getStor (by line_inv)
      hpushFlash1).trans
        ((Line.of_inv Devm.getStor (by line_inv)
          (Line.Run.cons hloadFlash Line.Run.nil)).trans
          ((Line.of_inv Devm.getStor (by line_inv)
            (Line.Run.cons hdupAmount Line.Run.nil)).trans
            ((Line.of_inv Devm.getStor (by line_inv)
              (Line.Run.cons haddFlash Line.Run.nil)).trans
              (Line.of_inv Devm.getStor (by line_inv) hpushFlash2)))))
  have h_flash_read : flash =
      (Devm.getStor s sevm.currentTarget).get flashMintedSlot := by
    rw [hflashRead]
    show (Devm.getStor sf1 sevm.currentTarget).get flashMintedSlot = _
    rw [← congrFun (Line.of_inv Devm.getStor (by line_inv)
      hpushFlash1) sevm.currentTarget,
      ← congrFun hstor sevm.currentTarget]
  have hcode := hcode.trans
    (Line.of_inv Devm.getCode (by line_inv) hflashLine)
  have hbal := hbal.trans
    (Line.of_inv Devm.getBal (by line_inv) hflashLine)
  have hm := hm.trans
    (Line.of_inv Devm.memory (by line_inv) hflashLine)
  have hlogs := hlogs.trans
    (Line.of_inv Devm.logs (by line_inv) hflashLine)
  have hout := hout.trans
    (Line.of_inv Devm.output (by line_inv) hflashLine)

  let totalLine : Line :=
    pushFlashMintedSlot ++ [sload, dup 0, pushB256 maxUint112, lt]
  rcases of_run_prepend totalLine _ run4 with
    ⟨st2, htotal, run5⟩
  have hstor_sf0_st2 : Devm.getStor sf0 = Devm.getStor st2 :=
    Line.of_inv Devm.getStor (by line_inv) htotal
  have hcode := hcode.trans
    (Line.of_inv Devm.getCode (by line_inv) htotal)
  have hbal := hbal.trans
    (Line.of_inv Devm.getBal (by line_inv) htotal)
  have hm := hm.trans
    (Line.of_inv Devm.memory (by line_inv) htotal)
  have hlogs := hlogs.trans
    (Line.of_inv Devm.logs (by line_inv) htotal)
  have hout := hout.trans
    (Line.of_inv Devm.output (by line_inv) htotal)
  have hpTotal :
      (maxUint112 <? (Sevm.argWord sevm 2 + flash)) ::
        (Sevm.argWord sevm 2 + flash) ::
        Sevm.argWord sevm 2 :: [] <<+ st2.stack := by
    unfold totalLine at htotal
    rcases of_run_append pushFlashMintedSlot htotal with
      ⟨st3, hpushTotal, htotal1⟩
    have hpT1 : flashMintedSlot :: Sevm.argWord sevm 2 :: [] <<+
        st3.stack := prefix_of_pushFlashMintedSlot hpF6 hpushTotal
    rcases Line.of_run_cons htotal1 with ⟨st4, hloadTotal, htotal2⟩
    rcases prefix_of_sload hloadTotal hpT1 with
      ⟨flash2, hpT2, hflash2Read⟩
    have h_flash2 : flash2 = Sevm.argWord sevm 2 + flash := by
      rw [hflash2Read]
      show (Devm.getStor st3 sevm.currentTarget).get flashMintedSlot = _
      rw [← congrFun (Line.of_inv Devm.getStor (by line_inv)
        hpushTotal) sevm.currentTarget,
        h_set_flash, Stor.get_set_self]
    rw [h_flash2] at hpT2
    rcases Line.of_run_cons htotal2 with ⟨st5, hdupTotal, htotal3⟩
    have hpT3 : (Sevm.argWord sevm 2 + flash) ::
        (Sevm.argWord sevm 2 + flash) ::
        Sevm.argWord sevm 2 :: [] <<+ st5.stack :=
      prefix_of_dup_val hdupTotal (by show_nth) hpT2
    rcases Line.of_run_cons htotal3 with ⟨st6, hmaxTotal, htotal4⟩
    have hpT4 : maxUint112 :: (Sevm.argWord sevm 2 + flash) ::
        (Sevm.argWord sevm 2 + flash) ::
        Sevm.argWord sevm 2 :: [] <<+ st6.stack :=
      prefix_of_push (of_run_pushB256 hmaxTotal) hpT3
    rcases Line.of_run_cons htotal4 with ⟨st7, hltTotal, hnil⟩
    cases hnil
    exact prefix_of_lt hltTotal hpT4
  have h_total_lookup :
      ((weth10 dp).main :: weth10Aux)[totalLimitErrorSlot]? =
        some (Func.revWith "WETH: total loan limit exceeded") := by
    simp [weth10, weth10Aux, totalLimitErrorSlot, totalLimitError]
  rcases of_run_branch_call_revWith h_total_lookup run5 with
    ⟨st8, htotalPop, run6⟩
  have htotalStack := htotalPop.stack
  simp only [Stack.Pop, Split, List.nil_append, List.cons_append] at htotalStack
  rw [htotalStack] at hpTotal
  have h_total_flag :
      (maxUint112 <? (Sevm.argWord sevm 2 + flash)) = 0 :=
    pref_head_unique hpTotal (pref_append [0] st8.stack)
  have h_total_le : Sevm.argWord sevm 2 + flash ≤ maxUint112 := by
    rw [← B256.not_lt]
    intro hlt
    rw [B256.ltCheck, if_pos hlt] at h_total_flag
    exact B256.zero_ne_one h_total_flag.symm
  rw [h_total_flag] at hpTotal
  have hpT8 : (Sevm.argWord sevm 2 + flash) ::
      Sevm.argWord sevm 2 :: [] <<+ st8.stack :=
    cons_pref_cons_inv hpTotal
  have hstor_sf0_st8 : Devm.getStor sf0 = Devm.getStor st8 :=
    hstor_sf0_st2.trans
      ((PopBurn.Inv.inv htotalPop))
  have hcode := hcode.trans
    (funext (fun a => getCode_eq_of_state_eq htotalPop.state a))
  have hbal := hbal.trans (PopBurn.Inv.inv htotalPop)
  have hm := hm.trans htotalPop.memory
  have hlogs := hlogs.trans htotalPop.logs
  have hout := hout.trans htotalPop.output
  rcases of_run_next run6 with ⟨st9, hpopTotal, run7⟩
  have hpT9 : [Sevm.argWord sevm 2] <<+ st9.stack := by
    have hp := prefix_of_pop (of_run_pop hpopTotal) hpT8
    exact hp
  have hstor_sf0_st9 : Devm.getStor sf0 = Devm.getStor st9 :=
    hstor_sf0_st8.trans
      (Line.of_inv Devm.getStor (by line_inv)
        (Line.Run.cons hpopTotal Line.Run.nil))
  have hcode := hcode.trans
    (Line.of_inv Devm.getCode (by line_inv)
      (Line.Run.cons hpopTotal Line.Run.nil))
  have hbal := hbal.trans
    (Line.of_inv Devm.getBal (by line_inv)
      (Line.Run.cons hpopTotal Line.Run.nil))
  have hm := hm.trans
    (Line.of_inv Devm.memory (by line_inv)
      (Line.Run.cons hpopTotal Line.Run.nil))
  have hlogs := hlogs.trans
    (Line.of_inv Devm.logs (by line_inv)
      (Line.Run.cons hpopTotal Line.Run.nil))
  have hout := hout.trans
    (Line.of_inv Devm.output (by line_inv)
      (Line.Run.cons hpopTotal Line.Run.nil))

  let mintLine : Line :=
    addressArg 0 ++ [dup 0, sload, dup 2, add, dup 1, sstore, swap 0]
  rcases of_run_prepend mintLine _ run7 with
    ⟨smint, hmint, run8⟩
  unfold mintLine at hmint
  rcases of_run_append (addressArg 0) hmint with
    ⟨sm1, hrecipient, hmint1⟩
  let key := (~~~ addressMask) &&& Sevm.argWord sevm 0
  let recipient := key.toAdr
  have h_key_valid : ValidAdr key :=
    normalizedAddress_valid (Sevm.argWord sevm 0)
  have h_key : recipient.toB256 = key :=
    toB256_toAdr h_key_valid
  have hpM1 : key :: Sevm.argWord sevm 2 :: [] <<+ sm1.stack :=
    prefix_of_addressArg hpT9 hrecipient
  rcases Line.of_run_cons hmint1 with ⟨sm2, hdupKey, hmint2⟩
  have hpM2 : key :: key :: Sevm.argWord sevm 2 :: [] <<+ sm2.stack :=
    prefix_of_dup_val hdupKey (by show_nth) hpM1
  rcases Line.of_run_cons hmint2 with ⟨sm3, hloadBal, hmint3⟩
  rcases prefix_of_sload hloadBal hpM2 with
    ⟨oldBal, hpM3, holdBal⟩
  rcases Line.of_run_cons hmint3 with ⟨sm4, hdupAmount2, hmint4⟩
  have hpM4 : Sevm.argWord sevm 2 :: oldBal :: key ::
      Sevm.argWord sevm 2 :: [] <<+ sm4.stack :=
    prefix_of_dup_val hdupAmount2 (by show_nth) hpM3
  rcases Line.of_run_cons hmint4 with ⟨sm5, haddBal, hmint5⟩
  have hpM5 : (Sevm.argWord sevm 2 + oldBal) :: key ::
      Sevm.argWord sevm 2 :: [] <<+ sm5.stack :=
    prefix_of_add haddBal hpM4
  rcases Line.of_run_cons hmint5 with ⟨sm6, hdupKey2, hmint6⟩
  have hpM6 : key :: (Sevm.argWord sevm 2 + oldBal) :: key ::
      Sevm.argWord sevm 2 :: [] <<+ sm6.stack :=
    prefix_of_dup_val hdupKey2 (by show_nth) hpM5
  rcases Line.of_run_cons hmint6 with ⟨sm7, hstoreBal, hmint7⟩
  have h_set_bal : Devm.getStor sm7 sevm.currentTarget =
      (Devm.getStor sm6 sevm.currentTarget).set key
        (Sevm.argWord sevm 2 + oldBal) :=
    sstore_getStor_set hstoreBal hpM6
  have hpM7 : key :: Sevm.argWord sevm 2 :: [] <<+ sm7.stack :=
    prefix_of_sstore hstoreBal hpM6
  rcases Line.of_run_cons hmint7 with ⟨sm8, hswapMint, hnilMint⟩
  cases hnilMint
  have hswapCore : Stack.Swap (0 : Fin 16).val
      [key, Sevm.argWord sevm 2]
      [Sevm.argWord sevm 2, key] := Stack.swapCore_zero
  have hpMint : [Sevm.argWord sevm 2, key] <<+ smint.stack :=
    Stack.prefix_of_swap hswapCore (of_run_swap hswapMint) hpM7
  have h_stor_sf0_sm6 : Devm.getStor sf0 = Devm.getStor sm6 :=
    hstor_sf0_st9.trans
      ((Line.of_inv Devm.getStor (by line_inv) hrecipient).trans
        ((Line.of_inv Devm.getStor (by line_inv)
          (Line.Run.cons hdupKey Line.Run.nil)).trans
          ((Line.of_inv Devm.getStor (by line_inv)
            (Line.Run.cons hloadBal Line.Run.nil)).trans
            ((Line.of_inv Devm.getStor (by line_inv)
              (Line.Run.cons hdupAmount2 Line.Run.nil)).trans
              ((Line.of_inv Devm.getStor (by line_inv)
                (Line.Run.cons haddBal Line.Run.nil)).trans
                (Line.of_inv Devm.getStor (by line_inv)
                  (Line.Run.cons hdupKey2 Line.Run.nil)))))))
  have h_stor_sm7_smint : Devm.getStor sm7 = Devm.getStor smint :=
    Line.of_inv Devm.getStor (by line_inv)
      (Line.Run.cons hswapMint Line.Run.nil)
  have h_old_bal : oldBal =
      (Devm.getStor s sevm.currentTarget).get key := by
    rw [holdBal]
    show (Devm.getStor sm2 sevm.currentTarget).get key = _
    rw [← congrFun (Line.of_inv Devm.getStor (by line_inv)
          (Line.Run.cons hdupKey Line.Run.nil)) sevm.currentTarget,
      ← congrFun (Line.of_inv Devm.getStor (by line_inv)
        hrecipient) sevm.currentTarget,
      ← congrFun hstor_sf0_st9 sevm.currentTarget,
      h_set_flash, ← congrFun h_stor_s_sf5 sevm.currentTarget]
    rw [← h_key]
    exact Stor.get_set_ne _
      (balanceKey_ne_flashMintedSlot recipient).symm _
  have h_stor_mint : Devm.getStor smint sevm.currentTarget =
      ((Devm.getStor s sevm.currentTarget).set flashMintedSlot
        (Sevm.argWord sevm 2 + flash)).set key
          (Sevm.argWord sevm 2 + oldBal) := by
    rw [← congrFun h_stor_sm7_smint sevm.currentTarget, h_set_bal,
      ← congrFun h_stor_sf0_sm6 sevm.currentTarget, h_set_flash,
      ← congrFun h_stor_s_sf5 sevm.currentTarget]
  have hcode := hcode.trans
    (Line.of_inv Devm.getCode (by line_inv) hmint)
  have hbal := hbal.trans
    (Line.of_inv Devm.getBal (by line_inv) hmint)
  have hm := hm.trans
    (Line.of_inv Devm.memory (by line_inv) hmint)
  have hlogs := hlogs.trans
    (Line.of_inv Devm.logs (by line_inv) hmint)
  have hout := hout.trans
    (Line.of_inv Devm.output (by line_inv) hmint)

  let eventCheck : Line :=
    [dup 0] ++ mstoreAt 0 ++
      [dup 1, pushB256 0, pushB256 Blanc.transferEvent] ++
      logWith 2 0 1 ++ [dup 1, extcodesize, iszero]
  rcases of_run_prepend eventCheck _ run8 with
    ⟨scheck, hcheck, run9⟩
  unfold eventCheck at hcheck
  rcases Line.of_run_cons hcheck with
    ⟨ec1, hdupEvent, hcheck1⟩
  have hpE1 : Sevm.argWord sevm 2 :: Sevm.argWord sevm 2 ::
      key :: [] <<+ ec1.stack :=
    prefix_of_dup_val hdupEvent (by show_nth) hpMint
  rcases of_run_append (mstoreAt 0) hcheck1 with
    ⟨ec2, hstoreEvent, hcheck2⟩
  rcases of_run_mstoreAt_val hstoreEvent hpE1 with
    ⟨hpE2, hmemE2⟩
  rcases Line.of_run_cons hcheck2 with
    ⟨ec3, hdupTopic, hcheck3⟩
  have hpE3 : key :: Sevm.argWord sevm 2 :: key :: [] <<+
      ec3.stack :=
    prefix_of_dup_val hdupTopic (by show_nth) hpE2
  rcases Line.of_run_cons hcheck3 with
    ⟨ec4, hzeroTopic, hcheck4⟩
  have hpE4 : (0 : B256) :: key :: Sevm.argWord sevm 2 ::
      key :: [] <<+ ec4.stack :=
    prefix_of_push (of_run_pushB256 hzeroTopic) hpE3
  rcases Line.of_run_cons hcheck4 with
    ⟨ec5, heventTopic, hcheck5⟩
  have hpE5 : Blanc.transferEvent :: (0 : B256) :: key ::
      Sevm.argWord sevm 2 :: key :: [] <<+ ec5.stack :=
    prefix_of_push (of_run_pushB256 heventTopic) hpE4
  rcases of_run_append (logWith 2 0 1) hcheck5 with
    ⟨ec6, hlogEvent, hcheck6⟩
  rcases of_logWith201_val hpE5 hlogEvent with
    ⟨hpE6, hlogsE6⟩
  have hmemE6 := of_logWith201_mem hpE5 hlogEvent
  rcases Line.of_run_cons hcheck6 with
    ⟨ec7, hdupReceiver2, hcheck7⟩
  have hpE7 : key :: Sevm.argWord sevm 2 :: key :: [] <<+
      ec7.stack :=
    prefix_of_dup_val hdupReceiver2 (by show_nth) hpE6
  rcases Line.of_run_cons hcheck7 with
    ⟨ec8, hextsize, hcheck8⟩
  rcases of_extcodesize_frame hpE7 hextsize with
    ⟨size, hpE8, hmemExtsize⟩
  rcases Line.of_run_cons hcheck8 with
    ⟨ec9, hiszeroCode, hnilCheck⟩
  cases hnilCheck
  have hpE9 := prefix_of_iszero hiszeroCode hpE8
  have hcode := hcode.trans
    (Line.of_inv Devm.getCode (by line_inv) hcheck)
  have hbal := hbal.trans
    (Line.of_inv Devm.getBal (by line_inv) hcheck)
  have hout := hout.trans
    (Line.of_inv Devm.output (by line_inv) hcheck)
  have hstor_smint_scheck : Devm.getStor smint = Devm.getStor scheck :=
    Line.of_inv Devm.getStor (by line_inv) hcheck
  rcases of_run_branch_rev run9 with
    ⟨sready, hcheckPop, run10⟩
  have hpReady : [Sevm.argWord sevm 2, key] <<+ sready.stack := by
    have hpopStack := hcheckPop.stack
    simp only [Stack.Pop, Split, List.nil_append,
      List.cons_append] at hpopStack
    rw [hpopStack] at hpE9
    have hflag : (size =? 0) = 0 :=
      pref_head_unique hpE9 (pref_append [0] sready.stack)
    rw [hflag] at hpE9
    exact cons_pref_cons_inv hpE9
  have hcode := hcode.trans
    (funext (fun a => getCode_eq_of_state_eq hcheckPop.state a))
  have hbal := hbal.trans (PopBurn.Inv.inv hcheckPop)
  have hstor_smint_sready : Devm.getStor smint = Devm.getStor sready :=
    hstor_smint_scheck.trans (PopBurn.Inv.inv hcheckPop)
  have hmem_smint_ec1 : smint.memory = ec1.memory :=
    Line.of_inv Devm.memory (by line_inv)
      (Line.Run.cons hdupEvent Line.Run.nil)
  have hmemE2' : ec2.memory =
      ec1.memory.write 0 (Sevm.argWord sevm 2).toBytes := by
    rw [show (0 * 32 : B256).toNat = 0 by decide +kernel] at hmemE2
    exact hmemE2
  have hmem_ec2_ec5 : ec2.memory = ec5.memory :=
    (Line.of_inv Devm.memory (by line_inv)
      (Line.Run.cons hdupTopic Line.Run.nil)).trans
      ((Line.of_inv Devm.memory (by line_inv)
        (Line.Run.cons hzeroTopic Line.Run.nil)).trans
        (Line.of_inv Devm.memory (by line_inv)
          (Line.Run.cons heventTopic Line.Run.nil)))
  have hmem_ec6_scheck : ec6.memory = scheck.memory :=
    (Line.of_inv Devm.memory (by line_inv)
      (Line.Run.cons hdupReceiver2 Line.Run.nil)).trans
      (hmemExtsize.trans
        (Line.of_inv Devm.memory (by line_inv)
          (Line.Run.cons hiszeroCode Line.Run.nil)))
  have hlogs_smint_ec5 : smint.logs = ec5.logs :=
    (Line.of_inv Devm.logs (by line_inv)
      (Line.Run.cons hdupEvent Line.Run.nil)).trans
      ((Line.of_inv Devm.logs (by line_inv) hstoreEvent).trans
        ((Line.of_inv Devm.logs (by line_inv)
          (Line.Run.cons hdupTopic Line.Run.nil)).trans
          ((Line.of_inv Devm.logs (by line_inv)
            (Line.Run.cons hzeroTopic Line.Run.nil)).trans
            (Line.of_inv Devm.logs (by line_inv)
              (Line.Run.cons heventTopic Line.Run.nil)))))
  have hlogs_ec6_scheck : ec6.logs = scheck.logs :=
    Line.of_inv Devm.logs (by line_inv) hcheck6
  have h_amount_bytes_ne : (Sevm.argWord sevm 2).toBytes ≠ [] := by
    intro hnil
    have hlen := B256.length_toBytes (Sevm.argWord sevm 2)
    rw [hnil] at hlen
    simp at hlen
  have h_event_data : (ec5.memory.read 0 32).1 =
      (Sevm.argWord sevm 2).toBytes := by
    rw [← hmem_ec2_ec5, hmemE2']
    exact _root_.Blanc.Mem.read_write_zero ec1.memory h_amount_bytes_ne
  have h_event_logs : sready.logs = s.logs ++
      [⟨sevm.currentTarget,
        [Blanc.transferEvent, 0, recipient.toB256],
        (Sevm.argWord sevm 2).toBytes⟩] := by
    calc
      sready.logs = scheck.logs := hcheckPop.logs.symm
      _ = ec6.logs := hlogs_ec6_scheck.symm
      _ = ec5.logs ++
          [⟨sevm.currentTarget, [Blanc.transferEvent, 0, key],
            (ec5.memory.read 0 32).1⟩] := hlogsE6
      _ = smint.logs ++
          [⟨sevm.currentTarget, [Blanc.transferEvent, 0, key],
            (Sevm.argWord sevm 2).toBytes⟩] := by
            rw [h_event_data, ← hlogs_smint_ec5]
      _ = s.logs ++
          [⟨sevm.currentTarget,
            [Blanc.transferEvent, 0, recipient.toB256],
            (Sevm.argWord sevm 2).toBytes⟩] := by
            rw [← hlogs, h_key]

  rcases of_run_next run10 with ⟨sh0, hdupHead, run11⟩
  have hpH0 : Sevm.argWord sevm 2 :: Sevm.argWord sevm 2 :: key :: [] <<+
      sh0.stack := prefix_of_dup_val hdupHead (by show_nth) hpReady
  have hsetupStor : Devm.getStor sready = Devm.getStor sh0 :=
    Line.of_inv Devm.getStor (by line_inv)
      (Line.Run.cons hdupHead Line.Run.nil)
  have hsetupCode : Devm.getCode sready = Devm.getCode sh0 :=
    Line.of_inv Devm.getCode (by line_inv)
      (Line.Run.cons hdupHead Line.Run.nil)
  have hsetupBal : Devm.getBal sready = Devm.getBal sh0 :=
    Line.of_inv Devm.getBal (by line_inv)
      (Line.Run.cons hdupHead Line.Run.nil)
  have hmemReadyH0 : sready.memory = sh0.memory :=
    Line.of_inv Devm.memory (by line_inv)
      (Line.Run.cons hdupHead Line.Run.nil)
  have hsetupLogs : sready.logs = sh0.logs :=
    Line.of_inv Devm.logs (by line_inv)
      (Line.Run.cons hdupHead Line.Run.nil)
  have hsetupOutput : sready.output = sh0.output :=
    Line.of_inv Devm.output (by line_inv)
      (Line.Run.cons hdupHead Line.Run.nil)
  rcases of_run_prepend storeFlashCallbackHead _ run11 with
    ⟨sh1, hhead, run12⟩
  rcases of_storeFlashCallbackHead_frame hpH0 hhead with
    ⟨hpH1, hmemHead⟩
  have hsetupStor := hsetupStor.trans
    (Line.of_inv Devm.getStor (by line_inv) hhead)
  have hsetupCode := hsetupCode.trans
    (Line.of_inv Devm.getCode (by line_inv) hhead)
  have hsetupBal := hsetupBal.trans
    (Line.of_inv Devm.getBal (by line_inv) hhead)
  have hsetupLogs := hsetupLogs.trans
    (Line.of_inv Devm.logs (by line_inv) hhead)
  have hsetupOutput := hsetupOutput.trans
    (Line.of_inv Devm.output (by line_inv) hhead)
  rcases of_run_prepend (pushList [0, 0]) _ run12 with
    ⟨sh2, hzeros, run13⟩
  have hpH2 : (0 : B256) :: 0 :: Sevm.argWord sevm 2 :: key :: [] <<+
      sh2.stack := by
    unfold pushList at hzeros
    simp only [List.map] at hzeros
    rcases Line.of_run_cons hzeros with
      ⟨z1, hz1, hzeros1⟩
    have hpZ1 : (0 : B256) :: Sevm.argWord sevm 2 :: key :: [] <<+
        z1.stack :=
      prefix_of_push (of_run_pushB256 hz1) hpH1
    rcases Line.of_run_cons hzeros1 with
      ⟨z2, hz2, hnilZeros⟩
    cases hnilZeros
    exact prefix_of_push (of_run_pushB256 hz2) hpZ1
  have hsetupStor := hsetupStor.trans
    (Line.of_inv Devm.getStor (by line_inv) hzeros)
  have hsetupCode := hsetupCode.trans
    (Line.of_inv Devm.getCode (by line_inv) hzeros)
  have hsetupBal := hsetupBal.trans
    (Line.of_inv Devm.getBal (by line_inv) hzeros)
  have hmemH1H2 : sh1.memory = sh2.memory :=
    Line.of_inv Devm.memory (by line_inv) hzeros
  have hsetupLogs := hsetupLogs.trans
    (Line.of_inv Devm.logs (by line_inv) hzeros)
  have hsetupOutput := hsetupOutput.trans
    (Line.of_inv Devm.output (by line_inv) hzeros)
  rcases of_run_prepend (forwardArgTail 3 6) _ run13 with
    ⟨sh3, htail, run14⟩
  rcases of_forwardArgTail_val hpH2 htail with
    ⟨hpH3, hmemTail⟩
  have hsetupStor := hsetupStor.trans
    (Line.of_inv Devm.getStor (by line_inv) htail)
  have hsetupCode := hsetupCode.trans
    (Line.of_inv Devm.getCode (by line_inv) htail)
  have hsetupBal := hsetupBal.trans
    (Line.of_inv Devm.getBal (by line_inv) htail)
  have hsetupLogs := hsetupLogs.trans
    (Line.of_inv Devm.logs (by line_inv) htail)
  have hsetupOutput := hsetupOutput.trans
    (Line.of_inv Devm.output (by line_inv) htail)
  rcases of_run_prepend flashCallbackArgsSize _ run14 with
    ⟨sh4, hsize, run15⟩
  let inputSize : B256 :=
    0xc4 + ((~~~ (31 : B256)) &&& (31 + Sevm.tailLen sevm 3))
  have hpH4 : inputSize :: 0 :: 0 :: Sevm.argWord sevm 2 :: key :: [] <<+
      sh4.stack := by
    simpa only [inputSize] using
      (prefix_of_flashCallbackArgsSize_exact hpH3 hsize)
  have hsetupStor := hsetupStor.trans
    (Line.of_inv Devm.getStor (by line_inv) hsize)
  have hsetupCode := hsetupCode.trans
    (Line.of_inv Devm.getCode (by line_inv) hsize)
  have hsetupBal := hsetupBal.trans
    (Line.of_inv Devm.getBal (by line_inv) hsize)
  have hmemH3H4 : sh3.memory = sh4.memory :=
    Line.of_inv Devm.memory (by line_inv) hsize
  have hsetupLogs := hsetupLogs.trans
    (Line.of_inv Devm.logs (by line_inv) hsize)
  have hsetupOutput := hsetupOutput.trans
    (Line.of_inv Devm.output (by line_inv) hsize)
  rcases of_run_next run15 with ⟨sh5, hoffset, run16⟩
  have hpH5 : callbackArgsOffset :: inputSize :: 0 :: 0 ::
      Sevm.argWord sevm 2 :: key :: [] <<+ sh5.stack :=
    prefix_of_push (of_run_pushB256 hoffset) hpH4
  have hsetupStor := hsetupStor.trans
    (Line.of_inv Devm.getStor (by line_inv)
      (Line.Run.cons hoffset Line.Run.nil))
  have hsetupCode := hsetupCode.trans
    (Line.of_inv Devm.getCode (by line_inv)
      (Line.Run.cons hoffset Line.Run.nil))
  have hsetupBal := hsetupBal.trans
    (Line.of_inv Devm.getBal (by line_inv)
      (Line.Run.cons hoffset Line.Run.nil))
  have hmemH4H5 : sh4.memory = sh5.memory :=
    Line.of_inv Devm.memory (by line_inv)
      (Line.Run.cons hoffset Line.Run.nil)
  have hsetupLogs := hsetupLogs.trans
    (Line.of_inv Devm.logs (by line_inv)
      (Line.Run.cons hoffset Line.Run.nil))
  have hsetupOutput := hsetupOutput.trans
    (Line.of_inv Devm.output (by line_inv)
      (Line.Run.cons hoffset Line.Run.nil))
  rcases of_run_next run16 with ⟨sh6, hzero, run17⟩
  have hpH6 : (0 : B256) :: callbackArgsOffset :: inputSize :: 0 :: 0 ::
      Sevm.argWord sevm 2 :: key :: [] <<+ sh6.stack :=
    prefix_of_push (of_run_pushB256 hzero) hpH5
  have hsetupStor := hsetupStor.trans
    (Line.of_inv Devm.getStor (by line_inv)
      (Line.Run.cons hzero Line.Run.nil))
  have hsetupCode := hsetupCode.trans
    (Line.of_inv Devm.getCode (by line_inv)
      (Line.Run.cons hzero Line.Run.nil))
  have hsetupBal := hsetupBal.trans
    (Line.of_inv Devm.getBal (by line_inv)
      (Line.Run.cons hzero Line.Run.nil))
  have hmemH5H6 : sh5.memory = sh6.memory :=
    Line.of_inv Devm.memory (by line_inv)
      (Line.Run.cons hzero Line.Run.nil)
  have hsetupLogs := hsetupLogs.trans
    (Line.of_inv Devm.logs (by line_inv)
      (Line.Run.cons hzero Line.Run.nil))
  have hsetupOutput := hsetupOutput.trans
    (Line.of_inv Devm.output (by line_inv)
      (Line.Run.cons hzero Line.Run.nil))
  rcases of_run_next run17 with ⟨sh7, hdupReceiver, run18⟩
  have hpH7 : key :: 0 :: callbackArgsOffset :: inputSize :: 0 :: 0 ::
      Sevm.argWord sevm 2 :: key :: [] <<+ sh7.stack :=
    prefix_of_dup_val hdupReceiver (by show_nth) hpH6
  have hsetupStor := hsetupStor.trans
    (Line.of_inv Devm.getStor (by line_inv)
      (Line.Run.cons hdupReceiver Line.Run.nil))
  have hsetupCode := hsetupCode.trans
    (Line.of_inv Devm.getCode (by line_inv)
      (Line.Run.cons hdupReceiver Line.Run.nil))
  have hsetupBal := hsetupBal.trans
    (Line.of_inv Devm.getBal (by line_inv)
      (Line.Run.cons hdupReceiver Line.Run.nil))
  have hmemH6H7 : sh6.memory = sh7.memory :=
    Line.of_inv Devm.memory (by line_inv)
      (Line.Run.cons hdupReceiver Line.Run.nil)
  have hsetupLogs := hsetupLogs.trans
    (Line.of_inv Devm.logs (by line_inv)
      (Line.Run.cons hdupReceiver Line.Run.nil))
  have hsetupOutput := hsetupOutput.trans
    (Line.of_inv Devm.output (by line_inv)
      (Line.Run.cons hdupReceiver Line.Run.nil))
  rcases of_run_next run18 with ⟨sc, hgas, htailRun⟩
  rcases of_run_gas hgas with ⟨g, hgasPush⟩
  have hpCall : g :: key :: 0 :: callbackArgsOffset :: inputSize :: 0 :: 0 ::
      Sevm.argWord sevm 2 :: key :: [] <<+ sc.stack :=
    prefix_of_push hgasPush hpH7
  have hsetupStor := hsetupStor.trans
    (Line.of_inv Devm.getStor (by line_inv)
      (Line.Run.cons hgas Line.Run.nil))
  have hsetupCode := hsetupCode.trans
    (Line.of_inv Devm.getCode (by line_inv)
      (Line.Run.cons hgas Line.Run.nil))
  have hsetupBal := hsetupBal.trans
    (Line.of_inv Devm.getBal (by line_inv)
      (Line.Run.cons hgas Line.Run.nil))
  have hmemH7Sc : sh7.memory = sc.memory :=
    Line.of_inv Devm.memory (by line_inv)
      (Line.Run.cons hgas Line.Run.nil)
  have hsetupLogs := hsetupLogs.trans
    (Line.of_inv Devm.logs (by line_inv)
      (Line.Run.cons hgas Line.Run.nil))
  have hsetupOutput := hsetupOutput.trans
    (Line.of_inv Devm.output (by line_inv)
      (Line.Run.cons hgas Line.Run.nil))

  have h_stor_smint_sc : Devm.getStor smint = Devm.getStor sc :=
    hstor_smint_sready.trans hsetupStor
  have hmemoryFrame : ∀ img,
      Mem.Wf s.memory → Mem.Reads s.memory img →
      Mem.Wf sc.memory ∧
        Mem.Reads sc.memory
          (Bytes.writeAt
            (Bytes.writeAt
              (Bytes.writeAt
                (Bytes.writeAt
                  (Bytes.writeAt
                    (Bytes.writeAt
                      (Bytes.writeAt
                        (Bytes.writeAt
                          (Bytes.writeAt img 0
                            (Sevm.argWord sevm 2).toBytes)
                          0 onFlashLoanSelector.toBytes)
                        32 sevm.caller.toB256.toBytes)
                      64 sevm.currentTarget.toB256.toBytes)
                    96 (Sevm.argWord sevm 2).toBytes)
                  128 (0 : B256).toBytes)
                160 (0xa0 : B256).toBytes)
              192 (Sevm.tailLen sevm 3).toBytes)
            224 (Sevm.tailBytes sevm 3)) := by
    intro img hwf hreads
    have hwfE1 : Mem.Wf ec1.memory := by
      rw [← hmem_smint_ec1, ← hm]
      exact hwf
    have hrdE1 : Mem.Reads ec1.memory img := by
      rw [← hmem_smint_ec1, ← hm]
      exact hreads
    have hwfE2 : Mem.Wf ec2.memory := by
      rw [hmemE2']
      exact hwfE1.write 0 _
    have hrdE2 : Mem.Reads ec2.memory
        (Bytes.writeAt img 0 (Sevm.argWord sevm 2).toBytes) := by
      rw [hmemE2']
      exact Mem.Reads.write hwfE1 hrdE1 0 _
    have hwfE5 : Mem.Wf ec5.memory := by
      rw [← hmem_ec2_ec5]
      exact hwfE2
    have hrdE5 : Mem.Reads ec5.memory
        (Bytes.writeAt img 0 (Sevm.argWord sevm 2).toBytes) := by
      rw [← hmem_ec2_ec5]
      exact hrdE2
    have hwfE6 : Mem.Wf ec6.memory := by
      rw [hmemE6]
      exact hwfE5.extend 0 32
    have hrdE6 : Mem.Reads ec6.memory
        (Bytes.writeAt img 0 (Sevm.argWord sevm 2).toBytes) := by
      rw [hmemE6]
      exact hrdE5.extend 0 32
    have hwfReady : Mem.Wf sready.memory := by
      rw [← hcheckPop.memory, ← hmem_ec6_scheck]
      exact hwfE6
    have hrdReady : Mem.Reads sready.memory
        (Bytes.writeAt img 0 (Sevm.argWord sevm 2).toBytes) := by
      rw [← hcheckPop.memory, ← hmem_ec6_scheck]
      exact hrdE6
    have hwfH0 : Mem.Wf sh0.memory := by
      rw [← hmemReadyH0]
      exact hwfReady
    have hrdH0 : Mem.Reads sh0.memory
        (Bytes.writeAt img 0 (Sevm.argWord sevm 2).toBytes) := by
      rw [← hmemReadyH0]
      exact hrdReady
    let img0 := Bytes.writeAt img 0 (Sevm.argWord sevm 2).toBytes
    let img1 := Bytes.writeAt img0 0 onFlashLoanSelector.toBytes
    let img2 := Bytes.writeAt img1 32 sevm.caller.toB256.toBytes
    let img3 := Bytes.writeAt img2 64 sevm.currentTarget.toB256.toBytes
    let img4 := Bytes.writeAt img3 96 (Sevm.argWord sevm 2).toBytes
    let img5 := Bytes.writeAt img4 128 (0 : B256).toBytes
    let img6 := Bytes.writeAt img5 160 (0xa0 : B256).toBytes
    have wf1 := hwfH0.write 0 onFlashLoanSelector.toBytes
    have rd1 : Mem.Reads
        (sh0.memory.write 0 onFlashLoanSelector.toBytes) img1 := by
      exact Mem.Reads.write hwfH0 hrdH0 0 _
    have wf2 := wf1.write 32 sevm.caller.toB256.toBytes
    have rd2 : Mem.Reads
        ((sh0.memory.write 0 onFlashLoanSelector.toBytes).write
          32 sevm.caller.toB256.toBytes) img2 := by
      exact Mem.Reads.write wf1 rd1 32 _
    have wf3 := wf2.write 64 sevm.currentTarget.toB256.toBytes
    have rd3 : Mem.Reads
        (((sh0.memory.write 0 onFlashLoanSelector.toBytes).write
          32 sevm.caller.toB256.toBytes).write
          64 sevm.currentTarget.toB256.toBytes) img3 := by
      exact Mem.Reads.write wf2 rd2 64 _
    have wf4 := wf3.write 96 (Sevm.argWord sevm 2).toBytes
    have rd4 : Mem.Reads
        ((((sh0.memory.write 0 onFlashLoanSelector.toBytes).write
          32 sevm.caller.toB256.toBytes).write
          64 sevm.currentTarget.toB256.toBytes).write
          96 (Sevm.argWord sevm 2).toBytes) img4 := by
      exact Mem.Reads.write wf3 rd3 96 _
    have wf5 := wf4.write 128 (0 : B256).toBytes
    have rd5 : Mem.Reads
        (((((sh0.memory.write 0 onFlashLoanSelector.toBytes).write
          32 sevm.caller.toB256.toBytes).write
          64 sevm.currentTarget.toB256.toBytes).write
          96 (Sevm.argWord sevm 2).toBytes).write
          128 (0 : B256).toBytes) img5 := by
      exact Mem.Reads.write wf4 rd4 128 _
    have wf6 := wf5.write 160 (0xa0 : B256).toBytes
    have rd6 : Mem.Reads
        ((((((sh0.memory.write 0 onFlashLoanSelector.toBytes).write
          32 sevm.caller.toB256.toBytes).write
          64 sevm.currentTarget.toB256.toBytes).write
          96 (Sevm.argWord sevm 2).toBytes).write
          128 (0 : B256).toBytes).write
          160 (0xa0 : B256).toBytes) img6 := by
      exact Mem.Reads.write wf5 rd5 160 _
    have hwfH1 : Mem.Wf sh1.memory := by
      rw [hmemHead]
      exact wf6
    have hrdH1 : Mem.Reads sh1.memory img6 := by
      rw [hmemHead]
      exact rd6
    have hwfH2 : Mem.Wf sh2.memory := by
      rw [← hmemH1H2]
      exact hwfH1
    have hrdH2 : Mem.Reads sh2.memory img6 := by
      rw [← hmemH1H2]
      exact hrdH1
    let img7 := Bytes.writeAt img6 192 (Sevm.tailLen sevm 3).toBytes
    let img8 := Bytes.writeAt img7 224 (Sevm.tailBytes sevm 3)
    have wf7 := hwfH2.write 192 (Sevm.tailLen sevm 3).toBytes
    have rd7 : Mem.Reads
        (sh2.memory.write 192 (Sevm.tailLen sevm 3).toBytes) img7 := by
      exact Mem.Reads.write hwfH2 hrdH2 192 _
    have wf8 := wf7.write 224 (Sevm.tailBytes sevm 3)
    have rd8 : Mem.Reads
        ((sh2.memory.write 192 (Sevm.tailLen sevm 3).toBytes).write
          224 (Sevm.tailBytes sevm 3)) img8 := by
      exact Mem.Reads.write wf7 rd7 224 _
    have hwfH3 : Mem.Wf sh3.memory := by
      rw [hmemTail]
      exact wf8
    have hrdH3 : Mem.Reads sh3.memory img8 := by
      rw [hmemTail]
      exact rd8
    have hwfSc : Mem.Wf sc.memory := by
      rw [← hmemH7Sc, ← hmemH6H7, ← hmemH5H6, ← hmemH4H5,
        ← hmemH3H4]
      exact hwfH3
    have hrdSc : Mem.Reads sc.memory img8 := by
      rw [← hmemH7Sc, ← hmemH6H7, ← hmemH5H6, ← hmemH4H5,
        ← hmemH3H4]
      exact hrdH3
    exact ⟨hwfSc, by simpa only [img0, img1, img2, img3, img4, img5,
      img6, img7, img8] using hrdSc⟩
  have h_inc : Increase recipient (Sevm.argWord sevm 2)
      (Stor.rest (Devm.getStor s sevm.currentTarget))
      (Stor.rest (Devm.getStor sc sevm.currentTarget)) := by
    intro a
    constructor
    · intro ha
      subst a
      simp only [Stor.rest, Function.comp_apply]
      rw [← congrFun h_stor_smint_sc sevm.currentTarget,
        h_stor_mint, h_key, Stor.get_set_self, h_old_bal,
        B256.add_comm]
    · intro hne
      simp only [Stor.rest, Function.comp_apply]
      rw [← congrFun h_stor_smint_sc sevm.currentTarget, h_stor_mint]
      rw [← h_key]
      rw [Stor.get_set_ne _ (fun he => hne (Adr.toB256_inj he)) _]
      exact (Stor.get_set_ne _
        (fun he => flashMintedSlot_not_valid ⟨a, he.symm⟩) _).symm
  have h_flash_sc :
      (Devm.getStor sc sevm.currentTarget).get flashMintedSlot =
        flash + Sevm.argWord sevm 2 := by
    rw [← congrFun h_stor_smint_sc sevm.currentTarget, h_stor_mint]
    rw [← h_key]
    have h_balance_flash : recipient.toB256 ≠ flashMintedSlot := by
      simpa only [balanceKey] using
        balanceKey_ne_flashMintedSlot recipient
    rw [Stor.get_set_ne _
      h_balance_flash,
      Stor.get_set_self, B256.add_comm]
  refine ⟨recipient, sc, g, inputSize, flash,
    h_flash_read, ?_, h_token_self, h_amount_le, ?_, h_inc, h_flash_sc,
    ?_, ?_, rfl, ?_,
    hmemoryFrame, ?_, ?_, ?_⟩
  · simpa only [key] using h_key
  · simpa only [B256.add_comm] using h_total_le
  · exact hcode.trans hsetupCode
  · exact hbal.trans hsetupBal
  · simpa only [h_key] using hpCall
  · exact hsetupLogs.symm.trans h_event_logs
  · exact (hout.trans (hcheckPop.output.trans hsetupOutput)).symm
  · simpa only [flashLoanFromCall] using htailRun

/-- State/stack projection of `of_flashLoan_toCall_frame`, preserving the
original successful-prefix API. -/
theorem of_flashLoan_toCall
    (dp : DeployParams) {sevm : Sevm} {s r : Devm}
    (run : Func.Run ((weth10 dp).main :: weth10Aux) sevm s flashLoan r) :
    ∃ (recipient : Adr) (sc : Devm) (g inputSize base : B256),
      base = (Devm.getStor s sevm.currentTarget).get flashMintedSlot ∧
      Sevm.argWord sevm 2 ≤ maxUint112 ∧
      base + Sevm.argWord sevm 2 ≤ maxUint112 ∧
      Increase recipient (Sevm.argWord sevm 2)
        (Stor.rest (Devm.getStor s sevm.currentTarget))
        (Stor.rest (Devm.getStor sc sevm.currentTarget)) ∧
      (Devm.getStor sc sevm.currentTarget).get flashMintedSlot =
        base + Sevm.argWord sevm 2 ∧
      Devm.getCode s = Devm.getCode sc ∧
      Devm.getBal s = Devm.getBal sc ∧
      (g :: recipient.toB256 :: (0 : B256) :: callbackArgsOffset ::
        inputSize :: 0 :: 0 ::
        [Sevm.argWord sevm 2, recipient.toB256] <<+ sc.stack) ∧
      Func.Run ((weth10 dp).main :: weth10Aux) sevm sc
        flashLoanFromCall r :=
  by
    rcases of_flashLoan_toCall_frame dp run with
      ⟨recipient, sc, g, inputSize, base, hbase, _, _, hamount, htotal,
        hinc, hflash, hcode, hbal, _, hp, _, _, _, htail⟩
    exact ⟨recipient, sc, g, inputSize, base, hbase, hamount, htotal,
      hinc, hflash, hcode, hbal, hp, htail⟩

/-- A successful post-callback decoder reaches the single `flashSettle`
continuation.  Everything between the borrower `CALL` result and that tail
jump is storage- and balance-silent. -/
theorem of_run_flashLoanFromCall
    (dp : DeployParams) {sevm : Sevm} {s r : Devm}
    (run : Func.Run ((weth10 dp).main :: weth10Aux) sevm s
      flashLoanFromCall r) :
    ∃ sf ss,
      Ninst.Run sevm s call sf ∧
      Func.Run ((weth10 dp).main :: weth10Aux) sevm ss
        flashSettle r ∧
      Devm.getStor sf = Devm.getStor ss ∧
      Devm.getBal sf = Devm.getBal ss := by
  simp only [flashLoanFromCall] at run
  rcases of_run_next run with ⟨sf, hcall, run1⟩
  rcases of_run_next run1 with ⟨si, hiszeroCall, run2⟩
  rcases of_run_branch run2 with
      ⟨s2, hpopCall, hcontinue⟩ |
      ⟨w, s2, s3, hnz, hpopCall, hburnCall, hbubbleCall⟩
  · rcases of_run_prepend (retdataShorterThan 32) _ hcontinue with
      ⟨s3, hshort, run3⟩
    rcases of_run_branch_rev run3 with
      ⟨s4, hpopShort, run4⟩
    let checkLine : Line :=
      checkRetdataHead CALLBACK_SUCCESS 0 ++ [iszero]
    rcases of_run_prepend checkLine _ run4 with
      ⟨s5, hcheck, run5⟩
    have h_failed_lookup :
        ((weth10 dp).main :: weth10Aux)[flashFailedErrorSlot]? =
          some (Func.revWith "WETH: flash loan failed") := by
      simp [weth10, weth10Aux, flashFailedErrorSlot, flashFailedError]
    rcases of_run_branch_call_revWith h_failed_lookup run5 with
      ⟨s6, hpopCheck, run6⟩
    rcases of_run_next run6 with ⟨s7, hpop1, run7⟩
    rcases of_run_next run7 with ⟨s8, hpop2, hcallSettle⟩
    rcases of_run_call hcallSettle with
      ⟨f, ss, hget, hburnSettle, hsettle⟩
    have h_settle_lookup :
        ((weth10 dp).main :: weth10Aux)[flashSettleSlot]? =
          some flashSettle := by
      simp [weth10, weth10Aux, flashSettleSlot]
    have hf : f = flashSettle := by
      rw [h_settle_lookup] at hget
      exact Option.some.inj hget.symm
    subst f
    have h_stor : Devm.getStor sf = Devm.getStor ss :=
      (Line.of_inv Devm.getStor (by line_inv)
        (Line.Run.cons hiszeroCall Line.Run.nil)).trans
        ((PopBurn.Inv.inv hpopCall).trans
          ((Line.of_inv Devm.getStor (by line_inv) hshort).trans
            ((PopBurn.Inv.inv hpopShort).trans
              ((Line.of_inv Devm.getStor (by line_inv) hcheck).trans
                ((PopBurn.Inv.inv hpopCheck).trans
                  ((Line.of_inv Devm.getStor (by line_inv)
                    (Line.Run.cons hpop1 Line.Run.nil)).trans
                    ((Line.of_inv Devm.getStor (by line_inv)
                      (Line.Run.cons hpop2 Line.Run.nil)).trans
                      (Burn.Inv.inv hburnSettle))))))))
    have h_bal : Devm.getBal sf = Devm.getBal ss :=
      (Line.of_inv Devm.getBal (by line_inv)
        (Line.Run.cons hiszeroCall Line.Run.nil)).trans
        ((PopBurn.Inv.inv hpopCall).trans
          ((Line.of_inv Devm.getBal (by line_inv) hshort).trans
            ((PopBurn.Inv.inv hpopShort).trans
              ((Line.of_inv Devm.getBal (by line_inv) hcheck).trans
                ((PopBurn.Inv.inv hpopCheck).trans
                  ((Line.of_inv Devm.getBal (by line_inv)
                    (Line.Run.cons hpop1 Line.Run.nil)).trans
                    ((Line.of_inv Devm.getBal (by line_inv)
                      (Line.Run.cons hpop2 Line.Run.nil)).trans
                      (Burn.Inv.inv hburnSettle))))))))
    exact ⟨sf, ss, hcall, hsettle, h_stor, h_bal⟩
  · rcases of_run_call hbubbleCall with
      ⟨f, sb, hget, hburn, hbubble⟩
    have h_bubble_lookup :
        ((weth10 dp).main :: weth10Aux)[bubbleRevertSlot]? =
          some bubbleRevert := by
      simp [weth10, weth10Aux, bubbleRevertSlot]
    have hf : f = bubbleRevert := by
      rw [h_bubble_lookup] at hget
      exact Option.some.inj hget.symm
    subst f
    exact absurd hbubble not_run_bubbleRevert

/-! ### Relational flash-floor dispatch

A fixed-floor `FuncSoundNoMem` induction hypothesis cannot be instantiated at
the
larger counter created immediately before a flash callback.  The relation
below quantifies the floor outside `Pre`/`Post`; a successful subexecution can
therefore be reused at the counter actually present at that subexecution's
entry. -/

/-- Every admissible flash floor at `pre` remains admissible at `post`. -/
def FlashFloorsRel (dp : DeployParams) (ca : Adr)
    (_sevm : Sevm) (pre post : Devm) : Prop :=
  ∀ floor,
    (flashFloorSpec dp floor).Pre ca _sevm pre →
    (flashFloorSpec dp floor).Post ca _sevm post

/-- The relational deeper-frame hypothesis used only by the flash-floor
closure. -/
def FlashFloorsDepth (dp : DeployParams) (ca : Adr) (depth : Nat) : Prop :=
  ForallSubExec depth ca (weth10 dp) (FlashFloorsRel dp ca)

/-- A selector body preserves an arbitrary caller-supplied floor while its
deeper WETH10 executions preserve every admissible floor. -/
def FloorRelFuncSound (dp : DeployParams) (ca : Adr) (f : Func) : Prop :=
  ∀ {floor : B256} {sevm : Sevm} {s r : Devm},
    sevm.currentTarget = ca →
    (flashFloorSpec dp floor).Pre ca sevm s →
    FlashFloorsDepth dp ca sevm.depth →
    Func.Run ((weth10 dp).main :: weth10Aux) sevm s f r →
    (flashFloorSpec dp floor).Post ca sevm r

/-- Specialize a relational deeper-frame hypothesis at one concrete floor. -/
theorem flashFloorInvDepth_of_rel
    (dp : DeployParams) (ca : Adr) (floor : B256) {depth : Nat}
    (ih : FlashFloorsDepth dp ca depth) :
    Exec.InvDepth depth ca (weth10 dp)
      ((flashFloorSpec dp floor).PreWf ca)
      ((flashFloorSpec dp floor).Post ca) := by
  intro pc' sevm' pre' exn' ex' h_depth h_at
  cases exn' with
  | error e => simp only [ifOk, implies_true]
  | ok post' =>
    intro h_pre'
    exact ih pc' sevm' pre' post' ex' h_depth h_at floor h_pre'.pre

/-- The floor-preserving call lemma with the resumed Boolean flag retained on
the caller stack, for bodies that continue after the callback. -/
theorem flashFloorPostStack_of_value_call
    (dp : DeployParams) (floor : B256) (ca : Adr)
    {sevm : Sevm} {s sf : Devm} {g c v ii is oi os : B256}
    {xs : Stack}
    (h_target : sevm.currentTarget = ca)
    (ih : Exec.InvDepth sevm.depth ca (weth10 dp)
      ((flashFloorSpec dp floor).PreWf ca)
      ((flashFloorSpec dp floor).Post ca))
    (hp : (g :: c :: v :: ii :: is :: oi :: os :: xs) <<+ s.stack)
    (h_code : some (s.getCode ca).toList = Prog.compile (weth10 dp))
    (h_floor : Stor.FlashFloor floor (Devm.getStor s ca))
    (h_run : Ninst.Run sevm s call sf) :
    (flashFloorSpec dp floor).Post ca sevm sf ∧
      ∃ b, b :: xs <<+ sf.stack := by
  have h_post := flashFloorPost_of_value_call dp floor ca
    h_target ih hp h_code h_floor h_run
  refine ⟨h_post, ?_⟩
  rcases of_run_call_val_with_depth hp h_run with
    ⟨hstack, hworld⟩ |
    ⟨parent, child, xl, delegated, na, code, avail, hdepth,
      hstack, hstate, hmemory, hdelegation, hfill, hpm,
      hclean, hresume, hsfstate, hret, hmem, hsfstack⟩
  · exact ⟨0, hstack⟩
  · rw [hstack] at hp
    replace hp := cons_pref_cons_inv hp
    replace hp := cons_pref_cons_inv hp
    replace hp := cons_pref_cons_inv hp
    replace hp := cons_pref_cons_inv hp
    replace hp := cons_pref_cons_inv hp
    replace hp := cons_pref_cons_inv hp
    replace hp := cons_pref_cons_inv hp
    refine ⟨1, ?_⟩
    rw [hsfstack]
    exact pref_cons hp

/-- Ordinary fixed-floor proofs lift directly into the relational leaf
interface: specialize the relational subexecution hypothesis at the same
fixed floor. -/
theorem FloorRelFuncSound.of_funcSound
    (dp : DeployParams) (ca : Adr) {f : Func}
    (h : ∀ floor,
      (flashFloorSpec dp floor).FuncSoundNoMem ca weth10Aux f) :
    FloorRelFuncSound dp ca f := by
  intro floor sevm s r h_target h_pre ih run
  apply h floor h_target h_pre
  · exact flashFloorInvDepth_of_rel dp ca floor ih
  · exact run

/-- Contract-neutral frame steps transport the quantified floor pointwise;
only the at-target WETH10 program walk remains contract-specific. -/
theorem flashFloors_lift
    (dp : DeployParams) (ca : Adr)
    (body : ∀ {sevm pre post},
      Prog.Run sevm pre (weth10 dp) post →
      sevm.currentTarget = ca →
      FlashFloorsDepth dp ca sevm.depth →
      FlashFloorsRel dp ca sevm pre post) :
    ∀ pc sevm pre post,
      Exec pc sevm pre (.ok post) →
      Prog.At (weth10 dp) ca pc sevm pre →
      FlashFloorsRel dp ca sevm pre post := by
  apply @Blanc.lift (FlashFloorsRel dp ca) ca (weth10 dp) body
  · intro pc sevm pre n inter post h_at h_run _ h_ne h_rel
    intro floor h_pre
    apply h_rel floor
    cases n with
    | push xs le =>
      simp only [Ninst.StepRun, Ninst.step_push, Step.run_ofExecution] at h_run
      rcases Except.bind_eq_ok h_run.2.symm with
        ⟨devm1, h_charge, h_push⟩
      exact h_pre.state_eq
        (((Devm.burn_of_chargeGas h_charge).state).trans
          ((Devm.push_of_push h_push).state)).symm
    | reg r =>
      have h_reg : Rinst.run ⟨pc, sevm, pre⟩ r = .ok inter := by
        simp only [Ninst.StepRun, Ninst.step_reg,
          Step.run_ofExecution] at h_run
        exact h_run.2.symm
      by_cases h_ss : r = Rinst.sstore
      · subst h_ss
        have h_frame := Rinst.sstore_run_stateWriteFrame pc pre sevm
        rw [h_reg] at h_frame
        refine ContractSpec.Pre.of_eqs h_pre
          (h_frame.getCode_eq ca).symm ?_
          (sstore_preserves_getStor_ne h_reg h_ne)
        funext b
        exact (h_frame.getBal_eq b).symm
      · exact ContractSpec.Pre.of_eqs h_pre
          (Rinst.preserves_getCode h_reg ca)
          (Rinst.preserves_bal h_reg).symm
          (congrFun (Rinst.preserves_stor h_ss h_reg) ca).symm
    | exec x =>
      refine ContractSpec.Xinst.none_preserves_precond (x := x) ?_ h_ne h_pre
      simpa only [Ninst.StepRun, Ninst.step_exec,
        XStep.run_toStep, Xinst.Run] using h_run
  · intro pc sevm pre n evm' exn' inter post h_at h_run ex_sub _
      h_ne h_child h_rel
    intro floor h_pre
    cases n with
    | push xs le =>
      simp only [Ninst.StepRun, Ninst.step_push,
        Step.run_ofExecution] at h_run
      cases h_run.1
    | reg r =>
      simp only [Ninst.StepRun, Ninst.step_reg,
        Step.run_ofExecution] at h_run
      cases h_run.1
    | exec x =>
      rcases ContractSpec.Xinst.some_preserves_precond (x := x) (by
          simpa only [Ninst.StepRun, Ninst.step_exec,
            XStep.run_toStep, Xinst.Run] using h_run)
          ex_sub h_ne h_pre with
        ⟨h_pre_child, h_resume⟩
      apply h_rel floor
      apply h_resume
      cases exn' with
      | error e => trivial
      | ok childPost => exact h_child floor h_pre_child
  · intro pc sevm pre j pc' inter post h_at h_run _ h_ne h_rel
    intro floor h_pre
    exact h_rel floor
      (ContractSpec.Pre.state_eq h_pre (Jinst.preserves_state h_run))
  · intro pc sevm pre l post h_at h_run h_ne
    intro floor h_pre
    exact ContractSpec.Linst.inv_postcond h_run h_ne h_pre

/-- Generated-dispatch decomposition for the relational leaf interface. -/
theorem flashFloorPost_of_run_dispatch
    (dp : DeployParams) (ca : Adr)
    (h_funcs : ∀ p ∈ weth10Funcs dp,
      FloorRelFuncSound dp ca p.2)
    (h_fall : FloorRelFuncSound dp ca Func.rev)
    {floor : B256} {sevm : Sevm} {s r : Devm}
    (h_target : sevm.currentTarget = ca)
    (h_pre : (flashFloorSpec dp floor).Pre ca sevm s)
    (ih : FlashFloorsDepth dp ca sevm.depth)
    (run : Func.Run ((weth10 dp).main :: weth10Aux) sevm s
      (dispatchWith fallbackSlot (weth10Tree dp)) r) :
    (flashFloorSpec dp floor).Post ca sevm r := by
  apply
    (@dispatchWith_inv
      ((weth10 dp).main :: weth10Aux) fallbackSlot Func.rev
      (fun e s =>
        e.currentTarget = ca ∧
        (flashFloorSpec dp floor).Pre ca e s ∧
        FlashFloorsDepth dp ca e.depth)
      (fun e r => (flashFloorSpec dp floor).Post ca e r)
      ?_ ?_ ?_ ?_ (weth10Tree dp) ?_
      sevm s r ⟨h_target, h_pre, ih⟩ run)
  · intro e s0 x w s' s'' ⟨h_ct, hp, hih⟩ hline hpop
    refine ⟨h_ct, ?_, hih⟩
    have h_state : s0.state = s'.state :=
      Line.of_inv Devm.state (by line_inv) hline
    exact hp.state_eq (hpop.state.symm.trans h_state.symm)
  · intro e s0 x w s' s'' ⟨h_ct, hp, hih⟩ hline hpop
    refine ⟨h_ct, ?_, hih⟩
    have h_state : s0.state = s'.state :=
      Line.of_inv Devm.state (by line_inv) hline
    exact hp.state_eq (hpop.state.symm.trans h_state.symm)
  · simp [weth10, weth10Aux, fallbackSlot]
  · intro e s0 s' r0 ⟨h_ct, hp, hih⟩ hburn hrun
    exact h_fall h_ct (hp.state_eq hburn.state.symm) hih hrun
  · intro e s0 r0 wf h_mem ⟨h_ct, hp, hih⟩ hrun
    exact h_funcs wf
      (DispatchTree.mem_of_mem_ofSorted
        (List.cons_ne_nil _ _) h_mem)
      h_ct hp hih hrun

/-- Receive-aware WETH10 ingress for the quantified floor relation. -/
theorem flashFloorsRel_of_prog_run
    (dp : DeployParams) (ca : Adr)
    (h_funcs : ∀ p ∈ weth10Funcs dp,
      FloorRelFuncSound dp ca p.2)
    (h_receive : FloorRelFuncSound dp ca receiveEther)
    {sevm : Sevm} {pre post : Devm}
    (run : Prog.Run sevm pre (weth10 dp) post)
    (h_target : sevm.currentTarget = ca)
    (ih : FlashFloorsDepth dp ca sevm.depth) :
    FlashFloorsRel dp ca sevm pre post := by
  intro floor h_pre
  dsimp only [Prog.Run] at run
  cases run
  rename (_ = _) => h_eq
  rename (Func.Run _ _ _ _ _) => hrun
  rename (Devm.Burn _ _) => burn
  rename Devm => s0
  cases h_eq
  have h_pre0 : (flashFloorSpec dp floor).Pre ca sevm s0 :=
    h_pre.state_eq burn.state.symm
  have hrun' : Func.Run ((weth10 dp).main :: weth10Aux) sevm s0
      (calldatasize ::: iszero :::
        (receiveEther <?>
          (fsig +++ dispatchWith fallbackSlot (weth10Tree dp)))) post := by
    simpa only [weth10, weth10Main] using hrun
  refine run_prepend_elim _ [calldatasize, iszero] ?_ hrun'
  intro s1 hentry hbranch
  have h_pre1 : (flashFloorSpec dp floor).Pre ca sevm s1 :=
    h_pre0.of_eqs
      (congrFun (Line.of_inv Devm.getCode (by line_inv) hentry).symm ca)
      (Line.of_inv Devm.getBal (by line_inv) hentry).symm
      (congrFun (Line.of_inv Devm.getStor (by line_inv) hentry).symm ca)
  rcases of_run_branch hbranch with
    ⟨s2, hpop, hdispatch⟩ |
    ⟨w, s2, s3, hnz, hpop, hburn, hreceive⟩
  · refine run_prepend_elim _ fsig ?_ hdispatch
    intro s3 hfsig hdispatch'
    have h_pre3 : (flashFloorSpec dp floor).Pre ca sevm s3 :=
      (h_pre1.state_eq hpop.state.symm).of_eqs
        (congrFun (Line.of_inv Devm.getCode (by line_inv) hfsig).symm ca)
        (Line.of_inv Devm.getBal (by line_inv) hfsig).symm
        (congrFun (Line.of_inv Devm.getStor (by line_inv) hfsig).symm ca)
    exact flashFloorPost_of_run_dispatch dp ca h_funcs
      (by
        intro floor' e x y hct hp hih hrev
        exact absurd hrev not_run_rev)
      h_target h_pre3 ih hdispatch'
  · exact h_receive h_target
      (h_pre1.state_eq (hburn.state.symm.trans hpop.state.symm))
      ih hreceive

/-! ### Exact flash-counter stability

The floor relation above is deliberately one-sided.  Flash settlement also
needs the stronger fact that a successful reentrant WETH10 dispatch restores
the exact counter present at its entry.  This relation is kept separate from
the frozen backing spec and from the floor relation. -/

/-- Equality to one caller-chosen flash-counter value. -/
def Stor.FlashAt (flash : B256) (s : Stor) : Prop :=
  s.get flashMintedSlot = flash

/-- Storage-only exact-counter spec used internally to transport the direct
equality relation through contract-neutral frame settlement. -/
def flashExactSpec (dp : DeployParams) (flash : B256) : ContractSpec where
  prog := weth10 dp
  Inv := fun s _ _ => Stor.FlashAt flash s
  Side := fun _ => True
  inv_forget := id
  inv_mono := fun h _ => h
  inv_recv := fun h _ => h
  side_le := fun _ _ => trivial
  side_transfer := fun _ _ => trivial
  side_addBal := fun _ _ => trivial
  inv_transfer := by
    intro st st' caller callee ca wad v h_sub h_ne _ h_inv
    show Stor.FlashAt flash _
    have h_stor : (st'.addBal callee wad).getStor ca = st.getStor ca := by
      rcases State.of_subBal h_sub with ⟨-, h_st'⟩
      show ((st'.setBal callee _).get ca).stor = (st.get ca).stor
      rw [State.setBal_get_stor, h_st', State.setBal_get_stor]
    rw [h_stor]
    exact h_inv
  inv_recv_transfer := by
    intro st st' caller ca wad h_sub h_ne _ h_inv
    show Stor.FlashAt flash _
    have h_stor : (st'.addBal ca wad).getStor ca = st.getStor ca := by
      rcases State.of_subBal h_sub with ⟨-, h_st'⟩
      show ((st'.setBal ca _).get ca).stor = (st.get ca).stor
      rw [State.setBal_get_stor, h_st', State.setBal_get_stor]
    rw [h_stor]
    exact h_inv
  inv_addBal := by
    intro w ca a val v _ _ h_inv
    show Stor.FlashAt flash _
    have h_stor : (w.addBal a val).getStor ca = w.getStor ca := by
      show ((w.setBal a _).get ca).stor = (w.get ca).stor
      rw [State.setBal_get_stor]
    rw [h_stor]
    exact h_inv

/-- Exact preservation of WETH10's temporary flash-mint counter. -/
def FlashExactRel (_dp : DeployParams) (ca : Adr)
    (_sevm : Sevm) (pre post : Devm) : Prop :=
  (Devm.getStor post ca).get flashMintedSlot =
    (Devm.getStor pre ca).get flashMintedSlot

/-- Every caller-chosen exact counter assertion admitted at `pre` remains true
at `post`.  Quantifying the assertion outside `Pre`/`Post` is what lets the
contract-neutral execution lift transport it through nested frames. -/
def FlashExactSpecsRel (dp : DeployParams) (ca : Adr)
    (sevm : Sevm) (pre post : Devm) : Prop :=
  ∀ flash,
    (flashExactSpec dp flash).Pre ca sevm pre →
    (flashExactSpec dp flash).Post ca sevm post

/-- A direct slot equality discharges the quantified exact-spec relation. -/
theorem flashExactSpecsRel_of_rel
    (dp : DeployParams) (ca : Adr)
    {sevm : Sevm} {pre post : Devm}
    (hrel : FlashExactRel dp ca sevm pre post) :
    FlashExactSpecsRel dp ca sevm pre post := by
  intro flash hpre
  refine ⟨trivial, ?_⟩
  change Stor.FlashAt flash (Devm.getStor post ca)
  have hinv : Stor.FlashAt flash (Devm.getStor pre ca) := by
    by_cases htarget : sevm.currentTarget = ca
    · exact hpre.inv.1 htarget
    · exact hpre.inv.2 htarget
  unfold FlashExactRel at hrel
  unfold Stor.FlashAt at hinv ⊢
  exact hrel.trans hinv

/-- Specializing the quantified relation at the entry counter recovers direct
slot equality whenever the entry carries the compiled WETH10 code. -/
theorem flashExactRel_of_specs
    (dp : DeployParams) (ca : Adr)
    {sevm : Sevm} {pre post : Devm}
    (hcode : some (pre.getCode ca).toList = Prog.compile (weth10 dp))
    (hspecs : FlashExactSpecsRel dp ca sevm pre post) :
    FlashExactRel dp ca sevm pre post := by
  let flash := (Devm.getStor pre ca).get flashMintedSlot
  have hpre : (flashExactSpec dp flash).Pre ca sevm pre := by
    refine ⟨hcode, trivial, ?_⟩
    constructor <;> intro _ <;> rfl
  have hpost := hspecs flash hpre
  unfold FlashExactRel
  change (Devm.getStor post ca).get flashMintedSlot = flash
  exact hpost.inv

/-- Deeper successful WETH10 executions preserve the exact entry counter. -/
def FlashExactDepth (dp : DeployParams) (ca : Adr) (depth : Nat) : Prop :=
  ForallSubExec depth ca (weth10 dp) (FlashExactSpecsRel dp ca)

/-- Contract-neutral execution transport for the quantified exact-counter
relation.  Frame steps use the ordinary `ContractSpec` ladder; only the
at-target WETH10 program body is supplied by the caller. -/
theorem flashExactSpecs_lift
    (dp : DeployParams) (ca : Adr)
    (body : ∀ {sevm pre post},
      Prog.Run sevm pre (weth10 dp) post →
      sevm.currentTarget = ca →
      FlashExactDepth dp ca sevm.depth →
      FlashExactSpecsRel dp ca sevm pre post) :
    ∀ pc sevm pre post,
      Exec pc sevm pre (.ok post) →
      Prog.At (weth10 dp) ca pc sevm pre →
      FlashExactSpecsRel dp ca sevm pre post := by
  apply @Blanc.lift (FlashExactSpecsRel dp ca) ca (weth10 dp) body
  · intro pc sevm pre n inter post h_at h_run _ h_ne h_rel flash h_pre
    apply h_rel flash
    cases n with
    | push xs le =>
      simp only [Ninst.StepRun, Ninst.step_push, Step.run_ofExecution] at h_run
      rcases Except.bind_eq_ok h_run.2.symm with
        ⟨devm1, h_charge, h_push⟩
      exact h_pre.state_eq
        (((Devm.burn_of_chargeGas h_charge).state).trans
          ((Devm.push_of_push h_push).state)).symm
    | reg r =>
      have h_reg : Rinst.run ⟨pc, sevm, pre⟩ r = .ok inter := by
        simp only [Ninst.StepRun, Ninst.step_reg,
          Step.run_ofExecution] at h_run
        exact h_run.2.symm
      by_cases h_ss : r = Rinst.sstore
      · subst h_ss
        have h_frame := Rinst.sstore_run_stateWriteFrame pc pre sevm
        rw [h_reg] at h_frame
        refine ContractSpec.Pre.of_eqs h_pre
          (h_frame.getCode_eq ca).symm ?_
          (sstore_preserves_getStor_ne h_reg h_ne)
        funext b
        exact (h_frame.getBal_eq b).symm
      · exact ContractSpec.Pre.of_eqs h_pre
          (Rinst.preserves_getCode h_reg ca)
          (Rinst.preserves_bal h_reg).symm
          (congrFun (Rinst.preserves_stor h_ss h_reg) ca).symm
    | exec x =>
      refine ContractSpec.Xinst.none_preserves_precond (x := x) ?_ h_ne h_pre
      simpa only [Ninst.StepRun, Ninst.step_exec,
        XStep.run_toStep, Xinst.Run] using h_run
  · intro pc sevm pre n evm' exn' inter post h_at h_run ex_sub _
      h_ne h_child h_rel flash h_pre
    cases n with
    | push xs le =>
      simp only [Ninst.StepRun, Ninst.step_push,
        Step.run_ofExecution] at h_run
      cases h_run.1
    | reg r =>
      simp only [Ninst.StepRun, Ninst.step_reg,
        Step.run_ofExecution] at h_run
      cases h_run.1
    | exec x =>
      rcases ContractSpec.Xinst.some_preserves_precond (x := x) (by
          simpa only [Ninst.StepRun, Ninst.step_exec,
            XStep.run_toStep, Xinst.Run] using h_run)
          ex_sub h_ne h_pre with
        ⟨h_pre_child, h_resume⟩
      apply h_rel flash
      apply h_resume
      cases exn' with
      | error e => trivial
      | ok childPost => exact h_child flash h_pre_child
  · intro pc sevm pre j pc' inter post h_at h_run _ h_ne h_rel flash h_pre
    exact h_rel flash
      (ContractSpec.Pre.state_eq h_pre (Jinst.preserves_state h_run))
  · intro pc sevm pre l post h_at h_run h_ne flash h_pre
    exact ContractSpec.Linst.inv_postcond h_run h_ne h_pre

/-- Leaf interface for exact flash-counter preservation.  The compiled-code
premise is explicit because callback-bearing leaves must construct the child
`Prog.At` witness used by the deeper-frame hypothesis. -/
def ExactRelFuncSound (dp : DeployParams) (ca : Adr) (f : Func) : Prop :=
  ∀ {sevm : Sevm} {s r : Devm},
    sevm.currentTarget = ca →
    some (s.getCode ca).toList = Prog.compile (weth10 dp) →
    FlashExactDepth dp ca sevm.depth →
    Func.Run ((weth10 dp).main :: weth10Aux) sevm s f r →
    FlashExactRel dp ca sevm s r

/-- An arbitrary value `CALL` preserves the exact flash counter whenever every
successful deeper WETH10 execution does.  Failed calls retain the parent
world; successful calls use `ProcessMessage` settlement and the recursive
`Prog.At` witness exactly as the floor proof does. -/
theorem flashExactRel_of_value_call
    (dp : DeployParams) (ca : Adr)
    {sevm : Sevm} {s sf : Devm} {g c v ii is oi os : B256}
    {xs : Stack}
    (h_target : sevm.currentTarget = ca)
    (ih : FlashExactDepth dp ca sevm.depth)
    (hp : (g :: c :: v :: ii :: is :: oi :: os :: xs) <<+ s.stack)
    (h_code : some (s.getCode ca).toList = Prog.compile (weth10 dp))
    (h_run : Ninst.Run sevm s call sf) :
    FlashExactRel dp ca sevm s sf := by
  rcases of_run_call_val_with_depth hp h_run with
    ⟨_, h_world⟩ |
      ⟨parent, child, xl, delegated, na, code, avail, h_depth,
        h_stack, h_parent_state, h_parent_memory, h_delegation,
        h_fill, h_pm, h_child_clean, h_resume, h_sf_state,
        h_returnData, h_memory, h_sf_stack⟩
  · unfold FlashExactRel
    rw [← h_world.getStor ca]
  · let childMsg :=
      callMsg sevm parent
        (min g.toNat (except64th avail) +
          (if v.toNat = 0 then 0 else gCallStipend))
        v sevm.currentTarget c.toAdr na true false
        ((s.memory.read ii.toNat is.toNat).1) code delegated
    change ProcessMessage childMsg xl (.ok child) at h_pm
    have hc_state : childMsg.benv.state = s.state := by
      change parent.state = s.state
      exact h_parent_state
    have hc_stv : childMsg.shouldTransferValue = true := rfl
    have hc_caller : childMsg.caller = ca := by
      change sevm.currentTarget = ca
      exact h_target
    have hc_value : childMsg.value = v := rfl
    have hc_target : childMsg.currentTarget = c.toAdr := rfl
    have hc_codeAddress : childMsg.codeAddress = some na := rfl
    obtain ⟨r0, hbody, hset⟩ := ProcessMessage.iff_body.mp h_pm
    unfold FrameBody at hbody
    rcases h_bt : childMsg.benvAfterTransfer with e | benv <;>
      rw [h_bt] at hbody
    · rw [hbody.2, processMessage.settle_error] at hset
      cases hset
    have h_exec : ExecuteCode (childMsg.withBenv benv) xl r0 := hbody
    rcases of_benvAfterTransfer hc_stv h_bt with
      ⟨st_mid, h_sub, h_benv⟩
    rw [hc_state, hc_caller, hc_value] at h_sub
    have h_benv_state :
        benv.state = st_mid.addBal c.toAdr v := by
      rw [h_benv, hc_target, hc_value]
      rfl
    rcases of_state_transfer_fields (callee := c.toAdr) h_sub with
      ⟨h_t_stor, h_t_code, h_le, h_t_self, h_t_ne⟩
    have h_entry_stor :
        Devm.getStor (initDevm (childMsg.withBenv benv)) ca =
          Devm.getStor s ca := by
      change benv.state.getStor ca = s.state.getStor ca
      rw [h_benv_state]
      change ((st_mid.addBal c.toAdr v).get ca).stor =
        (s.state.get ca).stor
      rw [h_t_stor ca]
    obtain ⟨evm2, h_r0, h_settle⟩ := processMessage.settle_ok_cases hset.symm
    subst h_r0
    rcases h_settle with ⟨h_err2, h_eq⟩ | ⟨h_err2, h_eq_child⟩
    · have : child.error.isSome = true := by
        rw [← h_eq]
        exact h_err2
      simp [h_child_clean] at this
    rw [h_eq_child] at h_exec h_err2
    have h_child_exact :
        FlashExactRel dp ca (initSevm (childMsg.withBenv benv))
          (initDevm (childMsg.withBenv benv)) child := by
      have hc_codeAddress' :
          (childMsg.withBenv benv).codeAddress = some na :=
        hc_codeAddress
      rcases of_executeCode_someCode hc_codeAddress' h_exec with
        ⟨h_precompile, h_xl_none, h_handle⟩ |
        ⟨h_precompile, exn, h_xl_some, h_handle⟩
      · have h_child_state :
            child.state = (initDevm (childMsg.withBenv benv)).state :=
          state_of_executePrecomp_ok h_handle h_err2
        unfold FlashExactRel
        exact congrArg
          (fun st => (st.getStor ca).get flashMintedSlot)
          h_child_state
      · have h_exn : exn = .ok child :=
          exec_ok_of_handleError h_handle h_err2
        rw [h_xl_some, h_exn] at h_fill
        obtain ⟨h_exec_child⟩ := h_fill
        have h_at : Prog.At (weth10 dp) ca 0
            (initSevm (childMsg.withBenv benv))
            (initDevm (childMsg.withBenv benv)) := by
          refine ⟨?_, ?_⟩
          · show some (benv.state.getCode ca).toList =
              Prog.compile (weth10 dp)
            rw [h_benv_state]
            change some ((st_mid.addBal c.toAdr v).get ca).code.toList =
              Prog.compile (weth10 dp)
            rw [h_t_code ca]
            exact h_code
          · intro h_child_target
            refine ⟨?_, rfl⟩
            have h_to_ca : c.toAdr = ca :=
              hc_target.symm.trans h_child_target
            change some code.toList = Prog.compile (weth10 dp)
            rcases h_delegation with
              ⟨h_none, _, h_code_self, h_not_delegated⟩ |
              ⟨d, h_some, _, h_code_delegated, h_delegated⟩
            · rw [h_code_self, h_to_ca]
              exact h_code
            · exfalso
              have h_not : ¬ isValidDelegation (s.getCode ca) :=
                not_delegation_of_compile h_code
              apply h_not
              unfold getDelegatedCodeAddress at h_some
              split at h_some
              · rename_i h_valid
                rw [h_to_ca] at h_valid
                exact h_valid
              · cases h_some
        have h_depth_lt :
            (initSevm (childMsg.withBenv benv)).depth < sevm.depth := by
          change sevm.depth - 1 < sevm.depth
          omega
        exact flashExactRel_of_specs dp ca h_at.left
          (ih 0
            (initSevm (childMsg.withBenv benv))
            (initDevm (childMsg.withBenv benv))
            child h_exec_child h_depth_lt h_at)
    unfold FlashExactRel at h_child_exact ⊢
    have h_stor : Devm.getStor sf ca = Devm.getStor child ca :=
      getStor_eq_of_state_eq h_sf_state ca
    rw [h_stor]
    exact h_child_exact.trans
      (congrArg (fun st => st.get flashMintedSlot) h_entry_stor)

/-- An arbitrary successful `STATICCALL` from a zero-value WETH10 frame
preserves the frozen backing invariant.  A failed call retains the parent
world; an entered call is discharged by ordinary child-frame settlement and
the recursive `FuncSoundNoMem` hypothesis. -/
theorem backedPost_of_static_call
    (dp : DeployParams) (ca : Adr)
    {sevm : Sevm} {s sf : Devm} {g t ii is oi os : B256}
    {xs : Stack}
    (h_target : sevm.currentTarget = ca)
    (h_value : sevm.value = 0)
    (ih : Exec.InvDepth sevm.depth ca (weth10 dp)
      ((backedSpec weth10 dp).PreWf ca) ((backedSpec weth10 dp).Post ca))
    (hp : (g :: t :: ii :: is :: oi :: os :: xs) <<+ s.stack)
    (h_pre : (backedSpec weth10 dp).Pre ca sevm s)
    (h_run : Ninst.Run sevm s statcall sf) :
    (backedSpec weth10 dp).Post ca sevm sf := by
  rcases of_run_statcall_val_with_depth hp h_run with
      ⟨_, h_world, _⟩ |
      ⟨parent, child, xl, delegated, na, code, avail, h_depth,
        h_stack, h_parent_state, h_parent_memory, h_delegation,
        h_fill, h_pm, h_child_clean, h_resume, h_sf_state,
        h_returnData, h_memory, h_sf_stack⟩
  · exact (backedSpec weth10 dp).post_of_pre
      (h_pre.state_eq h_world.1.symm)
  · let childMsg :=
      callMsg sevm parent (min g.toNat (except64th avail)) 0
        sevm.currentTarget t.toAdr na true true
        ((s.memory.read ii.toNat is.toNat).1) code delegated
    change ProcessMessage childMsg xl (.ok child) at h_pm
    have hc_state : childMsg.benv.state = s.state := by
      change parent.state = s.state
      exact h_parent_state
    have hc_stv : childMsg.shouldTransferValue = true := rfl
    have hc_caller : childMsg.caller = ca := by
      change sevm.currentTarget = ca
      exact h_target
    have hc_value : childMsg.value = 0 := rfl
    have hc_target : childMsg.currentTarget = t.toAdr := rfl
    have hc_codeAddress : childMsg.codeAddress = some na := rfl
    obtain ⟨r0, hbody, hset⟩ := ProcessMessage.iff_body.mp h_pm
    unfold FrameBody at hbody
    rcases h_bt : childMsg.benvAfterTransfer with e | benv <;>
      rw [h_bt] at hbody
    · rw [hbody.2, processMessage.settle_error] at hset
      cases hset
    have h_exec : ExecuteCode (childMsg.withBenv benv) xl r0 := hbody
    rcases of_benvAfterTransfer hc_stv h_bt with
      ⟨st_mid, h_sub, h_benv⟩
    rw [hc_state, hc_caller, hc_value] at h_sub
    have h_benv_state :
        benv.state = st_mid.addBal t.toAdr 0 := by
      rw [h_benv, hc_target, hc_value]
      rfl
    rcases of_state_transfer_fields (callee := t.toAdr) h_sub with
      ⟨h_t_stor, h_t_code, h_le, h_t_self, h_t_ne⟩
    have h_inv0 : Stor.Weth10Inv (Devm.getStor s ca) 0
        (s.getBal ca - 0) := by
      rw [b256_sub_zero]
      have h := h_pre.inv.1 h_target
      change Stor.Weth10Inv (Devm.getStor s ca) sevm.value
        (s.getBal ca) at h
      simpa only [h_value] using h
    have h_pre_child : (backedSpec weth10 dp).Pre ca
        (initSevm (childMsg.withBenv benv))
        (initDevm (childMsg.withBenv benv)) := by
      apply backedPre_of_withdraw_transfer dp
        (st := s.state) (st_mid := st_mid)
        (target := t.toAdr) (value := 0)
      · exact h_pre.code
      · exact h_pre.side
      · exact h_inv0
      · exact h_sub
      · exact h_benv_state
      · exact hc_target
      · exact hc_value
    obtain ⟨evm2, h_r0, h_settle⟩ := processMessage.settle_ok_cases hset.symm
    subst h_r0
    rcases h_settle with ⟨h_err2, h_eq⟩ | ⟨h_err2, h_eq_child⟩
    · have : child.error.isSome = true := by
        rw [← h_eq]
        exact h_err2
      simp [h_child_clean] at this
    rw [h_eq_child] at h_exec h_err2
    have h_child_post : (backedSpec weth10 dp).Post ca
        (initSevm (childMsg.withBenv benv)) child := by
      have hc_codeAddress' :
          (childMsg.withBenv benv).codeAddress = some na :=
        hc_codeAddress
      rcases of_executeCode_someCode hc_codeAddress' h_exec with
        ⟨h_precompile, h_xl_none, h_handle⟩ |
        ⟨h_precompile, exn, h_xl_some, h_handle⟩
      · have h_child_state :
            child.state = (initDevm (childMsg.withBenv benv)).state :=
          state_of_executePrecomp_ok h_handle h_err2
        exact (backedSpec weth10 dp).post_of_pre
          (h_pre_child.state_eq h_child_state)
      · have h_exn : exn = .ok child :=
          exec_ok_of_handleError h_handle h_err2
        rw [h_xl_some, h_exn] at h_fill
        obtain ⟨h_exec_child⟩ := h_fill
        have h_at : Prog.At (weth10 dp) ca 0
            (initSevm (childMsg.withBenv benv))
            (initDevm (childMsg.withBenv benv)) := by
          refine ⟨h_pre_child.code, ?_⟩
          intro h_child_target
          refine ⟨?_, rfl⟩
          have h_to_ca : t.toAdr = ca :=
            hc_target.symm.trans h_child_target
          change some code.toList = Prog.compile (weth10 dp)
          rcases h_delegation with
            ⟨h_none, _, h_code_self, h_not_delegated⟩ |
            ⟨d, h_some, _, h_code_delegated, h_delegated⟩
          · rw [h_code_self, h_to_ca]
            exact h_pre.code
          · exfalso
            have h_not : ¬ isValidDelegation (s.getCode ca) :=
              not_delegation_of_compile h_pre.code
            apply h_not
            unfold getDelegatedCodeAddress at h_some
            split at h_some
            · rename_i h_valid
              rw [h_to_ca] at h_valid
              exact h_valid
            · cases h_some
        have h_depth_lt :
            (initSevm (childMsg.withBenv benv)).depth < sevm.depth := by
          change sevm.depth - 1 < sevm.depth
          omega
        exact ih 0
          (initSevm (childMsg.withBenv benv))
          (initDevm (childMsg.withBenv benv))
          (.ok child) h_exec_child h_depth_lt h_at
          ⟨h_pre_child, fun _ => Mem.wf_empty⟩
    refine ⟨?_, ?_⟩
    · show SumNof sf.getBal
      have h_bal : sf.getBal = child.getBal :=
        funext (getBal_eq_of_state_eq h_sf_state)
      rw [h_bal]
      exact h_child_post.side
    · change Stor.Weth10Inv (Devm.getStor sf ca) 0 (sf.getBal ca)
      have h_stor : Devm.getStor sf ca = Devm.getStor child ca :=
        getStor_eq_of_state_eq h_sf_state ca
      have h_bal : sf.getBal ca = child.getBal ca :=
        getBal_eq_of_state_eq h_sf_state ca
      rw [h_stor, h_bal]
      exact h_child_post.inv

/-- An arbitrary `STATICCALL` preserves the exact flash counter whenever every
successful deeper WETH10 execution does.  This is the six-operand/static
counterpart of `flashExactRel_of_value_call`; in particular it also covers
delegated or non-precompile code at the permit recovery address. -/
theorem flashExactRel_of_static_call
    (dp : DeployParams) (ca : Adr)
    {sevm : Sevm} {s sf : Devm} {g t ii is oi os : B256}
    {xs : Stack}
    (h_target : sevm.currentTarget = ca)
    (ih : FlashExactDepth dp ca sevm.depth)
    (hp : (g :: t :: ii :: is :: oi :: os :: xs) <<+ s.stack)
    (h_code : some (s.getCode ca).toList = Prog.compile (weth10 dp))
    (h_run : Ninst.Run sevm s statcall sf) :
    FlashExactRel dp ca sevm s sf := by
  rcases of_run_statcall_val_with_depth hp h_run with
      ⟨_, h_world, _⟩ |
      ⟨parent, child, xl, delegated, na, code, avail, h_depth,
        h_stack, h_parent_state, h_parent_memory, h_delegation,
        h_fill, h_pm, h_child_clean, h_resume, h_sf_state,
        h_returnData, h_memory, h_sf_stack⟩
  · unfold FlashExactRel
    rw [← h_world.getStor ca]
  · let childMsg :=
      callMsg sevm parent (min g.toNat (except64th avail)) 0
        sevm.currentTarget t.toAdr na true true
        ((s.memory.read ii.toNat is.toNat).1) code delegated
    change ProcessMessage childMsg xl (.ok child) at h_pm
    have hc_state : childMsg.benv.state = s.state := by
      change parent.state = s.state
      exact h_parent_state
    have hc_stv : childMsg.shouldTransferValue = true := rfl
    have hc_caller : childMsg.caller = ca := by
      change sevm.currentTarget = ca
      exact h_target
    have hc_value : childMsg.value = 0 := rfl
    have hc_target : childMsg.currentTarget = t.toAdr := rfl
    have hc_codeAddress : childMsg.codeAddress = some na := rfl
    obtain ⟨r0, hbody, hset⟩ := ProcessMessage.iff_body.mp h_pm
    unfold FrameBody at hbody
    rcases h_bt : childMsg.benvAfterTransfer with e | benv <;>
      rw [h_bt] at hbody
    · rw [hbody.2, processMessage.settle_error] at hset
      cases hset
    have h_exec : ExecuteCode (childMsg.withBenv benv) xl r0 := hbody
    rcases of_benvAfterTransfer hc_stv h_bt with
      ⟨st_mid, h_sub, h_benv⟩
    rw [hc_state, hc_caller, hc_value] at h_sub
    have h_benv_state :
        benv.state = st_mid.addBal t.toAdr 0 := by
      rw [h_benv, hc_target, hc_value]
      rfl
    rcases of_state_transfer_fields (callee := t.toAdr) h_sub with
      ⟨h_t_stor, h_t_code, h_le, h_t_self, h_t_ne⟩
    have h_entry_stor :
        Devm.getStor (initDevm (childMsg.withBenv benv)) ca =
          Devm.getStor s ca := by
      change benv.state.getStor ca = s.state.getStor ca
      rw [h_benv_state]
      change ((st_mid.addBal t.toAdr 0).get ca).stor =
        (s.state.get ca).stor
      rw [h_t_stor ca]
    obtain ⟨evm2, h_r0, h_settle⟩ := processMessage.settle_ok_cases hset.symm
    subst h_r0
    rcases h_settle with ⟨h_err2, h_eq⟩ | ⟨h_err2, h_eq_child⟩
    · have : child.error.isSome = true := by
        rw [← h_eq]
        exact h_err2
      simp [h_child_clean] at this
    rw [h_eq_child] at h_exec h_err2
    have h_child_exact :
        FlashExactRel dp ca (initSevm (childMsg.withBenv benv))
          (initDevm (childMsg.withBenv benv)) child := by
      have hc_codeAddress' :
          (childMsg.withBenv benv).codeAddress = some na :=
        hc_codeAddress
      rcases of_executeCode_someCode hc_codeAddress' h_exec with
        ⟨h_precompile, h_xl_none, h_handle⟩ |
        ⟨h_precompile, exn, h_xl_some, h_handle⟩
      · have h_child_state :
            child.state = (initDevm (childMsg.withBenv benv)).state :=
          state_of_executePrecomp_ok h_handle h_err2
        unfold FlashExactRel
        exact congrArg
          (fun st => (st.getStor ca).get flashMintedSlot)
          h_child_state
      · have h_exn : exn = .ok child :=
          exec_ok_of_handleError h_handle h_err2
        rw [h_xl_some, h_exn] at h_fill
        obtain ⟨h_exec_child⟩ := h_fill
        have h_at : Prog.At (weth10 dp) ca 0
            (initSevm (childMsg.withBenv benv))
            (initDevm (childMsg.withBenv benv)) := by
          refine ⟨?_, ?_⟩
          · show some (benv.state.getCode ca).toList =
              Prog.compile (weth10 dp)
            rw [h_benv_state]
            change some ((st_mid.addBal t.toAdr 0).get ca).code.toList =
              Prog.compile (weth10 dp)
            rw [h_t_code ca]
            exact h_code
          · intro h_child_target
            refine ⟨?_, rfl⟩
            have h_to_ca : t.toAdr = ca :=
              hc_target.symm.trans h_child_target
            change some code.toList = Prog.compile (weth10 dp)
            rcases h_delegation with
              ⟨h_none, _, h_code_self, h_not_delegated⟩ |
              ⟨d, h_some, _, h_code_delegated, h_delegated⟩
            · rw [h_code_self, h_to_ca]
              exact h_code
            · exfalso
              have h_not : ¬ isValidDelegation (s.getCode ca) :=
                not_delegation_of_compile h_code
              apply h_not
              unfold getDelegatedCodeAddress at h_some
              split at h_some
              · rename_i h_valid
                rw [h_to_ca] at h_valid
                exact h_valid
              · cases h_some
        have h_depth_lt :
            (initSevm (childMsg.withBenv benv)).depth < sevm.depth := by
          change sevm.depth - 1 < sevm.depth
          omega
        exact flashExactRel_of_specs dp ca h_at.left
          (ih 0
            (initSevm (childMsg.withBenv benv))
            (initDevm (childMsg.withBenv benv))
            child h_exec_child h_depth_lt h_at)
    unfold FlashExactRel at h_child_exact ⊢
    have h_stor : Devm.getStor sf ca = Devm.getStor child ca :=
      getStor_eq_of_state_eq h_sf_state ca
    rw [h_stor]
    exact h_child_exact.trans
      (congrArg (fun st => st.get flashMintedSlot) h_entry_stor)

/-! ### Exact permit-slot transport -/

/-- Exact boundary for permit's only recursive machine step.  The generated
permit body is WETH10-silent on both sides of this retained `STATICCALL`;
the child itself stays explicit, so this relation makes no endpoint claim
across arbitrary code at the recovery address. -/
inductive PermitBalanceOwnSilent (sevm : Sevm) (pre post : Devm) : Prop
  | intro (callPre callPost : Devm) (pc : Nat) (slot : Xlot)
      (prefixSilent : Stor.Weth10Silent
        (Devm.getStor pre sevm.currentTarget)
        (Devm.getStor callPre sevm.currentTarget))
      (filled : Xlot.Filled slot)
      (step : Ninst.StepRun pc sevm callPre statcall slot (.ok callPost))
      (suffixSilent : Stor.Weth10Silent
        (Devm.getStor callPost sevm.currentTarget)
        (Devm.getStor post sevm.currentTarget))

theorem PermitBalanceOwnSilent.prepend
    {sevm : Sevm} {first pre post : Devm}
    (silent : Stor.Weth10Silent
      (Devm.getStor first sevm.currentTarget)
      (Devm.getStor pre sevm.currentTarget))
    (effect : PermitBalanceOwnSilent sevm pre post) :
    PermitBalanceOwnSilent sevm first post := by
  rcases effect with
    ⟨callPre, callPost, pc, slot, hprefixSilent, filled, step,
      hsuffixSilent⟩
  exact .intro callPre callPost pc slot
    (silent.trans hprefixSilent) filled step hsuffixSilent

theorem PermitBalanceOwnSilent.append
    {sevm : Sevm} {pre post last : Devm}
    (effect : PermitBalanceOwnSilent sevm pre post)
    (silent : Stor.Weth10Silent
      (Devm.getStor post sevm.currentTarget)
      (Devm.getStor last sevm.currentTarget)) :
    PermitBalanceOwnSilent sevm pre last := by
  rcases effect with
    ⟨callPre, callPost, pc, slot, hprefixSilent, filled, step,
      hsuffixSilent⟩
  exact .intro callPre callPost pc slot hprefixSilent filled step
    (hsuffixSilent.trans silent)

private lemma permit_prefix_of_chainid
    {e : Sevm} {s s' : Devm} {xs : Stack}
    (hp : xs <<+ s.stack) (run : Ninst.Run e s chainid s') :
    e.benvStat.chainId.toB256 :: xs <<+ s'.stack := by
  rcases of_run_reg run with ⟨pc, hrun⟩
  simp only [Rinst.run, Rinst.runCore] at hrun
  exact prefix_of_push (Devm.pushBurn_of_pushItem hrun) hp

/-- The nonce prefix isolated from `permit`.  Keeping this local to the state
proof avoids making the authentication-oriented permit module an upstream
dependency. -/
private def permitNonceFlashPrefix : Line :=
  [chainid] ++ addressArg 0 ++ [dup 0] ++ tagNonceKey ++
  [dup 0, sload, dup 0] ++ mstoreAt 4 ++
  [pushB256 1, add, swap 0, sstore, pop]

/-- The normalized nonce write is outside both the address-shaped balance
region and the flash slot. -/
private theorem permitNonceFlashPrefix_silent
    {sevm : Sevm} {s t : Devm}
    (run : Line.Run sevm s permitNonceFlashPrefix t) :
    Stor.Weth10Silent
      (Devm.getStor s sevm.currentTarget)
      (Devm.getStor t sevm.currentTarget) := by
  unfold permitNonceFlashPrefix at run
  rcases Line.of_run_cons run with ⟨s1, q1, run⟩
  have hp1 : sevm.benvStat.chainId.toB256 :: [] <<+ s1.stack :=
    permit_prefix_of_chainid nil_pref q1
  rcases of_run_append (addressArg 0) run with ⟨s2, h2, run⟩
  have hp2 : ((~~~ addressMask) &&& Sevm.argWord sevm 0) ::
      sevm.benvStat.chainId.toB256 :: [] <<+ s2.stack :=
    prefix_of_addressArg hp1 h2
  rcases Line.of_run_cons run with ⟨s3, q3, run⟩
  have hp3 : ((~~~ addressMask) &&& Sevm.argWord sevm 0) ::
      ((~~~ addressMask) &&& Sevm.argWord sevm 0) ::
      sevm.benvStat.chainId.toB256 :: [] <<+ s3.stack :=
    prefix_of_dup_val q3 (by show_nth) hp2
  rcases of_run_append tagNonceKey run with ⟨s4, h4, run⟩
  have hp4 :
      (nonceTagWord ||| ((~~~ addressMask) &&& Sevm.argWord sevm 0)) ::
      ((~~~ addressMask) &&& Sevm.argWord sevm 0) ::
      sevm.benvStat.chainId.toB256 :: [] <<+ s4.stack := by
    unfold tagNonceKey at h4
    rcases Line.of_run_cons h4 with ⟨u41, q41, h4⟩
    have hp41 : nonceTagWord ::
        ((~~~ addressMask) &&& Sevm.argWord sevm 0) ::
        ((~~~ addressMask) &&& Sevm.argWord sevm 0) ::
        sevm.benvStat.chainId.toB256 :: [] <<+ u41.stack :=
      prefix_of_push (of_run_pushB256 q41) hp3
    rcases Line.of_run_cons h4 with ⟨u42, q42, hnil⟩
    cases hnil
    exact prefix_of_or q42 hp41
  rcases Line.of_run_cons run with ⟨s5, q5, run⟩
  have hp5 :
      (nonceTagWord ||| ((~~~ addressMask) &&& Sevm.argWord sevm 0)) ::
      (nonceTagWord ||| ((~~~ addressMask) &&& Sevm.argWord sevm 0)) ::
      ((~~~ addressMask) &&& Sevm.argWord sevm 0) ::
      sevm.benvStat.chainId.toB256 :: [] <<+ s5.stack :=
    prefix_of_dup_val q5 (by show_nth) hp4
  rcases Line.of_run_cons run with ⟨s6, q6, run⟩
  rcases prefix_of_sload q6 hp5 with ⟨nonce, hp6, hnonce⟩
  rcases Line.of_run_cons run with ⟨s7, q7, run⟩
  have hp7 : nonce :: nonce ::
      (nonceTagWord ||| ((~~~ addressMask) &&& Sevm.argWord sevm 0)) ::
      ((~~~ addressMask) &&& Sevm.argWord sevm 0) ::
      sevm.benvStat.chainId.toB256 :: [] <<+ s7.stack :=
    prefix_of_dup_val q7 (by show_nth) hp6
  rcases of_run_append (mstoreAt 4) run with ⟨s8, h8, run⟩
  rcases of_run_mstoreAt_val h8 hp7 with ⟨hp8, hm8⟩
  rcases Line.of_run_cons run with ⟨s9, q9, run⟩
  have hp9 : (1 : B256) :: nonce ::
      (nonceTagWord ||| ((~~~ addressMask) &&& Sevm.argWord sevm 0)) ::
      ((~~~ addressMask) &&& Sevm.argWord sevm 0) ::
      sevm.benvStat.chainId.toB256 :: [] <<+ s9.stack :=
    prefix_of_push (of_run_pushB256 q9) hp8
  rcases Line.of_run_cons run with ⟨s10, q10, run⟩
  have hp10 : (nonce + 1) ::
      (nonceTagWord ||| ((~~~ addressMask) &&& Sevm.argWord sevm 0)) ::
      ((~~~ addressMask) &&& Sevm.argWord sevm 0) ::
      sevm.benvStat.chainId.toB256 :: [] <<+ s10.stack := by
    have h := prefix_of_add q10 hp9
    simpa only [B256.add_comm] using h
  rcases Line.of_run_cons run with ⟨s11, q11, run⟩
  have hp11 :
      (nonceTagWord ||| ((~~~ addressMask) &&& Sevm.argWord sevm 0)) ::
      (nonce + 1) ::
      ((~~~ addressMask) &&& Sevm.argWord sevm 0) ::
      sevm.benvStat.chainId.toB256 :: [] <<+ s11.stack := by
    have hswap : Stack.Swap (0 : Fin 16).val
        ((nonce + 1) ::
          (nonceTagWord ||| ((~~~ addressMask) &&& Sevm.argWord sevm 0)) ::
          ((~~~ addressMask) &&& Sevm.argWord sevm 0) ::
          sevm.benvStat.chainId.toB256 :: [])
        ((nonceTagWord ||| ((~~~ addressMask) &&& Sevm.argWord sevm 0)) ::
          (nonce + 1) ::
          ((~~~ addressMask) &&& Sevm.argWord sevm 0) ::
          sevm.benvStat.chainId.toB256 :: []) :=
      Stack.swapCore_zero
    exact Stack.prefix_of_swap hswap (of_run_swap q11) hp10
  rcases Line.of_run_cons run with ⟨s12, q12, run⟩
  have hset : Devm.getStor s12 sevm.currentTarget =
      (Devm.getStor s11 sevm.currentTarget).set
        (nonceTagWord ||| ((~~~ addressMask) &&& Sevm.argWord sevm 0))
        (nonce + 1) :=
    sstore_getStor_set q12 hp11
  rcases Line.of_run_cons run with ⟨s13, q13, hnil⟩
  cases hnil
  have hstor11 : Devm.getStor s = Devm.getStor s11 := by
    calc
      Devm.getStor s = Devm.getStor s1 :=
        Ninst.Hinv.inv (f := Devm.getStor) q1
      _ = Devm.getStor s2 := Line.of_inv Devm.getStor (by line_inv) h2
      _ = Devm.getStor s3 := Ninst.Hinv.inv (f := Devm.getStor) q3
      _ = Devm.getStor s4 := Line.of_inv Devm.getStor (by
        unfold tagNonceKey
        line_inv) h4
      _ = Devm.getStor s5 := Ninst.Hinv.inv (f := Devm.getStor) q5
      _ = Devm.getStor s6 := Ninst.Hinv.inv (f := Devm.getStor) q6
      _ = Devm.getStor s7 := Ninst.Hinv.inv (f := Devm.getStor) q7
      _ = Devm.getStor s8 := Line.of_inv Devm.getStor (by line_inv) h8
      _ = Devm.getStor s9 := Ninst.Hinv.inv (f := Devm.getStor) q9
      _ = Devm.getStor s10 := Ninst.Hinv.inv (f := Devm.getStor) q10
      _ = Devm.getStor s11 := Ninst.Hinv.inv (f := Devm.getStor) q11
  have hstor12 : Devm.getStor s12 = Devm.getStor t :=
    Ninst.Hinv.inv (f := Devm.getStor) q13
  rw [← congrFun hstor12 sevm.currentTarget, hset,
    ← congrFun hstor11 sevm.currentTarget]
  exact Stor.Weth10Silent.set
    (runtimeNonceKey_not_valid (Sevm.argWord sevm 0))
    (runtimeNonceKey_ne_flash (Sevm.argWord sevm 0))

/-- Exact-counter projection of the stronger normalized nonce-write frame. -/
private theorem permitNonceFlashPrefix_exactRel
    (dp : DeployParams) (ca : Adr)
    {sevm : Sevm} {s t : Devm}
    (h_target : sevm.currentTarget = ca)
    (run : Line.Run sevm s permitNonceFlashPrefix t) :
    FlashExactRel dp ca sevm s t := by
  subst ca
  exact (permitNonceFlashPrefix_silent run).2

private def permitRecoverFlashWrites : Line :=
  mstoreAt 0 ++
  arg 4 ++ mstoreAt 1 ++
  arg 5 ++ mstoreAt 2 ++
  arg 6 ++ mstoreAt 3 ++
  [pushB256 0] ++ mstoreAt 4 ++
  pushList [32, 128, 128, 0, 1]

private def permitRecoverFlashPrepare : Line :=
  permitRecoverFlashWrites ++ [gas]

private lemma exists_head_of_run_mstoreAt
    {e : Sevm} {s t : Devm} {k : B256}
    (run : Line.Run e s (mstoreAt k) t) :
    ∃ word xs, word :: xs <<+ s.stack := by
  unfold mstoreAt at run
  rcases Line.of_run_cons run with ⟨u, hpush, run⟩
  rcases Line.of_run_cons run with ⟨v, hstore, hnil⟩
  cases hnil
  have hpb := of_run_pushB256 hpush
  rcases of_run_mstore hstore with ⟨offset, word, hpop⟩
  have hs : (k * 32) :: s.stack = offset :: word :: t.stack :=
    hpb.stack.symm.trans hpop
  injection hs with hoff htail
  refine ⟨word, t.stack, ?_⟩
  rw [htail]
  simpa using (pref_append (word :: t.stack) [])

/-- Stack and world frame at permit's recovery `STATICCALL`. -/
private theorem permitRecoverFlashPrepare_frame
    {sevm : Sevm} {s t : Devm} {word : B256} {xs : Stack}
    (hp : word :: xs <<+ s.stack)
    (run : Line.Run sevm s permitRecoverFlashPrepare t) :
    ∃ g : B256,
      g :: (1 : B256) :: (0 : B256) :: (128 : B256) ::
        (128 : B256) :: (32 : B256) :: xs <<+ t.stack ∧
      Devm.getStor s = Devm.getStor t ∧
      Devm.getCode s = Devm.getCode t := by
  unfold permitRecoverFlashPrepare permitRecoverFlashWrites at run
  rcases of_run_append (mstoreAt 0) run with ⟨s1, h1, run⟩
  rcases of_run_mstoreAt_val h1 hp with ⟨hp1, hm1⟩
  rcases of_run_append (arg 4) run with ⟨s2, h2, run⟩
  have hp2 : Sevm.argWord sevm 4 :: xs <<+ s2.stack :=
    prefix_of_arg hp1 h2
  rcases of_run_append (mstoreAt 1) run with ⟨s3, h3, run⟩
  rcases of_run_mstoreAt_val h3 hp2 with ⟨hp3, hm3⟩
  rcases of_run_append (arg 5) run with ⟨s4, h4, run⟩
  have hp4 : Sevm.argWord sevm 5 :: xs <<+ s4.stack :=
    prefix_of_arg hp3 h4
  rcases of_run_append (mstoreAt 2) run with ⟨s5, h5, run⟩
  rcases of_run_mstoreAt_val h5 hp4 with ⟨hp5, hm5⟩
  rcases of_run_append (arg 6) run with ⟨s6, h6, run⟩
  have hp6 : Sevm.argWord sevm 6 :: xs <<+ s6.stack :=
    prefix_of_arg hp5 h6
  rcases of_run_append (mstoreAt 3) run with ⟨s7, h7, run⟩
  rcases of_run_mstoreAt_val h7 hp6 with ⟨hp7, hm7⟩
  rcases of_run_append [pushB256 0] run with ⟨s8, h8, run⟩
  rcases Line.of_run_cons h8 with ⟨u8, q8, hnil⟩
  cases hnil
  have hp8 : (0 : B256) :: xs <<+ s8.stack :=
    prefix_of_push (of_run_pushB256 q8) hp7
  rcases of_run_append (mstoreAt 4) run with ⟨s9, h9, run⟩
  rcases of_run_mstoreAt_val h9 hp8 with ⟨hp9, hm9⟩
  rcases of_run_append (pushList [32, 128, 128, 0, 1]) run with
    ⟨s10, h10, hgas⟩
  have hpushes := h10
  simp only [pushList, List.map] at h10
  rcases Line.of_run_cons h10 with ⟨u1, q1, h10⟩
  have hp10a : (32 : B256) :: xs <<+ u1.stack :=
    prefix_of_push (of_run_pushB256 q1) hp9
  rcases Line.of_run_cons h10 with ⟨u2, q2, h10⟩
  have hp10b : (128 : B256) :: (32 : B256) :: xs <<+ u2.stack :=
    prefix_of_push (of_run_pushB256 q2) hp10a
  rcases Line.of_run_cons h10 with ⟨u3, q3, h10⟩
  have hp10c : (128 : B256) :: (128 : B256) :: (32 : B256) :: xs <<+
      u3.stack := prefix_of_push (of_run_pushB256 q3) hp10b
  rcases Line.of_run_cons h10 with ⟨u4, q4, h10⟩
  have hp10d : (0 : B256) :: (128 : B256) :: (128 : B256) ::
      (32 : B256) :: xs <<+ u4.stack :=
    prefix_of_push (of_run_pushB256 q4) hp10c
  rcases Line.of_run_cons h10 with ⟨u5, q5, hnil⟩
  cases hnil
  have hp10 : (1 : B256) :: (0 : B256) :: (128 : B256) ::
      (128 : B256) :: (32 : B256) :: xs <<+ s10.stack :=
    prefix_of_push (of_run_pushB256 q5) hp10d
  rcases Line.of_run_cons hgas with ⟨s11, q11, hnil⟩
  cases hnil
  rcases of_run_gas q11 with ⟨g, hpush⟩
  have hstorWrites : Devm.getStor s = Devm.getStor s10 := by
    calc
      Devm.getStor s = Devm.getStor s1 :=
        Line.of_inv Devm.getStor (by line_inv) h1
      _ = Devm.getStor s2 := Line.of_inv Devm.getStor (by line_inv) h2
      _ = Devm.getStor s3 := Line.of_inv Devm.getStor (by line_inv) h3
      _ = Devm.getStor s4 := Line.of_inv Devm.getStor (by line_inv) h4
      _ = Devm.getStor s5 := Line.of_inv Devm.getStor (by line_inv) h5
      _ = Devm.getStor s6 := Line.of_inv Devm.getStor (by line_inv) h6
      _ = Devm.getStor s7 := Line.of_inv Devm.getStor (by line_inv) h7
      _ = Devm.getStor s8 := Line.of_inv Devm.getStor (by line_inv) h8
      _ = Devm.getStor s9 := Line.of_inv Devm.getStor (by line_inv) h9
      _ = Devm.getStor s10 := Line.of_inv Devm.getStor
        (show Line.Inv Devm.getStor (pushList [32, 128, 128, 0, 1]) by
          unfold pushList
          line_inv) hpushes
  have hcodeWrites : Devm.getCode s = Devm.getCode s10 := by
    calc
      Devm.getCode s = Devm.getCode s1 :=
        Line.of_inv Devm.getCode (by line_inv) h1
      _ = Devm.getCode s2 := Line.of_inv Devm.getCode (by line_inv) h2
      _ = Devm.getCode s3 := Line.of_inv Devm.getCode (by line_inv) h3
      _ = Devm.getCode s4 := Line.of_inv Devm.getCode (by line_inv) h4
      _ = Devm.getCode s5 := Line.of_inv Devm.getCode (by line_inv) h5
      _ = Devm.getCode s6 := Line.of_inv Devm.getCode (by line_inv) h6
      _ = Devm.getCode s7 := Line.of_inv Devm.getCode (by line_inv) h7
      _ = Devm.getCode s8 := Line.of_inv Devm.getCode (by line_inv) h8
      _ = Devm.getCode s9 := Line.of_inv Devm.getCode (by line_inv) h9
      _ = Devm.getCode s10 := Line.of_inv Devm.getCode
        (show Line.Inv Devm.getCode (pushList [32, 128, 128, 0, 1]) by
          unfold pushList
          line_inv) hpushes
  refine ⟨g, prefix_of_push hpush hp10, ?_, ?_⟩
  · exact hstorWrites.trans (funext fun a =>
      getStor_eq_of_state_eq hpush.state a)
  · exact hcodeWrites.trans (funext fun a =>
      getCode_eq_of_state_eq hpush.state a)

/-- The recovery line's own instructions are balance-silent on both sides of
its exact `STATICCALL` instruction. -/
private theorem recoverPermitSigner_balanceOwnSilent
    {sevm : Sevm} {s r : Devm}
    (run : Line.Run sevm s recoverPermitSigner r) :
    PermitBalanceOwnSilent sevm s r := by
  change Line.Run sevm s
    (permitRecoverFlashPrepare ++ [statcall, pop, pushB256 128, mload]) r
    at run
  rcases of_run_append permitRecoverFlashPrepare run with
    ⟨callPre, hprepare, run⟩
  rcases Line.of_run_cons run with ⟨callPost, hcall, htail⟩
  rcases hcall with ⟨slot, hfilled, pc, hstep⟩
  have hstorPrepare : Devm.getStor s = Devm.getStor callPre :=
    Line.of_inv Devm.getStor (by
      unfold permitRecoverFlashPrepare permitRecoverFlashWrites pushList
      line_inv) hprepare
  have hstorTail : Devm.getStor callPost = Devm.getStor r :=
    Line.of_inv Devm.getStor (by line_inv) htail
  exact .intro callPre callPost pc slot
    (Stor.Weth10Silent.of_eq
      (congrFun hstorPrepare sevm.currentTarget))
    hfilled hstep
    (Stor.Weth10Silent.of_eq
      (congrFun hstorTail sevm.currentTarget))

/-- Permit recovery is exact-counter preserving even when address `1` is not
the canonical precompile: the arbitrary static subtree is discharged by the
deeper-frame relation. -/
private theorem recoverPermitSigner_exactRel
    (dp : DeployParams) (ca : Adr)
    {sevm : Sevm} {s r : Devm}
    (h_target : sevm.currentTarget = ca)
    (ih : FlashExactDepth dp ca sevm.depth)
    (h_code : some (s.getCode ca).toList = Prog.compile (weth10 dp))
    (run : Line.Run sevm s recoverPermitSigner r) :
    FlashExactRel dp ca sevm s r := by
  change Line.Run sevm s
    (permitRecoverFlashPrepare ++ [statcall, pop, pushB256 128, mload]) r at run
  rcases of_run_append permitRecoverFlashPrepare run with
    ⟨sp, hprep, run⟩
  have hfirst : ∃ s1,
      Line.Run sevm s (mstoreAt 0) s1 := by
    unfold permitRecoverFlashPrepare permitRecoverFlashWrites at hprep
    rcases of_run_append (mstoreAt 0) hprep with ⟨s1, hfirst, hrest⟩
    exact ⟨s1, hfirst⟩
  rcases hfirst with ⟨s1, hfirst⟩
  rcases exists_head_of_run_mstoreAt hfirst with ⟨word, xs, hp⟩
  rcases permitRecoverFlashPrepare_frame hp hprep with
    ⟨g, hpCall, hstorPrep, hcodePrep⟩
  rcases Line.of_run_cons run with ⟨sc, hcall, htail⟩
  have hcodeSp : some (sp.getCode ca).toList =
      Prog.compile (weth10 dp) := by
    rw [← hcodePrep]
    exact h_code
  have hcallExact := flashExactRel_of_static_call dp ca
    h_target ih hpCall hcodeSp hcall
  have hstorTail : Devm.getStor sc = Devm.getStor r :=
    Line.of_inv Devm.getStor (by line_inv) htail
  unfold FlashExactRel at hcallExact ⊢
  exact (congrArg (fun st => st.get flashMintedSlot)
      (congrFun hstorTail ca)).symm.trans
    (hcallExact.trans
      (congrArg (fun st => st.get flashMintedSlot)
        (congrFun hstorPrep ca)).symm)

/-- Permit recovery's arbitrary static subtree preserves backing, while the
scratch preparation and post-call word load are world-silent. -/
private theorem recoverPermitSigner_backed
    (dp : DeployParams) (ca : Adr)
    {sevm : Sevm} {s r : Devm}
    (h_target : sevm.currentTarget = ca)
    (h_value : sevm.value = 0)
    (h_pre : (backedSpec weth10 dp).Pre ca sevm s)
    (ih : Exec.InvDepth sevm.depth ca (weth10 dp)
      ((backedSpec weth10 dp).PreWf ca) ((backedSpec weth10 dp).Post ca))
    (run : Line.Run sevm s recoverPermitSigner r) :
    (backedSpec weth10 dp).Post ca sevm r := by
  change Line.Run sevm s
    (permitRecoverFlashPrepare ++ [statcall, pop, pushB256 128, mload]) r at run
  rcases of_run_append permitRecoverFlashPrepare run with
    ⟨sp, hprep, run⟩
  have hfirst : ∃ s1,
      Line.Run sevm s (mstoreAt 0) s1 := by
    unfold permitRecoverFlashPrepare permitRecoverFlashWrites at hprep
    rcases of_run_append (mstoreAt 0) hprep with ⟨s1, hfirst, hrest⟩
    exact ⟨s1, hfirst⟩
  rcases hfirst with ⟨s1, hfirst⟩
  rcases exists_head_of_run_mstoreAt hfirst with ⟨word, xs, hp⟩
  rcases permitRecoverFlashPrepare_frame hp hprep with
    ⟨g, hpCall, hstorPrep, hcodePrep⟩
  have hbalPrep : Devm.getBal s = Devm.getBal sp :=
    Line.of_inv Devm.getBal (by
      unfold permitRecoverFlashPrepare permitRecoverFlashWrites pushList
      line_inv) hprep
  have hpreSp : (backedSpec weth10 dp).Pre ca sevm sp :=
    backedPre_of_silent dp ca h_pre
      (Stor.Weth10Silent.of_eq (congrFun hstorPrep ca))
      hbalPrep (congrFun hcodePrep ca)
  rcases Line.of_run_cons run with ⟨sc, hcall, htail⟩
  have hpostCall := backedPost_of_static_call dp ca h_target h_value ih
    hpCall hpreSp hcall
  have hstorTail : Devm.getStor sc = Devm.getStor r :=
    Line.of_inv Devm.getStor (by line_inv) htail
  have hbalTail : Devm.getBal sc = Devm.getBal r :=
    Line.of_inv Devm.getBal (by line_inv) htail
  exact backedPost_of_silent dp ca hpostCall
    (Stor.Weth10Silent.of_eq (congrFun hstorTail ca)) hbalTail

/-- The successful permit approval tail writes only a tagged allowance key. -/
private theorem approvePermit_storage_silent (dp : DeployParams)
    {sevm : Sevm} {s r : Devm}
    (run : Func.Run ((weth10 dp).main :: weth10Aux) sevm s
      approvePermit r) :
    Stor.Weth10Silent
      (Devm.getStor s sevm.currentTarget)
      (Devm.getStor r sevm.currentTarget) := by
  unfold approvePermit at run
  rcases of_run_prepend (argCopy 0 0 2) _ run with
    ⟨s1, hcopy, run⟩
  rcases of_run_prepend allowanceKeyFromMemory _ run with
    ⟨s2, hkey, run⟩
  rcases prefix_of_allowanceKeyFromMemory nil_pref hkey with
    ⟨hash, hp2⟩
  let key := allowanceTagWord ||| (allowancePayloadMask &&& hash)
  rcases of_run_prepend (arg 2) _ run with ⟨s3, harg, run⟩
  have hp3 : Sevm.argWord sevm 2 :: key :: [] <<+ s3.stack :=
    prefix_of_arg hp2 harg
  rcases of_run_next run with ⟨s4, hswap, run⟩
  have hswapCore : Stack.Swap (0 : Fin 16).val
      [Sevm.argWord sevm 2, key] [key, Sevm.argWord sevm 2] :=
    Stack.swapCore_zero
  have hp4 : key :: Sevm.argWord sevm 2 :: [] <<+ s4.stack :=
    Stack.prefix_of_swap hswapCore (of_run_swap hswap) hp3
  rcases of_run_next run with ⟨s5, hstore, htail⟩
  have hset : Devm.getStor s5 sevm.currentTarget =
      (Devm.getStor s4 sevm.currentTarget).set key
        (Sevm.argWord sevm 2) :=
    sstore_getStor_set hstore hp4
  have hbefore : Devm.getStor s = Devm.getStor s4 := by
    rw [Line.of_inv Devm.getStor (by line_inv) hcopy,
      Line.of_inv Devm.getStor (by line_inv) hkey,
      Line.of_inv Devm.getStor (by line_inv) harg,
      Line.of_inv Devm.getStor (by line_inv)
        (Line.Run.cons hswap Line.Run.nil)]
  have hafter : Devm.getStor s5 = Devm.getStor r :=
    Func.of_inv Devm.getStor Devm.getStor (by func_inv) htail
  rw [← congrFun hafter sevm.currentTarget, hset,
    ← congrFun hbefore sevm.currentTarget]
  exact Stor.Weth10Silent.set
    (runtimeAllowanceKey_not_valid hash)
    (runtimeAllowanceKey_ne_flash hash)

private theorem approvePermit_flashStable (dp : DeployParams) :
    FlashStable dp approvePermit := by
  intro sevm s r run
  exact (approvePermit_storage_silent dp run).2

private def permitSignerFlashGuards : Func :=
  dup 0 ::: iszero :::
  (.call invalidPermitErrorSlot) <?>
  (arg 0 +++ eq ::: iszero :::
    (.call invalidPermitErrorSlot) <?>
    approvePermit)

/-- The signer guards themselves are world-silent, and their only successful
continuation is the tagged allowance write proved silent above. -/
private theorem permitSignerFlashGuards_balanceSilent
    (dp : DeployParams) {sevm : Sevm} {s r : Devm}
    (run : Func.Run ((weth10 dp).main :: weth10Aux) sevm s
      permitSignerFlashGuards r) :
    Stor.Weth10Silent
      (Devm.getStor s sevm.currentTarget)
      (Devm.getStor r sevm.currentTarget) := by
  unfold permitSignerFlashGuards at run
  rcases of_run_next run with ⟨s1, hdup, run⟩
  rcases of_run_next run with ⟨s2, hzero, run⟩
  rcases of_run_branch run with
      ⟨s3, hpop1, run⟩ |
      ⟨w1, s3, s4, hnz1, hpop1, hburn1, hinvalid1⟩
  · rcases of_run_prepend (arg 0) _ run with ⟨s4, harg0, run⟩
    rcases of_run_next run with ⟨s5, heq, run⟩
    rcases of_run_next run with ⟨s6, hzero2, run⟩
    rcases of_run_branch run with
        ⟨t, hpop2, happrove⟩ |
        ⟨w2, t0, t, hnz2, hpop2, hburn2, hinvalid2⟩
    · have hstor : Devm.getStor s = Devm.getStor t := by
        calc
          Devm.getStor s = Devm.getStor s1 :=
            Ninst.Hinv.inv (f := Devm.getStor) hdup
          _ = Devm.getStor s2 :=
            Ninst.Hinv.inv (f := Devm.getStor) hzero
          _ = Devm.getStor s3 := PopBurn.Inv.inv hpop1
          _ = Devm.getStor s4 :=
            Line.of_inv Devm.getStor (by line_inv) harg0
          _ = Devm.getStor s5 :=
            Ninst.Hinv.inv (f := Devm.getStor) heq
          _ = Devm.getStor s6 :=
            Ninst.Hinv.inv (f := Devm.getStor) hzero2
          _ = Devm.getStor t := PopBurn.Inv.inv hpop2
      exact (Stor.Weth10Silent.of_eq
        (congrFun hstor sevm.currentTarget)).trans
          (approvePermit_storage_silent dp happrove)
    · rcases of_run_call hinvalid2 with
        ⟨f, u, hget, hcallBurn, hrev⟩
      have hf : f = invalidPermitError := by
        simpa [weth10Aux, invalidPermitErrorSlot] using hget.symm
      subst f
      exact absurd hrev Func.not_run_revWith
  · rcases of_run_call hinvalid1 with ⟨f, u, hget, hcallBurn, hrev⟩
    have hf : f = invalidPermitError := by
      simpa [weth10Aux, invalidPermitErrorSlot] using hget.symm
    subst f
    exact absurd hrev Func.not_run_revWith

/-- The complete recovery auxiliary has the same retained static boundary;
digest preparation is silent before it and the signer/allowance tail is
silent after it. -/
private theorem permitRecover_balanceOwnSilent
    (dp : DeployParams) {sevm : Sevm} {s r : Devm}
    (run : Func.Run ((weth10 dp).main :: weth10Aux) sevm s
      permitRecover r) :
    PermitBalanceOwnSilent sevm s r := by
  change Func.Run ((weth10 dp).main :: weth10Aux) sevm s
    (permitDigest +++ recoverPermitSigner +++ permitSignerFlashGuards) r
    at run
  rcases of_run_prepend permitDigest _ run with ⟨digestPre, hdigest, run⟩
  rcases of_run_prepend recoverPermitSigner _ run with
    ⟨guardsPre, hrecover, hguards⟩
  have hstorDigest : Devm.getStor s = Devm.getStor digestPre :=
    Line.of_inv Devm.getStor (by
      unfold permitDigest pushList
      line_inv) hdigest
  exact ((recoverPermitSigner_balanceOwnSilent hrecover).prepend
      (Stor.Weth10Silent.of_eq
        (congrFun hstorDigest sevm.currentTarget))).append
    (permitSignerFlashGuards_balanceSilent dp hguards)

/-- Both signer guards are storage-silent; a successful path must reach the
tagged approval tail because the two deliberate-error functions cannot return
successfully. -/
private theorem permitSignerFlashGuards_exactRel
    (dp : DeployParams) (ca : Adr)
    {sevm : Sevm} {s r : Devm}
    (h_target : sevm.currentTarget = ca)
    (run : Func.Run ((weth10 dp).main :: weth10Aux) sevm s
      permitSignerFlashGuards r) :
    FlashExactRel dp ca sevm s r := by
  unfold permitSignerFlashGuards at run
  rcases of_run_next run with ⟨s1, hdup, run⟩
  rcases of_run_next run with ⟨s2, hzero, run⟩
  rcases of_run_branch run with
      ⟨s3, hpop1, run⟩ |
      ⟨w1, s3, s4, hnz1, hpop1, hburn1, hinvalid1⟩
  · rcases of_run_prepend (arg 0) _ run with ⟨s4, harg0, run⟩
    rcases of_run_next run with ⟨s5, heq, run⟩
    rcases of_run_next run with ⟨s6, hzero2, run⟩
    rcases of_run_branch run with
        ⟨t, hpop2, happrove⟩ |
        ⟨w2, t0, t, hnz2, hpop2, hburn2, hinvalid2⟩
    · have hstor : Devm.getStor s = Devm.getStor t := by
        calc
          Devm.getStor s = Devm.getStor s1 :=
            Ninst.Hinv.inv (f := Devm.getStor) hdup
          _ = Devm.getStor s2 :=
            Ninst.Hinv.inv (f := Devm.getStor) hzero
          _ = Devm.getStor s3 := PopBurn.Inv.inv hpop1
          _ = Devm.getStor s4 :=
            Line.of_inv Devm.getStor (by line_inv) harg0
          _ = Devm.getStor s5 :=
            Ninst.Hinv.inv (f := Devm.getStor) heq
          _ = Devm.getStor s6 :=
            Ninst.Hinv.inv (f := Devm.getStor) hzero2
          _ = Devm.getStor t := PopBurn.Inv.inv hpop2
      have happroveExact := approvePermit_flashStable dp happrove
      subst ca
      unfold FlashExactRel
      exact happroveExact.trans
        (congrArg (fun st => st.get flashMintedSlot)
          (congrFun hstor sevm.currentTarget)).symm
    · rcases of_run_call hinvalid2 with
        ⟨f, u, hget, hcallBurn, hrev⟩
      have hf : f = invalidPermitError := by
        simpa [weth10Aux, invalidPermitErrorSlot] using hget.symm
      subst f
      exact absurd hrev Func.not_run_revWith
  · rcases of_run_call hinvalid1 with
      ⟨f, u, hget, hcallBurn, hrev⟩
    have hf : f = invalidPermitError := by
      simpa [weth10Aux, invalidPermitErrorSlot] using hget.symm
    subst f
    exact absurd hrev Func.not_run_revWith

/-- Once recovery has established backing, the signer guards and successful
tagged approval tail preserve that postcondition. -/
private theorem permitSignerFlashGuards_backedPost
    (dp : DeployParams) (ca : Adr)
    {sevm : Sevm} {s r : Devm}
    (h_target : sevm.currentTarget = ca)
    (h_post : (backedSpec weth10 dp).Post ca sevm s)
    (run : Func.Run ((weth10 dp).main :: weth10Aux) sevm s
      permitSignerFlashGuards r) :
    (backedSpec weth10 dp).Post ca sevm r := by
  subst ca
  unfold permitSignerFlashGuards at run
  rcases of_run_next run with ⟨s1, hdup, run⟩
  rcases of_run_next run with ⟨s2, hzero, run⟩
  rcases of_run_branch run with
      ⟨s3, hpop1, run⟩ |
      ⟨w1, s3, s4, hnz1, hpop1, hburn1, hinvalid1⟩
  · rcases of_run_prepend (arg 0) _ run with ⟨s4, harg0, run⟩
    rcases of_run_next run with ⟨s5, heq, run⟩
    rcases of_run_next run with ⟨s6, hzero2, run⟩
    rcases of_run_branch run with
        ⟨t, hpop2, happrove⟩ |
        ⟨w2, t0, t, hnz2, hpop2, hburn2, hinvalid2⟩
    · have hstor : Devm.getStor s = Devm.getStor t := by
        calc
          Devm.getStor s = Devm.getStor s1 :=
            Ninst.Hinv.inv (f := Devm.getStor) hdup
          _ = Devm.getStor s2 :=
            Ninst.Hinv.inv (f := Devm.getStor) hzero
          _ = Devm.getStor s3 := PopBurn.Inv.inv hpop1
          _ = Devm.getStor s4 :=
            Line.of_inv Devm.getStor (by line_inv) harg0
          _ = Devm.getStor s5 :=
            Ninst.Hinv.inv (f := Devm.getStor) heq
          _ = Devm.getStor s6 :=
            Ninst.Hinv.inv (f := Devm.getStor) hzero2
          _ = Devm.getStor t := PopBurn.Inv.inv hpop2
      have hbal : Devm.getBal s = Devm.getBal t := by
        calc
          Devm.getBal s = Devm.getBal s1 :=
            Ninst.Hinv.inv (f := Devm.getBal) hdup
          _ = Devm.getBal s2 :=
            Ninst.Hinv.inv (f := Devm.getBal) hzero
          _ = Devm.getBal s3 := PopBurn.Inv.inv hpop1
          _ = Devm.getBal s4 :=
            Line.of_inv Devm.getBal (by line_inv) harg0
          _ = Devm.getBal s5 :=
            Ninst.Hinv.inv (f := Devm.getBal) heq
          _ = Devm.getBal s6 :=
            Ninst.Hinv.inv (f := Devm.getBal) hzero2
          _ = Devm.getBal t := PopBurn.Inv.inv hpop2
      have hpostT := backedPost_of_silent dp sevm.currentTarget h_post
        (Stor.Weth10Silent.of_eq
          (congrFun hstor sevm.currentTarget)) hbal
      have hbalApprove : Devm.getBal t = Devm.getBal r :=
        Func.of_inv Devm.getBal Devm.getBal (by func_inv) happrove
      exact backedPost_of_silent dp sevm.currentTarget hpostT
        (approvePermit_storage_silent dp happrove) hbalApprove
    · rcases of_run_call hinvalid2 with
        ⟨f, u, hget, hcallBurn, hrev⟩
      have hf : f = invalidPermitError := by
        simpa [weth10Aux, invalidPermitErrorSlot] using hget.symm
      subst f
      exact absurd hrev Func.not_run_revWith
  · rcases of_run_call hinvalid1 with
      ⟨f, u, hget, hcallBurn, hrev⟩
    have hf : f = invalidPermitError := by
      simpa [weth10Aux, invalidPermitErrorSlot] using hget.symm
    subst f
    exact absurd hrev Func.not_run_revWith

/-- The whole recovery function preserves the exact counter: digesting is
local, recovery crosses the recursively-checked static subtree, and the only
successful tail write is the disjoint allowance entry. -/
private theorem permitRecover_exactRel
    (dp : DeployParams) (ca : Adr)
    {sevm : Sevm} {s r : Devm}
    (h_target : sevm.currentTarget = ca)
    (ih : FlashExactDepth dp ca sevm.depth)
    (h_code : some (s.getCode ca).toList = Prog.compile (weth10 dp))
    (run : Func.Run ((weth10 dp).main :: weth10Aux) sevm s
      permitRecover r) :
    FlashExactRel dp ca sevm s r := by
  change Func.Run ((weth10 dp).main :: weth10Aux) sevm s
    (permitDigest +++ recoverPermitSigner +++ permitSignerFlashGuards) r at run
  rcases of_run_prepend permitDigest _ run with
    ⟨sd, hdigest, run⟩
  rcases of_run_prepend recoverPermitSigner _ run with
    ⟨sr, hrecover, hguards⟩
  have hstorDigest : Devm.getStor s = Devm.getStor sd :=
    Line.of_inv Devm.getStor (by
      unfold permitDigest pushList
      line_inv) hdigest
  have hcodeDigest : Devm.getCode s = Devm.getCode sd :=
    Line.of_inv Devm.getCode (by
      unfold permitDigest pushList
      line_inv) hdigest
  have hcodeSd : some (sd.getCode ca).toList =
      Prog.compile (weth10 dp) := by
    rw [← hcodeDigest]
    exact h_code
  have hrecoverExact := recoverPermitSigner_exactRel dp ca
    h_target ih hcodeSd hrecover
  have hguardsExact := permitSignerFlashGuards_exactRel dp ca
    h_target hguards
  unfold FlashExactRel at hrecoverExact hguardsExact ⊢
  exact hguardsExact.trans (hrecoverExact.trans
    (congrArg (fun st => st.get flashMintedSlot)
      (congrFun hstorDigest ca)).symm)

/-- The permit recovery auxiliary preserves backing across its local digest,
arbitrary static recovery frame, and successful tagged approval. -/
private theorem permitRecover_backed
    (dp : DeployParams) (ca : Adr)
    {sevm : Sevm} {s r : Devm}
    (h_target : sevm.currentTarget = ca)
    (h_value : sevm.value = 0)
    (h_pre : (backedSpec weth10 dp).Pre ca sevm s)
    (ih : Exec.InvDepth sevm.depth ca (weth10 dp)
      ((backedSpec weth10 dp).PreWf ca) ((backedSpec weth10 dp).Post ca))
    (run : Func.Run ((weth10 dp).main :: weth10Aux) sevm s
      permitRecover r) :
    (backedSpec weth10 dp).Post ca sevm r := by
  change Func.Run ((weth10 dp).main :: weth10Aux) sevm s
    (permitDigest +++ recoverPermitSigner +++ permitSignerFlashGuards) r at run
  rcases of_run_prepend permitDigest _ run with
    ⟨sd, hdigest, run⟩
  rcases of_run_prepend recoverPermitSigner _ run with
    ⟨sr, hrecover, hguards⟩
  have hstorDigest : Devm.getStor s = Devm.getStor sd :=
    Line.of_inv Devm.getStor (by
      unfold permitDigest pushList
      line_inv) hdigest
  have hbalDigest : Devm.getBal s = Devm.getBal sd :=
    Line.of_inv Devm.getBal (by
      unfold permitDigest pushList
      line_inv) hdigest
  have hcodeDigest : Devm.getCode s = Devm.getCode sd :=
    Line.of_inv Devm.getCode (by
      unfold permitDigest pushList
      line_inv) hdigest
  have hpreSd : (backedSpec weth10 dp).Pre ca sevm sd :=
    backedPre_of_silent dp ca h_pre
      (Stor.Weth10Silent.of_eq (congrFun hstorDigest ca))
      hbalDigest (congrFun hcodeDigest ca)
  have hpostRecover := recoverPermitSigner_backed dp ca h_target h_value
    hpreSd ih hrecover
  exact permitSignerFlashGuards_backedPost dp ca h_target
    hpostRecover hguards

private def permitStructFlashPrepare : Line :=
  [pushB256 PERMIT_TYPEHASH] ++ mstoreAt 0 ++
  argCopy 1 0 3 ++ arg 3 ++ mstoreAt 5 ++
  pushList [192, 0] ++ [kec]

private def permitDomainFlashDispatch (dp : DeployParams) : Func :=
  dup 1 ::: pushDeployWord dp.deploymentChainId ::: eq :::
  (swap 0 ::: pop ::: pushDeployWord dp.cachedDomainSeparator :::
    .call permitRecoverSlot) <?>
  (swap 0 ::: calculateDomainSeparator +++ .call permitRecoverSlot)

/-- Both domain-separator branches reach the same recovery auxiliary after a
storage-silent generated prefix. -/
private theorem permitDomainFlashDispatch_balanceOwnSilent
    (dp : DeployParams) {sevm : Sevm} {s r : Devm}
    (run : Func.Run ((weth10 dp).main :: weth10Aux) sevm s
      (permitDomainFlashDispatch dp) r) :
    PermitBalanceOwnSilent sevm s r := by
  unfold permitDomainFlashDispatch at run
  rcases of_run_next run with ⟨s1, q1, run⟩
  rcases of_run_next run with ⟨s2, q2, run⟩
  rcases of_run_next run with ⟨s3, q3, run⟩
  have hstor3 : Devm.getStor s = Devm.getStor s3 := by
    calc
      Devm.getStor s = Devm.getStor s1 :=
        Ninst.Hinv.inv (f := Devm.getStor) q1
      _ = Devm.getStor s2 := by
        unfold pushDeployWord at q2
        exact Ninst.Hinv.inv (f := Devm.getStor) q2
      _ = Devm.getStor s3 :=
        Ninst.Hinv.inv (f := Devm.getStor) q3
  rcases of_run_branch run with
      ⟨branchPre, hpop, hfork⟩ |
      ⟨w, branchPre, branchBurn, hnz, hpop, hburn, hcached⟩
  · rcases of_run_next hfork with ⟨s4, q4, hfork⟩
    rcases of_run_prepend calculateDomainSeparator _ hfork with
      ⟨s5, hdomain, hcall⟩
    rcases of_run_call hcall with
      ⟨f, recoverPre, hget, hcallBurn, hrecover⟩
    have hf : f = permitRecover := by
      simpa [weth10Aux, permitRecoverSlot] using hget.symm
    subst f
    have hstor : Devm.getStor s = Devm.getStor recoverPre := by
      calc
        Devm.getStor s = Devm.getStor s3 := hstor3
        _ = Devm.getStor branchPre := PopBurn.Inv.inv hpop
        _ = Devm.getStor s4 :=
          Ninst.Hinv.inv (f := Devm.getStor) q4
        _ = Devm.getStor s5 :=
          Line.of_inv Devm.getStor (by
            unfold calculateDomainSeparator pushList
            line_inv) hdomain
        _ = Devm.getStor recoverPre := Burn.Inv.inv hcallBurn
    exact (permitRecover_balanceOwnSilent dp hrecover).prepend
      (Stor.Weth10Silent.of_eq
        (congrFun hstor sevm.currentTarget))
  · rcases of_run_next hcached with ⟨s4, q4, hcached⟩
    rcases of_run_next hcached with ⟨s5, q5, hcached⟩
    rcases of_run_next hcached with ⟨s6, q6, hcall⟩
    rcases of_run_call hcall with
      ⟨f, recoverPre, hget, hcallBurn, hrecover⟩
    have hf : f = permitRecover := by
      simpa [weth10Aux, permitRecoverSlot] using hget.symm
    subst f
    have hstor : Devm.getStor s = Devm.getStor recoverPre := by
      calc
        Devm.getStor s = Devm.getStor s3 := hstor3
        _ = Devm.getStor branchPre := PopBurn.Inv.inv hpop
        _ = Devm.getStor branchBurn := Burn.Inv.inv hburn
        _ = Devm.getStor s4 :=
          Ninst.Hinv.inv (f := Devm.getStor) q4
        _ = Devm.getStor s5 :=
          Ninst.Hinv.inv (f := Devm.getStor) q5
        _ = Devm.getStor s6 := by
          unfold pushDeployWord at q6
          exact Ninst.Hinv.inv (f := Devm.getStor) q6
        _ = Devm.getStor recoverPre := Burn.Inv.inv hcallBurn
    exact (permitRecover_balanceOwnSilent dp hrecover).prepend
      (Stor.Weth10Silent.of_eq
        (congrFun hstor sevm.currentTarget))

/-- Cached and recomputed EIP-712 domain selection are storage-silent before
the fixed recovery auxiliary call. -/
private theorem permitDomainFlashDispatch_exactRel
    (dp : DeployParams) (ca : Adr)
    {sevm : Sevm} {s r : Devm}
    (h_target : sevm.currentTarget = ca)
    (ih : FlashExactDepth dp ca sevm.depth)
    (h_code : some (s.getCode ca).toList = Prog.compile (weth10 dp))
    (run : Func.Run ((weth10 dp).main :: weth10Aux) sevm s
      (permitDomainFlashDispatch dp) r) :
    FlashExactRel dp ca sevm s r := by
  unfold permitDomainFlashDispatch at run
  rcases of_run_next run with ⟨s1, q1, run⟩
  rcases of_run_next run with ⟨s2, q2, run⟩
  rcases of_run_next run with ⟨s3, q3, run⟩
  have hstor3 : Devm.getStor s = Devm.getStor s3 := by
    calc
      Devm.getStor s = Devm.getStor s1 :=
        Ninst.Hinv.inv (f := Devm.getStor) q1
      _ = Devm.getStor s2 := by
        unfold pushDeployWord at q2
        exact Ninst.Hinv.inv (f := Devm.getStor) q2
      _ = Devm.getStor s3 :=
        Ninst.Hinv.inv (f := Devm.getStor) q3
  have hcode3 : Devm.getCode s = Devm.getCode s3 := by
    funext a
    calc
      Devm.getCode s a = Devm.getCode s1 a :=
        congrFun (Ninst.Hinv.inv (f := Devm.getCode) q1) a
      _ = Devm.getCode s2 a := by
        unfold pushDeployWord at q2
        exact congrFun (Ninst.Hinv.inv (f := Devm.getCode) q2) a
      _ = Devm.getCode s3 a :=
        congrFun (Ninst.Hinv.inv (f := Devm.getCode) q3) a
  rcases of_run_branch run with
      ⟨sp, hpop, hfork⟩ |
      ⟨w, sp, sb, hnz, hpop, hburn, hcached⟩
  · rcases of_run_next hfork with ⟨s4, q4, hfork⟩
    rcases of_run_prepend calculateDomainSeparator _ hfork with
      ⟨s5, hdomain, hcall⟩
    rcases of_run_call hcall with
      ⟨f, t, hget, hcallBurn, hrecover⟩
    have hf : f = permitRecover := by
      simpa [weth10Aux, permitRecoverSlot] using hget.symm
    subst f
    have hstor : Devm.getStor s = Devm.getStor t := by
      calc
        Devm.getStor s = Devm.getStor s3 := hstor3
        _ = Devm.getStor sp := PopBurn.Inv.inv hpop
        _ = Devm.getStor s4 :=
          Ninst.Hinv.inv (f := Devm.getStor) q4
        _ = Devm.getStor s5 :=
          Line.of_inv Devm.getStor (by
            unfold calculateDomainSeparator pushList
            line_inv) hdomain
        _ = Devm.getStor t := Burn.Inv.inv hcallBurn
    have hcode : Devm.getCode s = Devm.getCode t := by
      funext a
      calc
        Devm.getCode s a = Devm.getCode s3 a := congrFun hcode3 a
        _ = Devm.getCode sp a := getCode_eq_of_state_eq hpop.state a
        _ = Devm.getCode s4 a :=
          congrFun (Ninst.Hinv.inv (f := Devm.getCode) q4) a
        _ = Devm.getCode s5 a :=
          congrFun (Line.of_inv Devm.getCode (by
            unfold calculateDomainSeparator pushList
            line_inv) hdomain) a
        _ = Devm.getCode t a :=
          getCode_eq_of_state_eq hcallBurn.state a
    have hcodeT : some (t.getCode ca).toList =
        Prog.compile (weth10 dp) := by
      rw [← hcode]
      exact h_code
    have hexact := permitRecover_exactRel dp ca
      h_target ih hcodeT hrecover
    unfold FlashExactRel at hexact ⊢
    exact hexact.trans
      (congrArg (fun st => st.get flashMintedSlot)
        (congrFun hstor ca)).symm
  · rcases of_run_next hcached with ⟨s4, q4, hcached⟩
    rcases of_run_next hcached with ⟨s5, q5, hcached⟩
    rcases of_run_next hcached with ⟨s6, q6, hcall⟩
    rcases of_run_call hcall with
      ⟨f, t, hget, hcallBurn, hrecover⟩
    have hf : f = permitRecover := by
      simpa [weth10Aux, permitRecoverSlot] using hget.symm
    subst f
    have hstor : Devm.getStor s = Devm.getStor t := by
      calc
        Devm.getStor s = Devm.getStor s3 := hstor3
        _ = Devm.getStor sp := PopBurn.Inv.inv hpop
        _ = Devm.getStor sb := Burn.Inv.inv hburn
        _ = Devm.getStor s4 :=
          Ninst.Hinv.inv (f := Devm.getStor) q4
        _ = Devm.getStor s5 :=
          Ninst.Hinv.inv (f := Devm.getStor) q5
        _ = Devm.getStor s6 := by
          unfold pushDeployWord at q6
          exact Ninst.Hinv.inv (f := Devm.getStor) q6
        _ = Devm.getStor t := Burn.Inv.inv hcallBurn
    have hcode : Devm.getCode s = Devm.getCode t := by
      funext a
      calc
        Devm.getCode s a = Devm.getCode s3 a := congrFun hcode3 a
        _ = Devm.getCode sp a := getCode_eq_of_state_eq hpop.state a
        _ = Devm.getCode sb a := getCode_eq_of_state_eq hburn.state a
        _ = Devm.getCode s4 a :=
          congrFun (Ninst.Hinv.inv (f := Devm.getCode) q4) a
        _ = Devm.getCode s5 a :=
          congrFun (Ninst.Hinv.inv (f := Devm.getCode) q5) a
        _ = Devm.getCode s6 a := by
          unfold pushDeployWord at q6
          exact congrFun (Ninst.Hinv.inv (f := Devm.getCode) q6) a
        _ = Devm.getCode t a :=
          getCode_eq_of_state_eq hcallBurn.state a
    have hcodeT : some (t.getCode ca).toList =
        Prog.compile (weth10 dp) := by
      rw [← hcode]
      exact h_code
    have hexact := permitRecover_exactRel dp ca
      h_target ih hcodeT hrecover
    unfold FlashExactRel at hexact ⊢
    exact hexact.trans
      (congrArg (fun st => st.get flashMintedSlot)
        (congrFun hstor ca)).symm

/-- Both cached and recomputed domain-separator paths are world-silent before
the same backing-preserving recovery auxiliary. -/
private theorem permitDomainFlashDispatch_backed
    (dp : DeployParams) (ca : Adr)
    {sevm : Sevm} {s r : Devm}
    (h_target : sevm.currentTarget = ca)
    (h_value : sevm.value = 0)
    (h_pre : (backedSpec weth10 dp).Pre ca sevm s)
    (ih : Exec.InvDepth sevm.depth ca (weth10 dp)
      ((backedSpec weth10 dp).PreWf ca) ((backedSpec weth10 dp).Post ca))
    (run : Func.Run ((weth10 dp).main :: weth10Aux) sevm s
      (permitDomainFlashDispatch dp) r) :
    (backedSpec weth10 dp).Post ca sevm r := by
  unfold permitDomainFlashDispatch at run
  rcases of_run_next run with ⟨s1, q1, run⟩
  rcases of_run_next run with ⟨s2, q2, run⟩
  rcases of_run_next run with ⟨s3, q3, run⟩
  have hstor3 : Devm.getStor s = Devm.getStor s3 := by
    calc
      Devm.getStor s = Devm.getStor s1 :=
        Ninst.Hinv.inv (f := Devm.getStor) q1
      _ = Devm.getStor s2 := by
        unfold pushDeployWord at q2
        exact Ninst.Hinv.inv (f := Devm.getStor) q2
      _ = Devm.getStor s3 :=
        Ninst.Hinv.inv (f := Devm.getStor) q3
  have hbal3 : Devm.getBal s = Devm.getBal s3 := by
    calc
      Devm.getBal s = Devm.getBal s1 :=
        Ninst.Hinv.inv (f := Devm.getBal) q1
      _ = Devm.getBal s2 := by
        unfold pushDeployWord at q2
        exact Ninst.Hinv.inv (f := Devm.getBal) q2
      _ = Devm.getBal s3 :=
        Ninst.Hinv.inv (f := Devm.getBal) q3
  have hcode3 : Devm.getCode s = Devm.getCode s3 := by
    funext a
    calc
      Devm.getCode s a = Devm.getCode s1 a :=
        congrFun (Ninst.Hinv.inv (f := Devm.getCode) q1) a
      _ = Devm.getCode s2 a := by
        unfold pushDeployWord at q2
        exact congrFun (Ninst.Hinv.inv (f := Devm.getCode) q2) a
      _ = Devm.getCode s3 a :=
        congrFun (Ninst.Hinv.inv (f := Devm.getCode) q3) a
  rcases of_run_branch run with
      ⟨sp, hpop, hfork⟩ |
      ⟨w, sp, sb, hnz, hpop, hburn, hcached⟩
  · rcases of_run_next hfork with ⟨s4, q4, hfork⟩
    rcases of_run_prepend calculateDomainSeparator _ hfork with
      ⟨s5, hdomain, hcall⟩
    rcases of_run_call hcall with
      ⟨f, t, hget, hcallBurn, hrecover⟩
    have hf : f = permitRecover := by
      simpa [weth10Aux, permitRecoverSlot] using hget.symm
    subst f
    have hstor : Devm.getStor s = Devm.getStor t := by
      calc
        Devm.getStor s = Devm.getStor s3 := hstor3
        _ = Devm.getStor sp := PopBurn.Inv.inv hpop
        _ = Devm.getStor s4 :=
          Ninst.Hinv.inv (f := Devm.getStor) q4
        _ = Devm.getStor s5 :=
          Line.of_inv Devm.getStor (by
            unfold calculateDomainSeparator pushList
            line_inv) hdomain
        _ = Devm.getStor t := Burn.Inv.inv hcallBurn
    have hbal : Devm.getBal s = Devm.getBal t := by
      calc
        Devm.getBal s = Devm.getBal s3 := hbal3
        _ = Devm.getBal sp := PopBurn.Inv.inv hpop
        _ = Devm.getBal s4 :=
          Ninst.Hinv.inv (f := Devm.getBal) q4
        _ = Devm.getBal s5 :=
          Line.of_inv Devm.getBal (by
            unfold calculateDomainSeparator pushList
            line_inv) hdomain
        _ = Devm.getBal t := Burn.Inv.inv hcallBurn
    have hcode : Devm.getCode s = Devm.getCode t := by
      funext a
      calc
        Devm.getCode s a = Devm.getCode s3 a := congrFun hcode3 a
        _ = Devm.getCode sp a := getCode_eq_of_state_eq hpop.state a
        _ = Devm.getCode s4 a :=
          congrFun (Ninst.Hinv.inv (f := Devm.getCode) q4) a
        _ = Devm.getCode s5 a :=
          congrFun (Line.of_inv Devm.getCode (by
            unfold calculateDomainSeparator pushList
            line_inv) hdomain) a
        _ = Devm.getCode t a :=
          getCode_eq_of_state_eq hcallBurn.state a
    have hpreT : (backedSpec weth10 dp).Pre ca sevm t :=
      backedPre_of_silent dp ca h_pre
        (Stor.Weth10Silent.of_eq (congrFun hstor ca))
        hbal (congrFun hcode ca)
    exact permitRecover_backed dp ca h_target h_value hpreT ih hrecover
  · rcases of_run_next hcached with ⟨s4, q4, hcached⟩
    rcases of_run_next hcached with ⟨s5, q5, hcached⟩
    rcases of_run_next hcached with ⟨s6, q6, hcall⟩
    rcases of_run_call hcall with
      ⟨f, t, hget, hcallBurn, hrecover⟩
    have hf : f = permitRecover := by
      simpa [weth10Aux, permitRecoverSlot] using hget.symm
    subst f
    have hstor : Devm.getStor s = Devm.getStor t := by
      calc
        Devm.getStor s = Devm.getStor s3 := hstor3
        _ = Devm.getStor sp := PopBurn.Inv.inv hpop
        _ = Devm.getStor sb := Burn.Inv.inv hburn
        _ = Devm.getStor s4 :=
          Ninst.Hinv.inv (f := Devm.getStor) q4
        _ = Devm.getStor s5 :=
          Ninst.Hinv.inv (f := Devm.getStor) q5
        _ = Devm.getStor s6 := by
          unfold pushDeployWord at q6
          exact Ninst.Hinv.inv (f := Devm.getStor) q6
        _ = Devm.getStor t := Burn.Inv.inv hcallBurn
    have hbal : Devm.getBal s = Devm.getBal t := by
      calc
        Devm.getBal s = Devm.getBal s3 := hbal3
        _ = Devm.getBal sp := PopBurn.Inv.inv hpop
        _ = Devm.getBal sb := Burn.Inv.inv hburn
        _ = Devm.getBal s4 :=
          Ninst.Hinv.inv (f := Devm.getBal) q4
        _ = Devm.getBal s5 :=
          Ninst.Hinv.inv (f := Devm.getBal) q5
        _ = Devm.getBal s6 := by
          unfold pushDeployWord at q6
          exact Ninst.Hinv.inv (f := Devm.getBal) q6
        _ = Devm.getBal t := Burn.Inv.inv hcallBurn
    have hcode : Devm.getCode s = Devm.getCode t := by
      funext a
      calc
        Devm.getCode s a = Devm.getCode s3 a := congrFun hcode3 a
        _ = Devm.getCode sp a := getCode_eq_of_state_eq hpop.state a
        _ = Devm.getCode sb a := getCode_eq_of_state_eq hburn.state a
        _ = Devm.getCode s4 a :=
          congrFun (Ninst.Hinv.inv (f := Devm.getCode) q4) a
        _ = Devm.getCode s5 a :=
          congrFun (Ninst.Hinv.inv (f := Devm.getCode) q5) a
        _ = Devm.getCode s6 a := by
          unfold pushDeployWord at q6
          exact congrFun (Ninst.Hinv.inv (f := Devm.getCode) q6) a
        _ = Devm.getCode t a :=
          getCode_eq_of_state_eq hcallBurn.state a
    have hpreT : (backedSpec weth10 dp).Pre ca sevm t :=
      backedPre_of_silent dp ca h_pre
        (Stor.Weth10Silent.of_eq (congrFun hstor ca))
        hbal (congrFun hcode ca)
    exact permitRecover_backed dp ca h_target h_value hpreT ih hrecover

private def permitAfterDeadlineFlash (dp : DeployParams) : Func :=
  permitNonceFlashPrefix +++ permitStructFlashPrepare +++
    permitDomainFlashDispatch dp

/-- The live permit prefix performs only the normalized tagged nonce write
before the retained recovery boundary. -/
private theorem permitAfterDeadline_balanceOwnSilent
    (dp : DeployParams) {sevm : Sevm} {s r : Devm}
    (run : Func.Run ((weth10 dp).main :: weth10Aux) sevm s
      (permitAfterDeadlineFlash dp) r) :
    PermitBalanceOwnSilent sevm s r := by
  unfold permitAfterDeadlineFlash at run
  rcases of_run_prepend permitNonceFlashPrefix _ run with
    ⟨noncePost, hnonce, run⟩
  rcases of_run_prepend permitStructFlashPrepare _ run with
    ⟨domainPre, hstruct, hdomain⟩
  have hstorStruct : Devm.getStor noncePost = Devm.getStor domainPre :=
    Line.of_inv Devm.getStor (by
      unfold permitStructFlashPrepare argCopy cdc pushList
      line_inv) hstruct
  exact ((permitDomainFlashDispatch_balanceOwnSilent dp hdomain).prepend
      (Stor.Weth10Silent.of_eq
        (congrFun hstorStruct sevm.currentTarget))).prepend
    (permitNonceFlashPrefix_silent hnonce)

private theorem permitAfterDeadline_exactRel
    (dp : DeployParams) (ca : Adr)
    {sevm : Sevm} {s r : Devm}
    (h_target : sevm.currentTarget = ca)
    (ih : FlashExactDepth dp ca sevm.depth)
    (h_code : some (s.getCode ca).toList = Prog.compile (weth10 dp))
    (run : Func.Run ((weth10 dp).main :: weth10Aux) sevm s
      (permitAfterDeadlineFlash dp) r) :
    FlashExactRel dp ca sevm s r := by
  unfold permitAfterDeadlineFlash at run
  rcases of_run_prepend permitNonceFlashPrefix _ run with
    ⟨sn, hnonce, run⟩
  rcases of_run_prepend permitStructFlashPrepare _ run with
    ⟨ss, hstruct, hdomain⟩
  have hnonceExact := permitNonceFlashPrefix_exactRel dp ca
    h_target hnonce
  have hstorStruct : Devm.getStor sn = Devm.getStor ss :=
    Line.of_inv Devm.getStor (by
      unfold permitStructFlashPrepare argCopy cdc pushList
      line_inv) hstruct
  have hcodeStruct : Devm.getCode sn = Devm.getCode ss :=
    Line.of_inv Devm.getCode (by
      unfold permitStructFlashPrepare argCopy cdc pushList
      line_inv) hstruct
  have hcodeNonce : Devm.getCode s = Devm.getCode sn :=
    Line.of_inv Devm.getCode (by
      unfold permitNonceFlashPrefix addressArg normalizeAddress
        pushAddressMask tagNonceKey mstoreAt
      line_inv) hnonce
  have hcodeSs : some (ss.getCode ca).toList =
      Prog.compile (weth10 dp) := by
    rw [← hcodeStruct, ← hcodeNonce]
    exact h_code
  have hdomainExact := permitDomainFlashDispatch_exactRel dp ca
    h_target ih hcodeSs hdomain
  unfold FlashExactRel at hnonceExact hdomainExact ⊢
  exact hdomainExact.trans
    ((congrArg (fun st => st.get flashMintedSlot)
      (congrFun hstorStruct ca)).symm.trans hnonceExact)

/-- The normalized nonce write and typed-data scratch preparation preserve
backing before domain selection enters the common recovery path. -/
private theorem permitAfterDeadline_backed
    (dp : DeployParams) (ca : Adr)
    {sevm : Sevm} {s r : Devm}
    (h_target : sevm.currentTarget = ca)
    (h_value : sevm.value = 0)
    (h_pre : (backedSpec weth10 dp).Pre ca sevm s)
    (ih : Exec.InvDepth sevm.depth ca (weth10 dp)
      ((backedSpec weth10 dp).PreWf ca) ((backedSpec weth10 dp).Post ca))
    (run : Func.Run ((weth10 dp).main :: weth10Aux) sevm s
      (permitAfterDeadlineFlash dp) r) :
    (backedSpec weth10 dp).Post ca sevm r := by
  unfold permitAfterDeadlineFlash at run
  rcases of_run_prepend permitNonceFlashPrefix _ run with
    ⟨sn, hnonce, run⟩
  rcases of_run_prepend permitStructFlashPrepare _ run with
    ⟨ss, hstruct, hdomain⟩
  have hnonceSilent := permitNonceFlashPrefix_silent hnonce
  have hbalNonce : Devm.getBal s = Devm.getBal sn :=
    Line.of_inv Devm.getBal (by
      unfold permitNonceFlashPrefix addressArg normalizeAddress
        pushAddressMask tagNonceKey mstoreAt
      line_inv) hnonce
  have hcodeNonce : Devm.getCode s = Devm.getCode sn :=
    Line.of_inv Devm.getCode (by
      unfold permitNonceFlashPrefix addressArg normalizeAddress
        pushAddressMask tagNonceKey mstoreAt
      line_inv) hnonce
  have hpreSn : (backedSpec weth10 dp).Pre ca sevm sn :=
    backedPre_of_silent dp ca h_pre (h_target ▸ hnonceSilent)
      hbalNonce (congrFun hcodeNonce ca)
  have hstorStruct : Devm.getStor sn = Devm.getStor ss :=
    Line.of_inv Devm.getStor (by
      unfold permitStructFlashPrepare argCopy cdc pushList
      line_inv) hstruct
  have hbalStruct : Devm.getBal sn = Devm.getBal ss :=
    Line.of_inv Devm.getBal (by
      unfold permitStructFlashPrepare argCopy cdc pushList
      line_inv) hstruct
  have hcodeStruct : Devm.getCode sn = Devm.getCode ss :=
    Line.of_inv Devm.getCode (by
      unfold permitStructFlashPrepare argCopy cdc pushList
      line_inv) hstruct
  have hpreSs : (backedSpec weth10 dp).Pre ca sevm ss :=
    backedPre_of_silent dp ca hpreSn
      (Stor.Weth10Silent.of_eq (congrFun hstorStruct ca))
      hbalStruct (congrFun hcodeStruct ca)
  exact permitDomainFlashDispatch_backed dp ca h_target h_value hpreSs ih
    hdomain

/-- Successful permit execution must take the live deadline arm; its guard is
storage-silent before the exact generated own-balance boundary. -/
private theorem permitBody_balanceOwnSilent
    (dp : DeployParams) {sevm : Sevm} {s r : Devm}
    (run : Func.Run ((weth10 dp).main :: weth10Aux) sevm s
      (permit dp) r) :
    PermitBalanceOwnSilent sevm s r := by
  change Func.Run ((weth10 dp).main :: weth10Aux) sevm s
    (arg 3 +++ [timestamp, gt] +++
      ((.call expiredPermitErrorSlot) <?>
        permitAfterDeadlineFlash dp)) r at run
  rcases of_run_prepend (arg 3 ++ [timestamp, gt]) _ run with
    ⟨guardPost, hguard, hbranch⟩
  have hstorGuard : Devm.getStor s = Devm.getStor guardPost :=
    Line.of_inv Devm.getStor (by line_inv) hguard
  rcases of_run_branch hbranch with
      ⟨livePre, hpop, hlive⟩ |
      ⟨w, errorPre, errorCallPre, hnz, hpop, hburn, hexpired⟩
  · have hstorLive : Devm.getStor s = Devm.getStor livePre :=
      hstorGuard.trans (PopBurn.Inv.inv hpop)
    exact (permitAfterDeadline_balanceOwnSilent dp hlive).prepend
      (Stor.Weth10Silent.of_eq
        (congrFun hstorLive sevm.currentTarget))
  · rcases of_run_call hexpired with
      ⟨f, u, hget, hcallBurn, hrev⟩
    have hf : f = expiredPermitError := by
      simpa [weth10Aux, expiredPermitErrorSlot] using hget.symm
    subst f
    exact absurd hrev Func.not_run_revWith

private theorem permitBody_exactRelFuncSound
    (dp : DeployParams) (ca : Adr) :
    ExactRelFuncSound dp ca (permit dp) := by
  intro sevm s r h_target h_code ih run
  change Func.Run ((weth10 dp).main :: weth10Aux) sevm s
    (arg 3 +++ [timestamp, gt] +++
      ((.call expiredPermitErrorSlot) <?>
        permitAfterDeadlineFlash dp)) r at run
  rcases of_run_prepend (arg 3 ++ [timestamp, gt]) _ run with
    ⟨sg, hguard, hbranch⟩
  have hstorGuard : Devm.getStor s = Devm.getStor sg :=
    Line.of_inv Devm.getStor (by line_inv) hguard
  have hcodeGuard : Devm.getCode s = Devm.getCode sg :=
    Line.of_inv Devm.getCode (by line_inv) hguard
  rcases of_run_branch hbranch with
      ⟨mid, hpop, hlive⟩ |
      ⟨w, mid0, mid, hnz, hpop, hburn, hexpired⟩
  · have hstorMid : Devm.getStor s = Devm.getStor mid :=
      hstorGuard.trans (PopBurn.Inv.inv hpop)
    have hcodeMid : Devm.getCode s = Devm.getCode mid := by
      funext a
      exact (congrFun hcodeGuard a).trans
        (getCode_eq_of_state_eq hpop.state a)
    have hcodeMid' : some (mid.getCode ca).toList =
        Prog.compile (weth10 dp) := by
      rw [← hcodeMid]
      exact h_code
    have hexact := permitAfterDeadline_exactRel dp ca
      h_target ih hcodeMid' hlive
    unfold FlashExactRel at hexact ⊢
    exact hexact.trans
      (congrArg (fun st => st.get flashMintedSlot)
        (congrFun hstorMid ca)).symm
  · rcases of_run_call hexpired with
      ⟨f, u, hget, hcallBurn, hrev⟩
    have hf : f = expiredPermitError := by
      simpa [weth10Aux, expiredPermitErrorSlot] using hget.symm
    subst f
    exact absurd hrev Func.not_run_revWith

private theorem permitBody_backed
    (dp : DeployParams) (ca : Adr)
    {sevm : Sevm} {s r : Devm}
    (h_target : sevm.currentTarget = ca)
    (h_value : sevm.value = 0)
    (h_pre : (backedSpec weth10 dp).Pre ca sevm s)
    (ih : Exec.InvDepth sevm.depth ca (weth10 dp)
      ((backedSpec weth10 dp).PreWf ca) ((backedSpec weth10 dp).Post ca))
    (run : Func.Run ((weth10 dp).main :: weth10Aux) sevm s
      (permit dp) r) :
    (backedSpec weth10 dp).Post ca sevm r := by
  change Func.Run ((weth10 dp).main :: weth10Aux) sevm s
    (arg 3 +++ [timestamp, gt] +++
      ((.call expiredPermitErrorSlot) <?>
        permitAfterDeadlineFlash dp)) r at run
  rcases of_run_prepend (arg 3 ++ [timestamp, gt]) _ run with
    ⟨sg, hguard, hbranch⟩
  have hstorGuard : Devm.getStor s = Devm.getStor sg :=
    Line.of_inv Devm.getStor (by line_inv) hguard
  have hbalGuard : Devm.getBal s = Devm.getBal sg :=
    Line.of_inv Devm.getBal (by line_inv) hguard
  have hcodeGuard : Devm.getCode s = Devm.getCode sg :=
    Line.of_inv Devm.getCode (by line_inv) hguard
  rcases of_run_branch hbranch with
      ⟨mid, hpop, hlive⟩ |
      ⟨w, mid0, mid, hnz, hpop, hburn, hexpired⟩
  · have hstorMid : Devm.getStor s = Devm.getStor mid :=
      hstorGuard.trans (PopBurn.Inv.inv hpop)
    have hbalMid : Devm.getBal s = Devm.getBal mid :=
      hbalGuard.trans (PopBurn.Inv.inv hpop)
    have hcodeMid : Devm.getCode s = Devm.getCode mid := by
      funext a
      exact (congrFun hcodeGuard a).trans
        (getCode_eq_of_state_eq hpop.state a)
    have hpreMid : (backedSpec weth10 dp).Pre ca sevm mid :=
      backedPre_of_silent dp ca h_pre
        (Stor.Weth10Silent.of_eq (congrFun hstorMid ca))
        hbalMid (congrFun hcodeMid ca)
    exact permitAfterDeadline_backed dp ca h_target h_value hpreMid ih hlive
  · rcases of_run_call hexpired with
      ⟨f, u, hget, hcallBurn, hrev⟩
    have hf : f = expiredPermitError := by
      simpa [weth10Aux, expiredPermitErrorSlot] using hget.symm
    subst f
    exact absurd hrev Func.not_run_revWith

/-- Exact generated-program proof that public `permit` has no own
balance-region write.  The only recursive machine step remains the concrete
retained `STATICCALL` gap of `PermitBalanceOwnSilent`. -/
theorem permit_balanceOwnSilent
    (dp : DeployParams) {sevm : Sevm} {s r : Devm}
    (run : Func.Run ((weth10 dp).main :: weth10Aux) sevm s
      (nonpayable (permit dp)) r) :
    PermitBalanceOwnSilent sevm s r := by
  rcases run_body_of_run_nonpayable run with
    ⟨bodyPre, _, hstate, hbody⟩
  exact (permitBody_balanceOwnSilent dp hbody).prepend
    (Stor.Weth10Silent.of_eq
      (getStor_eq_of_state_eq hstate sevm.currentTarget))

/-- Short public spelling for the generated permit own-write theorem. -/
theorem permit_balanceSilent
    (dp : DeployParams) {sevm : Sevm} {s r : Devm}
    (run : Func.Run ((weth10 dp).main :: weth10Aux) sevm s
      (nonpayable (permit dp)) r) :
    PermitBalanceOwnSilent sevm s r :=
  permit_balanceOwnSilent dp run

/-- Unconditional exact flash-counter preservation for the normalized public
`permit` selector, including arbitrary delegated/static recovery subtrees. -/
theorem permit_exactRelFuncSound
    (dp : DeployParams) (ca : Adr) :
    ExactRelFuncSound dp ca (nonpayable (permit dp)) := by
  intro sevm s r h_target h_code ih run
  rcases run_body_of_run_nonpayable run with
    ⟨mid, _, h_state, hrun⟩
  have h_code_mid : some (mid.getCode ca).toList =
      Prog.compile (weth10 dp) := by
    rw [← h_code]
    congr 2
    exact getCode_eq_of_state_eq h_state.symm ca
  have h_exact := permitBody_exactRelFuncSound dp ca
    h_target h_code_mid ih hrun
  unfold FlashExactRel at h_exact ⊢
  exact h_exact.trans (congrArg
    (fun st => (st.get ca).stor.get flashMintedSlot) h_state.symm)

/-- Blanc's nonpayable `permit` selector preserves the frozen backing
invariant, including arbitrary delegated/static recovery subtrees. -/
theorem backedSpec_permit_funcSound
    (dp : DeployParams) (ca : Adr) :
    (backedSpec weth10 dp).FuncSoundNoMem ca weth10Aux
      (nonpayable (permit dp)) := by
  intro sevm s r h_target h_pre ih run
  rcases run_body_of_run_nonpayable run with
    ⟨mid, h_value, h_state, hrun⟩
  have hpreMid : (backedSpec weth10 dp).Pre ca sevm mid :=
    h_pre.state_eq h_state.symm
  exact permitBody_backed dp ca h_target h_value hpreMid ih hrun

/-- An already flash-stable leaf satisfies the exact relational interface. -/
theorem ExactRelFuncSound.of_stable
    (dp : DeployParams) (ca : Adr) {f : Func}
    (hstable : FlashStable dp f) :
    ExactRelFuncSound dp ca f := by
  intro sevm s r h_target h_code ih run
  unfold FlashExactRel
  rw [← h_target]
  exact hstable run

/-- Exact relational preservation lifts through WETH10's nonpayable entry
wrapper without changing the recursive-depth hypothesis. -/
theorem ExactRelFuncSound.nonpayable
    (dp : DeployParams) (ca : Adr) {body : Func}
    (hbody : ExactRelFuncSound dp ca body) :
    ExactRelFuncSound dp ca (nonpayable body) := by
  intro sevm s r h_target h_code ih run
  rcases run_body_of_run_nonpayable run with
    ⟨mid, _, h_state, hrun⟩
  have h_code_mid :
      some (mid.getCode ca).toList = Prog.compile (weth10 dp) := by
    rw [← h_code]
    congr 2
    exact getCode_eq_of_state_eq h_state.symm ca
  have h_exact := hbody h_target h_code_mid ih hrun
  unfold FlashExactRel at h_exact ⊢
  exact h_exact.trans (congrArg
    (fun st => (st.get ca).stor.get flashMintedSlot) h_state.symm)

/-- Generated-dispatch decomposition for exact flash-counter preservation. -/
theorem flashExactPost_of_run_dispatch
    (dp : DeployParams) (ca : Adr)
    (h_funcs : ∀ p ∈ weth10Funcs dp,
      ExactRelFuncSound dp ca p.2)
    (h_fall : ExactRelFuncSound dp ca Func.rev)
    {flash : B256} {sevm : Sevm} {s r : Devm}
    (h_target : sevm.currentTarget = ca)
    (h_pre : (flashExactSpec dp flash).Pre ca sevm s)
    (ih : FlashExactDepth dp ca sevm.depth)
    (run : Func.Run ((weth10 dp).main :: weth10Aux) sevm s
      (dispatchWith fallbackSlot (weth10Tree dp)) r) :
    (flashExactSpec dp flash).Post ca sevm r := by
  apply
    (@dispatchWith_inv
      ((weth10 dp).main :: weth10Aux) fallbackSlot Func.rev
      (fun e s =>
        e.currentTarget = ca ∧
        (flashExactSpec dp flash).Pre ca e s ∧
        FlashExactDepth dp ca e.depth)
      (fun e r => (flashExactSpec dp flash).Post ca e r)
      ?_ ?_ ?_ ?_ (weth10Tree dp) ?_
      sevm s r ⟨h_target, h_pre, ih⟩ run)
  · intro e s0 x w s' s'' ⟨h_ct, hp, hih⟩ hline hpop
    refine ⟨h_ct, ?_, hih⟩
    have h_state : s0.state = s'.state :=
      Line.of_inv Devm.state (by line_inv) hline
    exact hp.state_eq (hpop.state.symm.trans h_state.symm)
  · intro e s0 x w s' s'' ⟨h_ct, hp, hih⟩ hline hpop
    refine ⟨h_ct, ?_, hih⟩
    have h_state : s0.state = s'.state :=
      Line.of_inv Devm.state (by line_inv) hline
    exact hp.state_eq (hpop.state.symm.trans h_state.symm)
  · simp [weth10, weth10Aux, fallbackSlot]
  · intro e s0 s' r0 ⟨h_ct, hp, hih⟩ hburn hrun
    have hpre := hp.state_eq hburn.state.symm
    exact (flashExactSpecsRel_of_rel dp ca
      (h_fall h_ct hpre.code hih hrun)) flash hpre
  · intro e s0 r0 wf h_mem ⟨h_ct, hp, hih⟩ hrun
    have hrel := h_funcs wf
      (DispatchTree.mem_of_mem_ofSorted
        (List.cons_ne_nil _ _) h_mem)
      h_ct hp.code hih hrun
    exact (flashExactSpecsRel_of_rel dp ca hrel) flash hp

/-- Receive-aware WETH10 ingress for the quantified exact-counter relation. -/
theorem flashExactSpecsRel_of_prog_run
    (dp : DeployParams) (ca : Adr)
    (h_funcs : ∀ p ∈ weth10Funcs dp,
      ExactRelFuncSound dp ca p.2)
    (h_receive : ExactRelFuncSound dp ca receiveEther)
    {sevm : Sevm} {pre post : Devm}
    (run : Prog.Run sevm pre (weth10 dp) post)
    (h_target : sevm.currentTarget = ca)
    (ih : FlashExactDepth dp ca sevm.depth) :
    FlashExactSpecsRel dp ca sevm pre post := by
  intro flash h_pre
  dsimp only [Prog.Run] at run
  cases run
  rename (_ = _) => h_eq
  rename (Func.Run _ _ _ _ _) => hrun
  rename (Devm.Burn _ _) => burn
  rename Devm => s0
  cases h_eq
  have h_pre0 : (flashExactSpec dp flash).Pre ca sevm s0 :=
    h_pre.state_eq burn.state.symm
  have hrun' : Func.Run ((weth10 dp).main :: weth10Aux) sevm s0
      (calldatasize ::: iszero :::
        (receiveEther <?>
          (fsig +++ dispatchWith fallbackSlot (weth10Tree dp)))) post := by
    simpa only [weth10, weth10Main] using hrun
  refine run_prepend_elim _ [calldatasize, iszero] ?_ hrun'
  intro s1 hentry hbranch
  have h_pre1 : (flashExactSpec dp flash).Pre ca sevm s1 :=
    h_pre0.of_eqs
      (congrFun (Line.of_inv Devm.getCode (by line_inv) hentry).symm ca)
      (Line.of_inv Devm.getBal (by line_inv) hentry).symm
      (congrFun (Line.of_inv Devm.getStor (by line_inv) hentry).symm ca)
  rcases of_run_branch hbranch with
    ⟨s2, hpop, hdispatch⟩ |
    ⟨w, s2, s3, hnz, hpop, hburn, hreceive⟩
  · refine run_prepend_elim _ fsig ?_ hdispatch
    intro s3 hfsig hdispatch'
    have h_pre3 : (flashExactSpec dp flash).Pre ca sevm s3 :=
      (h_pre1.state_eq hpop.state.symm).of_eqs
        (congrFun (Line.of_inv Devm.getCode (by line_inv) hfsig).symm ca)
        (Line.of_inv Devm.getBal (by line_inv) hfsig).symm
        (congrFun (Line.of_inv Devm.getStor (by line_inv) hfsig).symm ca)
    exact flashExactPost_of_run_dispatch dp ca h_funcs
      (by
        intro e x y hct hcode hih hrev
        exact absurd hrev not_run_rev)
      h_target h_pre3 ih hdispatch'
  · have h_pre3 :=
      h_pre1.state_eq (hburn.state.symm.trans hpop.state.symm)
    have hrel := h_receive h_target h_pre3.code ih hreceive
    exact (flashExactSpecsRel_of_rel dp ca hrel) flash h_pre3

/-- The exact Boolean callback tail preserves the entry flash counter across
its arbitrary zero-value child and storage-silent decoder. -/
theorem flashExactRel_of_run_callBoolCallback
    (dp : DeployParams) (ca : Adr)
    {sevm : Sevm} {s r : Devm} {sel target dataArg : B256}
    {value : Line}
    (h_target : sevm.currentTarget = ca)
    (ih : FlashExactDepth dp ca sevm.depth)
    (h_code : some (s.getCode ca).toList = Prog.compile (weth10 dp))
    (h_value_stor : Line.Inv Devm.getStor value)
    (h_value_bal : Line.Inv Devm.getBal value)
    (h_value_code : Line.Inv Devm.getCode value)
    (run : Func.Run ((weth10 dp).main :: weth10Aux) sevm s
      (callBoolCallback sel target dataArg value) r) :
    FlashExactRel dp ca sevm s r := by
  obtain ⟨sc, sf, g, inputSize, xs, hpCall, hcall, hbool,
      h_stor_s_sc, h_bal_s_sc, h_code_s_sc⟩ :=
    of_run_callBoolCallback dp sel target dataArg value
      h_value_stor h_value_bal h_value_code run
  have h_code_sc :
      some (sc.getCode ca).toList = Prog.compile (weth10 dp) := by
    rw [← h_target, ← h_code_s_sc, h_target]
    exact h_code
  have h_call := flashExactRel_of_value_call dp ca
    h_target ih hpCall h_code_sc hcall
  obtain ⟨h_stor_tail, h_bal_tail, h_code_tail⟩ :=
    of_run_call_boolReturn_preserves_fields dp hbool
  unfold FlashExactRel at h_call ⊢
  exact (congrArg (fun st => st.get flashMintedSlot)
      (congrFun h_stor_tail ca)).symm.trans
    (h_call.trans (congrArg (fun st => st.get flashMintedSlot)
      (congrFun h_stor_s_sc ca).symm))

theorem depositToAndCall_exactRelFuncSound
    (dp : DeployParams) (ca : Adr) :
    ExactRelFuncSound dp ca depositToAndCall := by
  intro sevm s r h_target h_code ih run
  subst ca
  simp only [depositToAndCall] at run
  rcases of_run_prepend mintToPrefix _ run with
    ⟨smint, hmint, hcallback⟩
  obtain ⟨recipient, h_inc, h_flash⟩ :=
    mintToPrefix_storage
      (fs := (weth10 dp).main :: weth10Aux) hmint
  have h_code_mint :
      some (smint.getCode sevm.currentTarget).toList =
        Prog.compile (weth10 dp) := by
    rw [← congrFun (Line.of_inv Devm.getCode (by line_inv) hmint)
      sevm.currentTarget]
    exact h_code
  have h_callback := flashExactRel_of_run_callBoolCallback dp
    sevm.currentTarget rfl ih h_code_mint
    (by line_inv) (by line_inv) (by line_inv) hcallback
  unfold FlashExactRel at h_callback ⊢
  exact h_callback.trans h_flash

theorem approveAndCall_exactRelFuncSound
    (dp : DeployParams) (ca : Adr) :
    ExactRelFuncSound dp ca (nonpayable approveAndCall) := by
  apply ExactRelFuncSound.nonpayable dp ca
  intro sevm s r h_target h_code ih run
  subst ca
  simp only [approveAndCall] at run
  rcases of_run_prepend approvePrefix _ run with
    ⟨sapprove, happrove, hcallback⟩
  have h_silent := approvePrefix_storage_silent happrove
  have h_code_approve :
      some (sapprove.getCode sevm.currentTarget).toList =
        Prog.compile (weth10 dp) := by
    rw [← congrFun (Line.of_inv Devm.getCode (by line_inv) happrove)
      sevm.currentTarget]
    exact h_code
  have h_callback := flashExactRel_of_run_callBoolCallback dp
    sevm.currentTarget rfl ih h_code_approve
    (by line_inv) (by line_inv) (by line_inv) hcallback
  unfold FlashExactRel at h_callback ⊢
  exact h_callback.trans h_silent.2

/-- The zero-recipient transfer prefix preserves the exact flash counter
across its accepted ETH call and exposes the continuation state. -/
theorem of_transferZeroThen_exact
    (dp : DeployParams) (ca : Adr)
    {sevm : Sevm} {s r : Devm} {next : Func}
    (h_target : sevm.currentTarget = ca)
    (ih : FlashExactDepth dp ca sevm.depth)
    (h_code : some (s.getCode ca).toList = Prog.compile (weth10 dp))
    (run : Func.Run ((weth10 dp).main :: weth10Aux) sevm s
      (transferZeroThen next) r) :
    ∃ snext,
      FlashExactRel dp ca sevm s snext ∧
      some (snext.getCode ca).toList = Prog.compile (weth10 dp) ∧
      Func.Run ((weth10 dp).main :: weth10Aux) sevm snext next r := by
  subst ca
  simp only [transferZeroThen] at run
  rcases of_run_prepend (loadCallerBalanceAmount 1) _ run with
    ⟨s1, hload, run1⟩
  rcases prefix_of_loadCallerBalanceAmount nil_pref hload with
    ⟨balance, h_balance, hp1⟩
  rcases of_run_prepend balanceTooSmall _ run1 with
    ⟨s2, hguard, run2⟩
  have hp2 :
      (balance <? Sevm.argWord sevm 1) :: balance ::
        Sevm.argWord sevm 1 :: sevm.caller.toB256 :: [] <<+ s2.stack :=
    prefix_of_balanceTooSmall hp1 hguard
  have h_burn_lookup :
      ((weth10 dp).main :: weth10Aux)[burnBalanceErrorSlot]? =
        some (Func.revWith "WETH: burn amount exceeds balance") := by
    simp [weth10, weth10Aux, burnBalanceErrorSlot, burnBalanceError]
  rcases of_run_branch_call_revWith h_burn_lookup run2 with
    ⟨s3, hpopGuard, run3⟩
  have hpopStack := hpopGuard.stack
  simp only [Stack.Pop, Split, List.nil_append, List.cons_append] at hpopStack
  rw [hpopStack] at hp2
  have h_flag : (balance <? Sevm.argWord sevm 1) = 0 :=
    pref_head_unique hp2 (pref_append [0] s3.stack)
  have h_token_le : Sevm.argWord sevm 1 ≤ balance := by
    rw [← B256.not_lt]
    intro hlt
    rw [B256.ltCheck, if_pos hlt] at h_flag
    exact B256.zero_ne_one h_flag.symm
  rw [h_flag] at hp2
  have hp3 :
      [balance, Sevm.argWord sevm 1, sevm.caller.toB256] <<+ s3.stack :=
    cons_pref_cons_inv hp2
  have h_stor_s_s3 : Devm.getStor s = Devm.getStor s3 :=
    (Line.of_inv Devm.getStor (by line_inv) hload).trans
      ((Line.of_inv Devm.getStor (by line_inv) hguard).trans
        (PopBurn.Inv.inv hpopGuard))
  have h_code_s_s3 :
      s.getCode sevm.currentTarget = s3.getCode sevm.currentTarget :=
    (congrFun (Line.of_inv Devm.getCode (by line_inv) hload)
      sevm.currentTarget).trans
      ((congrFun (Line.of_inv Devm.getCode (by line_inv) hguard)
        sevm.currentTarget).trans
        (getCode_eq_of_state_eq hpopGuard.state sevm.currentTarget))
  have h_balance3 :
      balance =
        (Devm.getStor s3 sevm.currentTarget).get sevm.caller.toB256 := by
    rw [h_balance, congrFun h_stor_s_s3 sevm.currentTarget]
  rcases of_run_prepend debitLoadedBalance _ run3 with
    ⟨s4, hdebit, run4⟩
  obtain ⟨h_dec, h_cover, h_flash⟩ :=
    debitLoadedBalance_storage (validAdr_toB256 sevm.caller)
      h_balance3 h_token_le hp3 hdebit
  let eventLine : Line :=
    [caller] ++ arg 1 ++ [pushB256 0] ++ emitTransfer ++ [swap 0, pop]
  rcases of_run_prepend eventLine _ run4 with
    ⟨s5, hevent, run5⟩
  have hp5 : Sevm.argWord sevm 1 :: [] <<+ s5.stack := by
    apply prefix_of_burnEvent 1 nil_pref
    simpa only [eventLine] using hevent
  rcases of_run_prepend sendValueToCaller _ run5 with
    ⟨s6, hsend, run6⟩
  obtain ⟨sc, g, hpCall, hcall, h_stor_s5_sc, h_bal_s5_sc,
      h_code_s5_sc⟩ := of_sendValueToCaller hp5 hsend
  rcases of_run_next run6 with ⟨si, hiszero, run7⟩
  have h_eth_lookup :
      ((weth10 dp).main :: weth10Aux)[ethTransferErrorSlot]? =
        some (Func.revWith "WETH: ETH transfer failed") := by
    simp [weth10, weth10Aux, ethTransferErrorSlot, ethTransferError]
  rcases of_run_branch_call_revWith h_eth_lookup run7 with
    ⟨sb, hpopCall, hnext⟩
  have h_stor_s4_sc : Devm.getStor s4 = Devm.getStor sc :=
    (Line.of_inv Devm.getStor (by line_inv) hevent).trans h_stor_s5_sc
  have h_code_s3_sc :
      s3.getCode sevm.currentTarget = sc.getCode sevm.currentTarget :=
    (congrFun (Line.of_inv Devm.getCode (by line_inv) hdebit)
      sevm.currentTarget).trans
      ((congrFun (Line.of_inv Devm.getCode (by line_inv) hevent)
        sevm.currentTarget).trans
        (congrFun h_code_s5_sc sevm.currentTarget))
  have h_code_sc :
      some (sc.getCode sevm.currentTarget).toList =
        Prog.compile (weth10 dp) := by
    rw [← h_code_s3_sc, ← h_code_s_s3]
    exact h_code
  have h_exact_sc :
      FlashExactRel dp sevm.currentTarget sevm s sc := by
    unfold FlashExactRel
    rw [← congrFun h_stor_s4_sc sevm.currentTarget,
      h_flash, ← congrFun h_stor_s_s3 sevm.currentTarget]
  have h_call_exact := flashExactRel_of_value_call dp
    sevm.currentTarget rfl ih hpCall h_code_sc hcall
  have h_stor_s6_si : Devm.getStor s6 = Devm.getStor si :=
    Line.of_inv Devm.getStor (by line_inv)
      (Line.Run.cons hiszero Line.Run.nil)
  have h_stor_si_sb : Devm.getStor si = Devm.getStor sb :=
    PopBurn.Inv.inv hpopCall
  have h_exact_sb :
      FlashExactRel dp sevm.currentTarget sevm s sb := by
    unfold FlashExactRel at h_call_exact h_exact_sc ⊢
    rw [← congrFun h_stor_si_sb sevm.currentTarget,
      ← congrFun h_stor_s6_si sevm.currentTarget]
    exact h_call_exact.trans h_exact_sc
  have h_code_nonempty :
      (sc.getCode sevm.currentTarget).toList ≠ [] := by
    intro he
    apply Prog.compile_ne_nil (p := weth10 dp)
    rw [← h_code_sc, he]
  have h_code_s6_sc :
      s6.getCode sevm.currentTarget = sc.getCode sevm.currentTarget :=
    code_eq_of_ninst_run h_code_nonempty hcall
  have h_code_s6_si :
      s6.getCode sevm.currentTarget = si.getCode sevm.currentTarget :=
    congrFun (Line.of_inv Devm.getCode (by line_inv)
      (Line.Run.cons hiszero Line.Run.nil)) sevm.currentTarget
  have h_code_si_sb :
      si.getCode sevm.currentTarget = sb.getCode sevm.currentTarget :=
    getCode_eq_of_state_eq hpopCall.state sevm.currentTarget
  have h_code_sb_sc :
      sb.getCode sevm.currentTarget = sc.getCode sevm.currentTarget :=
    (h_code_s6_si.trans h_code_si_sb).symm.trans h_code_s6_sc
  refine ⟨sb, h_exact_sb, ?_, hnext⟩
  rw [h_code_sb_sc]
  exact h_code_sc

/-- `transferThen` preserves the exact flash counter up to its arbitrary
continuation, in both recipient branches. -/
theorem of_transferThen_exact
    (dp : DeployParams) (ca : Adr)
    {sevm : Sevm} {s r : Devm} {next : Func}
    (h_target : sevm.currentTarget = ca)
    (ih : FlashExactDepth dp ca sevm.depth)
    (h_code : some (s.getCode ca).toList = Prog.compile (weth10 dp))
    (run : Func.Run ((weth10 dp).main :: weth10Aux) sevm s
      (transferThen next) r) :
    ∃ snext,
      FlashExactRel dp ca sevm s snext ∧
      some (snext.getCode ca).toList = Prog.compile (weth10 dp) ∧
      Func.Run ((weth10 dp).main :: weth10Aux) sevm snext next r := by
  subst ca
  simp only [transferThen] at run
  rcases of_run_prepend (arg 0) _ run with ⟨s1, harg, run1⟩
  have hp1 : Sevm.argWord sevm 0 :: [] <<+ s1.stack :=
    prefix_of_arg nil_pref harg
  rcases of_run_next run1 with ⟨s2, hiszero, run2⟩
  have hp2 : (Sevm.argWord sevm 0 =? 0) :: [] <<+ s2.stack :=
    prefix_of_iszero hiszero hp1
  rcases of_run_branch run2 with
      ⟨s3, hpop, hnonzero⟩ |
      ⟨w, s3, s4, hnz, hpop, hburn, hzero⟩
  · have h_stor_s_s3 : Devm.getStor s = Devm.getStor s3 :=
      (Line.of_inv Devm.getStor (by line_inv) harg).trans
        ((Line.of_inv Devm.getStor (by line_inv)
          (Line.Run.cons hiszero Line.Run.nil)).trans
            (PopBurn.Inv.inv hpop))
    have h_code_s_s3 :
        s.getCode sevm.currentTarget = s3.getCode sevm.currentTarget :=
      (congrFun (Line.of_inv Devm.getCode (by line_inv) harg)
        sevm.currentTarget).trans
        ((congrFun (Line.of_inv Devm.getCode (by line_inv)
          (Line.Run.cons hiszero Line.Run.nil))
          sevm.currentTarget).trans
          (getCode_eq_of_state_eq hpop.state sevm.currentTarget))
    obtain ⟨snext, h_flash, h_code_next, hnext⟩ :=
      of_transferNonzeroThen_flash dp hnonzero
    refine ⟨snext, ?_, ?_, hnext⟩
    · unfold FlashExactRel
      exact h_flash.trans (congrArg (fun st => st.get flashMintedSlot)
        (congrFun h_stor_s_s3 sevm.currentTarget).symm)
    · rw [h_code_next, ← h_code_s_s3]
      exact h_code
  · have h_stor_s_s4 : Devm.getStor s = Devm.getStor s4 :=
      (Line.of_inv Devm.getStor (by line_inv) harg).trans
        ((Line.of_inv Devm.getStor (by line_inv)
          (Line.Run.cons hiszero Line.Run.nil)).trans
            ((PopBurn.Inv.inv hpop).trans (Burn.Inv.inv hburn)))
    have h_code_s_s4 :
        s.getCode sevm.currentTarget = s4.getCode sevm.currentTarget :=
      (congrFun (Line.of_inv Devm.getCode (by line_inv) harg)
        sevm.currentTarget).trans
        ((congrFun (Line.of_inv Devm.getCode (by line_inv)
          (Line.Run.cons hiszero Line.Run.nil))
          sevm.currentTarget).trans
          ((getCode_eq_of_state_eq hpop.state sevm.currentTarget).trans
            (getCode_eq_of_state_eq hburn.state sevm.currentTarget)))
    have h_code4 :
        some (s4.getCode sevm.currentTarget).toList =
          Prog.compile (weth10 dp) := by
      rw [← h_code_s_s4]
      exact h_code
    obtain ⟨snext, h_exact, h_code_next, hnext⟩ :=
      of_transferZeroThen_exact dp sevm.currentTarget rfl ih h_code4 hzero
    refine ⟨snext, ?_, h_code_next, hnext⟩
    unfold FlashExactRel at h_exact ⊢
    exact h_exact.trans (congrArg (fun st => st.get flashMintedSlot)
      (congrFun h_stor_s_s4 sevm.currentTarget).symm)

/-- Exact flash-counter preservation for `transferAndCall`, including its
arbitrary successful callback subtree. -/
theorem transferAndCall_exactRelFuncSound
    (dp : DeployParams) (ca : Adr) :
    ExactRelFuncSound dp ca (nonpayable transferAndCall) := by
  apply ExactRelFuncSound.nonpayable dp ca
  intro sevm s r h_target h_code ih run
  change Func.Run ((weth10 dp).main :: weth10Aux) sevm s
    transferAndCall r at run
  obtain ⟨snext, h_exact, h_code_next, hcallback⟩ :=
    of_transferThen_exact dp ca h_target ih h_code
      (by simpa only [transferAndCall] using run)
  have h_callback := flashExactRel_of_run_callBoolCallback dp ca
    h_target ih h_code_next
    (by line_inv) (by line_inv) (by line_inv) hcallback
  unfold FlashExactRel at h_callback h_exact ⊢
  exact h_callback.trans h_exact

/-- Successful Boolean `CALL` guard transport for the exact flash relation,
with the compiled-code premise retained for the continuation. -/
theorem flashExactCode_of_call_success_guard
    (dp : DeployParams) (ca : Adr)
    {sevm : Sevm} {sc s6 si sb : Devm}
    {g c v ii is oi os : B256} {xs : Stack}
    (h_target : sevm.currentTarget = ca)
    (ih : FlashExactDepth dp ca sevm.depth)
    (hp : (g :: c :: v :: ii :: is :: oi :: os :: xs) <<+ sc.stack)
    (h_code : some (sc.getCode ca).toList = Prog.compile (weth10 dp))
    (hcall : Ninst.Run sevm sc call s6)
    (hiszero : Ninst.Run sevm s6 iszero si)
    (hpop : Devm.PopBurn [0] si sb) :
    FlashExactRel dp ca sevm sc sb ∧
      some (sb.getCode ca).toList = Prog.compile (weth10 dp) := by
  have h_call := flashExactRel_of_value_call dp ca
    h_target ih hp h_code hcall
  have h_stor_s6_si : Devm.getStor s6 = Devm.getStor si :=
    Line.of_inv Devm.getStor (by line_inv)
      (Line.Run.cons hiszero Line.Run.nil)
  have h_stor_si_sb : Devm.getStor si = Devm.getStor sb :=
    PopBurn.Inv.inv hpop
  have h_exact : FlashExactRel dp ca sevm sc sb := by
    unfold FlashExactRel at h_call ⊢
    exact (congrArg (fun st => st.get flashMintedSlot)
        (congrFun h_stor_si_sb ca)).symm.trans
      ((congrArg (fun st => st.get flashMintedSlot)
        (congrFun h_stor_s6_si ca)).symm.trans h_call)
  have h_code_nonempty : (sc.getCode ca).toList ≠ [] := by
    intro he
    apply Prog.compile_ne_nil (p := weth10 dp)
    rw [← h_code, he]
  have h_code_s6_sc : s6.getCode ca = sc.getCode ca :=
    code_eq_of_ninst_run h_code_nonempty hcall
  have h_code_s6_si : s6.getCode ca = si.getCode ca :=
    congrFun (Line.of_inv Devm.getCode (by line_inv)
      (Line.Run.cons hiszero Line.Run.nil)) ca
  have h_code_si_sb : si.getCode ca = sb.getCode ca :=
    getCode_eq_of_state_eq hpop.state ca
  have h_code_sb_sc : sb.getCode ca = sc.getCode ca :=
    (h_code_s6_si.trans h_code_si_sb).symm.trans h_code_s6_sc
  refine ⟨h_exact, ?_⟩
  rw [h_code_sb_sc]
  exact h_code

/-- Generic caller-burn/value-send prefix preserving the exact flash counter
through the accepted external call. -/
theorem of_callerBurnThen_exact
    (dp : DeployParams) (ca : Adr)
    (amountArg : B256) (send : Line) (sendErrorSlot : Nat)
    (sendError : String) {next : Func}
    {sevm : Sevm} {s r : Devm}
    (h_target : sevm.currentTarget = ca)
    (ih : FlashExactDepth dp ca sevm.depth)
    (h_code : some (s.getCode ca).toList = Prog.compile (weth10 dp))
    (h_send : ∀ {s0 r0 : Devm} {value : B256} {xs : Stack},
      value :: xs <<+ s0.stack → Line.Run sevm s0 send r0 →
      ∃ sc g target,
        (g :: target :: value :: 0 :: 0 :: 0 :: 0 :: xs) <<+ sc.stack ∧
        Ninst.Run sevm sc call r0 ∧
        Devm.getStor s0 = Devm.getStor sc ∧
        s0.getCode = sc.getCode)
    (h_error_lookup :
      ((weth10 dp).main :: weth10Aux)[sendErrorSlot]? =
        some (Func.revWith sendError))
    (run : Func.Run ((weth10 dp).main :: weth10Aux) sevm s
      (loadCallerBalanceAmount amountArg +++ balanceTooSmall +++
        (.call burnBalanceErrorSlot) <?>
        (debitLoadedBalance +++
          caller ::: arg amountArg +++ pushB256 0 ::: emitTransfer +++
          swap 0 ::: pop :::
          send +++ iszero :::
          (.call sendErrorSlot) <?> next)) r) :
    ∃ snext,
      FlashExactRel dp ca sevm s snext ∧
      some (snext.getCode ca).toList = Prog.compile (weth10 dp) ∧
      Func.Run ((weth10 dp).main :: weth10Aux) sevm snext next r := by
  subst ca
  rcases of_run_prepend (loadCallerBalanceAmount amountArg) _ run with
    ⟨s1, hload, run1⟩
  rcases prefix_of_loadCallerBalanceAmount nil_pref hload with
    ⟨balance, h_balance, hp1⟩
  rcases of_run_prepend balanceTooSmall _ run1 with
    ⟨s2, hguard, run2⟩
  have hp2 :
      (balance <? Sevm.argWord sevm amountArg) :: balance ::
        Sevm.argWord sevm amountArg :: sevm.caller.toB256 :: [] <<+
          s2.stack :=
    prefix_of_balanceTooSmall hp1 hguard
  have h_burn_lookup :
      ((weth10 dp).main :: weth10Aux)[burnBalanceErrorSlot]? =
        some (Func.revWith "WETH: burn amount exceeds balance") := by
    simp [weth10, weth10Aux, burnBalanceErrorSlot, burnBalanceError]
  rcases of_run_branch_call_revWith h_burn_lookup run2 with
    ⟨s3, hpopGuard, run3⟩
  have hpopStack := hpopGuard.stack
  simp only [Stack.Pop, Split, List.nil_append, List.cons_append] at hpopStack
  rw [hpopStack] at hp2
  have h_flag : (balance <? Sevm.argWord sevm amountArg) = 0 :=
    pref_head_unique hp2 (pref_append [0] s3.stack)
  have h_token_le : Sevm.argWord sevm amountArg ≤ balance := by
    rw [← B256.not_lt]
    intro hlt
    rw [B256.ltCheck, if_pos hlt] at h_flag
    exact B256.zero_ne_one h_flag.symm
  rw [h_flag] at hp2
  have hp3 :
      [balance, Sevm.argWord sevm amountArg, sevm.caller.toB256] <<+
        s3.stack := cons_pref_cons_inv hp2
  have h_stor_s_s3 : Devm.getStor s = Devm.getStor s3 :=
    (Line.of_inv Devm.getStor (by line_inv) hload).trans
      ((Line.of_inv Devm.getStor (by line_inv) hguard).trans
        (PopBurn.Inv.inv hpopGuard))
  have h_code_s_s3 :
      s.getCode sevm.currentTarget = s3.getCode sevm.currentTarget :=
    (congrFun (Line.of_inv Devm.getCode (by line_inv) hload)
      sevm.currentTarget).trans
      ((congrFun (Line.of_inv Devm.getCode (by line_inv) hguard)
        sevm.currentTarget).trans
        (getCode_eq_of_state_eq hpopGuard.state sevm.currentTarget))
  have h_balance3 :
      balance =
        (Devm.getStor s3 sevm.currentTarget).get sevm.caller.toB256 := by
    rw [h_balance, congrFun h_stor_s_s3 sevm.currentTarget]
  rcases of_run_prepend debitLoadedBalance _ run3 with
    ⟨s4, hdebit, run4⟩
  obtain ⟨h_dec, h_cover, h_flash⟩ :=
    debitLoadedBalance_storage (validAdr_toB256 sevm.caller)
      h_balance3 h_token_le hp3 hdebit
  let eventLine : Line :=
    [caller] ++ arg amountArg ++ [pushB256 0] ++ emitTransfer ++
      [swap 0, pop]
  rcases of_run_prepend eventLine _ run4 with
    ⟨s5, hevent, run5⟩
  have hp5 : Sevm.argWord sevm amountArg :: [] <<+ s5.stack := by
    apply prefix_of_burnEvent amountArg nil_pref
    simpa only [eventLine] using hevent
  rcases of_run_prepend send _ run5 with ⟨s6, hsend, run6⟩
  obtain ⟨sc, g, target, hpCall, hcall, h_stor_s5_sc,
      h_code_s5_sc⟩ := h_send hp5 hsend
  rcases of_run_next run6 with ⟨si, hiszero, run7⟩
  rcases of_run_branch_call_revWith h_error_lookup run7 with
    ⟨sb, hpopCall, hnext⟩
  have h_stor_s4_sc : Devm.getStor s4 = Devm.getStor sc :=
    (Line.of_inv Devm.getStor (by line_inv) hevent).trans h_stor_s5_sc
  have h_code_s3_sc :
      s3.getCode sevm.currentTarget = sc.getCode sevm.currentTarget :=
    (congrFun (Line.of_inv Devm.getCode (by line_inv) hdebit)
      sevm.currentTarget).trans
      ((congrFun (Line.of_inv Devm.getCode (by line_inv) hevent)
        sevm.currentTarget).trans
        (congrFun h_code_s5_sc sevm.currentTarget))
  have h_code_sc :
      some (sc.getCode sevm.currentTarget).toList =
        Prog.compile (weth10 dp) := by
    rw [← h_code_s3_sc, ← h_code_s_s3]
    exact h_code
  have h_exact_sc :
      FlashExactRel dp sevm.currentTarget sevm s sc := by
    unfold FlashExactRel
    rw [← congrFun h_stor_s4_sc sevm.currentTarget,
      h_flash, ← congrFun h_stor_s_s3 sevm.currentTarget]
  obtain ⟨h_exact_sb, h_code_sb⟩ :=
    flashExactCode_of_call_success_guard dp sevm.currentTarget
      rfl ih hpCall h_code_sc hcall hiszero hpopCall
  refine ⟨sb, ?_, h_code_sb, hnext⟩
  unfold FlashExactRel at h_exact_sb h_exact_sc ⊢
  exact h_exact_sb.trans h_exact_sc

/-- Generic normalized-source burn/value-send prefix preserving the exact
flash counter through the accepted external call. -/
theorem of_argBurnThen_exact
    (dp : DeployParams) (ca : Adr)
    (ownerArg amountArg : B256) (send : Line) (sendErrorSlot : Nat)
    (sendError : String) {next : Func}
    {sevm : Sevm} {s r : Devm}
    (h_target : sevm.currentTarget = ca)
    (ih : FlashExactDepth dp ca sevm.depth)
    (h_code : some (s.getCode ca).toList = Prog.compile (weth10 dp))
    (h_send : ∀ {s0 r0 : Devm} {value : B256} {xs : Stack},
      value :: xs <<+ s0.stack → Line.Run sevm s0 send r0 →
      ∃ sc g target,
        (g :: target :: value :: 0 :: 0 :: 0 :: 0 :: xs) <<+ sc.stack ∧
        Ninst.Run sevm sc call r0 ∧
        Devm.getStor s0 = Devm.getStor sc ∧
        s0.getCode = sc.getCode)
    (h_error_lookup :
      ((weth10 dp).main :: weth10Aux)[sendErrorSlot]? =
        some (Func.revWith sendError))
    (run : Func.Run ((weth10 dp).main :: weth10Aux) sevm s
      (loadArgBalanceAmount ownerArg amountArg +++ balanceTooSmall +++
        (.call burnBalanceErrorSlot) <?>
        (debitLoadedBalance +++
          addressArg ownerArg +++ arg amountArg +++ pushB256 0 :::
          emitTransfer +++ swap 0 ::: pop :::
          send +++ iszero :::
          (.call sendErrorSlot) <?> next)) r) :
    ∃ snext,
      FlashExactRel dp ca sevm s snext ∧
      some (snext.getCode ca).toList = Prog.compile (weth10 dp) ∧
      Func.Run ((weth10 dp).main :: weth10Aux) sevm snext next r := by
  subst ca
  rcases of_run_prepend (loadArgBalanceAmount ownerArg amountArg) _ run with
    ⟨s1, hload, run1⟩
  rcases prefix_of_loadArgBalanceAmount ownerArg amountArg nil_pref hload with
    ⟨balance, owner, h_owner, h_balance, hp1⟩
  rcases of_run_prepend balanceTooSmall _ run1 with
    ⟨s2, hguard, run2⟩
  have hp2 :
      (balance <? Sevm.argWord sevm amountArg) :: balance ::
        Sevm.argWord sevm amountArg :: owner :: [] <<+ s2.stack :=
    prefix_of_balanceTooSmall hp1 hguard
  have h_burn_lookup :
      ((weth10 dp).main :: weth10Aux)[burnBalanceErrorSlot]? =
        some (Func.revWith "WETH: burn amount exceeds balance") := by
    simp [weth10, weth10Aux, burnBalanceErrorSlot, burnBalanceError]
  rcases of_run_branch_call_revWith h_burn_lookup run2 with
    ⟨s3, hpopGuard, run3⟩
  have hpopStack := hpopGuard.stack
  simp only [Stack.Pop, Split, List.nil_append, List.cons_append] at hpopStack
  rw [hpopStack] at hp2
  have h_flag : (balance <? Sevm.argWord sevm amountArg) = 0 :=
    pref_head_unique hp2 (pref_append [0] s3.stack)
  have h_token_le : Sevm.argWord sevm amountArg ≤ balance := by
    rw [← B256.not_lt]
    intro hlt
    rw [B256.ltCheck, if_pos hlt] at h_flag
    exact B256.zero_ne_one h_flag.symm
  rw [h_flag] at hp2
  have hp3 : [balance, Sevm.argWord sevm amountArg, owner] <<+ s3.stack :=
    cons_pref_cons_inv hp2
  have h_stor_s_s3 : Devm.getStor s = Devm.getStor s3 :=
    (Line.of_inv Devm.getStor (by line_inv) hload).trans
      ((Line.of_inv Devm.getStor (by line_inv) hguard).trans
        (PopBurn.Inv.inv hpopGuard))
  have h_code_s_s3 :
      s.getCode sevm.currentTarget = s3.getCode sevm.currentTarget :=
    (congrFun (Line.of_inv Devm.getCode (by line_inv) hload)
      sevm.currentTarget).trans
      ((congrFun (Line.of_inv Devm.getCode (by line_inv) hguard)
        sevm.currentTarget).trans
        (getCode_eq_of_state_eq hpopGuard.state sevm.currentTarget))
  have h_balance3 : balance =
      (Devm.getStor s3 sevm.currentTarget).get owner := by
    rw [h_balance, congrFun h_stor_s_s3 sevm.currentTarget]
  rcases of_run_prepend debitLoadedBalance _ run3 with
    ⟨s4, hdebit, run4⟩
  obtain ⟨h_dec, h_cover, h_flash⟩ :=
    debitLoadedBalance_storage (by
      rw [h_owner]
      exact normalizedAddress_valid (Sevm.argWord sevm ownerArg))
      h_balance3 h_token_le hp3 hdebit
  let eventLine : Line :=
    addressArg ownerArg ++ arg amountArg ++ [pushB256 0] ++
      emitTransfer ++ [swap 0, pop]
  rcases of_run_prepend eventLine _ run4 with
    ⟨s5, hevent, run5⟩
  have hp5 : Sevm.argWord sevm amountArg :: [] <<+ s5.stack := by
    apply prefix_of_burnEventFromArg ownerArg amountArg nil_pref
    simpa only [eventLine] using hevent
  rcases of_run_prepend send _ run5 with ⟨s6, hsend, run6⟩
  obtain ⟨sc, g, target, hpCall, hcall, h_stor_s5_sc,
      h_code_s5_sc⟩ := h_send hp5 hsend
  rcases of_run_next run6 with ⟨si, hiszero, run7⟩
  rcases of_run_branch_call_revWith h_error_lookup run7 with
    ⟨sb, hpopCall, hnext⟩
  have h_stor_s4_sc : Devm.getStor s4 = Devm.getStor sc :=
    (Line.of_inv Devm.getStor (by line_inv) hevent).trans h_stor_s5_sc
  have h_code_s3_sc :
      s3.getCode sevm.currentTarget = sc.getCode sevm.currentTarget :=
    (congrFun (Line.of_inv Devm.getCode (by line_inv) hdebit)
      sevm.currentTarget).trans
      ((congrFun (Line.of_inv Devm.getCode (by line_inv) hevent)
        sevm.currentTarget).trans
        (congrFun h_code_s5_sc sevm.currentTarget))
  have h_code_sc :
      some (sc.getCode sevm.currentTarget).toList =
        Prog.compile (weth10 dp) := by
    rw [← h_code_s3_sc, ← h_code_s_s3]
    exact h_code
  have h_exact_sc :
      FlashExactRel dp sevm.currentTarget sevm s sc := by
    unfold FlashExactRel
    rw [← congrFun h_stor_s4_sc sevm.currentTarget,
      h_flash, ← congrFun h_stor_s_s3 sevm.currentTarget]
  obtain ⟨h_exact_sb, h_code_sb⟩ :=
    flashExactCode_of_call_success_guard dp sevm.currentTarget
      rfl ih hpCall h_code_sc hcall hiszero hpopCall
  refine ⟨sb, ?_, h_code_sb, hnext⟩
  unfold FlashExactRel at h_exact_sb h_exact_sc ⊢
  exact h_exact_sb.trans h_exact_sc

private theorem b256_add_sub_cancel_right (x y : B256) :
    x + y - y = x := by
  apply B256.toNat_inj
  rw [B256.toNat_sub, B256.toNat_add]
  have hx := B256.toNat_lt x
  have hy := B256.toNat_lt y
  unfold Nat.lo
  by_cases h : x.toNat + y.toNat < 2 ^ 256
  · rw [Nat.mod_eq_of_lt h]
    rw [show 2 ^ 256 + (x.toNat + y.toNat) - y.toNat =
        2 ^ 256 + x.toNat by omega,
      Nat.add_mod_left,
      Nat.mod_eq_of_lt hx]
  · rw [Nat.not_lt] at h
    have hsum : x.toNat + y.toNat < 2 * 2 ^ 256 := by omega
    rw [Nat.add_mod_eq_add_sub hx hy h]
    have hle : y.toNat ≤
        x.toNat + y.toNat - 2 ^ 256 + 2 ^ 256 := by omega
    omega

/-- A successful flash loan restores the exact entry flash counter across the
arbitrary borrower call, decoder, allowance phase, and final burn. -/
theorem flashLoan_exactRelFuncSound
    (dp : DeployParams) (ca : Adr) :
    ExactRelFuncSound dp ca flashLoan := by
  intro sevm s r h_target h_code ih run
  subst ca
  rcases of_flashLoan_toCall dp run with
    ⟨recipient, sc, g, inputSize, base, hbase, hamount, htotal,
      hinc, hflash, hcodeSc, hbalSc, hpCall, htail⟩
  have h_code_sc : some (sc.getCode sevm.currentTarget).toList =
      Prog.compile (weth10 dp) := by
    rw [← congrFun hcodeSc sevm.currentTarget]
    exact h_code
  rcases of_run_flashLoanFromCall dp htail with
    ⟨sf, ss, hcall, hsettle, hstorSfSs, hbalSfSs⟩
  have hcallExact := flashExactRel_of_value_call dp sevm.currentTarget
    rfl ih hpCall h_code_sc hcall
  have hflashSs :
      (Devm.getStor ss sevm.currentTarget).get flashMintedSlot =
        base + Sevm.argWord sevm 2 := by
    calc
      (Devm.getStor ss sevm.currentTarget).get flashMintedSlot =
          (Devm.getStor sf sevm.currentTarget).get flashMintedSlot :=
        congrArg (fun st => st.get flashMintedSlot)
          (congrFun hstorSfSs sevm.currentTarget).symm
      _ = (Devm.getStor sc sevm.currentTarget).get flashMintedSlot :=
        hcallExact
      _ = base + Sevm.argWord sevm 2 := hflash
  rcases of_run_flashSettle dp hsettle with
    ⟨sb, hburn, hsilent, hbalSilent, hcodeSilent⟩
  have hflashSb :
      (Devm.getStor sb sevm.currentTarget).get flashMintedSlot =
        base + Sevm.argWord sevm 2 :=
    hsilent.2.trans hflashSs
  have hburnFacts := flashBurn_storage_at_receiver dp hburn
  unfold FlashExactRel
  calc
    (Devm.getStor r sevm.currentTarget).get flashMintedSlot =
        (Devm.getStor sb sevm.currentTarget).get flashMintedSlot -
          Sevm.argWord sevm 2 := hburnFacts.2.2.1
    _ = (base + Sevm.argWord sevm 2) - Sevm.argWord sevm 2 := by
      rw [hflashSb]
    _ = base := b256_add_sub_cancel_right _ _
    _ = (Devm.getStor s sevm.currentTarget).get flashMintedSlot := hbase

/-- Exact flash-counter preservation for ordinary `transfer`, including the
zero-recipient ETH-call branch. -/
theorem transfer_exactRelFuncSound
    (dp : DeployParams) (ca : Adr) :
    ExactRelFuncSound dp ca (nonpayable transfer) := by
  apply ExactRelFuncSound.nonpayable dp ca
  intro sevm s r h_target h_code ih run
  change Func.Run ((weth10 dp).main :: weth10Aux) sevm s transfer r at run
  obtain ⟨snext, h_exact, h_code_next, hreturn⟩ :=
    of_transferThen_exact dp ca h_target ih h_code
      (by simpa only [transfer] using run)
  have hs : Devm.getStor snext = Devm.getStor r :=
    Func.of_inv Devm.getStor Devm.getStor (by func_inv) hreturn
  unfold FlashExactRel at h_exact ⊢
  exact (congrArg (fun st => st.get flashMintedSlot)
    (congrFun hs ca).symm).trans h_exact

/-- Exact flash-counter preservation for `withdraw`, including its accepted
ETH transfer subtree. -/
theorem withdraw_exactRelFuncSound
    (dp : DeployParams) (ca : Adr) :
    ExactRelFuncSound dp ca (nonpayable withdraw) := by
  apply ExactRelFuncSound.nonpayable dp ca
  intro sevm s r h_target h_code ih run
  change Func.Run ((weth10 dp).main :: weth10Aux) sevm s withdraw r at run
  obtain ⟨snext, h_exact, h_code_next, hstop⟩ :=
    of_callerBurnThen_exact dp ca 0 sendValueToCaller
      ethTransferErrorSlot "WETH: ETH transfer failed"
      h_target ih h_code (by
        intro s0 r0 value xs hp hsend
        rcases of_sendValueToCaller hp hsend with
          ⟨sc, g, hpCall, hcall, hstor, hbal, hcode⟩
        exact ⟨sc, g, sevm.caller.toB256, hpCall, hcall, hstor, hcode⟩)
      (by
        simp [weth10, weth10Aux, ethTransferErrorSlot,
          ethTransferError])
      (by simpa only [withdraw] using run)
  have hs : Devm.getStor snext = Devm.getStor r :=
    Func.of_inv Devm.getStor Devm.getStor (by func_inv) hstop
  unfold FlashExactRel at h_exact ⊢
  exact (congrArg (fun st => st.get flashMintedSlot)
    (congrFun hs ca).symm).trans h_exact

/-- Exact flash-counter preservation for `withdrawTo`, including its accepted
ETH transfer subtree. -/
theorem withdrawTo_exactRelFuncSound
    (dp : DeployParams) (ca : Adr) :
    ExactRelFuncSound dp ca (nonpayable withdrawTo) := by
  apply ExactRelFuncSound.nonpayable dp ca
  intro sevm s r h_target h_code ih run
  change Func.Run ((weth10 dp).main :: weth10Aux) sevm s withdrawTo r at run
  obtain ⟨snext, h_exact, h_code_next, hstop⟩ :=
    of_callerBurnThen_exact dp ca 1 (sendValueToArg 0)
      ethTransferErrorSlot "WETH: ETH transfer failed"
      h_target ih h_code (by
        intro s0 r0 value xs hp hsend
        rcases of_sendValueToArg 0 hp hsend with
          ⟨sc, g, hpCall, hcall, hstor, hbal, hcode⟩
        exact ⟨sc, g, Sevm.argWord sevm 0, hpCall, hcall,
          hstor, hcode⟩)
      (by
        simp [weth10, weth10Aux, ethTransferErrorSlot,
          ethTransferError])
      (by simpa only [withdrawTo] using run)
  have hs : Devm.getStor snext = Devm.getStor r :=
    Func.of_inv Devm.getStor Devm.getStor (by func_inv) hstop
  unfold FlashExactRel at h_exact ⊢
  exact (congrArg (fun st => st.get flashMintedSlot)
    (congrFun hs ca).symm).trans h_exact

theorem transferFromZero_exactRelFuncSound
    (dp : DeployParams) (ca : Adr) :
    ExactRelFuncSound dp ca transferFromZero := by
  intro sevm s r h_target h_code ih run
  change Func.Run ((weth10 dp).main :: weth10Aux) sevm s
    transferFromZero r at run
  obtain ⟨snext, h_exact, h_code_next, hreturn⟩ :=
    of_argBurnThen_exact dp ca 0 2 sendValueToCaller
      ethTransferErrorSlot "WETH: ETH transfer failed"
      h_target ih h_code (by
        intro s0 r0 value xs hp hsend
        rcases of_sendValueToCaller hp hsend with
          ⟨sc, g, hpCall, hcall, hstor, hbal, hcode⟩
        exact ⟨sc, g, sevm.caller.toB256, hpCall, hcall, hstor, hcode⟩)
      (by
        simp [weth10, weth10Aux, ethTransferErrorSlot,
          ethTransferError])
      (by simpa only [transferFromZero] using run)
  have hs : Devm.getStor snext = Devm.getStor r :=
    Func.of_inv Devm.getStor Devm.getStor (by func_inv) hreturn
  unfold FlashExactRel at h_exact ⊢
  exact (congrArg (fun st => st.get flashMintedSlot)
    (congrFun hs ca).symm).trans h_exact

theorem transferFromCore_exactRelFuncSound
    (dp : DeployParams) (ca : Adr) :
    ExactRelFuncSound dp ca transferFromCore := by
  intro sevm s r h_target h_code ih run
  change Func.Run ((weth10 dp).main :: weth10Aux) sevm s
    transferFromCore r at run
  simp only [transferFromCore] at run
  rcases of_run_prepend (arg 1) _ run with ⟨s1, harg, run1⟩
  have hp1 : Sevm.argWord sevm 1 :: [] <<+ s1.stack :=
    prefix_of_arg nil_pref harg
  rcases of_run_next run1 with ⟨s2, hiszero, run2⟩
  have hp2 : (Sevm.argWord sevm 1 =? 0) :: [] <<+ s2.stack :=
    prefix_of_iszero hiszero hp1
  rcases of_run_branch run2 with
      ⟨s3, hpop, hnonzero⟩ |
      ⟨w, s3, s4, hnz, hpop, hburn, hzero⟩
  · have h_stor_s_s3 : Devm.getStor s = Devm.getStor s3 :=
      (Line.of_inv Devm.getStor (by line_inv) harg).trans
        ((Line.of_inv Devm.getStor (by line_inv)
          (Line.Run.cons hiszero Line.Run.nil)).trans
            (PopBurn.Inv.inv hpop))
    have h_nonzero := transferFromNonzero_flashStable dp hnonzero
    unfold FlashExactRel
    rw [← h_target]
    exact h_nonzero.trans (congrArg (fun st => st.get flashMintedSlot)
      (congrFun h_stor_s_s3 sevm.currentTarget).symm)
  · have h_stor_s_s4 : Devm.getStor s = Devm.getStor s4 :=
      (Line.of_inv Devm.getStor (by line_inv) harg).trans
        ((Line.of_inv Devm.getStor (by line_inv)
          (Line.Run.cons hiszero Line.Run.nil)).trans
            ((PopBurn.Inv.inv hpop).trans (Burn.Inv.inv hburn)))
    have h_code_s_s4 :
        s.getCode sevm.currentTarget = s4.getCode sevm.currentTarget :=
      (congrFun (Line.of_inv Devm.getCode (by line_inv) harg)
        sevm.currentTarget).trans
        ((congrFun (Line.of_inv Devm.getCode (by line_inv)
          (Line.Run.cons hiszero Line.Run.nil))
          sevm.currentTarget).trans
          ((getCode_eq_of_state_eq hpop.state sevm.currentTarget).trans
            (getCode_eq_of_state_eq hburn.state sevm.currentTarget)))
    have h_code4 :
        some (s4.getCode ca).toList = Prog.compile (weth10 dp) := by
      rw [← h_target, ← h_code_s_s4, h_target]
      exact h_code
    have h_zero := transferFromZero_exactRelFuncSound dp ca
      h_target h_code4 ih hzero
    unfold FlashExactRel at h_zero ⊢
    exact h_zero.trans (congrArg (fun st => st.get flashMintedSlot)
      (congrFun h_stor_s_s4 ca).symm)

theorem transferFrom_exactRelFuncSound
    (dp : DeployParams) (ca : Adr) :
    ExactRelFuncSound dp ca (nonpayable transferFrom) := by
  apply ExactRelFuncSound.nonpayable dp ca
  intro sevm s r h_target h_code ih run
  change Func.Run ((weth10 dp).main :: weth10Aux) sevm s transferFrom r at run
  have h_core_lookup :
      ((weth10 dp).main :: weth10Aux)[transferFromCoreSlot]? =
        some transferFromCore := by
    simp [weth10, weth10Aux, transferFromCoreSlot]
  obtain ⟨sc, hcore, h_silent, h_bal, h_code_s_sc⟩ :=
    of_run_spendCallerAllowanceThen dp 2 transferFromCoreSlot
      transferFromCore h_core_lookup (by
        simpa only [transferFrom] using run)
  have h_code_sc :
      some (sc.getCode ca).toList = Prog.compile (weth10 dp) := by
    rw [← h_target, ← h_code_s_sc, h_target]
    exact h_code
  have h_core := transferFromCore_exactRelFuncSound dp ca
    h_target h_code_sc ih hcore
  unfold FlashExactRel at h_core ⊢
  exact h_core.trans (by
    simpa only [h_target] using h_silent.2)

theorem withdrawFromCore_exactRelFuncSound
    (dp : DeployParams) (ca : Adr) :
    ExactRelFuncSound dp ca withdrawFromCore := by
  intro sevm s r h_target h_code ih run
  change Func.Run ((weth10 dp).main :: weth10Aux) sevm s
    withdrawFromCore r at run
  obtain ⟨snext, h_exact, h_code_next, hstop⟩ :=
    of_argBurnThen_exact dp ca 0 2 (sendValueToArg 1)
      etherTransferErrorSlot "WETH: Ether transfer failed"
      h_target ih h_code (by
        intro s0 r0 value xs hp hsend
        rcases of_sendValueToArg 1 hp hsend with
          ⟨sc, g, hpCall, hcall, hstor, hbal, hcode⟩
        exact ⟨sc, g, Sevm.argWord sevm 1, hpCall, hcall,
          hstor, hcode⟩)
      (by
        simp [weth10, weth10Aux, etherTransferErrorSlot,
          etherTransferError])
      (by simpa only [withdrawFromCore] using run)
  have hs : Devm.getStor snext = Devm.getStor r :=
    Func.of_inv Devm.getStor Devm.getStor (by func_inv) hstop
  unfold FlashExactRel at h_exact ⊢
  exact (congrArg (fun st => st.get flashMintedSlot)
    (congrFun hs ca).symm).trans h_exact

theorem withdrawFrom_exactRelFuncSound
    (dp : DeployParams) (ca : Adr) :
    ExactRelFuncSound dp ca (nonpayable withdrawFrom) := by
  apply ExactRelFuncSound.nonpayable dp ca
  intro sevm s r h_target h_code ih run
  change Func.Run ((weth10 dp).main :: weth10Aux) sevm s withdrawFrom r at run
  have h_core_lookup :
      ((weth10 dp).main :: weth10Aux)[withdrawFromCoreSlot]? =
        some withdrawFromCore := by
    simp [weth10, weth10Aux, withdrawFromCoreSlot]
  obtain ⟨sc, hcore, h_silent, h_bal, h_code_s_sc⟩ :=
    of_run_spendCallerAllowanceThen dp 2 withdrawFromCoreSlot
      withdrawFromCore h_core_lookup (by
        simpa only [withdrawFrom] using run)
  have h_code_sc :
      some (sc.getCode ca).toList = Prog.compile (weth10 dp) := by
    rw [← h_target, ← h_code_s_sc, h_target]
    exact h_code
  have h_core := withdrawFromCore_exactRelFuncSound dp ca
    h_target h_code_sc ih hcore
  unfold FlashExactRel at h_core ⊢
  exact h_core.trans (by
    simpa only [h_target] using h_silent.2)

private theorem approve_flashStable (dp : DeployParams) :
    FlashStable dp (nonpayable approve) := by
  apply FlashStable.nonpayable dp
  intro sevm s r run
  exact (approve_storage_silent run).2

private theorem depositTo_flashStable (dp : DeployParams) :
    FlashStable dp depositTo := by
  intro sevm s r run
  exact (depositTo_storage run).choose_spec.2

private theorem deposit_flashStable (dp : DeployParams) :
    FlashStable dp deposit := by
  intro sevm s r run
  exact (mintCaller_storage (by simpa only [deposit] using run)).2

private theorem receiveEther_flashStable (dp : DeployParams) :
    FlashStable dp receiveEther := by
  intro sevm s r run
  exact (mintCaller_storage (by simpa only [receiveEther] using run)).2

private theorem flashFee_flashStable (dp : DeployParams) :
    FlashStable dp (nonpayable flashFee) := by
  apply FlashStable.nonpayable dp
  intro sevm s r run
  have hs := (run_flashFee_observations_eq dp run).1
  rw [← congrFun hs sevm.currentTarget]

/-- The exact relation is discharged for every one of the 27 Blanc
selector leaves. -/
theorem weth10Funcs_exactRelFuncSound
    (dp : DeployParams) (ca : Adr) :
    ∀ p ∈ weth10Funcs dp, ExactRelFuncSound dp ca p.2 := by
  intro p hp
  simp only [weth10Funcs, List.mem_cons] at hp
  rcases hp with
    (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | hnil)
  · exact ExactRelFuncSound.of_stable dp ca
      (FlashStable.nonpayable dp (FlashStable.of_inv dp (by func_inv)))
  · exact ExactRelFuncSound.of_stable dp ca (approve_flashStable dp)
  · exact ExactRelFuncSound.of_stable dp ca
      (FlashStable.nonpayable dp (FlashStable.of_inv dp (by func_inv)))
  · exact withdrawTo_exactRelFuncSound dp ca
  · exact transferFrom_exactRelFuncSound dp ca
  · exact withdraw_exactRelFuncSound dp ca
  · exact ExactRelFuncSound.of_stable dp ca
      (FlashStable.nonpayable dp (FlashStable.of_inv dp (by func_inv)))
  · exact ExactRelFuncSound.of_stable dp ca
      (FlashStable.nonpayable dp (FlashStable.of_inv dp (by func_inv)))
  · apply ExactRelFuncSound.of_stable dp ca
    apply FlashStable.nonpayable dp
    apply FlashStable.of_inv dp
    unfold domainSeparator returnDeployWord pushDeployWord
    func_inv
  · exact transferAndCall_exactRelFuncSound dp ca
  · exact ExactRelFuncSound.nonpayable dp ca
      (flashLoan_exactRelFuncSound dp ca)
  · exact depositToAndCall_exactRelFuncSound dp ca
  · exact ExactRelFuncSound.of_stable dp ca
      (FlashStable.nonpayable dp (FlashStable.of_inv dp (by func_inv)))
  · exact ExactRelFuncSound.of_stable dp ca
      (FlashStable.nonpayable dp (FlashStable.of_inv dp (by func_inv)))
  · exact ExactRelFuncSound.of_stable dp ca
      (FlashStable.nonpayable dp (FlashStable.of_inv dp (by func_inv)))
  · exact ExactRelFuncSound.of_stable dp ca
      (FlashStable.nonpayable dp (FlashStable.of_inv dp (by func_inv)))
  · exact ExactRelFuncSound.of_stable dp ca
      (FlashStable.nonpayable dp (FlashStable.of_inv dp (by func_inv)))
  · exact withdrawFrom_exactRelFuncSound dp ca
  · exact ExactRelFuncSound.of_stable dp ca
      (FlashStable.nonpayable dp (FlashStable.of_inv dp (by func_inv)))
  · exact transfer_exactRelFuncSound dp ca
  · exact ExactRelFuncSound.of_stable dp ca (depositTo_flashStable dp)
  · exact approveAndCall_exactRelFuncSound dp ca
  · apply ExactRelFuncSound.of_stable dp ca
    apply FlashStable.nonpayable dp
    apply FlashStable.of_inv dp
    unfold deploymentChainId returnDeployWord pushDeployWord
    func_inv
  · exact ExactRelFuncSound.of_stable dp ca (deposit_flashStable dp)
  · exact permit_exactRelFuncSound dp ca
  · exact ExactRelFuncSound.of_stable dp ca (flashFee_flashStable dp)
  · exact ExactRelFuncSound.of_stable dp ca
      (FlashStable.nonpayable dp (FlashStable.of_inv dp (by func_inv)))
  · simp at hnil

theorem receiveEther_exactRelFuncSound
    (dp : DeployParams) (ca : Adr) :
    ExactRelFuncSound dp ca receiveEther :=
  ExactRelFuncSound.of_stable dp ca (receiveEther_flashStable dp)

/-- Every successful compiled WETH10 execution preserves its entry flash
counter, at every depth and without a recursive premise. -/
theorem flashExactDepth
    (dp : DeployParams) (ca : Adr) (depth : Nat) :
    FlashExactDepth dp ca depth := by
  intro pc sevm pre post run h_depth h_at
  exact flashExactSpecs_lift dp ca
    (flashExactSpecsRel_of_prog_run dp ca
      (weth10Funcs_exactRelFuncSound dp ca)
      (receiveEther_exactRelFuncSound dp ca))
    pc sevm pre post run h_at

private theorem maxUint112_toNat : maxUint112.toNat = maxFlashMinted := by
  unfold maxUint112 maxFlashMinted
  apply B256.toNat_toB256_of_lt
  omega

/-- The successful flash-loan prefix establishes the backed temporary-mint
state and exposes the borrower call. -/
theorem of_flashLoan_toCall_backed
    (dp : DeployParams) {sevm : Sevm} {s r : Devm}
    (h_inv : Stor.Weth10Inv
      (Devm.getStor s sevm.currentTarget) 0
      (Devm.getBal s sevm.currentTarget))
    (h_code : some (s.getCode sevm.currentTarget).toList =
      Prog.compile (weth10 dp))
    (h_side : SumNof s.getBal)
    (run : Func.Run ((weth10 dp).main :: weth10Aux) sevm s flashLoan r) :
    ∃ (recipient : Adr) (sc : Devm) (g inputSize base : B256),
      B256.Nof base (Sevm.argWord sevm 2) ∧
      Stor.Weth10Inv
        (Devm.getStor sc sevm.currentTarget) 0
        (Devm.getBal sc sevm.currentTarget) ∧
      some (sc.getCode sevm.currentTarget).toList =
        Prog.compile (weth10 dp) ∧
      SumNof sc.getBal ∧
      (Devm.getStor sc sevm.currentTarget).get flashMintedSlot =
        base + Sevm.argWord sevm 2 ∧
      (g :: recipient.toB256 :: (0 : B256) :: callbackArgsOffset ::
        inputSize :: 0 :: 0 ::
        [Sevm.argWord sevm 2, recipient.toB256] <<+ sc.stack) ∧
      Func.Run ((weth10 dp).main :: weth10Aux) sevm sc
        flashLoanFromCall r := by
  rcases of_flashLoan_toCall dp run with
    ⟨recipient, sc, g, inputSize, base, hbase, hamount, htotal,
      hinc, hflash, hcodeSc, hbalSc, hpCall, htail⟩
  have h_base_cap : base.toNat ≤ maxFlashMinted := by
    rw [hbase]
    exact h_inv.2
  have h_amount_cap := B256.toNat_le_toNat hamount
  have h_nof : B256.Nof base (Sevm.argWord sevm 2) := by
    rw [maxUint112_toNat] at h_amount_cap
    unfold B256.Nof
    unfold maxFlashMinted at h_base_cap h_amount_cap
    omega
  have h_total_cap :
      (base + Sevm.argWord sevm 2).toNat ≤ maxFlashMinted := by
    have h := B256.toNat_le_toNat htotal
    rw [maxUint112_toNat] at h
    exact h
  have h_total_cap' :
      base.toNat + (Sevm.argWord sevm 2).toNat ≤ maxFlashMinted := by
    rw [← B256.toNat_add_eq_of_nof _ _ h_nof]
    exact h_total_cap
  have h_inv_sc : Stor.Weth10Inv
      (Devm.getStor sc sevm.currentTarget) 0
      (Devm.getBal sc sevm.currentTarget) := by
    rw [← congrFun hbalSc sevm.currentTarget]
    unfold Stor.Weth10Inv at h_inv ⊢
    rw [hflash, B256.toNat_add_eq_of_nof _ _ h_nof]
    rcases h_inv with ⟨h_backed, h_cap⟩
    rw [← hbase] at h_backed
    constructor
    · have h_sum : balSum (Devm.getStor sc sevm.currentTarget) ≤
          balSum (Devm.getStor s sevm.currentTarget) +
            (Sevm.argWord sevm 2).toNat := by
        simpa only [balSum] using sum_increase_le hinc
      simp only [B256.toNat_zero, Nat.add_zero] at h_backed ⊢
      omega
    · exact h_total_cap'
  have h_code_sc :
      some (sc.getCode sevm.currentTarget).toList =
        Prog.compile (weth10 dp) := by
    rw [← congrFun hcodeSc sevm.currentTarget]
    exact h_code
  have h_side_sc : SumNof sc.getBal := by
    rw [← hbalSc]
    exact h_side
  exact ⟨recipient, sc, g, inputSize, base, h_nof, h_inv_sc,
    h_code_sc, h_side_sc, hflash, hpCall, htail⟩

/-- The borrower call and fixed decoder carry backing and the exact temporary
counter to the `flashSettle` entry. -/
theorem of_flashLoanFromCall_backed
    (dp : DeployParams) (ca : Adr) {base : B256}
    {sevm : Sevm} {sc r : Devm} {g inputSize : B256}
    {recipient : Adr}
    (h_target : sevm.currentTarget = ca)
    (ih : Exec.InvDepth sevm.depth ca (weth10 dp)
      ((backedSpec weth10 dp).PreWf ca) ((backedSpec weth10 dp).Post ca))
    (h_inv_sc : Stor.Weth10Inv
      (Devm.getStor sc ca) 0 (Devm.getBal sc ca))
    (h_code_sc : some (sc.getCode ca).toList =
      Prog.compile (weth10 dp))
    (h_side_sc : SumNof sc.getBal)
    (hflash : (Devm.getStor sc ca).get flashMintedSlot =
      base + Sevm.argWord sevm 2)
    (hpCall :
      (g :: recipient.toB256 :: (0 : B256) :: callbackArgsOffset ::
        inputSize :: 0 :: 0 ::
        [Sevm.argWord sevm 2, recipient.toB256] <<+ sc.stack))
    (run : Func.Run ((weth10 dp).main :: weth10Aux) sevm sc
      flashLoanFromCall r) :
    ∃ ss,
      Func.Run ((weth10 dp).main :: weth10Aux) sevm ss flashSettle r ∧
      Stor.Weth10Inv (Devm.getStor ss ca) 0 (Devm.getBal ss ca) ∧
      SumNof ss.getBal ∧
      (Devm.getStor ss ca).get flashMintedSlot =
        base + Sevm.argWord sevm 2 := by
  subst ca
  rcases of_run_flashLoanFromCall dp run with
    ⟨sf, ss, hcall, hsettle, hstorSfSs, hbalSfSs⟩
  have h_inv_call : Stor.Weth10Inv
      (Devm.getStor sc sevm.currentTarget) 0
      (Devm.getBal sc sevm.currentTarget - 0) := by
    rw [b256_sub_zero]
    exact h_inv_sc
  have h_post_call := backedPost_of_value_call dp sevm.currentTarget
    rfl ih hpCall h_code_sc h_side_sc (b256_zero_le _)
      h_inv_call hcall
  have h_call_exact := flashExactRel_of_value_call dp sevm.currentTarget
    rfl (flashExactDepth dp sevm.currentTarget sevm.depth)
      hpCall h_code_sc hcall
  have h_inv_ss : Stor.Weth10Inv
      (Devm.getStor ss sevm.currentTarget) 0
      (Devm.getBal ss sevm.currentTarget) := by
    rw [← congrFun hstorSfSs sevm.currentTarget,
      ← congrFun hbalSfSs sevm.currentTarget]
    exact h_post_call.inv
  have h_flash_ss :
      (Devm.getStor ss sevm.currentTarget).get flashMintedSlot =
        base + Sevm.argWord sevm 2 := by
    unfold FlashExactRel at h_call_exact
    exact (congrArg (fun st => st.get flashMintedSlot)
      (congrFun hstorSfSs sevm.currentTarget).symm).trans
        (h_call_exact.trans hflash)
  have h_side_ss : SumNof ss.getBal := by
    rw [← hbalSfSs]
    exact h_post_call.side
  exact ⟨ss, hsettle, h_inv_ss, h_side_ss, h_flash_ss⟩

/-- Final flash settlement consumes the exact temporary counter and preserves
the frozen backing invariant. -/
theorem backedPost_of_flashSettle
    (dp : DeployParams) (ca : Adr) {base : B256}
    {sevm : Sevm} {s r : Devm}
    (h_target : sevm.currentTarget = ca)
    (h_value : sevm.value = 0)
    (h_nof : B256.Nof base (Sevm.argWord sevm 2))
    (h_inv : Stor.Weth10Inv (Devm.getStor s ca) 0 (Devm.getBal s ca))
    (h_side : SumNof s.getBal)
    (hflash : (Devm.getStor s ca).get flashMintedSlot =
      base + Sevm.argWord sevm 2)
    (run : Func.Run ((weth10 dp).main :: weth10Aux) sevm s
      flashSettle r) :
    (backedSpec weth10 dp).Post ca sevm r := by
  subst ca
  have h_floor_ss : Stor.FlashFloor
      (base + Sevm.argWord sevm 2)
      (Devm.getStor s sevm.currentTarget) := by
    refine ⟨h_inv.2, ?_⟩
    rw [hflash]
  have h_inv' : Stor.Weth10Inv
      (Devm.getStor s sevm.currentTarget) sevm.value
      (Devm.getBal s sevm.currentTarget) := by
    rw [h_value]
    exact h_inv
  have h_settled :
      Stor.Weth10Inv
          (Devm.getStor r sevm.currentTarget) sevm.value
          (Devm.getBal r sevm.currentTarget) ∧
        Stor.FlashFloor base
          (Devm.getStor r sevm.currentTarget) :=
    flashSettle_backed_floor (dp := dp) (base := base)
      (sevm := sevm) (s := s) (r := r)
      h_nof h_floor_ss h_inv' run
  have hbalSsR : Devm.getBal s = Devm.getBal r :=
    flashSettle_balance dp run
  have h_settled_inv : Stor.Weth10Inv
      (Devm.getStor r sevm.currentTarget) 0
      (Devm.getBal r sevm.currentTarget) := by
    rw [← h_value]
    exact h_settled.1
  refine ⟨?_, h_settled_inv⟩
  rw [← hbalSsR]
  exact h_side

/-- Blanc's nonpayable `flashLoan` selector preserves the frozen backing
invariant. -/
theorem backedSpec_flashLoan_funcSound
    (dp : DeployParams) (ca : Adr) :
    (backedSpec weth10 dp).FuncSoundNoMem ca weth10Aux
      (nonpayable flashLoan) := by
  intro sevm s r h_target h_pre ih run
  subst ca
  obtain ⟨mid, h_value, h_state_mid, h_body⟩ :=
    run_body_of_run_nonpayable run
  have h_pre_mid := h_pre.state_eq h_state_mid.symm
  have h_inv_mid : Stor.Weth10Inv
      (Devm.getStor mid sevm.currentTarget) 0
      (Devm.getBal mid sevm.currentTarget) := by
    have h := h_pre_mid.inv.1 rfl
    change Stor.Weth10Inv
      (Devm.getStor mid sevm.currentTarget) sevm.value
      (Devm.getBal mid sevm.currentTarget) at h
    simpa only [h_value] using h
  rcases of_flashLoan_toCall_backed dp h_inv_mid h_pre_mid.code
      h_pre_mid.side h_body with
    ⟨recipient, sc, g, inputSize, base, h_nof, h_inv_sc,
      h_code_sc, h_side_sc, hflash, hpCall, htail⟩
  rcases of_flashLoanFromCall_backed dp sevm.currentTarget
      rfl ih h_inv_sc h_code_sc h_side_sc hflash hpCall htail with
    ⟨ss, hsettle, h_inv_ss, h_side_ss, h_flash_ss⟩
  exact backedPost_of_flashSettle dp sevm.currentTarget
    rfl h_value h_nof h_inv_ss h_side_ss h_flash_ss hsettle

/-- Every one of the 27 Blanc selector leaves preserves the frozen backing
invariant. -/
theorem weth10Funcs_backed_funcSound
    (dp : DeployParams) (ca : Adr) :
    ∀ p ∈ weth10Funcs dp,
      (backedSpec weth10 dp).FuncSoundNoMem ca weth10Aux p.2 := by
  intro p hp
  simp only [weth10Funcs, List.mem_cons] at hp
  rcases hp with
    (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | hnil)
  · exact backedSpec_name_funcSound dp ca
  · exact backedSpec_approve_funcSound dp ca
  · exact backedSpec_totalSupply_funcSound dp ca
  · exact backedSpec_withdrawTo_funcSound dp ca
  · exact backedSpec_transferFrom_funcSound dp ca
  · exact backedSpec_withdraw_funcSound dp ca
  · exact backedSpec_permitTypehash_funcSound dp ca
  · exact backedSpec_decimals_funcSound dp ca
  · exact backedSpec_domainSeparator_funcSound dp ca
  · exact backedSpec_transferAndCall_funcSound dp ca
  · exact backedSpec_flashLoan_funcSound dp ca
  · exact backedSpec_depositToAndCall_funcSound dp ca
  · exact backedSpec_maxFlashLoan_funcSound dp ca
  · exact backedSpec_balanceOf_funcSound dp ca
  · exact backedSpec_nonces_funcSound dp ca
  · exact backedSpec_callbackSuccess_funcSound dp ca
  · exact backedSpec_flashMinted_funcSound dp ca
  · exact backedSpec_withdrawFrom_funcSound dp ca
  · exact backedSpec_symbol_funcSound dp ca
  · exact backedSpec_transfer_funcSound dp ca
  · exact backedSpec_depositTo_funcSound dp ca
  · exact backedSpec_approveAndCall_funcSound dp ca
  · exact backedSpec_deploymentChainId_funcSound dp ca
  · exact backedSpec_deposit_funcSound dp ca
  · exact backedSpec_permit_funcSound dp ca
  · exact backedSpec_flashFee_funcSound dp ca
  · exact backedSpec_allowance_funcSound dp ca
  · simp at hnil

/-- Premise-free receive-aware soundness of the compiled Blanc WETH10 program
for the frozen backing invariant.  Premise-free in both senses: no unproved
selector obligation is left over, and the obligation itself carries no memory
premise. -/
theorem backedSpec_soundNoMem (dp : DeployParams) (ca : Adr) :
    (backedSpec weth10 dp).SoundNoMem ca :=
  backedSpec_sound_of_funcSound_all dp ca
    (weth10Funcs_backed_funcSound dp ca)

/-- The memory-carrying obligation, for any consumer that wants it: dropping a
premise WETH10 never used. -/
theorem backedSpec_sound (dp : DeployParams) (ca : Adr) :
    (backedSpec weth10 dp).Sound ca :=
  ContractSpec.SoundNoMem.sound (backedSpec_soundNoMem dp ca)

/-- Every successful WETH10 subexecution preserves the frozen backing
invariant, at arbitrary depth and through receive dispatch — whatever the
machine's memory holds on entry. -/
theorem backedSpec_preservesNoMem (dp : DeployParams) (ca : Adr) :
    (backedSpec weth10 dp).PreservesNoMem ca :=
  backedSpec_preserves_of_funcSound_all dp ca
    (weth10Funcs_backed_funcSound dp ca)

/-- The memory-carrying form the message-, transaction- and block-level rungs
consume. -/
theorem backedSpec_preserves (dp : DeployParams) (ca : Adr) :
    (backedSpec weth10 dp).Preserves ca :=
  ContractSpec.PreservesNoMem.preserves (backedSpec_preservesNoMem dp ca)

end Weth10

end Blanc
