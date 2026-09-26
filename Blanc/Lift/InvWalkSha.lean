import Blanc.Lift.InvWalkWorld
import Blanc.Lift.PackedShaCovered
import Blanc.StaticPrecompileMessage

namespace Blanc.Lift

open Jaune

/-! ## Hash-set identities

Copies of `ForwardSha256.lean`'s private helpers (making those public would rebuild every
importer of that module); hoist them there at the next edit of that file. -/

private theorem rawInsertIfNew_eq_self_of_contains
    {α : Type} {β : α → Type} [BEq α] [Hashable α]
    (m : Std.DHashMap.Internal.Raw₀ α β) (a : α) (b : β a)
    (h : Std.DHashMap.Internal.Raw₀.contains m a = true) :
    Std.DHashMap.Internal.Raw₀.insertIfNew m a b = m := by
  rcases m with ⟨⟨size, buckets⟩, hm⟩
  unfold Std.DHashMap.Internal.Raw₀.contains at h
  unfold Std.DHashMap.Internal.Raw₀.insertIfNew
  dsimp only at h ⊢
  split
  · rfl
  · contradiction

private theorem rawInsertListIfNew_eq_self_of_forall_contains
    {α : Type} {β : α → Type} [BEq α] [Hashable α]
    (m : Std.DHashMap.Internal.Raw₀ α β)
    (l : List ((a : α) × β a))
    (h : ∀ p ∈ l,
      Std.DHashMap.Internal.Raw₀.contains m p.1 = true) :
    Std.DHashMap.Internal.Raw₀.insertListIfNewₘ m l = m := by
  induction l with
  | nil => rfl
  | cons hd tl ih =>
      rw [Std.DHashMap.Internal.Raw₀.insertListIfNewₘ,
        rawInsertIfNew_eq_self_of_contains m hd.1 hd.2
          (h hd (by simp))]
      exact ih (fun p hp => h p (by simp [hp]))

private theorem rawUnion_self
    {α : Type} {β : α → Type}
    [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α]
    (m : Std.DHashMap.Internal.Raw₀ α β)
    (hwf : Std.DHashMap.Internal.Raw.WFImp m.1) :
    Std.DHashMap.Internal.Raw₀.union m m = m := by
  unfold Std.DHashMap.Internal.Raw₀.union
  rw [ite_eq_left_iff.mpr (fun h => absurd (le_refl _) h)]
  rw [Std.DHashMap.Internal.Raw₀.insertManyIfNew_eq_insertListIfNewₘ_toListModel]
  apply rawInsertListIfNew_eq_self_of_forall_contains
  intro p hp
  rw [Std.DHashMap.Internal.Raw₀.contains_eq_containsKey hwf]
  exact Std.Internal.List.containsKey_of_mem hp

private theorem hashSet_union_self
    {α : Type} [BEq α] [Hashable α] [EquivBEq α]
    [LawfulHashable α] (m : Std.HashSet α) :
    m.union m = m := by
  rcases m with ⟨⟨⟨raw, wf⟩⟩⟩
  have hu := congrArg Subtype.val
    (rawUnion_self ⟨raw, wf.size_buckets_pos⟩
      (Std.DHashMap.Internal.Raw.WF.out wf))
  unfold Std.HashSet.union Std.HashMap.union Std.DHashMap.union
  congr 3

private theorem hashSet_insert_eq_self_of_mem
    {α : Type} [BEq α] [Hashable α]
    (m : Std.HashSet α) (a : α) (h : a ∈ m) :
    m.insert a = m := by
  rcases m with ⟨⟨⟨raw, wf⟩⟩⟩
  change Std.DHashMap.Internal.Raw₀.contains
    ⟨raw, wf.size_buckets_pos⟩ a = true at h
  have hi := congrArg Subtype.val
    (rawInsertIfNew_eq_self_of_contains
      ⟨raw, wf.size_buckets_pos⟩ a () h)
  simp only [Std.HashSet.insert, Std.HashMap.insertIfNew,
    Std.DHashMap.insertIfNew]
  congr 3

/-- Warming a warm address changes nothing. -/
theorem addAccessedAddress_eq_self_of_mem {d : Devm} {a : Adr} (h : a ∈ d.accessedAddresses) :
    addAccessedAddress d a = d := by
  have h' := hashSet_insert_eq_self_of_mem _ _ h
  rcases d with ⟨m, v, w⟩
  simp only [Devm.accessedAddresses] at h'
  simp only [addAccessedAddress, liftMachMetaPure, Meta.addAccessedAddress, h']

/-- A clean 64-byte SHA-256 child keeps the parent's access sets and logs nothing (the
meta-field companion of `output_of_processMessage_sha256_64_clean`). -/
theorem meta_of_processMessage_sha256_64_clean
    {sevm : Sevm} {parent child : Devm} {gas : Nat} {calldata : Bytes}
    {code : ByteArray} {xl : Xlot}
    (hpre : decide (sevm.benvStat.rules.isPrecomp 2) = true)
    (hlen : calldata.length = 64)
    (hpm : ProcessMessage
      (callMsg sevm parent gas 0 sevm.currentTarget 2 2 true true
        calldata code false) xl (.ok child))
    (hclean : child.error.isSome = false) (hfork : CoveredFork sevm.benvStat.fork) :
    child.accessedAddresses = parent.accessedAddresses ∧
      child.accessedStorageKeys = parent.accessedStorageKeys ∧ child.logs = [] := by
  have hgas : 84 ≤ gas :=
    gasSha25664_le_of_processMessage_clean hpre hlen hpm hclean
  obtain ⟨r0, hbody, hset⟩ := ProcessMessage.iff_body.mp hpm
  unfold FrameBody at hbody
  rcases hbt :
      (callMsg sevm parent gas 0 sevm.currentTarget 2 2 true true
        calldata code false).benvAfterTransfer with e | benv <;>
    rw [hbt] at hbody
  · rw [hbody.2] at hset
    unfold processMessage.settle at hset
    cases hset
  · obtain ⟨st_mid, hsub, hbenv⟩ := of_benvAfterTransfer rfl hbt
    subst benv
    have hca :
        ((callMsg sevm parent gas 0 sevm.currentTarget 2 2 true true
          calldata code false).withBenv (((callMsg sevm parent gas 0 sevm.currentTarget 2 2 true
            true calldata code false).benv.withState st_mid).addBal 2 0)).codeAddress =
          some 2 := rfl
    rcases of_executeCode_someCode hca hbody with hpc | hinterp
    · have hexec := hpc.2.2
      rw [executePrecomp_two_of_length_64 (by
        change calldata.length = 64
        exact hlen) (by
        change 84 ≤ gas
        exact hgas)] at hexec
      simp only [applyPrecompResult, executeCode.handleErrorWith] at hexec
      split at hexec <;>
        simp only [executeCode.handleError,
          executeCode.handleErrorAmsterdam] at hexec
      all_goals
        rw [← hexec] at hset
        unfold processMessage.settle at hset
        simp only [bind, Except.bind, Option.isSome] at hset
        injection hset with hchild
        subst child
        refine ⟨rfl, rfl, ?_⟩
        have hsg := hfork.rules_stateGas_none
        simp only [initEvm, initDevm, Devm.withOutput_logs]
        dsimp only [Devm.withGasLeft, Devm.setMach, Devm.logs, liftMachPure]
        split
        · rfl
        · rename_i heq
          exact absurd (heq.symm.trans hsg) (by simp)
    · exact False.elim (hinterp.1 hpre)

/-- The successful resume of a call: access sets merged, error kept. -/
theorem Resume.call_ok_meta {parent child sf : Devm} {oi os : Nat}
    (h : (Resume.call parent oi os).run (.ok child) = .ok sf)
    (hc : child.error.isSome = false) :
    sf.accessedAddresses = parent.accessedAddresses.union child.accessedAddresses ∧
      sf.accessedStorageKeys = parent.accessedStorageKeys.union child.accessedStorageKeys ∧
      sf.error = parent.error := by
  unfold Resume.run liftToExecution at h
  simp only [bind, Except.bind, hc] at h
  rcases hp : (incorporateChildOnSuccess parent child child.output).push 1 with _ | d' <;>
    rw [hp] at h
  · cases h
  · injection h with h
    subst h
    have := Devm.eq_of_push_ok hp
    subst this
    exact ⟨rfl, rfl, rfl⟩

/-- **`STATICCALL` of the SHA-256 precompile, inverted.**  Over a 64-byte input window at
`ii` and a 32-byte output window at `oi`, with address 2 warm, undelegated and a precompile of
a covered fork: a successful step either pushed the failure flag `0`, or
pushed `1` over a base `b'` that `ShaCallPost`-extends `b` with the digest as return data,
with the digest written over the (extended) output window. -/
theorem ri_staticcall_sha {sevm : Sevm} {b : Devm} {S : List B256} {M : Mem} {G : Nat}
    {g ii oi : B256} {d : Devm}
    (hnodeleg : getDelegatedCodeAddress (b.getCode 2) = none)
    (hwarm : (2 : Adr) ∈ b.accessedAddresses)
    (hpre : decide (sevm.benvStat.rules.isPrecomp 2) = true)
    (hfork : CoveredFork sevm.benvStat.fork)
    (h : Ninst.Run sevm (St b (g :: 2 :: ii :: 64 :: oi :: 32 :: S) M G) (.exec .staticcall) d) :
    d.stack = 0 :: S ∨
      ∃ b' G', ShaCallPost b b' (Bytes.sha256 (M.read ii.toNat 64).1).toBytes ∧
        d = St b' (1 :: S) ((M.extends [⟨ii.toNat, 64⟩, ⟨oi.toNat, 32⟩]).write oi.toNat
          (Bytes.sha256 (M.read ii.toNat 64).1).toBytes) G' := by
  rcases h with ⟨xl, h_fill, pc, h_run⟩
  simp only [Ninst.StepRun, Ninst.step_exec, XStep.run_toStep, Xinst.step,
    Bind.bind, Except.bind, hfork.rules_stateGas_none] at h_run
  rw [show (St b (g :: 2 :: ii :: 64 :: oi :: 32 :: S) M G).pop =
    .ok (g, St b (2 :: ii :: 64 :: oi :: 32 :: S) M G) from rfl] at h_run
  simp only at h_run
  rw [show (St b (2 :: ii :: 64 :: oi :: 32 :: S) M G).popToAdr =
    .ok ((2 : Adr), St b (ii :: 64 :: oi :: 32 :: S) M G) from rfl] at h_run
  simp only at h_run
  rw [show (St b (ii :: 64 :: oi :: 32 :: S) M G).popToNat =
    .ok (ii.toNat, St b (64 :: oi :: 32 :: S) M G) from rfl] at h_run
  simp only at h_run
  rw [show (St b (64 :: oi :: 32 :: S) M G).popToNat =
    .ok (64, St b (oi :: 32 :: S) M G) from rfl] at h_run
  simp only at h_run
  rw [show (St b (oi :: 32 :: S) M G).popToNat =
    .ok (oi.toNat, St b (32 :: S) M G) from rfl] at h_run
  simp only at h_run
  rw [show (St b (32 :: S) M G).popToNat =
    .ok (32, St b S M G) from rfl] at h_run
  simp only at h_run
  have hAD : sevm.benvStat.rules.gas.accessDelegation (addAccessedAddress (St b S M G) 2) 2 =
      ⟨false, 2, b.getCode 2, 0, addAccessedAddress (St b S M G) 2⟩ := by
    unfold GasSchedule.accessDelegation
    simp only [show (addAccessedAddress (St b S M G) 2).state.getCode 2 = b.getCode 2 from rfl,
      hnodeleg]
  have hA : addAccessedAddress (St b S M G) 2 = St b S M G :=
    addAccessedAddress_eq_self_of_mem hwarm
  rw [hAD, hA] at h_run
  simp only at h_run
  split at h_run
  · cases XStep.run_ofExcept_error h_run
  rename_i v hcharge
  by_cases hdepth : sevm.depth = 0
  · left
    simp only [pure, Except.pure, XStep.ofExcept, genericCall.step, hdepth, ite_true] at h_run
    obtain ⟨Gv, rfl⟩ : ∃ Gv, v = St b S M Gv :=
      ⟨_, Devm.eq_setGas_of_burn (Devm.burn_of_chargeGas hcharge)⟩
    simp only [bind, Except.bind] at h_run
    split at h_run
    · simp [XStep.Run] at h_run
    · rename_i d' hp
      split at hp
      · cases hp
      · rename_i d'' hpush
        cases hp
        simp only [XStep.Run, Except.ok.injEq] at h_run
        rw [h_run.2, Devm.eq_of_push_ok hpush]
        rfl
  simp only [pure, Except.pure, XStep.ofExcept, genericCall.step, hdepth, ite_false] at h_run
  simp only [XStep.Run] at h_run
  rcases h_run with ⟨ex', run_pm₀, h_split⟩
  obtain ⟨Gv, rfl⟩ : ∃ Gv, v = St b S M Gv :=
    ⟨_, Devm.eq_setGas_of_burn (Devm.burn_of_chargeGas hcharge)⟩
  rcases ex' with err' | child
  · cases Resume.call_run_error h_split.symm
  have hsplit := h_split.symm
  have hstk := Resume.call_stack_flag hsplit
  by_cases herr : child.error.isSome
  · left
    simp only [herr, ↓reduceIte] at hstk
    exact hstk
  right
  have hclean : child.error.isSome = false := by simpa using herr
  simp only [hclean, Bool.false_eq_true, ↓reduceIte] at hstk
  set P := ((St b S M Gv).memExtends [(ii.toNat, 64), (oi.toNat, 32)]).withReturnData [] with hP
  have hcd : Array.sliceD P.memory.data ii.toNat 64 0 = (M.read ii.toNat 64).1 := rfl
  rw [hcd] at run_pm₀
  obtain ⟨gas, pm⟩ : ∃ gas, ProcessMessage (callMsg sevm P gas 0 sevm.currentTarget 2 2 true true
      (M.read ii.toNat 64).1 (b.getCode 2) false) xl (.ok child) :=
    ⟨_, by simpa [ProcessMessage] using run_pm₀⟩
  have hlen : (M.read ii.toNat 64).1.length = 64 := by
    rw [← hcd, Array.sliceD_eq_map, List.length_map, List.length_range]
  have hout := output_of_processMessage_sha256_64_clean hpre hlen pm hclean
  have hstor := stor_of_processMessage_staticPrecomp hpre pm
  have hcode := code_of_processMessage_staticPrecomp hpre pm
  obtain ⟨hca, hck, hcl⟩ := meta_of_processMessage_sha256_64_clean hpre hlen pm hclean hfork
  obtain ⟨hra, hrk, hre⟩ := Resume.call_ok_meta hsplit hclean
  have hlogs := Resume.call_logs hsplit
  simp only [hclean, Bool.false_eq_true, ↓reduceIte, hcl, List.append_nil] at hlogs
  have hmem := Resume.call_memory hsplit
  rw [hout, List.take_of_length_le (by rw [B256.length_toBytes])] at hmem
  have hst := Resume.call_state hsplit
  refine ⟨d, d.gasLeft, ⟨fun a => ?_, fun a => ?_, ?_, ?_, hlogs, (Resume.call_output hsplit).trans rfl, hre,
    (Resume.call_returnData hsplit).trans hout⟩, St.self hstk hmem⟩
  · exact (getStor_eq_of_state_eq hst a).trans (hstor a)
  · exact (getCode_eq_of_state_eq hst a).trans (hcode a)
  · rw [hra, hca, hashSet_union_self]; rfl
  · rw [hrk, hck, hashSet_union_self]; rfl

/-! ## The solc packed-SHA site, inverted -/

section Copy

variable {fs : List SFunc} {sevm : Sevm} {C : List Nat} {b : Devm} {r : Seg}
  {R : List B256} {M : Mem} {G : Nat} {e0 e1 r0 r1 : UInt8} {k : Nat} {X T : SFunc}

/-- **One copy pass, inverted** (`len ≥ 32`): the pass copies the source word to `d` and
enters entry `k` with the operands advanced. -/
theorem ric_mcpy_iter {s d l n : Nat} (hl : 32 ≤ l) (hl' : l < 2 ^ 256) (hs : M.size = n)
    (hn : n % 32 = 0) (hsrc : s + 32 ≤ n) (hsl : s + 64 < 2 ^ 256) (hdl : d + 64 < 2 ^ 256)
    (hk : fs[k]? = some T) (hkC : k ∉ C)
    (run : SFunc.RunCut fs sevm C (St b (Nat.toB256 s :: Nat.toB256 d :: Nat.toB256 l :: R) M G)
      (mcpyTree e0 e1 r0 r1 k X) r) :
    ∃ G', SFunc.RunCut fs sevm C
      (St b (Nat.toB256 (s + 32) :: Nat.toB256 (d + 32) :: Nat.toB256 (l - 32) :: R)
        (M.write d (M.read s 32).1) G') T r := by
  unfold mcpyTree mcpyBody at run
  obtain ⟨G1, run⟩ := ric_dest run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G2, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G3, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G4, rfl⟩ := ri_lt s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G5, rfl⟩ := ri_push s1
  have hlt : B256.ltCheck (Nat.toB256 l) (Bytes.toB256 [0x20]) = 0 := by
    rw [show Bytes.toB256 [0x20] = Nat.toB256 32 by decide, lt_toB256 hl' (by norm_num)]
    simp [show ¬ l < 32 by omega]
  rw [hlt] at run
  rcases ric_branch run with ⟨-, G6, run⟩ | ⟨hw, -⟩
  swap; · exact absurd rfl hw
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G7, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G8, rfl⟩ := ri_mload s1
  rw [toNat_toB256' (by omega), read_covered hs hn hsrc] at run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G9, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G10, rfl⟩ := ri_mstore s1
  rw [toNat_toB256' (by omega), toBytes_read] at run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G11, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G12, rfl⟩ := ri_swap rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G13, rfl⟩ := ri_swap rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G14, rfl⟩ := ri_add s1
  rw [add_minus32 hl hl'] at run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G15, rfl⟩ := ri_swap rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G16, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G17, rfl⟩ := ri_swap rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G18, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G19, rfl⟩ := ri_add s1
  rw [push20_add (by omega)] at run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G20, rfl⟩ := ri_swap rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G21, rfl⟩ := ri_add s1
  rw [push20_add (by omega)] at run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G22, rfl⟩ := ri_push s1
  exact ric_jump hkC hk run

/-- **The copy's exit test, inverted** (`len < 32`): control passes to the exit `X`. -/
theorem ric_mcpy_exit {s d l : Nat} (hl : l < 32)
    (run : SFunc.RunCut fs sevm C (St b (Nat.toB256 s :: Nat.toB256 d :: Nat.toB256 l :: R) M G)
      (mcpyTree e0 e1 r0 r1 k X) r) :
    ∃ G', SFunc.RunCut fs sevm C
      (St b (Nat.toB256 s :: Nat.toB256 d :: Nat.toB256 l :: R) M G') X r := by
  unfold mcpyTree at run
  obtain ⟨G1, run⟩ := ric_dest run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G2, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G3, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G4, rfl⟩ := ri_lt s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G5, rfl⟩ := ri_push s1
  have hlt : B256.ltCheck (Nat.toB256 l) (Bytes.toB256 [0x20]) = 1 := by
    rw [show Bytes.toB256 [0x20] = Nat.toB256 32 by decide, lt_toB256 (by omega) (by norm_num)]
    simp [hl]
  rw [hlt] at run
  rcases ric_branch run with ⟨hw, -⟩ | ⟨-, G6, run⟩
  · exact absurd hw (by decide)
  exact ⟨_, run⟩

/-- **The merge with nothing left over, inverted**: the destination word is read (extending
memory) and stored back; control passes to `K` with `0x20` on the stack. -/
theorem ric_merge0 {s d n : Nat} {K : SFunc} (hs : M.size = n) (hn : n % 32 = 0)
    (hsrc : s + 32 ≤ n) (hsl : s < 2 ^ 256) (hdl : d < 2 ^ 256)
    (run : SFunc.RunCut fs sevm C (St b (Nat.toB256 s :: Nat.toB256 d :: Nat.toB256 0 :: R) M G)
      (mergeTree K) r) :
    ∃ G', SFunc.RunCut fs sevm C
      (St b (Bytes.toB256 [0x20] :: R) ((M.read d 32).2.write d (M.read d 32).1) G') K r := by
  unfold mergeTree at run
  obtain ⟨G1, run⟩ := ric_dest run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G2, rfl⟩ := ri_mload s1
  rw [toNat_toB256' hsl, read_covered hs hn hsrc] at run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G3, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G4, rfl⟩ := ri_mload s1
  rw [toNat_toB256' hdl] at run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G5, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G6, rfl⟩ := ri_swap rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G7, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G8, rfl⟩ := ri_sub s1
  rw [show Bytes.toB256 [32] - Nat.toB256 0 = Nat.toB256 32 by decide] at run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G9, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G10, rfl⟩ := ri_exp s1
  rw [bexp_256_32] at run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G11, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G12, rfl⟩ := ri_add s1
  rw [show Bytes.toB256 onesPush + 0 = B256.max from ones_add_zero] at run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G13, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G14, rfl⟩ := ri_not s1
  rw [B256.not_max] at run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G15, rfl⟩ := ri_swap rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G16, rfl⟩ := ri_swap rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G17, rfl⟩ := ri_and s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G18, rfl⟩ := ri_swap rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G19, rfl⟩ := ri_and s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G20, rfl⟩ := ri_or s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G21, rfl⟩ := ri_swap rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G22, rfl⟩ := ri_mstore s1
  simp only [b256_and_zero, b256_max_and, b256_or_zero, toNat_toB256' hdl, toBytes_read] at run
  exact ⟨_, run⟩

/-- **The precompile call and its two checks, inverted.**  From the stack the merge leaves,
with the free pointer `d` (word-aligned, past the scratch words) and memory covering the input
window: the call succeeded (its failure arm is `noOk`; the size check cannot fail), the digest of the 64 bytes at `d`
was written at `d`, and control passes to `T` with the returned size and `d` on the stack. -/
theorem ric_shaCall {img : Bytes} {n d : Nat} {x1 x3 x4 : B256} {c0 c1 v0 v1 : UInt8}
    {fail1 fail2 : SFunc}
    (hf1 : fail1.noOk = true)
    (hwf : Mem.Wf M) (hr : Mem.Reads M img) (hs : M.size = n) (hn : n % 32 = 0)
    (hdn : d + 64 ≤ n) (hd96 : 96 ≤ d) (hd32 : d % 32 = 0) (hdb : d + 64 < 2 ^ 256)
    (hfp : img.sliceD 64 32 0 = (Nat.toB256 d).toBytes)
    (hnodeleg : getDelegatedCodeAddress (b.getCode 2) = none)
    (hwarm : (2 : Adr) ∈ b.accessedAddresses)
    (hpre : decide (sevm.benvStat.rules.isPrecomp 2) = true)
    (hfork : CoveredFork sevm.benvStat.fork)
    (run : SFunc.RunCut fs sevm C
      (St b (Bytes.toB256 [0x20] :: Nat.toB256 64 :: x1 :: Nat.toB256 d :: x3 :: x4 :: 2 :: R)
        M G) (shaCallTree c0 c1 v0 v1 fail1 fail2 T) r) :
    ∃ b' G', ShaCallPost b b' (Bytes.sha256 (M.read d 64).1).toBytes ∧
      SFunc.RunCut fs sevm C (St b' (Nat.toB256 32 :: Nat.toB256 d :: R)
        (M.write d (Bytes.sha256 (M.read d 64).1).toBytes) G') T r := by
  have h40 : (Bytes.toB256 [0x40]).toNat = 64 := by decide
  have hd : (Nat.toB256 d).toNat = d := toNat_toB256' (by omega)
  unfold shaCallTree at run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G1, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G2, rfl⟩ := ri_mload s1
  rw [h40, read_word hr 64 hfp, read_covered hs hn (by omega)] at run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G3, rfl⟩ := ri_swap rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G4, rfl⟩ := ri_swap rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G5, rfl⟩ := ri_swap rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G6, rfl⟩ := ri_add s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G7, rfl⟩ := ri_swap rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G8, rfl⟩ := ri_pop s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G9, rfl⟩ := ri_swap rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G10, rfl⟩ := ri_swap rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G11, rfl⟩ := ri_pop s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G12, rfl⟩ := ri_pop s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G13, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G14, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G15, rfl⟩ := ri_sub s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G16, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G17, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨w, G18, rfl⟩ := ri_gas s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  have e64 : Nat.toB256 d + Nat.toB256 64 - Nat.toB256 d = 64 := by
    rw [toB256_add_toB256 hdb, toB256_sub_toB256 (by omega) hdb, show d + 64 - d = 64 by omega]
    decide
  have e32 : Bytes.toB256 [32] = 32 := by decide
  have s1' : Ninst.Run sevm (St b (w :: 2 :: Nat.toB256 d :: 64 :: Nat.toB256 d :: 32 ::
      (Nat.toB256 d + Nat.toB256 64) :: 2 :: R) M G18) (.exec .staticcall) d1 := by
    rw [← e64, ← e32]; exact s1
  clear s1
  have hcov : M.extends [⟨d, 64⟩, ⟨d, 32⟩] = M :=
    Mem.extends_covered (by rw [hs]; exact memExtsSize_two_covered hn (by omega) (by omega))
  rcases ri_staticcall_sha hnodeleg hwarm hpre hfork s1' with hfail | ⟨b', G19, hpost, rfl⟩
  · -- the failure flag: the first check's arm
    rw [St.self hfail rfl] at run
    obtain ⟨d2, s2, run⟩ := ric_next run; obtain ⟨G20, rfl⟩ := ri_iszero s2
    obtain ⟨d2, s2, run⟩ := ric_next run; obtain ⟨G21, rfl⟩ := ri_dup rfl s2
    obtain ⟨d2, s2, run⟩ := ric_next run; obtain ⟨G22, rfl⟩ := ri_iszero s2
    obtain ⟨d2, s2, run⟩ := ric_next run; obtain ⟨G23, rfl⟩ := ri_push s2
    rw [show B256.eqCheck (B256.eqCheck (0 : B256) 0) 0 = 0 by decide] at run
    rcases ric_branch run with ⟨-, G24, run⟩ | ⟨hw, -⟩
    · exact (run.false_of_noOk hf1).elim
    · exact absurd rfl hw
  rw [hd, hcov] at run
  rw [hd] at hpost
  set sha := (Bytes.sha256 (M.read d 64).1).toBytes with hsha
  have hr' : Mem.Reads (M.write d sha) (Bytes.writeAt img d sha) := hr.write hwf d sha
  have hs' : (M.write d sha).size = n := by
    rw [hsha, Mem.size_write_word_aligned (by omega) hd32]; omega
  have hfp' : (Bytes.writeAt img d sha).sliceD 64 32 0 = (Nat.toB256 d).toBytes := by
    rw [Bytes.sliceD_writeAt_before _ _ _ _ _ (by omega), hfp]
  obtain ⟨d2, s2, run⟩ := ric_next run; obtain ⟨G20, rfl⟩ := ri_iszero s2
  obtain ⟨d2, s2, run⟩ := ric_next run; obtain ⟨G21, rfl⟩ := ri_dup rfl s2
  obtain ⟨d2, s2, run⟩ := ric_next run; obtain ⟨G22, rfl⟩ := ri_iszero s2
  obtain ⟨d2, s2, run⟩ := ric_next run; obtain ⟨G23, rfl⟩ := ri_push s2
  rw [show B256.eqCheck (B256.eqCheck (1 : B256) 0) 0 = 1 by decide] at run
  rcases ric_branch run with ⟨hw, -⟩ | ⟨-, G24, run⟩
  · exact absurd hw (by decide)
  obtain ⟨G25, run⟩ := ric_dest run
  obtain ⟨d2, s2, run⟩ := ric_next run; obtain ⟨G26, rfl⟩ := ri_pop s2
  obtain ⟨d2, s2, run⟩ := ric_next run; obtain ⟨G27, rfl⟩ := ri_pop s2
  obtain ⟨d2, s2, run⟩ := ric_next run; obtain ⟨G28, rfl⟩ := ri_pop s2
  obtain ⟨d2, s2, run⟩ := ric_next run; obtain ⟨G29, rfl⟩ := ri_push s2
  obtain ⟨d2, s2, run⟩ := ric_next run; obtain ⟨G30, rfl⟩ := ri_mload s2
  rw [h40, read_word hr' 64 hfp', read_covered hs' hn (by omega)] at run
  obtain ⟨d2, s2, run⟩ := ric_next run; obtain ⟨G31, rfl⟩ := ri_returndatasize s2
  rw [hpost.returnData, B256.length_toBytes] at run
  obtain ⟨d2, s2, run⟩ := ric_next run; obtain ⟨G32, rfl⟩ := ri_push s2
  obtain ⟨d2, s2, run⟩ := ric_next run; obtain ⟨G33, rfl⟩ := ri_dup rfl s2
  obtain ⟨d2, s2, run⟩ := ric_next run; obtain ⟨G34, rfl⟩ := ri_lt s2
  obtain ⟨d2, s2, run⟩ := ric_next run; obtain ⟨G35, rfl⟩ := ri_iszero s2
  obtain ⟨d2, s2, run⟩ := ric_next run; obtain ⟨G36, rfl⟩ := ri_push s2
  have hlt : B256.ltCheck (Nat.toB256 32) (Bytes.toB256 [0x20]) = 0 := by
    rw [show Bytes.toB256 [0x20] = Nat.toB256 32 by decide, lt_toB256 (by norm_num) (by norm_num)]
    simp
  rw [hlt, show B256.eqCheck (0 : B256) 0 = 1 by decide] at run
  rcases ric_branch run with ⟨hw, -⟩ | ⟨-, G37, run⟩
  · exact absurd hw (by decide)
  exact ⟨b', G37, hpost, run⟩

/-- **Copy, merge and call, inverted** (the converse of `copy_sha_gen`): from the copy loop's
head with the two words `w1`, `w2` at `s` and `s + 0x20` to be copied to the free pointer
`d = s + 0x40`, every successful cut run makes the two copy passes, the merge and the
precompile call, and continues with `T` over a base that `ShaCallPost`-extends `b` with the
digest `sha256 (w1 ‖ w2)`, memory reading as `shaImg img d w1 w2` of size `max n (d + 0x60)`,
and the returned size and `d` on the stack.  The head's own exit `X` is never taken. -/
theorem ric_copy_sha {img : Bytes} {n s d : Nat} {w1 w2 x1 x3 x4 : B256}
    {c0 c1 v0 v1 : UInt8} {fail1 fail2 : SFunc}
    (hk : fs[k]? = some (mcpyTree e0 e1 r0 r1 k
      (mergeTree (shaCallTree c0 c1 v0 v1 fail1 fail2 T))))
    (hkC : k ∉ C) (hf1 : fail1.noOk = true)
    (hwf : Mem.Wf M) (hr : Mem.Reads M img) (hs : M.size = n) (hn : n % 32 = 0)
    (hdn : d ≤ n) (hsd : s + 64 = d) (hd32 : d % 32 = 0) (hd96 : 96 ≤ s)
    (hdb : n + 1000 < 2 ^ 256) (hfp : img.sliceD 64 32 0 = (Nat.toB256 d).toBytes)
    (hw1 : img.sliceD s 32 0 = w1.toBytes) (hw2 : img.sliceD (s + 32) 32 0 = w2.toBytes)
    (hnodeleg : getDelegatedCodeAddress (b.getCode 2) = none)
    (hwarm : (2 : Adr) ∈ b.accessedAddresses)
    (hpre : decide (sevm.benvStat.rules.isPrecomp 2) = true)
    (hfork : CoveredFork sevm.benvStat.fork)
    (run : SFunc.RunCut fs sevm C
      (St b (Nat.toB256 s :: Nat.toB256 d :: Nat.toB256 64 :: Nat.toB256 64 :: x1 ::
        Nat.toB256 d :: x3 :: x4 :: 2 :: R) M G) (mcpyTree e0 e1 r0 r1 k X) r) :
    ∃ b' M' G', ShaCallPost b b' (Bytes.sha256 (w1.toBytes ++ w2.toBytes)).toBytes ∧
      Mem.Wf M' ∧ Mem.Reads M' (shaImg img d w1 w2) ∧ M'.size = max n (d + 96) ∧
      SFunc.RunCut fs sevm C (St b' (Nat.toB256 32 :: Nat.toB256 d :: R) M' G') T r := by
  set n1 := max n (d + 32) with hn1
  set n2 := max n (d + 64) with hn2
  set n3 := max n (d + 96) with hn3
  have hw1' : (M.read s 32).1 = w1.toBytes := by rw [hr.read, hw1]
  set M5 := M.write d (M.read s 32).1 with hM5
  have hwf5 : Mem.Wf M5 := hwf.write _ _
  have hr5 : Mem.Reads M5 (Bytes.writeAt img d w1.toBytes) := by
    rw [hM5, hw1']; exact hr.write hwf _ _
  have hs5 : M5.size = n1 := by
    rw [hM5, hw1', Mem.size_write_word_aligned (by omega) (by omega)]; omega
  have hw2' : (M5.read (s + 32) 32).1 = w2.toBytes := by
    rw [hr5.read, Bytes.sliceD_writeAt_before _ _ _ _ _ (by omega), hw2]
  set M6 := M5.write (d + 32) (M5.read (s + 32) 32).1 with hM6
  have hwf6 : Mem.Wf M6 := hwf5.write _ _
  have hr6 : Mem.Reads M6 (copyImg2 img d w1 w2) := by
    rw [hM6, hw2']; exact hr5.write hwf5 _ _
  have hs6 : M6.size = n2 := by
    rw [hM6, hw2', Mem.size_write_word_aligned (by omega) (by omega)]; omega
  set M7 := (M6.read (d + 64) 32).2.write (d + 64) (M6.read (d + 64) 32).1 with hM7
  have hs6' : (M6.read (d + 64) 32).2.size = n3 := by
    rw [read_ext_size hs6 (by omega) (by omega)]; omega
  have hwf7 : Mem.Wf M7 := (hwf6.extend _ _).write _ _
  have hr7 : Mem.Reads M7 (copyImg2 img d w1 w2) := by
    rw [hM7, hr6.read]
    exact Mem.Reads.write_self (hwf6.extend _ _) (hr6.extend _ _) _
  have hs7 : M7.size = n3 := by
    rw [hM7, ← toBytes_read, Mem.size_write_word_aligned (by omega) (by omega), hs6']; omega
  have hin : (M7.read d 64).1 = w1.toBytes ++ w2.toBytes := by
    rw [hr7.read, copyImg2_input]
  have hw7 : (copyImg2 img d w1 w2).sliceD 64 32 0 = (Nat.toB256 d).toBytes := by
    rw [copyImg2_word64 (by omega), hfp]
  -- the two copy passes and the exit test
  obtain ⟨G1, run⟩ := ric_mcpy_iter (s := s) (d := d) (l := 64) (n := n) (by omega) (by omega)
    hs hn (by omega) (by omega) (by omega) hk hkC run
  rw [show (64 : Nat) - 32 = 32 from rfl] at run
  obtain ⟨G2, run⟩ := ric_mcpy_iter (s := s + 32) (d := d + 32) (l := 32) (n := n1) (by omega)
    (by omega) hs5 (by omega) (by omega) (by omega) (by omega) hk hkC run
  rw [show (32 : Nat) - 32 = 0 from rfl, show s + 32 + 32 = s + 64 by omega,
    show d + 32 + 32 = d + 64 by omega] at run
  obtain ⟨G3, run⟩ := ric_mcpy_exit (s := s + 64) (d := d + 64) (l := 0) (by omega) run
  -- the merge
  obtain ⟨G4, run⟩ := ric_merge0 (s := s + 64) (d := d + 64) (n := n2) hs6 (by omega) (by omega)
    (by omega) (by omega) run
  -- the call
  obtain ⟨b', G5, hpost, run⟩ := ric_shaCall (img := copyImg2 img d w1 w2) (n := n3) hf1 hwf7
    hr7 hs7 (by omega) (by omega) (by omega) hd32 (by omega) hw7 hnodeleg hwarm hpre hfork
    run
  rw [hin] at hpost run
  exact ⟨b', _, G5, hpost, hwf7.write _ _, hr7.write hwf7 d _,
    by rw [Mem.size_write_word_aligned (by omega) (by omega), hs7]; omega, run⟩

end Copy

/-! ## Added for s-sha -/

section Pack

variable {fs : List SFunc} {sevm : Sevm} {C : List Nat} {b : Devm} {r : Seg}
  {R : List B256} {M : Mem} {G : Nat} {e0 e1 r0 r1 : UInt8} {k : Nat} {X T : SFunc}

/-- **Pack two words, copy, merge and call, inverted** (the converse of `packed_sha_pair`):
from `bw :: a :: 2` over the free pointer `f`, every successful cut run stores `a`, `bw` at
`f + 0x20`, `f + 0x40` with the length at `f` and the free pointer `f + 0x60`, then makes the
copy site of `ric_copy_sha`, continuing with `T` over the digest `sha256 (a ‖ bw)`. -/
theorem ric_pack_sha {img : Bytes} {n f : Nat} {a bw : B256}
    {c0 c1 v0 v1 : UInt8} {fail1 fail2 : SFunc}
    (hk : fs[k]? = some (mcpyTree e0 e1 r0 r1 k
      (mergeTree (shaCallTree c0 c1 v0 v1 fail1 fail2 T))))
    (hkC : k ∉ C) (hf1 : fail1.noOk = true)
    (hwf : Mem.Wf M) (hr : Mem.Reads M img) (hs : M.size = n) (hn : n % 32 = 0)
    (h96 : 96 ≤ n) (hnf : n ≤ f + 96) (hf32 : f % 32 = 0) (hf96 : 96 ≤ f)
    (hfb : f + 2000 < 2 ^ 256) (hfp : img.sliceD 64 32 0 = (Nat.toB256 f).toBytes)
    (hnodeleg : getDelegatedCodeAddress (b.getCode 2) = none)
    (hwarm : (2 : Adr) ∈ b.accessedAddresses)
    (hpre : decide (sevm.benvStat.rules.isPrecomp 2) = true)
    (hfork : CoveredFork sevm.benvStat.fork)
    (run : SFunc.RunCut fs sevm C (St b (bw :: a :: 2 :: R) M G)
      (pack2Tree (mcpyTree e0 e1 r0 r1 k X)) r) :
    ∃ b' M' G', ShaCallPost b b' (Bytes.sha256 (a.toBytes ++ bw.toBytes)).toBytes ∧
      Mem.Wf M' ∧ Mem.Reads M' (shaImg (packImg img f a bw) (f + 96) a bw) ∧
      M'.size = f + 192 ∧
      SFunc.RunCut fs sevm C (St b' (Nat.toB256 32 :: Nat.toB256 (f + 96) :: R) M' G') T r := by
  have h40 : (Bytes.toB256 [0x40]).toNat = 64 := by decide
  have tf : (Nat.toB256 f).toNat = f := toNat_toB256' (by omega)
  have tf32 : (Nat.toB256 (f + 32)).toNat = f + 32 := toNat_toB256' (by omega)
  have tf64 : (Nat.toB256 (f + 64)).toNat = f + 64 := toNat_toB256' (by omega)
  set M1 := M.write (f + 32) a.toBytes with hM1
  set M2 := M1.write (f + 64) bw.toBytes with hM2
  set M3 := M2.write f (Nat.toB256 64).toBytes with hM3
  set M4 := M3.write 64 (Nat.toB256 (f + 96)).toBytes with hM4
  have hs1 : M1.size = max n (f + 64) := by
    rw [hM1, Mem.size_write_word_aligned (by omega) (by omega)]; omega
  have hs2 : M2.size = f + 96 := by
    rw [hM2, Mem.size_write_word_aligned (by omega) (by omega)]; omega
  have hs3 : M3.size = f + 96 := by
    rw [hM3, Mem.size_write_word_aligned (by omega) (by omega)]; omega
  have hs4 : M4.size = f + 96 := by
    rw [hM4, Mem.size_write_word_aligned (by omega) (by omega)]; omega
  have hwf1 : Mem.Wf M1 := hwf.write _ _
  have hwf2 : Mem.Wf M2 := hwf1.write _ _
  have hwf3 : Mem.Wf M3 := hwf2.write _ _
  have hwf4 : Mem.Wf M4 := hwf3.write _ _
  have hr1 := hr.write hwf (f + 32) a.toBytes
  have hr2 := hr1.write hwf1 (f + 64) bw.toBytes
  have hr3 := hr2.write hwf2 f (Nat.toB256 64).toBytes
  have hr4 : Mem.Reads M4 (packImg img f a bw) := hr3.write hwf3 64 _
  have hfp2 : (Bytes.writeAt (Bytes.writeAt img (f + 32) a.toBytes) (f + 64)
      bw.toBytes).sliceD 64 32 0 = (Nat.toB256 f).toBytes := by
    rw [Bytes.sliceD_writeAt_before _ _ _ _ _ (by omega),
      Bytes.sliceD_writeAt_before _ _ _ _ _ (by omega), hfp]
  unfold pack2Tree at run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_mload s1
  rw [h40, read_word hr 64 hfp, read_covered hs hn (by omega)] at run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_val (w := Nat.toB256 (f + 32))
    (push20_add (by omega)) (ri_add s1)
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_mstore s1
  rw [tf32, ← hM1] at run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_val (w := Nat.toB256 (f + 64))
    (push20_add' rfl (by omega)) (ri_add s1)
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_mstore s1
  rw [tf64, ← hM2] at run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_val (w := Nat.toB256 (f + 96))
    (push20_add' rfl (by omega)) (ri_add s1)
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_swap rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_pop s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_pop s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_pop s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_mload s1
  rw [h40, read_word hr2 64 hfp2, read_covered hs2 (by omega) (by omega)] at run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_val (w := Nat.toB256 96)
    (sub_toB256' (by omega) (by omega) (by omega)) (ri_sub s1)
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_val (w := Nat.toB256 64)
    (by decide) (ri_sub s1)
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_mstore s1
  rw [tf, ← hM3] at run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_swap rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_mstore s1
  rw [h40, ← hM4] at run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_mload s1
  rw [h40, read_word hr4 64 (packImg_word64 hf96), read_covered hs4 (by omega) (by omega)] at run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_mload s1
  rw [tf, read_word hr4 f (packImg_len hf96), read_covered hs4 (by omega) (by omega)] at run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_swap rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_val (w := Nat.toB256 (f + 32))
    (push20_add (by omega)) (ri_add s1)
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_swap rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_dup rfl s1
  obtain ⟨b', M', G', hpost, hwf', hr', hs', run⟩ := ric_copy_sha (s := f + 32) (d := f + 96)
    (n := f + 96) hk hkC hf1 hwf4 hr4 hs4 (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (packImg_word64 hf96) (packImg_a hf96)
    (by rw [show f + 32 + 32 = f + 64 by omega]; exact packImg_b hf96)
    hnodeleg hwarm hpre hfork run
  exact ⟨b', M', G', hpost, hwf', hr', by rw [hs']; omega, run⟩

end Pack

end Blanc.Lift
