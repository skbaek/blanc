import Blanc.Lift.Curve3Crv.SafeBodies

/-!
# Safety: the six views, inverted

The four word views (`totalSupply`, `decimals`, `balanceOf`, `allowance`: one shared tail
`safe_wordTail`) and the two string views (`name`, `symbol`: one loop-and-join shape,
`safe_strView` over `safe_strJoin`), each inverted from the entry state `entrySt sevm b G` like the
writing bodies in `SafeBodies.lean`, and concluding the model's exact return bytes.
-/

namespace Blanc.Lift.Curve3Crv

open Jaune

section

variable {sevm : Sevm} {b : Devm}

local notation "stor₀" => Devm.getStor b sevm.currentTarget

/-! ### The word views, inverted -/

/-- The tail every word view ends with, inverted: `SLOAD` the key, `mstore(0, word)`,
`return(0, 32)` returns exactly the stored word and keeps storage and logs. -/
private theorem safe_wordTail (hfork : CoveredFork sevm.benvStat.fork) {M : Mem} (hwf : Mem.Wf M)
    {k : B256} {G : Nat} {post : Devm}
    (run : SFunc.RunCut prog sevm [] (St b [k] M G)
      (.next (.reg .sload) (.next (.push [0x00] (by decide)) (.next (.reg .mstore)
        (.next (.push [0x20] (by decide)) (.next (.push [0x00] (by decide)) (.last .return_))))))
      (.done (.halted post))) :
    Lands sevm b post (stor₀, [], some (b.getStorVal sevm.currentTarget k).toBytes) := by
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G1, rfl⟩ := ri_sload hfork s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G2, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G3, rfl⟩ := ri_mstore s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G4, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G5, rfl⟩ := ri_push s1
  cases run with
  | last hl =>
    obtain ⟨hout, hstor, hlogs⟩ := ri_return hl
    have h0 : (Bytes.toB256 [0x00]).toNat = 0 := by decide
    have h32 : (Bytes.toB256 [0x20]).toNat = 32 := by decide
    refine ⟨?_, fun a _ => ?_, ?_, fun o ho => ?_, fun h => by cases h⟩
    · rw [hstor, afterSload_getStor]
    · rw [hstor, afterSload_getStor]
    · rw [hlogs, afterSload_logs, List.append_nil]
    · cases ho
      rw [hout, h0, h32, Mem.read_write_word_of_wf hwf]

-- SEGMENT: safeWordViews (the four word views, inverted)
/-- `totalSupply()`, inverted. -/
theorem safe_totalSupply (hfork : CoveredFork sevm.benvStat.fork) :
    SafeBody sevm b t_0240_c0 (rawTotalSupply sevm stor₀) := by
  intro G post run
  have run := run.cut
  unfold entrySt at run
  obtain ⟨hv, G1, run⟩ := ric_vyNonpayable (h := 0x02) (l := 0x4a) (fail := t_0246_c0)
    (by decide) run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G2, rfl⟩ := ri_push s1
  exact ⟨_, by simp only [rawTotalSupply, hv, ite_true]; rfl,
    safe_wordTail hfork (vyMem_wf Mem.wf_empty _) run⟩

/-- `decimals()`, inverted. -/
theorem safe_decimals (hfork : CoveredFork sevm.benvStat.fork) :
    SafeBody sevm b t_087e_c0 (rawDecimals sevm stor₀) := by
  intro G post run
  have run := run.cut
  unfold entrySt at run
  obtain ⟨hv, G1, run⟩ := ric_vyNonpayable (h := 0x08) (l := 0x88) (fail := t_0884_c0)
    (by decide) run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G2, rfl⟩ := ri_push s1
  exact ⟨_, by simp only [rawDecimals, hv, ite_true]; rfl,
    safe_wordTail hfork (vyMem_wf Mem.wf_empty _) run⟩

/-- `balanceOf(a)`, inverted. -/
theorem safe_balanceOf (hfork : CoveredFork sevm.benvStat.fork) :
    SafeBody sevm b t_08a5_c0 (rawBalanceOf sevm stor₀) := by
  intro G post run
  have hM := vyMem_empty_size (Sevm.dataWord sevm 0)
  have run := run.cut
  unfold entrySt at run
  obtain ⟨hv, G1, run⟩ := ric_vyNonpayable (h := 0x08) (l := 0xaf) (fail := t_08ab_c0)
    (by decide) run
  obtain ⟨ha, G2, run⟩ := ric_vyAddrArg (p := 0x04) (h := 0x08) (l := 0xc0) (fail := t_08bc_c0)
    (by decide) (vyMem_reads Mem.wf_empty Mem.reads_empty _) (vyImg_clamps _ _) (by rw [hM])
    (by rw [hM]; omega) run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G3, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G4, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G5, rfl⟩ := ri_calldataload s1
  obtain ⟨G6, run⟩ := ric_vySlot run
  have ha' : (Sevm.argWord sevm 0).toNat < 2 ^ 160 := ha
  exact ⟨_, by simp only [rawBalanceOf, hv, ha', and_self, ite_true]; rfl,
    safe_wordTail hfork (vySlotMem_wf (vyMem_wf Mem.wf_empty _) _ _) run⟩

/-- `allowance(o, p)`, inverted. -/
theorem safe_allowance (hfork : CoveredFork sevm.benvStat.fork) :
    SafeBody sevm b t_0267_c0 (rawAllowance sevm stor₀) := by
  intro G post run
  have hM := vyMem_empty_size (Sevm.dataWord sevm 0)
  have run := run.cut
  unfold entrySt at run
  obtain ⟨hv, G1, run⟩ := ric_vyNonpayable (h := 0x02) (l := 0x71) (fail := t_026d_c0)
    (by decide) run
  obtain ⟨ho, G2, run⟩ := ric_vyAddrArg (p := 0x04) (h := 0x02) (l := 0x82) (fail := t_027e_c0)
    (by decide) (vyMem_reads Mem.wf_empty Mem.reads_empty _) (vyImg_clamps _ _) (by rw [hM])
    (by rw [hM]; omega) run
  obtain ⟨hq, G3, run⟩ := ric_vyAddrArg (p := 0x24) (h := 0x02) (l := 0x94) (fail := t_0290_c0)
    (by decide) (vyMem_reads Mem.wf_empty Mem.reads_empty _) (vyImg_clamps _ _) (by rw [hM])
    (by rw [hM]; omega) run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G4, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G5, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G6, rfl⟩ := ri_calldataload s1
  obtain ⟨G7, run⟩ := ric_vySlot run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G8, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G9, rfl⟩ := ri_calldataload s1
  obtain ⟨G10, run⟩ := ric_vySlot run
  have ho' : (Sevm.argWord sevm 0).toNat < 2 ^ 160 := ho
  have hq4 : Sevm.dataWord sevm (Bytes.toB256 [0x24]) = Sevm.argWord sevm 1 := by
    show Sevm.dataWord sevm _ = Sevm.dataWord sevm _
    congr 1
  have hq' : (Sevm.argWord sevm 1).toNat < 2 ^ 160 := by rw [← hq4]; exact hq
  rw [hq4] at run
  exact ⟨_, by simp only [rawAllowance, hv, ho', hq', and_self, ite_true]; rfl,
    safe_wordTail hfork (vySlotMem_wf (vySlotMem_wf (vyMem_wf Mem.wf_empty _) _ _) _ _) run⟩

end


/-! ### The string views, inverted -/

section StrViews

variable {sevm : Sevm} {b : Devm}

local notation "stor₀" => Devm.getStor b sevm.currentTarget

/-- The string views' join, inverted: over a memory whose word at `0x180` is the length and
whose bytes at `0x1a0` are the string, a successful halt returns exactly `abiString` of the
string and keeps storage and logs. -/
theorem safe_strJoin (hcd : sevm.data.length < 2 ^ 256) {M : Mem} {sz : Nat} {Lw : B256}
    {str : Bytes} {a1 a2 a3 a4 a5 a6 : B256} (hwf : Mem.Wf M) (hs : M.size = sz)
    (hsz32 : sz % 32 = 0) (hsz : 0x1a0 + ceil32 Lw.toNat ≤ sz) (hL : Lw.toNat ≤ 64)
    (hLw : (M.read 0x180 32).1 = Lw.toBytes) (hstr : (M.read 0x1a0 Lw.toNat).1 = str)
    (hlen : str.length = Lw.toNat) (bb : Devm) {G : Nat} {post : Devm}
    (run : SFunc.RunCut prog sevm [] (St bb [a1, a2, a3, a4, a5, a6] M G) t_0774_c5
      (.done (.halted post))) :
    (∀ a, Devm.getStor post a = Devm.getStor bb a) ∧ post.logs = bb.logs ∧
      post.output = abiString str := by
  unfold t_0774_c5 at run
  obtain ⟨G1, run⟩ := ric_dest run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G2, rfl⟩ := ri_pop s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G3, rfl⟩ := ri_pop s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G4, rfl⟩ := ri_pop s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G5, rfl⟩ := ri_pop s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G6, rfl⟩ := ri_pop s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G7, rfl⟩ := ri_pop s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G8, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G9, rfl⟩ := ri_mload s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G10, rfl⟩ := ri_dup (n := 0) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G11, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G12, rfl⟩ := ri_add s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G13, rfl⟩ := ri_dup (n := 1) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G14, rfl⟩ := ri_dup (n := 2) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G15, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G16, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G17, rfl⟩ := ri_dup (n := 2) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G18, rfl⟩ := ri_sub s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G19, rfl⟩ := ri_mod s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G20, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G21, rfl⟩ := ri_dup (n := 2) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G22, rfl⟩ := ri_add s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G23, rfl⟩ := ri_sub s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G24, rfl⟩ := ri_swap (n := 0) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G25, rfl⟩ := ri_pop s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G26, rfl⟩ := ri_sub s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G27, rfl⟩ := ri_calldatasize s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G28, rfl⟩ := ri_dup (n := 2) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G29, rfl⟩ := ri_calldatacopy s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G30, rfl⟩ := ri_pop s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G31, rfl⟩ := ri_pop s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G32, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G33, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G34, rfl⟩ := ri_mstore s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G35, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G36, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G37, rfl⟩ := ri_mload s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G38, rfl⟩ := ri_add s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G39, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G40, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G41, rfl⟩ := ri_dup (n := 2) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G42, rfl⟩ := ri_sub s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G43, rfl⟩ := ri_mod s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G44, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G45, rfl⟩ := ri_dup (n := 2) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G46, rfl⟩ := ri_add s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G47, rfl⟩ := ri_sub s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G48, rfl⟩ := ri_swap (n := 0) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G49, rfl⟩ := ri_pop s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G50, rfl⟩ := ri_push s1
  cases run with
  | last hl =>
  obtain ⟨hout, hstor, hlogs⟩ := ri_return hl
  refine ⟨hstor, hlogs, ?_⟩
  rw [hout]
  set L := Lw.toNat with hLdef
  have hc := ceil32_eq L
  have h180 : (Bytes.toB256 [0x01, 0x80]).toNat = 384 := by decide
  have h160 : (Bytes.toB256 [0x01, 0x60]).toNat = 352 := by decide
  rw [h180, read_covered hs hsz32 (by omega), hLw, B256.toB256_toBytes]
  set z := ceil32 L - L with hzdef
  have hz : z = 31 - (L + 31) % 32 := by omega
  have hLt : L < 2 ^ 256 := by omega
  have h1a0 : (Bytes.toB256 [0x01, 0xa0]).toNat = 416 := by decide
  have hX : (Bytes.toB256 [0x01, 0xa0] + Lw).toNat = 416 + L := by
    rw [B256.toNat_add, h1a0, Nat.lo_eq_of_lt (by omega)]
  have h1 : (Bytes.toB256 [0x01]).toNat = 1 := by decide
  have h20 : (Bytes.toB256 [0x20]).toNat = 32 := by decide
  have h1f : (Bytes.toB256 [0x1f]).toNat = 31 := by decide
  have h40 : (Bytes.toB256 [0x40]).toNat = 64 := by decide
  have hmod : ∀ x : B256, x.toNat < 2 ^ 256 → ((x - Bytes.toB256 [0x01]) % Bytes.toB256 [0x20]).toNat
      = (x.toNat + 31) % 32 := by
    intro x _
    rw [B256.toNat_mod (by decide), B256.toNat_sub, h1, h20, Nat.lo]
    omega
  have hm : ((Lw - Bytes.toB256 [0x01]) % Bytes.toB256 [0x20]).toNat = (L + 31) % 32 :=
    hmod Lw (B256.toNat_lt Lw)
  have hL31 : (Lw + Bytes.toB256 [0x1f]).toNat = L + 31 := by
    rw [B256.toNat_add, h1f, Nat.lo_eq_of_lt (by omega)]
  have hsub1 : (Lw + Bytes.toB256 [0x1f] - (Lw - Bytes.toB256 [0x01]) % Bytes.toB256 [0x20]).toNat
      = L + 31 - (L + 31) % 32 := by
    rw [B256.toNat_sub_eq_of_le _ _ (by rw [B256.le_iff_toNat_le_toNat, hm, hL31]; omega), hm, hL31]
  have hzB : (Lw + Bytes.toB256 [0x1f] - (Lw - Bytes.toB256 [0x01]) % Bytes.toB256 [0x20] -
      Lw).toNat = z := by
    rw [B256.toNat_sub_eq_of_le _ _ (by rw [B256.le_iff_toNat_le_toNat, hsub1]; omega), hsub1]
    omega
  rw [hX, hzB, B256.toNat_toB256_of_lt hcd, sliceD_data_end, h160]
  have hA : (Lw + Bytes.toB256 [0x40]).toNat = L + 64 := by
    rw [B256.toNat_add, h40, Nat.lo_eq_of_lt (by omega)]
  have hm' : ((Lw + Bytes.toB256 [0x40] - Bytes.toB256 [0x01]) % Bytes.toB256 [0x20]).toNat =
      (L + 63) % 32 := by
    rw [hmod _ (B256.toNat_lt _), hA]; omega
  have hA31 : (Lw + Bytes.toB256 [0x40] + Bytes.toB256 [0x1f]).toNat = L + 95 := by
    rw [B256.toNat_add, h1f, hA, Nat.lo_eq_of_lt (by omega)]
  have hret : (Lw + Bytes.toB256 [0x40] + Bytes.toB256 [0x1f] -
      (Lw + Bytes.toB256 [0x40] - Bytes.toB256 [0x01]) % Bytes.toB256 [0x20]).toNat =
      64 + ceil32 L := by
    rw [B256.toNat_sub_eq_of_le _ _ (by rw [B256.le_iff_toNat_le_toNat, hm', hA31]; omega), hm',
      hA31]
    omega
  -- the memory
  have hrd : ∀ i n, (M.read i n).1 = M.data.toList.sliceD i n 0 := (Mem.reads_data M).read
  set M1 := M.write (416 + L) (List.replicate z 0)
  have hM1s : M1.size = sz := by
    rw [Mem.size_write_of_le (by rw [List.length_replicate, hs]; omega), hs]
  have hwf1 : Mem.Wf M1 := hwf.write _ _
  have hr1 : Mem.Reads M1 (Bytes.writeAt M.data.toList (416 + L) (List.replicate z 0)) :=
    (Mem.reads_data M).write hwf _ _
  set M2 := M1.write 352 (Bytes.toB256 [0x20]).toBytes
  have hM2s : M2.size = sz := by
    rw [Mem.size_write_of_le (by rw [B256.length_toBytes, hM1s]; omega), hM1s]
  have hr2 := hr1.write hwf1 352 (Bytes.toB256 [0x20]).toBytes
  have hread180 : Bytes.toB256 (M2.read 384 32).1 = Lw := by
    rw [hr2.read, Bytes.sliceD_writeAt_after _ _ _ _ _ (by rw [B256.length_toBytes]),
      Bytes.sliceD_writeAt_before _ _ _ _ _ (by omega), ← hrd, hLw, B256.toB256_toBytes]
  rw [read_covered hM2s hsz32 (by omega), hread180, hret]
  rw [hr2.read, show 64 + ceil32 L = 32 + (32 + (L + z)) by omega, List.sliceD_split,
    List.sliceD_split, List.sliceD_split, sliceD_word_same,
    show (352 : Nat) + 32 = 384 from rfl, show (384 : Nat) + 32 = 416 from rfl,
    Bytes.sliceD_writeAt_after _ _ _ _ _ (by rw [B256.length_toBytes]),
    Bytes.sliceD_writeAt_before _ _ _ _ _ (by omega), ← hrd, hLw,
    Bytes.sliceD_writeAt_after _ _ _ _ _ (by rw [B256.length_toBytes]; omega),
    Bytes.sliceD_writeAt_before _ _ _ _ _ (by omega), ← hrd, hstr,
    Bytes.sliceD_writeAt_after _ _ _ _ _ (by rw [B256.length_toBytes]; omega),
    Bytes.sliceD_writeAt_inside _ _ _ _ _ (by omega) (by rw [List.length_replicate]),
    Nat.sub_self, Bytes.sliceD_zero_length (List.length_replicate ..)]
  unfold abiString
  rw [hlen, hLdef, toB256_toNat, show Bytes.toB256 [0x20] = (32 : B256) by decide]
  simp only [List.append_assoc]
  rfl

/-- **The string views, inverted**, for either view: a successful halt passed the `CALLVALUE`
guard and returns exactly `abiString` of the stored string (`n` data words), over storage whose
length word is within the variable's bound; storage and logs are kept. -/
theorem safe_strView (hfork : CoveredFork sevm.benvStat.fork) (hcd : sevm.data.length < 2 ^ 256)
    {h0 h1 sl cp : UInt8} {fail : SFunc} (hf : fail.noOk = true) {e0 e1 x0 x1 r0 r1 : UInt8}
    {j k n : Nat} {joinT : SFunc} (hjT : joinT = t_0774_c5)
    (hk : prog[k]? = some (vyLoadLoopTree e0 e1 x0 x1 r0 r1 j k joinT))
    (hj : prog[j]? = some joinT)
    (hcase : (cp = 3 ∧ n = 2 ∧ ((stor₀).get (Bytes.toB256 [sl]).toBytes.keccak).toNat ≤ 64) ∨
      (cp = 2 ∧ n = 1 ∧ ((stor₀).get (Bytes.toB256 [sl]).toBytes.keccak).toNat ≤ 32))
    {G : Nat} {post : Devm}
    (run : SFunc.Run prog sevm (entrySt sevm b G)
      (vyStrView h0 h1 sl cp fail (vyLoadLoopTree e0 e1 x0 x1 r0 r1 j k joinT)) (.halted post)) :
    sevm.value = 0 ∧
      Lands sevm b post (stor₀, [], some (abiString (vyStrOf stor₀ (Bytes.toB256 [sl]).toBytes.keccak n))) := by
  subst hjT
  have run := run.cut
  unfold entrySt vyStrView at run
  obtain ⟨hv, G1, run⟩ := ric_vyNonpayable (h := h0) (l := h1) (fail := fail) hf run
  refine ⟨hv, ?_⟩
  set base := (Bytes.toB256 [sl]).toBytes.keccak with hbase
  set Lw := b.getStorVal sevm.currentTarget base with hLwdef
  have hLst : (stor₀).get base = Lw := rfl
  rw [hLst] at hcase
  set L := Lw.toNat with hLdef
  have hM0 := vyMem_empty_size (Sevm.dataWord sevm 0)
  have hwf0 : Mem.Wf (vyMem Mem.empty (Sevm.dataWord sevm 0)) := vyMem_wf Mem.wf_empty _
  have hc0 : (Bytes.toB256 [0xc0]).toNat = 192 := by decide
  have h20 : (Bytes.toB256 [0x20]).toNat = 32 := by decide
  have h120 : (Bytes.toB256 [0x01, 0x20]).toNat = 288 := by decide
  have hz0 : Bytes.toB256 [0x00] = Nat.toB256 0 := by decide
  set M1 := (vyMem Mem.empty (Sevm.dataWord sevm 0)).write 192 (Bytes.toB256 [sl]).toBytes
  have hM1 : M1.size = 224 := by simp only [M1, Mem.size_write_word_at, hM0]; decide
  have hwf1 : Mem.Wf M1 := hwf0.write _ _
  -- the prefix
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G2, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G3, rfl⟩ := ri_dup (n := 0) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G4, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G5, rfl⟩ := ri_mstore s1
  rw [hc0] at run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G6, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G7, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G8, rfl⟩ := ri_keccak s1
  rw [hc0, h20, Mem.read_write_word_of_wf hwf0, read_covered hM1 (by decide) (by decide)] at run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G9, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G10, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G11, rfl⟩ := ri_dup (n := 2) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G12, rfl⟩ := ri_sload hfork s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G13, rfl⟩ := ri_add s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G14, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G15, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G16, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G17, rfl⟩ := ri_dup (n := 1) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G18, rfl⟩ := ri_dup (n := 3) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G19, rfl⟩ := ri_mstore s1
  rw [h120, hz0] at run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G20, rfl⟩ := ri_add s1
  have hp120 : Bytes.toB256 [0x01, 0x20] = 0x120 := by decide
  have h384 : (Bytes.toB256 [0x01, 0x80]).toNat = 384 := by decide
  rw [hp120] at run
  clear s1
  set lp := b.getStorVal sevm.currentTarget (Bytes.toB256 [sl]).toBytes.keccak + Bytes.toB256 [0x20]
  have hlp : lp.toNat = L + 32 := by
    show (Lw + Bytes.toB256 [0x20]).toNat = L + 32
    rw [B256.toNat_add, show (Bytes.toB256 [0x20]).toNat = 32 by decide,
      Nat.lo_eq_of_lt (by have := hcase; omega)]
  set b1 := afterSload sevm b base
  set M2 := M1.write 288 (Nat.toB256 0).toBytes
  have hM2 : M2.size = 320 := by simp only [M2, Mem.size_write_word_at, hM1]; decide
  have hwf2 : Mem.Wf M2 := hwf1.write _ _
  have hc2 : (M2.read 0x120 32).1 = (Nat.toB256 0).toBytes := Mem.read_write_word_of_wf hwf1 _ _
  have hkC : k ∉ ([] : List Nat) := by simp
  have hjC : j ∉ ([] : List Nat) := by simp
  have hcap1 : Bytes.toB256 [cp] + Nat.toB256 0 ≠ Nat.toB256 (0 + 1) := by
    rcases hcase with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> decide
  -- iteration 0
  rcases ric_vyLoadIter hfork (i := 0) hM2 (by decide) (by decide) h384 (by decide) (by decide)
    (by decide) (by decide) hwf2 hc2 hk hkC hj hjC run with ⟨hlt, -⟩ | ⟨-, G21, run⟩
  · omega
  rw [ite_eq_right_of_eq_false _ _ (eq_false hcap1)] at run
  set b2 := afterSload sevm b1 (base + Nat.toB256 0)
  set b3 := afterSload sevm b2 (base + Nat.toB256 1)
  set u0 := b1.getStorVal sevm.currentTarget (base + Nat.toB256 0)
  set u1 := b2.getStorVal sevm.currentTarget (base + Nat.toB256 1)
  have hu0 : u0 = Lw := by
    show (afterSload sevm b base).getStorVal _ _ = _
    rw [getStorVal_afterSload, show base + Nat.toB256 0 = base by
      apply B256.toNat_inj
      rw [B256.toNat_add, B256.toNat_toB256_of_lt (by decide), Nat.add_zero,
        Nat.lo_eq_of_lt (B256.toNat_lt _)]]
  have hu1 : u1 = (stor₀).get (base + Nat.toB256 (0 + 1)) := by
    show (afterSload sevm (afterSload sevm b base) _).getStorVal _ _ = _
    rw [getStorVal_afterSload, getStorVal_afterSload]; rfl
  -- The memory images from here on are kept opaque (`generalize`, then `subst` inside each
  -- fact's own proof): a `set` image makes the kernel unfold the concrete write chain whenever a
  -- size or read of it is converted.
  generalize hM3d : (M2.write (384 + 32 * 0) u0.toBytes).write 0x120
    (Nat.toB256 (0 + 1)).toBytes = M3 at run
  have hM3 : M3.size = 416 := by
    subst hM3d; simp only [Mem.size_write_word_at, hM2]; decide
  have hwf3 : Mem.Wf M3 := by subst hM3d; exact (hwf2.write _ _).write _ _
  have hc3 : (M3.read 0x120 32).1 = (Nat.toB256 1).toBytes := by
    subst hM3d; exact Mem.read_write_word_of_wf (hwf2.write _ _) _ _
  -- iteration 1
  rcases ric_vyLoadIter hfork (i := 1) hM3 (by decide) (by decide) h384 (by decide) (by decide)
    (by decide) (by decide) hwf3 hc3 hk hkC hj hjC run with ⟨hlt, -⟩ | ⟨-, G22, run⟩
  · omega
  generalize hM4d : (M3.write (384 + 32 * 1) u1.toBytes).write 0x120
    (Nat.toB256 (1 + 1)).toBytes = M4 at run
  have hM4 : M4.size = 448 := by
    subst hM4d; simp only [Mem.size_write_word_at, hM3]; decide
  have hwf4 : Mem.Wf M4 := by subst hM4d; exact (hwf3.write _ _).write _ _
  have hc4 : (M4.read 0x120 32).1 = (Nat.toB256 2).toBytes := by
    subst hM4d; exact Mem.read_write_word_of_wf (hwf3.write _ _) _ _
  have hfacts4 : (M4.read 384 32).1 = Lw.toBytes ∧
      ((M4.read 416 L).1 = u1.toBytes.take L ∨ 32 < L) ∧ ((M4.read 416 L).1).length = L := by
    subst hM4d; subst hM3d
    have hr2 := Mem.reads_data M2
    have hr4 := ((((hr2.write hwf2 (384 + 32 * 0) u0.toBytes).write (hwf2.write _ _) 0x120
      (Nat.toB256 (0 + 1)).toBytes).write hwf3 (384 + 32 * 1) u1.toBytes).write
      (hwf3.write _ _) 0x120 (Nat.toB256 (1 + 1)).toBytes)
    refine ⟨?_, ?_, ?_⟩
    · rw [hr4.read, Bytes.sliceD_writeAt_after _ _ _ _ _ (by simp [B256.length_toBytes]),
        Bytes.sliceD_writeAt_before _ _ _ _ _ (by omega),
        Bytes.sliceD_writeAt_after _ _ _ _ _ (by simp [B256.length_toBytes]),
        Bytes.sliceD_writeAt_inside _ _ _ _ _ (by omega) (by simp [B256.length_toBytes]),
        show 384 - (384 + 32 * 0) = 0 from rfl, Bytes.sliceD_zero_length (B256.length_toBytes _), hu0]
    · by_cases hL32 : L ≤ 32
      · left
        rw [hr4.read, Bytes.sliceD_writeAt_after _ _ _ _ _ (by rw [B256.length_toBytes]; omega),
          Bytes.sliceD_writeAt_inside _ _ _ _ _ (by omega) (by rw [B256.length_toBytes]; omega),
          show 416 - (384 + 32 * 1) = 0 from rfl,
          sliceD_zero_take _ (by rw [B256.length_toBytes]; exact hL32)]
      · right; omega
    · rw [hr4.read, List.length_sliceD]
  obtain ⟨hLw4, hread4, hlen4⟩ := hfacts4
  have hc := ceil32_eq L
  have hlands : ∀ post : Devm, ∀ bb : Devm, (∀ a, Devm.getStor bb a = Devm.getStor b a) →
      bb.logs = b.logs → (∀ a, Devm.getStor post a = Devm.getStor bb a) → post.logs = bb.logs →
      post.output = abiString (vyStrOf stor₀ base n) →
      Lands sevm b post (stor₀, [], some (abiString (vyStrOf stor₀ base n))) := by
    intro post bb h1 h2 h3 h4 h5
    refine ⟨by rw [h3, h1], fun a _ => by rw [h3, h1], by rw [h4, h2, List.append_nil],
      fun o ho => ?_, fun h => by cases h⟩
    cases ho; exact h5
  rcases hcase with ⟨rfl, rfl, hL⟩ | ⟨rfl, rfl, hL⟩
  · -- `name`: a third pass
    rw [ite_eq_right_of_eq_false _ _ (eq_false (by decide))] at run
    set u2 := b3.getStorVal sevm.currentTarget (base + Nat.toB256 2)
    have hu2 : u2 = (stor₀).get (base + Nat.toB256 (1 + 1)) := by
      show (afterSload sevm (afterSload sevm (afterSload sevm b base) _) _).getStorVal _ _ = _
      rw [getStorVal_afterSload, getStorVal_afterSload, getStorVal_afterSload]; rfl
    have hW : vyStrWords stor₀ base 2 = u1.toBytes ++ u2.toBytes := by
      rw [hu1, hu2]; rfl
    rcases ric_vyLoadIter hfork (i := 2) hM4 (by decide) (by decide) h384 (by decide) (by decide)
      (by decide) (by decide) hwf4 hc4 hk hkC hj hjC run with ⟨hlt, G23, run⟩ | ⟨hle, G23, run⟩
    · -- the test fails at the third word
      have hstr : (M4.read 416 L).1 = vyStrOf stor₀ base 2 := by
        rcases hread4 with h | h
        · rw [h, vyStrOf, hLst, hW, List.take_append_of_le_length (by rw [B256.length_toBytes]; omega)]
        · omega
      obtain ⟨hst, hlg, hout⟩ := safe_strJoin hcd hwf4 hM4 (by decide)
        (by rw [← hLdef]; omega) (by rw [← hLdef]; omega) hLw4 hstr (by rw [← hstr, hlen4]) b3 run
      exact hlands post b3 (fun a => by simp only [b3, b2, b1, afterSload_getStor])
        (by simp only [b3, b2, b1, afterSload_logs]) hst hlg hout
    · -- the third word is copied, and the counter reaches the cap
      rw [ite_eq_left_of_eq_true _ _ (eq_true (by decide))] at run
      set b4 := afterSload sevm b3 (base + Nat.toB256 2)
      generalize hM5d : (M4.write (384 + 32 * 2) u2.toBytes).write 0x120
        (Nat.toB256 (2 + 1)).toBytes = M5 at run
      have hM5 : M5.size = 480 := by
        subst hM5d; simp only [Mem.size_write_word_at, hM4]; decide
      have hwf5 : Mem.Wf M5 := by subst hM5d; exact (hwf4.write _ _).write _ _
      have hfacts5 : (M5.read 384 32).1 = Lw.toBytes ∧
          (M5.read 416 (32 + (L - 32))).1 = vyStrOf stor₀ base 2 ∧
          ((M5.read 416 L).1).length = L := by
        subst hM5d; subst hM4d; subst hM3d
        have hr2 := Mem.reads_data M2
        have hr4 := ((((hr2.write hwf2 (384 + 32 * 0) u0.toBytes).write (hwf2.write _ _) 0x120
          (Nat.toB256 (0 + 1)).toBytes).write hwf3 (384 + 32 * 1) u1.toBytes).write
          (hwf3.write _ _) 0x120 (Nat.toB256 (1 + 1)).toBytes)
        have hr5 := (hr4.write hwf4 (384 + 32 * 2) u2.toBytes).write (hwf4.write _ _) 0x120
          (Nat.toB256 (2 + 1)).toBytes
        refine ⟨?_, ?_, ?_⟩
        · rw [hr5.read, Bytes.sliceD_writeAt_after _ _ _ _ _ (by simp [B256.length_toBytes]),
            Bytes.sliceD_writeAt_before _ _ _ _ _ (by omega), ← hr4.read, hLw4]
        · rw [hr5.read, List.sliceD_split,
            Bytes.sliceD_writeAt_after _ _ _ _ _ (by simp [B256.length_toBytes]),
            Bytes.sliceD_writeAt_before _ _ _ _ _ (by omega), ← hr4.read,
            Bytes.sliceD_writeAt_after _ _ _ _ _ (by simp [B256.length_toBytes]),
            Bytes.sliceD_writeAt_inside _ _ _ _ _ (by omega) (by simp [B256.length_toBytes]; omega),
            show 416 + 32 - (384 + 32 * 2) = 0 from rfl,
            sliceD_zero_take _ (by rw [B256.length_toBytes]; omega), hr4.read,
            Bytes.sliceD_writeAt_after _ _ _ _ _ (by simp [B256.length_toBytes]),
            Bytes.sliceD_writeAt_inside _ _ _ _ _ (by omega) (by simp [B256.length_toBytes]),
            show 416 - (384 + 32 * 1) = 0 from rfl,
            Bytes.sliceD_zero_length (B256.length_toBytes _), vyStrOf, hLst, hW,
            List.take_append, B256.length_toBytes,
            List.take_of_length_le (l := u1.toBytes) (by rw [B256.length_toBytes]; omega)]
        · rw [hr5.read, List.length_sliceD]
      obtain ⟨hLw5, hstr', hlen5⟩ := hfacts5
      have hstr : (M5.read 416 L).1 = vyStrOf stor₀ base 2 := by
        rwa [show 32 + (L - 32) = L by omega] at hstr'
      obtain ⟨hst, hlg, hout⟩ := safe_strJoin hcd hwf5 hM5 (by decide)
        (by rw [← hLdef]; omega) (by rw [← hLdef]; omega) hLw5 hstr (by rw [← hstr, hlen5]) b4 run
      exact hlands post b4 (fun a => by simp only [b4, b3, b2, b1, afterSload_getStor])
        (by simp only [b4, b3, b2, b1, afterSload_logs]) hst hlg hout
  · -- `symbol`: the counter reached the cap
    rw [ite_eq_left_of_eq_true _ _ (eq_true (by decide))] at run
    have hstr : (M4.read 416 L).1 = vyStrOf stor₀ base 1 := by
      rcases hread4 with h | h
      · rw [h, vyStrOf, hLst, hu1]; rfl
      · omega
    obtain ⟨hst, hlg, hout⟩ := safe_strJoin hcd hwf4 hM4 (by decide)
      (by rw [← hLdef]; omega) (by rw [← hLdef]; omega) hLw4 hstr (by rw [← hstr, hlen4]) b3 run
    exact hlands post b3 (fun a => by simp only [b3, b2, b1, afterSload_getStor])
      (by simp only [b3, b2, b1, afterSload_logs]) hst hlg hout

-- SEGMENT: safeStringViews (`name` and `symbol`, one shape, inverted)
/-- `name()`, inverted, over storage whose length word is within `String[64]`. -/
theorem safe_name (hfork : CoveredFork sevm.benvStat.fork) (hcd : sevm.data.length < 2 ^ 256)
    (hL : ((stor₀).get vyNameBase).toNat ≤ 64) :
    SafeBody sevm b t_0716_c0 (rawName sevm stor₀) := by
  intro G post run
  have hb : vyNameBase = (Bytes.toB256 [0x00]).toBytes.keccak := by
    rw [show Bytes.toB256 [0x00] = 0 by decide]; rfl
  obtain ⟨hv, hl⟩ := safe_strView (h0 := 0x07) (h1 := 0x20) (fail := t_071c_c0) (e0 := 0x07)
    (e1 := 0x52) (x0 := 0x07) (x1 := 0x74) (r0 := 0x07) (r1 := 0x3f) hfork hcd (by decide) rfl rfl
    rfl (Or.inl ⟨rfl, rfl, by rw [← hb]; exact hL⟩) run
  rw [← hb] at hl
  exact ⟨_, by simp only [rawName, hv, hL, and_self, ite_true], hl⟩

/-- `symbol()`, inverted, over storage whose length word is within `String[32]`. -/
theorem safe_symbol (hfork : CoveredFork sevm.benvStat.fork) (hcd : sevm.data.length < 2 ^ 256)
    (hL : ((stor₀).get vySymbolBase).toNat ≤ 32) :
    SafeBody sevm b t_07ca_c0 (rawSymbol sevm stor₀) := by
  intro G post run
  have hb : vySymbolBase = (Bytes.toB256 [0x01]).toBytes.keccak := by
    rw [show Bytes.toB256 [0x01] = 1 by decide]; rfl
  obtain ⟨hv, hl⟩ := safe_strView (h0 := 0x07) (h1 := 0xd4) (fail := t_07d0_c0) (e0 := 0x08)
    (e1 := 0x06) (x0 := 0x08) (x1 := 0x28) (r0 := 0x07) (r1 := 0xf3) (joinT := t_0828_c6) hfork hcd
    (by decide) rfl rfl rfl (Or.inr ⟨rfl, rfl, by rw [← hb]; exact hL⟩) run
  rw [← hb] at hl
  exact ⟨_, by simp only [rawSymbol, hv, hL, and_self, ite_true], hl⟩

end StrViews

end Blanc.Lift.Curve3Crv
