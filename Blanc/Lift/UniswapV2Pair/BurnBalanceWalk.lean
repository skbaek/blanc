import Blanc.Lift.UniswapV2Pair.SkimSecondWalk

/-! Actual Burn post-transfer balance observations at the moved free pointer. -/
namespace Blanc.Lift.UniswapV2Pair
open Jaune

inductive BurnFinalBalanceSite where
  | first
  | second

def BurnFinalBalanceSite.callTree : BurnFinalBalanceSite → SFunc
  | .first => t_170f_c13
  | .second => t_17ab_c13

def BurnFinalBalanceSite.returnTree : BurnFinalBalanceSite → SFunc
  | .first => t_1723_c13
  | .second => t_17bf_c13

def BurnFinalBalanceSite.decodeTree : BurnFinalBalanceSite → SFunc
  | .first => t_1739_c13
  | .second => t_17d5_c13

def BurnFinalBalanceSite.afterDecodeTree (site : BurnFinalBalanceSite) : SFunc :=
  match site.decodeTree with
  | .dest (.next _ (.next _ tail)) => tail
  | _ => .undefined

def burnBalanceReplyMemory (M : Mem) (p : B256) (out : Bytes) : Mem :=
  (M.extends [(p.toNat, 36), (p.toNat, 32)]).write p.toNat (out.take 32)

/-- Both actual post-transfer balance sites retain the original call witness,
derive full reply width from the guards, and decode the moved output window. -/
theorem burnFinalBalanceRead_inv {P : Sevm → Devm → Ninst → Devm → Prop}
    {sevm : Sevm} {b : Devm} {R : List B256} {C : List Nat} {M : Mem} {G n : Nat}
    {p z token a x y : B256} {seg : Seg} (site : BurnFinalBalanceSite)
    (project : ∀ {e d i d'}, P e d i d' → Ninst.Run e d i d')
    (fork : CoveredFork sevm.benvStat.fork) (mem : PtrMem p n M)
    (low : 96 ≤ p.toNat) (fit : p.toNat + 36 ≤ n)
    (run : SFunc.RunCutP P cert.prog sevm C
      (St b (z :: token :: p :: 36 :: p :: 32 :: a :: x :: y :: R) M G)
      site.callTree seg) :
    ∃ (gw : B256) (callGas : Nat) (d : Devm) (out : Bytes) (tailGas : Nat),
      P sevm (St b (gw :: token :: p :: 36 :: p :: 32 :: a :: x :: y :: R) M callGas)
        (.exec .staticcall) d ∧
      StaticCallPost b d (a :: x :: y :: R) M p 36 p 32 1 out ∧
      32 ≤ out.length ∧ out.length < 2 ^ 256 ∧
      StaticAnswered sevm b token.toAdr (M.read p.toNat 36).1 out ∧
      PtrMem p n (burnBalanceReplyMemory M p out) ∧
      SFunc.RunCutP P cert.prog sevm C
        (St d (Bytes.toB256 (out.take 32) :: R)
          (burnBalanceReplyMemory M p out) tailGas) site.afterDecodeTree seg := by
  have callObservation : ∃ (gw : B256) (callGas : Nat) (d : Devm) (out : Bytes) (tailGas : Nat),
      P sevm (St b (gw :: token :: p :: 36 :: p :: 32 :: a :: x :: y :: R) M callGas)
        (.exec .staticcall) d ∧
      StaticCallPost b d (a :: x :: y :: R) M p 36 p 32 1 out ∧
      out.length < 2 ^ 256 ∧
      StaticAnswered sevm b token.toAdr (M.read p.toNat 36).1 out ∧
      SFunc.RunCutP P cert.prog sevm C
        (St d (0 :: a :: x :: y :: R) (burnBalanceReplyMemory M p out) tailGas)
        site.returnTree seg := by
    cases site
    · exact staticCallGuard_invP [0x17, 0x23] (by decide) rfl project fork (by decide) run
    · exact staticCallGuard_invP [0x17, 0xbf] (by decide) rfl project fork (by decide) run
  obtain ⟨gw, callGas, d, out, _, call, post, bound, answered, tail⟩ := callObservation
  have extended : M.extends [(p.toNat, 36), (p.toNat, 32)] = M := by
    unfold Mem.extends
    rw [mem.size]
    simp only [memExtsSize]
    rw [memExtSize_of_le mem.n32 fit,
      memExtSize_of_le mem.n32 (by omega : p.toNat + 32 ≤ n), ← mem.size]
  have replyMem : PtrMem p n (burnBalanceReplyMemory M p out) := by
    unfold burnBalanceReplyMemory
    rw [extended]
    exact mem.write_bytes_of_le p.toNat (out.take 32)
      (by have := List.length_take_le 32 out; omega) (Or.inr low)
  have full : d.returnData.length < 2 ^ 256 := by rw [post.returnData]; exact bound
  have guarded : 32 ≤ d.returnData.length ∧ ∃ G',
      SFunc.RunCutP P cert.prog sevm C
        (St d (d.returnData.length.toB256 :: p :: R)
          (burnBalanceReplyMemory M p out) G') site.decodeTree seg := by
    cases site
    · exact returnWidthGuard_invP [0x17, 0x39] (by decide) rfl project replyMem full (by decide) tail
    · exact returnWidthGuard_invP [0x17, 0xd5] (by decide) rfl project replyMem full (by decide) tail
  obtain ⟨long, _, decoded⟩ := guarded
  rw [post.returnData] at long decoded
  have shape : site.decodeTree = .dest (.next (.reg .pop)
      (.next (.reg .mload) site.afterDecodeTree)) := by cases site <;> rfl
  rw [shape] at decoded
  obtain ⟨_, decoded⟩ := ric_destP decoded
  obtain ⟨_, step, decoded⟩ := ric_nextP decoded
  obtain ⟨_, rfl⟩ := ri_pop (project step)
  obtain ⟨loaded, step, decoded⟩ := ric_nextP decoded
  obtain ⟨tailGas, state⟩ := ri_mload (project step)
  have word : Bytes.toB256 ((burnBalanceReplyMemory M p out).read p.toNat 32).1 =
      Bytes.toB256 (out.take 32) := by
    have length : (out.take 32).length = 32 := by rw [List.length_take, Nat.min_eq_left long]
    have image := Bytes.sliceD_writeAt M.data.toList (out.take 32) p.toNat
    rw [length] at image
    unfold burnBalanceReplyMemory
    rw [extended, (Mem.reads_data M |>.write mem.wf p.toNat (out.take 32)).read, image]
  rw [word, replyMem.read_self (by omega : p.toNat + 32 ≤ n)] at state
  subst loaded
  exact ⟨gw, callGas, d, out, tailGas, call, post, long, bound, answered, replyMem, decoded⟩

def burnFinalFirstRequestLine : List Ninst := [
  .push [0x40] (by decide),
  .reg (.dup 0),
  .reg .mload,
  .push [0x70, 0xa0, 0x82, 0x31, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (by decide),
  .reg (.dup 1),
  .reg .mstore,
  .reg .address,
  .push [4] (by decide),
  .reg (.dup 2),
  .reg .add,
  .reg .mstore,
  .reg (.swap 0),
  .reg .mload,
  .push [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff] (by decide),
  .reg (.dup 9),
  .reg .and,
  .reg (.swap 1),
  .push [0x70, 0xa0, 0x82, 0x31] (by decide),
  .reg (.swap 1),
  .push [0x24] (by decide),
  .reg (.dup 0),
  .reg (.dup 3),
  .reg .add,
  .reg (.swap 2),
  .push [0x20] (by decide),
  .reg (.swap 2),
  .reg (.swap 1),
  .reg (.swap 0),
  .reg (.dup 2),
  .reg (.swap 0),
  .reg .sub,
  .reg .add,
  .reg (.dup 1),
  .reg (.dup 6),
  .reg (.dup 0)]

theorem burnFinalFirstRequestLine_inv {sevm : Sevm} {b final : Devm}
    {R : List B256} {M : Mem} {G : Nat} {p : B256}
    {supply f L b1 b0 token1 token0 r1 r0 amount1 amount0 toWord extρ : B256}
    (ptr : PtrWord p M) (low : 96 ≤ p.toNat) (high : p.toNat + 1024 < 2 ^ 256)
    (run : Line.Run sevm
      (St b (burnPricedLocals supply f L b1 b0 token1 token0 r1 r0 amount1 amount0 toWord extρ R) M G)
      burnFinalFirstRequestLine final) :
    ∃ gas, final = St b
      ((token0 &&& 0xffffffffffffffffffffffffffffffffffffffff) ::
        (token0 &&& 0xffffffffffffffffffffffffffffffffffffffff) :: p :: 36 :: p :: 32 ::
        (p + 36) :: 0x70a08231 :: (token0 &&& 0xffffffffffffffffffffffffffffffffffffffff) ::
        burnPricedLocals supply f L b1 b0 token1 token0 r1 r0 amount1 amount0 toWord extρ R)
      (skimRequestMemory M p sevm.currentTarget) gas := by
  have word0 := ptr.2
  have p4 : (p + Bytes.toB256 [4]).toNat = p.toNat + 4 :=
    B256.toNat_add_eq_of_nof _ _ (by change p.toNat + 4 < 2 ^ 256; omega)
  have word1 : Bytes.toB256 ((((M.read 64 32).2.write p.toNat balanceOfSelectorWord.toBytes).write
      (p + Bytes.toB256 [4]).toNat sevm.currentTarget.toB256.toBytes).read 64 32).1 = p :=
    (((ptr.extend 64 32).write p.toNat _ low).write (p + Bytes.toB256 [4]).toNat _
      (by rw [p4]; omega)).2
  dsimp only [balanceOfSelectorWord] at word1
  dsimp only [burnFinalFirstRequestLine, burnPricedLocals] at run
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_push hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_dup rfl hs
  obtain ⟨d, hs, run⟩ := Line.of_run_cons run
  obtain ⟨_, state⟩ := ri_mload hs
  rw [show (Bytes.toB256 [0x40]).toNat = 64 from rfl, word0] at state
  subst d
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_push hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_dup rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_mstore hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run
  have address := of_run_address hs
  have stack := address.stack
  simp only [Stack.Push, Split, St.stack] at stack
  have state := St.of_stackRel address
  rw [stack] at state
  rw [state] at run
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_push hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_dup rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_add hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_mstore hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_swap rfl hs
  obtain ⟨d, hs, run⟩ := Line.of_run_cons run
  obtain ⟨_, state⟩ := ri_mload hs
  rw [show (Bytes.toB256 [0x40]).toNat = 64 from rfl, word1] at state
  subst d
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_push hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_dup rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_and hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_swap rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_push hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_swap rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_push hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_dup rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_dup rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_add hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_swap rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_push hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_swap rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_swap rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_swap rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_dup rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_swap rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_sub hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_add hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_dup rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_dup rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨gas, rfl⟩ := ri_dup rfl hs
  cases run
  refine ⟨gas, ?_⟩
  rw [B256.sub_self]
  rfl

/-- The first post-transfer Burn query is staged by its literal instructions;
the same successful source run passes its actual code guard into STATICCALL. -/
theorem burnFinalFirstRequest_inv {P : Sevm → Devm → Ninst → Devm → Prop}
    {sevm : Sevm} {b : Devm} {R : List B256} {C : List Nat} {M : Mem} {G : Nat} {p : B256} {seg : Seg}
    {supply f L b1 b0 token1 token0 r1 r0 amount1 amount0 toWord extρ : B256}
    (project : ∀ {e d i d'}, P e d i d' → Ninst.Run e d i d')
    (fork : CoveredFork sevm.benvStat.fork) (ptr : PtrWord p M)
    (low : 96 ≤ p.toNat) (high : p.toNat + 1024 < 2 ^ 256)
    (run : SFunc.RunCutP P cert.prog sevm C
      (St b (burnPricedLocals supply f L b1 b0 token1 token0 r1 r0 amount1 amount0 toWord extρ R) M G)
      t_16a3_c13 seg) :
    (b.getCode (token0 &&& 0xffffffffffffffffffffffffffffffffffffffff).toAdr).size.toB256 ≠ 0 ∧
    ∃ gas, SFunc.RunCutP P cert.prog sevm C
      (St (temporalAccountAccessBase b (token0 &&& 0xffffffffffffffffffffffffffffffffffffffff).toAdr)
        (0 :: (token0 &&& 0xffffffffffffffffffffffffffffffffffffffff) :: p :: 36 :: p :: 32 ::
          (p + 36) :: 0x70a08231 :: (token0 &&& 0xffffffffffffffffffffffffffffffffffffffff) ::
          burnPricedLocals supply f L b1 b0 token1 token0 r1 r0 amount1 amount0 toWord extρ R)
        (skimRequestMemory M p sevm.currentTarget) gas) t_170f_c13 seg := by
  unfold t_16a3_c13 at run
  obtain ⟨_, run⟩ := ric_destP run
  change SFunc.RunCutP P cert.prog sevm C _
    (burnFinalFirstRequestLine.foldr SFunc.next (syncCodeGuardLine.foldr SFunc.next
      (.next (.push [0x17, 0x0f] (by decide)) (.branch t_170b_c13 t_170f_c13)))) seg at run
  obtain ⟨_, line, run⟩ := run.split_nexts (fun step => project step) burnFinalFirstRequestLine
  obtain ⟨_, state⟩ := burnFinalFirstRequestLine_inv ptr low high line
  rw [state] at run
  obtain ⟨_, line, run⟩ := run.split_nexts (fun step => project step) syncCodeGuardLine
  obtain ⟨_, state⟩ := syncCodeGuardLine_inv fork line
  rw [state] at run
  obtain ⟨_, step, run⟩ := ric_nextP run
  obtain ⟨_, rfl⟩ := ri_push (project step)
  rcases ric_branchP run with ⟨_, _, failed⟩ | ⟨accepted, gas, run⟩
  · exact (failed.false_of_noOk (by decide : t_170b_c13.noOk = true)).elim
  · have zero := eq_zero_of_iszero_ne_zero accepted
    have code : (b.getCode (token0 &&& 0xffffffffffffffffffffffffffffffffffffffff).toAdr).size.toB256 ≠ 0 := by
      intro empty
      change B256.eqCheck ((b.getCode (token0 &&& 0xffffffffffffffffffffffffffffffffffffffff).toAdr).size.toB256) 0 = 0 at zero
      rw [empty, show B256.eqCheck (0 : B256) 0 = 1 from by decide] at zero
      exact (by decide : (1 : B256) ≠ 0) zero
    rw [zero] at run
    exact ⟨code, gas, run⟩

/-- The two physical reply bounds leave room for the complete following
balance-query staging area, beyond the final64-byte ABI area. -/
theorem burnFinalPointer_bounds {firstReply secondReply : Bytes}
    (firstWidth : firstReply.length < 2 ^ 160)
    (secondWidth : secondReply.length < 2 ^ 160) :
    96 ≤ (burnSecondTransferPointer firstReply secondReply).toNat ∧
      (burnSecondTransferPointer firstReply secondReply).toNat + 1024 < 2 ^ 256 := by
  have first := burnFirstTransferPointer_layout firstWidth
  have second := burnSecondTransferPointer_layout firstWidth secondWidth
  have firstDivision := Nat.mod_add_div (firstReply.length + 63) 32
  have secondDivision := Nat.mod_add_div (secondReply.length + 63) 32
  have firstBound : (burnFirstTransferPointer firstReply).toNat ≤ firstReply.length + 355 := by
    rw [first.1]
    split <;> omega
  have secondBound : (burnSecondTransferPointer firstReply secondReply).toNat ≤
      firstReply.length + secondReply.length + 582 := by
    rw [second.1]
    split <;> omega
  have margin : 2 * 2 ^ 160 + 1606 < (2 ^ 256 : Nat) := by decide
  exact ⟨by have := second.2.1; have := first.2.1; omega, by omega⟩

/-- Literal overlapping request writes preserve the moved pointer and pay
for the entire36-byte calldata/output window. -/
theorem burnBalanceRequest_memoryLayout {M : Mem} {p : B256} {n : Nat} {pair : Adr}
    (mem : PtrMem p n M) (low : 96 ≤ p.toNat)
    (high : p.toNat + 1024 < 2 ^ 256) :
    PtrMem p (skimRequestMemory M p pair).size (skimRequestMemory M p pair) ∧
      p.toNat + 36 ≤ (skimRequestMemory M p pair).size := by
  have p4 : (p + 4).toNat = p.toNat + 4 :=
    B256.toNat_add_eq_of_nof _ _ (by change p.toNat + 4 < 2 ^ 256; omega)
  have first := (mem.extend 64 32).write p.toNat balanceOfSelectorWord (Or.inr low)
  have second := first.write (p + 4).toNat pair.toB256 (Or.inr (by rw [p4]; omega))
  have image := second.extend 64 32
  have covered := Jaune.memExtSize_access_le
    (memExtSize (memExtSize n 64 32) p.toNat 32) (p + 4).toNat 32 (by decide)
  have grown := Blanc.Lift.memExtSize_ge
    (memExtSize (memExtSize (memExtSize n 64 32) p.toNat 32) (p + 4).toNat 32) 64 32
  have fit : p.toNat + 36 ≤ (skimRequestMemory M p pair).size := by
    rw [p4] at covered grown
    have size : (skimRequestMemory M p pair).size =
        memExtSize (memExtSize (memExtSize (memExtSize n 64 32) p.toNat 32)
          (p + 4).toNat 32) 64 32 := image.size
    rw [size, p4]
    omega
  have sized : PtrMem p (skimRequestMemory M p pair).size (skimRequestMemory M p pair) := by
    have size : (skimRequestMemory M p pair).size =
        memExtSize (memExtSize (memExtSize (memExtSize n 64 32) p.toNat 32)
          (p + 4).toNat 32) 64 32 := image.size
    rw [size]
    exact image
  exact ⟨sized, fit⟩

/-- The first actual post-transfer balance read has canonical balanceOf
calldata and retains the same execution into the second request's prefix. -/
theorem burnFinalFirstBalance_inv {P : Sevm → Devm → Ninst → Devm → Prop}
    {sevm : Sevm} {b : Devm} {R : List B256} {C : List Nat} {M : Mem} {G n : Nat} {p : B256} {seg : Seg}
    {supply f L b1 b0 token1 token0 r1 r0 amount1 amount0 toWord extρ : B256}
    (project : ∀ {e d i d'}, P e d i d' → Ninst.Run e d i d')
    (fork : CoveredFork sevm.benvStat.fork) (mem : PtrMem p n M)
    (low : 96 ≤ p.toNat) (high : p.toNat + 1024 < 2 ^ 256)
    (run : SFunc.RunCutP P cert.prog sevm C
      (St b (burnPricedLocals supply f L b1 b0 token1 token0 r1 r0 amount1 amount0 toWord extρ R) M G)
      t_16a3_c13 seg) :
    ∃ (gw : B256) (callGas : Nat) (d : Devm) (out : Bytes) (tailGas : Nat),
      let token := token0 &&& 0xffffffffffffffffffffffffffffffffffffffff
      let access := temporalAccountAccessBase b token.toAdr
      let Q := skimRequestMemory M p sevm.currentTarget
      let locals := burnPricedLocals supply f L b1 b0 token1 token0 r1 r0 amount1 amount0 toWord extρ R
      (b.getCode token.toAdr).size.toB256 ≠ 0 ∧
      P sevm (St access (gw :: token :: p :: 36 :: p :: 32 ::
        (p + 36) :: 0x70a08231 :: token :: locals) Q callGas) (.exec .staticcall) d ∧
      StaticCallPost access d ((p + 36) :: 0x70a08231 :: token :: locals) Q p 36 p 32 1 out ∧
      32 ≤ out.length ∧ out.length < 2 ^ 256 ∧
      StaticAnswered sevm access token.toAdr (ExternalOperation.encode (.balanceOf sevm.currentTarget)) out ∧
      PtrMem p Q.size (burnBalanceReplyMemory Q p out) ∧
      SFunc.RunCutP P cert.prog sevm C
        (St d (Bytes.toB256 (out.take 32) :: locals)
          (burnBalanceReplyMemory Q p out) tailGas) BurnFinalBalanceSite.first.afterDecodeTree seg := by
  obtain ⟨code, _, prepared⟩ := burnFinalFirstRequest_inv project fork (PtrWord.of_ptrMem mem) low high run
  obtain ⟨requestMem, fit⟩ := burnBalanceRequest_memoryLayout (pair := sevm.currentTarget) mem low high
  obtain ⟨gw, callGas, d, out, tailGas, call, post, long, bound, answered, replyMem, tail⟩ :=
    burnFinalBalanceRead_inv .first project fork requestMem low fit prepared
  rw [skimRequestMemory_read mem.wf high] at answered
  exact ⟨gw, callGas, d, out, tailGas, code, call, post, long, bound, answered, replyMem, tail⟩

def burnFinalSecondRequestLine : List Ninst := [
  .push [0x40] (by decide),
  .reg (.dup 0),
  .reg .mload,
  .push [0x70, 0xa0, 0x82, 0x31, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (by decide),
  .reg (.dup 1),
  .reg .mstore,
  .reg .address,
  .push [4] (by decide),
  .reg (.dup 2),
  .reg .add,
  .reg .mstore,
  .reg (.swap 0),
  .reg .mload,
  .reg (.swap 1),
  .reg (.swap 6),
  .reg .pop,
  .push [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff] (by decide),
  .reg (.dup 8),
  .reg .and,
  .reg (.swap 1),
  .push [0x70, 0xa0, 0x82, 0x31] (by decide),
  .reg (.swap 1),
  .push [0x24] (by decide),
  .reg (.dup 0),
  .reg (.dup 2),
  .reg .add,
  .reg (.swap 2),
  .push [0x20] (by decide),
  .reg (.swap 2),
  .reg (.swap 0),
  .reg (.swap 1),
  .reg (.swap 0),
  .reg (.dup 2),
  .reg (.swap 0),
  .reg .sub,
  .reg .add,
  .reg (.dup 1),
  .reg (.dup 6),
  .reg (.dup 0)]

theorem burnFinalSecondRequestLine_inv {sevm : Sevm} {b final : Devm}
    {R : List B256} {M : Mem} {G : Nat} {p : B256}
    {supply f L b1 b0 token1 token0 r1 r0 amount1 amount0 toWord extρ balance0 : B256}
    (ptr : PtrWord p M) (low : 96 ≤ p.toNat) (high : p.toNat + 1024 < 2 ^ 256)
    (run : Line.Run sevm
      (St b (balance0 :: burnPricedLocals supply f L b1 b0 token1 token0 r1 r0 amount1 amount0 toWord extρ R) M G)
      burnFinalSecondRequestLine final) :
    ∃ gas, final = St b
      ((token1 &&& 0xffffffffffffffffffffffffffffffffffffffff) ::
        (token1 &&& 0xffffffffffffffffffffffffffffffffffffffff) :: p :: 36 :: p :: 32 ::
        (p + 36) :: 0x70a08231 :: (token1 &&& 0xffffffffffffffffffffffffffffffffffffffff) ::
        burnPricedLocals supply f L b1 balance0 token1 token0 r1 r0 amount1 amount0 toWord extρ R)
      (skimRequestMemory M p sevm.currentTarget) gas := by
  have word0 := ptr.2
  have p4 : (p + Bytes.toB256 [4]).toNat = p.toNat + 4 :=
    B256.toNat_add_eq_of_nof _ _ (by change p.toNat + 4 < 2 ^ 256; omega)
  have word1 : Bytes.toB256 ((((M.read 64 32).2.write p.toNat balanceOfSelectorWord.toBytes).write
      (p + Bytes.toB256 [4]).toNat sevm.currentTarget.toB256.toBytes).read 64 32).1 = p :=
    (((ptr.extend 64 32).write p.toNat _ low).write (p + Bytes.toB256 [4]).toNat _
      (by rw [p4]; omega)).2
  dsimp only [balanceOfSelectorWord] at word1
  dsimp only [burnFinalSecondRequestLine, burnPricedLocals] at run
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_push hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_dup rfl hs
  obtain ⟨d, hs, run⟩ := Line.of_run_cons run
  obtain ⟨_, state⟩ := ri_mload hs
  rw [show (Bytes.toB256 [0x40]).toNat = 64 from rfl, word0] at state
  subst d
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_push hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_dup rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_mstore hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run
  have address := of_run_address hs
  have stack := address.stack
  simp only [Stack.Push, Split, St.stack] at stack
  have state := St.of_stackRel address
  rw [stack] at state
  rw [state] at run
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_push hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_dup rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_add hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_mstore hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_swap rfl hs
  obtain ⟨d, hs, run⟩ := Line.of_run_cons run
  obtain ⟨_, state⟩ := ri_mload hs
  rw [show (Bytes.toB256 [0x40]).toNat = 64 from rfl, word1] at state
  subst d
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_swap rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_swap rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_pop hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_push hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_dup rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_and hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_swap rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_push hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_swap rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_push hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_dup rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_dup rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_add hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_swap rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_push hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_swap rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_swap rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_swap rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_swap rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_dup rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_swap rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_sub hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_add hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_dup rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_dup rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨gas, rfl⟩ := ri_dup rfl hs
  cases run
  refine ⟨gas, ?_⟩
  rw [B256.sub_self]
  rfl

/-- The second post-transfer Burn query is staged by its literal instructions;
the same successful source run passes its actual code guard into STATICCALL. -/
theorem burnFinalSecondRequest_inv {P : Sevm → Devm → Ninst → Devm → Prop}
    {sevm : Sevm} {b : Devm} {R : List B256} {C : List Nat} {M : Mem} {G : Nat} {p : B256} {seg : Seg}
    {supply f L b1 b0 token1 token0 r1 r0 amount1 amount0 toWord extρ balance0 : B256}
    (project : ∀ {e d i d'}, P e d i d' → Ninst.Run e d i d')
    (fork : CoveredFork sevm.benvStat.fork) (ptr : PtrWord p M)
    (low : 96 ≤ p.toNat) (high : p.toNat + 1024 < 2 ^ 256)
    (run : SFunc.RunCutP P cert.prog sevm C
      (St b (balance0 :: burnPricedLocals supply f L b1 b0 token1 token0 r1 r0 amount1 amount0 toWord extρ R) M G)
      BurnFinalBalanceSite.first.afterDecodeTree seg) :
    (b.getCode (token1 &&& 0xffffffffffffffffffffffffffffffffffffffff).toAdr).size.toB256 ≠ 0 ∧
    ∃ gas, SFunc.RunCutP P cert.prog sevm C
      (St (temporalAccountAccessBase b (token1 &&& 0xffffffffffffffffffffffffffffffffffffffff).toAdr)
        (0 :: (token1 &&& 0xffffffffffffffffffffffffffffffffffffffff) :: p :: 36 :: p :: 32 ::
          (p + 36) :: 0x70a08231 :: (token1 &&& 0xffffffffffffffffffffffffffffffffffffffff) ::
          burnPricedLocals supply f L b1 balance0 token1 token0 r1 r0 amount1 amount0 toWord extρ R)
        (skimRequestMemory M p sevm.currentTarget) gas) t_17ab_c13 seg := by
  change SFunc.RunCutP P cert.prog sevm C _
    (burnFinalSecondRequestLine.foldr SFunc.next (syncCodeGuardLine.foldr SFunc.next
      (.next (.push [0x17, 0xab] (by decide)) (.branch t_17a7_c13 t_17ab_c13)))) seg at run
  obtain ⟨_, line, run⟩ := run.split_nexts (fun step => project step) burnFinalSecondRequestLine
  obtain ⟨_, state⟩ := burnFinalSecondRequestLine_inv ptr low high line
  rw [state] at run
  obtain ⟨_, line, run⟩ := run.split_nexts (fun step => project step) syncCodeGuardLine
  obtain ⟨_, state⟩ := syncCodeGuardLine_inv fork line
  rw [state] at run
  obtain ⟨_, step, run⟩ := ric_nextP run
  obtain ⟨_, rfl⟩ := ri_push (project step)
  rcases ric_branchP run with ⟨_, _, failed⟩ | ⟨accepted, gas, run⟩
  · exact (failed.false_of_noOk (by decide : t_17a7_c13.noOk = true)).elim
  · have zero := eq_zero_of_iszero_ne_zero accepted
    have code : (b.getCode (token1 &&& 0xffffffffffffffffffffffffffffffffffffffff).toAdr).size.toB256 ≠ 0 := by
      intro empty
      change B256.eqCheck ((b.getCode (token1 &&& 0xffffffffffffffffffffffffffffffffffffffff).toAdr).size.toB256) 0 = 0 at zero
      rw [empty, show B256.eqCheck (0 : B256) 0 = 1 from by decide] at zero
      exact (by decide : (1 : B256) ≠ 0) zero
    rw [zero] at run
    exact ⟨code, gas, run⟩

/-- Both post-transfer balance answers come from the same Burn source run.
Canonical requests, full reply guards and actual call provenance are retained
through the cached balance0 replacement into the literal update caller. -/
theorem burnFinalBalances_inv {P : Sevm → Devm → Ninst → Devm → Prop}
    {sevm : Sevm} {b : Devm} {R : List B256} {C : List Nat} {M : Mem} {G n : Nat} {p : B256} {seg : Seg}
    {supply f L b1 b0 token1 token0 r1 r0 amount1 amount0 toWord extρ : B256}
    (project : ∀ {e d i d'}, P e d i d' → Ninst.Run e d i d')
    (fork : CoveredFork sevm.benvStat.fork) (mem : PtrMem p n M)
    (low : 96 ≤ p.toNat) (high : p.toNat + 1024 < 2 ^ 256)
    (run : SFunc.RunCutP P cert.prog sevm C
      (St b (burnPricedLocals supply f L b1 b0 token1 token0 r1 r0 amount1 amount0 toWord extρ R) M G)
      t_16a3_c13 seg) :
    ∃ (gw0 : B256) (callGas0 : Nat) (d0 : Devm) (out0 : Bytes)
        (gw1 : B256) (callGas1 : Nat) (d1 : Devm) (out1 : Bytes) (tailGas : Nat),
      let t0 := token0 &&& 0xffffffffffffffffffffffffffffffffffffffff
      let t1 := token1 &&& 0xffffffffffffffffffffffffffffffffffffffff
      let Q0 := skimRequestMemory M p sevm.currentTarget
      let N0 := burnBalanceReplyMemory Q0 p out0
      let Q1 := skimRequestMemory N0 p sevm.currentTarget
      let locals0 := burnPricedLocals supply f L b1 b0 token1 token0 r1 r0 amount1 amount0 toWord extρ R
      let locals1 := burnPricedLocals supply f L b1 (Bytes.toB256 (out0.take 32))
        token1 token0 r1 r0 amount1 amount0 toWord extρ R
      let access0 := temporalAccountAccessBase b t0.toAdr
      let access1 := temporalAccountAccessBase d0 t1.toAdr
      (b.getCode t0.toAdr).size.toB256 ≠ 0 ∧
      (d0.getCode t1.toAdr).size.toB256 ≠ 0 ∧
      P sevm (St access0 (gw0 :: t0 :: p :: 36 :: p :: 32 ::
        (p + 36) :: 0x70a08231 :: t0 :: locals0) Q0 callGas0) (.exec .staticcall) d0 ∧
      P sevm (St access1 (gw1 :: t1 :: p :: 36 :: p :: 32 ::
        (p + 36) :: 0x70a08231 :: t1 :: locals1) Q1 callGas1) (.exec .staticcall) d1 ∧
      StaticCallPost access0 d0 ((p + 36) :: 0x70a08231 :: t0 :: locals0) Q0 p 36 p 32 1 out0 ∧
      StaticCallPost access1 d1 ((p + 36) :: 0x70a08231 :: t1 :: locals1) Q1 p 36 p 32 1 out1 ∧
      32 ≤ out0.length ∧ out0.length < 2 ^ 256 ∧
      32 ≤ out1.length ∧ out1.length < 2 ^ 256 ∧
      StaticAnswered sevm access0 t0.toAdr (ExternalOperation.encode (.balanceOf sevm.currentTarget)) out0 ∧
      StaticAnswered sevm access1 t1.toAdr (ExternalOperation.encode (.balanceOf sevm.currentTarget)) out1 ∧
      PtrMem p Q1.size (burnBalanceReplyMemory Q1 p out1) ∧
      SFunc.RunCutP P cert.prog sevm C
        (St d1 (Bytes.toB256 (out1.take 32) :: locals1)
          (burnBalanceReplyMemory Q1 p out1) tailGas) BurnFinalBalanceSite.second.afterDecodeTree seg := by
  obtain ⟨gw0, callGas0, d0, out0, _, code0, call0, post0, long0, bound0, answered0, mem0, tail0⟩ :=
    burnFinalFirstBalance_inv project fork mem low high run
  obtain ⟨code1, _, prepared1⟩ :=
    burnFinalSecondRequest_inv project fork (PtrWord.of_ptrMem mem0) low high tail0
  obtain ⟨requestMem1, fit1⟩ := burnBalanceRequest_memoryLayout (pair := sevm.currentTarget) mem0 low high
  obtain ⟨gw1, callGas1, d1, out1, tailGas, call1, post1, long1, bound1, answered1, mem1, tail1⟩ :=
    burnFinalBalanceRead_inv .second project fork requestMem1 low fit1 prepared1
  rw [skimRequestMemory_read mem0.wf high] at answered1
  exact ⟨gw0, callGas0, d0, out0, gw1, callGas1, d1, out1, tailGas,
    code0, code1, call0, call1, post0, post1, long0, bound0, long1, bound1,
    answered0, answered1, mem1, tail1⟩

end Blanc.Lift.UniswapV2Pair
