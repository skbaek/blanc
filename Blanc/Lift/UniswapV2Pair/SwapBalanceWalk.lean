import Blanc.Lift.UniswapV2Pair.SwapCut
import Blanc.Lift.UniswapV2Pair.BalanceCallWalk
import Blanc.Lift.CodeSizeWalk
import Blanc.Lift.PtrWordMemory

/-! The two post-callback `balanceOf(pair)` STATICCALLs of the actual swap body,
from the cut `t_09c3_c5` to the first amount-in ternary `t_0af5_c5`'s tail.
Both requests are built at the moved free pointer `p` and leave it in place. -/
namespace Blanc.Lift.UniswapV2Pair
open Jaune

/-- The literal request prefix of each post-callback balance query, up to its
staging: load `p`, store the selector word and the Pair address, reload `p`. -/
def swapRequestLine : List Ninst := [
  .push [0x40] (by decide),
  .reg (.dup 0),
  .reg .mload,
  .push [0x70, 0xa0, 0x82, 0x31, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] (by decide),
  .reg (.dup 1),
  .reg .mstore,
  .reg .address,
  .push [0x04] (by decide),
  .reg (.dup 2),
  .reg .add,
  .reg .mstore,
  .reg (.swap 0),
  .reg .mload]

/-- The balance request at the moved pointer: selector word, then Pair address. -/
def swapBalanceRequest (M : Mem) (p : B256) (pair : Adr) : Mem :=
  (M.write p.toNat balanceOfSelectorWord.toBytes).write (p + 4).toNat pair.toB256.toBytes

theorem swapPtr_add {p : B256} {k : Nat} (fit : p.toNat + k < 2 ^ 256) :
    (p + k.toB256).toNat = p.toNat + k := by
  rw [B256.toNat_add, B256.toNat_toB256_of_lt (by omega), Nat.lo_eq_of_lt fit]

/-- The request keeps the free pointer and its allocation covers the 36-byte window. -/
theorem swapBalanceRequest_ptr {M : Mem} {p : B256} {n : Nat} {pair : Adr}
    (mem : PtrMem p n M) (lower : 128 ≤ p.toNat) (width : p.toNat + 260 < 2 ^ 256) :
    PtrMem p (memExtSize (memExtSize n p.toNat 32) (p.toNat + 4) 32)
      (swapBalanceRequest M p pair) := by
  have p4 : (p + 4).toNat = p.toNat + 4 := swapPtr_add (k := 4) (by omega)
  unfold swapBalanceRequest
  rw [p4]
  exact (mem.write p.toNat balanceOfSelectorWord (Or.inr (by omega))).write
    (p.toNat + 4) pair.toB256 (Or.inr (by omega))

/-- The literal request prefix leaves `p` twice over the incoming stack, with the
balance request installed at `p` and no other effect. -/
theorem swapRequestLine_inv {sevm : Sevm} {b final : Devm} {S : List B256} {M : Mem}
    {G n : Nat} {p : B256}
    (mem : PtrMem p n M) (lower : 128 ≤ p.toNat) (width : p.toNat + 260 < 2 ^ 256)
    (run : Line.Run sevm (St b S M G) swapRequestLine final) :
    ∃ gas, final = St b (p :: p :: S) (swapBalanceRequest M p sevm.currentTarget) gas := by
  have p4 : (p + Bytes.toB256 [4]).toNat = p.toNat + 4 := swapPtr_add (k := 4) (by omega)
  have m1 := mem.write p.toNat balanceOfSelectorWord (Or.inr (by omega))
  have m2 := swapBalanceRequest_ptr (pair := sevm.currentTarget) mem lower width
  dsimp only [swapRequestLine] at run
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_push hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_dup rfl hs
  obtain ⟨d, hs, run⟩ := Line.of_run_cons run
  obtain ⟨_, hd⟩ := ri_mload hs
  rw [show (Bytes.toB256 [64]).toNat = 64 from by decide,
    mem.read_self (by have := mem.ge; omega), (PtrWord.of_ptrMem mem).2] at hd
  subst d
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_push hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_dup rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_mstore hs
  obtain ⟨d, hs, run⟩ := Line.of_run_cons run
  have hp := of_run_address hs
  have stack := hp.stack
  simp only [Stack.Push, Split, St.stack] at stack
  have hd := St.of_stackRel hp
  rw [stack] at hd
  rw [hd] at run
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_push hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_dup rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_add hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_mstore hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_swap rfl hs
  obtain ⟨d, hs, run⟩ := Line.of_run_cons run
  obtain ⟨gas, hd⟩ := ri_mload hs
  have p4' : (p + 4).toNat = p.toNat + 4 := swapPtr_add (k := 4) (by omega)
  have read := m2.read_self (i := 64) (sz := 32) (by have := m2.ge; omega)
  have word := (PtrWord.of_ptrMem m2).2
  unfold swapBalanceRequest at read word
  rw [p4'] at read word
  rw [show (Bytes.toB256 [64]).toNat = 64 from by decide, p4] at hd
  change _ = St b (Bytes.toB256 ((((M.write p.toNat balanceOfSelectorWord.toBytes).write
    (p.toNat + 4) sevm.currentTarget.toB256.toBytes).read 64 32).1) :: _)
    (((M.write p.toNat balanceOfSelectorWord.toBytes).write
    (p.toNat + 4) sevm.currentTarget.toB256.toBytes).read 64 32).2 gas at hd
  rw [read, word] at hd
  subst d
  cases run
  refine ⟨gas, ?_⟩
  unfold swapBalanceRequest
  rw [p4']
  rfl

/-- The moved request's 36-byte window is exactly the source balanceOf calldata. -/
theorem swapBalanceRequest_read {M : Mem} {p : B256} {pair : Adr} (wf : Mem.Wf M)
    (width : p.toNat + 260 < 2 ^ 256) :
    ((swapBalanceRequest M p pair).read p.toNat 36).1 =
      ExternalOperation.encode (.balanceOf pair) := by
  have p4 : (p + 4).toNat = p.toNat + 4 := swapPtr_add (k := 4) (by omega)
  have r2 := (Mem.reads_data M).write wf p.toNat balanceOfSelectorWord.toBytes
  have r3 : Mem.Reads (swapBalanceRequest M p pair) _ :=
    r2.write (wf.write _ _) (p + 4).toNat pair.toB256.toBytes
  rw [r3.read, p4, show (36 : Nat) = 4 + 32 from rfl, List.sliceD_split,
    Bytes.sliceD_writeAt_before _ _ p.toNat 4 (p.toNat + 4) (by omega),
    Bytes.sliceD_writeAt_inside _ _ p.toNat p.toNat 4 (by omega)
      (by rw [B256.length_toBytes]; omega), Nat.sub_self,
    show balanceOfSelectorWord.toBytes.sliceD 0 4 0 = [0x70, 0xa0, 0x82, 0x31] from by decide,
    ← B256.length_toBytes pair.toB256, Bytes.sliceD_writeAt]
  simp only [ExternalOperation.encode, encodeWords, List.flatMap_cons,
    List.flatMap_nil, List.append_nil]

/-- The request allocation after both stores at the moved pointer. -/
def swapRequestSize (n : Nat) (p : B256) : Nat :=
  memExtSize (memExtSize n p.toNat 32) (p.toNat + 4) 32

/-- Memory after one successful balance STATICCALL: the actual input and output
window extensions, then the first returned word over the request. -/
def swapBalanceReply (M : Mem) (p : B256) (pair : Adr) (out : Bytes) : Mem :=
  ((swapBalanceRequest M p pair).extends [(p.toNat, 36), (p.toNat, 32)]).write p.toNat
    (out.take 32)

/-- The request allocation covers the reply word at `p`. -/
theorem swapRequestSize_cover {M : Mem} {p : B256} {n : Nat} (mem : PtrMem p n M) :
    p.toNat + 32 ≤ swapRequestSize n p := by
  have h := (Mem.memWord_write_word M p.toNat balanceOfSelectorWord).2
  have grow := memExtSize_ge (memExtSize n p.toNat 32) (p.toNat + 4) 32
  have size := Mem.size_write_of_size (i := p.toNat) mem.size mem.n32
    (B256.length_toBytes balanceOfSelectorWord)
  rw [size] at h
  unfold swapRequestSize
  omega

/-- The window extensions are already allocated; the reply keeps pointer and size. -/
theorem swapBalanceReply_ptr {M : Mem} {p : B256} {n : Nat} {pair : Adr} (out : Bytes)
    (mem : PtrMem p n M) (lower : 128 ≤ p.toNat) (width : p.toNat + 260 < 2 ^ 256) :
    PtrMem p (swapRequestSize n p) (swapBalanceReply M p pair out) := by
  have req := swapBalanceRequest_ptr (pair := pair) mem lower width
  have cover : p.toNat + 4 + 32 ≤ swapRequestSize n p := by
    have h := (Mem.memWord_write_word (M.write p.toNat balanceOfSelectorWord.toBytes)
      (p + 4).toNat pair.toB256).2
    have p4 : (p + 4).toNat = p.toNat + 4 := swapPtr_add (k := 4) (by omega)
    change (p + 4).toNat + 32 ≤ (swapBalanceRequest M p pair).size at h
    rw [req.size, p4] at h
    exact h
  unfold swapBalanceReply
  generalize requestEq : swapBalanceRequest M p pair = request at req ⊢
  have extendedEq : request.extends [(p.toNat, 36), (p.toNat, 32)] = request := by
    unfold Mem.extends
    rw [req.size]
    change (⟨request.data, memExtSize (memExtSize (swapRequestSize n p) p.toNat 36)
      p.toNat 32⟩ : Mem) = request
    unfold swapRequestSize at cover ⊢
    rw [memExtSize_of_le req.n32 (by omega), memExtSize_of_le req.n32 (by omega), ← req.size]
  rw [extendedEq]
  apply req.write_bytes_of_le p.toNat (out.take 32)
  · rw [List.length_take]
    have := Nat.min_le_left 32 out.length
    unfold swapRequestSize at cover
    omega
  · exact Or.inr (by omega)

/-- Only the first word is decoded, while the actual call retains full returndata. -/
theorem swapBalanceReply_word {M : Mem} {p : B256} {pair : Adr} (wf : Mem.Wf M) (out : Bytes)
    (long : 32 ≤ out.length) :
    Bytes.toB256 ((swapBalanceReply M p pair out).read p.toNat 32).1 =
      Bytes.toB256 (out.take 32) := by
  have length : (out.take 32).length = 32 := by
    rw [List.length_take, Nat.min_eq_left long]
  have requestWf : Mem.Wf (swapBalanceRequest M p pair) :=
    (wf.write _ _).write _ _
  have image := Mem.Reads.extends [(p.toNat, 36), (p.toNat, 32)]
    (Mem.reads_data (swapBalanceRequest M p pair))
  have written := Mem.Reads.write (requestWf.extends [(p.toNat, 36), (p.toNat, 32)])
    image p.toNat (out.take 32)
  unfold swapBalanceReply
  have slice := Bytes.sliceD_writeAt (swapBalanceRequest M p pair).data.toList (out.take 32)
    p.toNat
  rw [length] at slice
  rw [written.read, slice]

/-- The literal STATICCALL staging and code guard after each masked token load.
The two sites stage the same operands through slightly different shuffles. -/
def swapStageTail (second : Bool) : List Ninst :=
  [.reg (.swap 1), .push [0x70, 0xa0, 0x82, 0x31] (by decide), .reg (.swap 1),
    .push [0x24] (by decide), .reg (.dup 0), .reg (.dup (if second then 2 else 3)), .reg .add,
    .reg (.swap 2), .push [0x20] (by decide), .reg (.swap 2)] ++
  (if second then [.reg (.swap 0), .reg (.swap 1), .reg (.swap 0)]
    else [.reg (.swap 1), .reg (.swap 0)]) ++
  [.reg (.dup 2), .reg (.swap 0), .reg .sub, .reg .add, .reg (.dup 1), .reg (.dup 6),
    .reg (.dup 0), .reg .extcodesize, .reg .iszero, .reg (.dup 0), .reg .iszero]

theorem swapStageTail_inv {sevm : Sevm} {b final : Devm} {S : List B256} {M : Mem}
    {G : Nat} {second : Bool} {p tm : B256} (fork : CoveredFork sevm.benvStat.fork)
    (run : Line.Run sevm (St b (tm :: p :: p :: S) M G) (swapStageTail second) final) :
    ∃ gas, final = St (temporalAccountAccessBase b tm.toAdr)
      (B256.eqCheck (B256.eqCheck (b.getCode tm.toAdr).size.toB256 0) 0 ::
        B256.eqCheck (b.getCode tm.toAdr).size.toB256 0 ::
        tm :: p :: 36 :: p :: 32 :: (p + 36) :: 0x70a08231 :: tm :: S) M gas := by
  cases second
  · dsimp only [swapStageTail, ite_false, List.cons_append, List.nil_append] at run
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
    obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_dup rfl hs
    obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_extcodesize fork hs
    obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_iszero hs
    obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_dup rfl hs
    obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨gas, rfl⟩ := ri_iszero hs
    cases run
    exact ⟨gas, by rw [B256.sub_self]; rfl⟩
  · dsimp only [swapStageTail, ite_true, List.cons_append, List.nil_append] at run
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
    obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_dup rfl hs
    obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_extcodesize fork hs
    obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_iszero hs
    obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_dup rfl hs
    obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨gas, rfl⟩ := ri_iszero hs
    cases run
    exact ⟨gas, by rw [B256.sub_self]; rfl⟩

/-- The masked token word each balance query targets. -/
def swapTokenWord (t : B256) : B256 := t &&& 0xffffffffffffffffffffffffffffffffffffffff

/-- One successful post-callback balance query, from the staged STATICCALL
operands to the decoder: the same-derivation call step, its abstract post, the
decoder width and the exact source request. -/
def SwapBalanceCall (D : Exec.Deriv) (sevm : Sevm) (b : Devm) (M : Mem) (p t : B256)
    (S : List B256) (d : Devm) (out : Bytes) : Prop :=
  let tm := swapTokenWord t
  let W := temporalAccountAccessBase b tm.toAdr
  let Q := swapBalanceRequest M p sevm.currentTarget
  let S' := (p + 36) :: 0x70a08231 :: tm :: S
  (b.getCode tm.toAdr).size.toB256 ≠ 0 ∧
  ∃ (gw : B256) (callGas : Nat),
    StepIn D sevm (St W (gw :: tm :: p :: 36 :: p :: 32 :: S') Q callGas) (.exec .staticcall) d ∧
    StaticCallPost W d S' Q p 36 p 32 1 out ∧
    32 ≤ out.length ∧ out.length < 2 ^ 256 ∧
    StaticAnswered sevm W tm.toAdr (ExternalOperation.encode (.balanceOf sevm.currentTarget)) out

/-- From the code guard's staged stack through the call and the return-width
guard, ending at the decoder tree with the actual reply memory. -/
theorem swapBalanceGuard_inv {D : Exec.Deriv} {sevm : Sevm} {b : Devm} {S : List B256}
    {C : List Nat} {M : Mem} {G n : Nat} {p t : B256} {seg : Seg}
    {codeFail failTree callTree okTree shortTree decodeTree : SFunc} (dest0 dest1 dest2 : Bytes)
    (le0 : dest0.length ≤ 32) (le1 : dest1.length ≤ 32) (le2 : dest2.length ≤ 32)
    (fork : CoveredFork sevm.benvStat.fork) (mem : PtrMem p n M)
    (lower : 128 ≤ p.toNat) (width : p.toNat + 260 < 2 ^ 256)
    (codeNo : codeFail.noOk = true) (failNo : failTree.noOk = true)
    (callShape : callTree = .dest (.next (.reg .pop) (.next (.reg .gas)
      (.next (.exec .staticcall) (.next (.reg .iszero) (.next (.reg (.dup 0))
        (.next (.reg .iszero) (.next (.push dest1 le1)
          (.branch failTree okTree)))))))))
    (okShape : okTree = .dest (.next (.reg .pop) (.next (.reg .pop)
      (.next (.reg .pop) (.next (.reg .pop) (.next (.push [0x40] (by decide))
        (.next (.reg .mload) (.next (.reg .returndatasize)
          (.next (.push [0x20] (by decide)) (.next (.reg (.dup 1)) (.next (.reg .lt)
            (.next (.reg .iszero) (.next (.push dest2 le2)
              (.branch shortTree decodeTree))))))))))))))
    (shortNo : shortTree.noOk = true)
    (run : SFunc.RunCutP (StepIn D) cert.prog sevm C
      (St (temporalAccountAccessBase b (swapTokenWord t).toAdr)
        (B256.eqCheck (B256.eqCheck (b.getCode (swapTokenWord t).toAdr).size.toB256 0) 0 ::
          B256.eqCheck (b.getCode (swapTokenWord t).toAdr).size.toB256 0 ::
          swapTokenWord t :: p :: 36 :: p :: 32 :: (p + 36) :: 0x70a08231 :: swapTokenWord t :: S)
        (swapBalanceRequest M p sevm.currentTarget) G)
      (.next (.push dest0 le0) (.branch codeFail callTree)) seg) :
    ∃ (d : Devm) (out : Bytes) (tailGas : Nat),
      SwapBalanceCall D sevm b M p t S d out ∧
      SFunc.RunCutP (StepIn D) cert.prog sevm C
        (St d (out.length.toB256 :: p :: S) (swapBalanceReply M p sevm.currentTarget out) tailGas)
        decodeTree seg := by
  obtain ⟨_, hs, run⟩ := ric_nextP run
  obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun hs)
  rcases ric_branchP run with ⟨_, _, failed⟩ | ⟨accepted, _, run⟩
  · exact (failed.false_of_noOk codeNo).elim
  have zero := eq_zero_of_iszero_ne_zero accepted
  have codeNonzero : (b.getCode (swapTokenWord t).toAdr).size.toB256 ≠ 0 := by
    intro hz
    rw [hz, show B256.eqCheck (0 : B256) 0 = 1 from by decide] at zero
    exact (by decide : (1 : B256) ≠ 0) zero
  rw [callShape] at run
  obtain ⟨gw, callGas, d, out, _, call, post, bound, answered, run⟩ :=
    staticCallGuard_invP dest1 le1 rfl StepIn.toRun fork failNo run
  rw [show (36 : B256).toNat = 36 from rfl,
    swapBalanceRequest_read mem.wf width] at answered
  have reply := swapBalanceReply_ptr (pair := sevm.currentTarget) out mem lower width
  change SFunc.RunCutP (StepIn D) cert.prog sevm C
    (St d (0 :: (p + 36) :: 0x70a08231 :: swapTokenWord t :: S)
      (swapBalanceReply M p sevm.currentTarget out) _) okTree seg at run
  have full : d.returnData.length < 2 ^ 256 := by rw [post.returnData]; exact bound
  obtain ⟨long, tailGas, decoded⟩ :=
    returnWidthGuard_invP dest2 le2 okShape StepIn.toRun reply full shortNo run
  rw [post.returnData] at long decoded
  exact ⟨d, out, tailGas, ⟨codeNonzero, gw, callGas, call, post, long, bound, answered⟩, decoded⟩

/-- The first post-callback query: `balanceOf(pair)` to the cached `token0`. -/
theorem swapFirstBalance_inv {D : Exec.Deriv} {sevm : Sevm} {b : Devm} {R0 : List B256}
    {C : List Nat} {M : Mem} {G n : Nat} {p t1 t0 : B256} {seg : Seg}
    (fork : CoveredFork sevm.benvStat.fork) (mem : PtrMem p n M)
    (lower : 128 ≤ p.toNat) (width : p.toNat + 260 < 2 ^ 256)
    (run : SFunc.RunCutP (StepIn D) cert.prog sevm C
      (St b (t1 :: t0 :: 0 :: 0 :: R0) M G) t_09c3_c5 seg) :
    ∃ (d : Devm) (out : Bytes) (tailGas : Nat),
      SwapBalanceCall D sevm b M p t0 (t1 :: t0 :: 0 :: 0 :: R0) d out ∧
      SFunc.RunCutP (StepIn D) cert.prog sevm C
        (St d (out.length.toB256 :: p :: t1 :: t0 :: 0 :: 0 :: R0)
          (swapBalanceReply M p sevm.currentTarget out) tailGas) t_0a59_c5 seg := by
  unfold t_09c3_c5 at run
  obtain ⟨_, run⟩ := ric_destP run
  change SFunc.RunCutP (StepIn D) cert.prog sevm C _
    (swapRequestLine.foldr SFunc.next
      (.next (.push [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff] (by decide))
        (.next (.reg (.dup 4)) (.next (.reg .and)
          ((swapStageTail false).foldr SFunc.next
            (.next (.push [0x0a, 0x2f] (by decide)) (.branch t_0a2b_c5 t_0a2f_c5))))))) _ at run
  obtain ⟨_, line, run⟩ := SFunc.RunCutP.split_nexts (fun step => StepIn.toRun step) swapRequestLine run
  obtain ⟨_, state⟩ := swapRequestLine_inv mem lower width line
  rw [state] at run
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_dup rfl (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_and (StepIn.toRun hs)
  obtain ⟨_, line, run⟩ := SFunc.RunCutP.split_nexts (fun step => StepIn.toRun step) (swapStageTail false) run
  obtain ⟨_, state⟩ := swapStageTail_inv fork line
  rw [state] at run
  exact swapBalanceGuard_inv (t := t0) _ [0x0a, 0x43] [0x0a, 0x59] _ (by decide) (by decide)
    fork mem lower width (by decide) (by decide) rfl rfl (by decide) run

/-- The second post-callback query: decode `balance0`, then `balanceOf(pair)` to
the cached `token1`, with `balance0` stored in its local slot. -/
theorem swapSecondBalance_inv {D : Exec.Deriv} {sevm : Sevm} {b : Devm} {R0 : List B256}
    {C : List Nat} {M : Mem} {G n : Nat} {p t1 t0 rds : B256} {out0 : Bytes} {seg : Seg}
    (fork : CoveredFork sevm.benvStat.fork) (mem : PtrMem p n M)
    (lower : 128 ≤ p.toNat) (width : p.toNat + 260 < 2 ^ 256) (long0 : 32 ≤ out0.length)
    (run : SFunc.RunCutP (StepIn D) cert.prog sevm C
      (St b (rds :: p :: t1 :: t0 :: 0 :: 0 :: R0) (swapBalanceReply M p sevm.currentTarget out0) G)
      t_0a59_c5 seg) :
    ∃ (d : Devm) (out : Bytes) (tailGas : Nat),
      SwapBalanceCall D sevm b (swapBalanceReply M p sevm.currentTarget out0) p t1
        (t1 :: t0 :: 0 :: Bytes.toB256 (out0.take 32) :: R0) d out ∧
      SFunc.RunCutP (StepIn D) cert.prog sevm C
        (St d (out.length.toB256 :: p :: t1 :: t0 :: 0 :: Bytes.toB256 (out0.take 32) :: R0)
          (swapBalanceReply (swapBalanceReply M p sevm.currentTarget out0) p sevm.currentTarget out)
          tailGas) t_0af5_c5 seg := by
  have reply := swapBalanceReply_ptr (pair := sevm.currentTarget) out0 mem lower width
  have cover := swapRequestSize_cover mem
  unfold t_0a59_c5 at run
  obtain ⟨_, run⟩ := ric_destP run
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_pop (StepIn.toRun hs)
  obtain ⟨d, hs, run⟩ := ric_nextP run
  obtain ⟨_, hd⟩ := ri_mload (StepIn.toRun hs)
  rw [swapBalanceReply_word mem.wf out0 long0, reply.read_self cover] at hd
  subst d
  change SFunc.RunCutP (StepIn D) cert.prog sevm C _
    (swapRequestLine.foldr SFunc.next
      (.next (.reg (.swap 1)) (.next (.reg (.swap 5)) (.next (.reg .pop)
      (.next (.push [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff] (by decide))
        (.next (.reg (.dup 3)) (.next (.reg .and)
          ((swapStageTail true).foldr SFunc.next
            (.next (.push [0x0a, 0xcb] (by decide)) (.branch t_0ac7_c5 t_0acb_c5)))))))))) _ at run
  obtain ⟨_, line, run⟩ := SFunc.RunCutP.split_nexts (fun step => StepIn.toRun step) swapRequestLine run
  obtain ⟨_, state⟩ := swapRequestLine_inv reply lower width line
  rw [state] at run
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_swap rfl (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_swap rfl (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_pop (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_dup rfl (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_and (StepIn.toRun hs)
  obtain ⟨_, line, run⟩ := SFunc.RunCutP.split_nexts (fun step => StepIn.toRun step) (swapStageTail true) run
  obtain ⟨_, state⟩ := swapStageTail_inv fork line
  rw [state] at run
  exact swapBalanceGuard_inv (t := t1) _ [0x0a, 0xdf] [0x0a, 0xf5] _ (by decide) (by decide)
    fork reply lower width (by decide) (by decide) rfl rfl (by decide) run

end Blanc.Lift.UniswapV2Pair
