import Blanc.Lift.VyperArraySlot
import Blanc.Lift.StaticCall
import Blanc.Lift.StableSwapNewton.Defs

/-!
# A balance difference across a call: two `balanceOf` replies and a checked subtraction

Vyper 0.2.x credits a fee-on-transfer coin with what actually arrived:

```
before = ERC20(coin).balanceOf(self)   # STATICCALL, success asserted, RETURNDATASIZE > 31
... raw_call(coin, transferFrom(...)) ...
credited = ERC20(coin).balanceOf(self) - before   # checked SUB
```

This module gives the two contract-neutral pieces, as trees with their inversion and
forward twins, and the arithmetic that composes them:

* `vyReplyWord`: the tail after a `STATICCALL` whose output window is one word at `O`:
  `PUSH2 ok JUMPI` (revert on failure), `PUSH1 0x1f RETURNDATASIZE GT PUSH2 ok JUMPI`
  (revert on a reply of at most 31 bytes), `PUSH1 0 POP PUSH2 O MLOAD`.
  `ric_vyStaticReply` inverts the call node and the tail together: the call succeeded, a static
  child message to the callee answered `out` with `31 < out.length`, and the pushed word is
  `Bytes.toB256 (out.take 32)`; `rxc_vyStaticReply` is the forward twin, over the call step
  supplied as a premise (the callee's behaviour is a premise of any liveness statement).
* `vyChkSubMem`: `PUSH2 V MLOAD DUP1 DUP3 LT ISZERO PUSH2 ok JUMPI` (revert on underflow),
  `JUMPDEST DUP1 DUP3 SUB SWAP1 POP SWAP1 POP` — the reply on the stack minus the word saved
  at `V`.  `ric_vyChkSubMem` / `rxc_vyChkSubMem`.
* `chkSub_of_le`: the pushed difference is `StableSwapNewton.chkSub post pre` — with
  `post`, `pre` the two answers this is the credited amount.

A walk applies `ric_vyStaticReply` at both `balanceOf` sites (the first value stored at `V`),
walks the call in between, and finishes with `ric_vyChkSubMem` at `V`.
Nothing here mentions a contract.
-/

namespace Blanc.Lift

open Jaune

/-- A 32-byte payload written at `n` reads back, on any memory (no `Mem.Wf`). -/
theorem Mem.read_write_32 (μ : Mem) (n : Nat) {ys : Bytes} (h : ys.length = 32) :
    ((μ.write n ys).read n 32).1 = ys := by
  rw [← Bytes.toBytes_toB256_of_length h]
  exact Mem.read_write_word_self μ n _

/-- The tail after a one-word-output `STATICCALL` (see the module doc). -/
def vyReplyWord (h1 l1 h2 l2 oh ol : UInt8) (fail1 fail2 f : SFunc) : SFunc :=
  .next (.push [h1, l1] (by simp only [List.length_cons, List.length_nil, zero_add,
    Nat.reduceAdd, Nat.reduceLeDiff]))
  (.branch fail1 (.dest
    (.next (.push [0x1f] (by decide)) (.next (.reg .returndatasize) (.next (.reg .gt)
    (.next (.push [h2, l2] (by simp only [List.length_cons, List.length_nil, zero_add,
      Nat.reduceAdd, Nat.reduceLeDiff]))
    (.branch fail2 (.dest
      (.next (.push [0x00] (by decide)) (.next (.reg .pop)
      (.next (.push [oh, ol] (by simp only [List.length_cons, List.length_nil, zero_add,
        Nat.reduceAdd, Nat.reduceLeDiff]))
      (.next (.reg .mload) f))))))))))))

/-- The checked subtraction of the word saved at `V` from the stack top (see the module doc). -/
def vyChkSubMem (vh vl h l : UInt8) (fail f : SFunc) : SFunc :=
  .next (.push [vh, vl] (by simp only [List.length_cons, List.length_nil, zero_add,
    Nat.reduceAdd, Nat.reduceLeDiff]))
  (.next (.reg .mload) (.next (.reg (.dup 0)) (.next (.reg (.dup 2)) (.next (.reg .lt)
  (.next (.reg .iszero) (.next (.push [h, l] (by simp only [List.length_cons, List.length_nil,
    zero_add, Nat.reduceAdd, Nat.reduceLeDiff]))
  (.branch fail (.dest (.next (.reg (.dup 0)) (.next (.reg (.dup 2)) (.next (.reg .sub)
    (.next (.reg (.swap 0)) (.next (.reg .pop) (.next (.reg (.swap 0)) (.next (.reg .pop)
      f)))))))))))))))

/-- The memory a one-word `STATICCALL` leaves, as `StaticCallPost` states it. -/
def staticOutMem (M : Mem) (ii is oi os : B256) (out : Bytes) : Mem :=
  (M.extends [(ii.toNat, is.toNat), (oi.toNat, os.toNat)]).write oi.toNat (out.take os.toNat)

/-- A word difference that does not underflow is the checked difference. -/
theorem chkSub_of_le {x y : B256} (h : y.toNat ≤ x.toNat) :
    StableSwapNewton.chkSub x.toNat y.toNat = some (x - y).toNat := by
  rw [StableSwapNewton.chkSub, ite_eq_left h, B256.toNat_sub_eq_of_le _ _
    (B256.le_iff_toNat_le_toNat.mpr h)]

section Inv

variable {fs : List SFunc} {sevm : Sevm} {C : List Nat} {b : Devm} {S : List B256} {M : Mem}
  {G : Nat} {f : SFunc} {r : Seg}

/-- **A one-word `STATICCALL` and its reply checks, inverted.**  Over an output window of one
word at `O` (the pushed `[oh, ol]`): the call succeeded, the callee answered `out` through a
static child message (`StaticAnswered`), `out` is longer than 31 bytes, and the continuation
starts from the call's successor `d` with the first word of `out` on the stack. -/
theorem ric_vyStaticReply {h1 l1 h2 l2 oh ol : UInt8} {fail1 fail2 : SFunc}
    {g t ii is oi os : B256} (hoi : oi = Bytes.toB256 [oh, ol]) (hos : os.toNat = 32)
    (hfork : CoveredFork sevm.benvStat.fork) (hf1 : fail1.noOk = true) (hf2 : fail2.noOk = true)
    (run : SFunc.RunCut fs sevm C (St b (g :: t :: ii :: is :: oi :: os :: S) M G)
      (.next (.exec .staticcall) (vyReplyWord h1 l1 h2 l2 oh ol fail1 fail2 f)) r) :
    ∃ out d G', StaticCallPost b d S M ii is oi os 1 out ∧
      StaticAnswered sevm b t.toAdr (M.read ii.toNat is.toNat).1 out ∧
      31 < out.length ∧
      SFunc.RunCut fs sevm C
        (St d (Bytes.toB256 (out.take 32) :: S)
          ((staticOutMem M ii is oi os out).read oi.toNat 32).2 G') f r := by
  obtain ⟨d0, s0, run⟩ := ric_next run
  obtain ⟨flag, out, hpost, hlt, hans⟩ := ri_staticcall_bounded hfork s0
  rw [hpost.eq_St] at run
  unfold vyReplyWord at run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G1, rfl⟩ := ri_push s1
  rcases ric_branch run with ⟨-, G2, run⟩ | ⟨hflag, G2, run⟩
  · exact (run.false_of_noOk hf1).elim
  have h1 : flag = 1 := hpost.flag.resolve_left hflag
  obtain ⟨G3, run⟩ := ric_dest run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G4, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G5, rfl⟩ := ri_returndatasize s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G6, rfl⟩ := ri_gt s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G7, rfl⟩ := ri_push s1
  rcases ric_branch run with ⟨-, G8, run⟩ | ⟨hgt, G8, run⟩
  · exact (run.false_of_noOk hf2).elim
  have hlen : 31 < out.length := by
    rw [hpost.returnData] at hgt
    by_contra hle
    apply hgt
    simp only [B256.gtCheck]
    rw [ite_eq_right]
    rw [GT.gt, B256.lt_iff_toNat_lt_toNat, B256.toNat_toB256_of_lt hlt,
      show (Bytes.toB256 [0x1f]).toNat = 31 by decide]
    omega
  obtain ⟨G9, run⟩ := ric_dest run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G10, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G11, rfl⟩ := ri_pop s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G12, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G13, rfl⟩ := ri_mload s1
  rw [← hoi] at run
  have htake : (out.take os.toNat).length = 32 := by
    rw [hos, List.length_take]; omega
  have hread : ((staticOutMem M ii is oi os out).read oi.toNat 32).1 = out.take 32 := by
    unfold staticOutMem
    rw [Mem.read_write_32 _ _ htake, hos]
  rw [← h1] at hans
  refine ⟨out, d0, G13, h1 ▸ hpost, hans rfl, hlen, ?_⟩
  unfold staticOutMem at hread ⊢
  rw [hread] at run
  exact run

/-- **The checked subtraction from a saved word, inverted.**  With `pre` the word saved at `V`:
`pre ≤ post`, and the continuation sees `post - pre`. -/
theorem ric_vyChkSubMem {vh vl h l : UInt8} {fail : SFunc} {post : B256}
    (hf : fail.noOk = true)
    (run : SFunc.RunCut fs sevm C (St b (post :: S) M G) (vyChkSubMem vh vl h l fail f) r) :
    let pre := Bytes.toB256 (M.read (Bytes.toB256 [vh, vl]).toNat 32).1
    pre.toNat ≤ post.toNat ∧ ∃ G', SFunc.RunCut fs sevm C
      (St b ((post - pre) :: S) (M.read (Bytes.toB256 [vh, vl]).toNat 32).2 G') f r := by
  intro pre
  unfold vyChkSubMem at run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G1, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G2, rfl⟩ := ri_mload s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G3, rfl⟩ := ri_dup (n := 0) (w := pre) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G4, rfl⟩ := ri_dup (n := 2) (w := post) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G5, rfl⟩ := ri_lt s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G6, rfl⟩ := ri_iszero s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G7, rfl⟩ := ri_push s1
  rcases ric_branch run with ⟨-, G8, run⟩ | ⟨hw, G8, run⟩
  · exact (run.false_of_noOk hf).elim
  have hle : pre.toNat ≤ post.toNat := by
    by_contra hlt
    apply hw
    have : post < pre := by
      rw [B256.lt_iff_toNat_lt_toNat]; omega
    simp only [B256.ltCheck, this, ↓reduceIte, B256.eqCheck]
    decide
  obtain ⟨G9, run⟩ := ric_dest run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G10, rfl⟩ := ri_dup (n := 0) (w := pre) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G11, rfl⟩ := ri_dup (n := 2) (w := post) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G12, rfl⟩ := ri_sub s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G13, rfl⟩ := ri_swap (S' := pre :: (post - pre) :: post :: S) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G14, rfl⟩ := ri_pop s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G15, rfl⟩ := ri_swap (S' := post :: (post - pre) :: S) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G16, rfl⟩ := ri_pop s1
  exact ⟨hle, G16, run⟩

end Inv

section Fwd

variable {fs : List SFunc} {sevm : Sevm} {C : List Nat} {b : Devm} {S : List B256} {M : Mem}
  {G : Nat} {f : SFunc} {r : Seg}

/-- **A one-word `STATICCALL` and its reply checks, forward.**  The call step to `d` is a
premise; given its successful outcome `out` (`StaticCallPost` with flag `1`) longer than 31
bytes, over an output memory that is word-aligned and covers the window, the tail costs 47
gas. -/
theorem rxc_vyStaticReply {h1 l1 h2 l2 oh ol : UInt8} {fail1 fail2 : SFunc}
    {g t ii is oi os : B256} {d : Devm} {out : Bytes}
    (hoi : oi = Bytes.toB256 [oh, ol]) (hos : os.toNat = 32)
    (hcall : Ninst.RunCompiled sevm (St b (g :: t :: ii :: is :: oi :: os :: S) M G)
      (.exec .staticcall) d)
    (hpost : StaticCallPost b d S M ii is oi os 1 out) (hlen : 31 < out.length)
    (hlt : out.length < 2 ^ 256)
    (h32 : (staticOutMem M ii is oi os out).size % 32 = 0)
    (hcov : oi.toNat + 32 ≤ (staticOutMem M ii is oi os out).size)
    (hroom : S.length + 2 < 1024) {G' : Nat} (hgas : d.gasLeft = G' + 47)
    (k : SFunc.RunExactCut fs sevm C
      (St d (Bytes.toB256 (out.take 32) :: S) (staticOutMem M ii is oi os out) G') f r) :
    SFunc.RunExactCut fs sevm C (St b (g :: t :: ii :: is :: oi :: os :: S) M G)
      (.next (.exec .staticcall) (vyReplyWord h1 l1 h2 l2 oh ol fail1 fail2 f)) r := by
  refine .next hcall ?_
  unfold staticOutMem at h32 hcov k
  rw [hpost.eq_St, hgas]
  unfold vyReplyWord
  refine rxc_push (G := G' + 44) rfl (by (try simp only [List.length_cons]); omega) ?_
  refine rxc_branch_succ (by decide) (rxc_dest ?_)
  refine rxc_push (G := G' + 30) rfl (by omega) ?_
  refine rxc_returndatasize (G := G' + 28) (by (try simp only [List.length_cons]); omega) ?_
  refine rxc_binary (fn := B256.gtCheck) (c := gVerylow) (v := 1) (G := G' + 25)
    (by rintro ⟨⟩) (fun _ => rfl) ?_ (by omega) ?_
  · rw [hpost.returnData]
    simp only [B256.gtCheck]
    rw [ite_eq_left]
    rw [GT.gt, B256.lt_iff_toNat_lt_toNat, B256.toNat_toB256_of_lt hlt,
      show (Bytes.toB256 [0x1f]).toNat = 31 by decide]
    exact hlen
  refine rxc_push (G := G' + 22) rfl (by (try simp only [List.length_cons]); omega) ?_
  refine rxc_branch_succ (by decide) (rxc_dest ?_)
  refine rxc_push (G := G' + 8) rfl (by omega) ?_
  refine rxc_pop ?_
  refine rxc_push (G := G' + 3) rfl (by omega) ?_
  rw [← hoi]
  refine rxc_mload (c := 3) ?_ ?_ ?_ (by omega) k
  · rw [St, Devm.extCost_zero_of_le h32 hcov]; rfl
  · have htake : (out.take os.toNat).length = 32 := by
      rw [hos, List.length_take]; omega
    rw [Mem.read_write_32 _ _ htake, hos]
  · exact Mem.read_snd_eq_self (memExtSize_of_le h32 hcov)

/-- **The checked subtraction from a saved word, forward** (51 gas over a word-aligned memory
covering `V`). -/
theorem rxc_vyChkSubMem {vh vl h l : UInt8} {fail : SFunc} {post pre : B256}
    (hpre : Bytes.toB256 (M.read (Bytes.toB256 [vh, vl]).toNat 32).1 = pre)
    (hle : pre.toNat ≤ post.toNat)
    (h32 : M.size % 32 = 0) (hcov : (Bytes.toB256 [vh, vl]).toNat + 32 ≤ M.size)
    (hroom : S.length + 4 < 1024)
    (k : SFunc.RunExactCut fs sevm C (St b ((post - pre) :: S) M G) f r) :
    SFunc.RunExactCut fs sevm C (St b (post :: S) M (G + 51)) (vyChkSubMem vh vl h l fail f) r := by
  unfold vyChkSubMem
  refine rxc_push (G := G + 48) rfl (by (try simp only [List.length_cons]); omega) ?_
  refine rxc_mload (c := 3) ?_ hpre (Mem.read_snd_eq_self (memExtSize_of_le h32 hcov))
    (by (try simp only [List.length_cons]); omega) ?_
  · rw [St, Devm.extCost_zero_of_le h32 hcov]; rfl
  refine rxc_dup (n := 0) (w := pre) rfl (by (try simp only [List.length_cons]); omega) ?_
  refine rxc_dup (n := 2) (w := post) rfl (by (try simp only [List.length_cons]); omega) ?_
  refine rxc_lt (v := 0) ?_ (by (try simp only [List.length_cons]); omega) ?_
  · simp only [B256.ltCheck]
    rw [ite_eq_right]
    rw [B256.lt_iff_toNat_lt_toNat]; omega
  refine rxc_iszero (v := 1) (by simp only [B256.eqCheck, ↓reduceIte])
    (by (try simp only [List.length_cons]); omega) ?_
  refine rxc_push (G := G + 30) rfl (by (try simp only [List.length_cons]); omega) ?_
  refine rxc_branch_succ (by decide) (rxc_dest ?_)
  refine rxc_dup (n := 0) (w := pre) rfl (by (try simp only [List.length_cons]); omega) ?_
  refine rxc_dup (n := 2) (w := post) rfl (by (try simp only [List.length_cons]); omega) ?_
  refine rxc_binary (fn := (· - ·)) (c := gVerylow) (v := post - pre) (G := G + 10)
    (by rintro ⟨⟩) (fun _ => rfl) rfl (by (try simp only [List.length_cons]); omega) ?_
  refine rxc_swap (n := 0) (S' := pre :: (post - pre) :: post :: S) rfl ?_
  refine rxc_pop ?_
  refine rxc_swap (n := 0) (S' := post :: (post - pre) :: S) rfl ?_
  exact rxc_pop k

end Fwd

end Blanc.Lift
