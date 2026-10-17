import Blanc.Composition.UniswapV2PairWeth9SwapLegs
import Blanc.Lift.UniswapV2Pair.SwapBackTurns

/-!
# WETH9 `balanceOf` read legs at a caller-fixed need (C4(b), U8b1)

`wethReadLeg` is the WETH9 `balanceOf(pair)` `STATICCALL` (`wethBalanceCall`) at the call gas that
makes its residual gas exactly what the caller's continuation needs, for any need that reads the
call's result only off its gas-free columns.  The need is evaluated on the gas-free skeleton
(`wethBalanceSkel`), and the call gas is that need plus the access, expansion and WETH9 charges.

The swap's first post-callback query with WETH9 as `token0` (`swapWethRead0`) is the first
instance; the sync and mint reads are in `UniswapV2PairWeth9LegsSync` and `UniswapV2PairWeth9LegsMint`.
Code-only: no premise mentions WETH9's answer or the callback subtree.
-/

namespace Blanc.Composition.UniswapV2PairWeth9Joint

open Jaune Blanc Blanc.Lift Blanc.Lift.UniswapV2Pair

/-! ## The generic read leg -/

section ReadLeg

variable (sevm : Sevm) (B : Devm) (S : List B256) (M : Mem) (p t : B256) (need : Devm → Nat)

/-- The call gas of a WETH9 `balanceOf` query whose caller needs `need d` left after it. -/
def readLegGas : Nat :=
  need (wethBalanceSkel sevm B S M p t) +
    (balAcc B t + balExt sevm B S M p t + balUsed sevm B S M p t)

/-- **The WETH9 `balanceOf(pair)` `STATICCALL` at the call gas the caller's need fixes**: its
result and its call gas. -/
noncomputable def wethReadLeg : Devm × Nat :=
  (wethBalanceCall sevm B S M p t (readLegGas sevm B S M p t need), readLegGas sevm B S M p t need)

end ReadLeg

/-- **Spec of the generic read leg.**  WETH9's code at the token, no precompile there, call depth
left, stack room, a well-formed memory, the window's width, the call gas a word, and room for
WETH9's view under the 63/64 rule: the query runs from its staged state, succeeds, replies with the
pair's WETH9 balance word, and leaves exactly what the caller needs. -/
theorem wethReadLeg_spec {sevm : Sevm} {B : Devm} {S : List B256} {M : Mem} {p t : B256}
    {need : Devm → Nat} (gasFree : ∀ d x, need (d.withGasLeft x) = need d)
    (fork : CoveredFork sevm.benvStat.fork)
    (hcode : B.state.getCode (balTok t) = Weth9.code) (depth : sevm.depth ≠ 0)
    (notPrecompile : sevm.benvStat.rules.isPrecomp (balTok t) = false)
    (stackRoom : S.length < 1018) (wf : Mem.Wf M) (width : p.toNat + 260 < 2 ^ 256)
    (fits : (wethReadLeg sevm B S M p t need).2 < 2 ^ 256)
    (room : balUsed sevm B S M p t ≤
      except64th (need (wethBalanceSkel sevm B S M p t) + balUsed sevm B S M p t)) :
    Ninst.RunCompiled sevm (balCallState sevm B S M p t (wethReadLeg sevm B S M p t need).2)
        (.exec .staticcall) (wethReadLeg sevm B S M p t need).1 ∧
      (wethReadLeg sevm B S M p t need).1.stack = 1 :: balRest S p t ∧
      (wethReadLeg sevm B S M p t need).1.returnData =
        (B.getStorVal (balTok t) (Weth9.balSlot sevm.currentTarget)).toBytes ∧
      (wethReadLeg sevm B S M p t need).1.gasLeft = need (wethReadLeg sevm B S M p t need).1 := by
  have spec := wethBalanceCall_spec (sevm := sevm) (B := B) (S := S) (M := M) (p := p) (t := t)
    (cg := readLegGas sevm B S M p t need) fork hcode depth notPrecompile stackRoom wf width fits
    (by unfold readLegGas; omega)
    (by
      have e : readLegGas sevm B S M p t need - balExt sevm B S M p t - balAcc B t =
          need (wethBalanceSkel sevm B S M p t) + balUsed sevm B S M p t := by
        unfold readLegGas; omega
      rw [e]
      exact room)
  obtain ⟨hrun, hstk, hret, hgas⟩ := spec
  refine ⟨hrun, hstk, hret, ?_⟩
  have hskel : wethBalanceCall sevm B S M p t (readLegGas sevm B S M p t need) =
      (wethBalanceSkel sevm B S M p t).withGasLeft _ :=
    wethBalanceCallAt_eq _ _ _ _ _ _ _ _ _ _
  change (wethBalanceCall sevm B S M p t (readLegGas sevm B S M p t need)).gasLeft =
    need (wethBalanceCall sevm B S M p t (readLegGas sevm B S M p t need))
  rw [hgas]
  conv => rhs; rw [hskel, gasFree]
  unfold readLegGas
  omega

/-- The reply word of a WETH9 `balanceOf` reply, as the Pair's decoders read it. -/
theorem toB256_take_toBytes (v : B256) : Bytes.toB256 (v.toBytes.take 32) = v := by
  rw [List.take_of_length_le (by rw [B256.length_toBytes]), B256.toB256_toBytes]

/-- A WETH9 reply is at least one word long. -/
theorem toBytes_long (v : B256) : 32 ≤ v.toBytes.length := by
  rw [B256.length_toBytes]

/-! ## The swap's first post-callback query (WETH9 = token0) -/

section Read0

variable (sevm : Sevm) (d : Devm) (M : Mem) (n : Nat) (p : B256) (w : SwapCutWords) (ρ : B256)
  (R : List B256) (callGas1 : Nat)

/-- The words under the first query's operands. -/
def read0Stack : List B256 := w.token1 :: w.token0 :: 0 :: 0 :: swapCutTail w ρ R

/-- What the Pair needs left after the first query: the second query's staging and call gas (the
record's `tailGas + 64`). -/
def read0Need (d0 : Devm) : Nat :=
  callGas1 + 5 + swapRequestCharge d0 (swapRequestSize n p) p w.token1 83 + 21 + 64

end Read0

/-- The WETH9 first post-callback `balanceOf(pair)` `STATICCALL` of the swap (token0 = WETH9), at
the join world `d`: its result and the call gas WETH9's code determines, given the second query's
call gas `callGas1`. -/
noncomputable def swapWethRead0 (sevm : Sevm) (d : Devm) (M : Mem) (n : Nat) (p : B256)
    (w : SwapCutWords) (ρ : B256) (R : List B256) (callGas1 : Nat) : Devm × Nat :=
  wethReadLeg sevm d (read0Stack w ρ R) M p w.token0 (read0Need n p w callGas1)

theorem read0Need_gasFree (n : Nat) (p : B256) (w : SwapCutWords) (callGas1 : Nat) (d : Devm)
    (x : Nat) : read0Need n p w callGas1 (d.withGasLeft x) = read0Need n p w callGas1 d := rfl

theorem weth9_code_nonzero {b : Devm} {a : Adr} (h : b.state.getCode a = Weth9.code) :
    (b.getCode a).size.toB256 ≠ 0 := by
  change (b.state.getCode a).size.toB256 ≠ 0
  rw [h]
  exact weth9_code_size_word

/-- **The swap's first WETH9 read leg (WETH9 = token0), frame level.**  At the post-callback join
world `d`: WETH9's code at token0 there, not a precompile, call depth left, a well-formed memory,
the pointer's width bound, stack room, the call gas a word, and room for WETH9's view.  Then
`swapWethRead0` is the `SwapBackCalleeEnv.first` record, and its reply is the pair's WETH9 balance
at `d`.  Code-only: nothing is assumed of the callback subtree or of WETH9's answer. -/
theorem swapWethRead0_spec {sevm : Sevm} {d : Devm} {M : Mem} {n : Nat} {p : B256}
    {w : SwapCutWords} {ρ : B256} {R : List B256} {callGas1 : Nat}
    (fork : CoveredFork sevm.benvStat.fork) (depth : sevm.depth ≠ 0)
    (wethCode : d.state.getCode (swapTokenWord w.token0).toAdr = Weth9.code)
    (notPrecompile : sevm.benvStat.rules.isPrecomp (swapTokenWord w.token0).toAdr = false)
    (wf : Mem.Wf M) (width : p.toNat + 260 < 2 ^ 256)
    (stackRoom : (swapCutTail w ρ R).length < 1014)
    (fits : (swapWethRead0 sevm d M n p w ρ R callGas1).2 < 2 ^ 256)
    (room : balUsed sevm d (read0Stack w ρ R) M p w.token0 ≤
      except64th (read0Need n p w callGas1 (wethBalanceSkel sevm d (read0Stack w ρ R) M p w.token0) +
        balUsed sevm d (read0Stack w ρ R) M p w.token0)) :
    SwapBalanceEnv sevm d M p w.token0 (w.token1 :: w.token0 :: 0 :: 0 :: swapCutTail w ρ R)
      (swapWethRead0 sevm d M n p w ρ R callGas1).1 (swapWethRead0 sevm d M n p w ρ R callGas1).2
      (callGas1 + 5 + swapRequestCharge (swapWethRead0 sevm d M n p w ρ R callGas1).1
        (swapRequestSize n p) p w.token1 83 + 21) ∧
    (swapWethRead0 sevm d M n p w ρ R callGas1).1.returnData =
      (d.getStorVal (swapTokenWord w.token0).toAdr (Weth9.balSlot sevm.currentTarget)).toBytes := by
  obtain ⟨hrun, hstk, hret, hgas⟩ := wethReadLeg_spec (sevm := sevm) (B := d) (S := read0Stack w ρ R)
    (M := M) (p := p) (t := w.token0) (need := read0Need n p w callGas1) (read0Need_gasFree n p w callGas1)
    fork wethCode depth notPrecompile (by simp only [read0Stack, List.length_cons]; omega) wf width
    fits room
  unfold swapWethRead0
  exact ⟨⟨weth9_code_nonzero wethCode, hrun, hstk, by rw [hret]; exact toBytes_long _, hgas⟩, hret⟩

end Blanc.Composition.UniswapV2PairWeth9Joint
