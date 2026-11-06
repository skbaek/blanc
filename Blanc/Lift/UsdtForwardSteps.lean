import Blanc.Lift.WalkFpMove

/-!
# Forward steps of a solc 0.4 runtime

`xs` covers a walk over a free-memory pointer at `0x80`. A solc 0.4 runtime keeps it at `0x60`, so its
event and result word lands in the word that the image grows into, and its packed reads go through
`EXP`. `ys` is `xs` plus those steps, and names no contract.
-/

namespace Blanc.Lift.AccumulatedWalk

open Jaune Blanc Blanc.Lift

/-- The charge of an `MSTORE` at `0x60` over an image of `n` bytes. -/
def memC (n : Nat) : Nat := if n = 96 then 6 else 3

theorem memC_le (n : Nat) : memC n ≤ 6 := by
  unfold memC
  split <;> omega

section Steps

variable {fs : List SFunc} {sevm : Sevm} {b : Devm} {S : List B256} {M : Mem} {G : Nat}
  {f : SFunc} {o : Outcome} {n : Nat} {fp : B256}

/-- `MSTORE` at `0x60`, the word just above a three-word image or inside a four-word one. -/
theorem rx_mstore60 {i v : B256} (hM : FpM fp n M) (hn : n = 96 ∨ n = 128) (hi : i.toNat = 96)
    (k : FpM fp 128 (M.write 96 v.toBytes) →
      SFunc.RunExact fs sevm (St b S (M.write 96 v.toBytes) G) f o) :
    SFunc.RunExact fs sevm (St b (i :: v :: S) M (G + memC n)) (.next (.reg .mstore) f) o := by
  rcases hn with rfl | rfl
  · exact rx_mstoreGrow hM hi (le_refl _) rfl k
  · exact rx_mstoreP (i0 := 96) hM hi (by decide) (by decide) (k (hM.write 96 v (by decide) (by decide)))

end Steps

/-- One accumulated forward step of a solc 0.4 runtime: `xs`, or `EXP`, or the word at `0x60` and the
event over it. -/
macro "ys" : tactic => `(tactic| first
  | xs
  | (xunfold; apply rk; refine rx_exp' rfl (by xroom) ?_)
  | (xunfold; apply rk; refine rx_mstore60 (by xfp) (by first | exact Or.inl rfl | exact Or.inr rfl | assumption)
      (by decide) fun _ => ?_)
  | (xunfold; apply rk; refine rx_log3At (by with_reducible assumption) (by with_reducible rfl) (by xfp) (by xfp)
      (by decide) (by decide) (by decide) ?_))

open _root_.Lean _root_.Lean.Elab _root_.Lean.Elab.Tactic in
/-- `ys` until it fails. -/
elab "yrun" : tactic => do
  let mut i := 0
  while i < 100000 do
    let ok ← (do evalTactic (← `(tactic| ys)); pure true) <|> pure false
    if !ok then break
    i := i + 1

open _root_.Lean _root_.Lean.Elab _root_.Lean.Elab.Tactic _root_.Lean.Meta in
/-- `ys` until the walk stands at the named tree, for a walk split at a tree boundary. -/
elab "yrunTo " t:ident : tactic => withMainContext do
  let n ← realizeGlobalConstNoOverloadWithInfo t
  let atTree : TacticM Bool := do
    let tgt := (← instantiateMVars (← getMainTarget)).cleanupAnnotations
    match tgt.getAppArgs[3]? with
    | some f => isDefEq f (mkConst n)
    | none => return false
  let mut i := 0
  while i < 100000 do
    if ← atTree then return
    evalTactic (← `(tactic| ys))
    i := i + 1

/-- **What a frame that stops leaves**: `FrameLands` for a missing return value, the reply empty. -/
structure StopLands (prog : List SFunc) (sevm : Sevm) (pre post : Devm) (used : Nat) (σ' : Stor) (R : Prop) : Prop where
  run : SProg.RunExact prog sevm pre post
  gas : post.gasLeft = pre.gasLeft - used
  out : post.output = []
  keeps : Keeps sevm pre post
  stor : Devm.getStor post sevm.currentTarget = σ'
  refund : R → pre.refundCounter ≤ post.refundCounter

/-- A frame run to `STOP` at every residual gas above the store sentry lands. -/
theorem stopLands_of {prog : List SFunc} {f : SFunc} {sevm : Sevm} {pre B : Devm} {S : List B256} {M : Mem}
    {c K : Nat} {σ' : Stor} {R : Prop} (hf : prog[0]? = some f)
    (hrun : ∀ G, 2300 ≤ G → SFunc.RunExact prog sevm (St pre [] Mem.empty (G + c)) f (.halted (St B S M G)))
    (hs : pre.stack = []) (hm : pre.memory = Mem.empty) (hc : c ≤ K) (hgas : K + 2300 ≤ pre.gasLeft)
    (hk : Keeps sevm pre B) (hst : Devm.getStor B sevm.currentTarget = σ') (hout : B.output = [])
    (hr : R → pre.refundCounter ≤ B.refundCounter) :
    StopLands prog sevm pre (St B S M (pre.gasLeft - c)) c σ' R := by
  refine ⟨⟨f, hf, ?_⟩, rfl, hout, ⟨hk.code, hk.other, hk.error, hk.created⟩, hst, hr⟩
  have h := hrun (pre.gasLeft - c) (by omega)
  rwa [pre_eq_St hs hm (Nat.sub_add_cancel (by omega))] at h

end Blanc.Lift.AccumulatedWalk
