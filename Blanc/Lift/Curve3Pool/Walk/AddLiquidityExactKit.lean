import Blanc.Lift.Curve3Pool.Walk.ExchangeLiveKit

/-!
# Exact-gas step twins for `add_liquidity`'s stage cores

The forward walk's memory and call steps (`rxe_mloadX`, `rxe_staticWord`) hand their
continuations bounds only. Their literal-memory twins (`rxe_mloadXL`, `rxe_staticWordE`,
`ExchangeLiveKit`) hand on, in addition, the literal memory a call or an expansion leaves and an
exact call's relation `E` (`StaticWordOkAtE`), so a stage core can report its exact cost and its
literal memory while the bounded stage stays its projection. `rxe_mloadXE` and
`rxe_staticWordAlE` are those twins in the form `add_liquidity`'s cores consume. The exact storage
steps (`G = G' + sloadCost …`, `G = G' + sstoreCost …`) are `rxe_sloadVX` and `rxe_sstoreVX`
(`ExchangeLiveKit`); the memories equal at every byte that a crossed `get_D_mem` leaves are
carried by MemGlue's `eqB_*` lemmas.
-/

namespace Blanc.Lift.Curve3Pool

open Jaune Blanc.Lift

section Fwd

variable {fs : List SFunc} {sevm : Sevm} {b : Devm} {S : List B256} {M : Mem} {G : Nat}
  {f : SFunc} {img : Bytes}

/-- `MLOAD` past the memory's end over the image carrier, to some outcome, at the literal
extended memory (`rxe_mloadX` with the memory named). -/
theorem rxe_mloadXE {Q : Outcome → Prop} {i : B256} {o s c : Nat} (hR : Mem.Reads M img)
    (hW : Mem.Wf M) (hsz : M.size = s) (ho : i.toNat = o)
    (hc : gVerylow + (calculateMemoryGasCost (memExtSize s o 32) - calculateMemoryGasCost s) = c ∧
      s % 32 = 0) (hroom : S.length < 1024)
    (k : ∀ M', M' = M.extend o 32 → Mem.Reads M' img → Mem.Wf M' →
      M'.size = memExtSize s o 32 →
      SFunc.RunEx fs sevm (St b (Bytes.toB256 (img.sliceD o 32 0) :: S) M' G) f Q) :
    SFunc.RunEx fs sevm (St b (i :: S) M (G + c)) (.next (.reg .mload) f) Q :=
  rxe_mloadXL hR hW hsz ho hc hroom (k _ rfl)

end Fwd

/-- **A one-word `STATICCALL` answered by a relation premise, forward**: `rxe_staticWord` over
`StaticWordOkAtE`, the continuation also receiving the literal post memory and `E` at the
call's actual input and gas. -/
theorem rxe_staticWordAlE {sevm : Sevm} {W W' : Devm → Prop} {σ : Stor} {b : Devm}
    {S : List B256} {M : Mem} {img : Bytes} {G U : Nat} {t A ii is oi : B256} {data : Bytes}
    {o s : Nat} {Q : Outcome → Prop} {f : SFunc} {E : Devm → List B256 → Mem → Nat → Devm → Prop}
    (hL : ExLive sevm W b σ) (hW'c : WClosed sevm W')
    (hp : StaticWordOkAtE sevm W W' t data A U ii is oi E) (hU : U ≤ G) (hG : G < 2 ^ 256)
    (hroom : S.length < 1024)
    (hin : (M.read ii.toNat is.toNat).1 = data) (hR : Mem.Reads M img) (hW : Mem.Wf M)
    (hoi : oi.toNat = o)
    (hext : (M.extends [(ii.toNat, is.toNat), (oi.toNat, 0x20)]).size = s) (hfit : o + 0x20 ≤ s)
    (k : ∀ (d : Devm) (M' : Mem) (out : Bytes), ExLive sevm W' d σ →
      Mem.Reads M' (Bytes.writeAt img o (out.take 0x20)) → Mem.Wf M' → M'.size = s →
      32 ≤ out.length → out.length < 2 ^ 256 → Bytes.toB256 (out.take 32) = A →
      d.returnData = out → G ≤ d.gasLeft + U → d.gasLeft ≤ G →
      M' = (M.extends [(ii.toNat, is.toNat), (oi.toNat, 0x20)]).write o (out.take 0x20) →
      E b S M G d →
      SFunc.RunEx cert.prog sevm (St d (1 :: S) M' d.gasLeft) f Q) :
    SFunc.RunEx cert.prog sevm (St b (Nat.toB256 G :: t :: ii :: is :: oi :: 0x20 :: S) M G)
      (.next (.exec .staticcall) f) Q :=
  rxe_staticWordE hL hW'c hp hU hG hroom hin hR hW hoi hext hfit k

end Blanc.Lift.Curve3Pool
