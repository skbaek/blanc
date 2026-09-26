import Blanc.Lift.PackedSha

/-!
# The solc packed-SHA site over memory that already covers the destination

`copy_sha_gen` (`Blanc/Lift/PackedSha.lean`) walks a solc 0.6 `sha256(abi.encodePacked(...))`
site's copy loop, merge and precompile call over memory of any word-aligned size `n ≥ d`.
`copy_sha_covered` is its corollary for memory that already covers the destination's three
words (`d + 0x60 ≤ n`): a flat 598-gas charge, memory keeps its size, and the image facts a
caller needs are stated directly (the free-pointer word, the digest, everything below `d`).

Also: the cut walk step for `CALLDATACOPY`.

Nothing here mentions a contract.
-/

namespace Blanc.Lift

open Jaune

section CutCopy

variable {fs : List SFunc} {sevm : Sevm} {C : List Nat} {b : Devm} {f : SFunc} {r : Seg}
  {S : List B256} {M : Mem} {G : Nat}

/-- `CALLDATACOPY` inside a cut run. -/
theorem rxc_calldatacopy {di si sz : B256} {c : Nat} {M' : Mem}
    (hc : gVerylow + gasCopy * ceilDiv sz.toNat 32
      + (St b (di :: si :: sz :: S) M (G + c)).extCost [⟨di.toNat, sz.toNat⟩] = c)
    (hw : M.write di.toNat (sevm.data.sliceD si.toNat sz.toNat 0) = M')
    (k : SFunc.RunExactCut fs sevm C (St b S M' G) f r) :
    SFunc.RunExactCut fs sevm C (St b (di :: si :: sz :: S) M (G + c))
      (.next (.reg .calldatacopy) f) r :=
  .next (Ninst.runCompiled_calldatacopy_of (devm := St b (di :: si :: sz :: S) M (G + c))
    (G := G) rfl hc hw rfl) k

end CutCopy

section SiteCovered

variable {fs : List SFunc} {sevm : Sevm} {C : List Nat} {b : Devm} {r : Seg}
  {R : List B256} {M : Mem} {G : Nat} {e0 e1 r0 r1 c0 c1 v0 v1 : UInt8} {k : Nat}
  {fail1 fail2 T : SFunc}

/-- **Copy, merge and call inside memory**: `copy_sha` when memory already covers the
destination's three words (`d + 0x60 ≤ n`), so nothing is expanded: 598 gas flat, and memory
keeps its size.  (The beacon deposit's `pubkey_root` packs below the event's data.)  The first
pass runs the site's own copy head `mcpyTree … k X0`, whose exit `X0` it never takes, so a head
inlined at the site need not be entry `k`'s tree. -/
theorem copy_sha_covered {img : Bytes} {n s d : Nat} {w1 w2 x1 x3 x4 : B256} {X0 : SFunc}
    (hk : fs[k]? = some (mcpyTree e0 e1 r0 r1 k
      (mergeTree (shaCallTree c0 c1 v0 v1 fail1 fail2 T))))
    (hkC : k ∉ C)
    (hwf : Mem.Wf M) (hr : Mem.Reads M img) (hs : M.size = n) (hn : n % 32 = 0)
    (hdn : d + 96 ≤ n) (hsd : s + 64 = d) (hd32 : d % 32 = 0) (hd96 : 96 ≤ s)
    (hnb : n + 1000 < 2 ^ 256) (hfp : img.sliceD 64 32 0 = (Nat.toB256 d).toBytes)
    (hw1 : img.sliceD s 32 0 = w1.toBytes) (hw2 : img.sliceD (s + 32) 32 0 = w2.toBytes)
    (hR : R.length < 900)
    (hnodeleg : getDelegatedCodeAddress (b.getCode 2) = none)
    (hwarm : (2 : Adr) ∈ b.accessedAddresses)
    (hpre : decide (sevm.benvStat.rules.isPrecomp 2) = true)
    (hfork : CoveredFork sevm.benvStat.fork) (hdepth : sevm.depth ≠ 0)
    (hG : G + 246 < 2 ^ 256) :
    ∃ b' M' img', ShaCallPost b b' (Bytes.sha256 (w1.toBytes ++ w2.toBytes)).toBytes ∧
      Mem.Wf M' ∧ Mem.Reads M' img' ∧ M'.size = n ∧
      img'.sliceD 64 32 0 = (Nat.toB256 d).toBytes ∧
      img'.sliceD d 32 0 = (Bytes.sha256 (w1.toBytes ++ w2.toBytes)).toBytes ∧
      (∀ i l, i + l ≤ d → img'.sliceD i l 0 = img.sliceD i l 0) ∧
      ∀ r, SFunc.RunExactCut fs sevm C (St b' (Nat.toB256 32 :: Nat.toB256 d :: R) M' G) T r →
      SFunc.RunExactCut fs sevm C
        (St b (Nat.toB256 s :: Nat.toB256 d :: Nat.toB256 64 :: Nat.toB256 64 :: x1 ::
          Nat.toB256 d :: x3 :: x4 :: 2 :: R) M (G + 598))
        (mcpyTree e0 e1 r0 r1 k X0) r := by
  obtain ⟨b', M', hpost, hwf', hr', hs', hrun⟩ := copy_sha_gen (X := X0) (x1 := x1) (x3 := x3)
    (x4 := x4) (R := R) (G := G) hk hkC hwf hr hs hn (by omega) hsd hd32 hd96 (by omega) hfp hw1
    hw2 hR hnodeleg hwarm hpre hfork hdepth hG
  have hmax : max n (d + 96) = n := by omega
  refine ⟨b', M', shaImg img d w1 w2, hpost, hwf', hr', by rw [hs', hmax],
    (shaImg_out (d := d) (start := 64) (len := 32) (by omega)).trans hfp, shaImg_digest,
    fun i l hil => shaImg_out (Or.inl hil), fun r kont => ?_⟩
  have hc := hrun r kont
  rwa [hmax, Nat.sub_self, Nat.add_zero] at hc

end SiteCovered

end Blanc.Lift
