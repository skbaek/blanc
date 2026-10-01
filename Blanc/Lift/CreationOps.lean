import Blanc.Lift.WalkSteps

/-!
# More walk steps for constructors: `PUSH0`, `SLT`, `CODESIZE`, `LOG2`

Forward (`rx_*`) steps the solc 0.8 constructors of the creation walks need beyond the shared
kits: `PUSH0`, `SLT`, `CODESIZE` (the length of the executing code, `sevm.code.size`) and a
two-topic `LOG2`.

Nothing here mentions a contract.
-/

namespace Blanc.Lift

open Jaune

section Steps

variable {fs : List SFunc} {sevm : Sevm} {b : Devm} {S : List B256} {M : Mem} {G : Nat}
  {f : SFunc} {o : Outcome}

/-- `PUSH0`. -/
theorem rx_push0 {le : ([] : Bytes).length ≤ 32} (hroom : S.length < 1024)
    (k : SFunc.RunExact fs sevm (St b (0 :: S) M G) f o) :
    SFunc.RunExact fs sevm (St b S M (G + 2)) (.next (.push [] le) f) o :=
  .next (Ninst.runCompiled_pushBytes (devm := St b S M (G + 2)) (c := gBase) (G := G)
    (by simp only [pushCost, ↓reduceIte]) rfl hroom) k

/-- `SLT`. -/
theorem rx_slt {x y v : B256} (hv : B256.sltCheck x y = v) (hroom : S.length < 1024)
    (k : SFunc.RunExact fs sevm (St b (v :: S) M G) f o) :
    SFunc.RunExact fs sevm (St b (x :: y :: S) M (G + 3)) (.next (.reg .slt) f) o :=
  rx_binary (fn := B256.sltCheck) (c := gVerylow) (by rintro ⟨⟩) (fun _ => rfl) hv hroom k

/-- `CODESIZE`: the length of the executing code. -/
theorem rx_codesize (hroom : S.length < 1024)
    (k : SFunc.RunExact fs sevm (St b (sevm.code.size.toB256 :: S) M G) f o) :
    SFunc.RunExact fs sevm (St b S M (G + 2)) (.next (.reg .codesize) f) o :=
  .next (Ninst.runCompiled_pushItem (devm := St b S M (G + 2)) (G := G) (cost := gBase)
    (by rintro ⟨⟩) rfl rfl hroom) k

/-- `LOG2`, with the whole charge named. -/
theorem rx_log2 {i sz t1 t2 : B256} {c : Nat} {data : Bytes}
    (hstatic : sevm.isStatic = false)
    (hc : gLog + gLogdata * sz.toNat + gLogtopic * 2 +
      (St b (i :: sz :: t1 :: t2 :: S) M (G + c)).extCost [⟨i.toNat, sz.toNat⟩] = c)
    (hd : (M.read i.toNat sz.toNat).1 = data) (hM : (M.read i.toNat sz.toNat).2 = M)
    (k : SFunc.RunExact fs sevm
      (St (b.addLog ⟨sevm.currentTarget, [t1, t2], data⟩) S M G) f o) :
    SFunc.RunExact fs sevm (St b (i :: sz :: t1 :: t2 :: S) M (G + c))
      (.next (.reg (.log 2)) f) o :=
  .next (Ninst.runCompiled_log_of (n := 2) (topics := [t1, t2]) (s := S) rfl rfl hstatic hc hd
    hM rfl) k

end Steps

/-- A window inside a word-aligned image extends nothing (any window length). -/
theorem read_covered_len {M : Mem} {n i len : Nat} (hs : M.size = n) (hn : n % 32 = 0)
    (hi : i + len ≤ n) : (M.read i len).2 = M :=
  Mem.read_snd_eq_self (by rw [hs]; exact memExtSize_of_le hn hi)

end Blanc.Lift
