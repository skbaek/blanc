import Blanc.Lift.CopyLoop
import Blanc.Lift.InvWalk
import Blanc.Lift.Loop
import Blanc.Lift.MemMap
import Blanc.Lift.MemPotential

/-!
# F4 `Blanc/Lift/CopyLoopKeep.lean` (the copy loop as a safety walk; generic)

Crossing the solc word-copy loop (`Blanc/Lift/CopyLoop.lean`) under the memory
potential (`Blanc/Lift/MemPotential.lean`): the loop leaves every byte below
the destination alone and exits with `len ≤ i'`.

Decision `ns-f4-hdst`: `hdst` is `dst.toNat ≤ memCap` (not `fpCap`); then
`dst + i ≤ 2 * memCap = 2 ^ 161` never wraps a word. Reads at `i + src` may
still wrap; they only read, so `Mem.AgreeOutside` is unaffected.

Route: induction over the `SFunc.RunCutP` derivation, tracking one position of
the head++body straight line at a time (`J` below); the exit arm supplies the
witness (the first exit) directly, so `exitT` is never analyzed. Reuses the
`ri_*` inversion kit (`Blanc/Lift/InvWalk.lean`), `Mem.write_agree`
(`Blanc/Lift/MemMap.lean`), `Pot.size_lt` (`Blanc/Lift/MemPotential.lean`),
`B256.toNat_add_eq_of_nof`, `toNat_ge_of_ltCheck_eq_zero` and
`eq_zero_of_iszero_ne_zero` (`Blanc/Lift/InvWalkOps.lean`, restated below where
the `Silent`/`MemPotential` import clash forbids the import; see the note).

Nothing here mentions a contract.
-/

namespace Blanc.Lift.FreePtr

open Jaune

/-! ## Memory agreement helpers (generic) -/

theorem Mem.AgreeOutside.trans {μ μ' μ'' : Mem} {lo hi : Nat}
    (h1 : Mem.AgreeOutside μ μ' lo hi) (h2 : Mem.AgreeOutside μ' μ'' lo hi) :
    Mem.AgreeOutside μ μ'' lo hi := by
  refine ⟨le_trans h1.1 h2.1, fun i hlt hout => ?_⟩
  rw [h2.2 i (lt_of_lt_of_le hlt h1.1) hout, h1.2 i hlt hout]

theorem Mem.AgreeOutside.of_data_eq {μ μ' : Mem} {lo hi : Nat}
    (hdata : μ'.data = μ.data) (hsize : μ.size ≤ μ'.size) :
    Mem.AgreeOutside μ μ' lo hi :=
  ⟨hsize, fun i _ _ => by rw [hdata]⟩

/-- Agreement on an inner window is agreement outside any outer interval. -/
theorem Mem.AgreeOutside.mono {μ μ' : Mem} {lo hi lo' hi' : Nat}
    (hlo : lo ≤ lo') (hhi : hi' ≤ hi) (h : Mem.AgreeOutside μ μ' lo' hi') :
    Mem.AgreeOutside μ μ' lo hi := by
  refine ⟨h.1, fun i hlt hout => ?_⟩
  rcases hout with hlt' | hle'
  · exact h.2 i hlt (Or.inl (lt_of_lt_of_le hlt' hlo))
  · exact h.2 i hlt (Or.inr (le_trans hhi hle'))

/-- A `MemKeep` step agrees outside any interval. -/
theorem MemKeep.agreeOutside {d d' : Devm} {lo hi : Nat} (h : MemKeep d d') :
    Mem.AgreeOutside d.memory d'.memory lo hi := by
  have h' : d'.memory.data = d.memory.data ∧ d.memory.size ≤ d'.memory.size := h
  exact Mem.AgreeOutside.of_data_eq h'.1 h'.2

/-- A `Mem.read` extension agrees with the old memory everywhere. -/
theorem Mem.read_agree {b : Devm} {S : List B256} {G : Nat} (μ : Mem)
    (n len lo hi : Nat) : Mem.AgreeOutside μ (μ.read n len).2 lo hi :=
  MemKeep.agreeOutside (MemKeep.memRead (St b S μ G) n len)

/-- Push immediates are words. -/
theorem pushLen_e {e0 e1 : UInt8} : [e0, e1].length ≤ 32 := by
  simp only [List.length_cons, List.length_nil, zero_add, Nat.reduceAdd,
    Nat.reduceLeDiff]

/-- Push immediates are words. -/
theorem pushLen_r {r0 r1 : UInt8} : [r0, r1].length ≤ 32 := by
  simp only [List.length_cons, List.length_nil, zero_add, Nat.reduceAdd,
    Nat.reduceLeDiff]

/-! ## Positions of the head++body straight line -/

/-- The loop states, one disjunct per straight-line position: the stack has the
position's shape over the loop index `j`, memory agrees with the initial memory
below `dst`, and the tree is the position's suffix. -/
inductive J {b : Devm} {src dst len : B256} {R : List B256} {M0 : Mem}
    {e0 e1 r0 r1 : UInt8} {k : Nat} {exitT : SFunc} : Devm → SFunc → Prop
  | h0 (M' : Mem) (G' : Nat) (j : B256) :
    Mem.AgreeOutside M0 M' dst.toNat (2 ^ 256) → j.toNat ≤ memCap →
    @J b src dst len R M0 e0 e1 r0 r1 k exitT
      (St b (j :: src :: dst :: len :: R) M' G')
      (.dest (.next (.reg (.dup 3))
        (.next (.reg (.dup 1))
          (.next (.reg .lt)
            (.next (.reg .iszero)
              (.next (.push [e0, e1] pushLen_e)
                (.branch
                  (.next (.reg (.dup 1))
                    (.next (.reg (.dup 1))
                      (.next (.reg .add)
                        (.next (.reg .mload)
                          (.next (.reg (.dup 3))
                            (.next (.reg (.dup 2))
                              (.next (.reg .add)
                                (.next (.reg .mstore)
                                  (.next (.push [0x20] (by decide))
                                    (.next (.reg .add)
                                      (.next (.push [r0, r1] pushLen_r)
                                        (.jump k))))))))))))
                  exitT)))))))
  | h1 (M' : Mem) (G' : Nat) (j : B256) :
    Mem.AgreeOutside M0 M' dst.toNat (2 ^ 256) → j.toNat ≤ memCap →
    @J b src dst len R M0 e0 e1 r0 r1 k exitT
      (St b (j :: src :: dst :: len :: R) M' G')
      (.next (.reg (.dup 3))
        (.next (.reg (.dup 1))
          (.next (.reg .lt)
            (.next (.reg .iszero)
              (.next (.push [e0, e1] pushLen_e)
                (.branch (copyBody r0 r1 k) exitT))))))
  | h2 (M' : Mem) (G' : Nat) (j : B256) :
    Mem.AgreeOutside M0 M' dst.toNat (2 ^ 256) → j.toNat ≤ memCap →
    @J b src dst len R M0 e0 e1 r0 r1 k exitT
      (St b (len :: j :: src :: dst :: len :: R) M' G')
      (.next (.reg (.dup 1))
        (.next (.reg .lt)
          (.next (.reg .iszero)
            (.next (.push [e0, e1] pushLen_e)
              (.branch (copyBody r0 r1 k) exitT)))))
  | h3 (M' : Mem) (G' : Nat) (j : B256) :
    Mem.AgreeOutside M0 M' dst.toNat (2 ^ 256) → j.toNat ≤ memCap →
    @J b src dst len R M0 e0 e1 r0 r1 k exitT
      (St b (j :: len :: j :: src :: dst :: len :: R) M' G')
      (.next (.reg .lt)
        (.next (.reg .iszero)
          (.next (.push [e0, e1] pushLen_e)
            (.branch (copyBody r0 r1 k) exitT))))
  | h4 (M' : Mem) (G' : Nat) (j : B256) :
    Mem.AgreeOutside M0 M' dst.toNat (2 ^ 256) → j.toNat ≤ memCap →
    @J b src dst len R M0 e0 e1 r0 r1 k exitT
      (St b (B256.ltCheck j len :: j :: src :: dst :: len :: R) M' G')
      (.next (.reg .iszero)
        (.next (.push [e0, e1] pushLen_e)
          (.branch (copyBody r0 r1 k) exitT)))
  | h5 (M' : Mem) (G' : Nat) (j : B256) :
    Mem.AgreeOutside M0 M' dst.toNat (2 ^ 256) → j.toNat ≤ memCap →
    @J b src dst len R M0 e0 e1 r0 r1 k exitT
      (St b (B256.eqCheck (B256.ltCheck j len) 0 :: j :: src :: dst :: len :: R) M' G')
      (.next (.push [e0, e1] pushLen_e) (.branch (copyBody r0 r1 k) exitT))
  | h6 (M' : Mem) (G' : Nat) (j : B256) :
    Mem.AgreeOutside M0 M' dst.toNat (2 ^ 256) → j.toNat ≤ memCap →
    @J b src dst len R M0 e0 e1 r0 r1 k exitT
      (St b (Bytes.toB256 [e0, e1] :: B256.eqCheck (B256.ltCheck j len) 0 ::
        j :: src :: dst :: len :: R) M' G')
      (.branch
        (.next (.reg (.dup 1))
          (.next (.reg (.dup 1))
            (.next (.reg .add)
              (.next (.reg .mload)
                (.next (.reg (.dup 3))
                  (.next (.reg (.dup 2))
                    (.next (.reg .add)
                      (.next (.reg .mstore)
                        (.next (.push [0x20] (by decide))
                          (.next (.reg .add)
                            (.next (.push [r0, r1] pushLen_r) (.jump k))))))))))))
        exitT)
  | b0 (M' : Mem) (G' : Nat) (j : B256) :
    Mem.AgreeOutside M0 M' dst.toNat (2 ^ 256) → j.toNat ≤ memCap →
    @J b src dst len R M0 e0 e1 r0 r1 k exitT
      (St b (j :: src :: dst :: len :: R) M' G')
      (.next (.reg (.dup 1))
        (.next (.reg (.dup 1))
          (.next (.reg .add)
            (.next (.reg .mload)
              (.next (.reg (.dup 3))
                (.next (.reg (.dup 2))
                  (.next (.reg .add)
                    (.next (.reg .mstore)
                      (.next (.push [0x20] (by decide))
                        (.next (.reg .add)
                          (.next (.push [r0, r1] pushLen_r) (.jump k))))))))))))
  | b1 (M' : Mem) (G' : Nat) (j : B256) :
    Mem.AgreeOutside M0 M' dst.toNat (2 ^ 256) → j.toNat ≤ memCap →
    @J b src dst len R M0 e0 e1 r0 r1 k exitT
      (St b (src :: j :: src :: dst :: len :: R) M' G')
      (.next (.reg (.dup 1))
        (.next (.reg .add)
          (.next (.reg .mload)
            (.next (.reg (.dup 3))
              (.next (.reg (.dup 2))
                (.next (.reg .add)
                  (.next (.reg .mstore)
                    (.next (.push [0x20] (by decide))
                      (.next (.reg .add)
                        (.next (.push [r0, r1] pushLen_r) (.jump k)))))))))))
  | b2 (M' : Mem) (G' : Nat) (j : B256) :
    Mem.AgreeOutside M0 M' dst.toNat (2 ^ 256) → j.toNat ≤ memCap →
    @J b src dst len R M0 e0 e1 r0 r1 k exitT
      (St b (j :: src :: j :: src :: dst :: len :: R) M' G')
      (.next (.reg .add)
        (.next (.reg .mload)
          (.next (.reg (.dup 3))
            (.next (.reg (.dup 2))
              (.next (.reg .add)
                (.next (.reg .mstore)
                  (.next (.push [0x20] (by decide))
                    (.next (.reg .add)
                      (.next (.push [r0, r1] pushLen_r) (.jump k))))))))))
  | b3 (M' : Mem) (G' : Nat) (j : B256) :
    Mem.AgreeOutside M0 M' dst.toNat (2 ^ 256) → j.toNat ≤ memCap →
    @J b src dst len R M0 e0 e1 r0 r1 k exitT
      (St b ((j + src) :: j :: src :: dst :: len :: R) M' G')
      (.next (.reg .mload)
        (.next (.reg (.dup 3))
          (.next (.reg (.dup 2))
            (.next (.reg .add)
              (.next (.reg .mstore)
                (.next (.push [0x20] (by decide))
                  (.next (.reg .add)
                    (.next (.push [r0, r1] pushLen_r) (.jump k)))))))))
  | b4 (w : B256) (M' : Mem) (G' : Nat) (j : B256) :
    Mem.AgreeOutside M0 M' dst.toNat (2 ^ 256) → j.toNat ≤ memCap →
    @J b src dst len R M0 e0 e1 r0 r1 k exitT
      (St b (w :: j :: src :: dst :: len :: R) M' G')
      (.next (.reg (.dup 3))
        (.next (.reg (.dup 2))
          (.next (.reg .add)
            (.next (.reg .mstore)
              (.next (.push [0x20] (by decide))
                (.next (.reg .add)
                  (.next (.push [r0, r1] pushLen_r) (.jump k))))))))
  | b5 (w : B256) (M' : Mem) (G' : Nat) (j : B256) :
    Mem.AgreeOutside M0 M' dst.toNat (2 ^ 256) → j.toNat ≤ memCap →
    @J b src dst len R M0 e0 e1 r0 r1 k exitT
      (St b (dst :: w :: j :: src :: dst :: len :: R) M' G')
      (.next (.reg (.dup 2))
        (.next (.reg .add)
          (.next (.reg .mstore)
            (.next (.push [0x20] (by decide))
              (.next (.reg .add)
                (.next (.push [r0, r1] pushLen_r) (.jump k)))))))
  | b6 (w : B256) (M' : Mem) (G' : Nat) (j : B256) :
    Mem.AgreeOutside M0 M' dst.toNat (2 ^ 256) → j.toNat ≤ memCap →
    @J b src dst len R M0 e0 e1 r0 r1 k exitT
      (St b (j :: dst :: w :: j :: src :: dst :: len :: R) M' G')
      (.next (.reg .add)
        (.next (.reg .mstore)
          (.next (.push [0x20] (by decide))
            (.next (.reg .add)
              (.next (.push [r0, r1] pushLen_r) (.jump k))))))
  | b7 (w : B256) (M' : Mem) (G' : Nat) (j : B256) :
    Mem.AgreeOutside M0 M' dst.toNat (2 ^ 256) → j.toNat ≤ memCap →
    @J b src dst len R M0 e0 e1 r0 r1 k exitT
      (St b ((j + dst) :: w :: j :: src :: dst :: len :: R) M' G')
      (.next (.reg .mstore)
        (.next (.push [0x20] (by decide))
          (.next (.reg .add) (.next (.push [r0, r1] pushLen_r) (.jump k)))))
  | b8 (M' : Mem) (G' : Nat) (j : B256) :
    Mem.AgreeOutside M0 M' dst.toNat (2 ^ 256) → j.toNat ≤ memCap →
    j.toNat + 32 ≤ memCap →
    @J b src dst len R M0 e0 e1 r0 r1 k exitT
      (St b (j :: src :: dst :: len :: R) M' G')
      (.next (.push [0x20] (by decide))
        (.next (.reg .add) (.next (.push [r0, r1] pushLen_r) (.jump k))))
  | b9 (M' : Mem) (G' : Nat) (j : B256) :
    Mem.AgreeOutside M0 M' dst.toNat (2 ^ 256) → j.toNat ≤ memCap →
    j.toNat + 32 ≤ memCap →
    @J b src dst len R M0 e0 e1 r0 r1 k exitT
      (St b (Bytes.toB256 [0x20] :: j :: src :: dst :: len :: R) M' G')
      (.next (.reg .add) (.next (.push [r0, r1] pushLen_r) (.jump k)))
  | b10 (M' : Mem) (G' : Nat) (j : B256) :
    Mem.AgreeOutside M0 M' dst.toNat (2 ^ 256) → j.toNat ≤ memCap →
    j.toNat + 32 ≤ memCap → (Bytes.toB256 [0x20] + j).toNat ≤ memCap →
    @J b src dst len R M0 e0 e1 r0 r1 k exitT
      (St b ((Bytes.toB256 [0x20] + j) :: src :: dst :: len :: R) M' G')
      (.next (.push [r0, r1] pushLen_r) (.jump k))
  | b11 (M' : Mem) (G' : Nat) (j : B256) :
    Mem.AgreeOutside M0 M' dst.toNat (2 ^ 256) → j.toNat ≤ memCap →
    (Bytes.toB256 [0x20] + j).toNat ≤ memCap →
    @J b src dst len R M0 e0 e1 r0 r1 k exitT
      (St b (Bytes.toB256 [r0, r1] :: (Bytes.toB256 [0x20] + j) ::
        src :: dst :: len :: R) M' G')
      (.jump k)

/-! ## Restated inversion kit

`Blanc/Lift/InvWalkOps.lean` cannot be imported here: it (transitively via
`Blanc/Lift/Silent.lean`) defines `Blanc.Lift.Outcome.devm`, which
`Blanc/Lift/MemPotential.lean` (needed for `Pot`) defines a second time, so
importing both fails. The brief forbids editing existing files, so the four
facts below are proved here instead of reused; each proof is copied from
`InvWalkOps`. If the duplicate `Outcome.devm` is ever removed, delete these and
import `InvWalkOps`.
-/

theorem St.memRead_fst {b : Devm} {S : List B256} {M : Mem} {G i sz : Nat} :
    ((St b S M G).memRead i sz).1 = (M.read i sz).1 := rfl

theorem St.memRead_snd {b : Devm} {S : List B256} {M : Mem} {G i sz : Nat} :
    ((St b S M G).memRead i sz).2 = St b S (M.read i sz).2 G := rfl

/-- `MLOAD`, inverted. -/
theorem ri_mload {sevm : Sevm} {b : Devm} {S : List B256} {M : Mem} {G : Nat}
    {i : B256} {d : Devm}
    (h : Ninst.Run sevm (St b (i :: S) M G) (.reg .mload) d) :
    ∃ G', d = St b (Bytes.toB256 (M.read i.toNat 32).1 :: S) (M.read i.toNat 32).2 G' := by
  rcases of_run_reg h with ⟨pc, run⟩
  simp only [Rinst.run, Rinst.runCore] at run
  rcases Except.bind_eq_ok run with ⟨⟨si, s₁⟩, h1, run₁⟩
  rcases Except.bind_eq_ok run₁ with ⟨s₂, h2, run₂⟩
  rcases Devm.pop_of_popToNat_val h1 with ⟨x, p1, rfl⟩
  have hb := Devm.burn_of_chargeGas h2
  have hpb := Devm.popBurn_of_pop_of_burn p1 hb
  obtain ⟨rfl, hs₂⟩ := St.of_pop1 hpb
  rw [hs₂] at run₂
  simp only [St.memRead_fst, St.memRead_snd] at run₂
  have hp := Devm.push_of_push run₂
  have hs : d.stack = Bytes.toB256 (M.read i.toNat 32).1 :: S := by
    have := hp.stack
    simpa only [Stack.Push, Split, St.stack, List.cons_append, List.nil_append] using this
  have e := St.of_stackRel (S := S) (M := (M.read i.toNat 32).2) (G := s₂.gasLeft) hp
  rw [hs] at e
  exact ⟨_, e⟩

/-- `MSTORE`, inverted. -/
theorem ri_mstore {sevm : Sevm} {b : Devm} {S : List B256} {M : Mem} {G : Nat}
    {i v : B256} {d : Devm}
    (h : Ninst.Run sevm (St b (i :: v :: S) M G) (.reg .mstore) d) :
    ∃ G', d = St b S (M.write i.toNat v.toBytes) G' := by
  rcases of_run_reg h with ⟨pc, run⟩
  simp only [Rinst.run, Rinst.runCore] at run
  rcases Except.bind_eq_ok run with ⟨⟨i', s₁⟩, h1, run'⟩
  rcases Except.bind_eq_ok run' with ⟨⟨v', s₂⟩, h2, run''⟩
  rcases Except.bind_eq_ok run'' with ⟨s₃, h3, h4⟩
  rcases Devm.pop_of_popToNat_val h1 with ⟨x, p1, rfl⟩
  have p2 := Devm.pop_of_pop h2
  have hb := Devm.burn_of_chargeGas h3
  injection h4 with eq
  have hpb := Devm.popBurn_of_pop_of_burn (Devm.pop_append p1 p2) hb
  obtain ⟨rfl, rfl, hs₃⟩ := St.of_pop2 hpb
  rw [hs₃] at eq
  exact ⟨_, eq.symm⟩

lemma toNat_ge_of_ltCheck_eq_zero {x y : B256} (h : B256.ltCheck x y = 0) :
    y.toNat ≤ x.toNat := by
  unfold B256.ltCheck at h; split at h
  · cases h
  · rename_i hnlt
    rw [B256.lt_iff_toNat_lt_toNat] at hnlt
    omega

lemma eq_zero_of_iszero_ne_zero {x : B256} (h : B256.eqCheck x 0 ≠ 0) : x = 0 := by
  unfold B256.eqCheck at h; split at h
  · assumption
  · contradiction

/-! ## The shape of `J` -/

/-- Every `J` position is a dest, a next, a branch or a jump. -/
theorem J_shape {b : Devm} {src dst len : B256} {R : List B256} {M0 : Mem}
    {e0 e1 r0 r1 : UInt8} {k : Nat} {exitT : SFunc} {devm : Devm} {f : SFunc}
    (hJ : J (b := b) (src := src) (dst := dst) (len := len) (R := R) (M0 := M0)
      (e0 := e0) (e1 := e1) (r0 := r0) (r1 := r1) (k := k) (exitT := exitT) devm f) :
    (∃ g, f = .dest g) ∨ (∃ n g, f = .next n g) ∨
      (∃ g₁ g₂, f = .branch g₁ g₂) ∨ (∃ k, f = .jump k) := by
  cases hJ <;> first
    | exact Or.inl ⟨_, rfl⟩
    | exact Or.inr (Or.inl ⟨_, _, rfl⟩)
    | exact Or.inr (Or.inr (Or.inl ⟨_, _, rfl⟩))
    | exact Or.inr (Or.inr (Or.inr ⟨_, rfl⟩))

/-! ## The walk -/

/-- **Crossing the solc word-copy loop** under the potential: the loop leaves every byte below
the destination alone and grows nothing it does not write; it exits with `len ≤ i'`. -/
theorem copy_loop_keep {P : Sevm → Devm → Ninst → Devm → Prop}
    (hP : ∀ {s d n d'}, P s d n d' → Ninst.Run s d n d' ∧ Pot d ∧ Pot d')
    {fs : List SFunc} {sevm : Sevm} {C : List Nat} {k : Nat} {e0 e1 r0 r1 : UInt8}
    {exitT : SFunc} (hk : fs[k]? = some (copyLoopTree e0 e1 r0 r1 k exitT)) (hkC : k ∉ C)
    (hfork : CoveredFork sevm.benvStat.fork)
    {b : Devm} {i src dst len : B256} {R : List B256} {M : Mem} {G : Nat} {r : Seg}
    (hi : i.toNat ≤ memCap) (hdst : dst.toNat ≤ memCap)
    (run : SFunc.RunCutP P fs sevm C (St b (i :: src :: dst :: len :: R) M G)
      (copyLoopTree e0 e1 r0 r1 k exitT) r) :
    ∃ i' M' G', len.toNat ≤ i'.toNat ∧ i'.toNat ≤ memCap ∧
      Mem.AgreeOutside M M' dst.toNat (2 ^ 256) ∧
      SFunc.RunCutP P fs sevm C (St b (i' :: src :: dst :: len :: R) M' G') exitT r := by
  have hmem : memCap = 2 ^ 160 := rfl
  have h2mem : 2 * memCap < 2 ^ 256 := by rw [hmem]; decide
  have hmem_le : memCap ≤ 2 ^ 256 := by rw [hmem]; decide
  have h32mem : 32 ≤ memCap := by rw [hmem]; decide
  have hc32 : (Bytes.toB256 [0x20]).toNat = 32 := by decide
  have main : ∀ {devm f r},
      SFunc.RunCutP P fs sevm C devm f r →
      J (b := b) (src := src) (dst := dst) (len := len) (R := R) (M0 := M)
        (e0 := e0) (e1 := e1) (r0 := r0) (r1 := r1) (k := k) (exitT := exitT)
        devm f →
      (∃ i' M' G', len.toNat ≤ i'.toNat ∧ i'.toNat ≤ memCap ∧
        Mem.AgreeOutside M M' dst.toNat (2 ^ 256) ∧
        SFunc.RunCutP P fs sevm C (St b (i' :: src :: dst :: len :: R) M' G') exitT r) := by
    intro devm f r hrun hJ
    induction hrun with
    | zero d hpop tail ih =>
      cases hJ with
      | h6 M' G' j hag hle =>
        have e := (St.of_pop2 hpop).2.2
        rw [e] at tail ih
        exact ih (J.b0 M' _ j hag hle)
    | succ d w hnz hpop tail ih =>
      cases hJ with
      | h6 M' G' j hag hle =>
        obtain ⟨_, hizw, e⟩ := St.of_pop2 hpop
        have hiz : B256.eqCheck (B256.ltCheck j len) 0 ≠ 0 := by
          rw [hizw]; exact hnz
        have hleLen := toNat_ge_of_ltCheck_eq_zero (eq_zero_of_iszero_ne_zero hiz)
        rw [e] at tail
        exact ⟨j, M', _, hleLen, hle, hag, tail⟩
    | next h tail ih =>
      cases hJ with
      | h1 M' G' j hag hle =>
        obtain ⟨hrun, _, _⟩ := hP h
        obtain ⟨G'', e2⟩ := ri_dup (w := len) rfl hrun
        subst e2
        exact ih (J.h2 M' G'' j hag hle)
      | h2 M' G' j hag hle =>
        obtain ⟨hrun, _, _⟩ := hP h
        obtain ⟨G'', e2⟩ := ri_dup (w := j) rfl hrun
        subst e2
        exact ih (J.h3 M' G'' j hag hle)
      | h3 M' G' j hag hle =>
        obtain ⟨hrun, _, _⟩ := hP h
        obtain ⟨G'', e2⟩ := ri_lt hrun
        subst e2
        exact ih (J.h4 M' G'' j hag hle)
      | h4 M' G' j hag hle =>
        obtain ⟨hrun, _, _⟩ := hP h
        obtain ⟨G'', e2⟩ := ri_iszero hrun
        subst e2
        exact ih (J.h5 M' G'' j hag hle)
      | h5 M' G' j hag hle =>
        obtain ⟨hrun, _, _⟩ := hP h
        obtain ⟨G'', e2⟩ := ri_push hrun
        subst e2
        exact ih (J.h6 M' G'' j hag hle)
      | b0 M' G' j hag hle =>
        obtain ⟨hrun, _, _⟩ := hP h
        obtain ⟨G'', e2⟩ := ri_dup (w := src) rfl hrun
        subst e2
        exact ih (J.b1 M' G'' j hag hle)
      | b1 M' G' j hag hle =>
        obtain ⟨hrun, _, _⟩ := hP h
        obtain ⟨G'', e2⟩ := ri_dup (w := j) rfl hrun
        subst e2
        exact ih (J.b2 M' G'' j hag hle)
      | b2 M' G' j hag hle =>
        obtain ⟨hrun, _, _⟩ := hP h
        obtain ⟨G'', e2⟩ := ri_add hrun
        subst e2
        exact ih (J.b3 M' G'' j hag hle)
      | b3 M' G' j hag hle =>
        obtain ⟨hrun, _, _⟩ := hP h
        obtain ⟨G'', e2⟩ := ri_mload hrun
        subst e2
        have hag1 : Mem.AgreeOutside M' ((M'.read (j + src).toNat 32).2)
            dst.toNat (2 ^ 256) :=
          Mem.read_agree (b := b) (S := (j :: src :: dst :: len :: R)) (G := G')
            M' _ _ _ _
        exact ih (J.b4 _ _ _ j (Mem.AgreeOutside.trans hag hag1) hle)
      | b4 w M' G' j hag hle =>
        obtain ⟨hrun, _, _⟩ := hP h
        obtain ⟨G'', e2⟩ := ri_dup (w := dst) rfl hrun
        subst e2
        exact ih (J.b5 w M' G'' j hag hle)
      | b5 w M' G' j hag hle =>
        obtain ⟨hrun, _, _⟩ := hP h
        obtain ⟨G'', e2⟩ := ri_dup (w := j) rfl hrun
        subst e2
        exact ih (J.b6 w M' G'' j hag hle)
      | b6 w M' G' j hag hle =>
        obtain ⟨hrun, _, _⟩ := hP h
        obtain ⟨G'', e2⟩ := ri_add hrun
        subst e2
        exact ih (J.b7 w M' G'' j hag hle)
      | b7 w M' G' j hag hle =>
        obtain ⟨hrun, _, hpot⟩ := hP h
        obtain ⟨G'', e2⟩ := ri_mstore hrun
        subst e2
        have hnof : B256.Nof j dst := by unfold B256.Nof; omega
        have hb : (j + dst).toNat = j.toNat + dst.toNat :=
          B256.toNat_add_eq_of_nof _ _ hnof
        have hne : w.toBytes ≠ [] := by
          intro hcon
          have hlen := B256.length_toBytes w
          rw [hcon, List.length_nil] at hlen
          omega
        obtain ⟨A, hdata, hA, hsz, hfit, hagree⟩ :=
          Mem.write_base M' (j + dst).toNat hne
        have hlen32 : w.toBytes.length = 32 := B256.length_toBytes w
        rw [hlen32] at hfit
        have hsize : (M'.write (j + dst).toNat w.toBytes).size < memCap :=
          Pot.size_lt hpot
        have hbnd : j.toNat + 32 ≤ memCap := by omega
        have hle256 : (j + dst).toNat + 32 ≤ 2 ^ 256 := by omega
        have hw := Mem.write_agree M' (j + dst).toNat w.toBytes
        rw [hlen32] at hw
        have hagw : Mem.AgreeOutside M' (M'.write (j + dst).toNat w.toBytes)
            dst.toNat (2 ^ 256) :=
          Mem.AgreeOutside.mono (by omega) hle256 hw
        exact ih (J.b8 _ _ j (Mem.AgreeOutside.trans hag hagw) hle hbnd)
      | b8 M' G' j hag hle hhb =>
        obtain ⟨hrun, _, _⟩ := hP h
        obtain ⟨G'', e2⟩ := ri_push hrun
        subst e2
        exact ih (J.b9 M' G'' j hag hle hhb)
      | b9 M' G' j hag hle hhb =>
        obtain ⟨hrun, _, _⟩ := hP h
        obtain ⟨G'', e2⟩ := ri_add hrun
        subst e2
        have hnof : B256.Nof (Bytes.toB256 [0x20]) j := by unfold B256.Nof; omega
        have hi' : (Bytes.toB256 [0x20] + j).toNat ≤ memCap := by
          rw [B256.toNat_add_eq_of_nof _ _ hnof, hc32]; omega
        exact ih (J.b10 M' G'' j hag hle hhb hi')
      | b10 M' G' j hag hle hhb hi' =>
        obtain ⟨hrun, _, _⟩ := hP h
        obtain ⟨G'', e2⟩ := ri_push hrun
        subst e2
        exact ih (J.b11 M' G'' j hag hle hi')
    | dest hburn tail ih =>
      cases hJ with
      | h0 M' G' j hag hle =>
        have e := St.of_burn hburn
        rw [e] at tail ih
        exact ih (J.h1 M' _ j hag hle)
    | jumpCut d hkMem hpop =>
      cases hJ with
      | b11 M' G' j hag hle hi' =>
        exact absurd hkMem hkC
    | jump d hnot hget hpop tail ih =>
      cases hJ with
      | b11 M' G' j hag hle hi' =>
        rw [hk] at hget
        cases hget
        have e := (St.of_pop1 hpop).2
        rw [e] at tail ih
        exact ih (J.h0 M' _ _ hag hi')
    | toZero _ _ _ _ =>
      rcases J_shape hJ with ⟨_, h⟩ | ⟨_, _, h⟩ | ⟨_, _, h⟩ | ⟨_, h⟩ <;> cases h
    | toSuccCut _ _ _ _ _ =>
      rcases J_shape hJ with ⟨_, h⟩ | ⟨_, _, h⟩ | ⟨_, _, h⟩ | ⟨_, h⟩ <;> cases h
    | toSucc _ _ _ _ _ _ _ _ =>
      rcases J_shape hJ with ⟨_, h⟩ | ⟨_, _, h⟩ | ⟨_, _, h⟩ | ⟨_, h⟩ <;> cases h
    | last _ =>
      rcases J_shape hJ with ⟨_, h⟩ | ⟨_, _, h⟩ | ⟨_, _, h⟩ | ⟨_, h⟩ <;> cases h
    | ret _ _ =>
      rcases J_shape hJ with ⟨_, h⟩ | ⟨_, _, h⟩ | ⟨_, _, h⟩ | ⟨_, h⟩ <;> cases h
    | callHalt _ _ _ _ =>
      rcases J_shape hJ with ⟨_, h⟩ | ⟨_, _, h⟩ | ⟨_, _, h⟩ | ⟨_, h⟩ <;> cases h
    | callRet _ _ _ _ _ _ =>
      rcases J_shape hJ with ⟨_, h⟩ | ⟨_, _, h⟩ | ⟨_, _, h⟩ | ⟨_, h⟩ <;> cases h
    | pcAt _ _ _ _ =>
      rcases J_shape hJ with ⟨_, h⟩ | ⟨_, _, h⟩ | ⟨_, _, h⟩ | ⟨_, h⟩ <;> cases h
  exact main run (J.h0 M G i (Mem.AgreeOutside.refl M _ _) hi)
