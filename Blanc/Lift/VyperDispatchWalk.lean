import Blanc.Lift.FrameWalkKit
import Blanc.Lift.Vyper

/-!
# A Vyper selector dispatcher, walked by evaluation

A Vyper 0.2 dispatcher writes the selector word into memory with its prologue (`vyMem`) and then
runs a linear chain of tests `PUSH4 c PUSH1 0 MLOAD EQ ISZERO PUSH2 t JUMPI`: a hit falls into the
arm (14 bytes on), a miss jumps to `t`, a `JUMPDEST` that starts the next test.  Between tests the
compiler leaves always-taken skips `PUSH1 0 ISZERO PUSH2 t JUMPI` over dead code.

The chain is read off any sound decoder `dec` of the frame's code (`DecSound`), so for a concrete
contract the kernel evaluates the chain; the walk of the frame's actual
derivation (`XAt`) is proved once here:

* `vyTestAt`/`vyPassAt`: the recognized test (its constant and its miss target past the
  `JUMPDEST`) or skip at a pc; `xa_vyTest`, `xa_vyPass`: one of them, walked;
* `vyChain dec n p`: the chain of tests and skips from `p` and the pc it ends at, which a
  contract evaluates once by the kernel into a literal list; `vyHit σ ls e`: the pc that list hands
  the selector `σ` (the arm of its first equal constant, or the end);
* `xa_vyChain`: a frame with selector `σ` reaches `vyHit σ ls e`; `xa_vyChain_miss`: a selector
  equal to none of the chain's constants reaches its end.

Nothing here mentions a contract.
-/

namespace Blanc.Lift

open Jaune

/-- A decoder of `code`: every instruction it decodes is the real one. -/
def DecSound (dec : Nat → Option Inst) (code : ByteArray) : Prop :=
  ∀ {pc : Nat} {i : Inst}, dec pc = some i → code.getInst pc = some i

section Decode

variable {dec : Nat → Option Inst} {pc : Nat}

/-- The constant of a `PUSH4` decoded at `pc`. -/
def decPush4 (dec : Nat → Option Inst) (pc : Nat) : Option B256 :=
  match dec pc with
  | some (.next (.push [c0, c1, c2, c3] _)) => some (Bytes.toB256 [c0, c1, c2, c3])
  | _ => none

/-- The destination of a `PUSH2` decoded at `pc`. -/
def decPush2 (dec : Nat → Option Inst) (pc : Nat) : Option Nat :=
  match dec pc with
  | some (.next (.push [h, l] _)) => some (Bytes.toB256 [h, l]).toNat
  | _ => none

/-- A `PUSH1 0` is decoded at `pc`. -/
def decPush0 (dec : Nat → Option Inst) (pc : Nat) : Bool :=
  match dec pc with
  | some (.next (.push [z] _)) => z == 0
  | _ => false

/-- The register instruction `r` is decoded at `pc`. -/
def decReg (dec : Nat → Option Inst) (pc : Nat) (r : Rinst) : Bool :=
  match dec pc with
  | some (.next (.reg r')) => r' == r
  | _ => false

/-- The jump instruction `j` is decoded at `pc`. -/
def decJmp (dec : Nat → Option Inst) (pc : Nat) (j : Jinst) : Bool :=
  match dec pc with
  | some (.jump j') => j' == j
  | _ => false

theorem decPush4_spec {c : B256} (h : decPush4 dec pc = some c) :
    ∃ c0 c1 c2 c3 le, dec pc = some (.next (.push [c0, c1, c2, c3] le)) ∧
      Bytes.toB256 [c0, c1, c2, c3] = c := by
  unfold decPush4 at h
  split at h
  · rename_i c0 c1 c2 c3 le e
    exact ⟨c0, c1, c2, c3, le, e, Option.some.inj h⟩
  · cases h

theorem decPush2_spec {t : Nat} (h : decPush2 dec pc = some t) :
    ∃ hi lo le, dec pc = some (.next (.push [hi, lo] le)) ∧ (Bytes.toB256 [hi, lo]).toNat = t := by
  unfold decPush2 at h
  split at h
  · rename_i hi lo le e
    exact ⟨hi, lo, le, e, Option.some.inj h⟩
  · cases h

theorem decPush0_spec (h : decPush0 dec pc = true) : ∃ le, dec pc = some (.next (.push [0] le)) := by
  unfold decPush0 at h
  split at h
  · rename_i z _ e
    rw [beq_iff_eq] at h
    subst h
    exact ⟨_, e⟩
  · cases h

theorem decReg_spec {r : Rinst} (h : decReg dec pc r = true) : dec pc = some (.next (.reg r)) := by
  unfold decReg at h
  split at h
  · rename_i r' e
    rw [beq_iff_eq] at h
    subst h
    exact e
  · cases h

theorem decJmp_spec {j : Jinst} (h : decJmp dec pc j = true) : dec pc = some (.jump j) := by
  unfold decJmp at h
  split at h
  · rename_i j' e
    rw [beq_iff_eq] at h
    subst h
    exact e
  · cases h

end Decode

/-- The selector test at `p`, `PUSH4 c PUSH1 0 MLOAD EQ ISZERO PUSH2 t JUMPI` with a `JUMPDEST`
at `t`: its constant `c` and the pc `t + 1` a miss continues at. -/
def vyTestAt (dec : Nat → Option Inst) (p : Nat) : Option (B256 × Nat) :=
  match decPush4 dec p, decPush2 dec (p + 10) with
  | some c, some t =>
      if decPush0 dec (p + 5) && decReg dec (p + 7) .mload && decReg dec (p + 8) .eq &&
          decReg dec (p + 9) .iszero && decJmp dec (p + 13) .jumpi && decJmp dec t .jumpdest
      then some (c, t + 1) else none
  | _, _ => none

/-- The always-taken skip at `p`, `PUSH1 0 ISZERO PUSH2 t JUMPI` with a `JUMPDEST` at `t`: the
pc `t + 1` it continues at. -/
def vyPassAt (dec : Nat → Option Inst) (p : Nat) : Option Nat :=
  match decPush2 dec (p + 3) with
  | some t =>
      if decPush0 dec p && decReg dec (p + 2) .iszero && decJmp dec (p + 6) .jumpi &&
          decJmp dec t .jumpdest
      then some (t + 1) else none
  | none => none

/-- The dispatcher's chain from `p` along the all-miss path, within `n` links: each test's pc
and constant (`some c`) or each skip's pc (`none`), and the pc the chain ends at (the first that is
neither shape).  For a concrete contract the kernel evaluates it once; routing a selector then
reads the resulting list (`vyHit`) without decoding again. -/
def vyChain (dec : Nat → Option Inst) : Nat → Nat → List (Nat × Option B256) × Nat
  | 0, p => ([], p)
  | n + 1, p =>
      match vyTestAt dec p with
      | some (c, q) => ((p, some c) :: (vyChain dec n q).1, (vyChain dec n q).2)
      | none =>
          match vyPassAt dec p with
          | some q => ((p, none) :: (vyChain dec n q).1, (vyChain dec n q).2)
          | none => ([], p)

/-- The pc a chain hands the selector `σ`: the arm (14 bytes past the test) of its first test of
`σ`, or the chain's end `e`. -/
def vyHit (σ : B256) : List (Nat × Option B256) → Nat → Nat
  | [], e => e
  | (p, some c) :: ls, e => if c = σ then p + 14 else vyHit σ ls e
  | (_, none) :: ls, e => vyHit σ ls e

/-- A selector no test of the chain compares is handed the chain's end. -/
theorem vyHit_of_not_mem {σ : B256} {e : Nat} :
    ∀ {ls : List (Nat × Option B256)}, (∀ c ∈ ls.filterMap Prod.snd, σ ≠ c) → vyHit σ ls e = e
  | [], _ => rfl
  | (p, some c) :: ls, h => by
      rw [vyHit, ite_eq_right (fun hc => h c List.mem_cons_self hc.symm)]
      exact vyHit_of_not_mem (fun c' hc' => h c' (List.mem_cons_of_mem _ hc'))
  | (p, none) :: ls, h => by
      rw [vyHit]
      exact vyHit_of_not_mem h

/-- The prologue's memory word at offset `0` is the frame's selector. -/
theorem vyMem_word0_selector {sevm : Sevm} :
    Bytes.toB256 ((vyImg [] (Sevm.dataWord sevm 0)).sliceD (Bytes.toB256 [0]).toNat 32 0) =
      Sevm.selector sevm := by
  rw [show (Bytes.toB256 [0]).toNat = 0 from rfl, vyImg_selector]
  rfl

section Walk

variable {sevm : Sevm} {b : Devm}

/-- An `MLOAD` at offset `0` of the prologue's memory leaves it unchanged (it is already six
words long) and reads the image's first word. -/
theorem ri_mload_vy0 {S : List B256} {G : Nat} {d : Devm} {w : B256}
    (h : Ninst.Run sevm (St b (Bytes.toB256 [0] :: S) (vyMem Mem.empty w) G) (.reg .mload) d) :
    ∃ G', d = St b (Bytes.toB256 ((vyImg [] w).sliceD (Bytes.toB256 [0]).toNat 32 0) :: S)
      (vyMem Mem.empty w) G' := by
  obtain ⟨G', rfl⟩ := ri_mload h
  refine ⟨G', ?_⟩
  have hR := vyMem_reads Mem.wf_empty Mem.reads_empty w
  have hs := vyMem_empty_size w
  have hx : (Mem.read (vyMem Mem.empty w) (Bytes.toB256 [0]).toNat 32).2 = vyMem Mem.empty w := by
    show Mem.mk _ (memExtSize _ _ _) = _
    rw [hs]
    cases e : vyMem Mem.empty w with
    | mk data size => rw [e] at hs; subst hs; rfl
  rw [Mem.Reads.read hR, hx]

variable {dec : Nat → Option Inst} {post : Devm} {L : List Exec.Frame} {S : List B256}

local notation "Mv" => vyMem Mem.empty (Sevm.dataWord sevm 0)

/-- **One selector test**, either way: a hit falls into the arm at `p + 14`, a miss continues
at `q`. -/
theorem xa_vyTest (hdec : DecSound dec sevm.code) {p q : Nat} {c : B256}
    (ht : vyTestAt dec p = some (c, q)) {G : Nat} (h : XAt sevm post p (St b S Mv G) L) :
    (Sevm.selector sevm = c ∧ ∃ G', XAt sevm post (p + 14) (St b S Mv G') L) ∨
      (Sevm.selector sevm ≠ c ∧ ∃ G', XAt sevm post q (St b S Mv G') L) := by
  unfold vyTestAt at ht
  split at ht
  · rename_i c' t hc ht2
    split at ht
    · rename_i hb
      simp only [Option.some.injEq, Prod.mk.injEq] at ht
      obtain ⟨rfl, rfl⟩ := ht
      simp only [Bool.and_eq_true] at hb
      obtain ⟨⟨⟨⟨⟨hz, hm⟩, he⟩, hi⟩, hj⟩, hd⟩ := hb
      obtain ⟨c0, c1, c2, c3, le4, e4, rfl⟩ := decPush4_spec hc
      obtain ⟨hi', lo, le2, e2, rfl⟩ := decPush2_spec ht2
      obtain ⟨le1, e1⟩ := decPush0_spec hz
      obtain ⟨_, s, h⟩ := xa_nextAt (pc' := p + 5) (hdec e4) (by nofun) rfl h
      obtain ⟨_, rfl⟩ := ri_push s
      obtain ⟨_, s, h⟩ := xa_nextAt (pc' := p + 7) (hdec e1) (by nofun) rfl h
      obtain ⟨_, rfl⟩ := ri_push s
      obtain ⟨_, s, h⟩ := xa_nextAt (pc' := p + 8) (hdec (decReg_spec hm)) (by nofun) rfl h
      obtain ⟨_, rfl⟩ := ri_mload_vy0 s
      obtain ⟨_, s, h⟩ := xa_nextAt (pc' := p + 9) (hdec (decReg_spec he)) (by nofun) rfl h
      obtain ⟨_, rfl⟩ := ri_eq s
      obtain ⟨_, s, h⟩ := xa_nextAt (pc' := p + 10) (hdec (decReg_spec hi)) (by nofun) rfl h
      obtain ⟨_, rfl⟩ := ri_iszero s
      obtain ⟨_, s, h⟩ := xa_nextAt (pc' := p + 13) (hdec e2) (by nofun) rfl h
      obtain ⟨_, rfl⟩ := ri_push s
      rw [vyMem_word0_selector] at h
      rcases xa_jumpiAt (pf := p + 14) (hdec (decJmp_spec hj)) rfl rfl h with
        ⟨hw, _, h⟩ | ⟨hw, _, h⟩
      · exact .inl ⟨isNe_fall hw, _, h⟩
      · exact .inr ⟨isNe_jump hw, xa_jumpdestAt (hdec (decJmp_spec hd)) rfl h⟩
    · cases ht
  · cases ht

/-- **One always-taken skip.** -/
theorem xa_vyPass (hdec : DecSound dec sevm.code) {p q : Nat} (ht : vyPassAt dec p = some q)
    {M : Mem} {G : Nat} (h : XAt sevm post p (St b S M G) L) :
    ∃ G', XAt sevm post q (St b S M G') L := by
  unfold vyPassAt at ht
  split at ht
  · rename_i t ht2
    split at ht
    · rename_i hb
      cases ht
      simp only [Bool.and_eq_true] at hb
      obtain ⟨⟨⟨hz, hi⟩, hj⟩, hd⟩ := hb
      obtain ⟨hi', lo, le2, e2, rfl⟩ := decPush2_spec ht2
      obtain ⟨le1, e1⟩ := decPush0_spec hz
      obtain ⟨_, s, h⟩ := xa_nextAt (pc' := p + 2) (hdec e1) (by nofun) rfl h
      obtain ⟨_, rfl⟩ := ri_push s
      obtain ⟨_, s, h⟩ := xa_nextAt (pc' := p + 3) (hdec (decReg_spec hi)) (by nofun) rfl h
      obtain ⟨_, rfl⟩ := ri_iszero s
      obtain ⟨_, s, h⟩ := xa_nextAt (pc' := p + 6) (hdec e2) (by nofun) rfl h
      obtain ⟨_, rfl⟩ := ri_push s
      rcases xa_jumpiAt (pf := p + 7) (hdec (decJmp_spec hj)) rfl rfl h with
        ⟨hw, -⟩ | ⟨-, _, h⟩
      · exact absurd hw (by decide)
      · exact xa_jumpdestAt (hdec (decJmp_spec hd)) rfl h
    · cases ht
  · cases ht

/-- **The dispatcher's chain**: a frame whose selector is `σ` reaches the pc the chain hands
`σ`. -/
theorem xa_vyChain (hdec : DecSound dec sevm.code) {σ : B256} (hσ : Sevm.selector sevm = σ)
    (n : Nat) {p e : Nat} {ls : List (Nat × Option B256)} (hc : vyChain dec n p = (ls, e)) {G : Nat}
    (h : XAt sevm post p (St b S Mv G) L) :
    ∃ G', XAt sevm post (vyHit σ ls e) (St b S Mv G') L := by
  induction n generalizing p ls e G with
  | zero =>
      simp only [vyChain, Prod.mk.injEq] at hc
      obtain ⟨rfl, rfl⟩ := hc
      exact ⟨_, h⟩
  | succ n ih =>
      rw [vyChain] at hc
      split at hc
      · rename_i c q ht
        simp only [Prod.mk.injEq] at hc
        obtain ⟨rfl, rfl⟩ := hc
        rw [vyHit]
        split
        · rename_i hc
          rcases xa_vyTest hdec ht h with ⟨-, h'⟩ | ⟨hne, -⟩
          · exact h'
          · exact absurd (hσ.trans hc.symm) hne
        · rename_i hc
          rcases xa_vyTest hdec ht h with ⟨hs, -⟩ | ⟨-, _, h'⟩
          · exact absurd (hs.symm.trans hσ) hc
          · exact ih rfl h'
      · split at hc
        · rename_i q hq
          simp only [Prod.mk.injEq] at hc
          obtain ⟨rfl, rfl⟩ := hc
          rw [vyHit]
          obtain ⟨_, h'⟩ := xa_vyPass hdec hq h
          exact ih rfl h'
        · simp only [Prod.mk.injEq] at hc
          obtain ⟨rfl, rfl⟩ := hc
          exact ⟨_, h⟩

/-- **The all-miss path**: a frame whose selector equals none of the chain's constants reaches
the chain's end. -/
theorem xa_vyChain_miss (hdec : DecSound dec sevm.code) (n : Nat) {p e : Nat}
    {ls : List (Nat × Option B256)} (hc : vyChain dec n p = (ls, e))
    (hmiss : ∀ c ∈ ls.filterMap Prod.snd, Sevm.selector sevm ≠ c) {G : Nat}
    (h : XAt sevm post p (St b S Mv G) L) : ∃ G', XAt sevm post e (St b S Mv G') L := by
  have := xa_vyChain hdec rfl n hc h
  rwa [vyHit_of_not_mem hmiss] at this

end Walk

end Blanc.Lift
