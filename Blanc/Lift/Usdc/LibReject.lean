import Blanc.Lift.StaticSilent
import Blanc.Lift.PairCode
import Blanc.Lift.Usdc.Lib.Check
import Blanc.Lift.Usdc.ProxyWalk
import Blanc.Lift.InvWalkStep
import Blanc.Lift.CodeSizeWalk
import Blanc.Lift.Vyper
import Blanc.Lift.PtrWordMemory

/-!
# The `SignatureChecker` library rejects a Pair signer (U7a, library side)

`lib_rejects_pair`: a successful frame running the 1,741-byte `SignatureChecker` runtime
(`Lib.code`) from a fresh machine, whose first calldata argument names an account holding the
certified Pair runtime outside the precompile range, returns the ABI word `false` (its output is at
least a word long and begins with 32 zero bytes).

The walk, over the library certificate: the preamble sets the free pointer to `0x80` and the
dispatcher admits only `isValidSignatureNow(address,bytes32,bytes)` (`0x6ccea652`), whose decoder
bounds the signature length by `2 ^ 32`; entry 6 asks `isContract` (entry 8, `extcodesize`), which
holds for the Pair, so entry 10 (`isValidERC1271SignatureNow`) runs.  Entry 10 encodes the call
data above the free pointer (`e10_pre`, the word-copy loop `loop12`, the selector word `selWord`
at `F + 32` in `e2_head`), copies it to the new free pointer `E` (`copy_first`, `loop7`), and
`STATICCALL`s the signer with call data whose selector is `0x1626ba7e` (`selWord_shr`).  The Pair
answers no such call (the `hsilent` instance of `NoStaticAnswer`, amendment A11), so the flag
is `0`, entry 10 returns `false` (`e7_exit`, `tail3`), and the frame returns that word
(`final_output`).

Every memory fact is derived inside the frame and carried by `LibMem p M`: the 64 bytes below the
free-pointer word are never written, and the free-pointer word reads `p`; all other writes land at
or above `96` without wrapping.
-/

namespace Blanc.Lift.Usdc

open Jaune Blanc Blanc.Lift Lib

/-- One `ri_shl` step of a cut run. -/
macro "lshl " h:ident : tactic => `(tactic|
  (have h' := ric_next $h; clear $h; obtain ⟨_, hd, $h:ident⟩ := h'
   obtain ⟨_, e⟩ := ri_shl hd; subst e; clear hd))

/-- One `ri_mul` step of a cut run. -/
macro "lmul " h:ident : tactic => `(tactic|
  (have h' := ric_next $h; clear $h; obtain ⟨_, hd, $h:ident⟩ := h'
   obtain ⟨_, e⟩ := ri_mul hd; subst e; clear hd))

/-- One `ri_exp` step of a cut run. -/
macro "lexp " h:ident : tactic => `(tactic|
  (have h' := ric_next $h; clear $h; obtain ⟨_, hd, $h:ident⟩ := h'
   obtain ⟨_, e⟩ := ri_exp hd; subst e; clear hd))

/-- One `ri_address` step of a cut run. -/
macro "laddr " h:ident : tactic => `(tactic|
  (have h' := ric_next $h; clear $h; obtain ⟨_, hd, $h:ident⟩ := h'
   obtain ⟨_, e⟩ := ri_address hd; subst e; clear hd))

/-- One `ri_calldatacopy` step of a cut run. -/
macro "lcdc " h:ident : tactic => `(tactic|
  (have h' := ric_next $h; clear $h; obtain ⟨_, hd, $h:ident⟩ := h'
   obtain ⟨_, e⟩ := ri_calldatacopy hd; subst e; clear hd))

/-- One `ri_returndatasize` step of a cut run. -/
macro "lrds " h:ident : tactic => `(tactic|
  (have h' := ric_next $h; clear $h; obtain ⟨_, hd, $h:ident⟩ := h'
   obtain ⟨_, e⟩ := ri_returndatasize hd; subst e; clear hd))

/-- One `ri_gas` step of a cut run. -/
macro "lgas " h:ident : tactic => `(tactic|
  (have h' := ric_next $h; clear $h; obtain ⟨_, hd, $h:ident⟩ := h'
   obtain ⟨_, _, e⟩ := ri_gas hd; subst e; clear hd))

/-- One `ri_extcodesize` step of a cut run. -/
macro "lecs " h:ident : tactic => `(tactic|
  (have h' := ric_next $h; clear $h; obtain ⟨_, hd, $h:ident⟩ := h'
   obtain ⟨_, e⟩ := ri_extcodesize ‹CoveredFork _› hd; subst e; clear hd))

/-- One `stepX` instruction of a cut run. -/
macro "lx " h:ident : tactic => `(tactic|
  (have h' := ric_next $h; clear $h; obtain ⟨_, hd, $h:ident⟩ := h'
   obtain ⟨_, e⟩ := ri_stepX ‹CoveredFork _› hd rfl
   try dsimp only [List.set, Fin.isValue, Fin.val_zero, Fin.val_one, Fin.val_two] at e
   subst e; clear hd))

/-- A `JUMPDEST` of a cut run. -/
macro "ldest " h:ident : tactic => `(tactic|
  (have h' := ric_dest $h; clear $h; obtain ⟨_, $h:ident⟩ := h'))

theorem lib_run_cut {sevm : Sevm} {b post : Devm} {G : Nat}
    (run : Exec 0 sevm (St b [] Mem.empty G) (.ok post))
    (code : sevm.code = Lib.code) (fork : CoveredFork sevm.benvStat.fork) :
    SFunc.RunCut Lib.cert.prog sevm [] (St b [] Mem.empty G) Lib.t_0000_c0 (.done (.halted post)) := by
  obtain ⟨f, hf, frun⟩ := lift_sound Lib.cert_check code fork run
  rw [show Lib.cert.prog[0]? = some Lib.t_0000_c0 from rfl] at hf
  cases hf
  exact SFunc.Run.cut frun

/-! ## Word and memory helpers -/

theorem add_toNat_small {x y : B256} (h : x.toNat + y.toNat < 2 ^ 256) :
    (x + y).toNat = x.toNat + y.toNat := by
  rw [B256.toNat_add]
  exact Nat.mod_eq_of_lt h

theorem read_write_off {M : Mem} {n i k : Nat} {ys : Bytes} (hwf : Mem.Wf M)
    (h : n + ys.length ≤ i ∨ i + k ≤ n) : ((M.write n ys).read i k).1 = (M.read i k).1 :=
  Mem.read_write_disjoint hwf n ys h

theorem wf_read {M : Mem} (h : Mem.Wf M) (i n : Nat) : Mem.Wf (M.read i n).2 := h.extend i n

theorem wf_write {M : Mem} (h : Mem.Wf M) (i : Nat) (ys : Bytes) : Mem.Wf (M.write i ys) :=
  h.write i ys

/-- Well-formedness of a memory built by writes and reads from a well-formed one. -/
macro "wf_tac" : tactic => `(tactic| repeat (first | assumption | apply wf_write | apply wf_read))

theorem ne_zero_of_iszero_eq {x : B256} (h : B256.eqCheck x 0 = 0) : x ≠ 0 := by
  intro e
  subst e
  exact absurd h (by decide)

theorem eq_zero_of_iszero_ne {x : B256} (h : B256.eqCheck x 0 ≠ 0) : x = 0 := by
  unfold B256.eqCheck at h
  split at h
  · assumption
  · exact absurd rfl h

theorem lt_of_ltCheck_ne {x y : B256} (h : B256.ltCheck x y ≠ 0) : x < y := by
  unfold B256.ltCheck at h
  split at h
  · assumption
  · exact absurd rfl h

theorem not_lt_of_ltCheck_eq {x y : B256} (h : B256.ltCheck x y = 0) : ¬ x < y := by
  intro l
  unfold B256.ltCheck at h
  simp only [l, ↓reduceIte] at h
  exact absurd h (by decide)

/-- A read of at least a word is that word followed by the rest. -/
theorem read_split (M : Mem) (i n : Nat) (h : 32 ≤ n) :
    (M.read i n).1 = (M.read i 32).1 ++ (M.read (i + 32) (n - 32)).1 := by
  rw [(Mem.reads_data M).read, (Mem.reads_data M).read, (Mem.reads_data M).read,
    ← List.sliceD_split]
  congr 1
  omega

/-- Calldata whose head word is `v` has `v`'s top four bytes as its selector. -/
theorem sel_of_head {e : Sevm} {v : B256} {rest : Bytes} (he : e.data = v.toBytes ++ rest) :
    Blanc.Sevm.selector e = v >>> 224 := by
  rw [Sevm.selector_eq_toB256_takeD_four, he, List.takeD_eq_take _ (by
      simp only [List.length_append, B256.length_toBytes]; omega),
    List.take_append_of_le_length (by rw [B256.length_toBytes]; omega),
    shiftRight_224_eq_toB256_take_four]

theorem sub32_toNat {x : B256} (h : 32 ≤ x.toNat) :
    (x + Bytes.toB256 [255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
      255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 224]).toNat =
      x.toNat - 32 := by
  rw [B256.toNat_add]
  have hn : (Bytes.toB256 [255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
      255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 224]).toNat =
      2 ^ 256 - 32 := by decide
  rw [hn]
  have := B256.toNat_lt x
  show (x.toNat + (2 ^ 256 - 32)) % 2 ^ 256 = _
  rw [show x.toNat + (2 ^ 256 - 32) = (x.toNat - 32) + 2 ^ 256 by omega, Nat.add_mod_right,
    Nat.mod_eq_of_lt (by omega)]

theorem one_or_ne_zero (y : B256) : (1 ||| y) ≠ 0 := by
  intro h
  have e := congrArg B256.toNat h
  rw [Blanc.B256.toNat_or, B256.toNat_zero, show (1 : B256).toNat = 1 from rfl] at e
  have t := Nat.testBit_or 1 y.toNat 0
  rw [e] at t
  simp only [Nat.testBit_zero, Nat.zero_mod, Nat.one_mod, decide_true, Bool.true_or] at t
  exact absurd t (by decide)

/-- A decoder guard `iszero(x > c ∨ …)` that passed bounds `x` by `c`. -/
theorem le_of_gt_or_guard {x c y : B256} (h : B256.eqCheck (B256.gtCheck x c ||| y) 0 ≠ 0) :
    x.toNat ≤ c.toNat := by
  have e := eq_zero_of_iszero_ne h
  unfold B256.gtCheck at e
  split at e
  · exact absurd e (one_or_ne_zero y)
  · rename_i hn
    exact B256.le_iff_toNat_le_toNat.mp (le_of_not_gt hn)

/-- The library frame's memory discipline: well-formed, the 64 bytes below the free-pointer word
never written (zero), and the free-pointer word reading `p`. -/
structure LibMem (p : B256) (M : Mem) : Prop where
  wf : Mem.Wf M
  zero : (M.read 0 64).1 = List.replicate 64 0
  ptr : Bytes.toB256 (M.read 64 32).1 = p

theorem LibMem.write {p : B256} {M : Mem} (h : LibMem p M) (i : Nat) (bs : Bytes) (far : 96 ≤ i) :
    LibMem p (M.write i bs) :=
  ⟨h.wf.write i bs, by rw [read_write_off h.wf (by omega)]; exact h.zero,
    by rw [read_write_off h.wf (by omega)]; exact h.ptr⟩

theorem LibMem.extend {p : B256} {M : Mem} (h : LibMem p M) (i n : Nat) : LibMem p (M.read i n).2 :=
  ⟨h.wf.extend i n, by rw [memRead_extend_fst]; exact h.zero,
    by rw [memRead_extend_fst]; exact h.ptr⟩

theorem LibMem.extends {p : B256} {M : Mem} (h : LibMem p M) (pairs : List (Nat × Nat)) :
    LibMem p (M.extends pairs) :=
  ⟨h.wf.extends pairs,
    by rw [((Mem.reads_data M).extends pairs).read, ← (Mem.reads_data M).read]; exact h.zero,
    by rw [((Mem.reads_data M).extends pairs).read, ← (Mem.reads_data M).read]; exact h.ptr⟩

theorem LibMem.set {p : B256} {M : Mem} (h : LibMem p M) (q : B256) :
    LibMem q (M.write 64 q.toBytes) :=
  ⟨h.wf.write _ _, by rw [read_write_off h.wf (by simp only [B256.length_toBytes]; omega)]; exact h.zero,
    by rw [Mem.read_write_word_of_wf h.wf, B256.toB256_toBytes]⟩

theorem lit32 : (Bytes.toB256 [32]).toNat = 32 := by decide
theorem lit36_toNat : (Bytes.toB256 [36]).toNat = 36 := by decide
theorem lit64 : (Bytes.toB256 [64]).toNat = 64 := by decide

/-- **Entry 10's prologue** (`isValidERC1271SignatureNow(signer, digest, signature)`, up to the
encoding loop): the digest and the head words are written above the free pointer `F`, and the
signature length is read back. -/
theorem e10_pre {sevm : Sevm} {b : Devm} {sig dig signer ret F len : B256} {S : List B256}
    {M : Mem} {G : Nat} {o : Outcome} (fork : CoveredFork sevm.benvStat.fork)
    (hp : LibMem F M) (hF : 128 ≤ F.toNat ∧ F.toNat < 2 ^ 40) (hsig : sig.toNat + 32 ≤ F.toNat + 36)
    (hlen : Bytes.toB256 (M.read sig.toNat 32).1 = len)
    (run : SFunc.Run cert.prog sevm (St b (sig :: dig :: signer :: ret :: S) M G) t_0203_c10 o) :
    ∃ M' G', LibMem F M' ∧ SFunc.RunCut cert.prog sevm [] (St b
      (Bytes.toB256 [0] :: (Bytes.toB256 [32] + sig) ::
        (Bytes.toB256 [32] + (Bytes.toB256 [32] + (Bytes.toB256 [32] + (Bytes.toB256 [36] + F)))) ::
        len :: len :: (Bytes.toB256 [32] + sig) ::
        (Bytes.toB256 [32] + (Bytes.toB256 [32] + (Bytes.toB256 [32] + (Bytes.toB256 [36] + F)))) ::
        (Bytes.toB256 [32] + (Bytes.toB256 [36] + F)) :: (Bytes.toB256 [36] + F) :: sig :: dig ::
        Bytes.toB256 [22, 38, 186, 126] <<< (Bytes.toB256 [224]).toNat ::
        (Bytes.toB256 [255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
          255, 255, 255, 255] &&& signer) ::
        Bytes.toB256 [96] :: Bytes.toB256 [0] :: Bytes.toB256 [0] :: sig :: dig :: signer :: ret :: S)
      M' G') t_0257_c10 (.done o) := by
  have h := run.cut
  clear run
  unfold t_0203_c10 at h
  ldest h
  iterate 8 lx h
  lshl h
  iterate 40 lx h
  have hF0 : (M.read (Bytes.toB256 [64]).toNat 32).1.toB256 = F := by rw [lit64]; exact hp.ptr
  rw [hF0] at h
  have hF36 : (Bytes.toB256 [36] + F).toNat = 36 + F.toNat := by
    rw [add_toNat_small (by rw [lit36_toNat]; omega), lit36_toNat]
  have hF68 : (Bytes.toB256 [32] + (Bytes.toB256 [36] + F)).toNat = 68 + F.toNat := by
    rw [add_toNat_small (by rw [lit32, hF36]; omega), lit32, hF36]
    omega
  have hF100 : (Bytes.toB256 [32] + (Bytes.toB256 [32] + (Bytes.toB256 [36] + F))).toNat =
      100 + F.toNat := by
    rw [add_toNat_small (by rw [lit32, hF68]; omega), lit32, hF68]
    omega
  have hwf := hp.wf
  rw [read_write_off (by wf_tac) (by simp only [hF100, B256.length_toBytes]; omega), memRead_extend_fst,
    read_write_off (by wf_tac) (by simp only [hF68, B256.length_toBytes]; omega),
    read_write_off (by wf_tac) (by simp only [hF36, B256.length_toBytes]; omega), memRead_extend_fst,
    hlen] at h
  refine ⟨_, _, ?_, h⟩
  refine ((((hp.extend _ _).write _ _ ?_).write _ _ ?_).extend _ _ |>.write _ _ ?_).extend _ _
  · rw [hF36]; omega
  · rw [hF68]; omega
  · rw [hF100]; omega

theorem t0257_eq : t_0257_c10 = t_0257_c12 := rfl

/-- **The encoding loop** (entry 12, solc's word copy of the signature bytes): every run from its
head keeps the free-pointer word `F` (all writes land at or above `dst ≥ 96`, with no wrap), so
it satisfies whatever every exit satisfies. -/
theorem loop12 {sevm : Sevm} {b : Devm} {src dst len F : B256} {R : List B256} {r : Seg}
    (Q : Seg → Prop) (fork : CoveredFork sevm.benvStat.fork) (hQ : ∀ r, Q r → ∃ o, r = .done o)
    (hdst : 96 ≤ dst.toNat) (hfit : dst.toNat + len.toNat + 64 < 2 ^ 256)
    (exit : ∀ i M G r, LibMem F M → SFunc.RunCut cert.prog sevm [12]
      (St b (i :: src :: dst :: len :: R) M G) t_026f_c12 r → Q r)
    {i : B256} {M : Mem} {G : Nat} (hp : LibMem F M) (hi : i.toNat < len.toNat + 32)
    (run : SFunc.RunCut cert.prog sevm [] (St b (i :: src :: dst :: len :: R) M G) t_0257_c12 r) :
    Q r := by
  refine SFunc.RunCutP.loop (k := 12) rfl (by decide)
    (fun d => ∃ i M G, d = St b (i :: src :: dst :: len :: R) M G ∧ LibMem F M ∧
      i.toNat < len.toNat + 32) Q ?_ _ r ⟨i, M, G, rfl, hp, hi⟩ run
  rintro d ⟨i, M, G, rfl, hp, hi⟩ r h
  unfold t_0257_c12 at h
  ldest h
  iterate 5 lx h
  ibranch h c
  · -- body
    iterate 11 lx h
    obtain ⟨_, e⟩ := ric_jumpCut List.mem_cons_self h
    subst e
    have lt := B256.lt_iff_toNat_lt_toNat.mp (lt_of_ltCheck_ne (ne_zero_of_iszero_eq c))
    have hsrc : (i + dst).toNat = i.toNat + dst.toNat := add_toNat_small (by omega)
    simp only [Seg.LoopPost, ↓reduceIte]
    refine ⟨_, _, _, rfl, ((hp.extend _ _).write _ _ (by omega)), ?_⟩
    rw [add_toNat_small (by rw [lit32]; omega), lit32]
    omega
  · have q := exit _ _ _ _ hp h
    obtain ⟨o, rfl⟩ := hQ _ q
    exact q

/-- `-32`, as solc pushes it. -/
local notation "wNeg32" => Bytes.toB256 [255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 224]
/-- The top four bytes of a word. -/
local notation "maskHi4" => Bytes.toB256 [255, 255, 255, 255, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- The low 28 bytes of a word. -/
local notation "maskLo28" => Bytes.toB256 [255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255]
/-- The address mask. -/
local notation "maskAddr" => Bytes.toB256 [255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255]
/-- `isValidSignature`'s selector, shifted into the top four bytes. -/
local notation "selShl" => Bytes.toB256 [22, 38, 186, 126] <<< B256.toNat (Bytes.toB256 [224])

/-- The word `abi.encodeWithSelector` leaves at the head of the call data: the selector over the
low 28 bytes of what was there. -/
def selWord (w : B256) : B256 := selShl &&& maskHi4 ||| maskLo28 &&& w

theorem top_limb (x : UInt64) :
    ((0x1626ba7e00000000 : UInt64) ||| ((0xffffffff : UInt64) &&& x)) >>> 32 = 0x1626ba7e := by
  apply UInt64.toNat_inj.mp
  rw [UInt64.toNat_shiftRight, UInt64.toNat_or, UInt64.toNat_and]
  have hm : (0xffffffff : UInt64).toNat = 2 ^ 32 - 1 := rfl
  have hc : (0x1626ba7e00000000 : UInt64).toNat = 0x1626ba7e <<< 32 := rfl
  rw [hm, hc, Nat.and_comm, Nat.and_two_pow_sub_one_eq_mod,
    ← Nat.shiftLeft_add_eq_or_of_lt (Nat.mod_lt _ (by decide)), Nat.shiftRight_eq_div_pow,
    Nat.shiftLeft_eq, show UInt64.toNat 32 % 64 = 32 from rfl]
  show _ = 0x1626ba7e
  have := Nat.mod_lt x.toNat (show 0 < 2 ^ 32 by decide)
  omega

/-- The selector word's top four bytes are `isValidSignature`'s selector. -/
theorem selWord_shr (w : B256) : selWord w >>> 224 = 0x1626ba7e := by
  rcases w with ⟨⟨x3, x2⟩, ⟨x1, x0⟩⟩
  have t := top_limb x3
  change ((((0 : UInt64), (0 : UInt64)), ((0 : UInt64),
    ((0x1626ba7e00000000 : UInt64) ||| ((0xffffffff : UInt64) &&& x3)) >>> 32)) : B256) =
    (0x1626ba7e : B256)
  rw [t]
  rfl

/-- **Entry 2** (the tail of `abi.encodeWithSelector`): the encoded length at `F`, the new free
pointer `E`, and the selector word at `F + 32`. -/
theorem e2_head {sevm : Sevm} {b : Devm} {sig dig signer ret F E x : B256} {S : List B256}
    {M : Mem} {G : Nat} {C : List Nat} {r : Seg} (fork : CoveredFork sevm.benvStat.fork)
    (hp : LibMem F M)
    (hF : 128 ≤ F.toNat ∧ F.toNat < 2 ^ 40)
    (h : SFunc.RunCut cert.prog sevm C (St b
      (x :: E :: (Bytes.toB256 [32] + (Bytes.toB256 [36] + F)) :: (Bytes.toB256 [36] + F) :: sig :: dig ::
        selShl :: (maskAddr &&& signer) ::
        Bytes.toB256 [96] :: Bytes.toB256 [0] :: Bytes.toB256 [0] :: sig :: dig :: signer :: ret :: S)
      M G) t_029c_c2 r) :
    ∃ w Me G', LibMem E Me ∧ (Me.read (F + Bytes.toB256 [32]).toNat 32).1 = (selWord w).toBytes ∧
      SFunc.RunCut cert.prog sevm C (St b
        ((F + Bytes.toB256 [32]) :: E :: (E - F + wNeg32) :: (E - F + wNeg32) ::
          (F + Bytes.toB256 [32]) :: E :: E :: F :: (maskAddr &&& signer) ::
          Bytes.toB256 [96] :: Bytes.toB256 [0] :: Bytes.toB256 [0] :: sig :: dig :: signer :: ret :: S)
        Me G') t_032c_c2 r := by
  unfold t_029c_c2 at h
  ldest h
  iterate 49 lx h
  have hF0 : (M.read (Bytes.toB256 [64]).toNat 32).1.toB256 = F := by rw [lit64]; exact hp.ptr
  rw [hF0] at h
  generalize hMa : (M.read (Bytes.toB256 [64]).toNat 32).2.write F.toNat (E - F + wNeg32).toBytes = Ma at h
  generalize hMb : Ma.write (Bytes.toB256 [64]).toNat E.toBytes = Mb at h
  generalize hR : Mb.read (F + Bytes.toB256 [32]).toNat 32 = R at h
  generalize hMc : R.2.write (F + Bytes.toB256 [32]).toNat
    (selShl &&& maskHi4 ||| maskLo28 &&& R.1.toB256).toBytes = Mc at h
  have hF32 : (F + Bytes.toB256 [32]).toNat = F.toNat + 32 := by
    rw [add_toNat_small (by rw [lit32]; omega), lit32]
  rw [lit64] at hMa hMb h
  have wM := hp.wf
  have wMa : Mem.Wf Ma := by rw [← hMa]; wf_tac
  have wMb : Mem.Wf Mb := by rw [← hMb]; wf_tac
  have wR : Mem.Wf R.2 := by rw [← hR]; wf_tac
  have e1 : (Mc.read 64 32).1.toB256 = E := by
    rw [← hMc, read_write_off wR (by rw [hF32]; omega), ← hR, memRead_extend_fst, ← hMb,
      Mem.read_write_word_of_wf wMa, B256.toB256_toBytes]
  rw [e1] at h
  generalize hMd : (Mc.read 64 32).2 = Md at h
  have e2 : (Md.read F.toNat 32).1.toB256 = E - F + wNeg32 := by
    rw [← hMd, memRead_extend_fst, ← hMc, read_write_off wR (by rw [hF32]; omega), ← hR, memRead_extend_fst, ← hMb,
      read_write_off wMa (by simp only [B256.length_toBytes]; omega), ← hMa,
      Mem.read_write_word_of_wf (wf_read wM _ _), B256.toB256_toBytes]
  rw [e2] at h
  generalize hMe : (Md.read F.toNat 32).2 = Me at h
  refine ⟨R.1.toB256, Me, _, ?_, ?_, h⟩
  · have pMa : LibMem F Ma := by
      rw [← hMa]; exact (hp.extend _ _).write _ _ (by omega)
    have pMb : LibMem E Mb := by rw [← hMb]; exact pMa.set E
    have pR : LibMem E R.2 := by rw [← hR]; exact pMb.extend _ _
    rw [← hMe, ← hMd, ← hMc]
    exact ((pR.write _ _ (by rw [hF32]; omega)).extend _ _).extend _ _
  · rw [← hMe, memRead_extend_fst, ← hMd, memRead_extend_fst, ← hMc, Mem.read_write_word_of_wf wR]
    rfl

/-- **Entries 3 and 4 after a failed `STATICCALL`**: the flag `0` is the result, and entry 10
returns it. -/
theorem tail3 {sevm : Sevm} {b : Devm} {a c sig dig signer ret : B256} {S : List B256}
    {M : Mem} {G : Nat} {C : List Nat} {r : Seg} (fork : CoveredFork sevm.benvStat.fork)
    (hC : 4 ∉ C)
    (h : SFunc.RunCut cert.prog sevm C (St b (a :: c :: 0 :: Bytes.toB256 [96] :: Bytes.toB256 [0] ::
      Bytes.toB256 [0] :: sig :: dig :: signer :: ret :: S) M G) t_03ce_c3 r) :
    ∃ b' G', r = .done (.returned (St b' (0 :: S) M G')) := by
  unfold t_03ce_c3 at h
  ldest h
  iterate 9 lx h
  rcases ric_branchTo hC rfl h with ⟨c1, _, h⟩ | ⟨-, _, h⟩
  · exact absurd c1 (by decide)
  change SFunc.RunCut _ _ _ _ t_03e2_c4 _ at h
  unfold t_03e2_c4 at h
  ldest h
  iterate 3 lx h
  rcases ric_branch h with ⟨c2, _, h⟩ | ⟨-, _, h⟩
  · exact absurd c2 (by decide)
  unfold t_01f9_c4 at h
  ldest h
  iterate 8 lx h
  obtain ⟨_, e⟩ := ric_ret h
  exact ⟨_, _, e⟩

/-- **The copy loop's exit and the `STATICCALL`** (entry 7's exit, then entries 3 and 4): the
partial last word lands above the head word; the call data at the free pointer `E` begins with the
selector word, so a Pair signer cannot answer (the `hsilent` hypothesis, amendment A11),
the flag is `0`, and entry 10 returns `0`. -/
theorem e7_exit {sevm : Sevm} {b : Devm} {sig dig signer ret F E L src dst len w : B256}
    {S : List B256} {M : Mem} {G : Nat} {C : List Nat} {r : Seg}
    (fork : CoveredFork sevm.benvStat.fork) (hC3 : 3 ∉ C) (hC4 : 4 ∉ C)
    (hcode : b.getCode (maskAddr &&& signer).toAdr = UniswapV2Pair.code)
    (notPrecompile : ¬ sevm.benvStat.rules.isPrecomp (maskAddr &&& signer).toAdr)
    (hsilent : NoStaticAnswer UniswapV2Pair.code 0x1626ba7e)
    (hp : LibMem E M) (hw : (M.read E.toNat 32).1 = (selWord w).toBytes)
    (hE : 96 ≤ E.toNat) (hEb : E.toNat < 2 ^ 200) (hdst : E.toNat + 32 ≤ dst.toNat) (hL : 32 ≤ (L + E - E).toNat)
    (h : SFunc.RunCut cert.prog sevm (7 :: C) (St b
        (src :: dst :: len :: L ::
          (F + Bytes.toB256 [32]) :: E :: E :: F :: (maskAddr &&& signer) ::
          Bytes.toB256 [96] :: Bytes.toB256 [0] :: Bytes.toB256 [0] :: sig :: dig :: signer :: ret :: S)
        M G) t_0369_c7 r) :
    ∃ b' q M' G', LibMem q M' ∧ r = .done (.returned (St b' (0 :: S) M' G')) := by
  unfold t_0369_c7 at h
  ldest h
  iterate 5 lx h
  lexp h
  iterate 35 lx h
  lgas h
  generalize hRs : M.read src.toNat 32 = Rs at h
  generalize hRd : Rs.2.read dst.toNat 32 = Rd at h
  generalize hWp : (Rs.1.toB256 &&& ~~~((Bytes.toB256 [1, 0]).bexp (Bytes.toB256 [32] - len) -
    Bytes.toB256 [1]) ||| Rd.1.toB256 &&& (Bytes.toB256 [1, 0]).bexp (Bytes.toB256 [32] - len) -
    Bytes.toB256 [1]) = Wp at h
  generalize hMw : Rd.2.write dst.toNat Wp.toBytes = Mw at h
  rw [lit64] at h
  have wR : Mem.Wf Rd.2 := by rw [← hRd, ← hRs]; have := hp.wf; wf_tac
  have e64 : (Mw.read 64 32).1.toB256 = E := by
    rw [← hMw, read_write_off wR (by omega), ← hRd, memRead_extend_fst, ← hRs, memRead_extend_fst]
    exact hp.ptr
  rw [e64] at h
  generalize hMx : (Mw.read 64 32).2 = Mx at h
  have hx : (Mx.read E.toNat 32).1 = (selWord w).toBytes := by
    rw [← hMx, memRead_extend_fst, ← hMw, read_write_off wR (by omega), ← hRd, memRead_extend_fst, ← hRs, memRead_extend_fst, hw]
  obtain ⟨_, hd, h⟩ := ric_next h
  obtain ⟨flag, out, post, hans⟩ := ri_staticcall fork hd
  rw [post.eq_St] at h
  have hf0 : flag = 0 := by
    rcases post.flag with h0 | h1
    · exact h0
    · exfalso
      refine hsilent hcode notPrecompile fork (fun e he => ?_) (hans h1)
      rw [read_split _ _ _ hL, hx] at he
      rw [sel_of_head he]
      exact selWord_shr w
  subst hf0
  have pRd : LibMem E Rd.2 := by rw [← hRd, ← hRs]; exact (hp.extend _ _).extend _ _
  have pMx : LibMem E Mx := by rw [← hMx, ← hMw]; exact (pRd.write _ _ (by omega)).extend _ _
  generalize hMp : (Mx.extends [(E.toNat, (L + E - E).toNat), (E.toNat, (Bytes.toB256 [0]).toNat)]).write
    E.toNat (List.take (Bytes.toB256 [0]).toNat out) = Mp at h
  have pMp : LibMem E Mp := by rw [← hMp]; exact (pMx.extends _).write _ _ hE
  iterate 3 lx h
  lrds h
  iterate 5 lx h
  rcases ric_branch h with ⟨-, _, h⟩ | ⟨-, _, h⟩
  · unfold t_03a8_c7 at h
    iterate 7 lx h
    lrds h
    iterate 6 lx h
    lrds h
    iterate 2 lx h
    lrds h
    iterate 4 lx h
    obtain ⟨_, hd, h⟩ := ric_next h
    obtain ⟨-, _, e⟩ := ri_returndatacopy hd
    subst e
    lx h
    obtain ⟨_, h⟩ := ric_jump (List.not_mem_cons_of_ne_of_not_mem (by decide) hC3) rfl h
    obtain ⟨b', G', e⟩ := tail3 fork (List.not_mem_cons_of_ne_of_not_mem (by decide) hC4) h
    have pE : (Mp.read (Bytes.toB256 [64]).toNat 32).1.toB256 = E := by rw [lit64]; exact pMp.ptr
    rw [pE, lit64] at e
    exact ⟨b', _, _, G', (((pMp.extend _ _).set _).write _ _ hE).write _ _
      (by rw [add_toNat_small (by rw [lit32]; omega), lit32]; omega), e⟩
  · unfold t_03c9_c7 at h
    ldest h
    iterate 3 lx h
    obtain ⟨b', G', e⟩ := tail3 fork (List.not_mem_cons_of_ne_of_not_mem (by decide) hC4) h
    exact ⟨b', E, Mp, G', pMp, e⟩

/-- **The call-data copy loop** (entry 7, solc's copy of `bytes memory` into a call buffer at
`E`): each iteration writes one word above the head word and keeps the free pointer `E`; the exit
is `e7_exit`. -/
theorem loop7 {sevm : Sevm} {b : Devm} {sig dig signer ret F E L w : B256} {S : List B256}
    {C : List Nat} {r : Seg} (fork : CoveredFork sevm.benvStat.fork)
    (hC7 : 7 ∉ C) (hC3 : 3 ∉ C) (hC4 : 4 ∉ C)
    (hcode : b.getCode (maskAddr &&& signer).toAdr = UniswapV2Pair.code)
    (notPrecompile : ¬ sevm.benvStat.rules.isPrecomp (maskAddr &&& signer).toAdr)
    (hsilent : NoStaticAnswer UniswapV2Pair.code 0x1626ba7e)
    (hE : 96 ≤ E.toNat) (hEb : E.toNat < 2 ^ 200) (hL : 32 ≤ (L + E - E).toNat)
    {src dst len : B256} {M : Mem} {G : Nat}
    (hp : LibMem E M) (hw : (M.read E.toNat 32).1 = (selWord w).toBytes)
    (hdst : E.toNat + 32 ≤ dst.toNat) (hfit : dst.toNat + len.toNat < 2 ^ 200)
    (run : SFunc.RunCut cert.prog sevm C (St b
        (src :: dst :: len :: L ::
          (F + Bytes.toB256 [32]) :: E :: E :: F :: (maskAddr &&& signer) ::
          Bytes.toB256 [96] :: Bytes.toB256 [0] :: Bytes.toB256 [0] :: sig :: dig :: signer :: ret :: S)
        M G) t_032c_c7 r) :
    ∃ b' q M' G', LibMem q M' ∧ r = .done (.returned (St b' (0 :: S) M' G')) := by
  refine SFunc.RunCutP.loop (k := 7) rfl hC7
    (fun d => ∃ src dst len M G, d = St b (src :: dst :: len :: L ::
          (F + Bytes.toB256 [32]) :: E :: E :: F :: (maskAddr &&& signer) ::
          Bytes.toB256 [96] :: Bytes.toB256 [0] :: Bytes.toB256 [0] :: sig :: dig :: signer :: ret :: S)
        M G ∧ LibMem E M ∧ (M.read E.toNat 32).1 = (selWord w).toBytes ∧
        E.toNat + 32 ≤ dst.toNat ∧ dst.toNat + len.toNat < 2 ^ 200)
    (fun r => ∃ b' q M' G', LibMem q M' ∧ r = .done (.returned (St b' (0 :: S) M' G'))) ?_ _ r
    ⟨src, dst, len, M, G, rfl, hp, hw, hdst, hfit⟩ run
  rintro d ⟨src, dst, len, M, G, rfl, hp, hw, hdst, hfit⟩ r h
  unfold t_032c_c7 at h
  ldest h
  iterate 4 lx h
  rcases ric_branch h with ⟨c, _, h⟩ | ⟨-, _, h⟩
  · iterate 16 lx h
    obtain ⟨_, e⟩ := ric_jumpCut List.mem_cons_self h
    subst e
    have l32 : 32 ≤ len.toNat := by
      have := not_lt_of_ltCheck_eq c
      rw [B256.lt_iff_toNat_lt_toNat, lit32] at this
      omega
    simp only [Seg.LoopPost, ↓reduceIte]
    refine ⟨_, _, _, _, _, rfl, (hp.extend _ _).write _ _ (by omega), ?_, ?_, ?_⟩
    · rw [read_write_off (wf_read hp.wf _ _) (by omega), memRead_extend_fst, hw]
    · rw [add_toNat_small (by rw [lit32]; omega), lit32]
      omega
    · rw [add_toNat_small (by rw [lit32]; omega), lit32, sub32_toNat l32]
      omega
  · obtain ⟨b', q, M', G', pq, e⟩ := e7_exit fork hC3 hC4 hcode notPrecompile hsilent hp hw hE hEb hdst hL h
    subst e
    exact ⟨b', q, M', G', pq, rfl⟩

theorem add_sub_cancel_toNat (a e : B256) : (a + e - e).toNat = a.toNat := by
  rw [B256.toNat_sub, B256.toNat_add]
  have := B256.toNat_lt a
  have := B256.toNat_lt e
  show (2 ^ 256 + (a.toNat + e.toNat) % 2 ^ 256 - e.toNat) % 2 ^ 256 = a.toNat
  omega

/-- **The call-data copy, from its first test** (entry 2's inline loop head): the encoding is at
least a word long, so the first iteration copies the selector word to `E`, then the loop runs. -/
theorem copy_first {sevm : Sevm} {b : Devm} {sig dig signer ret F E w : B256} {S : List B256}
    {M : Mem} {G : Nat} {C : List Nat} {r : Seg} (fork : CoveredFork sevm.benvStat.fork)
    (hC7 : 7 ∉ C) (hC3 : 3 ∉ C) (hC4 : 4 ∉ C)
    (hcode : b.getCode (maskAddr &&& signer).toAdr = UniswapV2Pair.code)
    (notPrecompile : ¬ sevm.benvStat.rules.isPrecomp (maskAddr &&& signer).toAdr)
    (hsilent : NoStaticAnswer UniswapV2Pair.code 0x1626ba7e)
    (hF : 128 ≤ F.toNat) (hEF : F.toNat + 132 ≤ E.toNat) (hE : E.toNat < 2 ^ 100)
    (hp : LibMem E M) (hw : (M.read (F + Bytes.toB256 [32]).toNat 32).1 = (selWord w).toBytes)
    (h : SFunc.RunCut cert.prog sevm C (St b
        ((F + Bytes.toB256 [32]) :: E :: (E - F + wNeg32) :: (E - F + wNeg32) ::
          (F + Bytes.toB256 [32]) :: E :: E :: F :: (maskAddr &&& signer) ::
          Bytes.toB256 [96] :: Bytes.toB256 [0] :: Bytes.toB256 [0] :: sig :: dig :: signer :: ret :: S)
        M G) t_032c_c2 r) :
    ∃ b' q M' G', LibMem q M' ∧ r = .done (.returned (St b' (0 :: S) M' G')) := by
  have hEF' : (E - F).toNat = E.toNat - F.toNat :=
    B256.toNat_sub_eq_of_le _ _ (B256.le_iff_toNat_le_toNat.mpr (by omega))
  have hL : (E - F + wNeg32).toNat = E.toNat - F.toNat - 32 := by
    rw [sub32_toNat (by omega), hEF']
  unfold t_032c_c2 at h
  ldest h
  iterate 4 lx h
  rcases ric_branch h with ⟨-, _, h⟩ | ⟨c, _, h⟩
  swap
  · have := lt_of_ltCheck_ne c
    rw [B256.lt_iff_toNat_lt_toNat, lit32, hL] at this
    omega
  iterate 16 lx h
  obtain ⟨_, h⟩ := ric_jump hC7 rfl h
  have hF32 : (F + Bytes.toB256 [32]).toNat = F.toNat + 32 := by
    rw [add_toNat_small (by rw [lit32]; omega), lit32]
  refine loop7 (w := w) fork hC7 hC3 hC4 hcode notPrecompile hsilent (by omega) (by omega) (by rw [add_sub_cancel_toNat, hL]; omega)
    ((hp.extend _ _).write _ _ (by omega)) ?_ ?_ ?_ h
  · rw [Mem.read_write_word_of_wf (wf_read hp.wf _ _), hw, B256.toB256_toBytes]
  · rw [add_toNat_small (by rw [lit32]; omega), lit32]
    omega
  · rw [add_toNat_small (by rw [lit32]; omega), lit32, sub32_toNat (by omega), hL]
    omega

theorem and31_le (x : B256) : (Bytes.toB256 [31] &&& x).toNat ≤ x.toNat := by
  rw [B256.toNat_and]
  exact Nat.and_le_right

/-- **Entry 10, `isValidERC1271SignatureNow(signer, digest, signature)`, for a Pair signer**:
whatever the signature, the frame returns `false`.  The free pointer `F` lies above the signature
length word at `sig`, and that length is at most `2 ^ 32` (the facts the library's own calldata
decoder establishes). -/
theorem e10_inv {sevm : Sevm} {b : Devm} {sig dig signer ret F len : B256} {S : List B256}
    {M : Mem} {G : Nat} {o : Outcome} (fork : CoveredFork sevm.benvStat.fork)
    (hcode : b.getCode (maskAddr &&& signer).toAdr = UniswapV2Pair.code)
    (notPrecompile : ¬ sevm.benvStat.rules.isPrecomp (maskAddr &&& signer).toAdr)
    (hsilent : NoStaticAnswer UniswapV2Pair.code 0x1626ba7e)
    (hp : LibMem F M) (hF : 128 ≤ F.toNat ∧ F.toNat < 2 ^ 40) (hsig : sig.toNat + 32 ≤ F.toNat + 36)
    (hlen : Bytes.toB256 (M.read sig.toNat 32).1 = len) (hlen32 : len.toNat ≤ 2 ^ 32)
    (run : SFunc.Run cert.prog sevm (St b (sig :: dig :: signer :: ret :: S) M G) t_0203_c10 o) :
    ∃ b' q M' G', LibMem q M' ∧ o = .returned (St b' (0 :: S) M' G') := by
  obtain ⟨M1, G1, hp1, h⟩ := e10_pre fork hp hF hsig hlen run
  rw [t0257_eq] at h
  have hF36 : (Bytes.toB256 [36] + F).toNat = 36 + F.toNat := by
    rw [add_toNat_small (by rw [lit36_toNat]; omega), lit36_toNat]
  have hF68 : (Bytes.toB256 [32] + (Bytes.toB256 [36] + F)).toNat = 68 + F.toNat := by
    rw [add_toNat_small (by rw [lit32, hF36]; omega), lit32, hF36]
    omega
  have hF100 : (Bytes.toB256 [32] + (Bytes.toB256 [32] + (Bytes.toB256 [36] + F))).toNat =
      100 + F.toNat := by
    rw [add_toNat_small (by rw [lit32, hF68]; omega), lit32, hF68]
    omega
  have hD : (Bytes.toB256 [32] + (Bytes.toB256 [32] + (Bytes.toB256 [32] + (Bytes.toB256 [36] + F)))).toNat =
      F.toNat + 132 := by
    rw [add_toNat_small (by rw [lit32, hF100]; omega), lit32, hF100]
    omega
  have key := loop12 (fun r => ∃ b' q M' G', LibMem q M' ∧ r = .done (.returned (St b' (0 :: S) M' G'))) fork
    (fun r ⟨b', q, M', G', _, e⟩ => ⟨_, e⟩) (by rw [hD]; omega) (by rw [hD]; omega) ?_ hp1
    (by simp only [show (Bytes.toB256 [0]).toNat = 0 by decide]; omega) h
  · obtain ⟨b', q, M', G', pq, e⟩ := key
    exact ⟨b', q, M', G', pq, Seg.done.inj e⟩
  intro i M2 G2 r hp2 h
  unfold t_026f_c12 at h
  ldest h
  iterate 15 lx h
  have hE0 : (len + (Bytes.toB256 [32] + (Bytes.toB256 [32] + (Bytes.toB256 [32] +
      (Bytes.toB256 [36] + F))))).toNat = len.toNat + (F.toNat + 132) := by
    rw [add_toNat_small (by rw [hD]; omega), hD]
  have hr := and31_le len
  rcases ric_branchTo (by decide) rfl h with ⟨-, _, h⟩ | ⟨-, _, h⟩
  · unfold t_0283_c12 at h
    iterate 10 lx h
    lexp h
    iterate 9 lx h
    have hsub : (len + (Bytes.toB256 [32] + (Bytes.toB256 [32] + (Bytes.toB256 [32] +
        (Bytes.toB256 [36] + F)))) - (Bytes.toB256 [31] &&& len)).toNat =
        len.toNat + (F.toNat + 132) - (Bytes.toB256 [31] &&& len).toNat := by
      rw [B256.toNat_sub_eq_of_le _ _ (B256.le_iff_toNat_le_toNat.mpr (by rw [hE0]; omega)), hE0]
    obtain ⟨w, Me, G3, hpe, hwe, h⟩ := e2_head fork ((hp2.extend _ _).write _ _ (by omega)) hF h
    have hE1 : (Bytes.toB256 [32] + (len + (Bytes.toB256 [32] + (Bytes.toB256 [32] +
        (Bytes.toB256 [32] + (Bytes.toB256 [36] + F)))) - (Bytes.toB256 [31] &&& len))).toNat =
        32 + (len.toNat + (F.toNat + 132) - (Bytes.toB256 [31] &&& len).toNat) := by
      rw [add_toNat_small (by rw [lit32, hsub]; omega), lit32, hsub]
    exact copy_first fork (by decide) (by decide) (by decide) hcode notPrecompile hsilent hF.1
      (by rw [hE1]; omega) (by rw [hE1]; omega) hpe hwe h
  · obtain ⟨w, Me, G3, hpe, hwe, h⟩ := e2_head fork hp2 hF h
    exact copy_first fork (by decide) (by decide) (by decide) hcode notPrecompile hsilent hF.1
      (by rw [hE0]; omega) (by rw [hE0]; omega) hpe hwe h

/-- **Entry 8, `isContract(addr)`**: `extcodesize(addr) > 0`. -/
theorem lib_e8_inv {sevm : Sevm} {b : Devm} {x ret : B256} {S : List B256} {M : Mem} {G : Nat}
    {o : Outcome} (fork : CoveredFork sevm.benvStat.fork)
    (run : SFunc.Run cert.prog sevm (St b (x :: ret :: S) M G) t_0179_c8 o) :
    ∃ G', o = .returned (St (temporalAccountAccessBase b x.toAdr)
      (B256.eqCheck (B256.eqCheck (b.getCode x.toAdr).size.toB256 0) 0 :: S) M G') := by
  have h := run.cut
  clear run
  unfold t_0179_c8 at h
  ldest h
  lecs h
  iterate 3 lx h
  obtain ⟨G', e⟩ := ric_ret h
  exact ⟨G', Seg.done.inj e⟩

theorem pair_size_ne : (UniswapV2Pair.code.size.toB256 : B256) ≠ 0 := by decide +kernel

theorem and_mask_toAdr (v : B256) : (v &&& maskAddr).toAdr = v.toAdr := by
  rw [show maskAddr = ⟨⟨0, 0xffffffff⟩, ⟨0xffffffffffffffff, 0xffffffffffffffff⟩⟩ from rfl]
  obtain ⟨⟨hh, hl⟩, ⟨lh, ll⟩⟩ := v
  show ((hl &&& 4294967295).toUInt32, lh &&& 18446744073709551615, ll &&& 18446744073709551615) =
    (hl.toUInt32, lh, ll)
  rw [UInt64.toUInt32_and, show (4294967295 : UInt64).toUInt32 = -1 from rfl,
    show (18446744073709551615 : UInt64) = -1 from rfl, UInt32.and_neg_one, UInt64.and_neg_one,
    UInt64.and_neg_one]

theorem access_getCode (b : Devm) (a x : Adr) :
    (temporalAccountAccessBase b a).getCode x = b.getCode x := by
  simp only [Devm.getCode, Devm.getAcct, Blanc.Lift.temporalAccountAccessBase_state]

theorem mask_toAdr (x : B256) : (maskAddr &&& x).toAdr = x.toAdr := by
  rw [ff20_and_word, toAdr_toB256]

/-- **Entry 6, `isValidSignatureNow(signer, digest, signature)`, for a Pair signer**: the signer
has code, so the EIP-1271 branch (entry 10) runs, and the frame returns `false`. -/
theorem e6_inv {sevm : Sevm} {b : Devm} {sig dig signer ret F len : B256} {S : List B256}
    {M : Mem} {G : Nat} {o : Outcome} (fork : CoveredFork sevm.benvStat.fork)
    (hcode : b.getCode signer.toAdr = UniswapV2Pair.code)
    (notPrecompile : ¬ sevm.benvStat.rules.isPrecomp signer.toAdr)
    (hsilent : NoStaticAnswer UniswapV2Pair.code 0x1626ba7e)
    (hp : LibMem F M) (hF : 128 ≤ F.toNat ∧ F.toNat < 2 ^ 40) (hsig : sig.toNat + 32 ≤ F.toNat + 36)
    (hlen : Bytes.toB256 (M.read sig.toNat 32).1 = len) (hlen32 : len.toNat ≤ 2 ^ 32)
    (run : SFunc.Run cert.prog sevm (St b (sig :: dig :: signer :: ret :: S) M G) t_0116_c6 o) :
    ∃ b' q M' G', LibMem q M' ∧ o = .returned (St b' (0 :: S) M' G') := by
  have h := run.cut
  clear run
  unfold t_0116_c6 at h
  ldest h
  iterate 4 lx h
  rcases ric_call rfl h with ⟨G1, ⟨D, hc, h⟩ | ⟨D, hc, -⟩⟩
  swap
  · obtain ⟨_, e⟩ := lib_e8_inv fork hc
    cases e
  obtain ⟨G2, e⟩ := lib_e8_inv fork hc
  cases e
  clear hc
  unfold t_0121_c6 at h
  ldest h
  lx h
  rcases ric_branch h with ⟨c, _, h⟩ | ⟨-, _, h⟩
  · rw [hcode] at c
    exact absurd (eq_zero_of_iszero_ne (ne_zero_of_iszero_eq c)) pair_size_ne
  unfold t_0164_c6 at h
  ldest h
  iterate 5 lx h
  rcases ric_call rfl h with ⟨G3, ⟨D, hc, h⟩ | ⟨D, hc, -⟩⟩
  swap
  · obtain ⟨_, _, _, _, _, e⟩ := e10_inv fork (by rw [access_getCode, mask_toAdr]; exact hcode)
      (by rw [mask_toAdr]; exact notPrecompile) hsilent hp hF hsig hlen hlen32 hc
    cases e
  obtain ⟨b4, q4, M4, G4, p4, e⟩ := e10_inv fork (by rw [access_getCode, mask_toAdr]; exact hcode)
    (by rw [mask_toAdr]; exact notPrecompile) hsilent hp hF hsig hlen hlen32 hc
  cases e
  clear hc
  unfold t_016f_c6 at h
  ldest h
  iterate 2 lx h
  unfold t_0172_c1 at h
  ldest h
  iterate 5 lx h
  obtain ⟨G5, e⟩ := ric_ret h
  exact ⟨_, q4, M4, _, p4, Seg.done.inj e⟩

theorem read_len (M : Mem) (i n : Nat) : (M.read i n).1.length = n := by
  rw [(Mem.reads_data M).read, List.sliceD_eq_map, List.length_map, List.length_range]

/-- The high 31 bytes of a word below 96 are zero. -/
theorem small_bytes : ∀ n : Fin 96, ∀ j : Fin 31, (Nat.toB256 n.val).toBytes.getD j.val 0 = 0 := by
  decide +kernel

theorem getD_rep0_fin : ∀ i : Fin 32, (List.replicate 32 (0 : UInt8)).getD i.val 0 = 0 := by decide

theorem getD_rep0 (i : Nat) (h : i < 32) : (List.replicate 32 (0 : UInt8)).getD i 0 = 0 :=
  getD_rep0_fin ⟨i, h⟩

theorem toB256_replicate_zero : Bytes.toB256 (List.replicate 32 0) = 0 := by decide

theorem zero_toBytes : (0 : B256).toBytes = List.replicate 32 0 := by decide

/-- The word read at `64` after writing a zero word at `q < 96`: unchanged below `64`, zero from
`64` on (the write reaches the free-pointer word's low byte). -/
theorem ptr_after_low_write {M : Mem} {q : B256} (pq : LibMem q M) (hq : q.toNat < 96) :
    Bytes.toB256 (((M.read 64 32).2.write q.toNat (0 : B256).toBytes).read 64 32).1 =
      if q.toNat < 64 then q else 0 := by
  have wf := pq.wf.extend 64 32
  have hR := (Mem.reads_data M).extend 64 32
  change Bytes.toB256 (((M.extend 64 32).write q.toNat (0 : B256).toBytes).read 64 32).1 = _
  rw [(hR.write wf q.toNat _).read]
  have old : M.data.toList.sliceD 64 32 0 = q.toBytes := by
    rw [← (Mem.reads_data M).read, ← Bytes.toBytes_toB256_of_length (read_len M 64 32), pq.ptr]
  have qn : q = Nat.toB256 q.toNat :=
    B256.toNat_inj _ _ (by rw [B256.toNat_toB256_of_lt (by omega)])
  have byte : ∀ j, j < 31 → M.data.toList.getD (64 + j) 0 = 0 := by
    intro j hj
    have e := congrArg (fun l => List.getD l j 0) old
    simp only [List.sliceD_eq_map, List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_range (show j < 32 by omega), Option.map_some, Option.getD_some] at e
    rw [List.getD_eq_getElem?_getD, e, qn]
    exact small_bytes ⟨q.toNat, hq⟩ ⟨j, hj⟩
  split
  · rename_i hlt
    have e : (Bytes.writeAt M.data.toList q.toNat (0 : B256).toBytes).sliceD 64 32 0 =
        M.data.toList.sliceD 64 32 0 := by
      rw [List.sliceD_eq_map, List.sliceD_eq_map]
      apply List.map_congr_left
      intro j hj
      have hj' := List.mem_range.mp hj
      rw [Bytes.getD_writeAt, B256.length_toBytes]
      split
      · rw [zero_toBytes, getD_rep0 (64 + j - q.toNat) (by omega), byte j (by omega)]
      · rfl
    rw [e, old, B256.toB256_toBytes]
  · rename_i hge
    have e : (Bytes.writeAt M.data.toList q.toNat (0 : B256).toBytes).sliceD 64 32 0 =
        List.replicate 32 0 := by
      rw [show List.replicate 32 (0 : UInt8) = (List.range 32).map (fun _ => 0) by
        rw [List.map_const', List.length_range], List.sliceD_eq_map]
      apply List.map_congr_left
      intro j hj
      have hj' := List.mem_range.mp hj
      rw [Bytes.getD_writeAt, B256.length_toBytes]
      split
      · rw [zero_toBytes, getD_rep0 (64 + j - q.toNat) (by omega)]
      · exact byte j (by omega)
    rw [e, toB256_replicate_zero]

theorem take_read_split (M : Mem) (i n : Nat) (h : 32 ≤ n) :
    (M.read i n).1.take 32 = (M.read i 32).1 := by
  rw [read_split M i n h, List.take_left' (read_len M i 32)]

theorem sub_self_toNat (x : B256) : (Bytes.toB256 [32] + (x - x)).toNat = 32 := by
  rw [B256.toNat_add, B256.toNat_sub, lit32]
  have := B256.toNat_lt x
  show (32 + (2 ^ 256 + x.toNat - x.toNat) % 2 ^ 256) % 2 ^ 256 = 32
  omega

/-- **The library's `return(mload(0x40), 32)` of a zero word** (entry 13's tail): whatever the
free pointer `q`, the returned bytes are at least a word long and begin with 32 zero bytes. -/
theorem final_output {M : Mem} {q : B256} (pq : LibMem q M) :
    32 ≤ ((((M.read 64 32).2.write q.toNat (0 : B256).toBytes).read 64 32).2.read
        (Bytes.toB256 (((M.read 64 32).2.write q.toNat (0 : B256).toBytes).read 64 32).1).toNat
        (Bytes.toB256 [32] + (q - Bytes.toB256 (((M.read 64 32).2.write q.toNat
          (0 : B256).toBytes).read 64 32).1)).toNat).1.length ∧
    ((((M.read 64 32).2.write q.toNat (0 : B256).toBytes).read 64 32).2.read
        (Bytes.toB256 (((M.read 64 32).2.write q.toNat (0 : B256).toBytes).read 64 32).1).toNat
        (Bytes.toB256 [32] + (q - Bytes.toB256 (((M.read 64 32).2.write q.toNat
          (0 : B256).toBytes).read 64 32).1)).toNat).1.take 32 = List.replicate 32 0 := by
  have wR := wf_read pq.wf 64 32
  have same : Bytes.toB256 (((M.read 64 32).2.write q.toNat (0 : B256).toBytes).read 64 32).1 = q →
      32 ≤ ((((M.read 64 32).2.write q.toNat (0 : B256).toBytes).read 64 32).2.read
        (Bytes.toB256 (((M.read 64 32).2.write q.toNat (0 : B256).toBytes).read 64 32).1).toNat
        (Bytes.toB256 [32] + (q - Bytes.toB256 (((M.read 64 32).2.write q.toNat
          (0 : B256).toBytes).read 64 32).1)).toNat).1.length ∧
      ((((M.read 64 32).2.write q.toNat (0 : B256).toBytes).read 64 32).2.read
        (Bytes.toB256 (((M.read 64 32).2.write q.toNat (0 : B256).toBytes).read 64 32).1).toNat
        (Bytes.toB256 [32] + (q - Bytes.toB256 (((M.read 64 32).2.write q.toNat
          (0 : B256).toBytes).read 64 32).1)).toNat).1.take 32 = List.replicate 32 0 := by
    intro e
    rw [e, sub_self_toNat, read_len]
    refine ⟨le_refl _, ?_⟩
    rw [memRead_extend_fst, Mem.read_write_word_of_wf wR, zero_toBytes, List.take_replicate]
    rfl
  by_cases hq : 96 ≤ q.toNat
  · apply same
    rw [read_write_off wR (Or.inr (by omega)), memRead_extend_fst]
    exact pq.ptr
  have e := ptr_after_low_write pq (by omega)
  by_cases hl : q.toNat < 64
  · simp only [hl, ↓reduceIte] at e
    exact same e
  simp only [hl, ↓reduceIte] at e
  rw [e]
  have h0 : (q - 0).toNat = q.toNat := by
    rw [B256.toNat_sub_eq_of_le _ _ (B256.le_iff_toNat_le_toNat.mpr (by rw [B256.toNat_zero]; omega)),
      B256.toNat_zero, Nat.sub_zero]
  have hs : (Bytes.toB256 [32] + (q - 0)).toNat = 32 + q.toNat := by
    rw [add_toNat_small (by rw [lit32, h0]; omega), lit32, h0]
  rw [hs, read_len, B256.toNat_zero]
  refine ⟨by omega, ?_⟩
  rw [take_read_split _ _ _ (by omega), memRead_extend_fst,
    read_write_off wR (Or.inr (by omega)), memRead_extend_fst]
  have z := pq.zero
  rw [read_split M 0 64 (by omega)] at z
  have := congrArg (List.take 32) z
  rw [List.take_left' (read_len M 0 32), List.take_replicate] at this
  exact this

/-- **The `SignatureChecker` library rejects every Pair signer** (U7a, library side).  A successful
frame running the library runtime from a fresh machine, whose calldata's first argument word names
an account holding the Pair's runtime outside the precompile range, returns the ABI word `false`:
the signer has code, so the library asks it `isValidSignature` by `STATICCALL`, and the Pair answers
no such call.  Every free-pointer fact the walk uses is derived inside the frame (the library sets
`mstore(0x40, 0x80)` at pc 0 and bounds the signature length by `2 ^ 32` while decoding). -/
theorem lib_rejects_pair {sevm : Sevm} {b post : Devm} {G : Nat}
    (run : Exec 0 sevm (St b [] Mem.empty G) (.ok post))
    (code : sevm.code = Lib.code) (fork : CoveredFork sevm.benvStat.fork)
    (hcode : b.getCode (Sevm.dataWord sevm 4).toAdr = UniswapV2Pair.code)
    (notPrecompile : ¬ sevm.benvStat.rules.isPrecomp (Sevm.dataWord sevm 4).toAdr)
    (hsilent : NoStaticAnswer UniswapV2Pair.code 0x1626ba7e) :
    32 ≤ post.output.length ∧ post.output.take 32 = List.replicate 32 0 := by
  have h := lib_run_cut run code fork
  clear run
  unfold t_0000_c0 at h
  lx h
  laddr h
  lx h
  lx h
  lx h
  lx h
  lx h
  lx h
  lx h
  lx h
  ibranch h c0
  unfold t_0024_c0 at h
  iterate 8 lx h
  rcases ric_branchTo (by decide) rfl h with ⟨c1, _, h⟩ | ⟨c1, _, h⟩
  · exact (SFunc.RunCutP.false_of_noOk h (by decide)).elim
  ldest h
  iterate 10 lx h
  ibranch h c2
  ldest h
  iterate 25 lx h
  ibranch h c3
  ldest h
  iterate 9 lx h
  ibranch h c4
  ldest h
  iterate 9 lx h
  lmul h
  iterate 9 lx h
  ibranch h c5
  ldest h
  iterate 10 lx h
  lmul h
  iterate 24 lx h
  lcdc h
  iterate 18 lx h
  have hr0 : ((Mem.empty.write (Bytes.toB256 [64]).toNat (Bytes.toB256 [128]).toBytes).read
      (Bytes.toB256 [64]).toNat 32).1.toB256 = Bytes.toB256 [128] := by
    rw [Mem.read_write_word_of_wf Mem.wf_empty, B256.toB256_toBytes]
  rw [hr0] at h
  generalize hL : Sevm.dataWord sevm (Bytes.toB256 [4] + Sevm.dataWord sevm (Bytes.toB256 [4] +
    Bytes.toB256 [64])) = L at h c5
  generalize hF : Bytes.toB256 [128] + (Bytes.toB256 [32] + (Bytes.toB256 [31] + L) /
    Bytes.toB256 [32] * Bytes.toB256 [32]) = F at h
  have hL32 : L.toNat ≤ 2 ^ 32 := by
    have := le_of_gt_or_guard c5
    rwa [show (Bytes.toB256 [1, 0, 0, 0, 0]).toNat = 2 ^ 32 by decide] at this
  rw [lit64] at h hr0
  generalize hW : Mem.empty.write 64 (Bytes.toB256 [128]).toBytes = W0 at h hr0
  have wW : Mem.Wf W0 := by rw [← hW]; exact Mem.wf_empty.write _ _
  have pW : LibMem (Bytes.toB256 [128]) W0 := by
    refine ⟨wW, ?_, hr0⟩
    rw [← hW, read_write_off Mem.wf_empty (Or.inr (by omega))]
    decide
  have l128 : (Bytes.toB256 [128]).toNat = 128 := by decide
  have h160 : (Bytes.toB256 [32] + Bytes.toB256 [128]).toNat = 160 := by decide
  have hFL : (Bytes.toB256 [32] + Bytes.toB256 [128] + L).toNat = 160 + L.toNat := by
    rw [add_toNat_small (by rw [h160]; omega), h160]
  have ha : (Bytes.toB256 [31] + L).toNat = 31 + L.toNat := by
    rw [add_toNat_small (by rw [show (Bytes.toB256 [31]).toNat = 31 by decide]; omega),
      show (Bytes.toB256 [31]).toNat = 31 by decide]
  have hd : ((Bytes.toB256 [31] + L) / Bytes.toB256 [32]).toNat = (31 + L.toNat) / 32 := by
    rw [B256.toNat_div (by decide), ha, lit32]
  have hm : ((Bytes.toB256 [31] + L) / Bytes.toB256 [32] * Bytes.toB256 [32]).toNat =
      (31 + L.toNat) / 32 * 32 := by
    rw [B256.toNat_mul, hd, lit32]
    exact Nat.mod_eq_of_lt (by omega)
  have hs : (Bytes.toB256 [32] + (Bytes.toB256 [31] + L) / Bytes.toB256 [32] *
      Bytes.toB256 [32]).toNat = 32 + (31 + L.toNat) / 32 * 32 := by
    rw [add_toNat_small (by rw [lit32, hm]; omega), lit32, hm]
  have hFn : F.toNat = 160 + (31 + L.toNat) / 32 * 32 := by
    rw [← hF, add_toNat_small (by rw [l128, hs]; omega), l128, hs]
    omega
  generalize hM1 : ((((W0.read 64 32).2.write 64 F.toBytes).write (Bytes.toB256 [128]).toNat
      L.toBytes).write (Bytes.toB256 [32] + Bytes.toB256 [128]).toNat
      (List.sliceD sevm.data (Bytes.toB256 [32] + (Bytes.toB256 [4] + Sevm.dataWord sevm
        (Bytes.toB256 [4] + Bytes.toB256 [64]))).toNat L.toNat 0)).write
      (Bytes.toB256 [32] + Bytes.toB256 [128] + L).toNat (Bytes.toB256 [0]).toBytes = M1 at h
  have hp1 : LibMem F M1 := by
    rw [← hM1]
    refine (((pW.extend _ _).set F).write _ _ ?_ |>.write _ _ ?_).write _ _ ?_
    · rw [l128]; omega
    · rw [h160]; omega
    · rw [hFL]; omega
  have hlen : Bytes.toB256 (M1.read (Bytes.toB256 [128]).toNat 32).1 = L := by
    rw [← hM1, read_write_off (by wf_tac) (by rw [hFL, l128]; omega),
      read_write_off (by wf_tac) (by rw [h160, l128]; omega),
      Mem.read_write_word_of_wf (by wf_tac), B256.toB256_toBytes]
  have hcode' : b.getCode (Sevm.dataWord sevm (Bytes.toB256 [4]) &&& maskAddr).toAdr =
      UniswapV2Pair.code := by
    rw [and_mask_toAdr, show Bytes.toB256 [4] = (4 : B256) by decide]
    exact hcode
  have np' : ¬ sevm.benvStat.rules.isPrecomp (Sevm.dataWord sevm (Bytes.toB256 [4]) &&& maskAddr).toAdr := by
    rw [and_mask_toAdr, show Bytes.toB256 [4] = (4 : B256) by decide]
    exact notPrecompile
  have hFb : 128 ≤ F.toNat ∧ F.toNat < 2 ^ 40 := ⟨by omega, by omega⟩
  rcases ric_call rfl h with ⟨G1, ⟨D, hc, h⟩ | ⟨D, hc, -⟩⟩
  swap
  · obtain ⟨_, _, _, _, _, e⟩ := e6_inv fork hcode' np' hsilent hp1 hFb (by rw [l128]; omega) hlen hL32 hc
    cases e
  obtain ⟨b', q, M', G', pq, e⟩ := e6_inv fork hcode' np' hsilent hp1 hFb (by rw [l128]; omega) hlen hL32 hc
  cases e
  clear hc
  unfold t_0102_c13 at h
  ldest h
  iterate 16 lx h
  cases h with
  | last hl =>
    obtain ⟨hout, -, -⟩ := ri_return hl
    rw [hout, lit64, show B256.eqCheck (B256.eqCheck 0 0) 0 = (0 : B256) by decide, pq.ptr]
    exact final_output pq


end Blanc.Lift.Usdc
