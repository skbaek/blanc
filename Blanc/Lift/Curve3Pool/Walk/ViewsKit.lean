import Blanc.Lift.Curve3Pool.Walk.ViewsDispatch
import Blanc.Lift.Curve3Pool.Callee.A
import Blanc.Lift.Curve3Pool.Callee.GetDMem
import Blanc.Lift.FrameWalkNode
import Blanc.Lift.InvWalkCallNext
import Blanc.Lift.Curve3Pool.Walk.ViewsLoop
import Blanc.Lift.MemGlue

/-!
# The views' walking kit: `PC` on the derivation and bridged callees

* `xa_pcAt`: a `PC` step on the actual derivation pushes its own pc (the internal-call idiom
  `PUSH1 6; PC; ADD; PUSH2 callee; JUMP` pushes the return tag);
* `xa_calleeC`: crossing a certified exec-free callee (Bridge.lean's `xa_callee`) with the
  certificate's checkedness `hc : Cert.CheckedM code cert mems true` as a premise, so that walk
  files need not import `Check.lean`;
* `xa_vA`: `_A` (entry 27) crossed and read through its spec `a_spec`: the walk resumes at the
  return tag with the amplification `aChk s t` on the caller's stack, over `aBase`, the memory
  kept off `aWin`.
-/

namespace Blanc.Lift.Curve3Pool

open Jaune Blanc.Lift Blanc.StableSwapNewton

section

variable {sevm : Sevm} {post b : Devm} {L : List Exec.Frame} {S : List B256} {M : Mem}
  {G pc : Nat}

/-- **A `PC` step** on the actual derivation pushes its pc. -/
theorem xa_pcAt {pc' : Nat} (hat : Ninst.At sevm.code pc (.reg .pc)) (hpc : pc + 1 = pc')
    (h : XAt sevm post pc (St b S M G) L) :
    ∃ G', XAt sevm post pc' (St b (Nat.toB256 pc :: S) M G') L := by
  have hstep : Evm.step ⟨pc, sevm, St b S M G⟩ = Ninst.step ⟨pc, sevm, St b S M G⟩ (.reg .pc) :=
    Evm.step_next hat
  obtain ⟨exc, rfl, hg⟩ := h
  cases exc with
  | halt h => cases Ninst.step_ne_halt_ok (hstep.symm.trans h)
  | @cont _ _ _ _ d' _ h next =>
    have hs := hstep.symm.trans h
    cases Ninst.step_cont_pc hs
    have sr : Ninst.StepRun pc sevm (St b S M G) (.reg .pc) .none (.ok d') := by
      simp only [Ninst.StepRun, hs, Step.Run]
      exact ⟨trivial, trivial⟩
    have hp := Devm.pushBurn_of_pushItem (pushItem_of_stepRun_pc sr)
    have hst : _ := hp.stack
    simp only [Stack.Push, Split, St.stack, List.cons_append, List.nil_append] at hst
    have e := St.of_stackRel hp
    rw [hst] at e
    subst hpc
    have hx : XAt sevm post (pc + 1) d' _ := ⟨next, rfl, lt_trans (gas_cont h) hg⟩
    exact ⟨_, XAt.of_eq e hx⟩
  | doneOk h _ _ _ =>
    obtain ⟨x, hx, -⟩ := Ninst.step_spawn_inv (hstep.symm.trans h)
    cases hx
  | runOk h _ _ _ _ =>
    obtain ⟨x, hx, -⟩ := Ninst.step_spawn_inv (hstep.symm.trans h)
    cases hx

set_option hygiene false in
/-- A `PC` at the walk's pc, landing at `pc'`. -/
macro "xpc " pc:term:max : tactic => `(tactic| (
  replace h := xa_pcAt (pc' := $pc) (atN hcode (by kernel_rfl)) (by rfl) h
  obtain ⟨_, h⟩ := h))

/-- **Crossing a certified exec-free callee** (`xa_callee`, Bridge.lean), with the
certificate's checkedness as a premise. -/
theorem xa_calleeC (hc : Cert.CheckedM code cert mems true) {k : Nat} {e : Entry} {f : SFunc}
    {E : List Nat}
    (hk : cert.entries[k]? = some e) (hf : cert.prog[k]? = some f)
    (hm : mems.getD k [] = []) (hE : ExecFreeSet cert.prog E = true)
    (hfree : f.execFreeIn E = true)
    {sevm : Sevm} {post d : Devm} {ρ : B256} {S base : List B256} {L : List Exec.Frame}
    (hcode : sevm.code = code) (hfork : CoveredFork sevm.benvStat.fork)
    (hstack : d.stack = S ++ base) (hframe : FrameMatches ρ e.frame S)
    (h : XAt sevm post e.pc d L) :
    (SFunc.Run cert.prog sevm d f (.halted post) ∧ L = []) ∨
      ∃ (d' : Devm) (S' : List B256),
        SFunc.Run cert.prog sevm d f (.returned d') ∧ XAt sevm post ρ.toNat d' L ∧
        d'.stack = S' ++ base ∧ S'.length = e.rets := by
  have hcheck := hc k e f hk hf
  rw [hm] at hcheck
  exact xa_node_span hc hE hcode hfork hcheck hfree hstack hframe (memMatches_nil _ _) h

/-! ## `_A` -/

theorem vk_a_entry : cert.entries[27]? = some ⟨0xa9, [.ret], 1⟩ := rfl
theorem vk_a_mems : mems.getD 27 [] = [] := by decide
theorem vk_a_execFreeSet : ExecFreeSet cert.prog [27] = true := by decide
theorem vk_a_free : t_00a9_c27.execFreeIn [27] = true := by decide

/-- **`_A` crossed and read**: a walk at `_A`'s entry with the return tag `ρ` over `S` resumes
at `ρ` with `aChk s t` on `S`, over `aBase`, the memory kept off `aWin`, the same remaining
children. -/
theorem xa_vA (hc : Cert.CheckedM code cert mems true) {sevm : Sevm} {post b : Devm} {ρ : B256}
    {S : List B256} {M : Mem} {G : Nat} {L : List Exec.Frame} {s : State}
    (hcode : sevm.code = code) (hfork : CoveredFork sevm.benvStat.fork)
    (ha : Abstracts (b.getStor sevm.currentTarget) s) (hwf : Mem.Wf M)
    (h : XAt sevm post 0xa9 (St b (ρ :: S) M G) L) :
    ∃ v M' G', XAt sevm post ρ.toNat (St (aBase sevm b) (v :: S) M' G') L ∧
      aChk s sevm.benvStat.time.toNat = some v.toNat ∧ Mem.KeepsOff M M' aWin ∧ Mem.Wf M' ∧
      (M.size % 32 = 0 → M'.size % 32 = 0) := by
  rcases xa_calleeC hc vk_a_entry prog_27 vk_a_mems vk_a_execFreeSet vk_a_free hcode hfork
      (S := [ρ]) (base := S) rfl (List.Forall₂.cons rfl .nil) h with
    ⟨run, -⟩ | ⟨d', S', run, hx, -, -⟩
  · obtain ⟨d, he, -⟩ := a_spec hfork ha hwf run
    cases he
  · obtain ⟨d, he, v, M', G', rfl, hv, hk, hw, hal⟩ := a_spec hfork ha hwf run
    cases he
    exact ⟨v, M', G', hx, hv, hk, hw, hal⟩

end

/-! ## The word carrier -/

/-- The first carried word at offset `o`. -/
def wlook : List (Nat × B256) → Nat → Option B256
  | [], _ => none
  | (q, v) :: L, o => if q = o then some v else wlook L o

theorem wlook_mem : ∀ {L : List (Nat × B256)} {o : Nat} {v : B256}, wlook L o = some v →
    (o, v) ∈ L
  | [], _, _, h => by cases h
  | (q, w) :: L, o, v, h => by
    unfold wlook at h
    split at h
    · cases h; subst q; exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (wlook_mem h)

/-- **The views' memory carrier**: the words `L` carried, well formed, word-aligned size. -/
structure VW (M : Mem) (L : List (Nat × B256)) : Prop where
  words : Words M L
  wf : Mem.Wf M
  al : M.size % 32 = 0

/-- The carried words whose bytes miss every window of `W`. -/
def wordsOffW (W : List (Nat × Nat)) (L : List (Nat × B256)) : List (Nat × B256) :=
  L.filter fun p => W.all fun w => decide (p.1 + 32 ≤ w.1) || decide (w.2 ≤ p.1)

theorem VW.sub {M : Mem} {L L' : List (Nat × B256)} (h : VW M L) (hs : L' ⊆ L) : VW M L' :=
  ⟨h.words.sub hs, h.wf, h.al⟩

/-- Across a callee that kept memory off `W`: the words off `W` survive. -/
theorem VW.keepsOff {M M' : Mem} {L : List (Nat × B256)} {W : List (Nat × Nat)} (h : VW M L)
    (hk : Mem.KeepsOff M M' W) (hwf : Mem.Wf M') (hal : M'.size % 32 = 0) :
    VW M' (wordsOffW W L) := by
  refine ⟨(h.words.sub (List.filter_subset_self _)).keepsOff hk ?_, hwf, hal⟩
  intro o v hm j hj w hw
  have h' := List.all_eq_true.mp (List.mem_filter.mp hm).2 w hw
  simp only [Bool.or_eq_true, decide_eq_true_eq] at h'
  omega

/-- A word store: the word is carried, and so is every carried word it misses. -/
theorem VW.write {M : Mem} {L : List (Nat × B256)} (h : VW M L) (o : Nat) (v : B256) :
    VW (M.write o v.toBytes) ((o, v) :: wordsOff o L) := by
  refine ⟨(h.words.sub (L' := wordsOff o L) (List.filter_subset_self _)).write fun o' w hm => ?_,
    h.wf.write _ _, Mem.size_write_word_mod h.al⟩
  have h' := (List.mem_filter.mp hm).2
  simpa only [Bool.or_eq_true, decide_eq_true_eq] using h'

section

variable {sevm : Sevm} {b d : Devm} {S : List B256} {M : Mem} {G : Nat} {L : List (Nat × B256)}

/-- `MLOAD` of a carried word. -/
theorem ri_mloadV {i v : B256} {o : Nat} (hV : VW M L) (hl : wlook L o = some v)
    (ho : i.toNat = o) (h : Ninst.Run sevm (St b (i :: S) M G) (.reg .mload) d) :
    ∃ G', d = St b (v :: S) M G' := by
  obtain ⟨G', rfl⟩ := ri_mload h
  obtain ⟨hv, hM⟩ := hV.words.read hV.al (wlook_mem hl)
  rw [ho, hv, hM]
  exact ⟨G', rfl⟩

/-- `MLOAD` of an uncarried word: some word, the memory possibly grown. -/
theorem ri_mloadU {i : B256} (hV : VW M L)
    (h : Ninst.Run sevm (St b (i :: S) M G) (.reg .mload) d) :
    ∃ v M' G', d = St b (v :: S) M' G' ∧ VW M' L := by
  obtain ⟨G', rfl⟩ := ri_mload h
  have hk := Mem.KeepsOff.extend M i.toNat 32 []
  refine ⟨_, _, G', rfl, ⟨fun o v hm => ?_, hV.wf.extend _ _, Mem.size_extend_mod _ _ hV.al⟩⟩
  obtain ⟨hs, hv⟩ := hV.words o v hm
  exact ⟨le_trans hs hk.1, hv⟩

/-- `MSTORE` at a literal offset. -/
theorem ri_mstoreV {i v : B256} {o : Nat} (hV : VW M L) (ho : i.toNat = o)
    (h : Ninst.Run sevm (St b (i :: v :: S) M G) (.reg .mstore) d) :
    ∃ G', d = St b S (M.write o v.toBytes) G' ∧ VW (M.write o v.toBytes) ((o, v) :: wordsOff o L) := by
  obtain ⟨G', rfl⟩ := ri_mstore h
  rw [ho]
  exact ⟨G', rfl, hV.write o v⟩

end

/-! ## The frame loops over the carrier -/

theorem saveMem_wf {M : Mem} (hwf : Mem.Wf M) (c lo : Nat) : ∀ n, Mem.Wf (saveMem M c lo n)
  | 0 => hwf
  | n + 1 => (saveMem_wf hwf c lo n).write _ _

theorem restoreMem_wf {c : Nat} : ∀ {M : Mem} {p : Nat} (ws : List B256), Mem.Wf M →
    Mem.Wf (restoreMem c M p ws)
  | _, _, [], h => h
  | _, _, _ :: ws, h => restoreMem_wf ws ((h.write _ _).write _ _)

/-- Across a save loop: the counter word and every carried word off it. -/
theorem VW.saveMem {M : Mem} {L : List (Nat × B256)} {c lo : Nat} (h : VW M L)
    (hctr : memWord M c = Nat.toB256 lo) (hcs : c + 32 ≤ M.size) (n : Nat) :
    VW (saveMem M c lo n) ((c, Nat.toB256 (lo + 32 * n)) :: wordsOff c L) := by
  refine ⟨Words.cons.mpr ⟨⟨by rw [saveMem_size hcs]; exact hcs, saveMem_ctr hctr n⟩, ?_⟩,
    saveMem_wf h.wf c lo n, by rw [saveMem_size hcs]; exact h.al⟩
  refine (h.words.sub (List.filter_subset_self _)).saveMem (fun o v hm => ?_) n
  have h' := (List.mem_filter.mp hm).2
  simpa only [Bool.or_eq_true, decide_eq_true_eq] using h'

/-- The carried words off the half-open range `[lo, hi)`. -/
def wordsOffR (lo hi : Nat) (L : List (Nat × B256)) : List (Nat × B256) :=
  L.filter fun p => decide (p.1 + 32 ≤ lo) || decide (hi ≤ p.1)

/-- Across a restore loop from the counter value `p`: every carried word below the restored
range or above the counter. -/
theorem VW.restoreMem {M : Mem} {L : List (Nat × B256)} {c p : Nat} {ws : List B256}
    (h : VW M L) (hcs : c + 32 ≤ M.size) (hp : p + 32 ≤ c) :
    VW (restoreMem c M p ws) (wordsOffR (p + 32 - 32 * ws.length) (c + 32) L) := by
  refine ⟨(h.words.sub (List.filter_subset_self _)).restoreMem hp (fun o v hm => ?_),
    restoreMem_wf ws h.wf, by rw [restoreMem_size ws hcs (by omega)]; exact h.al⟩
  have h' := (List.mem_filter.mp hm).2
  simpa only [Bool.or_eq_true, decide_eq_true_eq] using h'

/-! ## A `STATICCALL` over the carrier -/

theorem memExtsSize_mod : ∀ {s : Nat} (ps : List (Nat × Nat)), s % 32 = 0 →
    memExtsSize s ps % 32 = 0
  | _, [], h => h
  | _, (_, _) :: ps, h => memExtsSize_mod ps (memExtSize_mod_32 h)

theorem VW.extends {M : Mem} {L : List (Nat × B256)} (h : VW M L) (ps : List (Nat × Nat)) :
    VW (M.extends ps) L :=
  ⟨fun o v hm => ⟨le_trans (h.words o v hm).1 (memExtsSize_ge _ _), (h.words o v hm).2⟩,
    Mem.Wf.extends _ h.wf, memExtsSize_mod ps h.al⟩

/-- A 32-byte (or longer) answer laid at `o` is carried as its first word. -/
theorem VW.writeOut {M : Mem} {L : List (Nat × B256)} (h : VW M L) (o : Nat) {out : Bytes}
    (hl : 32 ≤ out.length) :
    VW (M.write o (out.take 32)) ((o, Bytes.toB256 (out.take 32)) :: wordsOff o L) := by
  have hlen : (out.take 32).length = 32 := by rw [List.length_take]; omega
  have e := Bytes.toBytes_toB256_of_length hlen
  have h' := h.write o (Bytes.toB256 (out.take 32))
  rwa [e] at h'

section

variable {sevm : Sevm} {post b : Devm} {L : List Exec.Frame} {S : List B256} {M : Mem}
  {G pc : Nat} {LW : List (Nat × B256)}

/-- **A `STATICCALL` over the carrier**, with a one-word output window at `o`: the flag and
returned data `out`; a reply of at least a word is carried at `o`; storage and logs kept; on a
nonzero flag, a precompile target and no child, or the next remaining child is the call's. -/
theorem xa_staticcallV {pc' : Nat} {g t ii is oi os : B256} {o : Nat}
    (hfork : CoveredFork sevm.benvStat.fork) (hat : Ninst.At sevm.code pc (.exec .staticcall))
    (hpc : pc + 1 = pc') (hoi : oi.toNat = o) (hos : os.toNat = 32) (hV : VW M LW)
    (h : XAt sevm post pc (St b (g :: t :: ii :: is :: oi :: os :: S) M G) L) :
    ∃ d flag out M' L', XAt sevm post pc' (St d (flag :: S) M' d.gasLeft) L' ∧
      (32 ≤ out.length → VW M' ((o, Bytes.toB256 (out.take 32)) :: wordsOff o LW)) ∧
      d.returnData = out ∧ out.length < 2 ^ 256 ∧ (∀ a, d.getStor a = b.getStor a) ∧
      d.logs = b.logs ∧
      (flag ≠ 0 →
        (sevm.benvStat.rules.isPrecomp t.toAdr ∧ L = L') ∨
        (∃ c, L = c :: L' ∧ 0 < sevm.depth ∧ d.output = b.output ∧ Devm.AccGrow b d ∧
          (∀ a, b.getCode a ≠ .empty → d.getCode a = b.getCode a) ∧
          c.sevm.currentTarget = t.toAdr ∧ c.sevm.data = (M.read ii.toNat is.toNat).1 ∧
          c.sevm.isStatic = true ∧ c.post.output = out ∧ c.post.logs = [] ∧
          (∀ a, c.pre.getCode a = b.getCode a) ∧ (∀ a, d.getCode a = c.post.getCode a))) := by
  subst hpc hoi
  obtain ⟨d, s, L', h, hk⟩ := xa_staticcall hfork hat rfl h
  obtain ⟨flag, out, hpost, hbound, -⟩ := ri_staticcall_bounded hfork s
  refine ⟨d, flag, out, _, L', hpost.eq_St ▸ h, fun hl => ?_, hpost.returnData,
    hbound, hpost.stor, hpost.logs, fun nz => ?_⟩
  · rw [hos]
    exact (hV.extends _).writeOut _ hl
  rcases hk flag S hpost.stack nz with hp | ⟨c, hL, hdep, -, hc⟩
  · exact .inl hp
  · refine .inr ⟨c, hL, hdep, hc.outputKeep, hc.warm, hc.code, hc.target, hc.data, hc.isStatic,
      hc.output.trans hpost.returnData, ?_, hc.codePre, hc.codePost⟩
    have e := hc.logs
    rw [hpost.logs] at e
    have e2 : b.logs ++ c.post.logs = b.logs := e.symm
    exact List.append_right_eq_self.mp e2

end

/-! ## Bridged callees over the carrier -/

section

variable {sevm : Sevm} {post b : Devm} {ρ : B256} {S : List B256} {M : Mem} {G : Nat}
  {L : List Exec.Frame} {LW : List (Nat × B256)} {s : State}

/-- `_A` over the carrier. -/
theorem xa_vAV (hc : Cert.CheckedM code cert mems true)
    (hcode : sevm.code = code) (hfork : CoveredFork sevm.benvStat.fork)
    (ha : Abstracts (b.getStor sevm.currentTarget) s) (hV : VW M LW)
    (h : XAt sevm post 0xa9 (St b (ρ :: S) M G) L) :
    ∃ v b' M' G', SloadsOnly sevm b b' ∧ XAt sevm post ρ.toNat (St b' (v :: S) M' G') L ∧
      aChk s sevm.benvStat.time.toNat = some v.toNat ∧ VW M' (wordsOffW aWin LW) := by
  obtain ⟨v, M', G', hx, hv, hk, hw, hal⟩ := xa_vA hc hcode hfork ha hV.wf h
  exact ⟨v, _, M', G', aBase_sloadsOnly sevm b, hx, hv, hV.keepsOff hk hw (hal hV.al)⟩

theorem vk_xp_entry : cert.entries[31]? = some ⟨0x281, [.ret], 3⟩ := rfl
theorem vk_xp_prog : cert.prog[31]? = some t_0281_c31 := by decide +kernel
theorem vk_xp_mems : mems.getD 31 [] = [] := by decide
theorem vk_xp_free : t_0281_c31.execFreeIn [31, 56, 83, 105, 126, 148, 170] = true := by
  decide +kernel

/-- **`_xp` crossed and read** over the carrier: the words of `xpChk s.balances` (coin 0 on
top) on `S`, over a base of storage loads, the words off `xpWin` kept. -/
theorem xa_vXp (hc : Cert.CheckedM code cert mems true)
    (hcode : sevm.code = code) (hfork : CoveredFork sevm.benvStat.fork)
    (ha : Abstracts (b.getStor sevm.currentTarget) s) (hV : VW M LW)
    (h : XAt sevm post 0x281 (St b (ρ :: S) M G) L) :
    ∃ x0 x1 x2 b' M' G', SloadsOnly sevm b b' ∧
      XAt sevm post ρ.toNat (St b' (x0 :: x1 :: x2 :: S) M' G') L ∧
      xpChk s.balances = some ⟨x0.toNat, x1.toNat, x2.toNat⟩ ∧ VW M' (wordsOffW xpWin LW) := by
  rcases xa_calleeC hc vk_xp_entry vk_xp_prog vk_xp_mems xp_execFreeSet vk_xp_free hcode hfork
      (S := [ρ]) (base := S) rfl (List.Forall₂.cons rfl .nil) h with
    ⟨run, -⟩ | ⟨d', S', run, hx, -, -⟩
  · obtain ⟨d, he, -⟩ := xp_spec hfork ha hV.wf run
    cases he
  · obtain ⟨d, he, x0, x1, x2, M', G', rfl, hv, hk, hw, hal⟩ := xp_spec hfork ha hV.wf run
    cases he
    exact ⟨x0, x1, x2, _, M', G', xpBase_sloadsOnly sevm b, hx, hv, hV.keepsOff hk hw (hal hV.al)⟩

theorem vk_gd_entry : cert.entries[417]? = some ⟨0x4c9, [.ret, .unk, .unk, .unk, .unk], 1⟩ := by
  rfl
theorem vk_gd_prog : cert.prog[417]? = some t_04c9_c417 := by decide +kernel
theorem vk_gd_mems : mems.getD 417 [] = [] := by decide +kernel

/-- **`get_D` crossed and read** over the carrier (memory covering `[0, 0x340)`): `D` with
`getDChk x amp 1 = some D` on `S`, the base unchanged, the words off its windows kept and `D`
at the scratch word `0`. -/
theorem xa_vGetD (hc : Cert.CheckedM code cert mems true)
    (hcode : sevm.code = code) (hfork : CoveredFork sevm.benvStat.fork) {x0 x1 x2 amp : B256}
    (hV : VW M LW) (hcov : 0x340 ≤ M.size)
    (h : XAt sevm post 0x4c9 (St b (ρ :: x0 :: x1 :: x2 :: amp :: S) M G) L) :
    ∃ v M' G', XAt sevm post ρ.toNat (St b (v :: S) M' G') L ∧
      getDChk (V3.mk x0.toNat x1.toNat x2.toNat).get amp.toNat 1 = some v.toNat ∧
      M'.size = M.size ∧
      VW M' ((0, v) :: wordsOffW [(0, 32), (0x140, 0x340)] LW) := by
  rcases xa_calleeC hc vk_gd_entry vk_gd_prog vk_gd_mems gd_execFreeSet gd_free hcode hfork
      (S := [ρ, x0, x1, x2, amp]) (base := S) rfl
      (.cons rfl (.cons trivial (.cons trivial (.cons trivial (.cons trivial .nil))))) h with
    ⟨run, -⟩ | ⟨d', S', run, hx, -, -⟩
  · obtain ⟨d, he, -⟩ := getD_spec hV.al hcov run
    cases he
  · obtain ⟨d, he, v, M', G', rfl, hv, hsz, hw0, hk⟩ := getD_spec hV.al hcov run
    cases he
    obtain ⟨hk, hwf⟩ := hk hV.wf
    have hV' := hV.keepsOff hk hwf (by rw [hsz]; exact hV.al)
    exact ⟨v, M', G', hx, hv, hsz, ⟨Words.cons.mpr ⟨hw0 0 v List.mem_cons_self, hV'.words⟩,
      hwf, hV'.al⟩⟩

end

set_option hygiene false in
/-- Normalize the carrier's word list to an explicit list. -/
macro "vnorm" : tactic => `(tactic| (try simp (config := {decide := true}) only [wordsOff,
  wordsOffW, wordsOffR, FrameLoopTpl.c, List.filter_cons, List.filter_nil, List.all_cons,
  List.all_nil, ↓reduceIte] at hV))

set_option hygiene false in
/-- `MLOAD` of a carried word at the walk's pc, landing at `pc'` (carrier `hV`). -/
macro "xl " pc:term:max o:term:max : tactic => `(tactic| (
  replace h := xa_nextAt (n := .reg .mload) (pc' := $pc) (atN hcode (by kernel_rfl)) (by nofun)
    (by rfl) h
  obtain ⟨_, s, h⟩ := h
  obtain ⟨_, rfl⟩ := ri_mloadV (o := $o) hV (by rfl) (by rfl) s
  clear s))

set_option hygiene false in
/-- `SHA3` of a carried word at a literal offset (length `32`). -/
macro "xk " pc:term:max o:term:max : tactic => `(tactic| (
  replace h := xa_nextAt (n := .reg .keccak256) (pc' := $pc) (atN hcode (by kernel_rfl))
    (by nofun) (by rfl) h
  obtain ⟨_, s, h⟩ := h
  obtain ⟨_, rfl⟩ := ri_keccakV (o := $o) hV (by rfl) (by rfl) (by rfl) s
  clear s))

set_option hygiene false in
/-- `MLOAD` of an uncarried word. -/
macro "xlu " pc:term:max : tactic => `(tactic| (
  replace h := xa_nextAt (n := .reg .mload) (pc' := $pc) (atN hcode (by kernel_rfl)) (by nofun)
    (by rfl) h
  obtain ⟨_, s, h⟩ := h
  have e := ri_mloadU hV s
  clear s hV
  obtain ⟨_, _, _, rfl, hV⟩ := e))

set_option hygiene false in
/-- `MSTORE` at a literal offset (carrier `hV`). -/
macro "xsw " pc:term:max o:term:max : tactic => `(tactic| (
  replace h := xa_nextAt (n := .reg .mstore) (pc' := $pc) (atN hcode (by kernel_rfl)) (by nofun)
    (by rfl) h
  obtain ⟨_, s, h⟩ := h
  have e := ri_mstoreV (o := $o) hV (by rfl) s
  clear s hV
  obtain ⟨_, rfl, hV⟩ := e
  vnorm))

set_option hygiene false in
/-- The save loop's `SaveAt` facts at a concrete head, decoded from the code tries. -/
macro "vsave" : term => `(⟨atJ hcode (by kernel_rfl), atN hcode (by kernel_rfl),
  atN hcode (by kernel_rfl), atN hcode (by kernel_rfl), atN hcode (by kernel_rfl),
  atN hcode (by kernel_rfl), atN hcode (by kernel_rfl), atN hcode (by kernel_rfl),
  atN hcode (by kernel_rfl), atN hcode (by kernel_rfl), atN hcode (by kernel_rfl),
  atN hcode (by kernel_rfl), atN hcode (by kernel_rfl), atN hcode (by kernel_rfl),
  atN hcode (by kernel_rfl), atN hcode (by kernel_rfl), atJ hcode (by kernel_rfl),
  atN hcode (by kernel_rfl), atJ hcode (by kernel_rfl), atJ hcode (by kernel_rfl), by decide⟩)

set_option hygiene false in
/-- The restore loop's `RestoreAt` facts at a concrete head. -/
macro "vrestore" : term => `(⟨atJ hcode (by kernel_rfl), atN hcode (by kernel_rfl),
  atN hcode (by kernel_rfl), atN hcode (by kernel_rfl), atN hcode (by kernel_rfl),
  atN hcode (by kernel_rfl), atN hcode (by kernel_rfl), atN hcode (by kernel_rfl),
  atN hcode (by kernel_rfl), atN hcode (by kernel_rfl), atN hcode (by kernel_rfl),
  atN hcode (by kernel_rfl), atN hcode (by kernel_rfl), atN hcode (by kernel_rfl),
  atN hcode (by kernel_rfl), atN hcode (by kernel_rfl), atN hcode (by kernel_rfl),
  atJ hcode (by kernel_rfl), atN hcode (by kernel_rfl), atJ hcode (by kernel_rfl),
  atJ hcode (by kernel_rfl), by decide⟩)

/-- A carried counter word. -/
theorem VW.ctr {M : Mem} {L : List (Nat × B256)} (h : VW M L) {c lo : Nat} {w : B256}
    (hl : wlook L c = some w) (hw : w = Nat.toB256 lo) :
    memWord M c = Nat.toB256 lo ∧ c + 32 ≤ M.size :=
  ⟨(h.words.memWord (wlook_mem hl)).trans hw, (h.words c w (wlook_mem hl)).1⟩

section

variable {sevm : Sevm} {post b : Devm} {L : List Exec.Frame} {S : List B256} {M : Mem}
  {G H : Nat} {t : FrameLoopTpl} {LW : List (Nat × B256)}

/-- **A save loop over the carrier**: the `n` frame words pushed (`ws`), the counter carried. -/
theorem xa_saveV (hat : SaveAt sevm.code H t) {lo n : Nat} (hn : 0 < n) (hV : VW M LW)
    {w : B256} (hl : wlook LW t.c = some w) (hw : w = Nat.toB256 lo) (he : t.e = lo + 32 * n)
    (hreg : lo + 32 * n ≤ t.c) (h : XAt sevm post H (St b S M G) L) :
    ∃ ws M' G', ws.length = n ∧ ws = (frameWords M lo n).reverse ∧
      XAt sevm post (t.x + 1) (St b (ws ++ S) M' G') L ∧
      VW M' ((t.c, Nat.toB256 (lo + 32 * n)) :: wordsOff t.c LW) := by
  obtain ⟨hctr, hcs⟩ := hV.ctr hl hw
  obtain ⟨G', h⟩ := xa_frameSave hat hn hV.al hcs hctr he hreg h
  exact ⟨_, _, G', by rw [List.length_reverse, length_frameWords], rfl, h,
    hV.saveMem hctr hcs n⟩

/-- **A restore loop over the carrier**: the words `ts` written down from the top slot; the
carried words below `lo` or above the counter kept. -/
theorem xa_restoreV (hat : RestoreAt sevm.code H t) {lo : Nat} {ts : List B256} (hne : ts ≠ [])
    (hlo : 32 ≤ lo) (he : t.e = lo) (hV : VW M LW)
    {w : B256} (hl : wlook LW t.c = some w) (hw : w = Nat.toB256 (lo + 32 * (ts.length - 1)))
    (hreg : lo + 32 * ts.length ≤ t.c) (h : XAt sevm post H (St b (ts ++ S) M G) L) :
    ∃ M' G', XAt sevm post (t.x + 1) (St b S M' G') L ∧
      M' = restoreMem t.c M (lo + 32 * (ts.length - 1)) ts ∧
      VW M' (wordsOffR lo (t.c + 32) LW) := by
  obtain ⟨hctr, hcs⟩ := hV.ctr hl hw
  obtain ⟨G', h⟩ := xa_frameRestore hat hne hlo he hV.al hcs hreg hctr h
  have hlen : 0 < ts.length := List.length_pos_iff.mpr hne
  have hV' := hV.restoreMem (ws := ts) hcs (p := lo + 32 * (ts.length - 1)) (by omega)
  rw [show lo + 32 * (ts.length - 1) + 32 - 32 * ts.length = lo by omega] at hV'
  exact ⟨_, G', h, rfl, hV'⟩

end

/-! ## More carrier steps and callees -/

section

variable {sevm : Sevm} {post b d : Devm} {ρ : B256} {S : List B256} {M : Mem} {G : Nat}
  {L : List Exec.Frame} {LW : List (Nat × B256)}

/-- `SHA3` of one carried word. -/
theorem ri_keccakV {i n w : B256} {o : Nat} (hV : VW M LW) (hl : wlook LW o = some w)
    (ho : i.toNat = o) (hn : n.toNat = 32)
    (h : Ninst.Run sevm (St b (i :: n :: S) M G) (.reg .keccak256) d) :
    ∃ G', d = St b (Bytes.keccak w.toBytes :: S) M G' := by
  obtain ⟨G', rfl⟩ := ri_keccak h
  obtain ⟨hv, hM⟩ := hV.words.read hV.al (wlook_mem hl)
  have hlen : (M.read o 32).1.length = 32 := by
    simp only [Mem.read, Array.sliceD_eq_map, List.length_map, List.length_range]
  rw [ho, hn, hM, ← Bytes.toBytes_toB256_of_length hlen, hv]
  exact ⟨G', rfl⟩

theorem vk_gdm_entry : cert.entries[29]? = some ⟨0x7b7, [.ret, .unk, .unk, .unk, .unk], 1⟩ := by
  rfl
theorem vk_gdm_mems : mems.getD 29 [] = [] := by decide +kernel

/-- **`get_D_mem` crossed and read** over the carrier: `getDMem b amp` on `S`, the base
unchanged, the words off `gdmWin` kept and the result at the scratch word `0`. -/
theorem xa_vGetDMem (hc : Cert.CheckedM code cert mems true)
    (hcode : sevm.code = code) (hfork : CoveredFork sevm.benvStat.fork) {b0 b1 b2 amp : B256}
    (hV : VW M LW)
    (h : XAt sevm post 0x7b7 (St b (ρ :: b0 :: b1 :: b2 :: amp :: S) M G) L) :
    ∃ v M' G', XAt sevm post ρ.toNat (St b (v :: S) M' G') L ∧
      getDMem ⟨b0.toNat, b1.toNat, b2.toNat⟩ amp.toNat = some v.toNat ∧
      VW M' ((0, v) :: wordsOffW gdmWin LW) := by
  rcases xa_calleeC hc vk_gdm_entry t_07b7_c29_prog vk_gdm_mems gdm_execFreeSet gdm_free hcode
      hfork (S := [ρ, b0, b1, b2, amp]) (base := S) rfl
      (.cons rfl (.cons trivial (.cons trivial (.cons trivial (.cons trivial .nil))))) h with
    ⟨run, -⟩ | ⟨d', S', run, hx, -, -⟩
  · obtain ⟨d, he, -⟩ := getDMem_spec hV.wf hV.al run
    cases he
  · obtain ⟨d, he, v, M', G', rfl, hv, hk, hw0, hwf, hal⟩ := getDMem_spec hV.wf hV.al run
    cases he
    have hV' := hV.keepsOff hk hwf hal
    exact ⟨v, M', G', hx, hv, ⟨Words.cons.mpr ⟨hw0 0 v List.mem_cons_self, hV'.words⟩, hwf,
      hal⟩⟩

end

section

variable {sevm : Sevm} {post b : Devm} {L : List Exec.Frame} {S : List B256} {M : Mem}
  {G H : Nat} {t : FrameLoopTpl} {LW : List (Nat × B256)}

/-- **A restore loop giving back a saved frame**: the stack words were pushed by a save of the
frame `[lo, lo + 32 n)` of `W`, whose carried words `LF` (aligned in the frame) come back. -/
theorem xa_restoreFrameV (hat : RestoreAt sevm.code H t) {lo n : Nat} {W : Mem}
    {LF : List (Nat × B256)} (hn : 0 < n) (hlo : 32 ≤ lo) (he : t.e = lo) (hV : VW M LW)
    {w : B256} (hl : wlook LW t.c = some w) (hw : w = Nat.toB256 (lo + 32 * (n - 1)))
    (hreg : lo + 32 * n ≤ t.c) (hF : Words W LF)
    (hal : ∀ o v, (o, v) ∈ LF → ∃ i, i < n ∧ o = lo + 32 * i)
    (h : XAt sevm post H (St b ((frameWords W lo n).reverse ++ S) M G) L) :
    ∃ M' G', XAt sevm post (t.x + 1) (St b S M' G') L ∧
      VW M' (LF ++ wordsOffR lo (t.c + 32) LW) := by
  have hlen : ((frameWords W lo n).reverse).length = n := by
    rw [List.length_reverse, length_frameWords]
  have hne : (frameWords W lo n).reverse ≠ [] := by
    intro e; rw [e] at hlen; simp only [List.length_nil] at hlen; omega
  obtain ⟨hctr, hcs⟩ := hV.ctr hl (by rw [hw])
  obtain ⟨M', G', h', rfl, hV'⟩ := xa_restoreV hat hne hlo he hV hl (by rw [hlen, hw])
    (by rw [hlen]; exact hreg) h
  refine ⟨_, G', h', Words.append.mpr ⟨fun o v hm => ?_, hV'.words⟩, hV'.wf, hV'.al⟩
  have hfr := restoreMem_frameWords (c := t.c) (M := M) (W := W) (lo := lo) (n := n) hcs hreg
  obtain ⟨i, hi, rfl⟩ := hal o v hm
  have hmem : (lo + 32 * i, memWord W (lo + 32 * i)) ∈ frameSlots W lo n := by
    simp only [frameSlots, List.mem_map, List.mem_range, Prod.mk.injEq]
    exact ⟨i, hi, rfl, rfl⟩
  rw [hlen] at *
  obtain ⟨hs, hv⟩ := hfr _ _ hmem
  exact ⟨hs, hv.trans (hF.memWord hm)⟩

end

end Blanc.Lift.Curve3Pool
