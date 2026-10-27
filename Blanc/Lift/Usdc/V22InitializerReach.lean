import Blanc.Lift.Usdc.V22TransferFromCallee
import Blanc.Lift.Usdc.V22BlacklistReach
import Blanc.Lift.FrameSkip

/-! Original inherited initializeV2_1 stores in V2.2, with their actual hash inputs. -/
namespace Blanc.Lift.Usdc.V22InitializerReach
open Jaune Blanc Blanc.Lift
variable {observe : Conf → Conf → Prop}

def BlacklistSource (Q : Sevm → Devm → Ninst → Devm → Prop)
    (observe : Conf → Conf → Prop) (sevm : Sevm) (T : Conf) : Prop :=
  (∃ value rest, T.d.stack = mapSlot sevm.currentTarget.toB256 9 :: value :: 1 :: rest) ∧
    ObservedKeccak Q observe sevm
      (sevm.currentTarget.toB256.toBytes ++ (9 : B256).toBytes) (fun _ => True)

/-- The actual blacklist call sets flag1 and preserves that flag at its packed store. -/
theorem blacklist_source {Q : Sevm → Devm → Ninst → Devm → Prop}
    (erase : ∀ {s d n d'}, Q s d n d' → Ninst.Run s d n d')
    {sevm : Sevm} {b : Devm} {tag : B256} {S : List B256} {M : Mem} {G : Nat}
    {T : Conf}
    (run : ObservedReach Q observe Impl.cert.prog sevm
      ⟨St b (sevm.currentTarget.toB256 :: tag :: S) M G, Impl.t_4224_c86, []⟩ T)
    (hT : AtSstore T) : BlacklistSource Q observe sevm T := by
  unfold Impl.t_4224_c86 at run
  orsd
  iterate 4 orsx
  obtain ⟨g, _, hg, run⟩ := ObservedReach.rs_callIn run hT
  rw [show Impl.cert.prog[109]? = some Impl.t_4cc7_c109 from rfl] at hg
  cases hg
  unfold Impl.t_4cc7_c109 at run
  orsd
  iterate 2 orsx
  rcases ObservedReach.rs_branch run hT with ⟨wrong, _, run⟩ | ⟨-, _, run⟩
  · exact ((by decide : Bytes.toB256 [1] ≠ 0) wrong).elim
  unfold Impl.t_4cda_c109 at run
  orsd
  iterate 13 orsx
  orsld
  iterate 2 orsx
  obtain ⟨stack, hash⟩ := V22BlacklistReach.store_source erase run hT
    (by intro f member; have same := List.mem_singleton.mp member; subst f; decide +kernel)
  exact ⟨⟨_, _, stack⟩, hash⟩

/-- Once the blacklist call returns, the only remaining store is version slot18. -/
theorem version_source {Q : Sevm → Devm → Ninst → Devm → Prop}
    (erase : ∀ {s d n d'}, Q s d n d' → Ninst.Run s d n d')
    {sevm : Sevm} {b : Devm} {x y : B256} {S : List B256} {M : Mem} {G : Nat}
    {K : List SFunc} {T : Conf}
    (run : ObservedReach Q observe Impl.cert.prog sevm
      ⟨St b (x :: y :: S) M G, Impl.t_188c_c64, K⟩ T)
    (hT : AtSstore T) (cont : ∀ f ∈ K, f.sstoreFreeIn [] = true) :
    ∃ rest, T.d.stack = 18 :: rest := by
  unfold Impl.t_188c_c64 at run
  orsd
  iterate 4 orsx
  orsld
  iterate 5 orsx
  rcases ObservedReach.sstoreS run with rfl | ⟨d', step, _, run⟩
  · exact ⟨_, rfl⟩
  exact (Reach.false_of_sstoreFree (E := []) rfl run.forget hT (by decide +kernel) cont).elim

/-- Split the actual blacklist callee and recover its saved caller stack on return. -/
theorem after_source {Q : Sevm → Devm → Ninst → Devm → Prop}
    (erase : ∀ {s d n d'}, Q s d n d' → Ninst.Run s d n d')
    {sevm : Sevm} {b : Devm} {x y : B256} {S : List B256} {M : Mem} {G : Nat}
    {K : List SFunc} {T : Conf} (hsg : sevm.benvStat.rules.stateGas = none)
    (run : ObservedReach Q observe Impl.cert.prog sevm
      ⟨St b (x :: y :: S) M G, Impl.t_1883_c64, K⟩ T)
    (hT : AtSstore T) (cont : ∀ f ∈ K, f.sstoreFreeIn [] = true) :
    (∃ rest, T.d.stack = 18 :: rest) ∨ BlacklistSource Q observe sevm T := by
  unfold Impl.t_1883_c64 at run
  orsd
  iterate 3 orsx
  obtain ⟨g, _, hg, run⟩ := ObservedReach.rs_callIn run hT
  rw [show Impl.cert.prog[86]? = some Impl.t_4224_c86 from rfl] at hg
  cases hg
  rcases ObservedReach.split run (S := []) rfl with
    ⟨target, inside, same⟩ | ⟨returned, callee, _, later⟩
  · have atStore : AtSstore target := by rw [same] at hT; exact hT
    obtain ⟨stack, hash⟩ := blacklist_source erase inside atStore
    rw [same]
    exact .inr ⟨stack, hash.below (Impl.t_188c_c64 :: K)⟩
  obtain ⟨Y, stack, length⟩ := callee.entry_stack_below_noStateGas erase Impl.cert_check hsg
    (k := 86) (ρ := 0x188c) (X := [sevm.currentTarget.toB256, 0x188c])
    (R := x :: y :: S)
    (show Impl.cert.entries[86]? = some ⟨0x4224, [.unk, .ret], 0⟩ from rfl)
    (show Impl.cert.prog[86]? = some Impl.t_4224_c86 from rfl) rfl
    (by exact .cons trivial (.cons rfl .nil))
  have empty : Y = [] := by
    cases Y with
    | nil => rfl
    | cons head tail => simp only [List.length_cons] at length; omega
  simp only [empty, List.nil_append] at stack
  rw [St.self stack rfl] at later
  exact .inl (version_source erase later hT cont)

/-- The optional original transfer returns into the packed blacklist/version suffix. -/
theorem body_source {Q : Sevm → Devm → Ninst → Devm → Prop}
    (erase : ∀ {s d n d'}, Q s d n d' → Ninst.Run s d n d')
    {sevm : Sevm} {recipient : Adr} {b : Devm} {tag : B256}
    {S : List B256} {M : Mem} {G : Nat} {K : List SFunc} {T : Conf}
    (hsg : sevm.benvStat.rules.stateGas = none)
    (run : ObservedReach Q observe Impl.cert.prog sevm
      ⟨St b (recipient.toB256 :: tag :: S) M G, Impl.t_1853_c64, K⟩ T)
    (hT : AtSstore T) (cont : ∀ f ∈ K, f.sstoreFreeIn [] = true) :
    V22TransferReach.ObservedSource Q observe sevm sevm.currentTarget recipient T ∨
      (∃ rest, T.d.stack = 18 :: rest) ∨ BlacklistSource Q observe sevm T := by
  unfold Impl.t_1853_c64 at run
  orsd
  orsx
  orsld
  iterate 5 orsx
  rcases ObservedReach.rs_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
  · exact (Reach.false_of_sstoreFree (E := []) rfl run.forget hT (by decide +kernel) cont).elim
  unfold Impl.t_1865_c64 at run
  orsd
  iterate 4 orsx
  obtain ⟨g, _, hg, run⟩ := ObservedReach.rs_callIn run hT
  rw [show Impl.cert.prog[96]? = some Impl.t_41da_c96 from rfl] at hg
  cases hg
  obtain ⟨_, amount, _, _, run⟩ := V22TransferReach.balance_reach_observed erase run hT
  unfold Impl.t_1870_c64 at run
  orsd
  iterate 5 orsx
  rcases ObservedReach.rs_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
  swap
  · exact .inr (after_source erase hsg run hT cont)
  unfold Impl.t_1879_c64 at run
  iterate 5 orsx
  obtain ⟨g, _, hg, run⟩ := ObservedReach.rs_callIn run hT
  rw [show Impl.cert.prog[93]? = some Impl.t_3f98_c93 from rfl] at hg
  cases hg
  rcases V22TransferFromCallee.body_source_or_return erase run hT with
    source | ⟨returned, callee, _, later⟩
  · exact .inl source
  obtain ⟨Y, stack, length⟩ := callee.entry_stack_below_noStateGas erase Impl.cert_check hsg
    (k := 93) (ρ := 0x1883)
    (X := [amount, recipient.toB256, sevm.currentTarget.toB256, 0x1883])
    (R := amount :: recipient.toB256 :: tag :: S)
    (show Impl.cert.entries[93]? = some ⟨0x3f98, [.unk, .unk, .unk, .ret], 0⟩ from rfl)
    (show Impl.cert.prog[93]? = some Impl.t_3f98_c93 from rfl) rfl
    (by exact .cons trivial (.cons trivial (.cons trivial (.cons rfl .nil))))
  have empty : Y = [] := by
    cases Y with
    | nil => rfl
    | cons head tail => simp only [List.length_cons] at length; omega
  simp only [empty, List.nil_append] at stack
  rw [St.self stack rfl] at later
  exact .inr (after_source erase hsg later hT cont)

/-- Exact selector routing through the inherited initializer wrapper. -/
theorem route_initializer : SFunc.selWalk 0x2fc81e09
    (.next (.reg (.dup 0)) (.next (.push [0x84, 0x56, 0xcb, 0x59] (by decide))
      (.next (.reg .gt) (.next (.push [0x01, 0xd3] (by decide))
        (.branch Impl.t_002b_c0 Impl.t_01d3_c0))))) =
    .inl (Bytes.toB256 [0x2f, 0xc8, 0x1e, 0x09], 171) := by
  decide +kernel

/-- Original entry and ABI decoding reach either the transfer's balance store or
the initializer suffix, with no assumption about eventual frame success. -/
theorem entry_source {Q : Sevm → Devm → Ninst → Devm → Prop}
    (erase : ∀ {s d n d'}, Q s d n d' → Ninst.Run s d n d')
    {sevm : Sevm} {b : Devm} {S : List B256} {M : Mem} {G : Nat} {T : Conf}
    (hsg : sevm.benvStat.rules.stateGas = none)
    (selected : Blanc.Sevm.selector sevm = 0x2fc81e09)
    (run : ObservedReach Q observe Impl.cert.prog sevm
      ⟨St b S M G, Impl.t_0000_c0, []⟩ T)
    (hT : AtSstore T) :
    V22TransferReach.ObservedSource Q observe sevm sevm.currentTarget
      (Sevm.dataWord sevm 4).toAdr T ∨ (∃ rest, T.d.stack = 18 :: rest) ∨ BlacklistSource Q observe sevm T := by
  unfold Impl.t_0000_c0 at run
  iterate 7 orsx
  rcases ObservedReach.rs_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
  · exact (Reach.false_of_sstoreFree (E := []) rfl run.forget hT (by decide +kernel)
      (fun _ h => by cases h)).elim
  unfold Impl.t_0010_c0 at run
  orsd
  iterate 5 orsx
  rcases ObservedReach.rs_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
  swap
  · exact (Reach.false_of_sstoreFree (E := []) rfl run.forget hT (by decide +kernel)
      (fun _ h => by cases h)).elim
  unfold Impl.t_001a_c0 at run
  iterate 4 orsx
  have word : Sevm.dataWord sevm (Bytes.toB256 [0]) >>> (Bytes.toB256 [0xe0]).toNat =
      0x2fc81e09 := selected
  rw [word] at run
  obtain ⟨-, g, _, hg, run⟩ := ObservedReach.selWalk_inlS erase route_initializer run hT
  rw [show Impl.cert.prog[171]? = some Impl.t_0501_c171 from rfl] at hg
  cases hg
  unfold Impl.t_0501_c171 at run
  orsd
  iterate 10 orsx
  rcases ObservedReach.rs_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
  · exact (Reach.false_of_sstoreFree (E := []) rfl run.forget hT (by decide +kernel)
      (fun _ h => by cases h)).elim
  unfold Impl.t_0517_c171 at run
  orsd
  iterate 5 orsx
  rw [show Bytes.toB256 [0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,
      0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff] = ff20 from rfl,
    ff20_and_word] at run
  obtain ⟨g, _, hg, run⟩ := ObservedReach.rs_callIn run hT
  rw [show Impl.cert.prog[64]? = some Impl.t_1853_c64 from rfl] at hg
  cases hg
  apply body_source erase hsg run hT
  intro f member
  have same := List.mem_singleton.mp member
  subst f
  decide +kernel

/-- Every original successful store is the version word or has its actual
transfer return tag or blacklist flag, exact key and earlier successful hash. -/
theorem successfulSstore_source {root node : Exec.Deriv}
    (pc : root.pc = 0) (code : root.sevm.code = Impl.code)
    (hsg : root.sevm.benvStat.rules.stateGas = none)
    (chain : Exec.Deriv.ParentPrefix root node)
    (selected : Blanc.Sevm.selector root.sevm = 0x2fc81e09)
    {write : Exec.StorageWrite} (found : Exec.Deriv.successfulSstore? node = some write) :
    write.key = 18 ∨
    (node.devm.stack[2]? = some 0x40e8 ∧ write.key = mapSlot root.sevm.currentTarget.toB256 9 ∧
      ∃ hashPc, KeccakBefore root node
        (root.sevm.currentTarget.toB256.toBytes ++ (9 : B256).toBytes) hashPc) ∨
    (node.devm.stack[2]? = some 0x40f9 ∧
      write.key = mapSlot (Sevm.dataWord root.sevm 4).toAdr.toB256 9 ∧
      ∃ hashPc, KeccakBefore root node
        ((Sevm.dataWord root.sevm 4).toAdr.toB256.toBytes ++ (9 : B256).toBytes) hashPc) ∨
    (node.devm.stack[2]? = some 1 ∧ write.key = mapSlot root.sevm.currentTarget.toB256 9 ∧
      ∃ hashPc, KeccakBefore root node
        (root.sevm.currentTarget.toB256.toBytes ++ (9 : B256).toBytes) hashPc) := by
  obtain ⟨decoded, rest, stack⟩ := Exec.Deriv.successfulSstore?_decoded found
  obtain ⟨κ, reach, ok⟩ :=
    observed_reach_of_parentPrefix_noStateGas Impl.cert_check pc code hsg chain
  obtain ⟨g, tree, -⟩ := ok.tree_of_sstore decoded
  have target : AtSstore (κ.conf node.devm) := ⟨g, tree⟩
  have walk := reach
  change ObservedReach (StepIn root) (Cursor.RawEdgeAt Impl.code Impl.cert root node)
    Impl.cert.prog root.sevm ⟨root.devm, Impl.t_0000_c0, []⟩ (κ.conf node.devm) at walk
  rw [St.self' root.devm] at walk
  rcases entry_source (fun h => StepIn.toRun h) hsg selected walk target with
    source | fixed | blacklist
  · rcases source with ⟨⟨value, other, keyStack⟩, _, hash⟩ | ⟨⟨value, other, keyStack⟩, _, hash⟩
    · obtain ⟨occ, next, here, instruction, result, before, edge, after, _, _, hashStack, read⟩ :=
        hash.actual
      exact .inr (.inl ⟨by change node.devm.stack = _ at keyStack; rw [keyStack]; rfl,
        (List.cons.inj (stack.symm.trans keyStack)).1,
        _, occ, next, rfl, instruction, result, before, edge, after, hashStack, read⟩)
    · obtain ⟨occ, next, here, instruction, result, before, edge, after, _, _, hashStack, read⟩ :=
        hash.actual
      exact .inr (.inr (.inl ⟨by change node.devm.stack = _ at keyStack; rw [keyStack]; rfl,
        (List.cons.inj (stack.symm.trans keyStack)).1,
        _, occ, next, rfl, instruction, result, before, edge, after, hashStack, read⟩))
  · obtain ⟨other, keyStack⟩ := fixed
    exact .inl (List.cons.inj (stack.symm.trans keyStack)).1
  · obtain ⟨⟨value, other, keyStack⟩, hash⟩ := blacklist
    obtain ⟨occ, next, here, instruction, result, before, edge, after, _, _, hashStack, read⟩ :=
      hash.actual
    exact .inr (.inr (.inr ⟨by change node.devm.stack = _ at keyStack; rw [keyStack]; rfl,
      (List.cons.inj (stack.symm.trans keyStack)).1,
      _, occ, next, rfl, instruction, result, before, edge, after, hashStack, read⟩))


end Blanc.Lift.Usdc.V22InitializerReach
