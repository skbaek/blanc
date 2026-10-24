import Blanc.Lift.Usdc.InitReach06
import Blanc.Lift.Usdc.OldInitializerV1Callee

/-!
# FiatTokenV1's `initialize` on a prefix reach

The V1 implementation code's `initialize` path walked on `Reach` to an `SSTORE`, over the same
trees the whole-run classifier `OldInitializerV1Callee.initialize_observed` walks: the
solc 0.4.24 dispatcher's linear comparison chain to entry `60`, the nonpayable check, the ABI
wrapper (`SolcAbiStringStaging.strFrag`/`rotFrag`/`staticFrag`, through
`ReachAbi.strFrag_reach` and its siblings, with the three allocations' `Staged3` facts), the
callee `t_16b0_c16` (the initialized and nonzero-address checks, three calls of the
`string storage = string memory` helper `46`, the packed setters, the owner setter `47` and the
initialized flag). Helper `46` stores the header at the slot and either the short string there
or the payload words through the copy loop (`ReachPayload.payloadB_reach`, entry `52`), and
clears the old tail through helper `42` (`ReachClear.legacyClear_reach`, entries `50`/`51`).
Every reached `SSTORE` writes a key of `Init06.KeysInit06` (the same fixed slots and payload
keys as the V2-line `initialize`) or zero (`initV1_reach`).
-/

namespace Blanc.Lift.Usdc.InitReachV1

open Jaune Blanc Blanc.Lift
open SolcStringAllocation SolcAbiStringStaging OldInitializerV1Staging
open Init06 (KeysInit KeysInit06)

variable {Q : Sevm → Devm → Ninst → Devm → Prop} {sevm : Sevm} {T : Conf}

/-- The shared exit tail `7` on a reach: it drops three words, clears the old tail through
helper `42` (zero stores only) and returns the slot word into the pending continuation. -/
theorem tail7_reach (erase : ∀ {s d n d'}, Q s d n d' → Ninst.Run s d n d')
    {K : List SFunc} {b : Devm} {x y z e slot r : B256} {S : List B256} {M : Mem} {G : Nat}
    (run : Reach Q ImplV1.cert.prog sevm
      ⟨St b (x :: y :: z :: e :: slot :: r :: S) M G, ImplV1.t_2ef9_c7, K⟩ T)
    (hT : AtSstore T) :
    ReachClear.ZeroAt T ∨ ∃ f K' b' G', K = f :: K' ∧
      Reach Q ImplV1.cert.prog sevm ⟨St b' (slot :: S) M G', f, K'⟩ T := by
  unfold ImplV1.t_2ef9_c7 at run
  rsd
  iterate 7 rsx
  obtain ⟨g, _, hg, run⟩ := rs_callIn run hT
  rw [show ImplV1.cert.prog[42]? = some ImplV1.t_2f0a_c42 from rfl] at hg
  cases hg
  unfold ImplV1.t_2f0a_c42 at run
  rsd
  iterate 3 rsx
  rw [OldInitializerV1Callee.t_2f10_c42_shape] at run
  rcases ReachClear.legacyClear_reach erase OldInitializerV1Payload.entry50
      OldInitializerV1Payload.retEntry51 rfl run hT with h | ⟨f, K', b', G', hK, run⟩
  · exact .inl h
  cases hK
  unfold ImplV1.t_2f06_c7 at run
  rsd
  iterate 2 rsx
  exact .inr (rs_retM run hT)

/-- **Helper `46` on a reach.** Entered with `L :: D :: slot :: r :: S` (the string length,
its data pointer in memory, the slot and the return tag), with `D + L` not wrapping, the reach
stops at a store of the slot, of zero or of `keccak(slot) + j` for `j < (L + 31) / 32`; or the
helper returns `slot :: S` into the pending continuation, with every byte of the entry memory
but the scratch word at `0` kept. -/
theorem helper46_reach (eraseQ : ∀ {s d n d'}, Q s d n d' → Ninst.Run s d n d')
    {K : List SFunc} {b : Devm} {L D slot r : B256} {S : List B256} {M : Mem} {G : Nat}
    (hnw : D.toNat + L.toNat < 2 ^ 256)
    (run : Reach (FreePtr.PotStep Q) ImplV1.cert.prog sevm
      ⟨St b (L :: D :: slot :: r :: S) M G, ImplV1.t_2e8a_c46, K⟩ T)
    (hT : AtSstore T) :
    StrStore.StoreAt slot ((L.toNat + 31) / 32) T ∨ ∃ f K' b' M' G', K = f :: K' ∧
      SolcStorageReturn.Keeps (M.write 0 slot.toBytes) M' ∧
      Reach (FreePtr.PotStep Q) ImplV1.cert.prog sevm ⟨St b' (slot :: S) M' G', f, K'⟩ T := by
  have erase : ∀ {s d n d'}, FreePtr.PotStep Q s d n d' → Ninst.Run s d n d' :=
    fun h => eraseQ h.1
  unfold ImplV1.t_2e8a_c46 at run
  rsd
  iterate 2 rsx
  rsload
  iterate 31 rsx
  rw [scratch_word M slot] at run
  have k0 : SolcStorageReturn.Keeps (M.write 0 slot.toBytes)
      ((M.write (Bytes.toB256 [0]).toNat slot.toBytes).read (Bytes.toB256 [0]).toNat
        (Bytes.toB256 [32]).toNat).2 := SolcStorageReturn.Keeps.read _ _ _
  generalize ((M.write (Bytes.toB256 [0]).toNat slot.toBytes).read (Bytes.toB256 [0]).toNat
    (Bytes.toB256 [32]).toNat).2 = M1 at run k0
  rcases rs_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
  · -- short string: header store at the slot, then the shared tail
    unfold ImplV1.t_2ebb_c46 at run
    iterate 10 rsx
    rcases Reach.sstoreS run with rfl | ⟨_, hstep, run⟩
    · exact .inl ⟨_, _, _, rfl, .inl rfl⟩
    obtain ⟨_, _, e⟩ := SolcStorageReturn.ri_sstore_any (erase hstep)
    subst e
    clear hstep
    rsx
    obtain ⟨g, _, hg, run⟩ := rs_jump run hT
    rw [show ImplV1.cert.prog[7]? = some ImplV1.t_2ef9_c7 from rfl] at hg
    cases hg
    rcases tail7_reach erase run hT with ⟨x, S', h⟩ | ⟨f, K', b', G', hK, run⟩
    · exact .inl ⟨_, _, _, h, .inr (.inl rfl)⟩
    · exact .inr ⟨f, K', b', _, G', hK, k0.trans (SolcStorageReturn.Keeps.read _ _ _), run⟩
  · -- long string: header store at the slot, payload loop, shared tail
    unfold ImplV1.t_2ecb_c46 at run
    rsd
    iterate 6 rsx
    rcases Reach.sstoreS run with rfl | ⟨_, hstep, run⟩
    · exact .inl ⟨_, _, _, rfl, .inl rfl⟩
    obtain ⟨_, _, e⟩ := SolcStorageReturn.ri_sstore_any (erase hstep)
    subst e
    clear hstep
    iterate 3 rsx
    rcases rs_branchTo run hT with ⟨-, _, run⟩ | ⟨-, g, _, hg, run⟩
    · unfold ImplV1.t_2eda_c46 at run
      iterate 3 rsx
      rw [OldInitializerV1Callee.t_2edd_c46_shape] at run
      generalize (slot.toBytes.keccak +
          (Bytes.toB256 [31] + (Bytes.toB256 [1, 0] * ((Bytes.toB256 [1] &&& _) =? 0) -
            Bytes.toB256 [1] &&& _) / Bytes.toB256 [2]) / Bytes.toB256 [32]) = E at run
      have cnt : SolcStoragePayload.count (D + L) D.toNat = (L.toNat + 31) / 32 := by
        unfold SolcStoragePayload.count
        rw [B256.toNat_add_eq_of_nof _ _ hnw]
        congr 1
        omega
      rcases ReachPayload.payloadB_reach erase (by intro h; cases h)
          (ReachPayload.mload_rdStep eraseQ) (ReachPayload.mload_win eraseQ)
          OldInitializerV1Payload.entry52 (i := 0) (fin := D + L)
          (base0 := slot.toBytes.keccak) (p := D.toNat) (rest := E :: slot :: r :: S)
          ⟨Nat.zero_le _, by omega, by
            rw [St.stack, Nat.mul_zero, Nat.add_zero, toB256_toNat,
              show ((0 : Nat).toB256) = 0 from rfl, B256.add_zero]⟩ run hT with
        ⟨j, v, S', hj, h⟩ | ⟨i, b', M', G', -, hk, run⟩
      · rw [cnt] at hj
        exact .inl ⟨_, _, _, h, .inr (.inr ⟨j, hj, rfl⟩)⟩
      · unfold ImplV1.t_2ef8_c52 at run
        rsd
        rcases tail7_reach erase run hT with ⟨x, S', h⟩ | ⟨f, K', b'', G'', hK, run⟩
        · exact .inl ⟨_, _, _, h, .inr (.inl rfl)⟩
        · exact .inr ⟨f, K', b'', _, G'', hK, k0.trans hk, run⟩
    · rw [show ImplV1.cert.prog[7]? = some ImplV1.t_2ef9_c7 from rfl] at hg
      cases hg
      rcases tail7_reach erase run hT with ⟨x, S', h⟩ | ⟨f, K', b', G', hK, run⟩
      · exact .inl ⟨_, _, _, h, .inr (.inl rfl)⟩
      · exact .inr ⟨f, K', b', _, G', hK, k0, run⟩

private theorem lit20 : Bytes.toB256 [0x20] = (32 : B256) := by decide

/-- One `callFrag` (stage string `j` for helper `46` at `slot`) on a reach: the reach stops in
the helper at a store of the slot, of zero or of a payload word of the string whose header at
`p` reads `L`, or returns past the call with the slot word on top and every word but the
scratch word kept. -/
theorem callFrag_reach (eraseQ : ∀ {s d n d'}, Q s d n d' → Ninst.Run s d n d')
    {j : Fin 16} {slot tag : Bytes} {hs : slot.length ≤ 32} {ht : tag.length ≤ 32} {k : SFunc}
    {b : Devm} {S : List B256} {M : Mem} {G : Nat} {p L : B256} (hp : S[j.val]? = some p)
    (hL : memWord M p.toNat = L) (hnw : p.toNat + 32 + L.toNat < 2 ^ 256)
    (run : Reach (FreePtr.PotStep Q) ImplV1.cert.prog sevm
      ⟨St b S M G, OldInitializerV1Callee.callFrag j slot tag hs ht k, []⟩ T)
    (hT : AtSstore T) :
    StrStore.StoreAt (Bytes.toB256 slot) ((L.toNat + 31) / 32) T ∨ ∃ b' M' G',
      SolcStorageReturn.Keeps (((M.read p.toNat 32).2).write 0 (Bytes.toB256 slot).toBytes) M' ∧
      Reach (FreePtr.PotStep Q) ImplV1.cert.prog sevm
        ⟨St b' (Bytes.toB256 slot :: S) M' G', k, []⟩ T := by
  have erase : ∀ {s d n d'}, FreePtr.PotStep Q s d n d' → Ninst.Run s d n d' :=
    fun h => eraseQ h.1
  unfold OldInitializerV1Callee.callFrag at run
  have hnext := rs_next run hT
  clear run
  obtain ⟨_, hstep, run⟩ := hnext
  obtain ⟨_, rfl⟩ := ri_dup hp (erase hstep)
  clear hstep
  iterate 13 rsx
  obtain ⟨g, _, hg, run⟩ := rs_callIn run hT
  rw [show ImplV1.cert.prog[46]? = some ImplV1.t_2e8a_c46 from rfl] at hg
  cases hg
  have e1 : (M.read p.toNat 32).1.toB256 = L := hL
  rw [e1, lit20] at run
  rcases helper46_reach eraseQ (OldInitializerV1Callee.nowrap hnw) run hT with
    h | ⟨f, K', b', M', G', hK, hk, run⟩
  · exact .inl h
  · cases hK
    exact .inr ⟨b', M', G', hk, run⟩

/-- The keys of `initialize` with the three lengths read at the V1 heads. -/
abbrev KeysV1 (sevm : Sevm) : B256 → Prop :=
  KeysInit (lenAt sevm head1).toNat (lenAt sevm head2).toNat (lenAt sevm head3).toNat

theorem keysV1_eq (sevm : Sevm) : KeysInit06 sevm = KeysV1 sevm := by
  unfold KeysInit06 Init06.len06 KeysV1 lenAt head1 head2 head3
  rw [show Bytes.toB256 [4] + Bytes.toB256 [32] + Bytes.toB256 [32] = (68 : B256) by decide,
    show Bytes.toB256 [4] + Bytes.toB256 [32] = (36 : B256) by decide,
    show Bytes.toB256 [4] = (4 : B256) by decide]

/-- **The V1 callee on a reach.** From the call-16 entry stack the wrapper stages and memory
holding the three string headers, a reach of `t_16b0_c16` to an `SSTORE` stops at a write of
`KeysV1` or of zero. -/
theorem callee_reach (eraseQ : ∀ {s d n d'}, Q s d n d' → Ninst.Run s d n d')
    {a1 a2 a3 a4 a5 p1 p2 p3 : B256} {R : List B256} {b : Devm} {M : Mem} {G : Nat}
    (hdr1 : memWord M p1.toNat = lenAt sevm head1)
    (hdr2 : memWord M p2.toNat = lenAt sevm head2)
    (hdr3 : memWord M p3.toNat = lenAt sevm head3)
    (h32₂ : 32 ≤ p2.toNat) (h32₃ : 32 ≤ p3.toNat)
    (fit2 : p2.toNat + 32 ≤ M.size) (fit3 : p3.toNat + 32 ≤ M.size)
    (nw1 : p1.toNat + 32 + (lenAt sevm head1).toNat < 2 ^ 256)
    (nw2 : p2.toNat + 32 + (lenAt sevm head2).toNat < 2 ^ 256)
    (nw3 : p3.toNat + 32 + (lenAt sevm head3).toNat < 2 ^ 256)
    (run : Reach (FreePtr.PotStep Q) ImplV1.cert.prog sevm
      ⟨St b (a1 :: a2 :: a3 :: a4 :: a5 :: p3 :: p2 :: p1 :: retTag :: R) M G,
        ImplV1.t_16b0_c16, []⟩ T)
    (hT : AtSstore T) : InitStore (KeysV1 sevm) T := by
  have erase : ∀ {s d n d'}, FreePtr.PotStep Q s d n d' → Ninst.Run s d n d' :=
    fun h => eraseQ h.1
  unfold ImplV1.t_16b0_c16 at run
  rsd
  repeat rsa
  rcases rs_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
  · exact (Reach.false_of_sstoreFree (E := []) rfl run hT rfl (fun _ h => by cases h)).elim
  unfold ImplV1.t_16cc_c16 at run
  rsd
  repeat rsa
  rcases rs_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
  · exact (Reach.false_of_sstoreFree (E := []) rfl run hT rfl (fun _ h => by cases h)).elim
  unfold ImplV1.t_1708_c16 at run
  rsd
  repeat rsa
  rcases rs_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
  · exact (Reach.false_of_sstoreFree (E := []) rfl run hT rfl (fun _ h => by cases h)).elim
  unfold ImplV1.t_1744_c16 at run
  rsd
  repeat rsa
  rcases rs_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
  · exact (Reach.false_of_sstoreFree (E := []) rfl run hT rfl (fun _ h => by cases h)).elim
  unfold ImplV1.t_1780_c16 at run
  rsd
  repeat rsa
  rcases rs_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
  · exact (Reach.false_of_sstoreFree (E := []) rfl run hT rfl (fun _ h => by cases h)).elim
  -- name (slot 4)
  rw [OldInitializerV1Callee.t_17bc_shape] at run
  rsd
  rcases callFrag_reach eraseQ (p := p1) rfl hdr1 nw1 run hT with
    ⟨key, v, S', hs, hk | hv | ⟨j, hj, hk⟩⟩ | ⟨b1, M1, G1, keep1, run⟩
  · exact InitStore.of_eq hs (.inl (.inl (by rw [hk]; decide)))
  · exact InitStore.of_eq hs (.inr hv)
  · exact InitStore.of_eq hs (.inl (.inr (.inl ⟨j, hj, by rw [hk]; rfl⟩)))
  obtain ⟨m2, s1⟩ := OldInitializerV1Callee.memWord_keeps keep1 h32₂ fit2
  obtain ⟨m3, -⟩ := OldInitializerV1Callee.memWord_keeps keep1 h32₃ fit3
  -- symbol (slot 5)
  rw [OldInitializerV1Callee.t_17d2_shape] at run
  rsd
  rsx
  rcases callFrag_reach eraseQ (p := p2) rfl (m2.trans hdr2) nw2 run hT with
    ⟨key, v, S', hs, hk | hv | ⟨j, hj, hk⟩⟩ | ⟨b2, M2, G2, keep2, run⟩
  · exact InitStore.of_eq hs (.inl (.inl (by rw [hk]; decide)))
  · exact InitStore.of_eq hs (.inr hv)
  · exact InitStore.of_eq hs (.inl (.inr (.inr (.inl ⟨j, hj, by rw [hk]; rfl⟩))))
  obtain ⟨m3', -⟩ := OldInitializerV1Callee.memWord_keeps keep2 h32₃ (le_trans fit3 s1)
  -- currency (slot 7)
  rw [OldInitializerV1Callee.t_17e9_shape] at run
  rsd
  rsx
  rcases callFrag_reach eraseQ (p := p3) rfl (m3'.trans (m3.trans hdr3)) nw3 run hT with
    ⟨key, v, S', hs, hk | hv | ⟨j, hj, hk⟩⟩ | ⟨b3, M3, G3, -, run⟩
  · exact InitStore.of_eq hs (.inl (.inl (by rw [hk]; decide)))
  · exact InitStore.of_eq hs (.inr hv)
  · exact InitStore.of_eq hs (.inl (.inr (.inr (.inr ⟨j, hj, by rw [hk]; rfl⟩))))
  -- the packed setters, the owner setter and the initialized flag
  unfold ImplV1.t_1800_c16 at run
  rsd
  iterate 4
    repeat rsa
    rcases Reach.sstoreS run with rfl | ⟨_, hstep, run⟩
    · exact InitStore.of_top rfl (.inl (by decide))
    obtain ⟨_, _, e⟩ := SolcStorageReturn.ri_sstore_any (erase hstep)
    subst e
    clear hstep
  repeat rsa
  obtain ⟨g, _, hg, run⟩ := rs_callIn run hT
  rw [show ImplV1.cert.prog[47]? = some ImplV1.t_2e47_c47 from rfl] at hg
  cases hg
  unfold ImplV1.t_2e47_c47 at run
  rsd
  repeat rsa
  rcases Reach.sstoreS run with rfl | ⟨_, hstep, run⟩
  · exact InitStore.of_top rfl (.inl (by decide))
  obtain ⟨_, _, e⟩ := SolcStorageReturn.ri_sstore_any (erase hstep)
  subst e
  clear hstep
  repeat rsa
  obtain ⟨f, K', b₄, M₄, G₄, hK, run⟩ := rs_ret run hT
  cases hK
  unfold ImplV1.t_18e8_c16 at run
  rsd
  repeat rsa
  rcases Reach.sstoreS run with rfl | ⟨_, hstep, run⟩
  · exact InitStore.of_top rfl (.inl (by decide))
  obtain ⟨_, _, e⟩ := SolcStorageReturn.ri_sstore_any (erase hstep)
  subst e
  clear hstep
  repeat rsa
  exact (Reach.not_ret_nilS run hT).elim

private theorem lit4 : Bytes.toB256 [0x04] = (4 : B256) := by decide
private theorem lit584 : Bytes.toB256 [0x05, 0x84] = retTag := by decide
private theorem e36 : (32 : B256) + 4 = 36 := by decide
private theorem e68 : (32 : B256) + 36 = 68 := by decide
private theorem e100 : (32 : B256) + 68 = 100 := by decide
private theorem e132 : (32 : B256) + 100 = 132 := by decide
private theorem e164 : (32 : B256) + 132 = 164 := by decide
private theorem e196 : (32 : B256) + 164 = 196 := by decide
private theorem e228 : (32 : B256) + 196 = 228 := by decide

/-- **The V1 wrapper on a reach.** From memory whose free pointer is `p1 ≥ 96`, a reach of the
`initialize` wrapper `t_0410_c60` to an `SSTORE` stops at a write of `KeysV1` or of zero. -/
theorem wrapper_reach (eraseQ : ∀ {s d n d'}, Q s d n d' → Ninst.Run s d n d')
    {b : Devm} {cv : B256} {R : List B256} {M0 : Mem} {G0 : Nat} {p1 : B256}
    (hfp : memWord M0 64 = p1) (hp96 : 96 ≤ p1.toNat)
    (run : Reach (FreePtr.PotStep Q) ImplV1.cert.prog sevm
      ⟨St b (cv :: R) M0 G0, ImplV1.t_0410_c60, []⟩ T)
    (hT : AtSstore T) : InitStore (KeysV1 sevm) T := by
  have erase : ∀ {s d n d'}, FreePtr.PotStep Q s d n d' → Ninst.Run s d n d' :=
    fun h => eraseQ h.1
  subst hfp
  rw [t_0410_shape] at run
  rsd
  iterate 10 rsx
  rw [lit4, lit584] at run
  obtain ⟨_, -, run⟩ := ReachAbi.strFrag_reach eraseQ run hT
  obtain ⟨_, run⟩ := ReachAbi.rotFrag_reach eraseQ run hT
  rw [e36] at run
  obtain ⟨_, -, run⟩ := ReachAbi.strFrag_reach eraseQ run hT
  rw [t_04a4_shape] at run
  obtain ⟨_, run⟩ := ReachAbi.rotFrag_reach eraseQ run hT
  rw [e68] at run
  obtain ⟨_, hpost, run⟩ := ReachAbi.strFrag_reach eraseQ run hT
  obtain ⟨_, run⟩ := ReachAbi.rotFrag_reach eraseQ run hT
  rw [e100] at run
  obtain ⟨_, run⟩ := ReachAbi.staticFrag_reach eraseQ run hT
  rw [e132] at run
  obtain ⟨_, run⟩ := ReachAbi.staticFrag_reach eraseQ run hT
  rw [e164] at run
  obtain ⟨_, run⟩ := ReachAbi.staticFrag_reach eraseQ run hT
  rw [e196] at run
  obtain ⟨_, run⟩ := ReachAbi.staticFrag_reach eraseQ run hT
  rw [e228] at run
  obtain ⟨_, run⟩ := ReachAbi.staticFrag_reach eraseQ run hT
  iterate 4 rsx
  obtain ⟨_, T', inside, rfl⟩ := rs_callInto (E := []) rfl entry16 rfl (fun _ h => by cases h)
    run hT
  have hT' : AtSstore T' := AtSstore.below.mp hT
  have hS := stage3 hp96 (sliceD_length _ _ _) (sliceD_length _ _ _) (sliceD_length _ _ _) rfl rfl
    hpost
  have n1 := hS.next1
  have n2 := hS.next2
  have o12 := hS.ord12
  have o23 := hS.ord23
  have o34 := hS.ord34
  have b4 := hS.below4
  have f2 := hS.fit2
  have f3 := hS.fit3
  have l1 : (lenAt sevm head1).toNat = (Sevm.dataWord sevm (4 + Sevm.dataWord sevm 4)).toNat := rfl
  have l2 : (lenAt sevm head2).toNat = (Sevm.dataWord sevm (4 + Sevm.dataWord sevm 36)).toNat :=
    rfl
  have l3 : (lenAt sevm head3).toNat = (Sevm.dataWord sevm (4 + Sevm.dataWord sevm 68)).toNat :=
    rfl
  exact InitStore.below.mpr (callee_reach eraseQ hS.hdr1 hS.hdr2 hS.hdr3 (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega) inside hT')

/-- solc 0.4.24's selector word as the V1 dispatcher computes it: `and(0xffffffff,
div(calldataload(0), 2 ^ 224))`. -/
def selWordV1 (sevm : Sevm) : B256 :=
  Bytes.toB256 [0xff, 0xff, 0xff, 0xff] &&&
    (Sevm.dataWord sevm (Bytes.toB256 [0x00]) / Bytes.toB256 [0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00])

theorem route_init : SFunc.selWalk 0x3357162b
    (.next (.reg (.dup 0)) (.next (.push [0x06, 0xfd, 0xde, 0x03] (by decide)) (.next (.reg .eq)
      (.next (.push [0x01, 0x90] (by decide)) (.branchTo ImplV1.t_0041_c0 53))))) =
    .inl (Bytes.toB256 [0x33, 0x57, 0x16, 0x2b], 60) := by
  decide +kernel

/-- **V1 `initialize` on a prefix reach.** A reach of the V1 code from entry `0`, with empty
stack and memory and the `initialize` selector, to an `SSTORE` stops at a write of
`KeysInit06` or of zero. -/
theorem initV1_reach (eraseQ : ∀ {s d n d'}, Q s d n d' → Ninst.Run s d n d')
    (hs : selWordV1 sevm = 0x3357162b) {d : Devm} {G : Nat}
    (run : Reach (FreePtr.PotStep Q) ImplV1.cert.prog sevm
      ⟨St d [] Mem.empty G, ImplV1.t_0000_c0, []⟩ T)
    (hT : AtSstore T) : InitStore (KeysInit06 sevm) T := by
  have erase : ∀ {s d n d'}, FreePtr.PotStep Q s d n d' → Ninst.Run s d n d' :=
    fun h => eraseQ h.1
  rw [keysV1_eq]
  unfold ImplV1.t_0000_c0 at run
  iterate 7 rsx
  rcases rs_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
  swap
  · exact (Reach.false_of_sstoreFree (E := []) rfl run hT rfl (fun _ h => by cases h)).elim
  unfold ImplV1.t_000d_c0 at run
  iterate 7 rsx
  have hs' : Bytes.toB256 [0xff, 0xff, 0xff, 0xff] &&&
      (Sevm.dataWord sevm (Bytes.toB256 [0x00]) / Bytes.toB256 [0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00]) = 0x3357162b := hs
  rw [hs'] at run
  obtain ⟨-, g, G1, hg, run⟩ := Reach.selWalk_inlS erase route_init run hT
  rw [show ImplV1.cert.prog[60]? = some ImplV1.t_0404_c60 from rfl] at hg
  cases hg
  unfold ImplV1.t_0404_c60 at run
  rsd
  iterate 4 rsx
  rcases rs_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
  · exact (Reach.false_of_sstoreFree (E := []) rfl run hT rfl (fun _ h => by cases h)).elim
  have w := Mem.memWord_write_word Mem.empty (Bytes.toB256 [0x40]).toNat (Bytes.toB256 [0x80])
  rw [show (Bytes.toB256 [0x40]).toNat = 64 by decide] at w run
  exact wrapper_reach eraseQ w.1 (by decide) run hT

end Blanc.Lift.Usdc.InitReachV1
