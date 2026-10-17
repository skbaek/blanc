import Blanc.Lift.Curve3Pool.Walk.ExchangeDispatch
import Blanc.Lift.Curve3Pool.Walk.ExchangePull
import Blanc.Lift.Curve3Pool.Walk.ExchangeTail
import Blanc.Lift.Curve3Pool.Walk.ExchangeX
import Blanc.Lift.Curve3Pool.Walk.ExchangeChecks

/-!
# `exchange`: the frame up to `x`

`xa_ex_front` composes the dispatcher, the guards (`xa_ex_pre`), `_xp_mem` (crossed with
`xa_ex_xpMem`), the frame restore (`xa_ex_xp`), the pull with its optional `balanceOf` pair
(`xa_ex_bal1`, `xa_ex_pull`, `xa_ex_tail1`, `xa_ex_bal2`): from the frame's entry with the
`exchange` selector the walk reaches `0x26c9` (the computation of `x`) having consumed exactly
the pull's children, with the base's pool storage the entry storage with the lock set.

`ExBase` is what the walk keeps of the base between children.
-/

namespace Blanc.Lift.Curve3Pool

open Jaune Blanc.Lift Blanc.StableSwapNewton

/-- The base the walk carries: the pool's storage is `σ` slot by slot, its code and the frame's
output are the entry's, and the identity precompile is ready. -/
structure ExBase (sevm : Sevm) (b0 b : Devm) (σ : Stor) : Prop where
  stor : ∀ x, (b.getStor sevm.currentTarget).get x = σ.get x
  code : b.getCode sevm.currentTarget = b0.getCode sevm.currentTarget
  output : b.output = b0.output
  id : IdReady sevm b

theorem ExBase.rel {sevm : Sevm} {b0 b b' : Devm} {σ : Stor} (h : ExBase sevm b0 b σ)
    (hr : BaseRel b b') : ExBase sevm b0 b' σ :=
  ⟨fun x => by rw [hr.stor]; exact h.stor x, by rw [hr.code]; exact h.code,
    by rw [hr.output]; exact h.output, h.id.of_rel hr⟩

/-- Across a committed call child that keeps the pool's storage and address 4's code. -/
theorem ExBase.child {sevm : Sevm} {b0 b d : Devm} {σ : Stor} {t : Adr} {input : Bytes}
    {v : B256} {st : Bool} {c : Exec.Frame} (h : ExBase sevm b0 b σ)
    (hc : ChildOf b d t input v st c) (hpc : b0.getCode sevm.currentTarget ≠ .empty)
    (hkeep : ∀ x, (c.post.getStor sevm.currentTarget).get x =
      (c.pre.getStor sevm.currentTarget).get x)
    (hidk : c.post.getCode 4 = c.pre.getCode 4) : ExBase sevm b0 d σ := by
  have hpc' : b.getCode sevm.currentTarget ≠ .empty := by rw [h.code]; exact hpc
  refine ⟨fun x => ?_, by rw [hc.code _ hpc', h.code], by rw [hc.outputKeep, h.output],
    ⟨by rw [hc.codePost, hidk, hc.codePre]; exact h.id.nodeleg, hc.warm _ h.id.warm, h.id.pre,
      h.id.fork⟩⟩
  rw [hc.storPost _ hpc' x, hkeep x, hc.storPre _ hpc', h.stor]

/-- Across a `balanceOf` child. -/
theorem ExBase.bal {sevm : Sevm} {b0 b d : Devm} {σ : Stor} {C : B256} {c : Exec.Frame}
    (h : ExBase sevm b0 b σ) (hc : ExBal sevm b d C c)
    (hpc : b0.getCode sevm.currentTarget ≠ .empty)
    (hidk : c.post.getCode 4 = c.pre.getCode 4) : ExBase sevm b0 d σ := by
  have hpc' : b.getCode sevm.currentTarget ≠ .empty := by rw [h.code]; exact hpc
  refine ⟨fun x => by rw [hc.stor]; exact h.stor x, by rw [hc.code _ hpc', h.code],
    by rw [hc.output, h.output],
    ⟨by rw [hc.codePost, hidk, hc.codePre]; exact h.id.nodeleg, hc.acc _ h.id.warm, h.id.pre,
      h.id.fork⟩⟩

theorem ExBase.sload {sevm : Sevm} {b0 b : Devm} {σ : Stor} (h : ExBase sevm b0 b σ) (k : B256) :
    ExBase sevm b0 (afterSload sevm b k) σ :=
  ⟨fun x => by rw [afterSload_getStor]; exact h.stor x, by rw [afterSload_getCode]; exact h.code,
    by rw [afterSload_output]; exact h.output, h.id.afterSload k⟩

/-- A `balanceOf(self)` child at the coin word `C`, as `EnvOf` reads it. -/
structure ExBalChild (sevm : Sevm) (C : B256) (c : Exec.Frame) : Prop where
  target : c.sevm.currentTarget = C.toAdr
  data : c.sevm.data = balanceOfData sevm.currentTarget
  static : c.sevm.isStatic = true
  len : 32 ≤ c.post.output.length
  logs : c.post.logs = []

theorem ExBal.child {sevm : Sevm} {b d : Devm} {C : B256} {c : Exec.Frame}
    (h : ExBal sevm b d C c) : ExBalChild sevm C c :=
  ⟨h.target, h.data, h.static, h.len, h.logs⟩

/-- The first word a child returned. -/
abbrev exAns (c : Exec.Frame) : B256 := Bytes.toB256 (c.post.output.take 32)

/-- The pull's children and the credited amount `D`: for `i ≠ FEE_INDEX` the `transferFrom`
alone and `D = dx`; for `i == FEE_INDEX` the two `balanceOf` children around it and `D` their
answers' difference (checked). -/
def ExPull (sevm : Sevm) (C D : B256) (Lp : List Exec.Frame) (cp : Exec.Frame) : Prop :=
  (exI sevm ≠ 2 ∧ Lp = [cp] ∧ D = exDx sevm) ∨
  (exI sevm = 2 ∧ ∃ c1 c2, Lp = [c1, cp, c2] ∧ ExBalChild sevm C c1 ∧ ExBalChild sevm C c2 ∧
    ¬ exAns c2 < exAns c1 ∧ D = exAns c2 - exAns c1)

/-- **`exchange` up to `x`** (see the module note). -/
theorem xa_ex_front {sevm : Sevm} {post b : Devm} {L : List Exec.Frame} {G : Nat}
    (hcode : sevm.code = code) (hfork : CoveredFork sevm.benvStat.fork)
    (hlen : 4 ≤ sevm.data.length) (hcd : sevm.data.length < 2 ^ 256)
    (hsel : Sevm.selector sevm = selExchange)
    (hcoin : (exI sevm).toNat < 3 → ¬ sevm.benvStat.rules.isPrecomp
      ((b.getStor sevm.currentTarget).get (coinsBase + exI sevm)).toAdr)
    (hpc : b.getCode sevm.currentTarget ≠ .empty) (hid : IdReady sevm b)
    (hkeep : ∀ c ∈ L, ∀ x, (c.post.getStor sevm.currentTarget).get x =
      (c.pre.getStor sevm.currentTarget).get x)
    (hidk : ∀ c ∈ L, c.post.getCode 4 = c.pre.getCode 4)
    (h : XAt sevm post 0 (St b [] Mem.empty G) L) :
    (b.getStor sevm.currentTarget).get lockSlot = 0 ∧ sevm.value = 0 ∧
    (b.getStor sevm.currentTarget).get isKilledSlot = 0 ∧ (exI sevm).toNat < 3 ∧
    ∃ x0 x1 x2 : B256,
      xpChk ⟨(balAt (b.getStor sevm.currentTarget) 0).toNat,
        (balAt (b.getStor sevm.currentTarget) 1).toNat,
        (balAt (b.getStor sevm.currentTarget) 2).toNat⟩ =
        some ⟨x0.toNat, x1.toNat, x2.toNat⟩ ∧
    ∃ (Lp L' : List Exec.Frame) (cp : Exec.Frame) (D : B256) (d : Devm) (M : Mem) (img : Bytes)
      (G' : Nat), 0 < sevm.depth ∧ L = Lp ++ L' ∧ cp ∈ Lp ∧
      cp.sevm.currentTarget = ((b.getStor sevm.currentTarget).get (coinsBase + exI sevm)).toAdr ∧
      cp.sevm.data = exPullData sevm ∧ cp.sevm.value = 0 ∧ cp.sevm.isStatic = sevm.isStatic ∧
      RawCallOk cp.post.output ∧
      ExPull sevm ((b.getStor sevm.currentTarget).get (coinsBase + exI sevm)) D Lp cp ∧
      ExBase sevm b d ((b.getStor sevm.currentTarget).set lockSlot 1) ∧
      d.logs = b.logs ++ Lp.flatMap (fun c => c.post.logs) ∧
      Mem.Reads M img ∧ Mem.Wf M ∧
      ExFrame img (exW3 (balAt (b.getStor sevm.currentTarget) 0)
        (balAt (b.getStor sevm.currentTarget) 1) (balAt (b.getStor sevm.currentTarget) 2))
        (exW3 x0 x1 x2) D ((b.getStor sevm.currentTarget).get (coinsBase + exI sevm)) ∧
      XAt sevm post 0x26c9 (St d [] M G') L' := by
  obtain ⟨G1, h⟩ := xa_dispatch_exchange hcode hlen hcd hsel h
  obtain ⟨hlock, hval, hkill, b1, M1, img1, G1, z0, z1, z2, hs1, hl1, ho1, hcd1, hid1, hR, hW,
    h⟩ := xa_ex_pre hcode hfork (vyMem_reads Mem.wf_empty Mem.reads_empty _)
      (vyMem_wf Mem.wf_empty _) h
  refine ⟨hlock, hval, hkill, ?_⟩
  obtain ⟨x0, x1, x2, M2, G2, h, hxp, -, hW2⟩ := xa_ex_xpMem hcode hfork hW h
  rw [show (Nat.toB256 0x2458).toNat = 0x2458 from B256.toNat_toB256_of_lt (by decide)] at h
  obtain ⟨hi3, M3, img3, G3, hR, hW, hF, hbr⟩ :=
    xa_ex_xp hcode hfork (Mem.reads_data M2) hW2 h
  refine ⟨hi3, x0, x1, x2, hxp, ?_⟩
  have hcoin := hcoin hi3
  have hexI : Nat.toB256 (exI sevm).toNat = exI sevm := toB256_toNat _
  have hC : (b1.getStor sevm.currentTarget).get (coinsBase + exI sevm) =
      (b.getStor sevm.currentTarget).get (coinsBase + exI sevm) := by
    rw [hs1, Stor.get_set_ne _ (by rw [← hexI]; exact coin_ne_lock hi3)]
  rw [hC] at hF
  have hB1 : ExBase sevm b b1 ((b.getStor sevm.currentTarget).set lockSlot 1) :=
    ⟨hs1, hcd1 _, ho1, hid1 hid⟩
  have hB2 := hB1.sload (coinsBase + exI sevm)
  have hl2 : (afterSload sevm b1 (coinsBase + exI sevm)).logs = b.logs := by
    rw [afterSload_logs, hl1]
  -- the optional first `balanceOf`
  have hmid : ∃ (Lpre L1 : List Exec.Frame) (bb : Devm) (M : Mem) (img : Bytes) (G : Nat)
      (D1 : B256), L = Lpre ++ L1 ∧
      ((exI sevm ≠ 2 ∧ Lpre = [] ∧ D1 = exDx sevm) ∨
        (exI sevm = 2 ∧ ∃ c1, Lpre = [c1] ∧
          ExBalChild sevm ((b.getStor sevm.currentTarget).get (coinsBase + exI sevm)) c1 ∧
          D1 = exAns c1)) ∧
      ExBase sevm b bb ((b.getStor sevm.currentTarget).set lockSlot 1) ∧
      bb.logs = b.logs ++ Lpre.flatMap (fun c => c.post.logs) ∧ Mem.Reads M img ∧ Mem.Wf M ∧
      ExFrame img (exW3 (balAt (b.getStor sevm.currentTarget) 0)
        (balAt (b.getStor sevm.currentTarget) 1) (balAt (b.getStor sevm.currentTarget) 2))
        (exW3 x0 x1 x2) D1 ((b.getStor sevm.currentTarget).get (coinsBase + exI sevm)) ∧
      XAt sevm post 0x2517 (St bb [] M G) L1 := by
    rcases hbr with ⟨hne, h⟩ | ⟨he, h⟩
    · exact ⟨[], L, _, _, _, _, _, rfl, .inl ⟨hne, rfl, rfl⟩, hB2,
        by rw [hl2, List.flatMap_nil, List.append_nil], hR, hW, hF, h⟩
    · obtain ⟨c1, L1, d1, M', img', G', rfl, -, hb1, hR', hW', hF', h'⟩ :=
        xa_ex_bal1 hcode hfork hR hW hF hcoin h
      refine ⟨[c1], L1, d1, M', img', G', _, rfl, .inr ⟨he, c1, rfl, hb1.child, rfl⟩,
        hB2.bal hb1 hpc (hidk c1 List.mem_cons_self), ?_, hR', hW', hF', h'⟩
      rw [hb1.dlogs, hl2, List.flatMap_cons, hb1.logs, List.flatMap_nil, List.append_nil,
        List.append_nil]
  clear hbr hF hR hW
  obtain ⟨Lpre, L1, bb, M4, img4, G4, D1, rfl, hpre, hBb, hlb, hR, hW, hF, h⟩ := hmid
  -- the pull and its `raw_call` test
  have hk1 : ∀ c ∈ L1, ∀ x, (c.post.getStor sevm.currentTarget).get x =
      (c.pre.getStor sevm.currentTarget).get x :=
    fun c hc => hkeep c (List.mem_append_right _ hc)
  have hi1 : ∀ c ∈ L1, c.post.getCode 4 = c.pre.getCode 4 :=
    fun c hc => hidk c (List.mem_append_right _ hc)
  obtain ⟨hdepth, b', cp, L2, d, img5, G5, hbr', rfl, hcp, hF5, hR5, hW5, hrd5, h⟩ :=
    xa_ex_pull hcode hfork hR hW hF hBb.id hcoin h
  have hBd := (hBb.rel hbr').child hcp hpc (hk1 cp List.mem_cons_self)
    (hi1 cp List.mem_cons_self)
  obtain ⟨hok, b6, M6, img6, G6, hb6, hR6, hW6, hk6, h⟩ := xa_ex_tail1 hcode hBd.id hR5 hW5 hrd5 h
  have hF6 : ExFrame img6 _ _ D1 _ := hF5.mono fun o v hv ho =>
    hk6 o v hv (by omega) (by omega)
  have hB6 := hBd.rel hb6
  have hl6 : b6.logs = b.logs ++ Lpre.flatMap (fun c => c.post.logs) ++ cp.post.logs := by
    rw [hb6.logs, hcp.logs, hbr'.logs, hlb]
  -- the optional second `balanceOf`
  rcases xa_ex_bal2 hcode hfork hR6 hW6 hF6 hcoin h with ⟨hne, G7, hX⟩ |
    ⟨he, c2, L3, d2, M7, img7, G7, rfl, hb2, hle, hR7, hW7, hF7, hX⟩
  · rcases hpre with ⟨-, rfl, rfl⟩ | ⟨he, -⟩
    · refine ⟨[cp], L2, cp, exDx sevm, b6, M6, img6, G7, hdepth, rfl, List.mem_singleton_self _,
        hcp.target, hcp.data, hcp.value, hcp.isStatic, hcp.output ▸ hok,
        .inl ⟨hne, rfl, rfl⟩, hB6, ?_, hR6, hW6, hF6, hX⟩
      rw [hl6, List.flatMap_nil, List.append_nil, List.flatMap_cons, List.flatMap_nil,
        List.append_nil]
    · exact absurd he hne
  · rcases hpre with ⟨hne, -⟩ | ⟨-, c1, rfl, hc1, rfl⟩
    · exact absurd he hne
    · have hmem2 : c2 ∈ cp :: c2 :: L3 := List.mem_cons_of_mem _ List.mem_cons_self
      refine ⟨[c1, cp, c2], L3, cp, exAns c2 - exAns c1, d2, M7, img7, G7, hdepth, by simp only [List.cons_append, List.nil_append], List.mem_cons_of_mem _ List.mem_cons_self,
        hcp.target, hcp.data, hcp.value, hcp.isStatic, hcp.output ▸ hok,
        .inr ⟨he, c1, c2, rfl, hc1, hb2.child, hle, rfl⟩,
        hB6.bal hb2 hpc (hi1 c2 hmem2), ?_, hR7, hW7, hF7, hX⟩
      rw [hb2.dlogs, hl6]
      simp only [List.flatMap_cons, List.flatMap_nil, hc1.logs, hb2.logs, List.append_nil,
        List.nil_append]

end Blanc.Lift.Curve3Pool
