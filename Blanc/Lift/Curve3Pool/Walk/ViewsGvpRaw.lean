import Blanc.Lift.Curve3Pool.Walk.ViewsGvp
import Blanc.Lift.Curve3Pool.Walk.ViewsA

/-!
# `get_virtual_price()`: the frame and its raw effect

`xa_gvp` composes the dispatcher with the three segments of `ViewsGvp.lean`; `gvp_raw_of`
reads the model's `getVirtualPrice` off it, with the environment's supply the `totalSupply()`
reply (`vEnv`).
-/

namespace Blanc.Lift.Curve3Pool

open Jaune Blanc.Lift Blanc.StableSwapNewton

/-- The environment a view frame observed: the quiet one with the supply `T`. -/
def vEnv (sevm : Sevm) (T : Option Nat) : Env :=
  ⟨sevm.benvStat.time.toNat, sevm.caller.toB256.toNat, sevm.value.toNat,
    fun _ => ⟨none, none, false, false⟩, T, false, false⟩

/-- A frame whose only child is the `totalSupply()` call observes `vEnv` with its reply. -/
theorem envOf_vEnv {D : Exec.Deriv} {c : Exec.Frame} (hL : children D = [c])
    (htgt : c.sevm.currentTarget = tokenAdr D) (hdata : c.sevm.data = totalSupplyData)
    (hlen : 32 ≤ c.post.output.length) :
    EnvOf D (vEnv D.sevm (some (vSupply c).toNat)) where
  time := rfl
  caller := rfl
  value := rfl
  coin _ :=
    ⟨fun _ h => (by cases h), fun _ h => (by cases h), fun h => (by cases h),
      fun h => (by cases h)⟩
  supply T h := by
    cases h
    exact .inr ⟨0, c, by rw [hL]; rfl, htgt, hdata, hlen, rfl⟩
  mintOk h := by cases h
  burnOk h := by cases h

section

variable {sevm : Sevm} {post b : Devm} {L : List Exec.Frame} {G : Nat} {s : State}

/-- The constant `PRECISION`, as pushed. -/
theorem prec_lit : (Bytes.toB256 [0x0d, 0xe0, 0xb6, 0xb3, 0xa7, 0x64, 0x00, 0x00]).toNat =
    precision := by decide

/-- The model's `get_virtual_price` when every check passes. -/
theorem getVirtualPrice_eq {s : State} {e : Env} {amp x0 x1 x2 D T : Nat}
    (hamp : aChk s e.time = some amp) (hxp : xpChk s.balances = some ⟨x0, x1, x2⟩)
    (hD : getDChk (V3.mk x0 x1 x2).get amp 1 = some D) (hm : D * precision < wordSize)
    (hT : e.supply = some T) (hT0 : T ≠ 0) :
    getVirtualPrice s e = some (D * precision / T) := by
  have hg : getDMem s.balances amp = some D := by
    unfold getDMem
    rw [hxp, Option.bind_eq_bind, Option.bind_some]
    exact hD
  unfold getVirtualPrice
  rw [hamp, Option.bind_eq_bind, Option.bind_some, hg, Option.bind_some, hT, Option.bind_some]
  simp only [chkMul, chkDiv, hm, hT0, ↓reduceIte, Option.bind_some]

/-- **The `get_virtual_price()` frame.** -/
theorem xa_gvp (hc : Cert.CheckedM code cert mems true)
    (hcode : sevm.code = code) (hfork : CoveredFork sevm.benvStat.fork)
    (hlen : 4 ≤ sevm.data.length) (hcd : sevm.data.length < 2 ^ 256)
    (hsel : Sevm.selector sevm = selGetVirtualPrice)
    (ha : Abstracts (b.getStor sevm.currentTarget) s)
    (htok : ¬ sevm.benvStat.rules.isPrecomp ((b.getStor sevm.currentTarget).get tokenSlot).toAdr)
    (h : XAt sevm post 0 (St b [] Mem.empty G) L) :
    sevm.value = 0 ∧ ∃ (c : Exec.Frame) (x0 x1 x2 amp D : B256), L = [c] ∧
      c.sevm.currentTarget = ((b.getStor sevm.currentTarget).get tokenSlot).toAdr ∧
      c.sevm.data = totalSupplyData ∧ c.sevm.isStatic = true ∧ 32 ≤ c.post.output.length ∧
      c.post.logs = [] ∧
      xpChk s.balances = some ⟨x0.toNat, x1.toNat, x2.toNat⟩ ∧
      aChk s sevm.benvStat.time.toNat = some amp.toNat ∧
      getDChk (V3.mk x0.toNat x1.toNat x2.toNat).get amp.toNat 1 = some D.toNat ∧
      D.toNat * precision < 2 ^ 256 ∧ vSupply c ≠ 0 ∧
      (∀ a, post.getStor a = b.getStor a) ∧ post.logs = b.logs ∧
      post.output = word (D.toNat * precision / (vSupply c).toNat) := by
  obtain ⟨_, h⟩ := xa_vd_getVirtualPrice hcode hlen hcd hsel h
  obtain ⟨hval, x0, x1, x2, b1, ws, M, G1, hb1, hws, h, hx, hV⟩ := xa_gvp_xp hc hcode hfork ha h
  have ha1 : Abstracts (b1.getStor sevm.currentTarget) s := by rw [hb1.getStor]; exact ha
  obtain ⟨amp, b2, M2, G2, ρ, hb2, hρ, h, hamp, hV2⟩ := xa_gvp_a hc hcode hfork ha1 hV h
  have hb := hb1.trans hb2
  obtain ⟨c, D, hL, htgt, hdata, hstat, hlen', hclogs, hD, hmul, hT, hstor, hlogs, hout⟩ :=
    xa_gvp_d hc hcode hfork hρ hws hV2 (by rw [hb.getStor]; exact htok) h
  have hm := mul_check_toNat hmul
  rw [prec_lit] at hm
  refine ⟨hval, c, x0, x1, x2, amp, D, hL, by rw [htgt, hb.getStor], hdata, hstat, hlen',
    hclogs, hx, hamp, hD, hm, hT, fun a => by rw [hstor, hb.getStor], by rw [hlogs, hb.logs], ?_⟩
  rw [hout, word, ← prec_lit, ← rlOut_toNat (by rw [prec_lit]; exact hm) hT, toB256_toNat]

/-- **`get_virtual_price()`'s raw effect**, given the certificate's checkedness. -/
theorem gvp_raw_of (hc : Cert.CheckedM code cert mems true) {pre : Devm}
    (exc : Exec 0 sevm pre (.ok post))
    (hcode : sevm.code = code) (hfork : CoveredFork sevm.benvStat.fork)
    (hlen : 4 ≤ sevm.data.length) (hcd : sevm.data.length < 2 ^ 256)
    (hsel : Sevm.selector sevm = selGetVirtualPrice)
    (hstack : pre.stack = []) (hmem : pre.memory = Mem.empty) (hgas : pre.gasMeasure < 2 ^ 256)
    (hck : Checkpoint (pre.getStor sevm.currentTarget) s)
    (htok : ¬ sevm.benvStat.rules.isPrecomp
      ((pre.getStor sevm.currentTarget).get tokenSlot).toAdr) :
    ∃ e o, step s e (decodeCall sevm) = some o ∧
      RawEffect ⟨0, sevm, pre, .ok post, exc⟩ post e o := by
  have hx : XAt sevm post 0 (St pre [] Mem.empty pre.gasLeft) (Exec.childFrames exc) :=
    XAt.of_eq (St.self hstack hmem) (XAt.of_exec exc hgas)
  obtain ⟨hval, c, x0, x1, x2, amp, D, hL, htgt, hdata, hstat, hlen', hclogs, hxp, hamp, hD, hm, hT,
    hstor, hlogs, hout⟩ := xa_gvp hc hcode hfork hlen hcd hsel hck.abs htok hx
  have hdec : decodeCall sevm = .getVirtualPrice := decodeCall_at (k := 1) rfl hsel hlen
  have hT0 := toNat_ne_zero hT
  refine ⟨vEnv sevm (some (vSupply c).toNat), viewOut s (D.toNat * precision / (vSupply c).toNat),
    ?_, ?_⟩
  · have hg := getVirtualPrice_eq (e := vEnv sevm (some (vSupply c).toNat)) hamp hxp hD hm rfl hT0
    rw [hdec]
    show (if (vEnv sevm _).value = 0 then body s _ .getVirtualPrice else none) = _
    rw [show (vEnv sevm (some (vSupply c).toNat)).value = 0 by rw [vEnv, hval]; rfl, ite_eq_left rfl]
    show (getVirtualPrice s _).bind (fun r => some (viewOut s r)) = _
    rw [hg]
    rfl
  · have hch : children ⟨0, sevm, pre, .ok post, exc⟩ = [c] := hL
    refine rawEffect_view (envOf_vEnv hch htgt hdata hlen') (by rw [hdec]; rfl)
      (fun x => by rw [hstor]; rfl) ?_ hout ?_
    · rw [hch, hlogs]
      simp only [List.flatMap_cons, List.flatMap_nil, hclogs, List.append_nil]
    · intro c' hc'
      rw [hch, List.mem_singleton] at hc'
      rw [hc']
      exact hstat

end

end Blanc.Lift.Curve3Pool
