import Blanc.Lift.Curve3Pool.Walk.ViewsKit
import Blanc.Lift.Curve3Pool.Walk.Quiet
import Blanc.Lift.Curve3Pool.Spec

/-!
# `A()`: the raw effect, with `_A` bridged

The body (`0x253`) is the non-payable guard, the internal call of `_A` (`PUSH1 6; PC; ADD;
PUSH2 0xa9; JUMP`, return tag `0x266`), crossed on the derivation by `xa_vA`, and the one-word
`RETURN` through `0x140` and the scratch word `0`.

* `rawEffect_view`: a view frame's `RawEffect` from its storage kept, its logs its children's,
  its output the word and its children static;
* `xa_vA_frame`: the frame on the derivation;
* `a_raw`: the target, given the certificate's checkedness `hc` (`BridgeChecks.lean` discharges
  it).
-/

namespace Blanc.Lift.Curve3Pool

open Jaune Blanc.Lift

/-- **A view frame's raw effect**: storage kept, the children's logs only, the output the word
`r`, every child static. -/
theorem rawEffect_view {D : Exec.Deriv} {post : Devm} {e : Env} {s : State} {r : Nat}
    (henv : EnvOf D e) (hfp : footprint (decodeCall D.sevm) = [])
    (hstor : ∀ x, (post.getStor D.sevm.currentTarget).get x = (entryStor D).get x)
    (hlogs : post.logs = D.devm.logs ++ (children D).flatMap (fun c => c.post.logs))
    (hout : post.output = word r)
    (hstatic : ∀ c ∈ children D, c.sevm.isStatic = true) :
    RawEffect D post e (viewOut s r) := by
  refine ⟨henv, ⟨fun x _ => hstor x, by rw [hfp]; nofun⟩, ?_, hout, fun _ => ?_⟩
  · rw [hlogs]
    simp only [viewOut, List.map_nil, List.append_nil]
  · rw [CallsOf, List.filterMap_eq_nil_iff.mpr]
    · rfl
    · intro c hc
      simp only [hstatic c hc, ↓reduceIte]

section

variable {sevm : Sevm} {post b : Devm} {L : List Exec.Frame} {G : Nat} {s : State}

/-- **The `A()` frame.** From the frame's entry with the `A()` selector, a successful frame
had no value and no child, and returned the word `v` with `aChk s t = some v`, keeping the
storage and logs. -/
theorem xa_vA_frame (hc : Cert.CheckedM code cert mems true)
    (hcode : sevm.code = code) (hfork : CoveredFork sevm.benvStat.fork)
    (hlen : 4 ≤ sevm.data.length) (hcd : sevm.data.length < 2 ^ 256)
    (hsel : Sevm.selector sevm = selA) (ha : Abstracts (b.getStor sevm.currentTarget) s)
    (h : XAt sevm post 0 (St b [] Mem.empty G) L) :
    sevm.value = 0 ∧ L = [] ∧ ∃ v : B256, aChk s sevm.benvStat.time.toNat = some v.toNat ∧
      (∀ a, post.getStor a = b.getStor a) ∧ post.logs = b.logs ∧ post.output = v.toBytes := by
  obtain ⟨_, h⟩ := xa_vd_A hcode hlen hcd hsel h
  xs 0x254 (.reg .callvalue) ri_callvalue
  xs 0x255 (.reg .iszero) ri_iszero
  xs 0x258 (.push [0x02, 0x5d] (by decide)) ri_push
  xji 0x259 0x25d hw
  · xdead
  have hval := eqCheck_ne_zero_eq hw
  xjd 0x25e
  xs 0x260 (.push [0x06] (by decide)) ri_push
  xpc 0x261
  xs 0x262 (.reg .add) ri_add
  xs 0x265 (.push [0x00, 0xa9] (by decide)) ri_push
  xjmp 0xa9
  obtain ⟨v, M, _, h, hv, -, hW, -⟩ := xa_vA hc hcode hfork ha (vyMem_wf Mem.wf_empty _) h
  have hR := Mem.reads_data M
  xjd 0x267
  xs 0x26a (.push [0x01, 0x40] (by decide)) ri_push
  xm 0x26b (.reg .mstore) ri_mstore_img
  xs 0x26e (.push [0x01, 0x40] (by decide)) ri_push
  xm 0x26f (.reg .mload) ri_mload_img
  xs 0x271 (.push [0x00] (by decide)) ri_push
  xm 0x272 (.reg .mstore) ri_mstore_img
  xs 0x274 (.push [0x20] (by decide)) ri_push
  xs 0x276 (.push [0x00] (by decide)) ri_push
  obtain ⟨hrun, rfl⟩ := xa_halt (l := .return_) (atL hcode (by kernel_rfl)) h
  obtain ⟨hout, hstor, hlogs⟩ := ri_return hrun
  refine ⟨hval, rfl, v, hv, fun a => by rw [hstor, (aBase_sloadsOnly sevm b).getStor],
    by rw [hlogs, (aBase_sloadsOnly sevm b).logs], ?_⟩
  rw [hout, hR.read, (WordAt.write_self _ _ v).read]
  exact WordAt.write_self _ _ _

/-- **`A()`'s raw effect**, given the certificate's checkedness. -/
theorem a_raw_of (hc : Cert.CheckedM code cert mems true) {pre : Devm}
    (exc : Exec 0 sevm pre (.ok post))
    (hcode : sevm.code = code) (hfork : CoveredFork sevm.benvStat.fork)
    (hlen : 4 ≤ sevm.data.length) (hcd : sevm.data.length < 2 ^ 256)
    (hsel : Sevm.selector sevm = selA)
    (hstack : pre.stack = []) (hmem : pre.memory = Mem.empty) (hgas : pre.gasMeasure < 2 ^ 256)
    (hck : Checkpoint (pre.getStor sevm.currentTarget) s) :
    ∃ e o, step s e (decodeCall sevm) = some o ∧
      RawEffect ⟨0, sevm, pre, .ok post, exc⟩ post e o := by
  have hx : XAt sevm post 0 (St pre [] Mem.empty pre.gasLeft) (Exec.childFrames exc) :=
    XAt.of_eq (St.self hstack hmem) (XAt.of_exec exc hgas)
  obtain ⟨hval, hL, v, hv, hstor, hlogs, hout⟩ :=
    xa_vA_frame hc hcode hfork hlen hcd hsel hck.abs hx
  have hdec : decodeCall sevm = .a := decodeCall_at (k := 0) rfl hsel hlen
  refine ⟨quietEnv sevm, viewOut s v.toNat, ?_, ?_⟩
  · rw [hdec]
    simp only [step, body, quietEnv, hval, hv]
    rfl
  · have hch : children ⟨0, sevm, pre, .ok post, exc⟩ = [] := hL
    refine rawEffect_view (envOf_quiet _) (by rw [hdec]; rfl) (fun x => by rw [hstor]; rfl)
      ?_ ?_ ?_
    · rw [hch, hlogs]
      simp only [List.flatMap_nil, List.append_nil]
    · rw [hout, word, toB256_toNat]
    · intro c hc'
      rw [hch] at hc'
      cases hc'

end

end Blanc.Lift.Curve3Pool
