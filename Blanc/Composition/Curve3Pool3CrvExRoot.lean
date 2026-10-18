import Blanc.Composition.Curve3Pool3CrvWorld
import Blanc.Lift.Curve3Pool.Walk.Exchange
import Blanc.Lift.Curve3Pool.CallGuards
import Blanc.Lift.Curve3Pool.SpawnKinds
import Blanc.Lift.ChildFrameCode

/-!
# U9(b): the children and the raw frames of an `exchange` frame over synthetic-token coins

An `exchange` frame of the pool's runtime whose three coins hold the synthetic token `Token20`
(which spawns nothing) at its entry:

* `exRoot_coinChild_keeps`: a direct committed child at a coin runs `Token20`, keeps the pool's
  storage and the code at `4` (`Exec.childFrames_code`, `Exec.Frame.keeps_of_spawnFree`);
* `exRoot_children`: with the exchange walk (`xa_exchange`, whose keep premises concern only the
  coin children) every direct committed child is at a coin, so every child keeps the pool's storage
  and the code at `4` — the per-child ENV premises of `exchange_rawE`/`exchange_live`
  (`PoolCallsKeep`, children keep code `4`) hold, from the coins' code;
* `exRoot_raw`: every raw frame the exchange enters is a direct committed child running `Token20`
  at a coin, with no raw frame below it (`Exec.rawFrameDescendants_of_guardCheck_entry`: the 3pool
  runtime tests every call's flag, `code_guardCheck`).
-/

namespace Blanc.Composition.Curve3Pool3CrvInstance

open Jaune Blanc Blanc.Lift Blanc.Lift.Curve3Pool

section Root

variable {sevm : Sevm} {b post : Devm}

/-- The pool frame's same-frame chain decodes only `CALL`/`STATICCALL`. -/
theorem exRoot_callKinds (hcode : sevm.code = Curve3Pool.code)
    (exc : Exec 0 sevm b (.ok post)) :
    ∀ N, Exec.Deriv.ParentPrefix ⟨0, sevm, b, .ok post, exc⟩ N →
      ∀ x, Xinst.At N.sevm.code N.pc x → x = .call ∨ x = .staticcall := by
  intro N pp x hx
  have hb := Exec.Deriv.ParentPrefix.noPush pp (noPushBefore_zero _ _)
  have hNs : N.sevm = sevm := Blanc.Exec.Deriv.ParentPrefix.sevm_eq pp
  rw [hNs, hcode] at hb hx
  exact callKinds_of_check code_callKinds hb hx

theorem token20_code_ne : (VyperNonreentrantDeployed.Token20.code).toList ≠ [] := by
  decide +kernel

theorem token20_not_delegation : ¬ isValidDelegation VyperNonreentrantDeployed.Token20.code := by
  intro h
  have h1 := h.1
  revert h1
  decide +kernel

theorem pool_code_ne : (Curve3Pool.code).toList ≠ [] := by
  intro h
  have := Curve3Pool.code_toList_length
  rw [h] at this
  cases this

/-- **A coin child keeps the pool's storage and the code at `4`.** -/
theorem exRoot_coinChild_keeps (hcode : sevm.code = Curve3Pool.code)
    (hfork : CoveredFork sevm.benvStat.fork) (hpool : b.getCode sevm.currentTarget = Curve3Pool.code)
    (exc : Exec 0 sevm b (.ok post)) {t : Adr}
    (htc : b.getCode t = VyperNonreentrantDeployed.Token20.code) (htp : t ≠ sevm.currentTarget)
    (ht4 : t ≠ 4) :
    ∀ c ∈ Exec.childFrames exc, c.sevm.currentTarget = t →
      (∀ x, (c.post.getStor sevm.currentTarget).get x = (c.pre.getStor sevm.currentTarget).get x) ∧
        c.post.getCode 4 = c.pre.getCode 4 := by
  intro c hc ht
  have htc' := htc
  have hpool' := hpool
  obtain ⟨cfork, cpre, ccode⟩ := Exec.childFrames_code exc hfork (exRoot_callKinds hcode exc) c hc
  have hcc : c.sevm.code = VyperNonreentrantDeployed.Token20.code := by
    rw [ccode t (by rw [htc']; exact token20_code_ne) (by rw [htc']; exact token20_not_delegation)
      ht, htc']
  have hsf : SpawnFreeReach c.sevm.code := by
    rw [hcc]; exact VyperNonreentrantDeployed.Token20.spawnFreeReach
  have hpc := Exec.childFrames_pc exc c hc
  obtain ⟨hst, -⟩ := Exec.Frame.keeps_of_spawnFree c hpc cfork hsf (a := sevm.currentTarget)
    (by rw [ht]; exact htp.symm)
  obtain ⟨-, h4⟩ := Exec.Frame.keeps_of_spawnFree c hpc cfork hsf (a := 4)
    (by rw [ht]; exact fun h => ht4 h.symm)
  refine ⟨hst (by rw [cpre _ (by rw [hpool']; exact pool_code_ne), hpool']; exact pool_code_ne),
    h4⟩

/-- The pool's coin `k` as its storage names it at the frame's entry base. -/
abbrev exCoin (sevm : Sevm) (b : Devm) (k : Fin 3) : Adr :=
  ((b.getStor sevm.currentTarget).get (coinSlot k)).toAdr

/-- **Every direct committed child of the `exchange` frame is at a coin, and keeps the pool's
storage and the code at `4`.** -/
theorem exRoot_children {s : Curve3Pool.State} (exc : Exec 0 sevm b (.ok post))
    (hcode : sevm.code = Curve3Pool.code) (hfork : CoveredFork sevm.benvStat.fork)
    (hlen : 4 ≤ sevm.data.length) (hcd : sevm.data.length < 2 ^ 256)
    (hsel : Sevm.selector sevm = selExchange)
    (ha : Abstracts (b.getStor sevm.currentTarget) s)
    (hcoinPre : ∀ k : Fin 3, ¬ sevm.benvStat.rules.isPrecomp (exCoin sevm b k))
    (hpool : b.getCode sevm.currentTarget = Curve3Pool.code) (hid : IdReady sevm b)
    (hstack : b.stack = []) (hmem : b.memory = Mem.empty) (hgas : b.gasMeasure < 2 ^ 256)
    (hcoins : ∀ k : Fin 3, b.getCode (exCoin sevm b k) = VyperNonreentrantDeployed.Token20.code ∧
      exCoin sevm b k ≠ sevm.currentTarget ∧ exCoin sevm b k ≠ 4) :
    (∀ c ∈ Exec.childFrames exc, ExCoinChild sevm b c) ∧
      PoolCallsKeep ⟨0, sevm, b, .ok post, exc⟩ ∧
      ∀ c ∈ Exec.childFrames exc, c.post.getCode 4 = c.pre.getCode 4 := by
  have keeps : ∀ c ∈ Exec.childFrames exc, ExCoinChild sevm b c →
      (∀ x, (c.post.getStor sevm.currentTarget).get x = (c.pre.getStor sevm.currentTarget).get x) ∧
        c.post.getCode 4 = c.pre.getCode 4 := by
    intro c hc ⟨k, hk⟩
    obtain ⟨h1, h2, h3⟩ := hcoins k
    exact exRoot_coinChild_keeps hcode hfork hpool exc h1 h2 h3 c hc hk
  have hpc : b.getCode sevm.currentTarget ≠ .empty := by
    rw [hpool]
    intro h
    have := pool_code_ne
    rw [h, ByteArray.toList_eq_toList_data] at this
    exact this rfl
  have hci : (exI sevm).toNat < 3 → ¬ sevm.benvStat.rules.isPrecomp
      ((b.getStor sevm.currentTarget).get (coinsBase + exI sevm)).toAdr := fun hi => by
    simpa only [exCoin, coinSlot, toB256_toNat] using hcoinPre ⟨_, hi⟩
  have hcj : (exJ sevm).toNat < 3 → ¬ sevm.benvStat.rules.isPrecomp
      ((b.getStor sevm.currentTarget).get (coinsBase + exJ sevm)).toAdr := fun hj => by
    simpa only [exCoin, coinSlot, toB256_toNat] using hcoinPre ⟨_, hj⟩
  obtain ⟨-, -, -, hi3, hj3, x0, x1, x2, -, Lp, cp, cq, D, y, amp, hL, hcpm, hpt, -, -, -, -,
    hpull, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hqt, -⟩ :=
    xa_exchange hcode hfork hlen hcd hsel rfl ha hci hcj hpc hid
      (fun c hc hk => (keeps c hc hk).1) (fun c hc hk => (keeps c hc hk).2)
      (XAt.of_eq (St.self hstack hmem) (XAt.of_exec exc hgas))
  have coin : ∀ c ∈ Exec.childFrames exc, ExCoinChild sevm b c := by
    intro c hc
    rw [hL] at hc
    rcases List.mem_append.mp hc with hc | hc
    · rcases hpull with ⟨-, rfl, -⟩ | ⟨-, c1, c2, rfl, hb1, hb2, -⟩
      · rw [List.mem_singleton] at hc
        subst hc
        exact exCoinChild_of hi3 hpt
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
        rcases hc with rfl | rfl | rfl
        · exact exCoinChild_of hi3 hb1.target
        · exact exCoinChild_of hi3 hpt
        · exact exCoinChild_of hi3 hb2.target
    · rw [List.mem_singleton] at hc
      subst hc
      exact exCoinChild_of hj3 hqt
  exact ⟨coin, fun c hc => (keeps c hc (coin c hc)).1, fun c hc => (keeps c hc (coin c hc)).2⟩

/-- **The raw frames an `exchange` frame enters** are its direct committed children, each at a coin
running `Token20`, entering nothing further. -/
theorem exRoot_raw {s : Curve3Pool.State} (exc : Exec 0 sevm b (.ok post))
    (hcode : sevm.code = Curve3Pool.code) (hfork : CoveredFork sevm.benvStat.fork)
    (hlen : 4 ≤ sevm.data.length) (hcd : sevm.data.length < 2 ^ 256)
    (hsel : Sevm.selector sevm = selExchange)
    (ha : Abstracts (b.getStor sevm.currentTarget) s)
    (hcoinPre : ∀ k : Fin 3, ¬ sevm.benvStat.rules.isPrecomp (exCoin sevm b k))
    (hpool : b.getCode sevm.currentTarget = Curve3Pool.code) (hid : IdReady sevm b)
    (hstack : b.stack = []) (hmem : b.memory = Mem.empty) (hgas : b.gasMeasure < 2 ^ 256)
    (hcoins : ∀ k : Fin 3, b.getCode (exCoin sevm b k) = VyperNonreentrantDeployed.Token20.code ∧
      exCoin sevm b k ≠ sevm.currentTarget ∧ exCoin sevm b k ≠ 4) :
    ∀ r ∈ Exec.rawFrameDescendants exc, ∃ c ∈ Exec.childFrames exc, ExCoinChild sevm b c ∧
      r.sevm = c.sevm ∧ c.sevm.code = VyperNonreentrantDeployed.Token20.code ∧
      Exec.rawFrameDescendants r.exc = [] := by
  obtain ⟨coin, -, h4⟩ := exRoot_children exc hcode hfork hlen hcd hsel ha hcoinPre hpool hid
    hstack hmem hgas hcoins
  intro r hr
  obtain ⟨c, hc, hrc⟩ := Exec.rawFrameDescendants_of_guardCheck_entry code_guardCheck exc hcode
    hfork (of_decide_eq_true hid.pre) hgas hid.nodeleg h4 r hr
  obtain ⟨k, hk⟩ := coin c hc
  obtain ⟨htc, -, -⟩ := hcoins k
  have htc' := htc
  obtain ⟨cfork, -, ccode⟩ := Exec.childFrames_code exc hfork (exRoot_callKinds hcode exc) c hc
  have hcc : c.sevm.code = VyperNonreentrantDeployed.Token20.code := by
    rw [ccode _ (by rw [htc']; exact token20_code_ne) (by rw [htc']; exact token20_not_delegation)
      hk, htc']
  have hnil : Exec.rawFrameDescendants c.run = [] := by
    have hpc := Exec.childFrames_pc exc c hc
    obtain ⟨cpc, csevm, cpre, cout, crun, ccom⟩ := c
    dsimp only at hpc hcc ⊢
    subst hpc
    exact Exec.rawFrameDescendants_eq_nil_of_reach crun (noPushBefore_zero _ _)
      (by rw [hcc]; exact VyperNonreentrantDeployed.Token20.spawnFreeReach)
  simp only [Exec.rawFrameRoots, hnil, List.mem_singleton] at hrc
  subst hrc
  exact ⟨c, hc, ⟨k, hk⟩, rfl, hcc, hnil⟩

end Root

end Blanc.Composition.Curve3Pool3CrvInstance
