import Blanc.Lift.InvWalkOps
import Blanc.Lift.InvWalkWorld
import Blanc.Lift.ExactWalkCutOps
import Blanc.ForwardCall

/-!
# More walk steps: `CALLER`, `KECCAK256`, `LOG3`/`LOG4`, selected `SSTORE`

Forward (`rx_*`) and inverse (`ri_*`) steps the solc walks did not need: `CALLER`
(`rx_caller`, `ri_caller`), `KECCAK256` inverted (`ri_keccak`; forward `rx_keccak` is in
`ExactWalk.lean`), a three-topic `LOG3` (`rx_log3`, `ri_log3`), a four-topic `LOG4`
inverted (`ri_log4`), and `SSTORE` forward at its selected cost (`rx_sstore`; inverse
`ri_sstore` is in `InvWalk.lean`).

Nothing here mentions a contract.
-/

namespace Blanc.Lift

open Jaune

section Steps

variable {fs : List SFunc} {sevm : Sevm} {b : Devm} {S : List B256} {M : Mem} {G : Nat}
  {f : SFunc} {o : Outcome}

theorem rx_caller (hroom : S.length < 1024)
    (k : SFunc.RunExact fs sevm (St b (sevm.caller.toB256 :: S) M G) f o) :
    SFunc.RunExact fs sevm (St b S M (G + 2)) (.next (.reg .caller) f) o :=
  .next (Ninst.runCompiled_pushItem (devm := St b S M (G + 2)) (G := G) (cost := gBase)
    (by rintro ⟨⟩) rfl rfl hroom) k

/-- `CALLER`, inverted. -/
theorem ri_caller {d : Devm}
    (h : Ninst.Run sevm (St b S M G) (.reg .caller) d) :
    ∃ G', d = St b (sevm.caller.toB256 :: S) M G' := by
  have hp := of_run_caller h
  have hs : d.stack = sevm.caller.toB256 :: S := by
    have := hp.stack
    simpa [Stack.Push, Split] using this
  have e := St.of_stackRel hp
  rw [hs] at e
  exact ⟨_, e⟩

/-- `KECCAK256`, inverted: the digest of the window, memory the window read's image. -/
theorem ri_keccak {i sz : B256} {d : Devm}
    (h : Ninst.Run sevm (St b (i :: sz :: S) M G) (.reg .keccak256) d) :
    ∃ G', d = St b ((M.read i.toNat sz.toNat).1.keccak :: S) (M.read i.toNat sz.toNat).2 G' := by
  rcases of_run_reg h with ⟨pc, run⟩
  simp only [Rinst.run, Rinst.runCore] at run
  rw [show (St b (i :: sz :: S) M G).popToNat = .ok (i.toNat, St b (sz :: S) M G) from rfl] at run
  simp only [Except.bind_ok] at run
  rw [show (St b (sz :: S) M G).popToNat = .ok (sz.toNat, St b S M G) from rfl] at run
  simp only [Except.bind_ok] at run
  rcases Except.bind_eq_ok run with ⟨s1, h1, h2⟩
  have e1 := Devm.eq_setGas_of_burn (Devm.burn_of_chargeGas h1)
  rw [e1, show ((St b S M G).setMach ⟨(St b S M G).stack, (St b S M G).memory, s1.gasLeft,
    (St b S M G).stateGas⟩) = St b S M s1.gasLeft from rfl, St.memRead_fst, St.memRead_snd] at h2
  refine ⟨s1.gasLeft, ?_⟩
  rw [Devm.eq_of_push_ok h2]
  rfl

/-- `LOG3`, with the whole charge named. -/
theorem rx_log3 {i sz t1 t2 t3 : B256} {c : Nat} {data : Bytes}
    (hstatic : sevm.isStatic = false)
    (hc : gLog + gLogdata * sz.toNat + gLogtopic * 3 +
      (St b (i :: sz :: t1 :: t2 :: t3 :: S) M (G + c)).extCost [⟨i.toNat, sz.toNat⟩] = c)
    (hd : (M.read i.toNat sz.toNat).1 = data) (hM : (M.read i.toNat sz.toNat).2 = M)
    (k : SFunc.RunExact fs sevm
      (St (b.addLog ⟨sevm.currentTarget, [t1, t2, t3], data⟩) S M G) f o) :
    SFunc.RunExact fs sevm (St b (i :: sz :: t1 :: t2 :: t3 :: S) M (G + c))
      (.next (.reg (.log 3)) f) o :=
  .next (Ninst.runCompiled_log_of (n := 3) (topics := [t1, t2, t3]) (s := S) rfl rfl hstatic hc hd
    hM rfl) k

/-- `LOG3`, inverted. -/
theorem ri_log3 {i sz t1 t2 t3 : B256} {d : Devm}
    (h : Ninst.Run sevm (St b (i :: sz :: t1 :: t2 :: t3 :: S) M G) (.reg (.log 3)) d) :
    ∃ G', d = St (b.addLog ⟨sevm.currentTarget, [t1, t2, t3], (M.read i.toNat sz.toNat).1⟩) S
      (M.read i.toNat sz.toNat).2 G' := by
  rcases of_run_reg h with ⟨pc, run⟩
  simp only [Rinst.run, Rinst.runCore] at run
  rw [show (St b (i :: sz :: t1 :: t2 :: t3 :: S) M G).popToNat =
    .ok (i.toNat, St b (sz :: t1 :: t2 :: t3 :: S) M G) from rfl] at run
  simp only [Except.bind_ok] at run
  rw [show (St b (sz :: t1 :: t2 :: t3 :: S) M G).popToNat =
    .ok (sz.toNat, St b (t1 :: t2 :: t3 :: S) M G) from rfl] at run
  simp only [Except.bind_ok] at run
  rw [show (St b (t1 :: t2 :: t3 :: S) M G).popN ((3 : Fin 5) : Nat) =
    .ok ([t1, t2, t3], St b S M G) from rfl] at run
  simp only [Except.bind_ok] at run
  rcases Except.bind_eq_ok run with ⟨s1, h1, h2⟩
  rcases Except.bind_eq_ok h2 with ⟨_, -, h3⟩
  cases h3
  have e1 := Devm.eq_setGas_of_burn (Devm.burn_of_chargeGas h1)
  refine ⟨s1.gasLeft, ?_⟩
  rw [e1]
  rfl

/-- `LOG4`, inverted. -/
theorem ri_log4 {i sz t1 t2 t3 t4 : B256} {d : Devm}
    (h : Ninst.Run sevm (St b (i :: sz :: t1 :: t2 :: t3 :: t4 :: S) M G) (.reg (.log 4)) d) :
    ∃ G', d = St (b.addLog ⟨sevm.currentTarget, [t1, t2, t3, t4], (M.read i.toNat sz.toNat).1⟩)
      S (M.read i.toNat sz.toNat).2 G' := by
  rcases of_run_reg h with ⟨pc, run⟩
  simp only [Rinst.run, Rinst.runCore] at run
  rw [show (St b (i :: sz :: t1 :: t2 :: t3 :: t4 :: S) M G).popToNat =
    .ok (i.toNat, St b (sz :: t1 :: t2 :: t3 :: t4 :: S) M G) from rfl] at run
  simp only [Except.bind_ok] at run
  rw [show (St b (sz :: t1 :: t2 :: t3 :: t4 :: S) M G).popToNat =
    .ok (sz.toNat, St b (t1 :: t2 :: t3 :: t4 :: S) M G) from rfl] at run
  simp only [Except.bind_ok] at run
  rw [show (St b (t1 :: t2 :: t3 :: t4 :: S) M G).popN ((4 : Fin 5) : Nat) =
    .ok ([t1, t2, t3, t4], St b S M G) from rfl] at run
  simp only [Except.bind_ok] at run
  rcases Except.bind_eq_ok run with ⟨s1, h1, h2⟩
  rcases Except.bind_eq_ok h2 with ⟨_, -, h3⟩
  cases h3
  have e1 := Devm.eq_setGas_of_burn (Devm.burn_of_chargeGas h1)
  refine ⟨s1.gasLeft, ?_⟩
  rw [e1]
  rfl

/-- `RETURN`, inverted: the output is the window, storage and logs are the base's. -/
theorem ri_return {i sz : B256} {d : Devm}
    (h : Linst.Run sevm (St b (i :: sz :: S) M G) .return_ (.ok d)) :
    d.output = (M.read i.toNat sz.toNat).1 ∧ (∀ a, Devm.getStor d a = Devm.getStor b a) ∧
      d.logs = b.logs := by
  simp only [Linst.Run, Linst.run] at h
  rw [show (St b (i :: sz :: S) M G).popToNat = .ok (i.toNat, St b (sz :: S) M G) from rfl] at h
  simp only [Except.bind_ok] at h
  rw [show (St b (sz :: S) M G).popToNat = .ok (sz.toNat, St b S M G) from rfl] at h
  simp only [Except.bind_ok] at h
  rcases Except.bind_eq_ok h with ⟨s1, h1, h2⟩
  have e1 := Devm.eq_setGas_of_burn (Devm.burn_of_chargeGas h1)
  cases h2
  rw [e1]
  exact ⟨rfl, fun _ => rfl, rfl⟩

/-- `SSTORE` at its selected cost (warm/cold, EIP-2200 schedule), with the sentry premise. -/
theorem rx_sstore {k' v : B256} (hfork : CoveredFork sevm.benvStat.fork)
    (hsentry : gCallStipend < G + sstoreCost sevm b k' v) (hstatic : sevm.isStatic = false)
    (k : SFunc.RunExact fs sevm (St (afterSstore sevm b k' v) S M G) f o) :
    SFunc.RunExact fs sevm (St b (k' :: v :: S) M (G + sstoreCost sevm b k' v))
      (.next (.reg .sstore) f) o := by
  refine .next (Ninst.runCompiled_sstore_selected_setMach hfork hsentry hstatic) ?_
  rw [← afterSstore_stateGas (sevm := sevm) (devm := b) (key := k') (value := v)]
  exact k

end Steps

/-- Every memory reads as its own backing array. -/
theorem Mem.reads_data (μ : Mem) : Mem.Reads μ μ.data.toList := by
  intro index
  by_cases bound : index < μ.data.size <;>
    simp [Array.getD, bound, List.getD_eq_getElem?_getD]

/-- A word written into a well-formed memory reads back. -/
theorem Mem.read_write_word_of_wf {M : Mem} (hwf : Mem.Wf M) (n : Nat) (v : B256) :
    ((M.write n v.toBytes).read n 32).1 = v.toBytes := by
  rw [(Mem.reads_data M).write hwf n v.toBytes |>.read]
  exact sliceD_word_same _ _ _

/-! ## A load then a store of one key, and a log entry, seen from the world -/

/-- The word at `key` after `SLOAD k; SSTORE k v` over `b`. -/
theorem getStorVal_afterStore {sevm : Sevm} {b : Devm} {k v key : B256} :
    (afterSstore sevm (afterSload sevm b k) k v).getStorVal sevm.currentTarget key =
      ((Devm.getStor b sevm.currentTarget).set k v).get key := by
  show (Devm.getStor _ _).get _ = _
  rw [afterSstore_getStor_self, afterSload_getStor]

theorem getStor_afterStore {sevm : Sevm} {b : Devm} {k v : B256} :
    Devm.getStor (afterSstore sevm (afterSload sevm b k) k v) sevm.currentTarget =
      (Devm.getStor b sevm.currentTarget).set k v := by
  rw [afterSstore_getStor_self, afterSload_getStor]

theorem getStor_afterStore_ne {sevm : Sevm} {b : Devm} {k v : B256} {a : Adr}
    (ha : a ≠ sevm.currentTarget) :
    Devm.getStor (afterSstore sevm (afterSload sevm b k) k v) a = Devm.getStor b a := by
  rw [afterSstore_getStor_ne _ _ _ _ _ (Ne.symm ha), afterSload_getStor]

theorem getStorVal_afterSload {sevm : Sevm} {b : Devm} {k : B256} {a : Adr} {x : B256} :
    (afterSload sevm b k).getStorVal a x = b.getStorVal a x := by
  show (Devm.getStor _ _).get _ = (Devm.getStor _ _).get _
  rw [afterSload_getStor]

theorem getStor_addLog (d : Devm) (L : Log) (a : Adr) :
    Devm.getStor (d.addLog L) a = Devm.getStor d a := rfl

/-- The state `RETURN` leaves keeps the base's storage. -/
theorem getStor_St_return (b : Devm) (S : List B256) (M : Mem) (G i n : Nat) (out : Bytes)
    (a : Adr) :
    Devm.getStor (((St b S M G).memRead i n).2.withOutput out) a = Devm.getStor b a := rfl

theorem logs_St_return (b : Devm) (S : List B256) (M : Mem) (G i n : Nat) (out : Bytes) :
    (((St b S M G).memRead i n).2.withOutput out).logs = b.logs := rfl

theorem output_St_return (b : Devm) (S : List B256) (M : Mem) (G i n : Nat) (out : Bytes) :
    (((St b S M G).memRead i n).2.withOutput out).output = out := rfl

theorem logs_addLog (d : Devm) (L : Log) : (d.addLog L).logs = d.logs ++ [L] := rfl

theorem logs_afterStore {sevm : Sevm} {b : Devm} {k v : B256} :
    (afterSstore sevm (afterSload sevm b k) k v).logs = b.logs := by
  rw [afterSstore_logs, afterSload_logs]

end Blanc.Lift
