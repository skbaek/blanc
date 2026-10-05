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

theorem rx_number (hroom : S.length < 1024)
    (k : SFunc.RunExact fs sevm
      (St b (sevm.benvStat.number.toB256 :: S) M G) f o) :
    SFunc.RunExact fs sevm (St b S M (G + 2)) (.next (.reg .number) f) o :=
  .next (Ninst.runCompiled_pushItem (devm := St b S M (G + 2)) (r := .number)
    (x := sevm.benvStat.number.toB256) (G := G) (cost := gBase)
    (by rintro ⟨⟩) rfl rfl hroom) k

theorem rx_timestamp (hroom : S.length < 1024)
    (k : SFunc.RunExact fs sevm
      (St b (sevm.benvStat.time :: S) M G) f o) :
    SFunc.RunExact fs sevm (St b S M (G + 2)) (.next (.reg .timestamp) f) o :=
  .next (Ninst.runCompiled_pushItem (devm := St b S M (G + 2)) (r := .timestamp)
    (x := sevm.benvStat.time) (G := G) (cost := gBase)
    (by rintro ⟨⟩) rfl rfl hroom) k

/-- `CALLER`, inverted. -/
theorem ri_caller {d : Devm}
    (h : Ninst.Run sevm (St b S M G) (.reg .caller) d) :
    ∃ G', d = St b (sevm.caller.toB256 :: S) M G' := by
  have hp := of_run_caller h
  have hs : d.stack = sevm.caller.toB256 :: S := by
    have := hp.stack
    simpa only [Stack.Push, Split, St.stack, List.cons_append, List.nil_append] using this
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

/-! ## `SLT`, `TIMESTAMP`, `LOG2`, `TLOAD`, `TSTORE` inverted

(Hoisted from the deployed Lido CircuitBreaker walks.) -/

/-- `SLT`, inverted, value forgotten. -/
theorem ri_slt {x y : B256} {d : Devm}
    (h : Ninst.Run sevm (St b (x :: y :: S) M G) (.reg .slt) d) :
    ∃ z G', d = St b (z :: S) M G' := by
  rcases of_run_reg h with ⟨pc, run⟩
  simp only [Rinst.run, Rinst.runCore] at run
  exact ⟨_, St.of_diff (Devm.diffBurn_of_applyBinary run)⟩

/-- The actual header timestamp, with its fixed base charge. -/
theorem rx_timestamp (hroom : S.length < 1024)
    (k : SFunc.RunExact fs sevm (St b (sevm.benvStat.time :: S) M G) f o) :
    SFunc.RunExact fs sevm (St b S M (G + 2)) (.next (.reg .timestamp) f) o :=
  .next (Ninst.runCompiled_pushItem (devm := St b S M (G + 2)) (G := G) (cost := gBase)
    (by rintro ⟨⟩) rfl rfl hroom) k

/-- `TIMESTAMP`, inverted. -/
theorem ri_timestamp {d : Devm}
    (h : Ninst.Run sevm (St b S M G) (.reg .timestamp) d) :
    ∃ G', d = St b (sevm.benvStat.time :: S) M G' := by
  rcases of_run_reg h with ⟨pc, run⟩
  simp only [Rinst.run, Rinst.runCore] at run
  have hp := Devm.pushBurn_of_pushItem run
  have hs : d.stack = sevm.benvStat.time :: S := by
    simpa only [Stack.Push, Split, St.stack, List.cons_append, List.nil_append] using hp.stack
  have e := St.of_stackRel hp
  rw [hs] at e
  exact ⟨_, e⟩

/-- `LOG2` exposes its exact added log and actual read-expanded memory. -/
theorem ri_log2_post {i sz t1 t2 : B256} {d : Devm}
    (h : Ninst.Run sevm (St b (i :: sz :: t1 :: t2 :: S) M G) (.reg (.log 2)) d) :
    ∃ G', d = St
      (b.addLog ⟨sevm.currentTarget, [t1, t2], (M.read i.toNat sz.toNat).1⟩) S
      (M.read i.toNat sz.toNat).2 G' := by
  rcases of_run_reg h with ⟨pc, run⟩
  simp only [Rinst.run, Rinst.runCore] at run
  rw [show (St b (i :: sz :: t1 :: t2 :: S) M G).popToNat =
    .ok (i.toNat, St b (sz :: t1 :: t2 :: S) M G) from rfl] at run
  simp only [Except.bind_ok] at run
  rw [show (St b (sz :: t1 :: t2 :: S) M G).popToNat =
    .ok (sz.toNat, St b (t1 :: t2 :: S) M G) from rfl] at run
  simp only [Except.bind_ok] at run
  rw [show (St b (t1 :: t2 :: S) M G).popN ((2 : Fin 5) : Nat) =
    .ok ([t1, t2], St b S M G) from rfl] at run
  simp only [Except.bind_ok] at run
  rcases Except.bind_eq_ok run with ⟨s1, h1, h2⟩
  rcases Except.bind_eq_ok h2 with ⟨_, -, h3⟩
  cases h3
  have e1 := Devm.eq_setGas_of_burn (Devm.burn_of_chargeGas h1)
  refine ⟨s1.gasLeft, ?_⟩
  rw [e1]
  rfl

/-- Compatibility projection that forgets the new log and memory image. -/
theorem ri_log2 {i sz t1 t2 : B256} {d : Devm}
    (h : Ninst.Run sevm (St b (i :: sz :: t1 :: t2 :: S) M G) (.reg (.log 2)) d) :
    ∃ b' M' G', d = St b' S M' G' := by
  obtain ⟨gas, post⟩ := ri_log2_post h
  exact ⟨_, _, gas, post⟩

/-- `TLOAD`, inverted. -/
theorem ri_tload {k : B256} {d : Devm}
    (h : Ninst.Run sevm (St b (k :: S) M G) (.reg .tload) d) :
    ∃ G', d = St b (b.getTransVal sevm.currentTarget k :: S) M G' := by
  rcases of_run_reg h with ⟨pc, run⟩
  simp only [Rinst.run, Rinst.runCore] at run
  rw [show (St b (k :: S) M G).pop = .ok (k, St b S M G) from rfl] at run
  simp only [Except.bind_ok] at run
  have hp := Devm.pushBurn_of_pushItem run
  have hs : d.stack = b.getTransVal sevm.currentTarget k :: S := by
    have h2 := hp.stack
    simp only [Stack.Push, Split, List.cons_append, List.nil_append] at h2
    exact h2
  have e := St.of_stackRel hp
  rw [hs] at e
  exact ⟨_, e⟩

/-- `TSTORE`, inverted (no state-gas dimension under a covered fork). -/
theorem ri_tstore {k v : B256} {d : Devm} (hfork : CoveredFork sevm.benvStat.fork)
    (h : Ninst.Run sevm (St b (k :: v :: S) M G) (.reg .tstore) d) :
    ∃ G', d = St (b.setTransVal sevm.currentTarget k v) S M G' := by
  rcases of_run_reg h with ⟨pc, run⟩
  simp only [Rinst.run, Rinst.runCore, hfork.rules_stateGas_none] at run
  rw [show (St b (k :: v :: S) M G).pop = .ok (k, St b (v :: S) M G) from rfl] at run
  simp only [Except.bind_ok] at run
  rw [show (St b (v :: S) M G).pop = .ok (v, St b S M G) from rfl] at run
  simp only [Except.bind_ok] at run
  rcases Except.bind_eq_ok run with ⟨s1, h1, run1⟩
  rcases Except.bind_eq_ok run1 with ⟨_, -, h2⟩
  cases h2
  have e1 := Devm.eq_setGas_of_burn (Devm.burn_of_chargeGas h1)
  refine ⟨s1.gasLeft, ?_⟩
  rw [e1]
  rfl

theorem getStor_setTransVal (d : Devm) (a : Adr) (k v : B256) :
    Devm.getStor (d.setTransVal a k v) = Devm.getStor d := rfl

theorem getCode_setTransVal (d : Devm) (a : Adr) (k v : B256) :
    Devm.getCode (d.setTransVal a k v) = Devm.getCode d := rfl

end Steps

/-- Every memory reads as its own backing array. -/
theorem Mem.reads_data (μ : Mem) : Mem.Reads μ μ.data.toList := by
  intro index
  by_cases bound : index < μ.data.size <;>
    simp only [Array.getD, bound, ↓reduceDIte, Array.getInternal_eq_getElem, List.getD_eq_getElem?_getD, Array.length_toList, getElem?_pos, Array.getElem_toList, Option.getD_some, not_false_eq_true, getElem?_neg, Option.getD_none]

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

/-- A log leaves every account unchanged. -/
theorem getAcct_addLog (d : Devm) (L : Log) (a : Adr) :
    (d.addLog L).getAcct a = d.getAcct a := rfl

/-- A log leaves the enclosing output field unchanged. -/
theorem output_addLog (d : Devm) (L : Log) :
    (d.addLog L).output = d.output := rfl

theorem logs_addLog (d : Devm) (L : Log) : (d.addLog L).logs = d.logs ++ [L] := rfl

theorem logs_afterStore {sevm : Sevm} {b : Devm} {k v : B256} :
    (afterSstore sevm (afterSload sevm b k) k v).logs = b.logs := by
  rw [afterSstore_logs, afterSload_logs]

/-! ## Storage chains of the executing contract

(Hoisted from the deployed Lido CircuitBreaker `setPauser` walks.) -/

/-- `b'` agrees with `b` except in the contract's own storage, which is `s`
(access sets may differ): every other account's storage and the log list are
unchanged. -/
structure StorStep (sevm : Sevm) (b b' : Devm) (s : Stor) : Prop where
  self : Devm.getStor b' sevm.currentTarget = s
  other : ∀ a, a ≠ sevm.currentTarget → Devm.getStor b' a = Devm.getStor b a
  logs : b'.logs = b.logs

theorem getStorVal_eq_getStor (d : Devm) (a : Adr) (k : B256) :
    d.getStorVal a k = (Devm.getStor d a).get k := rfl

/-- Any chain of selected loads and stores is a `StorStep` from its base, with
the contract storage read off the chain. -/
theorem StorStep.of_getStor {sevm : Sevm} {b b' : Devm}
    (other : ∀ a, a ≠ sevm.currentTarget → Devm.getStor b' a = Devm.getStor b a)
    (logs : b'.logs = b.logs) :
    StorStep sevm b b' (Devm.getStor b' sevm.currentTarget) :=
  ⟨rfl, other, logs⟩

theorem StorStep.refl (sevm : Sevm) (b : Devm) :
    StorStep sevm b b (Devm.getStor b sevm.currentTarget) :=
  ⟨rfl, fun _ _ => rfl, rfl⟩

theorem StorStep.getStorVal {sevm : Sevm} {b b' : Devm} {s : Stor} (h : StorStep sevm b b' s)
    (k : B256) : b'.getStorVal sevm.currentTarget k = s.get k := by
  show (Devm.getStor b' sevm.currentTarget).get k = _
  rw [h.self]

theorem StorStep.sload {sevm : Sevm} {b b' : Devm} {s : Stor} (h : StorStep sevm b b' s)
    (k : B256) : StorStep sevm b (afterSload sevm b' k) s :=
  ⟨by rw [afterSload_getStor, h.self],
   fun a ha => by rw [afterSload_getStor, h.other a ha],
   by rw [afterSload_logs, h.logs]⟩

theorem StorStep.sstore {sevm : Sevm} {b b' : Devm} {s : Stor} (h : StorStep sevm b b' s)
    (k v : B256) : StorStep sevm b (afterSstore sevm b' k v) (s.set k v) :=
  ⟨by rw [afterSstore_getStor_self, h.self],
   fun a ha => by rw [afterSstore_getStor_ne _ _ _ _ _ (Ne.symm ha), h.other a ha],
   by rw [afterSstore_logs, h.logs]⟩

theorem StorStep.congr {sevm : Sevm} {b b' : Devm} {s s' : Stor} (h : StorStep sevm b b' s)
    (e : s = s') : StorStep sevm b b' s' :=
  e ▸ h

theorem StorStep.trans {sevm : Sevm} {b b' b'' : Devm} {s s' : Stor}
    (h : StorStep sevm b b' s) (h' : StorStep sevm b' b'' s') : StorStep sevm b b'' s' :=
  ⟨h'.self, fun a ha => by rw [h'.other a ha, h.other a ha], by rw [h'.logs, h.logs]⟩

end Blanc.Lift
