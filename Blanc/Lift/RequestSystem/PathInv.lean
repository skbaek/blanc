import Blanc.Lift.RequestSystem.Output
import Blanc.Lift.RequestSystem.PlainExcess
import Blanc.Lift.RequestFee.Plain

/-!
# A request contract's system path, inverted

`Path.lean` walks the system path forward from storage it is given. This is the converse: every
*successful* run of the path, from any storage, any memory, any calldata and any gas, ends in `sysState`
and returns the records the loop wrote. The trees are the shared ones (`dispatchTree`, `sysSetup`,
`sysHeader`, `sysBook`, `plainExcess`, `sysFinal`), inverted node by node on the covered forks' `SLOAD` and
`SSTORE`; the record body and the excess arm enter as the runtime's own inversions (`SysPath.BodyInv`,
`SysPath.ExcessInv`); `excess_inv` is the second for the EIP-7002/EIP-7251 arm.

* `SysPath.frame_inv`: a successful system-arm run is non-static, its post state is `sysState`, and it
  returns the window over the loop's memory.
* `SysOutput.frame_inv_output`: on well-formed memory that window is `drained`, whatever the frame's memory
  held before, because each record's writes cover its window.
* `SysPath.exec_frame_inv`: the same for any successful execution of the bytes at the system caller.

Nothing here says which storage is reachable.
-/

namespace Blanc.Lift.RequestSystem

open Jaune
open RequestFee (PushWord)

variable {fs : List SFunc} {sevm : Sevm}

/-- `RETURN`, inverted: the world state is the base's. -/
theorem ri_return_state {i sz : B256} {b d : Devm} {S : List B256} {M : Mem} {G : Nat}
    (h : Linst.Run sevm (St b (i :: sz :: S) M G) .return_ (.ok d)) : d.state = b.state := by
  simp only [Linst.Run, Linst.run] at h
  rw [show (St b (i :: sz :: S) M G).popToNat = .ok (i.toNat, St b (sz :: S) M G) from rfl] at h
  simp only [Except.bind_ok] at h
  rw [show (St b (sz :: S) M G).popToNat = .ok (sz.toNat, St b S M G) from rfl] at h
  simp only [Except.bind_ok] at h
  rcases Except.bind_eq_ok h with ⟨s1, h1, h2⟩
  cases h2
  rw [Devm.eq_setGas_of_burn (Devm.burn_of_chargeGas h1)]
  rfl

/-- Two bases with one world state read the same storage. -/
theorem getStorVal_eq_of_state {b b' : Devm} (h : b'.state = b.state) (a : Adr) :
    b'.getStorVal a = b.getStorVal a :=
  funext fun key => (SysPath.getStorVal_of_state h key).trans (SysPath.getStorVal_of_state rfl key).symm

/-- A successful dispatch at the system caller reaches the system arm, on the same stack and memory. -/
theorem dispatch_system_inv {dest : PushWord} {user system : SFunc} {b : Devm} {M : Mem} {G : Nat}
    {o : Outcome} (caller : sevm.caller = systemAddress)
    (run : SFunc.Run fs sevm (St b [] M G) (dispatchTree dest user system) o) :
    ∃ G', SFunc.Run fs sevm (St b [] M G') system o := by
  have run := run.cut
  unfold dispatchTree at run
  winv 2
  rw [system_push] at run
  winv 1
  rw [adr_eqCheck, ite_eq_left caller] at run
  winv 1
  rcases ric_branch run with ⟨flag, _, _⟩ | ⟨_, G', run⟩
  · exact absurd flag (by decide)
  · exact ⟨G', run.uncut⟩

/-- A successful setup reads tail and head and enters the loop header at index 0 with the drain count. -/
theorem setup_inv (p : SysShape) {body : SFunc} {b : Devm} {M : Mem} {G : Nat} {o : Outcome}
    (fork : ShanghaiOnwards sevm.benvStat.fork) (h2 : fs[p.entryIdx]? = some (sysEntry p body))
    (run : SFunc.Run fs sevm (St b [] M G) (sysSetup p body) o) :
    ∃ b' G', b'.state = b.state ∧ b'.logs = b.logs ∧ SFunc.Run fs sevm
      (St b' [0, drainCount p.cap.word (b.getStorVal sevm.currentTarget 2) (b.getStorVal sevm.currentTarget 3),
        b.getStorVal sevm.currentTarget 2, b.getStorVal sevm.currentTarget 3] M G') (sysHeader p body) o := by
  have run := run.cut
  unfold sysSetup at run
  winv 2
  obtain ⟨_, hd, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_sload fork hd
  clear hd
  winv 1
  obtain ⟨_, hd, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_sload fork hd
  clear hd
  winv
  rw [afterSload_getStorVal, show Bytes.toB256 [0x02] = 2 from rfl,
    show Bytes.toB256 [0x03] = 3 from rfl] at run
  have hst : (afterSload sevm (afterSload sevm b 3) 2).state = b.state := by
    rw [RequestFee.afterSload_state, RequestFee.afterSload_state]
  have hlogs : (afterSload sevm (afterSload sevm b 3) 2).logs = b.logs := by
    rw [afterSload_logs, afterSload_logs]
  generalize b.getStorVal sevm.currentTarget 2 = h at run ⊢
  generalize b.getStorVal sevm.currentTarget 3 = t at run ⊢
  rcases ric_branchTo List.not_mem_nil h2 run with ⟨flag, _, run⟩ | ⟨flag, _, run⟩
  · have flag : B256.gtCheck p.cap.word (t - h) = 0 := flag
    winv 2 at run
    unfold sysEntry at run
    winv 2 at run
    have hdc : drainCount p.cap.word h t = p.cap.word := by
      unfold drainCount
      rw [ite_eq_right]
      intro hgt
      simp only [B256.gtCheck, hgt, ite_true] at flag
      exact absurd flag (by decide)
    exact ⟨_, _, hst, hlogs, by rw [hdc]; exact run.uncut⟩
  · have flag : B256.gtCheck p.cap.word (t - h) ≠ 0 := flag
    unfold sysEntry at run
    winv 2 at run
    have hdc : drainCount p.cap.word h t = t - h := by
      unfold drainCount
      rw [ite_eq_left]
      by_contra hgt
      exact flag (by simp only [B256.gtCheck, hgt, ite_false])
    exact ⟨_, _, hst, hlogs, by rw [hdc]; exact run.uncut⟩

/-- A successful header run either leaves the loop (index at the count) or runs the body. -/
theorem header_inv (p : SysShape) {body : SFunc} {b : Devm} {M : Mem} {G : Nat} {i c h t : B256}
    {o : Outcome} (run : SFunc.Run fs sevm (St b [i, c, h, t] M G) (sysHeader p body) o) :
    ∃ G', SFunc.Run fs sevm (St b [i, c, h, t] M G') (if i = c then sysBook p else body) o := by
  have run := run.cut
  unfold sysHeader at run
  winv
  by_cases same : i = c
  · rw [ite_eq_left same]
    rcases ric_branch run with ⟨flag, _, _⟩ | ⟨_, G', run⟩
    · simp only [B256.eqCheck, same, ite_true] at flag
      exact absurd flag (by decide)
    · exact ⟨G', run.uncut⟩
  · rw [ite_eq_right same]
    rcases ric_branch run with ⟨_, G', run⟩ | ⟨flag, _, _⟩
    · exact ⟨G', run.uncut⟩
    · simp only [B256.eqCheck, same, ite_false] at flag
      exact absurd rfl flag

/-- The pointer stores' effect on the world state: both pointers cleared when the drain reaches the tail,
else the head advanced. -/
def bookState (σ : State) (a : Adr) (h c t : B256) : State :=
  if h + c = t then (σ.setStorVal a 2 0).setStorVal a 3 0 else σ.setStorVal a 2 (h + c)

/-- A successful bookkeeping run stores the pointers, which needs a non-static frame, and enters the excess
update on the count. -/
theorem book_inv (p : SysShape) (fork : CoveredFork sevm.benvStat.fork) {q : Devm} {c h t : B256} {M : Mem}
    {G : Nat} {o : Outcome} (h3 : fs[p.excessIdx]? = some p.excessTree)
    (run : SFunc.Run fs sevm (St q [c, c, h, t] M G) (sysBook p) o) :
    sevm.isStatic = false ∧ ∃ q' G', q'.state = bookState q.state sevm.currentTarget h c t ∧
      q'.logs = q.logs ∧ SFunc.Run fs sevm (St q' [c] M G') p.excessTree o := by
  have run := run.cut
  unfold sysBook at run
  winv
  by_cases emptied : h + c = t
  · rcases ric_branch run with ⟨flag, _, _⟩ | ⟨_, _, run⟩
    · simp only [B256.eqCheck, emptied, ite_true] at flag
      exact absurd flag (by decide)
    · unfold sysEmptied at run
      winv at run
      obtain ⟨_, hd, run⟩ := ric_next run
      have static := ri_sstore_nonstatic fork hd
      obtain ⟨_, rfl⟩ := ri_sstore fork.shanghaiOnwards hd
      clear hd
      winv at run
      obtain ⟨_, hd, run⟩ := ric_next run
      obtain ⟨_, rfl⟩ := ri_sstore fork.shanghaiOnwards hd
      clear hd
      refine ⟨static, _, _, ?_, by rw [afterSstore_logs, afterSstore_logs], run.uncut⟩
      rw [afterSstore_state, afterSstore_state]
      simp only [bookState, emptied, ite_true]
      rfl
  · rcases ric_branch run with ⟨_, _, run⟩ | ⟨flag, _, _⟩
    · unfold sysAdvance at run
      winv at run
      obtain ⟨_, hd, run⟩ := ric_next run
      have static := ri_sstore_nonstatic fork hd
      obtain ⟨_, rfl⟩ := ri_sstore fork.shanghaiOnwards hd
      clear hd
      winv at run
      obtain ⟨_, run⟩ := ric_jump List.not_mem_nil h3 run
      refine ⟨static, _, _, ?_, afterSstore_logs _ _ _ _, run.uncut⟩
      rw [afterSstore_state]
      simp only [bookState, emptied, ite_false]
      rfl
    · have hne : t ≠ h + c := fun e => emptied e.symm
      simp only [B256.eqCheck, hne, ite_false] at flag
      exact absurd rfl flag

/-- A successful final run stores the excess and clears the count; it returns the window of `len` bytes per
drained record and emits no logs. -/
theorem final_inv (len : PushWord) (fork : ShanghaiOnwards sevm.benvStat.fork) {d post : Devm} {e c : B256}
    {M : Mem} {G : Nat} (run : SFunc.Run fs sevm (St d [e, c] M G) (sysFinal len) (.halted post)) :
    post.state = (d.state.setStorVal sevm.currentTarget 0 e).setStorVal sevm.currentTarget 1 0 ∧
      post.output = (M.read 0 (len.word * c).toNat).1 ∧ post.logs = d.logs := by
  have run := run.cut
  unfold sysFinal at run
  winv
  obtain ⟨_, hd, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_sstore fork hd
  clear hd
  winv
  obtain ⟨_, hd, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_sstore fork hd
  clear hd
  winv
  cases run with
  | last hret =>
    refine ⟨?_, (ri_return hret).1, ?_⟩
    · rw [ri_return_state hret, afterSstore_state, afterSstore_state]
      rfl
    · rw [(ri_return hret).2.2, afterSstore_logs, afterSstore_logs]

section Plain

variable (p : PlainWords)

/-- A successful comparison stores `count + excess - target` above the target, else zero. -/
theorem over_inv (fork : ShanghaiOnwards sevm.benvStat.fork) {d : Devm} {e c : B256} {M : Mem} {G : Nat}
    {o : Outcome} (hfinal : fs[p.finalIdx]? = some (sysFinal p.len))
    (run : SFunc.Run fs sevm (St d [e, c] M G) (plainOver p) o) :
    ∃ d' G', d'.state = d.state ∧ d'.logs = d.logs ∧ SFunc.Run fs sevm
      (St d' [if d.getStorVal sevm.currentTarget 1 + e > p.target.word then
          (d.getStorVal sevm.currentTarget 1 + e) - p.target.word else 0, c] M G') (sysFinal p.len) o := by
  have run := run.cut
  unfold plainOver at run
  winv
  obtain ⟨_, hd, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_sload fork hd
  clear hd
  winv
  rw [show Bytes.toB256 [0x01] = 1 from rfl] at run
  have hst : (afterSload sevm d 1).state = d.state := RequestFee.afterSload_state _ _ _
  have hlogs : (afterSload sevm d 1).logs = d.logs := afterSload_logs _ _ _
  generalize d.getStorVal sevm.currentTarget 1 = n at run ⊢
  by_cases hgt : n + e > p.target.word
  · rw [ite_eq_left hgt]
    rcases ric_branch run with ⟨flag, _, _⟩ | ⟨_, _, run⟩
    · simp only [B256.gtCheck, hgt, ite_true] at flag
      exact absurd flag (by decide)
    · unfold plainCarry at run
      winv 5 at run
      exact ⟨_, _, hst, hlogs, run.uncut⟩
  · rw [ite_eq_right hgt]
    rcases ric_branch run with ⟨_, _, run⟩ | ⟨flag, _, _⟩
    · unfold plainNoCarry at run
      winv at run
      obtain ⟨_, run⟩ := ric_jump List.not_mem_nil hfinal run
      exact ⟨_, _, hst, hlogs, run.uncut⟩
    · simp only [B256.gtCheck, hgt, ite_false] at flag
      exact absurd rfl flag

/-- A successful excess update reads slots 0 and 1 and enters the final stores on the stored excess. -/
theorem excess_inv (fork : ShanghaiOnwards sevm.benvStat.fork) {d : Devm} {c : B256} {M : Mem} {G : Nat}
    {o : Outcome} (hover : fs[p.overIdx]? = some (plainOver p))
    (hfinal : fs[p.finalIdx]? = some (sysFinal p.len))
    (run : SFunc.Run fs sevm (St d [c] M G) (plainExcess p) o) :
    ∃ d' G', d'.state = d.state ∧ d'.logs = d.logs ∧ SFunc.Run fs sevm
      (St d' [plainNext p.target.word (d.getStorVal sevm.currentTarget 0)
        (d.getStorVal sevm.currentTarget 1), c] M G') (sysFinal p.len) o := by
  have run := run.cut
  unfold plainExcess at run
  winv
  obtain ⟨_, hd, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_sload fork hd
  clear hd
  winv
  rw [show Bytes.toB256 [] = 0 from rfl, inhibitor_push] at run
  have hst : (afterSload sevm d 0).state = d.state := RequestFee.afterSload_state _ _ _
  have hlogs : (afterSload sevm d 0).logs = d.logs := afterSload_logs _ _ _
  have hn : (afterSload sevm d 0).getStorVal sevm.currentTarget 1 = d.getStorVal sevm.currentTarget 1 :=
    afterSload_getStorVal _ _ _ _ _
  generalize he : d.getStorVal sevm.currentTarget 0 = e at run ⊢
  have finish : ∀ {G'}, SFunc.Run fs sevm (St (afterSload sevm d 0) [plainBase e, c] M G') (plainOver p) o →
      ∃ d' G', d'.state = d.state ∧ d'.logs = d.logs ∧ SFunc.Run fs sevm
        (St d' [plainNext p.target.word e (d.getStorVal sevm.currentTarget 1), c] M G') (sysFinal p.len) o := by
    intro G' r
    obtain ⟨d', G'', hst', hlogs', r⟩ := over_inv p fork hfinal r
    rw [hn] at r
    exact ⟨d', G'', hst'.trans hst, hlogs'.trans hlogs, r⟩
  rcases ric_branchTo List.not_mem_nil hover run with ⟨flag, _, run⟩ | ⟨flag, _, run⟩
  · have hinh : B256.max = e := by
      by_contra hne
      simp only [B256.eqCheck, hne, ite_false] at flag
      exact absurd flag (by decide)
    have hbase : plainBase e = 0 := by simp only [plainBase, hinh, ite_true]
    winv 2 at run
    exact finish (by rw [hbase]; exact run.uncut)
  · have hinh : B256.max ≠ e := by
      intro heq
      simp only [B256.eqCheck, heq, ite_true] at flag
      exact flag (by decide)
    have hbase : plainBase e = e := by simp only [plainBase, hinh, ite_false]
    exact finish (by rw [hbase]; exact run.uncut)

end Plain

namespace SysPath

variable (k : SysPath)

/-- The memory the loop leaves, from the storage it reads: each record's writes, in order. -/
def memFold (rd : B256 → B256) (h : B256) : Nat → Nat → Mem → Mem
  | _, 0, M => M
  | index, n + 1, M => memFold rd h (index + 1) n ((k.stage rd h index.toB256).applyMemory M)

/-- The forward loop's memory is the memory fold over the storage it reads. -/
theorem fold_memory (sevm : Sevm) (h : B256) (index n : Nat) (b : Devm) (M : Mem) :
    (k.fold sevm h index n b M).memory = k.memFold (b.getStorVal sevm.currentTarget) h index n M := by
  induction n generalizing index b M with
  | zero => rfl
  | succ n ih =>
    show (k.fold sevm h (index + 1) n _ _).memory = _
    rw [ih, readsBase_getStorVal]
    rfl

/-- A runtime's record body, inverted: a successful run from the body keeps the world state and logs, writes the
record's stage over the storage it read, and re-enters the header at the next index. -/
def BodyInv (sevm : Sevm) : Prop :=
  ∀ {b : Devm} {M : Mem} {G : Nat} {i c h t : B256} {o : Outcome},
    SFunc.Run k.cert.prog sevm (St b [i, c, h, t] M G) k.body o →
    ∃ b' G', b'.state = b.state ∧ b'.logs = b.logs ∧ SFunc.Run k.cert.prog sevm
      (St b' [(1 : B256) + i, c, h, t] ((k.stage (b.getStorVal sevm.currentTarget) h i).applyMemory M) G')
      (sysHeader k.shape k.body) o

/-- A runtime's excess arm, inverted: a successful run keeps the world state and logs and enters the final stores on
the shape's stored excess. -/
def ExcessInv (sevm : Sevm) : Prop :=
  ∀ {d : Devm} {M : Mem} {G : Nat} {c : B256} {o : Outcome},
    SFunc.Run k.cert.prog sevm (St d [c] M G) k.shape.excessTree o →
    ∃ d' G', d'.state = d.state ∧ d'.logs = d.logs ∧ SFunc.Run k.cert.prog sevm
      (St d' [k.shape.next (d.getStorVal sevm.currentTarget 0) (d.getStorVal sevm.currentTarget 1), c] M G')
      (sysFinal k.shape.len) o

/-- **The loop, inverted**, by induction on the remaining count: a successful run from the header at `index`
reaches the bookkeeping on the same world state and logs, with the remaining records' writes applied. -/
theorem loop_inv (bodyInv : k.BodyInv sevm) {h t c : B256} (n : Nat) {index : Nat} {b : Devm} {M : Mem}
    {G : Nat} {o : Outcome} (bound : index + n = c.toNat)
    (run : SFunc.Run k.cert.prog sevm (St b [index.toB256, c, h, t] M G) (sysHeader k.shape k.body) o) :
    ∃ b' G', b'.state = b.state ∧ b'.logs = b.logs ∧ SFunc.Run k.cert.prog sevm
      (St b' [c, c, h, t] (k.memFold (b.getStorVal sevm.currentTarget) h index n M) G') (sysBook k.shape) o := by
  induction n generalizing index b M G with
  | zero =>
    have same : index.toB256 = c := by
      rw [show index = c.toNat by omega, toB256_toNat]
    obtain ⟨G', run⟩ := header_inv k.shape run
    rw [ite_eq_left same, same] at run
    exact ⟨b, G', rfl, rfl, run⟩
  | succ n ih =>
    have different : index.toB256 ≠ c := by
      intro eq
      have eqNat := congrArg B256.toNat eq
      rw [B256.toNat_toB256_of_lt (by have := B256.toNat_lt c; omega)] at eqNat
      omega
    obtain ⟨G', run⟩ := header_inv k.shape run
    rw [ite_eq_right different] at run
    obtain ⟨b', G'', hst, hlogs, run⟩ := bodyInv run
    rw [show (1 : B256) = Bytes.toB256 [0x01] from rfl,
      one_add_toB256 (by have := B256.toNat_lt c; omega)] at run
    obtain ⟨b'', G''', hst', hlogs', run⟩ := ih (index := index + 1) (by omega) run
    rw [getStorVal_eq_of_state hst] at run
    exact ⟨b'', G''', hst'.trans hst, hlogs'.trans hlogs, run⟩

variable {k}

/-- **The system arm, inverted.** A successful run of a runtime's dispatch at the system caller, from any
storage, memory and gas, on a covered fork: the frame is non-static, the post state is `sysState`, the output
is the window of `len` bytes per drained record over the loop's memory, and logs are unchanged. -/
theorem frame_inv (bodyInv : k.BodyInv sevm) (excessInv : k.ExcessInv sevm)
    (fork : CoveredFork sevm.benvStat.fork) (caller : sevm.caller = systemAddress) {b post : Devm} {M : Mem}
    {G : Nat} (run : SFunc.Run k.cert.prog sevm (St b [] M G)
      (dispatchTree k.systemDest k.user (sysSetup k.shape k.body)) (.halted post)) :
    sevm.isStatic = false ∧ post.state = sysState k.shape b.state sevm.currentTarget ∧
      post.output = ((k.memFold (rd sevm b) (rd sevm b 2) 0 (k.count sevm b).toNat M).read 0
        (k.outLen sevm b).toNat).1 ∧ post.logs = b.logs := by
  obtain ⟨_, run⟩ := dispatch_system_inv caller run
  obtain ⟨b1, _, hst1, hlogs1, run⟩ := setup_inv k.shape fork.shanghaiOnwards k.entry run
  obtain ⟨b2, _, hst2, hlogs2, run⟩ := k.loop_inv bodyInv (k.count sevm b).toNat (index := 0) (Nat.zero_add _) run
  rw [getStorVal_eq_of_state hst1] at run
  obtain ⟨static, b3, _, hst3, hlogs3, run⟩ := book_inv k.shape fork k.excessEntry run
  obtain ⟨b4, _, hst4, hlogs4, run⟩ := excessInv run
  obtain ⟨hstate, hout, hlogs⟩ := final_inv k.shape.len fork.shanghaiOnwards run
  refine ⟨static, ?_, hout, ?_⟩
  · have h01 : ∀ key : B256, key.toNat ≤ 1 →
        b3.getStorVal sevm.currentTarget key = b.getStorVal sevm.currentTarget key := by
      intro key hkey
      rw [SysPath.getStorVal_of_state hst3, hst2, hst1, bookState]
      have hne : ∀ x : B256, 2 ≤ x.toNat → x ≠ key := fun x hx e => by rw [e] at hx; omega
      split
      · rw [State.getStor_setStorVal_self, Stor.get_set_ite, ite_eq_right (hne 3 (by decide)),
          State.getStor_setStorVal_self, Stor.get_set_ite, ite_eq_right (hne 2 (by decide))]
        rfl
      · rw [State.getStor_setStorVal_self, Stor.get_set_ite, ite_eq_right (hne 2 (by decide))]
        rfl
    rw [hstate, hst4, hst3, hst2, hst1, h01 0 (by decide), h01 1 (by decide)]
    rfl
  · exact hlogs.trans (hlogs4.trans (hlogs3.trans (hlogs2.trans hlogs1)))

/-- **Any successful execution of a system-path runtime's bytes at the system caller**, from an empty
stack, ends as `frame_inv` says. -/
theorem exec_frame_inv (bodyInv : k.BodyInv sevm) (excessInv : k.ExcessInv sevm)
    (hcode : sevm.code = k.code) (fork : CoveredFork sevm.benvStat.fork)
    (caller : sevm.caller = systemAddress) {pre post : Devm} (stack : pre.stack = [])
    (exec : Exec 0 sevm pre (.ok post)) :
    sevm.isStatic = false ∧ post.state = sysState k.shape pre.state sevm.currentTarget ∧
      post.output = ((k.memFold (rd sevm pre) (rd sevm pre 2) 0 (k.count sevm pre).toNat pre.memory).read 0
        (k.outLen sevm pre).toNat).1 ∧ post.logs = pre.logs := by
  obtain ⟨f, hf, run⟩ := lift_sound_noExec k.check hcode k.noExec exec
  rw [k.root] at hf
  cases hf
  rw [St.self stack rfl] at run
  exact frame_inv bodyInv excessInv fork caller run

end SysPath

/-- **What a successful system frame returns**, on well-formed memory: the drained records, whatever the
memory held before, since each record's writes cover its window. -/
theorem SysOutput.frame_inv_output {k : SysPath} {m : SysMemory k} (o : SysOutput k m) (sevm : Sevm)
    (b : Devm) {M : Mem} (wf : Mem.Wf M) :
    ((k.memFold (SysPath.rd sevm b) (SysPath.rd sevm b 2) 0 (k.count sevm b).toNat M).read 0
        (k.outLen sevm b).toNat).1 =
      o.drained (SysPath.rd sevm b) (SysPath.rd sevm b 2) (k.count sevm b).toNat := by
  obtain ⟨final, hr, hs⟩ := o.fold_image (sevm := sevm) (h := SysPath.rd sevm b 2)
    (k.count sevm b).toNat (index := 0) (b := b) (M := M) (image := M.data.toList)
    rfl wf (Mem.reads_data M) (by have := k.count_le sevm b; omega) (by
      simp only [Nat.mul_zero]
      rfl)
  rw [← k.fold_memory, hr.read, SysOutput.outLen_toNat (m := m)]
  simpa only [Nat.zero_add] using hs

end Blanc.Lift.RequestSystem
