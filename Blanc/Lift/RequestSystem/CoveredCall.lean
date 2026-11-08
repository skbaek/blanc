import Blanc.Lift.RequestSystem.Output

/-!
# A request contract's system call on a covered fork

The same `SysPath` that `SysCall.spec` takes through Amsterdam's system call, taken through the covered
forks' (Prague onward, before Amsterdam): the frame is `SysPath.frame_runOn` on `coveredStores`, from the
real `initDevm` base, and the envelope is `processCheckedSystemTransaction_of_exec`
(`Blanc/SystemCallForward.lean`), which needs the runtime to be a canonical system contract
(`systemContracts`). There is no state gas on these forks, so every unit of the frame's charge is regular gas,
bounded by `SysPath.frameBoundOn` at a fresh set's `SSTORE` charge.

Nothing here says which storage is reachable: every statement is from any storage.
-/

namespace Blanc.Lift.RequestSystem

open Jaune

namespace SysPath

/-- The SYSTEM caller's message to `target` running the runtime on empty calldata. -/
abbrev coveredMsg (k : SysPath) (benv : Benv) (target : Adr) : Msg := systemCallMsg benv target k.code []

/-- The frame's exact charge on a covered fork. -/
abbrev coveredCost (k : SysPath) (benv : Benv) (target : Adr) : Nat :=
  k.frameCostOn (initDevm (k.coveredMsg benv target)) (coveredStores (initSevm (k.coveredMsg benv target)))

/-- The post frame of the system call on a covered fork, at the message's gas. -/
abbrev coveredPost (k : SysPath) (benv : Benv) (target : Adr) : Devm :=
  k.framePostOn (initDevm (k.coveredMsg benv target)) (coveredStores (initSevm (k.coveredMsg benv target)))
    (systemTransactionGas - k.coveredCost benv target)

variable {k : SysPath} {benv : Benv} {target : Adr}

/-- The frame's base is ready for its four stores: no error, no refund, every slot as the transaction
found it. -/
theorem coveredReady_base :
    CoveredReady (initSevm (k.coveredMsg benv target)) (initDevm (k.coveredMsg benv target)) [2, 3, 0, 1] where
  error := rfl
  refund := (Int.le_refl 0 :)
  clean := fun _ _ => by
    unfold SlotClean Devm.getOrigStorVal
    split
    · exact Or.inr rfl
    · exact Or.inl rfl

/-- **The checked system call on a covered fork, over the whole frame, from any storage.** -/
theorem covered_call (m : SysMemory k) (fork : CoveredFork benv.stat.fork)
    (member : (target, k.code) ∈ systemContracts) (installed : benv.state.getCode target = k.code)
    (room : k.frameBoundOn m.alloc (gasColdSload + gasStorageSet) + gCallStipend < systemTransactionGas) :
    processCheckedSystemTransaction benv target [] =
      .ok ((k.coveredPost benv target).state, systemCallOutput (k.coveredPost benv target)) := by
  let s := initSevm (k.coveredMsg benv target)
  let b := initDevm (k.coveredMsg benv target)
  have fork' : CoveredFork s.benvStat.fork := fork
  have laws := coveredStores_laws s
  have hle : k.frameCostOn b (coveredStores s) ≤ k.frameBoundOn m.alloc (gasColdSload + gasStorageSet) :=
    frameCost_leOn m laws b
  have r : CoveredReady s b [2, 3, 0, 1] := coveredReady_base
  have hG : gCallStipend < systemTransactionGas - k.frameCostOn b (coveredStores s) := by omega
  have run := k.frame_runOn (sevm := s) (b := b) (w := coveredStores s) (coveredStores_runs fork') laws
    fork'.rules_access fork'.rules_push0 fork'.rules_shifts rfl rfl rfl r hG
  rw [show systemTransactionGas - k.frameCostOn b (coveredStores s) + k.frameCostOn b (coveredStores s) =
    systemTransactionGas by omega,
    show St b [] .empty systemTransactionGas = b from rfl] at run
  have hexec : Nonempty (Exec 0 s b (.ok (k.coveredPost benv target))) :=
    lift_exact_noExec k.check k.jumps rfl k.noExec ⟨_, k.root, run⟩
  have hrun0 : exec ⟨0, s, b⟩ = .ok (k.coveredPost benv target) := (exec_iff_exec_eq _ _ _ _).mp hexec
  have hinit : initEvm (systemCallMsg benv target k.code []) = ⟨0, s, b⟩ := rfl
  have hrun : exec (initEvm (systemCallMsg benv target k.code [])) = .ok (k.coveredPost benv target) := by
    rw [hinit]
    exact hrun0
  have rSetup : CoveredReady s (setupBase s b) [2, 3, 0, 1] := laws.read (laws.read r 3) 2
  have rDrain := k.fold_readyOn laws (h := SysPath.rd s b 2) 0 (k.count s b).toNat (M := .empty) rSetup
  have rBooked := ready_bookOn laws rDrain (SysPath.rd s b 2) (k.count s b) (SysPath.rd s b 3)
  have rRead : CoveredReady s (k.excessReadOn b (coveredStores s)) [0, 1] :=
    laws.read (laws.read rBooked 0) 1
  have rEnd := laws.write (laws.write rRead (by decide) (k.excessStoredOn b (coveredStores s)))
    (by decide) (0 : B256)
  have clean : (k.coveredPost benv target).error = none := by
    rw [coveredPost, framePostOn, chargedRetPost_error]
    exact laws.error rEnd
  have nonneg : 0 ≤ (k.coveredPost benv target).refundCounter := by
    rw [coveredPost, framePostOn, chargedRetPost_refundCounter]
    exact laws.refund rEnd
  exact processCheckedSystemTransaction_of_exec (p := (target, k.code)) member fork installed hrun
    clean nonneg

/-- **The checked system call on a covered fork with its exact post state and a gas bound**, from any
storage. There is no state gas on these forks: the bound is on all the gas the call spends. -/
theorem covered_call_spec (m : SysMemory k) {B : Nat} (fork : CoveredFork benv.stat.fork)
    (member : (target, k.code) ∈ systemContracts) (installed : benv.state.getCode target = k.code)
    (hB : k.frameBoundOn m.alloc (gasColdSload + gasStorageSet) ≤ B)
    (room : B + gCallStipend < systemTransactionGas) :
    processCheckedSystemTransaction benv target [] =
      .ok (sysState k.shape benv.state target, systemCallOutput (k.coveredPost benv target)) ∧
    RegularGasWithin (k.coveredPost benv target).gasLeft B := by
  have hle : k.coveredCost benv target ≤ k.frameBoundOn m.alloc (gasColdSload + gasStorageSet) :=
    frameCost_leOn m (coveredStores_laws (initSevm (k.coveredMsg benv target)))
      (initDevm (k.coveredMsg benv target))
  have hcall := covered_call m fork member installed (by omega)
  have hstate : (k.coveredPost benv target).state = sysState k.shape benv.state target :=
    framePostOn_state (coveredStores_laws _) _ _
  rw [hstate] at hcall
  refine ⟨hcall, ?_⟩
  show systemTransactionGas - k.coveredCost benv target ≤ systemTransactionGas ∧
    systemTransactionGas - (systemTransactionGas - k.coveredCost benv target) ≤ B
  omega

end SysPath

/-- A canonical system contract's facts for its system call on the covered forks: its address, its
stated gas bound, and that the bound holds and leaves the stipend free of the 30,000,000 gas. -/
structure CoveredSysCall (k : SysPath) where
  memory : SysMemory k
  target : Adr
  bound : Nat
  member : (target, k.code) ∈ systemContracts
  bound_le : k.frameBoundOn memory.alloc (gasColdSload + gasStorageSet) ≤ bound
  room : bound + gCallStipend < systemTransactionGas

/-- **A request system call on a covered fork with its exact post state and a gas bound**, from any
storage. -/
theorem CoveredSysCall.spec {k : SysPath} (c : CoveredSysCall k) {benv : Benv}
    (fork : CoveredFork benv.stat.fork) (installed : benv.state.getCode c.target = k.code) :
    processCheckedSystemTransaction benv c.target [] =
      .ok (sysState k.shape benv.state c.target, systemCallOutput (k.coveredPost benv c.target)) ∧
    RegularGasWithin (k.coveredPost benv c.target).gasLeft c.bound :=
  SysPath.covered_call_spec c.memory fork c.member installed c.bound_le c.room

/-- What the call returns on a covered fork, from any storage. -/
theorem SysOutput.coveredPost_output {k : SysPath} {m : SysMemory k} (o : SysOutput k m) (benv : Benv)
    (target : Adr) :
    (k.coveredPost benv target).output =
      o.drained (storOf benv.state target) ((benv.state.getStor target).get 2)
        (drainCount k.shape.cap.word ((benv.state.getStor target).get 2)
          ((benv.state.getStor target).get 3)).toNat :=
  o.framePostOn_output _ _ _

end Blanc.Lift.RequestSystem
