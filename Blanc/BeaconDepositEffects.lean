import Blanc.BeaconDepositCode
import Blanc.BeaconDepositEncoding

/-!
# Beacon deposit compiled effects

The first executable correctness seam for the BeaconDeposit runtime: the
ERC-165 endpoint, its nonpayable guard, and the concrete selector route.  The
endpoint reads the high four bytes of argument word zero exactly as the runtime
does; no canonical-padding or exact-calldata-length premise is built into the
generic result.
-/

namespace Blanc.BeaconDeposit

open Jaune
open Jaune.Ninst Ninst

/-! ## The interface word actually observed by the runtime -/

def supportsInterfaceWord (word : B256) : Bool :=
  decide (word = erc165InterfaceId ∨ word = depositInterfaceId)

def supportsInterfaceArg (sevm : Sevm) : Bool :=
  supportsInterfaceWord (Sevm.argWord sevm 0 >>> 224)

@[simp] theorem supportsInterfaceWord_eq_true_iff (word : B256) :
    supportsInterfaceWord word = true ↔
      word = erc165InterfaceId ∨ word = depositInterfaceId := by
  simp [supportsInterfaceWord]

@[simp] theorem supportsInterfaceWord_eq_false_iff (word : B256) :
    supportsInterfaceWord word = false ↔
      word ≠ erc165InterfaceId ∧ word ≠ depositInterfaceId := by
  simp [supportsInterfaceWord]

@[simp] theorem supportsInterfaceArg_eq_true_iff (sevm : Sevm) :
    supportsInterfaceArg sevm = true ↔
      Sevm.argWord sevm 0 >>> 224 = erc165InterfaceId ∨
        Sevm.argWord sevm 0 >>> 224 = depositInterfaceId := by
  simp [supportsInterfaceArg]

@[simp] theorem supportsInterfaceArg_eq_false_iff (sevm : Sevm) :
    supportsInterfaceArg sevm = false ↔
      Sevm.argWord sevm 0 >>> 224 ≠ erc165InterfaceId ∧
        Sevm.argWord sevm 0 >>> 224 ≠ depositInterfaceId := by
  simp [supportsInterfaceArg]

@[simp] theorem supportsInterfaceWord_erc165 :
    supportsInterfaceWord erc165InterfaceId = true := by
  simp

@[simp] theorem supportsInterfaceWord_deposit :
    supportsInterfaceWord depositInterfaceId = true := by
  simp

theorem supportsInterfaceWord_other {word : B256}
    (herc165 : word ≠ erc165InterfaceId)
    (hdeposit : word ≠ depositInterfaceId) :
    supportsInterfaceWord word = false := by
  simp [herc165, hdeposit]

@[simp] theorem supportsInterfaceWord_ffffffff :
    supportsInterfaceWord (0xffffffff : B256) = false := by
  decide +kernel

private def supportsInterfaceResultWord (sevm : Sevm) : B256 :=
  B256.or
    (B256.eqCheck depositInterfaceId (Sevm.argWord sevm 0 >>> 224))
    (B256.eqCheck erc165InterfaceId (Sevm.argWord sevm 0 >>> 224))

private theorem supportsInterfaceWord_eqCheck_or (word : B256) :
    B256.or (B256.eqCheck depositInterfaceId word)
        (B256.eqCheck erc165InterfaceId word) =
      (if supportsInterfaceWord word then 1 else 0) := by
  by_cases herc : word = erc165InterfaceId
  · subst word
    simp only [supportsInterfaceWord, B256.eqCheck]
    decide +kernel
  · by_cases hdeposit : word = depositInterfaceId
    · subst word
      simp only [supportsInterfaceWord, B256.eqCheck]
      decide +kernel
    · have herc' : erc165InterfaceId ≠ word := Ne.symm herc
      have hdeposit' : depositInterfaceId ≠ word := Ne.symm hdeposit
      (simp [supportsInterfaceWord, B256.eqCheck, herc, hdeposit,
          herc', hdeposit'];
        decide +kernel)

def supportsInterfaceEndpointGas : Nat := 67

private lemma gasLeft_withOutput {devm : Devm} {out : Bytes} :
    (devm.withOutput out).gasLeft = devm.gasLeft := rfl

private lemma gasLeft_memRead_snd {devm : Devm} {i sz : Nat} :
    (devm.memRead i sz).2.gasLeft = devm.gasLeft := rfl

private def returnWordPre
    (base : Devm) (word : B256) (gas : Nat) : Devm :=
  base.setMach ⟨[], Mem.empty.write 0 word.toBytes, gas⟩

private theorem returnWord_runCompiled
    {fs : List Func} {sevm : Sevm} {base : Devm} {word : B256}
    {g G : Nat} (hgas : g = G + 5) :
    ∃ post,
      Func.RunCompiled fs sevm
        (returnWordPre base word g)
        (returnMemoryRange 0 32) post ∧
      post.gasLeft = G ∧
      Devm.output post = word.toBytes ∧
      Devm.WorldEq base post ∧
      post.logs = base.logs := by
  let M := Mem.empty.write 0 word.toBytes
  let retPre := base.setMach
    ⟨[(0 : B256), (32 : B256)], M, g - 5⟩
  let d := (retPre.setMach ⟨[], retPre.memory, g - 5⟩).memRead 0 32
  let post := d.2.withOutput word.toBytes
  refine ⟨post, ?_, ?_, rfl, ?_, rfl⟩
  · simp only [returnWordPre, returnMemoryRange, pushList]
    func_run (2) []
    simp only [List.map, prepend]
    change Func.RunCompiled fs sevm retPre Func.ret post
    have hext :
        retPre.extCost [⟨(0 : B256).toNat, (32 : B256).toNat⟩] = 0 := by
      change retPre.extCost [((0 : Nat), (32 : Nat))] = 0
      simpa only [retPre, M] using
        (Devm.extCost_word_word Mem.size_write_word)
    have hread :
        (retPre.setMach ⟨[], retPre.memory, g - 5⟩).memRead 0 32 =
          ⟨word.toBytes, d.2⟩ := by
      exact Prod.ext
        (Devm.memRead_word_fst
          (by simp only [Devm.memory_setMach, retPre, M]))
        rfl
    exact Func.runCompiled_ret_of (devm := retPre) (G := g - 5) (e := 0)
      (out := word.toBytes) (d' := d.2) rfl hext
      (by simp only [retPre, Devm.gasLeft_setMach, Nat.add_zero])
      hread
  · simp only [post, d, retPre, gasLeft_withOutput,
      gasLeft_memRead_snd, Devm.gasLeft_setMach]
    omega
  · exact ⟨rfl, rfl⟩

private theorem supportsInterfaceStoreReturn_runCompiled
    (fs : List Func) (sevm : Sevm) (base : Devm)
    (word : B256) (G : Nat) :
    ∃ post,
      Func.RunCompiled fs sevm
        (base.setMach ⟨[word], Mem.empty, G + 13⟩)
        (mstoreAt 0 +++ returnMemoryRange 0 32) post ∧
      post.gasLeft = G ∧
      Devm.output post = word.toBytes ∧
      Devm.WorldEq base post ∧
      post.logs = base.logs := by
  rcases returnWord_runCompiled (fs := fs) (sevm := sevm)
      (base := base) (word := word) (g := G + 5) (G := G) (by omega) with
    ⟨post, hreturn, hgas, houtput, hworld, hlogs⟩
  refine ⟨post, ?_, hgas, houtput, hworld, hlogs⟩
  have hzero : ((0 : B256) * 32).toNat = 0 := by decide +kernel
  have hboundary : G + 13 - 8 = G + 5 := by omega
  unfold mstoreAt
  func_run (2) [3]
  · exact Devm.extCost_empty_word
  · simpa only [hzero, hboundary, returnWordPre, prepend] using hreturn

private def supportsInterfaceBody : Func :=
  arg 0 +++ pushB256 224 ::: shr :::
  dup 0 ::: pushB256 erc165InterfaceId ::: eq ::: swap 0 :::
  pushB256 depositInterfaceId ::: eq ::: Ninst.or :::
  mstoreAt 0 +++ returnMemoryRange 0 32

private theorem supportsInterfaceBody_runCompiled
    (fs : List Func) (sevm : Sevm) (base : Devm) (G : Nat) :
    ∃ post,
      Func.RunCompiled fs sevm
        (base.setMach ⟨[], Mem.empty, G + 46⟩)
        supportsInterfaceBody post ∧
      post.gasLeft = G ∧
      Devm.output post = (supportsInterfaceResultWord sevm).toBytes ∧
      Devm.WorldEq base post ∧
      post.logs = base.logs := by
  rcases supportsInterfaceStoreReturn_runCompiled fs sevm base
      (supportsInterfaceResultWord sevm) G with
    ⟨post, hreturn, hgas, houtput, hworld, hlogs⟩
  refine ⟨post, ?_, hgas, houtput, hworld, hlogs⟩
  have hboundary : G + 46 - 33 = G + 13 := by omega
  have h224 : (224 : B256).toNat = 224 := by decide +kernel
  unfold supportsInterfaceBody arg cdl
  func_run (11) []
  simpa only [supportsInterfaceResultWord, hboundary, Sevm.argWord, h224]
    using hreturn

private theorem supportsInterfaceResultWord_eq (sevm : Sevm) :
    supportsInterfaceResultWord sevm =
      (if supportsInterfaceArg sevm then 1 else 0) := by
  unfold supportsInterfaceResultWord supportsInterfaceArg
  exact supportsInterfaceWord_eqCheck_or (Sevm.argWord sevm 0 >>> 224)

/-- The body accepts every in-bounds ABI head, including dirty low padding and
arbitrary trailing calldata, and returns the answer for the four bytes it
actually extracts. -/
theorem supportsInterfaceEndpoint_runCompiled
    (fs : List Func) (sevm : Sevm) (base : Devm) (G : Nat)
    (hdataLength : 36 ≤ sevm.data.length)
    (hdataBound : sevm.data.length < 2 ^ 256) :
    ∃ post,
      Func.RunCompiled fs sevm
        (base.setMach
          ⟨[], Mem.empty, G + supportsInterfaceEndpointGas⟩)
        supportsInterfaceEndpoint post ∧
      post.gasLeft = G ∧
      Devm.output post = abiBoolReturn (supportsInterfaceArg sevm) ∧
      Devm.WorldEq base post ∧
      post.logs = base.logs := by
  have hnotShort :
      B256.ltCheck sevm.data.length.toB256 36 = 0 := by
    simp only [B256.ltCheck]
    rw [if_neg]
    rw [B256.lt_iff_toNat_lt_toNat,
      B256.toNat_toB256_of_lt hdataBound,
      show (36 : B256).toNat = 36 by decide +kernel]
    omega
  rcases supportsInterfaceBody_runCompiled fs sevm base G with
    ⟨post, hbody, hgas, houtput, hworld, hlogs⟩
  refine ⟨post, ?_, hgas, ?_, hworld, hlogs⟩
  · have hboundary : G + 67 - 21 = G + 46 := by omega
    unfold supportsInterfaceEndpoint supportsInterfaceEndpointGas
    func_run (4) [0]
    simpa only [hboundary, supportsInterfaceBody] using hbody
  · calc
      post.output = (supportsInterfaceResultWord sevm).toBytes := houtput
      _ = abiBoolReturn (supportsInterfaceArg sevm) := by
        simp only [abiBoolReturn, supportsInterfaceResultWord_eq]

def supportsInterfaceEndpointShortGas : Nat := 26

theorem supportsInterfaceEndpoint_short_runCompiledTo
    {fs : List Func} {sevm : Sevm} {base : Devm} {G : Nat}
    (hshort : sevm.data.length < 36)
    (hroom : base.stack.length < 1023) :
    Func.RunCompiledTo fs sevm
      (base.setMach
        ⟨base.stack, base.memory, G + supportsInterfaceEndpointShortGas⟩)
      supportsInterfaceEndpoint
      (.error (.revert,
        (base.setMach ⟨base.stack, base.memory, G⟩).withOutput [])) := by
  have hlt : B256.ltCheck sevm.data.length.toB256 36 = 1 := by
    simp only [B256.ltCheck]
    rw [if_pos]
    rw [B256.lt_iff_toNat_lt_toNat,
      B256.toNat_toB256_of_lt (by omega),
      show (36 : B256).toNat = 36 by decide +kernel]
    exact hshort
  unfold supportsInterfaceEndpoint supportsInterfaceEndpointShortGas
  func_run (4) [1]
  all_goals try {
    simp only [Devm.stack_setMach, List.length_cons] at *
    omega }
  all_goals try omega
  exact Func.runCompiledTo_rev_func
    (devm := base.setMach
      ⟨base.stack, base.memory, G + 4⟩)
    (G := G)
    (by simp only [Devm.gasLeft_setMach, gBase])
    (by simp only [Devm.stack_setMach]; omega)

/-! ## The contract-local nonpayable wrapper -/

def nonpayableEndpointZeroGas : Nat := 15
def nonpayableEndpointRevertGas : Nat := 20

theorem nonpayableEndpoint_zero_runCompiled
    {fs : List Func} {sevm : Sevm} {base post : Devm}
    {body : Func} {G : Nat}
    (hvalue : sevm.value = 0)
    (hroom : base.stack.length < 1023)
    (hbody : Func.RunCompiled fs sevm
      (base.setMach ⟨base.stack, base.memory, G⟩) body post) :
    Func.RunCompiled fs sevm
      (base.setMach
        ⟨base.stack, base.memory, G + nonpayableEndpointZeroGas⟩)
      (nonpayableEndpoint body) post := by
  unfold nonpayableEndpoint nonpayableEndpointZeroGas
  func_run (1) []
  · simp only [Devm.stack_setMach]
    omega
  · rw [hvalue]
    func_run (1) []
    · simp only [Devm.stack_setMach, List.length_cons]
      omega
    · have hboundary : G + 15 - 15 = G := by omega
      simpa only [Devm.setMach_setMach, hboundary] using hbody

theorem nonpayableEndpoint_zero_runCompiledTo
    {fs : List Func} {sevm : Sevm} {base : Devm}
    {body : Func} {out : Execution} {G : Nat}
    (hvalue : sevm.value = 0)
    (hroom : base.stack.length < 1023)
    (hbody : Func.RunCompiledTo fs sevm
      (base.setMach ⟨base.stack, base.memory, G⟩) body out) :
    Func.RunCompiledTo fs sevm
      (base.setMach
        ⟨base.stack, base.memory, G + nonpayableEndpointZeroGas⟩)
      (nonpayableEndpoint body) out := by
  unfold nonpayableEndpoint nonpayableEndpointZeroGas
  func_run (1) []
  · simp only [Devm.stack_setMach]
    omega
  · rw [hvalue]
    func_run (1) []
    · simp only [Devm.stack_setMach, List.length_cons]
      omega
    · have hboundary : G + 15 - 15 = G := by omega
      simpa only [Devm.setMach_setMach, hboundary] using hbody

/-- Nonzero value is rejected before `body` can inspect calldata or world
state, with the exact empty-revert payload and gas decrement. -/
theorem nonpayableEndpoint_nonzero_runCompiledTo
    {fs : List Func} {sevm : Sevm} {base : Devm}
    {G : Nat} {body : Func}
    (hvalue : sevm.value ≠ 0)
    (hroom : base.stack.length < 1023) :
    Func.RunCompiledTo fs sevm
      (base.setMach
        ⟨base.stack, base.memory, G + nonpayableEndpointRevertGas⟩)
      (nonpayableEndpoint body)
      (.error (.revert,
        (base.setMach ⟨base.stack, base.memory, G⟩).withOutput [])) := by
  unfold nonpayableEndpoint nonpayableEndpointRevertGas
  func_run (1) []
  · simp only [Devm.stack_setMach]
    omega
  · refine Func.runCompiledTo_branch_succ (G := G + 4)
      hvalue rfl ?_ ?_ ?_
    · simp only [Devm.stack_setMach, List.length_cons]
      omega
    · simp only [Devm.gasLeft_setMach, gVerylow, gHigh, gJumpdest]
      omega
    · exact Func.runCompiledTo_rev_func
        (devm := base.setMach ⟨base.stack, base.memory, G + 4⟩)
        (G := G) (by simp only [Devm.gasLeft_setMach, gBase])
        (by simp only [Devm.stack_setMach]; exact hroom)

/-! ## The supports-interface selector path -/

def supportsInterfaceDispatchGas : Nat := 54

private def supportsInterfaceLeaf : Func :=
  pushB256 supportsInterfaceSelector ::: eq :::
    ((nonpayableEndpoint supportsInterfaceEndpoint) <?> Func.rev)

private def supportsInterfaceRightTree : DispatchTree :=
  .fork
    (.leaf depositSelector depositEndpoint)
    (.fork
      (.leaf getDepositCountSelector
        (nonpayableEndpoint getDepositCountEndpoint))
      (.leaf getDepositRootSelector
        (nonpayableEndpoint getDepositRootEndpoint)))

private def supportsInterfaceRootDispatch : Func :=
  dup 0 ::: pushB256 depositSelector ::: gt :::
    (supportsInterfaceLeaf <?> dispatch supportsInterfaceRightTree)

private def supportsInterfaceMain : Func :=
  fsig +++ supportsInterfaceRootDispatch

private theorem supportsInterfaceMain_eq :
    Func.main tree = supportsInterfaceMain := by
  rfl

private theorem supportsInterfaceLeaf_runCompiledTo
    {fs : List Func} {sevm : Sevm} {base : Devm}
    {out : Execution} {G : Nat}
    (hbody : Func.RunCompiledTo fs sevm
      (base.setMach ⟨[], Mem.empty, G⟩)
      (nonpayableEndpoint supportsInterfaceEndpoint) out) :
    Func.RunCompiledTo fs sevm
      (base.setMach
        ⟨[supportsInterfaceSelector], Mem.empty, G + 20⟩)
      supportsInterfaceLeaf out := by
  unfold supportsInterfaceLeaf
  have hpushCost :
      pushCost supportsInterfaceSelector.toBytes.sig = gVerylow := by
    rw [supportsInterfaceSelector_eq]
    decide +kernel
  have hpushGas :
      (base.setMach
        ⟨[supportsInterfaceSelector], Mem.empty, G + 20⟩).gasLeft =
          G + 17 + gVerylow := by
    simp only [Devm.gasLeft_setMach, gVerylow]
  have hpushRoom :
      (base.setMach
        ⟨[supportsInterfaceSelector], Mem.empty, G + 20⟩).stack.length <
          1024 := by
    simp only [Devm.stack_setMach, List.length_cons, List.length_nil]
    omega
  refine Func.RunCompiledTo.next
    (Ninst.runCompiled_pushB256 hpushCost hpushGas hpushRoom) ?_
  simp only [Devm.setMach_setMach, Devm.stack_setMach, Devm.memory_setMach]
  have heqGas : G + 17 = G + 14 + gVerylow := by
    simp only [gVerylow]
  refine Func.RunCompiledTo.next
    (Ninst.runCompiled_binary (r := .eq) (f := B256.eqCheck)
      (cost := gVerylow) (G := G + 14) (v := 1)
      (by rintro ⟨⟩) rfl rfl (by decide +kernel) heqGas
      (by decide)) ?_
  simp only [Devm.setMach_setMach]
  have hbranchRoom :
      (base.setMach ⟨[(1 : B256)], Mem.empty, G + 14⟩).stack.length <
        1024 := by
    simp only [Devm.stack_setMach, List.length_cons, List.length_nil]
    omega
  have hbranchGas :
      (base.setMach ⟨[(1 : B256)], Mem.empty, G + 14⟩).gasLeft =
        G + (gVerylow + gHigh + gJumpdest) := by
    simp only [Devm.gasLeft_setMach, gVerylow, gHigh, gJumpdest]
  exact Func.runCompiledTo_branch_succ (w := (1 : B256)) (s := [])
    (G := G) (by decide) rfl hbranchRoom hbranchGas hbody

private theorem supportsInterfaceLeaf_runCompiled
    {fs : List Func} {sevm : Sevm} {base post : Devm} {G : Nat}
    (hbody : Func.RunCompiled fs sevm
      (base.setMach ⟨[], Mem.empty, G⟩)
      (nonpayableEndpoint supportsInterfaceEndpoint) post) :
    Func.RunCompiled fs sevm
      (base.setMach
        ⟨[supportsInterfaceSelector], Mem.empty, G + 20⟩)
      supportsInterfaceLeaf post :=
  Func.RunCompiled.of_runCompiledTo_ok
    (supportsInterfaceLeaf_runCompiledTo
      (Func.RunCompiledTo.of_runCompiled hbody))

private theorem supportsInterfaceRootDispatch_runCompiledTo
    {fs : List Func} {sevm : Sevm} {base : Devm}
    {out : Execution} {G : Nat}
    (hleaf : Func.RunCompiledTo fs sevm
      (base.setMach
        ⟨[supportsInterfaceSelector], Mem.empty, G + 20⟩)
      supportsInterfaceLeaf out) :
    Func.RunCompiledTo fs sevm
      (base.setMach
        ⟨[supportsInterfaceSelector], Mem.empty, G + 43⟩)
      supportsInterfaceRootDispatch out := by
  unfold supportsInterfaceRootDispatch
  refine Func.RunCompiledTo.next
    (Ninst.runCompiled_dup (n := 0) (w := supportsInterfaceSelector)
      (G := G + 40) rfl
      (by simp only [Devm.gasLeft_setMach, gVerylow])
      (by
        simp only [Devm.stack_setMach, List.length_cons, List.length_nil]
        omega)) ?_
  simp only [Devm.setMach_setMach, Devm.stack_setMach, Devm.memory_setMach]
  have hpushCost : pushCost depositSelector.toBytes.sig = gVerylow := by
    rw [depositSelector_eq]
    decide +kernel
  refine Func.RunCompiledTo.next
    (Ninst.runCompiled_pushB256 (G := G + 37) hpushCost
      (by simp only [Devm.gasLeft_setMach, gVerylow])
      (by
        simp only [Devm.stack_setMach, List.length_cons, List.length_nil]
        omega)) ?_
  simp only [Devm.setMach_setMach, Devm.stack_setMach, Devm.memory_setMach]
  refine Func.RunCompiledTo.next
    (Ninst.runCompiled_binary (r := .gt) (f := B256.gtCheck)
      (cost := gVerylow) (G := G + 34) (v := 1)
      (by rintro ⟨⟩) rfl rfl (by
        rw [supportsInterfaceSelector_eq, depositSelector_eq]
        decide +kernel)
      (by simp only [Devm.gasLeft_setMach, gVerylow])
      (by
        simp only [List.length_cons, List.length_nil]
        omega)) ?_
  simp only [Devm.setMach_setMach]
  exact Func.runCompiledTo_branch_succ (w := (1 : B256))
    (s := [supportsInterfaceSelector]) (G := G + 20)
    (by decide) rfl
    (by
      simp only [Devm.stack_setMach, List.length_cons, List.length_nil]
      omega)
    (by simp only [Devm.gasLeft_setMach, gVerylow, gHigh, gJumpdest])
    (by
      simpa only [Devm.setMach_setMach, Devm.memory_setMach] using hleaf)

private theorem supportsInterfaceRootDispatch_runCompiled
    {fs : List Func} {sevm : Sevm} {base post : Devm} {G : Nat}
    (hleaf : Func.RunCompiled fs sevm
      (base.setMach
        ⟨[supportsInterfaceSelector], Mem.empty, G + 20⟩)
      supportsInterfaceLeaf post) :
    Func.RunCompiled fs sevm
      (base.setMach
        ⟨[supportsInterfaceSelector], Mem.empty, G + 43⟩)
      supportsInterfaceRootDispatch post :=
  Func.RunCompiled.of_runCompiledTo_ok
    (supportsInterfaceRootDispatch_runCompiledTo
      (Func.RunCompiledTo.of_runCompiled hleaf))

private theorem supportsInterfaceMain_runCompiledTo
    {fs : List Func} {sevm : Sevm} {base : Devm}
    {out : Execution} {G : Nat}
    (hselector : Sevm.selector sevm = supportsInterfaceSelector)
    (hroot : Func.RunCompiledTo fs sevm
      (base.setMach
        ⟨[supportsInterfaceSelector], Mem.empty, G + 43⟩)
      supportsInterfaceRootDispatch out) :
    Func.RunCompiledTo fs sevm
      (base.setMach ⟨[], Mem.empty, G + supportsInterfaceDispatchGas⟩)
      (Func.main tree) out := by
  rw [supportsInterfaceMain_eq]
  unfold supportsInterfaceMain supportsInterfaceDispatchGas fsig shiftRight cdl
  refine Func.RunCompiledTo.next
    (Ninst.runCompiled_pushB256 (c := gBase) (G := G + 52)
      pushCost_zero (by simp only [Devm.gasLeft_setMach, gBase])
      (by simp only [Devm.stack_setMach, List.length_nil]; omega)) ?_
  simp only [Devm.setMach_setMach, Devm.stack_setMach, Devm.memory_setMach]
  refine Func.RunCompiledTo.next
    (Ninst.runCompiled_calldataload (v := Sevm.dataWord sevm 0)
      (G := G + 49) rfl rfl
      (by simp only [Devm.gasLeft_setMach, gVerylow])
      (by decide)) ?_
  simp only [Devm.setMach_setMach, Devm.memory_setMach]
  have hpush224 : pushCost (224 : B256).toBytes.sig = gVerylow := by
    decide +kernel
  refine Func.RunCompiledTo.next
    (Ninst.runCompiled_pushB256 (G := G + 46) hpush224
      (by simp only [Devm.gasLeft_setMach, gVerylow])
      (by
        simp only [Devm.stack_setMach, List.length_cons, List.length_nil]
        omega)) ?_
  simp only [Devm.setMach_setMach, Devm.stack_setMach, Devm.memory_setMach]
  have h224 : (224 : B256).toNat = 224 := by decide +kernel
  have hselector' :
      Sevm.dataWord sevm 0 >>> (224 : B256).toNat =
        supportsInterfaceSelector := by
    rw [h224]
    exact hselector
  refine Func.RunCompiledTo.next
    (Ninst.runCompiled_binary (r := .shr)
      (f := fun x y => y >>> x.toNat)
      (cost := gVerylow) (G := G + 43)
      (v := supportsInterfaceSelector)
      (by rintro ⟨⟩) rfl rfl hselector'
      (by simp only [Devm.gasLeft_setMach, gVerylow])
      (by decide)) ?_
  simp only [Devm.setMach_setMach]
  simpa only [Devm.memory_setMach, prepend] using hroot

private theorem supportsInterfaceMain_runCompiled
    {fs : List Func} {sevm : Sevm} {base post : Devm} {G : Nat}
    (hselector : Sevm.selector sevm = supportsInterfaceSelector)
    (hroot : Func.RunCompiled fs sevm
      (base.setMach
        ⟨[supportsInterfaceSelector], Mem.empty, G + 43⟩)
      supportsInterfaceRootDispatch post) :
    Func.RunCompiled fs sevm
      (base.setMach ⟨[], Mem.empty, G + supportsInterfaceDispatchGas⟩)
      (Func.main tree) post :=
  Func.RunCompiled.of_runCompiledTo_ok
    (supportsInterfaceMain_runCompiledTo hselector
      (Func.RunCompiledTo.of_runCompiled hroot))

def supportsInterfaceRouteGas : Nat := 71

private theorem supportsInterfaceRoute_runCompiledTo
    {sevm : Sevm} {base : Devm} {out : Execution} {K : Nat}
    (hnonempty : sevm.data.length.toB256 ≠ 0)
    (hselector : Sevm.selector sevm = supportsInterfaceSelector)
    (hbody : Func.RunCompiledTo (runtime.main :: runtime.aux) sevm
      (base.setMach ⟨[], Mem.empty, K⟩)
      (nonpayableEndpoint supportsInterfaceEndpoint) out) :
    Prog.RunCompiledTo sevm
      (base.setMach
        ⟨[], Mem.empty, K + supportsInterfaceRouteGas⟩)
      runtime out := by
  have hleaf := supportsInterfaceLeaf_runCompiledTo (G := K) hbody
  have hroot := supportsInterfaceRootDispatch_runCompiledTo (G := K) hleaf
  have hmain := supportsInterfaceMain_runCompiledTo
    (G := K) hselector hroot
  refine Prog.runCompiledTo_intro
    (mid := base.setMach ⟨[], Mem.empty, K + 70⟩)
    (G := K + 70) ?_ rfl ?_
  · simp only [Devm.gasLeft_setMach, supportsInterfaceRouteGas,
      gJumpdest]
  · unfold runtime
    func_run (1) []
    exact Func.runCompiledTo_branch_succ
      (w := sevm.data.length.toB256) (s := []) (G := K + 54)
      hnonempty rfl
      (by
        simp only [Devm.stack_setMach, List.length_cons, List.length_nil]
        omega)
      (by
        simp only [Devm.gasLeft_setMach, gVerylow, gHigh, gJumpdest]
        omega)
      (by
        have hboundary : K + supportsInterfaceDispatchGas = K + 54 := by
          simp only [supportsInterfaceDispatchGas]
        simpa only [runtime, Devm.setMach_setMach, Devm.memory_setMach,
            hboundary] using hmain)

/-! ## The concrete public selector route -/

def supportsInterfaceRuntimeGas : Nat := 153

/-- The exact compiled public route for `supportsInterface(bytes4)`.  Its ABI
premises describe only what the executable route needs: an in-bounds first
argument word and a calldata length representable without `B256` wraparound.
The low 28 bytes of that word and any trailing calldata remain unrestricted. -/
theorem supportsInterface_runCompiled
    (sevm : Sevm) (base : Devm) (G : Nat)
    (hdataLength : 36 ≤ sevm.data.length)
    (hdataBound : sevm.data.length < 2 ^ 256)
    (hvalue : sevm.value = 0)
    (hselector : Sevm.selector sevm = supportsInterfaceSelector)
    (hcode : sevm.code.toList = code) :
    ∃ post,
      Prog.RunCompiled sevm
        (base.setMach
          ⟨[], Mem.empty, G + supportsInterfaceRuntimeGas⟩)
        runtime post ∧
      post.gasLeft = G ∧
      Devm.output post = abiBoolReturn (supportsInterfaceArg sevm) ∧
      Devm.WorldEq base post ∧
      post.logs = base.logs ∧
      some sevm.code.toList = Prog.compile runtime := by
  rcases supportsInterfaceEndpoint_runCompiled
      (runtime.main :: runtime.aux) sevm base G hdataLength hdataBound with
    ⟨post, hendpoint, hgas, houtput, hworld, hlogs⟩
  have hwrapped :
      Func.RunCompiled (runtime.main :: runtime.aux) sevm
        (base.setMach ⟨[], Mem.empty, G + 82⟩)
        (nonpayableEndpoint supportsInterfaceEndpoint) post := by
    have hboundary :
        G + supportsInterfaceEndpointGas + nonpayableEndpointZeroGas =
          G + 82 := by
      simp only [supportsInterfaceEndpointGas, nonpayableEndpointZeroGas]
    simpa only [Devm.setMach_setMach, Devm.stack_setMach,
        Devm.memory_setMach, hboundary] using
      (nonpayableEndpoint_zero_runCompiled
        (fs := runtime.main :: runtime.aux) (sevm := sevm)
        (base := base.setMach ⟨[], Mem.empty, base.gasLeft⟩) (post := post)
        (G := G + supportsInterfaceEndpointGas)
        (body := supportsInterfaceEndpoint) hvalue
        (by simp only [Devm.stack_setMach, List.length_nil]; omega)
        (by
          simpa only [Devm.setMach_setMach, Devm.stack_setMach,
            Devm.memory_setMach] using hendpoint))
  have hleaf := supportsInterfaceLeaf_runCompiled
    (G := G + 82) hwrapped
  have hroot := supportsInterfaceRootDispatch_runCompiled
    (G := G + 82) hleaf
  have hmain := supportsInterfaceMain_runCompiled
    (G := G + 82) hselector hroot
  have hlengthWordNe : sevm.data.length.toB256 ≠ 0 := by
    intro hzero
    have hnat := congrArg B256.toNat hzero
    rw [B256.toNat_toB256_of_lt hdataBound] at hnat
    simp only [B256.toNat_zero] at hnat
    omega
  refine ⟨post, ?_, hgas, houtput, hworld, hlogs, ?_⟩
  · refine Prog.runCompiled_intro
      (mid := base.setMach ⟨[], Mem.empty, G + 152⟩)
      (G := G + 152) ?_ rfl ?_
    · simp only [Devm.gasLeft_setMach, supportsInterfaceRuntimeGas,
        gJumpdest]
    · unfold runtime
      func_run (1) []
      exact Func.runCompiled_branch_succ
        (w := sevm.data.length.toB256) (s := []) (G := G + 136)
        hlengthWordNe rfl
        (by
          simp only [Devm.stack_setMach, List.length_cons, List.length_nil]
          omega)
        (by
          simp only [Devm.gasLeft_setMach, gVerylow, gHigh, gJumpdest]
          omega)
        (by
          have hboundary :
              G + 82 + supportsInterfaceDispatchGas = G + 136 := by
            simp only [supportsInterfaceDispatchGas]
          simpa only [runtime, Devm.setMach_setMach, Devm.memory_setMach,
              hboundary] using hmain)
  · rw [hcode, code_compile]

def supportsInterfaceNonzeroValueRuntimeGas : Nat := 91

/-- A value-carrying interface query is rejected before the endpoint can
inspect calldata beyond selector dispatch. -/
theorem supportsInterface_nonzero_value_runCompiledTo
    (sevm : Sevm) (base : Devm) (G : Nat)
    (hnonempty : sevm.data.length.toB256 ≠ 0)
    (hvalue : sevm.value ≠ 0)
    (hselector : Sevm.selector sevm = supportsInterfaceSelector)
    (hcode : sevm.code.toList = code) :
    Prog.RunCompiledTo sevm
      (base.setMach
        ⟨[], Mem.empty, G + supportsInterfaceNonzeroValueRuntimeGas⟩)
      runtime
      (.error (.revert,
        (base.setMach ⟨[], Mem.empty, G⟩).withOutput [])) ∧
    some sevm.code.toList = Prog.compile runtime := by
  let routeBase := base.setMach ⟨[], Mem.empty, base.gasLeft⟩
  have hbody := nonpayableEndpoint_nonzero_runCompiledTo
    (fs := runtime.main :: runtime.aux) (sevm := sevm)
    (base := routeBase) (G := G)
    (body := supportsInterfaceEndpoint) hvalue
    (by simp only [routeBase, Devm.stack_setMach, List.length_nil]; omega)
  have hroute := supportsInterfaceRoute_runCompiledTo
    (base := base) (K := G + nonpayableEndpointRevertGas)
    hnonempty hselector (by
      simpa only [routeBase, Devm.setMach_setMach, Devm.stack_setMach,
        Devm.memory_setMach] using hbody)
  constructor
  · have hboundary :
        G + nonpayableEndpointRevertGas + supportsInterfaceRouteGas =
          G + supportsInterfaceNonzeroValueRuntimeGas := by
      simp only [nonpayableEndpointRevertGas, supportsInterfaceRouteGas,
        supportsInterfaceNonzeroValueRuntimeGas]
    simpa only [hboundary] using hroute
  · rw [hcode, code_compile]

def supportsInterfaceShortCalldataRuntimeGas : Nat := 112

/-- With zero value, a selected query whose first ABI word is out of bounds
reaches the endpoint's empty revert after the nonpayable guard. -/
theorem supportsInterface_short_calldata_runCompiledTo
    (sevm : Sevm) (base : Devm) (G : Nat)
    (hnonempty : sevm.data.length.toB256 ≠ 0)
    (hshort : sevm.data.length < 36)
    (hvalue : sevm.value = 0)
    (hselector : Sevm.selector sevm = supportsInterfaceSelector)
    (hcode : sevm.code.toList = code) :
    Prog.RunCompiledTo sevm
      (base.setMach
        ⟨[], Mem.empty, G + supportsInterfaceShortCalldataRuntimeGas⟩)
      runtime
      (.error (.revert,
        (base.setMach ⟨[], Mem.empty, G⟩).withOutput [])) ∧
    some sevm.code.toList = Prog.compile runtime := by
  let routeBase := base.setMach ⟨[], Mem.empty, base.gasLeft⟩
  have hendpoint := supportsInterfaceEndpoint_short_runCompiledTo
    (fs := runtime.main :: runtime.aux) (sevm := sevm)
    (base := routeBase) (G := G) hshort
    (by simp only [routeBase, Devm.stack_setMach, List.length_nil]; omega)
  have hbody := nonpayableEndpoint_zero_runCompiledTo
    (fs := runtime.main :: runtime.aux) (sevm := sevm)
    (base := routeBase)
    (G := G + supportsInterfaceEndpointShortGas)
    (body := supportsInterfaceEndpoint) hvalue
    (by simp only [routeBase, Devm.stack_setMach, List.length_nil]; omega)
    (by
      simpa only [routeBase, Devm.setMach_setMach, Devm.stack_setMach,
        Devm.memory_setMach] using hendpoint)
  have hroute := supportsInterfaceRoute_runCompiledTo
    (base := base)
    (K := G + supportsInterfaceEndpointShortGas +
      nonpayableEndpointZeroGas)
    hnonempty hselector (by
      simpa only [routeBase, Devm.setMach_setMach, Devm.stack_setMach,
        Devm.memory_setMach] using hbody)
  constructor
  · have hboundary :
        G + supportsInterfaceEndpointShortGas + nonpayableEndpointZeroGas +
            supportsInterfaceRouteGas =
          G + supportsInterfaceShortCalldataRuntimeGas := by
      simp only [supportsInterfaceEndpointShortGas,
        nonpayableEndpointZeroGas, supportsInterfaceRouteGas,
        supportsInterfaceShortCalldataRuntimeGas]
    simpa only [hboundary] using hroute
  · rw [hcode, code_compile]

private theorem supportsInterfaceAnswer_runCompiled
    (sevm : Sevm) (base : Devm) (G : Nat) (answer : Bool)
    (hdataLength : 36 ≤ sevm.data.length)
    (hdataBound : sevm.data.length < 2 ^ 256)
    (hvalue : sevm.value = 0)
    (hselector : Sevm.selector sevm = supportsInterfaceSelector)
    (hcode : sevm.code.toList = code)
    (hanswer : supportsInterfaceArg sevm = answer) :
    ∃ post,
      Prog.RunCompiled sevm
        (base.setMach
          ⟨[], Mem.empty, G + supportsInterfaceRuntimeGas⟩)
        runtime post ∧
      post.gasLeft = G ∧
      Devm.output post = abiBoolReturn answer ∧
      Devm.WorldEq base post ∧
      post.logs = base.logs ∧
      some sevm.code.toList = Prog.compile runtime := by
  rcases supportsInterface_runCompiled sevm base G hdataLength hdataBound
      hvalue hselector hcode with
    ⟨post, hrun, hgas, houtput, hworld, hlogs, hcompiled⟩
  rw [hanswer] at houtput
  exact ⟨post, hrun, hgas, houtput, hworld, hlogs, hcompiled⟩

theorem supportsInterface_erc165_runCompiled
    (sevm : Sevm) (base : Devm) (G : Nat)
    (hdataLength : 36 ≤ sevm.data.length)
    (hdataBound : sevm.data.length < 2 ^ 256)
    (hvalue : sevm.value = 0)
    (hselector : Sevm.selector sevm = supportsInterfaceSelector)
    (harg : Sevm.argWord sevm 0 >>> 224 = erc165InterfaceId)
    (hcode : sevm.code.toList = code) :
    ∃ post,
      Prog.RunCompiled sevm
        (base.setMach
          ⟨[], Mem.empty, G + supportsInterfaceRuntimeGas⟩)
        runtime post ∧
      post.gasLeft = G ∧
      Devm.output post = abiBoolReturn true ∧
      Devm.WorldEq base post ∧
      post.logs = base.logs ∧
      some sevm.code.toList = Prog.compile runtime := by
  apply supportsInterfaceAnswer_runCompiled sevm base G true
    hdataLength hdataBound hvalue hselector hcode
  simp [supportsInterfaceArg, harg]

theorem supportsInterface_deposit_runCompiled
    (sevm : Sevm) (base : Devm) (G : Nat)
    (hdataLength : 36 ≤ sevm.data.length)
    (hdataBound : sevm.data.length < 2 ^ 256)
    (hvalue : sevm.value = 0)
    (hselector : Sevm.selector sevm = supportsInterfaceSelector)
    (harg : Sevm.argWord sevm 0 >>> 224 = depositInterfaceId)
    (hcode : sevm.code.toList = code) :
    ∃ post,
      Prog.RunCompiled sevm
        (base.setMach
          ⟨[], Mem.empty, G + supportsInterfaceRuntimeGas⟩)
        runtime post ∧
      post.gasLeft = G ∧
      Devm.output post = abiBoolReturn true ∧
      Devm.WorldEq base post ∧
      post.logs = base.logs ∧
      some sevm.code.toList = Prog.compile runtime := by
  apply supportsInterfaceAnswer_runCompiled sevm base G true
    hdataLength hdataBound hvalue hselector hcode
  simp [supportsInterfaceArg, harg]

theorem supportsInterface_other_runCompiled
    (sevm : Sevm) (base : Devm) (G : Nat)
    (hdataLength : 36 ≤ sevm.data.length)
    (hdataBound : sevm.data.length < 2 ^ 256)
    (hvalue : sevm.value = 0)
    (hselector : Sevm.selector sevm = supportsInterfaceSelector)
    (herc165 : Sevm.argWord sevm 0 >>> 224 ≠ erc165InterfaceId)
    (hdeposit : Sevm.argWord sevm 0 >>> 224 ≠ depositInterfaceId)
    (hcode : sevm.code.toList = code) :
    ∃ post,
      Prog.RunCompiled sevm
        (base.setMach
          ⟨[], Mem.empty, G + supportsInterfaceRuntimeGas⟩)
        runtime post ∧
      post.gasLeft = G ∧
      Devm.output post = abiBoolReturn false ∧
      Devm.WorldEq base post ∧
      post.logs = base.logs ∧
      some sevm.code.toList = Prog.compile runtime := by
  apply supportsInterfaceAnswer_runCompiled sevm base G false
    hdataLength hdataBound hvalue hselector hcode
  simp [supportsInterfaceArg, herc165, hdeposit]

theorem supportsInterface_ffffffff_runCompiled
    (sevm : Sevm) (base : Devm) (G : Nat)
    (hdataLength : 36 ≤ sevm.data.length)
    (hdataBound : sevm.data.length < 2 ^ 256)
    (hvalue : sevm.value = 0)
    (hselector : Sevm.selector sevm = supportsInterfaceSelector)
    (harg : Sevm.argWord sevm 0 >>> 224 = (0xffffffff : B256))
    (hcode : sevm.code.toList = code) :
    ∃ post,
      Prog.RunCompiled sevm
        (base.setMach
          ⟨[], Mem.empty, G + supportsInterfaceRuntimeGas⟩)
        runtime post ∧
      post.gasLeft = G ∧
      Devm.output post = abiBoolReturn false ∧
      Devm.WorldEq base post ∧
      post.logs = base.logs ∧
      some sevm.code.toList = Prog.compile runtime := by
  apply supportsInterfaceAnswer_runCompiled sevm base G false
    hdataLength hdataBound hvalue hselector hcode
  simp [supportsInterfaceArg, harg]

end Blanc.BeaconDeposit
