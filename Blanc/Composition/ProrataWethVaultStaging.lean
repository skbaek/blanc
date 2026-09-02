import Blanc.CompiledWalkInversion
import Blanc.Composition.ProrataWethVaultEffects
import Blanc.Ladder

/-!
# Source staging and checked WETH returns for the PRORATA vault

The boundary module identifies a retained child from an already pinned CALL
window.  This module discharges that pin from the vault's own source.  Its
straight-line prefixes write the three permitted selectors and their exact ABI
words, derive the CALL-family operand stacks, and leave no target behaviour in
the premises.

The second half follows the source checks after the crossing.  A successful
outer walk first proves that the actual CALL flag is nonzero.  Only after that
flag is refined to the EVM's canonical `1` is the copied return window used to
prove the exact 32-byte result (and, for mutations, canonical Boolean `true`).
-/

namespace Blanc.Composition.ProrataWethVault

open Jaune
open Jaune.Ninst Ninst

namespace Source

/-! ## The source prefixes that end immediately before the crossing -/

def balanceOfStaging : Line :=
  [pushB256 Blanc.ProrataWethVault.wethBalanceOfSelector] ++ mstoreAt 0 ++
  [address] ++ mstoreAt 1 ++
  pushList [32, 0, 36, 28] ++
  [pushB256 Blanc.ProrataWethVault.assetAddress, gas]

def transferFromStaging (assetsWord : B256) : Line :=
  [pushB256 Blanc.ProrataWethVault.wethTransferFromSelector] ++ mstoreAt 0 ++
  [caller] ++ mstoreAt 1 ++
  [address] ++ mstoreAt 2 ++
  Blanc.ProrataWethVault.loadWord assetsWord ++ mstoreAt 3 ++
  pushList [32, 0, 100, 28, 0] ++
  [pushB256 Blanc.ProrataWethVault.assetAddress, gas]

def transferStaging (receiverWord assetsWord : B256) : Line :=
  [pushB256 Blanc.ProrataWethVault.wethTransferSelector] ++ mstoreAt 0 ++
  Blanc.ProrataWethVault.loadWord receiverWord ++ mstoreAt 1 ++
  Blanc.ProrataWethVault.loadWord assetsWord ++ mstoreAt 2 ++
  pushList [32, 0, 68, 28, 0] ++
  [pushB256 Blanc.ProrataWethVault.assetAddress, gas]

/-! ## Whole-source external-call closure -/

private def lineCodeEndsWith (whole suffix : Line) : Bool :=
  let wholeCode := whole.flatMap Ninst.toBytes
  let suffixCode := suffix.flatMap Ninst.toBytes
  decide (wholeCode.drop (wholeCode.length - suffixCode.length) = suffixCode)

/-- Scan one complete source body, on both branch arms, and accept an external
instruction only when the instructions immediately before it are one of the
three vault call forms (with the inbound/outbound amount in its operation or
quote word). Internal Blanc table calls are checked separately when their body
appears in the program table. -/
private def exactWethSourceBody (history : Line) : Func → Bool
  | .branch left right =>
      exactWethSourceBody history left && exactWethSourceBody history right
  | .last _ => true
  | .call _ => true
  | .next instruction tail =>
      let allowed :=
        match instruction with
        | .exec .statcall => lineCodeEndsWith history balanceOfStaging
        | .exec .call =>
            lineCodeEndsWith history
                (transferFromStaging Blanc.ProrataWethVault.amountWord) ||
              lineCodeEndsWith history
                (transferFromStaging Blanc.ProrataWethVault.quoteWord) ||
              lineCodeEndsWith history
                (transferStaging Blanc.ProrataWethVault.receiverWord
                  Blanc.ProrataWethVault.amountWord) ||
              lineCodeEndsWith history
                (transferStaging Blanc.ProrataWethVault.receiverWord
                  Blanc.ProrataWethVault.quoteWord)
        | .exec _ => false
        | _ => true
      allowed && exactWethSourceBody (history ++ [instruction]) tail

/-- Executable whole-program closure for the exact vault source. It scans the
main dispatcher, every auxiliary function, every branch arm, and rejects any
external opcode whose immediate staging is not one of the exact configured
WETH query or transfer forms above. -/
def exactWethSourceClosure (program : Prog) : Bool :=
  (program.main :: program.aux).all fun body =>
    exactWethSourceBody [] body

/-- The exact vault has no external source path beyond its configured WETH
`balanceOf`, `transferFrom`, and `transfer` stagings. In particular, adding an
`approve`, `withdraw`, computed-selector, wrong-target, or other external-call
path makes this kernel decision false. -/
theorem vault_externalWethCallSites_complete :
    exactWethSourceClosure Blanc.ProrataWethVault.vault = true := by
  decide +kernel

theorem readTotalAssets_sourceShape (body : Func) :
    Blanc.ProrataWethVault.readTotalAssets body =
      balanceOfStaging +++
        (statcall ::: iszero :::
          (Func.rev <?>
            (pushB256 32 ::: retdatasize ::: eq ::: iszero :::
              (Func.rev <?> (pushB256 0 ::: mload ::: body))))) := by
  rfl

theorem callWethTransferFrom_sourceShape
    (assetsWord : B256) (body : Func) :
    Blanc.ProrataWethVault.callWethTransferFrom
        (Blanc.ProrataWethVault.loadWord assetsWord) body =
      transferFromStaging assetsWord +++
        (call ::: iszero :::
          (Func.rev <?>
            Blanc.ProrataWethVault.requireCanonicalWethTrue body)) := by
  rfl

theorem callWethTransfer_sourceShape
    (receiverWord assetsWord : B256) (body : Func) :
    Blanc.ProrataWethVault.callWethTransfer
        (Blanc.ProrataWethVault.loadWord receiverWord)
        (Blanc.ProrataWethVault.loadWord assetsWord) body =
      transferStaging receiverWord assetsWord +++
        (call ::: iszero :::
          (Func.rev <?>
            Blanc.ProrataWethVault.requireCanonicalWethTrue body)) := by
  rfl

/-! ## Complete WETH selector surface staged by the vault -/

/-- The three source helpers above stage exactly the boundary allowlist.  In
particular, the vault has no source helper that stages WETH `approve` or
`withdraw`. -/
theorem stagedWethSelectors_complete :
    [ Blanc.ProrataWethVault.wethBalanceOfSelector,
      Blanc.ProrataWethVault.wethTransferFromSelector,
      Blanc.ProrataWethVault.wethTransferSelector ] =
      allowedWethSelectors := by
  rfl

theorem approveSelector_not_staged :
    selector "approve" [.address, .uint256] ∉
      [ Blanc.ProrataWethVault.wethBalanceOfSelector,
        Blanc.ProrataWethVault.wethTransferFromSelector,
        Blanc.ProrataWethVault.wethTransferSelector ] := by
  rw [stagedWethSelectors_complete]
  exact approveSelector_not_allowed

theorem withdrawSelector_not_staged :
    selector "withdraw" [.uint256] ∉
      [ Blanc.ProrataWethVault.wethBalanceOfSelector,
        Blanc.ProrataWethVault.wethTransferFromSelector,
        Blanc.ProrataWethVault.wethTransferSelector ] := by
  rw [stagedWethSelectors_complete]
  exact withdrawSelector_not_allowed

/-! ## Proof-carrying source memory -/

def MemoryImage (devm : Devm) (image : Bytes) : Prop :=
  Mem.Wf devm.memory ∧ Mem.Reads devm.memory image

def ImageWordAt (image : Bytes) (word : B256) (value : B256) : Prop :=
  image.sliceD (word * 32).toNat 32 0 = value.toBytes

private lemma sliceD_split {ξ : Type} (xs : List ξ) (d : ξ) :
    ∀ (a m b : Nat),
      xs.sliceD m (a + b) d =
        xs.sliceD m a d ++ xs.sliceD (m + a) b d := by
  intro a
  induction a with
  | zero => intro m b; simp [List.sliceD, List.takeD]
  | succ a ih =>
    intro m b
    rw [show a + 1 + b = (a + b) + 1 from by omega,
      List.sliceD_succ, ih (m + 1) b,
      List.sliceD_succ xs m a d,
      show m + (a + 1) = m + 1 + a from by omega]
    rfl

private lemma drop_of_length_append {ξ : Type} (a b : List ξ) (n : Nat)
    (length : a.length = n) : (a ++ b).drop n = b := by
  subst length
  exact List.drop_left

private lemma selectorSlice (image : Bytes) (selected : B256) :
    (Bytes.writeAt image 0 selected.toBytes).sliceD 28 4 0 =
      abiSelectorBytes selected := by
  have selectedLength : selected.toBytes.length = 32 :=
    B256.length_toBytes selected
  have wholeWord :
      (Bytes.writeAt image 0 selected.toBytes).sliceD 0 32 0 =
        selected.toBytes := by
    have readback := Bytes.sliceD_writeAt image selected.toBytes 0
    rwa [selectedLength] at readback
  have split := sliceD_split
    (Bytes.writeAt image 0 selected.toBytes) (0 : UInt8) 28 0 4
  simp only [show (28 : Nat) + 4 = 32 from rfl,
    show (0 : Nat) + 28 = 28 from rfl] at split
  have prefixLength :
      ((Bytes.writeAt image 0 selected.toBytes).sliceD 0 28 0).length = 28 :=
    List.takeD_length _ _ _
  have dropped : abiSelectorBytes selected =
      (((Bytes.writeAt image 0 selected.toBytes).sliceD 0 28 0) ++
        (Bytes.writeAt image 0 selected.toBytes).sliceD 28 4 0).drop 28 := by
    rw [← split, wholeWord]
    rfl
  rw [dropped, drop_of_length_append _ _ 28 prefixLength]

private lemma selectorOneWordImage
    (image : Bytes) (selected word : B256) :
    (Bytes.writeAt (Bytes.writeAt image 0 selected.toBytes)
      32 word.toBytes).sliceD 28 36 0 =
        abiSelectorBytes selected ++ word.toBytes := by
  have low :
      (Bytes.writeAt (Bytes.writeAt image 0 selected.toBytes)
        32 word.toBytes).sliceD 28 4 0 =
      (Bytes.writeAt image 0 selected.toBytes).sliceD 28 4 0 :=
    Bytes.sliceD_writeAt_before _ _ 28 4 32 (by omega)
  have high :
      (Bytes.writeAt (Bytes.writeAt image 0 selected.toBytes)
        32 word.toBytes).sliceD 32 32 0 = word.toBytes := by
    have readback := Bytes.sliceD_writeAt
      (Bytes.writeAt image 0 selected.toBytes) word.toBytes 32
    rwa [B256.length_toBytes] at readback
  have split := sliceD_split
    (Bytes.writeAt (Bytes.writeAt image 0 selected.toBytes)
      32 word.toBytes) (0 : UInt8) 4 28 32
  simp only [show (4 : Nat) + 32 = 36 from rfl,
    show (28 : Nat) + 4 = 32 from rfl] at split
  rw [split, low, selectorSlice, high]

private lemma selectorTwoWordImage
    (image : Bytes) (selected first second : B256) :
    (Bytes.writeAt
      (Bytes.writeAt (Bytes.writeAt image 0 selected.toBytes)
        32 first.toBytes)
      64 second.toBytes).sliceD 28 68 0 =
        abiSelectorBytes selected ++ first.toBytes ++ second.toBytes := by
  let prior := Bytes.writeAt (Bytes.writeAt image 0 selected.toBytes)
    32 first.toBytes
  have low :
      (Bytes.writeAt prior 64 second.toBytes).sliceD 28 36 0 =
        prior.sliceD 28 36 0 :=
    Bytes.sliceD_writeAt_before _ _ 28 36 64 (by omega)
  have high :
      (Bytes.writeAt prior 64 second.toBytes).sliceD 64 32 0 =
        second.toBytes := by
    have readback := Bytes.sliceD_writeAt prior second.toBytes 64
    rwa [B256.length_toBytes] at readback
  have split := sliceD_split (Bytes.writeAt prior 64 second.toBytes)
    (0 : UInt8) 36 28 32
  simp only [show (36 : Nat) + 32 = 68 from rfl,
    show (28 : Nat) + 36 = 64 from rfl] at split
  rw [split, low, selectorOneWordImage, high, List.append_assoc]

private lemma selectorThreeWordImage
    (image : Bytes) (selected first second third : B256) :
    (Bytes.writeAt
      (Bytes.writeAt
        (Bytes.writeAt (Bytes.writeAt image 0 selected.toBytes)
          32 first.toBytes)
        64 second.toBytes)
      96 third.toBytes).sliceD 28 100 0 =
        abiSelectorBytes selected ++ first.toBytes ++ second.toBytes ++
          third.toBytes := by
  let prior := Bytes.writeAt
    (Bytes.writeAt (Bytes.writeAt image 0 selected.toBytes) 32 first.toBytes)
    64 second.toBytes
  have low :
      (Bytes.writeAt prior 96 third.toBytes).sliceD 28 68 0 =
        prior.sliceD 28 68 0 :=
    Bytes.sliceD_writeAt_before _ _ 28 68 96 (by omega)
  have high :
      (Bytes.writeAt prior 96 third.toBytes).sliceD 96 32 0 =
        third.toBytes := by
    have readback := Bytes.sliceD_writeAt prior third.toBytes 96
    rwa [B256.length_toBytes] at readback
  have split := sliceD_split (Bytes.writeAt prior 96 third.toBytes)
    (0 : UInt8) 68 28 32
  simp only [show (68 : Nat) + 32 = 100 from rfl,
    show (28 : Nat) + 68 = 96 from rfl] at split
  rw [split, low, selectorTwoWordImage, high, List.append_assoc]

private lemma imageWord_after_write_below
    (image : Bytes) (written : B256) (writeOffset wordOffset : Nat)
    (below : writeOffset + 32 ≤ wordOffset) :
    (Bytes.writeAt image writeOffset written.toBytes).sliceD
        wordOffset 32 0 = image.sliceD wordOffset 32 0 := by
  apply Bytes.sliceD_writeAt_after
  simpa only [B256.length_toBytes] using below

/-! ## Derived operand stacks and calldata windows -/

theorem balanceOfStaging_boundary
    {sevm : Sevm} {entry callPre : Devm} {image : Bytes}
    (memory : MemoryImage entry image)
    (run : Line.Run sevm entry balanceOfStaging callPre) :
    ∃ (gasWord : B256) (rest : List B256),
      callPre.stack =
        gasWord :: wethAccount.toB256 :: 28 :: 36 :: 0 :: 32 :: rest ∧
      (callPre.memory.read 28 36).1 =
        balanceOfCalldata sevm.currentTarget := by
  obtain ⟨wf0, reads0⟩ := memory
  simp only [balanceOfStaging, List.append_assoc] at run
  obtain ⟨s1, r1, run⟩ :=
    of_run_append
      [pushB256 Blanc.ProrataWethVault.wethBalanceOfSelector] run
  rcases Line.of_run_cons r1 with ⟨_, q1, qnil⟩
  cases qnil
  have push1 := of_run_pushB256 q1
  have p1 := prefix_of_push push1 nil_pref
  have wf1 : Mem.Wf s1.memory := by rw [← push1.memory]; exact wf0
  have reads1 : Mem.Reads s1.memory image := by
    rw [← push1.memory]
    exact reads0
  obtain ⟨s2, r2, run⟩ := of_run_append (mstoreAt 0) run
  obtain ⟨p2, mem2⟩ := of_run_mstoreAt_val r2 p1
  have wf2 : Mem.Wf s2.memory := by rw [mem2]; exact wf1.write _ _
  have reads2 : Mem.Reads s2.memory
      (Bytes.writeAt image 0
        Blanc.ProrataWethVault.wethBalanceOfSelector.toBytes) := by
    rw [mem2]
    exact Mem.Reads.write wf1 reads1 _ _
  obtain ⟨s3, r3, run⟩ := of_run_append [address] run
  rcases Line.of_run_cons r3 with ⟨_, q3, qnil⟩
  cases qnil
  have p3 : sevm.currentTarget.toB256 :: [] <<+ s3.stack :=
    prefix_of_push (of_run_address q3) p2
  have wf3 : Mem.Wf s3.memory := by
    rw [← (of_run_address q3).memory]
    exact wf2
  have reads3 : Mem.Reads s3.memory
      (Bytes.writeAt image 0
        Blanc.ProrataWethVault.wethBalanceOfSelector.toBytes) := by
    rw [← (of_run_address q3).memory]
    exact reads2
  obtain ⟨s4, r4, run⟩ := of_run_append (mstoreAt 1) run
  obtain ⟨p4, mem4⟩ := of_run_mstoreAt_val r4 p3
  let staged := Bytes.writeAt
    (Bytes.writeAt image 0
      Blanc.ProrataWethVault.wethBalanceOfSelector.toBytes)
    32 sevm.currentTarget.toB256.toBytes
  have wf4 : Mem.Wf s4.memory := by rw [mem4]; exact wf3.write _ _
  have reads4 : Mem.Reads s4.memory staged := by
    rw [mem4]
    exact Mem.Reads.write wf3 reads3 _ _
  have tailRun := run
  obtain ⟨s5, r5, run⟩ :=
    of_run_append (pushList [32, 0, 36, 28]) run
  have p5 : (28 : B256) :: 36 :: 0 :: 32 :: [] <<+ s5.stack := by
    simp only [pushList, List.map] at r5
    rcases Line.of_run_cons r5 with ⟨_, a, r5⟩
    rcases Line.of_run_cons r5 with ⟨_, b, r5⟩
    rcases Line.of_run_cons r5 with ⟨_, c, r5⟩
    rcases Line.of_run_cons r5 with ⟨_, d, qnil⟩
    cases qnil
    exact prefix_of_push (of_run_pushB256 d)
      (prefix_of_push (of_run_pushB256 c)
        (prefix_of_push (of_run_pushB256 b)
          (prefix_of_push (of_run_pushB256 a) p4)))
  obtain ⟨s6, r6, run⟩ :=
    of_run_append [pushB256 Blanc.ProrataWethVault.assetAddress] run
  rcases Line.of_run_cons r6 with ⟨_, q6, qnil⟩
  cases qnil
  have p6 : Blanc.ProrataWethVault.assetAddress ::
      28 :: 36 :: 0 :: 32 :: [] <<+
      s6.stack := prefix_of_push (of_run_pushB256 q6) p5
  rcases Line.of_run_cons run with ⟨_, q7, qnil⟩
  cases qnil
  obtain ⟨gasWord, gasPush⟩ := of_run_gas q7
  obtain ⟨rest, stack⟩ := prefix_of_push gasPush p6
  have finalMemory : s4.memory = callPre.memory :=
    Line.of_inv Devm.memory (by
      simp only [pushList, List.map]
      line_inv) tailRun
  have finalReads : Mem.Reads callPre.memory staged := by
    rw [← finalMemory]
    exact reads4
  refine ⟨gasWord, rest, ?_, ?_⟩
  · unfold Split at stack
    simpa only [wethAccount_toB256, List.cons_append,
      List.nil_append] using stack
  · rw [Mem.Reads.read finalReads]
    simpa only [staged, balanceOfCalldata,
      Blanc.ProrataWethVault.wethBalanceOfSelector] using
      selectorOneWordImage image
        Blanc.ProrataWethVault.wethBalanceOfSelector
        sevm.currentTarget.toB256

theorem transferFromStaging_boundary
    {sevm : Sevm} {entry callPre : Devm} {image : Bytes}
    {assetsWord assets : B256}
    (memory : MemoryImage entry image)
    (assetsAt : ImageWordAt image assetsWord assets)
    (assetsAboveCalldata : 96 ≤ (assetsWord * 32).toNat)
    (run : Line.Run sevm entry (transferFromStaging assetsWord) callPre) :
    ∃ (gasWord : B256) (rest : List B256),
      callPre.stack =
        gasWord :: wethAccount.toB256 :: 0 :: 28 :: 100 :: 0 :: 32 :: rest ∧
      (callPre.memory.read 28 100).1 =
        transferFromCalldata sevm.caller sevm.currentTarget assets := by
  obtain ⟨wf0, reads0⟩ := memory
  simp only [transferFromStaging, List.append_assoc] at run
  obtain ⟨s1, r1, run⟩ :=
    of_run_append
      [pushB256 Blanc.ProrataWethVault.wethTransferFromSelector] run
  rcases Line.of_run_cons r1 with ⟨_, q1, qnil⟩
  cases qnil
  have push1 := of_run_pushB256 q1
  have p1 := prefix_of_push push1 nil_pref
  have wf1 : Mem.Wf s1.memory := by rw [← push1.memory]; exact wf0
  have reads1 : Mem.Reads s1.memory image := by
    rw [← push1.memory]
    exact reads0
  obtain ⟨s2, r2, run⟩ := of_run_append (mstoreAt 0) run
  obtain ⟨p2, mem2⟩ := of_run_mstoreAt_val r2 p1
  let image2 := Bytes.writeAt image 0
    Blanc.ProrataWethVault.wethTransferFromSelector.toBytes
  have wf2 : Mem.Wf s2.memory := by rw [mem2]; exact wf1.write _ _
  have reads2 : Mem.Reads s2.memory image2 := by
    rw [mem2]
    exact Mem.Reads.write wf1 reads1 _ _
  obtain ⟨s3, r3, run⟩ := of_run_append [caller] run
  rcases Line.of_run_cons r3 with ⟨_, q3, qnil⟩
  cases qnil
  have p3 : sevm.caller.toB256 :: [] <<+ s3.stack :=
    prefix_of_push (of_run_caller q3) p2
  have wf3 : Mem.Wf s3.memory := by rw [← (of_run_caller q3).memory]; exact wf2
  have reads3 : Mem.Reads s3.memory image2 := by
    rw [← (of_run_caller q3).memory]
    exact reads2
  obtain ⟨s4, r4, run⟩ := of_run_append (mstoreAt 1) run
  obtain ⟨p4, mem4⟩ := of_run_mstoreAt_val r4 p3
  let image4 := Bytes.writeAt image2 32 sevm.caller.toB256.toBytes
  have wf4 : Mem.Wf s4.memory := by rw [mem4]; exact wf3.write _ _
  have reads4 : Mem.Reads s4.memory image4 := by
    rw [mem4]
    exact Mem.Reads.write wf3 reads3 _ _
  obtain ⟨s5, r5, run⟩ := of_run_append [address] run
  rcases Line.of_run_cons r5 with ⟨_, q5, qnil⟩
  cases qnil
  have p5 : sevm.currentTarget.toB256 :: [] <<+ s5.stack :=
    prefix_of_push (of_run_address q5) p4
  have wf5 : Mem.Wf s5.memory := by rw [← (of_run_address q5).memory]; exact wf4
  have reads5 : Mem.Reads s5.memory image4 := by
    rw [← (of_run_address q5).memory]
    exact reads4
  obtain ⟨s6, r6, run⟩ := of_run_append (mstoreAt 2) run
  obtain ⟨p6, mem6⟩ := of_run_mstoreAt_val r6 p5
  let image6 := Bytes.writeAt image4 64 sevm.currentTarget.toB256.toBytes
  have wf6 : Mem.Wf s6.memory := by rw [mem6]; exact wf5.write _ _
  have reads6 : Mem.Reads s6.memory image6 := by
    rw [mem6]
    exact Mem.Reads.write wf5 reads5 _ _
  have assetsAt6 : ImageWordAt image6 assetsWord assets := by
    unfold ImageWordAt at assetsAt ⊢
    unfold image6 image4 image2
    rw [imageWord_after_write_below _ _ 64
        (assetsWord * 32).toNat (by omega),
      imageWord_after_write_below _ _ 32
        (assetsWord * 32).toNat (by omega),
      imageWord_after_write_below _ _ 0
        (assetsWord * 32).toNat (by omega)]
    exact assetsAt
  obtain ⟨s7, r7, run⟩ := of_run_append
    (Blanc.ProrataWethVault.loadWord assetsWord) run
  have loaded7 := of_run_loadWordAt_image nil_pref wf6 reads6
    (by rw [assetsAt6, B256.toB256_toBytes]) r7
  obtain ⟨p7, wf7, reads7, -⟩ := loaded7
  obtain ⟨s8, r8, run⟩ := of_run_append (mstoreAt 3) run
  obtain ⟨p8, mem8⟩ := of_run_mstoreAt_val r8 p7
  let image8 := Bytes.writeAt image6 96 assets.toBytes
  have wf8 : Mem.Wf s8.memory := by rw [mem8]; exact wf7.write _ _
  have reads8 : Mem.Reads s8.memory image8 := by
    rw [mem8]
    exact Mem.Reads.write wf7 reads7 _ _
  have tailRun := run
  obtain ⟨s9, r9, run⟩ :=
    of_run_append (pushList [32, 0, 100, 28, 0]) run
  have p9 : (0 : B256) :: 28 :: 100 :: 0 :: 32 :: [] <<+ s9.stack := by
    simp only [pushList, List.map] at r9
    rcases Line.of_run_cons r9 with ⟨_, a, r9⟩
    rcases Line.of_run_cons r9 with ⟨_, b, r9⟩
    rcases Line.of_run_cons r9 with ⟨_, c, r9⟩
    rcases Line.of_run_cons r9 with ⟨_, d, r9⟩
    rcases Line.of_run_cons r9 with ⟨_, e, qnil⟩
    cases qnil
    exact prefix_of_push (of_run_pushB256 e)
      (prefix_of_push (of_run_pushB256 d)
        (prefix_of_push (of_run_pushB256 c)
          (prefix_of_push (of_run_pushB256 b)
            (prefix_of_push (of_run_pushB256 a) p8))))
  obtain ⟨s10, r10, run⟩ :=
    of_run_append [pushB256 Blanc.ProrataWethVault.assetAddress] run
  rcases Line.of_run_cons r10 with ⟨_, q10, qnil⟩
  cases qnil
  have p10 : Blanc.ProrataWethVault.assetAddress ::
      0 :: 28 :: 100 :: 0 :: 32 :: [] <<+
      s10.stack := prefix_of_push (of_run_pushB256 q10) p9
  rcases Line.of_run_cons run with ⟨_, q11, qnil⟩
  cases qnil
  obtain ⟨gasWord, gasPush⟩ := of_run_gas q11
  obtain ⟨rest, stack⟩ := prefix_of_push gasPush p10
  have finalMemory : s8.memory = callPre.memory :=
    Line.of_inv Devm.memory (by
      simp only [pushList, List.map]
      line_inv) tailRun
  have finalReads : Mem.Reads callPre.memory image8 := by
    rw [← finalMemory]
    exact reads8
  refine ⟨gasWord, rest, ?_, ?_⟩
  · unfold Split at stack
    simpa only [wethAccount_toB256, List.cons_append,
      List.nil_append] using stack
  · rw [Mem.Reads.read finalReads]
    simpa only [image8, image6, image4, image2, transferFromCalldata,
      Blanc.ProrataWethVault.wethTransferFromSelector,
      List.append_assoc] using
        selectorThreeWordImage image
          Blanc.ProrataWethVault.wethTransferFromSelector
          sevm.caller.toB256 sevm.currentTarget.toB256 assets

theorem transferStaging_boundary
    {sevm : Sevm} {entry callPre : Devm} {image : Bytes}
    {receiverWord assetsWord assets : B256} {receiver : Adr}
    (memory : MemoryImage entry image)
    (receiverAt : ImageWordAt image receiverWord receiver.toB256)
    (assetsAt : ImageWordAt image assetsWord assets)
    (receiverAboveSelector : 32 ≤ (receiverWord * 32).toNat)
    (assetsAboveReceiver : 64 ≤ (assetsWord * 32).toNat)
    (run : Line.Run sevm entry
      (transferStaging receiverWord assetsWord) callPre) :
    ∃ (gasWord : B256) (rest : List B256),
      callPre.stack =
        gasWord :: wethAccount.toB256 :: 0 :: 28 :: 68 :: 0 :: 32 :: rest ∧
      (callPre.memory.read 28 68).1 =
        transferCalldata receiver assets := by
  obtain ⟨wf0, reads0⟩ := memory
  simp only [transferStaging, List.append_assoc] at run
  obtain ⟨s1, r1, run⟩ :=
    of_run_append
      [pushB256 Blanc.ProrataWethVault.wethTransferSelector] run
  rcases Line.of_run_cons r1 with ⟨_, q1, qnil⟩
  cases qnil
  have push1 := of_run_pushB256 q1
  have p1 := prefix_of_push push1 nil_pref
  have wf1 : Mem.Wf s1.memory := by rw [← push1.memory]; exact wf0
  have reads1 : Mem.Reads s1.memory image := by
    rw [← push1.memory]
    exact reads0
  obtain ⟨s2, r2, run⟩ := of_run_append (mstoreAt 0) run
  obtain ⟨p2, mem2⟩ := of_run_mstoreAt_val r2 p1
  let image2 := Bytes.writeAt image 0
    Blanc.ProrataWethVault.wethTransferSelector.toBytes
  have wf2 : Mem.Wf s2.memory := by rw [mem2]; exact wf1.write _ _
  have reads2 : Mem.Reads s2.memory image2 := by
    rw [mem2]
    exact Mem.Reads.write wf1 reads1 _ _
  have receiverAt2 : ImageWordAt image2 receiverWord receiver.toB256 := by
    unfold ImageWordAt at receiverAt ⊢
    unfold image2
    rw [imageWord_after_write_below _ _ 0
      (receiverWord * 32).toNat (by omega)]
    exact receiverAt
  obtain ⟨s3, r3, run⟩ := of_run_append
    (Blanc.ProrataWethVault.loadWord receiverWord) run
  have loaded3 := of_run_loadWordAt_image nil_pref wf2 reads2
    (by rw [receiverAt2, B256.toB256_toBytes]) r3
  obtain ⟨p3, wf3, reads3, -⟩ := loaded3
  obtain ⟨s4, r4, run⟩ := of_run_append (mstoreAt 1) run
  obtain ⟨p4, mem4⟩ := of_run_mstoreAt_val r4 p3
  let image4 := Bytes.writeAt image2 32 receiver.toB256.toBytes
  have wf4 : Mem.Wf s4.memory := by rw [mem4]; exact wf3.write _ _
  have reads4 : Mem.Reads s4.memory image4 := by
    rw [mem4]
    exact Mem.Reads.write wf3 reads3 _ _
  have assetsAt4 : ImageWordAt image4 assetsWord assets := by
    unfold ImageWordAt at assetsAt ⊢
    unfold image4 image2
    rw [imageWord_after_write_below _ _ 32
        (assetsWord * 32).toNat (by omega),
      imageWord_after_write_below _ _ 0
        (assetsWord * 32).toNat (by omega)]
    exact assetsAt
  obtain ⟨s5, r5, run⟩ := of_run_append
    (Blanc.ProrataWethVault.loadWord assetsWord) run
  have loaded5 := of_run_loadWordAt_image nil_pref wf4 reads4
    (by rw [assetsAt4, B256.toB256_toBytes]) r5
  obtain ⟨p5, wf5, reads5, -⟩ := loaded5
  obtain ⟨s6, r6, run⟩ := of_run_append (mstoreAt 2) run
  obtain ⟨p6, mem6⟩ := of_run_mstoreAt_val r6 p5
  let image6 := Bytes.writeAt image4 64 assets.toBytes
  have wf6 : Mem.Wf s6.memory := by rw [mem6]; exact wf5.write _ _
  have reads6 : Mem.Reads s6.memory image6 := by
    rw [mem6]
    exact Mem.Reads.write wf5 reads5 _ _
  have tailRun := run
  obtain ⟨s7, r7, run⟩ :=
    of_run_append (pushList [32, 0, 68, 28, 0]) run
  have p7 : (0 : B256) :: 28 :: 68 :: 0 :: 32 :: [] <<+ s7.stack := by
    simp only [pushList, List.map] at r7
    rcases Line.of_run_cons r7 with ⟨_, a, r7⟩
    rcases Line.of_run_cons r7 with ⟨_, b, r7⟩
    rcases Line.of_run_cons r7 with ⟨_, c, r7⟩
    rcases Line.of_run_cons r7 with ⟨_, d, r7⟩
    rcases Line.of_run_cons r7 with ⟨_, e, qnil⟩
    cases qnil
    exact prefix_of_push (of_run_pushB256 e)
      (prefix_of_push (of_run_pushB256 d)
        (prefix_of_push (of_run_pushB256 c)
          (prefix_of_push (of_run_pushB256 b)
            (prefix_of_push (of_run_pushB256 a) p6))))
  obtain ⟨s8, r8, run⟩ :=
    of_run_append [pushB256 Blanc.ProrataWethVault.assetAddress] run
  rcases Line.of_run_cons r8 with ⟨_, q8, qnil⟩
  cases qnil
  have p8 : Blanc.ProrataWethVault.assetAddress ::
      0 :: 28 :: 68 :: 0 :: 32 :: [] <<+
      s8.stack := prefix_of_push (of_run_pushB256 q8) p7
  rcases Line.of_run_cons run with ⟨_, q9, qnil⟩
  cases qnil
  obtain ⟨gasWord, gasPush⟩ := of_run_gas q9
  obtain ⟨rest, stack⟩ := prefix_of_push gasPush p8
  have finalMemory : s6.memory = callPre.memory :=
    Line.of_inv Devm.memory (by
      simp only [pushList, List.map]
      line_inv) tailRun
  have finalReads : Mem.Reads callPre.memory image6 := by
    rw [← finalMemory]
    exact reads6
  refine ⟨gasWord, rest, ?_, ?_⟩
  · unfold Split at stack
    simpa only [wethAccount_toB256, List.cons_append,
      List.nil_append] using stack
  · rw [Mem.Reads.read finalReads]
    simpa only [image6, image4, image2, transferCalldata,
      Blanc.ProrataWethVault.wethTransferSelector,
      List.append_assoc] using
        selectorTwoWordImage image
          Blanc.ProrataWethVault.wethTransferSelector
          receiver.toB256 assets

/-! ## Source-walk extraction -/

theorem readTotalAssets_trace
    {fs : List Func} {sevm : Sevm} {entry : Devm} {body : Func}
    {execution : Execution}
    (run : Func.RunCompiledTo fs sevm entry
      (Blanc.ProrataWethVault.readTotalAssets body) execution) :
    ∃ callPre callPost,
      Line.Run sevm entry balanceOfStaging callPre ∧
      Ninst.RunCompiled sevm callPre statcall callPost ∧
      Func.RunCompiledTo fs sevm callPost
        (iszero :::
          (Func.rev <?>
            (pushB256 32 ::: retdatasize ::: eq ::: iszero :::
              (Func.rev <?> (pushB256 0 ::: mload ::: body))))) execution := by
  rw [readTotalAssets_sourceShape] at run
  obtain ⟨callPre, staging, run⟩ := runCompiledTo_prepend_inv run
  obtain ⟨callPost, crossing, suffix⟩ := runCompiledTo_next_inv run
  exact ⟨callPre, callPost, staging, crossing, suffix⟩

theorem callWethTransferFrom_trace
    {fs : List Func} {sevm : Sevm} {entry : Devm}
    {assetsWord : B256} {body : Func} {execution : Execution}
    (run : Func.RunCompiledTo fs sevm entry
      (Blanc.ProrataWethVault.callWethTransferFrom
        (Blanc.ProrataWethVault.loadWord assetsWord) body) execution) :
    ∃ callPre callPost,
      Line.Run sevm entry (transferFromStaging assetsWord) callPre ∧
      Ninst.RunCompiled sevm callPre call callPost ∧
      Func.RunCompiledTo fs sevm callPost
        (iszero :::
          (Func.rev <?>
            Blanc.ProrataWethVault.requireCanonicalWethTrue body))
        execution := by
  rw [callWethTransferFrom_sourceShape] at run
  obtain ⟨callPre, staging, run⟩ := runCompiledTo_prepend_inv run
  obtain ⟨callPost, crossing, suffix⟩ := runCompiledTo_next_inv run
  exact ⟨callPre, callPost, staging, crossing, suffix⟩

theorem callWethTransfer_trace
    {fs : List Func} {sevm : Sevm} {entry : Devm}
    {receiverWord assetsWord : B256} {body : Func} {execution : Execution}
    (run : Func.RunCompiledTo fs sevm entry
      (Blanc.ProrataWethVault.callWethTransfer
        (Blanc.ProrataWethVault.loadWord receiverWord)
        (Blanc.ProrataWethVault.loadWord assetsWord) body) execution) :
    ∃ callPre callPost,
      Line.Run sevm entry
        (transferStaging receiverWord assetsWord) callPre ∧
      Ninst.RunCompiled sevm callPre call callPost ∧
      Func.RunCompiledTo fs sevm callPost
        (iszero :::
          (Func.rev <?>
            Blanc.ProrataWethVault.requireCanonicalWethTrue body))
        execution := by
  rw [callWethTransfer_sourceShape] at run
  obtain ⟨callPre, staging, run⟩ := runCompiledTo_prepend_inv run
  obtain ⟨callPost, crossing, suffix⟩ := runCompiledTo_next_inv run
  exact ⟨callPre, callPost, staging, crossing, suffix⟩

/-! ## Resource facts and retained-child adapters -/

def StaticGasAvailable (pre : Devm) (inputSize : B256) : Prop :=
  ∀ (gasWord : B256) (rest : List B256),
    pre.stack =
      gasWord :: wethAccount.toB256 :: 28 :: inputSize :: 0 :: 32 :: rest →
    let base := addAccessedAddress
      (pre.setMach ⟨rest, pre.memory, pre.gasLeft⟩) wethAccount
    let ext := (pre.setMach ⟨rest, pre.memory, pre.gasLeft⟩).extCost
      [⟨28, inputSize.toNat⟩, ⟨0, 32⟩]
    let access := accessCost wethAccount
      (pre.setMach ⟨rest, pre.memory, pre.gasLeft⟩).accessedAddresses
    (calculateMsgCallGas 0 gasWord.toNat base.gasLeft ext access).1 + ext ≤
      base.gasLeft

def CallGasAvailable (pre : Devm) (inputSize : B256) : Prop :=
  ∀ (gasWord : B256) (rest : List B256),
    pre.stack =
      gasWord :: wethAccount.toB256 :: 0 :: 28 :: inputSize :: 0 :: 32 ::
        rest →
    let base := addAccessedAddress
      (pre.setMach ⟨rest, pre.memory, pre.gasLeft⟩) wethAccount
    let ext := (pre.setMach ⟨rest, pre.memory, pre.gasLeft⟩).extCost
      [⟨28, inputSize.toNat⟩, ⟨0, 32⟩]
    let access := accessCost wethAccount
      (pre.setMach ⟨rest, pre.memory, pre.gasLeft⟩).accessedAddresses
    (calculateMsgCallGas 0 gasWord.toNat base.gasLeft ext access).1 + ext ≤
      base.gasLeft

theorem balanceOfStaging_occurrence
    {sevm : Sevm} {entry callPre callPost : Devm} {image : Bytes}
    (config : DirectWethConfiguration sevm.currentTarget sevm callPre)
    (memory : MemoryImage entry image)
    (staging : Line.Run sevm entry balanceOfStaging callPre)
    (depth : sevm.depth ≠ 0)
    (gasAvailable : StaticGasAvailable callPre 36)
    (crossing : Ninst.RunCompiled sevm callPre statcall callPost) :
    ExactWethChildOccurrence sevm callPre callPost statcall
      (balanceOfCalldata sevm.currentTarget) true := by
  obtain ⟨gasWord, rest, stack, window⟩ :=
    balanceOfStaging_boundary memory staging
  apply exactWethStatcallOccurrence_of_runCompiled config stack window depth
  · exact gasAvailable gasWord rest stack
  · exact crossing

theorem transferFromStaging_occurrence
    {sevm : Sevm} {entry callPre callPost : Devm} {image : Bytes}
    {assetsWord assets : B256}
    (config : DirectWethConfiguration sevm.currentTarget sevm callPre)
    (memory : MemoryImage entry image)
    (assetsAt : ImageWordAt image assetsWord assets)
    (assetsAboveCalldata : 96 ≤ (assetsWord * 32).toNat)
    (staging : Line.Run sevm entry
      (transferFromStaging assetsWord) callPre)
    (depth : sevm.depth ≠ 0)
    (dynamic : sevm.isStatic = false)
    (gasAvailable : CallGasAvailable callPre 100)
    (crossing : Ninst.RunCompiled sevm callPre call callPost) :
    ExactWethChildOccurrence sevm callPre callPost call
      (transferFromCalldata sevm.caller sevm.currentTarget assets) false := by
  obtain ⟨gasWord, rest, stack, window⟩ :=
    transferFromStaging_boundary memory assetsAt assetsAboveCalldata staging
  apply exactWethCallOccurrence_of_runCompiled config stack window depth dynamic
  · exact gasAvailable gasWord rest stack
  · exact crossing

theorem transferStaging_occurrence
    {sevm : Sevm} {entry callPre callPost : Devm} {image : Bytes}
    {receiverWord assetsWord assets : B256} {receiver : Adr}
    (config : DirectWethConfiguration sevm.currentTarget sevm callPre)
    (memory : MemoryImage entry image)
    (receiverAt : ImageWordAt image receiverWord receiver.toB256)
    (assetsAt : ImageWordAt image assetsWord assets)
    (receiverAboveSelector : 32 ≤ (receiverWord * 32).toNat)
    (assetsAboveReceiver : 64 ≤ (assetsWord * 32).toNat)
    (staging : Line.Run sevm entry
      (transferStaging receiverWord assetsWord) callPre)
    (depth : sevm.depth ≠ 0)
    (dynamic : sevm.isStatic = false)
    (gasAvailable : CallGasAvailable callPre 68)
    (crossing : Ninst.RunCompiled sevm callPre call callPost) :
    ExactWethChildOccurrence sevm callPre callPost call
      (transferCalldata receiver assets) false := by
  obtain ⟨gasWord, rest, stack, window⟩ :=
    transferStaging_boundary memory receiverAt assetsAt
      receiverAboveSelector assetsAboveReceiver staging
  apply exactWethCallOccurrence_of_runCompiled config stack window depth dynamic
  · exact gasAvailable gasWord rest stack
  · exact crossing

/-! ## Successful source checks refine the actual CALL result -/

private theorem iszeroRun_shape
    {sevm : Sevm} {pre post : Devm}
    (run : Ninst.RunCompiled sevm pre iszero post) :
    ∃ (word : B256) (tail : List B256),
      pre.stack = word :: tail ∧
      post.stack = (word =? 0) :: tail ∧
      post.memory = pre.memory ∧
      post.returnData = pre.returnData := by
  rcases of_run_reg (Ninst.Run.of_runCompiled run) with ⟨_, raw⟩
  simp only [Rinst.run, Rinst.runCore] at raw
  obtain ⟨word, diff⟩ := Devm.diffBurn_of_applyUnary raw
  obtain ⟨tail, popped, pushed⟩ := diff.stack
  exact ⟨word, tail, popped, pushed, diff.memory.symm,
    diff.returnData.symm⟩

private theorem rev_not_ok
    {fs : List Func} {sevm : Sevm} {pre final : Devm}
    (run : Func.RunCompiledTo fs sevm pre Func.rev (.ok final)) : False := by
  rcases runCompiledTo_rev_inv run with ⟨_, impossible, -⟩
  cases impossible

/-- A successful source suffix after a CALL-family instruction cannot have
seen status zero: zero is inverted to the nonzero branch selector, whose arm
is the vault's `REVERT`.  This theorem intentionally stops at "nonzero"; the
retained-child relation below supplies the EVM's stronger `{0,1}` fact. -/
theorem checkedCall_status_nonzero
    {fs : List Func} {sevm : Sevm} {callPost final : Devm} {body : Func}
    (run : Func.RunCompiledTo fs sevm callPost
      (iszero ::: (Func.rev <?> body)) (.ok final)) :
    ∃ (status : B256) (tail : List B256) (bodyPre : Devm),
      callPost.stack = status :: tail ∧
      status ≠ 0 ∧
      bodyPre.memory = callPost.memory ∧
      bodyPre.returnData = callPost.returnData ∧
      Func.RunCompiledTo fs sevm bodyPre body (.ok final) := by
  obtain ⟨branchPre, zeroRun, branchRun⟩ := runCompiledTo_next_inv run
  obtain ⟨status, tail, callStack, branchStack, branchMemory,
    branchReturnData⟩ := iszeroRun_shape zeroRun
  rcases runCompiledTo_branch_inv branchRun with
    ⟨bodyPre, selectedStack, pop, bodyRun⟩ |
      ⟨_, _, _, _, _, revertRun⟩
  · have flagZero : (status =? 0) = 0 := by
      rw [branchStack] at selectedStack
      exact (List.cons.inj selectedStack).1
    have statusNonzero : status ≠ 0 := by
      intro statusZero
      subst statusZero
      rw [B256.eqCheck, if_pos rfl] at flagZero
      exact B256.zero_ne_one flagZero.symm
    exact ⟨status, tail, bodyPre, callStack, statusNonzero,
      pop.memory.symm.trans branchMemory,
      pop.returnData.symm.trans branchReturnData, bodyRun⟩
  · exact (rev_not_ok revertRun).elim

/-- The retained EVM call flag is exactly `1` once the source has ruled out
zero.  The proof opens the actual child occurrence; it does not assume a token
success predicate. -/
theorem ExactWethChildOccurrence.successFlag_of_nonzero
    {sevm : Sevm} {pre post : Devm} {instruction : Ninst}
    {calldata : Bytes} {static : Bool} {status : B256} {tail : List B256}
    (occurrence : ExactWethChildOccurrence sevm pre post instruction
      calldata static)
    (statusStack : post.stack = status :: tail)
    (statusNonzero : status ≠ 0) :
    ∃ actualTail, post.stack = (1 : B256) :: actualTail := by
  unfold ExactWethChildOccurrence ExactWethChildExecution at occurrence
  rcases occurrence with ⟨msg, xl, child, pc, nextPc, resume,
    target, executes, childWorld, childRules, spawn, filled, process, stepRun,
    state, childOutput, childLogs, actualTail, actualStack, -⟩
  have statusEq :
      status = (if child.error.isSome then (0 : B256) else 1) := by
    exact (List.cons.inj (statusStack.symm.trans actualStack)).1
  by_cases childError : child.error.isSome
  · have statusZero : status = 0 := by
      simpa only [childError, if_pos] using statusEq
    exact (statusNonzero statusZero).elim
  · have childErrorFalse : child.error.isSome = false :=
      Bool.eq_false_of_not_eq_true childError
    exact ⟨actualTail, by simp only [childErrorFalse] at actualStack; exact actualStack⟩

/-! ## The exact-size half shared by balance reads and Boolean returns -/

private theorem exactSizeGuard_of_ok
    {fs : List Func} {sevm : Sevm} {pre final : Devm} {body : Func}
    (returndataBound : pre.returnData.length < 2 ^ 256)
    (run : Func.RunCompiledTo fs sevm pre
      (pushB256 32 ::: retdatasize ::: eq ::: iszero :::
        (Func.rev <?> body)) (.ok final)) :
    pre.returnData.length = 32 ∧
      ∃ bodyPre,
        bodyPre.memory = pre.memory ∧
        bodyPre.returnData = pre.returnData ∧
        Func.RunCompiledTo fs sevm bodyPre body (.ok final) := by
  obtain ⟨s1, q1, run⟩ := runCompiledTo_next_inv run
  obtain ⟨s2, q2, run⟩ := runCompiledTo_next_inv run
  obtain ⟨s3, q3, run⟩ := runCompiledTo_next_inv run
  obtain ⟨branchPre, q4, branchRun⟩ := runCompiledTo_next_inv run
  obtain ⟨_, _, _, _, q4Memory, q4ReturnData⟩ := iszeroRun_shape q4
  have q3ReturnData : s3.returnData = s2.returnData := by
    rcases of_run_reg (Ninst.Run.of_runCompiled q3) with ⟨_, rawEq⟩
    simp only [Rinst.run, Rinst.runCore] at rawEq
    obtain ⟨_, _, diff⟩ := Devm.diffBurn_of_applyBinary rawEq
    exact diff.returnData.symm
  have push32 := of_run_pushB256 (Ninst.Run.of_runCompiled q1)
  have p1 : (32 : B256) :: [] <<+ s1.stack :=
    prefix_of_push push32 nil_pref
  have returnSize := of_run_retdatasize_val (Ninst.Run.of_runCompiled q2)
  rw [← push32.returnData] at returnSize
  have p2 : pre.returnData.length.toB256 :: 32 :: [] <<+ s2.stack :=
    prefix_of_push returnSize p1
  have p3 : (pre.returnData.length.toB256 =? 32) :: [] <<+ s3.stack :=
    prefix_of_eq (Ninst.Run.of_runCompiled q3) p2
  have p4 : ((pre.returnData.length.toB256 =? 32) =? 0) :: [] <<+
      branchPre.stack :=
    prefix_of_iszero (Ninst.Run.of_runCompiled q4) p3
  rcases runCompiledTo_branch_inv branchRun with
    ⟨bodyPre, selectedStack, pop, bodyRun⟩ |
      ⟨_, _, _, _, _, revertRun⟩
  · have zeroPrefix : (0 : B256) :: [] <<+ branchPre.stack := by
      rw [selectedStack]
      exact pref_append [0] bodyPre.stack
    have testZero : ((pre.returnData.length.toB256 =? 32) =? 0) = 0 :=
      pref_head_unique p4 zeroPrefix
    have sizeWord : pre.returnData.length.toB256 = 32 := by
      by_cases sizeWord : pre.returnData.length.toB256 = 32
      · exact sizeWord
      · simp [B256.eqCheck, sizeWord] at testZero
        exact (B256.zero_ne_one testZero.symm).elim
    have sizeNat := congrArg B256.toNat sizeWord
    rw [B256.toNat_toB256_of_lt returndataBound] at sizeNat
    refine ⟨sizeNat, bodyPre, ?_, ?_, bodyRun⟩
    · exact pop.memory.symm.trans
        (q4Memory.trans
          ((Ninst.Hinv.inv (f := Devm.memory)
            (Ninst.Run.of_runCompiled q3)).symm.trans
            (returnSize.memory.symm.trans push32.memory.symm)))
    · exact pop.returnData.symm.trans
        (q4ReturnData.trans
          (q3ReturnData.trans
            (returnSize.returnData.symm.trans push32.returnData.symm)))
  · exact (rev_not_ok revertRun).elim

/-! ## The 32-byte return window copied by CALL and STATICCALL -/

private theorem prefix_of_mload_read
    {sevm : Sevm} {pre post : Devm} {offset : B256}
    {tail : List B256}
    (run : Ninst.Run sevm pre mload post)
    (stack : offset :: tail <<+ pre.stack) :
    Bytes.toB256 (pre.memory.read offset.toNat 32).1 :: tail <<+
      post.stack := by
  rcases of_run_mload_val run with ⟨actualOffset, ⟨middle, popped, pushed⟩,
    -, -⟩
  have offsetEq : offset = actualOffset :=
    (List.of_cons_pref_of_cons_pref stack (pref_of_split popped)).1
  subst offsetEq
  exact append_pref pushed (of_append_pref popped stack)

private theorem call_outputWindow_of_success
    {sevm : Sevm} {pre post : Devm}
    {gasWord target inputSize : B256} {rest : List B256}
    (stack : pre.stack =
      gasWord :: target :: 0 :: 28 :: inputSize :: 0 :: 32 :: rest)
    (crossing : Ninst.RunCompiled sevm pre call post)
    (successFlag : ∃ tail, post.stack = (1 : B256) :: tail)
    (returnDataLength : post.returnData.length = 32) :
    (post.memory.read 0 32).1 = post.returnData := by
  have operandPrefix :
      gasWord :: target :: 0 :: 28 :: inputSize :: 0 :: 32 :: rest <<+
        pre.stack := by
    rw [stack]
    exact ⟨[], by simp [Split]⟩
  rcases of_run_call_val_with_depth operandPrefix
      (Ninst.Run.of_runCompiled crossing) with failure | success
  · obtain ⟨zeroPrefix, -⟩ := failure
    obtain ⟨tail, successStack⟩ := successFlag
    have onePrefix : (1 : B256) :: [] <<+ post.stack := by
      rw [successStack]
      exact pref_append [1] tail
    have impossible : (0 : B256) = 1 :=
      pref_head_unique zeroPrefix onePrefix
    exact (B256.zero_ne_one impossible).elim
  · rcases success with
      ⟨parent, child, _, _, _, _, _, -, -, -, parentMemory, -, -, -, -, -,
        -, childReturnData, finalMemory, -⟩
    have childLength : child.output.length = 32 := by
      rw [← childReturnData]
      exact returnDataLength
    have childNonempty : child.output ≠ [] := by
      intro empty
      rw [empty] at childLength
      cases childLength
    have takeAll : child.output.take (32 : B256).toNat = child.output := by
      apply (List.take_eq_self_iff child.output).2
      rw [show (32 : B256).toNat = 32 from rfl, childLength]
    rw [finalMemory, childReturnData, takeAll]
    change ((parent.memory.write 0 child.output).read 0 32).1 = child.output
    simpa only [childLength] using
      Mem.read_write_zero parent.memory childNonempty

private theorem statcall_outputWindow_of_success
    {sevm : Sevm} {pre post : Devm}
    {gasWord target inputSize : B256} {rest : List B256}
    (stack : pre.stack =
      gasWord :: target :: 28 :: inputSize :: 0 :: 32 :: rest)
    (crossing : Ninst.RunCompiled sevm pre statcall post)
    (successFlag : ∃ tail, post.stack = (1 : B256) :: tail)
    (returnDataLength : post.returnData.length = 32) :
    (post.memory.read 0 32).1 = post.returnData := by
  have operandPrefix :
      gasWord :: target :: 28 :: inputSize :: 0 :: 32 :: rest <<+
        pre.stack := by
    rw [stack]
    exact ⟨[], by simp [Split]⟩
  rcases of_run_statcall_val_with_depth operandPrefix
      (Ninst.Run.of_runCompiled crossing) with failure | success
  · obtain ⟨zeroPrefix, -, -⟩ := failure
    obtain ⟨tail, successStack⟩ := successFlag
    have onePrefix : (1 : B256) :: [] <<+ post.stack := by
      rw [successStack]
      exact pref_append [1] tail
    have impossible : (0 : B256) = 1 :=
      pref_head_unique zeroPrefix onePrefix
    exact (B256.zero_ne_one impossible).elim
  · rcases success with
      ⟨parent, child, _, _, _, _, _, -, -, -, parentMemory, -, -, -, -, -,
        -, childReturnData, finalMemory, -⟩
    have childLength : child.output.length = 32 := by
      rw [← childReturnData]
      exact returnDataLength
    have childNonempty : child.output ≠ [] := by
      intro empty
      rw [empty] at childLength
      cases childLength
    have takeAll : child.output.take (32 : B256).toNat = child.output := by
      apply (List.take_eq_self_iff child.output).2
      rw [show (32 : B256).toNat = 32 from rfl, childLength]
    rw [finalMemory, childReturnData, takeAll]
    change ((parent.memory.write 0 child.output).read 0 32).1 = child.output
    simpa only [childLength] using
      Mem.read_write_zero parent.memory childNonempty

/-! ## Joined checked results -/

/-- A successful `readTotalAssets` suffix turns its actual retained STATICCALL
into an exact successful WETH child and hands the returned balance word to the
continuation.  The only length premise excludes mathematical `Nat → B256`
wraparound; no WETH result is accepted as an assumption. -/
theorem checkedBalanceOf_success
    {fs : List Func} {sevm : Sevm} {callPre callPost final : Devm}
    {body : Func} {gasWord : B256} {rest : List B256}
    (occurrence : ExactWethChildOccurrence sevm callPre callPost statcall
      (balanceOfCalldata sevm.currentTarget) true)
    (stack : callPre.stack =
      gasWord :: wethAccount.toB256 :: 28 :: 36 :: 0 :: 32 :: rest)
    (crossing : Ninst.RunCompiled sevm callPre statcall callPost)
    (returndataBound : callPost.returnData.length < 2 ^ 256)
    (suffix : Func.RunCompiledTo fs sevm callPost
      (iszero :::
        (Func.rev <?>
          (pushB256 32 ::: retdatasize ::: eq ::: iszero :::
            (Func.rev <?> (pushB256 0 ::: mload ::: body)))))
      (.ok final)) :
    ∃ (word : B256) (bodyPre : Devm),
      ExactWethChildSuccess sevm callPre callPost statcall
        (balanceOfCalldata sevm.currentTarget) word.toBytes true ∧
      callPost.returnData = word.toBytes ∧
      word :: [] <<+ bodyPre.stack ∧
      Func.RunCompiledTo fs sevm bodyPre body (.ok final) := by
  obtain ⟨status, statusTail, sizePre, statusStack, statusNonzero,
    sizeMemory, sizeReturnData, sizeRun⟩ :=
    checkedCall_status_nonzero suffix
  have successFlag :=
    ExactWethChildOccurrence.successFlag_of_nonzero occurrence
      statusStack statusNonzero
  have sizeBound : sizePre.returnData.length < 2 ^ 256 := by
    rw [sizeReturnData]
    exact returndataBound
  obtain ⟨sizeLength, decodePre, decodeMemory, -, decodeRun⟩ :=
    exactSizeGuard_of_ok sizeBound sizeRun
  have returnDataLength : callPost.returnData.length = 32 := by
    rw [← sizeReturnData]
    exact sizeLength
  have outputWindow := statcall_outputWindow_of_success stack crossing
    successFlag returnDataLength
  obtain ⟨mloadPre, pushZeroRun, decodeRun⟩ :=
    runCompiledTo_next_inv decodeRun
  obtain ⟨bodyPre, mloadRun, bodyRun⟩ :=
    runCompiledTo_next_inv decodeRun
  have pushZero := of_run_pushB256 (Ninst.Run.of_runCompiled pushZeroRun)
  have zeroPrefix : (0 : B256) :: [] <<+ mloadPre.stack :=
    prefix_of_push pushZero nil_pref
  have wordPrefix := prefix_of_mload_read
    (Ninst.Run.of_runCompiled mloadRun) zeroPrefix
  have mloadMemory : mloadPre.memory = callPost.memory :=
    pushZero.memory.symm.trans (decodeMemory.trans sizeMemory)
  rw [mloadMemory] at wordPrefix
  simp only [show (0 : B256).toNat = 0 from rfl] at wordPrefix
  rw [outputWindow] at wordPrefix
  let word := Bytes.toB256 callPost.returnData
  have outputEq : callPost.returnData = word.toBytes := by
    exact (Bytes.toBytes_toB256_of_length returnDataLength).symm
  refine ⟨word, bodyPre,
    occurrence.success_of_post successFlag outputEq, outputEq, ?_, bodyRun⟩
  exact wordPrefix

/-- A successful mutating WETH suffix proves both layers of the vault's
source check: the actual CALL status is `1`, and the copied one-word return is
the canonical ABI encoding of Boolean `true`. -/
theorem checkedCanonicalTrue_success
    {fs : List Func} {sevm : Sevm} {callPre callPost final : Devm}
    {body : Func} {calldata : Bytes} {inputSize gasWord : B256}
    {rest : List B256}
    (occurrence : ExactWethChildOccurrence sevm callPre callPost call
      calldata false)
    (stack : callPre.stack =
      gasWord :: wethAccount.toB256 :: 0 :: 28 :: inputSize :: 0 :: 32 ::
        rest)
    (crossing : Ninst.RunCompiled sevm callPre call callPost)
    (returndataBound : callPost.returnData.length < 2 ^ 256)
    (suffix : Func.RunCompiledTo fs sevm callPost
      (iszero :::
        (Func.rev <?>
          Blanc.ProrataWethVault.requireCanonicalWethTrue body))
      (.ok final)) :
    ∃ bodyPre,
      ExactWethChildSuccess sevm callPre callPost call calldata
        (1 : B256).toBytes false ∧
      Func.RunCompiledTo fs sevm bodyPre body (.ok final) := by
  obtain ⟨status, statusTail, sizePre, statusStack, statusNonzero,
    sizeMemory, sizeReturnData, sizeRun⟩ :=
    checkedCall_status_nonzero suffix
  have successFlag :=
    ExactWethChildOccurrence.successFlag_of_nonzero occurrence
      statusStack statusNonzero
  rw [Blanc.ProrataWethVault.requireCanonicalWethTrue] at sizeRun
  have sizeBound : sizePre.returnData.length < 2 ^ 256 := by
    rw [sizeReturnData]
    exact returndataBound
  obtain ⟨sizeLength, canonicalPre, canonicalMemory, -, canonicalRun⟩ :=
    exactSizeGuard_of_ok sizeBound sizeRun
  have returnDataLength : callPost.returnData.length = 32 := by
    rw [← sizeReturnData]
    exact sizeLength
  have outputWindow := call_outputWindow_of_success stack crossing
    successFlag returnDataLength
  obtain ⟨mloadPre, pushZeroRun, canonicalRun⟩ :=
    runCompiledTo_next_inv canonicalRun
  obtain ⟨pushOnePre, mloadRun, canonicalRun⟩ :=
    runCompiledTo_next_inv canonicalRun
  obtain ⟨eqPre, pushOneRun, canonicalRun⟩ :=
    runCompiledTo_next_inv canonicalRun
  obtain ⟨zeroPre, eqRun, canonicalRun⟩ :=
    runCompiledTo_next_inv canonicalRun
  obtain ⟨branchPre, zeroRun, branchRun⟩ :=
    runCompiledTo_next_inv canonicalRun
  have pushZero := of_run_pushB256 (Ninst.Run.of_runCompiled pushZeroRun)
  have p0 : (0 : B256) :: [] <<+ mloadPre.stack :=
    prefix_of_push pushZero nil_pref
  have pLoad := prefix_of_mload_read
    (Ninst.Run.of_runCompiled mloadRun) p0
  have mloadMemory : mloadPre.memory = callPost.memory :=
    pushZero.memory.symm.trans (canonicalMemory.trans sizeMemory)
  rw [mloadMemory] at pLoad
  simp only [show (0 : B256).toNat = 0 from rfl] at pLoad
  rw [outputWindow] at pLoad
  have pushOne := of_run_pushB256 (Ninst.Run.of_runCompiled pushOneRun)
  have pOne : (1 : B256) :: Bytes.toB256 callPost.returnData :: [] <<+
      eqPre.stack := prefix_of_push pushOne pLoad
  have pEq : ((1 : B256) =? Bytes.toB256 callPost.returnData) :: [] <<+
      zeroPre.stack :=
    prefix_of_eq (Ninst.Run.of_runCompiled eqRun) pOne
  have pZero : (((1 : B256) =? Bytes.toB256 callPost.returnData) =? 0) ::
      [] <<+ branchPre.stack :=
    prefix_of_iszero (Ninst.Run.of_runCompiled zeroRun) pEq
  rcases runCompiledTo_branch_inv branchRun with
    ⟨bodyPre, selectedStack, pop, bodyRun⟩ |
      ⟨_, _, _, _, _, revertRun⟩
  · have zeroPrefix : (0 : B256) :: [] <<+ branchPre.stack := by
      rw [selectedStack]
      exact pref_append [0] bodyPre.stack
    have testZero :
        (((1 : B256) =? Bytes.toB256 callPost.returnData) =? 0) = 0 :=
      pref_head_unique pZero zeroPrefix
    have loadedEq : Bytes.toB256 callPost.returnData = 1 := by
      by_cases equal : (1 : B256) = Bytes.toB256 callPost.returnData
      · exact equal.symm
      · simp [B256.eqCheck, equal] at testZero
        exact (B256.zero_ne_one testZero.symm).elim
    have outputEq : callPost.returnData = (1 : B256).toBytes := by
      calc
        callPost.returnData =
            (Bytes.toB256 callPost.returnData).toBytes :=
          (Bytes.toBytes_toB256_of_length returnDataLength).symm
        _ = (1 : B256).toBytes := congrArg B256.toBytes loadedEq
    exact ⟨bodyPre,
      occurrence.success_of_post successFlag outputEq, bodyRun⟩
  · exact (rev_not_ok revertRun).elim

/-! ## Source-level exact effects and rollback -/

/-- A successful source-level asset query executes the exact configured WETH
program, preserves the whole storage world and log frame, returns the
configured vault's balance, and hands that same word to the source
continuation. -/
theorem readTotalAssets_exactEffect
    {fs : List Func} {sevm : Sevm}
    {entry callPre callPost final : Devm} {image : Bytes} {body : Func}
    (config : DirectWethConfiguration sevm.currentTarget sevm callPre)
    (memory : MemoryImage entry image)
    (staging : Line.Run sevm entry balanceOfStaging callPre)
    (depth : sevm.depth ≠ 0)
    (gasAvailable : StaticGasAvailable callPre 36)
    (crossing : Ninst.RunCompiled sevm callPre statcall callPost)
    (suffix : Func.RunCompiledTo fs sevm callPost
      (iszero :::
        (Func.rev <?>
          (pushB256 32 ::: retdatasize ::: eq ::: iszero :::
            (Func.rev <?> (pushB256 0 ::: mload ::: body)))))
      (.ok final)) :
    ∃ (word : B256) (bodyPre : Devm),
      Devm.getStor callPost = Devm.getStor callPre ∧
      callPost.logs = callPre.logs ∧
      word.toBytes =
          ((callPre.state.getStor wethAccount).get
            sevm.currentTarget.toB256).toBytes ∧
      word :: [] <<+ bodyPre.stack ∧
      Func.RunCompiledTo fs sevm bodyPre body (.ok final) := by
  obtain ⟨gasWord, rest, stack, -⟩ :=
    balanceOfStaging_boundary memory staging
  have occurrence := balanceOfStaging_occurrence config memory staging depth
    gasAvailable crossing
  obtain ⟨status, statusTail, _, statusStack, statusNonzero, _, _, _⟩ :=
    checkedCall_status_nonzero suffix
  have successFlag :=
    ExactWethChildOccurrence.successFlag_of_nonzero occurrence
      statusStack statusNonzero
  have rawSuccess :
      ExactWethChildSuccess sevm callPre callPost statcall
        (balanceOfCalldata sevm.currentTarget) callPost.returnData true :=
    ExactWethChildOccurrence.success_of_post occurrence successFlag rfl
  have worldRun := ExactWethChildSuccess.worldProgramRun rawSuccess
  obtain ⟨storage, logs, output⟩ :=
    SuccessfulWethWorldProgramRun.balanceOf_effect worldRun
  have returnDataLength : callPost.returnData.length = 32 := by
    rw [output, B256.length_toBytes]
  have returndataBound : callPost.returnData.length < 2 ^ 256 := by
    rw [returnDataLength]
    decide +kernel
  obtain ⟨word, bodyPre, _, returnedWord, wordPrefix, bodyRun⟩ :=
    checkedBalanceOf_success occurrence stack crossing returndataBound suffix
  exact ⟨word, bodyPre, storage, logs, returnedWord.symm.trans output,
    wordPrefix, bodyRun⟩

/-- A successful source-level delegated transfer executes exact WETH
`transferFrom(owner,vault,assets)` and exposes its exact balance-row movement
before the vault continuation runs. -/
theorem callWethTransferFrom_exactEffect
    {fs : List Func} {sevm : Sevm}
    {entry callPre callPost final : Devm} {image : Bytes}
    {assetsWord assets : B256} {body : Func}
    (config : DirectWethConfiguration sevm.currentTarget sevm callPre)
    (memory : MemoryImage entry image)
    (assetsAt : ImageWordAt image assetsWord assets)
    (assetsAboveCalldata : 96 ≤ (assetsWord * 32).toNat)
    (staging : Line.Run sevm entry
      (transferFromStaging assetsWord) callPre)
    (depth : sevm.depth ≠ 0)
    (dynamic : sevm.isStatic = false)
    (gasAvailable : CallGasAvailable callPre 100)
    (crossing : Ninst.RunCompiled sevm callPre call callPost)
    (suffix : Func.RunCompiledTo fs sevm callPost
      (iszero :::
        (Func.rev <?>
          Blanc.ProrataWethVault.requireCanonicalWethTrue body))
      (.ok final)) :
    ∃ bodyPre,
      Transfer
          (Stor.rest (callPre.state.getStor wethAccount))
          sevm.caller assets sevm.currentTarget
          (Stor.rest (callPost.state.getStor wethAccount)) ∧
      callPost.returnData = (1 : B256).toBytes ∧
      Func.RunCompiledTo fs sevm bodyPre body (.ok final) := by
  obtain ⟨gasWord, rest, stack, -⟩ :=
    transferFromStaging_boundary memory assetsAt assetsAboveCalldata staging
  have occurrence := transferFromStaging_occurrence config memory assetsAt
    assetsAboveCalldata staging depth dynamic gasAvailable crossing
  obtain ⟨status, statusTail, _, statusStack, statusNonzero, _, _, _⟩ :=
    checkedCall_status_nonzero suffix
  have successFlag :=
    ExactWethChildOccurrence.successFlag_of_nonzero occurrence
      statusStack statusNonzero
  have rawSuccess :
      ExactWethChildSuccess sevm callPre callPost call
        (transferFromCalldata sevm.caller sevm.currentTarget assets)
        callPost.returnData false :=
    ExactWethChildOccurrence.success_of_post occurrence successFlag rfl
  have programRun := ExactWethChildSuccess.programRun rawSuccess
  obtain ⟨movement, output⟩ :=
    SuccessfulWethProgramRun.transferFrom_effect programRun
  have returnDataLength : callPost.returnData.length = 32 := by
    rw [output, B256.length_toBytes]
  have returndataBound : callPost.returnData.length < 2 ^ 256 := by
    rw [returnDataLength]
    decide +kernel
  obtain ⟨bodyPre, _, bodyRun⟩ :=
    checkedCanonicalTrue_success occurrence stack crossing returndataBound
      suffix
  exact ⟨bodyPre, movement, output, bodyRun⟩

/-- A successful source-level outbound transfer executes exact WETH
`transfer(receiver,assets)`, debits the vault, credits the canonical receiver,
and changes no unrelated WETH balance row. -/
theorem callWethTransfer_exactEffect
    {fs : List Func} {sevm : Sevm}
    {entry callPre callPost final : Devm} {image : Bytes}
    {receiverWord assetsWord assets : B256} {receiver : Adr} {body : Func}
    (config : DirectWethConfiguration sevm.currentTarget sevm callPre)
    (memory : MemoryImage entry image)
    (receiverAt : ImageWordAt image receiverWord receiver.toB256)
    (assetsAt : ImageWordAt image assetsWord assets)
    (receiverAboveSelector : 32 ≤ (receiverWord * 32).toNat)
    (assetsAboveReceiver : 64 ≤ (assetsWord * 32).toNat)
    (staging : Line.Run sevm entry
      (transferStaging receiverWord assetsWord) callPre)
    (depth : sevm.depth ≠ 0)
    (dynamic : sevm.isStatic = false)
    (gasAvailable : CallGasAvailable callPre 68)
    (crossing : Ninst.RunCompiled sevm callPre call callPost)
    (suffix : Func.RunCompiledTo fs sevm callPost
      (iszero :::
        (Func.rev <?>
          Blanc.ProrataWethVault.requireCanonicalWethTrue body))
      (.ok final)) :
    ∃ bodyPre,
      Transfer
          (Stor.rest (callPre.state.getStor wethAccount))
          sevm.currentTarget assets receiver
          (Stor.rest (callPost.state.getStor wethAccount)) ∧
      Stor.AgreeOffAdr
          (callPre.state.getStor wethAccount)
          (callPost.state.getStor wethAccount) ∧
      callPost.returnData = (1 : B256).toBytes ∧
      Func.RunCompiledTo fs sevm bodyPre body (.ok final) := by
  obtain ⟨gasWord, rest, stack, -⟩ :=
    transferStaging_boundary memory receiverAt assetsAt
      receiverAboveSelector assetsAboveReceiver staging
  have occurrence := transferStaging_occurrence config memory receiverAt
    assetsAt receiverAboveSelector assetsAboveReceiver staging depth dynamic
    gasAvailable crossing
  obtain ⟨status, statusTail, _, statusStack, statusNonzero, _, _, _⟩ :=
    checkedCall_status_nonzero suffix
  have successFlag :=
    ExactWethChildOccurrence.successFlag_of_nonzero occurrence
      statusStack statusNonzero
  have rawSuccess :
      ExactWethChildSuccess sevm callPre callPost call
        (transferCalldata receiver assets) callPost.returnData false :=
    ExactWethChildOccurrence.success_of_post occurrence successFlag rfl
  have programRun := ExactWethChildSuccess.programRun rawSuccess
  obtain ⟨movement, offAddress, output⟩ :=
    SuccessfulWethProgramRun.transfer_effect programRun
  have returnDataLength : callPost.returnData.length = 32 := by
    rw [output, B256.length_toBytes]
  have returndataBound : callPost.returnData.length < 2 ^ 256 := by
    rw [returnDataLength]
    decide +kernel
  obtain ⟨bodyPre, _, bodyRun⟩ :=
    checkedCanonicalTrue_success occurrence stack crossing returndataBound
      suffix
  exact ⟨bodyPre, movement, offAddress, output, bodyRun⟩

/-- A failed staged asset query exposes no partial WETH write. -/
theorem balanceOfStaging_rollback
    {sevm : Sevm} {entry callPre callPost : Devm} {image : Bytes}
    (config : DirectWethConfiguration sevm.currentTarget sevm callPre)
    (memory : MemoryImage entry image)
    (staging : Line.Run sevm entry balanceOfStaging callPre)
    (depth : sevm.depth ≠ 0)
    (gasAvailable : StaticGasAvailable callPre 36)
    (crossing : Ninst.RunCompiled sevm callPre statcall callPost)
    (failureFlag : ∃ tail, callPost.stack = (0 : B256) :: tail) :
    callPost.state = callPre.state := by
  exact ExactWethChildOccurrence.rollback_of_post
    (balanceOfStaging_occurrence config memory staging depth gasAvailable
      crossing) failureFlag

/-- A failed staged delegated transfer exposes no partial WETH write. -/
theorem transferFromStaging_rollback
    {sevm : Sevm} {entry callPre callPost : Devm} {image : Bytes}
    {assetsWord assets : B256}
    (config : DirectWethConfiguration sevm.currentTarget sevm callPre)
    (memory : MemoryImage entry image)
    (assetsAt : ImageWordAt image assetsWord assets)
    (assetsAboveCalldata : 96 ≤ (assetsWord * 32).toNat)
    (staging : Line.Run sevm entry
      (transferFromStaging assetsWord) callPre)
    (depth : sevm.depth ≠ 0)
    (dynamic : sevm.isStatic = false)
    (gasAvailable : CallGasAvailable callPre 100)
    (crossing : Ninst.RunCompiled sevm callPre call callPost)
    (failureFlag : ∃ tail, callPost.stack = (0 : B256) :: tail) :
    callPost.state = callPre.state := by
  exact ExactWethChildOccurrence.rollback_of_post
    (transferFromStaging_occurrence config memory assetsAt
      assetsAboveCalldata staging depth dynamic gasAvailable crossing)
    failureFlag

/-- A failed staged outbound transfer exposes no partial WETH write. -/
theorem transferStaging_rollback
    {sevm : Sevm} {entry callPre callPost : Devm} {image : Bytes}
    {receiverWord assetsWord assets : B256} {receiver : Adr}
    (config : DirectWethConfiguration sevm.currentTarget sevm callPre)
    (memory : MemoryImage entry image)
    (receiverAt : ImageWordAt image receiverWord receiver.toB256)
    (assetsAt : ImageWordAt image assetsWord assets)
    (receiverAboveSelector : 32 ≤ (receiverWord * 32).toNat)
    (assetsAboveReceiver : 64 ≤ (assetsWord * 32).toNat)
    (staging : Line.Run sevm entry
      (transferStaging receiverWord assetsWord) callPre)
    (depth : sevm.depth ≠ 0)
    (dynamic : sevm.isStatic = false)
    (gasAvailable : CallGasAvailable callPre 68)
    (crossing : Ninst.RunCompiled sevm callPre call callPost)
    (failureFlag : ∃ tail, callPost.stack = (0 : B256) :: tail) :
    callPost.state = callPre.state := by
  exact ExactWethChildOccurrence.rollback_of_post
    (transferStaging_occurrence config memory receiverAt assetsAt
      receiverAboveSelector assetsAboveReceiver staging depth dynamic
      gasAvailable crossing) failureFlag

end Source

end Blanc.Composition.ProrataWethVault
