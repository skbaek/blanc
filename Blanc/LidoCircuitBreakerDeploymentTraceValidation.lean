-- LidoCircuitBreakerDeploymentTraceValidation.lean : bounded validation walk.
--
-- Named continuation checkpoints keep each source-order constructor check
-- independent of the large memory-image elaboration unit.

import Blanc.LidoCircuitBreakerDeploymentTraceImages

namespace Blanc

open Jaune
open Jaune.Ninst Ninst

namespace LidoCircuitBreaker

/-! ## Gas-exact validation prefix -/

set_option maxRecDepth 4096

/-! The source body is intentionally kept literal above for bytecode-shape
certificates.  These suffix names give proof elaboration bounded continuation
checkpoints without changing that source presentation. -/

private def officialConstructorValidationFinish : Func :=
  pushFixedNat 4282 :::
  pushFixedNat 616 :::
  pushCompactNat constructorRuntimeBase :::
  officialConstructorEffectBody

private def officialConstructorInitialHeartbeatMaxStage : Func :=
  loadArgumentIndex 4 +++
  loadArgumentIndex 6 +++ gt :::
  ((.call 10) <?> officialConstructorValidationFinish)

private def officialConstructorInitialHeartbeatMinStage : Func :=
  loadArgumentIndex 3 +++
  loadArgumentIndex 6 +++ lt :::
  ((.call 9) <?> officialConstructorInitialHeartbeatMaxStage)

private def officialConstructorInitialPauseMaxStage : Func :=
  loadArgumentIndex 2 +++
  loadArgumentIndex 5 +++ gt :::
  ((.call 8) <?> officialConstructorInitialHeartbeatMinStage)

private def officialConstructorInitialPauseMinStage : Func :=
  loadArgumentIndex 1 +++
  loadArgumentIndex 5 +++ lt :::
  ((.call 7) <?> officialConstructorInitialPauseMaxStage)

private def officialConstructorHeartbeatBoundsStage : Func :=
  loadArgumentIndex 4 +++
  loadArgumentIndex 3 +++ gt :::
  ((.call 6) <?> officialConstructorInitialPauseMinStage)

private def officialConstructorMinHeartbeatNonzeroStage : Func :=
  loadArgumentIndex 3 +++ iszero :::
  ((.call 5) <?> officialConstructorHeartbeatBoundsStage)

private def officialConstructorPauseBoundsStage : Func :=
  loadArgumentIndex 2 +++
  loadArgumentIndex 1 +++ gt :::
  ((.call 4) <?> officialConstructorMinHeartbeatNonzeroStage)

private def officialConstructorMinPauseNonzeroStage : Func :=
  loadArgumentIndex 1 +++ iszero :::
  ((.call 3) <?> officialConstructorPauseBoundsStage)

private def officialConstructorAdminNonzeroStage : Func :=
  loadArgumentIndex 0 +++ iszero :::
  ((.call 2) <?> officialConstructorMinPauseNonzeroStage)

private def officialConstructorCanonicalAdminStage : Func :=
  loadArgumentIndex 0 +++ checkNonAddress +++
  ((.call 1) <?> officialConstructorAdminNonzeroStage)

private theorem officialConstructorValidationBody_eq_staged :
    officialConstructorValidationBody =
      pushFixedNat 5122 ::: codesize ::: lt :::
      ((.call 1) <?>
        (pushCompactNat 224 :::
          pushFixedNat 4898 :::
          pushCompactNat 0 :::
          codecopy :::
          officialConstructorCanonicalAdminStage)) := by
  unfold officialConstructorValidationBody
    officialConstructorCanonicalAdminStage
    officialConstructorAdminNonzeroStage
    officialConstructorMinPauseNonzeroStage
    officialConstructorPauseBoundsStage
    officialConstructorMinHeartbeatNonzeroStage
    officialConstructorHeartbeatBoundsStage
    officialConstructorInitialPauseMinStage
    officialConstructorInitialPauseMaxStage
    officialConstructorInitialHeartbeatMinStage
    officialConstructorInitialHeartbeatMaxStage
    officialConstructorValidationFinish
  rfl

private theorem officialConstructorValidationFinish_runCompiled
    {fs : List Func} {sevm : Sevm} {base post : Devm} {G : Nat}
    (hrest : Func.RunCompiled fs sevm
      (base.setMach
        ⟨[(224 : B256), (616 : B256), (4282 : B256)],
          officialConstructorDecodedMemory, G⟩)
      officialConstructorEffectBody post) :
    Func.RunCompiled fs sevm
      (base.setMach ⟨[], officialConstructorDecodedMemory, G + 9⟩)
      officialConstructorValidationFinish post := by
  unfold officialConstructorValidationFinish pushCompactNat pushFixedNat
  simp only [
    if_pos (show 4282 < 2 ^ 16 by decide),
    if_pos (show 616 < 2 ^ 16 by decide)]
  func_run (3)
  exact hrest

private theorem officialConstructorInitialHeartbeatMaxStage_runCompiled
    {fs : List Func} {sevm : Sevm} {base post : Devm} {G : Nat}
    (hrest : Func.RunCompiled fs sevm
      (base.setMach ⟨[], officialConstructorDecodedMemory, G⟩)
      officialConstructorValidationFinish post) :
    Func.RunCompiled fs sevm
      (base.setMach ⟨[], officialConstructorDecodedMemory, G + 28⟩)
      officialConstructorInitialHeartbeatMaxStage post := by
  have hv4 : Bytes.toB256
      ((officialConstructorDecodedMemory.read 128 32).1) =
      officialParams.maxHeartbeatInterval := by
    simpa [officialConstructorArgumentWord] using
      officialConstructorDecodedMemory_read_argument ⟨4, by decide⟩
  have hv6 : Bytes.toB256
      ((officialConstructorDecodedMemory.read 192 32).1) =
      officialConstructorArgs.initialHeartbeatInterval := by
    simpa [officialConstructorArgumentWord] using
      officialConstructorDecodedMemory_read_argument ⟨6, by decide⟩
  have hm4 : (officialConstructorDecodedMemory.read 128 32).2 =
      officialConstructorDecodedMemory := by
    simpa using officialConstructorDecodedMemory_read_memory ⟨4, by decide⟩
  have hm6 : (officialConstructorDecodedMemory.read 192 32).2 =
      officialConstructorDecodedMemory := by
    simpa using officialConstructorDecodedMemory_read_memory ⟨6, by decide⟩
  unfold officialConstructorInitialHeartbeatMaxStage loadArgumentIndex
    pushCompactNat
  func_run (2) [3]
  all_goals try simp only [show (Nat.toB256 128).toNat = 128 by decide]
  all_goals try simp_rw [hm4, hv4]
  all_goals try
    exact Devm.extCost_add_of_size
      (a := gVerylow) officialConstructorDecodedMemory_size (by decide)
  try rw [hm4, hv4]
  func_run (2) [3]
  all_goals try simp only [show (Nat.toB256 192).toNat = 192 by decide]
  all_goals try simp_rw [hm6, hv6]
  all_goals try
    exact Devm.extCost_add_of_size
      (a := gVerylow) officialConstructorDecodedMemory_size (by decide)
  try rw [hm6, hv6]
  func_run (2) [0]
  exact hrest

private theorem officialConstructorInitialHeartbeatMinStage_runCompiled
    {fs : List Func} {sevm : Sevm} {base post : Devm} {G : Nat}
    (hrest : Func.RunCompiled fs sevm
      (base.setMach ⟨[], officialConstructorDecodedMemory, G⟩)
      officialConstructorInitialHeartbeatMaxStage post) :
    Func.RunCompiled fs sevm
      (base.setMach ⟨[], officialConstructorDecodedMemory, G + 28⟩)
      officialConstructorInitialHeartbeatMinStage post := by
  have hv3 : Bytes.toB256
      ((officialConstructorDecodedMemory.read 96 32).1) =
      officialParams.minHeartbeatInterval := by
    simpa [officialConstructorArgumentWord] using
      officialConstructorDecodedMemory_read_argument ⟨3, by decide⟩
  have hv6 : Bytes.toB256
      ((officialConstructorDecodedMemory.read 192 32).1) =
      officialConstructorArgs.initialHeartbeatInterval := by
    simpa [officialConstructorArgumentWord] using
      officialConstructorDecodedMemory_read_argument ⟨6, by decide⟩
  have hm3 : (officialConstructorDecodedMemory.read 96 32).2 =
      officialConstructorDecodedMemory := by
    simpa using officialConstructorDecodedMemory_read_memory ⟨3, by decide⟩
  have hm6 : (officialConstructorDecodedMemory.read 192 32).2 =
      officialConstructorDecodedMemory := by
    simpa using officialConstructorDecodedMemory_read_memory ⟨6, by decide⟩
  unfold officialConstructorInitialHeartbeatMinStage loadArgumentIndex
    pushCompactNat
  func_run (2) [3]
  all_goals try simp only [show (Nat.toB256 96).toNat = 96 by decide]
  all_goals try simp_rw [hm3, hv3]
  all_goals try
    exact Devm.extCost_add_of_size
      (a := gVerylow) officialConstructorDecodedMemory_size (by decide)
  try rw [hm3, hv3]
  func_run (2) [3]
  all_goals try simp only [show (Nat.toB256 192).toNat = 192 by decide]
  all_goals try simp_rw [hm6, hv6]
  all_goals try
    exact Devm.extCost_add_of_size
      (a := gVerylow) officialConstructorDecodedMemory_size (by decide)
  try rw [hm6, hv6]
  func_run (2) [0]
  exact hrest

private theorem officialConstructorInitialPauseMaxStage_runCompiled
    {fs : List Func} {sevm : Sevm} {base post : Devm} {G : Nat}
    (hrest : Func.RunCompiled fs sevm
      (base.setMach ⟨[], officialConstructorDecodedMemory, G⟩)
      officialConstructorInitialHeartbeatMinStage post) :
    Func.RunCompiled fs sevm
      (base.setMach ⟨[], officialConstructorDecodedMemory, G + 28⟩)
      officialConstructorInitialPauseMaxStage post := by
  have hv2 : Bytes.toB256
      ((officialConstructorDecodedMemory.read 64 32).1) =
      officialParams.maxPauseDuration := by
    simpa [officialConstructorArgumentWord] using
      officialConstructorDecodedMemory_read_argument ⟨2, by decide⟩
  have hv5 : Bytes.toB256
      ((officialConstructorDecodedMemory.read 160 32).1) =
      officialConstructorArgs.initialPauseDuration := by
    simpa [officialConstructorArgumentWord] using
      officialConstructorDecodedMemory_read_argument ⟨5, by decide⟩
  have hm2 : (officialConstructorDecodedMemory.read 64 32).2 =
      officialConstructorDecodedMemory := by
    simpa using officialConstructorDecodedMemory_read_memory ⟨2, by decide⟩
  have hm5 : (officialConstructorDecodedMemory.read 160 32).2 =
      officialConstructorDecodedMemory := by
    simpa using officialConstructorDecodedMemory_read_memory ⟨5, by decide⟩
  unfold officialConstructorInitialPauseMaxStage loadArgumentIndex
    pushCompactNat
  func_run (2) [3]
  all_goals try simp only [show (Nat.toB256 64).toNat = 64 by decide]
  all_goals try simp_rw [hm2, hv2]
  all_goals try
    exact Devm.extCost_add_of_size
      (a := gVerylow) officialConstructorDecodedMemory_size (by decide)
  try rw [hm2, hv2]
  func_run (2) [3]
  all_goals try simp only [show (Nat.toB256 160).toNat = 160 by decide]
  all_goals try simp_rw [hm5, hv5]
  all_goals try
    exact Devm.extCost_add_of_size
      (a := gVerylow) officialConstructorDecodedMemory_size (by decide)
  try rw [hm5, hv5]
  func_run (2) [0]
  exact hrest

private theorem officialConstructorInitialPauseMinStage_runCompiled
    {fs : List Func} {sevm : Sevm} {base post : Devm} {G : Nat}
    (hrest : Func.RunCompiled fs sevm
      (base.setMach ⟨[], officialConstructorDecodedMemory, G⟩)
      officialConstructorInitialPauseMaxStage post) :
    Func.RunCompiled fs sevm
      (base.setMach ⟨[], officialConstructorDecodedMemory, G + 28⟩)
      officialConstructorInitialPauseMinStage post := by
  have hv1 : Bytes.toB256
      ((officialConstructorDecodedMemory.read 32 32).1) =
      officialParams.minPauseDuration := by
    simpa [officialConstructorArgumentWord] using
      officialConstructorDecodedMemory_read_argument ⟨1, by decide⟩
  have hv5 : Bytes.toB256
      ((officialConstructorDecodedMemory.read 160 32).1) =
      officialConstructorArgs.initialPauseDuration := by
    simpa [officialConstructorArgumentWord] using
      officialConstructorDecodedMemory_read_argument ⟨5, by decide⟩
  have hm1 : (officialConstructorDecodedMemory.read 32 32).2 =
      officialConstructorDecodedMemory := by
    simpa using officialConstructorDecodedMemory_read_memory ⟨1, by decide⟩
  have hm5 : (officialConstructorDecodedMemory.read 160 32).2 =
      officialConstructorDecodedMemory := by
    simpa using officialConstructorDecodedMemory_read_memory ⟨5, by decide⟩
  unfold officialConstructorInitialPauseMinStage loadArgumentIndex
    pushCompactNat
  func_run (2) [3]
  all_goals try simp only [show (Nat.toB256 32).toNat = 32 by decide]
  all_goals try simp_rw [hm1, hv1]
  all_goals try
    exact Devm.extCost_add_of_size
      (a := gVerylow) officialConstructorDecodedMemory_size (by decide)
  try rw [hm1, hv1]
  func_run (2) [3]
  all_goals try simp only [show (Nat.toB256 160).toNat = 160 by decide]
  all_goals try simp_rw [hm5, hv5]
  all_goals try
    exact Devm.extCost_add_of_size
      (a := gVerylow) officialConstructorDecodedMemory_size (by decide)
  try rw [hm5, hv5]
  func_run (2) [0]
  exact hrest

private theorem officialConstructorHeartbeatBoundsStage_runCompiled
    {fs : List Func} {sevm : Sevm} {base post : Devm} {G : Nat}
    (hrest : Func.RunCompiled fs sevm
      (base.setMach ⟨[], officialConstructorDecodedMemory, G⟩)
      officialConstructorInitialPauseMinStage post) :
    Func.RunCompiled fs sevm
      (base.setMach ⟨[], officialConstructorDecodedMemory, G + 28⟩)
      officialConstructorHeartbeatBoundsStage post := by
  have hv4 : Bytes.toB256
      ((officialConstructorDecodedMemory.read 128 32).1) =
      officialParams.maxHeartbeatInterval := by
    simpa [officialConstructorArgumentWord] using
      officialConstructorDecodedMemory_read_argument ⟨4, by decide⟩
  have hv3 : Bytes.toB256
      ((officialConstructorDecodedMemory.read 96 32).1) =
      officialParams.minHeartbeatInterval := by
    simpa [officialConstructorArgumentWord] using
      officialConstructorDecodedMemory_read_argument ⟨3, by decide⟩
  have hm4 : (officialConstructorDecodedMemory.read 128 32).2 =
      officialConstructorDecodedMemory := by
    simpa using officialConstructorDecodedMemory_read_memory ⟨4, by decide⟩
  have hm3 : (officialConstructorDecodedMemory.read 96 32).2 =
      officialConstructorDecodedMemory := by
    simpa using officialConstructorDecodedMemory_read_memory ⟨3, by decide⟩
  unfold officialConstructorHeartbeatBoundsStage loadArgumentIndex
    pushCompactNat
  func_run (2) [3]
  all_goals try simp only [show (Nat.toB256 128).toNat = 128 by decide]
  all_goals try simp_rw [hm4, hv4]
  all_goals try
    exact Devm.extCost_add_of_size
      (a := gVerylow) officialConstructorDecodedMemory_size (by decide)
  try rw [hm4, hv4]
  func_run (2) [3]
  all_goals try simp only [show (Nat.toB256 96).toNat = 96 by decide]
  all_goals try simp_rw [hm3, hv3]
  all_goals try
    exact Devm.extCost_add_of_size
      (a := gVerylow) officialConstructorDecodedMemory_size (by decide)
  try rw [hm3, hv3]
  func_run (2) [0]
  exact hrest

private theorem officialConstructorMinHeartbeatNonzeroStage_runCompiled
    {fs : List Func} {sevm : Sevm} {base post : Devm} {G : Nat}
    (hrest : Func.RunCompiled fs sevm
      (base.setMach ⟨[], officialConstructorDecodedMemory, G⟩)
      officialConstructorHeartbeatBoundsStage post) :
    Func.RunCompiled fs sevm
      (base.setMach ⟨[], officialConstructorDecodedMemory, G + 22⟩)
      officialConstructorMinHeartbeatNonzeroStage post := by
  have hv3 : Bytes.toB256
      ((officialConstructorDecodedMemory.read 96 32).1) =
      officialParams.minHeartbeatInterval := by
    simpa [officialConstructorArgumentWord] using
      officialConstructorDecodedMemory_read_argument ⟨3, by decide⟩
  have hm3 : (officialConstructorDecodedMemory.read 96 32).2 =
      officialConstructorDecodedMemory := by
    simpa using officialConstructorDecodedMemory_read_memory ⟨3, by decide⟩
  unfold officialConstructorMinHeartbeatNonzeroStage loadArgumentIndex
    pushCompactNat
  func_run (2) [3]
  all_goals try simp only [show (Nat.toB256 96).toNat = 96 by decide]
  all_goals try simp_rw [hm3, hv3]
  all_goals try
    exact Devm.extCost_add_of_size
      (a := gVerylow) officialConstructorDecodedMemory_size (by decide)
  try rw [hm3, hv3]
  func_run (2) [0]
  exact hrest

private theorem officialConstructorPauseBoundsStage_runCompiled
    {fs : List Func} {sevm : Sevm} {base post : Devm} {G : Nat}
    (hrest : Func.RunCompiled fs sevm
      (base.setMach ⟨[], officialConstructorDecodedMemory, G⟩)
      officialConstructorMinHeartbeatNonzeroStage post) :
    Func.RunCompiled fs sevm
      (base.setMach ⟨[], officialConstructorDecodedMemory, G + 28⟩)
      officialConstructorPauseBoundsStage post := by
  have hv2 : Bytes.toB256
      ((officialConstructorDecodedMemory.read 64 32).1) =
      officialParams.maxPauseDuration := by
    simpa [officialConstructorArgumentWord] using
      officialConstructorDecodedMemory_read_argument ⟨2, by decide⟩
  have hv1 : Bytes.toB256
      ((officialConstructorDecodedMemory.read 32 32).1) =
      officialParams.minPauseDuration := by
    simpa [officialConstructorArgumentWord] using
      officialConstructorDecodedMemory_read_argument ⟨1, by decide⟩
  have hm2 : (officialConstructorDecodedMemory.read 64 32).2 =
      officialConstructorDecodedMemory := by
    simpa using officialConstructorDecodedMemory_read_memory ⟨2, by decide⟩
  have hm1 : (officialConstructorDecodedMemory.read 32 32).2 =
      officialConstructorDecodedMemory := by
    simpa using officialConstructorDecodedMemory_read_memory ⟨1, by decide⟩
  unfold officialConstructorPauseBoundsStage loadArgumentIndex pushCompactNat
  func_run (2) [3]
  all_goals try simp only [show (Nat.toB256 64).toNat = 64 by decide]
  all_goals try simp_rw [hm2, hv2]
  all_goals try
    exact Devm.extCost_add_of_size
      (a := gVerylow) officialConstructorDecodedMemory_size (by decide)
  try rw [hm2, hv2]
  func_run (2) [3]
  all_goals try simp only [show (Nat.toB256 32).toNat = 32 by decide]
  all_goals try simp_rw [hm1, hv1]
  all_goals try
    exact Devm.extCost_add_of_size
      (a := gVerylow) officialConstructorDecodedMemory_size (by decide)
  try rw [hm1, hv1]
  func_run (2) [0]
  exact hrest

private theorem officialConstructorMinPauseNonzeroStage_runCompiled
    {fs : List Func} {sevm : Sevm} {base post : Devm} {G : Nat}
    (hrest : Func.RunCompiled fs sevm
      (base.setMach ⟨[], officialConstructorDecodedMemory, G⟩)
      officialConstructorPauseBoundsStage post) :
    Func.RunCompiled fs sevm
      (base.setMach ⟨[], officialConstructorDecodedMemory, G + 22⟩)
      officialConstructorMinPauseNonzeroStage post := by
  have hv1 : Bytes.toB256
      ((officialConstructorDecodedMemory.read 32 32).1) =
      officialParams.minPauseDuration := by
    simpa [officialConstructorArgumentWord] using
      officialConstructorDecodedMemory_read_argument ⟨1, by decide⟩
  have hm1 : (officialConstructorDecodedMemory.read 32 32).2 =
      officialConstructorDecodedMemory := by
    simpa using officialConstructorDecodedMemory_read_memory ⟨1, by decide⟩
  unfold officialConstructorMinPauseNonzeroStage loadArgumentIndex pushCompactNat
  func_run (2) [3]
  all_goals try simp only [show (Nat.toB256 32).toNat = 32 by decide]
  all_goals try simp_rw [hm1, hv1]
  all_goals try
    exact Devm.extCost_add_of_size
      (a := gVerylow) officialConstructorDecodedMemory_size (by decide)
  try rw [hm1, hv1]
  func_run (2) [0]
  exact hrest

private theorem officialConstructorAdminNonzeroStage_runCompiled
    {fs : List Func} {sevm : Sevm} {base post : Devm} {G : Nat}
    (hrest : Func.RunCompiled fs sevm
      (base.setMach ⟨[], officialConstructorDecodedMemory, G⟩)
      officialConstructorMinPauseNonzeroStage post) :
    Func.RunCompiled fs sevm
      (base.setMach ⟨[], officialConstructorDecodedMemory, G + 21⟩)
      officialConstructorAdminNonzeroStage post := by
  have hv0 : Bytes.toB256
      ((officialConstructorDecodedMemory.read 0 32).1) =
      officialParams.admin := by
    simpa [officialConstructorArgumentWord] using
      officialConstructorDecodedMemory_read_argument ⟨0, by decide⟩
  have hm0 : (officialConstructorDecodedMemory.read 0 32).2 =
      officialConstructorDecodedMemory := by
    simpa using officialConstructorDecodedMemory_read_memory ⟨0, by decide⟩
  unfold officialConstructorAdminNonzeroStage loadArgumentIndex pushCompactNat
  func_run (2) [3]
  all_goals try simp only [show (Nat.toB256 0).toNat = 0 by decide]
  all_goals try simp_rw [hm0, hv0]
  all_goals try
    exact Devm.extCost_add_of_size
      (a := gVerylow) officialConstructorDecodedMemory_size (by decide)
  try rw [hm0, hv0]
  func_run (2) [0]
  exact hrest

private theorem officialConstructorCanonicalAdminStage_runCompiled
    {fs : List Func} {sevm : Sevm} {base post : Devm} {G : Nat}
    (hrest : Func.RunCompiled fs sevm
      (base.setMach ⟨[], officialConstructorDecodedMemory, G⟩)
      officialConstructorAdminNonzeroStage post) :
    Func.RunCompiled fs sevm
      (base.setMach ⟨[], officialConstructorDecodedMemory, G + 32⟩)
      officialConstructorCanonicalAdminStage post := by
  have hv0 : Bytes.toB256
      ((officialConstructorDecodedMemory.read 0 32).1) =
      officialParams.admin := by
    simpa [officialConstructorArgumentWord] using
      officialConstructorDecodedMemory_read_argument ⟨0, by decide⟩
  have hm0 : (officialConstructorDecodedMemory.read 0 32).2 =
      officialConstructorDecodedMemory := by
    simpa using officialConstructorDecodedMemory_read_memory ⟨0, by decide⟩
  unfold officialConstructorCanonicalAdminStage loadArgumentIndex
    pushCompactNat checkNonAddress pushAddressMask
  func_run (2) [3]
  all_goals try simp only [show (Nat.toB256 0).toNat = 0 by decide]
  all_goals try simp_rw [hm0, hv0]
  all_goals try
    exact Devm.extCost_add_of_size
      (a := gVerylow) officialConstructorDecodedMemory_size (by decide)
  try rw [hm0, hv0]
  func_run (6) [~~~(0 : B256), addressMask, 0]
  exact hrest

private theorem officialConstructorValidationDecode_runCompiled
    {fs : List Func} {sevm : Sevm} {base post : Devm} {G : Nat}
    (hvalue : sevm.value = 0)
    (hcode : sevm.code.toList = officialFullCreateInput)
    (hrest : Func.RunCompiled fs sevm
      (base.setMach ⟨[], officialConstructorDecodedMemory, G⟩)
      officialConstructorCanonicalAdminStage post) :
    Func.RunCompiled fs sevm
      (base.setMach ⟨[], Mem.empty, G + 93⟩)
      lidoCircuitBreakerConstructorProgram.main post := by
  have hcodeSize : sevm.code.size = 5122 := by
    rw [ByteArray.size_eq_length_toList, hcode,
      officialFullCreateInput_length_exact]
  rw [lidoCircuitBreakerConstructorProgram_main_official,
    officialConstructorValidationBody_eq_staged]
  simp only [pushFixedNat,
    if_pos (show 5122 < 2 ^ 16 by decide),
    if_pos (show 4898 < 2 ^ 16 by decide)]
  unfold pushCompactNat
  func_run (11) [1, 0, 45]
  all_goals try simp [B256.eqCheck, hvalue]
  all_goals try simp_rw [hcodeSize]
  all_goals try
    exact Devm.extCost_add_of_size
      (a := gVerylow + gasCopy * ceilDiv 224 32) rfl (by decide)
  all_goals try decide +kernel
  simp only [show (Nat.toB256 0).toNat = 0 by decide,
    show (Bytes.toB256 [19, 34]).toNat = 4898 by decide,
    show (Nat.toB256 224).toNat = 224 by decide]
  have hslice : sevm.code.sliceD 4898 224 (0 : UInt8) =
      abiEncodeConstructorArgs officialConstructorArgs := by
    rw [show (0 : UInt8) = Linst.toUInt8 .stop by decide]
    exact officialFullCreateInput_slice_constructorArgs hcode
  rw [hslice]
  have hdecoded :
      Mem.empty.write 0 (abiEncodeConstructorArgs officialConstructorArgs) =
        officialConstructorDecodedMemory := by
    rfl
  rw [hdecoded]
  exact hrest

theorem officialConstructorValidationPrefix_runCompiled
    {sevm : Sevm} {base post : Devm} {g : Nat}
    (hvalue : sevm.value = 0)
    (hcode : sevm.code.toList = officialFullCreateInput)
    (hgas : 367 ≤ g)
    (hrest : Func.RunCompiled
      (lidoCircuitBreakerConstructorProgram.main ::
        lidoCircuitBreakerConstructorProgram.aux)
      sevm
      (base.setMach
        ⟨[(224 : B256), (616 : B256), (4282 : B256)],
          officialConstructorDecodedMemory, g - 367⟩)
      officialConstructorEffectBody post) :
    Func.RunCompiled
      (lidoCircuitBreakerConstructorProgram.main ::
        lidoCircuitBreakerConstructorProgram.aux)
      sevm (base.setMach ⟨[], Mem.empty, g⟩)
      lidoCircuitBreakerConstructorProgram.main post := by
  have hfinish :=
    officialConstructorValidationFinish_runCompiled hrest
  have hheartbeatMax :=
    officialConstructorInitialHeartbeatMaxStage_runCompiled hfinish
  have hheartbeatMin :=
    officialConstructorInitialHeartbeatMinStage_runCompiled hheartbeatMax
  have hpauseMax :=
    officialConstructorInitialPauseMaxStage_runCompiled hheartbeatMin
  have hpauseMin :=
    officialConstructorInitialPauseMinStage_runCompiled hpauseMax
  have hheartbeatBounds :=
    officialConstructorHeartbeatBoundsStage_runCompiled hpauseMin
  have hheartbeatNonzero :=
    officialConstructorMinHeartbeatNonzeroStage_runCompiled hheartbeatBounds
  have hpauseBounds :=
    officialConstructorPauseBoundsStage_runCompiled hheartbeatNonzero
  have hpauseNonzero :=
    officialConstructorMinPauseNonzeroStage_runCompiled hpauseBounds
  have hadmin :=
    officialConstructorAdminNonzeroStage_runCompiled hpauseNonzero
  have hcanonical :=
    officialConstructorCanonicalAdminStage_runCompiled hadmin
  have hdecode :=
    officialConstructorValidationDecode_runCompiled hvalue hcode hcanonical
  have hgasExact :
      g - 367 + 9 + 28 + 28 + 28 + 28 + 28 + 22 + 28 + 22 + 21 + 32 +
        93 = g := by
    omega
  simpa only [hgasExact] using hdecode

end LidoCircuitBreaker

end Blanc
