import Blanc.Lift.Curve3Pool.Walk.Dispatch

/-!
# The dispatcher, arm by arm, on the actual derivation

The views and the ramp entries enter their arms through `Dispatch.lean`'s `xa_dispatch`, which
walks the dispatcher by evaluation: each `xa_vd_*` names the arm's body pc with the state
`St b [] (vdMem sevm) G` and the frame's remaining children unchanged (the dispatcher spawns
nothing).
-/

namespace Blanc.Lift.Curve3Pool

open Jaune Blanc.Lift

/-- The dispatcher's memory: the prologue's image over empty memory. -/
abbrev vdMem (sevm : Sevm) : Mem := vyMem Mem.empty (Sevm.dataWord sevm 0)

section

variable {sevm : Sevm} {post b : Devm} {L : List Exec.Frame} {G : Nat}

/-- **The dispatcher hands `A` its body** (`0x253`), with the prologue's exact memory
and the frame's remaining children unchanged. -/
theorem xa_vd_A (hcode : sevm.code = code)
    (hlen : 4 ≤ sevm.data.length) (hcd : sevm.data.length < 2 ^ 256)
    (hsel : Sevm.selector sevm = selA) (h : XAt sevm post 0 (St b [] Mem.empty G) L) :
    ∃ G', XAt sevm post 0x253 (St b [] (vdMem sevm) G') L :=
  xa_dispatch hcode hlen hcd hsel h

/-- **The dispatcher hands `getVirtualPrice` its body** (`0x91c`), with the prologue's exact memory
and the frame's remaining children unchanged. -/
theorem xa_vd_getVirtualPrice (hcode : sevm.code = code)
    (hlen : 4 ≤ sevm.data.length) (hcd : sevm.data.length < 2 ^ 256)
    (hsel : Sevm.selector sevm = selGetVirtualPrice) (h : XAt sevm post 0 (St b [] Mem.empty G) L) :
    ∃ G', XAt sevm post 0x91c (St b [] (vdMem sevm) G') L :=
  xa_dispatch hcode hlen hcd hsel h

/-- **The dispatcher hands `calcTokenAmount` its body** (`0xb07`), with the prologue's exact memory
and the frame's remaining children unchanged. -/
theorem xa_vd_calcTokenAmount (hcode : sevm.code = code)
    (hlen : 4 ≤ sevm.data.length) (hcd : sevm.data.length < 2 ^ 256)
    (hsel : Sevm.selector sevm = selCalcTokenAmount) (h : XAt sevm post 0 (St b [] Mem.empty G) L) :
    ∃ G', XAt sevm post 0xb07 (St b [] (vdMem sevm) G') L :=
  xa_dispatch hcode hlen hcd hsel h

/-- **The dispatcher hands `getDy` its body** (`0x1d22`), with the prologue's exact memory
and the frame's remaining children unchanged. -/
theorem xa_vd_getDy (hcode : sevm.code = code)
    (hlen : 4 ≤ sevm.data.length) (hcd : sevm.data.length < 2 ^ 256)
    (hsel : Sevm.selector sevm = selGetDy) (h : XAt sevm post 0 (St b [] Mem.empty G) L) :
    ∃ G', XAt sevm post 0x1d22 (St b [] (vdMem sevm) G') L :=
  xa_dispatch hcode hlen hcd hsel h

/-- **The dispatcher hands `getDyUnderlying` its body** (`0x2054`), with the prologue's exact memory
and the frame's remaining children unchanged. -/
theorem xa_vd_getDyUnderlying (hcode : sevm.code = code)
    (hlen : 4 ≤ sevm.data.length) (hcd : sevm.data.length < 2 ^ 256)
    (hsel : Sevm.selector sevm = selGetDyUnderlying) (h : XAt sevm post 0 (St b [] Mem.empty G) L) :
    ∃ G', XAt sevm post 0x2054 (St b [] (vdMem sevm) G') L :=
  xa_dispatch hcode hlen hcd hsel h

/-- **The dispatcher hands `calcWithdrawOneCoin` its body** (`0x4398`), with the prologue's exact memory
and the frame's remaining children unchanged. -/
theorem xa_vd_calcWithdrawOneCoin (hcode : sevm.code = code)
    (hlen : 4 ≤ sevm.data.length) (hcd : sevm.data.length < 2 ^ 256)
    (hsel : Sevm.selector sevm = selCalcWithdrawOneCoin) (h : XAt sevm post 0 (St b [] Mem.empty G) L) :
    ∃ G', XAt sevm post 0x4398 (St b [] (vdMem sevm) G') L :=
  xa_dispatch hcode hlen hcd hsel h

/-- **The dispatcher hands `rampA` its body** (`0x4777`), with the prologue's exact memory
and the frame's remaining children unchanged. -/
theorem xa_vd_rampA (hcode : sevm.code = code)
    (hlen : 4 ≤ sevm.data.length) (hcd : sevm.data.length < 2 ^ 256)
    (hsel : Sevm.selector sevm = selRampA) (h : XAt sevm post 0 (St b [] Mem.empty G) L) :
    ∃ G', XAt sevm post 0x4777 (St b [] (vdMem sevm) G') L :=
  xa_dispatch hcode hlen hcd hsel h

/-- **The dispatcher hands `stopRampA` its body** (`0x491a`), with the prologue's exact memory
and the frame's remaining children unchanged. -/
theorem xa_vd_stopRampA (hcode : sevm.code = code)
    (hlen : 4 ≤ sevm.data.length) (hcd : sevm.data.length < 2 ^ 256)
    (hsel : Sevm.selector sevm = selStopRampA) (h : XAt sevm post 0 (St b [] Mem.empty G) L) :
    ∃ G', XAt sevm post 0x491a (St b [] (vdMem sevm) G') L :=
  xa_dispatch hcode hlen hcd hsel h

end

end Blanc.Lift.Curve3Pool
