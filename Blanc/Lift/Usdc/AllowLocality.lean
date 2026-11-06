import Blanc.Lift.WriteSiteRowClass
import Blanc.AddressSlotProofs
import Blanc.Lift.Usdc.Slots
import Blanc.Lift.Usdc.ImplV1Ws
import Blanc.Lift.Usdc.ImplV2Ws
import Blanc.Lift.Usdc.ImplV2_1Ws

/-! # The allowance-locality law for USDC FiatTokenV1, V2 and V2_1 (unit H3)

`ws_row_locality` at the allowance mapping (slot 10) of the Pair, over each version's certified
root write sites (`implV*Run_ws`).  The frame facts are what the write-site checker certifies: an
allowance write's owner word is `caller` or calldata word 4 (masked to an address), and every root
site carries the dispatcher's selector guard.  `AllowedFrame` reads them: the frame's selector is a
caller-keyed writer and its caller is the Pair, or an owner-word writer and its calldata word 4 is
the Pair, or an initializer.

Per version, `SelTable` lists the selectors; the structural check `allowSiteOk` over the root list
is decided by the kernel, so a wrong table fails the build.

- **V1** (`0x3357162b` initialize only): `approve` is caller-keyed.  Its `transferFrom` write
  `allowed[cd4][caller]` is certified non-increasing: the write-site checker follows solc
  0.4.24's `ISZERO ISZERO ISZERO (GT b a)` guard through three live-symbol closures and a fourth
  learning round (A12).  V1 therefore has no owner-word exception.
- **V2**: caller-keyed `approve`, `increaseAllowance`, `decreaseAllowance`; owner-word (signed)
  `permit` and `approve`/`increase`/`decreaseAllowanceWithAuthorization`; initializers
  `initialize`, `initializeV2`; `transferFrom` is certified non-increasing.
- **V2_1**: as V2 with `permit` the only owner-word writer.

The initializer rows hold the `top` sites (string-copy slots after an `SLOAD`); the consumer
excludes them by the initialized flags (V1 `initialized`, slot 8 byte 20; V2 `_initializedVersion`,
slot 18, for `initializeV2`), under which those entries revert.

`RowSep` is the frame-local collision premise (`WriteSiteRows`). -/

namespace Blanc.Lift.Usdc

open Jaune Blanc Blanc.Lift Blanc.Lift.WriteSite

/-- A root site is allowed by the table, at the allowance mapping (slot 10). -/
abbrev allowSiteOk (t : SelTable) (s : Site) : Bool := rowSiteOk 10 t s

/-- **The allowance law over a checked site list.** -/
theorem allow_locality {t : SelTable} {pair : Adr} {Tr : Adr → Prop} {sites : List Site}
    {ε : Env} (hsel : t.selT.known = true) (hok : sites.all (allowSiteOk t) = true)
    (sep : RowSep 10 pair.toB256 (AllowKey Tr) sites ε)
    {P : Sevm → Devm → Ninst → Devm → Prop} {fs : List SFunc} {sevm : Sevm} {pre post : Devm}
    (run : SProg.RunP (WsStep sites ε P) fs sevm pre post) :
    SProg.RunP (fun s d n d' => P s d n d' ∧
        GuardObs (fun x => ∃ g, Tr g ∧ allowSlot pair g = x) (AllowedFrame t pair ε) s d n)
      fs sevm pre post :=
  row_locality hsel hok sep run

/-! ## The three versions -/

/-- solc 0.4.24's selector word: `and(div(cd0, 2^224), 0xffffffff)`. -/
def selV1T : Term :=
  .op2 .and (.op2 .div (.cd (.const 0x0))
    (.const 0x100000000000000000000000000000000000000000000000000000000)) (.const 0xffffffff)

/-- solc 0.6.12's selector word: `shr(0xe0, cd0)`. -/
def selV2T : Term := .op2 .shr (.const 0xe0) (.cd (.const 0x0))

/-- FiatTokenV1: `approve` caller-keyed; `transferFrom` certified non-increasing;
`initialize`. -/
def selV1 : SelTable := ⟨selV1T, [0x095ea7b3], [], [0x3357162b]⟩

/-- FiatTokenV2: `approve`, `increaseAllowance`, `decreaseAllowance`; `permit` and the three
`*AllowanceWithAuthorization`; `initialize`, `initializeV2`. -/
def selV2 : SelTable :=
  ⟨selV2T, [0x095ea7b3, 0x39509351, 0xa457c2d7], [0xd505accf, 0xe1560fd3, 0xc237108f, 0xb0086095],
    [0x3357162b, 0xd608ea64]⟩

/-- FiatTokenV2_1: as V2, with `permit` the only owner-word writer. -/
def selV2_1 : SelTable :=
  ⟨selV2T, [0x095ea7b3, 0x39509351, 0xa457c2d7], [0xd505accf], [0x3357162b, 0xd608ea64]⟩

theorem implV1_allowSitesOk : (wsRoot ImplV1Ws.implWsAnn).all (allowSiteOk selV1) = true := by
  decide +kernel

theorem implV2_allowSitesOk : (wsRoot ImplV2Ws.implWsAnn).all (allowSiteOk selV2) = true := by
  decide +kernel

theorem implV2_1_allowSitesOk :
    (wsRoot ImplV2_1Ws.implWsAnn).all (allowSiteOk selV2_1) = true := by
  decide +kernel

/-- **Allowance locality, FiatTokenV1**: in an ok run of V1's code, every `SSTORE` to a tracked
allowance row `allowSlot pair g` is non-increasing, or its frame is `approve` called by the Pair,
or `initialize`. -/
theorem implV1_allowLocality {pair : Adr} {Tr : Adr → Prop} {sevm : Sevm} {pre post : Devm}
    (run : Exec 0 sevm pre (.ok post)) (code : sevm.code = ImplV1.code)
    (fork : CoveredFork sevm.benvStat.fork)
    (sep : RowSep 10 pair.toB256 (AllowKey Tr) (wsRoot ImplV1Ws.implWsAnn)
      (WriteSite.Env.root sevm)) :
    SProg.RunP (fun s d n d' => StepIn ⟨0, sevm, pre, .ok post, run⟩ s d n d' ∧
        GuardObs (fun x => ∃ g, Tr g ∧ allowSlot pair g = x)
          (AllowedFrame selV1 pair (WriteSite.Env.root sevm)) s d n)
      ImplV1.cert.prog sevm pre post :=
  allow_locality (by decide) implV1_allowSitesOk sep (implV1Run_ws run code fork)

/-- **Allowance locality, FiatTokenV2**: in an ok run of V2's code, every `SSTORE` to a tracked
allowance row `allowSlot pair g` is non-increasing, or its frame is a caller-keyed allowance writer
called by the Pair, a signed allowance writer whose owner word is the Pair, or an initializer. -/
theorem implV2_allowLocality {pair : Adr} {Tr : Adr → Prop} {sevm : Sevm} {pre post : Devm}
    (run : Exec 0 sevm pre (.ok post)) (code : sevm.code = ImplV2.code)
    (fork : CoveredFork sevm.benvStat.fork)
    (sep : RowSep 10 pair.toB256 (AllowKey Tr) (wsRoot ImplV2Ws.implWsAnn)
      (WriteSite.Env.root sevm)) :
    SProg.RunP (fun s d n d' => StepIn ⟨0, sevm, pre, .ok post, run⟩ s d n d' ∧
        GuardObs (fun x => ∃ g, Tr g ∧ allowSlot pair g = x)
          (AllowedFrame selV2 pair (WriteSite.Env.root sevm)) s d n)
      ImplV2.cert.prog sevm pre post :=
  allow_locality (by decide) implV2_allowSitesOk sep (implV2Run_ws run code fork)

/-- **Allowance locality, FiatTokenV2_1**: as V2, with `permit` the only signed writer. -/
theorem implV2_1_allowLocality {pair : Adr} {Tr : Adr → Prop} {sevm : Sevm} {pre post : Devm}
    (run : Exec 0 sevm pre (.ok post)) (code : sevm.code = ImplV2_1.code)
    (fork : CoveredFork sevm.benvStat.fork)
    (sep : RowSep 10 pair.toB256 (AllowKey Tr) (wsRoot ImplV2_1Ws.implWsAnn)
      (WriteSite.Env.root sevm)) :
    SProg.RunP (fun s d n d' => StepIn ⟨0, sevm, pre, .ok post, run⟩ s d n d' ∧
        GuardObs (fun x => ∃ g, Tr g ∧ allowSlot pair g = x)
          (AllowedFrame selV2_1 pair (WriteSite.Env.root sevm)) s d n)
      ImplV2_1.cert.prog sevm pre post :=
  allow_locality (by decide) implV2_1_allowSitesOk sep (implV2_1Run_ws run code fork)

end Blanc.Lift.Usdc
