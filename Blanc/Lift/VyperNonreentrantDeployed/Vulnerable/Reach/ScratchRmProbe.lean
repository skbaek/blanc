import Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Reach.ViolRemoveRun1
import Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Reach.ViolCallback
import Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Frame1Kernel
import Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Reach.ViolRemoveRun4

namespace Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Reach.Viol

open Jaune Blanc.Lift Blanc.Lift.Witness Blanc.Lift.NodeWalk Blanc.ConcreteRun
open Blanc.Lift.VyperNonreentrantDeployed

def mProbe : Meta := (default : Devm).meta

def wProbe : World := (default : Devm).world

/-- Probe child: the callback settled machine with observed gas/output/error. -/
def dCbProbe : Devm := childObs gasCb [] default

def cRm339Probe : Cfg := cRm339 [] [] mProbe wProbe

def resumeRmProbe : Option Cfg :=
  callResume sRm cRm339Probe dCbProbe keysCb adrsCb storCb acsCb

def x1Probe : Res :=
  match resumeRmProbe with
  | some c => wrun fsI sRm 3 c
  | none => .stuck

def x2Probe : Res :=
  match x1Probe with
  | .cont c => wrun fsI sRm 220 c
  | _ => .stuck

def x2keys : List (Adr × B256) :=
  match x2Probe with
  | .cont c => c.keys
  | _ => []

#eval decide (x2keys = [(proxyAddr, (8 : Nat).toB256), (proxyAddr, (26 : Nat).toB256),
  (proxyAddr, (2 : Nat).toB256)] ++ keysCb)

#eval match x2Probe with
  | .cont c => some (c.adrs, c.stor)
  | _ => none

#eval match x2Probe with
  | .cont c => some (c.acs.map Boundary.acctKey, c.devm.returnData.length)
  | _ => none

def cTok3Probe : Cfg :=
  match wrun fsI sRm 234 (resumeRmProbe.getD (Boundary.cfgOfT bRm0 [] [] mProbe wProbe)) with
  | .cont c => c
  | _ => Boundary.cfgOfT bRm0 [] [] mProbe wProbe

def tokDoneProbe : Option (Devm × Cfg) :=
  match childRun Token20.prog Token20.code sRm 200 cTok3Probe with
  | .done (.halted d) cl => some (d, cl)
  | _ => none

def resume2Probe : Option Cfg :=
  match tokDoneProbe with
  | some (d, cl) => callResume sRm cTok3Probe d cl.keys cl.adrs cl.stor cl.acs
  | _ => none

def x3Probe : Res :=
  match resume2Probe with
  | some c => wrun fsI sRm 3 c
  | none => .stuck

#eval match x3Probe with
  | .cont c => some (c.adrs.take 24, c.adrs.drop 24)
  | _ => none

#eval adrsRm.length

#eval match x2Probe with
  | .cont c => some (c.devm.returnData.length, c.devm.returnData.take 40,
      (c.devm.returnData.drop 40).take 40, c.devm.returnData.drop 80)
  | _ => none

#eval match x3Probe with
  | .cont c => some (c.stor, c.acs.map Boundary.acctKey)
  | _ => none

#eval match tokDoneProbe with
  | some (_, cl) => some (cl.stor, cl.acs.map Boundary.acctKey)
  | _ => none

#eval match cTok3Probe with
  | c => some (c.stor.length, c.stor.take 3)

#eval match x2Probe with
  | .cont c => some ((c.devm.returnData.map UInt8.toNat).take 20,
      ((c.devm.returnData.map UInt8.toNat).drop 20).take 20,
      ((c.devm.returnData.map UInt8.toNat).drop 40).take 20,
      ((c.devm.returnData.map UInt8.toNat).drop 60).take 20,
      (c.devm.returnData.map UInt8.toNat).drop 80)
  | _ => none

#eval match x1Probe with
  | .cont c => some (((c.devm.mach.memory.data.toList.map UInt8.toNat).drop 0).take 40,
      ((c.devm.mach.memory.data.toList.map UInt8.toNat).drop 40).take 40,
      ((c.devm.mach.memory.data.toList.map UInt8.toNat).drop 80).take 40,
      ((c.devm.mach.memory.data.toList.map UInt8.toNat).drop 120).take 40)
  | _ => none

#eval match x1Probe with
  | .cont c => some (((c.devm.mach.memory.data.toList.map UInt8.toNat).drop 160).take 40,
      ((c.devm.mach.memory.data.toList.map UInt8.toNat).drop 200).take 40,
      ((c.devm.mach.memory.data.toList.map UInt8.toNat).drop 240).take 40,
      ((c.devm.mach.memory.data.toList.map UInt8.toNat).drop 280).take 40)
  | _ => none

#eval match x1Probe with
  | .cont c => some (((c.devm.mach.memory.data.toList.map UInt8.toNat).drop 320).take 40,
      ((c.devm.mach.memory.data.toList.map UInt8.toNat).drop 360).take 40,
      ((c.devm.mach.memory.data.toList.map UInt8.toNat).drop 400).take 40,
      ((c.devm.mach.memory.data.toList.map UInt8.toNat).drop 440).take 40)
  | _ => none

#eval match x2Probe with
  | .cont c => some (((c.devm.mach.memory.data.toList.map UInt8.toNat).drop 0).take 40,
      ((c.devm.mach.memory.data.toList.map UInt8.toNat).drop 40).take 40,
      ((c.devm.mach.memory.data.toList.map UInt8.toNat).drop 80).take 40,
      ((c.devm.mach.memory.data.toList.map UInt8.toNat).drop 120).take 40)
  | _ => none

#eval match x2Probe with
  | .cont c => some (((c.devm.mach.memory.data.toList.map UInt8.toNat).drop 160).take 40,
      ((c.devm.mach.memory.data.toList.map UInt8.toNat).drop 200).take 40,
      ((c.devm.mach.memory.data.toList.map UInt8.toNat).drop 240).take 40,
      ((c.devm.mach.memory.data.toList.map UInt8.toNat).drop 280).take 40)
  | _ => none

#eval match x2Probe with
  | .cont c => some (((c.devm.mach.memory.data.toList.map UInt8.toNat).drop 320).take 40,
      ((c.devm.mach.memory.data.toList.map UInt8.toNat).drop 360).take 40,
      ((c.devm.mach.memory.data.toList.map UInt8.toNat).drop 400).take 40,
      ((c.devm.mach.memory.data.toList.map UInt8.toNat).drop 440).take 40)
  | _ => none

#eval match x2Probe with
  | .cont c => some (((c.devm.mach.memory.data.toList.map UInt8.toNat).drop 480).take 40,
      ((c.devm.mach.memory.data.toList.map UInt8.toNat).drop 520).take 40,
      ((c.devm.mach.memory.data.toList.map UInt8.toNat).drop 560).take 40,
      ((c.devm.mach.memory.data.toList.map UInt8.toNat).drop 600).take 40)
  | _ => none

#eval match x2Probe with
  | .cont c => some (((c.devm.mach.memory.data.toList.map UInt8.toNat).drop 640).take 40,
      ((c.devm.mach.memory.data.toList.map UInt8.toNat).drop 680).take 40,
      ((c.devm.mach.memory.data.toList.map UInt8.toNat).drop 720).take 40,
      ((c.devm.mach.memory.data.toList.map UInt8.toNat).drop 760).take 40)
  | _ => none

#eval match x2Probe with
  | .cont c => some (((c.devm.mach.memory.data.toList.map UInt8.toNat).drop 800).take 40,
      ((c.devm.mach.memory.data.toList.map UInt8.toNat).drop 840).take 40,
      ((c.devm.mach.memory.data.toList.map UInt8.toNat).drop 880).take 40,
      ((c.devm.mach.memory.data.toList.map UInt8.toNat).drop 920).take 40)
  | _ => none

#eval match x3Probe with
  | .cont c => some (c.devm.mach.memory.data.toList.length,
      ((c.devm.mach.memory.data.toList.map UInt8.toNat).drop 0).take 40,
      ((c.devm.mach.memory.data.toList.map UInt8.toNat).drop 40).take 40,
      ((c.devm.mach.memory.data.toList.map UInt8.toNat).drop 80).take 40,
      ((c.devm.mach.memory.data.toList.map UInt8.toNat).drop 120).take 40)
  | _ => none

#eval match x3Probe with
  | .cont c => some (((c.devm.mach.memory.data.toList.map UInt8.toNat).drop 160).take 40,
      ((c.devm.mach.memory.data.toList.map UInt8.toNat).drop 200).take 40,
      ((c.devm.mach.memory.data.toList.map UInt8.toNat).drop 240).take 40,
      ((c.devm.mach.memory.data.toList.map UInt8.toNat).drop 280).take 40)
  | _ => none

#eval match x3Probe with
  | .cont c => some (((c.devm.mach.memory.data.toList.map UInt8.toNat).drop 320).take 40,
      ((c.devm.mach.memory.data.toList.map UInt8.toNat).drop 360).take 40,
      ((c.devm.mach.memory.data.toList.map UInt8.toNat).drop 400).take 40,
      ((c.devm.mach.memory.data.toList.map UInt8.toNat).drop 440).take 40)
  | _ => none

#eval match x3Probe with
  | .cont c => some (((c.devm.mach.memory.data.toList.map UInt8.toNat).drop 480).take 40,
      ((c.devm.mach.memory.data.toList.map UInt8.toNat).drop 520).take 40,
      ((c.devm.mach.memory.data.toList.map UInt8.toNat).drop 560).take 40,
      ((c.devm.mach.memory.data.toList.map UInt8.toNat).drop 600).take 40)
  | _ => none

#eval match x3Probe with
  | .cont c => some (((c.devm.mach.memory.data.toList.map UInt8.toNat).drop 640).take 40,
      ((c.devm.mach.memory.data.toList.map UInt8.toNat).drop 680).take 40,
      ((c.devm.mach.memory.data.toList.map UInt8.toNat).drop 720).take 40,
      ((c.devm.mach.memory.data.toList.map UInt8.toNat).drop 760).take 40)
  | _ => none

#eval match x3Probe with
  | .cont c => some (((c.devm.mach.memory.data.toList.map UInt8.toNat).drop 800).take 40,
      ((c.devm.mach.memory.data.toList.map UInt8.toNat).drop 840).take 40,
      ((c.devm.mach.memory.data.toList.map UInt8.toNat).drop 880).take 40,
      ((c.devm.mach.memory.data.toList.map UInt8.toNat).drop 920).take 40)
  | _ => none

#eval match x1Probe with
  | .cont c => some (((c.devm.mach.memory.data.toList.map UInt8.toNat).mapIdx
      (fun i b => (i, b))).filter (fun (p : Nat × Nat) => p.2 != 0))
  | _ => none

#eval match x3Probe with
  | .cont c => some (((c.devm.mach.memory.data.toList.map UInt8.toNat).drop 600).take 20,
      ((c.devm.mach.memory.data.toList.map UInt8.toNat).drop 620).take 20,
      ((c.devm.mach.memory.data.toList.map UInt8.toNat).drop 920).take 20,
      ((c.devm.mach.memory.data.toList.map UInt8.toNat).drop 940).take 20)
  | _ => none

-- X1 component checks against the `bRmX1` claim (empty tails).
#eval match x1Probe with
  | .cont c => some (c.devm.mach.memory.data.toList.length,
      c.devm.output.map UInt8.toNat, (c.devm.returnData.map UInt8.toNat),
      c.devm.error.isNone, c.devm.refundCounter,
      c.devm.accountsToDelete.toList.length, c.K.length)
  | _ => none

-- RLE printer: emits X1 memory as ready-to-paste Lean source.
def rleEnc : List Nat → List (Nat × Nat)
  | [] => []
  | b :: bs => go b 1 bs
where go (cur n : Nat) : List Nat → List (Nat × Nat)
  | [] => [(cur, n)]
  | b :: bs => if b == cur then go cur (n + 1) bs else (cur, n) :: go b 1 bs

def hexOf : Nat → String
  | 0 => "0x00"
  | 1 => "0x01"
  | 3 => "0x03"
  | 4 => "0x04"
  | 5 => "0x05"
  | 7 => "0x07"
  | 62 => "0x3e"
  | 68 => "0x44"
  | 100 => "0x64"
  | 113 => "0x71"
  | 156 => "0x9c"
  | 159 => "0x9f"
  | 169 => "0xa9"
  | 177 => "0xb1"
  | 187 => "0xbb"
  | 208 => "0xd0"
  | 232 => "0xe8"
  | 62 => "0x3e"
  | 68 => "0x44"
  | 100 => "0x64"
  | 113 => "0x71"
  | 159 => "0x9f"
  | 177 => "0xb1"
  | 208 => "0xd0"
  | 232 => "0xe8"
  | n => toString n

def segOf : Nat × Nat → String
  | (v, n) => if v == 0 then s!"List.replicate {n} 0"
      else s!"List.replicate {n} {hexOf v}"

def rleSrc (rle : List (Nat × Nat)) : String :=
  String.intercalate " ++ " (rle.map segOf)

#eval match x1Probe with
  | .cont c => some (rleEnc (c.devm.mach.memory.data.toList.map UInt8.toNat))
  | _ => none

#eval match x1Probe with
  | .cont c => rleSrc (rleEnc (c.devm.mach.memory.data.toList.map UInt8.toNat))
  | _ => ""

-- X2 component checks against the `bRmX2` draft (empty tails).
#eval match x2Probe with
  | .cont c => some (decide (c.devm.mach.stack =
      [(100 : Nat).toB256, (736 : Nat).toB256, (2 : Nat).toB256,
        (448 : Nat).toB256, (1051816351 : Nat).toB256]),
      decide (c.devm.mach.gasLeft = 847667),
      decide (c.devm.mach.memory.size = 1024),
      c.devm.mach.memory.data.toList.length)
  | _ => none

#eval match x2Probe with
  | .cont c => some (decide (c.keys =
      [(proxyAddr, (8 : Nat).toB256), (proxyAddr, (26 : Nat).toB256),
        (proxyAddr, (2 : Nat).toB256)] ++ keysCb),
      decide (c.adrs = [(4 : Adr), (4 : Adr), attackerAddr, (4 : Adr), implAddr,
        proxyAddr] ++ adrsCb),
      decide (c.stor = [((proxyAddr, (9 : Nat).toB256), (900 : Nat).toB256)] ++ storCb),
      decide (c.acs.map Boundary.acctKey =
        ([((4 : Adr), (⟨0, (0 : Nat).toB256, .empty, .empty⟩ : Acct)),
          (proxyAddr, (⟨1, (1000 : Nat).toB256, .empty, fwdCode⟩ : Acct)),
          ((4 : Adr), (⟨0, (0 : Nat).toB256, .empty, .empty⟩ : Acct)),
          (proxyAddr, (⟨1, (1000 : Nat).toB256, .empty, fwdCode⟩ : Acct))] ++
          acsCb).map Boundary.acctKey),
      c.acs.length)
  | _ => none

#eval match x2Probe with
  | .cont c => some (c.devm.output.map UInt8.toNat,
      (c.devm.returnData.map UInt8.toNat).length, c.devm.error.isNone,
      c.devm.refundCounter, c.devm.accountsToDelete.toList.length, c.K.length)
  | _ => none

#eval match x2Probe with
  | .cont c => (rleEnc (c.devm.mach.memory.data.toList.map UInt8.toNat)).length
  | _ => 0

#eval match x2Probe with
  | .cont c => rleSrc ((rleEnc (c.devm.mach.memory.data.toList.map UInt8.toNat)).take 24)
  | _ => ""

#eval match x2Probe with
  | .cont c => rleSrc ((rleEnc (c.devm.mach.memory.data.toList.map UInt8.toNat)).drop 24)
  | _ => ""

#eval match x2Probe with
  | .cont c => rleSrc (rleEnc (c.devm.returnData.map UInt8.toNat))
  | _ => ""

-- Token child result (empty tails): gas, output, error, shadow lengths.
#eval match tokDoneProbe with
  | some (d, cl) => some (d.gasLeft, d.output.map UInt8.toNat, d.error.isNone,
      cl.keys.length, cl.adrs.length, cl.stor.length, cl.acs.length)
  | _ => none

-- X3 shape (empty tails): machine scalars, shadow lengths, bookkeeping.
#eval match x3Probe with
  | .cont c => some (c.devm.mach.stack.length, c.devm.mach.gasLeft,
      c.devm.mach.memory.size, c.devm.mach.memory.data.toList.length,
      c.keys.length, c.adrs.length, c.stor.length, c.acs.length,
      c.devm.output.map UInt8.toNat, (c.devm.returnData.map UInt8.toNat).length,
      c.devm.error.isNone, c.devm.refundCounter,
      c.devm.accountsToDelete.toList.length, c.K.length)
  | _ => none

-- Full halt after 188 more steps from X3 (empty tails).
def x4Probe : Res :=
  match x3Probe with
  | .cont c => wrun fsI sRm 188 c
  | _ => .stuck

#eval match x4Probe with
  | .done (.halted d) cl => some (d.gasLeft, d.output.map UInt8.toNat,
      d.error.isNone, (lookupS cl.stor proxyAddr (26 : Nat).toB256).toNat,
      (lookupS cl.stor proxyAddr lpSlotA).toNat,
      (lookupS cl.stor proxyAddr (2 : Nat).toB256).toNat,
      cl.keys.length, cl.adrs.length)
  | _ => none

#eval (gasRm, gasTok, keysRm.length, adrsRm.length, outRm.length,
  decide (gasRm = 810345))

-- End-to-end: 188 steps from the `bRmX3` literal (empty tails).
#eval match wrun fsI sRm 188 (Boundary.cfgOfT bRmX3 [] [] mProbe wProbe) with
  | .done (.halted d) cl => some (d.gasLeft, d.output.map UInt8.toNat,
      d.error.isNone, (lookupS cl.stor proxyAddr (26 : Nat).toB256).toNat,
      (lookupS cl.stor proxyAddr lpSlotA).toNat,
      (lookupS cl.stor proxyAddr (2 : Nat).toB256).toNat,
      cl.keys.length, cl.adrs.length)
  | _ => none

-- Token CALL 11 steps after X2 (empty tails).
def tokCallProbe : Res :=
  match x2Probe with
  | .cont c => wrun fsI sRm 11 c
  | _ => .stuck

def tokCpProbe : Option CallPrep :=
  match tokCallProbe with
  | .cont c => callPrep sRm c
  | _ => none

#eval match tokCallProbe with
  | .cont c => some (c.keys.length, c.adrs.length, c.stor.length, c.acs.length,
      c.devm.mach.gasLeft, c.devm.mach.memory.size, c.K.length,
      c.devm.error.isNone)
  | _ => none

#eval match tokCpProbe with
  | some cp => match tokCallProbe with
    | .cont c => match frameEnterS cp.f c.acs with
      | .run e => some (decide (e.sta.currentTarget = tokenAddr),
          decide (e.sta.value = 0),
          decide (e.sta.code.data.toList = Token20.code.data.toList),
          frameEntryForkFree cp.f)
      | _ => none
    | _ => none
  | _ => none

-- Token halt shadows (empty tails): full keys/adrs/stor, acs keys + suffix split.
#eval match tokDoneProbe with
  | some (_, cl) => some (cl.keys, cl.adrs, cl.stor.take 6,
      decide ((cl.stor.drop 2) = storCb), decide ((cl.stor.drop 3) = storCb),
      decide ((cl.stor.drop 4) = storCb))
  | _ => none

-- (acs detail covered by acctInfo probes below)

#eval match x3Probe with
  | .cont c => rleSrc ((rleEnc (c.devm.mach.memory.data.toList.map UInt8.toNat)).take 20)
  | _ => ""

#eval match x3Probe with
  | .cont c => rleSrc ((rleEnc (c.devm.mach.memory.data.toList.map UInt8.toNat)).drop 20)
  | _ => ""

-- X3 shadows (empty tails).
#eval match x3Probe with
  | .cont c => some (c.keys.length, c.adrs.length, c.stor.take 6,
      decide ((c.stor.drop 2) = storCb), decide ((c.stor.drop 3) = storCb),
      decide ((c.stor.drop 4) = storCb))
  | _ => none

#eval match x3Probe with
  | .cont c => some (c.acs.map Boundary.acctKey,
      decide (((c.acs.drop 4).map Boundary.acctKey) = acsCb.map Boundary.acctKey),
      decide (((c.acs.drop 6).map Boundary.acctKey) = acsCb.map Boundary.acctKey),
      (c.acs.take 6).map (fun (p : Adr × Acct) => (p.1, p.2.nonce, p.2.stor.toList.length,
        p.2.code.data.toList.length)))
  | _ => none

def acctInfo (p : Adr × Acct) : Adr × UInt64 × Nat × Nat × Bool × Bool × Bool :=
  (p.1, p.2.nonce, p.2.stor.toList.length, p.2.code.data.toList.length,
    p.2.code.data.toList == Token20.code.data.toList,
    p.2.code.data.toList == fwdCode.data.toList,
    p.2.code.data.toList == ([] : List UInt8))

#eval match tokDoneProbe with
  | some (_, cl) => some (
      decide (((cl.acs.drop 4).map Boundary.acctKey) = acsCb.map Boundary.acctKey),
      decide (((cl.acs.drop 6).map Boundary.acctKey) = acsCb.map Boundary.acctKey),
      (cl.acs.take 6).map acctInfo,
      (cl.acs.take 6).map (fun (p : Adr × Acct) => p.2.stor.toList))
  | _ => none

#eval match x3Probe with
  | .cont c => some (
      decide (((c.acs.drop 4).map Boundary.acctKey) = acsCb.map Boundary.acctKey),
      decide (((c.acs.drop 6).map Boundary.acctKey) = acsCb.map Boundary.acctKey),
      (c.acs.take 6).map acctInfo,
      (c.acs.take 6).map (fun (p : Adr × Acct) => p.2.stor.toList))
  | _ => none

def wordNat (b : B256) : Nat := b.toNat

#eval match x3Probe with
  | .cont c => some (c.devm.mach.stack.map wordNat)
  | _ => none

#eval match tokDoneProbe with
  | some (_, cl) => some (decide (cl.stor =
      [((tokenAddr, (389733769954907444854315955391008805241582011460 : Nat).toB256),
        (100 : Nat).toB256),
       ((tokenAddr, (487167212443634306067894944238761006551977514325 : Nat).toB256),
        (900 : Nat).toB256),
       ((proxyAddr, (9 : Nat).toB256), (900 : Nat).toB256)] ++ storCb))
  | _ => none

#eval some (decide ((match x3Probe with | .cont c => c.stor | _ => []) =
    (match tokDoneProbe with | some (_, cl) => cl.stor | _ => [])))

#eval match x3Probe with
  | .cont c => some (c.keys, c.adrs)
  | _ => none

#eval match x3Probe with
  | .cont c => rleSrc (rleEnc (c.devm.returnData.map UInt8.toNat))
  | _ => ""

#eval (decide ((858993459, 3689348814741910323, 3689348814741910323) = tokenAddr),
  decide ((1431655765, 6148914691236517205, 6148914691236517205) = proxyAddr),
  decide ((1145324612, 4919131752989213764, 4919131752989213764) = attackerAddr))

#eval let tk := (match tokDoneProbe with | some (_, cl) => cl.keys | _ => []);
  let x3k := (match x3Probe with | .cont c => c.keys | _ => []);
  (decide (tk = [(tokenAddr, (389733769954907444854315955391008805241582011460 : Nat).toB256),
      (tokenAddr, (487167212443634306067894944238761006551977514325 : Nat).toB256),
      (proxyAddr, (7 : Nat).toB256), (proxyAddr, (8 : Nat).toB256),
      (proxyAddr, (26 : Nat).toB256), (proxyAddr, (2 : Nat).toB256)] ++ keysCb),
    decide (x3k = (tk.drop 2) ++ tk))

#eval let ta := (match tokDoneProbe with | some (_, cl) => cl.adrs | _ => []);
  let x3a := (match x3Probe with | .cont c => c.adrs | _ => []);
  (decide (ta = [tokenAddr, (4 : Adr), (4 : Adr), attackerAddr, (4 : Adr), implAddr,
      proxyAddr] ++ adrsCb),
    decide (x3a = ta ++ ta))

#eval let x3a := (match x3Probe with | .cont c => c.acs | _ => []);
  let tka := (match tokDoneProbe with | some (_, cl) => cl.acs | _ => []);
  (decide (x3a = tka))

#eval resKeys (childRun Token20.prog Token20.code sRm 200 cTok3Probe)

#eval match x1Probe with
  | .cont c => some (decide (c.keys =
      [(proxyAddr, (8 : Nat).toB256), (proxyAddr, (26 : Nat).toB256),
        (proxyAddr, (2 : Nat).toB256)] ++ keysCb),
      decide (c.adrs = [attackerAddr, (4 : Adr), implAddr, proxyAddr] ++ adrsCb),
      decide (c.stor = storCb),
      decide (c.acs.map Boundary.acctKey = acsCb.map Boundary.acctKey),
      c.acs.length, acsCb.length)
  | _ => none

#eval match x1Probe with
  | .cont c => some (decide (c.devm.mach.stack =
      [(2 : Nat).toB256, (448 : Nat).toB256, (1051816351 : Nat).toB256]),
      decide (c.devm.mach.gasLeft = 851668),
      decide (c.devm.mach.memory.size = 640))
  | _ => none
