-- DRIP's exact runtime source: fail-closed ingress, one shared fresh-index
-- machine, checked Maker-shaped rpow, and checks-effects-interactions exit.

import Blanc.DripCore

namespace Blanc

open Jaune
open Jaune.Ninst Ninst

namespace Drip

def freshStartSlot : Nat := 1
def rpowLoopSlot : Nat := 2
def rpowAfterSquareSlot : Nat := 3
def rpowAdvanceSlot : Nat := 4
def composeFreshSlot : Nat := 5
def freshRouteSlot : Nat := 6

def routeConvertToAssets : B256 := 1
def routeExit : B256 := 2
def routeConvertToUnits : B256 := 3
def routeDrip : B256 := 4
def routeJoin : B256 := 5

def routeWord : B256 := 1
def argumentWord : B256 := 2
def rowWord : B256 := 3
def totalWord : B256 := 4
def storedChiWord : B256 := 5
def nowWord : B256 := 6
def exponentWord : B256 := 7
def baseWord : B256 := 8
def accumulatorWord : B256 := 9
def freshChiWord : B256 := 10
def resultWord : B256 := 11
def newRowWord : B256 := 12
def newTotalWord : B256 := 13
def roundedWord : B256 := 14

def loadWord (word : B256) : Line :=
  [pushB256 (word * 32), mload]

def exactCalldata (size : B256) (body : Func) : Func :=
  pushB256 size ::: calldatasize ::: eq ::: (body <?> .revert)

def stageRoute (route : B256) : Line :=
  [pushB256 route] ++ mstoreAt routeWord

def guardedRoundedMul
    (leftWord rightWord outputWord : B256) (next : Func) : Func :=
  loadWord leftWord +++
  loadWord rightWord +++
  mul :::
  dup 0 :::
  loadWord rightWord +++
  swap 0 :::
  div :::
  loadWord leftWord +++
  eq :::
  iszero :::
  (.revert <?>
    (dup 0 :::
      pushB256 half :::
      add :::
      dup 0 :::
      mstoreAt roundedWord +++
      lt :::
      (.revert <?>
        (loadWord roundedWord +++
          pushB256 scale :::
          swap 0 :::
          div :::
          mstoreAt outputWord +++
          next))))

def composeFresh : Func :=
  loadWord storedChiWord +++
  loadWord accumulatorWord +++
  mul :::
  dup 0 :::
  loadWord accumulatorWord +++
  swap 0 :::
  div :::
  loadWord storedChiWord +++
  eq :::
  iszero :::
  (.revert <?>
    (pushB256 scale :::
      swap 0 :::
      div :::
      dup 0 :::
      mstoreAt freshChiWord +++
      pushB256 maxChi :::
      lt :::
      (.revert <?> .call freshRouteSlot)))

def rpowAdvance : Func :=
  loadWord exponentWord +++
  pushB256 2 :::
  swap 0 :::
  div :::
  mstoreAt exponentWord +++
  .call rpowLoopSlot

def rpowAfterSquare : Func :=
  loadWord exponentWord +++
  pushB256 1 :::
  and :::
  (guardedRoundedMul accumulatorWord baseWord accumulatorWord
      (.call rpowAdvanceSlot) <?>
    .call rpowAdvanceSlot)

def rpowLoop : Func :=
  loadWord exponentWord +++
  iszero :::
  (.call composeFreshSlot <?>
    guardedRoundedMul baseWord baseWord baseWord
      (.call rpowAfterSquareSlot))

def freshStart : Func :=
  let initializeNonzeroBase : Func :=
    let halveExponent : Func :=
      loadWord exponentWord +++
      pushB256 2 :::
      swap 0 :::
      div :::
      mstoreAt exponentWord +++
      .call rpowLoopSlot
    loadWord exponentWord +++
    iszero :::
    ((pushB256 scale :::
        mstoreAt accumulatorWord +++
        .call composeFreshSlot) <?>
      (loadWord exponentWord +++
        pushB256 1 :::
        and :::
        ((pushB256 rate :::
            mstoreAt accumulatorWord +++
            halveExponent) <?>
          (pushB256 scale :::
            mstoreAt accumulatorWord +++
            halveExponent))))
  let initializeRpow : Func :=
    pushB256 rate :::
    dup 0 :::
    mstoreAt baseWord +++
    iszero :::
    ((loadWord exponentWord +++
        iszero :::
        ((pushB256 scale :::
            mstoreAt accumulatorWord +++
            .call composeFreshSlot) <?>
          (pushB256 0 :::
            mstoreAt accumulatorWord +++
            .call composeFreshSlot))) <?>
      initializeNonzeroBase)
  let checkElapsed : Func :=
    loadWord exponentWord +++
    pushB256 maxElapsed :::
    lt :::
    (.revert <?> initializeRpow)
  let stageElapsed : Func :=
    pushB256 rhoSlot :::
    sload :::
    loadWord nowWord +++
    sub :::
    mstoreAt exponentWord +++
    checkElapsed
  let checkClock : Func :=
    pushB256 rhoSlot :::
    sload :::
    loadWord nowWord +++
    lt :::
    (.revert <?> stageElapsed)
  let stageClock : Func :=
    timestamp :::
    mstoreAt nowWord +++
    checkClock
  let checkUpperChi : Func :=
    loadWord storedChiWord +++
    pushB256 maxChi :::
    lt :::
    (.revert <?> stageClock)
  let checkLowerChi : Func :=
    pushB256 scale :::
    loadWord storedChiWord +++
    lt :::
    (.revert <?> checkUpperChi)
  pushB256 chiSlot :::
  sload :::
  mstoreAt storedChiWord +++
  checkLowerChi

def commitFresh : Line :=
  loadWord freshChiWord ++ [pushB256 chiSlot, sstore] ++
  loadWord nowWord ++ [pushB256 rhoSlot, sstore]

def returnScratch (word : B256) : Func :=
  loadWord word +++ mstoreAt 0 +++ returnMemoryRange 0 32

def afterDrip : Func :=
  commitFresh +++ returnScratch freshChiWord

def afterConvertToAssets : Func :=
  loadWord argumentWord +++
  loadWord freshChiWord +++
  mul :::
  pushB256 scale :::
  swap 0 :::
  div :::
  mstoreAt resultWord +++
  returnScratch resultWord

def afterConvertToUnits : Func :=
  loadWord argumentWord +++
  pushB256 scale :::
  mul :::
  loadWord freshChiWord +++
  swap 0 :::
  div :::
  mstoreAt resultWord +++
  returnScratch resultWord

def afterJoin : Func :=
  let commit : Func :=
    commitFresh +++
    loadWord newRowWord +++
    caller :::
    sstore :::
    loadWord newTotalWord +++
    pushB256 totalUnitsSlot :::
    sstore :::
    returnScratch resultWord
  let checkTotal : Func :=
    loadWord totalWord +++
    loadWord resultWord +++
    add :::
    dup 0 :::
    mstoreAt newTotalWord +++
    pushB256 maxPie :::
    lt :::
    (.revert <?> commit)
  loadWord argumentWord +++
  pushB256 scale :::
  mul :::
  loadWord freshChiWord +++
  swap 0 :::
  div :::
  dup 0 :::
  mstoreAt resultWord +++
  loadWord rowWord +++
  add :::
  dup 0 :::
  mstoreAt newRowWord +++
  pushB256 maxUnits :::
  lt :::
  (.revert <?> checkTotal)

def sendToCaller : Line :=
  pushList [0, 0, 0, 0] ++
  swap 3 :: caller :: gas :: call :: []

def afterExit : Func :=
  let returnOnSuccess : Func := returnScratch resultWord
  let callRecipient : Func :=
    loadWord resultWord +++
    sendToCaller +++
    (returnOnSuccess <?> .revert)
  let commit : Func :=
    commitFresh +++
    loadWord argumentWord +++
    loadWord rowWord +++
    sub :::
    caller :::
    sstore :::
    loadWord argumentWord +++
    loadWord totalWord +++
    sub :::
    pushB256 totalUnitsSlot :::
    sstore :::
    callRecipient
  loadWord argumentWord +++
  loadWord freshChiWord +++
  mul :::
  pushB256 scale :::
  swap 0 :::
  div :::
  mstoreAt resultWord +++
  commit

def freshRoute : Func :=
  let joinRoute : Func :=
    pushB256 routeJoin :::
    eq :::
    (afterJoin <?> .revert)
  let dripRoute : Func :=
    dup 0 :::
    pushB256 routeDrip :::
    eq :::
    ((pop ::: afterDrip) <?> joinRoute)
  let unitsRoute : Func :=
    dup 0 :::
    pushB256 routeConvertToUnits :::
    eq :::
    ((pop ::: afterConvertToUnits) <?> dripRoute)
  let exitRoute : Func :=
    dup 0 :::
    pushB256 routeExit :::
    eq :::
    ((pop ::: afterExit) <?> unitsRoute)
  loadWord routeWord +++
  dup 0 :::
  pushB256 routeConvertToAssets :::
  eq :::
  ((pop ::: afterConvertToAssets) <?> exitRoute)

def convertToAssets : Func :=
  arg 0 +++
  dup 0 :::
  mstoreAt argumentWord +++
  pushB256 maxUnits :::
  lt :::
  (.revert <?>
    (stageRoute routeConvertToAssets +++ .call freshStartSlot))

def convertToUnits : Func :=
  arg 0 +++
  dup 0 :::
  mstoreAt argumentWord +++
  pushB256 maxAsset :::
  lt :::
  (.revert <?>
    (stageRoute routeConvertToUnits +++ .call freshStartSlot))

def drip : Func :=
  stageRoute routeDrip +++ .call freshStartSlot

def join : Func :=
  let stageTotal : Func :=
    pushB256 totalUnitsSlot :::
    sload :::
    dup 0 :::
    mstoreAt totalWord +++
    pushB256 maxPie :::
    lt :::
    (.revert <?>
      (stageRoute routeJoin +++ .call freshStartSlot))
  let stageRow : Func :=
    caller :::
    sload :::
    dup 0 :::
    mstoreAt rowWord +++
    pushB256 maxUnits :::
    lt :::
    (.revert <?> stageTotal)
  callvalue :::
  dup 0 :::
  mstoreAt argumentWord +++
  pushB256 maxAsset :::
  lt :::
  (.revert <?> stageRow)

def exit : Func :=
  let checkTotalSufficient : Func :=
    loadWord argumentWord +++
    loadWord totalWord +++
    lt :::
    (.revert <?>
      (stageRoute routeExit +++ .call freshStartSlot))
  let checkRowSufficient : Func :=
    loadWord argumentWord +++
    loadWord rowWord +++
    lt :::
    (.revert <?> checkTotalSufficient)
  let stageTotal : Func :=
    pushB256 totalUnitsSlot :::
    sload :::
    dup 0 :::
    mstoreAt totalWord +++
    pushB256 maxPie :::
    lt :::
    (.revert <?> checkRowSufficient)
  let stageRow : Func :=
    caller :::
    sload :::
    dup 0 :::
    mstoreAt rowWord +++
    pushB256 maxUnits :::
    lt :::
    (.revert <?> stageTotal)
  arg 0 +++
  dup 0 :::
  mstoreAt argumentWord +++
  pushB256 maxUnits :::
  lt :::
  (.revert <?> stageRow)

def funcs : List (B256 × Func) :=
  [ (convertToAssetsSelector, nonpayable (exactCalldata 36 convertToAssets)),
    (exitSelector, nonpayable (exactCalldata 36 exit)),
    (convertToUnitsSelector, nonpayable (exactCalldata 36 convertToUnits)),
    (dripSelector, nonpayable (exactCalldata 4 drip)),
    (joinSelector, exactCalldata 4 join) ]

theorem funcs_sorted : DispatchTree.sorted funcs = true := by
  decide +kernel

def tree : DispatchTree := DispatchTree.ofSorted funcs

def main : Func :=
  calldatasize ::: (Func.main tree <?> Func.stop)

def aux : List Func :=
  [freshStart, rpowLoop, rpowAfterSquare, rpowAdvance, composeFresh, freshRoute]

def runtime : Prog := ⟨main, aux⟩

end Drip

end Blanc
