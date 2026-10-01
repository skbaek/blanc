import Blanc.ExecutionTrace

/-!
Exact request-output composition for retained request-system traces. The
incoming request prefix and both checked system-call outputs remain arbitrary.
Payload validity, contract behavior and FIFO provenance are separate claims.
-/

namespace Blanc.ExecutionTrace

open Jaune

/-- A nonempty payload contributes one request prefixed by its type byte. -/
def optionalRequestEntry (requestType : UInt8) (payload : Bytes) : List Bytes :=
  if payload.length > 0 then [[requestType] ++ payload] else []

/-- Omission depends only on payload emptiness, for any request type. -/
theorem optionalRequestEntry_eq_nil_iff (requestType : UInt8) (payload : Bytes) :
    optionalRequestEntry requestType payload = [] ↔ payload = [] := by
  by_cases empty : payload = []
  · rw [empty]
    simp only [optionalRequestEntry, List.length_nil, Nat.lt_irrefl, ite_false]
  · have positive : payload.length > 0 := List.length_pos_iff.mpr empty
    simp only [optionalRequestEntry, ite_eq_left positive, List.cons_ne_nil, empty]

theorem optionalRequestEntry_of_nonempty (requestType : UInt8) {payload : Bytes}
    (nonempty : payload ≠ []) :
    optionalRequestEntry requestType payload = [[requestType] ++ payload] := by
  exact ite_eq_left (List.length_pos_iff.mpr nonempty)

theorem append_optionalRequestEntry (prior : List Bytes) (requestType : UInt8)
    (payload : Bytes) :
    (if payload.length > 0 then prior ++ [[requestType] ++ payload] else prior) =
      prior ++ optionalRequestEntry requestType payload := by
  by_cases positive : payload.length > 0
  · simp only [optionalRequestEntry, ite_eq_left positive]
  · simp only [optionalRequestEntry, ite_eq_right positive, List.append_nil]

/-- The retained request pass appends deposits, withdrawal and consolidation
output in that order, omitting exactly the entries with empty payloads. -/
theorem RequestsTrace.requests_eq
    {benv : Benv} {bout : BlockOutput} {state : State} {bout' : BlockOutput}
    (trace : RequestsTrace benv bout state bout') :
    bout'.requests = bout.requests ++ optionalRequestEntry 0 trace.depositRequests ++
      optionalRequestEntry 1 trace.withdrawalOut.returnData ++
      optionalRequestEntry 2 trace.consolidationOut.returnData := by
  have run := trace.run
  unfold processGeneralPurposeRequests processGeneralPurposeRequestsAt at run
  rw [trace.parsed, trace.requestShape] at run
  simp only [runRequestContracts, trace.withdrawalRun, trace.consolidationRun,
    Except.bind, bind, depositRequestType, append_optionalRequestEntry] at run
  exact (congrArg (fun result : State × BlockOutput => result.2.requests)
    (Except.ok.inj run)).symm

end Blanc.ExecutionTrace
