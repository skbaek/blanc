import Blanc.Lift.BuilderRequest.Exit.Fifo
import Blanc.Lift.BuilderRequest.Latch

/-!
# The exit builder's calldata latch, under Amsterdam

**Build target.** Jaune pin `e8db2742`, built on `tests@v21.0.1`, EELS `1562e2f`; the bytes and `sys-asm`
`83f9801`, not the EIP text, which calls the inhibition permanent. These bytes reverse it: `latch_cycle`.
Nothing here says that a real block makes such a call: the request phase passes empty calldata
(`request_step_no_latch`).
-/

namespace Blanc.Lift.BuilderRequest.Exit

open Jaune
open RequestSystem
open Creation (address)

/-- **The exit builder's latch, from any storage.** Under Amsterdam, with the canonical code installed,
a checked system call with nonempty calldata returns within 161,000 regular gas (state gas excluded: it draws
on the reservoir of 16 × `storageSet`). Its post state is exactly `latchState`: the same pointer moves as the
empty-calldata call, slot 0 at the inhibitor, the count cleared. It returns what the empty-calldata call
returns. `hlen` says `CALLDATASIZE` reads the length faithfully: a list of `2 ^ 256` bytes would read as 0. -/
theorem latch_call {benv : Benv} {data : Bytes} (hfork : benv.stat.fork = .amsterdam)
    (installed : benv.state.getCode address = code) (hne : data ≠ []) (hlen : data.length < 2 ^ 256) :
    ∃ out emptyOut,
      processCheckedSystemTransaction benv address data =
        .ok (latchState sysShape benv.state address, out) ∧
      RegularGasWithin out.gasLeft 161000 ∧
      processCheckedSystemTransaction benv address [] =
        .ok (sysState sysShape benv.state address, emptyOut) ∧
      out.returnData = emptyOut.returnData :=
  latch_headline sysCall sysOutput sysWords rfl rfl hfork installed hne hlen

/-- **The exit builder's latch on a queue.** On storage representing a queue, the latch returns the oldest
`min(length, 16)` records and leaves the drained queue with slot 0 at the inhibitor and the count cleared. -/
theorem latch_fifo {benv : Benv} {data : Bytes} (hfork : benv.stat.fork = .amsterdam)
    (installed : benv.state.getCode address = code) (hne : data ≠ []) (hlen : data.length < 2 ^ 256)
    {st : QueueState Record} (rep : Represents 3 Record.word (storOf benv.state address) st) :
    ∃ post out, processCheckedSystemTransaction benv address data = .ok (post, out) ∧
      RegularGasWithin out.gasLeft 161000 ∧
      out.returnData = (st.queue.take 16).flatMap Record.out ∧
      Represents 3 Record.word (storOf post address)
        { drainedState 16 2 st with excess := 2 ^ 256 - 1 } := by
  obtain ⟨out, emptyOut, h1, g1, h2, hr⟩ := latch_call hfork installed hne hlen
  obtain ⟨_, out', h3, _, hout, _⟩ := system_call_fifo hfork installed rep
  rw [h2] at h3
  obtain ⟨-, rfl⟩ := Prod.mk.inj (Except.ok.inj h3)
  exact ⟨_, _, h1, g1, hr.trans hout, represents_latchState sysShape (by decide) rfl rep⟩

/-- **The exit builder's latch is reversible**, from any storage: after the latch, slot 0 is the
inhibitor, and the next empty-calldata call succeeds within 161,000 regular gas (state gas excluded) and moves
slot 0 to 0. -/
theorem latch_cycle {benv : Benv} {data : Bytes} (hfork : benv.stat.fork = .amsterdam)
    (installed : benv.state.getCode address = code) (hne : data ≠ []) (hlen : data.length < 2 ^ 256) :
    ∃ out out',
      processCheckedSystemTransaction benv address data =
        .ok (latchState sysShape benv.state address, out) ∧
      ((latchState sysShape benv.state address).getStor address).get 0 = B256.max ∧
      processCheckedSystemTransaction (benv.withState (latchState sysShape benv.state address)) address [] =
        .ok (sysState sysShape (latchState sysShape benv.state address) address, out') ∧
      RegularGasWithin out'.gasLeft 161000 ∧
      ((sysState sysShape (latchState sysShape benv.state address) address).getStor address).get 0 = 0 :=
  BuilderRequest.latch_cycle sysCall sysWords rfl rfl rfl hfork installed hne hlen

end Blanc.Lift.BuilderRequest.Exit
