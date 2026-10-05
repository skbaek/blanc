import Blanc.Lift.VyperNonreentrantDeployed.Fixed.Reach.Deploy

/-! # The creations' settled worlds as terms

`setup_creations` states the worlds messages 1 and 2 settle to account by account.  A following
message whose kernel walk prices `SSTORE` against its block-original state (its input world)
needs that world as an explicit term: `implState W` and `setupState W` are the settled worlds
as the same `State` operations Jaune applies (`CreateEntry.entryState`, the constructor's
`SSTORE`, the code installation), and `setup_creations_exact` identifies them. -/

namespace Blanc.Lift.VyperNonreentrantDeployed.Fixed.Reach

open Jaune Blanc.Lift

/-- The settled world after message 1, as a term of the starting world. -/
def implState (W : State) : State :=
  ((CreateEntry.entryState W creator implAddr).setStorVal implAddr 1 1).setCode implAddr
    Blanc.Lift.VyperNonreentrantDeployed.Fixed.code

/-- The settled world after messages 1 and 2, as a term of the starting world. -/
def setupState (W : State) : State :=
  (CreateEntry.entryState (implState W) creator proxyAddr).setCode proxyAddr
    (Blanc.forwarderCode Blanc.curvePlainImpl847e)

/-- **The creations' settled worlds, exactly.** -/
theorem setup_creations_exact (fork : Fork) (hfork : CoveredFork fork) (W : State) :
    ∀ postI postP : Devm,
      processCreateMessage (implCreateMsg fork W) = .ok postI →
      processCreateMessage (cloneCreateMsg fork postI.state) = .ok postP →
      postI.state = implState W ∧ postP.state = setupState W := by
  intro postI postP h1 h2
  obtain ⟨qI, hq1, -, -, -, -, sI⟩ :=
    Creation.create_impl_exact (implCreateMsg fork W) hfork rfl rfl rfl rfl
      (by change 3690218 ≤ 4000000; decide)
  obtain ⟨qP, hq2, -, -, -, -, sP⟩ :=
    Clone.create_clone_exact (cloneCreateMsg fork postI.state) hfork rfl rfl rfl
      (by change 9028 ≤ 100000; decide)
  have eI : postI = qI := by rw [h1] at hq1; cases hq1; rfl
  have eP : postP = qP := by rw [h2] at hq2; cases hq2; rfl
  subst eI eP
  have hsI : postI.state = implState W := sI rfl
  refine ⟨hsI, ?_⟩
  rw [sP rfl]
  change (CreateEntry.entryState postI.state creator proxyAddr).setCode proxyAddr _ = _
  rw [hsI]
  rfl

end Blanc.Lift.VyperNonreentrantDeployed.Fixed.Reach
