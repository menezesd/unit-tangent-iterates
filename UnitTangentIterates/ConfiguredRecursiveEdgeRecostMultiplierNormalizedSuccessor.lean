import UnitTangentIterates.ConfiguredRecursiveEdgeRecostMultiplierNormalizedCompletion
import UnitTangentIterates.ConfiguredRecursiveEdgeRecostedScaledGeometricCoherence

/-!
# Normalized state successor for the diagonal multiplier recursion

The predecessor cell `(n+1,k)` and successor cell `(n,k+1)` share the same
shifted gauge output.  This module assembles the successor normalized state
without identifying the scaled and unscaled source densities.
-/

namespace ConfiguredRecursiveEdgeRecostMultiplierNormalizedSuccessor

open ConfiguredRecursiveEdgeRecostMultiplierNormalizedCompletion
open ConfiguredRecursiveEdgeRecostMultiplierPreCarrier
open ConfiguredRecursiveEdgeRecostedNormalizedReachableState
open ConfiguredRecursiveEdgeRecostedScaledGeometricStep
open FiniteSmoothRearFamilyMarkingAwareActualPullbackStages

noncomputable def nextState
    {Q : ℕ → MarkedSpace.Data} {e : ℕ → ℕ → ℝ}
    {P0 P1 G1 Cg Cprof Qmax : ℕ → ℝ}
    {kappaHat c dlt : ℝ}
    {X : ConfiguredRecursiveEdgeRecostedGeometricState.State
      Q e P0 P1 G1 Cg Cprof Qmax kappaHat c dlt
        ConfiguredCombinedPhysicalDiagonalLargeSeparation.sourceKh}
    (G : StepInput X) (n : ℕ)
    {MA NA Etotal Dtarget : ℝ}
    {RJ : ConfiguredRecursiveEdgeSourceP0RowJetTail.RowJetScalarOutput MA NA}
    {O : ConfiguredRecursiveEdgeFiniteColumnGaugeMajorant.Output RJ Etotal Dtarget}
    {P1Prev edgeDefect P1Next : ℝ}
    (H : State O (X.stage (n + 1)) P1Prev X.depth edgeDefect)
    (hE : Etotal ≤ 1 / 8)
    (hcur : (G.scaled n).eps ≤ O.major (X.depth + 1))
    (hupper : (G.scaled n).slice.periodUpper ≤ P1Next) :
    State O (G.next.stage n) P1Next (X.depth + 1) edgeDefect := by
  let I := G.scaled n
  let K := ConfiguredRecursiveEdgeRecostedScaledGeometricStep.core X (n + 1)
    (G.regularity (n + 1))
  let A := H.nextAncestry K (unscaled I) hE hcur
  refine
    { sourceFacts :=
        { slice := I.slice
          periodUpper_le := hupper
          functional := ?_
          eps := I.eps
          jets := I.sourceJets
          eps_le_major := hcur }
      intrinsic := nextIntrinsic H K I
      periodFloor := ?_
      ancestry := A
      terminalJ_eq := ?_
      terminalP_eq := ?_ }
  · have F :=
      FiniteSmoothRearFamilyMarkingAwareChosenExactFunctionalFacts.ChosenPath.functionalIntegrable_of_exactSource
        K.geometric.output.chosen
    simpa [I.path_eta] using F
  · intro t
    change 1 ≤ FiniteSmoothRearFamilyMarkingAwareAppliedSource.rearPeriod I.source t
    exact ConfiguredRecursiveEdgeRearPeriodFloor.one_le_rearPeriod t
  · dsimp [A]
    rw [State.nextAncestry]
    exact terminal_phi1_eq_scaled I
  · dsimp [A]
    rw [State.nextAncestry]
    exact terminal_period_eq_scaled I

end ConfiguredRecursiveEdgeRecostMultiplierNormalizedSuccessor
