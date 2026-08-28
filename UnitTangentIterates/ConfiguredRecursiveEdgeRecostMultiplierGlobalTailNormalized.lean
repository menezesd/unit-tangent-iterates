import UnitTangentIterates.ConfiguredRecursiveEdgeRecostMultiplierGlobalReachableSystem
import UnitTangentIterates.ConfiguredRecursiveEdgeRecostMultiplierGlobalBaseState
import UnitTangentIterates.ConfiguredRecursiveEdgeRecostMultiplierNormalizedSuccessor
import UnitTangentIterates.ConfiguredRecursiveEdgePhysicalBaseFinalTailState

/-! # Normalized-history certificate on the public tail of a global column -/

noncomputable section

open Function Set MarkedSpace PathMetric

namespace ConfiguredRecursiveEdgeRecostMultiplierGlobalTailNormalized

open ConfiguredRecursiveEdgeRecostMultiplierClosing
  ConfiguredRecursiveEdgeRecostMultiplierGlobalReachableSystem
  ConfiguredRecursiveEdgeRecostedGeometricState
  ConfiguredRecursiveEdgeRecostedNormalizedReachableState
  ConfiguredRecursiveEdgeRecostedScaledGeometricStep

variable {J : ConfiguredRecursiveEdgeSourceP0RowJetTail.RowJetScalarOutput
    ConfiguredRecursiveSourceP0FixedDistortion.choice.MA0
    ConfiguredRecursiveSourceP0FixedDistortion.choice.NA0}
  {O : GaugeOutput J} (R : RecostClosingOutput J O)

variable {Q : ℕ → Data} {e : ℕ → ℕ → ℝ}
  {P0 P1 G1 Cg C Qmax : ℕ → ℝ}
  {kappaHat c dlt : ℝ}

abbrev GlobalState
    (Q : ℕ → Data) (e : ℕ → ℕ → ℝ)
    (P0 P1 G1 Cg C Qmax : ℕ → ℝ) (kappaHat c dlt : ℝ) :=
  State Q e P0 P1 G1 Cg C Qmax kappaHat c dlt
    ConfiguredCombinedPhysicalDiagonalLargeSeparation.sourceKh

abbrev globalData
    (J : ConfiguredRecursiveEdgeSourceP0RowJetTail.RowJetScalarOutput
      ConfiguredRecursiveSourceP0FixedDistortion.choice.MA0
      ConfiguredRecursiveSourceP0FixedDistortion.choice.NA0) :=
  ConfiguredRecursiveEdgeSourceP0CappedRowProduction.D J.scalar

def diagonal
    (X : GlobalState Q e P0 P1 G1 Cg C Qmax kappaHat c dlt)
    (n : ℕ) : ℕ :=
  publicRow R n + X.depth

abbrev stateP1
    (X : GlobalState Q e P0 P1 G1 Cg C Qmax kappaHat c dlt)
    (n : ℕ) : ℝ :=
  ConfiguredRecursiveEdgeSourceP0Growth.edgeP1 (globalData J)
    ConfiguredRecursiveSourceP0FixedDistortion.choice.MA0 (diagonal R X n)

abbrev defect
    (X : GlobalState Q e P0 P1 G1 Cg C Qmax kappaHat c dlt)
    (n : ℕ) : ℝ :=
  ConfiguredRecursiveEdgeSourceP0Growth.edgePhysicalDefect (globalData J)
    (diagonal R X n + 1)

/-- At every public row, retain the exact normalized state whose gauge-major
index is the local diagonal depth. -/
structure TailNormalized
    (X : GlobalState Q e P0 P1 G1 Cg C Qmax kappaHat c dlt) where
  normalized : ∀ n,
    ConfiguredRecursiveEdgeRecostedNormalizedReachableState.State
      ((ConfiguredRecursiveEdgePhysicalBaseFinalTailState.finalGaugeOutput R).shiftOutput
        (n + X.depth))
      (X.stage (publicRow R n)) (stateP1 R X n) X.depth
      (defect R X n)

namespace TailNormalized

/-- The public-tail normalized certificate advances under one global step.
Only the new normalized jet major and period ceiling are needed. -/
noncomputable def next
    {X : GlobalState Q e P0 P1 G1 Cg C Qmax kappaHat c dlt}
    (H : TailNormalized R X) (G : StepInput X)
    (hcur : ∀ n, (G.scaled (publicRow R n)).eps ≤
      ((ConfiguredRecursiveEdgePhysicalBaseFinalTailState.finalGaugeOutput R).shiftOutput
        (n + 1 + X.depth)).major (X.depth + 1))
    (hupper : ∀ n,
      (G.scaled (publicRow R n)).slice.periodUpper ≤
        stateP1 R G.next n) :
    TailNormalized R G.next := by
  refine { normalized := fun n => ?_ }
  have Hprev := H.normalized (n + 1)
  have Hnext :=
    ConfiguredRecursiveEdgeRecostMultiplierNormalizedSuccessor.nextState
      G (publicRow R n) Hprev
      ConfiguredRecursiveEdgeFinitePresentedFinalAssembly.distortionTotal_le_eighth
      (hcur n) (hupper n)
  convert Hnext using 1 <;>
    simp [diagonal, publicRow, StepInput.next, State.next,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  change ConfiguredRecursiveEdgeSourceP0Growth.edgePhysicalDefect _ _ =
    ConfiguredRecursiveEdgeSourceP0Growth.edgePhysicalDefect _ _
  congr 1
  simp [diagonal, publicRow, StepInput.next, State.next,
    Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

end TailNormalized

/-- Concrete successor data sufficient for the reachable provider. -/
structure StepData
    (X : GlobalState Q e P0 P1 G1 Cg C Qmax kappaHat c dlt)
    (H : TailNormalized R X) where
  input : StepInput X
  edgeBudget_le_error : ∀ n,
    (rawMetric input (publicRow R n)).edgeBudget ≤ R.error n X.depth
  eps_le : ∀ n, (input.scaled (publicRow R n)).eps ≤
    ((ConfiguredRecursiveEdgePhysicalBaseFinalTailState.finalGaugeOutput R).shiftOutput
      (n + 1 + X.depth)).major (X.depth + 1)
  periodUpper_le : ∀ n,
    (input.scaled (publicRow R n)).slice.periodUpper ≤
      stateP1 R input.next n

namespace StepData

noncomputable def toReachableStep
    {X : GlobalState Q e P0 P1 G1 Cg C Qmax kappaHat c dlt}
    {H : TailNormalized R X} (I : StepData R X H) :
    ConfiguredRecursiveEdgeRecostMultiplierGlobalReachableSystem.StepData R
      (TailNormalized R) X where
  input := I.input
  edgeBudget_le_error := I.edgeBudget_le_error
  good_next := TailNormalized.next R H I.input I.eps_le I.periodUpper_le

end StepData

end ConfiguredRecursiveEdgeRecostMultiplierGlobalTailNormalized
