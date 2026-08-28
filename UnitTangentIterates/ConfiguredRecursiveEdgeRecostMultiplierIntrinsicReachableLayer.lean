import UnitTangentIterates.ConfiguredRecursiveEdgeRecostMultiplierIntrinsicDiagonalRows
import UnitTangentIterates.ConfiguredRecursiveEdgeRecostMultiplierNormalizedCompletion
import UnitTangentIterates.ConfiguredRecursiveEdgeRecostMultiplierRowBudget
import UnitTangentIterates.ConfiguredRecursiveEdgePhysicalBaseFinalTailState

/-! # Reachable normalized layers on intrinsically typed nodes -/

noncomputable section

open Function Set MarkedSpace PathMetric
open scoped BigOperators

namespace ConfiguredRecursiveEdgeRecostMultiplierIntrinsicReachableLayer

open ConfiguredRecursiveEdgeRecostMultiplierClosing
  ConfiguredRecursiveEdgeRecostMultiplierIntrinsicDiagonalRows
  ConfiguredRecursiveEdgeRecostMultiplierNormalizedCompletion
  ConfiguredRecursiveEdgeRecostMultiplierPreCarrier
  ConfiguredRecursiveEdgeRecostMultiplierRowBudget
  ConfiguredRecursiveEdgeRecostedNormalizedReachableState
  ConfiguredRecursiveEdgeRecostedScaledPreCarrier
  FiniteSmoothRearFamilyMarkingAwareFullyPhysicalJacobi

variable {J : ConfiguredRecursiveEdgeSourceP0RowJetTail.RowJetScalarOutput
    ConfiguredRecursiveSourceP0FixedDistortion.choice.MA0
    ConfiguredRecursiveSourceP0FixedDistortion.choice.NA0}
  {O : GaugeOutput J} (R : RecostClosingOutput J O)

abbrev rowP1 (q : ℕ) : ℝ :=
  ConfiguredRecursiveEdgeSourceP0Growth.edgeP1
    (ConfiguredRecursiveEdgeSourceP0CappedRowProduction.D J.scalar)
    ConfiguredRecursiveSourceP0FixedDistortion.choice.MA0 (R.totalShift + q)

abbrev rowDefect (q : ℕ) : ℝ :=
  ConfiguredRecursiveEdgeSourceP0Growth.edgePhysicalDefect
    (ConfiguredRecursiveEdgeSourceP0CappedRowProduction.D J.scalar)
      (R.totalShift + q + 1)

/-- Scalar synchronization is stated separately from the analytic node. -/
structure ConfiguredNode (q : ℕ) (N : Node) : Prop where
  P0_eq : N.P0 = ConfiguredRecursiveEdgeSourceP0.edgeSourceP0
    (ConfiguredRecursiveEdgeSourceP0CappedRowProduction.D J.scalar)
      (R.totalShift + q)
  khat_eq : N.khat =
    ConfiguredCombinedPhysicalDiagonalLargeSeparation.analyticKhat
      (ConfiguredRecursiveEdgeSourceP0CappedRowProduction.D J.scalar)
  Qmax_eq : N.Qmax = ConfiguredRecursiveEdgeSourceP0.edgeSpeedCap
    (ConfiguredRecursiveEdgeSourceP0CappedRowProduction.D J.scalar)
      (R.totalShift + q)

noncomputable def nextState
    {k n : ℕ} {S : ℕ → Node}
    (G : Step S k)
    (H : State
      ((ConfiguredRecursiveEdgePhysicalBaseFinalTailState.finalGaugeOutput R).shiftOutput
        (n + 1 + k))
      (S (n + 1)).stage (rowP1 R (n + 1 + k)) k
      (rowDefect R (n + 1 + k)))
    (hcur : (G.analytic n).eps ≤
      ((ConfiguredRecursiveEdgePhysicalBaseFinalTailState.finalGaugeOutput R).shiftOutput
        (n + 1 + k)).major (k + 1))
    (hupper : (G.analytic n).slice.periodUpper ≤ rowP1 R (n + (k + 1))) :
    State
      ((ConfiguredRecursiveEdgePhysicalBaseFinalTailState.finalGaugeOutput R).shiftOutput
        (n + (k + 1)))
      (G.next n).stage (rowP1 R (n + (k + 1))) (k + 1)
      (rowDefect R (n + (k + 1))) := by
  let C := G.pre (n + 1)
  let I := G.analytic n
  let A := H.nextAncestry C (unscaled I)
    ConfiguredRecursiveEdgeFinitePresentedFinalAssembly.distortionTotal_le_eighth hcur
  let X : State
      ((ConfiguredRecursiveEdgePhysicalBaseFinalTailState.finalGaugeOutput R).shiftOutput
        (n + 1 + k))
      (G.next n).stage (rowP1 R (n + (k + 1))) (k + 1)
      (rowDefect R (n + 1 + k)) :=
    { sourceFacts :=
        { slice := I.slice
          periodUpper_le := hupper
          functional := by
            have F :=
              FiniteSmoothRearFamilyMarkingAwareChosenExactFunctionalFacts.ChosenPath.functionalIntegrable_of_exactSource
                C.geometric.output.chosen
            simpa [I.path_eta] using F
          eps := I.eps
          jets := I.sourceJets
          eps_le_major := hcur }
      intrinsic := nextIntrinsic H C I
      periodFloor := fun t =>
        ConfiguredRecursiveEdgeRearPeriodFloor.one_le_rearPeriod t
      ancestry := A
      terminalJ_eq := by
        dsimp [A]
        rw [State.nextAncestry]
        exact terminal_phi1_eq_scaled I
      terminalP_eq := by
        dsimp [A]
        rw [State.nextAncestry]
        exact terminal_period_eq_scaled I }
  convert X using 1 <;>
    simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

structure Layer (k : ℕ) (S : ℕ → Node) where
  configured : ∀ n, ConfiguredNode R (n + k) (S n)
  normalized : ∀ n, State
    ((ConfiguredRecursiveEdgePhysicalBaseFinalTailState.finalGaugeOutput R).shiftOutput
      (n + k))
    (S n).stage (rowP1 R (n + k)) k (rowDefect R (n + k))

namespace Layer

noncomputable def next
    {k : ℕ} {S : ℕ → Node}
    (L : Layer R k S) (G : Step S k)
    (hconfigured : ∀ n, ConfiguredNode R (n + (k + 1)) (G.next n))
    (hcur : ∀ n, (G.analytic n).eps ≤
      ((ConfiguredRecursiveEdgePhysicalBaseFinalTailState.finalGaugeOutput R).shiftOutput
        (n + 1 + k)).major (k + 1))
    (hupper : ∀ n,
      (G.analytic n).slice.periodUpper ≤ rowP1 R (n + (k + 1))) :
    Layer R (k + 1) G.next where
  configured := hconfigured
  normalized n := nextState R G (L.normalized (n + 1)) (hcur n) (hupper n)

end Layer

end ConfiguredRecursiveEdgeRecostMultiplierIntrinsicReachableLayer
