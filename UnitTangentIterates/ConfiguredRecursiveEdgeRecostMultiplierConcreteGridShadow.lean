import UnitTangentIterates.ConfiguredRecursiveEdgeRecostMultiplierShadowBoundary

/-!
# Concrete-grid adapter for the configured shadow boundary

The scalar closing output already supplies the summable schedule, shrinking
radius, and stable Jacobi constants.  A concrete recursive grid therefore only
has to provide its row paths and limits, together with the propagated physical
comparison against the exact orbit which it shadows.

This record is deliberately independent of the construction of the grid.  In
particular, it can be instantiated by the reachable sigma-layer recursion and
used alongside the separate smooth physical-base input.
-/

noncomputable section

open Filter Topology MarkedTopology
open MarkedSpace PathMetric PathMetric.NormalPath

namespace ConfiguredRecursiveEdgeRecostMultiplierConcreteGridShadow

open AnchoredJacobiStableTransition
  ConfiguredRecursiveEdgeFiniteColumnGaugeMajorant
  ConfiguredRecursiveEdgeFinitePresentedFinalAssembly
  ConfiguredRecursiveEdgeRecostMultiplierClosing
  ConfiguredRecursiveEdgeRecostMultiplierShadowBoundary
  ConfiguredRecursiveEdgeSourceP0RowJetTail
  ConfiguredRecursiveSourceP0FixedDistortion
  FiniteSmoothRearFamilyMarkingAwareNonaffinePhysicalW

variable {J : RowJetScalarOutput choice.MA0 choice.NA0}
  {O : GaugeOutput J}

/-- The exact non-scalar data which a concrete reachable grid must supply to
the configured shadow boundary.  All scalar, tail, and stable-transition
constants are inherited from `R`.

`P` is the displayed triangular grid, `X` its completed rows, and `Y` the exact
inverse orbit to be identified with that completion. -/
structure ConcreteGridInput (R : RecostClosingOutput J O) where
  P : ℕ → ℕ → MarkedSpace.Data
  X : ℕ → MarkedSpace.Data
  step : ∀ n k, NormalPath (P n k) (P n (k + 1))
  step_cost : ∀ n k, cost (step n k) ≤ R.error n k
  row_tendsto : ∀ n, Tendsto (P n) atTop (nhds (X n))
  Y : ℕ → MarkedSpace.Data
  metricConst : ℝ
  metricConst_nonneg : 0 ≤ metricConst
  comparison : ℕ → ℕ → ℕ → Components
  comparison_nonnegative : ∀ n N k, (comparison n N k).Nonnegative
  comparison_initial : ∀ n N,
    (comparison n N 0).w ≤ R.radius N ∧
    (comparison n N 0).s0 ≤ R.radius N ∧
    (comparison n N 0).s1 ≤ R.radius N ∧
    (comparison n N 0).s2 ≤ R.radius N
  comparison_transition : ∀ n N k,
    Transition (comparison n N k) (comparison n N (k + 1))
      (NearIdentityDistortionBudget.invLower (pairedMajor O.major) k)
      (NearIdentityDistortionBudget.upper (pairedMajor O.major) k)
      (pairedMajor O.major k)
      physicalTransitionCeilings.C0 physicalTransitionCeilings.C1
      physicalTransitionCeilings.C2
  comparison_distance : ∀ n k, dist (X n) (Y n) ≤ metricConst *
    ((comparison n (n + k) k).w + (comparison n (n + k) k).s0 +
      (comparison n (n + k) k).s1 + (comparison n (n + k) k).s2)

/-- Paper-facing shadow conclusion for one concrete configured grid.

The first conjunct retains the no-discard quantifier over every row and gives
the scheduled finite-length AC tail ending at its completion.  The second
identifies that completion with the supplied exact inverse orbit. -/
theorem paperShadow (R : RecostClosingOutput J O) (I : ConcreteGridInput R) :
    (∀ n, ∃ C q : ℝ, Nonempty
      (GeometricScheduledACTail.Certificate (I.step n) (I.X n) C q)) ∧
    I.X = I.Y := by
  obtain ⟨htail, hunique⟩ := configured_shadow_boundary R I.P I.X I.step
    I.step_cost I.row_tendsto
  refine ⟨htail, ?_⟩
  exact hunique I.Y I.metricConst I.metricConst_nonneg I.comparison
    I.comparison_nonnegative I.comparison_initial I.comparison_transition
    I.comparison_distance

end ConfiguredRecursiveEdgeRecostMultiplierConcreteGridShadow
