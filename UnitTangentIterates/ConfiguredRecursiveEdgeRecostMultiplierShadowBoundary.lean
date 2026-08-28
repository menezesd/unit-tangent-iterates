import UnitTangentIterates.ConfiguredRecursiveEdgeRecostMultiplierCountableTailSchedule
import UnitTangentIterates.ConfiguredRecursiveEdgeRecostMultiplierShadowUniqueness

/-!
# Paper-facing terminal shadow boundary

This theorem combines the two parts of the terminal argument which are
independent of the still-dependent recursive grid constructor:

* every completed row is represented by the paper's scheduled
  piecewise-smooth/absolutely-continuous concatenation, with genuine finite
  normal paths and the terminal `S`-tail inequalities;
* the configured paired-major Jacobi invariant gives uniqueness among exact
  inverse orbits once the concrete propagated row comparisons are supplied.

No scalar, summability, endpoint-schedule, radius-decay, or stable-constant
callback remains.
-/

noncomputable section

open Filter Topology MarkedTopology
open MarkedSpace PathMetric PathMetric.NormalPath

namespace ConfiguredRecursiveEdgeRecostMultiplierShadowBoundary

open AnchoredJacobiStableTransition
  ConfiguredRecursiveEdgeFiniteColumnGaugeMajorant
  ConfiguredRecursiveEdgeFinitePresentedFinalAssembly
  ConfiguredRecursiveEdgeRecostMultiplierClosing
  ConfiguredRecursiveEdgeRecostMultiplierCountableTailSchedule
  ConfiguredRecursiveEdgeRecostMultiplierShadowUniqueness
  ConfiguredRecursiveEdgeSourceP0RowJetTail
  ConfiguredRecursiveSourceP0FixedDistortion
  FiniteSmoothRearFamilyMarkingAwareNonaffinePhysicalW

variable {J : RowJetScalarOutput choice.MA0 choice.NA0}
  {O : GaugeOutput J}

/-- The strongest callback-free terminal conclusion presently independent of
the concrete recursive grid.  The first conjunct has the exact no-discard
quantifier `∀ n`; the second has the exact uniqueness quantifier over every
competitor `Y` carrying the paper's propagated comparison paths. -/
theorem configured_shadow_boundary
    (R : RecostClosingOutput J O)
    (P : ℕ → ℕ → MarkedSpace.Data)
    (X : ℕ → MarkedSpace.Data)
    (step : ∀ n k, NormalPath (P n k) (P n (k + 1)))
    (hcost : ∀ n k, cost (step n k) ≤ R.error n k)
    (hlim : ∀ n, Tendsto (P n) atTop (nhds (X n))) :
    (∀ n, ∃ C q : ℝ, Nonempty
      (GeometricScheduledACTail.Certificate (step n) (X n) C q)) ∧
    ∀ (Y : ℕ → MarkedSpace.Data) (Cmetric : ℝ), 0 ≤ Cmetric →
      ∀ V : ℕ → ℕ → ℕ → Components,
      (∀ n N k, (V n N k).Nonnegative) →
      (∀ n N,
        (V n N 0).w ≤ R.radius N ∧
        (V n N 0).s0 ≤ R.radius N ∧
        (V n N 0).s1 ≤ R.radius N ∧
        (V n N 0).s2 ≤ R.radius N) →
      (∀ n N k, Transition (V n N k) (V n N (k + 1))
        (NearIdentityDistortionBudget.invLower (pairedMajor O.major) k)
        (NearIdentityDistortionBudget.upper (pairedMajor O.major) k)
        (pairedMajor O.major k)
        physicalTransitionCeilings.C0 physicalTransitionCeilings.C1
        physicalTransitionCeilings.C2) →
      (∀ n k, dist (X n) (Y n) ≤ Cmetric *
        ((V n (n + k) k).w + (V n (n + k) k).s0 +
          (V n (n + k) k).s1 + (V n (n + k) k).s2)) →
      X = Y := by
  constructor
  · intro n
    exact exists_scheduledACTail R (step n) n (hcost n) (X n) (hlim n)
  · intro Y Cmetric hCmetric V hV hinit hstep hdist
    exact unique_of_configured_component_comparisons R hCmetric V hV hinit
      hstep hdist

end ConfiguredRecursiveEdgeRecostMultiplierShadowBoundary
