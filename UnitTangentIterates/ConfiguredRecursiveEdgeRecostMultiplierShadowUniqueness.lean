import UnitTangentIterates.ConfiguredRecursiveEdgeRecostMultiplierClosing
import UnitTangentIterates.RegularizingBackwardShadowingPhysicalUniqueness

/-!
# Configured physical uniqueness for the multiplier recost closing radius

This specializes the paper's max-radius uniqueness argument to the final
configured closing output.  Summability, radius nonnegativity, radius decay,
the paired-major distortion budget, and the stable constant are all selected
internally.  Only the concrete propagated comparison components and their
geometric distance estimate remain as row data.
-/

noncomputable section

open Filter Topology MarkedTopology

namespace ConfiguredRecursiveEdgeRecostMultiplierShadowUniqueness

open AnchoredJacobiStableTransition
  ConfiguredRecursiveEdgeFiniteColumnGaugeMajorant
  ConfiguredRecursiveEdgeFinitePresentedFinalAssembly
  ConfiguredRecursiveEdgeRecostMultiplierClosing
  ConfiguredRecursiveEdgeSourceP0RowJetTail
  ConfiguredRecursiveSourceP0FixedDistortion
  FiniteSmoothRearFamilyMarkingAwareNonaffinePhysicalW
  RegularizingBackwardShadowingPhysicalUniqueness

variable {J : ConfiguredRecursiveEdgeSourceP0RowJetTail.RowJetScalarOutput
    choice.MA0 choice.NA0}
  {O : GaugeOutput J}

/-- The final configured row radius tends to zero. -/
theorem radius_tendsto_zero (R : RecostClosingOutput J O) :
    Tendsto R.radius atTop (nhds 0) := by
  let e : ℕ → ℝ := fun k ↦
    ConfiguredRecursiveEdgeFullRecostMetricDiagonal.fullRecostMetricDiagonal
      O.data choice.MA0 choice.NA0 distortionTotal
      physicalTransitionCeilings.C0 physicalTransitionCeilings.C1
      physicalTransitionCeilings.C2 J.scalar.Mend
      (R.preShift + R.large.N + k)
  have heq : R.radius = ShadowingTails.tail e := by
    funext n
    simp [RecostClosingOutput.radius,
      ExponentialDiagonalLargeSeparation.rowRadius,
      ExponentialDiagonalLargeSeparation.rowError,
      ExponentialDiagonalLargeSeparation.shiftSequence,
      ShadowingTails.tail, e, Nat.add_assoc]
  rw [heq]
  exact ShadowingTails.tail_tendsto_zero

/-- Callback-free scalar specialization of physical uniqueness.  The three
transition sequences and their depth-uniform stable constant are fixed by the
configured paired major; the final radius is the closing radius selected by
`R`. -/
theorem unique_of_configured_component_comparisons
    (R : RecostClosingOutput J O)
    {M : Type*} [MetricSpace M]
    {X Y : ℕ → M} {Cmetric : ℝ}
    (hCmetric : 0 ≤ Cmetric)
    (V : ℕ → ℕ → ℕ → Components)
    (hV : ∀ n N k, (V n N k).Nonnegative)
    (hinit : ∀ n N,
      (V n N 0).w ≤ R.radius N ∧
      (V n N 0).s0 ≤ R.radius N ∧
      (V n N 0).s1 ≤ R.radius N ∧
      (V n N 0).s2 ≤ R.radius N)
    (hstep : ∀ n N k, Transition (V n N k) (V n N (k + 1))
      (NearIdentityDistortionBudget.invLower (pairedMajor O.major) k)
      (NearIdentityDistortionBudget.upper (pairedMajor O.major) k)
      (pairedMajor O.major k)
      physicalTransitionCeilings.C0 physicalTransitionCeilings.C1
      physicalTransitionCeilings.C2)
    (distance_of_components : ∀ n k,
      dist (X n) (Y n) ≤ Cmetric *
        ((V n (n + k) k).w + (V n (n + k) k).s0 +
          (V n (n + k) k).s1 + (V n (n + k) k).s2)) :
    X = Y := by
  let B := pairedNearIdentityBudget O.major_nonnegative' O.major_summable'
    O.major_tsum_le' distortionTotal_le_eighth
  exact unique_of_anchored_component_comparisons B
    physicalTransitionCeilings.C0_nonnegative
    physicalTransitionCeilings.C1_nonnegative
    physicalTransitionCeilings.C2_nonnegative hCmetric
    R.radius_nonnegative (radius_tendsto_zero R) V hV hinit hstep
    distance_of_components

end ConfiguredRecursiveEdgeRecostMultiplierShadowUniqueness
