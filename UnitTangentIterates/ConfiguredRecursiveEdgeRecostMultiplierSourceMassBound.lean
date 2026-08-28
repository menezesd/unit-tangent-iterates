import UnitTangentIterates.ConfiguredRecursiveEdgeRecostMultiplierPreCarrier

/-! # Truthful mass bound of the newly multiplier-scaled source -/

noncomputable section

open Function Set MarkedSpace PathMetric

namespace ConfiguredRecursiveEdgeRecostMultiplierSourceMassBound

open ConfiguredRecursiveEdgeFiniteColumnGaugeMajorant
  ConfiguredRecursiveEdgeRecostMultiplierClosing
  ConfiguredRecursiveEdgeRecostMultiplierScalar
  ConfiguredRecursiveEdgeRecostMultiplierScaledDiagonal
  ConfiguredRecursiveEdgeRecostPeriodScaledDiagonal
  ConfiguredRecursiveEdgeSourceP0Growth
  FiniteSmoothRearFamilyMarkingAwareActualPullbackStages
  FiniteSmoothRearFamilyMarkingAwareAppliedSource
  FiniteSmoothRearFamilyMarkingAwareExactSuccessorDirectRecostSource
  FiniteSmoothRearFamilyMarkingAwareExactSuccessorScaledDirectRecostSource

variable {J : ConfiguredRecursiveEdgeSourceP0RowJetTail.RowJetScalarOutput
    ConfiguredRecursiveSourceP0FixedDistortion.choice.MA0
    ConfiguredRecursiveSourceP0FixedDistortion.choice.NA0}
  {O : GaugeOutput J}
  {p q a b : Data} {Gamma : NormalPath p q}
  {P0 khat Qmax : ℝ}
  {A : FiniteSmoothRearFamilyMarkingAwareSource.MarkingAwareSource Gamma P0
    ConfiguredCombinedPhysicalDiagonalLargeSeparation.sourceKh khat Qmax}
  {E : Applied Gamma A}

/-- The intermediate inequality used inside `recostScalar`: before the final
small-tail comparison, its scaled density already has exactly the configured
multiplier allowance. -/
theorem recostScalar_mass_le_allowance
    (R : RecostClosingOutput J O) (r : ℕ)
    (W : ChosenPath Gamma A E.Phi a b)
    (hC2 : C2NormalPathData W.Delta)
    (heta : Continuous (uncurry W.Delta.eta))
    (heta1 : Continuous (uncurry hC2.eta1))
    (heta2 : Continuous (uncurry hC2.eta2))
    (hcost : (carrier W hC2 heta heta1 heta2).cost ≤
      4 * configuredTarget
          ConfiguredRecursiveEdgeFinitePresentedFinalAssembly.distortionTotal
          ConfiguredRecursiveEdgeFinitePresentedFinalAssembly.physicalTransitionCeilings.C0
          ConfiguredRecursiveEdgeFinitePresentedFinalAssembly.physicalTransitionCeilings.C1
          ConfiguredRecursiveEdgeFinitePresentedFinalAssembly.physicalTransitionCeilings.C2 *
        (2 * recostPeriodScale R.data r *
          edgePhysicalDefect R.data (r + 1))) :
    (∫ t in (0 : ℝ)..W.Delta.T,
      (recostScalar R r W hC2 heta heta1 heta2 hcost).coeff *
        density
          (kap := ConfiguredCombinedPhysicalDiagonalLargeSeparation.sourceKh)
          W hC2 heta heta1 heta2 t) ≤
      multiplierRecostSourceAllowance R.data
        ConfiguredRecursiveEdgeFinitePresentedFinalAssembly.distortionTotal
        ConfiguredRecursiveEdgeFinitePresentedFinalAssembly.physicalTransitionCeilings.C0
        ConfiguredRecursiveEdgeFinitePresentedFinalAssembly.physicalTransitionCeilings.C1
        ConfiguredRecursiveEdgeFinitePresentedFinalAssembly.physicalTransitionCeilings.C2 r := by
  have hcoeff : 0 ≤ directRecostCompositionCoeff R.data r :=
    (by norm_num : (0 : ℝ) ≤ 2).trans
      (directRecostCompositionCoeff_two_le R.data r)
  have hsqrt : 0 ≤ Real.sqrt
      (1 - ConfiguredCombinedPhysicalDiagonalLargeSeparation.sourceKh ^ 2) :=
    Real.sqrt_nonneg _
  change (∫ t in (0 : ℝ)..W.Delta.T,
      directRecostCompositionCoeff R.data r *
        density
          (kap := ConfiguredCombinedPhysicalDiagonalLargeSeparation.sourceKh)
          W hC2 heta heta1 heta2 t) ≤ _
  calc
    _ = directRecostCompositionCoeff R.data r /
          Real.sqrt
            (1 - ConfiguredCombinedPhysicalDiagonalLargeSeparation.sourceKh ^ 2) *
        (carrier W hC2 heta heta1 heta2).cost := by
      rw [intervalIntegral.integral_const_mul]
      unfold density
      rw [intervalIntegral.integral_div]
      unfold NormalPath.cost
      rw [show W.Delta.T = (carrier W hC2 heta heta1 heta2).T by rfl]
      ring
    _ ≤ _ := by
      unfold multiplierRecostSourceAllowance
      exact mul_le_mul_of_nonneg_left hcost (div_nonneg hcoeff hsqrt)

end ConfiguredRecursiveEdgeRecostMultiplierSourceMassBound
