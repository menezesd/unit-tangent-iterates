import UnitTangentIterates.ConfiguredRecursiveEdgeRecostMultiplierPreCarrier
import UnitTangentIterates.ConfiguredRecursiveEdgePhysicalFiniteColumnSourceMass

/-! # Truthful source-mass bounds for multiplier recost carriers -/

noncomputable section

open Function Set MeasureTheory MarkedSpace PathMetric

namespace ConfiguredRecursiveEdgeRecostMultiplierSourceMass

open ConfiguredRecursiveEdgeFiniteColumnGaugeMajorant
  ConfiguredRecursiveEdgeRecostMultiplierClosing
  ConfiguredRecursiveEdgeRecostMultiplierScaledDiagonal
  ConfiguredRecursiveEdgeRecostMultiplierScalar
  ConfiguredRecursiveEdgeRecostPeriodScaledDiagonal
  ConfiguredRecursiveEdgeSourceP0Growth
  FiniteSmoothRearFamilyMarkingAwareAppliedSource
  FiniteSmoothRearFamilyMarkingAwareExactSuccessorDirectRecostSource
  FiniteSmoothRearFamilyMarkingAwareExactSuccessorScaledDirectRecostSource
  FiniteSmoothRearFamilyMarkingAwareSource
  FiniteSmoothRearFamilyMarkingAwareChosenVariableJetLinear
  FiniteSmoothRearFamilyMarkingAwareTimeRescaleCostObstruction

variable {J : ConfiguredRecursiveEdgeSourceP0RowJetTail.RowJetScalarOutput
    ConfiguredRecursiveSourceP0FixedDistortion.choice.MA0
    ConfiguredRecursiveSourceP0FixedDistortion.choice.NA0}
  {O : GaugeOutput J}
  {p q a b : Data} {Gamma : NormalPath p q}
  {P0 khat Qmax : ℝ}
  {A : MarkingAwareSource Gamma P0
    ConfiguredCombinedPhysicalDiagonalLargeSeparation.sourceKh khat Qmax}
  {E : Applied Gamma A}

/-- The sharp inequality used internally by the configured recost scalar,
before it is weakened to the unit-mass field of `RecostScalar`. -/
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

variable {P0u khatu Qmaxu : ℕ → ℝ} {j : ℕ}
  {S : FiniteSmoothRearFamilyMarkingAwareActualPullbackStages.Stage P0u
    (fun _ => ConfiguredCombinedPhysicalDiagonalLargeSeparation.sourceKh)
    khatu Qmaxu j}
  {C : ConfiguredRecursiveEdgeRecostedPreCarrier.Core S}
  {p0 khat0 : ℝ}

/-- A scaled pre-carrier whose scalar is the configured multiplier scalar has
the sharp allowance bound.  This is the positive-depth predecessor mass
estimate consumed by the nonaffine allowance constructor. -/
theorem scaledInput_sourceMass_le_allowance
    (R : RecostClosingOutput J O) (r : ℕ)
    (I : ConfiguredRecursiveEdgeRecostedScaledPreCarrier.Input C p0
      ConfiguredCombinedPhysicalDiagonalLargeSeparation.sourceKh khat0
      (ConfiguredRecursiveEdgeSourceP0.edgeSpeedCap R.data r))
    (hcost : (carrier C.geometric.output.chosen
        C.geometric.output.chosen.c2 C.eta_continuous C.eta1_continuous
        C.eta2_continuous).cost ≤
      4 * configuredTarget
          ConfiguredRecursiveEdgeFinitePresentedFinalAssembly.distortionTotal
          ConfiguredRecursiveEdgeFinitePresentedFinalAssembly.physicalTransitionCeilings.C0
          ConfiguredRecursiveEdgeFinitePresentedFinalAssembly.physicalTransitionCeilings.C1
          ConfiguredRecursiveEdgeFinitePresentedFinalAssembly.physicalTransitionCeilings.C2 *
        (2 * recostPeriodScale R.data r *
          edgePhysicalDefect R.data (r + 1)))
    (hscalar : I.recostScalar = recostScalar R r C.geometric.output.chosen
      C.geometric.output.chosen.c2 C.eta_continuous C.eta1_continuous
      C.eta2_continuous hcost) :
    sourceMass I.source ≤
      multiplierRecostSourceAllowance R.data
        ConfiguredRecursiveEdgeFinitePresentedFinalAssembly.distortionTotal
        ConfiguredRecursiveEdgeFinitePresentedFinalAssembly.physicalTransitionCeilings.C0
        ConfiguredRecursiveEdgeFinitePresentedFinalAssembly.physicalTransitionCeilings.C1
        ConfiguredRecursiveEdgeFinitePresentedFinalAssembly.physicalTransitionCeilings.C2 r := by
  have H := recostScalar_mass_le_allowance R r C.geometric.output.chosen
    C.geometric.output.chosen.c2 C.eta_continuous C.eta1_continuous
    C.eta2_continuous hcost
  rw [sourceMass]
  change (∫ t in (0 : ℝ)..C.path.T,
      I.recostScalar.coeff * density
        (kap := ConfiguredCombinedPhysicalDiagonalLargeSeparation.sourceKh)
        C.geometric.output.chosen C.geometric.output.chosen.c2
        C.eta_continuous C.eta1_continuous C.eta2_continuous t) ≤ _
  rw [hscalar]
  simpa [ConfiguredRecursiveEdgeRecostedPreCarrier.Core.path,
    CanonicalNormalPathRecost.recost,
    FiniteSmoothRearFamilyMarkingAwareExactSuccessorDirectRecostSource.carrier] using H

end ConfiguredRecursiveEdgeRecostMultiplierSourceMass
