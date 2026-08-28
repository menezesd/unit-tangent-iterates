import UnitTangentIterates.ConfiguredRecursiveEdgeRecostMultiplierClosing
import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareExactSuccessorScaledDirectRecostSource

/-! # Final-closing scalar for the multiplier-aware recost source -/

noncomputable section

open Function Set MarkedSpace PathMetric

namespace ConfiguredRecursiveEdgeRecostMultiplierScalar

open ConfiguredRecursiveEdgeFiniteColumnGaugeMajorant
  ConfiguredRecursiveEdgeRecostMultiplierClosing
  ConfiguredRecursiveEdgeRecostMultiplierScaledDiagonal
  ConfiguredRecursiveEdgeRecostPeriodScaledDiagonal
  ConfiguredRecursiveEdgeSourceP0Growth
  ConfiguredRecursiveEdgeSourceP0RowJetTail
  ConstructedConfiguredInductiveTubeBudget.WeightedData
  FiniteSmoothRearFamilyMarkingAwareAppliedSource
  FiniteSmoothRearFamilyMarkingAwareCorrelatedRecursion
  FiniteSmoothRearFamilyMarkingAwareExactSuccessorDirectRecostSource
  FiniteSmoothRearFamilyMarkingAwareExactSuccessorScaledDirectRecostSource
  FiniteSmoothRearFamilyMarkingAwareSource

variable {J : RowJetScalarOutput
    ConfiguredRecursiveSourceP0FixedDistortion.choice.MA0
    ConfiguredRecursiveSourceP0FixedDistortion.choice.NA0}
  {O : GaugeOutput J}

private theorem multiplierRecostSourceAllowance_shift
    (D : ConstructedConfiguredSequenceWeighted.Data) (N q : ℕ) :
    multiplierRecostSourceAllowance (shift D N)
        ConfiguredRecursiveEdgeFinitePresentedFinalAssembly.distortionTotal
        ConfiguredRecursiveEdgeFinitePresentedFinalAssembly.physicalTransitionCeilings.C0
        ConfiguredRecursiveEdgeFinitePresentedFinalAssembly.physicalTransitionCeilings.C1
        ConfiguredRecursiveEdgeFinitePresentedFinalAssembly.physicalTransitionCeilings.C2 q =
      multiplierRecostSourceAllowance D
        ConfiguredRecursiveEdgeFinitePresentedFinalAssembly.distortionTotal
        ConfiguredRecursiveEdgeFinitePresentedFinalAssembly.physicalTransitionCeilings.C0
        ConfiguredRecursiveEdgeFinitePresentedFinalAssembly.physicalTransitionCeilings.C1
        ConfiguredRecursiveEdgeFinitePresentedFinalAssembly.physicalTransitionCeilings.C2 (N + q) := by
  have hc : directRecostCompositionCoeff (shift D N) q =
      directRecostCompositionCoeff D (N + q) := by
    unfold directRecostCompositionCoeff
    rw [ConfiguredRecursiveEdgeSourceP0Growth.edgeCompositionCoeff_shift]
  have hL : recostPeriodScale (shift D N) q =
      recostPeriodScale D (N + q) := by
    simp [recostPeriodScale, ConfiguredRecursiveEdgeSourceP0.edgeSpeedCap,
      ConfiguredCombinedPhysicalDiagonalLargeSeparation.speedCap,
      ConstructedConfiguredInductiveTubeBudget.WeightedData.shift,
      Nat.add_assoc]
  have he : edgePhysicalDefect (shift D N) (q + 1) =
      edgePhysicalDefect D (N + q + 1) := by
    unfold edgePhysicalDefect
    unfold ConfiguredPolynomialDiagonalStableRowDefectProvider.physicalDefect
    rw [ConstructedRowDefectLargeSeparation.rowDefect_shift]
    simp [
      ConfiguredPolynomialDiagonalStableRowDefectProvider.physicalDefect,
      ConfiguredPolynomialDiagonalStableRowDefectProvider.physicalCoeff,
      ConstructedConfiguredInductiveTubeBudget.WeightedData.shift,
      Nat.add_assoc]
  unfold multiplierRecostSourceAllowance
  rw [hc, hL, he]

theorem mass_small_final (R : RecostClosingOutput J O) (q : ℕ) :
    multiplierRecostSourceAllowance R.data
      ConfiguredRecursiveEdgeFinitePresentedFinalAssembly.distortionTotal
      ConfiguredRecursiveEdgeFinitePresentedFinalAssembly.physicalTransitionCeilings.C0
      ConfiguredRecursiveEdgeFinitePresentedFinalAssembly.physicalTransitionCeilings.C1
      ConfiguredRecursiveEdgeFinitePresentedFinalAssembly.physicalTransitionCeilings.C2 q ≤ 1 := by
  let N := R.preShift + R.large.N
  have H : multiplierRecostSourceAllowance (shift O.data N)
      ConfiguredRecursiveEdgeFinitePresentedFinalAssembly.distortionTotal
      ConfiguredRecursiveEdgeFinitePresentedFinalAssembly.physicalTransitionCeilings.C0
      ConfiguredRecursiveEdgeFinitePresentedFinalAssembly.physicalTransitionCeilings.C1
      ConfiguredRecursiveEdgeFinitePresentedFinalAssembly.physicalTransitionCeilings.C2 q ≤ 1 := by
    rw [multiplierRecostSourceAllowance_shift]
    simpa [N, Nat.add_assoc] using R.mass_small q
  change multiplierRecostSourceAllowance
      (shift (ConfiguredRecursiveEdgeRecostScaledPaperCapstone.data J) R.totalShift)
      ConfiguredRecursiveEdgeFinitePresentedFinalAssembly.distortionTotal
      ConfiguredRecursiveEdgeFinitePresentedFinalAssembly.physicalTransitionCeilings.C0
      ConfiguredRecursiveEdgeFinitePresentedFinalAssembly.physicalTransitionCeilings.C1
      ConfiguredRecursiveEdgeFinitePresentedFinalAssembly.physicalTransitionCeilings.C2 q ≤ 1
  rw [multiplierRecostSourceAllowance_shift]
  change multiplierRecostSourceAllowance
      (shift (ConfiguredRecursiveEdgeRecostScaledPaperCapstone.data J) O.N)
      ConfiguredRecursiveEdgeFinitePresentedFinalAssembly.distortionTotal
      ConfiguredRecursiveEdgeFinitePresentedFinalAssembly.physicalTransitionCeilings.C0
      ConfiguredRecursiveEdgeFinitePresentedFinalAssembly.physicalTransitionCeilings.C1
      ConfiguredRecursiveEdgeFinitePresentedFinalAssembly.physicalTransitionCeilings.C2 (N + q) ≤ 1 at H
  rw [multiplierRecostSourceAllowance_shift] at H
  simpa [N, RecostClosingOutput.totalShift, Nat.add_assoc] using H

variable {p q a b : Data} {Gamma : NormalPath p q}
  {P0 khat Qmax : ℝ}
  {A : MarkingAwareSource Gamma P0
    ConfiguredCombinedPhysicalDiagonalLargeSeparation.sourceKh khat Qmax}
  {E : Applied Gamma A}

/-- The final multiplier closing and the physical-history recost estimate
produce the complete scalar package for the actual recursive source. -/
def recostScalar
    {J : RowJetScalarOutput
      ConfiguredRecursiveSourceP0FixedDistortion.choice.MA0
      ConfiguredRecursiveSourceP0FixedDistortion.choice.NA0}
    {O : GaugeOutput J} (R : RecostClosingOutput J O) (r : ℕ)
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
    RecostScalar W
      (kap := ConfiguredCombinedPhysicalDiagonalLargeSeparation.sourceKh)
      (QmaxNext := ConfiguredRecursiveEdgeSourceP0.edgeSpeedCap R.data r)
      hC2 heta heta1 heta2 where
  coeff := directRecostCompositionCoeff R.data r
  coeff_ge_two := directRecostCompositionCoeff_two_le R.data r
  scaled_mass_le_one := by
    have hcoeff : 0 ≤ directRecostCompositionCoeff R.data r :=
      (by norm_num : (0 : ℝ) ≤ 2).trans
        (directRecostCompositionCoeff_two_le R.data r)
    have hsqrt : 0 ≤ Real.sqrt
        (1 - ConfiguredCombinedPhysicalDiagonalLargeSeparation.sourceKh ^ 2) :=
      Real.sqrt_nonneg _
    calc
      (∫ t in (0 : ℝ)..W.Delta.T,
          directRecostCompositionCoeff R.data r *
            density
              (kap := ConfiguredCombinedPhysicalDiagonalLargeSeparation.sourceKh)
              W hC2 heta heta1 heta2 t) =
          directRecostCompositionCoeff R.data r /
              Real.sqrt
                (1 - ConfiguredCombinedPhysicalDiagonalLargeSeparation.sourceKh ^ 2) *
            (carrier W hC2 heta heta1 heta2).cost := by
        rw [intervalIntegral.integral_const_mul]
        unfold density
        rw [intervalIntegral.integral_div]
        unfold NormalPath.cost
        rw [show W.Delta.T = (carrier W hC2 heta heta1 heta2).T by rfl]
        ring
      _ ≤ multiplierRecostSourceAllowance R.data
          ConfiguredRecursiveEdgeFinitePresentedFinalAssembly.distortionTotal
          ConfiguredRecursiveEdgeFinitePresentedFinalAssembly.physicalTransitionCeilings.C0
          ConfiguredRecursiveEdgeFinitePresentedFinalAssembly.physicalTransitionCeilings.C1
          ConfiguredRecursiveEdgeFinitePresentedFinalAssembly.physicalTransitionCeilings.C2 r := by
        unfold multiplierRecostSourceAllowance
        exact mul_le_mul_of_nonneg_left hcost (div_nonneg hcoeff hsqrt)
      _ ≤ 1 := mass_small_final R r
  coeff_first := by
    have hk :=
      ConfiguredCombinedPhysicalDiagonalLargeSeparation.rearKappa1_sourceKh_le_analyticKhat
        R.data
    have hp : GaugeFlowDerivCost.costP1
        (ConfiguredRecursiveEdgeSourceP0.edgeSpeedCap R.data r)
        (GaugeMarkedDataOfRearFamily.rearKappa1
          ConfiguredCombinedPhysicalDiagonalLargeSeparation.sourceKh) 1 ≤
      GaugeFlowDerivCost.costP1
        (ConfiguredRecursiveEdgeSourceP0.edgeSpeedCap R.data r)
        (ConfiguredCombinedPhysicalDiagonalLargeSeparation.analyticKhat R.data) 1 := by
      unfold GaugeFlowDerivCost.costP1
      apply mul_le_mul_of_nonneg_left
      · exact Real.exp_le_exp.mpr (by nlinarith [hk])
      · exact ConfiguredRecursiveEdgeSourceP0.edgeSpeedCap_nonnegative R.data r
    exact (mul_le_mul_of_nonneg_left hp (by norm_num)).trans
      (by simpa [ConfiguredRecursiveEdgeSourceP0Growth.edgeFlowP1AtOne] using
        directRecostCompositionCoeff_first R.data r)
  coeff_second := by
    let ell := ConfiguredRecursiveEdgeSourceP0.edgeSpeedCap R.data r
    let k1 := GaugeMarkedDataOfRearFamily.rearKappa1
      ConfiguredCombinedPhysicalDiagonalLargeSeparation.sourceKh
    let ka := ConfiguredCombinedPhysicalDiagonalLargeSeparation.analyticKhat R.data
    let k2 := GaugeMarkedDataOfRearFamily.rearKappa2
      ConfiguredCombinedPhysicalDiagonalLargeSeparation.sourceKh
    let p := GaugeFlowDerivCost.costP1 ell k1 1
    let pa := GaugeFlowDerivCost.costP1 ell ka 1
    let g := GaugeFlowDerivCost.costG1 ell k1 k2 1
    let ga := GaugeFlowDerivCost.costG1 ell ka k2 1
    have hp : p ≤ pa := by
      unfold p pa GaugeFlowDerivCost.costP1
      apply mul_le_mul_of_nonneg_left
      · exact Real.exp_le_exp.mpr (by
          have hk :=
            ConfiguredCombinedPhysicalDiagonalLargeSeparation.rearKappa1_sourceKh_le_analyticKhat
              R.data
          dsimp [k1, ka]
          nlinarith [hk])
      · exact ConfiguredRecursiveEdgeSourceP0.edgeSpeedCap_nonnegative R.data r
    have hg : g ≤ ga := by
      unfold g ga GaugeFlowDerivCost.costG1
      have hlast : 0 ≤ k2 * 1 := mul_nonneg
        (GaugeMarkedDataOfRearFamily.rearKappa2_nonneg
          ConfiguredCombinedPhysicalDiagonalLargeSeparation.sourceKh_nonnegative
          ConfiguredCombinedPhysicalDiagonalLargeSeparation.sourceKh_lt_one)
        zero_le_one
      have hp0' : 0 ≤ GaugeFlowDerivCost.costP1 ell k1 1 := by
        unfold GaugeFlowDerivCost.costP1
        exact mul_nonneg
          (ConfiguredRecursiveEdgeSourceP0.edgeSpeedCap_nonnegative R.data r)
          (Real.exp_pos _).le
      have hpa0' : 0 ≤ GaugeFlowDerivCost.costP1 ell ka 1 := hp0'.trans hp
      exact mul_le_mul_of_nonneg_right
        ((sq_le_sq₀ hp0' hpa0').2 hp) hlast
    have hp0 : 0 ≤ p := by
      unfold p GaugeFlowDerivCost.costP1
      exact mul_nonneg
        (ConfiguredRecursiveEdgeSourceP0.edgeSpeedCap_nonnegative R.data r)
        (Real.exp_pos _).le
    have hpa0 : 0 ≤ pa := hp0.trans hp
    have hpsq : p ^ 2 ≤ pa ^ 2 := (sq_le_sq₀ hp0 hpa0).2 hp
    have H := directRecostCompositionCoeff_second R.data r
    have hs :
        FiniteSmoothRearFamilyMarkingAwareExactSuccessorAutomaticBounds.sourceConst =
          FiniteSmoothRearFamilyMarkingAwareSmoothSource.intrinsicSourceConst
            ConfiguredCombinedPhysicalDiagonalLargeSeparation.sourceKh
            (FiniteSmoothRearFamilyMarkingAwareSmoothSource.intrinsicDerivativeConst
              ConfiguredCombinedPhysicalDiagonalLargeSeparation.sourceKh) := rfl
    have hs0 : 0 ≤
        FiniteSmoothRearFamilyMarkingAwareSmoothSource.intrinsicSourceConst
          ConfiguredCombinedPhysicalDiagonalLargeSeparation.sourceKh
          (FiniteSmoothRearFamilyMarkingAwareSmoothSource.intrinsicDerivativeConst
            ConfiguredCombinedPhysicalDiagonalLargeSeparation.sourceKh) :=
      ConfiguredRecursiveSourceP0Growth.intrinsicSourceConst_nonnegative
    rw [hs]
    calc
      (2 * FiniteSmoothRearFamilyMarkingAwareSmoothSource.intrinsicSourceConst
              ConfiguredCombinedPhysicalDiagonalLargeSeparation.sourceKh
              (FiniteSmoothRearFamilyMarkingAwareSmoothSource.intrinsicDerivativeConst
                ConfiguredCombinedPhysicalDiagonalLargeSeparation.sourceKh) + 2) *
            p ^ 2 + 2 * g ≤
          (2 * FiniteSmoothRearFamilyMarkingAwareSmoothSource.intrinsicSourceConst
              ConfiguredCombinedPhysicalDiagonalLargeSeparation.sourceKh
              (FiniteSmoothRearFamilyMarkingAwareSmoothSource.intrinsicDerivativeConst
                ConfiguredCombinedPhysicalDiagonalLargeSeparation.sourceKh) + 2) *
            pa ^ 2 + 2 * ga := add_le_add
              (mul_le_mul_of_nonneg_left hpsq (by nlinarith [hs0]))
              (mul_le_mul_of_nonneg_left hg (by norm_num))
      _ = (2 * FiniteSmoothRearFamilyMarkingAwareSmoothSource.intrinsicSourceConst
              ConfiguredCombinedPhysicalDiagonalLargeSeparation.sourceKh
              (FiniteSmoothRearFamilyMarkingAwareSmoothSource.intrinsicDerivativeConst
                ConfiguredCombinedPhysicalDiagonalLargeSeparation.sourceKh) + 2) *
            edgeFlowP1AtOne R.data r ^ 2 +
          2 * edgeFlowG1AtOne R.data r := by
            rfl
      _ ≤ directRecostCompositionCoeff R.data r := H

end ConfiguredRecursiveEdgeRecostMultiplierScalar
