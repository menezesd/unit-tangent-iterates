import UnitTangentIterates.ConfiguredRecursiveEdgeMixedConversionEnvelope
import UnitTangentIterates.ConfiguredRecursiveEdgeRecostMultiplierScaledDiagonal

/-! # Full displayed-metric recost diagonal -/

noncomputable section

open Filter Real

namespace ConfiguredRecursiveEdgeFullRecostMetricDiagonal

open ConfiguredApproximateDefectPathRowwise
  ConfiguredApproximateDefectPathRowwiseCost
  ConfiguredCombinedPhysicalDiagonalLargeSeparation
  ConfiguredRecursiveEdgeRecostMultiplierScaledDiagonal
  ConfiguredRecursiveEdgeSourceP0Growth
  ConfiguredRecursiveEdgeWeightedEffectiveError
  ConfiguredRowDefectProvider
  ConstructedRowCPolynomialGrowth

/-- Complete configured charge for the canonical depth-zero displayed edge. -/
def baseDisplayedMetricDiagonal
    (D : ConstructedConfiguredSequenceWeighted.Data)
    (MA NA M : ℝ) (q : ℕ) : ℝ :=
  weightedSequence
    (edgeCombinedConversion D MA NA (analyticKhat D) sourceKh M)
    (edgeCompositionPhysicalDefect D) q

theorem baseDisplayedMetricDiagonal_nonnegative
    (D : ConstructedConfiguredSequenceWeighted.Data)
    {MA NA M : ℝ} : ∀ q, 0 ≤ baseDisplayedMetricDiagonal D MA NA M q := by
  intro q
  exact mul_nonneg
    (edgeCombinedConversion_nonnegative D sourceKh_nonnegative
      sourceKh_lt_one q)
    (edgeCompositionPhysicalDefect_nonnegative D (q + 1))

/-- Final displayed metric diagonal.  Its first summand remains the recursive
source allowance; the second is used only for the base displayed edge. -/
def fullRecostMetricDiagonal
    (D : ConstructedConfiguredSequenceWeighted.Data)
    (MA NA E0 C0 C1 C2 M : ℝ) (q : ℕ) : ℝ :=
  multiplierRecostDirectDiagonal D MA NA E0 C0 C1 C2 M q +
    baseDisplayedMetricDiagonal D MA NA M q

theorem fullRecostMetricDiagonal_nonnegative
    (D : ConstructedConfiguredSequenceWeighted.Data)
    {MA NA E0 C0 C1 C2 M : ℝ} :
    ∀ q, 0 ≤ fullRecostMetricDiagonal D MA NA E0 C0 C1 C2 M q := by
  intro q
  exact add_nonneg (multiplierRecostDirectDiagonal_nonnegative D q)
    (baseDisplayedMetricDiagonal_nonnegative D q)

theorem multiplierRecostSourceAllowance_le_fullRecostMetricDiagonal
    (D : ConstructedConfiguredSequenceWeighted.Data)
    (MA NA E0 C0 C1 C2 M : ℝ) (q : ℕ) :
    multiplierRecostSourceAllowance D E0 C0 C1 C2 q ≤
      fullRecostMetricDiagonal D MA NA E0 C0 C1 C2 M q := by
  exact (multiplierRecostSourceAllowance_le_diagonal
    D MA NA E0 C0 C1 C2 M q).trans
      (le_add_of_nonneg_right (baseDisplayedMetricDiagonal_nonnegative D q))

theorem edgePhysicalDefect_le_edgeCompositionPhysicalDefect
    (D : ConstructedConfiguredSequenceWeighted.Data) (j : ℕ) :
    edgePhysicalDefect D j ≤ edgeCompositionPhysicalDefect D j := by
  unfold edgePhysicalDefect
    ConfiguredPolynomialDiagonalStableRowDefectProvider.physicalDefect
    edgeCompositionPhysicalDefect edgeCompositionPhysicalCoeff
  have hc : 0 ≤ edgeCompositionCoeff D j :=
    (edgeCompositionCoeffEnvelope D).value_nonneg j
  have hd : 0 ≤ rowDefect D j := rowDefect_nonneg D j
  nlinarith

/-- The base raw edge pays both its variable-speed factor and endpoint cap. -/
theorem baseRawEdgeBudget_le_fullRecostMetricDiagonal
    (D : ConstructedConfiguredSequenceWeighted.Data)
    (MA NA E0 C0 C1 C2 M pathFactor rawBound endpointCap : ℝ) (q : ℕ)
    (hfactor : pathFactor ≤ edgeConversion D (analyticKhat D) MA NA q)
    (hraw : rawBound ≤ edgeCompositionPhysicalDefect D (q + 1))
    (hraw0 : 0 ≤ rawBound)
    (hendpoint : endpointCap ≤
      edgeEndpointConversion D sourceKh M q * edgePhysicalDefect D (q + 1)) :
    pathFactor * rawBound + endpointCap ≤
      fullRecostMetricDiagonal D MA NA E0 C0 C1 C2 M q := by
  let K := edgeConversion D (analyticKhat D) MA NA q
  let B := edgeEndpointConversion D sourceKh M q
  let dc := edgeCompositionPhysicalDefect D (q + 1)
  let d := edgePhysicalDefect D (q + 1)
  have hK0 : 0 ≤ K := edgeConversion_nonnegative D _ _ _ q
  have hB0 : 0 ≤ B := edgeEndpointConversion_nonnegative D
    sourceKh_nonnegative sourceKh_lt_one q
  have hdle : d ≤ dc := edgePhysicalDefect_le_edgeCompositionPhysicalDefect D _
  have hpath : pathFactor * rawBound ≤ K * dc :=
    mul_le_mul hfactor hraw hraw0 hK0
  have hcap : endpointCap ≤ B * dc :=
    hendpoint.trans (mul_le_mul_of_nonneg_left hdle hB0)
  calc
    pathFactor * rawBound + endpointCap ≤ K * dc + B * dc :=
      add_le_add hpath hcap
    _ = baseDisplayedMetricDiagonal D MA NA M q := by
      simp [baseDisplayedMetricDiagonal, weightedSequence,
        edgeCombinedConversion, K, B, dc]
      ring
    _ ≤ fullRecostMetricDiagonal D MA NA E0 C0 C1 C2 M q :=
      le_add_of_nonneg_left (multiplierRecostDirectDiagonal_nonnegative D q)

/-- Polynomial composition defects retain a pointwise exponential bound. -/
theorem exists_edgeCompositionPhysicalDefect_exp_bound
    (D : ConstructedConfiguredSequenceWeighted.Data) :
    ∃ beta K : ℝ, 0 < beta ∧ 0 ≤ K ∧ ∀ n,
      edgeCompositionPhysicalDefect D n ≤
        K * Real.exp (-(beta * D.Hs n)) := by
  let beta : ℝ := D.model.beta / 8
  have hmodelBeta : 0 < D.model.beta := (D.model.configs 0).hbeta0
  have hbeta : 0 < beta := div_pos hmodelBeta (by norm_num)
  let B := edgeCompositionPhysicalCoeffEnvelope D
  obtain ⟨E, hE0, hE⟩ := exists_one_add_pow_le_exp B.degree hbeta
  let Amodel := ModelDefectSummable.modelDefectConst
    (2 * D.kd) D.kstar (edgeCoefficient D) (D.Hs 0) D.model.beta
  have hAmodel : 0 ≤ Amodel :=
    ModelDefectSummable.modelDefectConst_nonneg
      (edgeCoefficient_nonneg D) D.kstar_nonneg D.separation_zero_pos hmodelBeta
  let K : ℝ := B.coeff * E * configuredCostConst D * Amodel
  have hK : 0 ≤ K := by
    dsimp [K]
    exact mul_nonneg
      (mul_nonneg (mul_nonneg B.coeff_nonneg hE0)
        (configuredCostConst_nonneg D)) hAmodel
  have hmodel : ∀ n, rowModelDefect D n ≤
      Amodel * Real.exp (-((D.model.beta / 4) * D.Hs n)) := by
    intro n
    simpa [Amodel, rowModelDefect] using
      (ModelDefectSummable.model_defect_le
        (M := 2 * D.kd) (kb := D.kstar) (Cm := edgeCoefficient D)
        (P0 := D.Hs 0) (beta := D.model.beta)
        (Hs := D.Hs) (eps := edgeEps D) (P := D.Hs)
        hmodelBeta (mul_nonneg (by norm_num) D.kd_nonneg)
        (edgeCoefficient_nonneg D) D.kstar_nonneg D.separation_zero_pos
        D.separation_lower (fun i ↦ (D.model.separation_pos i).le)
        (edgeEps_nonneg D) (edgeEps_le_exp_at_row D) n)
  refine ⟨beta, K, hbeta, hK, ?_⟩
  intro n
  have hH : 0 ≤ D.Hs n := (D.model.separation_pos n).le
  have hBexp : edgeCompositionPhysicalCoeff D n ≤
      B.coeff * E * Real.exp (beta * D.Hs n) := by
    calc
      edgeCompositionPhysicalCoeff D n ≤
          B.coeff * (1 + D.Hs n) ^ B.degree := B.bound n
      _ ≤ B.coeff * (E * Real.exp (beta * D.Hs n)) :=
        mul_le_mul_of_nonneg_left (hE (D.Hs n) hH) B.coeff_nonneg
      _ = B.coeff * E * Real.exp (beta * D.Hs n) := by ring
  have hdef : rowDefect D n ≤ configuredCostConst D * Amodel *
      Real.exp (-((D.model.beta / 4) * D.Hs n)) := by
    exact (rowDefect_le_configuredCostConst D n).trans <| by
      calc
        configuredCostConst D * rowModelDefect D n ≤
            configuredCostConst D *
              (Amodel * Real.exp (-((D.model.beta / 4) * D.Hs n))) :=
          mul_le_mul_of_nonneg_left (hmodel n) (configuredCostConst_nonneg D)
        _ = _ := by ring
  unfold edgeCompositionPhysicalDefect
  calc
    edgeCompositionPhysicalCoeff D n * rowDefect D n ≤
        (B.coeff * E * Real.exp (beta * D.Hs n)) *
          (configuredCostConst D * Amodel *
            Real.exp (-((D.model.beta / 4) * D.Hs n))) :=
      mul_le_mul hBexp hdef (rowDefect_nonneg D n)
        (mul_nonneg (mul_nonneg B.coeff_nonneg hE0) (Real.exp_pos _).le)
    _ = K * Real.exp (-(beta * D.Hs n)) := by
      rw [show -(beta * D.Hs n) = beta * D.Hs n +
          -((D.model.beta / 4) * D.Hs n) by
        dsimp [beta]
        ring, Real.exp_add]
      dsimp [K]
      ring

theorem exists_baseDisplayedMetricDiagonal_exp_bound
    (D : ConstructedConfiguredSequenceWeighted.Data)
    {MA NA M : ℝ} (hMA : 0 ≤ MA) (hNA : 0 ≤ NA) (hM : 0 ≤ M) :
    ∃ beta K : ℝ, 0 < beta ∧ 0 ≤ K ∧ ∀ q,
      baseDisplayedMetricDiagonal D MA NA M q ≤
        K * Real.exp (-(beta * D.Hs q)) := by
  obtain ⟨b, A, hb, hA, hd⟩ :=
    exists_edgeCompositionPhysicalDefect_exp_bound D
  let gamma : ℝ := b / 2
  have hgamma0 : 0 < gamma := half_pos hb
  have hgamma : gamma < b := by dsimp [gamma]; linarith
  obtain ⟨C0, hC0, hCgrowth⟩ :=
    exists_edgeCombinedConversion_growth_majorant D hMA hNA
      (analyticKhat_nonnegative D) sourceKh_nonnegative sourceKh_lt_one
      hM hgamma0
  simpa [baseDisplayedMetricDiagonal] using
    (exists_weightedSequence_exp_bound_of_growth D
      (edgeCombinedConversion D MA NA (analyticKhat D) sourceKh M)
      (edgeCompositionPhysicalDefect D)
      hC0 hA hb hgamma
      (edgeCombinedConversion_nonnegative D sourceKh_nonnegative sourceKh_lt_one)
      hCgrowth (edgeCompositionPhysicalDefect_nonnegative D)
      (fun j ↦ by simpa using hd j))

theorem exists_fullRecostMetricDiagonal_exp_bound
    (D : ConstructedConfiguredSequenceWeighted.Data)
    {MA NA E0 C0 C1 C2 M : ℝ}
    (hMA : 0 ≤ MA) (hNA : 0 ≤ NA) (hM : 0 ≤ M) :
    ∃ beta K : ℝ, 0 < beta ∧ 0 ≤ K ∧ ∀ q,
      fullRecostMetricDiagonal D MA NA E0 C0 C1 C2 M q ≤
        K * Real.exp (-(beta * D.Hs q)) := by
  obtain ⟨b1, K1, hb1, hK1, h1⟩ :=
    exists_multiplierRecostDirectDiagonal_exp_bound D
      (E0 := E0) (C0 := C0) (C1 := C1) (C2 := C2) hMA hNA hM
  obtain ⟨b2, K2, hb2, hK2, h2⟩ :=
    exists_baseDisplayedMetricDiagonal_exp_bound D hMA hNA hM
  refine ⟨min b1 b2, K1 + K2, lt_min hb1 hb2, add_nonneg hK1 hK2, ?_⟩
  intro q
  have hH : 0 ≤ D.Hs q := (D.model.separation_pos q).le
  have hnext : D.Hs q ≤ D.Hs (q + 1) := by
    linarith [D.separation_step q, D.deltaStep_pos]
  have he1 : Real.exp (-(b1 * D.Hs (q + 1))) ≤
      Real.exp (-(min b1 b2 * D.Hs q)) := Real.exp_le_exp.mpr (by
    have hmin : min b1 b2 * D.Hs q ≤ b1 * D.Hs q :=
      mul_le_mul_of_nonneg_right (min_le_left b1 b2) hH
    have hstep : b1 * D.Hs q ≤ b1 * D.Hs (q + 1) :=
      mul_le_mul_of_nonneg_left hnext hb1.le
    linarith)
  have he2 : Real.exp (-(b2 * D.Hs q)) ≤
      Real.exp (-(min b1 b2 * D.Hs q)) := Real.exp_le_exp.mpr (by
    have := mul_le_mul_of_nonneg_right (min_le_right b1 b2) hH
    linarith)
  calc
    fullRecostMetricDiagonal D MA NA E0 C0 C1 C2 M q ≤
        K1 * Real.exp (-(b1 * D.Hs (q + 1))) +
          K2 * Real.exp (-(b2 * D.Hs q)) := add_le_add (h1 q) (h2 q)
    _ ≤ K1 * Real.exp (-(min b1 b2 * D.Hs q)) +
          K2 * Real.exp (-(min b1 b2 * D.Hs q)) :=
      add_le_add (mul_le_mul_of_nonneg_left he1 hK1)
        (mul_le_mul_of_nonneg_left he2 hK2)
    _ = (K1 + K2) * Real.exp (-(min b1 b2 * D.Hs q)) := by ring

theorem fullRecostMetricDiagonal_summable
    (D : ConstructedConfiguredSequenceWeighted.Data)
    {MA NA E0 C0 C1 C2 M : ℝ}
    (hMA : 0 ≤ MA) (hNA : 0 ≤ NA) (hM : 0 ≤ M) :
    Summable (fullRecostMetricDiagonal D MA NA E0 C0 C1 C2 M) := by
  obtain ⟨beta, K, hbeta, hK, hbound⟩ :=
    exists_fullRecostMetricDiagonal_exp_bound D hMA hNA hM
  have hs :=
    (ModelDefectSummable.summable_exp_neg_of_growth hbeta
      D.deltaStep_pos D.separation_linear).mul_left K
  exact Summable.of_nonneg_of_le
    (fullRecostMetricDiagonal_nonnegative D) hbound hs

theorem exists_fullRecostMetricOutputAfter
    (D : ConstructedConfiguredSequenceWeighted.Data) (N : ℕ)
    {MA NA E0 C0 C1 C2 M Cw : ℝ}
    (hMA : 0 ≤ MA) (hNA : 0 ≤ NA) (hM : 0 ≤ M) (hCw : 0 ≤ Cw) :
    Nonempty (ExponentialDiagonalLargeSeparation.Output
      (ConstructedConfiguredInductiveTubeBudget.WeightedData.shift D N)
      (fun _ ↦ 1)
      (ExponentialDiagonalLargeSeparation.shiftSequence
        (fullRecostMetricDiagonal D MA NA E0 C0 C1 C2 M) N) Cw) := by
  obtain ⟨beta, K, hbeta, hK, hdiag⟩ :=
    exists_fullRecostMetricDiagonal_exp_bound D
      (E0 := E0) (C0 := C0) (C1 := C1) (C2 := C2) hMA hNA hM
  let Dp := ConstructedConfiguredInductiveTubeBudget.WeightedData.shift D N
  let w := fullRecostMetricDiagonal D MA NA E0 C0 C1 C2 M
  let wp := ExponentialDiagonalLargeSeparation.shiftSequence w N
  let gamma := beta / 2
  have hgamma : gamma < beta := by dsimp [gamma]; linarith
  apply ExponentialDiagonalLargeSeparation.exists_output Dp (fun _ ↦ 1) wp
    (fun _ ↦ zero_le_one) zero_le_one hK hbeta hgamma
  · intro j
    have hH : 0 ≤ Dp.Hs j := (Dp.model.separation_pos j).le
    have hg0 : 0 ≤ gamma := (half_pos hbeta).le
    have hsq : 1 ≤ (1 + Dp.Hs j) ^ 2 := by
      nlinarith [sq_nonneg (Dp.Hs j)]
    have hexp : 1 ≤ Real.exp (gamma * Dp.Hs j) := by
      rw [← Real.exp_zero]
      exact Real.exp_le_exp.mpr (mul_nonneg hg0 hH)
    simpa using mul_le_mul hsq hexp zero_le_one
      (sq_nonneg (1 + Dp.Hs j))
  · intro j
    exact fullRecostMetricDiagonal_nonnegative D (N + j)
  · intro j
    simpa [wp, w, Dp, ExponentialDiagonalLargeSeparation.shiftSequence,
      ConstructedConfiguredInductiveTubeBudget.WeightedData.shift,
      Nat.add_assoc] using hdiag (N + j)
  · exact hCw

end ConfiguredRecursiveEdgeFullRecostMetricDiagonal
