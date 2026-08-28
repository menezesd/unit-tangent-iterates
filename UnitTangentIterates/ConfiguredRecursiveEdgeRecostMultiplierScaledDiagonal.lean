import UnitTangentIterates.ConfiguredRecursiveEdgeRecostPeriodScaledDiagonal
import UnitTangentIterates.ConfiguredRecursiveEdgeRecostedAnalyticCarrier

/-! # Multiplier- and period-scaled direct recost diagonal -/

noncomputable section

open Filter Real

namespace ConfiguredRecursiveEdgeRecostMultiplierScaledDiagonal

open ConfiguredCombinedPhysicalDiagonalLargeSeparation
  ConfiguredRecursiveEdgeSourceP0Growth
  ConfiguredRecursiveEdgeFiniteColumnGaugeMajorant
  ConfiguredRecursiveEdgeFiniteColumnScalarClosing
  ConfiguredRecursiveEdgeRecostedAnalyticCarrier
  ConfiguredRecursiveEdgeRecostPeriodScaledDiagonal
  ConstructedRowCPolynomialGrowth

/-- The exact multiplier required by the direct canonical derivative bound.
Doubling the legacy composition coefficient pays the additional
`sourceConst * P1²` caused by canonical recost differentiation. -/
def directRecostCompositionCoeff
    (D : ConstructedConfiguredSequenceWeighted.Data) (j : ℕ) : ℝ :=
  2 * edgeCompositionCoeff D j

theorem edgeCompositionCoeff_le_directRecostCompositionCoeff
    (D : ConstructedConfiguredSequenceWeighted.Data) (j : ℕ) :
    edgeCompositionCoeff D j ≤ directRecostCompositionCoeff D j := by
  unfold directRecostCompositionCoeff
  nlinarith [edgeCompositionCoeff_one_le D j]

theorem directRecostCompositionCoeff_two_le
    (D : ConstructedConfiguredSequenceWeighted.Data) (j : ℕ) :
    2 ≤ directRecostCompositionCoeff D j := by
  unfold directRecostCompositionCoeff
  linarith [edgeCompositionCoeff_one_le D j]

theorem directRecostCompositionCoeff_first
    (D : ConstructedConfiguredSequenceWeighted.Data) (j : ℕ) :
    2 * edgeFlowP1AtOne D j ≤ directRecostCompositionCoeff D j :=
  (edgeCompositionCoeff_first D j).trans
    (edgeCompositionCoeff_le_directRecostCompositionCoeff D j)

theorem directRecostCompositionCoeff_second
    (D : ConstructedConfiguredSequenceWeighted.Data) (j : ℕ) :
    (2 *
        FiniteSmoothRearFamilyMarkingAwareSmoothSource.intrinsicSourceConst sourceKh
          (FiniteSmoothRearFamilyMarkingAwareSmoothSource.intrinsicDerivativeConst sourceKh) + 2) *
          edgeFlowP1AtOne D j ^ 2 + 2 * edgeFlowG1AtOne D j ≤
      directRecostCompositionCoeff D j := by
  have H := edgeCompositionCoeff_second D j
  have hp : 0 ≤ edgeFlowP1AtOne D j ^ 2 := sq_nonneg _
  have hg : 0 ≤ edgeFlowG1AtOne D j := by
    unfold edgeFlowG1AtOne GaugeFlowDerivCost.costG1
    exact mul_nonneg (sq_nonneg _)
      (mul_nonneg
        (GaugeMarkedDataOfRearFamily.rearKappa2_nonneg
          sourceKh_nonnegative sourceKh_lt_one) zero_le_one)
  have hs := ConfiguredRecursiveSourceP0Growth.intrinsicSourceConst_nonnegative
  unfold directRecostCompositionCoeff
  nlinarith

/-- Public direct diagonal after both normalized-history period scaling and
composition-density scaling.  The leading `2` pays the configured
inverse-square-root loss at `sourceKh`. -/
def multiplierRecostDirectDiagonal
    (D : ConstructedConfiguredSequenceWeighted.Data)
    (MA NA E0 C0 C1 C2 M : ℝ) (j : ℕ) : ℝ :=
  2 * directRecostCompositionCoeff D j *
    recostDirectDiagonal D MA NA E0 C0 C1 C2 M j

theorem multiplierRecostDirectDiagonal_nonnegative
    (D : ConstructedConfiguredSequenceWeighted.Data)
    {MA NA E0 C0 C1 C2 M : ℝ} :
    ∀ j, 0 ≤ multiplierRecostDirectDiagonal D MA NA E0 C0 C1 C2 M j := by
  intro j
  exact mul_nonneg
    (mul_nonneg (by norm_num)
      ((by norm_num : (0 : ℝ) ≤ 2).trans
        (directRecostCompositionCoeff_two_le D j)))
    (recostDirectDiagonal_nonnegative D j)

/-- The actual multiplier source mass allowed by a normalized history with
`d = 2 * L² * edgePhysicalDefect`. -/
def multiplierRecostSourceAllowance
    (D : ConstructedConfiguredSequenceWeighted.Data)
    (E0 C0 C1 C2 : ℝ) (q : ℕ) : ℝ :=
  directRecostCompositionCoeff D q /
      Real.sqrt (1 - sourceKh ^ 2) *
    (4 * configuredTarget E0 C0 C1 C2 *
      (2 * recostPeriodScale D q * edgePhysicalDefect D (q + 1)))

theorem multiplierRecostSourceAllowance_nonnegative
    (D : ConstructedConfiguredSequenceWeighted.Data)
    (E0 C0 C1 C2 : ℝ) (q : ℕ) :
    0 ≤ multiplierRecostSourceAllowance D E0 C0 C1 C2 q := by
  unfold multiplierRecostSourceAllowance
  exact mul_nonneg
    (div_nonneg ((by norm_num : (0 : ℝ) ≤ 2).trans
      (directRecostCompositionCoeff_two_le D q))
      (Real.sqrt_nonneg _))
    (mul_nonneg
      (mul_nonneg (by norm_num) (configuredTarget_nonnegative E0 C0 C1 C2))
      (mul_nonneg
        (mul_nonneg (by norm_num) (recostPeriodScale_nonnegative D q))
        (edgePhysicalDefect_nonnegative D (q + 1))))

/-- The updated public diagonal pays the complete multiplier source mass. -/
theorem multiplierRecostSourceAllowance_le_diagonal
    (D : ConstructedConfiguredSequenceWeighted.Data)
    (MA NA E0 C0 C1 C2 M : ℝ) (q : ℕ) :
    multiplierRecostSourceAllowance D E0 C0 C1 C2 q ≤
      multiplierRecostDirectDiagonal D MA NA E0 C0 C1 C2 M q := by
  let c := directRecostCompositionCoeff D q
  let L2 := recostPeriodScale D q
  let T := configuredTarget E0 C0 C1 C2
  let K := edgeConversion D (analyticKhat D) MA NA q
  let e := edgePhysicalDefect D (q + 1)
  have hc0 : 0 ≤ c := (by
    dsimp [c]
    exact (by norm_num : (0 : ℝ) ≤ 2).trans
      (directRecostCompositionCoeff_two_le D q))
  have hL0 : 0 ≤ L2 := recostPeriodScale_nonnegative D q
  have hT0 : 0 ≤ T := configuredTarget_nonnegative E0 C0 C1 C2
  have hK : 1 ≤ K :=
    NormalPathC2IncrementVariableSpeed.one_le_c2ConstVar _ _ _ _ _
  have he0 : 0 ≤ e := edgePhysicalDefect_nonnegative D (q + 1)
  have hs := div_sqrt_sourceKh_le_two_mul hc0
  have hend : 0 ≤ edgeEndpointConversion D sourceKh M q :=
    edgeEndpointConversion_nonnegative D sourceKh_nonnegative sourceKh_lt_one q
  have hmain :
      2 * c * (4 * T * (2 * L2 * e)) ≤
        2 * c * ((4 * T + 1) *
          ((2 * L2 * K + edgeEndpointConversion D sourceKh M q) * e)) := by
    have hLK : 2 * L2 ≤ 2 * L2 * K := by
      calc
        2 * L2 = (2 * L2) * 1 := by ring
        _ ≤ (2 * L2) * K :=
          mul_le_mul_of_nonneg_left hK (mul_nonneg (by norm_num) hL0)
    have hinside : 2 * L2 * e ≤
        (2 * L2 * K + edgeEndpointConversion D sourceKh M q) * e :=
      mul_le_mul_of_nonneg_right
        (hLK.trans (le_add_of_nonneg_right hend)) he0
    have hfactor : 4 * T ≤ 4 * T + 1 := by linarith
    have hproduct : 4 * T * (2 * L2 * e) ≤
        (4 * T + 1) *
          ((2 * L2 * K + edgeEndpointConversion D sourceKh M q) * e) :=
      mul_le_mul hfactor hinside
        (mul_nonneg (mul_nonneg (by norm_num) hL0) he0)
        (by linarith)
    exact mul_le_mul_of_nonneg_left hproduct (mul_nonneg (by norm_num) hc0)
  calc
    multiplierRecostSourceAllowance D E0 C0 C1 C2 q =
        (c / Real.sqrt (1 - sourceKh ^ 2)) *
          (4 * T * (2 * L2 * e)) := by rfl
    _ ≤ (2 * c) * (4 * T * (2 * L2 * e)) :=
      mul_le_mul_of_nonneg_right hs
        (mul_nonneg (mul_nonneg (by norm_num) hT0)
          (mul_nonneg (mul_nonneg (by norm_num) hL0) he0))
    _ ≤ 2 * c * ((4 * T + 1) *
          ((2 * L2 * K + edgeEndpointConversion D sourceKh M q) * e)) := hmain
    _ = multiplierRecostDirectDiagonal D MA NA E0 C0 C1 C2 M q := by
      unfold multiplierRecostDirectDiagonal recostDirectDiagonal
        ConfiguredRecursiveEdgeWeightedEffectiveError.weightedSequence
        recostDirectConversion recostCombinedConversion recostEdgeConversion
        directScale
      dsimp [c, L2, T, K, e]
      ring

/-- The multiplier diagonal still has exponential decay. -/
theorem exists_multiplierRecostDirectDiagonal_exp_bound
    (D : ConstructedConfiguredSequenceWeighted.Data)
    {MA NA E0 C0 C1 C2 M : ℝ}
    (hMA : 0 ≤ MA) (hNA : 0 ≤ NA) (hM : 0 ≤ M) :
    ∃ beta K : ℝ, 0 < beta ∧ 0 ≤ K ∧ ∀ j,
      multiplierRecostDirectDiagonal D MA NA E0 C0 C1 C2 M j ≤
        K * Real.exp (-(beta * D.Hs (j + 1))) := by
  obtain ⟨beta0, K0, hbeta0, hK0, hdiag⟩ :=
    exists_recostDirectDiagonal_exp_bound D
      (E0 := E0) (C0 := C0) (C1 := C1) (C2 := C2)
      hMA hNA hM
  let gamma := beta0 / 2
  let beta := beta0 / 2
  have hgamma : 0 < gamma := half_pos hbeta0
  have hbeta : 0 < beta := half_pos hbeta0
  obtain ⟨A, hA0, hpoly⟩ := exists_one_add_pow_le_exp 2 hgamma
  let Ec := edgeCompositionCoeffEnvelope D
  let K := 4 * Ec.coeff * A * K0
  have hK : 0 ≤ K := by
    dsimp [K]
    exact mul_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) Ec.coeff_nonneg) hA0) hK0
  refine ⟨beta, K, hbeta, hK, ?_⟩
  intro j
  have hnext : D.Hs j ≤ D.Hs (j + 1) := by
    linarith [D.separation_step j, D.deltaStep_pos]
  have hx0 : 0 ≤ 1 + D.Hs j := by
    linarith [(D.model.separation_pos j).le]
  have hxnext0 : 0 ≤ 1 + D.Hs (j + 1) := by
    linarith [(D.model.separation_pos (j + 1)).le]
  have hp : (1 + D.Hs j) ^ 2 ≤ (1 + D.Hs (j + 1)) ^ 2 := by
    exact pow_le_pow_left₀ hx0 (by linarith) 2
  have hec : edgeCompositionCoeff D j ≤
      Ec.coeff * (1 + D.Hs j) ^ 2 := Ec.bound j
  have hc : directRecostCompositionCoeff D j ≤
      2 * Ec.coeff * (1 + D.Hs (j + 1)) ^ 2 := by
    unfold directRecostCompositionCoeff
    convert mul_le_mul_of_nonneg_left
      (hec.trans
        (mul_le_mul_of_nonneg_left hp Ec.coeff_nonneg))
      (by norm_num : (0 : ℝ) ≤ 2) using 1 <;> ring
  have hpoly' := hpoly (D.Hs (j + 1)) (D.model.separation_pos (j + 1)).le
  have hm := mul_le_mul hc (hdiag j)
    (recostDirectDiagonal_nonnegative D j)
    (mul_nonneg (mul_nonneg (by norm_num) Ec.coeff_nonneg)
      (pow_nonneg hxnext0 2))
  calc
    multiplierRecostDirectDiagonal D MA NA E0 C0 C1 C2 M j =
        2 * (directRecostCompositionCoeff D j *
          recostDirectDiagonal D MA NA E0 C0 C1 C2 M j) := by
      unfold multiplierRecostDirectDiagonal
      ring
    _ ≤ 2 * (((2 * Ec.coeff) * (1 + D.Hs (j + 1)) ^ 2) *
          (K0 * Real.exp (-(beta0 * D.Hs (j + 1))))) := by
      exact mul_le_mul_of_nonneg_left hm (by norm_num)
    _ ≤ 2 * (((2 * Ec.coeff) *
          (A * Real.exp (gamma * D.Hs (j + 1)))) *
          (K0 * Real.exp (-(beta0 * D.Hs (j + 1))))) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply mul_le_mul_of_nonneg_right _
        (mul_nonneg hK0 (Real.exp_pos _).le)
      exact mul_le_mul_of_nonneg_left hpoly'
        (mul_nonneg (by norm_num) Ec.coeff_nonneg)
    _ = K * Real.exp (-(beta * D.Hs (j + 1))) := by
      rw [show -(beta * D.Hs (j + 1)) =
          gamma * D.Hs (j + 1) + -(beta0 * D.Hs (j + 1)) by
        dsimp [beta, gamma]
        ring, Real.exp_add]
      dsimp [K]
      ring

theorem multiplierRecostDirectDiagonal_summable
    (D : ConstructedConfiguredSequenceWeighted.Data)
    {MA NA E0 C0 C1 C2 M : ℝ}
    (hMA : 0 ≤ MA) (hNA : 0 ≤ NA) (hM : 0 ≤ M) :
    Summable (multiplierRecostDirectDiagonal D MA NA E0 C0 C1 C2 M) := by
  obtain ⟨beta, K, hbeta, hK, hbound⟩ :=
    exists_multiplierRecostDirectDiagonal_exp_bound D hMA hNA hM
  have hs : Summable (fun j : ℕ ↦
      K * Real.exp (-(beta * D.Hs (j + 1)))) := by
    have hbase := ModelDefectSummable.summable_exp_neg_of_growth hbeta
      D.deltaStep_pos D.separation_linear
    exact (hbase.comp_injective (by
      intro a b hab
      exact Nat.add_right_cancel hab)).mul_left K
  exact Summable.of_nonneg_of_le
    (multiplierRecostDirectDiagonal_nonnegative D) hbound hs

/-- A tail after which every actual multiplier source allowance is at most
one. -/
theorem exists_multiplierRecostSourceAllowance_tail_le_one
    (D : ConstructedConfiguredSequenceWeighted.Data)
    {MA NA E0 C0 C1 C2 M : ℝ}
    (hMA : 0 ≤ MA) (hNA : 0 ≤ NA) (hM : 0 ≤ M) :
    ∃ N, ∀ q, N ≤ q →
      multiplierRecostSourceAllowance D E0 C0 C1 C2 q ≤ 1 := by
  have ht := (multiplierRecostDirectDiagonal_summable D
    (E0 := E0) (C0 := C0) (C1 := C1) (C2 := C2)
    hMA hNA hM).tendsto_atTop_zero
  have he := ht.eventually (Iic_mem_nhds (show (0 : ℝ) < 1 by norm_num))
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 he
  exact ⟨N, fun q hq ↦
    (multiplierRecostSourceAllowance_le_diagonal D MA NA E0 C0 C1 C2 M q).trans
      (hN q hq)⟩

/-- The exponential large-separation package may be started after an
arbitrary preliminary mass tail. -/
theorem exists_multiplierRecostDirectOutputAfter
    (D : ConstructedConfiguredSequenceWeighted.Data) (N : ℕ)
    {MA NA E0 C0 C1 C2 M Cw : ℝ}
    (hMA : 0 ≤ MA) (hNA : 0 ≤ NA) (hM : 0 ≤ M) (hCw : 0 ≤ Cw) :
    Nonempty (ExponentialDiagonalLargeSeparation.Output
      (ConstructedConfiguredInductiveTubeBudget.WeightedData.shift D N)
      (fun _ ↦ 1)
      (ExponentialDiagonalLargeSeparation.shiftSequence
        (multiplierRecostDirectDiagonal D MA NA E0 C0 C1 C2 M) N)
      Cw) := by
  obtain ⟨beta, K, hbeta, hK, hdiag⟩ :=
    exists_multiplierRecostDirectDiagonal_exp_bound D
      (E0 := E0) (C0 := C0) (C1 := C1) (C2 := C2) hMA hNA hM
  let Dp := ConstructedConfiguredInductiveTubeBudget.WeightedData.shift D N
  let w := multiplierRecostDirectDiagonal D MA NA E0 C0 C1 C2 M
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
    exact multiplierRecostDirectDiagonal_nonnegative D (N + j)
  · intro j
    have H := hdiag (N + j)
    have hstep : D.Hs (N + j) ≤ D.Hs (N + j + 1) := by
      linarith [D.separation_step (N + j), D.deltaStep_pos]
    have hexp : Real.exp (-(beta * D.Hs (N + j + 1))) ≤
        Real.exp (-(beta * D.Hs (N + j))) :=
      Real.exp_le_exp.mpr (by
        have := mul_le_mul_of_nonneg_left hstep hbeta.le
        linarith)
    simpa [wp, w, Dp,
      ExponentialDiagonalLargeSeparation.shiftSequence,
      ConstructedConfiguredInductiveTubeBudget.WeightedData.shift,
      Nat.add_assoc] using H.trans (mul_le_mul_of_nonneg_left hexp hK)
  · exact hCw

end ConfiguredRecursiveEdgeRecostMultiplierScaledDiagonal
