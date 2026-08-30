import UnitTangentIterates.ConfiguredRecursiveEdgeFiniteColumnGaugeMajorant
import UnitTangentIterates.ConfiguredRecursiveEdgeWeightedEffectiveError
import UnitTangentIterates.ReachableVariableSpeedFrontCurvature

/-! # Combined configured scalar closing data for finite columns -/

noncomputable section

open Filter Real

namespace ConfiguredRecursiveEdgeFiniteColumnScalarClosing

open ConfiguredRecursiveEdgeFiniteColumnGaugeMajorant
  AnchoredJacobiStableTransition
  ConfiguredRecursiveEdgeSourceP0Growth
  ConfiguredRecursiveEdgeWeightedEffectiveError
  ConfiguredPolynomialDiagonalStableRowDefectProvider
  ConfiguredRecursiveSourceP0RowJetTail
  ConstructedConfiguredInductiveTubeBudget
  ConstructedConfiguredInductiveTubeBudget.WeightedData
  ConstructedRowCPolynomialGrowth
  ExponentialDiagonalLargeSeparation
  ConfiguredCombinedPhysicalDiagonalLargeSeparation
  NearIdentityDistortionBudget

variable {MA NA : ℝ}

def directScale (E0 C0 C1 C2 : ℝ) : ℝ :=
  4 * configuredTarget E0 C0 C1 C2 + 1

def directConversion (D : ConstructedConfiguredSequenceWeighted.Data)
    (MA NA E0 C0 C1 C2 M : ℝ) (j : ℕ) : ℝ :=
  directScale E0 C0 C1 C2 *
    edgeCombinedConversion D MA NA (analyticKhat D) sourceKh M j

def directDiagonal (D : ConstructedConfiguredSequenceWeighted.Data)
    (MA NA E0 C0 C1 C2 M : ℝ) : ℕ → ℝ :=
  weightedSequence (directConversion D MA NA E0 C0 C1 C2 M)
    (edgePhysicalDefect D)

theorem directScale_nonnegative (E0 C0 C1 C2 : ℝ) :
    0 ≤ directScale E0 C0 C1 C2 := by
  exact add_nonneg
    (mul_nonneg (by norm_num) (configuredTarget_nonnegative E0 C0 C1 C2))
    zero_le_one

theorem directDiagonal_nonnegative
    (D : ConstructedConfiguredSequenceWeighted.Data)
    {MA NA E0 C0 C1 C2 M : ℝ}
    (hMA : 0 ≤ MA) (hNA : 0 ≤ NA) (hM : 0 ≤ M) :
    ∀ j, 0 ≤ directDiagonal D MA NA E0 C0 C1 C2 M j := by
  intro j
  exact mul_nonneg
    (mul_nonneg (directScale_nonnegative E0 C0 C1 C2)
      (edgeCombinedConversion_nonnegative D sourceKh_nonnegative
        sourceKh_lt_one j))
    (edgePhysicalDefect_nonnegative D (j + 1))

/-- The fully configured direct diagonal is summable before any tail shift.
This is the summability input needed by the depthwise raw-source gauge
majorant. -/
theorem directDiagonal_summable
    (D : ConstructedConfiguredSequenceWeighted.Data)
    {MA NA E0 C0 C1 C2 M : ℝ}
    (hMA : 0 ≤ MA) (hNA : 0 ≤ NA) (hM : 0 ≤ M) :
    Summable (directDiagonal D MA NA E0 C0 C1 C2 M) := by
  let C := directConversion D MA NA E0 C0 C1 C2 M
  let d := edgePhysicalDefect D
  have hC0 : ∀ j, 0 ≤ C j := fun j ↦ mul_nonneg
    (directScale_nonnegative E0 C0 C1 C2)
    (edgeCombinedConversion_nonnegative D sourceKh_nonnegative
      sourceKh_lt_one j)
  have hd0 : ∀ j, 0 ≤ d j := edgePhysicalDefect_nonnegative D
  have hbeta : 0 < D.model.beta := (D.model.configs 0).hbeta0
  let gamma : ℝ := D.model.beta / 16
  let b : ℝ := D.model.beta / 8
  have hgamma0 : 0 < gamma := div_pos hbeta (by norm_num)
  have hb0 : 0 < b := div_pos hbeta (by norm_num)
  have hgb : gamma < b := by dsimp [gamma, b]; linarith
  obtain ⟨Cc, hCc0, hCgrowth0⟩ :=
    exists_edgeCombinedConversion_growth_majorant D hMA hNA
      (analyticKhat_nonnegative D) sourceKh_nonnegative sourceKh_lt_one
      hM hgamma0
  let Cs := directScale E0 C0 C1 C2 * Cc
  have hCs0 : 0 ≤ Cs := mul_nonneg (directScale_nonnegative _ _ _ _) hCc0
  have hCgrowth : ∀ j, C j ≤ Cs * (1 + D.Hs j) ^ 2 *
      Real.exp (gamma * D.Hs j) := by
    intro j
    calc
      C j = directScale E0 C0 C1 C2 *
          edgeCombinedConversion D MA NA (analyticKhat D) sourceKh M j := rfl
      _ ≤ directScale E0 C0 C1 C2 *
          (Cc * (1 + D.Hs j) ^ 2 * Real.exp (gamma * D.Hs j)) :=
        mul_le_mul_of_nonneg_left (hCgrowth0 j)
          (directScale_nonnegative E0 C0 C1 C2)
      _ = Cs * (1 + D.Hs j) ^ 2 * Real.exp (gamma * D.Hs j) := by
        dsimp [Cs]
        ring
  obtain ⟨A, hA0, hdexp0⟩ := exists_edgePhysicalDefect_exp_bound D
  have hdexp : ∀ j, d j ≤ A * Real.exp (-(b * D.Hs j)) := by
    intro j
    simpa [d, b] using hdexp0 j
  simpa [directDiagonal, C, d] using
    (summable_weightedSequence_of_growth D C d hCs0 hA0 hb0 hgb
      hC0 hCgrowth hd0 hdexp)

/-- The direct diagonal gives a summable gauge envelope at every fixed row
for the depthwise raw successor tower. -/
theorem depthwiseDirectGaugeMajor_summable
    (D : ConstructedConfiguredSequenceWeighted.Data)
    {MA NA E0 C0 C1 C2 M : ℝ}
    (hMA : 0 ≤ MA) (hNA : 0 ≤ NA) (hM : 0 ≤ M) (n : ℕ) :
    Summable
      (ConfiguredRecursiveEdgeFiniteColumnGaugeMajorant.depthwiseRawGaugeMajor
        D M (directDiagonal D MA NA E0 C0 C1 C2 M) n) :=
  ConfiguredRecursiveEdgeFiniteColumnGaugeMajorant.depthwiseRawGaugeMajor_summable
    D M (directDiagonal_summable D hMA hNA hM) n

/-- Quantitative decay behind `directDiagonal_summable`.  Exporting the
exponential bound allows any further fixed polynomial row amplification to
be absorbed without postulating monotonicity of the raw coefficients. -/
theorem exists_directDiagonal_exp_bound
    (D : ConstructedConfiguredSequenceWeighted.Data)
    {MA NA E0 C0 C1 C2 M : ℝ}
    (hMA : 0 ≤ MA) (hNA : 0 ≤ NA) (hM : 0 ≤ M) :
    ∃ beta K : ℝ, 0 < beta ∧ 0 ≤ K ∧ ∀ j,
      directDiagonal D MA NA E0 C0 C1 C2 M j ≤
        K * Real.exp (-(beta * D.Hs j)) := by
  let C := directConversion D MA NA E0 C0 C1 C2 M
  let d := edgePhysicalDefect D
  have hC0 : ∀ j, 0 ≤ C j := fun j ↦ mul_nonneg
    (directScale_nonnegative E0 C0 C1 C2)
    (edgeCombinedConversion_nonnegative D sourceKh_nonnegative
      sourceKh_lt_one j)
  have hd0 : ∀ j, 0 ≤ d j := edgePhysicalDefect_nonnegative D
  have hbetaModel : 0 < D.model.beta := (D.model.configs 0).hbeta0
  let gamma : ℝ := D.model.beta / 16
  let b : ℝ := D.model.beta / 8
  have hgamma0 : 0 < gamma := div_pos hbetaModel (by norm_num)
  have hb0 : 0 < b := div_pos hbetaModel (by norm_num)
  have hgb : gamma < b := by dsimp [gamma, b]; linarith
  obtain ⟨Cc, hCc0, hCgrowth0⟩ :=
    exists_edgeCombinedConversion_growth_majorant D hMA hNA
      (analyticKhat_nonnegative D) sourceKh_nonnegative sourceKh_lt_one
      hM hgamma0
  let Cs := directScale E0 C0 C1 C2 * Cc
  have hCs0 : 0 ≤ Cs := mul_nonneg (directScale_nonnegative _ _ _ _) hCc0
  have hCgrowth : ∀ j, C j ≤ Cs * (1 + D.Hs j) ^ 2 *
      Real.exp (gamma * D.Hs j) := by
    intro j
    calc
      C j = directScale E0 C0 C1 C2 *
          edgeCombinedConversion D MA NA (analyticKhat D) sourceKh M j := rfl
      _ ≤ directScale E0 C0 C1 C2 *
          (Cc * (1 + D.Hs j) ^ 2 * Real.exp (gamma * D.Hs j)) :=
        mul_le_mul_of_nonneg_left (hCgrowth0 j)
          (directScale_nonnegative E0 C0 C1 C2)
      _ = Cs * (1 + D.Hs j) ^ 2 * Real.exp (gamma * D.Hs j) := by
        dsimp [Cs]
        ring
  obtain ⟨A, hA0, hdexp0⟩ := exists_edgePhysicalDefect_exp_bound D
  have hdexp : ∀ j, d j ≤ A * Real.exp (-(b * D.Hs j)) := by
    intro j
    simpa [d, b] using hdexp0 j
  obtain ⟨beta, K, hbeta, hK, hbound⟩ :=
    exists_weightedSequence_exp_bound_of_growth D C d hCs0 hA0 hb0 hgb
      hC0 hCgrowth hd0 hdexp
  refine ⟨beta, K, hbeta, hK, ?_⟩
  intro j
  simpa [directDiagonal, C, d] using hbound j

/-- Polynomial coefficient evaluated on the actual successor diagonal
`j + 2`.  It dominates the row-jet coefficient at every `n + 1` and the
composition coefficient at every `n` with `n ≤ j`. -/
def depthwiseDirectCoeffMajor
    (D : ConstructedConfiguredSequenceWeighted.Data) (M : ℝ) (j : ℕ) : ℝ :=
  let EJ := rowJetCoeffEnvelope D M
  let EC := edgeCompositionCoeffEnvelope D
  (2 * EJ.coeff * EC.coeff) *
    (1 + D.Hs (j + 2)) ^ (EJ.degree + EC.degree)

/-- One summable scalar sequence dominating every raw recursive gauge error
on the diagonal `j = n + k`. -/
def depthwiseDirectGaugeDiagonal
    (D : ConstructedConfiguredSequenceWeighted.Data)
    (MA NA E0 C0 C1 C2 M : ℝ) (j : ℕ) : ℝ :=
  depthwiseDirectCoeffMajor D M j *
    directDiagonal D MA NA E0 C0 C1 C2 M (j + 2)

theorem depthwiseDirectGaugeDiagonal_nonnegative
    (D : ConstructedConfiguredSequenceWeighted.Data)
    {MA NA E0 C0 C1 C2 M : ℝ}
    (hMA : 0 ≤ MA) (hNA : 0 ≤ NA) (hM : 0 ≤ M) (j : ℕ) :
    0 ≤ depthwiseDirectGaugeDiagonal D MA NA E0 C0 C1 C2 M j := by
  unfold depthwiseDirectGaugeDiagonal depthwiseDirectCoeffMajor
  exact mul_nonneg
    (mul_nonneg
      (mul_nonneg (mul_nonneg (by norm_num)
        (rowJetCoeffEnvelope D M).coeff_nonneg)
        (edgeCompositionCoeffEnvelope D).coeff_nonneg)
      (pow_nonneg (by linarith [(D.model.separation_pos (j + 2)).le]) _))
    (directDiagonal_nonnegative D hMA hNA hM (j + 2))

theorem depthwiseRawGaugeMajor_le_directDiagonal
    (D : ConstructedConfiguredSequenceWeighted.Data)
    {MA NA E0 C0 C1 C2 M : ℝ}
    (hMA : 0 ≤ MA) (hNA : 0 ≤ NA) (hM : 0 ≤ M) (n k : ℕ) :
    ConfiguredRecursiveEdgeFiniteColumnGaugeMajorant.depthwiseRawGaugeMajor
        D M (directDiagonal D MA NA E0 C0 C1 C2 M) n k ≤
      depthwiseDirectGaugeDiagonal D MA NA E0 C0 C1 C2 M (n + k) := by
  let EJ := rowJetCoeffEnvelope D M
  let EC := edgeCompositionCoeffEnvelope D
  have hHmono : Monotone D.Hs :=
    monotone_nat_of_le_succ fun j ↦
      (le_add_of_nonneg_right D.deltaStep_pos.le).trans (D.separation_step j)
  have hn1 : n + 1 ≤ n + k + 2 := by omega
  have hn : n ≤ n + k + 2 := by omega
  have hx0 : 0 ≤ 1 + D.Hs (n + 1) := by
    linarith [(D.model.separation_pos (n + 1)).le]
  have hy0 : 0 ≤ 1 + D.Hs n := by
    linarith [(D.model.separation_pos n).le]
  have hrow : rowJetCoeff D M (n + 1) ≤
      EJ.coeff * (1 + D.Hs (n + k + 2)) ^ EJ.degree :=
    (EJ.bound (n + 1)).trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ hx0 (by linarith [hHmono hn1]) EJ.degree)
      EJ.coeff_nonneg)
  have hcomp : edgeCompositionCoeff D n ≤
      EC.coeff * (1 + D.Hs (n + k + 2)) ^ EC.degree :=
    (EC.bound n).trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ hy0 (by linarith [hHmono hn]) EC.degree)
      EC.coeff_nonneg)
  have hrow0 : 0 ≤ rowJetCoeff D M (n + 1) := EJ.value_nonneg _
  have hcomp0 : 0 ≤ edgeCompositionCoeff D n := EC.value_nonneg _
  have hxj0 : 0 ≤ 1 + D.Hs (n + k + 2) := by
    linarith [(D.model.separation_pos (n + k + 2)).le]
  have hdiag0 : 0 ≤ directDiagonal D MA NA E0 C0 C1 C2 M (n + k + 2) :=
    directDiagonal_nonnegative D hMA hNA hM _
  have hpair : rowJetCoeff D M (n + 1) *
      (2 * edgeCompositionCoeff D n) ≤
      (2 * EJ.coeff * EC.coeff) *
        (1 + D.Hs (n + k + 2)) ^ (EJ.degree + EC.degree) := by
    calc
      rowJetCoeff D M (n + 1) * (2 * edgeCompositionCoeff D n) ≤
          (EJ.coeff * (1 + D.Hs (n + k + 2)) ^ EJ.degree) *
            (2 * (EC.coeff * (1 + D.Hs (n + k + 2)) ^ EC.degree)) :=
        mul_le_mul hrow (mul_le_mul_of_nonneg_left hcomp (by norm_num))
          (mul_nonneg (by norm_num) hcomp0)
          (mul_nonneg EJ.coeff_nonneg
            (pow_nonneg hxj0 _))
      _ = (2 * EJ.coeff * EC.coeff) *
          (1 + D.Hs (n + k + 2)) ^ (EJ.degree + EC.degree) := by
        rw [pow_add]
        ring
  unfold ConfiguredRecursiveEdgeFiniteColumnGaugeMajorant.depthwiseRawGaugeMajor
    depthwiseDirectGaugeDiagonal depthwiseDirectCoeffMajor
  dsimp only [EJ, EC]
  rw [show n + k + 2 = (n + k) + 2 by omega]
  calc
    rowJetCoeff D M (n + 1) *
        (2 * edgeCompositionCoeff D n *
          directDiagonal D MA NA E0 C0 C1 C2 M (n + k + 2)) =
        (rowJetCoeff D M (n + 1) * (2 * edgeCompositionCoeff D n)) *
          directDiagonal D MA NA E0 C0 C1 C2 M (n + k + 2) := by ring
    _ ≤ ((2 * (rowJetCoeffEnvelope D M).coeff *
          (edgeCompositionCoeffEnvelope D).coeff) *
          (1 + D.Hs (n + k + 2)) ^
            ((rowJetCoeffEnvelope D M).degree +
              (edgeCompositionCoeffEnvelope D).degree)) *
        directDiagonal D MA NA E0 C0 C1 C2 M (n + k + 2) :=
      mul_le_mul_of_nonneg_right hpair hdiag0

theorem depthwiseDirectGaugeDiagonal_summable
    (D : ConstructedConfiguredSequenceWeighted.Data)
    {MA NA E0 C0 C1 C2 M : ℝ}
    (hMA : 0 ≤ MA) (hNA : 0 ≤ NA) (hM : 0 ≤ M) :
    Summable (depthwiseDirectGaugeDiagonal D MA NA E0 C0 C1 C2 M) := by
  obtain ⟨beta, K, hbeta, hK, hdiag⟩ :=
    exists_directDiagonal_exp_bound D hMA hNA hM
  let degree := (rowJetCoeffEnvelope D M).degree +
    (edgeCompositionCoeffEnvelope D).degree
  let coeff := 2 * (rowJetCoeffEnvelope D M).coeff *
    (edgeCompositionCoeffEnvelope D).coeff
  have hcoeff : 0 ≤ coeff := by
    dsimp [coeff]
    exact mul_nonneg
      (mul_nonneg (by positivity) (rowJetCoeffEnvelope D M).coeff_nonneg)
      (edgeCompositionCoeffEnvelope D).coeff_nonneg
  obtain ⟨A, hA0, hA⟩ :=
    exists_one_add_pow_le_exp degree (half_pos hbeta)
  have hmajor : Summable (fun j : ℕ ↦
      (coeff * A * K) * Real.exp (-((beta / 2) * D.Hs (j + 2)))) := by
    have H := ModelDefectSummable.summable_exp_neg_of_growth
      (half_pos hbeta) D.deltaStep_pos D.separation_linear
    have Hshift : Summable (fun j : ℕ ↦
        Real.exp (-((beta / 2) * D.Hs (j + 2)))) :=
      H.comp_injective (by
        intro a b hab
        exact Nat.add_right_cancel hab)
    exact Hshift.mul_left (coeff * A * K)
  apply Summable.of_nonneg_of_le
    (depthwiseDirectGaugeDiagonal_nonnegative D hMA hNA hM)
    (fun j ↦ ?_) hmajor
  have hH0 : 0 ≤ D.Hs (j + 2) := (D.model.separation_pos _).le
  have hpoly := hA (D.Hs (j + 2)) hH0
  have hd := hdiag (j + 2)
  have hexp0 : 0 ≤ Real.exp ((beta / 2) * D.Hs (j + 2)) :=
    (Real.exp_pos _).le
  have hnegexp0 : 0 ≤ Real.exp (-(beta * D.Hs (j + 2))) :=
    (Real.exp_pos _).le
  unfold depthwiseDirectGaugeDiagonal depthwiseDirectCoeffMajor
  calc
    ((2 * (rowJetCoeffEnvelope D M).coeff *
          (edgeCompositionCoeffEnvelope D).coeff) *
        (1 + D.Hs (j + 2)) ^ degree) *
        directDiagonal D MA NA E0 C0 C1 C2 M (j + 2) ≤
      (coeff * (A * Real.exp ((beta / 2) * D.Hs (j + 2)))) *
        (K * Real.exp (-(beta * D.Hs (j + 2)))) := by
          apply mul_le_mul
          · simpa [coeff, degree, mul_assoc] using
              mul_le_mul_of_nonneg_left hpoly hcoeff
          · exact hd
          · exact directDiagonal_nonnegative D hMA hNA hM _
          · exact mul_nonneg hcoeff (mul_nonneg hA0 hexp0)
    _ = (coeff * A * K) *
        Real.exp (-((beta / 2) * D.Hs (j + 2))) := by
      rw [show coeff * (A * Real.exp ((beta / 2) * D.Hs (j + 2))) *
          (K * Real.exp (-(beta * D.Hs (j + 2)))) =
          coeff * A * K * (Real.exp ((beta / 2) * D.Hs (j + 2)) *
            Real.exp (-(beta * D.Hs (j + 2)))) by ring,
        ← Real.exp_add]
      congr 1
      ring

/-- The depth-zero source term and the diagonalized raw recursive term share
one scalar sequence. -/
def depthwiseCombinedGaugeDiagonal
    (D : ConstructedConfiguredSequenceWeighted.Data)
    (MA NA E0 C0 C1 C2 M : ℝ) (j : ℕ) : ℝ :=
  ConfiguredRecursiveEdgeFiniteColumnGaugeMajorant.baseGaugeMajor D M j +
    depthwiseDirectGaugeDiagonal D MA NA E0 C0 C1 C2 M j

theorem depthwiseCombinedGaugeDiagonal_nonnegative
    (D : ConstructedConfiguredSequenceWeighted.Data)
    {MA NA E0 C0 C1 C2 M : ℝ}
    (hMA : 0 ≤ MA) (hNA : 0 ≤ NA) (hM : 0 ≤ M) (j : ℕ) :
    0 ≤ depthwiseCombinedGaugeDiagonal D MA NA E0 C0 C1 C2 M j :=
  add_nonneg
    (ConfiguredRecursiveEdgeFiniteColumnGaugeMajorant.baseGaugeMajor_nonnegative
      D M j)
    (depthwiseDirectGaugeDiagonal_nonnegative D hMA hNA hM j)

theorem depthwiseCombinedGaugeDiagonal_summable
    (D : ConstructedConfiguredSequenceWeighted.Data)
    {MA NA E0 C0 C1 C2 M : ℝ}
    (hMA : 0 ≤ MA) (hNA : 0 ≤ NA) (hM : 0 ≤ M) :
    Summable (depthwiseCombinedGaugeDiagonal D MA NA E0 C0 C1 C2 M) :=
  (ConfiguredRecursiveEdgeFiniteColumnGaugeMajorant.baseGaugeMajor_summable D M).add
    (depthwiseDirectGaugeDiagonal_summable D hMA hNA hM)

/-- A single tail choice simultaneously controls all spatial rows and all
recursive depths because each pair occurs at the diagonal index `n + k`. -/
structure DepthwiseGaugeOutput
    (D : ConstructedConfiguredSequenceWeighted.Data)
    (MA NA E0 C0 C1 C2 M Etotal : ℝ) where
  N : ℕ
  major_nonnegative : ∀ j, 0 ≤
    depthwiseCombinedGaugeDiagonal D MA NA E0 C0 C1 C2 M (N + j)
  major_summable : Summable (fun j ↦
    depthwiseCombinedGaugeDiagonal D MA NA E0 C0 C1 C2 M (N + j))
  major_half : ∀ j,
    depthwiseCombinedGaugeDiagonal D MA NA E0 C0 C1 C2 M (N + j) ≤ 1 / 2
  major_tsum_le : (∑' j,
    depthwiseCombinedGaugeDiagonal D MA NA E0 C0 C1 C2 M (N + j)) ≤ Etotal

namespace DepthwiseGaugeOutput

variable {D : ConstructedConfiguredSequenceWeighted.Data}
  {MA NA E0 C0 C1 C2 M Etotal : ℝ}

def major (O : DepthwiseGaugeOutput D MA NA E0 C0 C1 C2 M Etotal) :
    ℕ → ℝ := fun j ↦
  depthwiseCombinedGaugeDiagonal D MA NA E0 C0 C1 C2 M (O.N + j)

theorem major_nonnegative'
    (O : DepthwiseGaugeOutput D MA NA E0 C0 C1 C2 M Etotal) :
    ∀ j, 0 ≤ O.major j := O.major_nonnegative

theorem major_summable'
    (O : DepthwiseGaugeOutput D MA NA E0 C0 C1 C2 M Etotal) :
    Summable O.major := O.major_summable

theorem major_half'
    (O : DepthwiseGaugeOutput D MA NA E0 C0 C1 C2 M Etotal) :
    ∀ j, O.major j ≤ 1 / 2 := O.major_half

theorem major_tsum_le'
    (O : DepthwiseGaugeOutput D MA NA E0 C0 C1 C2 M Etotal) :
    (∑' j, O.major j) ≤ Etotal := O.major_tsum_le

/-- The common diagonal majorant as seen from spatial row `n`. -/
def rowMajor
    (O : DepthwiseGaugeOutput D MA NA E0 C0 C1 C2 M Etotal)
    (n k : ℕ) : ℝ := O.major (n + k)

theorem rowMajor_nonnegative
    (O : DepthwiseGaugeOutput D MA NA E0 C0 C1 C2 M Etotal) (n k : ℕ) :
    0 ≤ O.rowMajor n k := O.major_nonnegative' (n + k)

theorem rowMajor_half
    (O : DepthwiseGaugeOutput D MA NA E0 C0 C1 C2 M Etotal) (n k : ℕ) :
    O.rowMajor n k ≤ 1 / 2 := O.major_half' (n + k)

theorem rowMajor_summable
    (O : DepthwiseGaugeOutput D MA NA E0 C0 C1 C2 M Etotal) (n : ℕ) :
    Summable (O.rowMajor n) := by
  exact O.major_summable'.comp_injective (by
    intro a b hab
    exact Nat.add_left_cancel hab)

theorem rowMajor_tsum_le
    (O : DepthwiseGaugeOutput D MA NA E0 C0 C1 C2 M Etotal) (n : ℕ) :
    (∑' k, O.rowMajor n k) ≤ Etotal := by
  calc
    (∑' k, O.rowMajor n k) = ShadowingTails.tail O.major n := by
      rfl
    _ ≤ ShadowingTails.tail O.major 0 :=
      ShadowingTails.tail_antitone O.major_summable' O.major_nonnegative'
        (Nat.zero_le n)
    _ = ∑' j, O.major j := by
      simp [ShadowingTails.tail]
    _ ≤ Etotal := O.major_tsum_le'

/-- Every row receives a genuine distortion budget from the one selected
scalar tail.  Concrete gauge errors need only be pointwise dominated by the
corresponding diagonal entries. -/
def rowBudgetOfMajorant
    (O : DepthwiseGaugeOutput D MA NA E0 C0 C1 C2 M Etotal) (n : ℕ)
    {eps : ℕ → ℝ} (heps : ∀ k, 0 ≤ eps k)
    (hle : ∀ k, eps k ≤ O.rowMajor n k) :
    DistortionBudget
      (NearIdentityDistortionBudget.invLower eps)
      (NearIdentityDistortionBudget.upper eps) eps
      (2 * Etotal) Etotal Etotal :=
  NearIdentityDistortionBudgetMajorant.budgetOfMajorant
    heps (O.rowMajor_half n) (O.rowMajor_summable n)
      (O.rowMajor_tsum_le n) hle

end DepthwiseGaugeOutput

theorem exists_depthwiseGaugeOutput
    (D : ConstructedConfiguredSequenceWeighted.Data)
    {MA NA E0 C0 C1 C2 M Etotal : ℝ}
    (hMA : 0 ≤ MA) (hNA : 0 ≤ NA) (hM : 0 ≤ M)
    (hEtotal : 0 < Etotal) :
    Nonempty (DepthwiseGaugeOutput D MA NA E0 C0 C1 C2 M Etotal) := by
  let f := depthwiseCombinedGaugeDiagonal D MA NA E0 C0 C1 C2 M
  have hf0 : ∀ j, 0 ≤ f j :=
    depthwiseCombinedGaugeDiagonal_nonnegative D hMA hNA hM
  have hfs : Summable f :=
    depthwiseCombinedGaugeDiagonal_summable D hMA hNA hM
  have hevent : ∀ᶠ N in atTop,
      ShadowingTails.tail f N < min Etotal (1 / 2) :=
    ShadowingTails.tail_tendsto_zero.eventually
      (Iio_mem_nhds (lt_min hEtotal (by norm_num)))
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hevent
  have htail : ShadowingTails.tail f N ≤ min Etotal (1 / 2) :=
    (hN N le_rfl).le
  have hsummable : Summable (fun j ↦ f (N + j)) :=
    hfs.comp_injective (by
      intro a b hab
      exact Nat.add_left_cancel hab)
  refine ⟨{
    N := N
    major_nonnegative := fun j ↦ hf0 (N + j)
    major_summable := hsummable
    major_half := ?_
    major_tsum_le := ?_ }⟩
  · intro j
    calc
      f (N + j) ≤ ShadowingTails.tail f (N + j) :=
        ShadowingTails.le_tail hfs hf0 (N + j)
      _ ≤ ShadowingTails.tail f N :=
        ShadowingTails.tail_antitone hfs hf0 (Nat.le_add_right N j)
      _ ≤ min Etotal (1 / 2) := htail
      _ ≤ 1 / 2 := min_le_right _ _
  · change (∑' j, f (N + j)) ≤ Etotal
    calc
      (∑' j, f (N + j)) = ShadowingTails.tail f N := rfl
      _ ≤ min Etotal (1 / 2) := htail
      _ ≤ Etotal := min_le_left _ _

theorem model_ratio_le_two_thirds
    {H r : ℝ} (hH : 1 ≤ H) (hr0 : 0 ≤ r) (hr : r ≤ 1 / 10) :
    (((2 * H) ^ 2 * (1 / 2) + r) / (2 * H - r) ^ 2) ≤ 2 / 3 := by
  have hden : 0 < 2 * H - r := by linarith
  rw [div_le_iff₀ (sq_pos_of_pos hden)]
  nlinarith [sq_nonneg (H - 1),
    mul_nonneg (sub_nonneg.mpr hH) (sub_nonneg.mpr hr)]

structure ClosingOutput
    (J : ConfiguredRecursiveEdgeSourceP0RowJetTail.RowJetScalarOutput MA NA)
    (G : ConfiguredRecursiveEdgeFiniteColumnGaugeMajorant.Output
      J E0 (configuredSourceMassTarget E0 C0 C1 C2)) (E0 C0 C1 C2 : ℝ) where
  preShift : ℕ
  large : ExponentialDiagonalLargeSeparation.Output
    (shift G.data preShift) (fun _ ↦ 1)
    (shiftSequence
      (directDiagonal G.data MA NA E0 C0 C1 C2 J.scalar.Mend) preShift)
    J.scalar.Cw
  component_small : ∀ j,
    (4 * configuredTarget E0 C0 C1 C2) * edgePhysicalDefect G.data
      (preShift + large.N + j) <
        ReachableVariableSpeedFrontCurvature.sourceCurvatureCostBudget
  radius_small : ∀ n,
    rowRadius (shiftSequence (fun _ ↦ 1) large.N)
      (shiftSequence (shiftSequence
        (directDiagonal G.data MA NA E0 C0 C1 C2 J.scalar.Mend)
        preShift) large.N) n < 1 / 10

namespace ClosingOutput

variable {J : ConfiguredRecursiveEdgeSourceP0RowJetTail.RowJetScalarOutput MA NA}
  {G : ConfiguredRecursiveEdgeFiniteColumnGaugeMajorant.Output J E0
    (configuredSourceMassTarget E0 C0 C1 C2)}

def data (O : ClosingOutput J G E0 C0 C1 C2) :
    ConstructedConfiguredSequenceWeighted.Data :=
  shift (shift G.data O.preShift) O.large.N

def defect (O : ClosingOutput J G E0 C0 C1 C2) : ℕ → ℝ :=
  shiftSequence (shiftSequence
    (directDiagonal G.data MA NA E0 C0 C1 C2 J.scalar.Mend)
    O.preShift) O.large.N

def radius (O : ClosingOutput J G E0 C0 C1 C2) (n : ℕ) : ℝ :=
  rowRadius (shiftSequence (fun _ ↦ 1) O.large.N) O.defect n

theorem radius_eq_pullback (O : ClosingOutput J G E0 C0 C1 C2) (n : ℕ) :
    O.radius n = PullbackTubeTailBudget.radius 1 1 O.defect n := by
  change 1 * ShadowingTails.tail (fun k ↦ O.defect (n + k)) 0 =
    ShadowingTails.tail (fun k ↦ 1 * (1 ^ k * O.defect (n + k))) 0
  simp

theorem radius_nonnegative (O : ClosingOutput J G E0 C0 C1 C2)
    (hMA : 0 ≤ MA) (hNA : 0 ≤ NA) (n : ℕ) : 0 ≤ O.radius n := by
  unfold radius rowRadius rowError
  apply mul_nonneg
  · simp [shiftSequence]
  · apply ShadowingTails.tail_nonneg
    intro k
    exact directDiagonal_nonnegative G.data hMA hNA
      J.scalar.Mend_positive.le _

theorem separation_one (O : ClosingOutput J G E0 C0 C1 C2) :
    1 ≤ O.data.Hs 0 := by
  simpa [data, Nat.add_assoc] using O.large.separation_one

theorem initial_curvature_scalar
    (O : ClosingOutput J G E0 C0 C1 C2)
    (hMA : 0 ≤ MA) (hNA : 0 ≤ NA) (n : ℕ) :
    (((2 * O.data.Hs n) ^ 2 * (1 / 2) + O.radius n) /
        (2 * O.data.Hs n - O.radius n) ^ 2) ≤ 2 / 3 := by
  apply model_ratio_le_two_thirds
  · exact O.separation_one.trans (O.data.separation_lower n)
  · exact O.radius_nonnegative hMA hNA n
  · exact (O.radius_small n).le

theorem speed_tail (O : ClosingOutput J G E0 C0 C1 C2) (n : ℕ) :
    O.radius n ≤ O.data.Hs 0 := by
  simpa [radius, defect, data, PullbackTubeTailBudget.radius,
    ShadowingTails.tail, rowRadius, rowError, shiftSequence, Nat.add_assoc]
    using O.large.speed_tail n

theorem chord_tail (O : ClosingOutput J G E0 C0 C1 C2) (n : ℕ) :
    2 * O.radius n ≤
      (ConfiguredInductiveTubeBudget.chordBase O.data.model / 2) *
        ConstructedRowDefectLargeSeparation.rowRhoVariable
          O.data.model O.radius n := by
  simpa [radius, defect, data, PullbackTubeTailBudget.radius,
    ShadowingTails.tail, rowRadius, rowError, shiftSequence, Nat.add_assoc]
    using O.large.chord_tail n

theorem width_gap (O : ClosingOutput J G E0 C0 C1 C2) :
    J.scalar.Cw + 2 * O.radius 0 <
      (2 * O.data.Hs 0 - O.radius 0) / Real.pi := by
  simpa [radius, defect, data, PullbackTubeTailBudget.radius,
    ShadowingTails.tail, rowRadius, rowError, shiftSequence, Nat.add_assoc]
    using O.large.width_gap

end ClosingOutput

theorem exists_closingOutput
    (J : ConfiguredRecursiveEdgeSourceP0RowJetTail.RowJetScalarOutput MA NA)
    (G : ConfiguredRecursiveEdgeFiniteColumnGaugeMajorant.Output J E0
      (configuredSourceMassTarget E0 C0 C1 C2))
    (hMA : 0 ≤ MA) (hNA : 0 ≤ NA) (hE0 : 0 < E0) :
    Nonempty (ClosingOutput J G E0 C0 C1 C2) := by
  let D := G.data
  let C := directConversion D MA NA E0 C0 C1 C2 J.scalar.Mend
  let d := edgePhysicalDefect D
  let w := directDiagonal D MA NA E0 C0 C1 C2 J.scalar.Mend
  have hC0 : ∀ j, 0 ≤ C j := fun j ↦ mul_nonneg
    (directScale_nonnegative E0 C0 C1 C2)
    (edgeCombinedConversion_nonnegative D sourceKh_nonnegative sourceKh_lt_one j)
  have hd0 : ∀ j, 0 ≤ d j := edgePhysicalDefect_nonnegative D
  have hw0 : ∀ j, 0 ≤ w j := directDiagonal_nonnegative D hMA hNA
    J.scalar.Mend_positive.le
  have hbeta : 0 < D.model.beta := (D.model.configs 0).hbeta0
  let gamma : ℝ := D.model.beta / 16
  let b : ℝ := D.model.beta / 8
  have hgamma0 : 0 < gamma := div_pos hbeta (by norm_num)
  have hb0 : 0 < b := div_pos hbeta (by norm_num)
  have hgb : gamma < b := by dsimp [gamma, b]; linarith
  obtain ⟨Cc, hCc0, hCgrowth0⟩ :=
    exists_edgeCombinedConversion_growth_majorant D hMA hNA
      (analyticKhat_nonnegative D) sourceKh_nonnegative sourceKh_lt_one
      J.scalar.Mend_positive.le hgamma0
  let Cs := directScale E0 C0 C1 C2 * Cc
  have hCs0 : 0 ≤ Cs := mul_nonneg (directScale_nonnegative _ _ _ _) hCc0
  have hCgrowth : ∀ j, C j ≤ Cs * (1 + D.Hs j) ^ 2 *
      Real.exp (gamma * D.Hs j) := by
    intro j
    calc
      C j = directScale E0 C0 C1 C2 *
          edgeCombinedConversion D MA NA (analyticKhat D) sourceKh
            J.scalar.Mend j := rfl
      _ ≤ directScale E0 C0 C1 C2 *
          (Cc * (1 + D.Hs j) ^ 2 * Real.exp (gamma * D.Hs j)) :=
        mul_le_mul_of_nonneg_left (hCgrowth0 j)
          (directScale_nonnegative E0 C0 C1 C2)
      _ = Cs * (1 + D.Hs j) ^ 2 * Real.exp (gamma * D.Hs j) := by
        dsimp [Cs]
        ring
  obtain ⟨A, hA0, hdexp0⟩ := exists_edgePhysicalDefect_exp_bound D
  have hdexp : ∀ j, d j ≤ A * Real.exp (-(b * D.Hs j)) := by
    intro j
    simpa [d, b] using hdexp0 j
  have hws : Summable w := summable_weightedSequence_of_growth D C d
    hCs0 hA0 hb0 hgb hC0 hCgrowth hd0 hdexp
  let component : ℕ → ℝ := fun j ↦
    (4 * configuredTarget E0 C0 C1 C2) * d j
  have hcomponent0 : ∀ j, 0 ≤ component j := fun j ↦
    mul_nonneg
      (mul_nonneg (by norm_num) (configuredTarget_nonnegative _ _ _ _))
      (hd0 j)
  have hds : Summable d := by
    have H := summable_polynomial_mul_rowDefect D (physicalCoeffEnvelope D)
    simpa [d, edgePhysicalDefect, physicalDefect, mul_assoc] using H
  have hcomponents : Summable component := hds.mul_left _
  have hevComp := hcomponents.tendsto_atTop_zero.eventually
    (Iio_mem_nhds ReachableVariableSpeedFrontCurvature.sourceCurvatureCostBudget_pos)
  obtain ⟨Nc, hNc⟩ := Filter.eventually_atTop.1 hevComp
  obtain ⟨Nr, hNr⟩ := exists_shift_weightedRadius_lt hws hw0
    (by norm_num : (0 : ℝ) < 1 / 10)
  let N := max Nc Nr
  have hcompN : ∀ j, component (N + j) <
      ReachableVariableSpeedFrontCurvature.sourceCurvatureCostBudget := by
    intro j
    exact hNc (N + j)
      ((Nat.le_max_left Nc Nr).trans (Nat.le_add_right N j))
  have hradN : ∀ n, weightedRadius C d N n < 1 / 10 := by
    intro n
    have H := hNr (N - Nr + n)
    have heq : Nr + (N - Nr + n) = N + n := by omega
    simpa [weightedRadius_eq_tail, heq] using H
  obtain ⟨beta, K, hbetaW, hK, hwexp⟩ :=
    exists_weightedSequence_exp_bound_of_growth D C d hCs0 hA0 hb0 hgb
      hC0 hCgrowth hd0 hdexp
  let Dp := shift D N
  let wp := shiftSequence w N
  let gammaW := beta / 2
  have hgammaW : gammaW < beta := by dsimp [gammaW]; linarith
  obtain ⟨L⟩ := ExponentialDiagonalLargeSeparation.exists_output Dp
    (fun _ ↦ 1) wp (fun _ ↦ zero_le_one) zero_le_one hK hbetaW hgammaW
    (by
      intro n
      have hH := (Dp.model.separation_pos n).le
      have hg0 : 0 ≤ gammaW := (half_pos hbetaW).le
      have hsq : 1 ≤ (1 + Dp.Hs n) ^ 2 := by nlinarith [sq_nonneg (Dp.Hs n)]
      have hexp : 1 ≤ Real.exp (gammaW * Dp.Hs n) := by
        rw [← Real.exp_zero]
        exact Real.exp_le_exp.mpr (mul_nonneg hg0 hH)
      simpa using mul_le_mul hsq hexp zero_le_one (sq_nonneg (1 + Dp.Hs n)))
    (fun n ↦ hw0 (N + n))
    (by intro n; simpa [wp, Dp, shiftSequence] using hwexp (N + n))
    J.scalar.Cw_nonnegative
  refine ⟨{
    preShift := N
    large := L
    component_small := ?_
    radius_small := ?_ }⟩
  · intro j
    simpa [component, d, N, Nat.add_assoc] using hcompN (L.N + j)
  · intro n
    have H := hradN (L.N + n)
    simpa [rowRadius, rowError, directDiagonal, weightedRadius, weightedError,
      weightedSequence, C, d, wp, shiftSequence, ShadowingTails.tail,
      Nat.add_assoc] using H

end ConfiguredRecursiveEdgeFiniteColumnScalarClosing
