import UnitTangentIterates.ConfiguredRecursiveEdgeSourceP0
import UnitTangentIterates.ConfiguredRecursiveSourceP0Growth

/-!
# Polynomial growth at the successor-edge floor

The edge source in row `n` is the source on the configured output indexed by
`n + 1`.  Accordingly all upper ceilings are evaluated at `n + 1`, while the
speed floor is the minimum of the two adjacent recursive floors.  The model
configuration itself retains `H_{n+1} - 2 B <= H_n`; this supplies the missing
upper control needed to reindex polynomial envelopes.
-/

noncomputable section

namespace ConfiguredRecursiveEdgeSourceP0Growth

open ConfiguredCombinedPhysicalDiagonalLargeSeparation
  ConfiguredMarkingAwareMergedEndpointGrowth
  ConfiguredPhysicalDiagonalRowBudget
  ConfiguredPolynomialDiagonalStableRowDefectProvider
  ConfiguredRecursiveEdgeSourceP0
  ConfiguredRecursiveSourceP0
  ConfiguredRecursiveSourceP0Growth
  ConfiguredRowCeilingPolynomialEnvelopes
  ConstructedRowCPolynomialGrowth
  ConstructedRowCPolynomialGrowthVariableP0
  NormalPathC2IncrementVariableSpeed

def edgeGrowthFactor
    (D : ConstructedConfiguredSequenceWeighted.Data) : ℝ :=
  1 + 2 * max D.model.Bcell 0

theorem edgeGrowthFactor_one_le
    (D : ConstructedConfiguredSequenceWeighted.Data) :
    1 ≤ edgeGrowthFactor D := by
  unfold edgeGrowthFactor
  exact le_add_of_nonneg_right (mul_nonneg (by norm_num) (le_max_right _ _))

theorem one_add_next_le
    (D : ConstructedConfiguredSequenceWeighted.Data) (n : ℕ) :
    1 + D.Hs (n + 1) ≤ edgeGrowthFactor D * (1 + D.Hs n) := by
  have hPH := (D.model.configs n).hPH
  have hB : D.model.Bcell ≤ max D.model.Bcell 0 := le_max_left _ _
  have hH : 0 ≤ D.Hs n := (D.model.separation_pos n).le
  have hB0 : 0 ≤ max D.model.Bcell 0 := le_max_right _ _
  unfold edgeGrowthFactor
  nlinarith [mul_nonneg hB0 hH]

/-- Reindex any polynomial envelope from row `n` to the successor edge
`n + 1`, using the period comparison stored in the configured model. -/
def nextEnvelope
    (D : ConstructedConfiguredSequenceWeighted.Data) {f : ℕ → ℝ}
    (E : PolynomialEnvelope D.Hs f) :
    PolynomialEnvelope D.Hs (fun n ↦ f (n + 1)) where
  coeff := E.coeff * edgeGrowthFactor D ^ E.degree
  degree := E.degree
  coeff_nonneg := mul_nonneg E.coeff_nonneg
    (pow_nonneg (edgeGrowthFactor_one_le D |>.trans' zero_le_one) _)
  value_nonneg n := E.value_nonneg (n + 1)
  bound n := by
    have hnext0 : 0 ≤ 1 + D.Hs (n + 1) := by
      linarith [(D.model.separation_pos (n + 1)).le]
    have hpow := pow_le_pow_left₀ hnext0 (one_add_next_le D n) E.degree
    calc
      f (n + 1) ≤ E.coeff * (1 + D.Hs (n + 1)) ^ E.degree :=
        E.bound (n + 1)
      _ ≤ E.coeff * (edgeGrowthFactor D * (1 + D.Hs n)) ^ E.degree :=
        mul_le_mul_of_nonneg_left hpow E.coeff_nonneg
      _ = (E.coeff * edgeGrowthFactor D ^ E.degree) *
          (1 + D.Hs n) ^ E.degree := by rw [mul_pow]; ring

/-- One envelope simultaneously certifying a shifted base stage and the
successor-edge source attached to its next stage. -/
def currentNextEnvelope
    (D : ConstructedConfiguredSequenceWeighted.Data) {f : ℕ → ℝ}
    (E : PolynomialEnvelope D.Hs f) :
    PolynomialEnvelope D.Hs (fun n ↦ max (f n) (f (n + 1))) where
  coeff := E.coeff * (1 + edgeGrowthFactor D ^ E.degree)
  degree := E.degree
  coeff_nonneg := mul_nonneg E.coeff_nonneg
    (add_nonneg zero_le_one (pow_nonneg
      (edgeGrowthFactor_one_le D |>.trans' zero_le_one) _))
  value_nonneg n := le_max_of_le_left (E.value_nonneg n)
  bound n := by
    have hcur := E.bound n
    have hnxt := (nextEnvelope D E).bound n
    have hsum : max (f n) (f (n + 1)) ≤ f n + f (n + 1) := by
      apply max_le
      · exact le_add_of_nonneg_right (E.value_nonneg (n + 1))
      · exact le_add_of_nonneg_left (E.value_nonneg n)
    calc
      max (f n) (f (n + 1)) ≤ f n + f (n + 1) := hsum
      _ ≤ E.coeff * (1 + D.Hs n) ^ E.degree +
          (E.coeff * edgeGrowthFactor D ^ E.degree) *
            (1 + D.Hs n) ^ E.degree := add_le_add hcur hnxt
      _ = (E.coeff * (1 + edgeGrowthFactor D ^ E.degree)) *
          (1 + D.Hs n) ^ E.degree := by ring

def inverseEdgeSourceP0Envelope
    (D : ConstructedConfiguredSequenceWeighted.Data) :
    PolynomialEnvelope D.Hs (fun n ↦ 1 / edgeSourceP0 D n) where
  coeff := sourceDenomCoeff D *
    (1 + edgeGrowthFactor D ^ 2)
  degree := 2
  coeff_nonneg := mul_nonneg (sourceDenomCoeff_nonnegative D)
    (add_nonneg zero_le_one (sq_nonneg _))
  value_nonneg n := (one_div_pos.mpr (edgeSourceP0_pos D n)).le
  bound n := by
    have hcur := (inverseSourceP0Envelope D).bound n
    have hnxt := (nextEnvelope D (inverseSourceP0Envelope D)).bound n
    have hsum : 1 / edgeSourceP0 D n ≤
        1 / sourceP0 D n + 1 / sourceP0 D (n + 1) := by
      by_cases h : sourceP0 D n ≤ sourceP0 D (n + 1)
      · rw [edgeSourceP0, min_eq_left h]
        exact le_add_of_nonneg_right
          (one_div_pos.mpr (sourceP0_pos D (n + 1))).le
      · rw [edgeSourceP0, min_eq_right (le_of_not_ge h)]
        exact le_add_of_nonneg_left
          (one_div_pos.mpr (sourceP0_pos D n)).le
    calc
      1 / edgeSourceP0 D n ≤
          1 / sourceP0 D n + 1 / sourceP0 D (n + 1) := hsum
      _ ≤ sourceDenomCoeff D * (1 + D.Hs n) ^ 2 +
          (sourceDenomCoeff D * edgeGrowthFactor D ^ 2) *
            (1 + D.Hs n) ^ 2 := add_le_add hcur hnxt
      _ = (sourceDenomCoeff D * (1 + edgeGrowthFactor D ^ 2)) *
          (1 + D.Hs n) ^ 2 := by ring

/-- Flow-jet ceilings for a source density whose total mass has first been
forced below one by the common scalar tail. -/
def edgeFlowP1AtOne
    (D : ConstructedConfiguredSequenceWeighted.Data) (n : ℕ) : ℝ :=
  GaugeFlowDerivCost.costP1 (edgeSpeedCap D n) (analyticKhat D) 1

def edgeFlowG1AtOne
    (D : ConstructedConfiguredSequenceWeighted.Data) (n : ℕ) : ℝ :=
  GaugeFlowDerivCost.costG1 (edgeSpeedCap D n) (analyticKhat D)
    (GaugeMarkedDataOfRearFamily.rearKappa2 sourceKh) 1

/-- The edge first-flow ceiling includes both adjacent interpolation rows and
the actual mass-one source flow. -/
def edgeP1 (D : ConstructedConfiguredSequenceWeighted.Data)
    (MA : ℝ) : ℕ → ℝ :=
  fun n ↦ max (max (wideP1 D MA n) (wideP1 D MA (n + 1)))
    (edgeFlowP1AtOne D n)

/-- The edge second-flow ceiling includes both adjacent interpolation rows
and the actual mass-one source flow. -/
def edgeG1 (D : ConstructedConfiguredSequenceWeighted.Data)
    (MA NA : ℝ) : ℕ → ℝ :=
  fun n ↦ max (max (wideG1 D MA NA n) (wideG1 D MA NA (n + 1)))
    (edgeFlowG1AtOne D n)

/-- The source-density multiplier needed by the two chain-rule estimates for
the composed rear normal.  The Jacobi derivative coefficient is enlarged to
the already configured intrinsic source constant. -/
def edgeCompositionCoeff
    (D : ConstructedConfiguredSequenceWeighted.Data) (n : ℕ) : ℝ :=
  max 1 (max (2 * edgeFlowP1AtOne D n)
    ((FiniteSmoothRearFamilyMarkingAwareSmoothSource.intrinsicSourceConst sourceKh
          (FiniteSmoothRearFamilyMarkingAwareSmoothSource.intrinsicDerivativeConst sourceKh) + 2) *
        edgeFlowP1AtOne D n ^ 2 + 2 * edgeFlowG1AtOne D n))

theorem edgeCompositionCoeff_one_le
    (D : ConstructedConfiguredSequenceWeighted.Data) (n : ℕ) :
    1 ≤ edgeCompositionCoeff D n :=
  le_max_left _ _

theorem edgeCompositionCoeff_first
    (D : ConstructedConfiguredSequenceWeighted.Data) (n : ℕ) :
    2 * edgeFlowP1AtOne D n ≤ edgeCompositionCoeff D n :=
  (le_max_left _ _).trans (le_max_right _ _)

theorem edgeCompositionCoeff_second
    (D : ConstructedConfiguredSequenceWeighted.Data) (n : ℕ) :
    (FiniteSmoothRearFamilyMarkingAwareSmoothSource.intrinsicSourceConst sourceKh
        (FiniteSmoothRearFamilyMarkingAwareSmoothSource.intrinsicDerivativeConst sourceKh) + 2) *
          edgeFlowP1AtOne D n ^ 2 + 2 * edgeFlowG1AtOne D n ≤
      edgeCompositionCoeff D n :=
  (le_max_right _ _).trans (le_max_right _ _)

private def edgeFlowLinearCoeff
    (D : ConstructedConfiguredSequenceWeighted.Data) : ℝ :=
  3 * edgeGrowthFactor D * Real.exp (analyticKhat D)

private theorem edgeFlowLinearCoeff_nonnegative
    (D : ConstructedConfiguredSequenceWeighted.Data) :
    0 ≤ edgeFlowLinearCoeff D := by
  unfold edgeFlowLinearCoeff
  exact mul_nonneg
    (mul_nonneg (by norm_num) (zero_le_one.trans (edgeGrowthFactor_one_le D)))
    (Real.exp_pos _).le

private theorem edgeFlowP1AtOne_le
    (D : ConstructedConfiguredSequenceWeighted.Data) (n : ℕ) :
    edgeFlowP1AtOne D n ≤
      edgeFlowLinearCoeff D * (1 + D.Hs n) := by
  have he0 : 0 ≤ Real.exp (analyticKhat D) := (Real.exp_pos _).le
  unfold edgeFlowP1AtOne GaugeFlowDerivCost.costP1 edgeSpeedCap speedCap
    edgeFlowLinearCoeff
  have hn := one_add_next_le D n
  have h3 := mul_le_mul_of_nonneg_left hn (by norm_num : (0 : ℝ) ≤ 3)
  have he := mul_le_mul_of_nonneg_right h3 he0
  convert he using 1 <;> ring

private theorem edgeFlowP1AtOne_nonnegative
    (D : ConstructedConfiguredSequenceWeighted.Data) (n : ℕ) :
    0 ≤ edgeFlowP1AtOne D n := by
  unfold edgeFlowP1AtOne GaugeFlowDerivCost.costP1 edgeSpeedCap speedCap
  exact mul_nonneg
    (mul_nonneg (by norm_num)
      (add_nonneg zero_le_one (D.model.separation_pos (n + 1)).le))
    (Real.exp_pos _).le

private theorem edgeFlowG1AtOne_nonnegative
    (D : ConstructedConfiguredSequenceWeighted.Data) (n : ℕ) :
    0 ≤ edgeFlowG1AtOne D n := by
  unfold edgeFlowG1AtOne GaugeFlowDerivCost.costG1
  exact mul_nonneg (sq_nonneg _)
    (mul_nonneg
      (GaugeMarkedDataOfRearFamily.rearKappa2_nonneg
        sourceKh_nonnegative sourceKh_lt_one) zero_le_one)

/-- The composition multiplier has polynomial growth (degree two) in the
configured separation. -/
def edgeCompositionCoeffEnvelope
    (D : ConstructedConfiguredSequenceWeighted.Data) :
    PolynomialEnvelope D.Hs (edgeCompositionCoeff D) where
  coeff :=
    1 + 2 * edgeFlowLinearCoeff D +
      (FiniteSmoothRearFamilyMarkingAwareSmoothSource.intrinsicSourceConst sourceKh
          (FiniteSmoothRearFamilyMarkingAwareSmoothSource.intrinsicDerivativeConst sourceKh) + 2) *
        edgeFlowLinearCoeff D ^ 2 +
      2 * (edgeFlowLinearCoeff D ^ 2 *
        GaugeMarkedDataOfRearFamily.rearKappa2 sourceKh)
  degree := 2
  coeff_nonneg := by
    have hL := edgeFlowLinearCoeff_nonnegative D
    have hd := ConfiguredRecursiveSourceP0Growth.intrinsicSourceConst_nonnegative
    have hk2 := GaugeMarkedDataOfRearFamily.rearKappa2_nonneg
      sourceKh_nonnegative sourceKh_lt_one
    positivity
  value_nonneg n := by
    exact zero_le_one.trans (edgeCompositionCoeff_one_le D n)
  bound n := by
    let x : ℝ := 1 + D.Hs n
    let L : ℝ := edgeFlowLinearCoeff D
    let p : ℝ := edgeFlowP1AtOne D n
    let g : ℝ := edgeFlowG1AtOne D n
    let d : ℝ :=
      FiniteSmoothRearFamilyMarkingAwareSmoothSource.intrinsicSourceConst sourceKh
        (FiniteSmoothRearFamilyMarkingAwareSmoothSource.intrinsicDerivativeConst sourceKh)
    let k2 : ℝ := GaugeMarkedDataOfRearFamily.rearKappa2 sourceKh
    have hx : 1 ≤ x := by
      dsimp [x]
      linarith [(D.model.separation_pos n).le]
    have hL : 0 ≤ L := edgeFlowLinearCoeff_nonnegative D
    have hp0 : 0 ≤ p := edgeFlowP1AtOne_nonnegative D n
    have hg0 : 0 ≤ g := edgeFlowG1AtOne_nonnegative D n
    have hd0 : 0 ≤ d :=
      ConfiguredRecursiveSourceP0Growth.intrinsicSourceConst_nonnegative
    have hk20 : 0 ≤ k2 := GaugeMarkedDataOfRearFamily.rearKappa2_nonneg
      sourceKh_nonnegative sourceKh_lt_one
    have hp : p ≤ L * x := edgeFlowP1AtOne_le D n
    have hp2 : p ^ 2 ≤ (L * x) ^ 2 := by nlinarith
    have hg : g ≤ L ^ 2 * x ^ 2 * k2 := by
      have hg_eq : g = p ^ 2 * k2 := by
        dsimp [g, p, k2, edgeFlowG1AtOne, GaugeFlowDerivCost.costG1]
        unfold edgeFlowP1AtOne
        ring
      have h := mul_le_mul_of_nonneg_right hp2 hk20
      calc
        g = p ^ 2 * k2 := hg_eq
        _ ≤ (L * x) ^ 2 * k2 := h
        _ = L ^ 2 * x ^ 2 * k2 := by ring
    have hmax : edgeCompositionCoeff D n ≤
        1 + 2 * p + ((d + 2) * p ^ 2 + 2 * g) := by
      unfold edgeCompositionCoeff
      apply max_le
      · nlinarith
      · apply max_le
        · nlinarith
        · nlinarith [sq_nonneg p]
    dsimp [p, g, d, L, k2] at hmax ⊢
    calc
      edgeCompositionCoeff D n ≤
          1 + 2 * edgeFlowP1AtOne D n +
            ((FiniteSmoothRearFamilyMarkingAwareSmoothSource.intrinsicSourceConst sourceKh
                (FiniteSmoothRearFamilyMarkingAwareSmoothSource.intrinsicDerivativeConst sourceKh) + 2) *
              edgeFlowP1AtOne D n ^ 2 + 2 * edgeFlowG1AtOne D n) := hmax
      _ ≤ (1 + 2 * edgeFlowLinearCoeff D +
            (FiniteSmoothRearFamilyMarkingAwareSmoothSource.intrinsicSourceConst sourceKh
                (FiniteSmoothRearFamilyMarkingAwareSmoothSource.intrinsicDerivativeConst sourceKh) + 2) *
              edgeFlowLinearCoeff D ^ 2 +
            2 * (edgeFlowLinearCoeff D ^ 2 *
              GaugeMarkedDataOfRearFamily.rearKappa2 sourceKh)) *
            (1 + D.Hs n) ^ 2 := by
        dsimp [x, L, p, g, d, k2] at hx hL hp0 hg0 hd0 hk20 hp hp2 hg ⊢
        nlinarith

/-- The diagonal coefficient that simultaneously retains the old physical
component budget and three copies of the scaled audited source density. -/
def edgeCompositionPhysicalCoeff
    (D : ConstructedConfiguredSequenceWeighted.Data) (n : ℕ) : ℝ :=
  physicalCoeff D n + 3 * edgeCompositionCoeff D n

def edgeCompositionPhysicalCoeffEnvelope
    (D : ConstructedConfiguredSequenceWeighted.Data) :
    PolynomialEnvelope D.Hs (edgeCompositionPhysicalCoeff D) where
  coeff := 2 + 3 * (edgeCompositionCoeffEnvelope D).coeff
  degree := 2
  coeff_nonneg := add_nonneg (by norm_num)
    (mul_nonneg (by norm_num) (edgeCompositionCoeffEnvelope D).coeff_nonneg)
  value_nonneg n := add_nonneg
    ((physicalCoeffEnvelope D).value_nonneg n)
    (mul_nonneg (by norm_num) ((edgeCompositionCoeffEnvelope D).value_nonneg n))
  bound n := by
    have hx : 1 ≤ 1 + D.Hs n := by
      linarith [(D.model.separation_pos n).le]
    have hp := (physicalCoeffEnvelope D).bound n
    have hc := (edgeCompositionCoeffEnvelope D).bound n
    unfold edgeCompositionPhysicalCoeff
    have hp2 : physicalCoeff D n ≤ 2 * (1 + D.Hs n) ^ 2 := by
      unfold physicalCoeff at hp ⊢
      nlinarith [sq_nonneg (D.Hs n)]
    calc
      physicalCoeff D n + 3 * edgeCompositionCoeff D n ≤
          2 * (1 + D.Hs n) ^ 2 +
            3 * ((edgeCompositionCoeffEnvelope D).coeff *
              (1 + D.Hs n) ^ 2) :=
        add_le_add hp2 (mul_le_mul_of_nonneg_left hc (by norm_num))
      _ = (2 + 3 * (edgeCompositionCoeffEnvelope D).coeff) *
          (1 + D.Hs n) ^ 2 := by ring

def edgeCompositionPhysicalCertificate
    (D : ConstructedConfiguredSequenceWeighted.Data) :
    ConfiguredDiagonalStableRowDefectProvider.Certificate D
      (edgeCompositionPhysicalCoeff D) :=
  ConfiguredPolynomialDiagonalStableRowDefectProvider.polynomialCertificate D
    (edgeCompositionPhysicalCoeffEnvelope D)

def edgeCompositionPhysicalDefect
    (D : ConstructedConfiguredSequenceWeighted.Data) (n : ℕ) : ℝ :=
  edgeCompositionPhysicalCoeff D n *
    ConfiguredApproximateDefectPathRowwise.rowDefect D n

theorem edgeCompositionPhysicalDefect_nonnegative
    (D : ConstructedConfiguredSequenceWeighted.Data) (n : ℕ) :
    0 ≤ edgeCompositionPhysicalDefect D n :=
  mul_nonneg ((edgeCompositionPhysicalCoeffEnvelope D).value_nonneg n)
    (ConfiguredRowDefectProvider.rowDefect_nonneg D n)

theorem summable_edgeCompositionPhysicalDefect
    (D : ConstructedConfiguredSequenceWeighted.Data) :
    Summable (edgeCompositionPhysicalDefect D) := by
  simpa [edgeCompositionPhysicalDefect] using
    ConfiguredPolynomialDiagonalStableRowDefectProvider.summable_polynomial_mul_rowDefect
      D (edgeCompositionPhysicalCoeffEnvelope D)

/-- A finite scalar prefix makes the scaled audited source mass fit the fixed
unit budget used in `edgeFlowP1AtOne` and `edgeFlowG1AtOne`. -/
theorem exists_edgeCompositionPhysicalDefect_tail_le_one
    (D : ConstructedConfiguredSequenceWeighted.Data) :
    ∃ N, ∀ j, N ≤ j → edgeCompositionPhysicalDefect D j ≤ 1 := by
  have ht := (summable_edgeCompositionPhysicalDefect D).tendsto_atTop_zero
  have he := ht.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 he
  exact ⟨N, fun j hj ↦ (hN j hj).le⟩

theorem edgeCompositionPhysicalDefect_shift
    (D : ConstructedConfiguredSequenceWeighted.Data) (N n : ℕ) :
    edgeCompositionPhysicalDefect
      (ConstructedConfiguredInductiveTubeBudget.WeightedData.shift D N) n =
      edgeCompositionPhysicalDefect D (N + n) := by
  have hrow : ConfiguredApproximateDefectPathRowwise.rowDefect
      (ConstructedConfiguredInductiveTubeBudget.WeightedData.shift D N) n =
      ConfiguredApproximateDefectPathRowwise.rowDefect D (N + n) := rfl
  have hcoeff : edgeCompositionPhysicalCoeff
      (ConstructedConfiguredInductiveTubeBudget.WeightedData.shift D N) n =
      edgeCompositionPhysicalCoeff D (N + n) := by
    simp [edgeCompositionPhysicalCoeff,
    edgeCompositionCoeff, edgeFlowP1AtOne, edgeFlowG1AtOne,
    edgeSpeedCap, speedCap, analyticKhat,
    GaugeFlowDerivCost.costP1, GaugeFlowDerivCost.costG1,
    ConfiguredPolynomialDiagonalStableRowDefectProvider.physicalCoeff,
    ConstructedConfiguredInductiveTubeBudget.WeightedData.shift, Nat.add_assoc]
  unfold edgeCompositionPhysicalDefect
  rw [hcoeff, hrow]

theorem edgeCompositionCoeff_shift
    (D : ConstructedConfiguredSequenceWeighted.Data) (N n : ℕ) :
    edgeCompositionCoeff
      (ConstructedConfiguredInductiveTubeBudget.WeightedData.shift D N) n =
      edgeCompositionCoeff D (N + n) := by
  simp [edgeCompositionCoeff, edgeFlowP1AtOne, edgeFlowG1AtOne,
    edgeSpeedCap, speedCap, analyticKhat, GaugeFlowDerivCost.costP1,
    GaugeFlowDerivCost.costG1,
    ConstructedConfiguredInductiveTubeBudget.WeightedData.shift, Nat.add_assoc]

/-- A degree-four polynomial majorant for the composition coefficient at any
earlier row multiplied by the physical composition coefficient at the current
row.  The fixed square-root denominator is harmless because `sourceKh < 1`. -/
def edgeCompositionScaledMassEnvelopeValue
    (D : ConstructedConfiguredSequenceWeighted.Data) (j : ℕ) : ℝ :=
  ((edgeCompositionCoeffEnvelope D).coeff *
      (edgeCompositionPhysicalCoeffEnvelope D).coeff /
      Real.sqrt (1 - sourceKh ^ 2)) * (1 + D.Hs j) ^ 4

def edgeCompositionScaledMassEnvelope
    (D : ConstructedConfiguredSequenceWeighted.Data) :
    PolynomialEnvelope D.Hs (edgeCompositionScaledMassEnvelopeValue D) where
  coeff := (edgeCompositionCoeffEnvelope D).coeff *
    (edgeCompositionPhysicalCoeffEnvelope D).coeff /
      Real.sqrt (1 - sourceKh ^ 2)
  degree := 4
  coeff_nonneg := by
    exact div_nonneg
      (mul_nonneg (edgeCompositionCoeffEnvelope D).coeff_nonneg
        (edgeCompositionPhysicalCoeffEnvelope D).coeff_nonneg)
      (Real.sqrt_nonneg _)
  value_nonneg j := by
    unfold edgeCompositionScaledMassEnvelopeValue
    exact mul_nonneg
      (div_nonneg
        (mul_nonneg (edgeCompositionCoeffEnvelope D).coeff_nonneg
          (edgeCompositionPhysicalCoeffEnvelope D).coeff_nonneg)
        (Real.sqrt_nonneg _))
      (pow_nonneg (by linarith [(D.model.separation_pos j).le]) _)
  bound j := le_rfl

/-- The degree-four envelope dominates every earlier composition multiplier
against the current physical composition defect. -/
theorem edgeComposition_scaled_mass_le_envelope
    (D : ConstructedConfiguredSequenceWeighted.Data) {n j : ℕ} (hnj : n ≤ j) :
    edgeCompositionCoeff D n / Real.sqrt (1 - sourceKh ^ 2) *
        edgeCompositionPhysicalDefect D j ≤
      edgeCompositionScaledMassEnvelopeValue D j *
        ConfiguredApproximateDefectPathRowwise.rowDefect D j := by
  have hroot : 0 < Real.sqrt (1 - sourceKh ^ 2) :=
    Real.sqrt_pos.2 (by nlinarith [sourceKh_nonnegative, sourceKh_lt_one])
  have hHs : Monotone D.Hs :=
    monotone_nat_of_le_succ fun r ↦
      (le_add_of_nonneg_right D.deltaStep_pos.le).trans (D.separation_step r)
  have hx0 : 0 ≤ 1 + D.Hs n := by
    linarith [(D.model.separation_pos n).le]
  have hxj0 : 0 ≤ 1 + D.Hs j := by
    linarith [(D.model.separation_pos j).le]
  have hx : 1 + D.Hs n ≤ 1 + D.Hs j := by
    linarith [hHs hnj]
  have hxpow : (1 + D.Hs n) ^ 2 ≤ (1 + D.Hs j) ^ 2 :=
    pow_le_pow_left₀ hx0 hx 2
  have hc0 : 0 ≤ edgeCompositionCoeff D n :=
    (edgeCompositionCoeffEnvelope D).value_nonneg n
  have hp0 : 0 ≤ edgeCompositionPhysicalCoeff D j :=
    (edgeCompositionPhysicalCoeffEnvelope D).value_nonneg j
  have hc : edgeCompositionCoeff D n ≤
      (edgeCompositionCoeffEnvelope D).coeff * (1 + D.Hs j) ^ 2 :=
    (edgeCompositionCoeffEnvelope D).bound n |>.trans
      (mul_le_mul_of_nonneg_left hxpow
        (edgeCompositionCoeffEnvelope D).coeff_nonneg)
  have hp := (edgeCompositionPhysicalCoeffEnvelope D).bound j
  have hcdiv : edgeCompositionCoeff D n / Real.sqrt (1 - sourceKh ^ 2) ≤
      ((edgeCompositionCoeffEnvelope D).coeff * (1 + D.Hs j) ^ 2) /
        Real.sqrt (1 - sourceKh ^ 2) :=
    div_le_div_of_nonneg_right hc hroot.le
  have hcoeff : edgeCompositionCoeff D n / Real.sqrt (1 - sourceKh ^ 2) *
      edgeCompositionPhysicalCoeff D j ≤
      edgeCompositionScaledMassEnvelopeValue D j := by
    calc
      edgeCompositionCoeff D n / Real.sqrt (1 - sourceKh ^ 2) *
          edgeCompositionPhysicalCoeff D j ≤
        (((edgeCompositionCoeffEnvelope D).coeff * (1 + D.Hs j) ^ 2) /
            Real.sqrt (1 - sourceKh ^ 2)) *
          ((edgeCompositionPhysicalCoeffEnvelope D).coeff *
            (1 + D.Hs j) ^ 2) :=
        mul_le_mul hcdiv hp hp0
          (div_nonneg
            (mul_nonneg (edgeCompositionCoeffEnvelope D).coeff_nonneg
              (pow_nonneg hxj0 2)) hroot.le)
      _ = edgeCompositionScaledMassEnvelopeValue D j := by
        unfold edgeCompositionScaledMassEnvelopeValue
        ring
  unfold edgeCompositionPhysicalDefect
  calc
    edgeCompositionCoeff D n / Real.sqrt (1 - sourceKh ^ 2) *
        (edgeCompositionPhysicalCoeff D j *
          ConfiguredApproximateDefectPathRowwise.rowDefect D j) =
      (edgeCompositionCoeff D n / Real.sqrt (1 - sourceKh ^ 2) *
        edgeCompositionPhysicalCoeff D j) *
          ConfiguredApproximateDefectPathRowwise.rowDefect D j := by ring
    _ ≤ edgeCompositionScaledMassEnvelopeValue D j *
        ConfiguredApproximateDefectPathRowwise.rowDefect D j :=
      mul_le_mul_of_nonneg_right hcoeff
        (ConfiguredRowDefectProvider.rowDefect_nonneg D j)

theorem summable_edgeCompositionScaledMassEnvelopeDefect
    (D : ConstructedConfiguredSequenceWeighted.Data) :
    Summable (fun j ↦ edgeCompositionScaledMassEnvelopeValue D j *
      ConfiguredApproximateDefectPathRowwise.rowDefect D j) :=
  ConfiguredPolynomialDiagonalStableRowDefectProvider.summable_polynomial_mul_rowDefect
    D (edgeCompositionScaledMassEnvelope D)

/-- After one finite prefix, every earlier-row composition multiplier fits
the unit mass budget against every later physical composition defect. -/
theorem exists_edgeComposition_scaled_mass_tail_le_one
    (D : ConstructedConfiguredSequenceWeighted.Data) :
    ∃ N, ∀ n j, N ≤ j → n ≤ j →
      edgeCompositionCoeff D n / Real.sqrt (1 - sourceKh ^ 2) *
        edgeCompositionPhysicalDefect D j ≤ 1 := by
  have ht := (summable_edgeCompositionScaledMassEnvelopeDefect D).tendsto_atTop_zero
  have he := ht.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 he
  refine ⟨N, fun n j hj hnj ↦ ?_⟩
  exact (edgeComposition_scaled_mass_le_envelope D hnj).trans (hN j hj).le

def edgeCgWithKhat (D : ConstructedConfiguredSequenceWeighted.Data)
    (khat MA NA : ℝ) : ℕ → ℝ :=
  fun n ↦ max
    (max (wideCgWithKhat D khat MA NA n)
      (wideCgWithKhat D khat MA NA (n + 1)))
    (khat * edgeFlowG1AtOne D n +
      GaugeMarkedDataOfRearFamily.rearKappa2 sourceKh *
        edgeFlowP1AtOne D n ^ 2)

theorem edgeFlowP1AtOne_le_compositionCoeff
    (D : ConstructedConfiguredSequenceWeighted.Data) (n : ℕ) :
    edgeFlowP1AtOne D n ≤ edgeCompositionCoeff D n := by
  have h := edgeCompositionCoeff_first D n
  have h0 := edgeFlowP1AtOne_nonnegative D n
  linarith

theorem edgeFlowG1AtOne_le_compositionCoeff
    (D : ConstructedConfiguredSequenceWeighted.Data) (n : ℕ) :
    edgeFlowG1AtOne D n ≤ edgeCompositionCoeff D n := by
  have h := edgeCompositionCoeff_second D n
  have hp := edgeFlowP1AtOne_nonnegative D n
  have hc : 0 ≤
      FiniteSmoothRearFamilyMarkingAwareSmoothSource.intrinsicSourceConst sourceKh
        (FiniteSmoothRearFamilyMarkingAwareSmoothSource.intrinsicDerivativeConst sourceKh) + 2 :=
    add_nonneg ConfiguredRecursiveSourceP0Growth.intrinsicSourceConst_nonnegative
      (by norm_num)
  have hterm : 0 ≤
      (FiniteSmoothRearFamilyMarkingAwareSmoothSource.intrinsicSourceConst sourceKh
          (FiniteSmoothRearFamilyMarkingAwareSmoothSource.intrinsicDerivativeConst sourceKh) + 2) *
        edgeFlowP1AtOne D n ^ 2 := mul_nonneg hc (sq_nonneg _)
  have hg0 := edgeFlowG1AtOne_nonnegative D n
  linarith

theorem edgeFlowP1AtOne_nonneg
    (D : ConstructedConfiguredSequenceWeighted.Data) (n : ℕ) :
    0 ≤ edgeFlowP1AtOne D n :=
  edgeFlowP1AtOne_nonnegative D n

theorem edgeFlowG1AtOne_nonneg
    (D : ConstructedConfiguredSequenceWeighted.Data) (n : ℕ) :
    0 ≤ edgeFlowG1AtOne D n :=
  edgeFlowG1AtOne_nonnegative D n

def edgeP1Envelope
    (D : ConstructedConfiguredSequenceWeighted.Data) {MA : ℝ}
    (hMA : 0 ≤ MA) : PolynomialEnvelope D.Hs (edgeP1 D MA) where
  coeff := (currentNextEnvelope D (wideP1Envelope D hMA)).coeff +
    (edgeCompositionCoeffEnvelope D).coeff
  degree := 2
  coeff_nonneg := add_nonneg
    (currentNextEnvelope D (wideP1Envelope D hMA)).coeff_nonneg
    (edgeCompositionCoeffEnvelope D).coeff_nonneg
  value_nonneg n := le_max_of_le_right (edgeFlowP1AtOne_nonnegative D n)
  bound n := by
    let x := 1 + D.Hs n
    have hx : 1 ≤ x := by dsimp [x]; linarith [(D.model.separation_pos n).le]
    have hx0 : 0 ≤ x := zero_le_one.trans hx
    have hx12 : x ≤ x ^ 2 := by nlinarith
    let E := currentNextEnvelope D (wideP1Envelope D hMA)
    let F := edgeCompositionCoeffEnvelope D
    have hE : max (wideP1 D MA n) (wideP1 D MA (n + 1)) ≤ E.coeff * x := by
      simpa [E, x, currentNextEnvelope, wideP1Envelope] using E.bound n
    have hF := F.bound n
    have hflow := edgeFlowP1AtOne_le_compositionCoeff D n
    apply max_le
    · calc
        max (wideP1 D MA n) (wideP1 D MA (n + 1)) ≤ E.coeff * x := hE
        _ ≤ E.coeff * x ^ 2 := mul_le_mul_of_nonneg_left hx12 E.coeff_nonneg
        _ ≤ (E.coeff + F.coeff) * x ^ 2 := by
          exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_right F.coeff_nonneg)
            (sq_nonneg x)
    · calc
        edgeFlowP1AtOne D n ≤ edgeCompositionCoeff D n := hflow
        _ ≤ F.coeff * x ^ 2 := hF
        _ ≤ (E.coeff + F.coeff) * x ^ 2 := by
          exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_left E.coeff_nonneg)
            (sq_nonneg x)

def edgeG1Envelope
    (D : ConstructedConfiguredSequenceWeighted.Data) {MA NA : ℝ}
    (hMA : 0 ≤ MA) (hNA : 0 ≤ NA) :
    PolynomialEnvelope D.Hs (edgeG1 D MA NA) where
  coeff := (currentNextEnvelope D (wideG1Envelope D hMA hNA)).coeff +
    (edgeCompositionCoeffEnvelope D).coeff
  degree := 2
  coeff_nonneg := add_nonneg
    (currentNextEnvelope D (wideG1Envelope D hMA hNA)).coeff_nonneg
    (edgeCompositionCoeffEnvelope D).coeff_nonneg
  value_nonneg n := le_max_of_le_right (edgeFlowG1AtOne_nonnegative D n)
  bound n := by
    let x := 1 + D.Hs n
    let E := currentNextEnvelope D (wideG1Envelope D hMA hNA)
    let F := edgeCompositionCoeffEnvelope D
    have hE := E.bound n
    have hF := F.bound n
    have hflow := edgeFlowG1AtOne_le_compositionCoeff D n
    apply max_le
    · exact hE.trans (mul_le_mul_of_nonneg_right
        (le_add_of_nonneg_right F.coeff_nonneg) (sq_nonneg x))
    · exact hflow.trans (hF.trans (mul_le_mul_of_nonneg_right
        (le_add_of_nonneg_left E.coeff_nonneg) (sq_nonneg x)))

def edgeCgWithKhatEnvelope
    (D : ConstructedConfiguredSequenceWeighted.Data)
    {khat MA NA : ℝ} (hkhat : 0 ≤ khat) (hMA : 0 ≤ MA) (hNA : 0 ≤ NA) :
    PolynomialEnvelope D.Hs (edgeCgWithKhat D khat MA NA) where
  coeff := (currentNextEnvelope D
      (wideCgWithKhatEnvelope D hkhat hMA hNA)).coeff +
    (khat + GaugeMarkedDataOfRearFamily.rearKappa2 sourceKh) *
      (edgeCompositionCoeffEnvelope D).coeff ^ 2
  degree := 4
  coeff_nonneg := add_nonneg
    (currentNextEnvelope D
      (wideCgWithKhatEnvelope D hkhat hMA hNA)).coeff_nonneg
    (mul_nonneg (add_nonneg hkhat
      (GaugeMarkedDataOfRearFamily.rearKappa2_nonneg
        sourceKh_nonnegative sourceKh_lt_one)) (sq_nonneg _))
  value_nonneg n := by
    apply le_max_of_le_right
    exact add_nonneg
      (mul_nonneg hkhat (edgeFlowG1AtOne_nonnegative D n))
      (mul_nonneg (GaugeMarkedDataOfRearFamily.rearKappa2_nonneg
        sourceKh_nonnegative sourceKh_lt_one) (sq_nonneg _))
  bound n := by
    let x := 1 + D.Hs n
    let E := currentNextEnvelope D
      (wideCgWithKhatEnvelope D hkhat hMA hNA)
    let F := edgeCompositionCoeffEnvelope D
    let k2 := GaugeMarkedDataOfRearFamily.rearKappa2 sourceKh
    have hx : 1 ≤ x := by dsimp [x]; linarith [(D.model.separation_pos n).le]
    have hx0 : 0 ≤ x := zero_le_one.trans hx
    have hx2 : 1 ≤ x ^ 2 := by nlinarith [sq_nonneg (x - 1)]
    have hx24 : x ^ 2 ≤ x ^ 4 := by
      calc
        x ^ 2 ≤ x ^ 2 * x ^ 2 :=
          by simpa using mul_le_mul_of_nonneg_left hx2 (sq_nonneg x)
        _ = x ^ 4 := by ring
    have hE := E.bound n
    have hF := F.bound n
    have hF0 := F.value_nonneg n
    have hp := edgeFlowP1AtOne_le_compositionCoeff D n
    have hg := edgeFlowG1AtOne_le_compositionCoeff D n
    have hc1 := edgeCompositionCoeff_one_le D n
    have hk2 : 0 ≤ k2 := GaugeMarkedDataOfRearFamily.rearKappa2_nonneg
      sourceKh_nonnegative sourceKh_lt_one
    have hmixed : khat * edgeFlowG1AtOne D n +
        k2 * edgeFlowP1AtOne D n ^ 2 ≤
        (khat + k2) * edgeCompositionCoeff D n ^ 2 := by
      have hc0 : 0 ≤ edgeCompositionCoeff D n := zero_le_one.trans hc1
      have hg0 := edgeFlowG1AtOne_nonnegative D n
      have hp0 := edgeFlowP1AtOne_nonnegative D n
      have hc_le_sq : edgeCompositionCoeff D n ≤
          edgeCompositionCoeff D n ^ 2 := by nlinarith
      have hg_sq : edgeFlowG1AtOne D n ≤
          edgeCompositionCoeff D n ^ 2 := hg.trans hc_le_sq
      have hp_sq : edgeFlowP1AtOne D n ^ 2 ≤
          edgeCompositionCoeff D n ^ 2 :=
        (sq_le_sq₀ hp0 hc0).2 hp
      calc
        khat * edgeFlowG1AtOne D n + k2 * edgeFlowP1AtOne D n ^ 2 ≤
            khat * edgeCompositionCoeff D n ^ 2 +
              k2 * edgeCompositionCoeff D n ^ 2 :=
          add_le_add (mul_le_mul_of_nonneg_left hg_sq hkhat)
            (mul_le_mul_of_nonneg_left hp_sq hk2)
        _ = (khat + k2) * edgeCompositionCoeff D n ^ 2 := by ring
    have hF' : edgeCompositionCoeff D n ≤ F.coeff * x ^ 2 := by
      simpa [F, x, edgeCompositionCoeffEnvelope] using hF
    have hFsquare : edgeCompositionCoeff D n ^ 2 ≤
        F.coeff ^ 2 * x ^ 4 := by
      have hright : 0 ≤ F.coeff * x ^ 2 :=
        mul_nonneg F.coeff_nonneg (sq_nonneg x)
      have := (sq_le_sq₀ hF0 hright).2 hF'
      nlinarith
    apply max_le
    · calc
        max (wideCgWithKhat D khat MA NA n)
            (wideCgWithKhat D khat MA NA (n + 1)) ≤ E.coeff * x ^ 2 := hE
        _ ≤ E.coeff * x ^ 4 := mul_le_mul_of_nonneg_left hx24 E.coeff_nonneg
        _ ≤ (E.coeff + (khat + k2) * F.coeff ^ 2) * x ^ 4 := by
          exact mul_le_mul_of_nonneg_right
            (le_add_of_nonneg_right (mul_nonneg (add_nonneg hkhat hk2)
              (sq_nonneg _))) (pow_nonneg hx0 4)
    · calc
        khat * edgeFlowG1AtOne D n + k2 * edgeFlowP1AtOne D n ^ 2 ≤
            (khat + k2) * edgeCompositionCoeff D n ^ 2 := hmixed
        _ ≤ (khat + k2) * (F.coeff ^ 2 * x ^ 4) :=
          mul_le_mul_of_nonneg_left hFsquare (add_nonneg hkhat hk2)
        _ ≤ (E.coeff + (khat + k2) * F.coeff ^ 2) * x ^ 4 := by
          have := mul_nonneg E.coeff_nonneg (pow_nonneg hx0 4)
          ring_nf at *
          linarith

/-- The three widened edge ceilings automatically absorb every source whose
rear period is below `edgeSpeedCap` and whose total density mass is at most
one. -/
theorem flowCeilings_of_mass_one
    (D : ConstructedConfiguredSequenceWeighted.Data)
    {MA NA ell M : ℝ} (n : ℕ)
    (hell : 0 ≤ ell) (hellQ : ell ≤ edgeSpeedCap D n)
    (hM : 0 ≤ M) (hM1 : M ≤ 1) :
    GaugeFlowDerivCost.costP1 ell (analyticKhat D) M ≤ edgeP1 D MA n ∧
      GaugeFlowDerivCost.costG1 ell (analyticKhat D)
          (GaugeMarkedDataOfRearFamily.rearKappa2 sourceKh) M ≤
        edgeG1 D MA NA n ∧
      analyticKhat D * GaugeFlowDerivCost.costG1 ell (analyticKhat D)
          (GaugeMarkedDataOfRearFamily.rearKappa2 sourceKh) M +
        GaugeMarkedDataOfRearFamily.rearKappa2 sourceKh *
          GaugeFlowDerivCost.costP1 ell (analyticKhat D) M ^ 2 ≤
        edgeCgWithKhat D (analyticKhat D) MA NA n := by
  have hk := analyticKhat_nonnegative D
  have hk2 := GaugeMarkedDataOfRearFamily.rearKappa2_nonneg
    sourceKh_nonnegative sourceKh_lt_one
  have hP := GaugeFlowDerivCost.costP1_le hell hellQ hk hM hM1
  have hG := GaugeFlowDerivCost.costG1_le hell hellQ hk hk2 hM hM1
  have hC := GaugeFlowDerivCost.mixedCost_le hell hellQ hk hk2 hM hM1
  refine ⟨hP.trans ?_, hG.trans ?_, hC.trans ?_⟩
  · exact le_max_right _ _
  · exact le_max_right _ _
  · exact le_max_right _ _

def edgeConversion
    (D : ConstructedConfiguredSequenceWeighted.Data)
    (khat MA NA : ℝ) : ℕ → ℝ :=
  fun n ↦ c2ConstVar (edgeSourceP0 D n) (edgeP1 D MA n) khat
    (edgeG1 D MA NA n) (edgeCgWithKhat D khat MA NA n)

theorem edgeConversion_nonnegative
    (D : ConstructedConfiguredSequenceWeighted.Data)
    (khat MA NA : ℝ) (n : ℕ) : 0 ≤ edgeConversion D khat MA NA n :=
  c2ConstVar_nonneg _ _ _ _ _

theorem exists_edgeConversion_growth_majorant
    (D : ConstructedConfiguredSequenceWeighted.Data)
    {khat MA NA gamma : ℝ}
    (hkhat : 0 ≤ khat) (hMA : 0 ≤ MA) (hNA : 0 ≤ NA)
    (hgamma : 0 < gamma) :
    ∃ C0 : ℝ, 0 ≤ C0 ∧ ∀ n,
      edgeConversion D khat MA NA n ≤
        C0 * (1 + D.Hs n) ^ 2 * Real.exp (gamma * D.Hs n) := by
  exact exists_c2ConstVar_growth_majorant_of_inverseEnvelope
    (fun n ↦ (D.model.separation_pos n).le) (edgeSourceP0_pos D)
    (inverseEdgeSourceP0Envelope D)
    (edgeP1Envelope D hMA)
    (constantKhatEnvelope D hkhat)
    (edgeG1Envelope D hMA hNA)
    (edgeCgWithKhatEnvelope D hkhat hMA hNA) hgamma

def edgeEndpointConversion
    (D : ConstructedConfiguredSequenceWeighted.Data)
    (kh M : ℝ) : ℕ → ℝ :=
  fun n ↦ max
    (successorEndpointConversion D kh M n)
    (mergedEndpointConversion D kh M n)

theorem successorEndpointConversion_le_edgeEndpointConversion
    (D : ConstructedConfiguredSequenceWeighted.Data)
    (kh M : ℝ) (n : ℕ) :
    successorEndpointConversion D kh M n ≤
      edgeEndpointConversion D kh M n :=
  le_max_left _ _

theorem endpointConversion_succ_le_edgeEndpointConversion
    (D : ConstructedConfiguredSequenceWeighted.Data)
    (kh M : ℝ) (n : ℕ) :
    endpointConversion D kh M (n + 1) ≤
      edgeEndpointConversion D kh M n :=
  successorEndpointConversion_le_edgeEndpointConversion D kh M n

theorem mergedEndpointConversion_le_edgeEndpointConversion
    (D : ConstructedConfiguredSequenceWeighted.Data)
    (kh M : ℝ) (n : ℕ) :
    mergedEndpointConversion D kh M n ≤
      edgeEndpointConversion D kh M n :=
  le_max_right _ _

theorem endpointConversion_le_edgeEndpointConversion
    (D : ConstructedConfiguredSequenceWeighted.Data)
    (kh M : ℝ) (n : ℕ) :
    endpointConversion D kh M n ≤
      edgeEndpointConversion D kh M n :=
  (le_max_right _ _).trans
    (mergedEndpointConversion_le_edgeEndpointConversion D kh M n)

def edgeCombinedConversion
    (D : ConstructedConfiguredSequenceWeighted.Data)
    (MA NA khat kh M : ℝ) : ℕ → ℝ :=
  fun n ↦ edgeConversion D khat MA NA n +
    edgeEndpointConversion D kh M n

theorem edgeEndpointConversion_nonnegative
    (D : ConstructedConfiguredSequenceWeighted.Data)
    {kh M : ℝ} (hkh0 : 0 ≤ kh) (hkh1 : kh < 1) :
    ∀ n, 0 ≤ edgeEndpointConversion D kh M n := by
  intro n
  exact (mergedEndpointConversion_nonnegative D hkh0 hkh1 n).trans
    (mergedEndpointConversion_le_edgeEndpointConversion D kh M n)

theorem edgeCombinedConversion_nonnegative
    (D : ConstructedConfiguredSequenceWeighted.Data)
    {MA NA khat kh M : ℝ} (hkh0 : 0 ≤ kh) (hkh1 : kh < 1) :
    ∀ n, 0 ≤ edgeCombinedConversion D MA NA khat kh M n := by
  intro n
  exact add_nonneg (edgeConversion_nonnegative D khat MA NA n)
    (edgeEndpointConversion_nonnegative D hkh0 hkh1 n)

theorem exists_edgeEndpointConversion_growth_majorant
    (D : ConstructedConfiguredSequenceWeighted.Data)
    {kh M gamma : ℝ}
    (hkh0 : 0 ≤ kh) (hkh1 : kh < 1) (hM : 0 ≤ M)
    (hgamma : 0 < gamma) :
    ∃ C0 : ℝ, 0 ≤ C0 ∧ ∀ n,
      edgeEndpointConversion D kh M n ≤
        C0 * (1 + D.Hs n) ^ 2 * Real.exp (gamma * D.Hs n) := by
  obtain ⟨A, hA0, hA⟩ :=
    exists_successorEndpointConversion_growth_majorant
      D hkh0 hkh1 hM hgamma
  obtain ⟨B, hB0, hB⟩ :=
    exists_mergedEndpointConversion_growth_majorant
      D hkh0 hkh1 hM hgamma
  refine ⟨A + B, add_nonneg hA0 hB0, ?_⟩
  intro n
  have hz : 0 ≤ (1 + D.Hs n) ^ 2 * Real.exp (gamma * D.Hs n) := by
    positivity
  unfold edgeEndpointConversion
  apply max_le
  · apply (hA n).trans
    calc
      A * (1 + D.Hs n) ^ 2 * Real.exp (gamma * D.Hs n) =
          A * ((1 + D.Hs n) ^ 2 * Real.exp (gamma * D.Hs n)) := by ring
      _ ≤ (A + B) * ((1 + D.Hs n) ^ 2 * Real.exp (gamma * D.Hs n)) :=
        mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hB0) hz
      _ = (A + B) * (1 + D.Hs n) ^ 2 *
          Real.exp (gamma * D.Hs n) := by ring
  · apply (hB n).trans
    calc
      B * (1 + D.Hs n) ^ 2 * Real.exp (gamma * D.Hs n) =
          B * ((1 + D.Hs n) ^ 2 * Real.exp (gamma * D.Hs n)) := by ring
      _ ≤ (A + B) * ((1 + D.Hs n) ^ 2 * Real.exp (gamma * D.Hs n)) :=
        mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hA0) hz
      _ = (A + B) * (1 + D.Hs n) ^ 2 *
          Real.exp (gamma * D.Hs n) := by ring

theorem exists_edgeCombinedConversion_growth_majorant
    (D : ConstructedConfiguredSequenceWeighted.Data)
    {MA NA khat kh M gamma : ℝ}
    (hMA : 0 ≤ MA) (hNA : 0 ≤ NA) (hkhat : 0 ≤ khat)
    (hkh0 : 0 ≤ kh) (hkh1 : kh < 1) (hM : 0 ≤ M)
    (hgamma : 0 < gamma) :
    ∃ C0 : ℝ, 0 ≤ C0 ∧ ∀ n,
      edgeCombinedConversion D MA NA khat kh M n ≤
        C0 * (1 + D.Hs n) ^ 2 * Real.exp (gamma * D.Hs n) := by
  obtain ⟨A, hA0, hA⟩ :=
    exists_edgeConversion_growth_majorant D hkhat hMA hNA hgamma
  obtain ⟨B, hB0, hB⟩ :=
    exists_edgeEndpointConversion_growth_majorant D hkh0 hkh1 hM hgamma
  refine ⟨A + B, add_nonneg hA0 hB0, ?_⟩
  intro n
  calc
    edgeCombinedConversion D MA NA khat kh M n ≤
        A * (1 + D.Hs n) ^ 2 * Real.exp (gamma * D.Hs n) +
        B * (1 + D.Hs n) ^ 2 * Real.exp (gamma * D.Hs n) :=
      add_le_add (hA n) (hB n)
    _ = (A + B) * (1 + D.Hs n) ^ 2 * Real.exp (gamma * D.Hs n) := by ring

def edgePhysicalDefect
    (D : ConstructedConfiguredSequenceWeighted.Data) : ℕ → ℝ :=
  physicalDefect D

theorem edgePhysicalDefect_nonnegative
    (D : ConstructedConfiguredSequenceWeighted.Data) :
    ∀ n, 0 ≤ edgePhysicalDefect D n :=
  physicalDefect_nonneg D

theorem exists_edgePhysicalDefect_exp_bound
    (D : ConstructedConfiguredSequenceWeighted.Data) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ n, edgePhysicalDefect D n ≤
      A * Real.exp (-((D.model.beta / 8) * D.Hs n)) := by
  simpa [edgePhysicalDefect] using exists_physicalDefect_exp_bound D

end ConfiguredRecursiveEdgeSourceP0Growth
