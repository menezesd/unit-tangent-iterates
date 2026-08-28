import UnitTangentIterates.ConfiguredRecursiveEdgeFiniteColumnScalarClosing

/-!
# Period-scaled recost conversion diagonal

The terminal fully physical components divide the first and second spatial
components by one and two powers of the rear period.  Passing back to the
unweighted canonical recost is therefore sound after uniformly scaling the
whole component chain by the square of the configured rear-period cap.  This
file keeps that factor explicit and proves that the resulting configured
diagonal is still summable.

The summability proof deliberately retains the defect decay at `j + 1`.
There is no configured upper bound for `Hs (j + 1)` in terms of `Hs j`, so a
proof which first weakens everything to row `j` cannot absorb the period cap.
-/

noncomputable section

open Filter Real

namespace ConfiguredRecursiveEdgeRecostPeriodScaledDiagonal

open ConfiguredCombinedPhysicalDiagonalLargeSeparation
  ConfiguredRecursiveEdgeSourceP0
  ConfiguredRecursiveEdgeSourceP0Growth
  ConfiguredRecursiveEdgeWeightedEffectiveError
  ConfiguredRecursiveEdgeFiniteColumnScalarClosing
  ConstructedRowCPolynomialGrowth

/-- The square of the configured successor-edge rear-period cap. -/
def recostPeriodScale
    (D : ConstructedConfiguredSequenceWeighted.Data) (j : ℕ) : ℝ :=
  (edgeSpeedCap D j) ^ 2

/-- The physical-path conversion after uniformly scaling the component chain
by the square of the rear-period cap. -/
def recostEdgeConversion
    (D : ConstructedConfiguredSequenceWeighted.Data)
    (khat MA NA : ℝ) (j : ℕ) : ℝ :=
  2 * recostPeriodScale D j * edgeConversion D khat MA NA j

/-- The period-scaled physical conversion plus the unchanged endpoint cap. -/
def recostCombinedConversion
    (D : ConstructedConfiguredSequenceWeighted.Data)
    (MA NA khat kh M : ℝ) (j : ℕ) : ℝ :=
  recostEdgeConversion D khat MA NA j +
    edgeEndpointConversion D kh M j

def recostDirectConversion
    (D : ConstructedConfiguredSequenceWeighted.Data)
    (MA NA E0 C0 C1 C2 M : ℝ) (j : ℕ) : ℝ :=
  directScale E0 C0 C1 C2 *
    recostCombinedConversion D MA NA (analyticKhat D) sourceKh M j

def recostDirectDiagonal
    (D : ConstructedConfiguredSequenceWeighted.Data)
    (MA NA E0 C0 C1 C2 M : ℝ) : ℕ → ℝ :=
  weightedSequence (recostDirectConversion D MA NA E0 C0 C1 C2 M)
    (edgePhysicalDefect D)

/-- Natural one-edge metric error before the global stable-transition scale
is applied. -/
def recostCanonicalError
    (D : ConstructedConfiguredSequenceWeighted.Data)
    (MA NA khat kh M : ℝ) (j : ℕ) : ℝ :=
  weightedSequence (recostCombinedConversion D MA NA khat kh M)
    (edgePhysicalDefect D) j

theorem recostPeriodScale_nonnegative
    (D : ConstructedConfiguredSequenceWeighted.Data) (j : ℕ) :
    0 ≤ recostPeriodScale D j :=
  sq_nonneg _

theorem one_le_recostPeriodScale
    (D : ConstructedConfiguredSequenceWeighted.Data) (j : ℕ) :
    1 ≤ recostPeriodScale D j := by
  have hH : 0 ≤ D.Hs (j + 1) := (D.model.separation_pos (j + 1)).le
  unfold recostPeriodScale edgeSpeedCap speedCap
  nlinarith [sq_nonneg (3 * (1 + D.Hs (j + 1)) - 1)]

/-- The successor-edge period cap itself is at least one. -/
theorem one_le_edgeSpeedCap
    (D : ConstructedConfiguredSequenceWeighted.Data) (j : ℕ) :
    1 ≤ edgeSpeedCap D j := by
  have hH : 0 ≤ D.Hs (j + 1) := (D.model.separation_pos (j + 1)).le
  unfold edgeSpeedCap speedCap
  linarith

/-- The uniform component scaling has the factor-two reserve required by the
normalized physical-history endpoints. -/
theorem two_le_recostPeriodScale
    (D : ConstructedConfiguredSequenceWeighted.Data) (j : ℕ) :
    2 ≤ recostPeriodScale D j := by
  have hH : 0 ≤ D.Hs (j + 1) := (D.model.separation_pos (j + 1)).le
  unfold recostPeriodScale edgeSpeedCap speedCap
  nlinarith [sq_nonneg (3 * (1 + D.Hs (j + 1)) - 1)]

theorem recostCombinedConversion_nonnegative
    (D : ConstructedConfiguredSequenceWeighted.Data)
    {MA NA khat kh M : ℝ} (hkh0 : 0 ≤ kh) (hkh1 : kh < 1) :
    ∀ j, 0 ≤ recostCombinedConversion D MA NA khat kh M j := by
  intro j
  exact add_nonneg
    (mul_nonneg (mul_nonneg (by norm_num) (recostPeriodScale_nonnegative D j))
      (edgeConversion_nonnegative D khat MA NA j))
    (edgeEndpointConversion_nonnegative D hkh0 hkh1 j)

theorem recostCombinedConversion_le_scaled
    (D : ConstructedConfiguredSequenceWeighted.Data)
    {MA NA khat kh M : ℝ} (hkh0 : 0 ≤ kh) (hkh1 : kh < 1) (j : ℕ) :
    recostCombinedConversion D MA NA khat kh M j ≤
      2 * recostPeriodScale D j *
        edgeCombinedConversion D MA NA khat kh M j := by
  have hscale := one_le_recostPeriodScale D j
  have hend := edgeEndpointConversion_nonnegative D (M := M) hkh0 hkh1 j
  have htwo : 1 ≤ 2 * recostPeriodScale D j := by nlinarith
  have hscaledEnd := mul_le_mul_of_nonneg_right htwo hend
  unfold recostCombinedConversion recostEdgeConversion edgeCombinedConversion
  nlinarith

theorem recostDirectConversion_nonnegative
    (D : ConstructedConfiguredSequenceWeighted.Data)
    {MA NA E0 C0 C1 C2 M : ℝ} :
    ∀ j, 0 ≤ recostDirectConversion D MA NA E0 C0 C1 C2 M j := by
  intro j
  exact mul_nonneg (directScale_nonnegative E0 C0 C1 C2)
    (recostCombinedConversion_nonnegative D sourceKh_nonnegative
      sourceKh_lt_one j)

theorem recostCanonicalError_nonnegative
    (D : ConstructedConfiguredSequenceWeighted.Data)
    {MA NA khat kh M : ℝ} (hkh0 : 0 ≤ kh) (hkh1 : kh < 1) :
    ∀ j, 0 ≤ recostCanonicalError D MA NA khat kh M j := by
  intro j
  exact mul_nonneg
    (recostCombinedConversion_nonnegative D hkh0 hkh1 j)
    (edgePhysicalDefect_nonnegative D (j + 1))

theorem one_le_directScale (E0 C0 C1 C2 : ℝ) :
    1 ≤ directScale E0 C0 C1 C2 := by
  unfold directScale
  have h := ConfiguredRecursiveEdgeFiniteColumnGaugeMajorant.configuredTarget_nonnegative
    E0 C0 C1 C2
  linarith

theorem recostCanonicalError_le_directDiagonal
    (D : ConstructedConfiguredSequenceWeighted.Data)
    {MA NA E0 C0 C1 C2 M : ℝ} (j : ℕ) :
    recostCanonicalError D MA NA (analyticKhat D) sourceKh M j ≤
      recostDirectDiagonal D MA NA E0 C0 C1 C2 M j := by
  unfold recostCanonicalError recostDirectDiagonal weightedSequence
    recostDirectConversion
  have hconversion := recostCombinedConversion_nonnegative D
    (MA := MA) (NA := NA) (khat := analyticKhat D) (M := M)
    sourceKh_nonnegative sourceKh_lt_one j
  have hdefect := edgePhysicalDefect_nonnegative D (j + 1)
  have hscale := one_le_directScale E0 C0 C1 C2
  nlinarith [mul_nonneg (sub_nonneg.mpr hscale)
    (mul_nonneg hconversion hdefect)]

theorem recostDirectDiagonal_nonnegative
    (D : ConstructedConfiguredSequenceWeighted.Data)
    {MA NA E0 C0 C1 C2 M : ℝ} :
    ∀ j, 0 ≤ recostDirectDiagonal D MA NA E0 C0 C1 C2 M j := by
  intro j
  exact mul_nonneg (recostDirectConversion_nonnegative D j)
    (edgePhysicalDefect_nonnegative D (j + 1))

/-- Quantitative exponential decay of the period-scaled recost diagonal.
The two quadratic factors are absorbed together at the successor separation,
where the physical defect retains its full configured decay. -/
theorem exists_recostDirectDiagonal_exp_bound
    (D : ConstructedConfiguredSequenceWeighted.Data)
    {MA NA E0 C0 C1 C2 M : ℝ}
    (hMA : 0 ≤ MA) (hNA : 0 ≤ NA) (hM : 0 ≤ M) :
    ∃ beta K : ℝ, 0 < beta ∧ 0 ≤ K ∧ ∀ j,
      recostDirectDiagonal D MA NA E0 C0 C1 C2 M j ≤
        K * Real.exp (-(beta * D.Hs (j + 1))) := by
  have hbetaModel : 0 < D.model.beta := (D.model.configs 0).hbeta0
  let b : ℝ := D.model.beta / 8
  let gamma : ℝ := D.model.beta / 32
  let absorb : ℝ := D.model.beta / 32
  let beta : ℝ := D.model.beta / 16
  have hb : 0 < b := by dsimp [b]; positivity
  have hgamma : 0 < gamma := by dsimp [gamma]; positivity
  have habsorb : 0 < absorb := by dsimp [absorb]; positivity
  have hbeta : 0 < beta := by dsimp [beta]; positivity
  obtain ⟨Cc, hCc0, hCgrowth⟩ :=
    exists_edgeCombinedConversion_growth_majorant D hMA hNA
      (analyticKhat_nonnegative D) sourceKh_nonnegative sourceKh_lt_one
      hM hgamma
  obtain ⟨A, hA0, hdexp0⟩ := exists_edgePhysicalDefect_exp_bound D
  obtain ⟨E, hE0, hE⟩ := exists_one_add_pow_le_exp 4 habsorb
  let Cs : ℝ := directScale E0 C0 C1 C2 * Cc
  let K : ℝ := Cs * 18 * E * A
  have hCs0 : 0 ≤ Cs :=
    mul_nonneg (directScale_nonnegative E0 C0 C1 C2) hCc0
  have hK0 : 0 ≤ K := by
    dsimp [K]
    positivity
  refine ⟨beta, K, hbeta, hK0, ?_⟩
  intro j
  have hHj : 0 ≤ D.Hs j := (D.model.separation_pos j).le
  have hHnext : 0 ≤ D.Hs (j + 1) :=
    (D.model.separation_pos (j + 1)).le
  have hnext : D.Hs j ≤ D.Hs (j + 1) := by
    have hs := D.separation_step j
    have hd := D.deltaStep_pos
    linarith
  have hbase : 1 + D.Hs j ≤ 1 + D.Hs (j + 1) := by linarith
  have hp2 : (1 + D.Hs j) ^ 2 ≤ (1 + D.Hs (j + 1)) ^ 2 := by
    nlinarith [sq_nonneg ((1 + D.Hs (j + 1)) + (1 + D.Hs j))]
  have hexp : Real.exp (gamma * D.Hs j) ≤
      Real.exp (gamma * D.Hs (j + 1)) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hnext hgamma.le)
  have hcombined : edgeCombinedConversion D MA NA (analyticKhat D)
      sourceKh M j ≤ Cc * (1 + D.Hs (j + 1)) ^ 2 *
        Real.exp (gamma * D.Hs (j + 1)) := by
    calc
      edgeCombinedConversion D MA NA (analyticKhat D) sourceKh M j ≤
          Cc * (1 + D.Hs j) ^ 2 * Real.exp (gamma * D.Hs j) :=
        hCgrowth j
      _ ≤ Cc * (1 + D.Hs (j + 1)) ^ 2 *
          Real.exp (gamma * D.Hs (j + 1)) := by
        gcongr
  have hscale : recostPeriodScale D j =
      9 * (1 + D.Hs (j + 1)) ^ 2 := by
    simp [recostPeriodScale, edgeSpeedCap, speedCap]
    ring
  have hconversion : recostDirectConversion D MA NA E0 C0 C1 C2 M j ≤
      Cs * 18 * (1 + D.Hs (j + 1)) ^ 4 *
        Real.exp (gamma * D.Hs (j + 1)) := by
    calc
      recostDirectConversion D MA NA E0 C0 C1 C2 M j ≤
          directScale E0 C0 C1 C2 *
            (2 * recostPeriodScale D j *
              edgeCombinedConversion D MA NA (analyticKhat D)
                sourceKh M j) :=
        mul_le_mul_of_nonneg_left
          (recostCombinedConversion_le_scaled D sourceKh_nonnegative
            sourceKh_lt_one j)
          (directScale_nonnegative E0 C0 C1 C2)
      _ ≤ directScale E0 C0 C1 C2 *
          (2 * (9 * (1 + D.Hs (j + 1)) ^ 2) *
            (Cc * (1 + D.Hs (j + 1)) ^ 2 *
              Real.exp (gamma * D.Hs (j + 1)))) := by
        rw [hscale]
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hcombined
            (mul_nonneg (by norm_num)
              (mul_nonneg (by norm_num) (sq_nonneg _))))
          (directScale_nonnegative E0 C0 C1 C2)
      _ = Cs * 18 * (1 + D.Hs (j + 1)) ^ 4 *
          Real.exp (gamma * D.Hs (j + 1)) := by
        dsimp [Cs]
        ring
  have hdexp : edgePhysicalDefect D (j + 1) ≤
      A * Real.exp (-(b * D.Hs (j + 1))) := by
    simpa [b] using hdexp0 (j + 1)
  have hmul := mul_le_mul hconversion hdexp
    (edgePhysicalDefect_nonnegative D (j + 1))
    (by
      exact mul_nonneg
        (mul_nonneg
          (mul_nonneg hCs0 (by norm_num))
          (pow_nonneg (by linarith) 4))
        (Real.exp_pos _).le)
  have hpoly := hE (D.Hs (j + 1)) hHnext
  calc
    recostDirectDiagonal D MA NA E0 C0 C1 C2 M j ≤
        (Cs * 18 * (1 + D.Hs (j + 1)) ^ 4 *
          Real.exp (gamma * D.Hs (j + 1))) *
        (A * Real.exp (-(b * D.Hs (j + 1)))) := hmul
    _ ≤ (Cs * 18 * (E * Real.exp (absorb * D.Hs (j + 1))) *
          Real.exp (gamma * D.Hs (j + 1))) *
        (A * Real.exp (-(b * D.Hs (j + 1)))) := by
      gcongr
    _ = K * Real.exp (-(beta * D.Hs (j + 1))) := by
      rw [show -(beta * D.Hs (j + 1)) =
          absorb * D.Hs (j + 1) + gamma * D.Hs (j + 1) +
            -(b * D.Hs (j + 1)) by
        dsimp [beta, absorb, gamma, b]
        ring,
        Real.exp_add, Real.exp_add]
      dsimp [K]
      ring

theorem recostDirectDiagonal_summable
    (D : ConstructedConfiguredSequenceWeighted.Data)
    {MA NA E0 C0 C1 C2 M : ℝ}
    (hMA : 0 ≤ MA) (hNA : 0 ≤ NA) (hM : 0 ≤ M) :
    Summable (recostDirectDiagonal D MA NA E0 C0 C1 C2 M) := by
  obtain ⟨beta, K, hbeta, hK, hbound⟩ :=
    exists_recostDirectDiagonal_exp_bound D hMA hNA hM
  have hs : Summable (fun j : ℕ ↦
      K * Real.exp (-(beta * D.Hs (j + 1)))) := by
    have hbase := ModelDefectSummable.summable_exp_neg_of_growth hbeta
      D.deltaStep_pos D.separation_linear
    exact (hbase.comp_injective (by
      intro a b hab
      exact Nat.add_right_cancel hab)).mul_left K
  exact Summable.of_nonneg_of_le
    (recostDirectDiagonal_nonnegative D) hbound hs

/-- A large-separation tail package for the period-scaled recost diagonal.
Here the already combined diagonal is the stage defect, so the auxiliary
coefficient sequence is identically one. -/
theorem exists_recostDirectOutput
    (D : ConstructedConfiguredSequenceWeighted.Data)
    {MA NA E0 C0 C1 C2 M Cw : ℝ}
    (hMA : 0 ≤ MA) (hNA : 0 ≤ NA) (hM : 0 ≤ M) (hCw : 0 ≤ Cw) :
    Nonempty (ExponentialDiagonalLargeSeparation.Output D (fun _ ↦ 1)
      (recostDirectDiagonal D MA NA E0 C0 C1 C2 M) Cw) := by
  obtain ⟨beta, K, hbeta, hK, hdiag⟩ :=
    exists_recostDirectDiagonal_exp_bound D hMA hNA hM
  have hdiag' : ∀ j,
      recostDirectDiagonal D MA NA E0 C0 C1 C2 M j ≤
        K * Real.exp (-(beta * D.Hs j)) := by
    intro j
    have hnext : D.Hs j ≤ D.Hs (j + 1) := by
      have hs := D.separation_step j
      have hd := D.deltaStep_pos
      linarith
    exact (hdiag j).trans (mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (by
        have hm := mul_le_mul_of_nonneg_left hnext hbeta.le
        linarith)) hK)
  let gamma : ℝ := beta / 2
  have hgamma : gamma < beta := by dsimp [gamma]; linarith
  apply ExponentialDiagonalLargeSeparation.exists_output D (fun _ ↦ 1)
    (recostDirectDiagonal D MA NA E0 C0 C1 C2 M)
    (fun _ ↦ zero_le_one) zero_le_one hK hbeta hgamma
  · intro j
    have hH : 0 ≤ D.Hs j := (D.model.separation_pos j).le
    have hgamma0 : 0 ≤ gamma := (half_pos hbeta).le
    have hsquare : 1 ≤ (1 + D.Hs j) ^ 2 := by
      nlinarith [sq_nonneg (D.Hs j)]
    have hexp : 1 ≤ Real.exp (gamma * D.Hs j) := by
      rw [← Real.exp_zero]
      exact Real.exp_le_exp.mpr (mul_nonneg hgamma0 hH)
    simpa using mul_le_mul hsquare hexp zero_le_one
      (sq_nonneg (1 + D.Hs j))
  · exact recostDirectDiagonal_nonnegative D
  · exact hdiag'
  · exact hCw

/-- Canonical large-separation choice for the period-scaled recost error.
Its coefficient is one because `recostDirectDiagonal` already contains the
physical conversion, endpoint cap, stable-transition scale, and defect. -/
noncomputable def recostWeightedOutput
    (D : ConstructedConfiguredSequenceWeighted.Data)
    (MA NA E0 C0 C1 C2 M Cw : ℝ)
    (hMA : 0 ≤ MA) (hNA : 0 ≤ NA) (hM : 0 ≤ M) (hCw : 0 ≤ Cw) :
    ExponentialDiagonalLargeSeparation.Output D (fun _ ↦ 1)
      (recostDirectDiagonal D MA NA E0 C0 C1 C2 M) Cw :=
  Classical.choice (exists_recostDirectOutput D hMA hNA hM hCw)

/-- The canonical shifted cell error at row `n`, depth `k`. -/
def shiftedRecostError
    (D : ConstructedConfiguredSequenceWeighted.Data)
    (MA NA E0 C0 C1 C2 M Cw : ℝ)
    (hMA : 0 ≤ MA) (hNA : 0 ≤ NA) (hM : 0 ≤ M) (hCw : 0 ≤ Cw)
    (n k : ℕ) : ℝ :=
  let L := recostWeightedOutput D MA NA E0 C0 C1 C2 M Cw
    hMA hNA hM hCw
  ExponentialDiagonalLargeSeparation.shiftSequence
    (recostDirectDiagonal D MA NA E0 C0 C1 C2 M) L.N (n + k)

theorem shiftedRecostError_nonnegative
    (D : ConstructedConfiguredSequenceWeighted.Data)
    {MA NA E0 C0 C1 C2 M Cw : ℝ}
    (hMA : 0 ≤ MA) (hNA : 0 ≤ NA) (hM : 0 ≤ M) (hCw : 0 ≤ Cw) :
    ∀ n k, 0 ≤ shiftedRecostError D MA NA E0 C0 C1 C2 M Cw
      hMA hNA hM hCw n k := by
  intro n k
  exact recostDirectDiagonal_nonnegative D _

/-- The selected row radius is bounded by the shifted separation reserve. -/
theorem recostWeightedOutput_radius_le
    (D : ConstructedConfiguredSequenceWeighted.Data)
    {MA NA E0 C0 C1 C2 M Cw : ℝ}
    (hMA : 0 ≤ MA) (hNA : 0 ≤ NA) (hM : 0 ≤ M) (hCw : 0 ≤ Cw)
    (n : ℕ) :
    let L := recostWeightedOutput D MA NA E0 C0 C1 C2 M Cw
      hMA hNA hM hCw
    ExponentialDiagonalLargeSeparation.rowRadius
        (ExponentialDiagonalLargeSeparation.shiftSequence (fun _ ↦ 1) L.N)
        (ExponentialDiagonalLargeSeparation.shiftSequence
          (recostDirectDiagonal D MA NA E0 C0 C1 C2 M) L.N) n ≤
      (ConstructedConfiguredInductiveTubeBudget.WeightedData.shift D L.N).Hs 0 := by
  dsimp
  exact (recostWeightedOutput D MA NA E0 C0 C1 C2 M Cw
    hMA hNA hM hCw).speed_tail n

/-- The selected large-separation package retains the strict noncircle width
gap with the period-scaled recost radius. -/
theorem recostWeightedOutput_width_gap
    (D : ConstructedConfiguredSequenceWeighted.Data)
    {MA NA E0 C0 C1 C2 M Cw : ℝ}
    (hMA : 0 ≤ MA) (hNA : 0 ≤ NA) (hM : 0 ≤ M) (hCw : 0 ≤ Cw) :
    let L := recostWeightedOutput D MA NA E0 C0 C1 C2 M Cw
      hMA hNA hM hCw
    Cw + 2 * ExponentialDiagonalLargeSeparation.rowRadius
        (ExponentialDiagonalLargeSeparation.shiftSequence (fun _ ↦ 1) L.N)
        (ExponentialDiagonalLargeSeparation.shiftSequence
          (recostDirectDiagonal D MA NA E0 C0 C1 C2 M) L.N) 0 <
      (2 * (ConstructedConfiguredInductiveTubeBudget.WeightedData.shift D L.N).Hs 0 -
        ExponentialDiagonalLargeSeparation.rowRadius
          (ExponentialDiagonalLargeSeparation.shiftSequence (fun _ ↦ 1) L.N)
          (ExponentialDiagonalLargeSeparation.shiftSequence
            (recostDirectDiagonal D MA NA E0 C0 C1 C2 M) L.N) 0) /
        Real.pi := by
  dsimp
  exact (recostWeightedOutput D MA NA E0 C0 C1 C2 M Cw
    hMA hNA hM hCw).width_gap

end ConfiguredRecursiveEdgeRecostPeriodScaledDiagonal
