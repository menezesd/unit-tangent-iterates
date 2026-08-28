import UnitTangentIterates.ConfiguredRecursiveEdgeRecostFiniteHistoryJetBudget

/-! # Weighted physical-base gauge majors for finite diagonal histories -/

noncomputable section

open Filter Real

namespace ConfiguredRecursiveEdgeWeightedBaseGaugeHistoryMajor

set_option maxHeartbeats 2000000

open ConfiguredPolynomialDiagonalStableRowDefectProvider
  ConfiguredRecursiveEdgeFiniteColumnGaugeMajorant
  ConfiguredRecursiveEdgeRecostFiniteHistoryJetBudget
  ConfiguredRecursiveEdgeSourceP0Growth
  ConfiguredRecursiveSourceP0RowJetTail
  ConstructedConfiguredInductiveTubeBudget.WeightedData
  ConstructedRowCPolynomialGrowth

/-- The index itself has a linear envelope in the separation parameter. -/
private def natEnvelope
    (D : ConstructedConfiguredSequenceWeighted.Data) :
    PolynomialEnvelope D.Hs (fun n : ℕ => (n : ℝ)) where
  coeff := D.deltaStep⁻¹
  degree := 1
  coeff_nonneg := inv_nonneg.mpr D.deltaStep_pos.le
  value_nonneg := fun _ => Nat.cast_nonneg _
  bound := by
    intro n
    have hd := D.deltaStep_pos
    have hnD : (n : ℝ) * D.deltaStep ≤ D.Hs n := by
      linarith [D.separation_linear n, D.separation_zero_pos]
    have hn : (n : ℝ) ≤ D.Hs n / D.deltaStep := (le_div_iff₀ hd).2 hnD
    have hi : 0 ≤ D.deltaStep⁻¹ := inv_nonneg.mpr hd.le
    norm_num
    calc
      (n : ℝ) ≤ D.Hs n / D.deltaStep := hn
      _ = D.deltaStep⁻¹ * D.Hs n := by rw [div_eq_inv_mul]
      _ ≤ D.deltaStep⁻¹ * (1 + D.Hs n) := by gcongr; norm_num

/-- The successor index has the corresponding affine envelope. -/
private def natSuccEnvelope
    (D : ConstructedConfiguredSequenceWeighted.Data) :
    PolynomialEnvelope D.Hs (fun n : ℕ => (n + 1 : ℕ)) where
  coeff := 1 + D.deltaStep⁻¹
  degree := 1
  coeff_nonneg := add_nonneg zero_le_one (inv_nonneg.mpr D.deltaStep_pos.le)
  value_nonneg := fun _ => Nat.cast_nonneg _
  bound := by
    intro n
    have hd := D.deltaStep_pos
    have hnD : (n : ℝ) * D.deltaStep ≤ D.Hs n := by
      linarith [D.separation_linear n, D.separation_zero_pos]
    have hn : (n : ℝ) ≤ D.Hs n / D.deltaStep := (le_div_iff₀ hd).2 hnD
    have hi : 0 ≤ D.deltaStep⁻¹ := inv_nonneg.mpr hd.le
    norm_num
    calc
      (n : ℝ) + 1 ≤ D.Hs n / D.deltaStep + 1 := by linarith
      _ = D.deltaStep⁻¹ * D.Hs n + 1 := by rw [div_eq_inv_mul]
      _ ≤ (1 + D.deltaStep⁻¹) * (1 + D.Hs n) := by
        nlinarith [(D.model.separation_pos n).le]

private def mulEnvelope
    (D : ConstructedConfiguredSequenceWeighted.Data) {f g : ℕ → ℝ}
    (F : PolynomialEnvelope D.Hs f) (G : PolynomialEnvelope D.Hs g) :
    PolynomialEnvelope D.Hs (fun n => f n * g n) where
  coeff := F.coeff * G.coeff
  degree := F.degree + G.degree
  coeff_nonneg := mul_nonneg F.coeff_nonneg G.coeff_nonneg
  value_nonneg n := mul_nonneg (F.value_nonneg n) (G.value_nonneg n)
  bound := by
    intro n
    have hx : 0 ≤ 1 + D.Hs n := by
      linarith [(D.model.separation_pos n).le]
    calc
      f n * g n ≤
          (F.coeff * (1 + D.Hs n) ^ F.degree) *
            (G.coeff * (1 + D.Hs n) ^ G.degree) :=
        mul_le_mul (F.bound n) (G.bound n) (G.value_nonneg n)
          (mul_nonneg F.coeff_nonneg (pow_nonneg hx _))
      _ = (F.coeff * G.coeff) *
          (1 + D.Hs n) ^ (F.degree + G.degree) := by rw [pow_add]; ring

/-- The base-source part remains summable after multiplication by the finite
history length. -/
theorem weighted_baseGaugeMajor_summable
    (D : ConstructedConfiguredSequenceWeighted.Data) (M : ℝ) :
    Summable (fun q : ℕ => (q + 1 : ℕ) * baseGaugeMajor D M q) := by
  let E := mulEnvelope D (natEnvelope D)
    (mulEnvelope D (rowJetCoeffEnvelope D M)
      (edgeCompositionPhysicalCoeffEnvelope D))
  have H : Summable (fun j : ℕ =>
      ((j : ℝ) * (rowJetCoeff D M j * edgeCompositionPhysicalCoeff D j)) *
        ConfiguredApproximateDefectPathRowwise.rowDefect D j) := by
    simpa [E, mulEnvelope] using summable_polynomial_mul_rowDefect D E
  have H' := H.comp_injective (add_right_injective 1)
  refine H'.congr ?_
  intro q
  simp [baseGaugeMajor, edgeCompositionPhysicalDefect,
    ConfiguredPolynomialDiagonalStableRowDefectProvider.physicalDefect]
  ring

/-- The recursive gauge part has the same weighted summability property. -/
theorem weighted_gaugeMajor_summable
    (D : ConstructedConfiguredSequenceWeighted.Data) (M Dtarget : ℝ) :
    Summable (fun q : ℕ => (q + 1 : ℕ) * gaugeMajor D M Dtarget q) := by
  let E := mulEnvelope D (natSuccEnvelope D)
    (mulEnvelope D (nextEnvelope D (rowJetCoeffEnvelope D M))
      (mulEnvelope D (edgeCompositionCoeffEnvelope D) (physicalCoeffEnvelope D)))
  have H : Summable (fun q : ℕ =>
      (((q + 1 : ℕ) * rowJetCoeff D M (q + 1)) *
        (edgeCompositionCoeff D q * physicalCoeff D q)) *
          ConfiguredApproximateDefectPathRowwise.rowDefect D q) := by
    have H0 := summable_polynomial_mul_rowDefect D E
    refine H0.congr ?_
    intro q
    ring
  refine (H.mul_left Dtarget).congr ?_
  intro q
  simp [gaugeMajor, compositionRowEps, scaledSuccessorPhysicalDefect,
    edgePhysicalDefect,
    ConfiguredPolynomialDiagonalStableRowDefectProvider.physicalDefect]
  ring

/-- The complete physical-base gauge major remains summable with the history
length factor included. -/
theorem weightedCombinedGaugeMajor_summable
    (D : ConstructedConfiguredSequenceWeighted.Data) (M Dtarget : ℝ) :
    Summable (fun q : ℕ =>
      (q + 1 : ℕ) * combinedGaugeMajor D M Dtarget q) := by
  have H := (weighted_baseGaugeMajor_summable D M).add
    (weighted_gaugeMajor_summable D M Dtarget)
  refine H.congr ?_
  intro q
  simp [combinedGaugeMajor]
  ring

/-- One epsilon paying both the positive-depth recost jet and the physical
depth-zero gauge jet. -/
def combinedHistoryMajor
    (D : ConstructedConfiguredSequenceWeighted.Data)
    (M E0 C0 C1 C2 Dtarget : ℝ) (q : ℕ) : ℝ :=
  recostJetMajor D M E0 C0 C1 C2 q +
    combinedGaugeMajor D M Dtarget q

theorem combinedHistoryMajor_nonnegative
    (D : ConstructedConfiguredSequenceWeighted.Data)
    (M E0 C0 C1 C2 Dtarget : ℝ) (hDtarget : 0 ≤ Dtarget) (q : ℕ) :
    0 ≤ combinedHistoryMajor D M E0 C0 C1 C2 Dtarget q :=
  add_nonneg (recostJetMajor_nonnegative D M E0 C0 C1 C2 q)
    (combinedGaugeMajor_nonnegative D M Dtarget hDtarget q)

theorem combinedHistoryMajor_shift
    (D : ConstructedConfiguredSequenceWeighted.Data) (N q : ℕ)
    (M E0 C0 C1 C2 Dtarget : ℝ) :
    combinedHistoryMajor (shift D N) M E0 C0 C1 C2 Dtarget q =
      combinedHistoryMajor D M E0 C0 C1 C2 Dtarget (N + q) := by
  rw [combinedHistoryMajor, combinedHistoryMajor,
    recostJetMajor_shift, combinedGaugeMajor_shift]

theorem weightedCombinedHistoryMajor_summable
    (D : ConstructedConfiguredSequenceWeighted.Data)
    {MA NA M E0 C0 C1 C2 Dtarget : ℝ}
    (hMA : 0 ≤ MA) (hNA : 0 ≤ NA) (hM : 0 ≤ M) :
    Summable (fun q : ℕ =>
      (q + 1 : ℕ) * combinedHistoryMajor D M E0 C0 C1 C2 Dtarget q) := by
  have H := (weighted_recostJetMajor_summable D
    (MA := MA) (NA := NA) (M := M) (E0 := E0)
    (C0 := C0) (C1 := C1) (C2 := C2) hMA hNA hM).add
      (weightedCombinedGaugeMajor_summable D M Dtarget)
  refine H.congr ?_
  intro q
  simp [combinedHistoryMajor]
  ring

/-- A further shift makes the combined base/recursive epsilon fit every
finite segment whose length is bounded by its diagonal index. -/
theorem exists_shift_combinedHistoryMajor_bounds
    (D : ConstructedConfiguredSequenceWeighted.Data)
    {MA NA M E0 C0 C1 C2 Dtarget Etotal : ℝ}
    (hMA : 0 ≤ MA) (hNA : 0 ≤ NA) (hM : 0 ≤ M)
    (hDtarget : 0 ≤ Dtarget) (hE : 0 < Etotal) :
    ∃ N, ∀ q : ℕ,
      combinedHistoryMajor (shift D N) M E0 C0 C1 C2 Dtarget q ≤ 1 / 2 ∧
      (q + 1 : ℕ) *
          combinedHistoryMajor (shift D N) M E0 C0 C1 C2 Dtarget q ≤
        Etotal := by
  have hs := weightedCombinedHistoryMajor_summable D
    (MA := MA) (NA := NA) (M := M) (E0 := E0)
    (C0 := C0) (C1 := C1) (C2 := C2) (Dtarget := Dtarget)
    hMA hNA hM
  have hmin : 0 < min Etotal (1 / 2 : ℝ) := lt_min hE (by norm_num)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1
    (hs.tendsto_atTop_zero.eventually (Iic_mem_nhds hmin))
  refine ⟨N, fun q => ?_⟩
  have H := hN (N + q) (Nat.le_add_right N q)
  have hshift := combinedHistoryMajor_shift D N q M E0 C0 C1 C2 Dtarget
  have hnon := combinedHistoryMajor_nonnegative D M E0 C0 C1 C2 Dtarget
    hDtarget (N + q)
  have hfactor : combinedHistoryMajor D M E0 C0 C1 C2 Dtarget (N + q) ≤
      (N + q + 1 : ℕ) *
        combinedHistoryMajor D M E0 C0 C1 C2 Dtarget (N + q) := by
    have hNq : 0 ≤ (N + q : ℝ) := by positivity
    norm_num
    nlinarith
  constructor
  · rw [hshift]
    exact hfactor.trans (H.trans (min_le_right _ _))
  · rw [hshift]
    have hcast : (q + 1 : ℝ) ≤ (N + q + 1 : ℕ) := by
      norm_cast
      omega
    have Hfinal := (mul_le_mul_of_nonneg_right hcast hnon).trans
      (H.trans (min_le_left _ _))
    convert Hfinal using 1 <;> norm_num

end ConfiguredRecursiveEdgeWeightedBaseGaugeHistoryMajor
