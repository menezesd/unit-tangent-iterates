import UnitTangentIterates.FiniteHistoryMajorBudget
import UnitTangentIterates.ConfiguredRecursiveEdgeRecostMultiplierScaledDiagonal
import UnitTangentIterates.ConfiguredRecursiveEdgeFinitePresentedFinalAssembly
import UnitTangentIterates.ConfiguredRecursiveSourceP0RowJetTail
import UnitTangentIterates.ConstructedRowCPolynomialGrowth
import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareChosenNonaffineJetBounds

/-! # Scalar finite-history budget for multiplier recost jets -/

noncomputable section

open Filter Real MarkedSpace PathMetric

namespace ConfiguredRecursiveEdgeRecostFiniteHistoryJetBudget

set_option maxHeartbeats 2000000

open ConfiguredCombinedPhysicalDiagonalLargeSeparation
  ConfiguredRecursiveEdgeFinitePresentedFinalAssembly
  ConfiguredRecursiveEdgeRecostMultiplierScaledDiagonal
  ConfiguredRecursiveEdgeRecostPeriodScaledDiagonal
  ConfiguredRecursiveEdgeSourceP0
  ConfiguredRecursiveEdgeSourceP0Growth
  ConfiguredRecursiveSourceP0RowJetTail
  ConstructedConfiguredInductiveTubeBudget.WeightedData
  ConstructedRowCPolynomialGrowth
  FiniteHistoryMajorBudget
  FiniteSmoothRearFamilyMarkingAwareAppliedSource
  FiniteSmoothRearFamilyMarkingAwareChosenNonaffineJetBounds
  FiniteSmoothRearFamilyMarkingAwareChosenVariableJetLinear
  FiniteSmoothRearFamilyMarkingAwareSource

/-- Scalar envelope for the actual nonlinear chosen-jet coefficient times the
multiplier recost source allowance. -/
def recostJetMajor (D : ConstructedConfiguredSequenceWeighted.Data)
    (M E0 C0 C1 C2 : ℝ) (q : ℕ) : ℝ :=
  rowJetCoeff D M (q + 1) *
    multiplierRecostSourceAllowance D E0 C0 C1 C2 q

theorem recostJetMajor_nonnegative
    (D : ConstructedConfiguredSequenceWeighted.Data)
    (M E0 C0 C1 C2 : ℝ) (q : ℕ) :
    0 ≤ recostJetMajor D M E0 C0 C1 C2 q :=
  mul_nonneg (rowJetCoeff_nonnegative D M (q + 1))
    (multiplierRecostSourceAllowance_nonnegative D E0 C0 C1 C2 q)

/-- The exact source-dependent coefficient is bounded by the scalar envelope. -/
theorem floorJetLinearConst_mul_allowance_le
    (D : ConstructedConfiguredSequenceWeighted.Data)
    (M E0 C0 C1 C2 : ℝ) (q : ℕ)
    {p r : Data} {Gamma : NormalPath p r}
    {P0 khat Qmax : ℝ}
    (A : MarkingAwareSource Gamma P0 sourceKh khat Qmax)
    (hperiod : rearPeriod A 0 ≤ ellCap D (q + 1)) :
    floorJetLinearConst A 1 M *
        multiplierRecostSourceAllowance D E0 C0 C1 C2 q ≤
      recostJetMajor D M E0 C0 C1 C2 q := by
  have hcoeff : floorJetLinearConst A 1 M ≤ rowJetCoeff D M (q + 1) := by
    have H := jetLinearConst_le_rowJetCoeff D M (q + 1)
      (ell := rearPeriod A 0) (L := 1)
      (A.rear_period_pos 0).le hperiod (by norm_num)
    simpa [floorJetLinearConst] using H
  exact mul_le_mul_of_nonneg_right hcoeff
    (multiplierRecostSourceAllowance_nonnegative D E0 C0 C1 C2 q)

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
    have hH : 0 ≤ D.Hs n := (D.model.separation_pos n).le
    have hnD : (n : ℝ) * D.deltaStep ≤ D.Hs n := by
      linarith [D.separation_linear n, D.separation_zero_pos]
    have hn : (n : ℝ) ≤ D.Hs n / D.deltaStep := (le_div_iff₀ hd).2 hnD
    have hi : 0 ≤ D.deltaStep⁻¹ := inv_nonneg.mpr hd.le
    norm_num
    calc
      (n : ℝ) + 1 ≤ D.Hs n / D.deltaStep + 1 := by linarith
      _ = D.deltaStep⁻¹ * D.Hs n + 1 := by rw [div_eq_inv_mul]
      _ ≤ (1 + D.deltaStep⁻¹) * (1 + D.Hs n) := by nlinarith

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

/-- Exponential decay absorbs both the chosen-jet row coefficient and the
finite-history factor `q+1`. -/
theorem weighted_recostJetMajor_summable
    (D : ConstructedConfiguredSequenceWeighted.Data)
    {MA NA M E0 C0 C1 C2 : ℝ}
    (hMA : 0 ≤ MA) (hNA : 0 ≤ NA) (hM : 0 ≤ M) :
    Summable (fun q : ℕ =>
      (q + 1 : ℕ) * recostJetMajor D M E0 C0 C1 C2 q) := by
  obtain ⟨beta, K, hbeta, hK, hdiag⟩ :=
    exists_multiplierRecostDirectDiagonal_exp_bound D
      (E0 := E0) (C0 := C0) (C1 := C1) (C2 := C2) hMA hNA hM
  let EJ := nextEnvelope D (rowJetCoeffEnvelope D M)
  let EP := mulEnvelope D (natSuccEnvelope D) EJ
  let gamma := beta / 2
  obtain ⟨A, hA, hpoly⟩ :=
    exists_one_add_pow_le_exp EP.degree (half_pos hbeta)
  let C := EP.coeff * A * K
  have hC : 0 ≤ C := mul_nonneg (mul_nonneg EP.coeff_nonneg hA) hK
  have hs : Summable (fun q : ℕ =>
      C * Real.exp (-(gamma * D.Hs (q + 1)))) := by
    have H := ModelDefectSummable.summable_exp_neg_of_growth
      (half_pos hbeta) D.deltaStep_pos D.separation_linear
    simpa [gamma, Function.comp_apply, Nat.add_comm] using
      (H.comp_injective (add_right_injective 1)).mul_left C
  apply Summable.of_nonneg_of_le
    (fun q => mul_nonneg (Nat.cast_nonneg _)
      (recostJetMajor_nonnegative D M E0 C0 C1 C2 q)) (fun q => ?_) hs
  have hstep : D.Hs q ≤ D.Hs (q + 1) := by
    linarith [D.separation_step q, D.deltaStep_pos]
  have hq0 : 0 ≤ 1 + D.Hs q := by
    linarith [(D.model.separation_pos q).le]
  have hnext0 : 0 ≤ D.Hs (q + 1) := (D.model.separation_pos _).le
  have hEP : (q + 1 : ℕ) * rowJetCoeff D M (q + 1) ≤
      EP.coeff * A * Real.exp (gamma * D.Hs (q + 1)) := by
    calc
      (q + 1 : ℕ) * rowJetCoeff D M (q + 1) ≤
          EP.coeff * (1 + D.Hs q) ^ EP.degree := EP.bound q
      _ ≤ EP.coeff * (1 + D.Hs (q + 1)) ^ EP.degree :=
        mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ hq0 (by linarith) EP.degree) EP.coeff_nonneg
      _ ≤ EP.coeff * (A * Real.exp (gamma * D.Hs (q + 1))) :=
        mul_le_mul_of_nonneg_left (hpoly _ hnext0) EP.coeff_nonneg
      _ = EP.coeff * A * Real.exp (gamma * D.Hs (q + 1)) := by ring
  have hallow := multiplierRecostSourceAllowance_le_diagonal
    D MA NA E0 C0 C1 C2 M q |>.trans (hdiag q)
  unfold recostJetMajor
  calc
    (q + 1 : ℕ) *
        (rowJetCoeff D M (q + 1) *
          multiplierRecostSourceAllowance D E0 C0 C1 C2 q) =
        ((q + 1 : ℕ) * rowJetCoeff D M (q + 1)) *
          multiplierRecostSourceAllowance D E0 C0 C1 C2 q := by ring
    _ ≤ (EP.coeff * A * Real.exp (gamma * D.Hs (q + 1))) *
        (K * Real.exp (-(beta * D.Hs (q + 1)))) :=
      mul_le_mul hEP hallow
        (multiplierRecostSourceAllowance_nonnegative D E0 C0 C1 C2 q)
        (mul_nonneg (mul_nonneg EP.coeff_nonneg hA) (Real.exp_pos _).le)
    _ = C * Real.exp (-(gamma * D.Hs (q + 1))) := by
      rw [show -(gamma * D.Hs (q + 1)) =
        gamma * D.Hs (q + 1) + -(beta * D.Hs (q + 1)) by
          dsimp [gamma]; ring, Real.exp_add]
      dsimp [C]
      ring

theorem multiplierRecostSourceAllowance_shift
    (D : ConstructedConfiguredSequenceWeighted.Data)
    (N q : ℕ) (E0 C0 C1 C2 : ℝ) :
    multiplierRecostSourceAllowance (shift D N) E0 C0 C1 C2 q =
      multiplierRecostSourceAllowance D E0 C0 C1 C2 (N + q) := by
  have hc : directRecostCompositionCoeff (shift D N) q =
      directRecostCompositionCoeff D (N + q) := by
    unfold directRecostCompositionCoeff
    rw [edgeCompositionCoeff_shift]
  have hL : recostPeriodScale (shift D N) q =
      recostPeriodScale D (N + q) := by
    simp [recostPeriodScale, edgeSpeedCap, speedCap, shift, Nat.add_assoc]
  have he : edgePhysicalDefect (shift D N) (q + 1) =
      edgePhysicalDefect D (N + q + 1) := by
    unfold edgePhysicalDefect
      ConfiguredPolynomialDiagonalStableRowDefectProvider.physicalDefect
    rw [ConstructedRowDefectLargeSeparation.rowDefect_shift]
    simp [ConfiguredPolynomialDiagonalStableRowDefectProvider.physicalDefect,
      ConfiguredPolynomialDiagonalStableRowDefectProvider.physicalCoeff,
      shift, Nat.add_assoc]
  unfold multiplierRecostSourceAllowance
  rw [hc, hL, he]

theorem recostJetMajor_shift
    (D : ConstructedConfiguredSequenceWeighted.Data)
    (N q : ℕ) (M E0 C0 C1 C2 : ℝ) :
    recostJetMajor (shift D N) M E0 C0 C1 C2 q =
      recostJetMajor D M E0 C0 C1 C2 (N + q) := by
  have hj : rowJetCoeff (shift D N) M (q + 1) =
      rowJetCoeff D M (N + q + 1) := by
    simp [rowJetCoeff, ellCap, shift, Nat.add_assoc]
  unfold recostJetMajor
  rw [hj, multiplierRecostSourceAllowance_shift]

/-- A further scalar shift on any configured data makes every finite diagonal
history fit the fixed total and half budgets. -/
theorem exists_shift_history_bounds
    (D : ConstructedConfiguredSequenceWeighted.Data)
    {MA NA M E0 C0 C1 C2 Etotal : ℝ}
    (hMA : 0 ≤ MA) (hNA : 0 ≤ NA) (hM : 0 ≤ M)
    (hE : 0 < Etotal) :
    ∃ N, ∀ q : ℕ,
      recostJetMajor (shift D N) M E0 C0 C1 C2 q ≤ 1 / 2 ∧
      (q + 1 : ℕ) * recostJetMajor (shift D N) M E0 C0 C1 C2 q ≤ Etotal := by
  have hs := weighted_recostJetMajor_summable D
    (MA := MA) (NA := NA) (M := M) (E0 := E0)
    (C0 := C0) (C1 := C1) (C2 := C2) hMA hNA hM
  have ht := hs.tendsto_atTop_zero
  have hmin : 0 < min Etotal (1 / 2 : ℝ) := lt_min hE (by norm_num)
  have he := ht.eventually (Iic_mem_nhds hmin)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 he
  refine ⟨N, fun q => ?_⟩
  have H := hN (N + q) (Nat.le_add_right N q)
  have hshift : recostJetMajor (shift D N) M E0 C0 C1 C2 q =
      recostJetMajor D M E0 C0 C1 C2 (N + q) :=
    recostJetMajor_shift D N q M E0 C0 C1 C2
  have hnon := recostJetMajor_nonnegative D M E0 C0 C1 C2 (N + q)
  have hfactor : recostJetMajor D M E0 C0 C1 C2 (N + q) ≤
      (N + q + 1 : ℕ) * recostJetMajor D M E0 C0 C1 C2 (N + q) := by
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

/-- Package the scalar bounds as the abstract finite-history budget. -/
def segmentBudget
    (D : ConstructedConfiguredSequenceWeighted.Data)
    (M E0 C0 C1 C2 Etotal : ℝ) (q k : ℕ) (hk : k ≤ q)
    (hhalf : recostJetMajor D M E0 C0 C1 C2 q ≤ 1 / 2)
    (htotal : (q + 1 : ℕ) * recostJetMajor D M E0 C0 C1 C2 q ≤ Etotal) :
    MajorBudget Etotal :=
  by
    have hcast : (k + 1 : ℝ) ≤ (q + 1 : ℕ) := by
      exact_mod_cast Nat.add_le_add_right hk 1
    apply MajorBudget.ofSegment k
      (recostJetMajor_nonnegative D M E0 C0 C1 C2 q) hhalf
    have H := (mul_le_mul_of_nonneg_right hcast
      (recostJetMajor_nonnegative D M E0 C0 C1 C2 q)).trans htotal
    convert H using 1 <;> norm_num

end ConfiguredRecursiveEdgeRecostFiniteHistoryJetBudget
