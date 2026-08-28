import UnitTangentIterates.ConfiguredDiagonalStableRowDefectProvider
import UnitTangentIterates.ConfiguredRowCeilingPolynomialEnvelopes
import UnitTangentIterates.ConstructedRowDefectLargeSeparation

/-!
# Polynomial diagonal coefficients are summable

The configured defect decays like `exp (-(beta/4) H_n)`.  Any fixed
polynomial in `1+H_n` is absorbed into half that exponent, and the linear
separation lower bound then gives a geometric series.  Thus polynomial
row-dependent conversion factors introduce no recursive threshold.
-/

noncomputable section

open Real PathMetric

namespace ConfiguredPolynomialDiagonalStableRowDefectProvider

open ConfiguredApproximateDefectPathRowwise
  ConfiguredApproximateDefectPathRowwiseCost
  ConfiguredDiagonalStableRowDefectProvider
  ConfiguredRowDefectProvider
  ConstructedRowCPolynomialGrowth

theorem summable_polynomial_mul_rowDefect
    (D : ConstructedConfiguredSequenceWeighted.Data) {B : ℕ → ℝ}
    (hB : PolynomialEnvelope D.Hs B) :
    Summable (fun n ↦ B n * rowDefect D n) := by
  let gamma : ℝ := D.model.beta / 8
  have hbeta : 0 < D.model.beta := (D.model.configs 0).hbeta0
  have hgamma : 0 < gamma := div_pos hbeta (by norm_num)
  obtain ⟨E, hE0, hE⟩ := exists_one_add_pow_le_exp hB.degree hgamma
  let Amodel := ModelDefectSummable.modelDefectConst
    (2 * D.kd) D.kstar (edgeCoefficient D) (D.Hs 0) D.model.beta
  have hAmodel : 0 ≤ Amodel := by
    exact ModelDefectSummable.modelDefectConst_nonneg
      (edgeCoefficient_nonneg D) D.kstar_nonneg D.separation_zero_pos hbeta
  let C : ℝ := hB.coeff * E * configuredCostConst D * Amodel
  have hC : 0 ≤ C := by
    dsimp [C]
    exact mul_nonneg
      (mul_nonneg (mul_nonneg hB.coeff_nonneg hE0) (configuredCostConst_nonneg D))
      hAmodel
  have hmodel : ∀ n, rowModelDefect D n ≤
      Amodel * Real.exp (-((D.model.beta / 4) * D.Hs n)) := by
    intro n
    simpa [Amodel, rowModelDefect] using
      (ModelDefectSummable.model_defect_le
        (M := 2 * D.kd) (kb := D.kstar) (Cm := edgeCoefficient D)
        (P0 := D.Hs 0) (beta := D.model.beta)
        (Hs := D.Hs) (eps := edgeEps D) (P := D.Hs)
        hbeta (mul_nonneg (by norm_num) D.kd_nonneg)
        (edgeCoefficient_nonneg D) D.kstar_nonneg
        D.separation_zero_pos D.separation_lower
        (fun i ↦ (D.model.separation_pos i).le) (edgeEps_nonneg D)
        (edgeEps_le_exp_at_row D) n)
  have hdec : ∀ n, B n * rowDefect D n ≤
      C * Real.exp (-(gamma * D.Hs n)) := by
    intro n
    have hH : 0 ≤ D.Hs n := (D.model.separation_pos n).le
    have hBexp : B n ≤ hB.coeff * E * Real.exp (gamma * D.Hs n) := by
      calc
        B n ≤ hB.coeff * (1 + D.Hs n) ^ hB.degree := hB.bound n
        _ ≤ hB.coeff * (E * Real.exp (gamma * D.Hs n)) :=
          mul_le_mul_of_nonneg_left (hE (D.Hs n) hH) hB.coeff_nonneg
        _ = hB.coeff * E * Real.exp (gamma * D.Hs n) := by ring
    have hdef : rowDefect D n ≤ configuredCostConst D * Amodel *
        Real.exp (-((D.model.beta / 4) * D.Hs n)) := by
      exact (rowDefect_le_configuredCostConst D n).trans <| by
        calc
          configuredCostConst D * rowModelDefect D n ≤
              configuredCostConst D *
                (Amodel * Real.exp (-((D.model.beta / 4) * D.Hs n))) :=
            mul_le_mul_of_nonneg_left (hmodel n) (configuredCostConst_nonneg D)
          _ = _ := by ring
    calc
      B n * rowDefect D n ≤
          (hB.coeff * E * Real.exp (gamma * D.Hs n)) *
            (configuredCostConst D * Amodel *
              Real.exp (-((D.model.beta / 4) * D.Hs n))) :=
        mul_le_mul hBexp hdef (rowDefect_nonneg D n)
          (mul_nonneg (mul_nonneg hB.coeff_nonneg hE0) (Real.exp_pos _).le)
      _ = C * (Real.exp (gamma * D.Hs n) *
          Real.exp (-((D.model.beta / 4) * D.Hs n))) := by
        dsimp [C]
        ring
      _ = C * Real.exp
          (gamma * D.Hs n - (D.model.beta / 4) * D.Hs n) := by
        rw [← Real.exp_add]
        congr 2
      _ = C * Real.exp (-(gamma * D.Hs n)) := by
        dsimp [gamma]
        congr 2
        ring
  let q : ℝ := Real.exp (-(gamma * D.deltaStep))
  let C0 : ℝ := C * Real.exp (-(gamma * D.Hs 0))
  have hq0 : 0 ≤ q := (Real.exp_pos _).le
  have hq1 : q < 1 := by
    dsimp [q]
    rw [Real.exp_lt_one_iff]
    exact neg_neg_of_pos (mul_pos hgamma D.deltaStep_pos)
  have hgeo : ∀ n, B n * rowDefect D n ≤ C0 * q ^ n := by
    intro n
    apply (hdec n).trans
    have hexp : Real.exp (-(gamma * D.Hs n)) ≤
        Real.exp (-(gamma * (D.Hs 0 + n * D.deltaStep))) := by
      apply Real.exp_le_exp.mpr
      nlinarith [D.separation_linear n]
    calc
      C * Real.exp (-(gamma * D.Hs n)) ≤
          C * Real.exp (-(gamma * (D.Hs 0 + n * D.deltaStep))) :=
        mul_le_mul_of_nonneg_left hexp hC
      _ = C * (Real.exp (-(gamma * D.Hs 0)) *
          Real.exp (-(gamma * ((n : ℝ) * D.deltaStep)))) := by
        rw [← Real.exp_add]
        congr 2
        ring
      _ = C0 * q ^ n := by
        dsimp [C0, q]
        rw [← Real.exp_nat_mul]
        push_cast
        ring
  have hgeom : Summable (fun n : ℕ ↦ q ^ n) :=
    summable_geometric_of_lt_one hq0 hq1
  exact Summable.of_nonneg_of_le
    (fun n ↦ mul_nonneg (hB.value_nonneg n) (rowDefect_nonneg D n))
    hgeo (hgeom.mul_left C0)

def polynomialCertificate
    (D : ConstructedConfiguredSequenceWeighted.Data) {B : ℕ → ℝ}
    (hB : PolynomialEnvelope D.Hs B) : Certificate D B where
  coefficient_nonnegative := hB.value_nonneg
  summable_diagonal n := by
    simpa [ConfiguredDiagonalStableRowDefectProvider.error, Nat.add_comm] using
      (summable_polynomial_mul_rowDefect D hB).comp_injective
        (add_right_injective n)

/-- Exact physical initial coefficient supplied by the perimeter-scaled
component estimate. -/
def physicalCoeff (D : ConstructedConfiguredSequenceWeighted.Data) (n : ℕ) : ℝ :=
  2 * D.Hs n

def physicalCoeffEnvelope (D : ConstructedConfiguredSequenceWeighted.Data) :
    PolynomialEnvelope D.Hs (physicalCoeff D) where
  coeff := 2
  degree := 1
  coeff_nonneg := by norm_num
  value_nonneg n := mul_nonneg (by norm_num) (D.model.separation_pos n).le
  bound n := by
    simp only [physicalCoeff, pow_one]
    linarith

def physicalCertificate (D : ConstructedConfiguredSequenceWeighted.Data) :
    Certificate D (physicalCoeff D) :=
  polynomialCertificate D (physicalCoeffEnvelope D)

def physicalDefect (D : ConstructedConfiguredSequenceWeighted.Data) (n : ℕ) : ℝ :=
  physicalCoeff D n * rowDefect D n

theorem physicalDefect_nonneg
    (D : ConstructedConfiguredSequenceWeighted.Data) (n : ℕ) :
    0 ≤ physicalDefect D n :=
  mul_nonneg ((physicalCoeffEnvelope D).value_nonneg n) (rowDefect_nonneg D n)

/-- Multiplying by the physical perimeter consumes only half of the available
quarter-rate decay. -/
theorem exists_physicalDefect_exp_bound
    (D : ConstructedConfiguredSequenceWeighted.Data) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ n,
      physicalDefect D n ≤
        A * Real.exp (-((D.model.beta / 8) * D.Hs n)) := by
  let gamma : ℝ := D.model.beta / 8
  have hbeta : 0 < D.model.beta := (D.model.configs 0).hbeta0
  have hgamma : 0 < gamma := div_pos hbeta (by norm_num)
  obtain ⟨E, hE0, hE⟩ := exists_one_add_pow_le_exp 1 hgamma
  let A : ℝ := 2 * E * ConstructedRowDefectLargeSeparation.rowDefectExpConst D
  have hA : 0 ≤ A := by
    dsimp [A]
    exact mul_nonneg
      (mul_nonneg (by norm_num) hE0)
      (ConstructedRowDefectLargeSeparation.rowDefectExpConst_nonneg D)
  refine ⟨A, hA, ?_⟩
  intro n
  have hH : 0 ≤ D.Hs n := (D.model.separation_pos n).le
  have hlin : physicalCoeff D n ≤
      2 * E * Real.exp (gamma * D.Hs n) := by
    have hp := hE (D.Hs n) hH
    simp only [pow_one] at hp
    unfold physicalCoeff
    nlinarith [mul_le_mul_of_nonneg_left hp (by norm_num : (0 : ℝ) ≤ 2)]
  have hd := ConstructedRowDefectLargeSeparation.rowDefect_le_exp D n
  calc
    physicalDefect D n ≤
        (2 * E * Real.exp (gamma * D.Hs n)) *
          (ConstructedRowDefectLargeSeparation.rowDefectExpConst D *
            Real.exp (-((D.model.beta / 4) * D.Hs n))) := by
      exact mul_le_mul hlin hd (rowDefect_nonneg D n)
        (mul_nonneg (mul_nonneg (by norm_num) hE0) (Real.exp_pos _).le)
    _ = A * (Real.exp (gamma * D.Hs n) *
        Real.exp (-((D.model.beta / 4) * D.Hs n))) := by
      dsimp [A]
      ring
    _ = A * Real.exp
        (gamma * D.Hs n - (D.model.beta / 4) * D.Hs n) := by
      rw [← Real.exp_add]
      simp only [sub_eq_add_neg]
    _ = A * Real.exp (-((D.model.beta / 8) * D.Hs n)) := by
      dsimp [gamma]
      congr 2
      ring

end ConfiguredPolynomialDiagonalStableRowDefectProvider
