import UnitTangentIterates.ExpDecay
import UnitTangentIterates.NormalPathC2IncrementVariableSpeed

/-!
# Polynomial growth of the rowwise marked-distance constant

The variable-terminal construction uses the exact row constant
`c2ConstVar (P0 n) (P1 n) (khat n) (G1 n) (Cg n)`.  This module packages the
elementary fact that polynomial ceilings for its inputs, together with a
uniform positive lower speed, give the quadratic-times-exponential majorant
used by `ConstructedRowDefectLargeSeparation.exists_output`.
-/

noncomputable section

open NormalPathC2Increment NormalPathC2IncrementVariableSpeed

namespace ConstructedRowCPolynomialGrowth

set_option maxHeartbeats 2000000

/-- A nonnegative sequence with an explicit polynomial envelope in `1 + H`. -/
structure PolynomialEnvelope (H f : ℕ → ℝ) where
  coeff : ℝ
  degree : ℕ
  coeff_nonneg : 0 ≤ coeff
  value_nonneg : ∀ n, 0 ≤ f n
  bound : ∀ n, f n ≤ coeff * (1 + H n) ^ degree

/-- Every fixed power of `1 + x` is bounded by an arbitrarily small positive
exponential.  The coefficient is uniform for all `x ≥ 0`. -/
theorem exists_one_add_pow_le_exp (m : ℕ) {gamma : ℝ} (hgamma : 0 < gamma) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ x : ℝ, 0 ≤ x →
      (1 + x) ^ m ≤ A * Real.exp (gamma * x) := by
  let delta : ℝ := gamma / ((m : ℝ) + 1)
  let A : ℝ := 1 + 1 / (delta * Real.exp 1)
  have hden : 0 < (m : ℝ) + 1 := by positivity
  have hdelta : 0 < delta := div_pos hgamma hden
  have hA0 : 0 ≤ A := by
    dsimp [A]
    positivity
  refine ⟨A ^ m, pow_nonneg hA0 m, ?_⟩
  intro x hx
  have hbase := ExpDecay.one_add_mul_exp_decay
    (b := delta) (b' := 0) (x := x) hdelta hx
  have hbase' : (1 + x) * Real.exp (-(delta * x)) ≤ A := by
    simpa [A] using hbase
  have hlin : 1 + x ≤ A * Real.exp (delta * x) := by
    have hm := mul_le_mul_of_nonneg_right hbase'
      (Real.exp_pos (delta * x)).le
    calc
      1 + x = ((1 + x) * Real.exp (-(delta * x))) *
          Real.exp (delta * x) := by
        rw [mul_assoc, ← Real.exp_add]
        simp
      _ ≤ A * Real.exp (delta * x) := hm
  have hpow : (1 + x) ^ m ≤ (A * Real.exp (delta * x)) ^ m := by
    exact pow_le_pow_left₀ (by positivity) hlin m
  have hcoef : (m : ℝ) * delta ≤ gamma := by
    dsimp [delta]
    rw [show (m : ℝ) * (gamma / ((m : ℝ) + 1)) =
      ((m : ℝ) * gamma) / ((m : ℝ) + 1) by ring]
    rw [div_le_iff₀ hden]
    nlinarith
  have harg : (m : ℝ) * (delta * x) ≤ gamma * x := by
    calc
      (m : ℝ) * (delta * x) = ((m : ℝ) * delta) * x := by ring
      _ ≤ gamma * x := mul_le_mul_of_nonneg_right hcoef hx
  calc
    (1 + x) ^ m ≤ (A * Real.exp (delta * x)) ^ m := hpow
    _ = A ^ m * Real.exp ((m : ℝ) * (delta * x)) := by
      rw [mul_pow, ← Real.exp_nat_mul]
    _ ≤ A ^ m * Real.exp (gamma * x) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr harg) (pow_nonneg hA0 m)

/-- Polynomial row ceilings imply the exact growth hypothesis required by the
constructed large-separation theorem.  The loss `exp (gamma * H)` can be made
arbitrarily small: only `gamma > 0` is required.

The conclusion is stated directly for `c2ConstVar`; it rewrites to both
variable-terminal definitions of `rowC` by `rfl`. -/
theorem exists_c2ConstVar_growth_majorant
    {H P0 P1 khat G1 Cg : ℕ → ℝ}
    (hH : ∀ n, 0 ≤ H n)
    {pmin gamma : ℝ} (hpmin : 0 < pmin)
    (hP0 : ∀ n, pmin ≤ P0 n)
    (hP1 : PolynomialEnvelope H P1)
    (hkhat : PolynomialEnvelope H khat)
    (hG1 : PolynomialEnvelope H G1)
    (hCg : PolynomialEnvelope H Cg)
    (hgamma : 0 < gamma) :
    ∃ C0 : ℝ, 0 ≤ C0 ∧ ∀ n,
      c2ConstVar (P0 n) (P1 n) (khat n) (G1 n) (Cg n) ≤
        C0 * (1 + H n) ^ 2 * Real.exp (gamma * H n) := by
  let d : ℕ := hP1.degree + hkhat.degree + hG1.degree + hCg.degree
  let A : ℝ := 1 + hP1.coeff + hkhat.coeff + hG1.coeff + hCg.coeff
  let I : ℝ := 1 / pmin
  let B : ℝ := max 1 (max A I)
  let Cpoly : ℝ := 7 * (1 + B) ^ 4
  have hA1 : 1 ≤ A := by
    dsimp [A]
    linarith [hP1.coeff_nonneg, hkhat.coeff_nonneg,
      hG1.coeff_nonneg, hCg.coeff_nonneg]
  have hI0 : 0 ≤ I := by dsimp [I]; positivity
  have hB1 : 1 ≤ B := by exact le_max_left _ _
  have hB0 : 0 ≤ B := zero_le_one.trans hB1
  have hAleB : A ≤ B :=
    (le_max_left A I).trans (le_max_right 1 (max A I))
  have hIleB : I ≤ B :=
    (le_max_right A I).trans (le_max_right 1 (max A I))
  have hCpoly0 : 0 ≤ Cpoly := by dsimp [Cpoly]; positivity
  obtain ⟨E, hE0, hE⟩ := exists_one_add_pow_le_exp (4 * d) hgamma
  refine ⟨Cpoly * E, mul_nonneg hCpoly0 hE0, ?_⟩
  intro n
  let z : ℝ := 1 + H n
  let V : ℝ := B * z ^ d
  let W : ℝ := 1 + V
  have hz1 : 1 ≤ z := by dsimp [z]; linarith [hH n]
  have hz0 : 0 ≤ z := zero_le_one.trans hz1
  have hzd1 : 1 ≤ z ^ d := one_le_pow₀ hz1
  have hV0 : 0 ≤ V := by dsimp [V]; positivity
  have hW1 : 1 ≤ W := by dsimp [W]; linarith
  have hW0 : 0 ≤ W := zero_le_one.trans hW1
  have hdegreeP : hP1.degree ≤ d := by dsimp [d]; omega
  have hdegreeK : hkhat.degree ≤ d := by dsimp [d]; omega
  have hdegreeG : hG1.degree ≤ d := by dsimp [d]; omega
  have hdegreeC : hCg.degree ≤ d := by dsimp [d]; omega
  have hP1W : P1 n ≤ W := by
    calc
      P1 n ≤ hP1.coeff * z ^ hP1.degree := by simpa [z] using hP1.bound n
      _ ≤ hP1.coeff * z ^ d :=
        mul_le_mul_of_nonneg_left (pow_right_mono₀ hz1 hdegreeP) hP1.coeff_nonneg
      _ ≤ A * z ^ d := by
        gcongr
        dsimp [A]
        linarith [hkhat.coeff_nonneg, hG1.coeff_nonneg, hCg.coeff_nonneg]
      _ ≤ B * z ^ d := mul_le_mul_of_nonneg_right hAleB (pow_nonneg hz0 d)
      _ ≤ W := by dsimp [W, V]; linarith
  have hKW : khat n ≤ W := by
    calc
      khat n ≤ hkhat.coeff * z ^ hkhat.degree := by simpa [z] using hkhat.bound n
      _ ≤ hkhat.coeff * z ^ d :=
        mul_le_mul_of_nonneg_left (pow_right_mono₀ hz1 hdegreeK) hkhat.coeff_nonneg
      _ ≤ A * z ^ d := by
        gcongr
        dsimp [A]
        linarith [hP1.coeff_nonneg, hG1.coeff_nonneg, hCg.coeff_nonneg]
      _ ≤ B * z ^ d := mul_le_mul_of_nonneg_right hAleB (pow_nonneg hz0 d)
      _ ≤ W := by dsimp [W, V]; linarith
  have hG1W : G1 n ≤ W := by
    calc
      G1 n ≤ hG1.coeff * z ^ hG1.degree := by simpa [z] using hG1.bound n
      _ ≤ hG1.coeff * z ^ d :=
        mul_le_mul_of_nonneg_left (pow_right_mono₀ hz1 hdegreeG) hG1.coeff_nonneg
      _ ≤ A * z ^ d := by
        gcongr
        dsimp [A]
        linarith [hP1.coeff_nonneg, hkhat.coeff_nonneg, hCg.coeff_nonneg]
      _ ≤ B * z ^ d := mul_le_mul_of_nonneg_right hAleB (pow_nonneg hz0 d)
      _ ≤ W := by dsimp [W, V]; linarith
  have hCgW : Cg n ≤ W := by
    calc
      Cg n ≤ hCg.coeff * z ^ hCg.degree := by simpa [z] using hCg.bound n
      _ ≤ hCg.coeff * z ^ d :=
        mul_le_mul_of_nonneg_left (pow_right_mono₀ hz1 hdegreeC) hCg.coeff_nonneg
      _ ≤ A * z ^ d := by
        gcongr
        dsimp [A]
        linarith [hP1.coeff_nonneg, hkhat.coeff_nonneg, hG1.coeff_nonneg]
      _ ≤ B * z ^ d := mul_le_mul_of_nonneg_right hAleB (pow_nonneg hz0 d)
      _ ≤ W := by dsimp [W, V]; linarith
  have hP00 : 0 < P0 n := hpmin.trans_le (hP0 n)
  have hIW : 1 / P0 n ≤ W := by
    calc
      1 / P0 n ≤ I := by
        simpa [I] using one_div_le_one_div_of_le hpmin (hP0 n)
      _ ≤ B := hIleB
      _ ≤ B * z ^ d := by nlinarith [mul_le_mul_of_nonneg_left hzd1 hB0]
      _ ≤ W := by dsimp [W, V]; linarith
  have hi0 : 0 ≤ 1 / P0 n := by positivity
  have hW2W4 : W ^ 2 ≤ W ^ 4 := pow_right_mono₀ hW1 (by norm_num)
  have hWW4 : W ≤ W ^ 4 := by
    simpa using (pow_right_mono₀ hW1 (by norm_num : 1 ≤ 4))
  have hP2 : (P1 n) ^ 2 ≤ W ^ 2 := (sq_le_sq₀ (hP1.value_nonneg n) hW0).2 hP1W
  have hK2 : (khat n) ^ 2 ≤ W ^ 2 :=
    (sq_le_sq₀ (hkhat.value_nonneg n) hW0).2 hKW
  have hI2 : (1 / P0 n) ^ 2 ≤ W ^ 2 := (sq_le_sq₀ hi0 hW0).2 hIW
  have hP2I2 : (P1 n) ^ 2 * (1 / P0 n) ^ 2 ≤ W ^ 4 := by
    calc
      (P1 n) ^ 2 * (1 / P0 n) ^ 2 ≤ W ^ 2 * W ^ 2 :=
        mul_le_mul hP2 hI2 (sq_nonneg _) (sq_nonneg _)
      _ = W ^ 4 := by ring
  have hP2K2 : (P1 n) ^ 2 * (khat n) ^ 2 ≤ W ^ 4 := by
    calc
      (P1 n) ^ 2 * (khat n) ^ 2 ≤ W ^ 2 * W ^ 2 :=
        mul_le_mul hP2 hK2 (sq_nonneg _) (sq_nonneg _)
      _ = W ^ 4 := by ring
  have hGI : G1 n * (1 / P0 n) ≤ W ^ 4 := by
    calc
      G1 n * (1 / P0 n) ≤ W * W :=
        mul_le_mul hG1W hIW hi0 hW0
      _ = W ^ 2 := by ring
      _ ≤ W ^ 4 := hW2W4
  have hP2KI : (P1 n) ^ 2 * khat n * (1 / P0 n) ≤ W ^ 4 := by
    have hP2K : (P1 n) ^ 2 * khat n ≤ W ^ 2 * W :=
      mul_le_mul hP2 hKW (hkhat.value_nonneg n) (sq_nonneg W)
    calc
      (P1 n) ^ 2 * khat n * (1 / P0 n) ≤
          (W ^ 2 * W) * W :=
        mul_le_mul hP2K hIW hi0 (mul_nonneg (sq_nonneg W) hW0)
      _ = W ^ 4 := by ring
  have hvel : velConst (P0 n) (P1 n) (khat n) ≤ 2 * W ^ 2 := by
    unfold velConst
    have hKP : khat n * P1 n ≤ W * W :=
      mul_le_mul hKW hP1W (hP1.value_nonneg n) hW0
    have hPI : P1 n * (1 / P0 n) ≤ W * W :=
      mul_le_mul hP1W hIW hi0 hW0
    nlinarith
  have hacc : accConstVar (P0 n) (P1 n) (khat n) (G1 n) (Cg n) ≤
      7 * W ^ 4 := by
    unfold accConstVar
    have hCg4 : Cg n ≤ W ^ 4 := hCgW.trans hWW4
    have hP2Div : (P1 n) ^ 2 * (1 / (P0 n) ^ 2) ≤ W ^ 4 := by
      simpa [one_div, inv_pow] using hP2I2
    nlinarith [hP2Div, hP2K2, hGI, hP2KI]
  have hc2W : c2ConstVar (P0 n) (P1 n) (khat n) (G1 n) (Cg n) ≤
      7 * W ^ 4 := by
    unfold c2ConstVar
    apply max_le
    · exact (hW1.trans hWW4).trans (by nlinarith [sq_nonneg (W ^ 2)])
    · apply max_le
      · nlinarith [hvel, hW2W4]
      · exact hacc
  have hWpoly : W ≤ (1 + B) * z ^ d := by
    dsimp [W, V]
    nlinarith
  have hc2poly : c2ConstVar (P0 n) (P1 n) (khat n) (G1 n) (Cg n) ≤
      Cpoly * z ^ (4 * d) := by
    calc
      c2ConstVar (P0 n) (P1 n) (khat n) (G1 n) (Cg n) ≤ 7 * W ^ 4 := hc2W
      _ ≤ 7 * ((1 + B) * z ^ d) ^ 4 := by
        gcongr
      _ = Cpoly * z ^ (4 * d) := by
        dsimp [Cpoly]
        rw [mul_pow, ← pow_mul]
        ring
  have habsorb : z ^ (4 * d) ≤ E * Real.exp (gamma * H n) := by
    simpa [z] using hE (H n) (hH n)
  calc
    c2ConstVar (P0 n) (P1 n) (khat n) (G1 n) (Cg n)
        ≤ Cpoly * z ^ (4 * d) := hc2poly
    _ ≤ Cpoly * (E * Real.exp (gamma * H n)) :=
      mul_le_mul_of_nonneg_left habsorb hCpoly0
    _ ≤ (Cpoly * E) * z ^ 2 * Real.exp (gamma * H n) := by
      have hz2 : 1 ≤ z ^ 2 := one_le_pow₀ hz1
      have hCE : 0 ≤ Cpoly * E := mul_nonneg hCpoly0 hE0
      have hexp : 0 ≤ Real.exp (gamma * H n) := (Real.exp_pos _).le
      nlinarith [mul_le_mul_of_nonneg_left hz2 hCE]
    _ = (Cpoly * E) * (1 + H n) ^ 2 * Real.exp (gamma * H n) := by rfl

end ConstructedRowCPolynomialGrowth
