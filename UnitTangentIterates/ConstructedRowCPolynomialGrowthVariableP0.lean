import UnitTangentIterates.ConstructedRowCPolynomialGrowth

/-!
# Row conversion growth with a polynomially weakening speed floor

The recursive selected-rear source has `1 / P0(n)` of polynomial growth,
rather than a uniform positive lower bound for `P0`.  This is sufficient for
the same arbitrarily-small exponential loss in the diagonal argument.
-/

noncomputable section

open NormalPathC2Increment NormalPathC2IncrementVariableSpeed

namespace ConstructedRowCPolynomialGrowthVariableP0

open ConstructedRowCPolynomialGrowth

set_option maxHeartbeats 2000000

theorem exists_c2ConstVar_growth_majorant_of_inverseEnvelope
    {H P0 P1 khat G1 Cg : ℕ → ℝ}
    (hH : ∀ n, 0 ≤ H n)
    (hP0pos : ∀ n, 0 < P0 n)
    (hInv : PolynomialEnvelope H (fun n ↦ 1 / P0 n))
    (hP1 : PolynomialEnvelope H P1)
    (hkhat : PolynomialEnvelope H khat)
    (hG1 : PolynomialEnvelope H G1)
    (hCg : PolynomialEnvelope H Cg)
    {gamma : ℝ} (hgamma : 0 < gamma) :
    ∃ C0 : ℝ, 0 ≤ C0 ∧ ∀ n,
      c2ConstVar (P0 n) (P1 n) (khat n) (G1 n) (Cg n) ≤
        C0 * (1 + H n) ^ 2 * Real.exp (gamma * H n) := by
  let d : ℕ := hInv.degree + hP1.degree + hkhat.degree +
    hG1.degree + hCg.degree
  let A : ℝ := 1 + hInv.coeff + hP1.coeff + hkhat.coeff +
    hG1.coeff + hCg.coeff
  let B : ℝ := max 1 A
  let Cpoly : ℝ := 7 * (1 + B) ^ 4
  have hA1 : 1 ≤ A := by
    dsimp [A]
    linarith [hInv.coeff_nonneg, hP1.coeff_nonneg,
      hkhat.coeff_nonneg, hG1.coeff_nonneg, hCg.coeff_nonneg]
  have hB1 : 1 ≤ B := le_max_left _ _
  have hB0 : 0 ≤ B := zero_le_one.trans hB1
  have hAleB : A ≤ B := le_max_right _ _
  have hCpoly0 : 0 ≤ Cpoly := by dsimp [Cpoly]; positivity
  obtain ⟨E, hE0, hE⟩ := exists_one_add_pow_le_exp (4 * d) hgamma
  refine ⟨Cpoly * E, mul_nonneg hCpoly0 hE0, ?_⟩
  intro n
  let z : ℝ := 1 + H n
  let V : ℝ := B * z ^ d
  let W : ℝ := 1 + V
  have hz1 : 1 ≤ z := by dsimp [z]; linarith [hH n]
  have hz0 : 0 ≤ z := zero_le_one.trans hz1
  have hW1 : 1 ≤ W := by
    dsimp [W, V]
    exact le_add_of_nonneg_right (mul_nonneg hB0 (pow_nonneg hz0 d))
  have hW0 : 0 ≤ W := zero_le_one.trans hW1
  have hdegreeI : hInv.degree ≤ d := by dsimp [d]; omega
  have hdegreeP : hP1.degree ≤ d := by dsimp [d]; omega
  have hdegreeK : hkhat.degree ≤ d := by dsimp [d]; omega
  have hdegreeG : hG1.degree ≤ d := by dsimp [d]; omega
  have hdegreeC : hCg.degree ≤ d := by dsimp [d]; omega
  have hcoeffI : hInv.coeff ≤ A := by
    dsimp [A]
    linarith [hP1.coeff_nonneg, hkhat.coeff_nonneg,
      hG1.coeff_nonneg, hCg.coeff_nonneg]
  have hcoeffP : hP1.coeff ≤ A := by
    dsimp [A]
    linarith [hInv.coeff_nonneg, hkhat.coeff_nonneg,
      hG1.coeff_nonneg, hCg.coeff_nonneg]
  have hcoeffK : hkhat.coeff ≤ A := by
    dsimp [A]
    linarith [hInv.coeff_nonneg, hP1.coeff_nonneg,
      hG1.coeff_nonneg, hCg.coeff_nonneg]
  have hcoeffG : hG1.coeff ≤ A := by
    dsimp [A]
    linarith [hInv.coeff_nonneg, hP1.coeff_nonneg,
      hkhat.coeff_nonneg, hCg.coeff_nonneg]
  have hcoeffC : hCg.coeff ≤ A := by
    dsimp [A]
    linarith [hInv.coeff_nonneg, hP1.coeff_nonneg,
      hkhat.coeff_nonneg, hG1.coeff_nonneg]
  have envelope_le_W
      {f : ℕ → ℝ} (hf : PolynomialEnvelope H f)
      (hdeg : hf.degree ≤ d) (hcoeff : hf.coeff ≤ A) : f n ≤ W := by
    calc
      f n ≤ hf.coeff * z ^ hf.degree := by simpa [z] using hf.bound n
      _ ≤ hf.coeff * z ^ d :=
        mul_le_mul_of_nonneg_left (pow_right_mono₀ hz1 hdeg) hf.coeff_nonneg
      _ ≤ A * z ^ d :=
        mul_le_mul_of_nonneg_right hcoeff (pow_nonneg hz0 d)
      _ ≤ B * z ^ d :=
        mul_le_mul_of_nonneg_right hAleB (pow_nonneg hz0 d)
      _ ≤ W := by dsimp [W, V]; linarith
  have hIW : 1 / P0 n ≤ W := envelope_le_W hInv hdegreeI hcoeffI
  have hP1W : P1 n ≤ W := envelope_le_W hP1 hdegreeP hcoeffP
  have hKW : khat n ≤ W := envelope_le_W hkhat hdegreeK hcoeffK
  have hG1W : G1 n ≤ W := envelope_le_W hG1 hdegreeG hcoeffG
  have hCgW : Cg n ≤ W := envelope_le_W hCg hdegreeC hcoeffC
  have hi0 : 0 ≤ 1 / P0 n := (one_div_pos.mpr (hP0pos n)).le
  have hW2W4 : W ^ 2 ≤ W ^ 4 := pow_right_mono₀ hW1 (by norm_num)
  have hWW4 : W ≤ W ^ 4 := by
    simpa using (pow_right_mono₀ hW1 (by norm_num : 1 ≤ 4))
  have hP2 : P1 n ^ 2 ≤ W ^ 2 :=
    (sq_le_sq₀ (hP1.value_nonneg n) hW0).2 hP1W
  have hK2 : khat n ^ 2 ≤ W ^ 2 :=
    (sq_le_sq₀ (hkhat.value_nonneg n) hW0).2 hKW
  have hI2 : (1 / P0 n) ^ 2 ≤ W ^ 2 :=
    (sq_le_sq₀ hi0 hW0).2 hIW
  have hP2I2 : P1 n ^ 2 * (1 / P0 n) ^ 2 ≤ W ^ 4 := by
    calc
      _ ≤ W ^ 2 * W ^ 2 :=
        mul_le_mul hP2 hI2 (sq_nonneg _) (sq_nonneg _)
      _ = W ^ 4 := by ring
  have hP2K2 : P1 n ^ 2 * khat n ^ 2 ≤ W ^ 4 := by
    calc
      _ ≤ W ^ 2 * W ^ 2 :=
        mul_le_mul hP2 hK2 (sq_nonneg _) (sq_nonneg _)
      _ = W ^ 4 := by ring
  have hGI : G1 n * (1 / P0 n) ≤ W ^ 4 := by
    calc
      _ ≤ W * W := mul_le_mul hG1W hIW hi0 hW0
      _ = W ^ 2 := by ring
      _ ≤ W ^ 4 := hW2W4
  have hP2KI : P1 n ^ 2 * khat n * (1 / P0 n) ≤ W ^ 4 := by
    have hP2K : P1 n ^ 2 * khat n ≤ W ^ 2 * W :=
      mul_le_mul hP2 hKW (hkhat.value_nonneg n) (sq_nonneg W)
    calc
      _ ≤ (W ^ 2 * W) * W :=
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
    have hP2Div : P1 n ^ 2 * (1 / P0 n ^ 2) ≤ W ^ 4 := by
      simpa [one_div, inv_pow] using hP2I2
    nlinarith [hP2Div, hP2K2, hGI, hP2KI]
  have hc2W : c2ConstVar (P0 n) (P1 n) (khat n) (G1 n) (Cg n) ≤
      7 * W ^ 4 := by
    unfold c2ConstVar
    apply max_le
    · nlinarith [hW1, hWW4]
    · apply max_le
      · nlinarith [hvel, hW2W4]
      · exact hacc
  have hWpoly : W ≤ (1 + B) * z ^ d := by
    have hzpow : 1 ≤ z ^ d := one_le_pow₀ hz1
    dsimp [W, V]
    nlinarith
  have hW4poly : W ^ 4 ≤ (1 + B) ^ 4 * z ^ (4 * d) := by
    calc
      W ^ 4 ≤ ((1 + B) * z ^ d) ^ 4 :=
        pow_le_pow_left₀ hW0 hWpoly 4
      _ = (1 + B) ^ 4 * z ^ (4 * d) := by ring
  have hc2poly : c2ConstVar (P0 n) (P1 n) (khat n) (G1 n) (Cg n) ≤
      Cpoly * z ^ (4 * d) := by
    calc
      _ ≤ 7 * W ^ 4 := hc2W
      _ ≤ 7 * ((1 + B) ^ 4 * z ^ (4 * d)) :=
        mul_le_mul_of_nonneg_left hW4poly (by norm_num)
      _ = Cpoly * z ^ (4 * d) := by simp [Cpoly, mul_assoc]
  have hpow := hE (H n) (hH n)
  have hz2 : 1 ≤ z ^ 2 := one_le_pow₀ hz1
  calc
    _ ≤ Cpoly * z ^ (4 * d) := hc2poly
    _ ≤ Cpoly * (E * Real.exp (gamma * H n)) :=
      mul_le_mul_of_nonneg_left (by simpa [z] using hpow) hCpoly0
    _ ≤ (Cpoly * E) * z ^ 2 * Real.exp (gamma * H n) := by
      have hexp := (Real.exp_pos (gamma * H n)).le
      nlinarith [mul_nonneg hCpoly0 hE0,
        mul_nonneg (mul_nonneg hCpoly0 hE0) hexp]

end ConstructedRowCPolynomialGrowthVariableP0
