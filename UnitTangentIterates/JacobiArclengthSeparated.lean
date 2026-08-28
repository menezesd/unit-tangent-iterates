import UnitTangentIterates.JacobiArclengthUniform

/-! Sharp component-separated inverse Jacobi estimates. -/

noncomputable section

open MeasureTheory intervalIntegral MarkedTopology

namespace JacobiArclengthSeparated

open JacobiArclength JacobiArclengthUniform JacobiNormalized

structure Bounds (front rear : ℝ → ℝ) (A10 A11 A20 A21 A22 : ℝ) : Prop where
  s1 : supNorm (deriv rear) ≤
    A10 * (∫ u in (0 : ℝ)..1, |front u|) + A11 * supNorm front
  s2 : supNorm (deriv (deriv rear)) ≤
    A20 * (∫ u in (0 : ℝ)..1, |front u|) + A21 * supNorm front +
      A22 * supNorm (iteratedDeriv 1 front)

/-- The sharp coefficients before the historical proof replaces all of them
by one maximum. -/
theorem bounds
    {l P l0 c kh SF0 SF1 : ℝ} {etaR etaR1 etaR2 etaF : ℝ → ℝ}
    (hP : 0 < P) (hl0 : 0 < l0) (hc : 0 < c)
    (hR1 : ∀ x, HasDerivAt etaR (etaR1 x) x)
    (hR2 : ∀ x, HasDerivAt etaR1 (etaR2 x) x)
    (hS1 : ∀ x, |etaR1 x| ≤
      SF0 / c + (1 - Real.exp (-l0))⁻¹ * ∫ s in (0 : ℝ)..P, |etaF s|)
    (hS2 : ∀ x, |etaR2 x| ≤ SF1 / c ^ 2 + 2 * kh ^ 2 * SF0 / c ^ 3 +
      (SF0 / c + (1 - Real.exp (-l0))⁻¹ * ∫ s in (0 : ℝ)..P, |etaF s|))
    (hnorm0 : SF0 ≤ supNorm (fun u => etaF (P * u)))
    (hnorm1 : P * SF1 ≤ supNorm (iteratedDeriv 1 fun u => etaF (P * u))) :
    Bounds (fun u => etaF (P * u)) etaR
      (P / (1 - Real.exp (-l0))) (1 / c)
      (P / (1 - Real.exp (-l0)))
      (2 * kh ^ 2 / c ^ 3 + 1 / c) (1 / (P * c ^ 2)) := by
  have hden : 0 < 1 - Real.exp (-l0) := one_sub_exp_pos hl0
  have hL1 : (∫ s in (0 : ℝ)..P, |etaF s|) =
      P * ∫ u in (0 : ℝ)..1, |etaF (P * u)| := by
    rw [integral_abs_comp_mul hP.ne' etaF]
    field_simp
  let WF := ∫ u in (0 : ℝ)..1, |etaF (P * u)|
  let S0F := supNorm (fun u => etaF (P * u))
  let S1F := supNorm (iteratedDeriv 1 fun u => etaF (P * u))
  have hSF1 : SF1 ≤ S1F / P := by
    rw [le_div_iff₀ hP, mul_comm]
    exact hnorm1
  have hd1 : deriv etaR = etaR1 := funext fun x => (hR1 x).deriv
  have hd2 : deriv (deriv etaR) = etaR2 := by
    rw [hd1]
    exact funext fun x => (hR2 x).deriv
  refine { s1 := ?_, s2 := ?_ }
  · refine supNorm_le_of_forall fun x => ?_
    rw [hd1]
    refine (hS1 x).trans ?_
    rw [hL1]
    have h0 : SF0 / c ≤ (1 / c) * S0F := by
      rw [one_div, inv_mul_eq_div, div_le_div_iff_of_pos_right hc]
      exact hnorm0
    have hw : (1 - Real.exp (-l0))⁻¹ * (P * WF) =
        (P / (1 - Real.exp (-l0))) * WF := by field_simp
    rw [hw]
    linarith
  · refine supNorm_le_of_forall fun x => ?_
    rw [hd2]
    refine (hS2 x).trans ?_
    rw [hL1]
    have hs1 : SF1 / c ^ 2 ≤ (1 / (P * c ^ 2)) * S1F := by
      have hc2 : 0 < c ^ 2 := sq_pos_of_pos hc
      rw [div_le_iff₀ hc2]
      calc
        SF1 ≤ S1F / P := hSF1
        _ = (1 / (P * c ^ 2)) * S1F * c ^ 2 := by field_simp
    have hs0a : 2 * kh ^ 2 * SF0 / c ^ 3 ≤
        (2 * kh ^ 2 / c ^ 3) * S0F := by
      calc
        2 * kh ^ 2 * SF0 / c ^ 3 ≤ 2 * kh ^ 2 * S0F / c ^ 3 :=
          div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_left hnorm0
              (mul_nonneg (by norm_num) (sq_nonneg kh)))
            (pow_nonneg hc.le 3)
        _ = (2 * kh ^ 2 / c ^ 3) * S0F := by ring
    have hs0b : SF0 / c ≤ (1 / c) * S0F := by
      rw [one_div, inv_mul_eq_div, div_le_div_iff_of_pos_right hc]
      exact hnorm0
    have hw : (1 - Real.exp (-l0))⁻¹ * (P * WF) =
        (P / (1 - Real.exp (-l0))) * WF := by field_simp
    rw [hw]
    linarith

/-- Uniformize only the increasing/decreasing coefficient in which the front
period occurs; the lower-component coefficients remain separate. -/
def uniform
    {front rear : ℝ → ℝ} {P P0 P1 l0 c kh : ℝ}
    (B : Bounds front rear
      (P / (1 - Real.exp (-l0))) (1 / c)
      (P / (1 - Real.exp (-l0)))
      (2 * kh ^ 2 / c ^ 3 + 1 / c) (1 / (P * c ^ 2)))
    (hP0 : 0 < P0) (hl0 : 0 < l0) (hc : 0 < c)
    (hlo : P0 ≤ P) (hhi : P ≤ P1) :
    Bounds front rear
      (P1 / (1 - Real.exp (-l0))) (1 / c)
      (P1 / (1 - Real.exp (-l0)))
      (2 * kh ^ 2 / c ^ 3 + 1 / c) (1 / (P0 * c ^ 2)) := by
  have hden : 0 < 1 - Real.exp (-l0) := one_sub_exp_pos hl0
  have hP : 0 < P := hP0.trans_le hlo
  have hinc : P / (1 - Real.exp (-l0)) ≤ P1 / (1 - Real.exp (-l0)) :=
    div_le_div_of_nonneg_right hhi hden.le
  have hdec : 1 / (P * c ^ 2) ≤ 1 / (P0 * c ^ 2) := by
    apply one_div_le_one_div_of_le (mul_pos hP0 (sq_pos_of_pos hc))
    exact mul_le_mul_of_nonneg_right hlo (sq_nonneg c)
  have hw : 0 ≤ ∫ u in (0 : ℝ)..1, |front u| :=
    intervalIntegral.integral_nonneg zero_le_one (fun _ _ => abs_nonneg _)
  have hs0 : 0 ≤ supNorm front := supNorm_nonneg _
  have hs1 : 0 ≤ supNorm (iteratedDeriv 1 front) := supNorm_nonneg _
  refine
    { s1 := B.s1.trans (add_le_add
        (mul_le_mul_of_nonneg_right hinc hw) le_rfl)
      s2 := B.s2.trans (add_le_add (add_le_add
        (mul_le_mul_of_nonneg_right hinc hw) le_rfl)
        (mul_le_mul_of_nonneg_right hdec hs1)) }

end JacobiArclengthSeparated
