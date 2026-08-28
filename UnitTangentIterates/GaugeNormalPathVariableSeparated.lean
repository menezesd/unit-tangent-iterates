import UnitTangentIterates.GaugeNormalPathVariable
import UnitTangentIterates.GaugeNormalPathSeparated

/-! Separated density transport for a gauge flow with changing slice period. -/

noncomputable section

open Set Function MeasureTheory MarkedSpace MarkedTopology PathMetric

namespace GaugeNormalPathVariableSeparated

open UniformFrameBounds GaugeNormalPath GaugeNormalPathSeparated

theorem flowedBounds
    {p q : Data} (Gamma : NormalPath p q) (D : GaugeFrameData)
    {Phi : ℝ → ℝ → ℝ} {Qf Qf' : ℝ → ℝ}
    (hQpos : ∀ t, 0 < Qf t) (hQd : ∀ t, HasDerivAt Qf (Qf' t) t)
    (hvper : ∀ t, Periodic (D.v t) (Qf t))
    (hxiqp : ∀ t x, D.xi t (x + Qf t) = D.xi t x - Qf' t * D.v t x)
    (hPhid : ∀ u t, HasDerivAt (fun r => Phi r u)
      (GaugeRate.gaugeRate D.xi D.v t (Phi t u)) t)
    (hPhi0 : ∀ u, Phi 0 u = Qf 0 * u)
    {etaR : ℝ → ℝ → ℝ}
    (hetaC2 : ∀ t, ContDiff ℝ (2 : ℕ) (etaR t))
    (hetaper : ∀ t, Periodic (etaR t) (Qf t))
    (hrest : ∀ t ∉ Ioo (0 : ℝ) Gamma.T, etaR t = fun _ => 0)
    {CW C0 A10 A11 A20 A21 A22 : ℝ}
    (hCW : 0 ≤ CW) (hC0 : 0 ≤ C0)
    (hA10 : 0 ≤ A10) (hA11 : 0 ≤ A11)
    (hA20 : 0 ≤ A20) (hA21 : 0 ≤ A21) (hA22 : 0 ≤ A22)
    (hW : ∀ t ∈ Ioo (0 : ℝ) Gamma.T,
      (∫ x in (0 : ℝ)..Qf t, |etaR t x|) ≤
        CW * ∫ u in (0 : ℝ)..1, |Gamma.eta t u|)
    (hS0 : ∀ t ∈ Ioo (0 : ℝ) Gamma.T,
      supNorm (etaR t) ≤ C0 * ∫ u in (0 : ℝ)..1, |Gamma.eta t u|)
    (hsep : ∀ t ∈ Ioo (0 : ℝ) Gamma.T,
      JacobiArclengthSeparated.Bounds (Gamma.eta t) (etaR t)
        A10 A11 A20 A21 A22) :
    FlowedBounds Gamma.eta (fun t u => etaR t (Phi t u))
      (gaugeCW CW D.rateLip Gamma.T (Qf 0)) C0
      (flowFirst A10 D.rateLip Gamma.T (Qf 0))
      (flowFirst A11 D.rateLip Gamma.T (Qf 0))
      (flowSecond A20 D.rateLip Gamma.T (Qf 0) +
        flowDrift A10 D.rateLip D.rateBound2 Gamma.T (Qf 0))
      (flowSecond A21 D.rateLip Gamma.T (Qf 0) +
        flowDrift A11 D.rateLip D.rateBound2 Gamma.T (Qf 0))
      (flowSecond A22 D.rateLip Gamma.T (Qf 0)) := by
  let L := D.rateLip
  let R2 := D.rateBound2
  let T := Gamma.T
  let Q := Qf 0
  have hQ : 0 < Q := hQpos 0
  have hL : 0 ≤ L := D.rateLip_nonneg
  have hR2 : 0 ≤ R2 := D.rateBound2_nonneg
  have hT : 0 < T := Gamma.T_pos
  have hexp : ∀ t ∈ Ioo (0 : ℝ) T,
      Real.exp (L * |t|) ≤ Real.exp (L * T) := by
    intro t ht
    apply Real.exp_le_exp.mpr
    rw [abs_of_pos ht.1]
    exact mul_le_mul_of_nonneg_left ht.2.le hL
  have hdrift : ∀ t ∈ Ioo (0 : ℝ) T,
      R2 * Q ^ 2 * |t| * Real.exp (2 * L * |t|) ≤
        R2 * Q ^ 2 * T * Real.exp (2 * L * T) := by
    intro t ht
    rw [abs_of_pos ht.1]
    exact mul_le_mul
      (mul_le_mul_of_nonneg_left ht.2.le (mul_nonneg hR2 (sq_nonneg Q)))
      (Real.exp_le_exp.mpr
        (mul_le_mul_of_nonneg_left ht.2.le (by positivity : 0 ≤ 2 * L)))
      (Real.exp_pos _).le (by positivity)
  have hWF : ∀ t, 0 ≤ ∫ u in (0 : ℝ)..1, |Gamma.eta t u| := fun t =>
    intervalIntegral.integral_nonneg zero_le_one (fun _ _ => abs_nonneg _)
  have hdens := fun t => GaugeDensitiesVariable.gauge_densities_le_var D
    hQpos hQd hvper hxiqp hPhid hPhi0 t (hetaC2 t) (hetaper t)
  refine { w := ?_, s0 := ?_, s1 := ?_, s2 := ?_ }
  · intro t
    by_cases ht : t ∈ Ioo (0 : ℝ) T
    · calc
        (∫ u in (0 : ℝ)..1, |etaR t (Phi t u)|) ≤
            (Real.exp (L * |t|) / Q) * ∫ x in (0 : ℝ)..Qf t, |etaR t x| :=
          (hdens t).2.2.2
        _ ≤ (Real.exp (L * T) / Q) *
            (CW * ∫ u in (0 : ℝ)..1, |Gamma.eta t u|) := by
          exact mul_le_mul
            (div_le_div_of_nonneg_right (hexp t ht) hQ.le) (hW t ht)
            (intervalIntegral.integral_nonneg (hQpos t).le (fun _ _ => abs_nonneg _))
            (by positivity)
        _ = gaugeCW CW L T Q * ∫ u in (0 : ℝ)..1, |Gamma.eta t u| := by
          simp [gaugeCW]; ring
    · rw [hrest t ht]
      simp only [Pi.zero_apply, abs_zero, intervalIntegral.integral_zero]
      exact mul_nonneg (mul_nonneg hCW (by positivity)) (hWF t)
  · intro t
    by_cases ht : t ∈ Ioo (0 : ℝ) T
    · exact (hdens t).1.trans (hS0 t ht)
    · rw [hrest t ht]
      simp [supNorm]
      exact mul_nonneg hC0 (hWF t)
  · intro t
    by_cases ht : t ∈ Ioo (0 : ℝ) T
    · let w := ∫ u in (0 : ℝ)..1, |Gamma.eta t u|
      let s := supNorm (Gamma.eta t)
      have hw : 0 ≤ w := hWF t
      have hs : 0 ≤ s := supNorm_nonneg _
      have hf : Q * Real.exp (L * |t|) ≤ Q * Real.exp (L * T) :=
        mul_le_mul_of_nonneg_left (hexp t ht) hQ.le
      calc
        supNorm (iteratedDeriv 1 fun u => etaR t (Phi t u)) ≤
            supNorm (deriv (etaR t)) * (Q * Real.exp (L * |t|)) := (hdens t).2.1
        _ ≤ (A10 * w + A11 * s) * (Q * Real.exp (L * T)) :=
          mul_le_mul (hsep t ht).s1 hf (by positivity)
            (add_nonneg (mul_nonneg hA10 hw) (mul_nonneg hA11 hs))
        _ = flowFirst A10 L T Q * w + flowFirst A11 L T Q * s := by
          simp [flowFirst]; ring
    · rw [hrest t ht, iteratedDeriv_zero_fun]
      have h10 : 0 ≤ flowFirst A10 L T Q := by
        unfold flowFirst
        exact mul_nonneg hA10 (mul_nonneg hQ.le (Real.exp_pos _).le)
      have h11 : 0 ≤ flowFirst A11 L T Q := by
        unfold flowFirst
        exact mul_nonneg hA11 (mul_nonneg hQ.le (Real.exp_pos _).le)
      simpa [supNorm] using add_nonneg (mul_nonneg h10 (hWF t))
        (mul_nonneg h11 (supNorm_nonneg (Gamma.eta t)))
  · intro t
    by_cases ht : t ∈ Ioo (0 : ℝ) T
    · let w := ∫ u in (0 : ℝ)..1, |Gamma.eta t u|
      let s0 := supNorm (Gamma.eta t)
      let s1 := supNorm (iteratedDeriv 1 (Gamma.eta t))
      have hw : 0 ≤ w := hWF t
      have hs0 : 0 ≤ s0 := supNorm_nonneg _
      have hs1 : 0 ≤ s1 := supNorm_nonneg _
      have hf : (Q * Real.exp (L * |t|)) ^ 2 ≤
          (Q * Real.exp (L * T)) ^ 2 := by
        have hfac := mul_le_mul_of_nonneg_left (hexp t ht) hQ.le
        nlinarith [mul_nonneg hQ.le (Real.exp_pos (L * |t|)).le]
      let A := A20 * w + A21 * s0 + A22 * s1
      let B := A10 * w + A11 * s0
      have hA : 0 ≤ A := by dsimp [A]; positivity
      have hB : 0 ≤ B := by dsimp [B]; positivity
      calc
        supNorm (iteratedDeriv 2 fun u => etaR t (Phi t u)) ≤
            supNorm (deriv (deriv (etaR t))) * (Q * Real.exp (L * |t|)) ^ 2 +
              supNorm (deriv (etaR t)) *
                (R2 * Q ^ 2 * |t| * Real.exp (2 * L * |t|)) := (hdens t).2.2.1
        _ ≤ A * (Q * Real.exp (L * T)) ^ 2 +
              B * (R2 * Q ^ 2 * T * Real.exp (2 * L * T)) :=
          add_le_add (mul_le_mul (hsep t ht).s2 hf (by positivity) hA)
            (mul_le_mul (hsep t ht).s1 (hdrift t ht) (by positivity) hB)
        _ = (flowSecond A20 L T Q + flowDrift A10 L R2 T Q) * w +
              (flowSecond A21 L T Q + flowDrift A11 L R2 T Q) * s0 +
              flowSecond A22 L T Q * s1 := by
          simp [A, B, flowSecond, flowDrift]; ring
    · rw [hrest t ht, iteratedDeriv_zero_fun]
      have h20 : 0 ≤ flowSecond A20 L T Q + flowDrift A10 L R2 T Q := by
        unfold flowSecond flowDrift
        positivity
      have h21 : 0 ≤ flowSecond A21 L T Q + flowDrift A11 L R2 T Q := by
        unfold flowSecond flowDrift
        positivity
      have h22 : 0 ≤ flowSecond A22 L T Q := by
        unfold flowSecond
        positivity
      simpa [supNorm] using add_nonneg
        (add_nonneg (mul_nonneg h20 (hWF t))
          (mul_nonneg h21 (supNorm_nonneg (Gamma.eta t))))
        (mul_nonneg h22 (supNorm_nonneg (iteratedDeriv 1 (Gamma.eta t))))

end GaugeNormalPathVariableSeparated
