import Mathlib
import UnitTangentIterates.JacobiNormalized

/-!
# The inverse Jacobi estimates with the rear kept in arclength

`JacobiNormalized.lean` rewrites the four estimates of
`JacobiAssembly.jacobi_estimates` with **both** sides in the normalized
parameter, which is what `PathMetricJacobi.exists_normalPath_of_jacobi`
consumes.  That normalization of the rear presupposes that the rear family
moves normally in the linear parameter `x = ℓu`, which it does not: the family
of selected rears must first be put in the normal gauge, and the gauge
parameter is not the linear one.

`GaugeNormalPath.exists_normalPath_of_gauge_jacobi` performs that step, and it
consumes the four estimates with the **rear side in arclength** and only the
front side normalized.  This file states them in exactly that shape:

```
  ‖η_R‖_{L¹(0,ℓ)} ≤ P·W,   ‖η_R‖_∞ ≤ (P/(1-e^{-ℓ₀}))·W,
  ‖η_R'‖_∞ ≤ (1/c + P/(1-e^{-ℓ₀}))·(W + S₀),
  ‖η_R''‖_∞ ≤ (1/(Pc²) + 2κ̂²/c³ + 1/c + P/(1-e^{-ℓ₀}))·(W + S₀ + S₁),
```

`W`, `S₀`, `S₁` being the densities of the front in the normalized parameter.

Main result: `jacobi_estimates_arclength`.
-/

noncomputable section

open MeasureTheory intervalIntegral MarkedTopology

namespace JacobiArclength

open JacobiNormalized

/-- A pointwise bound gives a bound for the sup norm. -/
theorem supNorm_le_of_forall {f : ℝ → ℝ} {M : ℝ} (h : ∀ x, |f x| ≤ M) : supNorm f ≤ M :=
  ciSup_le h

/-! ### The constants -/

/-- The `L¹` constant with the rear in arclength: the front period. -/
def arcW (P : ℝ) : ℝ := P

/-- The `L¹ → L^∞` constant with the rear in arclength. -/
def arc0 (P l0 : ℝ) : ℝ := P / (1 - Real.exp (-l0))

/-- The first-order constant with the rear in arclength. -/
def arc1 (P l0 c : ℝ) : ℝ := 1 / c + P / (1 - Real.exp (-l0))

/-- The second-order constant with the rear in arclength. -/
def arc2 (P l0 c kh : ℝ) : ℝ :=
  1 / (P * c ^ 2) + 2 * kh ^ 2 / c ^ 3 + 1 / c + P / (1 - Real.exp (-l0))

theorem arcW_nonneg {P : ℝ} (hP : 0 < P) : 0 ≤ arcW P := hP.le

theorem arc0_nonneg {P l0 : ℝ} (hP : 0 < P) (hl0 : 0 < l0) : 0 ≤ arc0 P l0 := by
  have := one_sub_exp_pos hl0
  unfold arc0; positivity

theorem arc1_nonneg {P l0 c : ℝ} (hP : 0 < P) (hl0 : 0 < l0) (hc : 0 < c) :
    0 ≤ arc1 P l0 c := by
  have := one_sub_exp_pos hl0
  unfold arc1; positivity

theorem arc2_nonneg {P l0 c kh : ℝ} (hP : 0 < P) (hl0 : 0 < l0) (hc : 0 < c) :
    0 ≤ arc2 P l0 c kh := by
  have := one_sub_exp_pos hl0
  unfold arc2; positivity

/-! ### The estimates -/

/-- **The inverse Jacobi estimates with the rear in arclength.**  The four
estimates of `JacobiAssembly.jacobi_estimates` — whose right-hand sides involve
the arclength `L¹` norm of the front velocity and its arclength sup bounds
`SF0`, `SF1` — rewritten with the front side in the normalized parameter, the
rear side being left in its own arclength.  This is the shape consumed by
`GaugeNormalPath.exists_normalPath_of_gauge_jacobi`. -/
theorem jacobi_estimates_arclength {l P l0 c kh SF0 SF1 : ℝ}
    {etaR etaR1 etaR2 etaF : ℝ → ℝ}
    (hP : 0 < P) (hl0 : 0 < l0) (hc : 0 < c)
    (hR1 : ∀ x, HasDerivAt etaR (etaR1 x) x) (hR2 : ∀ x, HasDerivAt etaR1 (etaR2 x) x)
    (hSF0 : 0 ≤ SF0)
    (hW : (∫ x in (0:ℝ)..l, |etaR x|) ≤ ∫ s in (0:ℝ)..P, |etaF s|)
    (hS0 : ∀ x, |etaR x| ≤ (1 - Real.exp (-l0))⁻¹ * ∫ s in (0:ℝ)..P, |etaF s|)
    (hS1 : ∀ x, |etaR1 x|
      ≤ SF0 / c + (1 - Real.exp (-l0))⁻¹ * ∫ s in (0:ℝ)..P, |etaF s|)
    (hS2 : ∀ x, |etaR2 x| ≤ SF1 / c ^ 2 + 2 * kh ^ 2 * SF0 / c ^ 3
      + (SF0 / c + (1 - Real.exp (-l0))⁻¹ * ∫ s in (0:ℝ)..P, |etaF s|))
    (hnorm0 : SF0 ≤ supNorm (fun u => etaF (P * u)))
    (hnorm1 : P * SF1 ≤ supNorm (iteratedDeriv 1 fun u => etaF (P * u))) :
    (∫ x in (0:ℝ)..l, |etaR x|) ≤ arcW P * ∫ u in (0:ℝ)..1, |etaF (P * u)|
      ∧ supNorm etaR ≤ arc0 P l0 * ∫ u in (0:ℝ)..1, |etaF (P * u)|
      ∧ supNorm (deriv etaR) ≤ arc1 P l0 c * ((∫ u in (0:ℝ)..1, |etaF (P * u)|)
          + supNorm (fun u => etaF (P * u)))
      ∧ supNorm (deriv (deriv etaR)) ≤ arc2 P l0 c kh
          * ((∫ u in (0:ℝ)..1, |etaF (P * u)|) + supNorm (fun u => etaF (P * u))
            + supNorm (iteratedDeriv 1 fun u => etaF (P * u))) := by
  have hexp := one_sub_exp_pos hl0
  -- the front `L¹` norm in the two normalizations
  have hL1 : (∫ s in (0:ℝ)..P, |etaF s|) = P * ∫ u in (0:ℝ)..1, |etaF (P * u)| := by
    rw [integral_abs_comp_mul hP.ne' etaF]
    field_simp
  set WF : ℝ := ∫ u in (0:ℝ)..1, |etaF (P * u)| with hWF
  set S0F : ℝ := supNorm (fun u => etaF (P * u)) with hS0F
  set S1F : ℝ := supNorm (iteratedDeriv 1 fun u => etaF (P * u)) with hS1F
  have hWFnn : 0 ≤ WF := intervalIntegral.integral_nonneg zero_le_one (fun u _ => abs_nonneg _)
  have hS0Fnn : 0 ≤ S0F := supNorm_nonneg _
  have hS1Fnn : 0 ≤ S1F := supNorm_nonneg _
  have hSF1 : SF1 ≤ S1F / P := by
    rw [le_div_iff₀ hP, mul_comm]
    exact hnorm1
  -- the derivatives of the rear velocity
  have hd1 : deriv etaR = etaR1 := funext fun x => (hR1 x).deriv
  have hd2 : deriv (deriv etaR) = etaR2 := by
    rw [hd1]; exact funext fun x => (hR2 x).deriv
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hL1] at hW; simpa [arcW, hWF] using hW
  · refine supNorm_le_of_forall (fun x => le_trans (hS0 x) ?_)
    rw [hL1, arc0]
    apply le_of_eq
    field_simp
  · refine supNorm_le_of_forall (fun x => ?_)
    rw [hd1]
    refine le_trans (hS1 x) ?_
    rw [hL1, arc1]
    have h1 : SF0 / c ≤ (1 / c) * S0F := by
      rw [one_div, inv_mul_eq_div, div_le_div_iff_of_pos_right hc]
      exact hnorm0
    have h2 : (1 - Real.exp (-l0))⁻¹ * (P * WF) = (P / (1 - Real.exp (-l0))) * WF := by
      field_simp
    have h3 : (1 / c) * S0F ≤ (1 / c) * (WF + S0F) := by
      have : (0:ℝ) ≤ 1 / c := by positivity
      nlinarith
    have h4 : (P / (1 - Real.exp (-l0))) * WF
        ≤ (P / (1 - Real.exp (-l0))) * (WF + S0F) := by
      have hpn : (0:ℝ) ≤ P / (1 - Real.exp (-l0)) := by positivity
      nlinarith
    calc SF0 / c + (1 - Real.exp (-l0))⁻¹ * (P * WF)
        = SF0 / c + (P / (1 - Real.exp (-l0))) * WF := by rw [h2]
      _ ≤ (1 / c) * (WF + S0F) + (P / (1 - Real.exp (-l0))) * (WF + S0F) := by
          linarith
      _ = (1 / c + P / (1 - Real.exp (-l0))) * (WF + S0F) := by ring
  · refine supNorm_le_of_forall (fun x => ?_)
    rw [hd2]
    refine le_trans (hS2 x) ?_
    rw [hL1, arc2]
    have hB : (0:ℝ) ≤ WF + S0F + S1F := by linarith
    have h1 : SF1 / c ^ 2 ≤ (1 / (P * c ^ 2)) * S1F := by
      have hcc : (0:ℝ) < c ^ 2 := by positivity
      rw [div_le_iff₀ hcc]
      have : SF1 ≤ S1F / P := hSF1
      have hfac : (1 / (P * c ^ 2)) * S1F * c ^ 2 = S1F / P := by
        field_simp
      rw [hfac]
      exact this
    have h2 : 2 * kh ^ 2 * SF0 / c ^ 3 ≤ (2 * kh ^ 2 / c ^ 3) * S0F := by
      have hc3 : (0:ℝ) < c ^ 3 := by positivity
      rw [div_le_iff₀ hc3]
      have hk : (0:ℝ) ≤ 2 * kh ^ 2 / c ^ 3 := by positivity
      have : 2 * kh ^ 2 * SF0 ≤ 2 * kh ^ 2 * S0F := by nlinarith [sq_nonneg kh]
      calc 2 * kh ^ 2 * SF0 ≤ 2 * kh ^ 2 * S0F := this
        _ = (2 * kh ^ 2 / c ^ 3) * S0F * c ^ 3 := by field_simp
    have h3 : SF0 / c ≤ (1 / c) * S0F := by
      rw [one_div, inv_mul_eq_div, div_le_div_iff_of_pos_right hc]
      exact hnorm0
    have h4 : (1 - Real.exp (-l0))⁻¹ * (P * WF) = (P / (1 - Real.exp (-l0))) * WF := by
      field_simp
    have hA1 : (0:ℝ) ≤ 1 / (P * c ^ 2) := by positivity
    have hA2 : (0:ℝ) ≤ 2 * kh ^ 2 / c ^ 3 := by positivity
    have hA3 : (0:ℝ) ≤ 1 / c := by positivity
    have hA4 : (0:ℝ) ≤ P / (1 - Real.exp (-l0)) := by positivity
    calc SF1 / c ^ 2 + 2 * kh ^ 2 * SF0 / c ^ 3
          + (SF0 / c + (1 - Real.exp (-l0))⁻¹ * (P * WF))
        ≤ (1 / (P * c ^ 2)) * S1F + (2 * kh ^ 2 / c ^ 3) * S0F
            + ((1 / c) * S0F + (P / (1 - Real.exp (-l0))) * WF) := by
          rw [h4] at *
          linarith
      _ ≤ (1 / (P * c ^ 2)) * (WF + S0F + S1F) + (2 * kh ^ 2 / c ^ 3) * (WF + S0F + S1F)
            + ((1 / c) * (WF + S0F + S1F)
              + (P / (1 - Real.exp (-l0))) * (WF + S0F + S1F)) := by
          have e1 : (1 / (P * c ^ 2)) * S1F ≤ (1 / (P * c ^ 2)) * (WF + S0F + S1F) := by
            nlinarith
          have e2 : (2 * kh ^ 2 / c ^ 3) * S0F
              ≤ (2 * kh ^ 2 / c ^ 3) * (WF + S0F + S1F) := by nlinarith
          have e3 : (1 / c) * S0F ≤ (1 / c) * (WF + S0F + S1F) := by nlinarith
          have e4 : (P / (1 - Real.exp (-l0))) * WF
              ≤ (P / (1 - Real.exp (-l0))) * (WF + S0F + S1F) := by nlinarith
          linarith
      _ = (1 / (P * c ^ 2) + 2 * kh ^ 2 / c ^ 3 + 1 / c + P / (1 - Real.exp (-l0)))
            * (WF + S0F + S1F) := by ring

/-! ### Non-vacuity

The hypotheses of `jacobi_estimates_arclength` are simultaneously satisfiable
with a nonzero front: take the rear velocity identically zero and the front
velocity identically one. -/

example :
    (∫ x in (0:ℝ)..(1:ℝ), |(fun _ : ℝ => (0:ℝ)) x|)
        ≤ arcW 1 * ∫ u in (0:ℝ)..1, |(fun _ : ℝ => (1:ℝ)) (1 * u)|
      ∧ supNorm (fun _ : ℝ => (0:ℝ)) ≤ arc0 1 1 * ∫ u in (0:ℝ)..1, |(fun _ : ℝ => (1:ℝ)) (1 * u)|
      ∧ supNorm (deriv (fun _ : ℝ => (0:ℝ)))
          ≤ arc1 1 1 1 * ((∫ u in (0:ℝ)..1, |(fun _ : ℝ => (1:ℝ)) (1 * u)|)
            + supNorm (fun u => (fun _ : ℝ => (1:ℝ)) (1 * u)))
      ∧ supNorm (deriv (deriv (fun _ : ℝ => (0:ℝ)))) ≤ arc2 1 1 1 0
          * ((∫ u in (0:ℝ)..1, |(fun _ : ℝ => (1:ℝ)) (1 * u)|)
            + supNorm (fun u => (fun _ : ℝ => (1:ℝ)) (1 * u))
            + supNorm (iteratedDeriv 1 fun u => (fun _ : ℝ => (1:ℝ)) (1 * u))) := by
  have hzero : supNorm (fun _ : ℝ => (0:ℝ)) = 0 := by simp [MarkedTopology.supNorm]
  refine jacobi_estimates_arclength (l := 1) (kh := 0) (SF0 := 0) (SF1 := 0)
    (etaR1 := fun _ => 0) (etaR2 := fun _ => 0) (etaF := fun _ => 1)
    one_pos one_pos one_pos (fun x => hasDerivAt_const x 0)
    (fun x => hasDerivAt_const x 0) le_rfl ?_ ?_ ?_ ?_ ?_ ?_
  · simp
  · intro x; simp
  · intro x; simp
  · intro x; simp
  · simpa using supNorm_nonneg (fun _ : ℝ => (1:ℝ))
  · simp [iteratedDeriv_succ, iteratedDeriv_zero, hzero]

end JacobiArclength
