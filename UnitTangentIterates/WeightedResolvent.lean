module

public import UnitTangentIterates.Reduction

/-!
# `L¹` and `L^∞` bounds for periodic solutions of `w' + β w = f` (Lemma 6.2, (6.5)–(6.6))

By the Jacobi equation (`Ovals.jacobi_equation`), in the front parameter `u` the rear normal
velocity solves `∂ᵤη_R + β η_R = f` with `β = g cos δ` (the rear speed) and `f = g η_F`.  The
two estimates behind `W(ℬΓ) ≤ W(Γ)` and `S₀(ℬΓ) ≤ C₀ W(Γ)` are, for any continuous periodic
solution and without an explicit resolvent formula:

* `Ovals.integral_mul_abs_le_of_periodic`: `∫₀ᵖ β |w| ≤ ∫₀ᵖ |f|` (`L¹` non-expansion: the left
  side is the `L¹` norm of `η_R` in rear arclength, the right side that of `η_F` in front
  arclength);
* `Ovals.abs_le_integral_of_periodic`: `(1 - e^{-ℓ}) |w(u)| ≤ ∫₀ᵖ |f|`, where `ℓ = ∫₀ᵖ β` is
  the rear perimeter.
-/

@[expose] public section

namespace Ovals

open Real intervalIntegral MeasureTheory

/-- **`L¹` non-expansion.**  If `w` is a `p`-periodic solution of `w' = f - β w` with
`f, β` continuous and `β ≥ 0`, then `∫₀ᵖ β |w| ≤ ∫₀ᵖ |f|`. -/
theorem integral_mul_abs_le_of_periodic {w f β : ℝ → ℝ} {p : ℝ} (hp : 0 < p)
    (hf : Continuous f) (hβ : Continuous β) (hβ0 : ∀ u, 0 ≤ β u)
    (hw : ∀ u, HasDerivAt w (f u - β u * w u) u) (hwp : Function.Periodic w p) :
    ∫ u in (0 : ℝ)..p, β u * |w u| ≤ ∫ u in (0 : ℝ)..p, |f u| := by
  have hwc : Continuous w := continuous_iff_continuousAt.2 fun u => (hw u).continuousAt
  -- for every `ε > 0`, `∫ β |w| ≤ ∫ |f| + ε ∫ β`
  have key : ∀ ε > 0, ∫ u in (0 : ℝ)..p, β u * |w u| ≤
      (∫ u in (0 : ℝ)..p, |f u|) + ε * ∫ u in (0 : ℝ)..p, β u := by
    intro ε hε
    set φ : ℝ → ℝ := fun u => Real.sqrt (w u ^ 2 + ε ^ 2)
    have hpos : ∀ u, 0 < w u ^ 2 + ε ^ 2 := fun u => by positivity
    have hφpos : ∀ u, 0 < φ u := fun u => Real.sqrt_pos.2 (hpos u)
    have hφ : ∀ u, HasDerivAt φ (w u * (f u - β u * w u) / φ u) u := fun u => by
      have h1 : HasDerivAt (fun u => w u ^ 2 + ε ^ 2) (2 * w u * (f u - β u * w u)) u := by
        have := ((hw u).pow 2).add_const (ε ^ 2)
        convert this using 1; push_cast; ring
      have := h1.sqrt (hpos u).ne'
      convert this using 1
      simp only [φ]
      field_simp
    have hφ'c : Continuous fun u => w u * (f u - β u * w u) / φ u :=
      (hwc.mul (hf.sub (hβ.mul hwc))).div
        (Real.continuous_sqrt.comp ((hwc.pow 2).add continuous_const)) fun u => (hφpos u).ne'
    have hint0 : ∫ u in (0 : ℝ)..p, w u * (f u - β u * w u) / φ u = 0 := by
      rw [integral_eq_sub_of_hasDerivAt (fun u _ => hφ u) (hφ'c.intervalIntegrable _ _)]
      simp only [φ] at *
      rw [show p = 0 + p by ring, hwp 0]; ring
    have hpt : ∀ u, w u * (f u - β u * w u) / φ u ≤ |f u| - β u * |w u| + ε * β u := by
      intro u
      have hφu := hφpos u
      have habs : |w u| ≤ φ u := by
        rw [← Real.sqrt_sq_eq_abs]
        exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg ε])
      have h1 : w u * f u / φ u ≤ |f u| := by
        rw [div_le_iff₀ hφu]
        calc w u * f u ≤ |w u| * |f u| := by rw [← abs_mul]; exact le_abs_self _
          _ ≤ φ u * |f u| := mul_le_mul_of_nonneg_right habs (abs_nonneg _)
          _ = |f u| * φ u := by ring
      have h2 : |w u| - ε ≤ w u ^ 2 / φ u := by
        rw [le_div_iff₀ hφu]
        rcases le_or_gt (|w u|) ε with h | h
        · nlinarith [hφu.le]
        · have hφle : φ u ≤ |w u| + ε := by
            rw [show φ u = Real.sqrt (w u ^ 2 + ε ^ 2) from rfl]
            rw [Real.sqrt_le_left (by positivity)]
            nlinarith [abs_nonneg (w u), sq_abs (w u)]
          nlinarith [sq_abs (w u), mul_le_mul_of_nonneg_left hφle (by linarith : 0 ≤ |w u| - ε)]
      have e : w u * (f u - β u * w u) / φ u = w u * f u / φ u - β u * (w u ^ 2 / φ u) := by
        ring
      rw [e]
      nlinarith [mul_le_mul_of_nonneg_left h2 (hβ0 u)]
    have hc2 : Continuous fun u => |f u| - β u * |w u| + ε * β u :=
      ((continuous_abs.comp hf).sub (hβ.mul (continuous_abs.comp hwc))).add
        (continuous_const.mul hβ)
    have hmono := intervalIntegral.integral_mono_on (μ := volume) hp.le
      (hφ'c.intervalIntegrable 0 p) (hc2.intervalIntegrable 0 p) (fun u _ => hpt u)
    rw [hint0, intervalIntegral.integral_add, intervalIntegral.integral_sub,
      intervalIntegral.integral_const_mul] at hmono
    · linarith
    all_goals first
      | exact (continuous_abs.comp hf).intervalIntegrable _ _
      | exact (hβ.mul (continuous_abs.comp hwc)).intervalIntegrable _ _
      | exact ((continuous_abs.comp hf).sub (hβ.mul (continuous_abs.comp hwc))).intervalIntegrable _ _
      | exact (continuous_const.mul hβ).intervalIntegrable _ _
  have hβint : 0 ≤ ∫ u in (0 : ℝ)..p, β u := intervalIntegral.integral_nonneg hp.le fun u _ => hβ0 u
  refine le_of_forall_pos_lt_add fun ε hε => ?_
  set c := ∫ u in (0 : ℝ)..p, β u
  have := key (ε / (c + 1)) (by positivity)
  have hlt : ε / (c + 1) * c < ε := by
    rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]; nlinarith
  linarith

/-- **`L¹ → L^∞` bound.**  If `w` is a `p`-periodic solution of `w' = f - β w` with `f, β`
continuous, `p`-periodic and `β ≥ 0`, and `ℓ = ∫₀ᵖ β`, then `(1 - e^{-ℓ}) |w u| ≤ ∫₀ᵖ |f|`. -/
theorem abs_le_integral_of_periodic {w f β : ℝ → ℝ} {p : ℝ} (hp : 0 < p)
    (hf : Continuous f) (hβ : Continuous β) (hfp : Function.Periodic f p)
    (hβp : Function.Periodic β p) (hβ0 : ∀ u, 0 ≤ β u)
    (hw : ∀ u, HasDerivAt w (f u - β u * w u) u) (hwp : Function.Periodic w p) (u : ℝ) :
    (1 - Real.exp (-∫ v in (0 : ℝ)..p, β v)) * |w u| ≤ ∫ v in (0 : ℝ)..p, |f v| := by
  set B : ℝ → ℝ := fun v => ∫ r in u..v, β r
  have hB : ∀ v, HasDerivAt B (β v) v := fun v =>
    intervalIntegral.integral_hasDerivAt_right (hβ.intervalIntegrable _ _)
      (hβ.stronglyMeasurableAtFilter _ _) hβ.continuousAt
  set E : ℝ → ℝ := fun v => Real.exp (B v)
  have hwc : Continuous w := continuous_iff_continuousAt.2 fun v => (hw v).continuousAt
  have hEc : Continuous E :=
    Real.continuous_exp.comp (continuous_iff_continuousAt.2 fun v => (hB v).continuousAt)
  have hEw : ∀ v, HasDerivAt (fun v => E v * w v) (E v * f v) v := fun v => by
    have := ((hB v).exp).mul (hw v)
    convert this using 1; simp only [E]; ring
  have hftc := integral_eq_sub_of_hasDerivAt (a := u - p) (b := u) (fun v _ => hEw v)
    ((hEc.mul hf).intervalIntegrable _ _)
  have hBu : B u = 0 := by simp [B]
  have hBup : B (u - p) = -∫ v in (0 : ℝ)..p, β v := by
    simp only [B]
    have := hβp.intervalIntegral_add_eq (u - p) 0
    simp only [sub_add_cancel, zero_add] at this
    rw [intervalIntegral.integral_symm, this]
  simp only [E, hBu, hBup, Real.exp_zero, one_mul] at hftc
  rw [show w (u - p) = w u by rw [← hwp (u - p)]; ring_nf] at hftc
  have hle : |∫ v in (u - p)..u, E v * f v| ≤ ∫ v in (u - p)..u, |f v| := by
    refine (intervalIntegral.abs_integral_le_integral_abs (by linarith)).trans ?_
    refine intervalIntegral.integral_mono_on (by linarith)
      ((continuous_abs.comp (hEc.mul hf)).intervalIntegrable _ _)
      ((continuous_abs.comp hf).intervalIntegrable _ _) fun v hv => ?_
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    have hBv : B v ≤ 0 := by
      have : 0 ≤ ∫ r in v..u, β r := intervalIntegral.integral_nonneg hv.2 fun r _ => hβ0 r
      simp only [B]; rw [intervalIntegral.integral_symm]; linarith
    exact mul_le_of_le_one_left (abs_nonneg _) (Real.exp_le_one_iff.2 hBv)
  have hper : ∫ v in (u - p)..u, |f v| = ∫ v in (0 : ℝ)..p, |f v| := by
    have := (show Function.Periodic (fun v => |f v|) p from fun v => by simp [hfp v])
    have h2 := this.intervalIntegral_add_eq (u - p) 0
    simp only [sub_add_cancel, zero_add] at h2
    exact h2
  have e : (1 - Real.exp (-∫ v in (0 : ℝ)..p, β v)) * w u =
      ∫ v in (u - p)..u, E v * f v := by rw [hftc]; ring
  have h1 : 0 ≤ 1 - Real.exp (-∫ v in (0 : ℝ)..p, β v) := by
    have : 0 ≤ ∫ v in (0 : ℝ)..p, β v := intervalIntegral.integral_nonneg hp.le fun v _ => hβ0 v
    have := Real.exp_le_one_iff.2 (neg_nonpos.2 this)
    linarith
  calc (1 - Real.exp (-∫ v in (0 : ℝ)..p, β v)) * |w u|
      = |(1 - Real.exp (-∫ v in (0 : ℝ)..p, β v)) * w u| := by
        rw [abs_mul, abs_of_nonneg h1]
    _ ≤ _ := by rw [e]; exact hle.trans hper.le

end Ovals

end
