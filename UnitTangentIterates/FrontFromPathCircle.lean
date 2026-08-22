import Mathlib
import UnitTangentIterates.FrontFromPath
import UnitTangentIterates.PathMetricCircle

/-!
# The family of fronts of the dilation of a circle

`FrontFromPath.exists_front_of_path` identifies the slices of a normal path
with a family of fronts, provided they are closed curves of constant speed and
turning number one moving along their standard unit normal.  This file checks
that those hypotheses are consistent, on the radial dilation of
`PathMetricCircle`: the circles of radius

```
  ρ(t) = r + (R - r) B(t)
```

joining the circle of radius `r` to the circle of radius `R`, moving along
their *inward* normal `i τ` (the normal of the front convention, `ν = i e^{iΘ}`
for the counterclockwise parametrization).

* `dilationIn` : the dilation as a normal path with the inward normal;
* `front_of_dilation` : the family of fronts of that path — the hypotheses of
  `FrontFromPath.exists_front_of_path` all hold, with perimeter `2πρ(t)`.
-/

noncomputable section

open Set Function Complex MeasureTheory MarkedSpace PathMetric PathMetric.NormalPath
  PathMetricCircle

namespace FrontFromPathCircle

/-! ### The time profile stays in `[0,1]` -/

theorem w_eq_zero_of_nonpos {x : ℝ} (hx : x ≤ 0) : w x = 0 := by
  refine w_eq_zero (fun hmem => ?_)
  exact absurd hmem.1 (not_lt.mpr hx)

theorem w_eq_zero_of_one_le {x : ℝ} (hx : (1 : ℝ) ≤ x) : w x = 0 := by
  refine w_eq_zero (fun hmem => ?_)
  exact absurd hmem.2 (not_lt.mpr hx)

theorem B_monotone : Monotone B := by
  intro a b hab
  have h : B a + (∫ x in a..b, w x) = B b :=
    intervalIntegral.integral_add_adjacent_intervals
      (continuous_w.intervalIntegrable _ _) (continuous_w.intervalIntegrable _ _)
  have hpos : (0 : ℝ) ≤ ∫ x in a..b, w x :=
    intervalIntegral.integral_nonneg hab (fun x _ => w_nonneg x)
  linarith

theorem B_eq_zero_of_nonpos {t : ℝ} (ht : t ≤ 0) : B t = 0 := by
  have h : (∫ x in (0 : ℝ)..t, w x) = ∫ _x in (0 : ℝ)..t, (0 : ℝ) := by
    refine intervalIntegral.integral_congr (fun x hx => ?_)
    rw [uIcc_of_ge ht] at hx
    exact w_eq_zero_of_nonpos hx.2
  rw [B, h]
  simp

theorem B_eq_one_of_one_le {t : ℝ} (ht : (1 : ℝ) ≤ t) : B t = 1 := by
  have hsplit : (∫ x in (0 : ℝ)..t, w x)
      = (∫ x in (0 : ℝ)..1, w x) + ∫ x in (1 : ℝ)..t, w x :=
    (intervalIntegral.integral_add_adjacent_intervals
      (continuous_w.intervalIntegrable _ _) (continuous_w.intervalIntegrable _ _)).symm
  have hzero : (∫ x in (1 : ℝ)..t, w x) = ∫ _x in (1 : ℝ)..t, (0 : ℝ) := by
    refine intervalIntegral.integral_congr (fun x hx => ?_)
    rw [uIcc_of_le ht] at hx
    exact w_eq_zero_of_one_le hx.1
  rw [B, hsplit, hzero, integral_w]
  simp

theorem B_mem_Icc (t : ℝ) : B t ∈ Icc (0 : ℝ) 1 := by
  constructor
  · rcases le_or_gt t 0 with h | h
    · rw [B_eq_zero_of_nonpos h]
    · have := B_monotone h.le
      rwa [B_zero] at this
  · rcases le_or_gt 1 t with h | h
    · rw [B_eq_one_of_one_le h]
    · have := B_monotone h.le
      rwa [B_one] at this

/-! ### The dilation with the inward normal -/

/-- The radius of the dilating circle at time `t`. -/
def rho (r R : ℝ) (t : ℝ) : ℝ := r + (R - r) * B t

theorem rho_pos {r R : ℝ} (hr : 0 < r) (hR : 0 < R) (t : ℝ) : 0 < rho r R t := by
  obtain ⟨h0, h1⟩ := B_mem_Icc t
  rcases le_total r R with h | h
  · have : r ≤ rho r R t := by
      have : 0 ≤ (R - r) * B t := mul_nonneg (by linarith) h0
      simp only [rho]; linarith
    linarith
  · have : R ≤ rho r R t := by
      have : (R - r) * B t ≥ (R - r) * 1 := by
        apply mul_le_mul_of_nonpos_left h1 (by linarith)
      simp only [rho]; linarith
    linarith

/-- **The radial dilation with the inward normal.**  The same moving family of
circles as `PathMetricCircle.dilation`, written with the unit normal
`ν = i τ` of the front convention; the normal speed changes sign accordingly. -/
def dilationIn (r R : ℝ) : NormalPath (circleData r) (circleData R) where
  T := 1
  T_pos := one_pos
  X := fun t u => ((rho r R t : ℝ) : ℂ) * normExp u
  eta := fun t _ => -((R - r) * w t)
  nu := fun _ u => -normExp u
  m := fun t => |R - r| * w t
  start := fun u => by simp [rho, B_zero]
  finish := fun u => by simp [rho, B_one]
  hasDerivAt_time := by
    intro t u
    have hB : HasDerivAt (fun s => rho r R s) ((R - r) * w t) t :=
      (((hasDerivAt_B t).const_mul (R - r)).const_add r)
    have h := (hB.ofReal_comp.mul_const (normExp u))
    refine h.congr_deriv ?_
    push_cast
    ring
  cont_vel := fun u => by
    have h : Continuous fun t : ℝ => (-((R - r) * w t) : ℝ) :=
      (continuous_const.mul continuous_w).neg
    exact (Complex.continuous_ofReal.comp h).mul continuous_const
  norm_nu := fun _ u => by simp
  cont_m := continuous_const.mul continuous_w
  m_nonneg := fun t => mul_nonneg (abs_nonneg _) (w_nonneg t)
  m_stop := fun t ht => by rw [w_eq_zero ht, mul_zero]
  abs_eta_le := fun t _ => by
    rw [abs_neg, abs_mul, abs_of_nonneg (w_nonneg t)]
  le_m_L1 := fun t => by
    have h : (∫ _u in (0:ℝ)..1, |-((R - r) * w t)|) = |-((R - r) * w t)| := by simp
    rw [h, abs_neg, abs_mul, abs_of_nonneg (w_nonneg t)]
  le_m_sup := fun t j _ => by
    match j with
    | 0 =>
      rw [iteratedDeriv_zero, supNorm_const, abs_neg, abs_mul, abs_of_nonneg (w_nonneg t)]
    | (n + 1) =>
      rw [iteratedDeriv_succ_const, supNorm_const]
      simpa using mul_nonneg (abs_nonneg (R - r)) (w_nonneg t)

theorem dilationIn_X (r R : ℝ) (t u : ℝ) :
    (dilationIn r R).X t u = ((rho r R t : ℝ) : ℂ) * normExp u := rfl

theorem dilationIn_nu (r R : ℝ) (t u : ℝ) : (dilationIn r R).nu t u = -normExp u := rfl

/-! ### The family of fronts of the dilation -/

/-- **The dilation is a path of fronts.**  All the hypotheses of
`FrontFromPath.exists_front_of_path` hold for the dilating family of circles of
radius `ρ(t)`, with velocity and acceleration the derivatives of the slices in
the normalized parameter and with perimeter `P t = 2πρ(t)`: the slices are
closed, of constant speed, of turning number one, and the path moves along the
standard unit normal.  Hence the path *is* a path of fronts. -/
theorem front_of_dilation {r R : ℝ} (hr : 0 < r) (hR : 0 < R) :
    ∃ F : ℝ → ℝ → ℂ, ∃ Θ : ℝ → ℝ → ℝ,
      (∀ t u, (dilationIn r R).X t u = F t (2 * Real.pi * rho r R t * u)) ∧
      (∀ t s, HasDerivAt (F t) (Complex.exp (Complex.I * (Θ t s : ℂ))) s) ∧
      (∀ t u, (dilationIn r R).nu t u
        = Complex.I * Complex.exp (Complex.I * (Θ t (2 * Real.pi * rho r R t * u) : ℂ))) ∧
      (∀ t s, F t (s + 2 * Real.pi * rho r R t) = F t s) ∧
      (∀ t s, Θ t (s + 2 * Real.pi * rho r R t) = Θ t s + 2 * Real.pi) := by
  set P : ℝ → ℝ := fun t => 2 * Real.pi * rho r R t with hP
  set V : ℝ → ℝ → ℂ := fun t u => ((P t : ℝ) : ℂ) * Complex.I * normExp u with hV
  set A : ℝ → ℝ → ℂ := fun t u => -((2 * Real.pi * P t : ℝ) : ℂ) * normExp u with hA
  have hPpos : ∀ t, 0 < P t := fun t => by
    have := rho_pos hr hR t
    have hpi := Real.pi_pos
    simp only [hP]
    positivity
  refine FrontFromPath.exists_front_of_path (V := V) (A := A) (P := P) (dilationIn r R)
    ?_ ?_ ?_ ?_ hPpos ?_ ?_ ?_ ?_ ?_
  · -- the velocity of a slice
    intro t u
    have h := (hasDerivAt_normExp u).const_mul ((rho r R t : ℝ) : ℂ)
    have hfun : (dilationIn r R).X t = fun u => ((rho r R t : ℝ) : ℂ) * normExp u := rfl
    rw [hfun]
    refine h.congr_deriv ?_
    simp only [hV, hP]
    push_cast
    ring
  · -- the acceleration of a slice
    intro t u
    have h := (hasDerivAt_normExp u).const_mul (((P t : ℝ) : ℂ) * Complex.I)
    have hfun : V t = fun u => ((P t : ℝ) : ℂ) * Complex.I * normExp u := rfl
    rw [hfun]
    refine h.congr_deriv ?_
    simp only [hA, hP]
    push_cast
    ring_nf
    rw [Complex.I_sq]
    ring
  · intro t
    exact (continuous_const.mul continuous_normExp)
  · -- the speed is the perimeter
    intro t u
    simp only [hV, norm_mul, Complex.norm_I, norm_normExp, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (hPpos t)]
    ring
  · intro t u
    simp only [dilationIn_X]
    rw [periodic_normExp u]
  · intro t u
    simp only [hV]
    rw [periodic_normExp u]
  · intro t u
    simp only [hA]
    rw [periodic_normExp u]
  · -- the turning number is one
    intro t
    have hval : ∀ u : ℝ, ((starRingEnd ℂ) (V t u) * A t u).im / P t ^ 2 = 2 * Real.pi := by
      intro u
      have hc : (starRingEnd ℂ) (V t u) * A t u
          = ((P t * (2 * Real.pi * P t) : ℝ) : ℂ) * Complex.I
            * ((starRingEnd ℂ) (normExp u) * normExp u) := by
        simp only [hV, hA, map_mul, Complex.conj_I, Complex.conj_ofReal]
        push_cast
        ring
      rw [hc, conj_mul_normExp, mul_one]
      have : (((P t * (2 * Real.pi * P t) : ℝ) : ℂ) * Complex.I).im
          = P t * (2 * Real.pi * P t) := by
        simp
      rw [this]
      have hne := (hPpos t).ne'
      field_simp
    simp only [hval]
    simp
  · -- the path moves along the standard unit normal
    intro t u
    have hPne : ((P t : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (hPpos t).ne'
    rw [dilationIn_nu]
    simp only [hV]
    field_simp
    rw [Complex.I_sq]
    ring

end FrontFromPathCircle
