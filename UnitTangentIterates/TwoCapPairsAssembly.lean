import Mathlib
import UnitTangentIterates.CurvatureInterpolation
import UnitTangentIterates.RearTrack

/-!
# Exact two-cap pairs, assembled

This file assembles the pieces of the proposition *Exact two-cap pairs* of
*A Noncircular Oval with Convex Unit-Tangent Iterates* into statements about
the pair of curves themselves:

> Choose `Θ_H` with `Θ_H' = K_H` and define the unit-speed front by
> `F_H' = τ(Θ_H)`.  Because `δ_H` is periodic and `∫₀^H Y_H = π`, the front
> tangent reverses after one `H`-period, and `F_H` closes after two periods.
> Set `Ψ_H = Θ_H − δ_H` and `R_H = F_H − τ(Ψ_H)`.  Then `Ψ_H' = Y_H` and
> `R_H' = c_H τ(Ψ_H)`, so `R_H` is the rear track, has half-perimeter `P(H)`
> and also closes after two periods.  Both curves are centrally symmetric.

The front is the explicit curve of `UnitTangentIterates/CurvatureInterpolation.lean`
built from an `H`-periodic front curvature `K` of total turning `π` over one
period, and the rear is the reconstruction of `UnitTangentIterates/RearTrack.lean`
from a steering solution `δ` of `δ_s = K − sin δ`.

Main results, for such a pair:

* `front_hasDerivAt`, `front_unit_speed`, `front_periodic`,
  `front_add_halfPeriod` : the front is unit speed, `2H`-periodic and
  centrally symmetric;
* `rear_hasDerivAt` : `R' = cos δ · e^{iΨ}`;
* `unitTangent_rear_eq_front` : `R + e^{iΨ} = F`, and
  `unitTangentMap_rear_eq_front` : `𝒯R = F` once `cos δ > 0`;
* `rear_add_halfPeriod`, `rear_periodic` : the rear is centrally symmetric and
  closes after two periods;
* `front_perimeter` : the front perimeter is `2H`;
* `rear_perimeter` : the rear perimeter is `2∫₀^H cos δ = 2P(H)`.
-/

noncomputable section

open Real MeasureTheory intervalIntegral

namespace TwoCapPairsAssembly

open CurvatureInterpolation RearTrack

variable {kappa delta : ℝ → ℝ} {theta0 H : ℝ}

/-- The front tangent angle of the pair. -/
def frontAngle (kappa : ℝ → ℝ) (theta0 : ℝ) : ℝ → ℝ := tangentAngle kappa theta0

/-- The front curve of the pair. -/
def front (kappa : ℝ → ℝ) (theta0 H : ℝ) : ℝ → ℂ := interpCurve kappa theta0 H

/-- The rear curve of the pair. -/
def rear (kappa delta : ℝ → ℝ) (theta0 H : ℝ) : ℝ → ℂ :=
  rearTrack (front kappa theta0 H) (frontAngle kappa theta0) delta

/-- `τ(θ) = e^{iθ}`: the two conventions of the project agree. -/
theorem tau_eq_exp (x : ℝ) : tau x = Complex.exp (Complex.I * (x : ℂ)) := by
  rw [tau, mul_comm]

/-! ### The front -/

/-- The front is the unit-speed curve with tangent angle `Θ`. -/
theorem front_hasDerivAt (hk : Continuous kappa) (s : ℝ) :
    HasDerivAt (front kappa theta0 H)
      (Complex.exp (Complex.I * (frontAngle kappa theta0 s : ℂ))) s := by
  have h := hasDerivAt_interpCurve (kappa := kappa) (θ₀ := theta0) (L := H) hk s
  rwa [tau_eq_exp] at h

theorem front_unit_speed (hk : Continuous kappa) (s : ℝ) :
    ‖deriv (front kappa theta0 H) s‖ = 1 := by
  rw [(front_hasDerivAt (theta0 := theta0) (H := H) hk s).deriv]
  simp [Complex.norm_exp]

section Symmetry

variable (hk : Continuous kappa) (hper : Function.Periodic kappa H)
  (htotal : (∫ r in (0:ℝ)..H, kappa r) = Real.pi)

include hk hper htotal

/-- The front tangent angle advances by `π` over a half period. -/
theorem frontAngle_add_halfPeriod (s : ℝ) :
    frontAngle kappa theta0 (s + H) = frontAngle kappa theta0 s + Real.pi :=
  tangentAngle_add_halfPeriod hk hper htotal s

/-- **The front is centrally symmetric**: `F(s + H) = −F(s)`. -/
theorem front_add_halfPeriod (s : ℝ) :
    front kappa theta0 H (s + H) = -front kappa theta0 H s :=
  interpCurve_add_halfPeriod hk hper htotal s

/-- **The front closes after two periods.** -/
theorem front_periodic : Function.Periodic (front kappa theta0 H) (2 * H) :=
  interpCurve_periodic hk hper htotal

end Symmetry

/-! ### The rear -/

/-- **The rear velocity**: `R' = cos δ · e^{iΨ}`. -/
theorem rear_hasDerivAt (hk : Continuous kappa) {s : ℝ}
    (hdelta : HasDerivAt delta (kappa s - Real.sin (delta s)) s) :
    HasDerivAt (rear kappa delta theta0 H)
      ((Real.cos (delta s) : ℂ)
        * Complex.exp (Complex.I
            * (rearAngle (frontAngle kappa theta0) delta s : ℂ))) s :=
  hasDerivAt_rearTrack (front_hasDerivAt (theta0 := theta0) (H := H) hk s)
    (hasDerivAt_tangentAngle (θ₀ := theta0) hk s) hdelta

/-- The rear track and the front differ by the rear unit tangent. -/
theorem unitTangent_rear_eq_front (s : ℝ) :
    rear kappa delta theta0 H s
      + Complex.exp (Complex.I * (rearAngle (frontAngle kappa theta0) delta s : ℂ))
      = front kappa theta0 H s :=
  unitTangentMap_rearTrack (F := front kappa theta0 H) (Θ := frontAngle kappa theta0)
    (δ := delta) s

/-- **`𝒯R = F`**: adding to the rear its unit tangent gives the front, as soon
as the rear is regular (`cos δ > 0`). -/
theorem unitTangentMap_rear_eq_front (hk : Continuous kappa) {s : ℝ}
    (hdelta : HasDerivAt delta (kappa s - Real.sin (delta s)) s)
    (hcos : 0 < Real.cos (delta s)) :
    rear kappa delta theta0 H s
        + (deriv (rear kappa delta theta0 H) s) / ‖deriv (rear kappa delta theta0 H) s‖
      = front kappa theta0 H s := by
  have hd := rear_hasDerivAt (theta0 := theta0) (H := H) hk hdelta
  have hexp1 : ‖Complex.exp (Complex.I
      * (rearAngle (frontAngle kappa theta0) delta s : ℝ))‖ = 1 := by
    rw [Complex.norm_exp]; simp
  have hnorm : ‖(Real.cos (delta s) : ℂ)
      * Complex.exp (Complex.I
          * (rearAngle (frontAngle kappa theta0) delta s : ℝ))‖ = Real.cos (delta s) := by
    rw [norm_mul, hexp1, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hcos]
  rw [hd.deriv, hnorm]
  have hne : (Real.cos (delta s) : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt hcos
  have hsimp : ((Real.cos (delta s) : ℂ)
        * Complex.exp (Complex.I * (rearAngle (frontAngle kappa theta0) delta s : ℂ)))
      / (Real.cos (delta s) : ℂ)
      = Complex.exp (Complex.I * (rearAngle (frontAngle kappa theta0) delta s : ℂ)) := by
    field_simp
  rw [hsimp]
  exact unitTangent_rear_eq_front s

section RearSymmetry

variable (hk : Continuous kappa) (hper : Function.Periodic kappa H)
  (htotal : (∫ r in (0:ℝ)..H, kappa r) = Real.pi)
  (hdper : Function.Periodic delta H)

include hk hper htotal hdper

/-- The rear tangent angle also advances by `π` over a half period. -/
theorem rearAngle_add_halfPeriod (s : ℝ) :
    rearAngle (frontAngle kappa theta0) delta (s + H)
      = rearAngle (frontAngle kappa theta0) delta s + Real.pi := by
  simp only [rearAngle, frontAngle_add_halfPeriod (theta0 := theta0) hk hper htotal s, hdper s]
  ring

/-- **The rear is centrally symmetric**: `R(s + H) = −R(s)`. -/
theorem rear_add_halfPeriod (s : ℝ) :
    rear kappa delta theta0 H (s + H) = -rear kappa delta theta0 H s := by
  have hang := rearAngle_add_halfPeriod (theta0 := theta0) hk hper htotal hdper s
  have hexp : Complex.exp (Complex.I
        * (rearAngle (frontAngle kappa theta0) delta (s + H) : ℂ))
      = -Complex.exp (Complex.I * (rearAngle (frontAngle kappa theta0) delta s : ℂ)) := by
    rw [hang]
    push_cast
    rw [mul_add, Complex.exp_add,
      show Complex.I * (Real.pi : ℂ) = (Real.pi : ℂ) * Complex.I from by ring,
      Complex.exp_pi_mul_I]
    ring
  simp only [rear, rearTrack, hexp,
    front_add_halfPeriod (theta0 := theta0) hk hper htotal s]
  ring

/-- **The rear closes after two periods.** -/
theorem rear_periodic : Function.Periodic (rear kappa delta theta0 H) (2 * H) := by
  intro s
  have h1 := rear_add_halfPeriod (theta0 := theta0) hk hper htotal hdper s
  have h2 := rear_add_halfPeriod (theta0 := theta0) hk hper htotal hdper (s + H)
  rw [show s + 2 * H = s + H + H from by ring, h2, h1, neg_neg]

end RearSymmetry

/-! ### The perimeters -/

/-- **The front perimeter is `2H`.** -/
theorem front_perimeter (hk : Continuous kappa) :
    (∫ s in (0:ℝ)..(2 * H), ‖deriv (front kappa theta0 H) s‖) = 2 * H := by
  have hcongr : (∫ s in (0:ℝ)..(2 * H), ‖deriv (front kappa theta0 H) s‖)
      = ∫ _ in (0:ℝ)..(2 * H), (1:ℝ) :=
    intervalIntegral.integral_congr
      (fun s _ => front_unit_speed (theta0 := theta0) (H := H) hk s)
  rw [hcongr]
  simp

/-- **The rear perimeter is `2P(H) = 2∫₀^H cos δ`.**  (The rear speed is
`cos δ ≥ 0` on the selected strip.) -/
theorem rear_perimeter (hk : Continuous kappa) (hdc : Continuous delta)
    (hdper : Function.Periodic delta H)
    (hode : ∀ s, HasDerivAt delta (kappa s - Real.sin (delta s)) s)
    (hcos : ∀ s, 0 ≤ Real.cos (delta s)) :
    (∫ s in (0:ℝ)..(2 * H), ‖deriv (rear kappa delta theta0 H) s‖)
      = 2 * ∫ s in (0:ℝ)..H, Real.cos (delta s) := by
  have hspeed : ∀ s, ‖deriv (rear kappa delta theta0 H) s‖ = Real.cos (delta s) := by
    intro s
    have hexp1 : ‖Complex.exp (Complex.I
        * (rearAngle (frontAngle kappa theta0) delta s : ℝ))‖ = 1 := by
      rw [Complex.norm_exp]; simp
    rw [(rear_hasDerivAt (theta0 := theta0) (H := H) hk (hode s)).deriv, norm_mul, hexp1,
      mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hcos s)]
  have hcongr : (∫ s in (0:ℝ)..(2 * H), ‖deriv (rear kappa delta theta0 H) s‖)
      = ∫ s in (0:ℝ)..(2 * H), Real.cos (delta s) :=
    intervalIntegral.integral_congr (fun s _ => hspeed s)
  have hcont : Continuous fun s => Real.cos (delta s) := Real.continuous_cos.comp hdc
  have hsplit : (∫ s in (0:ℝ)..(2 * H), Real.cos (delta s))
      = (∫ s in (0:ℝ)..H, Real.cos (delta s)) + ∫ s in H..(2 * H), Real.cos (delta s) := by
    rw [intervalIntegral.integral_add_adjacent_intervals
      (hcont.intervalIntegrable _ _) (hcont.intervalIntegrable _ _)]
  have hshift : (∫ s in H..(2 * H), Real.cos (delta s))
      = ∫ s in (0:ℝ)..H, Real.cos (delta s) := by
    have hp : Function.Periodic (fun s => Real.cos (delta s)) H := fun s => by
      simp [hdper s]
    have h := hp.intervalIntegral_add_eq H 0
    simpa [two_mul] using h
  rw [hcongr, hsplit, hshift]
  ring

end TwoCapPairsAssembly
