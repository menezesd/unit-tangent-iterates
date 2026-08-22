import Mathlib
import UnitTangentIterates.SelInvPathCurvatureC2

/-!
# The perimeter of a pinched slice is pinched by universal constants

The hypotheses of the `C²` selected-inverse estimate pinch the curvature of the
slices of the normal path, `kminP ≤ K̂(t,σ) ≤ κ̂`, and the slices are closed
curves of constant speed and turning number one, so that

`∫₀¹ K̂(t,σ)·L(t) dσ = 2π` ,

`L(t)` being the perimeter of the slice.  Consequently the perimeter is not free:

`kminP·L(t) ≤ 2π ≤ κ̂·L(t)` , i.e. `2π/κ̂ ≤ L(t) ≤ 2π/kminP` .

This turns the two constants `P₀ ≤ L(t) ≤ P₁` that the uniform form of the
estimate asks for into *universal* constants, depending only on the curvature
pinching and not on the path — which is what a bound with one and the same
constant along a whole family of paths needs.

Main results: `turning_le_mul_perim`, `mul_perim_le_turning`,
`perim_lower_of_pinch`, `perim_upper_of_pinch`.
-/

noncomputable section

open Set Function Complex MeasureTheory intervalIntegral

namespace PerimeterFromTurning

open FrontFromPath SelInvPathRegularityC2 SelInvPathCurvatureC2

variable {X : ℝ → ℝ → ℂ} {P : ℝ → ℝ} {t : ℝ}

/-- The integrand of the turning integral of a slice is the normalized
curvature times the perimeter. -/
theorem turning_integrand (hP : P t ≠ 0) (u : ℝ) :
    ((starRingEnd ℂ) (pathVel X t u) * pathAcc X t u).im / P t ^ 2
      = pathKn X P t u * P t := by
  have h : u * P t / P t = u := mul_div_cancel_right₀ u hP
  simp only [pathKn, curvOfPath, h]
  field_simp

/-- **The total turning of a slice is at most `κ̂` times its perimeter.** -/
theorem turning_le_mul_perim {kh : ℝ} (hP : 0 < P t)
    (hcont : Continuous (pathKn X P t))
    (hturn : (∫ u in (0 : ℝ)..1,
        ((starRingEnd ℂ) (pathVel X t u) * pathAcc X t u).im / P t ^ 2) = 2 * Real.pi)
    (hmax : ∀ σ, pathKn X P t σ ≤ kh) :
    2 * Real.pi ≤ kh * P t := by
  have hrw : (∫ u in (0 : ℝ)..1,
      ((starRingEnd ℂ) (pathVel X t u) * pathAcc X t u).im / P t ^ 2)
      = ∫ u in (0 : ℝ)..1, pathKn X P t u * P t := by
    refine intervalIntegral.integral_congr (fun u _ => ?_)
    exact turning_integrand hP.ne' u
  have hint : IntervalIntegrable (fun u => pathKn X P t u * P t) volume 0 1 :=
    (hcont.mul continuous_const).intervalIntegrable 0 1
  have hle : (∫ u in (0 : ℝ)..1, pathKn X P t u * P t)
      ≤ ∫ _u in (0 : ℝ)..1, kh * P t := by
    refine intervalIntegral.integral_mono_on (by norm_num) hint
      (_root_.intervalIntegrable_const) (fun u _ => ?_)
    exact mul_le_mul_of_nonneg_right (hmax u) hP.le
  have hconst : (∫ _u in (0 : ℝ)..1, kh * P t) = kh * P t := by simp
  rw [hrw] at hturn
  rw [hturn, hconst] at hle
  exact hle

/-- **The total turning of a slice is at least `kminP` times its perimeter.** -/
theorem mul_perim_le_turning {kminP : ℝ} (hP : 0 < P t)
    (hcont : Continuous (pathKn X P t))
    (hturn : (∫ u in (0 : ℝ)..1,
        ((starRingEnd ℂ) (pathVel X t u) * pathAcc X t u).im / P t ^ 2) = 2 * Real.pi)
    (hmin : ∀ σ, kminP ≤ pathKn X P t σ) :
    kminP * P t ≤ 2 * Real.pi := by
  have hrw : (∫ u in (0 : ℝ)..1,
      ((starRingEnd ℂ) (pathVel X t u) * pathAcc X t u).im / P t ^ 2)
      = ∫ u in (0 : ℝ)..1, pathKn X P t u * P t := by
    refine intervalIntegral.integral_congr (fun u _ => ?_)
    exact turning_integrand hP.ne' u
  have hint : IntervalIntegrable (fun u => pathKn X P t u * P t) volume 0 1 :=
    (hcont.mul continuous_const).intervalIntegrable 0 1
  have hle : (∫ _u in (0 : ℝ)..1, kminP * P t)
      ≤ ∫ u in (0 : ℝ)..1, pathKn X P t u * P t := by
    refine intervalIntegral.integral_mono_on (by norm_num) _root_.intervalIntegrable_const hint
      (fun u _ => ?_)
    exact mul_le_mul_of_nonneg_right (hmin u) hP.le
  have hconst : (∫ _u in (0 : ℝ)..1, kminP * P t) = kminP * P t := by simp
  rw [hrw] at hturn
  rw [hturn, hconst] at hle
  exact hle

/-- **The perimeter of a pinched slice is at least `2π/κ̂`.** -/
theorem perim_lower_of_pinch {kh : ℝ} (hkh : 0 < kh) (hP : 0 < P t)
    (hcont : Continuous (pathKn X P t))
    (hturn : (∫ u in (0 : ℝ)..1,
        ((starRingEnd ℂ) (pathVel X t u) * pathAcc X t u).im / P t ^ 2) = 2 * Real.pi)
    (hmax : ∀ σ, pathKn X P t σ ≤ kh) :
    2 * Real.pi / kh ≤ P t := by
  rw [div_le_iff₀ hkh]
  have := turning_le_mul_perim hP hcont hturn hmax
  linarith [this]

/-- **The perimeter of a pinched slice is at most `2π/kminP`.** -/
theorem perim_upper_of_pinch {kminP : ℝ} (hkmin : 0 < kminP) (hP : 0 < P t)
    (hcont : Continuous (pathKn X P t))
    (hturn : (∫ u in (0 : ℝ)..1,
        ((starRingEnd ℂ) (pathVel X t u) * pathAcc X t u).im / P t ^ 2) = 2 * Real.pi)
    (hmin : ∀ σ, kminP ≤ pathKn X P t σ) :
    P t ≤ 2 * Real.pi / kminP := by
  rw [le_div_iff₀ hkmin]
  have := mul_perim_le_turning hP hcont hturn hmin
  linarith [this]

end PerimeterFromTurning
