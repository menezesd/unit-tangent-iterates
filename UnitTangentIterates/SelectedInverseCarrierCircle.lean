import Mathlib
import UnitTangentIterates.SelectedInverseCarrier

/-!
# The rear carrier is not vacuous: the circle

`SelectedInverseCarrier.rearOwn_carrier` shows that the rear track of a front,
written in its own arclength, carries the rear curvature `k_H` of a matching
configuration.  This file checks that its hypotheses can all be met, on the
simplest configuration of the paper: the **circle** of curvature `1/2`, whose
selected steering angle is the constant `π/6` (the steering equation
`δ_s = K − sin δ` has the rest point `sin δ = K`), whose rear track is the
concentric circle of radius `√3` and whose rear curvature is the constant
`tan(π/6)`.
-/

noncomputable section

open Real Set Function

namespace SelectedInverseCarrierCircle

open CurvatureInterpolation RearTrack SelectedInverseCarrier

/-- The constant steering angle of the circle of curvature `1/2`. -/
def dlc : ℝ → ℝ := fun _ => Real.pi / 6

/-- Its front curvature. -/
def Kc : ℝ → ℝ := fun _ => 1 / 2

/-- Its front tangent angle. -/
def Thc : ℝ → ℝ := fun s => s / 2

/-- The front itself: the circle of radius `2`, of unit speed. -/
def Fc : ℝ → ℂ := fun s => -2 * Complex.I * Complex.exp (Complex.I * ((s / 2 : ℝ) : ℂ))

/-- The inverse of the rear arclength. -/
def sfc : ℝ → ℝ := fun x => 2 * x / Real.sqrt 3

/-- The rear curvature. -/
def kHc : ℝ → ℝ := fun _ => Real.tan (Real.pi / 6)

theorem sqrt3_pos : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)

theorem cos_dlc (s : ℝ) : Real.cos (dlc s) = Real.sqrt 3 / 2 := by
  simp [dlc, Real.cos_pi_div_six]

theorem half_le_cos_dlc (s : ℝ) : (1 : ℝ) / 2 ≤ Real.cos (dlc s) := by
  rw [cos_dlc]
  have h : (1 : ℝ) ≤ Real.sqrt 3 := by
    rw [show (1:ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt (by norm_num)
  linarith

theorem hasDerivAt_Fc (s : ℝ) :
    HasDerivAt Fc (Complex.exp (Complex.I * (Thc s : ℂ))) s := by
  have h0 : HasDerivAt (fun t : ℝ => Complex.I * ((t / 2 : ℝ) : ℂ)) (Complex.I / 2) s := by
    have h1 : HasDerivAt (fun t : ℝ => ((t : ℂ))) 1 s := Complex.ofRealCLM.hasDerivAt
    have h2 : HasDerivAt (fun t : ℝ => ((t : ℂ)) / 2) (1 / 2) s := h1.div_const 2
    have h3 := h2.const_mul Complex.I
    refine h3.congr_deriv ?_ |>.congr_of_eventuallyEq ?_
    · ring
    · filter_upwards with t
      simp
  have h := (h0.cexp).const_mul (-2 * Complex.I)
  refine h.congr_deriv ?_
  have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
  calc -2 * Complex.I * (Complex.exp (Complex.I * ((s / 2 : ℝ) : ℂ)) * (Complex.I / 2))
      = (-(Complex.I * Complex.I)) * Complex.exp (Complex.I * ((s / 2 : ℝ) : ℂ)) := by ring
    _ = Complex.exp (Complex.I * (Thc s : ℂ)) := by rw [hI]; simp [Thc]

theorem rearArclength_dlc (s : ℝ) : rearArclength dlc s = s * (Real.sqrt 3 / 2) := by
  simp only [rearArclength, cos_dlc]
  simp
  ring

theorem hsfinv_c (x : ℝ) : rearArclength dlc (sfc x) = x := by
  rw [rearArclength_dlc, sfc]
  field_simp

/-- **The hypotheses of the rear carrier are not vacuous.**  For the circle of
curvature `1/2`, with its constant steering angle `π/6`, the rear track written
in its own arclength is a unit-speed curve whose tangent angle has derivative
the rear curvature `tan(π/6)`. -/
theorem rearOwn_carrier_circle :
    (∀ x, HasDerivAt (fun z => rearTrack Fc Thc dlc (sfc z))
        (tau (rearAngle Thc dlc (sfc x))) x) ∧
      ∀ x, HasDerivAt (fun z => rearAngle Thc dlc (sfc z)) (kHc x) x := by
  refine rearOwn_carrier (c := 1/2) (K := Kc) (kH := kHc) (by norm_num) continuous_const
    half_le_cos_dlc hsfinv_c hasDerivAt_Fc (fun s => ?_) (fun s => ?_) (fun t => ?_)
  · simpa [Thc, Kc] using (hasDerivAt_id s).div_const 2
  · have hsin : Real.sin (dlc s) = 1 / 2 := by simp [dlc, Real.sin_pi_div_six]
    have : Kc s - Real.sin (dlc s) = 0 := by rw [hsin]; simp [Kc]
    rw [this]
    exact hasDerivAt_const s (Real.pi / 6)
  · have hcos : Real.cos (dlc t) ≠ 0 := by
      have := half_le_cos_dlc t
      linarith
    rw [kHc, dlc, Real.tan_eq_sin_div_cos]
    field_simp

end SelectedInverseCarrierCircle
