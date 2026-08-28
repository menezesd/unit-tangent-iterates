import Mathlib
import UnitTangentIterates.NormalizedSelectedRearClosure

/-! # Rescaling normalized steering to a physical period -/

noncomputable section

open Set

namespace NormalizedSteeringPhysicalRescaling

open NormalizedSelectedRearClosure

/-- A period-one steering angle read in a physical arclength coordinate. -/
def deltaPhys {kap : ℝ} (d : SteeringData kap) (P : ℝ) : ℝ → ℝ :=
  fun s => d.delta (s / P)

/-- The physical curvature forced by the rescaled steering ODE.  The sine
correction is essential: the normalized exported ODE has unit coefficient in
front of both `K` and `sin δ`. -/
def curvaturePhys {kap : ℝ} (d : SteeringData kap) (P : ℝ) : ℝ → ℝ :=
  fun s => (d.K (s / P) + (P - 1) * Real.sin (d.delta (s / P))) / P

/-- Rescaling transports period one to physical period `P`. -/
theorem deltaPhys_periodic {kap P : ℝ} (d : SteeringData kap) :
    Function.Periodic (deltaPhys d P) P := by
  intro s
  by_cases hP : P = 0
  · simp [hP, deltaPhys]
  · dsimp [deltaPhys]
    convert d.delta_periodic (s / P) using 1 <;> field_simp <;> ring

/-- Strip membership is unchanged by physical rescaling. -/
theorem deltaPhys_mem {kap P : ℝ} (d : SteeringData kap) (s : ℝ) :
    deltaPhys d P s ∈ Icc 0 (Real.arcsin kap) :=
  d.delta_mem (s / P)

/-- The rescaled angle satisfies the physical selected-steering equation. -/
theorem hasDerivAt_deltaPhys {kap P : ℝ} (d : SteeringData kap) (hP : 0 < P)
    (s : ℝ) :
    HasDerivAt (deltaPhys d P)
      (curvaturePhys d P s - Real.sin (deltaPhys d P s)) s := by
  have hx : HasDerivAt (fun r : ℝ => r / P) (1 / P) s := by
    simpa [div_eq_mul_inv] using (hasDerivAt_id s).mul_const (P⁻¹)
  have hc := (d.steering (s / P)).comp s hx
  convert hc using 1 <;> dsimp [deltaPhys, curvaturePhys]
  field_simp [ne_of_gt hP]
  ring

/-- The physical curvature identity in a denominator-free form. -/
theorem curvaturePhys_mul_period {kap P : ℝ} (d : SteeringData kap)
    (hP : 0 < P) (s : ℝ) :
    P * curvaturePhys d P s =
      d.K (s / P) + (P - 1) * Real.sin (deltaPhys d P s) := by
  dsimp [curvaturePhys, deltaPhys]
  field_simp [ne_of_gt hP]

/-- Canonical physical tangent angle obtained by integrating the rescaled
curvature from a prescribed marked angle. -/
def thetaPhys {kap : ℝ} (d : SteeringData kap) (P theta0 : ℝ) : ℝ → ℝ :=
  fun s => theta0 + ∫ r in (0 : ℝ)..s, curvaturePhys d P r

/-- Continuity of the normalized curvature gives continuity of the physical
curvature. -/
theorem continuous_curvaturePhys {kap P : ℝ} (d : SteeringData kap)
    (hK : Continuous d.K) : Continuous (curvaturePhys d P) := by
  have hdelta : Continuous d.delta :=
    Differentiable.continuous fun u => (d.steering u).differentiableAt
  show Continuous fun s =>
    (d.K (s / P) + (P - 1) * Real.sin (d.delta (s / P))) / P
  fun_prop

/-- The canonical physical angle has derivative equal to physical curvature. -/
theorem hasDerivAt_thetaPhys {kap P theta0 : ℝ} (d : SteeringData kap)
    (hK : Continuous d.K) (s : ℝ) :
    HasDerivAt (thetaPhys d P theta0) (curvaturePhys d P s) s := by
  have hc := continuous_curvaturePhys (P := P) d hK
  exact ((hc.integral_hasStrictDerivAt (0 : ℝ) s).hasDerivAt).const_add theta0

theorem thetaPhys_zero {kap P theta0 : ℝ} (d : SteeringData kap) :
    thetaPhys d P theta0 0 = theta0 := by
  simp [thetaPhys]

/-- Complete physical steering package in the exact form expected by
`packagedRear_eq_selInv`. -/
theorem physical_steering_data {kap P theta0 : ℝ} (d : SteeringData kap)
    (hP : 0 < P) (hK : Continuous d.K) :
    Function.Periodic (deltaPhys d P) P ∧
      (∀ s, deltaPhys d P s ∈ Icc 0 (Real.arcsin kap)) ∧
      (∀ s, HasDerivAt (deltaPhys d P)
        (curvaturePhys d P s - Real.sin (deltaPhys d P s)) s) ∧
      (∀ s, HasDerivAt (thetaPhys d P theta0) (curvaturePhys d P s) s) :=
  ⟨deltaPhys_periodic d, deltaPhys_mem d,
    hasDerivAt_deltaPhys d hP, hasDerivAt_thetaPhys d hK⟩

end NormalizedSteeringPhysicalRescaling
