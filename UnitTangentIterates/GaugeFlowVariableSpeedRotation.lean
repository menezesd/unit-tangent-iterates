import Mathlib
import UnitTangentIterates.GaugeFlowVariableSpeedFamily

/-!
# Non-vacuity of the gauge-flow variable-speed assembly

`GaugeFlowVariableSpeedFamily.isVariableSpeedFamily_of_gauge_flow` has a long
hypothesis block: the field of the gauge flow, its two space derivatives and
their bounds, the two uniform bounds on the flow derivatives, and the time
derivatives of the tangent angle and of the curvature of the slices along the
flow line.  This file checks that the block is jointly satisfiable, on a family
that really moves: the unit circle rotating at unit angular speed,

```
  Y t s = −i·e^{i(s+t)} ,
```

parametrized by its own arclength, read in the affine marking `Φ(t,u) = u` —
the flow of the zero field.  The tangent angle is `α(t,s) = s + t` and the
curvature is `1`, so the angle turns at unit rate in the time and the curvature
does not move; with cost density `m ≡ 1` and constants `P₀ = P₁ = κ̂ = 1`,
`G₁ = C_g = 0`, every hypothesis holds.

Main result: `isVariableSpeedFamily_rotatingCircle`.
-/

noncomputable section

open Set Function

namespace GaugeFlowVariableSpeedRotation

open FlowDerivative GaugeFlowTimeDerivative GaugeFlowVariableSpeedFamily
  NormalPathC2IncrementVariableSpeed

/-- The unit circle rotating at unit angular speed, parametrized by arclength. -/
def rotCircle (t s : ℝ) : ℂ := -Complex.I * Complex.exp (Complex.I * ((s + t : ℝ) : ℂ))

/-- Its tangent angle. -/
def rotAngle (t s : ℝ) : ℝ := s + t

/-- Its curvature. -/
def rotCurv (_t _s : ℝ) : ℝ := 1

theorem hasDerivAt_rotCircle (t s : ℝ) :
    HasDerivAt (rotCircle t) (Complex.exp (Complex.I * (rotAngle t s : ℂ))) s := by
  have hlin : HasDerivAt (fun x : ℝ => Complex.I * ((x + t : ℝ) : ℂ)) Complex.I s := by
    have h : HasDerivAt (fun x : ℝ => ((x + t : ℝ) : ℂ)) 1 s := by
      simpa using ((hasDerivAt_id s).add_const t).ofReal_comp
    simpa using h.const_mul Complex.I
  have h := (hlin.cexp).const_mul (-Complex.I)
  refine h.congr_deriv ?_
  have hI : -Complex.I * (Complex.exp (Complex.I * ((s + t : ℝ) : ℂ)) * Complex.I)
      = Complex.exp (Complex.I * ((s + t : ℝ) : ℂ)) := by
    have : -Complex.I * Complex.I = 1 := by
      simp [Complex.I_mul_I]
    calc -Complex.I * (Complex.exp (Complex.I * ((s + t : ℝ) : ℂ)) * Complex.I)
        = (-Complex.I * Complex.I) * Complex.exp (Complex.I * ((s + t : ℝ) : ℂ)) := by ring
      _ = Complex.exp (Complex.I * ((s + t : ℝ) : ℂ)) := by rw [this, one_mul]
  simpa [rotAngle] using hI

theorem hasDerivAt_rotAngle (t s : ℝ) : HasDerivAt (rotAngle t) (rotCurv t s) s := by
  unfold rotAngle rotCurv
  exact (hasDerivAt_id s).add_const t

/-- **The rotating unit circle read in the affine marking satisfies the whole
hypothesis block of `isVariableSpeedFamily_of_gauge_flow`**, with cost density
`m ≡ 1` and constants `P₀ = P₁ = κ̂ = 1`, `G₁ = C_g = 0`. -/
theorem isVariableSpeedFamily_rotatingCircle :
    IsVariableSpeedFamily 1 1 1 0 0 (fun t u => rotCircle t u) (fun _ => 1) := by
  have hzero : ∀ s x : ℝ, HasDerivAt ((fun (_ _ : ℝ) => (0 : ℝ)) s) 0 x := fun _ _ =>
    hasDerivAt_const _ _
  have hflowDeriv : ∀ t u : ℝ,
      flowDeriv (fun _ _ => (0 : ℝ)) (fun _ u => u) 1 t u = 1 := by
    intro t u
    simp [flowDeriv]
  have hflowDeriv2 : ∀ t u : ℝ,
      flowDeriv2 (fun _ _ => (0 : ℝ)) (fun _ _ => (0 : ℝ)) (fun _ u => u) 1 t u = 0 := by
    intro t u
    simp [flowDeriv2]
  refine isVariableSpeedFamily_of_gauge_flow (Y := rotCircle) (alpha := rotAngle)
    (k := rotCurv) (h := fun _ _ => 0) (hx := fun _ _ => 0) (hxx := fun _ _ => 0)
    (Phi := fun _ u => u) (alphat := fun _ _ => 1) (kappat := fun _ _ => 0)
    (C := fun _ => 0) (C2 := fun _ => 0) (K := 0) (K2 := 0) (ell := 1)
    hasDerivAt_rotCircle hasDerivAt_rotAngle
    (fun _ => LipschitzWith.const 0) continuous_const
    (fun u t => hasDerivAt_const t u) one_pos (fun u => (one_mul u).symm)
    hzero continuous_const hzero continuous_const (fun _ _ => by norm_num)
    (fun t u => by rw [hflowDeriv t u]) (fun t u => by rw [hflowDeriv2 t u]; norm_num)
    (fun _ _ => by norm_num [rotCurv])
    (fun _ _ => by norm_num) (fun _ _ => by norm_num)
    (fun _ => le_rfl) (fun _ => le_rfl)
    (fun _ => by norm_num) (fun _ => by norm_num)
    (fun t u => by simpa [rotAngle] using (hasDerivAt_id t).const_add u)
    (fun _ => continuous_const) (fun _ _ => by norm_num)
    (fun t u => hasDerivAt_const t (1 : ℝ)) (fun _ => continuous_const)
    (fun _ _ => by norm_num)

end GaugeFlowVariableSpeedRotation
