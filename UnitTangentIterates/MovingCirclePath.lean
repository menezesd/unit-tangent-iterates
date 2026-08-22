import Mathlib
import UnitTangentIterates.MovingCircleFront
import UnitTangentIterates.MarkedSpaceCircle
import UnitTangentIterates.PathMetric

/-!
# The path of fronts of a circle whose radius moves

The family of fronts of `MovingCircleFront.lean` is a circle of radius
`R(t) = 1 / sin A(t)` growing from `√2` to `2` between the times `0` and `1`.
Read in the normalized parameter `u ↦ F(t, P(t) u)` it is the moving marked
curve

```
  X(t, u) = −i R(t) e^{2π i u} ,
```

whose velocity `−i R'(t) e^{2π i u}` is purely normal, of normal speed
`η(t) = −R'(t) = cos A · A' / sin²A`, the front normal velocity computed in
`MovingCircleFront.etaF_eq`.  Since `η` does not depend on the arclength, the
cost density `m(t) = |η(t)|` dominates every density of the path metric, and
the family is at rest outside `(0,1)` because the profile is.

Main definition: `movingPath`, a normal path of the marked space joining the
two circles.
-/

noncomputable section

open Set Function Complex MarkedSpace PathMetric MovingCircleProfile MovingCircle
open scoped BoundedContinuousFunction

namespace MovingCirclePath

/-! ### Two elementary lemmas -/

theorem iteratedDeriv_const_succ (n : ℕ) (c : ℝ) :
    iteratedDeriv (n + 1) (fun _ : ℝ => c) = fun _ => 0 := by
  rw [iteratedDeriv_succ']
  simp [PathMetric.iteratedDeriv_zero_fun]

theorem supNorm_const (c : ℝ) : MarkedTopology.supNorm (fun _ : ℝ => c) = |c| := by
  simp [MarkedTopology.supNorm]

/-! ### The moving front as a marked curve -/

/-- The front at time `t`, in the normalized parameter. -/
def frontBCF (t : ℝ) : ℝ →ᵇ ℂ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun u => -Complex.I * ((1 / sA t : ℝ) : ℂ) * normExp u)
    (by unfold normExp; fun_prop) |1 / sA t| (fun u => by simp)

/-- The front at time `t` as a marked curve. -/
def frontData (t : ℝ) : Data := (frontBCF t, 0, 0)

/-- The normal speed of the moving front. -/
def speed (t : ℝ) : ℝ := cA t * profD t / (sA t) ^ 2

theorem speed_eq_etaF (t s : ℝ) : speed t = etaFf t s := rfl

theorem continuous_speed : Continuous speed := by
  unfold speed
  have h1 : Continuous cA := contDiff_cA.continuous
  have h2 : Continuous profD := contDiff_profD.continuous
  have h3 : Continuous sA := contDiff_sA.continuous
  exact (h1.mul h2).div (h3.pow 2) (fun t => pow_ne_zero 2 (sA_ne t))

theorem speed_eq_zero_outside {t : ℝ} (ht : t ∉ Ioo (0 : ℝ) 1) : speed t = 0 := by
  simp [speed, profD_eq_zero_outside ht]

theorem hasDerivAt_frontX (t u : ℝ) :
    HasDerivAt (fun r => -Complex.I * ((1 / sA r : ℝ) : ℂ) * normExp u)
      ((speed t : ℂ) * (Complex.I * normExp u)) t := by
  have hg : HasDerivAt (fun r => ((1 / sA r : ℝ) : ℂ))
      (((-(cA t * profD t) / (sA t) ^ 2 : ℝ) : ℂ)) t := (hasDerivAt_invsA t).ofReal_comp
  have h := ((hg.const_mul (-Complex.I)).mul_const (normExp u))
  refine h.congr_deriv ?_
  simp only [speed]
  push_cast
  ring

/-! ### The normal path -/

/-- **The path of fronts of a circle whose radius moves.**  The slices are the
circles of radius `1 / sin A(t)`; the path is at rest outside `(0,1)` because
the profile is, and its cost density is the (constant in the arclength) normal
speed. -/
def movingPath : NormalPath (frontData 0) (frontData 1) where
  T := 1
  T_pos := one_pos
  X := fun t u => -Complex.I * ((1 / sA t : ℝ) : ℂ) * normExp u
  eta := fun t _ => speed t
  nu := fun _ u => Complex.I * normExp u
  m := fun t => |speed t|
  start := fun _ => rfl
  finish := fun _ => rfl
  hasDerivAt_time := hasDerivAt_frontX
  cont_vel := fun u => by
    have : Continuous fun t : ℝ => ((speed t : ℝ) : ℂ) :=
      Complex.continuous_ofReal.comp continuous_speed
    exact this.mul continuous_const
  norm_nu := fun _ _ => by simp
  cont_m := continuous_speed.abs
  m_nonneg := fun _ => abs_nonneg _
  m_stop := fun t ht => by rw [speed_eq_zero_outside ht, abs_zero]
  abs_eta_le := fun _ _ => le_rfl
  le_m_L1 := fun t => by simp
  le_m_sup := fun t j hj => by
    match j, hj with
    | 0, _ => simp [MarkedTopology.supNorm]
    | 1, _ => simp [iteratedDeriv_const_succ 0 (speed t), MarkedTopology.supNorm]
    | 2, _ => simp [iteratedDeriv_const_succ 1 (speed t), MarkedTopology.supNorm]

@[simp] theorem movingPath_T : movingPath.T = 1 := rfl

@[simp] theorem movingPath_eta (t u : ℝ) : movingPath.eta t u = speed t := rfl

end MovingCirclePath
