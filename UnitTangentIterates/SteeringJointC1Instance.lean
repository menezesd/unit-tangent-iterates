import Mathlib
import UnitTangentIterates.SteeringJointC1

/-!
# A worked instance of the joint regularity of the selected steering angle

`SteeringJointC1.contDiff_one_uncurry_delta` proves that the selected steering
angle of a path of fronts is jointly `C¹`, under a bundle of hypotheses: the
steering equation, periodicity, the selected strip, two-sided bounds for the
radius of curvature, and a Lipschitz and a quadratic Taylor bound for its
dependence on the path parameter.  This file checks that the bundle is
consistent, on the family

```
  q(a, φ) = 3 + sin a ,     δ(a, φ) = arcsin (1 / (3 + sin a)) ,
```

a genuinely moving path of fronts of constant curvature, for which the
steering angle is the constant solution of `δ_φ = 1 - q sin δ` and stays in the
selected strip of `κ̂ = 1/2`.

Main result: `steering_jointC1_instance`.
-/

noncomputable section

open Function Set Real

namespace SteeringJointC1Instance

/-- The radius of curvature of the instance: `q(a, φ) = 3 + sin a`. -/
def q (a : ℝ) (_ : ℝ) : ℝ := 3 + Real.sin a

/-- Its derivative in the path parameter. -/
def qd (a : ℝ) (_ : ℝ) : ℝ := Real.cos a

/-- The selected steering angle of the instance. -/
def delta (a : ℝ) (_ : ℝ) : ℝ := Real.arcsin (1 / (3 + Real.sin a))

theorem q_bounds (a x : ℝ) : (2 : ℝ) ≤ q a x ∧ q a x ≤ 4 := by
  have h := Real.neg_one_le_sin a
  have h' := Real.sin_le_one a
  constructor <;> simp only [q] <;> linarith

theorem q_pos (a x : ℝ) : 0 < q a x := lt_of_lt_of_le (by norm_num) (q_bounds a x).1

theorem inv_q_le_half (a x : ℝ) : 1 / q a x ≤ 1 / 2 := by
  have h := (q_bounds a x).1
  exact one_div_le_one_div_of_le (by norm_num) h

theorem inv_q_nonneg (a x : ℝ) : 0 ≤ 1 / q a x := le_of_lt (by
  have := q_pos a x
  positivity)

theorem sin_delta (a x : ℝ) : Real.sin (delta a x) = 1 / (3 + Real.sin a) := by
  have h1 : 1 / (3 + Real.sin a) = 1 / q a x := rfl
  have hle : 1 / q a x ≤ 1 := le_trans (inv_q_le_half a x) (by norm_num)
  have hge : -1 ≤ 1 / q a x := le_trans (by norm_num) (inv_q_nonneg a x)
  rw [delta, h1, Real.sin_arcsin hge hle]

/-- **The hypotheses of the joint regularity theorem are consistent.**  For the
family `q(a,φ) = 3 + sin a` of fronts of constant curvature, whose selected
steering angle is the constant solution `δ = arcsin(1/(3 + sin a))`, every
hypothesis of `SteeringJointC1.contDiff_one_uncurry_delta` holds, with
`κ̂ = 1/2`, `Q = 4`, `Q_d = 1`, `Q_lip = 1`, `C_q = 1` and any period `P > 0`,
so that the selected steering angle is jointly `C¹` and its derivative in the
path parameter is the periodic solution of the linearized equation. -/
theorem steering_jointC1_instance {P : ℝ} (hP : 0 < P) :
    ContDiff ℝ 1 (uncurry delta) ∧
      ∀ a x, HasDerivAt (fun b => delta b x)
        (SteeringJointC1.variation q qd delta P a x) a := by
  have hkap : (0 : ℝ) < 1 / 2 := by norm_num
  have hkap1 : (1 : ℝ) / 2 < 1 := by norm_num
  -- the steering equation: the angle is constant and the field vanishes
  have hsol : ∀ a x, HasDerivAt (delta a) (1 - q a x * Real.sin (delta a x)) x := by
    intro a x
    have hz : 1 - q a x * Real.sin (delta a x) = 0 := by
      rw [sin_delta a x]
      have hq : q a x = 3 + Real.sin a := rfl
      have hne : (3 : ℝ) + Real.sin a ≠ 0 := by
        have := Real.neg_one_le_sin a
        exact ne_of_gt (by linarith)
      rw [hq]
      field_simp
      ring
    rw [hz]
    exact hasDerivAt_const x _
  have hper : ∀ a, Function.Periodic (delta a) P := fun a x => rfl
  have hstrip : ∀ a x, delta a x ∈ Icc (0 : ℝ) (arcsin (1 / 2)) := by
    intro a x
    have hd : delta a x = Real.arcsin (1 / q a x) := rfl
    rw [hd]
    exact ⟨Real.arcsin_nonneg.mpr (inv_q_nonneg a x),
      Real.arcsin_le_arcsin (inv_q_le_half a x)⟩
  have hqlow : ∀ a x, ((1 : ℝ) / 2)⁻¹ ≤ q a x := by
    intro a x
    have := (q_bounds a x).1
    norm_num
    linarith
  have hqup : ∀ a x, q a x ≤ 4 := fun a x => (q_bounds a x).2
  have hqcont : Continuous (uncurry q) :=
    (continuous_const.add (Real.continuous_sin.comp continuous_fst))
  have hqdcont : Continuous (uncurry qd) := Real.continuous_cos.comp continuous_fst
  have hqper : ∀ a, Function.Periodic (q a) P := fun a x => rfl
  have hqdper : ∀ a, Function.Periodic (qd a) P := fun a x => rfl
  have hqlip : ∀ a b x, |q a x - q b x| ≤ 1 * |a - b| := by
    intro a b x
    have h : q a x - q b x = Real.sin a - Real.sin b := by simp [q]
    rw [h, one_mul, ← Real.dist_eq, ← Real.dist_eq]
    exact Real.lipschitzWith_sin.dist_le_mul a b |>.trans_eq (by simp)
  have hqtaylor : ∀ a b x, |q a x - q b x - (a - b) * qd b x| ≤ 1 * (a - b) ^ 2 := by
    intro a b x
    have h : q a x - q b x - (a - b) * qd b x
        = Real.sin (b + (a - b)) - Real.sin b - Real.cos b * (a - b) := by
      simp only [q, qd]
      ring_nf
    rw [h, one_mul]
    exact SteeringSmoothDependence.abs_sin_taylor b (a - b)
  have hqdbd : ∀ a x, |qd a x| ≤ 1 := fun a x => Real.abs_cos_le_one a
  refine ⟨SteeringJointC1.contDiff_one_uncurry_delta hP hkap hkap1 hqcont hqdcont hsol hper
      hstrip hqlow hqup hqper hqdper hqlip hqtaylor hqdbd (by norm_num), fun a x => ?_⟩
  exact SteeringJointC1.hasDerivAt_param_steering hP hkap hkap1 hqcont hqdcont hsol hper hstrip
    hqlow hqup hqper hqdper hqlip hqtaylor hqdbd (by norm_num) a x

end SteeringJointC1Instance
