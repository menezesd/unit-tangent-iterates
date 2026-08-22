import Mathlib
import UnitTangentIterates.PeriodicGreenJoint
import UnitTangentIterates.SteeringSmoothDependence
import UnitTangentIterates.JointC1

/-!
# The selected steering angle is jointly `C¹` along a path of fronts

`SteeringSmoothDependence.hasDerivAt_selected_steering` is the lemma *Smooth
dependence of the selected rear* of the paper *A Noncircular Oval with Convex
Unit-Tangent Iterates* at the level of the steering angle: along a path `a` of
fronts, parametrized by the tangent angle, the selected steering angle
`δ(a, ·)` — the `P`-periodic solution of

```
  δ_φ = 1 - q(a, φ) sin δ
```

inside the selected strip `0 ≤ δ ≤ arcsin κ̂` — is differentiable in `a`, with
derivative *a* periodic solution `w` of the linearized equation

```
  w_φ = -q cos δ · w - q̇ sin δ .
```

That statement is one-sided in two ways: the solution `w` has to be supplied,
and nothing is said about the *joint* regularity of `δ` in the pair `(a, φ)`,
which is what the assembly of the path metric consumes.

This file removes both restrictions.  The solution `w` is produced by the
periodic Green operator of `PeriodicGreen.lean`,

```
  w(a, ·) = 𝒢_{q(a,·) cos δ(a,·)} (-q̇(a,·) sin δ(a,·)) ,
```

whose coefficient is bounded below by `κ̂⁻¹√(1-κ̂²) > 0` on the selected strip,
so the operator applies; `PeriodicGreenJoint.lean` makes it jointly continuous
in `(a, φ)`, and the steering angle is itself jointly continuous because it is
Lipschitz in the parameter, uniformly in the angle.  Since the angle derivative
`1 - q sin δ` is jointly continuous too, the bridge of `JointC1.lean` turns the
two partial derivatives into joint `C¹` regularity.

Main results:

* `linCoeff_ge` — the linearized coefficient is at least `κ̂⁻¹√(1-κ̂²)`;
* `hasDerivAt_variation` — `w(a,·)` solves the linearized equation, and is
  `P`-periodic;
* `hasDerivAt_param_steering` — `∂_a δ(a, φ) = w(a, φ)` at *every* parameter;
* `continuous_uncurry_delta` — joint continuity of the steering angle;
* `contDiff_one_uncurry_delta` — **the selected steering angle is jointly
  `C¹`**, with the two partial derivatives `w` and `1 - q sin δ`.
-/

noncomputable section

open Function Set Real

namespace SteeringJointC1

open PeriodicGreen PeriodicGreenJoint

variable {q qd delta : ℝ → ℝ → ℝ} {P kap Q Qd Qlip Cq : ℝ}

/-- The coefficient `q cos δ` of the linearized steering equation. -/
def linCoeff (q delta : ℝ → ℝ → ℝ) (a x : ℝ) : ℝ := q a x * Real.cos (delta a x)

/-- The source `-q̇ sin δ` of the linearized steering equation. -/
def linSource (qd delta : ℝ → ℝ → ℝ) (a x : ℝ) : ℝ := -(qd a x * Real.sin (delta a x))

/-- The variation of the selected steering angle: the periodic solution of the
linearized steering equation, produced by the periodic Green operator. -/
def variation (q qd delta : ℝ → ℝ → ℝ) (P a : ℝ) : ℝ → ℝ :=
  periodicGreen (linCoeff q delta a) P (linSource qd delta a)

section Slices

/-- On the selected strip the linearized coefficient is at least
`κ̂⁻¹√(1-κ̂²) > 0`. -/
theorem linCoeff_ge (hkap : 0 < kap)
    (hqlow : ∀ a x, kap⁻¹ ≤ q a x) (hstrip : ∀ a x, delta a x ∈ Icc (0 : ℝ) (arcsin kap))
    (a x : ℝ) : Real.sqrt (1 - kap ^ 2) / kap ≤ linCoeff q delta a x := by
  have hm : Real.sqrt (1 - kap ^ 2) ≤ Real.cos (delta a x) :=
    Shadowing.cos_ge_of_mem_strip (hstrip a x).1 (hstrip a x).2
  have hmnn : (0 : ℝ) ≤ Real.sqrt (1 - kap ^ 2) := Real.sqrt_nonneg _
  have hq : kap⁻¹ ≤ q a x := hqlow a x
  have hqpos : 0 < q a x := lt_of_lt_of_le (by positivity) hq
  have : kap⁻¹ * Real.sqrt (1 - kap ^ 2) ≤ q a x * Real.cos (delta a x) :=
    mul_le_mul hq hm hmnn hqpos.le
  calc Real.sqrt (1 - kap ^ 2) / kap = kap⁻¹ * Real.sqrt (1 - kap ^ 2) := by
        field_simp
    _ ≤ linCoeff q delta a x := this

/-- Each slice of the steering angle is continuous. -/
theorem continuous_delta_slice
    (hsol : ∀ a x, HasDerivAt (delta a) (1 - q a x * Real.sin (delta a x)) x) (a : ℝ) :
    Continuous (delta a) := by
  have hdiff : Differentiable ℝ (delta a) := fun x => (hsol a x).differentiableAt
  exact hdiff.continuous

theorem continuous_linCoeff_slice (hqcont : Continuous (uncurry q))
    (hsol : ∀ a x, HasDerivAt (delta a) (1 - q a x * Real.sin (delta a x)) x) (a : ℝ) :
    Continuous (linCoeff q delta a) := by
  have hq : Continuous (q a) := hqcont.comp (continuous_const.prodMk continuous_id)
  exact hq.mul (Real.continuous_cos.comp (continuous_delta_slice hsol a))

theorem continuous_linSource_slice (hqdcont : Continuous (uncurry qd))
    (hsol : ∀ a x, HasDerivAt (delta a) (1 - q a x * Real.sin (delta a x)) x) (a : ℝ) :
    Continuous (linSource qd delta a) := by
  have hqd : Continuous (qd a) := hqdcont.comp (continuous_const.prodMk continuous_id)
  exact (hqd.mul (Real.continuous_sin.comp (continuous_delta_slice hsol a))).neg

theorem periodic_linCoeff_slice (hqper : ∀ a, Function.Periodic (q a) P)
    (hper : ∀ a, Function.Periodic (delta a) P) (a : ℝ) :
    Function.Periodic (linCoeff q delta a) P := by
  intro x
  simp only [linCoeff, hqper a x, hper a x]

theorem periodic_linSource_slice (hqdper : ∀ a, Function.Periodic (qd a) P)
    (hper : ∀ a, Function.Periodic (delta a) P) (a : ℝ) :
    Function.Periodic (linSource qd delta a) P := by
  intro x
  simp only [linSource, hqdper a x, hper a x]

/-- The primitive of the linearized coefficient over one period is positive. -/
theorem prim_linCoeff_pos (hP : 0 < P) (hkap : 0 < kap) (hkap1 : kap < 1)
    (hqcont : Continuous (uncurry q))
    (hsol : ∀ a x, HasDerivAt (delta a) (1 - q a x * Real.sin (delta a x)) x)
    (hqlow : ∀ a x, kap⁻¹ ≤ q a x) (hstrip : ∀ a x, delta a x ∈ Icc (0 : ℝ) (arcsin kap))
    (a : ℝ) : 0 < prim (linCoeff q delta a) P := by
  set c : ℝ := Real.sqrt (1 - kap ^ 2) / kap with hc
  have hmpos : 0 < Real.sqrt (1 - kap ^ 2) := Real.sqrt_pos.mpr (by nlinarith)
  have hcpos : 0 < c := div_pos hmpos hkap
  have hcont := continuous_linCoeff_slice hqcont hsol (delta := delta) a
  have hmono : (∫ t in (0 : ℝ)..P, c) ≤ ∫ t in (0 : ℝ)..P, linCoeff q delta a t := by
    refine intervalIntegral.integral_mono_on hP.le
      (intervalIntegrable_const) (hcont.intervalIntegrable _ _) (fun t _ => ?_)
    exact linCoeff_ge hkap hqlow hstrip a t
  have hconst : (∫ t in (0 : ℝ)..P, c) = c * P := by simp [mul_comm]
  have : 0 < c * P := by positivity
  rw [prim]
  linarith [hmono, hconst ▸ hmono]

/-- **The variation solves the linearized steering equation.** -/
theorem hasDerivAt_variation (hP : 0 < P) (hkap : 0 < kap) (hkap1 : kap < 1)
    (hqcont : Continuous (uncurry q)) (hqdcont : Continuous (uncurry qd))
    (hsol : ∀ a x, HasDerivAt (delta a) (1 - q a x * Real.sin (delta a x)) x)
    (hqlow : ∀ a x, kap⁻¹ ≤ q a x) (hstrip : ∀ a x, delta a x ∈ Icc (0 : ℝ) (arcsin kap))
    (hqper : ∀ a, Function.Periodic (q a) P) (hqdper : ∀ a, Function.Periodic (qd a) P)
    (hper : ∀ a, Function.Periodic (delta a) P) (a x : ℝ) :
    HasDerivAt (variation q qd delta P a)
      (-(q a x * Real.cos (delta a x)) * variation q qd delta P a x
        - qd a x * Real.sin (delta a x)) x := by
  have h := periodicGreen_hasDerivAt (a := linCoeff q delta a) (l := P)
    (f := linSource qd delta a) (continuous_linCoeff_slice hqcont hsol a)
    (periodic_linCoeff_slice hqper hper a)
    (prim_linCoeff_pos hP hkap hkap1 hqcont hsol hqlow hstrip a)
    (continuous_linSource_slice hqdcont hsol a) (periodic_linSource_slice hqdper hper a) x
  refine h.congr_deriv ?_
  simp only [linCoeff, linSource, variation]
  ring

/-- The variation is `P`-periodic. -/
theorem periodic_variation (hqcont : Continuous (uncurry q))
    (hsol : ∀ a x, HasDerivAt (delta a) (1 - q a x * Real.sin (delta a x)) x)
    (hqper : ∀ a, Function.Periodic (q a) P) (hqdper : ∀ a, Function.Periodic (qd a) P)
    (hper : ∀ a, Function.Periodic (delta a) P) (a : ℝ) :
    Function.Periodic (variation q qd delta P a) P :=
  periodicGreen_periodic (continuous_linCoeff_slice hqcont hsol a)
    (periodic_linCoeff_slice hqper hper a) (periodic_linSource_slice hqdper hper a)

end Slices

/-- **The selected steering angle is Lipschitz in the path parameter**, with a
constant uniform in the angle: `|δ(a,φ) - δ(b,φ)| ≤ Q_lip κ̂ |a-b| / √(1-κ̂²)`. -/
theorem abs_delta_sub_le (hP : 0 < P) (hkap : 0 < kap) (hkap1 : kap < 1)
    (hsol : ∀ a x, HasDerivAt (delta a) (1 - q a x * Real.sin (delta a x)) x)
    (hper : ∀ a, Function.Periodic (delta a) P)
    (hstrip : ∀ a x, delta a x ∈ Icc (0 : ℝ) (arcsin kap))
    (hqlow : ∀ a x, kap⁻¹ ≤ q a x)
    (hqlip : ∀ a b x, |q a x - q b x| ≤ Qlip * |a - b|) (a b x : ℝ) :
    |delta a x - delta b x| ≤ Qlip * |a - b| / (Real.sqrt (1 - kap ^ 2) / kap) := by
  set m : ℝ := Real.sqrt (1 - kap ^ 2) with hm
  have hmpos : 0 < m := Real.sqrt_pos.mpr (by nlinarith)
  set c : ℝ := m / kap with hc
  have hcpos : 0 < c := div_pos hmpos hkap
  refine PeriodicParameterDeriv.abs_param_diff_le_periodic
    (f := fun a s u => 1 - q a s * Real.sin u) (y := delta) (a0 := b) (P := P) (c := c)
    (A := Qlip) hP hcpos hsol hper ?_ ?_ a x
  · -- dissipativity
    intro a s
    have hsin := SelectedRear.sin_sub_mul_self_ge (kap := kap) (hstrip a s) (hstrip b s)
    have hq : kap⁻¹ ≤ q a s := hqlow a s
    have hqpos : 0 < q a s := lt_of_lt_of_le (by positivity) hq
    have hmul : q a s * (m * (delta a s - delta b s) ^ 2)
        ≤ q a s * ((Real.sin (delta a s) - Real.sin (delta b s)) * (delta a s - delta b s)) :=
      mul_le_mul_of_nonneg_left hsin hqpos.le
    have hlow : c * (delta a s - delta b s) ^ 2 ≤ q a s * (m * (delta a s - delta b s) ^ 2) := by
      have h1 : c ≤ q a s * m := by
        have : kap⁻¹ * m ≤ q a s * m := mul_le_mul_of_nonneg_right hq hmpos.le
        calc c = kap⁻¹ * m := by rw [hc]; field_simp
          _ ≤ q a s * m := this
      nlinarith [sq_nonneg (delta a s - delta b s)]
    have hexp : (1 - q a s * Real.sin (delta a s) - (1 - q a s * Real.sin (delta b s)))
        * (delta a s - delta b s)
        = -(q a s * ((Real.sin (delta a s) - Real.sin (delta b s))
          * (delta a s - delta b s))) := by ring
    rw [hexp]
    linarith
  · -- Lipschitz dependence on the parameter
    intro a s
    have hexp : (1 - q a s * Real.sin (delta b s)) - (1 - q b s * Real.sin (delta b s))
        = -((q a s - q b s) * Real.sin (delta b s)) := by ring
    rw [hexp, abs_neg, abs_mul]
    calc |q a s - q b s| * |Real.sin (delta b s)| ≤ (Qlip * |a - b|) * 1 := by
          refine mul_le_mul (hqlip a b s) (Real.abs_sin_le_one _) (abs_nonneg _) ?_
          exact le_trans (abs_nonneg _) (hqlip a b s)
      _ = Qlip * |a - b| := by ring

/-- **The selected steering angle is jointly continuous.**  It is continuous in
the angle for each parameter, and Lipschitz in the parameter uniformly in the
angle. -/
theorem continuous_uncurry_delta (hP : 0 < P) (hkap : 0 < kap) (hkap1 : kap < 1)
    (hsol : ∀ a x, HasDerivAt (delta a) (1 - q a x * Real.sin (delta a x)) x)
    (hper : ∀ a, Function.Periodic (delta a) P)
    (hstrip : ∀ a x, delta a x ∈ Icc (0 : ℝ) (arcsin kap))
    (hqlow : ∀ a x, kap⁻¹ ≤ q a x)
    (hqlip : ∀ a b x, |q a x - q b x| ≤ Qlip * |a - b|) :
    Continuous (uncurry delta) := by
  set L : ℝ := Qlip / (Real.sqrt (1 - kap ^ 2) / kap) with hL
  have hmpos : 0 < Real.sqrt (1 - kap ^ 2) := Real.sqrt_pos.mpr (by nlinarith)
  have hcpos : 0 < Real.sqrt (1 - kap ^ 2) / kap := div_pos hmpos hkap
  have hQlip0 : 0 ≤ Qlip := by
    have := hqlip 1 0 0
    have h1 : (0 : ℝ) ≤ Qlip * |(1 : ℝ) - 0| := le_trans (abs_nonneg _) this
    simpa using h1
  have hLnn : 0 ≤ L := by rw [hL]; positivity
  rw [Metric.continuous_iff]
  rintro ⟨a0, x0⟩ ε hε
  obtain ⟨d1, hd1pos, hd1⟩ :=
    Metric.continuousAt_iff.1
      ((continuous_delta_slice hsol a0).continuousAt (x := x0)) (ε / 2) (by linarith)
  refine ⟨min d1 (ε / (2 * (L + 1))), lt_min hd1pos (by positivity), ?_⟩
  rintro ⟨a, x⟩ hb
  rw [Prod.dist_eq, max_lt_iff] at hb
  obtain ⟨hba, hbx⟩ := hb
  have hbx' : dist x x0 < d1 := lt_of_lt_of_le hbx (min_le_left _ _)
  have hba' : |a - a0| < ε / (2 * (L + 1)) := by
    rw [← Real.dist_eq]
    exact lt_of_lt_of_le hba (min_le_right _ _)
  have h1 : |delta a x - delta a0 x| ≤ L * |a - a0| := by
    have := abs_delta_sub_le hP hkap hkap1 hsol hper hstrip hqlow hqlip a a0 x
    calc |delta a x - delta a0 x| ≤ Qlip * |a - a0| / (Real.sqrt (1 - kap ^ 2) / kap) := this
      _ = L * |a - a0| := by rw [hL]; ring
  have h2 : dist (delta a0 x) (delta a0 x0) < ε / 2 := hd1 hbx'
  have h3 : L * |a - a0| < ε / 2 := by
    have hlt : L * |a - a0| ≤ L * (ε / (2 * (L + 1))) :=
      mul_le_mul_of_nonneg_left hba'.le hLnn
    have hstep : L * (ε / (2 * (L + 1))) < ε / 2 := by
      rw [mul_div_assoc']
      rw [div_lt_div_iff₀ (by positivity) (by norm_num)]
      nlinarith [hε]
    linarith
  have : dist (uncurry delta (a, x)) (uncurry delta (a0, x0))
      ≤ |delta a x - delta a0 x| + dist (delta a0 x) (delta a0 x0) := by
    simp only [uncurry, Real.dist_eq]
    calc |delta a x - delta a0 x0| ≤ |delta a x - delta a0 x| + |delta a0 x - delta a0 x0| :=
          abs_sub_le _ _ _
      _ = |delta a x - delta a0 x| + dist (delta a0 x) (delta a0 x0) := by rw [Real.dist_eq]
  linarith

/-- **The derivative of the selected steering angle in the path parameter**, at
every parameter: it is the periodic solution of the linearized equation
produced by the Green operator. -/
theorem hasDerivAt_param_steering (hP : 0 < P) (hkap : 0 < kap) (hkap1 : kap < 1)
    (hqcont : Continuous (uncurry q)) (hqdcont : Continuous (uncurry qd))
    (hsol : ∀ a x, HasDerivAt (delta a) (1 - q a x * Real.sin (delta a x)) x)
    (hper : ∀ a, Function.Periodic (delta a) P)
    (hstrip : ∀ a x, delta a x ∈ Icc (0 : ℝ) (arcsin kap))
    (hqlow : ∀ a x, kap⁻¹ ≤ q a x) (hqup : ∀ a x, q a x ≤ Q)
    (hqper : ∀ a, Function.Periodic (q a) P) (hqdper : ∀ a, Function.Periodic (qd a) P)
    (hqlip : ∀ a b x, |q a x - q b x| ≤ Qlip * |a - b|)
    (hqtaylor : ∀ a b x, |q a x - q b x - (a - b) * qd b x| ≤ Cq * (a - b) ^ 2)
    (hqdbd : ∀ a x, |qd a x| ≤ Qd) (hCq : 0 ≤ Cq) (a x : ℝ) :
    HasDerivAt (fun b => delta b x) (variation q qd delta P a x) a := by
  refine SteeringSmoothDependence.hasDerivAt_selected_steering (q := q) (delta := delta)
    (qdot := qd a) (w := variation q qd delta P a) (a0 := a) (P := P) (kap := kap) (Q := Q)
    (Qd := Qd) (Qlip := Qlip) (Cq := Cq) hP hkap hkap1 hsol hper hstrip hqlow hqup
    (fun b s => hqlip b a s) (fun b s => hqtaylor b a s) (fun s => hqdbd a s) hCq ?_ ?_ x
  · exact fun s =>
      hasDerivAt_variation hP hkap hkap1 hqcont hqdcont hsol hqlow hstrip hqper hqdper hper a s
  · exact periodic_variation hqcont hsol hqper hqdper hper a

/-- **The selected steering angle is jointly `C¹` in the path parameter and the
tangent angle**, its partial derivatives being the periodic solution
`w = 𝒢(-q̇ sin δ)` of the linearized equation and the steering field
`1 - q sin δ`.  This is the joint form of the paper's lemma *Smooth dependence
of the selected rear* at the level of the steering angle. -/
theorem contDiff_one_uncurry_delta (hP : 0 < P) (hkap : 0 < kap) (hkap1 : kap < 1)
    (hqcont : Continuous (uncurry q)) (hqdcont : Continuous (uncurry qd))
    (hsol : ∀ a x, HasDerivAt (delta a) (1 - q a x * Real.sin (delta a x)) x)
    (hper : ∀ a, Function.Periodic (delta a) P)
    (hstrip : ∀ a x, delta a x ∈ Icc (0 : ℝ) (arcsin kap))
    (hqlow : ∀ a x, kap⁻¹ ≤ q a x) (hqup : ∀ a x, q a x ≤ Q)
    (hqper : ∀ a, Function.Periodic (q a) P) (hqdper : ∀ a, Function.Periodic (qd a) P)
    (hqlip : ∀ a b x, |q a x - q b x| ≤ Qlip * |a - b|)
    (hqtaylor : ∀ a b x, |q a x - q b x - (a - b) * qd b x| ≤ Cq * (a - b) ^ 2)
    (hqdbd : ∀ a x, |qd a x| ≤ Qd) (hCq : 0 ≤ Cq) :
    ContDiff ℝ 1 (uncurry delta) := by
  have hdcont : Continuous (uncurry delta) :=
    continuous_uncurry_delta hP hkap hkap1 hsol hper hstrip hqlow hqlip
  -- the two partial derivatives
  have h1 : ∀ a x, HasDerivAt (fun b => delta b x) (variation q qd delta P a x) a := fun a x =>
    hasDerivAt_param_steering hP hkap hkap1 hqcont hqdcont hsol hper hstrip hqlow hqup hqper
      hqdper hqlip hqtaylor hqdbd hCq a x
  have h2 : ∀ a x, HasDerivAt (delta a) (1 - q a x * Real.sin (delta a x)) x := hsol
  -- joint continuity of the first
  have hlinC : Continuous (uncurry (linCoeff q delta)) := by
    have : uncurry (linCoeff q delta)
        = fun p : ℝ × ℝ => uncurry q p * Real.cos (uncurry delta p) := rfl
    rw [this]
    exact hqcont.mul (Real.continuous_cos.comp hdcont)
  have hlinS : Continuous (uncurry (linSource qd delta)) := by
    have : uncurry (linSource qd delta)
        = fun p : ℝ × ℝ => -(uncurry qd p * Real.sin (uncurry delta p)) := rfl
    rw [this]
    exact (hqdcont.mul (Real.continuous_sin.comp hdcont)).neg
  have hc1 : Continuous (uncurry (variation q qd delta P)) := by
    have hpos : ∀ a, 0 < prim (linCoeff q delta a) P := fun a =>
      prim_linCoeff_pos hP hkap hkap1 hqcont hsol hqlow hstrip a
    have := continuous_periodicGreen_param (A := linCoeff q delta) (F := linSource qd delta)
      (l := P) hlinC hlinS hpos
    exact this
  have hc2 : Continuous (uncurry fun a x => 1 - q a x * Real.sin (delta a x)) := by
    have : (uncurry fun a x => 1 - q a x * Real.sin (delta a x))
        = fun p : ℝ × ℝ => 1 - uncurry q p * Real.sin (uncurry delta p) := rfl
    rw [this]
    exact continuous_const.sub (hqcont.mul (Real.continuous_sin.comp hdcont))
  exact JointC1.contDiff_one_of_continuous_partials h1 h2 hc1 hc2

end SteeringJointC1
