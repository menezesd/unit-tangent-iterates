import Mathlib
import UnitTangentIterates.SteeringArclengthJointC1
import UnitTangentIterates.PeriodicGreenSmooth
import UnitTangentIterates.RearOwnTangential

/-!
# The selected steering angle is jointly as smooth as the front curvature

`SteeringArclengthJointC1.lean` proves that the selected steering angle of a
path of fronts, in the arclength of the front, is jointly `C¹` in the path
parameter and the arclength, and identifies its derivative in the path
parameter as the periodic solution

```
  w(a, ·) = 𝒢_{cos δ(a,·)} (K̇(a,·))
```

of the linearized equation.  That identification is what unlocks all the higher
orders, by a bootstrap:

* if the steering angle is jointly `Cᵏ`, then so is `cos δ`, and the Green
  operator is jointly `Cᵏ` in its data (`PeriodicGreenSmooth.lean`), so the
  parameter derivative `w` is jointly `Cᵏ`;
* the arclength derivative `K - sin δ` is jointly `Cᵏ` as well;
* two jointly `Cᵏ` partial derivatives make the function jointly `C^{k+1}`
  (`RearOwnTangential.contDiff_succ_of_partials`).

So joint `Cⁿ` regularity of the front curvature and of its derivative in the
path parameter gives joint `C^{n+1}` regularity of the selected steering
angle — in particular the joint `C⁴` regularity the assembly of the path metric
consumes.

Main results:

* `contDiff_arcVariation_of_contDiff` — the parameter derivative is as smooth
  as the data;
* `contDiff_succ_uncurry_delta_arc` — **the selected steering angle is jointly
  `C^{n+1}`**;
* `contDiff_four_uncurry_delta_arc` — the joint `C⁴` case.
-/

noncomputable section

open Function Set Real

namespace SteeringArclengthSmooth

open PeriodicGreen SteeringArclengthJointC1

variable {K Kd delta : ℝ → ℝ → ℝ} {P kap Klip CK : ℝ} {n : ℕ}

/-- **The parameter derivative of the steering angle is as smooth as the
data.**  It is the Green solution of the linearized equation, whose coefficient
`cos δ` and source `K̇` are jointly `Cⁿ`. -/
theorem contDiff_arcVariation_of_contDiff (hP : 0 < P) (hkap0 : 0 ≤ kap) (hkap1 : kap < 1)
    (hsol : ∀ a s, HasDerivAt (delta a) (K a s - Real.sin (delta a s)) s)
    (hstrip : ∀ a s, delta a s ∈ Icc (0 : ℝ) (arcsin kap))
    (hdelta : ContDiff ℝ (n : ℕ) (uncurry delta)) (hKd : ContDiff ℝ (n : ℕ) (uncurry Kd)) :
    ContDiff ℝ (n : ℕ) (uncurry (arcVariation Kd delta P)) := by
  have hcos : ContDiff ℝ (n : ℕ) (uncurry fun a s => Real.cos (delta a s)) :=
    Real.contDiff_cos.comp hdelta
  have hpos : ∀ a, 0 < prim (fun s => Real.cos (delta a s)) P := fun a =>
    prim_cos_pos hP hkap0 hkap1 hsol hstrip a
  exact PeriodicGreenSmooth.contDiff_periodicGreen_param
    (A := fun a s => Real.cos (delta a s)) (F := Kd) (l := P) hcos hKd hpos

/-- **The selected steering angle in arclength is jointly `C^{n+1}`** as soon
as the front curvature and its derivative in the path parameter are jointly
`Cⁿ`. -/
theorem contDiff_succ_uncurry_delta_arc (hP : 0 < P) (hkap0 : 0 ≤ kap) (hkap1 : kap < 1)
    (hsol : ∀ a s, HasDerivAt (delta a) (K a s - Real.sin (delta a s)) s)
    (hper : ∀ a, Function.Periodic (delta a) P)
    (hstrip : ∀ a s, delta a s ∈ Icc (0 : ℝ) (arcsin kap))
    (hKdper : ∀ a, Function.Periodic (Kd a) P)
    (hKlip : ∀ a b s, |K a s - K b s| ≤ Klip * |a - b|)
    (hKtaylor : ∀ a b s, |K a s - K b s - (a - b) * Kd b s| ≤ CK * (a - b) ^ 2)
    (hCK : 0 ≤ CK) (hK : ContDiff ℝ (n : ℕ) (uncurry K))
    (hKd : ContDiff ℝ (n : ℕ) (uncurry Kd)) :
    ContDiff ℝ ((n + 1 : ℕ)) (uncurry delta) := by
  -- the derivative in the path parameter, at every parameter
  have hdt : ∀ a s, HasDerivAt (fun b => delta b s) (arcVariation Kd delta P a s) a :=
    fun a s => hasDerivAt_param_arc hP hkap0 hkap1 hKd.continuous hsol hper hstrip hKdper
      hKlip hKtaylor hCK a s
  induction n with
  | zero =>
      have h := contDiff_one_uncurry_delta_arc hP hkap0 hkap1 hK.continuous hKd.continuous
        hsol hper hstrip hKdper hKlip hKtaylor hCK
      simpa using h
  | succ k ih =>
      have hle : ((k : ℕ) : WithTop ℕ∞) ≤ ((k + 1 : ℕ) : WithTop ℕ∞) := by
        exact_mod_cast (by omega : (k : ℕ) ≤ k + 1)
      have hdelta : ContDiff ℝ ((k + 1 : ℕ)) (uncurry delta) :=
        ih (hK.of_le hle) (hKd.of_le hle)
      have hw : ContDiff ℝ ((k + 1 : ℕ)) (uncurry (arcVariation Kd delta P)) :=
        contDiff_arcVariation_of_contDiff hP hkap0 hkap1 hsol hstrip hdelta hKd
      have hs : ContDiff ℝ ((k + 1 : ℕ)) (uncurry fun a s => K a s - Real.sin (delta a s)) :=
        hK.sub (Real.contDiff_sin.comp hdelta)
      exact RearOwnTangential.contDiff_succ_of_partials hdt hsol hw hs

/-- The joint `C⁴` regularity of the selected steering angle, the form the
assembly of the path metric consumes: it follows from joint `C³` regularity of
the front curvature and of its derivative in the path parameter. -/
theorem contDiff_four_uncurry_delta_arc (hP : 0 < P) (hkap0 : 0 ≤ kap) (hkap1 : kap < 1)
    (hsol : ∀ a s, HasDerivAt (delta a) (K a s - Real.sin (delta a s)) s)
    (hper : ∀ a, Function.Periodic (delta a) P)
    (hstrip : ∀ a s, delta a s ∈ Icc (0 : ℝ) (arcsin kap))
    (hKdper : ∀ a, Function.Periodic (Kd a) P)
    (hKlip : ∀ a b s, |K a s - K b s| ≤ Klip * |a - b|)
    (hKtaylor : ∀ a b s, |K a s - K b s - (a - b) * Kd b s| ≤ CK * (a - b) ^ 2)
    (hCK : 0 ≤ CK) (hK : ContDiff ℝ (3 : ℕ) (uncurry K))
    (hKd : ContDiff ℝ (3 : ℕ) (uncurry Kd)) :
    ContDiff ℝ (4 : ℕ) (uncurry delta) := by
  have h := contDiff_succ_uncurry_delta_arc (n := 3) hP hkap0 hkap1 hsol hper hstrip hKdper
    hKlip hKtaylor hCK hK hKd
  simpa using h

/-! ### The worked instance, to fourth order -/

open SteeringArclengthJointC1.Instance in
/-- The hypotheses of the joint `C⁴` form are consistent: they hold for the
path of circles of curvature `(3 + sin a)/8`. -/
theorem steering_arc_contDiff_four_instance {P : ℝ} (hP : 0 < P) :
    ContDiff ℝ (4 : ℕ) (uncurry steer) := by
  have hsol : ∀ a s, HasDerivAt (steer a) (curv a s - Real.sin (steer a s)) s := by
    intro a s
    have hz : curv a s - Real.sin (steer a s) = 0 := by rw [sin_steer a s]; ring
    rw [hz]
    exact hasDerivAt_const s _
  have hper : ∀ a, Function.Periodic (steer a) P := fun a s => rfl
  have hstrip : ∀ a s, steer a s ∈ Icc (0 : ℝ) (arcsin (1 / 2)) := by
    intro a s
    have h1 := (curv_bounds a s).1
    have h2 := (curv_bounds a s).2
    have hd : steer a s = Real.arcsin (curv a s) := rfl
    rw [hd]
    exact ⟨Real.arcsin_nonneg.mpr (by linarith), Real.arcsin_le_arcsin h2⟩
  have hKdper : ∀ a, Function.Periodic (curvDot a) P := fun a s => rfl
  have hKlip : ∀ a b s, |curv a s - curv b s| ≤ (1 / 8) * |a - b| := by
    intro a b s
    have h : curv a s - curv b s = (Real.sin a - Real.sin b) / 8 := by
      simp only [curv]; ring
    rw [h, abs_div, abs_of_nonneg (by norm_num : (0:ℝ) ≤ (8:ℝ))]
    have hs : |Real.sin a - Real.sin b| ≤ |a - b| := by
      have := Real.lipschitzWith_sin.dist_le_mul a b
      simpa [Real.dist_eq] using this
    linarith
  have hKtaylor : ∀ a b s,
      |curv a s - curv b s - (a - b) * curvDot b s| ≤ (1 / 8) * (a - b) ^ 2 := by
    intro a b s
    have h : curv a s - curv b s - (a - b) * curvDot b s
        = (Real.sin (b + (a - b)) - Real.sin b - Real.cos b * (a - b)) / 8 := by
      simp only [curv, curvDot]
      ring_nf
    rw [h, abs_div, abs_of_nonneg (by norm_num : (0:ℝ) ≤ (8:ℝ))]
    have := SteeringSmoothDependence.abs_sin_taylor b (a - b)
    linarith
  have hK : ContDiff ℝ (3 : ℕ) (uncurry curv) :=
    (contDiff_const.add (Real.contDiff_sin.comp contDiff_fst)).div_const 8
  have hKd : ContDiff ℝ (3 : ℕ) (uncurry curvDot) :=
    (Real.contDiff_cos.comp contDiff_fst).div_const 8
  exact contDiff_four_uncurry_delta_arc (K := curv) hP (by norm_num) (by norm_num) hsol hper
    hstrip hKdper hKlip hKtaylor (by norm_num) hK hKd

end SteeringArclengthSmooth
