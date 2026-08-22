import Mathlib
import UnitTangentIterates.PeriodicGreenJoint
import UnitTangentIterates.SteeringSmoothDependence
import UnitTangentIterates.JointC1

/-!
# The selected steering angle in arclength is jointly `C¹`

`SteeringJointC1.lean` proves the joint `C¹` regularity of the selected
steering angle in the *tangent-angle* parametrization of the front, in which
the paper *A Noncircular Oval with Convex Unit-Tangent Iterates* states the
lemma *Smooth dependence of the selected rear*.  The assembly of the path
metric, on the other hand, works in the **arclength** of the front, where the
steering equation reads

```
  δ_s = K(a, s) - sin δ ,
```

`K` being the curvature of the front.  This file carries the same argument
there: the equation is dissipative on the selected strip, with rate
`cos δ ≥ √(1-κ̂²) > 0`, so the periodic Green operator of `PeriodicGreen.lean`
produces the periodic solution

```
  w(a, ·) = 𝒢_{cos δ(a,·)} (K̇(a,·))
```

of the linearized equation `w_s + cos δ · w = K̇`, which is the derivative of
the steering angle in the path parameter; `PeriodicGreenJoint.lean` makes it
jointly continuous, and the bridge of `JointC1.lean` turns the two partial
derivatives into joint `C¹` regularity.

The slices are asked to share one arclength period `P`, since the maximum
principle behind the parameter estimates compares two slices on one period.

Main results:

* `hasDerivAt_arcVariation`, `periodic_arcVariation` — `w(a,·)` is the periodic
  solution of the linearized equation;
* `hasDerivAt_param_arc` — `∂_a δ(a, s) = w(a, s)`;
* `continuous_uncurry_delta_arc` — joint continuity;
* `contDiff_one_uncurry_delta_arc` — **the selected steering angle in
  arclength is jointly `C¹`**.
-/

noncomputable section

open Function Set Real

namespace SteeringArclengthJointC1

open PeriodicGreen PeriodicGreenJoint

variable {K Kd delta : ℝ → ℝ → ℝ} {P kap Klip CK : ℝ}

/-- The variation of the selected steering angle in arclength: the periodic
solution of `w_s + cos δ · w = K̇`, produced by the periodic Green operator. -/
def arcVariation (Kd delta : ℝ → ℝ → ℝ) (P a : ℝ) : ℝ → ℝ :=
  periodicGreen (fun s => Real.cos (delta a s)) P (Kd a)

/-- Each slice of the steering angle is continuous. -/
theorem continuous_delta_slice
    (hsol : ∀ a s, HasDerivAt (delta a) (K a s - Real.sin (delta a s)) s) (a : ℝ) :
    Continuous (delta a) := by
  have hdiff : Differentiable ℝ (delta a) := fun s => (hsol a s).differentiableAt
  exact hdiff.continuous

theorem cos_delta_ge (hstrip : ∀ a s, delta a s ∈ Icc (0 : ℝ) (arcsin kap)) (a s : ℝ) :
    Real.sqrt (1 - kap ^ 2) ≤ Real.cos (delta a s) :=
  Shadowing.cos_ge_of_mem_strip (hstrip a s).1 (hstrip a s).2

/-- The primitive of `cos δ` over one period is positive. -/
theorem prim_cos_pos (hP : 0 < P) (hkap0 : 0 ≤ kap) (hkap1 : kap < 1)
    (hsol : ∀ a s, HasDerivAt (delta a) (K a s - Real.sin (delta a s)) s)
    (hstrip : ∀ a s, delta a s ∈ Icc (0 : ℝ) (arcsin kap)) (a : ℝ) :
    0 < prim (fun s => Real.cos (delta a s)) P := by
  have hmpos : 0 < Real.sqrt (1 - kap ^ 2) := Real.sqrt_pos.mpr (by nlinarith)
  have hcont : Continuous fun s => Real.cos (delta a s) :=
    Real.continuous_cos.comp (continuous_delta_slice hsol a)
  have hmono : (∫ _ in (0 : ℝ)..P, Real.sqrt (1 - kap ^ 2))
      ≤ ∫ s in (0 : ℝ)..P, Real.cos (delta a s) := by
    refine intervalIntegral.integral_mono_on hP.le intervalIntegrable_const
      (hcont.intervalIntegrable _ _) (fun s _ => cos_delta_ge hstrip a s)
  have hconst : (∫ _ in (0 : ℝ)..P, Real.sqrt (1 - kap ^ 2)) = Real.sqrt (1 - kap ^ 2) * P := by
    simp [mul_comm]
  have hpos : 0 < Real.sqrt (1 - kap ^ 2) * P := by positivity
  rw [prim]
  have hge : Real.sqrt (1 - kap ^ 2) * P ≤ ∫ s in (0 : ℝ)..P, Real.cos (delta a s) := by
    rw [← hconst]; exact hmono
  linarith

theorem periodic_cos_delta (hper : ∀ a, Function.Periodic (delta a) P) (a : ℝ) :
    Function.Periodic (fun s => Real.cos (delta a s)) P := by
  intro s
  simp only [hper a s]

/-- **The variation solves the linearized steering equation** `w_s + cos δ · w = K̇`. -/
theorem hasDerivAt_arcVariation (hP : 0 < P) (hkap0 : 0 ≤ kap) (hkap1 : kap < 1)
    (hKdcont : Continuous (uncurry Kd))
    (hsol : ∀ a s, HasDerivAt (delta a) (K a s - Real.sin (delta a s)) s)
    (hstrip : ∀ a s, delta a s ∈ Icc (0 : ℝ) (arcsin kap))
    (hper : ∀ a, Function.Periodic (delta a) P) (hKdper : ∀ a, Function.Periodic (Kd a) P)
    (a s : ℝ) :
    HasDerivAt (arcVariation Kd delta P a)
      (-Real.cos (delta a s) * arcVariation Kd delta P a s + Kd a s) s := by
  have hcos : Continuous fun s => Real.cos (delta a s) :=
    Real.continuous_cos.comp (continuous_delta_slice hsol a)
  have hKdslice : Continuous (Kd a) := hKdcont.comp (continuous_const.prodMk continuous_id)
  have h := periodicGreen_hasDerivAt (a := fun s => Real.cos (delta a s)) (l := P) (f := Kd a)
    hcos (periodic_cos_delta hper a) (prim_cos_pos hP hkap0 hkap1 hsol hstrip a) hKdslice
    (hKdper a) s
  refine h.congr_deriv ?_
  simp only [arcVariation]
  ring

/-- The variation is `P`-periodic. -/
theorem periodic_arcVariation
    (hsol : ∀ a s, HasDerivAt (delta a) (K a s - Real.sin (delta a s)) s)
    (hper : ∀ a, Function.Periodic (delta a) P) (hKdper : ∀ a, Function.Periodic (Kd a) P)
    (a : ℝ) : Function.Periodic (arcVariation Kd delta P a) P :=
  periodicGreen_periodic (Real.continuous_cos.comp (continuous_delta_slice hsol a))
    (periodic_cos_delta hper a) (hKdper a)

/-- **The selected steering angle is Lipschitz in the path parameter**, with a
constant uniform in the arclength. -/
theorem abs_delta_sub_le (hP : 0 < P) (hkap0 : 0 ≤ kap) (hkap1 : kap < 1)
    (hsol : ∀ a s, HasDerivAt (delta a) (K a s - Real.sin (delta a s)) s)
    (hper : ∀ a, Function.Periodic (delta a) P)
    (hstrip : ∀ a s, delta a s ∈ Icc (0 : ℝ) (arcsin kap))
    (hKlip : ∀ a b s, |K a s - K b s| ≤ Klip * |a - b|) (a b s : ℝ) :
    |delta a s - delta b s| ≤ Klip * |a - b| / Real.sqrt (1 - kap ^ 2) := by
  set m : ℝ := Real.sqrt (1 - kap ^ 2) with hm
  have hmpos : 0 < m := Real.sqrt_pos.mpr (by nlinarith)
  refine PeriodicParameterDeriv.abs_param_diff_le_periodic
    (f := fun a s u => K a s - Real.sin u) (y := delta) (a0 := b) (P := P) (c := m)
    (A := Klip) hP hmpos hsol hper ?_ ?_ a s
  · intro a s
    have hsin := SelectedRear.sin_sub_mul_self_ge (kap := kap) (hstrip a s) (hstrip b s)
    have hexp : (K a s - Real.sin (delta a s) - (K a s - Real.sin (delta b s)))
        * (delta a s - delta b s)
        = -((Real.sin (delta a s) - Real.sin (delta b s)) * (delta a s - delta b s)) := by ring
    rw [hexp]
    linarith
  · intro a s
    simpa using hKlip a b s

/-- **The selected steering angle in arclength is jointly continuous.** -/
theorem continuous_uncurry_delta_arc (hP : 0 < P) (hkap0 : 0 ≤ kap) (hkap1 : kap < 1)
    (hsol : ∀ a s, HasDerivAt (delta a) (K a s - Real.sin (delta a s)) s)
    (hper : ∀ a, Function.Periodic (delta a) P)
    (hstrip : ∀ a s, delta a s ∈ Icc (0 : ℝ) (arcsin kap))
    (hKlip : ∀ a b s, |K a s - K b s| ≤ Klip * |a - b|) :
    Continuous (uncurry delta) := by
  have hmpos : 0 < Real.sqrt (1 - kap ^ 2) := Real.sqrt_pos.mpr (by nlinarith)
  set L : ℝ := Klip / Real.sqrt (1 - kap ^ 2) with hL
  have hKlip0 : 0 ≤ Klip := by
    have h := hKlip 1 0 0
    have h1 : (0 : ℝ) ≤ Klip * |(1 : ℝ) - 0| := le_trans (abs_nonneg _) h
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
    have h := abs_delta_sub_le hP hkap0 hkap1 hsol hper hstrip hKlip a a0 x
    calc |delta a x - delta a0 x| ≤ Klip * |a - a0| / Real.sqrt (1 - kap ^ 2) := h
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
  have hsplit : dist (uncurry delta (a, x)) (uncurry delta (a0, x0))
      ≤ |delta a x - delta a0 x| + dist (delta a0 x) (delta a0 x0) := by
    simp only [uncurry, Real.dist_eq]
    calc |delta a x - delta a0 x0| ≤ |delta a x - delta a0 x| + |delta a0 x - delta a0 x0| :=
          abs_sub_le _ _ _
      _ = |delta a x - delta a0 x| + dist (delta a0 x) (delta a0 x0) := by rw [Real.dist_eq]
  linarith

/-- **The derivative of the selected steering angle in the path parameter**, in
arclength: it is the periodic solution of `w_s + cos δ · w = K̇` produced by the
Green operator. -/
theorem hasDerivAt_param_arc (hP : 0 < P) (hkap0 : 0 ≤ kap) (hkap1 : kap < 1)
    (hKdcont : Continuous (uncurry Kd))
    (hsol : ∀ a s, HasDerivAt (delta a) (K a s - Real.sin (delta a s)) s)
    (hper : ∀ a, Function.Periodic (delta a) P)
    (hstrip : ∀ a s, delta a s ∈ Icc (0 : ℝ) (arcsin kap))
    (hKdper : ∀ a, Function.Periodic (Kd a) P)
    (hKlip : ∀ a b s, |K a s - K b s| ≤ Klip * |a - b|)
    (hKtaylor : ∀ a b s, |K a s - K b s - (a - b) * Kd b s| ≤ CK * (a - b) ^ 2)
    (hCK : 0 ≤ CK) (a s : ℝ) :
    HasDerivAt (fun b => delta b s) (arcVariation Kd delta P a s) a := by
  set m : ℝ := Real.sqrt (1 - kap ^ 2) with hm
  have hmpos : 0 < m := Real.sqrt_pos.mpr (by nlinarith)
  refine PeriodicParameterDeriv.hasDerivAt_param_periodic
    (f := fun a s u => K a s - Real.sin u) (fa := fun a s _ => Kd a s)
    (fy := fun _ _ u => -Real.cos u) (y := delta) (w := arcVariation Kd delta P a)
    (a0 := a) (P := P) (c := m) (C := CK + 1) (A := Klip)
    hP hmpos (by linarith) hsol hper ?_ ?_ ?_ ?_ ?_ ?_ s
  · -- dissipativity
    intro b s
    have hsin := SelectedRear.sin_sub_mul_self_ge (kap := kap) (hstrip b s) (hstrip a s)
    have hexp : (K b s - Real.sin (delta b s) - (K b s - Real.sin (delta a s)))
        * (delta b s - delta a s)
        = -((Real.sin (delta b s) - Real.sin (delta a s)) * (delta b s - delta a s)) := by ring
    rw [hexp]
    linarith
  · -- Lipschitz dependence on the parameter
    intro b s
    simpa using hKlip b a s
  · -- the linearized coefficient is bounded below
    intro s
    simpa using cos_delta_ge hstrip a s
  · -- the Taylor remainder is quadratic
    intro b s
    set k : ℝ := delta b s - delta a s with hk
    have hsintaylor : |Real.sin (delta b s) - Real.sin (delta a s)
        - Real.cos (delta a s) * k| ≤ k ^ 2 := by
      have h := SteeringSmoothDependence.abs_sin_taylor (delta a s) k
      have hks : delta a s + k = delta b s := by rw [hk]; ring
      rwa [hks] at h
    have hKt : |K b s - K a s - (b - a) * Kd a s| ≤ CK * (b - a) ^ 2 := hKtaylor b a s
    have hid : (K b s - Real.sin (delta b s) - (K a s - Real.sin (delta a s))
        - Kd a s * (b - a) - (-Real.cos (delta a s)) * k)
        = (K b s - K a s - (b - a) * Kd a s)
          - (Real.sin (delta b s) - Real.sin (delta a s) - Real.cos (delta a s) * k) := by
      rw [hk]; ring
    rw [hid]
    have hsum : |K b s - K a s - (b - a) * Kd a s
        - (Real.sin (delta b s) - Real.sin (delta a s) - Real.cos (delta a s) * k)|
        ≤ CK * (b - a) ^ 2 + k ^ 2 := by
      refine le_trans (abs_sub _ _) ?_
      linarith
    have hfinal : CK * (b - a) ^ 2 + k ^ 2 ≤ (CK + 1) * ((b - a) ^ 2 + k ^ 2) := by nlinarith
    linarith
  · -- the linearized solution
    intro s
    have h := hasDerivAt_arcVariation (K := K) hP hkap0 hkap1 hKdcont hsol hstrip hper hKdper a s
    exact h.congr_deriv (by ring)
  · exact periodic_arcVariation hsol hper hKdper a

/-- **The selected steering angle in arclength is jointly `C¹`** in the path
parameter and the arclength, its partial derivatives being the periodic
solution `w = 𝒢(K̇)` of the linearized equation and the steering field
`K - sin δ`. -/
theorem contDiff_one_uncurry_delta_arc (hP : 0 < P) (hkap0 : 0 ≤ kap) (hkap1 : kap < 1)
    (hKcont : Continuous (uncurry K)) (hKdcont : Continuous (uncurry Kd))
    (hsol : ∀ a s, HasDerivAt (delta a) (K a s - Real.sin (delta a s)) s)
    (hper : ∀ a, Function.Periodic (delta a) P)
    (hstrip : ∀ a s, delta a s ∈ Icc (0 : ℝ) (arcsin kap))
    (hKdper : ∀ a, Function.Periodic (Kd a) P)
    (hKlip : ∀ a b s, |K a s - K b s| ≤ Klip * |a - b|)
    (hKtaylor : ∀ a b s, |K a s - K b s - (a - b) * Kd b s| ≤ CK * (a - b) ^ 2)
    (hCK : 0 ≤ CK) :
    ContDiff ℝ 1 (uncurry delta) := by
  have hdcont : Continuous (uncurry delta) :=
    continuous_uncurry_delta_arc hP hkap0 hkap1 hsol hper hstrip hKlip
  have h1 : ∀ a s, HasDerivAt (fun b => delta b s) (arcVariation Kd delta P a s) a := fun a s =>
    hasDerivAt_param_arc hP hkap0 hkap1 hKdcont hsol hper hstrip hKdper hKlip hKtaylor hCK a s
  have hcosC : Continuous (uncurry fun a s => Real.cos (delta a s)) := by
    have heq : (uncurry fun a s => Real.cos (delta a s))
        = fun p : ℝ × ℝ => Real.cos (uncurry delta p) := rfl
    rw [heq]
    exact Real.continuous_cos.comp hdcont
  have hc1 : Continuous (uncurry (arcVariation Kd delta P)) := by
    have hpos : ∀ a, 0 < prim (fun s => Real.cos (delta a s)) P := fun a =>
      prim_cos_pos hP hkap0 hkap1 hsol hstrip a
    exact continuous_periodicGreen_param (A := fun a s => Real.cos (delta a s)) (F := Kd)
      (l := P) hcosC hKdcont hpos
  have hc2 : Continuous (uncurry fun a s => K a s - Real.sin (delta a s)) := by
    have heq : (uncurry fun a s => K a s - Real.sin (delta a s))
        = fun p : ℝ × ℝ => uncurry K p - Real.sin (uncurry delta p) := rfl
    rw [heq]
    exact hKcont.sub (Real.continuous_sin.comp hdcont)
  exact JointC1.contDiff_one_of_continuous_partials h1 hsol hc1 hc2

/-! ### A worked instance

The hypotheses are consistent: for the path of circles of curvature
`k(a) = (3 + sin a)/8` the selected steering angle is the constant
`arcsin k(a)`, and every hypothesis holds with `κ̂ = 1/2`. -/

namespace Instance

/-- The curvature of the instance: the circle of curvature `(3 + sin a)/8`. -/
def curv (a : ℝ) (_ : ℝ) : ℝ := (3 + Real.sin a) / 8

/-- Its derivative in the path parameter. -/
def curvDot (a : ℝ) (_ : ℝ) : ℝ := Real.cos a / 8

/-- The selected steering angle of the instance. -/
def steer (a : ℝ) (_ : ℝ) : ℝ := Real.arcsin ((3 + Real.sin a) / 8)

theorem curv_bounds (a s : ℝ) : (1 : ℝ) / 4 ≤ curv a s ∧ curv a s ≤ 1 / 2 := by
  have h := Real.neg_one_le_sin a
  have h' := Real.sin_le_one a
  constructor <;> simp only [curv] <;> linarith

theorem sin_steer (a s : ℝ) : Real.sin (steer a s) = curv a s := by
  have h1 := (curv_bounds a s).1
  have h2 := (curv_bounds a s).2
  have hle : curv a s ≤ 1 := by linarith
  have hge : -1 ≤ curv a s := by linarith
  exact Real.sin_arcsin hge hle

/-- **The hypotheses of the arclength joint regularity theorem are
consistent.**  For the path of circles of curvature `(3 + sin a)/8`, whose
selected steering angle is the constant `arcsin((3 + sin a)/8)`, every
hypothesis of `contDiff_one_uncurry_delta_arc` holds, with `κ̂ = 1/2`,
`K_lip = C_K = 1/8` and any period `P > 0`. -/
theorem steering_arc_jointC1_instance {P : ℝ} (hP : 0 < P) :
    ContDiff ℝ 1 (uncurry steer) ∧
      ∀ a s, HasDerivAt (fun b => steer b s) (arcVariation curvDot steer P a s) a := by
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
  have hKcont : Continuous (uncurry curv) :=
    ((continuous_const.add (Real.continuous_sin.comp continuous_fst)).div_const 8)
  have hKdcont : Continuous (uncurry curvDot) :=
    (Real.continuous_cos.comp continuous_fst).div_const 8
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
  refine ⟨contDiff_one_uncurry_delta_arc (K := curv) hP (by norm_num) (by norm_num) hKcont
      hKdcont hsol hper hstrip hKdper hKlip hKtaylor (by norm_num), fun a s => ?_⟩
  exact hasDerivAt_param_arc (K := curv) hP (by norm_num) (by norm_num) hKdcont hsol hper hstrip
    hKdper hKlip hKtaylor (by norm_num) a s

end Instance

end SteeringArclengthJointC1
