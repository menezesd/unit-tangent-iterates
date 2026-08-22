import Mathlib
import UnitTangentIterates.SteeringVariablePeriod
import UnitTangentIterates.SteeringPeriodRigidity

/-!
# The selected steering angle in the normalized parameter

`SteeringVariablePeriod.lean` proves the joint regularity of the selected
steering angle for slices of moving arclength period, but it asks the parameter
derivative `K̇` of the front curvature to be periodic with the current period
`P(a)`.  `SteeringPeriodRigidity.lean` shows that this combination is rigid: it
forces `P'(a) ∂_sK = 0`, so a genuinely moving period is only possible for
circles.

The reason is the choice of parametrization.  Written in the arclength of each
slice, the parameter derivative of any front datum drifts by `−P'(a) ∂_s(·)`
over one period.  Written in the **normalized** parameter `σ = s / P(a)` every
datum is `1`-periodic for every `a`, and so are all its parameter derivatives.

This file develops the theory in that parametrization.  The steering equation
becomes

```
  ∂_σ δ = P(a) · (K(a,σ) − sin δ(a,σ)) ,
```

with `δ(a, ·)`, `K(a, ·)` and `K̇(a, ·)` all `1`-periodic, and the linearized
equation acquires the extra forcing `P'(a)(K − sin δ)`:

```
  ∂_σ w + P(a) cos δ · w = P'(a)(K − sin δ) + P(a) K̇ .
```

Everything else goes through: the dissipation rate is `P₀√(1−κ̂²) > 0`, the
averaged cosine of `SteeringVariablePeriod` still factors the difference of the
sines, and the Green operator on the circle of length one still inverts the
linearized equation.

Main results:

* `abs_delta_sub_le` — Lipschitz dependence on the path parameter;
* `abs_error_le` — the quadratic error of the linear prediction;
* `hasDerivAt_param` — `∂_a δ = w`, the periodic solution of the linearized
  equation;
* `contDiff_succ_uncurry_delta`, `contDiff_four_uncurry_delta` — joint
  `C^{n+1}` regularity from jointly `Cⁿ` data, with **no** restriction on the
  motion of the period;
* `contDiff_arclength_of_normalized` — the same regularity for the steering
  angle read back in the arclength of each slice, which is the form the
  path-metric assembly consumes.
-/

noncomputable section

open Function Set Real

namespace SteeringNormalizedPeriod

open PeriodicGreen BoundedLinearBound SteeringVariablePeriod

variable {K Kd delta : ℝ → ℝ → ℝ} {Pf Pd : ℝ → ℝ}
  {kap Klip CK Md P0 P1 Plip CP MP : ℝ} {n : ℕ}

/-! ### Constants -/

/-- The dissipation rate of the linearized equation on the selected strip. -/
def dissip (P0 kap : ℝ) : ℝ := P0 * Real.sqrt (1 - kap ^ 2)

/-- The Lipschitz constant of the steering angle in the path parameter. -/
def lipConst (P0 P1 kap Klip Plip : ℝ) : ℝ := (P1 * Klip + 2 * Plip) / dissip P0 kap

/-- The sup bound of the variation. -/
def varBound (P0 P1 kap Md MP : ℝ) : ℝ := (2 * MP + P1 * Md) / dissip P0 kap

/-- The numerator of the quadratic error constant. -/
def errNum (P0 P1 kap Klip CK Md Plip CP MP : ℝ) : ℝ :=
  P1 * CK + Md * Plip + 2 * CP
    + varBound P0 P1 kap Md MP * (P1 * lipConst P0 P1 kap Klip Plip + Plip)

theorem dissip_pos (hP0 : 0 < P0) (hkap0 : 0 ≤ kap) (hkap1 : kap < 1) :
    0 < dissip P0 kap := by
  have : 0 < Real.sqrt (1 - kap ^ 2) := Real.sqrt_pos.mpr (by nlinarith)
  rw [dissip]; positivity

/-! ### The data of the linearized equation -/

/-- The coefficient of the linearized equation: `P(a) cos δ(a, ·)`. -/
def coef (delta : ℝ → ℝ → ℝ) (Pf : ℝ → ℝ) (a : ℝ) : ℝ → ℝ :=
  fun s => Pf a * Real.cos (delta a s)

/-- Its forcing: `P'(a)(K − sin δ) + P(a) K̇`. -/
def source (K Kd delta : ℝ → ℝ → ℝ) (Pf Pd : ℝ → ℝ) (a : ℝ) : ℝ → ℝ :=
  fun s => Pd a * (K a s - Real.sin (delta a s)) + Pf a * Kd a s

/-- The derivative of the steering angle in the path parameter: the `1`-periodic
solution of the linearized equation. -/
def variation (K Kd delta : ℝ → ℝ → ℝ) (Pf Pd : ℝ → ℝ) (a : ℝ) : ℝ → ℝ :=
  periodicGreen (coef delta Pf a) 1 (source K Kd delta Pf Pd a)

theorem continuous_delta_slice
    (hsol : ∀ a s, HasDerivAt (delta a) (Pf a * (K a s - Real.sin (delta a s))) s) (a : ℝ) :
    Continuous (delta a) := by
  have hdiff : Differentiable ℝ (delta a) := fun s => (hsol a s).differentiableAt
  exact hdiff.continuous

/-- The averaged cosine of `SteeringVariablePeriod` is continuous as soon as the
slices are. -/
theorem continuous_avgCos_of_slices (hd : ∀ a, Continuous (delta a)) (a b : ℝ) :
    Continuous (avgCos delta a b) := by
  have hda : Continuous (delta a) := hd a
  have hdb : Continuous (delta b) := hd b
  have hF : Continuous (uncurry fun (s : ℝ) (θ : ℝ) =>
      Real.cos (delta b s + θ * (delta a s - delta b s))) := by
    refine Real.continuous_cos.comp ?_
    exact (hdb.comp continuous_fst).add
      (continuous_snd.mul ((hda.comp continuous_fst).sub (hdb.comp continuous_fst)))
  simpa [avgCos] using
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
      (a₀ := (0 : ℝ)) hF continuous_const

theorem continuous_coef
    (hsol : ∀ a s, HasDerivAt (delta a) (Pf a * (K a s - Real.sin (delta a s))) s) (a : ℝ) :
    Continuous (coef delta Pf a) :=
  continuous_const.mul (Real.continuous_cos.comp (continuous_delta_slice hsol a))

theorem periodic_coef (hper : ∀ a, Function.Periodic (delta a) 1) (a : ℝ) :
    Function.Periodic (coef delta Pf a) 1 := by
  intro s
  simp only [coef, hper a s]

theorem coef_ge (hP0 : 0 < P0) (hPl : ∀ a, P0 ≤ Pf a)
    (hstrip : ∀ a s, delta a s ∈ Icc (0 : ℝ) (arcsin kap)) (a s : ℝ) :
    dissip P0 kap ≤ coef delta Pf a s := by
  have hcos : Real.sqrt (1 - kap ^ 2) ≤ Real.cos (delta a s) :=
    Shadowing.cos_ge_of_mem_strip (hstrip a s).1 (hstrip a s).2
  have hsq : 0 ≤ Real.sqrt (1 - kap ^ 2) := Real.sqrt_nonneg _
  rw [dissip, coef]
  exact mul_le_mul (hPl a) hcos hsq (le_trans hP0.le (hPl a))

theorem continuous_source (hKcont : Continuous (uncurry K)) (hKdcont : Continuous (uncurry Kd))
    (hsol : ∀ a s, HasDerivAt (delta a) (Pf a * (K a s - Real.sin (delta a s))) s) (a : ℝ) :
    Continuous (source K Kd delta Pf Pd a) := by
  have hKa : Continuous (K a) := hKcont.comp (continuous_const.prodMk continuous_id)
  have hKda : Continuous (Kd a) := hKdcont.comp (continuous_const.prodMk continuous_id)
  exact (continuous_const.mul
      (hKa.sub (Real.continuous_sin.comp (continuous_delta_slice hsol a)))).add
    (continuous_const.mul hKda)

theorem periodic_source (hper : ∀ a, Function.Periodic (delta a) 1)
    (hKper : ∀ a, Function.Periodic (K a) 1) (hKdper : ∀ a, Function.Periodic (Kd a) 1)
    (a : ℝ) : Function.Periodic (source K Kd delta Pf Pd a) 1 := by
  intro s
  simp only [source, hper a s, hKper a s, hKdper a s]

theorem abs_source_le (hKdbd : ∀ a s, |Kd a s| ≤ Md) (hPdbd : ∀ a, |Pd a| ≤ MP)
    (hPu : ∀ a, Pf a ≤ P1) (hP0 : 0 < P0) (hPl : ∀ a, P0 ≤ Pf a)
    (hkap1 : kap < 1) (hKbd : ∀ a s, |K a s| ≤ kap) (a s : ℝ) :
    |source K Kd delta Pf Pd a s| ≤ 2 * MP + P1 * Md := by
  have hMd0 : 0 ≤ Md := le_trans (abs_nonneg _) (hKdbd a s)
  have hPfpos : 0 < Pf a := lt_of_lt_of_le hP0 (hPl a)
  have h1 : |K a s - Real.sin (delta a s)| ≤ 2 := by
    have hK := hKbd a s
    have hs1 := Real.neg_one_le_sin (delta a s)
    have hs2 := Real.sin_le_one (delta a s)
    rw [abs_le] at hK ⊢
    constructor <;> linarith [hK.1, hK.2]
  have h2 : |Pd a * (K a s - Real.sin (delta a s))| ≤ MP * 2 := by
    rw [abs_mul]
    exact mul_le_mul (hPdbd a) h1 (abs_nonneg _) (le_trans (abs_nonneg _) (hPdbd a))
  have h3 : |Pf a * Kd a s| ≤ P1 * Md := by
    rw [abs_mul, abs_of_pos hPfpos]
    exact mul_le_mul (hPu a) (hKdbd a s) (abs_nonneg _) (le_trans hPfpos.le (hPu a))
  calc |source K Kd delta Pf Pd a s|
      ≤ |Pd a * (K a s - Real.sin (delta a s))| + |Pf a * Kd a s| := abs_add_le _ _
    _ ≤ MP * 2 + P1 * Md := add_le_add h2 h3
    _ = 2 * MP + P1 * Md := by ring

theorem prim_coef_pos (hP0 : 0 < P0) (hkap0 : 0 ≤ kap) (hkap1 : kap < 1)
    (hPl : ∀ a, P0 ≤ Pf a)
    (hsol : ∀ a s, HasDerivAt (delta a) (Pf a * (K a s - Real.sin (delta a s))) s)
    (hstrip : ∀ a s, delta a s ∈ Icc (0 : ℝ) (arcsin kap)) (a : ℝ) :
    0 < prim (coef delta Pf a) 1 := by
  have hc : Continuous (coef delta Pf a) := continuous_coef hsol a
  have hmono : (∫ _ in (0 : ℝ)..1, dissip P0 kap) ≤ ∫ s in (0 : ℝ)..1, coef delta Pf a s := by
    refine intervalIntegral.integral_mono_on (by norm_num) intervalIntegrable_const
      (hc.intervalIntegrable _ _) (fun s _ => coef_ge hP0 hPl hstrip a s)
  have hpos : 0 < dissip P0 kap := dissip_pos hP0 hkap0 hkap1
  rw [prim]
  simpa using lt_of_lt_of_le (by simpa using hpos) hmono

/-- The variation solves the linearized equation. -/
theorem hasDerivAt_variation (hP0 : 0 < P0) (hkap0 : 0 ≤ kap) (hkap1 : kap < 1)
    (hPl : ∀ a, P0 ≤ Pf a) (hKcont : Continuous (uncurry K)) (hKdcont : Continuous (uncurry Kd))
    (hsol : ∀ a s, HasDerivAt (delta a) (Pf a * (K a s - Real.sin (delta a s))) s)
    (hstrip : ∀ a s, delta a s ∈ Icc (0 : ℝ) (arcsin kap))
    (hper : ∀ a, Function.Periodic (delta a) 1) (hKper : ∀ a, Function.Periodic (K a) 1)
    (hKdper : ∀ a, Function.Periodic (Kd a) 1) (a s : ℝ) :
    HasDerivAt (variation K Kd delta Pf Pd a)
      (source K Kd delta Pf Pd a s
        - coef delta Pf a s * variation K Kd delta Pf Pd a s) s :=
  periodicGreen_hasDerivAt (continuous_coef hsol a) (periodic_coef hper a)
    (prim_coef_pos hP0 hkap0 hkap1 hPl hsol hstrip a)
    (continuous_source hKcont hKdcont hsol a) (periodic_source hper hKper hKdper a) s

theorem periodic_variation
    (hsol : ∀ a s, HasDerivAt (delta a) (Pf a * (K a s - Real.sin (delta a s))) s)
    (hper : ∀ a, Function.Periodic (delta a) 1) (hKper : ∀ a, Function.Periodic (K a) 1)
    (hKdper : ∀ a, Function.Periodic (Kd a) 1) (a : ℝ) :
    Function.Periodic (variation K Kd delta Pf Pd a) 1 :=
  periodicGreen_periodic (continuous_coef hsol a) (periodic_coef hper a)
    (periodic_source hper hKper hKdper a)

theorem continuous_variation (hP0 : 0 < P0) (hkap0 : 0 ≤ kap) (hkap1 : kap < 1)
    (hPl : ∀ a, P0 ≤ Pf a) (hKcont : Continuous (uncurry K)) (hKdcont : Continuous (uncurry Kd))
    (hsol : ∀ a s, HasDerivAt (delta a) (Pf a * (K a s - Real.sin (delta a s))) s)
    (hstrip : ∀ a s, delta a s ∈ Icc (0 : ℝ) (arcsin kap))
    (hper : ∀ a, Function.Periodic (delta a) 1) (hKper : ∀ a, Function.Periodic (K a) 1)
    (hKdper : ∀ a, Function.Periodic (Kd a) 1) (a : ℝ) :
    Continuous (variation K Kd delta Pf Pd a) := by
  have hdiff : Differentiable ℝ (variation K Kd delta Pf Pd a) := fun s =>
    (hasDerivAt_variation hP0 hkap0 hkap1 hPl hKcont hKdcont hsol hstrip hper hKper
      hKdper a s).differentiableAt
  exact hdiff.continuous

/-- **The variation is bounded.** -/
theorem abs_variation_le (hP0 : 0 < P0) (hkap0 : 0 ≤ kap) (hkap1 : kap < 1)
    (hPl : ∀ a, P0 ≤ Pf a) (hPu : ∀ a, Pf a ≤ P1)
    (hKcont : Continuous (uncurry K)) (hKdcont : Continuous (uncurry Kd))
    (hsol : ∀ a s, HasDerivAt (delta a) (Pf a * (K a s - Real.sin (delta a s))) s)
    (hstrip : ∀ a s, delta a s ∈ Icc (0 : ℝ) (arcsin kap))
    (hper : ∀ a, Function.Periodic (delta a) 1) (hKper : ∀ a, Function.Periodic (K a) 1)
    (hKdper : ∀ a, Function.Periodic (Kd a) 1)
    (hKbd : ∀ a s, |K a s| ≤ kap) (hKdbd : ∀ a s, |Kd a s| ≤ Md) (hPdbd : ∀ a, |Pd a| ≤ MP)
    (a s : ℝ) :
    |variation K Kd delta Pf Pd a s| ≤ varBound P0 P1 kap Md MP := by
  have hd := dissip_pos hP0 hkap0 hkap1
  exact SelectedRear.periodic_linear_sup_bound (P := 1) one_pos
    (fun x => hasDerivAt_variation hP0 hkap0 hkap1 hPl hKcont hKdcont hsol hstrip hper hKper
      hKdper a x)
    (periodic_variation hsol hper hKper hKdper a) hd
    (fun x => coef_ge hP0 hPl hstrip a x)
    (fun x => abs_source_le hKdbd hPdbd hPu hP0 hPl hkap1 hKbd a x) s

/-! ### The estimates in the path parameter -/

theorem avgCos_le_one (delta : ℝ → ℝ → ℝ) (a b s : ℝ) : avgCos delta a b s ≤ 1 := by
  have hcont : Continuous fun θ : ℝ =>
      Real.cos (delta b s + θ * (delta a s - delta b s)) :=
    Real.continuous_cos.comp (continuous_const.add (continuous_id.mul continuous_const))
  have hmono : (∫ θ in (0 : ℝ)..1, Real.cos (delta b s + θ * (delta a s - delta b s)))
      ≤ ∫ _ in (0 : ℝ)..1, (1 : ℝ) := by
    refine intervalIntegral.integral_mono_on (by norm_num) (hcont.intervalIntegrable _ _)
      intervalIntegrable_const (fun θ _ => Real.cos_le_one _)
  simpa [avgCos] using hmono

theorem abs_avgCos_le_one (hstrip : ∀ a s, delta a s ∈ Icc (0 : ℝ) (arcsin kap)) (a b s : ℝ) :
    |avgCos delta a b s| ≤ 1 := by
  have hup := avgCos_le_one delta a b s
  have hlow : (0 : ℝ) ≤ avgCos delta a b s :=
    le_trans (Real.sqrt_nonneg _) (avgCos_ge hstrip a b s)
  rw [abs_of_nonneg hlow]
  exact hup

/-- **The selected steering angle is Lipschitz in the path parameter.** -/
theorem abs_delta_sub_le (hP0 : 0 < P0) (hkap0 : 0 ≤ kap) (hkap1 : kap < 1)
    (hPl : ∀ a, P0 ≤ Pf a) (hPu : ∀ a, Pf a ≤ P1) (hKcont : Continuous (uncurry K))
    (hsol : ∀ a s, HasDerivAt (delta a) (Pf a * (K a s - Real.sin (delta a s))) s)
    (hstrip : ∀ a s, delta a s ∈ Icc (0 : ℝ) (arcsin kap))
    (hKbd : ∀ a s, |K a s| ≤ kap)
    (hKlip : ∀ a b s, |K a s - K b s| ≤ Klip * |a - b|)
    (hPlip : ∀ a b, |Pf a - Pf b| ≤ Plip * |a - b|) (a b s : ℝ) :
    |delta a s - delta b s| ≤ lipConst P0 P1 kap Klip Plip * |a - b| := by
  have hd := dissip_pos hP0 hkap0 hkap1
  have hKa : Continuous (K a) := hKcont.comp (continuous_const.prodMk continuous_id)
  have hKb : Continuous (K b) := hKcont.comp (continuous_const.prodMk continuous_id)
  have hPfpos : 0 < Pf a := lt_of_lt_of_le hP0 (hPl a)
  set f : ℝ → ℝ := fun s => Pf a * (K a s - K b s)
    + (Pf a - Pf b) * (K b s - Real.sin (delta b s)) with hf
  have hfcont : Continuous f :=
    (continuous_const.mul (hKa.sub hKb)).add (continuous_const.mul
      (hKb.sub (Real.continuous_sin.comp (continuous_delta_slice hsol b))))
  have hfbd : ∀ x, |f x| ≤ (P1 * Klip + 2 * Plip) * |a - b| := by
    intro x
    have h1 : |Pf a * (K a x - K b x)| ≤ P1 * Klip * |a - b| := by
      rw [abs_mul, abs_of_pos hPfpos]
      have : Pf a * |K a x - K b x| ≤ P1 * (Klip * |a - b|) :=
        mul_le_mul (hPu a) (hKlip a b x) (abs_nonneg _) (le_trans hPfpos.le (hPu a))
      calc Pf a * |K a x - K b x| ≤ P1 * (Klip * |a - b|) := this
        _ = P1 * Klip * |a - b| := by ring
    have hKx := hKbd b x
    have hs1 := Real.neg_one_le_sin (delta b x)
    have hs2 := Real.sin_le_one (delta b x)
    have hbd2 : |K b x - Real.sin (delta b x)| ≤ 2 := by
      rw [abs_le] at hKx ⊢
      constructor <;> linarith [hKx.1, hKx.2]
    have h2 : |(Pf a - Pf b) * (K b x - Real.sin (delta b x))| ≤ 2 * Plip * |a - b| := by
      rw [abs_mul]
      have := mul_le_mul (hPlip a b) hbd2 (abs_nonneg _)
        (le_trans (abs_nonneg _) (hPlip a b))
      calc |Pf a - Pf b| * |K b x - Real.sin (delta b x)| ≤ Plip * |a - b| * 2 := this
        _ = 2 * Plip * |a - b| := by ring
    calc |f x| ≤ |Pf a * (K a x - K b x)| + |(Pf a - Pf b) * (K b x - Real.sin (delta b x))| :=
          abs_add_le _ _
      _ ≤ P1 * Klip * |a - b| + 2 * Plip * |a - b| := add_le_add h1 h2
      _ = (P1 * Klip + 2 * Plip) * |a - b| := by ring
  have hode : ∀ x, HasDerivAt (fun y => delta a y - delta b y)
      (f x - (Pf a * avgCos delta a b x) * (delta a x - delta b x)) x := by
    intro x
    have h := (hsol a x).sub (hsol b x)
    refine h.congr_deriv ?_
    have hid := sin_sub_eq_avgCos_mul delta a b x
    rw [hf]
    nlinarith [hid]
  have hAcont : Continuous fun x => Pf a * avgCos delta a b x :=
    continuous_const.mul
      (continuous_avgCos_of_slices (fun a' => continuous_delta_slice hsol a') a b)
  have hAge : ∀ x, dissip P0 kap ≤ Pf a * avgCos delta a b x := by
    intro x
    have h1 : Real.sqrt (1 - kap ^ 2) ≤ avgCos delta a b x := avgCos_ge hstrip a b x
    have h2 : 0 ≤ Real.sqrt (1 - kap ^ 2) := Real.sqrt_nonneg _
    rw [dissip]
    exact mul_le_mul (hPl a) h1 h2 (le_trans hP0.le (hPl a))
  have hbd : ∀ x, |delta a x - delta b x| ≤ 2 :=
    fun x => SteeringVariablePeriod.abs_delta_sub_le_two hstrip a b x
  have := abs_le_of_bounded_dissipative (u := fun y => delta a y - delta b y)
    (a := fun x => Pf a * avgCos delta a b x) (f := f) (c := dissip P0 kap)
    (M := (P1 * Klip + 2 * Plip) * |a - b|) (B := 2) hd hAcont hfcont hAge hode hbd hfbd s
  calc |delta a s - delta b s| ≤ (P1 * Klip + 2 * Plip) * |a - b| / dissip P0 kap := this
    _ = lipConst P0 P1 kap Klip Plip * |a - b| := by rw [lipConst]; ring

/-- **The quadratic error of the linear prediction.** -/
theorem abs_error_le (hP0 : 0 < P0) (hkap0 : 0 ≤ kap) (hkap1 : kap < 1)
    (hPl : ∀ a, P0 ≤ Pf a) (hPu : ∀ a, Pf a ≤ P1)
    (hKcont : Continuous (uncurry K)) (hKdcont : Continuous (uncurry Kd))
    (hsol : ∀ a s, HasDerivAt (delta a) (Pf a * (K a s - Real.sin (delta a s))) s)
    (hstrip : ∀ a s, delta a s ∈ Icc (0 : ℝ) (arcsin kap))
    (hper : ∀ a, Function.Periodic (delta a) 1) (hKper : ∀ a, Function.Periodic (K a) 1)
    (hKdper : ∀ a, Function.Periodic (Kd a) 1)
    (hKbd : ∀ a s, |K a s| ≤ kap) (hKdbd : ∀ a s, |Kd a s| ≤ Md) (hPdbd : ∀ a, |Pd a| ≤ MP)
    (hKlip : ∀ a b s, |K a s - K b s| ≤ Klip * |a - b|)
    (hPlip : ∀ a b, |Pf a - Pf b| ≤ Plip * |a - b|)
    (hKtaylor : ∀ a b s, |K a s - K b s - (a - b) * Kd b s| ≤ CK * (a - b) ^ 2)
    (hPtaylor : ∀ a b, |Pf a - Pf b - (a - b) * Pd b| ≤ CP * (a - b) ^ 2)
    (a b s : ℝ) :
    |delta b s - delta a s - (b - a) * variation K Kd delta Pf Pd a s|
      ≤ errNum P0 P1 kap Klip CK Md Plip CP MP / dissip P0 kap * (b - a) ^ 2 := by
  have hd := dissip_pos hP0 hkap0 hkap1
  set h : ℝ := b - a with hh
  set w : ℝ → ℝ := variation K Kd delta Pf Pd a with hw
  set e : ℝ → ℝ := fun x => delta b x - delta a x - h * w x with he
  set Wb : ℝ := varBound P0 P1 kap Md MP with hWb
  set Ld : ℝ := lipConst P0 P1 kap Klip Plip with hLd
  have hwbd : ∀ x, |w x| ≤ Wb := fun x =>
    abs_variation_le hP0 hkap0 hkap1 hPl hPu hKcont hKdcont hsol hstrip hper hKper hKdper
      hKbd hKdbd hPdbd a x
  have hwcont : Continuous w :=
    continuous_variation hP0 hkap0 hkap1 hPl hKcont hKdcont hsol hstrip hper hKper hKdper a
  have hKa : Continuous (K a) := hKcont.comp (continuous_const.prodMk continuous_id)
  have hKb : Continuous (K b) := hKcont.comp (continuous_const.prodMk continuous_id)
  have hKda : Continuous (Kd a) := hKdcont.comp (continuous_const.prodMk continuous_id)
  have hcosa : Continuous fun x => Real.cos (delta a x) :=
    Real.continuous_cos.comp (continuous_delta_slice hsol a)
  have havg : Continuous (avgCos delta b a) :=
    continuous_avgCos_of_slices (fun a' => continuous_delta_slice hsol a') b a
  -- the residual of the error equation
  set R : ℝ → ℝ := fun x =>
      Pf b * (K b x - K a x - h * Kd a x)
      + h * Kd a x * (Pf b - Pf a)
      + (Pf b - Pf a - h * Pd a) * (K a x - Real.sin (delta a x))
      + h * w x * (Pf a * Real.cos (delta a x) - Pf b * avgCos delta b a x) with hR
  have hRcont : Continuous R := by
    rw [hR]
    exact ((((continuous_const.mul ((hKb.sub hKa).sub (continuous_const.mul hKda))).add
        ((continuous_const.mul hKda).mul continuous_const)).add
      (continuous_const.mul (hKa.sub (Real.continuous_sin.comp
        (continuous_delta_slice hsol a))))).add
      ((continuous_const.mul hwcont).mul
        ((continuous_const.mul hcosa).sub (continuous_const.mul havg))))
  -- the error equation
  have hediff : ∀ x, HasDerivAt e (R x - (Pf b * avgCos delta b a x) * e x) x := by
    intro x
    have h1 := (hsol b x).sub (hsol a x)
    have h2 := (hasDerivAt_variation (Pd := Pd) hP0 hkap0 hkap1 hPl hKcont hKdcont hsol hstrip
      hper hKper hKdper a x).const_mul h
    have h3 := h1.sub h2
    refine h3.congr_deriv ?_
    have hid := sin_sub_eq_avgCos_mul delta b a x
    simp only [he, hR, coef, source]
    linear_combination (-(Pf b)) * hid
  -- the error is bounded
  have hebd : ∀ x, |e x| ≤ 2 + |h| * Wb := by
    intro x
    have h1 := SteeringVariablePeriod.abs_delta_sub_le_two hstrip b a x
    have h2 : |h * w x| ≤ |h| * Wb := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hwbd x) (abs_nonneg h)
    calc |e x| = |(delta b x - delta a x) - h * w x| := by rw [he]
      _ ≤ |delta b x - delta a x| + |h * w x| := abs_sub _ _
      _ ≤ 2 + |h| * Wb := add_le_add h1 h2
  -- the residual is quadratic
  have hMd0 : 0 ≤ Md := le_trans (abs_nonneg _) (hKdbd a 0)
  have hPlip0 : 0 ≤ Plip := by
    have h1 := hPlip 1 0
    have h2 : (0 : ℝ) ≤ Plip * |(1 : ℝ) - 0| := le_trans (abs_nonneg _) h1
    simpa using h2
  have habs : |h| * |h| = h ^ 2 := by
    rw [← abs_mul, abs_of_nonneg (mul_self_nonneg h)]; ring
  have hRbd : ∀ x, |R x| ≤ errNum P0 P1 kap Klip CK Md Plip CP MP * h ^ 2 := by
    intro x
    have hPfbpos : 0 < Pf b := lt_of_lt_of_le hP0 (hPl b)
    have h1 : |Pf b * (K b x - K a x - h * Kd a x)| ≤ P1 * CK * h ^ 2 := by
      rw [abs_mul, abs_of_pos hPfbpos]
      have hT : |K b x - K a x - h * Kd a x| ≤ CK * h ^ 2 := by
        have := hKtaylor b a x
        rw [hh]
        simpa [mul_comm] using this
      have hCK0 : 0 ≤ CK * h ^ 2 := le_trans (abs_nonneg _) hT
      calc Pf b * |K b x - K a x - h * Kd a x| ≤ P1 * (CK * h ^ 2) :=
            mul_le_mul (hPu b) hT (abs_nonneg _) (le_trans hPfbpos.le (hPu b))
        _ = P1 * CK * h ^ 2 := by ring
    have h2 : |h * Kd a x * (Pf b - Pf a)| ≤ Md * Plip * h ^ 2 := by
      rw [abs_mul, abs_mul]
      have hP : |Pf b - Pf a| ≤ Plip * |h| := by
        have := hPlip b a
        rw [hh]
        exact this
      have hK : |Kd a x| ≤ Md := hKdbd a x
      calc |h| * |Kd a x| * |Pf b - Pf a| ≤ |h| * Md * (Plip * |h|) := by
            refine mul_le_mul (mul_le_mul_of_nonneg_left hK (abs_nonneg h)) hP (abs_nonneg _) ?_
            positivity
        _ = Md * Plip * (|h| * |h|) := by ring
        _ = Md * Plip * h ^ 2 := by rw [habs]
    have h3 : |(Pf b - Pf a - h * Pd a) * (K a x - Real.sin (delta a x))| ≤ 2 * CP * h ^ 2 := by
      rw [abs_mul]
      have hP : |Pf b - Pf a - h * Pd a| ≤ CP * h ^ 2 := by
        have := hPtaylor b a
        rw [hh]
        simpa [mul_comm] using this
      have hKx := hKbd a x
      have hs1 := Real.neg_one_le_sin (delta a x)
      have hs2 := Real.sin_le_one (delta a x)
      have hbd2 : |K a x - Real.sin (delta a x)| ≤ 2 := by
        rw [abs_le] at hKx ⊢
        constructor <;> linarith [hKx.1, hKx.2]
      calc |Pf b - Pf a - h * Pd a| * |K a x - Real.sin (delta a x)| ≤ CP * h ^ 2 * 2 :=
            mul_le_mul hP hbd2 (abs_nonneg _) (le_trans (abs_nonneg _) hP)
        _ = 2 * CP * h ^ 2 := by ring
    have h4 : |h * w x * (Pf a * Real.cos (delta a x) - Pf b * avgCos delta b a x)|
        ≤ Wb * (P1 * Ld + Plip) * h ^ 2 := by
      have hsplit : Pf a * Real.cos (delta a x) - Pf b * avgCos delta b a x
          = Pf a * (Real.cos (delta a x) - avgCos delta b a x)
            + (Pf a - Pf b) * avgCos delta b a x := by ring
      have hc1 : |Real.cos (delta a x) - avgCos delta b a x| ≤ Ld * |h| := by
        have hb := SteeringVariablePeriod.abs_avgCos_sub_cos_le delta b a x
        have hdd : |delta b x - delta a x| ≤ Ld * |h| := by
          have := abs_delta_sub_le hP0 hkap0 hkap1 hPl hPu hKcont hsol hstrip hKbd hKlip hPlip
            b a x
          rw [hh]
          exact this
        calc |Real.cos (delta a x) - avgCos delta b a x|
            = |avgCos delta b a x - Real.cos (delta a x)| := abs_sub_comm _ _
          _ ≤ |delta b x - delta a x| := hb
          _ ≤ Ld * |h| := hdd
      have hPfapos : 0 < Pf a := lt_of_lt_of_le hP0 (hPl a)
      have hc2 : |Pf a * (Real.cos (delta a x) - avgCos delta b a x)| ≤ P1 * (Ld * |h|) := by
        rw [abs_mul, abs_of_pos hPfapos]
        exact mul_le_mul (hPu a) hc1 (abs_nonneg _) (le_trans hPfapos.le (hPu a))
      have hc3 : |(Pf a - Pf b) * avgCos delta b a x| ≤ Plip * |h| := by
        rw [abs_mul]
        have hP : |Pf a - Pf b| ≤ Plip * |h| := by
          have := hPlip a b
          have habh : |a - b| = |h| := by rw [hh, abs_sub_comm]
          rwa [habh] at this
        have hA : |avgCos delta b a x| ≤ 1 := abs_avgCos_le_one hstrip b a x
        calc |Pf a - Pf b| * |avgCos delta b a x| ≤ (Plip * |h|) * 1 :=
              mul_le_mul hP hA (abs_nonneg _) (le_trans (abs_nonneg _) hP)
          _ = Plip * |h| := by ring
      have hcsum : |Pf a * Real.cos (delta a x) - Pf b * avgCos delta b a x|
          ≤ (P1 * Ld + Plip) * |h| := by
        rw [hsplit]
        calc |Pf a * (Real.cos (delta a x) - avgCos delta b a x)
              + (Pf a - Pf b) * avgCos delta b a x|
            ≤ |Pf a * (Real.cos (delta a x) - avgCos delta b a x)|
              + |(Pf a - Pf b) * avgCos delta b a x| := abs_add_le _ _
          _ ≤ P1 * (Ld * |h|) + Plip * |h| := add_le_add hc2 hc3
          _ = (P1 * Ld + Plip) * |h| := by ring
      have hWb0 : 0 ≤ Wb := le_trans (abs_nonneg _) (hwbd 0)
      rw [abs_mul, abs_mul]
      calc |h| * |w x| * |Pf a * Real.cos (delta a x) - Pf b * avgCos delta b a x|
          ≤ |h| * Wb * ((P1 * Ld + Plip) * |h|) := by
            refine mul_le_mul (mul_le_mul_of_nonneg_left (hwbd x) (abs_nonneg h)) hcsum
              (abs_nonneg _) ?_
            positivity
        _ = Wb * (P1 * Ld + Plip) * (|h| * |h|) := by ring
        _ = Wb * (P1 * Ld + Plip) * h ^ 2 := by rw [habs]
    have hsum : |R x| ≤ P1 * CK * h ^ 2 + Md * Plip * h ^ 2 + 2 * CP * h ^ 2
        + Wb * (P1 * Ld + Plip) * h ^ 2 := by
      rw [hR]
      calc |Pf b * (K b x - K a x - h * Kd a x) + h * Kd a x * (Pf b - Pf a)
            + (Pf b - Pf a - h * Pd a) * (K a x - Real.sin (delta a x))
            + h * w x * (Pf a * Real.cos (delta a x) - Pf b * avgCos delta b a x)|
          ≤ |Pf b * (K b x - K a x - h * Kd a x) + h * Kd a x * (Pf b - Pf a)
              + (Pf b - Pf a - h * Pd a) * (K a x - Real.sin (delta a x))|
            + |h * w x * (Pf a * Real.cos (delta a x) - Pf b * avgCos delta b a x)| :=
            abs_add_le _ _
        _ ≤ (|Pf b * (K b x - K a x - h * Kd a x) + h * Kd a x * (Pf b - Pf a)|
              + |(Pf b - Pf a - h * Pd a) * (K a x - Real.sin (delta a x))|)
            + Wb * (P1 * Ld + Plip) * h ^ 2 := add_le_add (abs_add_le _ _) h4
        _ ≤ ((|Pf b * (K b x - K a x - h * Kd a x)| + |h * Kd a x * (Pf b - Pf a)|)
              + 2 * CP * h ^ 2) + Wb * (P1 * Ld + Plip) * h ^ 2 :=
            add_le_add (add_le_add (abs_add_le _ _) h3) le_rfl
        _ ≤ ((P1 * CK * h ^ 2 + Md * Plip * h ^ 2) + 2 * CP * h ^ 2)
            + Wb * (P1 * Ld + Plip) * h ^ 2 :=
            add_le_add (add_le_add (add_le_add h1 h2) le_rfl) le_rfl
        _ = P1 * CK * h ^ 2 + Md * Plip * h ^ 2 + 2 * CP * h ^ 2
            + Wb * (P1 * Ld + Plip) * h ^ 2 := by ring
    calc |R x| ≤ P1 * CK * h ^ 2 + Md * Plip * h ^ 2 + 2 * CP * h ^ 2
          + Wb * (P1 * Ld + Plip) * h ^ 2 := hsum
      _ = errNum P0 P1 kap Klip CK Md Plip CP MP * h ^ 2 := by
          rw [errNum, hWb, hLd]; ring
  have hAge : ∀ x, dissip P0 kap ≤ Pf b * avgCos delta b a x := by
    intro x
    have h1 : Real.sqrt (1 - kap ^ 2) ≤ avgCos delta b a x := avgCos_ge hstrip b a x
    have h2 : 0 ≤ Real.sqrt (1 - kap ^ 2) := Real.sqrt_nonneg _
    rw [dissip]
    exact mul_le_mul (hPl b) h1 h2 (le_trans hP0.le (hPl b))
  have := abs_le_of_bounded_dissipative (u := e) (a := fun x => Pf b * avgCos delta b a x)
    (f := R) (c := dissip P0 kap)
    (M := errNum P0 P1 kap Klip CK Md Plip CP MP * h ^ 2) (B := 2 + |h| * Wb) hd
    (continuous_const.mul havg) hRcont hAge hediff hebd hRbd s
  calc |delta b s - delta a s - h * w s| = |e s| := by rw [he]
    _ ≤ errNum P0 P1 kap Klip CK Md Plip CP MP * h ^ 2 / dissip P0 kap := this
    _ = errNum P0 P1 kap Klip CK Md Plip CP MP / dissip P0 kap * h ^ 2 := by ring

/-- **The derivative of the steering angle in the path parameter.** -/
theorem hasDerivAt_param (hP0 : 0 < P0) (hkap0 : 0 ≤ kap) (hkap1 : kap < 1)
    (hPl : ∀ a, P0 ≤ Pf a) (hPu : ∀ a, Pf a ≤ P1)
    (hKcont : Continuous (uncurry K)) (hKdcont : Continuous (uncurry Kd))
    (hsol : ∀ a s, HasDerivAt (delta a) (Pf a * (K a s - Real.sin (delta a s))) s)
    (hstrip : ∀ a s, delta a s ∈ Icc (0 : ℝ) (arcsin kap))
    (hper : ∀ a, Function.Periodic (delta a) 1) (hKper : ∀ a, Function.Periodic (K a) 1)
    (hKdper : ∀ a, Function.Periodic (Kd a) 1)
    (hKbd : ∀ a s, |K a s| ≤ kap) (hKdbd : ∀ a s, |Kd a s| ≤ Md) (hPdbd : ∀ a, |Pd a| ≤ MP)
    (hKlip : ∀ a b s, |K a s - K b s| ≤ Klip * |a - b|)
    (hPlip : ∀ a b, |Pf a - Pf b| ≤ Plip * |a - b|)
    (hKtaylor : ∀ a b s, |K a s - K b s - (a - b) * Kd b s| ≤ CK * (a - b) ^ 2)
    (hPtaylor : ∀ a b, |Pf a - Pf b - (a - b) * Pd b| ≤ CP * (a - b) ^ 2)
    (hCK : 0 ≤ CK) (hCP : 0 ≤ CP) (a s : ℝ) :
    HasDerivAt (fun b => delta b s) (variation K Kd delta Pf Pd a s) a := by
  have hd := dissip_pos hP0 hkap0 hkap1
  have hMd0 : 0 ≤ Md := le_trans (abs_nonneg _) (hKdbd a 0)
  have hMP0 : 0 ≤ MP := le_trans (abs_nonneg _) (hPdbd a)
  have hKlip0 : 0 ≤ Klip := by
    have h1 := hKlip 1 0 0
    have h2 : (0 : ℝ) ≤ Klip * |(1 : ℝ) - 0| := le_trans (abs_nonneg _) h1
    simpa using h2
  have hPlip0 : 0 ≤ Plip := by
    have h1 := hPlip 1 0
    have h2 : (0 : ℝ) ≤ Plip * |(1 : ℝ) - 0| := le_trans (abs_nonneg _) h1
    simpa using h2
  have hP1 : 0 < P1 := lt_of_lt_of_le (lt_of_lt_of_le hP0 (hPl a)) (hPu a)
  have hnum : 0 ≤ errNum P0 P1 kap Klip CK Md Plip CP MP := by
    rw [errNum, varBound, lipConst, dissip]
    have : 0 < Real.sqrt (1 - kap ^ 2) := Real.sqrt_pos.mpr (by nlinarith)
    positivity
  refine SteeringVariablePeriod.hasDerivAt_of_quadratic
    (C := errNum P0 P1 kap Klip CK Md Plip CP MP / dissip P0 kap) (by positivity) ?_
  intro b
  exact abs_error_le hP0 hkap0 hkap1 hPl hPu hKcont hKdcont hsol hstrip hper hKper hKdper
    hKbd hKdbd hPdbd hKlip hPlip hKtaylor hPtaylor a b s

/-! ### Joint regularity -/

/-- **The selected steering angle is jointly continuous.** -/
theorem continuous_uncurry_delta (hP0 : 0 < P0) (hkap0 : 0 ≤ kap) (hkap1 : kap < 1)
    (hPl : ∀ a, P0 ≤ Pf a) (hPu : ∀ a, Pf a ≤ P1) (hKcont : Continuous (uncurry K))
    (hsol : ∀ a s, HasDerivAt (delta a) (Pf a * (K a s - Real.sin (delta a s))) s)
    (hstrip : ∀ a s, delta a s ∈ Icc (0 : ℝ) (arcsin kap))
    (hKbd : ∀ a s, |K a s| ≤ kap)
    (hKlip : ∀ a b s, |K a s - K b s| ≤ Klip * |a - b|)
    (hPlip : ∀ a b, |Pf a - Pf b| ≤ Plip * |a - b|) :
    Continuous (uncurry delta) := by
  have hd := dissip_pos hP0 hkap0 hkap1
  set L : ℝ := lipConst P0 P1 kap Klip Plip with hL
  have hKlip0 : 0 ≤ Klip := by
    have h1 := hKlip 1 0 0
    have h2 : (0 : ℝ) ≤ Klip * |(1 : ℝ) - 0| := le_trans (abs_nonneg _) h1
    simpa using h2
  have hPlip0 : 0 ≤ Plip := by
    have h1 := hPlip 1 0
    have h2 : (0 : ℝ) ≤ Plip * |(1 : ℝ) - 0| := le_trans (abs_nonneg _) h1
    simpa using h2
  have hP1 : 0 < P1 := lt_of_lt_of_le (lt_of_lt_of_le hP0 (hPl 0)) (hPu 0)
  have hLnn : 0 ≤ L := by
    rw [hL, lipConst]
    positivity
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
  have h1 : |delta a x - delta a0 x| ≤ L * |a - a0| :=
    abs_delta_sub_le hP0 hkap0 hkap1 hPl hPu hKcont hsol hstrip hKbd hKlip hPlip a a0 x
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

/-- One step of the bootstrap. -/
theorem contDiff_succ_of_contDiff (hP0 : 0 < P0) (hkap0 : 0 ≤ kap) (hkap1 : kap < 1)
    (hPl : ∀ a, P0 ≤ Pf a) (hPu : ∀ a, Pf a ≤ P1)
    (hKcont : Continuous (uncurry K)) (hKdcont : Continuous (uncurry Kd))
    (hsol : ∀ a s, HasDerivAt (delta a) (Pf a * (K a s - Real.sin (delta a s))) s)
    (hstrip : ∀ a s, delta a s ∈ Icc (0 : ℝ) (arcsin kap))
    (hper : ∀ a, Function.Periodic (delta a) 1) (hKper : ∀ a, Function.Periodic (K a) 1)
    (hKdper : ∀ a, Function.Periodic (Kd a) 1)
    (hKbd : ∀ a s, |K a s| ≤ kap) (hKdbd : ∀ a s, |Kd a s| ≤ Md) (hPdbd : ∀ a, |Pd a| ≤ MP)
    (hKlip : ∀ a b s, |K a s - K b s| ≤ Klip * |a - b|)
    (hPlip : ∀ a b, |Pf a - Pf b| ≤ Plip * |a - b|)
    (hKtaylor : ∀ a b s, |K a s - K b s - (a - b) * Kd b s| ≤ CK * (a - b) ^ 2)
    (hPtaylor : ∀ a b, |Pf a - Pf b - (a - b) * Pd b| ≤ CP * (a - b) ^ 2)
    (hCK : 0 ≤ CK) (hCP : 0 ≤ CP) (hdelta : ContDiff ℝ (n : ℕ) (uncurry delta))
    (hPfC : ContDiff ℝ (n : ℕ) Pf) (hPdC : ContDiff ℝ (n : ℕ) Pd)
    (hKC : ContDiff ℝ (n : ℕ) (uncurry K)) (hKdC : ContDiff ℝ (n : ℕ) (uncurry Kd)) :
    ContDiff ℝ ((n + 1 : ℕ)) (uncurry delta) := by
  have hdt : ∀ a s, HasDerivAt (fun b => delta b s) (variation K Kd delta Pf Pd a s) a :=
    fun a s => hasDerivAt_param hP0 hkap0 hkap1 hPl hPu hKcont hKdcont hsol hstrip hper hKper
      hKdper hKbd hKdbd hPdbd hKlip hPlip hKtaylor hPtaylor hCK hCP a s
  have hcoefC : ContDiff ℝ (n : ℕ) (uncurry fun a s => coef delta Pf a s) := by
    have : ContDiff ℝ (n : ℕ) (uncurry fun a s => Pf a * Real.cos (delta a s)) :=
      (hPfC.comp contDiff_fst).mul (Real.contDiff_cos.comp hdelta)
    exact this
  have hsourceC : ContDiff ℝ (n : ℕ) (uncurry fun a s => source K Kd delta Pf Pd a s) := by
    have h1 : ContDiff ℝ (n : ℕ)
        (uncurry fun a s => Pd a * (K a s - Real.sin (delta a s))) :=
      (hPdC.comp contDiff_fst).mul (hKC.sub (Real.contDiff_sin.comp hdelta))
    have h2 : ContDiff ℝ (n : ℕ) (uncurry fun a s => Pf a * Kd a s) :=
      (hPfC.comp contDiff_fst).mul hKdC
    exact h1.add h2
  have hpos : ∀ a, 0 < prim (coef delta Pf a) 1 := fun a =>
    prim_coef_pos hP0 hkap0 hkap1 hPl hsol hstrip a
  have hw : ContDiff ℝ (n : ℕ) (uncurry (variation K Kd delta Pf Pd)) :=
    PeriodicGreenSmooth.contDiff_periodicGreen_param_var
      (A := fun a s => coef delta Pf a s) (F := fun a s => source K Kd delta Pf Pd a s)
      (L := fun _ => (1 : ℝ)) hcoefC hsourceC contDiff_const hpos
  have hs : ContDiff ℝ (n : ℕ)
      (uncurry fun a s => Pf a * (K a s - Real.sin (delta a s))) :=
    (hPfC.comp contDiff_fst).mul (hKC.sub (Real.contDiff_sin.comp hdelta))
  exact RearOwnTangential.contDiff_succ_of_partials hdt hsol hw hs

/-- **The selected steering angle is jointly `C^{n+1}`**, with no restriction on
the motion of the arclength period of the slices. -/
theorem contDiff_succ_uncurry_delta (hP0 : 0 < P0) (hkap0 : 0 ≤ kap) (hkap1 : kap < 1)
    (hPl : ∀ a, P0 ≤ Pf a) (hPu : ∀ a, Pf a ≤ P1)
    (hsol : ∀ a s, HasDerivAt (delta a) (Pf a * (K a s - Real.sin (delta a s))) s)
    (hstrip : ∀ a s, delta a s ∈ Icc (0 : ℝ) (arcsin kap))
    (hper : ∀ a, Function.Periodic (delta a) 1) (hKper : ∀ a, Function.Periodic (K a) 1)
    (hKdper : ∀ a, Function.Periodic (Kd a) 1)
    (hKbd : ∀ a s, |K a s| ≤ kap) (hKdbd : ∀ a s, |Kd a s| ≤ Md) (hPdbd : ∀ a, |Pd a| ≤ MP)
    (hKlip : ∀ a b s, |K a s - K b s| ≤ Klip * |a - b|)
    (hPlip : ∀ a b, |Pf a - Pf b| ≤ Plip * |a - b|)
    (hKtaylor : ∀ a b s, |K a s - K b s - (a - b) * Kd b s| ≤ CK * (a - b) ^ 2)
    (hPtaylor : ∀ a b, |Pf a - Pf b - (a - b) * Pd b| ≤ CP * (a - b) ^ 2)
    (hCK : 0 ≤ CK) (hCP : 0 ≤ CP)
    (hPfC : ContDiff ℝ (n : ℕ) Pf) (hPdC : ContDiff ℝ (n : ℕ) Pd)
    (hKC : ContDiff ℝ (n : ℕ) (uncurry K)) (hKdC : ContDiff ℝ (n : ℕ) (uncurry Kd)) :
    ContDiff ℝ ((n + 1 : ℕ)) (uncurry delta) := by
  have hcont : Continuous (uncurry delta) :=
    continuous_uncurry_delta hP0 hkap0 hkap1 hPl hPu hKC.continuous hsol hstrip hKbd hKlip hPlip
  induction n with
  | zero =>
      have hdelta0 : ContDiff ℝ ((0 : ℕ)) (uncurry delta) := by
        simpa using (contDiff_zero (𝕜 := ℝ) (f := uncurry delta)).mpr hcont
      exact contDiff_succ_of_contDiff hP0 hkap0 hkap1 hPl hPu hKC.continuous hKdC.continuous
        hsol hstrip hper hKper hKdper hKbd hKdbd hPdbd hKlip hPlip hKtaylor hPtaylor hCK hCP
        hdelta0 hPfC hPdC hKC hKdC
  | succ k ih =>
      have hle : ((k : ℕ) : WithTop ℕ∞) ≤ ((k + 1 : ℕ) : WithTop ℕ∞) := by
        exact_mod_cast (by omega : (k : ℕ) ≤ k + 1)
      have hdelta : ContDiff ℝ ((k + 1 : ℕ)) (uncurry delta) :=
        ih (hPfC.of_le hle) (hPdC.of_le hle) (hKC.of_le hle) (hKdC.of_le hle)
      exact contDiff_succ_of_contDiff hP0 hkap0 hkap1 hPl hPu hKC.continuous hKdC.continuous
        hsol hstrip hper hKper hKdper hKbd hKdbd hPdbd hKlip hPlip hKtaylor hPtaylor hCK hCP
        hdelta hPfC hPdC hKC hKdC

/-- The joint `C⁴` case, the regularity the assembly of the path metric
consumes. -/
theorem contDiff_four_uncurry_delta (hP0 : 0 < P0) (hkap0 : 0 ≤ kap) (hkap1 : kap < 1)
    (hPl : ∀ a, P0 ≤ Pf a) (hPu : ∀ a, Pf a ≤ P1)
    (hsol : ∀ a s, HasDerivAt (delta a) (Pf a * (K a s - Real.sin (delta a s))) s)
    (hstrip : ∀ a s, delta a s ∈ Icc (0 : ℝ) (arcsin kap))
    (hper : ∀ a, Function.Periodic (delta a) 1) (hKper : ∀ a, Function.Periodic (K a) 1)
    (hKdper : ∀ a, Function.Periodic (Kd a) 1)
    (hKbd : ∀ a s, |K a s| ≤ kap) (hKdbd : ∀ a s, |Kd a s| ≤ Md) (hPdbd : ∀ a, |Pd a| ≤ MP)
    (hKlip : ∀ a b s, |K a s - K b s| ≤ Klip * |a - b|)
    (hPlip : ∀ a b, |Pf a - Pf b| ≤ Plip * |a - b|)
    (hKtaylor : ∀ a b s, |K a s - K b s - (a - b) * Kd b s| ≤ CK * (a - b) ^ 2)
    (hPtaylor : ∀ a b, |Pf a - Pf b - (a - b) * Pd b| ≤ CP * (a - b) ^ 2)
    (hCK : 0 ≤ CK) (hCP : 0 ≤ CP)
    (hPfC : ContDiff ℝ (3 : ℕ) Pf) (hPdC : ContDiff ℝ (3 : ℕ) Pd)
    (hKC : ContDiff ℝ (3 : ℕ) (uncurry K)) (hKdC : ContDiff ℝ (3 : ℕ) (uncurry Kd)) :
    ContDiff ℝ (4 : ℕ) (uncurry delta) := by
  have h := contDiff_succ_uncurry_delta (n := 3) hP0 hkap0 hkap1 hPl hPu hsol hstrip hper
    hKper hKdper hKbd hKdbd hPdbd hKlip hPlip hKtaylor hPtaylor hCK hCP hPfC hPdC hKC hKdC
  simpa using h

/-! ### Back to the arclength of each slice -/

/-- **The steering angle in the arclength of each slice.**  If the normalized
steering angle is jointly `Cⁿ` and the period is jointly `Cⁿ` and positive, then
`δ♭(a, s) = δ(a, s / P(a))`, the steering angle read in the arclength of the
slice at time `a`, is jointly `Cⁿ` too. -/
theorem contDiff_arclength_of_normalized (hdelta : ContDiff ℝ (n : ℕ) (uncurry delta))
    (hPfC : ContDiff ℝ (n : ℕ) Pf) (hPpos : ∀ a, 0 < Pf a) :
    ContDiff ℝ (n : ℕ) (uncurry fun a s => delta a (s / Pf a)) := by
  have hmap : ContDiff ℝ (n : ℕ) (fun p : ℝ × ℝ => (p.1, p.2 / Pf p.1)) :=
    contDiff_fst.prodMk (contDiff_snd.div (hPfC.comp contDiff_fst) (fun p => (hPpos p.1).ne'))
  exact hdelta.comp hmap

end SteeringNormalizedPeriod
