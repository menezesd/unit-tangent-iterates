import Mathlib
import UnitTangentIterates.BoundedLinearBound
import UnitTangentIterates.PeriodicGreenSmooth
import UnitTangentIterates.SteeringArclengthJointC1
import UnitTangentIterates.RearOwnTangential

/-!
# The selected steering angle of a path of fronts of moving perimeter

`SteeringArclengthJointC1.lean` and `SteeringArclengthSmooth.lean` prove the
joint regularity of the selected steering angle in the arclength of the front,
but only for slices sharing **one** arclength period: the estimates in the path
parameter compare two slices through a maximum principle over one period.
Along a genuine path of fronts the perimeter moves, and two slices have
different periods.

This file removes that restriction.  Two ingredients replace periodicity:

* the maximum principle for **bounded** solutions of a dissipative linear
  equation (`BoundedLinearBound.lean`) — the difference of two steering angles
  and the error of its linear prediction are bounded, being confined to the
  selected strip, whatever their periods;
* the **averaged cosine**
  `avgCos(a,b,s) = ∫₀¹ cos(δ(b,s) + θ(δ(a,s) - δ(b,s))) dθ`, which turns the
  difference of the sines into a product `avgCos · (δ(a,·) - δ(b,·))` with a
  *continuous* coefficient, bounded below by `√(1-κ̂²)` on the selected strip.

With them the whole chain goes through with the period `P(a)` of each slice:
the derivative of the steering angle in the path parameter is the periodic
solution

```
  w(a, ·) = 𝒢_{cos δ(a,·)} (K̇(a,·))
```

of the linearized equation on the circle of length `P(a)`, and since the Green
operator is jointly `Cⁿ` in its data, period included
(`PeriodicGreenSmooth.contDiff_periodicGreen_param_var`), the bootstrap gives
joint `C^{n+1}` regularity of the steering angle from jointly `Cⁿ` front data.

Main results:

* `abs_delta_sub_le` — the steering angle is Lipschitz in the path parameter,
  uniformly in the arclength;
* `abs_error_le` — the quadratic error of the linear prediction;
* `hasDerivAt_param` — `∂_a δ(a,s) = w(a,s)`;
* `continuous_uncurry_delta` — joint continuity;
* `contDiff_succ_uncurry_delta` — **joint `C^{n+1}` regularity**, with the
  arclength period of each slice moving with the path parameter;
* `contDiff_four_uncurry_delta` — the joint `C⁴` case.
-/

noncomputable section

open Function Set Real

namespace SteeringVariablePeriod

open PeriodicGreen BoundedLinearBound

variable {K Kd delta : ℝ → ℝ → ℝ} {Pf : ℝ → ℝ} {kap Klip CK Md : ℝ} {n : ℕ}

/-! ### The averaged cosine -/

/-- The cosine averaged along the segment joining two steering angles. -/
def avgCos (delta : ℝ → ℝ → ℝ) (a b s : ℝ) : ℝ :=
  ∫ θ in (0 : ℝ)..1, Real.cos (delta b s + θ * (delta a s - delta b s))

/-- **The difference of the sines factors through the averaged cosine.** -/
theorem sin_sub_eq_avgCos_mul (delta : ℝ → ℝ → ℝ) (a b s : ℝ) :
    Real.sin (delta a s) - Real.sin (delta b s)
      = avgCos delta a b s * (delta a s - delta b s) := by
  set e : ℝ := delta b s with he
  set D : ℝ := delta a s - delta b s with hD
  have hderiv : ∀ θ : ℝ,
      HasDerivAt (fun t : ℝ => Real.sin (e + t * D)) (D * Real.cos (e + θ * D)) θ := by
    intro θ
    have h1 : HasDerivAt (fun t : ℝ => e + t * D) D θ := by
      simpa using ((hasDerivAt_id θ).mul_const D).const_add e
    simpa [mul_comm] using (Real.hasDerivAt_sin (e + θ * D)).comp θ h1
  have hcont : Continuous fun θ : ℝ => D * Real.cos (e + θ * D) :=
    continuous_const.mul (Real.continuous_cos.comp
      (continuous_const.add (continuous_id.mul continuous_const)))
  have hFTC : (∫ θ in (0 : ℝ)..1, D * Real.cos (e + θ * D))
      = Real.sin (e + 1 * D) - Real.sin (e + 0 * D) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun θ _ => hderiv θ)
      (hcont.intervalIntegrable _ _)
  rw [intervalIntegral.integral_const_mul] at hFTC
  have hea : e + 1 * D = delta a s := by rw [he, hD]; ring
  have heb : e + 0 * D = delta b s := by rw [he]; ring
  rw [hea, heb] at hFTC
  rw [avgCos, ← hFTC]
  ring

/-- On the selected strip the averaged cosine is at least `√(1-κ̂²)`. -/
theorem avgCos_ge (hstrip : ∀ a s, delta a s ∈ Icc (0 : ℝ) (arcsin kap)) (a b s : ℝ) :
    Real.sqrt (1 - kap ^ 2) ≤ avgCos delta a b s := by
  have hcont : Continuous fun θ : ℝ =>
      Real.cos (delta b s + θ * (delta a s - delta b s)) :=
    Real.continuous_cos.comp (continuous_const.add (continuous_id.mul continuous_const))
  have hmono : (∫ _ in (0 : ℝ)..1, Real.sqrt (1 - kap ^ 2))
      ≤ ∫ θ in (0 : ℝ)..1, Real.cos (delta b s + θ * (delta a s - delta b s)) := by
    refine intervalIntegral.integral_mono_on (by norm_num) intervalIntegrable_const
      (hcont.intervalIntegrable _ _) (fun θ hθ => ?_)
    have h0 : 0 ≤ delta b s + θ * (delta a s - delta b s) := by
      have ha := hstrip a s
      have hb := hstrip b s
      nlinarith [hθ.1, hθ.2, ha.1, hb.1]
    have h1 : delta b s + θ * (delta a s - delta b s) ≤ arcsin kap := by
      have ha := hstrip a s
      have hb := hstrip b s
      nlinarith [hθ.1, hθ.2, ha.2, hb.2]
    exact Shadowing.cos_ge_of_mem_strip h0 h1
  simpa using hmono

/-- The averaged cosine differs from the cosine at the base point by at most
the increment of the steering angle. -/
theorem abs_avgCos_sub_cos_le (delta : ℝ → ℝ → ℝ) (a b s : ℝ) :
    |avgCos delta a b s - Real.cos (delta b s)| ≤ |delta a s - delta b s| := by
  set e : ℝ := delta b s with he
  set D : ℝ := delta a s - delta b s with hD
  have hcont : Continuous fun θ : ℝ => Real.cos (e + θ * D) :=
    Real.continuous_cos.comp (continuous_const.add (continuous_id.mul continuous_const))
  have hsplit : avgCos delta a b s - Real.cos e
      = ∫ θ in (0 : ℝ)..1, (Real.cos (e + θ * D) - Real.cos e) := by
    rw [intervalIntegral.integral_sub (hcont.intervalIntegrable _ _)
      (intervalIntegrable_const)]
    simp [avgCos, he, hD]
  rw [hsplit]
  have hbd : ∀ θ ∈ Set.Icc (0 : ℝ) 1, |Real.cos (e + θ * D) - Real.cos e| ≤ |D| := by
    intro θ hθ
    have hlip : |Real.cos (e + θ * D) - Real.cos e| ≤ |θ * D| := by
      have := Real.lipschitzWith_cos.dist_le_mul (e + θ * D) e
      simpa [Real.dist_eq] using this
    have : |θ * D| ≤ |D| := by
      rw [abs_mul, abs_of_nonneg hθ.1]
      nlinarith [abs_nonneg D, hθ.1, hθ.2]
    linarith
  calc |∫ θ in (0 : ℝ)..1, (Real.cos (e + θ * D) - Real.cos e)|
      ≤ ∫ θ in (0 : ℝ)..1, |Real.cos (e + θ * D) - Real.cos e| :=
        intervalIntegral.abs_integral_le_integral_abs (by norm_num)
    _ ≤ ∫ _ in (0 : ℝ)..1, |D| := by
        refine intervalIntegral.integral_mono_on (by norm_num)
          ((hcont.sub continuous_const).abs.intervalIntegrable _ _)
          intervalIntegrable_const hbd
    _ = |D| := by simp

theorem continuous_delta_slice
    (hsol : ∀ a s, HasDerivAt (delta a) (K a s - Real.sin (delta a s)) s) (a : ℝ) :
    Continuous (delta a) := by
  have hdiff : Differentiable ℝ (delta a) := fun s => (hsol a s).differentiableAt
  exact hdiff.continuous

theorem continuous_avgCos
    (hsol : ∀ a s, HasDerivAt (delta a) (K a s - Real.sin (delta a s)) s) (a b : ℝ) :
    Continuous (avgCos delta a b) := by
  have hda : Continuous (delta a) := continuous_delta_slice hsol a
  have hdb : Continuous (delta b) := continuous_delta_slice hsol b
  have hF : Continuous (uncurry fun (s : ℝ) (θ : ℝ) =>
      Real.cos (delta b s + θ * (delta a s - delta b s))) := by
    refine Real.continuous_cos.comp ?_
    exact (hdb.comp continuous_fst).add
      (continuous_snd.mul ((hda.comp continuous_fst).sub (hdb.comp continuous_fst)))
  simpa [avgCos] using
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
      (a₀ := (0 : ℝ)) hF continuous_const

/-! ### The variation -/

/-- The derivative of the selected steering angle in the path parameter: the
periodic solution of `w_s + cos δ · w = K̇` on the circle of the current
arclength period. -/
def variation (Kd delta : ℝ → ℝ → ℝ) (Pf : ℝ → ℝ) (a : ℝ) : ℝ → ℝ :=
  periodicGreen (fun s => Real.cos (delta a s)) (Pf a) (Kd a)

theorem sqrt_pos_of_lt (hkap0 : 0 ≤ kap) (hkap1 : kap < 1) :
    0 < Real.sqrt (1 - kap ^ 2) := Real.sqrt_pos.mpr (by nlinarith)

theorem prim_cos_pos (hkap0 : 0 ≤ kap) (hkap1 : kap < 1) (hPf : ∀ a, 0 < Pf a)
    (hsol : ∀ a s, HasDerivAt (delta a) (K a s - Real.sin (delta a s)) s)
    (hstrip : ∀ a s, delta a s ∈ Icc (0 : ℝ) (arcsin kap)) (a : ℝ) :
    0 < prim (fun s => Real.cos (delta a s)) (Pf a) := by
  have hmpos := sqrt_pos_of_lt hkap0 hkap1
  have hcont : Continuous fun s => Real.cos (delta a s) :=
    Real.continuous_cos.comp (continuous_delta_slice hsol a)
  have hmono : (∫ _ in (0 : ℝ)..Pf a, Real.sqrt (1 - kap ^ 2))
      ≤ ∫ s in (0 : ℝ)..Pf a, Real.cos (delta a s) := by
    refine intervalIntegral.integral_mono_on (hPf a).le intervalIntegrable_const
      (hcont.intervalIntegrable _ _) (fun s _ => ?_)
    exact Shadowing.cos_ge_of_mem_strip (hstrip a s).1 (hstrip a s).2
  have hconst : (∫ _ in (0 : ℝ)..Pf a, Real.sqrt (1 - kap ^ 2))
      = Real.sqrt (1 - kap ^ 2) * Pf a := by simp [mul_comm]
  have hpos : 0 < Real.sqrt (1 - kap ^ 2) * Pf a := by
    have := hPf a; positivity
  rw [prim]
  have hge : Real.sqrt (1 - kap ^ 2) * Pf a ≤ ∫ s in (0 : ℝ)..Pf a, Real.cos (delta a s) := by
    rw [← hconst]; exact hmono
  linarith

theorem periodic_cos_delta (hper : ∀ a, Function.Periodic (delta a) (Pf a)) (a : ℝ) :
    Function.Periodic (fun s => Real.cos (delta a s)) (Pf a) := by
  intro s
  simp only [hper a s]

/-- The variation solves the linearized steering equation. -/
theorem hasDerivAt_variation (hkap0 : 0 ≤ kap) (hkap1 : kap < 1) (hPf : ∀ a, 0 < Pf a)
    (hKdcont : Continuous (uncurry Kd))
    (hsol : ∀ a s, HasDerivAt (delta a) (K a s - Real.sin (delta a s)) s)
    (hstrip : ∀ a s, delta a s ∈ Icc (0 : ℝ) (arcsin kap))
    (hper : ∀ a, Function.Periodic (delta a) (Pf a))
    (hKdper : ∀ a, Function.Periodic (Kd a) (Pf a)) (a s : ℝ) :
    HasDerivAt (variation Kd delta Pf a)
      (Kd a s - Real.cos (delta a s) * variation Kd delta Pf a s) s := by
  have hcos : Continuous fun s => Real.cos (delta a s) :=
    Real.continuous_cos.comp (continuous_delta_slice hsol a)
  have hKdslice : Continuous (Kd a) := hKdcont.comp (continuous_const.prodMk continuous_id)
  exact periodicGreen_hasDerivAt (a := fun s => Real.cos (delta a s)) (l := Pf a) (f := Kd a)
    hcos (periodic_cos_delta hper a)
    (prim_cos_pos (K := K) hkap0 hkap1 hPf hsol hstrip a) hKdslice (hKdper a) s

theorem periodic_variation
    (hsol : ∀ a s, HasDerivAt (delta a) (K a s - Real.sin (delta a s)) s)
    (hper : ∀ a, Function.Periodic (delta a) (Pf a))
    (hKdper : ∀ a, Function.Periodic (Kd a) (Pf a)) (a : ℝ) :
    Function.Periodic (variation Kd delta Pf a) (Pf a) :=
  periodicGreen_periodic (Real.continuous_cos.comp (continuous_delta_slice hsol a))
    (periodic_cos_delta hper a) (hKdper a)

theorem continuous_variation (hkap0 : 0 ≤ kap) (hkap1 : kap < 1) (hPf : ∀ a, 0 < Pf a)
    (hKdcont : Continuous (uncurry Kd))
    (hsol : ∀ a s, HasDerivAt (delta a) (K a s - Real.sin (delta a s)) s)
    (hstrip : ∀ a s, delta a s ∈ Icc (0 : ℝ) (arcsin kap))
    (hper : ∀ a, Function.Periodic (delta a) (Pf a))
    (hKdper : ∀ a, Function.Periodic (Kd a) (Pf a)) (a : ℝ) :
    Continuous (variation Kd delta Pf a) := by
  have hdiff : Differentiable ℝ (variation Kd delta Pf a) := fun s =>
    (hasDerivAt_variation (K := K) hkap0 hkap1 hPf hKdcont hsol hstrip hper hKdper a
      s).differentiableAt
  exact hdiff.continuous

/-- **The variation is bounded** by the sup bound of the source over the
dissipation rate. -/
theorem abs_variation_le (hkap0 : 0 ≤ kap) (hkap1 : kap < 1) (hPf : ∀ a, 0 < Pf a)
    (hKdcont : Continuous (uncurry Kd))
    (hsol : ∀ a s, HasDerivAt (delta a) (K a s - Real.sin (delta a s)) s)
    (hstrip : ∀ a s, delta a s ∈ Icc (0 : ℝ) (arcsin kap))
    (hper : ∀ a, Function.Periodic (delta a) (Pf a))
    (hKdper : ∀ a, Function.Periodic (Kd a) (Pf a))
    (hKdbd : ∀ a s, |Kd a s| ≤ Md) (a s : ℝ) :
    |variation Kd delta Pf a s| ≤ Md / Real.sqrt (1 - kap ^ 2) := by
  have hmpos := sqrt_pos_of_lt hkap0 hkap1
  exact SelectedRear.periodic_linear_sup_bound (P := Pf a) (hPf a)
    (fun x => hasDerivAt_variation (K := K) hkap0 hkap1 hPf hKdcont hsol hstrip hper hKdper a x)
    (periodic_variation (K := K) hsol hper hKdper a) hmpos
    (fun x => Shadowing.cos_ge_of_mem_strip (hstrip a x).1 (hstrip a x).2)
    (fun x => hKdbd a x) s

/-! ### The estimates in the path parameter -/

theorem abs_delta_sub_le_two
    (hstrip : ∀ a s, delta a s ∈ Icc (0 : ℝ) (arcsin kap)) (a b s : ℝ) :
    |delta a s - delta b s| ≤ 2 := by
  have ha := hstrip a s
  have hb := hstrip b s
  have harc : arcsin kap ≤ π / 2 := Real.arcsin_le_pi_div_two kap
  have hpi : π ≤ 4 := Real.pi_le_four
  rw [abs_le]
  constructor <;> [linarith [ha.1, hb.2]; linarith [ha.2, hb.1]]

/-- **The selected steering angle is Lipschitz in the path parameter**,
uniformly in the arclength, whatever the periods of the slices. -/
theorem abs_delta_sub_le (hkap0 : 0 ≤ kap) (hkap1 : kap < 1)
    (hKcont : Continuous (uncurry K))
    (hsol : ∀ a s, HasDerivAt (delta a) (K a s - Real.sin (delta a s)) s)
    (hstrip : ∀ a s, delta a s ∈ Icc (0 : ℝ) (arcsin kap))
    (hKlip : ∀ a b s, |K a s - K b s| ≤ Klip * |a - b|) (a b s : ℝ) :
    |delta a s - delta b s| ≤ Klip * |a - b| / Real.sqrt (1 - kap ^ 2) := by
  have hmpos := sqrt_pos_of_lt hkap0 hkap1
  have hKa : Continuous (K a) := hKcont.comp (continuous_const.prodMk continuous_id)
  have hKb : Continuous (K b) := hKcont.comp (continuous_const.prodMk continuous_id)
  refine abs_le_of_bounded_dissipative (u := fun s => delta a s - delta b s)
    (a := avgCos delta a b) (f := fun s => K a s - K b s) (c := Real.sqrt (1 - kap ^ 2))
    (M := Klip * |a - b|) (B := 2) hmpos (continuous_avgCos hsol a b) (hKa.sub hKb)
    (fun s => avgCos_ge hstrip a b s) ?_
    (fun s => abs_delta_sub_le_two hstrip a b s) (fun s => hKlip a b s) s
  intro x
  have h := (hsol a x).sub (hsol b x)
  refine h.congr_deriv ?_
  have hid := sin_sub_eq_avgCos_mul delta a b x
  linarith [hid]

/-- **The quadratic error of the linear prediction.** -/
theorem abs_error_le (hkap0 : 0 ≤ kap) (hkap1 : kap < 1) (hPf : ∀ a, 0 < Pf a)
    (hKcont : Continuous (uncurry K)) (hKdcont : Continuous (uncurry Kd))
    (hsol : ∀ a s, HasDerivAt (delta a) (K a s - Real.sin (delta a s)) s)
    (hstrip : ∀ a s, delta a s ∈ Icc (0 : ℝ) (arcsin kap))
    (hper : ∀ a, Function.Periodic (delta a) (Pf a))
    (hKdper : ∀ a, Function.Periodic (Kd a) (Pf a))
    (hKdbd : ∀ a s, |Kd a s| ≤ Md)
    (hKlip : ∀ a b s, |K a s - K b s| ≤ Klip * |a - b|)
    (hKtaylor : ∀ a b s, |K a s - K b s - (a - b) * Kd b s| ≤ CK * (a - b) ^ 2)
    (a b s : ℝ) :
    |delta b s - delta a s - (b - a) * variation Kd delta Pf a s|
      ≤ (CK + Md * Klip / Real.sqrt (1 - kap ^ 2) ^ 2) / Real.sqrt (1 - kap ^ 2) * (b - a) ^ 2 := by
  set m : ℝ := Real.sqrt (1 - kap ^ 2) with hm
  have hmpos : 0 < m := sqrt_pos_of_lt hkap0 hkap1
  set h : ℝ := b - a with hh
  set w : ℝ → ℝ := variation Kd delta Pf a with hw
  set e : ℝ → ℝ := fun s => delta b s - delta a s - h * w s with he
  set R : ℝ → ℝ := fun s => (K b s - K a s - h * Kd a s)
    + h * w s * (Real.cos (delta a s) - avgCos delta b a s) with hR
  have hMd0 : 0 ≤ Md := le_trans (abs_nonneg _) (hKdbd a 0)
  have hKlip0 : 0 ≤ Klip := by
    have h1 := hKlip 1 0 0
    have h2 : (0 : ℝ) ≤ Klip * |(1 : ℝ) - 0| := le_trans (abs_nonneg _) h1
    simpa using h2
  have hwbd : ∀ s, |w s| ≤ Md / m := fun s =>
    abs_variation_le (K := K) hkap0 hkap1 hPf hKdcont hsol hstrip hper hKdper hKdbd a s
  have hwcont : Continuous w :=
    continuous_variation (K := K) hkap0 hkap1 hPf hKdcont hsol hstrip hper hKdper a
  have hKa : Continuous (K a) := hKcont.comp (continuous_const.prodMk continuous_id)
  have hKb : Continuous (K b) := hKcont.comp (continuous_const.prodMk continuous_id)
  have hKda : Continuous (Kd a) := hKdcont.comp (continuous_const.prodMk continuous_id)
  have hcosa : Continuous fun s => Real.cos (delta a s) :=
    Real.continuous_cos.comp (continuous_delta_slice hsol a)
  have hRcont : Continuous R := by
    rw [hR]
    exact ((hKb.sub hKa).sub (continuous_const.mul hKda)).add
      ((continuous_const.mul hwcont).mul (hcosa.sub (continuous_avgCos hsol b a)))
  -- the error equation
  have hediff : ∀ x, HasDerivAt e (R x - avgCos delta b a x * e x) x := by
    intro x
    have h1 := (hsol b x).sub (hsol a x)
    have h2 := (hasDerivAt_variation (K := K) hkap0 hkap1 hPf hKdcont hsol hstrip hper hKdper a
      x).const_mul h
    have h3 := h1.sub h2
    refine h3.congr_deriv ?_
    have hid := sin_sub_eq_avgCos_mul delta b a x
    simp only [he, hR]
    nlinarith [hid]
  -- the error is bounded
  have hebd : ∀ x, |e x| ≤ 2 + |h| * (Md / m) := by
    intro x
    have h1 := abs_delta_sub_le_two hstrip b a x
    have h2 : |h * w x| ≤ |h| * (Md / m) := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hwbd x) (abs_nonneg h)
    calc |e x| = |(delta b x - delta a x) - h * w x| := by rw [he]
      _ ≤ |delta b x - delta a x| + |h * w x| := abs_sub _ _
      _ ≤ 2 + |h| * (Md / m) := add_le_add h1 h2
  -- the source is quadratic
  have hRbd : ∀ x, |R x| ≤ (CK + Md * Klip / m ^ 2) * h ^ 2 := by
    intro x
    have h1 : |K b x - K a x - h * Kd a x| ≤ CK * h ^ 2 := by
      have := hKtaylor b a x
      rw [hh]
      simpa [mul_comm] using this
    have hdd : |delta b x - delta a x| ≤ Klip * |h| / m := by
      have := abs_delta_sub_le hkap0 hkap1 hKcont hsol hstrip hKlip b a x
      rw [hh]
      exact this
    have h2 : |Real.cos (delta a x) - avgCos delta b a x| ≤ Klip * |h| / m := by
      have hb := abs_avgCos_sub_cos_le delta b a x
      calc |Real.cos (delta a x) - avgCos delta b a x|
          = |avgCos delta b a x - Real.cos (delta a x)| := abs_sub_comm _ _
        _ ≤ |delta b x - delta a x| := hb
        _ ≤ Klip * |h| / m := hdd
    have h3 : |h * w x * (Real.cos (delta a x) - avgCos delta b a x)|
        ≤ |h| * (Md / m) * (Klip * |h| / m) := by
      rw [abs_mul, abs_mul]
      refine mul_le_mul (mul_le_mul_of_nonneg_left (hwbd x) (abs_nonneg h)) h2 (abs_nonneg _) ?_
      positivity
    have hsum : |R x| ≤ CK * h ^ 2 + |h| * (Md / m) * (Klip * |h| / m) := by
      rw [hR]
      exact le_trans (abs_add_le _ _) (add_le_add h1 h3)
    have hsq : |h| * (Md / m) * (Klip * |h| / m) = Md * Klip / m ^ 2 * h ^ 2 := by
      have hab : |h| * |h| = h ^ 2 := by
        rw [← abs_mul, abs_of_nonneg (mul_self_nonneg h)]; ring
      calc |h| * (Md / m) * (Klip * |h| / m)
          = |h| * |h| * (Md * Klip) / (m * m) := by ring
        _ = h ^ 2 * (Md * Klip) / (m * m) := by rw [hab]
        _ = Md * Klip / m ^ 2 * h ^ 2 := by ring
    rw [hsq] at hsum
    calc |R x| ≤ CK * h ^ 2 + Md * Klip / m ^ 2 * h ^ 2 := hsum
      _ = (CK + Md * Klip / m ^ 2) * h ^ 2 := by ring
  have := abs_le_of_bounded_dissipative (u := e) (a := avgCos delta b a) (f := R)
    (c := m) (M := (CK + Md * Klip / m ^ 2) * h ^ 2) (B := 2 + |h| * (Md / m)) hmpos
    (continuous_avgCos hsol b a) hRcont (fun x => avgCos_ge hstrip b a x) hediff hebd hRbd s
  calc |delta b s - delta a s - h * w s| = |e s| := by rw [he]
    _ ≤ (CK + Md * Klip / m ^ 2) * h ^ 2 / m := this
    _ = (CK + Md * Klip / m ^ 2) / m * h ^ 2 := by ring

/-- A quadratic error bound gives the derivative. -/
theorem hasDerivAt_of_quadratic {g : ℝ → ℝ} {a L C : ℝ} (hC : 0 ≤ C)
    (hq : ∀ b, |g b - g a - (b - a) * L| ≤ C * (b - a) ^ 2) : HasDerivAt g L a := by
  rw [hasDerivAt_iff_isLittleO, Asymptotics.isLittleO_iff]
  intro eps heps
  have hsmall : ∀ᶠ b in nhds a, |b - a| ≤ eps / (C + 1) := by
    have hpos : 0 < eps / (C + 1) := by positivity
    filter_upwards [Metric.ball_mem_nhds a hpos] with b hb
    have : dist b a < eps / (C + 1) := hb
    rw [Real.dist_eq] at this
    exact this.le
  filter_upwards [hsmall] with b hb
  have habs : ‖g b - g a - (b - a) • L‖ = |g b - g a - (b - a) * L| := by simp [smul_eq_mul]
  rw [habs]
  have hq2 : (b - a) ^ 2 = |b - a| * |b - a| := by
    rw [← abs_mul, abs_of_nonneg (mul_self_nonneg (b - a))]; ring
  have hfac : C * |b - a| ≤ eps := by
    have h1 : C * |b - a| ≤ C * (eps / (C + 1)) := mul_le_mul_of_nonneg_left hb hC
    have h2 : C * (eps / (C + 1)) ≤ eps := by
      rw [mul_div_assoc']
      rw [div_le_iff₀ (by positivity)]
      nlinarith
    linarith
  calc |g b - g a - (b - a) * L| ≤ C * (b - a) ^ 2 := hq b
    _ = (C * |b - a|) * |b - a| := by rw [hq2]; ring
    _ ≤ eps * ‖b - a‖ := by
        have : ‖b - a‖ = |b - a| := rfl
        rw [this]
        exact mul_le_mul_of_nonneg_right hfac (abs_nonneg _)

/-- **The derivative of the steering angle in the path parameter.** -/
theorem hasDerivAt_param (hkap0 : 0 ≤ kap) (hkap1 : kap < 1) (hPf : ∀ a, 0 < Pf a)
    (hKcont : Continuous (uncurry K)) (hKdcont : Continuous (uncurry Kd))
    (hsol : ∀ a s, HasDerivAt (delta a) (K a s - Real.sin (delta a s)) s)
    (hstrip : ∀ a s, delta a s ∈ Icc (0 : ℝ) (arcsin kap))
    (hper : ∀ a, Function.Periodic (delta a) (Pf a))
    (hKdper : ∀ a, Function.Periodic (Kd a) (Pf a))
    (hKdbd : ∀ a s, |Kd a s| ≤ Md)
    (hKlip : ∀ a b s, |K a s - K b s| ≤ Klip * |a - b|)
    (hKtaylor : ∀ a b s, |K a s - K b s - (a - b) * Kd b s| ≤ CK * (a - b) ^ 2)
    (hCK : 0 ≤ CK) (a s : ℝ) :
    HasDerivAt (fun b => delta b s) (variation Kd delta Pf a s) a := by
  set m : ℝ := Real.sqrt (1 - kap ^ 2) with hm
  have hmpos : 0 < m := sqrt_pos_of_lt hkap0 hkap1
  have hMd0 : 0 ≤ Md := le_trans (abs_nonneg _) (hKdbd a 0)
  have hKlip0 : 0 ≤ Klip := by
    have h1 := hKlip 1 0 0
    have h2 : (0 : ℝ) ≤ Klip * |(1 : ℝ) - 0| := le_trans (abs_nonneg _) h1
    simpa using h2
  refine hasDerivAt_of_quadratic (C := (CK + Md * Klip / m ^ 2) / m) (by positivity) ?_
  intro b
  exact abs_error_le hkap0 hkap1 hPf hKcont hKdcont hsol hstrip hper hKdper hKdbd hKlip
    hKtaylor a b s

/-- **The selected steering angle is jointly continuous.** -/
theorem continuous_uncurry_delta (hkap0 : 0 ≤ kap) (hkap1 : kap < 1)
    (hKcont : Continuous (uncurry K))
    (hsol : ∀ a s, HasDerivAt (delta a) (K a s - Real.sin (delta a s)) s)
    (hstrip : ∀ a s, delta a s ∈ Icc (0 : ℝ) (arcsin kap))
    (hKlip : ∀ a b s, |K a s - K b s| ≤ Klip * |a - b|) :
    Continuous (uncurry delta) := by
  have hmpos := sqrt_pos_of_lt hkap0 hkap1
  set L : ℝ := Klip / Real.sqrt (1 - kap ^ 2) with hL
  have hKlip0 : 0 ≤ Klip := by
    have h1 := hKlip 1 0 0
    have h2 : (0 : ℝ) ≤ Klip * |(1 : ℝ) - 0| := le_trans (abs_nonneg _) h1
    simpa using h2
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
    have h := abs_delta_sub_le hkap0 hkap1 hKcont hsol hstrip hKlip a a0 x
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

/-! ### Higher joint regularity -/

/-- One step of the bootstrap: if the steering angle is jointly `Cⁿ`, so are
its two partial derivatives, hence it is jointly `C^{n+1}`. -/
theorem contDiff_succ_of_contDiff (hkap0 : 0 ≤ kap) (hkap1 : kap < 1) (hPf : ∀ a, 0 < Pf a)
    (hKcont : Continuous (uncurry K)) (hKdcont : Continuous (uncurry Kd))
    (hsol : ∀ a s, HasDerivAt (delta a) (K a s - Real.sin (delta a s)) s)
    (hstrip : ∀ a s, delta a s ∈ Icc (0 : ℝ) (arcsin kap))
    (hper : ∀ a, Function.Periodic (delta a) (Pf a))
    (hKdper : ∀ a, Function.Periodic (Kd a) (Pf a))
    (hKdbd : ∀ a s, |Kd a s| ≤ Md)
    (hKlip : ∀ a b s, |K a s - K b s| ≤ Klip * |a - b|)
    (hKtaylor : ∀ a b s, |K a s - K b s - (a - b) * Kd b s| ≤ CK * (a - b) ^ 2)
    (hCK : 0 ≤ CK) (hdelta : ContDiff ℝ (n : ℕ) (uncurry delta))
    (hPfC : ContDiff ℝ (n : ℕ) Pf) (hK : ContDiff ℝ (n : ℕ) (uncurry K))
    (hKd : ContDiff ℝ (n : ℕ) (uncurry Kd)) :
    ContDiff ℝ ((n + 1 : ℕ)) (uncurry delta) := by
  have hdt : ∀ a s, HasDerivAt (fun b => delta b s) (variation Kd delta Pf a s) a := fun a s =>
    hasDerivAt_param hkap0 hkap1 hPf hKcont hKdcont hsol hstrip hper hKdper hKdbd hKlip
      hKtaylor hCK a s
  have hcos : ContDiff ℝ (n : ℕ) (uncurry fun a s => Real.cos (delta a s)) :=
    Real.contDiff_cos.comp hdelta
  have hpos : ∀ a, 0 < prim (fun s => Real.cos (delta a s)) (Pf a) := fun a =>
    prim_cos_pos (K := K) hkap0 hkap1 hPf hsol hstrip a
  have hw : ContDiff ℝ (n : ℕ) (uncurry (variation Kd delta Pf)) :=
    PeriodicGreenSmooth.contDiff_periodicGreen_param_var
      (A := fun a s => Real.cos (delta a s)) (F := Kd) (L := Pf) hcos hKd hPfC hpos
  have hs : ContDiff ℝ (n : ℕ) (uncurry fun a s => K a s - Real.sin (delta a s)) :=
    hK.sub (Real.contDiff_sin.comp hdelta)
  exact RearOwnTangential.contDiff_succ_of_partials hdt hsol hw hs

/-- **The selected steering angle of a path of fronts of moving perimeter is
jointly `C^{n+1}`** as soon as the front curvature, its derivative in the path
parameter and the arclength period are jointly `Cⁿ`. -/
theorem contDiff_succ_uncurry_delta (hkap0 : 0 ≤ kap) (hkap1 : kap < 1) (hPf : ∀ a, 0 < Pf a)
    (hsol : ∀ a s, HasDerivAt (delta a) (K a s - Real.sin (delta a s)) s)
    (hstrip : ∀ a s, delta a s ∈ Icc (0 : ℝ) (arcsin kap))
    (hper : ∀ a, Function.Periodic (delta a) (Pf a))
    (hKdper : ∀ a, Function.Periodic (Kd a) (Pf a))
    (hKdbd : ∀ a s, |Kd a s| ≤ Md)
    (hKlip : ∀ a b s, |K a s - K b s| ≤ Klip * |a - b|)
    (hKtaylor : ∀ a b s, |K a s - K b s - (a - b) * Kd b s| ≤ CK * (a - b) ^ 2)
    (hCK : 0 ≤ CK) (hPfC : ContDiff ℝ (n : ℕ) Pf) (hK : ContDiff ℝ (n : ℕ) (uncurry K))
    (hKd : ContDiff ℝ (n : ℕ) (uncurry Kd)) :
    ContDiff ℝ ((n + 1 : ℕ)) (uncurry delta) := by
  have hcont : Continuous (uncurry delta) :=
    continuous_uncurry_delta hkap0 hkap1 hK.continuous hsol hstrip hKlip
  induction n with
  | zero =>
      have hdelta0 : ContDiff ℝ ((0 : ℕ)) (uncurry delta) := by
        simpa using (contDiff_zero (𝕜 := ℝ) (f := uncurry delta)).mpr hcont
      exact contDiff_succ_of_contDiff hkap0 hkap1 hPf hK.continuous hKd.continuous hsol hstrip
        hper hKdper hKdbd hKlip hKtaylor hCK hdelta0 hPfC hK hKd
  | succ k ih =>
      have hle : ((k : ℕ) : WithTop ℕ∞) ≤ ((k + 1 : ℕ) : WithTop ℕ∞) := by
        exact_mod_cast (by omega : (k : ℕ) ≤ k + 1)
      have hdelta : ContDiff ℝ ((k + 1 : ℕ)) (uncurry delta) :=
        ih (hPfC.of_le hle) (hK.of_le hle) (hKd.of_le hle)
      exact contDiff_succ_of_contDiff hkap0 hkap1 hPf hK.continuous hKd.continuous hsol hstrip
        hper hKdper hKdbd hKlip hKtaylor hCK hdelta hPfC hK hKd

/-- The joint `C⁴` case, the regularity the assembly of the path metric
consumes. -/
theorem contDiff_four_uncurry_delta (hkap0 : 0 ≤ kap) (hkap1 : kap < 1) (hPf : ∀ a, 0 < Pf a)
    (hsol : ∀ a s, HasDerivAt (delta a) (K a s - Real.sin (delta a s)) s)
    (hstrip : ∀ a s, delta a s ∈ Icc (0 : ℝ) (arcsin kap))
    (hper : ∀ a, Function.Periodic (delta a) (Pf a))
    (hKdper : ∀ a, Function.Periodic (Kd a) (Pf a))
    (hKdbd : ∀ a s, |Kd a s| ≤ Md)
    (hKlip : ∀ a b s, |K a s - K b s| ≤ Klip * |a - b|)
    (hKtaylor : ∀ a b s, |K a s - K b s - (a - b) * Kd b s| ≤ CK * (a - b) ^ 2)
    (hCK : 0 ≤ CK) (hPfC : ContDiff ℝ (3 : ℕ) Pf) (hK : ContDiff ℝ (3 : ℕ) (uncurry K))
    (hKd : ContDiff ℝ (3 : ℕ) (uncurry Kd)) :
    ContDiff ℝ (4 : ℕ) (uncurry delta) := by
  have h := contDiff_succ_uncurry_delta (n := 3) hkap0 hkap1 hPf hsol hstrip hper hKdper hKdbd
    hKlip hKtaylor hCK hPfC hK hKd
  simpa using h


/-! ### A worked instance with a genuinely moving perimeter -/

namespace Instance

/-- The front curvature of the instance: the circle of curvature `(3 + sin a)/8`. -/
def curv (a : ℝ) (_ : ℝ) : ℝ := (3 + Real.sin a) / 8

/-- Its derivative in the path parameter. -/
def curvDot (a : ℝ) (_ : ℝ) : ℝ := Real.cos a / 8

/-- The arclength period of the front: the perimeter `2π/κ` of that circle,
which genuinely moves along the path. -/
def per (a : ℝ) : ℝ := 16 * Real.pi / (3 + Real.sin a)

/-- The selected steering angle of the instance. -/
def steer (a : ℝ) (_ : ℝ) : ℝ := Real.arcsin ((3 + Real.sin a) / 8)

theorem curv_bounds (a s : ℝ) : (1 : ℝ) / 4 ≤ curv a s ∧ curv a s ≤ 1 / 2 := by
  have h := Real.neg_one_le_sin a
  have h' := Real.sin_le_one a
  constructor <;> simp only [curv] <;> linarith

theorem sin_steer (a s : ℝ) : Real.sin (steer a s) = curv a s := by
  have h1 := (curv_bounds a s).1
  have h2 := (curv_bounds a s).2
  simp only [curv] at h1 h2 ⊢
  exact Real.sin_arcsin (by linarith) (by linarith)

theorem denom_pos (a : ℝ) : 0 < 3 + Real.sin a := by
  have := Real.neg_one_le_sin a; linarith

theorem per_pos (a : ℝ) : 0 < per a := by
  have h := denom_pos a
  have hpi := Real.pi_pos
  simp only [per]
  positivity

theorem contDiff_per {m : ℕ} : ContDiff ℝ (m : ℕ) per := by
  have hden : ContDiff ℝ (m : ℕ) fun a : ℝ => 3 + Real.sin a :=
    contDiff_const.add (Real.contDiff_sin.of_le le_top)
  exact contDiff_const.div hden (fun a => (denom_pos a).ne')

/-- **The hypotheses of the moving-perimeter regularity theorem are
consistent.**  For the path of circles of curvature `(3 + sin a)/8`, whose
arclength period `16π/(3 + sin a)` genuinely varies with the path parameter,
every hypothesis of `contDiff_four_uncurry_delta` holds, with `κ̂ = 1/2` and
`M_d = K_lip = C_K = 1/8`. -/
theorem steering_variable_period_instance : ContDiff ℝ (4 : ℕ) (uncurry steer) := by
  have hsol : ∀ a s, HasDerivAt (steer a) (curv a s - Real.sin (steer a s)) s := by
    intro a s
    have hz : curv a s - Real.sin (steer a s) = 0 := by rw [sin_steer a s]; ring
    rw [hz]
    exact hasDerivAt_const s _
  have hstrip : ∀ a s, steer a s ∈ Icc (0 : ℝ) (arcsin (1 / 2)) := by
    intro a s
    have h1 := (curv_bounds a s).1
    have h2 := (curv_bounds a s).2
    have hd : steer a s = Real.arcsin (curv a s) := rfl
    rw [hd]
    exact ⟨Real.arcsin_nonneg.mpr (by linarith), Real.arcsin_le_arcsin h2⟩
  have hper : ∀ a, Function.Periodic (steer a) (per a) := fun a s => rfl
  have hKdper : ∀ a, Function.Periodic (curvDot a) (per a) := fun a s => rfl
  have hKdbd : ∀ a s, |curvDot a s| ≤ 1 / 8 := by
    intro a s
    have h := Real.abs_cos_le_one a
    simp only [curvDot]
    rw [abs_div, abs_of_nonneg (by norm_num : (0:ℝ) ≤ (8:ℝ))]
    linarith
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
  have hK : ContDiff ℝ ((3 : ℕ)) (uncurry curv) :=
    (contDiff_const.add ((Real.contDiff_sin.of_le le_top).comp contDiff_fst)).div_const 8
  have hKd : ContDiff ℝ ((3 : ℕ)) (uncurry curvDot) :=
    ((Real.contDiff_cos.of_le le_top).comp contDiff_fst).div_const 8
  exact contDiff_four_uncurry_delta (K := curv) (Kd := curvDot) (Pf := per) (kap := 1/2)
    (by norm_num) (by norm_num) per_pos hsol hstrip hper hKdper hKdbd hKlip hKtaylor
    (by norm_num) contDiff_per hK hKd

end Instance

end SteeringVariablePeriod
