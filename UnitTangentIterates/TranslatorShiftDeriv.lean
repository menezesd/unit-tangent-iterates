import Mathlib

/-!
# Differentiability of the translator shift

This file supplies the regularity input needed for the *translation law* of
Section 3 of the paper *A Noncircular Oval with Convex Unit-Tangent Iterates*.

Let `f` be a measurable profile with `0 < m ≤ f ≤ M` on the whole line and let
`A` be a primitive of `f`, in the sense that `A y - A x = ∫_x^y f`.  Then `A`
is a continuous, strictly increasing bijection of `ℝ`, so it has a continuous
inverse.  If `U` solves the defining equation `∫_θ^{U θ} f = sin θ` on
`(0, π)` and `f` is continuous there, then

`U θ = A⁻¹ (A θ + sin θ)`,

and the chain rule (with the inverse function theorem for `A⁻¹`) gives

`U'(θ) = (f θ + cos θ) / f (U θ)`.

Note that only *continuity* of `f` is needed: the shift is differentiable even
though the profile need not be.

Main results:

* `strictMono_primitive`, `continuous_primitive'`, `surjective_primitive` : the
  primitive is a homeomorphic order isomorphism of the line;
* `exists_inverse` : a continuous two-sided inverse;
* `hasDerivAt_primitive` : `A' = f` at points of continuity of `f`;
* `hasDerivAt_shift` : `U' = (f + cos)/f∘U` on `(0, π)`.
-/

noncomputable section

open Real Set MeasureTheory Filter Topology

namespace TranslatorShift

variable {f A U : ℝ → ℝ} {m M : ℝ}

/-! ### The primitive is an increasing homeomorphism of the line -/

/-- Lower bound for the increments of a primitive of a profile `≥ m`. -/
theorem le_sub_primitive (hint : ∀ a b : ℝ, IntervalIntegrable f volume a b)
    (hAsub : ∀ x y : ℝ, A y - A x = ∫ t in x..y, f t) (hmf : ∀ t, m ≤ f t)
    {x y : ℝ} (hxy : x ≤ y) : m * (y - x) ≤ A y - A x := by
  have h := intervalIntegral.integral_mono_on (μ := volume) (a := x) (b := y)
    (f := fun _ => m) (g := f) hxy _root_.intervalIntegrable_const (hint x y)
    (fun t _ => hmf t)
  rw [hAsub x y]
  simpa [mul_comm] using h

/-- Upper bound for the increments of a primitive of a profile `≤ M`. -/
theorem sub_primitive_le (hint : ∀ a b : ℝ, IntervalIntegrable f volume a b)
    (hAsub : ∀ x y : ℝ, A y - A x = ∫ t in x..y, f t) (hfM : ∀ t, f t ≤ M)
    {x y : ℝ} (hxy : x ≤ y) : A y - A x ≤ M * (y - x) := by
  have h := intervalIntegral.integral_mono_on (μ := volume) (a := x) (b := y)
    (f := f) (g := fun _ => M) hxy (hint x y) _root_.intervalIntegrable_const
    (fun t _ => hfM t)
  rw [hAsub x y]
  simpa [mul_comm] using h

theorem strictMono_primitive (hint : ∀ a b : ℝ, IntervalIntegrable f volume a b)
    (hAsub : ∀ x y : ℝ, A y - A x = ∫ t in x..y, f t) (hm0 : 0 < m) (hmf : ∀ t, m ≤ f t) :
    StrictMono A := by
  intro x y hxy
  have := le_sub_primitive hint hAsub hmf hxy.le
  nlinarith [this, mul_pos hm0 (sub_pos.mpr hxy)]

theorem continuous_primitive' (hint : ∀ a b : ℝ, IntervalIntegrable f volume a b)
    (hAsub : ∀ x y : ℝ, A y - A x = ∫ t in x..y, f t) : Continuous A := by
  have hc : Continuous fun y : ℝ => ∫ t in (0:ℝ)..y, f t :=
    intervalIntegral.continuous_primitive hint 0
  have heq : A = fun y => A 0 + ∫ t in (0:ℝ)..y, f t := by
    funext y; have := hAsub 0 y; linarith
  rw [heq]
  exact continuous_const.add hc

theorem surjective_primitive (hint : ∀ a b : ℝ, IntervalIntegrable f volume a b)
    (hAsub : ∀ x y : ℝ, A y - A x = ∫ t in x..y, f t) (hm0 : 0 < m) (hmf : ∀ t, m ≤ f t) :
    Function.Surjective A := by
  have hcont : Continuous A := continuous_primitive' hint hAsub
  have hmul : Tendsto (fun s : ℝ => m * s) atTop atTop :=
    Filter.Tendsto.const_mul_atTop hm0 tendsto_id
  have hmul' : Tendsto (fun s : ℝ => m * s) atBot atBot := by
    simpa using Filter.Tendsto.const_mul_atBot hm0 tendsto_id
  refine hcont.surjective ?_ ?_
  · refine tendsto_atTop_mono' atTop ?_ (tendsto_atTop_add_const_left _ (A 0) hmul)
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with s hs
    have := le_sub_primitive hint hAsub hmf hs
    simp only [sub_zero] at this
    linarith
  · refine tendsto_atBot_mono' atBot ?_ (tendsto_atBot_add_const_left _ (A 0) hmul')
    filter_upwards [eventually_le_atBot (0 : ℝ)] with s hs
    have := le_sub_primitive hint hAsub hmf hs
    simp only [zero_sub] at this
    linarith

/-- The primitive has a continuous two-sided inverse. -/
theorem exists_inverse (hint : ∀ a b : ℝ, IntervalIntegrable f volume a b)
    (hAsub : ∀ x y : ℝ, A y - A x = ∫ t in x..y, f t) (hm0 : 0 < m) (hmf : ∀ t, m ≤ f t) :
    ∃ Ainv : ℝ → ℝ, Continuous Ainv ∧ (∀ y, A (Ainv y) = y) ∧ (∀ x, Ainv (A x) = x) := by
  have hmono : StrictMono A := strictMono_primitive hint hAsub hm0 hmf
  have hsurj : Function.Surjective A := surjective_primitive hint hAsub hm0 hmf
  set iso : ℝ ≃o ℝ := hmono.orderIsoOfSurjective A hsurj with hiso
  have happ : ∀ x, iso x = A x := fun _ => rfl
  refine ⟨iso.symm, iso.symm.toHomeomorph.continuous, ?_, ?_⟩
  · intro y; rw [← happ]; exact iso.apply_symm_apply y
  · intro x; rw [← happ x]; exact iso.symm_apply_apply x

/-! ### The primitive is differentiable where the profile is continuous -/

/-- `A' = f` at any point where `f` is continuous. -/
theorem hasDerivAt_primitive (hint : ∀ a b : ℝ, IntervalIntegrable f volume a b)
    (hAsub : ∀ x y : ℝ, A y - A x = ∫ t in x..y, f t) (hmeas : Measurable f)
    {x : ℝ} (hx : ContinuousAt f x) : HasDerivAt A (f x) x := by
  have hd : HasDerivAt (fun u => ∫ t in (0:ℝ)..u, f t) (f x) x :=
    intervalIntegral.integral_hasDerivAt_right (hint 0 x)
      (hmeas.stronglyMeasurable.stronglyMeasurableAtFilter) hx
  have heq : A = fun y => A 0 + ∫ t in (0:ℝ)..y, f t := by
    funext y; have := hAsub 0 y; linarith
  rw [heq]
  simpa using hd.const_add (A 0)

/-! ### The shift is differentiable -/

/-- **The translator shift is differentiable**, with
`U'(θ) = (f θ + cos θ)/f(U θ)`, as soon as the profile is continuous on
`(0, π)` (no differentiability of the profile is needed). -/
theorem hasDerivAt_shift (hint : ∀ a b : ℝ, IntervalIntegrable f volume a b)
    (hAsub : ∀ x y : ℝ, A y - A x = ∫ t in x..y, f t) (hmeas : Measurable f)
    (hm0 : 0 < m) (hmf : ∀ t, m ≤ f t)
    (hcont : ContinuousOn f (Ioo 0 π))
    (hU : ∀ θ ∈ Ioo (0:ℝ) π, (∫ t in θ..U θ, f t) = Real.sin θ)
    (hmaps : ∀ θ ∈ Ioo (0:ℝ) π, U θ ∈ Ioo (0:ℝ) π)
    {θ : ℝ} (hθ : θ ∈ Ioo (0:ℝ) π) :
    HasDerivAt U ((f θ + Real.cos θ) / f (U θ)) θ := by
  obtain ⟨Ainv, hAinvc, hAinv, hinvA⟩ := exists_inverse hint hAsub hm0 hmf
  have hfcont : ∀ x ∈ Ioo (0:ℝ) π, ContinuousAt f x := fun x hx =>
    hcont.continuousAt (isOpen_Ioo.mem_nhds hx)
  -- derivative of `A` at `U θ`
  have hAU : HasDerivAt A (f (U θ)) (U θ) :=
    hasDerivAt_primitive hint hAsub hmeas (hfcont _ (hmaps θ hθ))
  have hfU : f (U θ) ≠ 0 := by
    have := hmf (U θ); linarith
  -- derivative of the inverse at `A (U θ)`
  have hpt : Ainv (A (U θ)) = U θ := hinvA _
  have hAinvd : HasDerivAt Ainv (f (U θ))⁻¹ (A (U θ)) := by
    refine HasDerivAt.of_local_left_inverse (f := A) (g := Ainv) hAinvc.continuousAt ?_ hfU ?_
    · rw [hpt]; exact hAU
    · filter_upwards with z using hAinv z
  -- derivative of `σ ↦ A σ + sin σ`
  have hg : HasDerivAt (fun σ => A σ + Real.sin σ) (f θ + Real.cos θ) θ :=
    (hasDerivAt_primitive hint hAsub hmeas (hfcont _ hθ)).add (Real.hasDerivAt_sin θ)
  have hval : A θ + Real.sin θ = A (U θ) := by
    have := hAsub θ (U θ)
    rw [hU θ hθ] at this
    linarith
  have hchain : HasDerivAt (fun σ => Ainv (A σ + Real.sin σ))
      ((f θ + Real.cos θ) * (f (U θ))⁻¹) θ := by
    have := (hval ▸ hAinvd).comp θ hg
    simpa [mul_comm] using this
  refine hchain.congr_of_eventuallyEq ?_
  filter_upwards [isOpen_Ioo.mem_nhds hθ] with σ hσ
  have : A σ + Real.sin σ = A (U σ) := by
    have h := hAsub σ (U σ)
    rw [hU σ hσ] at h
    linarith
  rw [this, hinvA]

end TranslatorShift
