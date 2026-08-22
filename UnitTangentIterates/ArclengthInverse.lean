import Mathlib
import UnitTangentIterates.RearTrack

/-!
# Inverting the rear arclength, and periodic bookkeeping

The inverse Jacobi estimates of the paper *A Noncircular Oval with Convex
Unit-Tangent Iterates* are stated in the **rear** arclength `x`, while the
steering equation lives in the **front** arclength `s`.  The change of variable
between them is the rear arclength function

`x(s) = ∫₀ˢ cos δ`,

which on the selected strip has derivative `cos δ ≥ c > 0`, hence is an
increasing bijection of the line.  This file collects the elementary facts
about its inverse `sf` and about periodic functions that the passage from the
geometry of one slice to the hypotheses of the Jacobi estimates needs:

* `leftInverse_of_rightInverse`, `continuous_of_rightInverse`,
  `hasDerivAt_of_rightInverse` — a right inverse of a function whose derivative
  is bounded below by `c > 0` is automatically a two-sided inverse, continuous,
  and differentiable with derivative `1/f'`;
* `rightInverse_add_of_shift` — it turns the shift `f(s+P) = f s + l` into the
  shift `sf(y+l) = sf y + P`;
* `rearArclength_add_period`, `rearArclength_ge`, `rearArclength_le_of_period` —
  the rear arclength of a `P`-periodic steering angle shifts by the rear period
  `l = x(P)` and satisfies `c·P ≤ l ≤ P`;
* `bddAbove_abs_of_periodic`, `periodic_of_hasDerivAt` — a continuous periodic
  function is bounded, and the derivative of a periodic function is periodic.
-/

noncomputable section

open Set MeasureTheory intervalIntegral Filter

namespace ArclengthInverse

/-! ### Periodic bookkeeping -/

/-- A continuous periodic function is bounded. -/
theorem bddAbove_abs_of_periodic {f : ℝ → ℝ} {P : ℝ} (hP : 0 < P) (hc : Continuous f)
    (hper : Function.Periodic f P) : BddAbove (Set.range fun s => |f s|) := by
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := (0:ℝ)) (b := P)).exists_bound_of_continuousOn
    hc.abs.continuousOn
  refine ⟨M, ?_⟩
  rintro y ⟨s, rfl⟩
  obtain ⟨t, ht, hts⟩ := hper.exists_mem_Ico₀ hP s
  have h := hM t ⟨ht.1, ht.2.le⟩
  simp only [Real.norm_eq_abs, abs_abs] at h
  show |f s| ≤ M
  rw [hts]
  exact h

/-- The derivative of a periodic function is periodic. -/
theorem periodic_of_hasDerivAt {f f' : ℝ → ℝ} {P : ℝ}
    (hd : ∀ s, HasDerivAt f (f' s) s) (hper : Function.Periodic f P) :
    Function.Periodic f' P := by
  intro s
  have hshift : HasDerivAt (fun r => f (r + P)) (f' (s + P)) s := by
    have h := (hd (s + P)).comp s ((hasDerivAt_id s).add_const P)
    simpa using h
  have heq : (fun r => f (r + P)) = f := funext fun r => hper r
  rw [heq] at hshift
  exact hshift.unique (hd s)

/-! ### Inverting a function with derivative bounded below -/

variable {f g finv : ℝ → ℝ} {c : ℝ}

/-- A function whose derivative is at least `c > 0` is strictly increasing. -/
theorem strictMono_of_deriv_ge (hc : 0 < c) (hf : ∀ s, HasDerivAt f (g s) s)
    (hg : ∀ s, c ≤ g s) : StrictMono f := by
  refine strictMono_of_deriv_pos fun s => ?_
  rw [(hf s).deriv]
  exact lt_of_lt_of_le hc (hg s)

/-- A function whose derivative is at least `c > 0` grows at least linearly. -/
theorem le_of_deriv_ge (hf : ∀ s, HasDerivAt f (g s) s) (hg : ∀ s, c ≤ g s)
    {s : ℝ} (hs : 0 ≤ s) : f 0 + c * s ≤ f s := by
  have hmono : MonotoneOn (fun y => f y - c * y) (Set.Ici 0) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici 0) ?_ ?_ ?_
    · exact Continuous.continuousOn <| by
        have : Continuous f := Differentiable.continuous fun y => (hf y).differentiableAt
        fun_prop
    · intro y _
      exact ((hf y).sub ((hasDerivAt_id y).const_mul c)).differentiableAt.differentiableWithinAt
    · intro y _
      have hd : HasDerivAt (fun z => f z - c * z) (g y - c) y := by
        simpa using (hf y).sub ((hasDerivAt_id y).const_mul c)
      rw [hd.deriv]
      linarith [hg y]
  have h := hmono (Set.self_mem_Ici) (Set.mem_Ici.mpr hs) hs
  simp only [mul_zero, sub_zero] at h
  linarith

/-- The symmetric bound below `0`. -/
theorem ge_of_deriv_ge (hf : ∀ s, HasDerivAt f (g s) s) (hg : ∀ s, c ≤ g s)
    {s : ℝ} (hs : s ≤ 0) : f s ≤ f 0 + c * s := by
  have hmono : MonotoneOn (fun y => f y - c * y) (Set.Iic 0) := by
    refine monotoneOn_of_deriv_nonneg (convex_Iic 0) ?_ ?_ ?_
    · exact Continuous.continuousOn <| by
        have : Continuous f := Differentiable.continuous fun y => (hf y).differentiableAt
        fun_prop
    · intro y _
      exact ((hf y).sub ((hasDerivAt_id y).const_mul c)).differentiableAt.differentiableWithinAt
    · intro y _
      have hd : HasDerivAt (fun z => f z - c * z) (g y - c) y := by
        simpa using (hf y).sub ((hasDerivAt_id y).const_mul c)
      rw [hd.deriv]
      linarith [hg y]
  have h := hmono (Set.mem_Iic.mpr hs) (Set.self_mem_Iic) hs
  simp only [mul_zero, sub_zero] at h
  linarith

/-- **A function whose derivative is bounded below by `c > 0` is a bijection of
the line**; in particular it has a right inverse. -/
theorem surjective_of_deriv_ge (hc : 0 < c) (hf : ∀ s, HasDerivAt f (g s) s)
    (hg : ∀ s, c ≤ g s) : Function.Surjective f := by
  have hcont : Continuous f := Differentiable.continuous fun y => (hf y).differentiableAt
  have hmul : Tendsto (fun s : ℝ => c * s) atTop atTop :=
    Filter.Tendsto.const_mul_atTop hc tendsto_id
  have hmul' : Tendsto (fun s : ℝ => c * s) atBot atBot := by
    simpa using Filter.Tendsto.const_mul_atBot hc tendsto_id
  have hct : Tendsto (fun s : ℝ => f 0 + c * s) atTop atTop :=
    tendsto_atTop_add_const_left _ _ hmul
  have hcb : Tendsto (fun s : ℝ => f 0 + c * s) atBot atBot :=
    tendsto_atBot_add_const_left _ _ hmul'
  refine hcont.surjective ?_ ?_
  · refine tendsto_atTop_mono' atTop ?_ hct
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with s hs
    exact le_of_deriv_ge hf hg hs
  · refine tendsto_atBot_mono' atBot ?_ hcb
    filter_upwards [eventually_le_atBot (0 : ℝ)] with s hs
    exact ge_of_deriv_ge hf hg hs

/-- Hence a right inverse always exists: the hypothesis `f ∘ finv = id` used
below is no restriction. -/
theorem exists_rightInverse (hc : 0 < c) (hf : ∀ s, HasDerivAt f (g s) s)
    (hg : ∀ s, c ≤ g s) : ∃ finv : ℝ → ℝ, ∀ y, f (finv y) = y := by
  obtain ⟨finv, hfinv⟩ := (surjective_of_deriv_ge hc hf hg).hasRightInverse
  exact ⟨finv, hfinv⟩

/-- If `f ∘ finv = id`, then `finv ∘ f = id` as well, once `f` is injective. -/
theorem leftInverse_of_rightInverse (hinj : Function.Injective f)
    (hinv : ∀ y, f (finv y) = y) (s : ℝ) : finv (f s) = s :=
  hinj (hinv (f s))

/-- The order isomorphism defined by a strictly monotone function with a right
inverse. -/
theorem continuous_of_rightInverse (hc : 0 < c) (hf : ∀ s, HasDerivAt f (g s) s)
    (hg : ∀ s, c ≤ g s) (hinv : ∀ y, f (finv y) = y) : Continuous finv := by
  have hmono : StrictMono f := strictMono_of_deriv_ge hc hf hg
  have hsurj : Function.Surjective f := fun y => ⟨finv y, hinv y⟩
  set iso : ℝ ≃o ℝ := hmono.orderIsoOfSurjective f hsurj with hiso
  have hisoapp : ∀ x, iso x = f x := fun _ => rfl
  have hfe : finv = iso.symm := by
    funext y
    have h1 : iso (finv y) = y := by rw [hisoapp]; exact hinv y
    have h2 : finv y = iso.symm (iso (finv y)) := (iso.symm_apply_apply _).symm
    rw [h2, h1]
  rw [hfe]
  exact iso.symm.toHomeomorph.continuous

/-- **The inverse of an increasing function is differentiable**, with
derivative `1/f'`. -/
theorem hasDerivAt_of_rightInverse (hc : 0 < c) (hf : ∀ s, HasDerivAt f (g s) s)
    (hg : ∀ s, c ≤ g s) (hinv : ∀ y, f (finv y) = y) (y : ℝ) :
    HasDerivAt finv (1 / g (finv y)) y := by
  have hcont : ContinuousAt finv y :=
    (continuous_of_rightInverse hc hf hg hinv).continuousAt
  have hne : g (finv y) ≠ 0 := ne_of_gt (lt_of_lt_of_le hc (hg _))
  have heq : ∀ᶠ z in nhds y, f (finv z) = z := by
    filter_upwards with z using hinv z
  simpa [one_div] using HasDerivAt.of_local_left_inverse hcont (hf (finv y)) hne heq

/-- **The inverse translates the shift.**  If `f(s + P) = f s + l`, then
`finv(y + l) = finv y + P`. -/
theorem rightInverse_add_of_shift {P l : ℝ} (hinj : Function.Injective f)
    (hshift : ∀ s, f (s + P) = f s + l) (hinv : ∀ y, f (finv y) = y) (y : ℝ) :
    finv (y + l) = finv y + P := by
  refine hinj ?_
  rw [hinv, hshift, hinv]

/-! ### The rear arclength -/

open RearTrack

variable {δ : ℝ → ℝ}

/-- The rear arclength of a `P`-periodic steering angle shifts by the rear
period `x(P)` over one front period. -/
theorem rearArclength_add_period {P : ℝ} (hδc : Continuous δ)
    (hper : Function.Periodic δ P) (s : ℝ) :
    rearArclength δ (s + P) = rearArclength δ s + rearArclength δ P := by
  have hc : Continuous fun u => Real.cos (δ u) := Real.continuous_cos.comp hδc
  have hint : ∀ a b : ℝ, IntervalIntegrable (fun u => Real.cos (δ u)) volume a b := fun a b =>
    hc.intervalIntegrable a b
  have hcosper : Function.Periodic (fun u => Real.cos (δ u)) P := fun u => by
    simp only [hper u]
  have hsplit : rearArclength δ (s + P)
      = rearArclength δ s + ∫ u in s..(s + P), Real.cos (δ u) := by
    rw [rearArclength, rearArclength,
      ← intervalIntegral.integral_add_adjacent_intervals (hint 0 s) (hint s (s + P))]
  rw [hsplit, hcosper.intervalIntegral_add_eq s 0]
  norm_num [rearArclength]

/-- On the selected strip the rear period is at least `c` times the front
period. -/
theorem rearArclength_ge {c : ℝ} (hδc : Continuous δ) (hcos : ∀ s, c ≤ Real.cos (δ s))
    {P : ℝ} (hP : 0 ≤ P) : c * P ≤ rearArclength δ P := by
  have hc : Continuous fun u => Real.cos (δ u) := Real.continuous_cos.comp hδc
  have h : (∫ _u in (0:ℝ)..P, c) ≤ ∫ u in (0:ℝ)..P, Real.cos (δ u) :=
    intervalIntegral.integral_mono_on hP intervalIntegral.intervalIntegrable_const
      (hc.intervalIntegrable 0 P) (fun u _ => hcos u)
  rw [intervalIntegral.integral_const] at h
  simpa [rearArclength, mul_comm] using h

/-- The rear period never exceeds the front period. -/
theorem rearArclength_le_of_period (hδc : Continuous δ) {P : ℝ} (hP : 0 ≤ P) :
    rearArclength δ P ≤ P := by
  have hc : Continuous fun u => Real.cos (δ u) := Real.continuous_cos.comp hδc
  have h : (∫ u in (0:ℝ)..P, Real.cos (δ u)) ≤ ∫ _u in (0:ℝ)..P, (1:ℝ) :=
    intervalIntegral.integral_mono_on hP (hc.intervalIntegrable 0 P)
      intervalIntegral.intervalIntegrable_const (fun u _ => Real.cos_le_one _)
  rw [intervalIntegral.integral_const] at h
  simpa [rearArclength] using h

/-- **The rear arclength always has an inverse on the selected strip**: since
`x_s = cos δ ≥ √(1 − κ̂²) > 0`, the map `s ↦ x(s)` is a bijection of the line.
So assuming a right inverse `sf` of the rear arclength, as the estimates of the
path metric do, is no restriction. -/
theorem exists_inverse_rearArclength {kap : ℝ} (hkap0 : 0 ≤ kap) (hkap1 : kap < 1)
    (hδc : Continuous δ) (hd0 : ∀ s, 0 ≤ δ s) (hd1 : ∀ s, δ s ≤ Real.arcsin kap) :
    ∃ sf : ℝ → ℝ, ∀ x, rearArclength δ (sf x) = x := by
  have hcpos : 0 < Real.sqrt (1 - kap ^ 2) := Real.sqrt_pos.mpr (by nlinarith)
  exact exists_rightInverse hcpos (fun s => hasDerivAt_rearArclength hδc s)
    (fun s => Shadowing.cos_ge_of_mem_strip (hd0 s) (hd1 s))

end ArclengthInverse
