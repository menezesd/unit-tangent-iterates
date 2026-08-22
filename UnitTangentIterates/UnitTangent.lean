import Mathlib

/-!
# The unit tangent transform: basic facts

This file formalizes the elementary facts about the unit-tangent transform
`(𝒯γ)(s) = γ(s) + τ_γ(s)` from Section 1-2 of the paper
*A Noncircular Oval with Convex Unit-Tangent Iterates*.

We model plane curves as maps `ℝ → ℂ`, and we work with arclength
parametrizations, so that the unit tangent is simply the derivative.

Main results:

* `unitTangentMap_circleCurve_abs`: a circle of radius `r` is mapped to a circle
  of radius `√(r² + 1)`.
* `Periodic.eq_zero_of_deriv_add_self_nonneg`: an auxiliary maximum-principle
  statement: a nonnegative periodic function `u` with `u' + u ≥ 0` that vanishes
  somewhere vanishes identically.
* `curvature_pos_of_next_track_convex`: Lemma 2.2 (*Convex consecutive tracks*):
  if a closed convex curve has convex unit-tangent image, then it is strictly
  convex.
-/

noncomputable section

open Real Complex

namespace UnitTangent

/-- The unit tangent transform of an arclength-parametrized plane curve. -/
noncomputable def unitTangentMap (γ : ℝ → ℂ) : ℝ → ℂ := fun s => γ s + deriv γ s

/-- The arclength parametrization of the circle of centre `c` and radius `r`. -/
noncomputable def circleCurve (c : ℂ) (r : ℝ) : ℝ → ℂ :=
  fun s => c + (r : ℂ) * Complex.exp (Complex.I * (s / r))

lemma hasDerivAt_circleCurve {c : ℂ} {r : ℝ} (hr : r ≠ 0) (s : ℝ) :
    HasDerivAt (circleCurve c r) (Complex.I * Complex.exp (Complex.I * (s / r))) s := by
  have hcast : ((r : ℂ)) ≠ 0 := by exact_mod_cast hr
  have h1 : HasDerivAt (fun s : ℝ => Complex.I * ((s : ℂ) / r)) (Complex.I / r) s := by
    have : HasDerivAt (fun s : ℝ => ((s : ℂ) / r)) (1 / r) s := by
      simpa using (Complex.ofRealCLM.hasDerivAt (x := s)).div_const (r : ℂ)
    simpa [mul_div_assoc] using this.const_mul Complex.I
  have h2 := (h1.cexp).const_mul (r : ℂ)
  have h3 := h2.const_add c
  have : (r : ℂ) * (Complex.exp (Complex.I * ((s : ℂ) / r)) * (Complex.I / r))
      = Complex.I * Complex.exp (Complex.I * ((s : ℂ) / r)) := by
    field_simp
  rw [this] at h3
  exact h3

/-- The circle parametrization is by arclength: its velocity is a unit vector. -/
lemma abs_deriv_circleCurve {c : ℂ} {r : ℝ} (hr : r ≠ 0) (s : ℝ) :
    ‖deriv (circleCurve c r) s‖ = 1 := by
  rw [(hasDerivAt_circleCurve (c := c) hr s).deriv]
  simp [Complex.norm_exp]

/-- **A circle of radius `r` is carried to a circle of radius `√(r² + 1)`.** -/
theorem unitTangentMap_circleCurve_abs {c : ℂ} {r : ℝ} (hr : r ≠ 0) (s : ℝ) :
    ‖unitTangentMap (circleCurve c r) s - c‖ = Real.sqrt (r ^ 2 + 1) := by
  have hd := (hasDerivAt_circleCurve (c := c) hr s).deriv
  have : unitTangentMap (circleCurve c r) s - c
      = ((r : ℂ) + Complex.I) * Complex.exp (Complex.I * (s / r)) := by
    simp [unitTangentMap, circleCurve, hd]
    ring
  rw [this, norm_mul, Complex.norm_exp]
  have h2 : ‖(r : ℂ) + Complex.I‖ = Real.sqrt (r ^ 2 + 1) := by
    rw [Complex.norm_def, Complex.normSq_apply]
    simp
    ring_nf
  simp [h2]

/-- The unit-tangent image of a circle is exactly the circle of radius
`√(r² + 1)` about the same centre. -/
theorem range_unitTangentMap_circleCurve {c : ℂ} {r : ℝ} (hr : 0 < r) :
    Set.range (unitTangentMap (circleCurve c r)) = Metric.sphere c (Real.sqrt (r ^ 2 + 1)) := by
  have hr' : r ≠ 0 := ne_of_gt hr
  have key : ∀ s : ℝ, unitTangentMap (circleCurve c r) s
      = c + ((r : ℂ) + Complex.I) * Complex.exp (Complex.I * (s / r)) := by
    intro s
    have hd := (hasDerivAt_circleCurve (c := c) hr' s).deriv
    simp [unitTangentMap, circleCurve, hd]
    ring
  ext z
  simp only [Set.mem_range, Metric.mem_sphere]
  constructor
  · rintro ⟨s, rfl⟩
    rw [Complex.dist_eq]
    exact unitTangentMap_circleCurve_abs hr' s
  · intro hz
    rw [Complex.dist_eq] at hz
    have hne : ((r : ℂ) + Complex.I) ≠ 0 := by
      intro h
      have : ((r : ℂ) + Complex.I).im = 0 := by rw [h]; simp
      simp at this
    have habs : ‖(r : ℂ) + Complex.I‖ = Real.sqrt (r ^ 2 + 1) := by
      rw [Complex.norm_def, Complex.normSq_apply]
      simp
      ring_nf
    have h1 : ‖(z - c) / ((r : ℂ) + Complex.I)‖ = 1 := by
      rw [norm_div, hz, habs]
      have : Real.sqrt (r ^ 2 + 1) ≠ 0 := by positivity
      field_simp
    obtain ⟨t, ht⟩ := (Complex.norm_eq_one_iff _).mp h1
    refine ⟨t * r, ?_⟩
    rw [key]
    have hcast : ((t * r : ℝ) : ℂ) / (r : ℂ) = (t : ℂ) := by
      have : ((r : ℂ)) ≠ 0 := by exact_mod_cast hr'
      push_cast
      field_simp
    rw [hcast]
    have hcomm : Complex.I * (t : ℂ) = (t : ℂ) * Complex.I := by ring
    rw [hcomm, ht, mul_div_cancel₀ _ hne]
    ring

section MaximumPrinciple

/-- If `u` is a nonnegative periodic differentiable function with `u' + u ≥ 0`
which vanishes at one point, then it vanishes identically. -/
theorem eq_zero_of_deriv_add_self_nonneg {u : ℝ → ℝ} {L : ℝ} (hL : 0 < L)
    (hper : Function.Periodic u L) (hdiff : Differentiable ℝ u)
    (hnn : ∀ x, 0 ≤ u x) (hineq : ∀ x, 0 ≤ deriv u x + u x)
    {x₀ : ℝ} (h0 : u x₀ = 0) : ∀ x, u x = 0 := by
  -- `w = eˣ u` is monotone, hence `u ≤ 0` to the left of `x₀`; periodicity finishes.
  set w : ℝ → ℝ := fun x => Real.exp x * u x with hw
  have hwderiv : ∀ x, HasDerivAt w (Real.exp x * (deriv u x + u x)) x := by
    intro x
    have h := (Real.hasDerivAt_exp x).mul ((hdiff x).hasDerivAt)
    have h2 : Real.exp x * (deriv u x + u x) = Real.exp x * u x + Real.exp x * deriv u x := by
      ring
    rw [hw, h2]
    exact h
  have hwdiff : Differentiable ℝ w := fun x => (hwderiv x).differentiableAt
  have hmono : Monotone w := by
    apply monotone_of_deriv_nonneg hwdiff
    intro x
    rw [(hwderiv x).deriv]
    exact mul_nonneg (Real.exp_pos x).le (hineq x)
  have hleft : ∀ x, x ≤ x₀ → u x = 0 := by
    intro x hx
    have h1 : Real.exp x * u x ≤ Real.exp x₀ * u x₀ := hmono hx
    rw [h0, mul_zero] at h1
    have h4 : u x ≤ 0 := nonpos_of_mul_nonpos_right h1 (Real.exp_pos x)
    linarith [hnn x]
  intro x
  obtain ⟨n, hn⟩ := exists_nat_gt ((x - x₀) / L)
  have hxn : x - n * L ≤ x₀ := by
    have : (x - x₀) / L * L < n * L := by
      exact (mul_lt_mul_of_pos_right hn hL)
    rw [div_mul_cancel₀ _ (ne_of_gt hL)] at this
    linarith
  have := hleft _ hxn
  rwa [hper.sub_nat_mul_eq n] at this

end MaximumPrinciple

/-- **Lemma 2.2 (Convex consecutive tracks).**  If `k ≥ 0` is the (periodic)
curvature of a closed convex curve, and the curvature
`K = u' + u`, `u = k / √(1 + k²)`, of the next track is nonnegative, then `k`
cannot vanish unless it vanishes identically; since a closed convex curve has
nonzero turning number, `k > 0` everywhere. -/
theorem curvature_pos_of_next_track_convex {k : ℝ → ℝ} {L : ℝ} (hL : 0 < L)
    (hper : Function.Periodic k L) (hdiff : Differentiable ℝ k)
    (hnn : ∀ x, 0 ≤ k x)
    (hK : ∀ x, 0 ≤ deriv (fun t => k t / Real.sqrt (1 + k t ^ 2)) x
        + k x / Real.sqrt (1 + k x ^ 2))
    (hne : ∃ x₁, k x₁ ≠ 0) : ∀ x, 0 < k x := by
  set u : ℝ → ℝ := fun t => k t / Real.sqrt (1 + k t ^ 2) with hu
  have hpos : ∀ t, 0 < Real.sqrt (1 + k t ^ 2) := by
    intro t
    have : (0:ℝ) < 1 + k t ^ 2 := by positivity
    exact Real.sqrt_pos.mpr this
  have hsq : Differentiable ℝ (fun t => Real.sqrt (1 + k t ^ 2)) :=
    Differentiable.sqrt ((hdiff.pow 2).const_add 1) (fun t => by positivity)
  have hudiff : Differentiable ℝ u :=
    Differentiable.div hdiff hsq (fun t => (hpos t).ne')
  have huper : Function.Periodic u L := by
    intro t; simp only [hu, hper t]
  have hunn : ∀ t, 0 ≤ u t := fun t => div_nonneg (hnn t) (hpos t).le
  have hzero : ∀ t, u t = 0 ↔ k t = 0 := by
    intro t
    constructor
    · intro h
      have := (div_eq_zero_iff.mp h)
      rcases this with h | h
      · exact h
      · exact absurd h (hpos t).ne'
    · intro h; simp [hu, h]
  intro x
  rcases lt_or_eq_of_le (hnn x) with h | h
  · exact h
  · exfalso
    obtain ⟨x₁, hx₁⟩ := hne
    have hux : u x = 0 := (hzero x).mpr h.symm
    have := eq_zero_of_deriv_add_self_nonneg hL huper hudiff hunn hK hux x₁
    exact hx₁ ((hzero x₁).mp this)

end UnitTangent
