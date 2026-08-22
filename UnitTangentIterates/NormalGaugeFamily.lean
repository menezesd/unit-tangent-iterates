import Mathlib
import UnitTangentIterates.NormalGaugeFrame

/-!
# The whole family in normal gauge

`UnitTangentIterates/NormalGaugeFrame.lean` produces, for one initial point, a flow
`φ' = -ξ/v` along which the family `a ↦ R(a, φ(a))` moves with a purely normal
velocity.  The path functionals of `PathMetric.lean` are computed for a whole
*family* of such flows, one for each value of the normalized parameter
`u ∈ [0,1]`, started from the arclength points `ℓ·u` of the reference slice.

This file assembles that family and records the two facts about it that the
comparison of the functionals needs:

* the flows never meet, and each `Φ t` is a strictly increasing
  reparametrization of the line (`strictMono`), so the moving curve
  `u ↦ R(t, Φ t u)` really is a reparametrization of the rear at time `t`;
* the two-sided Grönwall bound
  `ℓ|u−u'|e^{−K|t|} ≤ |Φ t u − Φ t u'| ≤ ℓ|u−u'|e^{K|t|}`,
  which controls the distortion of the parameter along the path.

Main results:

* `dist_ge_of_global_solutions` — the lower Grönwall bound for two solutions of
  the same globally Lipschitz field;
* `exists_normalGauge_family` — the family of gauge flows, its normal motion,
  its two-sided distortion bound and its strict monotonicity.
-/

noncomputable section

open Real Complex

namespace NormalGaugeFamily

/-- **The lower Grönwall bound.**  Two global solutions of the same globally
Lipschitz field cannot approach each other faster than exponentially:
`dist (α₁ t) (α₂ t) ≥ dist (α₁ t₀) (α₂ t₀) · e^{-K|t - t₀|}`. -/
theorem dist_ge_of_global_solutions {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {K : NNReal} {f : ℝ → E → E} {α₁ α₂ : ℝ → E}
    (hlip : ∀ t, LipschitzWith K (f t))
    (h₁ : ∀ t, HasDerivAt α₁ (f t (α₁ t)) t) (h₂ : ∀ t, HasDerivAt α₂ (f t (α₂ t)) t)
    (t₀ t : ℝ) :
    dist (α₁ t₀) (α₂ t₀) * Real.exp (-(K * |t - t₀|)) ≤ dist (α₁ t) (α₂ t) := by
  have h := GlobalODE.dist_le_of_global_solutions (K := K) hlip h₁ h₂ t t₀
  have habs : |t₀ - t| = |t - t₀| := abs_sub_comm t₀ t
  rw [habs] at h
  have hexp : 0 < Real.exp ((K : ℝ) * |t - t₀|) := Real.exp_pos _
  have := (div_le_iff₀ hexp).mpr h
  calc dist (α₁ t₀) (α₂ t₀) * Real.exp (-((K : ℝ) * |t - t₀|))
      = dist (α₁ t₀) (α₂ t₀) / Real.exp ((K : ℝ) * |t - t₀|) := by
        rw [Real.exp_neg]; field_simp
    _ ≤ dist (α₁ t) (α₂ t) := this

/-- **The family of gauge flows.**  With the frame data of
`NormalGaugeFrame.lean` and a tangential rate `-ξ/v` bounded and globally
Lipschitz in the state, there is a family `Φ` of flows, one for each value of
the normalized parameter, starting from the arclength points `ℓ·u` of the
reference slice, such that

* `u ↦ R(t, Φ t u)` moves with the purely normal velocity `η ν` at every time;
* `ℓ|u−u'|e^{−K|t|} ≤ |Φ t u − Φ t u'| ≤ ℓ|u−u'|e^{K|t|}`;
* every `Φ t` is strictly increasing.
-/
theorem exists_normalGauge_family {R : ℝ → ℝ → ℂ} {v xi eta psi : ℝ → ℝ → ℝ}
    {K L : NNReal} {ell : ℝ} (hell : 0 < ell)
    (hR : ContDiff ℝ 1 (Function.uncurry R))
    (hx : ∀ a x, HasDerivAt (fun x' => R a x')
      ((v a x : ℂ) * Complex.exp (Complex.I * (psi a x : ℂ))) x)
    (ha : ∀ a x, HasDerivAt (fun a' => R a' x)
      (((xi a x : ℂ) + Complex.I * (eta a x : ℂ))
        * Complex.exp (Complex.I * (psi a x : ℂ))) a)
    (hvne : ∀ a x, v a x ≠ 0)
    (hlip : ∀ a, LipschitzWith K (fun x => -(xi a x / v a x)))
    (hcont : ∀ x, Continuous fun a => -(xi a x / v a x))
    (hbd : ∀ a x, |(-(xi a x / v a x))| ≤ (L : ℝ)) :
    ∃ Phi : ℝ → ℝ → ℝ,
      (∀ u, Phi 0 u = ell * u) ∧
      (∀ t u, HasDerivAt (fun r => R r (Phi r u))
        ((eta t (Phi t u) : ℂ)
          * NormalGaugeFrame.frameNormalVector (psi t (Phi t u))) t) ∧
      (∀ t u u', |Phi t u - Phi t u'| ≤ ell * |u - u'| * Real.exp ((K : ℝ) * |t|)) ∧
      (∀ t u u', ell * |u - u'| * Real.exp (-((K : ℝ) * |t|)) ≤ |Phi t u - Phi t u'|) ∧
      (∀ t, StrictMono (Phi t)) := by
  -- one flow for each value of the normalized parameter
  have hex : ∀ u : ℝ, ∃ φ : ℝ → ℝ, φ 0 = ell * u ∧
      ∀ t, HasDerivAt φ (-(xi t (φ t) / v t (φ t))) t := fun u =>
    GlobalODE.exists_global_solution_real (h := fun a x => -(xi a x / v a x))
      hlip hcont hbd 0 (ell * u)
  choose flow hflow0 hflowd using hex
  set Phi : ℝ → ℝ → ℝ := fun t u => flow u t with hPhi
  -- the two Grönwall bounds
  have hdist : ∀ t u u', |Phi t u - Phi t u'| ≤ ell * |u - u'| * Real.exp ((K : ℝ) * |t|) := by
    intro t u u'
    have h := GlobalODE.dist_le_of_global_solutions (K := K)
      (f := fun a x => -(xi a x / v a x)) hlip (hflowd u) (hflowd u') 0 t
    simp only [Real.dist_eq, sub_zero, hflow0] at h
    have hEq : |ell * u - ell * u'| = ell * |u - u'| := by
      rw [← mul_sub, abs_mul, abs_of_pos hell]
    rw [hEq] at h
    exact h
  have hdist' : ∀ t u u',
      ell * |u - u'| * Real.exp (-((K : ℝ) * |t|)) ≤ |Phi t u - Phi t u'| := by
    intro t u u'
    have h := dist_ge_of_global_solutions (K := K)
      (f := fun a x => -(xi a x / v a x)) hlip (hflowd u) (hflowd u') 0 t
    simp only [Real.dist_eq, sub_zero, hflow0] at h
    have hEq : |ell * u - ell * u'| = ell * |u - u'| := by
      rw [← mul_sub, abs_mul, abs_of_pos hell]
    rw [hEq] at h
    exact h
  -- the flows never meet, so each slice is a strictly increasing reparametrization
  have hmono : ∀ t, StrictMono (Phi t) := by
    intro t u u' huu
    -- the difference is continuous in the time and never vanishes
    have hne : ∀ r : ℝ, Phi r u' - Phi r u ≠ 0 := by
      intro r hzero
      have h := hdist' r u' u
      rw [show Phi r u' - Phi r u = 0 from hzero] at h
      simp only [abs_zero] at h
      have hpos : 0 < ell * |u' - u| * Real.exp (-((K : ℝ) * |r|)) :=
        mul_pos (mul_pos hell (abs_pos.mpr (sub_ne_zero.mpr (ne_of_gt huu)))) (Real.exp_pos _)
      linarith
    have hcontd : Continuous fun r => Phi r u' - Phi r u := by
      have hd1 : Differentiable ℝ (flow u') := fun r => (hflowd u' r).differentiableAt
      have hd2 : Differentiable ℝ (flow u) := fun r => (hflowd u r).differentiableAt
      have h1 : Continuous (flow u') := hd1.continuous
      have h2 : Continuous (flow u) := hd2.continuous
      exact h1.sub h2
    have hzero : Phi 0 u' - Phi 0 u > 0 := by
      simp only [hPhi, hflow0]
      have : ell * u < ell * u' := by nlinarith
      linarith
    -- a continuous nonvanishing function keeping the sign of its value at `0`
    have hsign : 0 < Phi t u' - Phi t u := by
      by_contra hle
      push_neg at hle
      have hlt : Phi t u' - Phi t u < 0 := lt_of_le_of_ne hle (hne t)
      have hmem : (0 : ℝ) ∈ Set.uIcc (Phi 0 u' - Phi 0 u) (Phi t u' - Phi t u) := by
        rw [Set.mem_uIcc]
        exact Or.inr ⟨hlt.le, hzero.le⟩
      obtain ⟨c, -, hc⟩ := intermediate_value_uIcc (a := (0:ℝ)) (b := t)
        (f := fun r => Phi r u' - Phi r u) hcontd.continuousOn hmem
      exact hne c hc
    linarith
  refine ⟨Phi, fun u => hflow0 u, ?_, hdist, hdist', hmono⟩
  intro t u
  exact NormalGaugeFrame.hasDerivAt_normalGauge_of_frame (a0 := t) hR hx ha
    (hvne t (Phi t u)) (hflowd u t)

end NormalGaugeFamily
