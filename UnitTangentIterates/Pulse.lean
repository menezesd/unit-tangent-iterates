module

public import UnitTangentIterates.PulseAbstract

/-!
# Lemma 3.5: the pulse of the translating hairpin

Fix the translating hairpin of Theorem 3.4 with `ε = 1/21`, so that its profile satisfies
`m ≤ f ≤ M` with `m = 21 - 1/21`, `M = 23`, and its curvature `sin θ / f(θ)` is below `1/20`.
Regard it as a rear track, with arclength `x`, tangent angle `ψ(x)` and curvature
`K = sin ψ / f(ψ)`; its unit-tangent image is a translate of it.  In front arclength `s`, the
steering angle `δ(s)` satisfies `tan δ(s) = K(x(s))`, and the pulse is `y = sin δ`.

`pulse_exists` produces `y` with all the properties of Lemma 3.5 that Sections 4–7 use:
`0 < y ≤ A e^{-a|s|}`, `|y'|, |y''| ≤ D y`, `y ≤ b < 1`, `∫ y = π`, `K_* ≥ b₀ y` (where
`K_* = frontCurv y` is the front curvature), the translator identity
`K_*(x(s)) = y(s)/c(s)` with `x(s) = x₀ + ∫₀ˢ c`, and both curvatures `≤ 1/20`.
-/

@[expose] public section

namespace Ovals

open Real Set Filter Topology

/-- **Lemma 3.5 (the pulse of the translating hairpin).** -/
theorem pulse_exists :
    ∃ (y y' y'' : ℝ → ℝ) (A a D b b₀ x₀ : ℝ),
      (∀ t, HasDerivAt y (y' t) t) ∧ (∀ t, HasDerivAt y' (y'' t) t) ∧ (∀ t, 0 < y t) ∧
      (∀ t, y t ≤ A * Real.exp (-(a * |t|))) ∧ 0 < a ∧ (∀ t, |y' t| ≤ D * y t) ∧
      (∀ t, |y'' t| ≤ D * y t) ∧ (∀ t, y t ≤ b) ∧ b < 1 ∧ ∫ t, y t = π ∧ 0 < b₀ ∧
      (∀ t, b₀ * y t ≤ frontCurv y t) ∧
      (∀ s, frontCurv y (x₀ + ∫ r in (0 : ℝ)..s, √(1 - y r ^ 2)) = y s / √(1 - y s ^ 2)) ∧
      (∀ t, frontCurv y t ≤ 1 / 20) ∧ (∀ t, y t / √(1 - y t ^ 2) ≤ 1 / 20) := by
  -- the hairpin profile
  have hε0 : (0 : ℝ) < 1 / 21 := by norm_num
  have hε : (1 : ℝ) / 21 ≤ 1 / 10 := by norm_num
  obtain ⟨f, hfs, hfb, hT, -⟩ := hairpin_exists hε0 hε
  set m : ℝ := (1 / 21 : ℝ)⁻¹ - 1 / 21 with hmdef
  set M : ℝ := (1 / 21 : ℝ)⁻¹ + 2 with hMdef
  have hm1 : 1 < m := one_lt_inv_sub hε0 hε
  have hm0 : 0 < m := by linarith
  have hMm : m ≤ M := by rw [hmdef, hMdef]; norm_num
  have hM0 : 0 < M := by linarith
  have hf : ∀ θ ∈ Ioo 0 π, m ≤ f θ := fun θ hθ => (fMinus_ge hε0 θ).trans (hfb θ hθ).1
  have hfM : ∀ θ ∈ Ioo 0 π, f θ ≤ M := fun θ hθ => (hfb θ hθ).2.trans (fPlus_le hε0 hε θ)
  have hfd : DifferentiableOn ℝ f (Ioo 0 π) := hfs.differentiableOn (by simp)
  have hfc : ContinuousOn f (Ioo 0 π) := hfd.continuousOn
  -- the rear hairpin in arclength
  obtain ⟨ψ, U, hψmem, hψd, hψU, hUd, hψshift, hψdecay, hψbot, hψtop⟩ :=
    exists_rear_angle hm0 hf hfM hfc
  set K : ℝ → ℝ := fun x => Real.sin (ψ x) / f (ψ x) with hKdef
  set G : ℝ → ℝ := fun x => hairpinGd f (ψ x) with hGdef
  set σ : ℝ → ℝ := fun x => U (hairpinG f (ψ x)) with hσdef
  have hsinpos : ∀ x, 0 < Real.sin (ψ x) := fun x =>
    Real.sin_pos_of_pos_of_lt_pi (hψmem x).1 (hψmem x).2
  have hfpos : ∀ x, 0 < f (ψ x) := fun x => by linarith [hf _ (hψmem x)]
  have hKpos : ∀ x, 0 < K x := fun x => div_pos (hsinpos x) (hfpos x)
  have hKle' : ∀ x, K x ≤ Real.sin (ψ x) / m := fun x =>
    div_le_div_of_nonneg_left (hsinpos x).le hm0 (hf _ (hψmem x))
  have hKle : ∀ x, K x ≤ 1 / m := fun x =>
    (hKle' x).trans (div_le_div_of_nonneg_right (Real.sin_le_one _) hm0.le)
  have hκ : 1 / m < 1 := by rw [div_lt_one hm0]; exact hm1
  -- derivative of `K`: `K = tan (d ∘ ψ)`
  have hDd : ∀ x, HasDerivAt (fun x => hairpinD f (ψ x)) ((G x - 1) * K x) x := by
    intro x
    have h := ((hasDerivAt_hairpinG_gd hm1 hf hfd hT (hψmem x)).sub (hasDerivAt_id _)).comp x
      (hψd x)
    convert h using 1
    funext z; simp [hairpinG]
  have hKtan : K = fun x => Real.tan (hairpinD f (ψ x)) := by
    funext x; simp only [hKdef, hairpinD, Real.tan_arctan]
  have hK : ∀ x, HasDerivAt K ((1 + K x ^ 2) * (G x - 1) * K x) x := by
    intro x
    have hc : Real.cos (hairpinD f (ψ x)) ≠ 0 := (Real.cos_arctan_pos _).ne'
    have h := ((Real.hasDerivAt_tan hc).comp x (hDd x)).congr_of_eventuallyEq
      (Eventually.of_forall fun z => congrFun hKtan z)
    convert h using 1
    have e2 : Real.cos (hairpinD f (ψ x)) ^ 2 = 1 / (1 + K x ^ 2) := by
      show Real.cos (Real.arctan (K x)) ^ 2 = _
      rw [Real.cos_arctan, div_pow, Real.sq_sqrt (by positivity), one_pow]
    rw [e2]; field_simp
  -- front arclength `σ`
  have hσ : ∀ x, HasDerivAt σ (√(1 + K x ^ 2)) x := by
    intro x
    have hg := hairpinG_mem_Ioo hm1 hf (hψmem x)
    have h := (hUd _ hg).comp x ((hasDerivAt_hairpinG_gd hm1 hf hfd hT (hψmem x)).comp x
      (hψd x))
    convert h using 1
    exact (front_speed_identity hm1 hf (hψmem x)).symm
  have hσ1 : ∀ x, 1 ≤ √(1 + K x ^ 2) := fun x =>
    Real.one_le_sqrt.2 (by nlinarith [sq_nonneg (K x)])
  obtain ⟨X, hσX, -, hXd⟩ := exists_inverse_of_deriv_ge one_pos hσ hσ1
  have hshift : ∀ x, K (σ x) = K x * G x / √(1 + K x ^ 2) := by
    intro x
    have e : ψ (σ x) = hairpinG f (ψ x) := hψU _ (hairpinG_mem_Ioo hm1 hf (hψmem x))
    simp only [hKdef, hGdef]
    rw [e]
    exact front_curv_identity hm1 hf (hψmem x)
  have hcomp : ∀ x h, K (x + h) ≤ M / m * Real.exp (1 / m * |h|) * K x := by
    intro x h
    have h1 : K (x + h) ≤ Real.sin (ψ (x + h)) / m := hKle' _
    have h2 := hψshift x h
    have h3 : Real.sin (ψ x) / M ≤ K x :=
      div_le_div_of_nonneg_left (hsinpos x).le (hfpos x) (hfM _ (hψmem x))
    have e : Real.exp (1 / m * |h|) = Real.exp (|h| / m) := by ring_nf
    rw [e]
    calc K (x + h) ≤ Real.sin (ψ (x + h)) / m := h1
      _ ≤ Real.exp (|h| / m) * Real.sin (ψ x) / m := by gcongr
      _ = M / m * Real.exp (|h| / m) * (Real.sin (ψ x) / M) := by field_simp
      _ ≤ M / m * Real.exp (|h| / m) * K x := by gcongr
  have hdecay : ∀ x, K x ≤ 2 / m * Real.exp (-(1 / M * |x|)) := by
    intro x
    have e : -(1 / M * |x|) = -(|x| / M) := by ring
    rw [e]
    calc K x ≤ Real.sin (ψ x) / m := hKle' x
      _ ≤ 2 * Real.exp (-(|x| / M)) / m := by gcongr; exact hψdecay x
      _ = 2 / m * Real.exp (-(|x| / M)) := by ring
  have hG : ∀ x, 0 < G x ∧ G x ≤ (M + 1) / m := fun x => hairpinGd_bounds hm1 hf hfM (hψmem x)
  obtain ⟨y, y', y'', A, D, b, b₀, x₀, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13,
    h14⟩ := pulse_of_shift hK (fun x => rfl) hKpos hKle hκ hG hσ hσX hXd hshift hcomp
      (by positivity) hdecay (by positivity) hψd hψbot hψtop
  have hκ20 : 1 / m ≤ 1 / 20 := by rw [hmdef]; norm_num
  exact ⟨y, y', y'', A, 1 / M, D, b, b₀, x₀, h1, h2, h3, h4, by positivity, h5, h6, h7, h8, h9,
    h10, h11, h12, fun t => (h13 t).trans hκ20, fun t => (h14 t).trans hκ20⟩

end Ovals

end
