module

public import UnitTangentIterates.Defs

/-!
# Circles under the unit-tangent transform

The paper's introduction recalls that `𝒯` sends a circle of radius `r` to a circle of
radius `√(r² + 1)`.  We prove this, and deduce that all iterates of a circle are ovals
(circles of radius `√(r² + n)`).  This is the trivial family of examples; the main
theorem of the paper asserts that there are also *noncircular* such ovals.
-/

@[expose] public section

namespace Ovals

open Complex Real
open scoped ContDiff

theorem hasDerivAt_tau_comp {f : ℝ → ℝ} {f' x : ℝ} (hf : HasDerivAt f f' x) :
    HasDerivAt (fun s => tau (f s)) ((f' : ℂ) * I * tau (f x)) x := by
  unfold tau
  have h1 : HasDerivAt (fun s => ((f s : ℂ))) (f' : ℂ) x := hf.ofReal_comp
  have h2 := (h1.mul_const I).cexp
  convert h2 using 1
  ring

theorem norm_tau (ψ : ℝ) : ‖tau ψ‖ = 1 := by
  unfold tau; exact Complex.norm_exp_ofReal_mul_I ψ

theorem tau_ne_zero (ψ : ℝ) : tau ψ ≠ 0 := by
  unfold tau; exact Complex.exp_ne_zero _

theorem conj_tau_mul_tau (ψ : ℝ) : (starRingEnd ℂ) (tau ψ) * tau ψ = 1 := by
  rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, norm_tau]; simp

theorem tau_add (a b : ℝ) : tau (a + b) = tau a * tau b := by
  unfold tau; push_cast; rw [← Complex.exp_add]; ring_nf

theorem tau_eq (ψ : ℝ) : tau ψ = (Real.cos ψ : ℂ) + (Real.sin ψ : ℂ) * I := by
  unfold tau; rw [Complex.exp_mul_I]; simp [← Complex.ofReal_cos, ← Complex.ofReal_sin]

theorem contDiff_tau : ContDiff ℝ ∞ tau := by
  unfold tau
  have : ContDiff ℝ ∞ (fun ψ : ℝ => (ψ : ℂ)) := Complex.ofRealCLM.contDiff
  exact (this.mul contDiff_const).cexp

/-- The circle with center `c`, radius `r`, and phase `φ`, traversed counterclockwise. -/
noncomputable def circ (c : ℂ) (r φ : ℝ) : ℝ → ℂ := fun t => c + (r : ℂ) * tau (t + φ)

theorem hasDerivAt_circ (c : ℂ) (r φ t : ℝ) :
    HasDerivAt (circ c r φ) ((r : ℂ) * I * tau (t + φ)) t := by
  have h := hasDerivAt_tau_comp ((hasDerivAt_id t).add_const φ)
  have := (h.const_mul (r : ℂ)).const_add c
  convert this using 1
  simp; ring

theorem deriv_circ (c : ℂ) (r φ : ℝ) :
    deriv (circ c r φ) = fun t => (r : ℂ) * I * tau (t + φ) :=
  funext fun t => (hasDerivAt_circ c r φ t).deriv

theorem deriv_deriv_circ (c : ℂ) (r φ : ℝ) :
    deriv (deriv (circ c r φ)) = fun t => -(r : ℂ) * tau (t + φ) := by
  rw [deriv_circ]
  funext t
  have h := hasDerivAt_tau_comp ((hasDerivAt_id t).add_const φ)
  have h2 : HasDerivAt (fun t => (r : ℂ) * I * tau (t + φ))
      ((r : ℂ) * I * ((1 : ℝ) * I * tau (t + φ))) t := by
    simpa using h.const_mul ((r : ℂ) * I)
  rw [h2.deriv]
  simp only [Complex.ofReal_one]
  ring_nf
  rw [Complex.I_sq]; ring

theorem norm_deriv_circ (c : ℂ) {r : ℝ} (hr : 0 ≤ r) (φ t : ℝ) :
    ‖deriv (circ c r φ) t‖ = r := by
  rw [deriv_circ]; simp [norm_tau, abs_of_nonneg hr]

/-- `𝒯` maps the circle of radius `r` to the concentric circle of radius `√(r²+1)`. -/
theorem unitTangentTransform_circ (c : ℂ) {r : ℝ} (hr : 0 < r) (φ : ℝ) :
    unitTangentTransform (circ c r φ) = circ c (√(r ^ 2 + 1)) (φ + Real.arctan (1 / r)) := by
  funext t
  have key : (√(r ^ 2 + 1) : ℂ) * tau (Real.arctan (1 / r)) = (r : ℂ) + I := by
    rw [tau_eq, Real.cos_arctan, Real.sin_arctan]
    have h1 : √(1 + (1 / r) ^ 2) = √(r ^ 2 + 1) / r := by
      rw [show (1 : ℝ) + (1 / r) ^ 2 = (r ^ 2 + 1) / r ^ 2 by field_simp,
        Real.sqrt_div' _ (by positivity), Real.sqrt_sq hr.le]
    have h2 : 0 < √(r ^ 2 + 1) := Real.sqrt_pos.2 (by positivity)
    rw [h1]
    have e1 : (1 : ℝ) / (√(r ^ 2 + 1) / r) = r / √(r ^ 2 + 1) := by field_simp
    have e2 : (1 / r) / (√(r ^ 2 + 1) / r) = 1 / √(r ^ 2 + 1) := by field_simp
    rw [e1, e2]
    have hc : (√(r ^ 2 + 1) : ℂ) ≠ 0 := by exact_mod_cast h2.ne'
    push_cast
    field_simp
  unfold unitTangentTransform
  rw [norm_deriv_circ c hr.le, deriv_circ]
  unfold circ
  beta_reduce
  rw [show t + (φ + Real.arctan (1 / r)) = Real.arctan (1 / r) + (t + φ) by ring,
    tau_add (Real.arctan (1 / r)) (t + φ), ← mul_assoc, key]
  have : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  field_simp
  ring

theorem curvature_circ (c : ℂ) {r : ℝ} (hr : 0 < r) (φ t : ℝ) :
    curvature (circ c r φ) t = 1 / r := by
  unfold curvature
  rw [norm_deriv_circ c hr.le, deriv_deriv_circ, deriv_circ]
  have h : (starRingEnd ℂ) ((r : ℂ) * I * tau (t + φ)) * (-(r : ℂ) * tau (t + φ))
      = (r ^ 2 : ℝ) * I := by
    simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
    have := conj_tau_mul_tau (t + φ)
    push_cast
    linear_combination (r : ℂ) ^ 2 * I * this
  rw [h, Complex.mul_I_im, Complex.ofReal_re]
  field_simp

theorem circ_injOn (c : ℂ) {r : ℝ} (hr : 0 < r) (φ : ℝ) :
    Set.InjOn (circ c r φ) (Set.Ico 0 (2 * π)) := by
  intro s hs t ht hst
  unfold circ at hst
  have hr' : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have h1 : tau (s + φ) = tau (t + φ) := by
    have := add_left_cancel hst
    exact mul_left_cancel₀ hr' this
  unfold tau at h1
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.1 h1
  have hn' : s - t = n * (2 * π) := by
    have := congrArg Complex.im hn
    simp at this
    linarith
  have hlt : |s - t| < 2 * π := by
    rw [abs_lt]; constructor <;> linarith [hs.1, hs.2, ht.1, ht.2]
  rw [hn', abs_mul, abs_of_pos (by positivity : (0:ℝ) < 2 * π)] at hlt
  have : |(n : ℝ)| < 1 := by
    have := Real.pi_pos
    nlinarith [abs_nonneg (n : ℝ)]
  have hn0 : n = 0 := by
    have : |n| < 1 := by exact_mod_cast this
    exact Int.abs_lt_one_iff.mp this
  subst hn0
  simp at hn'
  linarith

theorem circ_periodic (c : ℂ) (r φ : ℝ) : Function.Periodic (circ c r φ) (2 * π) := by
  intro t
  unfold circ
  rw [show t + 2 * π + φ = (t + φ) + 2 * π by ring, tau_add]
  unfold tau
  simp

/-- A circle of positive radius is an oval. -/
theorem isOval_circ (c : ℂ) {r : ℝ} (hr : 0 < r) (φ : ℝ) : IsOval (circ c r φ) where
  contDiff := by
    unfold circ
    exact contDiff_const.add (contDiff_const.mul (contDiff_tau.comp
      (contDiff_id.add contDiff_const)))
  regular := fun t => by
    rw [← norm_ne_zero_iff, norm_deriv_circ c hr.le]; exact hr.ne'
  curvature_pos := fun t => by rw [curvature_circ c hr]; positivity
  closed_simple := ⟨2 * π, by positivity, circ_periodic c r φ, circ_injOn c hr φ⟩

/-- The `n`-th unit-tangent iterate of a circle of radius `r` is a concentric circle
of radius `√(r² + n)`. -/
theorem iterate_unitTangentTransform_circ (c : ℂ) {r : ℝ} (hr : 0 < r) (φ : ℝ) (n : ℕ) :
    ∃ φ' : ℝ, unitTangentTransform^[n] (circ c r φ) = circ c (√(r ^ 2 + n)) φ' := by
  induction n with
  | zero => exact ⟨φ, by simp [Real.sqrt_sq hr.le]⟩
  | succ n ih =>
    obtain ⟨φ', h⟩ := ih
    have hpos : 0 < √(r ^ 2 + n) := Real.sqrt_pos.2 (by positivity)
    refine ⟨φ' + Real.arctan (1 / √(r ^ 2 + n)), ?_⟩
    rw [Function.iterate_succ_apply', h, unitTangentTransform_circ c hpos]
    congr 2
    rw [Real.sq_sqrt (by positivity)]
    push_cast; ring_nf

/-- Every unit-tangent iterate of a circle is an oval: circles are the trivial examples. -/
theorem isOval_iterate_circ (c : ℂ) {r : ℝ} (hr : 0 < r) (φ : ℝ) (n : ℕ) :
    IsOval (unitTangentTransform^[n] (circ c r φ)) := by
  obtain ⟨φ', h⟩ := iterate_unitTangentTransform_circ c hr φ n
  rw [h]
  exact isOval_circ c (Real.sqrt_pos.2 (by positivity)) φ'

theorem isCircle_circ (c : ℂ) {r : ℝ} (hr : 0 ≤ r) (φ : ℝ) : IsCircle (circ c r φ) :=
  ⟨c, r, fun t => by simp [circ, norm_tau, abs_of_nonneg hr]⟩

end Ovals

end
