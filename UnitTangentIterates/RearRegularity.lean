import Mathlib

/-!
# The regularity gain of the selected inverse

The lemmas *Inverse Jacobi estimates* and *Selected inverse on the closed
strip* of the paper *A Noncircular Oval with Convex Unit-Tangent Iterates* end
with a regularity assertion: the selected inverse gains one derivative, a `Cʳ`
front (`r ≥ 2`) having a `C^{r+1}` selected rear.  The paper's derivative count
is:

* the front tangent angle `Θ` of a `Cʳ` front is `C^{r-1}`;
* the rear tangent angle in front arclength satisfies `Ψ_s = sin(Θ - Ψ)`, and
  the equation bootstraps `Ψ` to `Cʳ`;
* one integration in arclength, `X(x) = ∫₀ˣ e^{iΨ}`, gives a `C^{r+1}` rear
  curve.

This file formalizes the two bootstrap steps.

Main results:

* `contDiff_of_steering` : if `Θ` is `Cⁿ` and `Ψ_s = sin(Θ - Ψ)`, then `Ψ` is
  `C^{n+1}`;
* `contDiff_intervalIntegral` : the primitive of a `Cⁿ` function is `C^{n+1}`;
* `rear_contDiff` : the resulting regularity `C^{n+2}` of the reconstructed
  rear curve `x ↦ ∫₀ˣ e^{iΨ}` (with `n = r - 1` this is the asserted gain).
-/

noncomputable section

open Real

namespace RearRegularity

/-- **The steering equation bootstraps the regularity of the rear tangent
angle.**  If the front tangent angle `Θ` is `Cⁿ` and the rear tangent angle
satisfies `Ψ_s = sin(Θ - Ψ)`, then `Ψ` is `C^{n+1}`. -/
theorem contDiff_of_steering : ∀ (n : ℕ) {Theta Psi : ℝ → ℝ},
    ContDiff ℝ n Theta → (∀ s, HasDerivAt Psi (Real.sin (Theta s - Psi s)) s) →
    ContDiff ℝ (n + 1 : ℕ) Psi := by
  intro n
  induction n with
  | zero =>
    intro Theta Psi hT hP
    have hdiff : Differentiable ℝ Psi := fun s => (hP s).differentiableAt
    have hderiv : deriv Psi = fun s => Real.sin (Theta s - Psi s) := by
      funext s; exact (hP s).deriv
    have hcont : Continuous fun s => Real.sin (Theta s - Psi s) :=
      Real.continuous_sin.comp (hT.continuous.sub hdiff.continuous)
    have key : ContDiff ℝ (((0 : ℕ) : WithTop ℕ∞) + 1) Psi := by
      rw [contDiff_succ_iff_deriv]
      refine ⟨hdiff, by simp, ?_⟩
      rw [hderiv]
      simpa [contDiff_zero] using hcont
    exact_mod_cast key
  | succ n ih =>
    intro Theta Psi hT hP
    have hT' : ContDiff ℝ (n : ℕ) Theta := hT.of_le (by exact_mod_cast Nat.le_succ n)
    have hPsi : ContDiff ℝ (n + 1 : ℕ) Psi := ih hT' hP
    have hderiv : deriv Psi = fun s => Real.sin (Theta s - Psi s) := by
      funext s; exact (hP s).deriv
    have hd : ContDiff ℝ ((n + 1 : ℕ) : WithTop ℕ∞) (deriv Psi) := by
      rw [hderiv]
      exact Real.contDiff_sin.comp (hT.sub hPsi)
    have key : ContDiff ℝ (((n + 1 : ℕ) : WithTop ℕ∞) + 1) Psi := by
      rw [contDiff_succ_iff_deriv]
      exact ⟨fun s => (hP s).differentiableAt, by simp, hd⟩
    exact_mod_cast key

/-- **One integration gains one derivative**: the primitive of a `Cⁿ` function
is `C^{n+1}`. -/
theorem contDiff_intervalIntegral {n : ℕ} {f : ℝ → ℂ} (hf : ContDiff ℝ (n : ℕ) f) :
    ContDiff ℝ ((n : ℕ) + 1 : ℕ) (fun x => ∫ t in (0:ℝ)..x, f t) := by
  have hcont : Continuous f := hf.continuous
  have hderiv : ∀ x, HasDerivAt (fun x => ∫ t in (0:ℝ)..x, f t) (f x) x := fun x =>
    (hcont.integral_hasStrictDerivAt (0:ℝ) x).hasDerivAt
  have hd : deriv (fun x => ∫ t in (0:ℝ)..x, f t) = f := by
    funext x; exact (hderiv x).deriv
  have key : ContDiff ℝ (((n : ℕ) : WithTop ℕ∞) + 1) (fun x => ∫ t in (0:ℝ)..x, f t) := by
    rw [contDiff_succ_iff_deriv]
    exact ⟨fun x => (hderiv x).differentiableAt, by simp, by rw [hd]; exact hf⟩
  exact_mod_cast key

/-- The unit tangent `e^{iΨ}` of a `Cⁿ` tangent angle is `Cⁿ`. -/
theorem contDiff_unitTangent {n : ℕ} {Psi : ℝ → ℝ} (h : ContDiff ℝ (n : ℕ) Psi) :
    ContDiff ℝ (n : ℕ) (fun t => Complex.exp (Psi t * Complex.I)) :=
  Complex.contDiff_exp.comp ((Complex.ofRealCLM.contDiff.comp h).mul contDiff_const)

/-- **The regularity gain of the selected inverse.**  If the front tangent
angle `Θ` is `Cⁿ` (which is the case for a `C^{n+1}` front) and the rear
tangent angle solves `Ψ_s = sin(Θ - Ψ)`, then the reconstructed rear curve
`x ↦ ∫₀ˣ e^{iΨ}` is `C^{n+2}`: one derivative more than the front. -/
theorem rear_contDiff (n : ℕ) {Theta Psi : ℝ → ℝ} (hT : ContDiff ℝ (n : ℕ) Theta)
    (hP : ∀ s, HasDerivAt Psi (Real.sin (Theta s - Psi s)) s) :
    ContDiff ℝ (n + 2 : ℕ) (fun x => ∫ t in (0:ℝ)..x, Complex.exp (Psi t * Complex.I)) := by
  have hPsi : ContDiff ℝ (n + 1 : ℕ) Psi := contDiff_of_steering n hT hP
  have := contDiff_intervalIntegral (n := n + 1) (contDiff_unitTangent hPsi)
  simpa [Nat.add_assoc] using this

end RearRegularity
