import Mathlib

/-!
# Normal gauge and invariance of the path functionals

This file formalizes two soft steps of the shadowing section of the paper
*A Noncircular Oval with Convex Unit-Tangent Iterates*.

* *Reduction to normal gauge* (in the proof of the lemma *Completeness of
  summable normal paths*).  If the velocity of a path of curves is
  `X_t = ξ τ + η ν` and `X_u = g τ` with `g ≠ 0`, then reparametrizing by the
  flow `φ_t = -ξ/g` produces a path whose velocity is exactly `η ν`: the
  tangential component only moves the parameter.  This is
  `hasDerivAt_normalGauge`, a chain-rule identity for the composite
  `t ↦ X(t, φ(t))`.

* *Invariance of the path functionals under a constant arclength shift* (the
  lemma *Compatible markings*).  A constant shift of the arclength parameter
  changes neither the `L¹` norm of the normal velocity over one period nor its
  supremum, hence changes neither `W` nor the `S_j`; and the functionals are
  additive under concatenation of paths.

Main results:

* `hasDerivAt_normalGauge` : the reparametrization to normal gauge;
* `integral_abs_shift`, `iSup_abs_shift` : invariance of the `L¹`-over-a-period
  and sup norms under a constant arclength shift;
* `pathFunctional_concat` : additivity of `∫ ‖·‖ dt` under concatenation.
-/

noncomputable section

open MeasureTheory

namespace NormalGauge

/-! ### Reduction to normal gauge -/

/-- **Reduction to normal gauge.**  Let `X` be a path of curves, differentiable
in `(t, u)` with `X_t = ξ τ + η ν` and `X_u = g τ`, `g ≠ 0`.  If `φ` solves
`φ_t = -ξ/g`, the reparametrized path `t ↦ X(t, φ(t))` has velocity `η ν`: the
tangential component of the velocity has been absorbed into the
parametrization. -/
theorem hasDerivAt_normalGauge {F : ℝ × ℝ → ℂ} {L : ℝ × ℝ →L[ℝ] ℂ} {phi : ℝ → ℝ}
    {t xi eta g : ℝ} {tau nu : ℂ}
    (hF : HasFDerivAt F L (t, phi t))
    (hphi : HasDerivAt phi (-(xi / g)) t)
    (hLt : L (1, 0) = (xi : ℂ) * tau + (eta : ℂ) * nu)
    (hLu : L (0, 1) = (g : ℂ) * tau) (hg : g ≠ 0) :
    HasDerivAt (fun r => F (r, phi r)) ((eta : ℂ) * nu) t := by
  have hg' : (g : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hg
  have hc : HasDerivAt (fun r => (r, phi r)) ((1 : ℝ), -(xi / g)) t :=
    (hasDerivAt_id t).prodMk hphi
  have hcomp := hF.comp_hasDerivAt t hc
  have hsplit : ((1 : ℝ), -(xi / g)) = ((1:ℝ), (0:ℝ)) + (-(xi / g)) • ((0:ℝ), (1:ℝ)) := by
    simp
  have hL : L ((1 : ℝ), -(xi / g)) = (eta : ℂ) * nu := by
    rw [hsplit, map_add, map_smul, hLt, hLu, Complex.real_smul]
    push_cast
    field_simp
    ring
  rwa [hL] at hcomp

/-! ### Invariance of the path functionals under an arclength shift -/

/-- A constant shift of the arclength parameter does not change the `L¹` norm
of the normal velocity over one period. -/
theorem integral_abs_shift {eta : ℝ → ℝ} {P a : ℝ} (hper : Function.Periodic eta P) :
    (∫ s in (0:ℝ)..P, |eta (s + a)|) = ∫ s in (0:ℝ)..P, |eta s| := by
  have hper' : Function.Periodic (fun s => |eta s|) P := fun s => by
    simp [hper s]
  have hshift : (∫ s in (0:ℝ)..P, |eta (s + a)|) = ∫ s in a..(P + a), |eta s| := by
    have := intervalIntegral.integral_comp_add_right (a := (0:ℝ)) (b := P)
      (f := fun s => |eta s|) a
    simpa using this
  rw [hshift, show P + a = a + P by ring]
  simpa using hper'.intervalIntegral_add_eq a 0

/-- A constant shift of the arclength parameter does not change the supremum of
the normal velocity, hence changes none of the quantities `S_j`. -/
theorem iSup_abs_shift {eta : ℝ → ℝ} (a : ℝ) :
    ⨆ s : ℝ, |eta (s + a)| = ⨆ s : ℝ, |eta s| := by
  have hrange : Set.range (fun s : ℝ => |eta (s + a)|) = Set.range (fun s : ℝ => |eta s|) := by
    ext y
    constructor
    · rintro ⟨s, rfl⟩
      exact ⟨s + a, rfl⟩
    · rintro ⟨s, rfl⟩
      exact ⟨s - a, by simp⟩
  simp only [iSup, hrange]

/-- **Additivity under concatenation.**  The path functionals `W` and `S_j`
are integrals in the path parameter, hence additive when two paths are
concatenated. -/
theorem pathFunctional_concat {nrm : ℝ → ℝ} {a b c : ℝ} (h : Continuous nrm) :
    (∫ t in a..b, nrm t) + (∫ t in b..c, nrm t) = ∫ t in a..c, nrm t :=
  intervalIntegral.integral_add_adjacent_intervals (h.intervalIntegrable _ _)
    (h.intervalIntegrable _ _)

end NormalGauge
