import Mathlib

/-!
# The normal-flow identities

This file formalizes the differential identities

```
  τ_t = η_s ν,      κ_t = η_ss + κ² η,      (log g)_t = -κ η
```

used in the lemma *Completeness of summable normal paths* of the paper
*A Noncircular Oval with Convex Unit-Tangent Iterates*.

A path of plane curves is written in a fixed periodic parameter `u` as
`X : ℝ → ℝ → ℂ`, `(t, u) ↦ X t u`, with

```
  X_u = g · τ,      τ = e^{iθ},      ν = i e^{iθ},      κ = θ_u / g ,
```

and it is in *normal gauge* when `X_t = η ν`.  All the identities come from
the equality of the mixed partial derivatives of `X`, which is the hypothesis
`hmix` below: it says that `∂_t (g τ) = ∂_u (η ν)`.  Splitting that single
complex identity into its real and imaginary parts is
`normal_flow_split`, and everything else follows from it.

Main results:

* `normal_flow_split` : `g_t = -η θ_u` and `g θ_t = η_u`;
* `log_speed_deriv` : `(log g)_t = -κ η`;
* `tangent_deriv` : `τ_t = η_s ν`;
* `curvature_deriv` : `κ_t = η_ss + κ² η`.
-/

noncomputable section

open Complex

namespace NormalFlow

variable {g θ η : ℝ → ℝ → ℝ} {t u gt thetat etau thetau : ℝ}

/-- The speed vector `X_u = g e^{iθ}`. -/
def speedVector (g θ : ℝ → ℝ → ℝ) (t u : ℝ) : ℂ := (g t u : ℂ) * Complex.exp (Complex.I * θ t u)

/-- The normal velocity `X_t = η · i e^{iθ}`. -/
def normalVelocity (η θ : ℝ → ℝ → ℝ) (t u : ℝ) : ℂ :=
  (η t u : ℂ) * (Complex.I * Complex.exp (Complex.I * θ t u))

lemma hasDerivAt_speedVector_t (hg : HasDerivAt (fun r => g r u) gt t)
    (hθt : HasDerivAt (fun r => θ r u) thetat t) :
    HasDerivAt (fun r => speedVector g θ r u)
      (((gt : ℂ) + (g t u : ℂ) * (Complex.I * thetat)) *
        Complex.exp (Complex.I * θ t u)) t := by
  have h1 : HasDerivAt (fun r => ((g r u : ℝ) : ℂ)) ((gt : ℂ)) t :=
    (Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt t hg)
  have h2 : HasDerivAt (fun r => Complex.I * ((θ r u : ℝ) : ℂ)) (Complex.I * thetat) t := by
    exact (Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt t hθt).const_mul Complex.I
  have h3 := h1.mul h2.cexp
  simp only [speedVector]
  convert h3 using 1
  ring

lemma hasDerivAt_normalVelocity_u (hη : HasDerivAt (fun v => η t v) etau u)
    (hθu : HasDerivAt (fun v => θ t v) thetau u) :
    HasDerivAt (fun v => normalVelocity η θ t v)
      (((Complex.I * etau) - (η t u : ℂ) * thetau) * Complex.exp (Complex.I * θ t u)) u := by
  have h1 : HasDerivAt (fun v => ((η t v : ℝ) : ℂ)) ((etau : ℂ)) u :=
    (Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt u hη)
  have h2 : HasDerivAt (fun v => Complex.I * ((θ t v : ℝ) : ℂ)) (Complex.I * thetau) u := by
    exact (Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt u hθu).const_mul Complex.I
  have h3 := h1.mul (h2.cexp.const_mul Complex.I)
  simp only [normalVelocity]
  convert h3 using 1
  have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
  ring_nf
  rw [Complex.I_sq]
  ring

/-- **The normal-flow identities, split form.**  In normal gauge, equality of
the mixed partial derivatives of `X` gives `g_t = -η θ_u` (the speed equation)
and `g θ_t = η_u` (the tangent equation). -/
theorem normal_flow_split (hg : HasDerivAt (fun r => g r u) gt t)
    (hθt : HasDerivAt (fun r => θ r u) thetat t)
    (hη : HasDerivAt (fun v => η t v) etau u)
    (hθu : HasDerivAt (fun v => θ t v) thetau u)
    (hmix : deriv (fun r => speedVector g θ r u) t
      = deriv (fun v => normalVelocity η θ t v) u) :
    gt = -(η t u * thetau) ∧ g t u * thetat = etau := by
  rw [(hasDerivAt_speedVector_t hg hθt).deriv,
    (hasDerivAt_normalVelocity_u hη hθu).deriv] at hmix
  have hexp : Complex.exp (Complex.I * θ t u) ≠ 0 := Complex.exp_ne_zero _
  have hcancel : ((gt : ℂ) + (g t u : ℂ) * (Complex.I * thetat))
      = ((Complex.I * etau) - (η t u : ℂ) * thetau) :=
    mul_right_cancel₀ hexp hmix
  have hre := congrArg Complex.re hcancel
  have him := congrArg Complex.im hcancel
  simp [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im] at hre him
  constructor
  · linarith [hre]
  · linarith [him]

/-- **The speed equation** `(log g)_t = -κ η`, with `κ = θ_u / g`. -/
theorem log_speed_deriv (hgpos : 0 < g t u)
    (hg : HasDerivAt (fun r => g r u) gt t)
    (hgt : gt = -(η t u * thetau)) :
    HasDerivAt (fun r => Real.log (g r u)) (-(thetau / g t u * η t u)) t := by
  have h := hg.log (ne_of_gt hgpos)
  rw [hgt] at h
  convert h using 1
  field_simp

/-- **The tangent equation** `τ_t = η_s ν`, where `η_s = η_u / g` is the
derivative of `η` with respect to arclength. -/
theorem tangent_deriv (hgpos : 0 < g t u)
    (hθt : HasDerivAt (fun r => θ r u) thetat t)
    (hthetat : g t u * thetat = etau) :
    HasDerivAt (fun r => Complex.exp (Complex.I * θ r u))
      ((etau / g t u : ℝ) * (Complex.I * Complex.exp (Complex.I * θ t u))) t := by
  have h2 : HasDerivAt (fun r => Complex.I * ((θ r u : ℝ) : ℂ)) (Complex.I * thetat) t :=
    (Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt t hθt).const_mul Complex.I
  have h3 := h2.cexp
  convert h3 using 1
  have : thetat = etau / g t u := by
    rw [eq_div_iff (ne_of_gt hgpos), mul_comm]
    exact hthetat
  rw [this]
  push_cast
  ring

/-- **The curvature equation** `κ_t = η_ss + κ² η` for the curvature
`κ = θ_u / g`.  The hypothesis `hthetau` is the mixed partial
`θ_{ut} = ∂_u (η_u/g) · g = g η_ss` obtained from the tangent equation, and
`hg` is the speed equation. -/
theorem curvature_deriv {thetauF gF : ℝ → ℝ} {etass : ℝ} (hgpos : 0 < gF t)
    (hthetau : HasDerivAt thetauF (gF t * etass) t)
    (hg : HasDerivAt gF (-(η t u * thetauF t)) t) :
    HasDerivAt (fun r => thetauF r / gF r)
      (etass + (thetauF t / gF t) ^ 2 * η t u) t := by
  have h := hthetau.div hg (ne_of_gt hgpos)
  convert h using 1
  field_simp
  ring



/-! ### The first variation of length -/

section Perimeter

open MeasureTheory intervalIntegral

/-- **Pointwise first variation of the length element.**  With `θ_u = κ g` the
speed equation `g_t = -η θ_u` gives `|g_t| ≤ κ̂ |η| g` whenever `|κ| ≤ κ̂`. -/
theorem abs_speed_deriv_le {kappa khat gv etav gtv thetauv : ℝ} (hg : 0 < gv)
    (hthetau : thetauv = kappa * gv) (hgt : gtv = -(etav * thetauv))
    (hk : |kappa| ≤ khat) :
    |gtv| ≤ khat * |etav| * gv := by
  rw [hgt, hthetau, abs_neg, abs_mul, abs_mul, abs_of_pos hg]
  have h1 : |etav| * |kappa| ≤ |etav| * khat :=
    mul_le_mul_of_nonneg_left hk (abs_nonneg _)
  nlinarith [abs_nonneg etav, abs_nonneg kappa]

/-- **The absolute first-variation estimate for the perimeter along a normal
path.**  If the perimeter has derivative `P'` along the path and
`|P'(t)| ≤ κ̂ ‖η_t‖_{L¹}` at every time, then the total change of perimeter is
at most `κ̂ W`, where `W = ∫₀¹ ‖η_t‖_{L¹} dt`. -/
theorem perimeter_variation_bound {Per Pd nrm : ℝ → ℝ} {khat : ℝ}
    (hPer : ∀ t ∈ Set.uIcc (0:ℝ) 1, HasDerivAt Per (Pd t) t)
    (hPd : Continuous Pd) (hnrm : Continuous nrm)
    (hbound : ∀ t, |Pd t| ≤ khat * nrm t) :
    |Per 1 - Per 0| ≤ khat * ∫ t in (0:ℝ)..1, nrm t := by
  have hFTC : (∫ t in (0:ℝ)..1, Pd t) = Per 1 - Per 0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt hPer (hPd.intervalIntegrable _ _)
  rw [← hFTC]
  calc |∫ t in (0:ℝ)..1, Pd t| ≤ ∫ t in (0:ℝ)..1, |Pd t| :=
        intervalIntegral.abs_integral_le_integral_abs zero_le_one
    _ ≤ ∫ t in (0:ℝ)..1, khat * nrm t := by
        refine intervalIntegral.integral_mono_on zero_le_one
          (hPd.abs.intervalIntegrable _ _)
          ((continuous_const.mul hnrm).intervalIntegrable _ _) (fun t _ => hbound t)
    _ = khat * ∫ t in (0:ℝ)..1, nrm t := by
        rw [intervalIntegral.integral_const_mul]

end Perimeter

end NormalFlow
