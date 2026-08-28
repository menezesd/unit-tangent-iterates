import UnitTangentIterates.SelectedChangeOfVariable
import UnitTangentIterates.RearOwnHigherRegularity

/-!
# Spatial derivative of the time derivative of inverse rear arclength
-/

noncomputable section

open Function

namespace RearArclengthInverseTimeSpatial

open RearTrack RearOwnHigherRegularity SelectedChangeOfVariable

variable {delta deltaT sf K KT : ℝ → ℝ → ℝ}

def arclengthTime (delta deltaT : ℝ → ℝ → ℝ) (t s : ℝ) : ℝ :=
  ∫ u in (0 : ℝ)..s, cosTimeDeriv delta deltaT t u

def sfTimeFormula (delta deltaT sf : ℝ → ℝ → ℝ) (t x : ℝ) : ℝ :=
  -arclengthTime delta deltaT t (sf t x) /
    Real.cos (delta t (sf t x))

def sfTimeSpatial (delta deltaT sf K : ℝ → ℝ → ℝ) (t x : ℝ) : ℝ :=
  let s := sf t x
  let c := Real.cos (delta t s)
  let ds := K t s - Real.sin (delta t s)
  let At := arclengthTime delta deltaT t s
  let Ats := cosTimeDeriv delta deltaT t s
  let sx := 1 / c
  let Atx := Ats * sx
  let cx := (-Real.sin (delta t s) * ds) * sx
  ((-Atx) * c - (-At) * cx) / c ^ 2

/-- Chain rule for a jointly differentiable two-variable function, expressed
through the canonical partial derivatives. -/
theorem hasDerivAt_comp_partials {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f : ℝ → ℝ → E} {g : ℝ → ℝ} {gd t : ℝ}
    (hf : Differentiable ℝ (uncurry f)) (hg : HasDerivAt g gd t) :
    HasDerivAt (fun r ↦ f r (g r))
      (partialTime f t (g t) + gd • partialArc f t (g t)) t := by
  have h1 : HasFDerivAt (uncurry f) (fderiv ℝ (uncurry f) (t, g t)) (t, g t) :=
    (hf (t, g t)).hasFDerivAt
  have hc : HasDerivAt (fun r : ℝ ↦ ((r, g r) : ℝ × ℝ))
      ((1, gd) : ℝ × ℝ) t := by
    simpa using ((hasDerivAt_id t).prodMk hg)
  have h2 := h1.comp_hasDerivAt t hc
  have hsplit : ((1, gd) : ℝ × ℝ) =
      ((1, 0) : ℝ × ℝ) + gd • ((0, 1) : ℝ × ℝ) := by
    ext <;> simp
  have hval : fderiv ℝ (uncurry f) (t, g t) ((1, gd) : ℝ × ℝ) =
      partialTime f t (g t) + gd • partialArc f t (g t) := by
    rw [hsplit, map_add, map_smul]
    rfl
  rw [hval] at h2
  exact h2

theorem partialTime_sf_eq_formula
    (hdeltaC : ContDiff ℝ 1 (uncurry delta))
    (hsfC : ContDiff ℝ 1 (uncurry sf))
    (hdeltaT : ∀ t s, HasDerivAt (fun r ↦ delta r s) (deltaT t s) t)
    (hdeltaTC : Continuous (uncurry deltaT))
    (hinv : ∀ t x, rearArclength (delta t) (sf t x) = x)
    (hcos : ∀ t s, Real.cos (delta t s) ≠ 0) (t x : ℝ) :
    partialTime sf t x = sfTimeFormula delta deltaT sf t x := by
  let A : ℝ → ℝ → ℝ := fun a s ↦ rearArclength (delta a) s
  have hAC : ContDiff ℝ 1 (uncurry A) :=
    contDiff_one_rearArclengthFamily hdeltaC.continuous hdeltaT hdeltaTC
  have hsft : HasDerivAt (fun r ↦ sf r x) (partialTime sf t x) t :=
    hasDerivAt_partialTime (hsfC.differentiable (by norm_num)) t x
  have hcomp := hasDerivAt_comp_partials
    (hAC.differentiable (by norm_num)) hsft
  have hconst : HasDerivAt (fun _r : ℝ ↦ x) 0 t := hasDerivAt_const t x
  have hfun : (fun r ↦ A r (sf r x)) = fun _r : ℝ ↦ x := by
    funext r
    exact hinv r x
  rw [hfun] at hcomp
  have hsum : partialTime A t (sf t x) +
      partialTime sf t x * partialArc A t (sf t x) = 0 := by
    simpa [smul_eq_mul] using hcomp.unique hconst
  have hAt : partialTime A t (sf t x) =
      arclengthTime delta deltaT t (sf t x) :=
    (hasDerivAt_partialTime (hAC.differentiable (by norm_num)) t (sf t x)).unique
      (hasDerivAt_rearArclength_time hdeltaC.continuous hdeltaT hdeltaTC t (sf t x))
  have hAs : partialArc A t (sf t x) = Real.cos (delta t (sf t x)) :=
    (hasDerivAt_partialArc (hAC.differentiable (by norm_num)) t (sf t x)).unique
      (hasDerivAt_rearArclength_space hdeltaC.continuous t (sf t x))
  rw [hAt, hAs] at hsum
  rw [sfTimeFormula]
  apply (eq_div_iff (hcos t (sf t x))).2
  linarith

/-- The time derivative of the inverse rear arclength has an explicit spatial
derivative under only joint `C^1` regularity and the steering ODE. -/
theorem hasDerivAt_partialTime_sf
    (hdeltaC : ContDiff ℝ 1 (uncurry delta))
    (hsfC : ContDiff ℝ 1 (uncurry sf))
    (hdeltaT : ∀ t s, HasDerivAt (fun r ↦ delta r s) (deltaT t s) t)
    (hdeltaTC : Continuous (uncurry deltaT))
    (hsteer : ∀ t s, HasDerivAt (delta t)
      (K t s - Real.sin (delta t s)) s)
    (hsfS : ∀ t x, HasDerivAt (sf t)
      (1 / Real.cos (delta t (sf t x))) x)
    (hinv : ∀ t x, rearArclength (delta t) (sf t x) = x)
    (hcos : ∀ t s, Real.cos (delta t s) ≠ 0) (t x : ℝ) :
    HasDerivAt (partialTime sf t) (sfTimeSpatial delta deltaT sf K t x) x := by
  have heq : partialTime sf t = sfTimeFormula delta deltaT sf t := by
    funext y
    exact partialTime_sf_eq_formula hdeltaC hsfC hdeltaT hdeltaTC hinv hcos t y
  rw [heq]
  let At : ℝ → ℝ := fun y ↦ arclengthTime delta deltaT t y
  have hAt : HasDerivAt At (cosTimeDeriv delta deltaT t (sf t x)) (sf t x) := by
    exact intervalIntegral.integral_hasDerivAt_right
      ((continuous_cosTimeDeriv hdeltaC.continuous hdeltaTC).comp
        (continuous_const.prodMk continuous_id) |>.intervalIntegrable 0 (sf t x))
      (((continuous_cosTimeDeriv hdeltaC.continuous hdeltaTC).comp
        (continuous_const.prodMk continuous_id)).stronglyMeasurableAtFilter _ _)
      ((continuous_cosTimeDeriv hdeltaC.continuous hdeltaTC).comp
        (continuous_const.prodMk continuous_id)).continuousAt
  have hAtcomp := hAt.comp x (hsfS t x)
  have hdcomp := (hsteer t (sf t x)).comp x (hsfS t x)
  have hccomp := hdcomp.cos
  have hquot := hAtcomp.neg.div hccomp (hcos t (sf t x))
  change HasDerivAt
    (fun y ↦ -At (sf t y) / Real.cos (delta t (sf t y)))
    (sfTimeSpatial delta deltaT sf K t x) x
  apply hquot.congr_deriv
  simp [sfTimeSpatial, At, Function.comp_def]
  ring

end RearArclengthInverseTimeSpatial
