import Mathlib
import UnitTangentIterates.InterpolationFrenetEvolution
import UnitTangentIterates.PathMetricCircle

/-! # Profiling interpolation Frenet data by the stopped clock -/

noncomputable section

open Function Set

namespace InterpolationFrenetProfiled

/-- Raw frame-time and mixed-partial data transport through a differentiable
clock `B` with derivative `w`.  Both sides of the mixed identity acquire the
same scalar factor `w t`. -/
theorem frame_time_block_comp
    {alpha k alphaT kT kX : ℝ → ℝ → ℝ}
    {V : ℝ → ℝ → ℂ} {B w : ℝ → ℝ}
    (hBd : ∀ t, HasDerivAt B (w t) t)
    (hBc : Continuous B) (hwc : Continuous w)
    (halphaT : ∀ a x, HasDerivAt (fun r => alpha r x) (alphaT a x) a)
    (hkT : ∀ a x, HasDerivAt (fun r => k r x) (kT a x) a)
    (halphaTS : ∀ a x, HasDerivAt (alphaT a) (kT a x) x)
    (halphaTc : Continuous (uncurry alphaT))
    (hkTc : Continuous (uncurry kT))
    (hkXc : Continuous (uncurry kX))
    (hmixed : ∀ a x, ∃ W : ℂ,
      HasDerivAt
        (fun r => Complex.exp (Complex.I * (alpha r x : ℂ))) W a ∧
      HasDerivAt (V a) W x) :
    (∀ t x, HasDerivAt (fun r => alpha (B r) x)
      (w t * alphaT (B t) x) t) ∧
    (∀ t x, HasDerivAt (fun r => k (B r) x)
      (w t * kT (B t) x) t) ∧
    (∀ t x, HasDerivAt (fun y => w t * alphaT (B t) y)
      (w t * kT (B t) x) x) ∧
    Continuous (uncurry fun t x => w t * alphaT (B t) x) ∧
    Continuous (uncurry fun t x => w t * kT (B t) x) ∧
    Continuous (uncurry fun t x => kX (B t) x) ∧
    (∀ t x, ∃ W : ℂ,
      HasDerivAt
        (fun r => Complex.exp (Complex.I * (alpha (B r) x : ℂ))) W t ∧
      HasDerivAt (fun y => (w t : ℂ) * V (B t) y) W x) := by
  refine ⟨fun t x => (halphaT (B t) x).scomp t (hBd t),
    fun t x => (hkT (B t) x).scomp t (hBd t), ?_, ?_, ?_, ?_, ?_⟩
  · intro t x
    exact (halphaTS (B t) x).const_mul (w t)
  · exact (hwc.comp continuous_fst).mul
      (halphaTc.comp ((hBc.comp continuous_fst).prodMk continuous_snd))
  · exact (hwc.comp continuous_fst).mul
      (hkTc.comp ((hBc.comp continuous_fst).prodMk continuous_snd))
  · exact hkXc.comp ((hBc.comp continuous_fst).prodMk continuous_snd)
  · intro t x
    obtain ⟨W, hWt, hWx⟩ := hmixed (B t) x
    refine ⟨(w t : ℂ) * W, ?_, ?_⟩
    · simpa [smul_eq_mul] using hWt.scomp t (hBd t)
    · simpa using hWx.const_mul (w t : ℂ)

/-- Constant-period closing data for a profiled family. -/
theorem constant_period_closing
    {k alpha : ℝ → ℝ → ℝ} {B : ℝ → ℝ} {L turn : ℝ}
    (hL : 0 < L)
    (hkper : ∀ a, Periodic (k a) (2 * L))
    (halphaper : ∀ a x, alpha a (x + 2 * L) = alpha a x + turn) :
    (∀ _ : ℝ, 0 < (2 * L : ℝ)) ∧
    (∀ t : ℝ, HasDerivAt (fun _ : ℝ => 2 * L) 0 t) ∧
    (∀ _ _ : ℝ, (0 : ℝ) = 0 + 0) ∧
    (∀ t, Periodic (k (B t)) (2 * L)) ∧
    (∀ t x, alpha (B t) (x + 2 * L) = alpha (B t) x + turn) := by
  exact ⟨fun _ => by linarith, fun t => hasDerivAt_const t (2 * L),
    fun _ _ => by simp, fun t => hkper (B t), fun t => halphaper (B t)⟩

end InterpolationFrenetProfiled
