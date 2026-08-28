import Mathlib
import UnitTangentIterates.InterpolationSmooth
import UnitTangentIterates.SteeringArclengthSmooth
import UnitTangentIterates.RearOwnHigherRegularity

/-!
# Regularity bridge from curvature interpolation to selected rear families

This module packages the qualitative regularity hypotheses used by the
variable-speed normal-gauge shadowing interface.  The endpoint curvatures
produce the explicit interpolated front and tangent angle; the smooth
dependence theorem upgrades the selected steering family; and the global
rear-arclength inverse theorem transfers that regularity to the inverse
change of variables.
-/

noncomputable section

open Function Set Real

namespace InterpolationSelectedRearRegularity

open CurvatureInterpolation InterpolationSmooth SteeringArclengthSmooth
  RearOwnHigherRegularity RearTrack

variable {k0 k1 : ℝ → ℝ} {theta0 L P kap Klip CK : ℝ}
  {delta sf : ℝ → ℝ → ℝ}

/-- **The qualitative selected-rear data of the explicit curvature
interpolation.**

The conclusion simultaneously supplies joint `C⁴` regularity of the front,
its tangent angle, the selected steering angle, and inverse rear arclength,
together with their spatial ODE identities.  These are precisely the
regularity and space-derivative inputs appearing in
`GaugeRearFamilyFromFront.exists_variableSpeed_normalPath_of_rearFamily_from_front`.
The remaining inputs of that theorem are quantitative frame/Jacobi bounds,
period/closing data, and endpoint identifications. -/
theorem interpolation_selectedRear_core_data
    (hk0 : ContDiff ℝ (4 : ℕ) k0) (hk1 : ContDiff ℝ (4 : ℕ) k1)
    (hP : 0 < P) (hkap0 : 0 ≤ kap) (hkap1 : kap < 1)
    (hsol : ∀ t s, HasDerivAt (delta t)
      (kappaInterp k0 k1 t s - Real.sin (delta t s)) s)
    (hper : ∀ t, Function.Periodic (delta t) P)
    (hstrip0 : ∀ t s, 0 ≤ delta t s)
    (hstrip1 : ∀ t s, delta t s ≤ Real.arcsin kap)
    (hKdper : Function.Periodic (fun s => k1 s - k0 s) P)
    (hKlip : ∀ a b s,
      |kappaInterp k0 k1 a s - kappaInterp k0 k1 b s| ≤ Klip * |a - b|)
    (hKtaylor : ∀ a b s,
      |kappaInterp k0 k1 a s - kappaInterp k0 k1 b s
        - (a - b) * (k1 s - k0 s)| ≤ CK * (a - b) ^ 2)
    (hCK : 0 ≤ CK)
    (hsfinv : ∀ t x, rearArclength (delta t) (sf t x) = x) :
    let F : ℝ → ℝ → ℂ := fun t s =>
      interpCurve (kappaInterp k0 k1 t) theta0 L s
    let Theta : ℝ → ℝ → ℝ := fun t s =>
      tangentAngle (kappaInterp k0 k1 t) theta0 s
    ContDiff ℝ (4 : ℕ) (uncurry F) ∧
      ContDiff ℝ (4 : ℕ) (uncurry Theta) ∧
      ContDiff ℝ (4 : ℕ) (uncurry delta) ∧
      ContDiff ℝ (4 : ℕ) (uncurry sf) ∧
      (∀ t s, HasDerivAt (F t)
        (Complex.exp (Complex.I * (Theta t s : ℂ))) s) ∧
      (∀ t s, HasDerivAt (Theta t) (kappaInterp k0 k1 t s) s) ∧
      (∀ t s, HasDerivAt (delta t)
        (kappaInterp k0 k1 t s - Real.sin (delta t s)) s) ∧
      (∀ t x, HasDerivAt (sf t) (1 / Real.cos (delta t (sf t x))) x) := by
  dsimp only
  have hF4 : ContDiff ℝ (4 : ℕ)
      (uncurry fun t s => interpCurve (kappaInterp k0 k1 t) theta0 L s) := by
    simpa using contDiff_succ_uncurry_interpCurve (n := 3) (theta0 := theta0)
      (L := L) hk0 hk1
  have hTheta4 : ContDiff ℝ (4 : ℕ)
      (uncurry fun t s => tangentAngle (kappaInterp k0 k1 t) theta0 s) := by
    simpa using contDiff_succ_uncurry_tangentAngle (n := 3) (theta0 := theta0) hk0 hk1
  have hK3 : ContDiff ℝ (3 : ℕ)
      (fun p : ℝ × ℝ => kappaInterp k0 k1 p.1 p.2) :=
    (contDiff_succ_uncurry_kappaInterp (n := 3) hk0 hk1).of_le (by norm_num)
  have hKd3 : ContDiff ℝ (3 : ℕ)
      (uncurry fun (_ : ℝ) (s : ℝ) => k1 s - k0 s) := by
    exact ((hk1.of_le (by norm_num)).comp contDiff_snd).sub
      ((hk0.of_le (by norm_num)).comp contDiff_snd)
  have hstrip : ∀ t s, delta t s ∈ Icc (0 : ℝ) (Real.arcsin kap) :=
    fun t s => ⟨hstrip0 t s, hstrip1 t s⟩
  have hdelta4 : ContDiff ℝ (4 : ℕ) (uncurry delta) :=
    contDiff_four_uncurry_delta_arc hP hkap0 hkap1 hsol hper hstrip (fun _ => hKdper)
      hKlip hKtaylor hCK hK3 hKd3
  have hsf4 : ContDiff ℝ (4 : ℕ) (uncurry sf) :=
    contDiff_sf (n := 3) hkap0 hkap1 hdelta4 hstrip0 hstrip1 hsfinv
  refine ⟨hF4, hTheta4, hdelta4, hsf4, ?_, ?_, hsol, ?_⟩
  · intro t s
    simpa [CurvatureInterpolation.tau, mul_comm] using
      hasDerivAt_interpCurve
        (continuous_kappaInterp hk0.continuous hk1.continuous) s
  · intro t s
    exact hasDerivAt_tangentAngle
      (continuous_kappaInterp hk0.continuous hk1.continuous) s
  · intro t x
    exact SelectedChangeOfVariable.hasDerivAt_sf_space hkap0 hkap1
      hdelta4.continuous hstrip0 hstrip1 hsfinv t x

end InterpolationSelectedRearRegularity
