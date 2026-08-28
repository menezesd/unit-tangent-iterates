import UnitTangentIterates.ConfiguredBaseSmoothSelectedSteering
import UnitTangentIterates.InterpolationSmooth
import UnitTangentIterates.SelectedRearGaugeProfiled

/-!
# Profiled canonical rear data for the smooth configured base family

This adapter starts with the globally smooth configured interpolation and its
globally `C^4` selected steering/inverse.  It then applies the stopped clock
`PathMetricCircle.B`; it does not use the separate exact `C^1` selected
steering construction.
-/

noncomputable section

open Function Set

namespace ConfiguredBaseSmoothSelectedRearProfiled

open CurvatureInterpolation ConfiguredApproximateDefectPathActualTerminal
  ConfiguredBaseSmoothSelectedSteering SelectedRearGaugeProfiled

variable {D : ConstructedConfiguredSequenceWeighted.Data}

/-- The front reconstructed from the globally smooth configured curvature. -/
def front (D : ConstructedConfiguredSequenceWeighted.Data) (n : ℕ)
    (t s : ℝ) : ℂ :=
  interpCurve (ConfiguredBaseSmoothSelectedSteering.curvature D n t)
    D.model.thetaBase (D.Hs n) s

/-- Its tangent-angle lift. -/
def angle (D : ConstructedConfiguredSequenceWeighted.Data) (n : ℕ)
    (t s : ℝ) : ℝ :=
  tangentAngle (ConfiguredBaseSmoothSelectedSteering.curvature D n t)
    D.model.thetaBase s

/-- The constant common front period. -/
def period (D : ConstructedConfiguredSequenceWeighted.Data) (n : ℕ)
    (_t : ℝ) : ℝ :=
  2 * D.Hs n

theorem front_C3 (C : ConstructedPulseWidth.C3Certificate D) (n : ℕ) :
    ContDiff ℝ 3 (uncurry (front D n)) := by
  have hraw := InterpolationSmooth.contDiff_three_uncurry_interpCurve
    (theta0 := D.model.thetaBase) (L := D.Hs n)
    (ConfiguredBaseSmoothSelectedSteering.sourceK0_C3 C n)
    (ConfiguredBaseSmoothSelectedSteering.sourceK1_C3 C n)
  have hcomp : ContDiff ℝ 3 (fun p : ℝ × ℝ ↦
      (ConfiguredBaseSmoothSelectedSteering.time p.1, p.2)) :=
    ((ConfiguredBaseSmoothSelectedSteering.contDiff_time 3).comp
      contDiff_fst).prodMk contDiff_snd
  simpa [front, ConfiguredBaseSmoothSelectedSteering.curvature,
    CurvatureInterpolation.kappaInterp, uncurry] using hraw.comp hcomp

theorem angle_C3 (C : ConstructedPulseWidth.C3Certificate D) (n : ℕ) :
    ContDiff ℝ 3 (uncurry (angle D n)) := by
  have hraw := InterpolationSmooth.contDiff_succ_uncurry_tangentAngle
    (n := 2) (theta0 := D.model.thetaBase)
    (ConfiguredBaseSmoothSelectedSteering.sourceK0_C3 C n)
    (ConfiguredBaseSmoothSelectedSteering.sourceK1_C3 C n)
  have hcomp : ContDiff ℝ 3 (fun p : ℝ × ℝ ↦
      (ConfiguredBaseSmoothSelectedSteering.time p.1, p.2)) :=
    ((ConfiguredBaseSmoothSelectedSteering.contDiff_time 3).comp
      contDiff_fst).prodMk contDiff_snd
  simpa [angle, ConfiguredBaseSmoothSelectedSteering.curvature,
    CurvatureInterpolation.kappaInterp, uncurry] using hraw.comp hcomp

theorem curvature_continuous_slice
    (C : ConstructedPulseWidth.C3Certificate D) (n : ℕ) (t : ℝ) :
    Continuous (ConfiguredBaseSmoothSelectedSteering.curvature D n t) := by
  have h0 := (ConfiguredBaseSmoothSelectedSteering.sourceK0_C3 C n).continuous
  have h1 := (ConfiguredBaseSmoothSelectedSteering.sourceK1_C3 C n).continuous
  simpa [ConfiguredBaseSmoothSelectedSteering.curvature] using
    (continuous_const.mul h0).add (continuous_const.mul h1)

theorem front_frenet (C : ConstructedPulseWidth.C3Certificate D) (n : ℕ)
    (t s : ℝ) :
    HasDerivAt (front D n t)
      (Complex.exp (Complex.I * (angle D n t s : ℂ))) s := by
  have hk := curvature_continuous_slice C n t
  simpa [front, angle, CurvatureInterpolation.tau, mul_comm] using
    (CurvatureInterpolation.hasDerivAt_interpCurve
      (θ₀ := D.model.thetaBase) (L := D.Hs n) hk s)

theorem angle_frenet (C : ConstructedPulseWidth.C3Certificate D) (n : ℕ)
    (t s : ℝ) :
    HasDerivAt (angle D n t)
      (ConfiguredBaseSmoothSelectedSteering.curvature D n t s) s := by
  have hk := curvature_continuous_slice C n t
  exact CurvatureInterpolation.hasDerivAt_tangentAngle hk s

/-- The configured smooth selected rear, followed by the stopped clock,
supplies the entire weakened profiled rear-data certificate at a fixed depth. -/
theorem exists_profiled_configured
    (C : ConstructedPulseWidth.C3Certificate D)
    (H : ConfiguredActualSubunitCurvature.Certificate D) (n : ℕ) :
    ∃ delta sf : ℝ → ℝ → ℝ,
      ∃ Ydot : ℝ → ℝ → ℂ, ∃ alphaT kT : ℝ → ℝ → ℝ,
        Nonempty (ProfiledSelectedData
          (front D n) (angle D n) delta
          (ConfiguredBaseSmoothSelectedSteering.curvature D n) sf
          (period D n) H.k0 Ydot alphaT kT) := by
  obtain ⟨delta, sf, hper, hstrip, hsteer, hdelta4, hsf4, hinv, -⟩ :=
    ConfiguredBaseSmoothSelectedSteering.exists_selected C H n
  have hk0 : 0 ≤ H.k0 :=
    (H.front_nonnegative n 0).trans (H.front_le n 0)
  obtain ⟨Ydot, alphaT, kT, R⟩ :=
    SelectedRearGaugeProfiled.exists_profiled
      (F := front D n) (Theta := angle D n)
      (delta := delta)
      (K := ConfiguredBaseSmoothSelectedSteering.curvature D n)
      (sf := sf) (P := period D n) (kh := H.k0)
      hk0 H.k0_lt_one (front_C3 C n) (angle_C3 C n)
      hdelta4 hsf4 (front_frenet C n) (angle_frenet C n) hsteer
      (fun t s ↦ (hstrip t s).1) (fun t s ↦ (hstrip t s).2) hinv
      (by simpa [period] using hper)
  exact ⟨delta, sf, Ydot, alphaT, kT, R⟩

end ConfiguredBaseSmoothSelectedRearProfiled
