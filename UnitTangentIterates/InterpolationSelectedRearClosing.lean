import Mathlib
import UnitTangentIterates.InterpolationSelectedRearRegularity
import UnitTangentIterates.CurvatureInterpolationComplete
import UnitTangentIterates.RearOwnPathDistFrame

/-!
# Closing geometry of the interpolation-selected-rear family

An endpoint curvature has half-period `L` and total turning `π` on that
half-period.  Hence every affine interpolation slice has closed-front period
`2L` and tangent-angle increment `2π`.  A periodic selected steering angle and
an inverse rear-arclength coordinate then give a closed rear with period
`rearArclength δ (2L)` and the same total tangent turn.
-/

noncomputable section

open Function Set Real MeasureTheory RearTrack

namespace InterpolationSelectedRearClosing

open CurvatureInterpolation RearOwnArclength

variable {k0 k1 : ℝ → ℝ} {theta0 L kh : ℝ}
  {delta sf : ℝ → ℝ → ℝ}

/-- **All qualitative closing and rear-period facts for the concrete
curvature interpolation.**  The upper rear-period bound is the elementary
`Q_t ≤ 2L`; positivity follows from the selected strip. -/
theorem interpolation_selectedRear_closing_data
    (hL : 0 < L)
    (hk0 : Continuous k0) (hk1 : Continuous k1)
    (hper0 : Function.Periodic k0 L) (hper1 : Function.Periodic k1 L)
    (hint0 : (∫ r in (0 : ℝ)..L, k0 r) = Real.pi)
    (hint1 : (∫ r in (0 : ℝ)..L, k1 r) = Real.pi)
    (hkh0 : 0 ≤ kh) (hkh1 : kh < 1)
    (hdeltaC : Continuous (uncurry delta))
    (hdeltaper : ∀ t, Function.Periodic (delta t) (2 * L))
    (hstrip0 : ∀ t s, 0 ≤ delta t s)
    (hstrip1 : ∀ t s, delta t s ≤ Real.arcsin kh)
    (hsfinv : ∀ t x, rearArclength (delta t) (sf t x) = x) :
    let F : ℝ → ℝ → ℂ := fun t s =>
      interpCurve (kappaInterp k0 k1 t) theta0 L s
    let Theta : ℝ → ℝ → ℝ := fun t s =>
      tangentAngle (kappaInterp k0 k1 t) theta0 s
    (∀ t s, F t (s + 2 * L) = F t s) ∧
      (∀ t s, Theta t (s + 2 * L) = Theta t s + 2 * Real.pi) ∧
      (∀ t, Function.Periodic (delta t) (2 * L)) ∧
      (∀ t, 0 < rearArclength (delta t) (2 * L)) ∧
      (∀ t, rearArclength (delta t) (2 * L) ≤ 2 * L) ∧
      (∀ t x, rearOwn F Theta delta sf t
          (x + rearArclength (delta t) (2 * L)) = rearOwn F Theta delta sf t x) ∧
      (∀ t x, rearOwnAngle Theta delta sf t
          (x + rearArclength (delta t) (2 * L))
        = rearOwnAngle Theta delta sf t x + 2 * Real.pi) ∧
      F 0 = interpCurve k0 theta0 L ∧ F 1 = interpCurve k1 theta0 L ∧
      Theta 0 = tangentAngle k0 theta0 ∧ Theta 1 = tangentAngle k1 theta0 := by
  dsimp only
  have hkcont : ∀ t, Continuous (kappaInterp k0 k1 t) :=
    fun _ => continuous_kappaInterp hk0 hk1
  have hkper : ∀ t, Function.Periodic (kappaInterp k0 k1 t) L :=
    fun _ => periodic_kappaInterp hper0 hper1
  have hktotal : ∀ t, (∫ r in (0 : ℝ)..L, kappaInterp k0 k1 t r) = Real.pi :=
    fun _ => integral_kappaInterp hk0 hk1 hint0 hint1
  have hFper : ∀ t s,
      interpCurve (kappaInterp k0 k1 t) theta0 L (s + 2 * L)
        = interpCurve (kappaInterp k0 k1 t) theta0 L s :=
    fun t s => interpCurve_periodic (hkcont t) (hkper t) (hktotal t) s
  have hThetaper : ∀ t s,
      tangentAngle (kappaInterp k0 k1 t) theta0 (s + 2 * L)
        = tangentAngle (kappaInterp k0 k1 t) theta0 s + 2 * Real.pi := by
    intro t s
    have hfirst := tangentAngle_add_halfPeriod (θ₀ := theta0)
      (hkcont t) (hkper t) (hktotal t) s
    have hsecond := tangentAngle_add_halfPeriod (θ₀ := theta0)
      (hkcont t) (hkper t) (hktotal t) (s + L)
    rw [show s + 2 * L = (s + L) + L by ring, hsecond, hfirst]
    ring
  have hdeltaSlice : ∀ t, Continuous (delta t) := fun t =>
    hdeltaC.comp (continuous_const.prodMk continuous_id)
  have htwoL : 0 < 2 * L := by positivity
  have hQpos : ∀ t, 0 < rearArclength (delta t) (2 * L) := fun t =>
    SelectedPathData.rearPeriod_pos htwoL hkh0 hkh1 (hdeltaSlice t)
      (hstrip0 t) (hstrip1 t)
  have hQle : ∀ t, rearArclength (delta t) (2 * L) ≤ 2 * L := fun t =>
    ArclengthInverse.rearArclength_le_of_period (hdeltaSlice t) htwoL.le
  have hclose : ∀ t x, rearOwn
      (fun t s => interpCurve (kappaInterp k0 k1 t) theta0 L s)
      (fun t s => tangentAngle (kappaInterp k0 k1 t) theta0 s)
      delta sf t (x + rearArclength (delta t) (2 * L))
        = rearOwn
          (fun t s => interpCurve (kappaInterp k0 k1 t) theta0 L s)
          (fun t s => tangentAngle (kappaInterp k0 k1 t) theta0 s)
          delta sf t x :=
    rearOwn_closing hkh0 hkh1 hdeltaSlice hstrip0 hstrip1 hdeltaper hsfinv
      hFper hThetaper
  have hangle : ∀ t x, rearOwnAngle
      (fun t s => tangentAngle (kappaInterp k0 k1 t) theta0 s) delta sf t
        (x + rearArclength (delta t) (2 * L))
      = rearOwnAngle
          (fun t s => tangentAngle (kappaInterp k0 k1 t) theta0 s) delta sf t x
          + 2 * Real.pi :=
    RearOwnPathDistFrame.rearOwnAngle_shift hkh0 hkh1 hdeltaSlice hstrip0 hstrip1
      hdeltaper hsfinv hThetaper
  have hk0eq : kappaInterp k0 k1 0 = k0 := by
    funext r; simp [kappaInterp]
  have hk1eq : kappaInterp k0 k1 1 = k1 := by
    funext r; simp [kappaInterp]
  refine ⟨hFper, hThetaper, hdeltaper, hQpos, hQle, hclose, hangle, ?_, ?_, ?_, ?_⟩
  · funext s; rw [hk0eq]
  · funext s; rw [hk1eq]
  · funext s; rw [hk0eq]
  · funext s; rw [hk1eq]

end InterpolationSelectedRearClosing
