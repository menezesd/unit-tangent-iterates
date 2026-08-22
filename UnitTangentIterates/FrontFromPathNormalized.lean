import Mathlib
import UnitTangentIterates.FrontFromPath
import UnitTangentIterates.RearOwnPathDistNormalized

/-!
# The normalized path-distance bound, for the slices of the path itself

`RearOwnPathDistNormalized.pathDist_le_of_front_normalized` is the form of the
path-distance bound for the selected rears in which the front curvature and the
steering angle are given on the normalized circle, so that no hypothesis of the
chain forces the arclength period to stand still.  Like the sliced form, it
still relates the abstract normal path `Γ` to the family of fronts through the
geometric identification

```
  X(t, u) = F(t, P(t) u) ,      ν(t, u) = i e^{iΘ(t, P(t) u)} .
```

`FrontFromPath.lean` shows that this identification is automatic once the front
family is taken to be the family of slices of the path itself.  This file
combines the two: `pathDist_le_of_path_normalized` is the normalized bound with
the front, its tangent angle and its curvature replaced by the canonical data
of the path — `frontOfPath`, `angleOfPath`, `curvOfPath` — so that the only
remaining hypotheses on the path are that its slices are closed curves of
constant speed and turning number one, moving along their standard unit normal.
-/

noncomputable section

open Set Function Complex MeasureTheory MarkedSpace MarkedTopology PathMetric
  PathMetric.NormalPath RearTrack ArclengthInverse RearFamilyFrame RearOwnArclength
  RearOwnMotion

namespace FrontFromPathNormalized

open UniformFrameBounds GaugePathDistVariable RearOwnPathDistSmooth
  RearOwnHigherRegularity SelectedInverseJacobiODE RearOwnPathDistIntrinsic
  FrontFromPath

variable {V A : ℝ → ℝ → ℂ} {δ dn Kn Kdn : ℝ → ℝ → ℝ} {P Pd : ℝ → ℝ}
  {P0 P1 kh Klip Plip : ℝ}

/-- **The path pseudodistance of the selected rears of a normal path, with the
front data on the normalized circle.**

The bound of `RearOwnPathDistNormalized.pathDist_le_of_front_normalized` for
the canonical front data of the path itself: the slices written in their own
arclength (`FrontFromPath.frontOfPath`), their tangent angle
(`FrontFromPath.angleOfPath`) and their curvature (`FrontFromPath.curvOfPath`).
The geometric identification of the slices is discharged by
`FrontFromPath.exists_front_of_path`; what is asked of the path is that its
slices be closed curves of constant speed `P t` and turning number one moving
along their standard unit normal, and what is asked of the front data is
exactly what the normalized form asks — in particular nothing forces the
arclength period to stand still. -/
theorem pathDist_le_of_path_normalized {p q : Data} (Γ : NormalPath p q) (p' : Data)
    {Md MP CK CP : ℝ} {sf : ℝ → ℝ → ℝ}
    (hP0 : 0 < P0) (hkh0 : 0 ≤ kh) (hkh1 : kh < 1)
    (hPl : ∀ t, P0 ≤ P t) (hPu : ∀ t, P t ≤ P1)
    (hV : ∀ t u, HasDerivAt (Γ.X t) (V t u) u)
    (hA : ∀ t u, HasDerivAt (V t) (A t u) u)
    (hAcont : ∀ t, Continuous (A t))
    (hspeed : ∀ t u, ‖V t u‖ = P t)
    (hXper : ∀ t, Periodic (Γ.X t) 1) (hVper : ∀ t, Periodic (V t) 1)
    (hAper : ∀ t, Periodic (A t) 1)
    (hturn : ∀ t, (∫ u in (0 : ℝ)..1, ((starRingEnd ℂ) (V t u) * A t u).im / P t ^ 2)
      = 2 * Real.pi)
    (hnu : ∀ t u, Γ.nu t u = Complex.I * (V t u / (P t : ℂ)))
    (hdelta : ∀ t s, δ t s = dn t (s / P t))
    (hKeq : ∀ t s, curvOfPath V A P t s = Kn t (s / P t))
    (hsol : ∀ t σ, HasDerivAt (dn t) (P t * (Kn t σ - Real.sin (dn t σ))) σ)
    (hstrip : ∀ t σ, dn t σ ∈ Icc (0 : ℝ) (Real.arcsin kh))
    (hdnper : ∀ t, Function.Periodic (dn t) 1) (hKnper : ∀ t, Function.Periodic (Kn t) 1)
    (hKdnper : ∀ t, Function.Periodic (Kdn t) 1)
    (hKnbd : ∀ t σ, |Kn t σ| ≤ kh) (hKdnbd : ∀ t σ, |Kdn t σ| ≤ Md)
    (hPdbd : ∀ t, |Pd t| ≤ MP)
    (hKnlip : ∀ a b σ, |Kn a σ - Kn b σ| ≤ Klip * |a - b|)
    (hPlip : ∀ a b, |P a - P b| ≤ Plip * |a - b|)
    (hKntaylor : ∀ a b σ, |Kn a σ - Kn b σ - (a - b) * Kdn b σ| ≤ CK * (a - b) ^ 2)
    (hPtaylor : ∀ a b, |P a - P b - (a - b) * Pd b| ≤ CP * (a - b) ^ 2)
    (hCK : 0 ≤ CK) (hCP : 0 ≤ CP)
    (hPC4 : ContDiff ℝ (4 : ℕ) P) (hPdC3 : ContDiff ℝ (3 : ℕ) Pd)
    (hKnC3 : ContDiff ℝ (3 : ℕ) (uncurry Kn)) (hKdnC3 : ContDiff ℝ (3 : ℕ) (uncurry Kdn))
    (hFc4 : ContDiff ℝ (4 : ℕ) (uncurry (frontOfPath Γ.X P)))
    (hΘc4 : ContDiff ℝ (4 : ℕ) (uncurry (angleOfPath V A P)))
    (hsfinv : ∀ t x, rearArclength (δ t) (sf t x) = x)
    (hstart : ∀ u, p'.1 u
      = rearOwn (frontOfPath Γ.X P) (angleOfPath V A P) δ sf 0
          (rearArclength (δ 0) (P 0) * u)) :
    ∃ EF : ℝ, 0 ≤ EF ∧
      (∀ t s, |frontNormalVelocityAt (partialTime (frontOfPath Γ.X P))
        (angleOfPath V A P) δ t s| ≤ EF) ∧
      ∃ Phi : ℝ → ℝ → ℝ,
        (∀ u, Phi 0 u = rearArclength (δ 0) (P 0) * u) ∧
        ((∀ t, Γ.eta t 0 = 0) → ∀ t, Phi t 0 = 0) ∧
        ∀ q' : Data, (∀ u, q'.1 u
            = rearOwn (frontOfPath Γ.X P) (angleOfPath V A P) δ sf Γ.T (Phi Γ.T u)) →
          pathDist p' q' ≤ gaugeJacobiConst P0 P1 kh
              (EF / Real.sqrt (1 - kh ^ 2) * (kh / Real.sqrt (1 - kh ^ 2)))
              ((EF / Real.sqrt (1 - kh ^ 2) + EF / Real.sqrt (1 - kh ^ 2))
                  * (kh / Real.sqrt (1 - kh ^ 2))
                + EF / Real.sqrt (1 - kh ^ 2) * (2 * kh / Real.sqrt (1 - kh ^ 2) ^ 3)) Γ.T
            (rearArclength (δ 0) (P 0)) * cost Γ := by
  have hPpos : ∀ t, 0 < P t := fun t => lt_of_lt_of_le hP0 (hPl t)
  have hVcont : ∀ t, Continuous (V t) := fun t =>
    continuous_iff_continuousAt.2 fun u => (hA t u).continuousAt
  have hcurvcont : ∀ t, Continuous (curvOfPath V A P t) := fun t =>
    continuous_curvOfPath (hVcont t) (hAcont t)
  refine RearOwnPathDistNormalized.pathDist_le_of_front_normalized Γ p' hP0 hkh0 hkh1 hPl hPu
    hdelta hKeq hsol hstrip hdnper hKnper hKdnper hKnbd hKdnbd hPdbd hKnlip hPlip hKntaylor
    hPtaylor hCK hCP hPC4 hPdC3 hKnC3 hKdnC3 (fun t s => ?_)
    (fun t s => hasDerivAt_angleOfPath (hcurvcont t) s)
    (fun t s => periodic_frontOfPath (hXper t) (hPpos t) s)
    (fun t s => angleOfPath_add_period (hVper t) (hAper t) (hVcont t) (hAcont t) (hPpos t)
      (hturn t) s)
    hFc4 hΘc4 hsfinv (fun t u => ?_) (fun t u => ?_) hstart
  · rw [exp_angleOfPath (hA t) (hAcont t) (hVcont t) (hspeed t) (hPpos t) s]
    exact hasDerivAt_frontOfPath_tangent (hV t) (hPpos t) s
  · have hu : P t * u / P t = u := by have := hPpos t; field_simp
    rw [frontOfPath, hu]
  · have hu : P t * u / P t = u := by have := hPpos t; field_simp
    rw [hnu t u, exp_angleOfPath (hA t) (hAcont t) (hVcont t) (hspeed t) (hPpos t) (P t * u),
      tangentOfPath, hu]

end FrontFromPathNormalized
