import Mathlib
import UnitTangentIterates.FrontFromPathNormalized
import UnitTangentIterates.RearOwnPathDistNormalizedDefect

/-!
# The path pseudodistance for the path itself, together with the defect of its
gauge marking

`FrontFromPathNormalized.pathDist_le_of_path_normalized` states the bound for
the canonical front data of the normal path itself.  This file restates it with
the extra conclusions about the gauge marking `Φ` in which the pseudodistance is
read — `Φ` fixes the base point, reads exactly one rear period, and deviates
from the affine marking of the terminal period by at most
`2 P₁ κ̂/(1 − κ̂²) · cost Γ` — under the geometric hypothesis, already used to fix
the base point in the original statement, that the path does not move at its
marked point.

Main result: `pathDist_and_defect_le_of_path_normalized`.
-/

noncomputable section

open Set Function Complex MeasureTheory MarkedSpace MarkedTopology PathMetric
  PathMetric.NormalPath RearTrack ArclengthInverse RearFamilyFrame RearOwnArclength
  RearOwnMotion

namespace FrontFromPathNormalizedDefect

open UniformFrameBounds GaugePathDistVariable RearOwnPathDistSmooth
  RearOwnHigherRegularity SelectedInverseJacobiODE RearOwnPathDistIntrinsic
  FrontFromPath

variable {V A : ℝ → ℝ → ℂ} {δ dn Kn Kdn : ℝ → ℝ → ℝ} {P Pd : ℝ → ℝ}
  {P0 P1 kh Klip Plip : ℝ}

/-- **The path pseudodistance of the selected rears of a normal path, with the
front data on the normalized circle, together with the defect of its gauge
marking.**  `FrontFromPathNormalized.pathDist_le_of_path_normalized` with the
three extra conclusions about the marking. -/
theorem pathDist_and_defect_le_of_path_normalized {p q : Data} (Γ : NormalPath p q) (p' : Data)
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
          (rearArclength (δ 0) (P 0) * u))
    (hmark : ∀ t, Γ.eta t 0 = 0) :
    ∃ EF : ℝ, 0 ≤ EF ∧
      (∀ t s, |frontNormalVelocityAt (partialTime (frontOfPath Γ.X P))
        (angleOfPath V A P) δ t s| ≤ EF) ∧
      ∃ Phi : ℝ → ℝ → ℝ,
        (∀ u, Phi 0 u = rearArclength (δ 0) (P 0) * u) ∧
        (∀ t, Phi t 0 = 0) ∧ (∀ t, Phi t 1 = rearArclength (δ t) (P t)) ∧
        (∀ u, |Phi Γ.T u - rearArclength (δ Γ.T) (P Γ.T) * u|
          ≤ 2 * P1 * (kh / (1 - kh ^ 2)) * cost Γ) ∧
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
  refine RearOwnPathDistNormalizedDefect.pathDist_and_defect_le_of_front_normalized
    Γ p' hP0 hkh0 hkh1 hPl hPu
    hdelta hKeq hsol hstrip hdnper hKnper hKdnper hKnbd hKdnbd hPdbd hKnlip hPlip hKntaylor
    hPtaylor hCK hCP hPC4 hPdC3 hKnC3 hKdnC3 (fun t s => ?_)
    (fun t s => hasDerivAt_angleOfPath (hcurvcont t) s)
    (fun t s => periodic_frontOfPath (hXper t) (hPpos t) s)
    (fun t s => angleOfPath_add_period (hVper t) (hAper t) (hVcont t) (hAcont t) (hPpos t)
      (hturn t) s)
    hFc4 hΘc4 hsfinv (fun t u => ?_) (fun t u => ?_) hstart hmark
  · rw [exp_angleOfPath (hA t) (hAcont t) (hVcont t) (hspeed t) (hPpos t) s]
    exact hasDerivAt_frontOfPath_tangent (hV t) (hPpos t) s
  · have hu : P t * u / P t = u := by have := hPpos t; field_simp
    rw [frontOfPath, hu]
  · have hu : P t * u / P t = u := by have := hPpos t; field_simp
    rw [hnu t u, exp_angleOfPath (hA t) (hAcont t) (hVcont t) (hspeed t) (hPpos t) (P t * u),
      tangentOfPath, hu]

end FrontFromPathNormalizedDefect
