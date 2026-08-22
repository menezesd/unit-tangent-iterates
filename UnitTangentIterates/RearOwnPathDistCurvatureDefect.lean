import Mathlib
import UnitTangentIterates.RearOwnPathDistCurvature
import UnitTangentIterates.RearOwnPathDistFrontOnlyDefect

/-!
# The path pseudodistance from the front curvature alone, together with the
defect of its gauge marking

`RearOwnPathDistCurvature.pathDist_le_of_front_curvature` derives the joint `C⁴`
regularity of the selected steering angle from hypotheses on the curvature
alone.  This file restates it with the extra conclusions about the gauge marking
`Φ` in which the pseudodistance is read — `Φ` fixes the base point, reads exactly
one rear period, and deviates from the affine marking of the terminal period by
at most `2 P₁ κ̂/(1 − κ̂²) · cost Γ` — under the single extra hypothesis that the
base drift of the front vanishes.

Main result: `pathDist_and_defect_le_of_front_curvature`.
-/

noncomputable section

open Set Function Complex MeasureTheory MarkedSpace MarkedTopology PathMetric
  PathMetric.NormalPath RearTrack ArclengthInverse RearFamilyFrame RearOwnArclength
  RearOwnMotion

namespace RearOwnPathDistCurvatureDefect

open UniformFrameBounds GaugePathDistVariable RearOwnPathDistSmooth
  RearOwnHigherRegularity RearOwnPathDistFrontOnly

/-- **The path pseudodistance of the selected rears from the front curvature
alone, together with the defect of its gauge marking.**
`RearOwnPathDistCurvature.pathDist_le_of_front_curvature` with the three extra
conclusions about the marking. -/
theorem pathDist_and_defect_le_of_front_curvature {p q : Data} (Γ : NormalPath p q) (p' : Data)
    {P0 P1 kh EF Md Klip CK : ℝ} {P Qf' : ℝ → ℝ} {F : ℝ → ℝ → ℂ}
    {Θ δ K Kd sf : ℝ → ℝ → ℝ}
    (hP0 : 0 < P0) (hkh0 : 0 ≤ kh) (hkh1 : kh < 1)
    (hPl : ∀ t, P0 ≤ P t) (hPu : ∀ t, P t ≤ P1)
    (hF : ∀ t s, HasDerivAt (F t) (Complex.exp (Complex.I * (Θ t s : ℂ))) s)
    (hΘ : ∀ t s, HasDerivAt (Θ t) (K t s) s)
    (hsteer : ∀ t s, HasDerivAt (δ t) (K t s - Real.sin (δ t s)) s)
    (hstrip0 : ∀ t s, 0 ≤ δ t s) (hstrip1 : ∀ t s, δ t s ≤ Real.arcsin kh)
    (hdper : ∀ t, Function.Periodic (δ t) (P t))
    (hK : ∀ t s, |K t s| ≤ kh) (hKc : ∀ t, Continuous (K t))
    (hFper : ∀ t s, F t (s + P t) = F t s)
    (hΘper : ∀ t s, Θ t (s + P t) = Θ t s + 2 * Real.pi)
    (hFc4 : ContDiff ℝ (4 : ℕ) (uncurry F)) (hΘc4 : ContDiff ℝ (4 : ℕ) (uncurry Θ))
    (hKdper : ∀ t, Function.Periodic (Kd t) (P t))
    (hKdbd : ∀ t s, |Kd t s| ≤ Md)
    (hKlip : ∀ a b s, |K a s - K b s| ≤ Klip * |a - b|)
    (hKtaylor : ∀ a b s, |K a s - K b s - (a - b) * Kd b s| ≤ CK * (a - b) ^ 2)
    (hCK : 0 ≤ CK) (hPC3 : ContDiff ℝ (3 : ℕ) P) (hKC3 : ContDiff ℝ (3 : ℕ) (uncurry K))
    (hKdC3 : ContDiff ℝ (3 : ℕ) (uncurry Kd))
    (hsfinv : ∀ t x, rearArclength (δ t) (sf t x) = x)
    (hetaFper : ∀ t,
      Function.Periodic (frontNormalVelocityAt (partialTime F) Θ δ t) (P t))
    (hlink : ∀ t u, Γ.eta t u = frontNormalVelocityAt (partialTime F) Θ δ t (P t * u))
    (hQd : ∀ t, HasDerivAt (fun r => rearArclength (δ r) (P r)) (Qf' t) t)
    (hEF : ∀ t s, |frontNormalVelocityAt (partialTime F) Θ δ t s| ≤ EF)
    (hFrest : ∀ t ∉ Ioo (0 : ℝ) Γ.T, ∀ s,
      frontNormalVelocityAt (partialTime F) Θ δ t s = 0)
    (hstart : ∀ u, p'.1 u = rearOwn F Θ δ sf 0 (rearArclength (δ 0) (P 0) * u))
    (hdrift : ∀ t, RearBaseDrift.frontBaseDrift (RearOwnHigherRegularity.partialTime F) Θ δ t = 0) :
    ∃ Phi : ℝ → ℝ → ℝ,
      (∀ u, Phi 0 u = rearArclength (δ 0) (P 0) * u) ∧
      (∀ t, Phi t 0 = 0) ∧ (∀ t, Phi t 1 = rearArclength (δ t) (P t)) ∧
      (∀ u, |Phi Γ.T u - rearArclength (δ Γ.T) (P Γ.T) * u|
        ≤ 2 * P1 * (kh / (1 - kh ^ 2)) * cost Γ) ∧
      ∀ q' : Data, (∀ u, q'.1 u = rearOwn F Θ δ sf Γ.T (Phi Γ.T u)) →
        pathDist p' q' ≤ gaugeJacobiConst P0 P1 kh
            (EF / Real.sqrt (1 - kh ^ 2) * (kh / Real.sqrt (1 - kh ^ 2)))
            ((EF / Real.sqrt (1 - kh ^ 2) + EF / Real.sqrt (1 - kh ^ 2))
                * (kh / Real.sqrt (1 - kh ^ 2))
              + EF / Real.sqrt (1 - kh ^ 2) * (2 * kh / Real.sqrt (1 - kh ^ 2) ^ 3)) Γ.T
          (rearArclength (δ 0) (P 0)) * cost Γ := by
  have hPpos : ∀ t, 0 < P t := fun t => lt_of_lt_of_le hP0 (hPl t)
  have hstrip : ∀ t s, δ t s ∈ Icc (0 : ℝ) (Real.arcsin kh) := fun t s =>
    ⟨hstrip0 t s, hstrip1 t s⟩
  have hδc4 : ContDiff ℝ (4 : ℕ) (uncurry δ) :=
    SteeringVariablePeriod.contDiff_four_uncurry_delta (K := K) (Kd := Kd) (Pf := P)
      (kap := kh) hkh0 hkh1 hPpos hsteer hstrip hdper hKdper hKdbd hKlip hKtaylor hCK
      hPC3 hKC3 hKdC3
  exact RearOwnPathDistFrontOnlyDefect.pathDist_and_defect_le_of_front_curve Γ p' hP0 hkh0 hkh1 hPl hPu hF hΘ hsteer hstrip0 hstrip1
    hdper hK hKc hFper hΘper hFc4 hΘc4 hδc4 hsfinv hetaFper hlink hQd hEF hFrest hstart hdrift

end RearOwnPathDistCurvatureDefect
