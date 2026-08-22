import Mathlib
import UnitTangentIterates.RearOwnPathDistFrontOnly
import UnitTangentIterates.SteeringVariablePeriod

/-!
# The path pseudodistance of the selected rears, from the front curvature alone

`RearOwnPathDistFrontOnly.pathDist_le_of_front_curve` reduces the data of the
bound to the front curve, but it still *assumes* the joint `C⁴` regularity of
the selected steering angle `δ`, which is not a datum of the front: `δ` is the
selected periodic solution of `δ_s = K − sin δ`, and its regularity in the path
parameter is a theorem, not an assumption.

`SteeringVariablePeriod.contDiff_four_uncurry_delta` is that theorem, with each
slice carrying its own arclength period.  Feeding it to the previous file gives
the bound with the regularity of `δ` replaced by hypotheses on the curvature
alone: its Lipschitz and first-order Taylor bounds in the path parameter,
together with the joint `C³` regularity of the curvature, of its parameter
derivative and of the period.
-/

noncomputable section

open Set Function Complex MeasureTheory MarkedSpace MarkedTopology PathMetric
  PathMetric.NormalPath RearTrack ArclengthInverse RearFamilyFrame RearOwnArclength
  RearOwnMotion

namespace RearOwnPathDistCurvature

open UniformFrameBounds GaugePathDistVariable RearOwnPathDistSmooth
  RearOwnHigherRegularity RearOwnPathDistFrontOnly

/-- **The path pseudodistance of the selected rears, from the front curvature
alone.**

Same statement as `RearOwnPathDistFrontOnly.pathDist_le_of_front_curve`, with
the joint `C⁴` regularity of the selected steering angle *derived* instead of
assumed: the curvature `K` is jointly `C³`, Lipschitz and once differentiable
in the path parameter with a uniform first-order Taylor bound, its parameter
derivative `K̇` is jointly `C³`, bounded and periodic with the front period,
and the front period `P` is itself jointly `C³`. -/
theorem pathDist_le_of_front_curvature {p q : Data} (Γ : NormalPath p q) (p' : Data)
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
    (hstart : ∀ u, p'.1 u = rearOwn F Θ δ sf 0 (rearArclength (δ 0) (P 0) * u)) :
    ∃ Phi : ℝ → ℝ → ℝ,
      (∀ u, Phi 0 u = rearArclength (δ 0) (P 0) * u) ∧
      ((∀ t, RearBaseDrift.frontBaseDrift (RearOwnHigherRegularity.partialTime F) Θ δ t = 0) →
        ∀ t, Phi t 0 = 0) ∧
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
  exact pathDist_le_of_front_curve Γ p' hP0 hkh0 hkh1 hPl hPu hF hΘ hsteer hstrip0 hstrip1
    hdper hK hKc hFper hΘper hFc4 hΘc4 hδc4 hsfinv hetaFper hlink hQd hEF hFrest hstart

end RearOwnPathDistCurvature
