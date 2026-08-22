import Mathlib
import UnitTangentIterates.TurningNumberPath
import UnitTangentIterates.RearOwnPathDistSteering

/-!
# The path-distance bound of the selected rears, with the turning hypothesis produced

`RearOwnPathDistSteering.exists_steering_pathDist_le_of_path` bounds the path
pseudodistance between the selected rears of a normal path of fronts by a
uniform constant times the cost of the path, with the steering data produced
from the curvature.  Among the hypotheses it still carries is the
turning-number normalization of the slices,

`hturn : ∀ t, ∫_0^1 (conj V · A).im / P² = 2π`.

`TurningNumberPath.turning_of_path_of_pinched` produces that hypothesis from the
pinching of the curvature: the total turning of a closed slice is a multiple of
`2π`, and a two-sided bound `0 < kmin ≤ K̂ ≤ κ̂` with `κ̂·P(t) < 4π` leaves only
the value `2π`.  Since the curvature of the slices is already assumed to lie in
`[0, κ̂]` in that statement, what has to be added is a *positive* lower bound and
the length threshold `P(t) < 4π/κ̂`.

`exists_steering_pathDist_le_of_pinched_path` is the resulting statement: the
turning number of the slices is no longer assumed.
-/

noncomputable section

open Set Function Complex MeasureTheory MarkedSpace MarkedTopology PathMetric
  PathMetric.NormalPath RearTrack ArclengthInverse RearFamilyFrame RearOwnArclength
  RearOwnMotion

namespace TurningNumberPathDist

open RearOwnHigherRegularity GaugePathDistVariable

variable {Kn Kdn : ℝ → ℝ → ℝ} {P Pd : ℝ → ℝ} {P0 P1 kh Klip Plip : ℝ}

/-- **The path-distance bound for the selected rears of a normal path of fronts,
with the steering data produced and the turning number of the slices no longer
assumed.**  `RearOwnPathDistSteering.exists_steering_pathDist_le_of_path` with
its hypothesis `hturn` replaced by the pinching `0 < kmin ≤ K̂ ≤ κ̂` of the
curvature of the slices together with the length threshold `κ̂·P(t) < 4π`. -/
theorem exists_steering_pathDist_le_of_pinched_path {p q : Data} (Γ : NormalPath p q)
    {V A : ℝ → ℝ → ℂ} {Md MP CK CP kmin : ℝ}
    (hP0 : 0 < P0) (hkh0 : 0 ≤ kh) (hkh1 : kh < 1)
    (hPl : ∀ t, P0 ≤ P t) (hPu : ∀ t, P t ≤ P1)
    (hV : ∀ t u, HasDerivAt (Γ.X t) (V t u) u)
    (hA : ∀ t u, HasDerivAt (V t) (A t u) u)
    (hAcont : ∀ t, Continuous (A t))
    (hspeed : ∀ t u, ‖V t u‖ = P t)
    (hXper : ∀ t, Periodic (Γ.X t) 1) (hVper : ∀ t, Periodic (V t) 1)
    (hAper : ∀ t, Periodic (A t) 1)
    (hnuX : ∀ t u, Γ.nu t u = Complex.I * (V t u / (P t : ℂ)))
    (hKeq : ∀ t s, FrontFromPath.curvOfPath V A P t s = Kn t (s / P t))
    (hKnper : ∀ t, Function.Periodic (Kn t) 1)
    (hKdnper : ∀ t, Function.Periodic (Kdn t) 1)
    (hkmin : 0 < kmin) (hKnlow : ∀ t σ, kmin ≤ Kn t σ) (hKnk : ∀ t σ, Kn t σ ≤ kh)
    (hPsmall : ∀ t, kh * P t < 4 * Real.pi)
    (hKdnbd : ∀ t σ, |Kdn t σ| ≤ Md) (hPdbd : ∀ t, |Pd t| ≤ MP)
    (hKnlip : ∀ a b σ, |Kn a σ - Kn b σ| ≤ Klip * |a - b|)
    (hPlip : ∀ a b, |P a - P b| ≤ Plip * |a - b|)
    (hKntaylor : ∀ a b σ, |Kn a σ - Kn b σ - (a - b) * Kdn b σ| ≤ CK * (a - b) ^ 2)
    (hPtaylor : ∀ a b, |P a - P b - (a - b) * Pd b| ≤ CP * (a - b) ^ 2)
    (hCK : 0 ≤ CK) (hCP : 0 ≤ CP)
    (hPC4 : ContDiff ℝ (4 : ℕ) P) (hPdC3 : ContDiff ℝ (3 : ℕ) Pd)
    (hKnC3 : ContDiff ℝ (3 : ℕ) (uncurry Kn)) (hKdnC3 : ContDiff ℝ (3 : ℕ) (uncurry Kdn))
    (hFc4 : ContDiff ℝ (4 : ℕ) (uncurry (FrontFromPath.frontOfPath Γ.X P)))
    (hΘc4 : ContDiff ℝ (4 : ℕ) (uncurry (FrontFromPath.angleOfPath V A P))) :
    ∃ dn δ sf : ℝ → ℝ → ℝ,
      (∀ t, Function.Periodic (dn t) 1) ∧
      (∀ t σ, dn t σ ∈ Icc (0 : ℝ) (Real.arcsin kh)) ∧
      (∀ t σ, HasDerivAt (dn t) (P t * (Kn t σ - Real.sin (dn t σ))) σ) ∧
      (∀ t s, δ t s = dn t (s / P t)) ∧
      (∀ t x, rearArclength (δ t) (sf t x) = x) ∧
      ∀ p' : Data, (∀ u, p'.1 u = rearOwn (FrontFromPath.frontOfPath Γ.X P)
          (FrontFromPath.angleOfPath V A P) δ sf 0 (rearArclength (δ 0) (P 0) * u)) →
        ∃ EF : ℝ, 0 ≤ EF ∧
          (∀ t s, |frontNormalVelocityAt (partialTime (FrontFromPath.frontOfPath Γ.X P))
            (FrontFromPath.angleOfPath V A P) δ t s| ≤ EF) ∧
          ∃ Phi : ℝ → ℝ → ℝ,
            (∀ u, Phi 0 u = rearArclength (δ 0) (P 0) * u) ∧
            ((∀ t, Γ.eta t 0 = 0) → ∀ t, Phi t 0 = 0) ∧
            ∀ q' : Data, (∀ u, q'.1 u = rearOwn (FrontFromPath.frontOfPath Γ.X P)
                (FrontFromPath.angleOfPath V A P) δ sf Γ.T (Phi Γ.T u)) →
              pathDist p' q' ≤ gaugeJacobiConst P0 P1 kh
                  (EF / Real.sqrt (1 - kh ^ 2) * (kh / Real.sqrt (1 - kh ^ 2)))
                  ((EF / Real.sqrt (1 - kh ^ 2) + EF / Real.sqrt (1 - kh ^ 2))
                      * (kh / Real.sqrt (1 - kh ^ 2))
                    + EF / Real.sqrt (1 - kh ^ 2) * (2 * kh / Real.sqrt (1 - kh ^ 2) ^ 3)) Γ.T
                (rearArclength (δ 0) (P 0)) * cost Γ := by
  have hPpos : ∀ t, 0 < P t := fun t => lt_of_lt_of_le hP0 (hPl t)
  have hVcont : ∀ t, Continuous (V t) := fun t =>
    Differentiable.continuous fun u => (hA t u).differentiableAt
  have hturn : ∀ t, (∫ u in (0 : ℝ)..1, ((starRingEnd ℂ) (V t u) * A t u).im / P t ^ 2)
      = 2 * Real.pi :=
    TurningNumberPath.turning_of_path_of_pinched hA hVper hAper hVcont hAcont hspeed hPpos
      hkmin (fun t s => by rw [hKeq t s]; exact hKnlow t _)
      (fun t s => by rw [hKeq t s]; exact hKnk t _) hPsmall
  exact RearOwnPathDistSteering.exists_steering_pathDist_le_of_path Γ hP0 hkh0 hkh1 hPl hPu
    hV hA hAcont hspeed hXper hVper hAper hturn hnuX hKeq hKnper hKdnper
    (fun t σ => le_trans hkmin.le (hKnlow t σ)) hKnk hKdnbd hPdbd hKnlip hPlip hKntaylor
    hPtaylor hCK hCP hPC4 hPdC3 hKnC3 hKdnC3 hFc4 hΘc4

end TurningNumberPathDist
