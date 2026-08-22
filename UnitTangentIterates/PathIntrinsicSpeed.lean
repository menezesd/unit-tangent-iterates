import Mathlib
import UnitTangentIterates.FrontFromPath
import UnitTangentIterates.RearOwnPathDistSpeed

/-!
# The path-distance bound for the selected rears of a slow normal path

`FrontFromPath.pathDist_le_of_path_intrinsic` bounds the path pseudodistance of
the selected rears of a normal path in terms of the cost of that path, with a
constant computed from a sup bound `E_F` for the front normal velocity which the
statement *produces* by compactness.

This file states the same bound with `E_F` supplied by the **cost density of the
path**, through `RearOwnPathDistSpeed.pathDist_le_of_front_slices_speed`: the
slices of the path are its own family of fronts, so its normal speed is the
front normal velocity and any bound `M` for the cost density bounds `E_F`.  The
constant of the conclusion is therefore an explicit function of `M`, and
`PathMetricSpeed.exists_unitTime_bounded_speed` shows that a near-optimal path
may always be taken with `M` at most `3/2` times its cost.

Main result: `pathDist_le_of_path_intrinsic_speed`.
-/

noncomputable section

open Set Function Complex MeasureTheory MarkedSpace PathMetric PathMetric.NormalPath

namespace PathIntrinsicSpeed

open RearTrack ArclengthInverse RearOwnArclength UniformFrameBounds RearOwnHigherRegularity
  GaugePathDistVariable RearOwnPathDistSmooth SelectedInverseJacobiODE
  RearOwnPathDistIntrinsic RearFamilyFrame FrontFromPath RearOwnPathDistSpeed

variable {V A : ℝ → ℝ → ℂ} {P : ℝ → ℝ}

/-- **The path pseudodistance of the selected rears of a slow normal path.**

Same statement as `FrontFromPath.pathDist_le_of_path_intrinsic`, with the sup
bound of the front normal velocity replaced by any bound `M` for the cost
density of the path: the constant of the conclusion is then a function of `M`
alone, and not of a quantity produced from the path by compactness. -/
theorem pathDist_le_of_path_intrinsic_speed {p q : Data} (Γ : NormalPath p q) (p' : Data)
    {P0 P1 kh M Md Klip CK : ℝ} {δ Kd sf : ℝ → ℝ → ℝ}
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
    (hsteer : ∀ t s, HasDerivAt (δ t) (curvOfPath V A P t s - Real.sin (δ t s)) s)
    (hstrip0 : ∀ t s, 0 ≤ δ t s) (hstrip1 : ∀ t s, δ t s ≤ Real.arcsin kh)
    (hdper : ∀ t, Function.Periodic (δ t) (P t))
    (hK : ∀ t s, |curvOfPath V A P t s| ≤ kh)
    (hFc4 : ContDiff ℝ (4 : ℕ) (uncurry (frontOfPath Γ.X P)))
    (hΘc4 : ContDiff ℝ (4 : ℕ) (uncurry (angleOfPath V A P)))
    (hKdper : ∀ t, Function.Periodic (Kd t) (P t))
    (hKdbd : ∀ t s, |Kd t s| ≤ Md)
    (hKlip : ∀ a b s, |curvOfPath V A P a s - curvOfPath V A P b s| ≤ Klip * |a - b|)
    (hKtaylor : ∀ a b s,
      |curvOfPath V A P a s - curvOfPath V A P b s - (a - b) * Kd b s| ≤ CK * (a - b) ^ 2)
    (hCK : 0 ≤ CK) (hPC3 : ContDiff ℝ (3 : ℕ) P)
    (hKC3 : ContDiff ℝ (3 : ℕ) (uncurry (curvOfPath V A P)))
    (hKdC3 : ContDiff ℝ (3 : ℕ) (uncurry Kd))
    (hsfinv : ∀ t x, rearArclength (δ t) (sf t x) = x)
    (hm : ∀ t, Γ.m t ≤ M)
    (hstart : ∀ u, p'.1 u
      = rearOwn (frontOfPath Γ.X P) (angleOfPath V A P) δ sf 0
          (rearArclength (δ 0) (P 0) * u)) :
    ∃ Phi : ℝ → ℝ → ℝ,
      (∀ u, Phi 0 u = rearArclength (δ 0) (P 0) * u) ∧
      ((∀ t, Γ.eta t 0 = 0) → ∀ t, Phi t 0 = 0) ∧
      ∀ q' : Data, (∀ u, q'.1 u
          = rearOwn (frontOfPath Γ.X P) (angleOfPath V A P) δ sf Γ.T (Phi Γ.T u)) →
        pathDist p' q' ≤ gaugeJacobiConst P0 P1 kh
            (M / Real.sqrt (1 - kh ^ 2) * (kh / Real.sqrt (1 - kh ^ 2)))
            ((M / Real.sqrt (1 - kh ^ 2) + M / Real.sqrt (1 - kh ^ 2))
                * (kh / Real.sqrt (1 - kh ^ 2))
              + M / Real.sqrt (1 - kh ^ 2) * (2 * kh / Real.sqrt (1 - kh ^ 2) ^ 3)) Γ.T
          (rearArclength (δ 0) (P 0)) * cost Γ := by
  have hPpos : ∀ t, 0 < P t := fun t => lt_of_lt_of_le hP0 (hPl t)
  have hVcont : ∀ t, Continuous (V t) := fun t =>
    continuous_iff_continuousAt.2 fun u => (hA t u).continuousAt
  have hcurvcont : ∀ t, Continuous (curvOfPath V A P t) := fun t =>
    continuous_curvOfPath (hVcont t) (hAcont t)
  refine pathDist_le_of_front_slices_speed Γ p' (M := M) hP0 hkh0 hkh1 hPl hPu
    (fun t s => ?_) (fun t s => hasDerivAt_angleOfPath (hcurvcont t) s) hsteer hstrip0
    hstrip1 hdper hK (fun t => hcurvcont t) (fun t s => periodic_frontOfPath (hXper t) (hPpos t) s)
    (fun t s => angleOfPath_add_period (hVper t) (hAper t) (hVcont t) (hAcont t) (hPpos t)
      (hturn t) s)
    hFc4 hΘc4 hKdper hKdbd hKlip hKtaylor hCK hPC3 hKC3 hKdC3 hsfinv (fun t u => ?_)
    (fun t u => ?_) hm hstart
  · rw [exp_angleOfPath (hA t) (hAcont t) (hVcont t) (hspeed t) (hPpos t) s]
    exact hasDerivAt_frontOfPath_tangent (hV t) (hPpos t) s
  · have hu : P t * u / P t = u := by have := hPpos t; field_simp
    rw [frontOfPath, hu]
  · have hu : P t * u / P t = u := by have := hPpos t; field_simp
    rw [hnu t u, exp_angleOfPath (hA t) (hAcont t) (hVcont t) (hspeed t) (hPpos t) (P t * u),
      tangentOfPath, hu]

end PathIntrinsicSpeed
