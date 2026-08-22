import Mathlib
import UnitTangentIterates.SelectedInverseShiftPathRegularity
import UnitTangentIterates.RearTrackEmbedded

/-!
# The shift bound with the embeddedness of the rear tracks discharged

The shift bound of `SelectedInverseShiftPathRegularity.lean` carries, at each
of its two ends, the hypothesis that every steering solution on the selected
strip reconstructs an *embedded* rear track.  `RearTrackEmbedded.lean` proves
that this holds for a member of the tube whose front tangent angle turns by
`2π`: on the selected strip the rear tangent angle increases strictly, it
increases by exactly `2π` over one period, and a closed regular curve of
turning number one is embedded.

This file feeds that in.  The result below is the shift bound with the two
embeddedness hypotheses replaced by the turning number of the two fronts — a
global topological fact, carried as an explicit hypothesis here as everywhere
in this project.

Main result: `exists_steering_pathDistShift_selInv_le_embedded`.
-/

noncomputable section

open Set Function Complex MeasureTheory MarkedSpace MarkedTopology PathMetric
  PathMetric.NormalPath RearTrack ArclengthInverse RearFamilyFrame RearOwnArclength
  RearOwnMotion

namespace SelectedInverseShiftEmbedded

open UniformFrameBounds GaugePathDistVariable RearOwnHigherRegularity
  FrontFromPath SelectedInverseRearOwn PathDataTaylorBounds FrontDataRegularity

variable {V A : ℝ → ℝ → ℂ} {Kn : ℝ → ℝ → ℝ} {P : ℝ → ℝ} {P0 P1 kh : ℝ}

/-- **The shift bound for the marked selected inverses of the two ends of a
normal path, with the embeddedness of the rear tracks discharged.**

Same statement as
`SelectedInverseShiftPathRegularity.exists_steering_pathDistShift_selInv_le_pathSlit`,
with the two hypotheses asking every steering solution to reconstruct an
embedded rear track replaced by the turning number of the two fronts: the
tangent angle of each end increases by `2π` over one period.  The rear tracks
are then embedded by `RearTrackEmbedded.injOn_rearTrack_of_tube`. -/
theorem exists_steering_pathDistShift_selInv_le_embedded {p q : Data} (Γ : NormalPath p q)
    {c kmin dlt cq kminq dltq M : ℝ}
    (hc : 0 < c) (hkmin : 0 < kmin) (hp : IsTubeMember c kmin dlt p)
    (hub : ∀ u, ((starRingEnd ℂ) (p.2.1 u) * p.2.2 u).im ≤ kh * ‖p.2.1 u‖ ^ 3)
    (hturnp : ∃ Θ' K' : ℝ → ℝ,
      (∀ s, HasDerivAt (ev p) (Complex.exp (Complex.I * (Θ' s : ℂ))) s) ∧
      (∀ s, HasDerivAt Θ' (K' s) s) ∧
      (∀ s, Θ' (s + perim p) = Θ' s + 2 * Real.pi))
    (hcq : 0 < cq) (hkminq : 0 < kminq) (hq : IsTubeMember cq kminq dltq q)
    (hubq : ∀ u, ((starRingEnd ℂ) (q.2.1 u) * q.2.2 u).im ≤ kh * ‖q.2.1 u‖ ^ 3)
    (hturnq : ∃ Θ' K' : ℝ → ℝ,
      (∀ s, HasDerivAt (ev q) (Complex.exp (Complex.I * (Θ' s : ℂ))) s) ∧
      (∀ s, HasDerivAt Θ' (K' s) s) ∧
      (∀ s, Θ' (s + perim q) = Θ' s + 2 * Real.pi))
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
    (hKeq : ∀ t s, curvOfPath V A P t s = Kn t (s / P t))
    (hKnper : ∀ t, Function.Periodic (Kn t) 1)
    (hKn0 : ∀ t σ, 0 ≤ Kn t σ) (hKnk : ∀ t σ, Kn t σ ≤ kh)
    (hPC4 : ContDiff ℝ (4 : ℕ) P)
    (hKnC4 : ContDiff ℝ (4 : ℕ) (uncurry Kn))
    (hXC4 : ContDiff ℝ (4 : ℕ) (uncurry Γ.X))
    (hVC4 : ContDiff ℝ (4 : ℕ) (uncurry V))
    (hAC4 : ContDiff ℝ (4 : ℕ) (uncurry A))
    (hslit : ∀ t, V t 0 ∈ Complex.slitPlane)
    (hm : ∀ t, Γ.m t ≤ M) :
    ∃ dn δ sf : ℝ → ℝ → ℝ,
      (∀ t, Function.Periodic (dn t) 1) ∧
      (∀ t σ, dn t σ ∈ Icc (0 : ℝ) (Real.arcsin kh)) ∧
      (∀ t σ, HasDerivAt (dn t) (P t * (Kn t σ - Real.sin (dn t σ))) σ) ∧
      (∀ t s, δ t s = dn t (s / P t)) ∧
      (∀ t x, rearArclength (δ t) (sf t x) = x) ∧
      ∃ Phi : ℝ → ℝ → ℝ,
        (∀ u, Phi 0 u = perim (SelectedInverseMap.selInv kh p) * u) ∧
        ((∀ t, Γ.eta t 0 = 0) → ∀ t, Phi t 0 = 0) ∧
        ∀ (q' : Data) (dPhi : ℝ → ℝ) {cq' kq' dq' : ℝ},
          0 < cq' → 0 < kq' → 0 < dq' → IsTubeMember cq' kq' dq' q' →
          (∀ u, HasDerivAt (Phi Γ.T) (dPhi u) u) →
          (∀ u, q'.1 u
            = (SelectedInverseMap.selInv kh q).1
                (Phi Γ.T u / perim (SelectedInverseMap.selInv kh q))) →
          MarkedShift.pathDistShift (SelectedInverseMap.selInv kh p)
              (SelectedInverseMap.selInv kh q) ≤ gaugeJacobiConst P0 P1 kh
                (M / Real.sqrt (1 - kh ^ 2) * (kh / Real.sqrt (1 - kh ^ 2)))
                ((M / Real.sqrt (1 - kh ^ 2) + M / Real.sqrt (1 - kh ^ 2))
                    * (kh / Real.sqrt (1 - kh ^ 2))
                  + M / Real.sqrt (1 - kh ^ 2) * (2 * kh / Real.sqrt (1 - kh ^ 2) ^ 3)) Γ.T
              (rearArclength (δ 0) (P 0)) * cost Γ := by
  refine SelectedInverseShiftPathRegularity.exists_steering_pathDistShift_selInv_le_pathSlit
    Γ (M := M) hc hkmin hp hub ?_ hcq hkminq hq hubq ?_ hP0 hkh0 hkh1 hPl hPu hV hA hAcont
    hspeed hXper hVper hAper hturn hnu hKeq hKnper hKn0 hKnk hPC4 hKnC4 hXC4 hVC4 hAC4
    hslit hm
  · exact RearTrackEmbedded.injOn_rearTrack_of_tube hc hkmin hkh0 hkh1 hp hub hturnp
  · exact RearTrackEmbedded.injOn_rearTrack_of_tube hcq hkminq hkh0 hkh1 hq hubq hturnq

end SelectedInverseShiftEmbedded
