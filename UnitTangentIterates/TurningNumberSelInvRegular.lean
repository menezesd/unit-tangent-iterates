import Mathlib
import UnitTangentIterates.SelectedInverseShiftPathRegularity
import UnitTangentIterates.TurningNumberTube
import UnitTangentIterates.TurningNumberPath

/-!
# The shift bound for the marked selected inverses, with all global and
quantitative hypotheses produced

Two independent reductions of the shift bound for the marked selected inverses
of the two ends of a normal path of fronts are available in this project:

* `SelectedInverseShiftPathRegularity.exists_steering_pathDistShift_selInv_le_pathSlit`
  — the *quantitative* hypotheses are produced: the six constants describing
  how the front data moves in time (sup, Lipschitz and Taylor bounds of the
  time derivatives of the normalized curvature and of the arclength period) and
  the joint regularity of the front family and of its tangent angle all come
  from the regularity of the data of the path itself.  What it still assumes
  are the three *global* facts: embeddedness of every rear track of the two
  ends, and the turning number of the slices.
* `TurningNumberSelInv.exists_pinched_pathDistShift_selInv_le` — the three
  global facts are produced, from the curvature pinching together with the
  length threshold `κ̂·L < 4π`; but it is stated on the chain in which the six
  quantitative constants and the joint regularity are still hypotheses.

This file composes the two reductions, so that neither family of hypotheses is
assumed.  The turning number of every slice comes from
`TurningNumberPath.turning_of_path_of_pinched` and the embeddedness of the rear
tracks of the two ends from
`TurningNumberTube.injOn_rearTrack_of_tubeMember_of_short`, while the base
statement is the one in which the quantitative bounds are already produced.

Main result: `exists_pinched_pathDistShift_selInv_le_regular` — the shift bound
whose hypotheses are only:

* the tube data of the two ends, with their curvature at most `κ̂` and the
  length thresholds `κ̂ · perim < 4π`;
* the pinching `0 < kminK ≤ K̂ ≤ κ̂ < 1` of the normalized curvature along the
  path, with `κ̂ · P t < 4π`;
* the geometry of the path (constant speed `P t` with `P₀ ≤ P ≤ P₁`, unit
  period, normal motion) and the `C⁴` regularity of its data;
* the bound `Γ.m ≤ M` on the cost density.
-/

noncomputable section

open Set Function Complex MeasureTheory MarkedSpace MarkedTopology PathMetric
  PathMetric.NormalPath RearTrack ArclengthInverse RearFamilyFrame RearOwnArclength
  RearOwnMotion

namespace TurningNumberSelInvRegular

open UniformFrameBounds GaugePathDistVariable RearOwnHigherRegularity
  FrontFromPath SelectedInverseRearOwn

variable {V A : ℝ → ℝ → ℂ} {Kn : ℝ → ℝ → ℝ} {P : ℝ → ℝ} {P0 P1 kh : ℝ}

/-- **The shift bound for the marked selected inverses of the two ends of a
normal path, with every global and quantitative hypothesis produced.**

`SelectedInverseShiftPathRegularity.exists_steering_pathDistShift_selInv_le_pathSlit`
— in which the time bounds of the front data and the joint regularity of the
front family are already produced — with its three remaining global hypotheses
(embeddedness of the rear tracks of the two ends, turning number of the slices)
replaced by the curvature pinching `0 < kminK ≤ K̂ ≤ κ̂ < 1` and the length
thresholds `κ̂ · perim p < 4π`, `κ̂ · perim q < 4π`, `κ̂ · P t < 4π`. -/
theorem exists_pinched_pathDistShift_selInv_le_regular {p q : Data} (Γ : NormalPath p q)
    {c kmin dlt cq kminq dltq kminK M : ℝ}
    (hc : 0 < c) (hkmin : 0 < kmin) (hp : IsTubeMember c kmin dlt p)
    (hub : ∀ u, ((starRingEnd ℂ) (p.2.1 u) * p.2.2 u).im ≤ kh * ‖p.2.1 u‖ ^ 3)
    (hshortp : kh * perim p < 4 * Real.pi)
    (hcq : 0 < cq) (hkminq : 0 < kminq) (hq : IsTubeMember cq kminq dltq q)
    (hubq : ∀ u, ((starRingEnd ℂ) (q.2.1 u) * q.2.2 u).im ≤ kh * ‖q.2.1 u‖ ^ 3)
    (hshortq : kh * perim q < 4 * Real.pi)
    (hP0 : 0 < P0) (hkh0 : 0 ≤ kh) (hkh1 : kh < 1)
    (hPl : ∀ t, P0 ≤ P t) (hPu : ∀ t, P t ≤ P1)
    (hV : ∀ t u, HasDerivAt (Γ.X t) (V t u) u)
    (hA : ∀ t u, HasDerivAt (V t) (A t u) u)
    (hAcont : ∀ t, Continuous (A t))
    (hspeed : ∀ t u, ‖V t u‖ = P t)
    (hXper : ∀ t, Periodic (Γ.X t) 1) (hVper : ∀ t, Periodic (V t) 1)
    (hAper : ∀ t, Periodic (A t) 1)
    (hnu : ∀ t u, Γ.nu t u = Complex.I * (V t u / (P t : ℂ)))
    (hKeq : ∀ t s, curvOfPath V A P t s = Kn t (s / P t))
    (hKnper : ∀ t, Function.Periodic (Kn t) 1)
    (hkminK : 0 < kminK) (hKnlow : ∀ t σ, kminK ≤ Kn t σ) (hKnk : ∀ t σ, Kn t σ ≤ kh)
    (hPsmall : ∀ t, kh * P t < 4 * Real.pi)
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
  have hPpos : ∀ t, 0 < P t := fun t => lt_of_lt_of_le hP0 (hPl t)
  have hVcont : ∀ t, Continuous (V t) := fun t =>
    Differentiable.continuous fun u => (hA t u).differentiableAt
  have hturn : ∀ t, (∫ u in (0 : ℝ)..1, ((starRingEnd ℂ) (V t u) * A t u).im / P t ^ 2)
      = 2 * Real.pi :=
    TurningNumberPath.turning_of_path_of_pinched hA hVper hAper hVcont hAcont hspeed hPpos
      hkminK (fun t s => by rw [hKeq t s]; exact hKnlow t _)
      (fun t s => by rw [hKeq t s]; exact hKnk t _) hPsmall
  exact SelectedInverseShiftPathRegularity.exists_steering_pathDistShift_selInv_le_pathSlit
    Γ (M := M) hc hkmin hp hub
    (TurningNumberTube.injOn_rearTrack_of_tubeMember_of_short hc hkmin hkh1 hp hub hshortp)
    hcq hkminq hq hubq
    (TurningNumberTube.injOn_rearTrack_of_tubeMember_of_short hcq hkminq hkh1 hq hubq hshortq)
    hP0 hkh0 hkh1 hPl hPu hV hA hAcont hspeed hXper hVper hAper hturn hnu hKeq hKnper
    (fun t σ => le_trans hkminK.le (hKnlow t σ)) hKnk hPC4 hKnC4 hXC4 hVC4 hAC4 hslit hm

end TurningNumberSelInvRegular
