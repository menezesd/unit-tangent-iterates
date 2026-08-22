import Mathlib
import UnitTangentIterates.SelectedInverseShiftTaylor
import UnitTangentIterates.FrontDataRegularity

/-!
# The shift bound with the regularity of the front data reduced to that of the path

`SelectedInverseShiftTaylor.exists_steering_pathDistShift_selInv_le_regular` asks
the front family `F(t,s) = X(t, s/P t)` of the path and its tangent angle
`Θ(t,s)` to be jointly `C⁴`.  Neither is data of the path: the front is the
slice reparametrized by its own arclength and the angle is the primitive of the
curvature normalized at the marked point, both being built from the position,
the velocity, the acceleration and the arclength period.

`FrontDataRegularity` derives the regularity of the two from that of the path.
This file feeds it into the bound: the result below is the same bound with the
two hypotheses on the front data replaced by the joint `C⁴` regularity of the
position, the velocity and the acceleration of the path.

The one piece that does not reduce is the argument of the tangent at the marked
point, which stays as an explicit hypothesis `harg`: the complex argument has no
global continuous branch, so a path whose marked tangent crosses the negative
real axis has no regular normalization of this form, and choosing one is a
genuine extra piece of data.  The second result below replaces that hypothesis
by the geometric condition that the marked tangent never points in the negative
real direction, which is exactly the condition making the principal branch
regular along the path.

Main results: `exists_steering_pathDistShift_selInv_le_pathRegular` and
`exists_steering_pathDistShift_selInv_le_pathSlit`.
-/

noncomputable section

open Set Function Complex MeasureTheory MarkedSpace MarkedTopology PathMetric
  PathMetric.NormalPath RearTrack ArclengthInverse RearFamilyFrame RearOwnArclength
  RearOwnMotion

namespace SelectedInverseShiftPathRegularity

open UniformFrameBounds GaugePathDistVariable RearOwnHigherRegularity
  FrontFromPath SelectedInverseRearOwn PathDataTaylorBounds FrontDataRegularity

variable {V A : ℝ → ℝ → ℂ} {Kn : ℝ → ℝ → ℝ} {P : ℝ → ℝ} {P0 P1 kh : ℝ}

/-- **The shift bound for the marked selected inverses of the two ends of a
normal path, with the regularity of the front data reduced to that of the
path.**

Same statement as
`SelectedInverseShiftTaylor.exists_steering_pathDistShift_selInv_le_regular`,
with the joint `C⁴` regularity of the front family and of its tangent angle
replaced by that of the position, the velocity and the acceleration of the
path, together with a branch hypothesis for the argument of the tangent at the
marked point. -/
theorem exists_steering_pathDistShift_selInv_le_pathRegular {p q : Data} (Γ : NormalPath p q)
    {c kmin dlt cq kminq dltq M : ℝ}
    (hc : 0 < c) (hkmin : 0 < kmin) (hp : IsTubeMember c kmin dlt p)
    (hub : ∀ u, ((starRingEnd ℂ) (p.2.1 u) * p.2.2 u).im ≤ kh * ‖p.2.1 u‖ ^ 3)
    (hinjR : ∀ Θ' K' dl : ℝ → ℝ,
      (∀ s, HasDerivAt (ev p) (Complex.exp (Complex.I * (Θ' s : ℂ))) s) →
      (∀ s, HasDerivAt Θ' (K' s) s) →
      Function.Periodic dl (perim p) →
      (∀ s, dl s ∈ Icc 0 (Real.arcsin kh)) →
      (∀ s, HasDerivAt dl (K' s - Real.sin (dl s)) s) →
      InjOn (rearTrack (ev p) Θ' dl) (Ico 0 (perim p)))
    (hcq : 0 < cq) (hkminq : 0 < kminq) (hq : IsTubeMember cq kminq dltq q)
    (hubq : ∀ u, ((starRingEnd ℂ) (q.2.1 u) * q.2.2 u).im ≤ kh * ‖q.2.1 u‖ ^ 3)
    (hinjRq : ∀ Θ' K' dl : ℝ → ℝ,
      (∀ s, HasDerivAt (ev q) (Complex.exp (Complex.I * (Θ' s : ℂ))) s) →
      (∀ s, HasDerivAt Θ' (K' s) s) →
      Function.Periodic dl (perim q) →
      (∀ s, dl s ∈ Icc 0 (Real.arcsin kh)) →
      (∀ s, HasDerivAt dl (K' s - Real.sin (dl s)) s) →
      InjOn (rearTrack (ev q) Θ' dl) (Ico 0 (perim q)))
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
    (harg : ContDiff ℝ (4 : ℕ) fun t => (tangentOfPath V P t 0).arg)
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
  have hPne : ∀ t, P t ≠ 0 := fun t => (lt_of_lt_of_le hP0 (hPl t)).ne'
  have hFc4 : ContDiff ℝ (4 : ℕ) (uncurry (frontOfPath Γ.X P)) :=
    contDiff_frontOfPath (n := 4) hXC4 hPC4 hPne
  have hKc4 : ContDiff ℝ ((3 : ℕ) + 1) (uncurry (curvOfPath V A P)) := by
    have := contDiff_curvOfPath (n := 4) hVC4 hAC4 hPC4 hPne
    exact_mod_cast this
  have harg' : ContDiff ℝ ((3 : ℕ) + 1) fun t => (tangentOfPath V P t 0).arg := by
    exact_mod_cast harg
  have hΘc4 : ContDiff ℝ (4 : ℕ) (uncurry (angleOfPath V A P)) := by
    have := contDiff_angleOfPath (n := 3) hKc4 harg'
    exact_mod_cast this
  exact SelectedInverseShiftTaylor.exists_steering_pathDistShift_selInv_le_regular
    Γ (M := M) hc hkmin hp hub hinjR hcq hkminq hq hubq hinjRq hP0 hkh0 hkh1 hPl hPu hV hA
    hAcont hspeed hXper hVper hAper hturn hnu hKeq hKnper hKn0 hKnk hPC4 hKnC4 hFc4 hΘc4 hm

/-- **The shift bound for the marked selected inverses of the two ends of a
normal path, with the branch hypothesis replaced by a geometric condition.**

Same statement as `exists_steering_pathDistShift_selInv_le_pathRegular`, with
the regularity of the argument of the tangent at the marked point replaced by
the geometric condition that this tangent never points in the negative real
direction, so that the principal branch of the argument is a regular
normalization along the whole path. -/
theorem exists_steering_pathDistShift_selInv_le_pathSlit {p q : Data} (Γ : NormalPath p q)
    {c kmin dlt cq kminq dltq M : ℝ}
    (hc : 0 < c) (hkmin : 0 < kmin) (hp : IsTubeMember c kmin dlt p)
    (hub : ∀ u, ((starRingEnd ℂ) (p.2.1 u) * p.2.2 u).im ≤ kh * ‖p.2.1 u‖ ^ 3)
    (hinjR : ∀ Θ' K' dl : ℝ → ℝ,
      (∀ s, HasDerivAt (ev p) (Complex.exp (Complex.I * (Θ' s : ℂ))) s) →
      (∀ s, HasDerivAt Θ' (K' s) s) →
      Function.Periodic dl (perim p) →
      (∀ s, dl s ∈ Icc 0 (Real.arcsin kh)) →
      (∀ s, HasDerivAt dl (K' s - Real.sin (dl s)) s) →
      InjOn (rearTrack (ev p) Θ' dl) (Ico 0 (perim p)))
    (hcq : 0 < cq) (hkminq : 0 < kminq) (hq : IsTubeMember cq kminq dltq q)
    (hubq : ∀ u, ((starRingEnd ℂ) (q.2.1 u) * q.2.2 u).im ≤ kh * ‖q.2.1 u‖ ^ 3)
    (hinjRq : ∀ Θ' K' dl : ℝ → ℝ,
      (∀ s, HasDerivAt (ev q) (Complex.exp (Complex.I * (Θ' s : ℂ))) s) →
      (∀ s, HasDerivAt Θ' (K' s) s) →
      Function.Periodic dl (perim q) →
      (∀ s, dl s ∈ Icc 0 (Real.arcsin kh)) →
      (∀ s, HasDerivAt dl (K' s - Real.sin (dl s)) s) →
      InjOn (rearTrack (ev q) Θ' dl) (Ico 0 (perim q)))
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
  have hPpos : ∀ t, 0 < P t := fun t => lt_of_lt_of_le hP0 (hPl t)
  refine exists_steering_pathDistShift_selInv_le_pathRegular Γ (M := M) hc hkmin hp hub hinjR
    hcq hkminq hq hubq hinjRq hP0 hkh0 hkh1 hPl hPu hV hA hAcont hspeed hXper hVper hAper
    hturn hnu hKeq hKnper hKn0 hKnk hPC4 hKnC4 hXC4 hVC4 hAC4 ?_ hm
  exact contDiff_arg_tangentOfPath (n := 4) hVC4 hPC4 hPpos hslit

end SelectedInverseShiftPathRegularity
