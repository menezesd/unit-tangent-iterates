import Mathlib
import UnitTangentIterates.TurningNumberSelInv
import UnitTangentIterates.PathDataTaylorBounds
import UnitTangentIterates.FrontDataRegularity

/-!
# The marked path-distance bound for the selected inverses, with all
quantitative and global hypotheses produced

`TurningNumberSelInv.exists_pinched_pathDist_selInv_le` bounds the **marked**
path pseudodistance of the two marked selected inverses of the ends of a normal
path of fronts, when the marked point of the front is at rest along the path.
Its global hypotheses (embeddedness of the rear tracks, turning number of the
slices) are already produced there from the curvature pinching and the length
thresholds, but it still carries

* the two time derivatives `Kdn`, `Pd` of the normalized curvature and of the
  arclength period, together with six constants bounding them (sup, Lipschitz
  and first-order Taylor bounds), and
* the joint `C⁴` regularity of the front family and of its tangent angle.

Neither family of hypotheses has to be assumed, exactly as for the bound modulo
the marking:

* a normal path is at rest outside its time window
  (`PathDataTaylorBounds`), so the canonical time derivatives are bounded and
  the mean value inequality produces the six constants;
* the front family and its tangent angle are built from the position, the
  velocity, the acceleration and the period of the path, hence are as regular as
  those (`FrontDataRegularity`), the argument of the tangent at the marked point
  being regular as soon as that tangent never points in the negative real
  direction.

Main result: `exists_pinched_pathDist_selInv_le_regular`, the marked bound whose
hypotheses are only the tube data of the two ends with the length thresholds,
the curvature pinching `0 < kminK ≤ K̂ ≤ κ̂ < 1`, the geometry of the path and
the `C⁴` regularity of its data.
-/

noncomputable section

open Set Function Complex MeasureTheory MarkedSpace MarkedTopology PathMetric
  PathMetric.NormalPath RearTrack ArclengthInverse RearFamilyFrame RearOwnArclength
  RearOwnMotion

namespace MarkedSelInvRegular

open UniformFrameBounds GaugePathDistVariable RearOwnHigherRegularity
  FrontFromPath SelectedInverseRearOwn PathDataTaylorBounds FrontDataRegularity

variable {V A : ℝ → ℝ → ℂ} {Kn : ℝ → ℝ → ℝ} {P : ℝ → ℝ} {P0 P1 kh : ℝ}

/-- **The marked path-distance bound for the two selected inverses, with every
global and quantitative hypothesis produced.**

`TurningNumberSelInv.exists_pinched_pathDist_selInv_le` with the two time
derivatives of the front data and their six constants produced from the fact
that a normal path stands still outside its time window, and with the joint
regularity of the front family and of its tangent angle produced from the
regularity of the position, the velocity and the acceleration of the path.  As
there, the conclusion is a bound for the *marked* pseudodistance under the
geometric condition `∀ t, Γ.eta t 0 = 0` that the marked point of the front is
at rest along the path. -/
theorem exists_pinched_pathDist_selInv_le_regular {p q : Data} (Γ : NormalPath p q)
    {c kmin dlt cq kminq dltq kminK : ℝ}
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
    (hslit : ∀ t, V t 0 ∈ Complex.slitPlane) :
    ∃ dn δ sf : ℝ → ℝ → ℝ,
      (∀ t, Function.Periodic (dn t) 1) ∧
      (∀ t σ, dn t σ ∈ Icc (0 : ℝ) (Real.arcsin kh)) ∧
      (∀ t σ, HasDerivAt (dn t) (P t * (Kn t σ - Real.sin (dn t σ))) σ) ∧
      (∀ t s, δ t s = dn t (s / P t)) ∧
      (∀ t x, rearArclength (δ t) (sf t x) = x) ∧
      ∃ EF : ℝ, 0 ≤ EF ∧
        (∀ t s, |frontNormalVelocityAt (partialTime (frontOfPath Γ.X P))
          (angleOfPath V A P) δ t s| ≤ EF) ∧
        ∃ Phi : ℝ → ℝ → ℝ,
          (∀ u, Phi 0 u = perim (SelectedInverseMap.selInv kh p) * u) ∧
          ∀ (q' : Data) (dPhi : ℝ → ℝ) {cq' kq' dq' : ℝ},
            0 < cq' → 0 < kq' → 0 < dq' → IsTubeMember cq' kq' dq' q' →
            (∀ u, HasDerivAt (Phi Γ.T) (dPhi u) u) →
            (∀ u, q'.1 u
              = (SelectedInverseMap.selInv kh q).1
                  (Phi Γ.T u / perim (SelectedInverseMap.selInv kh q))) →
            (∀ t, Γ.eta t 0 = 0) →
            pathDist (SelectedInverseMap.selInv kh p) (SelectedInverseMap.selInv kh q)
              ≤ gaugeJacobiConst P0 P1 kh
                  (EF / Real.sqrt (1 - kh ^ 2) * (kh / Real.sqrt (1 - kh ^ 2)))
                  ((EF / Real.sqrt (1 - kh ^ 2) + EF / Real.sqrt (1 - kh ^ 2))
                      * (kh / Real.sqrt (1 - kh ^ 2))
                    + EF / Real.sqrt (1 - kh ^ 2) * (2 * kh / Real.sqrt (1 - kh ^ 2) ^ 3)) Γ.T
                (rearArclength (δ 0) (P 0)) * cost Γ := by
  have hT : (0:ℝ) ≤ Γ.T := Γ.T_pos.le
  have hPpos : ∀ t, 0 < P t := fun t => lt_of_lt_of_le hP0 (hPl t)
  have hPne : ∀ t, P t ≠ 0 := fun t => (hPpos t).ne'
  -- the front data of a normal path is at rest outside its time window
  have hPrest : ∀ t, P t = P (clampT 0 Γ.T t) := path_P_rest Γ hV hspeed
  have hKnrest : ∀ t σ, Kn t σ = Kn (clampT 0 Γ.T t) σ :=
    path_Kn_rest Γ hV hA hspeed hPpos hKeq
  -- the two time derivatives of the normalized curvature
  have hKnC1 : ContDiff ℝ 1 (uncurry Kn) := hKnC4.of_le (by norm_num)
  have hKnC3 : ContDiff ℝ (3 : ℕ) (uncurry Kn) := hKnC4.of_le (by norm_num)
  have hKdnC3 : ContDiff ℝ (3 : ℕ) (uncurry (partialT Kn)) :=
    contDiff_partialT (n := 3) (by exact_mod_cast hKnC4)
  have hKdnC1 : ContDiff ℝ 1 (uncurry (partialT Kn)) := hKdnC3.of_le (by norm_num)
  have hKddnC2 : ContDiff ℝ (2 : ℕ) (uncurry (partialT (partialT Kn))) :=
    contDiff_partialT (n := 2) (by exact_mod_cast hKdnC3)
  have hKdn_der : ∀ t σ, HasDerivAt (fun a => Kn a σ) (partialT Kn t σ) t :=
    fun t σ => hasDerivAt_partialT hKnC1 t σ
  have hKddn_der : ∀ t σ,
      HasDerivAt (fun a => partialT Kn a σ) (partialT (partialT Kn) t σ) t :=
    fun t σ => hasDerivAt_partialT hKdnC1 t σ
  have hKdnper : ∀ t, Function.Periodic (partialT Kn t) 1 := periodic_partialT hKnC1 hKnper
  have hKddnper : ∀ t, Function.Periodic (partialT (partialT Kn) t) 1 :=
    periodic_partialT hKdnC1 hKdnper
  have hKdnvan := partialT_vanishing_of_rest hT hKnC1 hKnrest
  have hKddnvan := partialT_vanishing_of_vanishing hKdnC1 hKdnvan
  obtain ⟨Md, CK, -, hCK0, hKdnbd, hKnlip, hKntaylor⟩ :=
    exists_lip_taylor_of_vanishing_periodic (T := Γ.T) hKdn_der hKddn_der
      hKdnC1.continuous hKddnC2.continuous hKdnper hKddnper hKdnvan hKddnvan
  -- the two time derivatives of the arclength period
  have hPC4' : ContDiff ℝ ((3 : ℕ) + 1) P := by exact_mod_cast hPC4
  have hPdC3 : ContDiff ℝ (3 : ℕ) (deriv P) := (contDiff_succ_iff_deriv.mp hPC4').2.2
  have hPdC3' : ContDiff ℝ ((2 : ℕ) + 1) (deriv P) := by exact_mod_cast hPdC3
  have hPddC2 : ContDiff ℝ (2 : ℕ) (deriv (deriv P)) := (contDiff_succ_iff_deriv.mp hPdC3').2.2
  have hP_der : ∀ t, HasDerivAt P (deriv P t) t := fun t =>
    (hPC4.differentiable (by norm_num) t).hasDerivAt
  have hPd_der : ∀ t, HasDerivAt (deriv P) (deriv (deriv P) t) t := fun t =>
    (hPdC3.differentiable (by norm_num) t).hasDerivAt
  have hPdvan := deriv_vanishing_of_rest hT hPrest
  have hPddvan := deriv_vanishing_of_vanishing hPdvan
  obtain ⟨MP, CP, -, hCP0, hPdbd, hPlip, hPtaylor⟩ :=
    exists_lip_taylor_of_vanishing (T := Γ.T) hT hP_der hPd_der hPdC3.continuous
      hPddC2.continuous hPdvan hPddvan
  -- the regularity of the front family and of its tangent angle
  have hFc4 : ContDiff ℝ (4 : ℕ) (uncurry (frontOfPath Γ.X P)) :=
    contDiff_frontOfPath (n := 4) hXC4 hPC4 hPne
  have hKc4 : ContDiff ℝ ((3 : ℕ) + 1) (uncurry (curvOfPath V A P)) := by
    have := contDiff_curvOfPath (n := 4) hVC4 hAC4 hPC4 hPne
    exact_mod_cast this
  have harg' : ContDiff ℝ ((3 : ℕ) + 1) fun t => (tangentOfPath V P t 0).arg := by
    have := contDiff_arg_tangentOfPath (n := 4) hVC4 hPC4 hPpos hslit
    exact_mod_cast this
  have hΘc4 : ContDiff ℝ (4 : ℕ) (uncurry (angleOfPath V A P)) := by
    have := contDiff_angleOfPath (n := 3) hKc4 harg'
    exact_mod_cast this
  exact TurningNumberSelInv.exists_pinched_pathDist_selInv_le Γ hc hkmin hp hub hshortp
    hcq hkminq hq hubq hshortq hP0 hkh0 hkh1 hPl hPu hV hA hAcont hspeed hXper hVper hAper
    hnu hKeq hKnper hKdnper hkminK hKnlow hKnk hPsmall hKdnbd hPdbd hKnlip hPlip hKntaylor
    hPtaylor hCK0 hCP0 hPC4 hPdC3 hKnC3 hKdnC3 hFc4 hΘc4

end MarkedSelInvRegular
