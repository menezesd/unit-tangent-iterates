import Mathlib
import UnitTangentIterates.SelInvPathPeriodFundamentalC2
import UnitTangentIterates.SelInvPathEmbeddedC2

/-!
# The `C²` estimate with the embeddedness of the rear tracks discharged

`SelInvPathPeriodFundamentalC2.exists_steering_dist_selInv_le_of_path_period_fundamental_C2` carries,
at each of its two ends, the hypothesis that every steering solution on the
selected strip reconstructs an *embedded* rear track.
`RearTrackEmbedded.injOn_rearTrack_of_tube` proves that this holds for a member
of the tube whose front tangent angle turns by `2π`: on the selected strip the
rear tangent angle increases strictly, it increases by exactly `2π` over one
period, and a closed regular curve of turning number one is embedded.

The result below is therefore the same estimate with the two embeddedness
hypotheses replaced by the turning number of the two ends — a global topological
fact, carried as an explicit hypothesis here as everywhere in this project.

This is the fundamental-domain form: the bound on the tangential drift of the
family of selected rears is asked on one rear period only, and the drift is
asked to vanish at the marked point; no periodicity of the drift, hence no
rigidity of the rear arclength period, is assumed.

Main result: `exists_steering_dist_selInv_le_of_path_embedded_fundamental_C2`.
-/

noncomputable section

open Set Function Complex MeasureTheory MarkedSpace MarkedTopology PathMetric
  PathMetric.NormalPath RearTrack ArclengthInverse RearFamilyFrame RearOwnArclength
  RearOwnMotion

namespace SelInvPathEmbeddedFundamentalC2

open SelInvPathEmbeddedC2

open UniformFrameBounds GaugePathDistVariable RearOwnPathDistSmooth
  RearOwnHigherRegularity SelectedInverseJacobiODE RearOwnPathDistIntrinsic
  FrontFromPath SelectedInverseRearOwn SelectedInverseRearOwnTerminal
  MarkingDeviationC2 MarkingFlowDefectC2 RearOwnTangentialCostC2
  NormalPathC2IncrementVariableSpeed GaugeFlowVariableSpeedPath GaugeFlowDerivCost
  GaugeMarkedDataOfRearFamily GaugeFlowUniqueness FlowDerivative
  GaugeFlowTimeDerivative GaugeFlowSupJacobi SelInvFrontCostC2 RearJacobiSourceCost
  SelInvFrontSourceC2 SelInvFrontStripC2 SelInvFrontMotionC2 SelInvFrontMixedC2
  SelInvFrontJacobiC2 SelInvFrontVelocityC2 SelInvFrontRegularityC2
  SelInvFrontChangeVarC2 SelInvFrontClosingC2 SelInvFrontNormalSpeedC2
  SelInvPathRegularityC2 SelInvPathAngleC2 SelInvPathSteeringC2 SelInvPathTaylorC2
  SelInvPathSteeringExistsC2 SelInvPathCurvatureC2 SelInvPathPeriodC2
  FrontDataRegularity RearOwnTangential

variable {P : ℝ → ℝ} {P0 P1 kh : ℝ}

/-- **The `C²` comparison of the two marked selected inverses, with the
embeddedness of the rear tracks discharged.**  The hypotheses are those of
`SelInvPathPeriodFundamentalC2.exists_steering_dist_selInv_le_of_path_period_fundamental_C2` with the
two hypotheses asking every steering solution to reconstruct an embedded rear
track replaced by the turning number of the two ends. -/
theorem exists_steering_dist_selInv_le_of_path_embedded_fundamental_C2 {p q : Data} (Γ : NormalPath p q)
    {c kmin dlt cq kminq dltq : ℝ}
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
    (hXC6 : ContDiff ℝ (6 : ℕ) (uncurry Γ.X))
    (hPl : ∀ t, P0 ≤ P t) (hPu : ∀ t, P t ≤ P1)
    (hPdef : ∀ t, P t = ‖pathVel Γ.X t 0‖)
    (hconst : ∀ t u, ‖(pathVel Γ.X) t u‖ = ‖pathVel Γ.X t 0‖)
    (hXper : ∀ t, Periodic (Γ.X t) 1)
    (hturn : ∀ t, (∫ u in (0 : ℝ)..1, ((starRingEnd ℂ) ((pathVel Γ.X) t u) * (pathAcc Γ.X) t u).im / P t ^ 2)
      = 2 * Real.pi)
    (hnu : ∀ t u, Γ.nu t u = Complex.I * ((pathVel Γ.X) t u / (P t : ℂ)))
    (hKn0 : ∀ t σ, 0 ≤ pathKn Γ.X P t σ) (hKnk : ∀ t σ, pathKn Γ.X P t σ ≤ kh)
    (hslit : ∀ t, pathVel Γ.X t 0 ∈ Complex.slitPlane)
    (hmark : ∀ t, Γ.eta t 0 = 0)
    -- the tangent-angle lift of the terminal marked selected inverse
    {kb kL : ℝ} {Θb kb' : ℝ → ℝ}
    (hevd : ∀ s, HasDerivAt (ev (SelectedInverseMap.selInv kh q))
      (Complex.exp (Complex.I * (Θb s : ℂ))) s)
    (hΘb : ∀ s, HasDerivAt Θb (kb' s) s) (hkbd : ∀ s, |kb' s| ≤ kb)
    (hklip : ∀ s t, |kb' s - kb' t| ≤ kL * |s - t|)
    -- the parameter derivative of the normal speed of the path
    (hetaC1 : ∀ t, ContDiff ℝ (1 : ℕ) (Γ.eta t)) :
    ∃ dn δ : ℝ → ℝ → ℝ,
      (∀ t, Function.Periodic (dn t) 1) ∧
      (∀ t σ, dn t σ ∈ Icc (0 : ℝ) (Real.arcsin kh)) ∧
      (∀ t σ, HasDerivAt (dn t) (P t * (pathKn Γ.X P t σ - Real.sin (dn t σ))) σ) ∧
      (∀ t s, δ t s = dn t (s / P t)) ∧
      ∀ (Rb : ℝ → ℝ) (Pv0 khat rr : ℝ),
        rearKappa1 kh ≤ khat →
        (∀ t, ∀ x ∈ Icc (0 : ℝ) (rearArclength (δ t) (P t)),
          |frameTangential (rearOwnVelocity Γ.X (pathVel Γ.X) (pathAcc Γ.X) P δ (SelInvFrontChangeVarC2.rearArclengthInv δ)) (rearOwnAngle (angleOfPath (pathVel Γ.X) (pathAcc Γ.X) P) δ (SelInvFrontChangeVarC2.rearArclengthInv δ)) t x| ≤ Rb t) →
        (∀ t, Rb t ≤ rr * Γ.m t) → 0 ≤ rr →
        (∀ t, frameTangential (rearOwnVelocity Γ.X (pathVel Γ.X) (pathAcc Γ.X) P δ (SelInvFrontChangeVarC2.rearArclengthInv δ)) (rearOwnAngle (angleOfPath (pathVel Γ.X) (pathAcc Γ.X) P) δ (SelInvFrontChangeVarC2.rearArclengthInv δ)) t 0 = 0) →
        2 + 2 * khat * rr ≤ 1 / Pv0 →
        ((jacobiSourceConst kh P0 + 2) + khat ^ 2 + 2 * rr * stripCurvConst kh
          ≤ 1 / Pv0 ^ 2 + khat ^ 2) →
        RearCostDensity.rearCostConst kh khat (rearKappa2 kh)
            (rearArclength (δ 0) (P 0)) (jacobiSourceConst kh P0) * cost Γ ≤ 1 →
    perim (SelectedInverseMap.selInv kh p) = rearArclength (δ 0) (P 0) ∧
      perim (SelectedInverseMap.selInv kh q) = rearArclength (δ Γ.T) (P Γ.T) ∧
      ∃ Phi : ℝ → ℝ → ℝ,
        (∀ u, Phi 0 u = perim (SelectedInverseMap.selInv kh p) * u) ∧
        (∀ t, Phi t 0 = 0) ∧
        (∀ u t, HasDerivAt (fun r => Phi r u)
          (-frameTangential (rearOwnVelocity Γ.X (pathVel Γ.X) (pathAcc Γ.X) P δ (SelInvFrontChangeVarC2.rearArclengthInv δ)) (rearOwnAngle (angleOfPath (pathVel Γ.X) (pathAcc Γ.X) P) δ (SelInvFrontChangeVarC2.rearArclengthInv δ)) t (Phi t u)) t) ∧
        dist (SelectedInverseMap.selInv kh q) (SelectedInverseMap.selInv kh p)
            ≤ markingC2Bound (2 * P1 * (kh / (1 - kh ^ 2)) * cost Γ)
                (flowDefectC1Int (rearArclength (δ 0) (P 0)) (kh / (1 - kh ^ 2) * cost Γ))
                (flowDefectC2Int (rearArclength (δ 0) (P 0)) (kh / (1 - kh ^ 2) * cost Γ)
                  (gaugeGrowth2 kh * cost Γ))
                (rearArclength (δ Γ.T) (P Γ.T)) kb kL
              + c2ConstVar Pv0
                  (costP1 (rearArclength (δ 0) (P 0)) khat
                    (RearCostDensity.rearCostConst kh khat (rearKappa2 kh)
                      (rearArclength (δ 0) (P 0))
                    (jacobiSourceConst kh P0) * cost Γ)) khat
                  (costG1 (rearArclength (δ 0) (P 0)) khat (rearKappa2 kh)
                    (RearCostDensity.rearCostConst kh khat (rearKappa2 kh)
                    (rearArclength (δ 0) (P 0))
                    (jacobiSourceConst kh P0) * cost Γ))
                  (khat * costG1 (rearArclength (δ 0) (P 0)) khat (rearKappa2 kh)
                      (RearCostDensity.rearCostConst kh khat (rearKappa2 kh)
                    (rearArclength (δ 0) (P 0))
                    (jacobiSourceConst kh P0) * cost Γ)
                    + rearKappa2 kh * costP1 (rearArclength (δ 0) (P 0)) khat
                      (RearCostDensity.rearCostConst kh khat (rearKappa2 kh)
                    (rearArclength (δ 0) (P 0))
                    (jacobiSourceConst kh P0) * cost Γ) ^ 2)
                * (RearCostDensity.rearCostConst kh khat (rearKappa2 kh)
                    (rearArclength (δ 0) (P 0))
                    (jacobiSourceConst kh P0) * cost Γ)     := by
  refine SelInvPathPeriodFundamentalC2.exists_steering_dist_selInv_le_of_path_period_fundamental_C2
    Γ hc hkmin hp hub ?_ hcq hkminq hq hubq ?_ hP0 hkh0 hkh1 hXC6 hPl hPu
    hPdef hconst hXper hturn hnu hKn0 hKnk hslit hmark hevd hΘb hkbd hklip hetaC1
  · exact RearTrackEmbedded.injOn_rearTrack_of_tube hc hkmin hkh0 hkh1 hp hub hturnp
  · exact RearTrackEmbedded.injOn_rearTrack_of_tube hcq hkminq hkh0 hkh1 hq hubq hturnq

end SelInvPathEmbeddedFundamentalC2
