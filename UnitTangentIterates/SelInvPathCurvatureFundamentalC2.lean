import Mathlib
import UnitTangentIterates.SelInvPathSteeringExistsFundamentalC2
import UnitTangentIterates.SelInvPathCurvatureC2

/-!
# The `C²` estimate with the normalized curvature of the slices produced

`SelInvPathSteeringExistsFundamentalC2.exists_steering_dist_selInv_le_of_path_fundamental_C2` still
carries the normalized curvature `K̂` of the slices as a datum, linked to the
path by `curvOfPath V A P (t, s) = K̂(t, s / P t)` and assumed periodic and
jointly `C⁴`.  It is of course determined by the path: `K̂(t,σ)` is the
curvature of the slice at the point of normalized parameter `σ`.

This file takes it to be that — `pathKn X P t σ = curvOfPath (pathVel X)
(pathAcc X) P t (σ · P t)` — and proves the three hypotheses: the change of
variable is inverse to the one of `curvOfPath`, the curvature of a `1`-periodic
slice is `1`-periodic in the normalized parameter, and the regularity follows
from that of the path.  What is left of the curvature is only the geometric
pinching `0 ≤ K̂ ≤ κ̂`.

This is the fundamental-domain form: the bound on the tangential drift of the
family of selected rears is asked on one rear period only, and the drift is
asked to vanish at the marked point; no periodicity of the drift, hence no
rigidity of the rear arclength period, is assumed.

Main result: `exists_steering_dist_selInv_le_of_path_curvature_fundamental_C2`.
-/

noncomputable section

open Set Function Complex MeasureTheory MarkedSpace MarkedTopology PathMetric
  PathMetric.NormalPath RearTrack ArclengthInverse RearFamilyFrame RearOwnArclength
  RearOwnMotion

namespace SelInvPathCurvatureFundamentalC2

open SelInvPathCurvatureC2

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
  SelInvPathSteeringExistsC2 FrontDataRegularity RearOwnTangential

variable {P : ℝ → ℝ} {P0 P1 kh : ℝ}

/-- **The `C²` comparison of the two marked selected inverses, with the
normalized curvature of the slices produced from the path.**  The hypotheses are
those of
`SelInvPathSteeringExistsFundamentalC2.exists_steering_dist_selInv_le_of_path_fundamental_C2` with the
normalized curvature taken to be the curvature of the slices in the normalized
parameter, so that its link with the path, its periodicity and its regularity
are all automatic; the pinching `0 ≤ K̂ ≤ κ̂` remains, as a condition on the
curvature of the slices. -/
theorem exists_steering_dist_selInv_le_of_path_curvature_fundamental_C2 {p q : Data} (Γ : NormalPath p q)
    {c kmin dlt cq kminq dltq : ℝ}
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
    (hXC6 : ContDiff ℝ (6 : ℕ) (uncurry Γ.X))
    (hPl : ∀ t, P0 ≤ P t) (hPu : ∀ t, P t ≤ P1)
    (hspeed : ∀ t u, ‖(pathVel Γ.X) t u‖ = P t)
    (hXper : ∀ t, Periodic (Γ.X t) 1)
    (hturn : ∀ t, (∫ u in (0 : ℝ)..1, ((starRingEnd ℂ) ((pathVel Γ.X) t u) * (pathAcc Γ.X) t u).im / P t ^ 2)
      = 2 * Real.pi)
    (hnu : ∀ t u, Γ.nu t u = Complex.I * ((pathVel Γ.X) t u / (P t : ℂ)))
    (hKn0 : ∀ t σ, 0 ≤ pathKn Γ.X P t σ) (hKnk : ∀ t σ, pathKn Γ.X P t σ ≤ kh)
    (hPC4 : ContDiff ℝ (4 : ℕ) P)
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
  have hPpos : ∀ t, 0 < P t := fun t => lt_of_lt_of_le hP0 (hPl t)
  have hPne : ∀ t, P t ≠ 0 := fun t => (hPpos t).ne'
  have hXdiff : Differentiable ℝ (uncurry Γ.X) := hXC6.differentiable (by norm_num)
  have hVC5 : ContDiff ℝ (5 : ℕ) (uncurry (pathVel Γ.X)) :=
    contDiff_partialArc_self (n := 5) (by exact_mod_cast hXC6)
  have hVC4 : ContDiff ℝ (4 : ℕ) (uncurry (pathVel Γ.X)) :=
    hVC5.of_le (by exact_mod_cast (by norm_num : (4 : ℕ) ≤ 5))
  have hVdiff : Differentiable ℝ (uncurry (pathVel Γ.X)) := hVC5.differentiable (by norm_num)
  have hAC4 : ContDiff ℝ (4 : ℕ) (uncurry (pathAcc Γ.X)) :=
    contDiff_partialArc_self (n := 4) (by exact_mod_cast hVC5)
  have hVper : ∀ t, Function.Periodic (pathVel Γ.X t) 1 :=
    SelInvPathRegularityC2.periodic_partialArc hXdiff hXper
  have hAper : ∀ t, Function.Periodic (pathAcc Γ.X t) 1 :=
    SelInvPathRegularityC2.periodic_partialArc hVdiff hVper
  exact SelInvPathSteeringExistsFundamentalC2.exists_steering_dist_selInv_le_of_path_fundamental_C2 (Kn := pathKn Γ.X P)
    Γ hc hkmin hp hub hinjR hcq hkminq hq hubq hinjRq hP0 hkh0 hkh1 hXC6 hPl hPu
    hspeed hXper hturn hnu (curvOfPath_eq_pathKn hPne)
    (periodic_pathKn hPne hVper hAper) hKn0 hKnk hPC4
    (contDiff_pathKn (n := 4) hPne hVC4 hAC4 hPC4) hslit hmark hevd hΘb hkbd hklip hetaC1

end SelInvPathCurvatureFundamentalC2
