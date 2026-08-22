import Mathlib
import UnitTangentIterates.SelInvPathSteeringBaseC2
import UnitTangentIterates.SelInvPathTaylorFundamentalDriftC2

/-!
# The `C²` estimate with the time bounds of the front data produced

`SelInvPathSteeringBaseC2.dist_selInv_le_of_path_steering_base_C2` still carries, besides
the regularity of the data of the path, the block of *quantitative* hypotheses
describing how the front data moves in the time: the two time derivatives `Kdn`,
`Pd` of the normalized curvature and of the arclength period, their sup bounds
`Md`, `MP`, their Lipschitz constants `Klip`, `Plip` and their first-order
Taylor constants `CK`, `CP`.  None of these appears in the conclusion.

None of them has to be assumed.  A normal path stands still outside its time
window (`PathDataTaylorBounds.path_X_rest` and its consequences), so the front
data is constant in the time there; being periodic in the space variable it is
bounded, together with its time derivatives, on the whole plane, and the mean
value inequality produces the Lipschitz and Taylor bounds globally.  The time
derivatives themselves are the canonical partial derivatives `partialT Kn` and
`deriv P`.

This is the base-point form: besides the drift bound, the vanishing of the
tangential drift of the selected rears at the marked point is discharged too,
from the marked point of the path being at rest, `∀ t, Γ.eta t 0 = 0`.

Main result: `dist_selInv_le_of_path_taylor_base_C2`.
-/

noncomputable section

open Set Function Complex MeasureTheory MarkedSpace MarkedTopology PathMetric
  PathMetric.NormalPath RearTrack ArclengthInverse RearFamilyFrame RearOwnArclength
  RearOwnMotion

namespace SelInvPathTaylorBaseC2

open SelInvPathTaylorFundamentalDriftC2

open SelInvPathTaylorFundamentalC2

open SelInvPathTaylorC2

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
  SelInvPathRegularityC2 SelInvPathAngleC2 SelInvPathSteeringC2 PathDataTaylorBounds
  RearOwnTangential

variable {δ dn Kn : ℝ → ℝ → ℝ} {P : ℝ → ℝ} {P0 P1 kh : ℝ}

/-- **The `C²` comparison of the two marked selected inverses, with the
quantitative time bounds of the front data produced rather than assumed.**  The
hypotheses are those of
`SelInvPathSteeringBaseC2.dist_selInv_le_of_path_steering_base_C2` with the time
derivatives of the normalized curvature and of the arclength period taken to be
the canonical ones, and with their sup, Lipschitz and Taylor constants produced
from the regularity of the data together with the fact that a normal path
stands still outside its time window. -/
theorem dist_selInv_le_of_path_taylor_base_C2 {p q : Data} (Γ : NormalPath p q)
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
    (hdelta : ∀ t s, δ t s = dn t (s / P t))
    (hKeq : ∀ t s, curvOfPath (pathVel Γ.X) (pathAcc Γ.X) P t s = Kn t (s / P t))
    (hsol : ∀ t σ, HasDerivAt (dn t) (P t * (Kn t σ - Real.sin (dn t σ))) σ)
    (hstrip : ∀ t σ, dn t σ ∈ Icc (0 : ℝ) (Real.arcsin kh))
    (hdnper : ∀ t, Function.Periodic (dn t) 1) (hKnper : ∀ t, Function.Periodic (Kn t) 1)
    (hKnbd : ∀ t σ, |Kn t σ| ≤ kh)
    (hPC4 : ContDiff ℝ (4 : ℕ) P) (hKnC4 : ContDiff ℝ (4 : ℕ) (uncurry Kn))
    (hslit : ∀ t, pathVel Γ.X t 0 ∈ Complex.slitPlane)
    (hmark : ∀ t, Γ.eta t 0 = 0)
    -- the tangent-angle lift of the terminal marked selected inverse
    {kb kL : ℝ} {Θb kb' : ℝ → ℝ}
    (hevd : ∀ s, HasDerivAt (ev (SelectedInverseMap.selInv kh q))
      (Complex.exp (Complex.I * (Θb s : ℂ))) s)
    (hΘb : ∀ s, HasDerivAt Θb (kb' s) s) (hkbd : ∀ s, |kb' s| ≤ kb)
    (hklip : ∀ s t, |kb' s - kb' t| ≤ kL * |s - t|)
    -- the motion of the family of selected rears, in its own arclength
    {Pv0 khat : ℝ}
    (hkappa1 : rearKappa1 kh ≤ khat)
    -- the parameter derivative of the normal speed of the path
    (hetaC1 : ∀ t, ContDiff ℝ (1 : ℕ) (Γ.eta t))
    (hnumA : 2 + 2 * khat * (P1 * (kh / (1 - kh ^ 2))) ≤ 1 / Pv0)
    (hnumK : (jacobiSourceConst kh P0 + 2) + khat ^ 2 + 2 * (P1 * (kh / (1 - kh ^ 2))) * stripCurvConst kh
      ≤ 1 / Pv0 ^ 2 + khat ^ 2)
    -- the total cost of the family of selected rears, with the density chosen
    -- proportional to that of the fronts, is at most one
    (hsmall : RearCostDensity.rearCostConst kh khat (rearKappa2 kh)
      (rearArclength (δ 0) (P 0)) (jacobiSourceConst kh P0) * cost Γ ≤ 1) :
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
  have hT : (0:ℝ) ≤ Γ.T := Γ.T_pos.le
  have hPpos : ∀ t, 0 < P t := fun t => lt_of_lt_of_le hP0 (hPl t)
  have hXdiff : Differentiable ℝ (uncurry Γ.X) := hXC6.differentiable (by norm_num)
  have hV : ∀ t u, HasDerivAt (Γ.X t) (pathVel Γ.X t u) u := hasDerivAt_partialArc hXdiff
  have hVC5 : ContDiff ℝ (5 : ℕ) (uncurry (pathVel Γ.X)) :=
    contDiff_partialArc_self (n := 5) (by exact_mod_cast hXC6)
  have hVdiff : Differentiable ℝ (uncurry (pathVel Γ.X)) := hVC5.differentiable (by norm_num)
  have hA : ∀ t u, HasDerivAt (pathVel Γ.X t) (pathAcc Γ.X t u) u :=
    hasDerivAt_partialArc hVdiff
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
  exact SelInvPathSteeringBaseC2.dist_selInv_le_of_path_steering_base_C2 (Kdn := partialT Kn) (Pd := deriv P)
    Γ hc hkmin hp hub hinjR hcq hkminq hq hubq hinjRq hP0 hkh0 hkh1 hXC6 hPl hPu
    hspeed hXper hturn hnu hdelta hKeq hsol hstrip hdnper hKnper hKdnper
    hKnbd hKdnbd hPdbd hKnlip hPlip hKntaylor hPtaylor hCK0 hCP0 hPC4 hPdC3 hKnC3 hKdnC3
    hslit hmark hevd hΘb hkbd hklip
    hkappa1 hetaC1 hnumA hnumK hsmall

end SelInvPathTaylorBaseC2
