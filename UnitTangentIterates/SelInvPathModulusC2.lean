import Mathlib
import UnitTangentIterates.SelInvPathLiftC2

/-!
# The `C²` estimate for the selected inverse, as a modulus of the cost

`SelInvPathLiftC2.dist_selInv_le_of_path_lift_C2` bounds the marked distance of
the two marked selected inverses of the ends of a normal path of fronts by an
explicit expression in the cost of the path.  That expression is exactly the
modulus `SelInvFrontCostC2.selInvFrontModulus` of the cost
(`bound_eq_front_modulus`), and its two length parameters are the perimeters of
the two marked selected inverses, which the same statement identifies with the
rear arclength periods.

So the estimate reads: **the marked distance of the two marked selected inverses
is at most a fixed continuous function of the cost of the path, vanishing with
it**, the function depending only on the tube data, the perimeters of the two
images and the constants of the rear side.

Main results: `dist_selInv_le_modulus_of_path_C2`,
`tendsto_modulus_zero_of_path_C2`.
-/

noncomputable section

open Set Function Complex MeasureTheory MarkedSpace MarkedTopology PathMetric
  PathMetric.NormalPath RearTrack ArclengthInverse RearFamilyFrame RearOwnArclength
  RearOwnMotion

namespace SelInvPathModulusC2

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
  SelInvPathEmbeddedC2 SelInvPathLiftC2 SelInvTerminalLift FrontDataRegularity
  RearOwnTangential

variable {P : ℝ → ℝ} {P0 P1 kh : ℝ}

/-- **The `C²` comparison of the two marked selected inverses, in modulus
form.**  The bound of `SelInvPathLiftC2.dist_selInv_le_of_path_lift_C2` is the
modulus `selInvFrontModulus` evaluated at the cost of the path, with the two
length parameters the perimeters of the two marked selected inverses. -/
theorem dist_selInv_le_modulus_of_path_C2 {p q : Data} (Γ : NormalPath p q)
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
    -- the parameter derivative of the normal speed of the path
    (hetaC1 : ∀ t, ContDiff ℝ (1 : ℕ) (Γ.eta t)) :
    ∃ dn δ : ℝ → ℝ → ℝ,
      (∀ t, Function.Periodic (dn t) 1) ∧
      (∀ t σ, dn t σ ∈ Icc (0 : ℝ) (Real.arcsin kh)) ∧
      (∀ t σ, HasDerivAt (dn t) (P t * (pathKn Γ.X P t σ - Real.sin (dn t σ))) σ) ∧
      (∀ t s, δ t s = dn t (s / P t)) ∧
      ∀ (Rb : ℝ → ℝ) (Pv0 khat rr : ℝ),
        rearKappa1 kh ≤ khat →
        (∀ t x,
          |frameTangential (rearOwnVelocity Γ.X (pathVel Γ.X) (pathAcc Γ.X) P δ (SelInvFrontChangeVarC2.rearArclengthInv δ)) (rearOwnAngle (angleOfPath (pathVel Γ.X) (pathAcc Γ.X) P) δ (SelInvFrontChangeVarC2.rearArclengthInv δ)) t x| ≤ Rb t) →
        (∀ t, Rb t ≤ rr * Γ.m t) → 0 ≤ rr →
        2 + 2 * khat * rr ≤ 1 / Pv0 →
        ((jacobiSourceConst kh P0 + 2) + khat ^ 2 + 2 * rr * stripCurvConst kh
          ≤ 1 / Pv0 ^ 2 + khat ^ 2) →
        RearCostDensity.rearCostConst kh khat (rearKappa2 kh)
            (rearArclength (δ 0) (P 0)) (jacobiSourceConst kh P0) * cost Γ ≤ 1 →
      dist (SelectedInverseMap.selInv kh q) (SelectedInverseMap.selInv kh p)
        ≤ selInvFrontModulus P1 kh (perim (SelectedInverseMap.selInv kh p))
            (perim (SelectedInverseMap.selInv kh q)) (kh / Real.sqrt (1 - kh ^ 2))
            (2 * kh / Real.sqrt (1 - kh ^ 2) ^ 3) Pv0 khat (jacobiSourceConst kh P0)
            (cost Γ) := by
  obtain ⟨dn, δ, hdnper, hstrip, hsol, hdelta, hmain⟩ :=
    dist_selInv_le_of_path_lift_C2
      Γ hc hkmin hp hub hturnp hcq hkminq hq hubq hturnq hP0 hkh0 hkh1 hXC6 hPl hPu
      hPdef hconst hXper hturn hnu hKn0 hKnk hslit hmark hetaC1
  refine ⟨dn, δ, hdnper, hstrip, hsol, hdelta,
    fun Rb Pv0 khat rr hkappa1 hRbd hRbm hr hnumA hnumK hsmall => ?_⟩
  obtain ⟨hperp, hperq, -, -, -, -, hbound⟩ :=
    hmain Rb Pv0 khat rr hkappa1 hRbd hRbm hr hnumA hnumK hsmall
  rw [hperp, hperq]
  exact hbound

/-- **The bound tends to zero with the cost of the path**: the estimate is a
genuine modulus of continuity. -/
theorem tendsto_modulus_zero_of_path_C2 (P1 kh ell L Pv0 khat P0 : ℝ) :
    Filter.Tendsto
      (fun c : ℝ => selInvFrontModulus P1 kh ell L (kh / Real.sqrt (1 - kh ^ 2))
        (2 * kh / Real.sqrt (1 - kh ^ 2) ^ 3) Pv0 khat (jacobiSourceConst kh P0) c)
      (nhds 0) (nhds 0) :=
  tendsto_selInvFrontModulus_zero P1 kh ell L (kh / Real.sqrt (1 - kh ^ 2))
    (2 * kh / Real.sqrt (1 - kh ^ 2) ^ 3) Pv0 khat (jacobiSourceConst kh P0)

end SelInvPathModulusC2
