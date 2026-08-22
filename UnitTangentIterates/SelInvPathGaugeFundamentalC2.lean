import Mathlib
import UnitTangentIterates.SelInvPathPerimFundamentalC2
import UnitTangentIterates.SelInvPathGaugeC2

/-!
# The `C²` estimate with the numerical gauge constant produced

`SelInvPathPerimFundamentalC2.dist_selInv_le_modulus_of_path_perim_fundamental_C2` asks the caller for
a constant `Pv0` obeying two numerical inequalities.  Both say only that `Pv0`
is small enough, and both are satisfied by the explicit choice

`pathPv0 κ̂ P₀ κ r = min (1/(2+2κr)) (1/√(jacobiSourceConst κ̂ P₀ + 2 + 2r·stripCurvConst κ̂))`,

which is positive, so the estimate holds with that value and the two numerical
hypotheses removed.

This is the fundamental-domain form: the bound on the tangential drift of the
family of selected rears is asked on one rear period only, and the drift is
asked to vanish at the marked point; no periodicity of the drift, hence no
rigidity of the rear arclength period, is assumed.

Main result: `dist_selInv_le_modulus_of_path_gauge_fundamental_C2`.
-/

noncomputable section

open Set Function Complex MeasureTheory MarkedSpace MarkedTopology PathMetric
  PathMetric.NormalPath RearTrack ArclengthInverse RearFamilyFrame RearOwnArclength
  RearOwnMotion

namespace SelInvPathGaugeFundamentalC2

open SelInvPathGaugeC2

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
  SelInvPathEmbeddedC2 SelInvPathLiftC2 SelInvTerminalLift SelInvPathModulusC2
  SelInvPathCurvBoundC2 SelInvPathEtaC2 SelInvPathPerimC2 FrontDataRegularity
  RearOwnTangential

variable {P0 P1 kh khat rr : ℝ}

/-- **The `C²` comparison of the two marked selected inverses, with the gauge
constant produced rather than assumed.**  The hypotheses are those of
`SelInvPathPerimFundamentalC2.dist_selInv_le_modulus_of_path_perim_fundamental_C2` with the constant
`Pv0` and the two numerical conditions it had to satisfy replaced by the
explicit `pathPv0`. -/
theorem dist_selInv_le_modulus_of_path_gauge_fundamental_C2 {p q : Data} (Γ : NormalPath p q)
    {c kmin dlt cq kminq dltq : ℝ}
    (hc : 0 < c) (hkmin : 0 < kmin) (hp : IsTubeMember c kmin dlt p)
    (hturnp : ∃ Θ' K' : ℝ → ℝ,
      (∀ s, HasDerivAt (ev p) (Complex.exp (Complex.I * (Θ' s : ℂ))) s) ∧
      (∀ s, HasDerivAt Θ' (K' s) s) ∧
      (∀ s, Θ' (s + perim p) = Θ' s + 2 * Real.pi))
    (hcq : 0 < cq) (hkminq : 0 < kminq) (hq : IsTubeMember cq kminq dltq q)
    (hturnq : ∃ Θ' K' : ℝ → ℝ,
      (∀ s, HasDerivAt (ev q) (Complex.exp (Complex.I * (Θ' s : ℂ))) s) ∧
      (∀ s, HasDerivAt Θ' (K' s) s) ∧
      (∀ s, Θ' (s + perim q) = Θ' s + 2 * Real.pi))
    (hP0 : 0 < P0) (hkh1 : kh < 1)
    (hXC6 : ContDiff ℝ (6 : ℕ) (uncurry Γ.X))
    (hPl : ∀ t, P0 ≤ (pathPerim Γ.X) t) (hPu : ∀ t, (pathPerim Γ.X) t ≤ P1)
    (hconst : ∀ t u, ‖(pathVel Γ.X) t u‖ = ‖pathVel Γ.X t 0‖)
    (hXper : ∀ t, Periodic (Γ.X t) 1)
    (hturn : ∀ t, (∫ u in (0 : ℝ)..1, ((starRingEnd ℂ) ((pathVel Γ.X) t u) * (pathAcc Γ.X) t u).im / (pathPerim Γ.X) t ^ 2)
      = 2 * Real.pi)
    (hnu : ∀ t u, Γ.nu t u = Complex.I * ((pathVel Γ.X) t u / ((pathPerim Γ.X) t : ℂ)))
    (hKn0 : ∀ t σ, 0 ≤ pathKn Γ.X (pathPerim Γ.X) t σ) (hKnk : ∀ t σ, pathKn Γ.X (pathPerim Γ.X) t σ ≤ kh)
    (hslit : ∀ t, pathVel Γ.X t 0 ∈ Complex.slitPlane)
    (hmark : ∀ t, Γ.eta t 0 = 0) :
    ∃ dn δ : ℝ → ℝ → ℝ,
      (∀ t, Function.Periodic (dn t) 1) ∧
      (∀ t σ, dn t σ ∈ Icc (0 : ℝ) (Real.arcsin kh)) ∧
      (∀ t σ, HasDerivAt (dn t) ((pathPerim Γ.X) t * (pathKn Γ.X (pathPerim Γ.X) t σ - Real.sin (dn t σ))) σ) ∧
      (∀ t s, δ t s = dn t (s / (pathPerim Γ.X) t)) ∧
      ∀ (Rb : ℝ → ℝ) (khat rr : ℝ),
        rearKappa1 kh ≤ khat →
        (∀ t, ∀ x ∈ Icc (0 : ℝ) (rearArclength (δ t) (pathPerim Γ.X t)),
          |frameTangential (rearOwnVelocity Γ.X (pathVel Γ.X) (pathAcc Γ.X) (pathPerim Γ.X) δ (SelInvFrontChangeVarC2.rearArclengthInv δ)) (rearOwnAngle (angleOfPath (pathVel Γ.X) (pathAcc Γ.X) (pathPerim Γ.X)) δ (SelInvFrontChangeVarC2.rearArclengthInv δ)) t x| ≤ Rb t) →
        (∀ t, Rb t ≤ rr * Γ.m t) → 0 ≤ rr →
        (∀ t, frameTangential (rearOwnVelocity Γ.X (pathVel Γ.X) (pathAcc Γ.X) (pathPerim Γ.X) δ (SelInvFrontChangeVarC2.rearArclengthInv δ)) (rearOwnAngle (angleOfPath (pathVel Γ.X) (pathAcc Γ.X) (pathPerim Γ.X)) δ (SelInvFrontChangeVarC2.rearArclengthInv δ)) t 0 = 0) →
        RearCostDensity.rearCostConst kh khat (rearKappa2 kh)
            (rearArclength (δ 0) ((pathPerim Γ.X) 0)) (jacobiSourceConst kh P0) * cost Γ ≤ 1 →
      dist (SelectedInverseMap.selInv kh q) (SelectedInverseMap.selInv kh p)
        ≤ selInvFrontModulus P1 kh (perim (SelectedInverseMap.selInv kh p))
            (perim (SelectedInverseMap.selInv kh q)) (kh / Real.sqrt (1 - kh ^ 2))
            (2 * kh / Real.sqrt (1 - kh ^ 2) ^ 3) (pathPv0 kh P0 khat rr) khat (jacobiSourceConst kh P0)
            (cost Γ) := by
  obtain ⟨dn, δ, hdnper, hstrip, hsol, hdel, hmain⟩ :=
    SelInvPathPerimFundamentalC2.dist_selInv_le_modulus_of_path_perim_fundamental_C2 Γ hc hkmin hp hturnp hcq hkminq hq hturnq
      hP0 hkh1 hXC6 hPl hPu hconst hXper hturn hnu hKn0 hKnk hslit hmark
  refine ⟨dn, δ, hdnper, hstrip, hsol, hdel,
    fun Rb khat rr hkappa1 hRbd hRbm hr hxi0 hsmall => ?_⟩
  have hkh0 : 0 ≤ kh := le_trans (hKn0 0 0) (hKnk 0 0)
  have hkhat : 0 ≤ khat := le_trans (rearKappa1_nonneg hkh0 hkh1) hkappa1
  exact hmain Rb (pathPv0 kh P0 khat rr) khat rr hkappa1 hRbd hRbm hr hxi0
    (pathPv0_numA hP0 hkh0 hkhat hr) (pathPv0_numK hP0 hkh0 hkhat hr) hsmall

end SelInvPathGaugeFundamentalC2
