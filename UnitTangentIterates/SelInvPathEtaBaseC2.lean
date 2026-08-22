import Mathlib
import UnitTangentIterates.SelInvPathCurvBoundBaseC2
import UnitTangentIterates.SelInvPathEtaFundamentalDriftC2

/-!
# The `C²` estimate with the regularity of the normal speed discharged

`SelInvPathCurvBoundBaseC2.dist_selInv_le_modulus_of_path_curv_base_C2` still asks that
the normal speed of the path be `C¹` in the parameter at every time.  It need
not be assumed.  A normal path moves as `∂_tX = η ν` with `‖ν‖ = 1`, so the
normal speed is the normal component of the velocity,
`η = Re(∂_tX · conj ν)` (`eta_eq_re`); and along a path whose unit normal is the
standard one of its slices, `ν = i V / P`, both `∂_tX` and `V` are parameter
derivatives of the jointly `C⁶` moving curve, hence jointly `C⁵`, so `η` is `C¹`
in the parameter — indeed much better (`contDiff_eta_of_path`).

This is the base-point form: besides the drift bound, the vanishing of the
tangential drift of the selected rears at the marked point is discharged too,
from the marked point of the path being at rest, `∀ t, Γ.eta t 0 = 0`.

Main result: `dist_selInv_le_modulus_of_path_eta_base_C2`.
-/

noncomputable section

open Set Function Complex MeasureTheory MarkedSpace MarkedTopology PathMetric
  PathMetric.NormalPath RearTrack ArclengthInverse RearFamilyFrame RearOwnArclength
  RearOwnMotion

namespace SelInvPathEtaBaseC2

open SelInvPathEtaFundamentalDriftC2

open SelInvPathEtaFundamentalC2

open SelInvPathEtaC2

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
  SelInvPathCurvBoundC2 FrontDataRegularity RearOwnTangential

variable {P : ℝ → ℝ} {P0 P1 kh : ℝ}

/-- **The `C²` comparison of the two marked selected inverses, with the
regularity of the normal speed discharged.**  The hypotheses are those of
`SelInvPathCurvBoundBaseC2.dist_selInv_le_modulus_of_path_curv_base_C2` with the `C¹`
regularity of the normal speed in the parameter removed: it follows from the
joint `C⁶` regularity of the moving curve and the identification of the unit
normal. -/
theorem dist_selInv_le_modulus_of_path_eta_base_C2 {p q : Data} (Γ : NormalPath p q)
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
    (hPl : ∀ t, P0 ≤ P t) (hPu : ∀ t, P t ≤ P1)
    (hPdef : ∀ t, P t = ‖pathVel Γ.X t 0‖)
    (hconst : ∀ t u, ‖(pathVel Γ.X) t u‖ = ‖pathVel Γ.X t 0‖)
    (hXper : ∀ t, Periodic (Γ.X t) 1)
    (hturn : ∀ t, (∫ u in (0 : ℝ)..1, ((starRingEnd ℂ) ((pathVel Γ.X) t u) * (pathAcc Γ.X) t u).im / P t ^ 2)
      = 2 * Real.pi)
    (hnu : ∀ t u, Γ.nu t u = Complex.I * ((pathVel Γ.X) t u / (P t : ℂ)))
    (hKn0 : ∀ t σ, 0 ≤ pathKn Γ.X P t σ) (hKnk : ∀ t σ, pathKn Γ.X P t σ ≤ kh)
    (hslit : ∀ t, pathVel Γ.X t 0 ∈ Complex.slitPlane)
    (hmark : ∀ t, Γ.eta t 0 = 0) :
    ∃ dn δ : ℝ → ℝ → ℝ,
      (∀ t, Function.Periodic (dn t) 1) ∧
      (∀ t σ, dn t σ ∈ Icc (0 : ℝ) (Real.arcsin kh)) ∧
      (∀ t σ, HasDerivAt (dn t) (P t * (pathKn Γ.X P t σ - Real.sin (dn t σ))) σ) ∧
      (∀ t s, δ t s = dn t (s / P t)) ∧
      ∀ (Pv0 khat : ℝ),
        rearKappa1 kh ≤ khat →
        2 + 2 * khat * (P1 * (kh / (1 - kh ^ 2))) ≤ 1 / Pv0 →
        ((jacobiSourceConst kh P0 + 2) + khat ^ 2 + 2 * (P1 * (kh / (1 - kh ^ 2))) * stripCurvConst kh
          ≤ 1 / Pv0 ^ 2 + khat ^ 2) →
        RearCostDensity.rearCostConst kh khat (rearKappa2 kh)
            (rearArclength (δ 0) (P 0)) (jacobiSourceConst kh P0) * cost Γ ≤ 1 →
      dist (SelectedInverseMap.selInv kh q) (SelectedInverseMap.selInv kh p)
        ≤ selInvFrontModulus P1 kh (perim (SelectedInverseMap.selInv kh p))
            (perim (SelectedInverseMap.selInv kh q)) (kh / Real.sqrt (1 - kh ^ 2))
            (2 * kh / Real.sqrt (1 - kh ^ 2) ^ 3) Pv0 khat (jacobiSourceConst kh P0)
            (cost Γ) := by
  refine SelInvPathCurvBoundBaseC2.dist_selInv_le_modulus_of_path_curv_base_C2 Γ hc hkmin hp hturnp hcq hkminq hq hturnq
    hP0 hkh1 hXC6 hPl hPu hPdef hconst hXper hturn hnu hKn0 hKnk hslit hmark ?_
  intro t
  exact contDiff_eta_of_path (n := 1) Γ (hXC6.of_le (by norm_num)) hnu t

end SelInvPathEtaBaseC2
