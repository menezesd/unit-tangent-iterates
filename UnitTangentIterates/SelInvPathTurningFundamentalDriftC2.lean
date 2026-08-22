import Mathlib
import UnitTangentIterates.SelInvPathBoundsFundamentalDriftC2
import UnitTangentIterates.SelInvPathTurningFundamentalC2

/-!
# The `C²` estimate with the turning numbers discharged

`SelInvPathBoundsFundamentalDriftC2.exists_bounds_dist_selInv_le_modulus_of_path_fundamental_drift_C2` still
carries three global topological hypotheses: that the tangent angle of each
slice of the path increases by `2π` over one period, and that the tangent angle
of each of the two ends does.  None of them has to be assumed when the slices
are short and their curvature is pinched away from zero.

The turning of a closed slice is quantized in `2π`
(`FrontFromPath.exists_int_turning`), and the total curvature of a slice lies in
`(0, 4π)` as soon as `0 < kmin ≤ K ≤ κ̂` and `κ̂·L < 4π`; so the turning number
is one (`turning_of_slice`).  At the two ends the same argument is already
available in the form of `TurningNumberTube.turning_of_tubeMember_of_short`.

This is the fundamental-domain form, with the drift bound discharged: the
tangential drift of the family of selected rears is controlled over one rear
period by `P₁·κ̂/(1−κ̂²)` times the normal speed of the path, so no bound on it
is left to the caller.

Main result: `dist_selInv_le_modulus_of_path_turning_fundamental_drift_C2`.
-/

noncomputable section

open Set Function Complex MeasureTheory MarkedSpace MarkedTopology PathMetric
  PathMetric.NormalPath RearTrack ArclengthInverse RearFamilyFrame RearOwnArclength
  RearOwnMotion

namespace SelInvPathTurningFundamentalDriftC2

open SelInvPathTurningFundamentalC2

open SelInvPathTurningC2

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
  SelInvPathCurvBoundC2 SelInvPathEtaC2 SelInvPathPerimC2 SelInvPathGaugeC2
  SelInvPathBoundsC2 TurningNumberTube PathDataTaylorBounds FrontDataRegularity
  RearOwnTangential

variable {kh : ℝ}

/-- **The `C²` comparison of the two marked selected inverses, with the turning
numbers discharged.**  The hypotheses are those of
`SelInvPathBoundsFundamentalDriftC2.exists_bounds_dist_selInv_le_modulus_of_path_fundamental_drift_C2` with the
turning number of the slices and of the two ends removed, in exchange for a
strictly positive lower bound on the curvature of the slices and the length
threshold `κ̂·L < 4π`. -/
theorem dist_selInv_le_modulus_of_path_turning_fundamental_drift_C2 {p q : Data} (Γ : NormalPath p q)
    {c kmin dlt cq kminq dltq kminP : ℝ}
    (hc : 0 < c) (hkmin : 0 < kmin) (hp : IsTubeMember c kmin dlt p)
    (hcq : 0 < cq) (hkminq : 0 < kminq) (hq : IsTubeMember cq kminq dltq q)
    (hkh1 : kh < 1)
    (hXC6 : ContDiff ℝ (6 : ℕ) (uncurry Γ.X))
    (hconst : ∀ t u, ‖(pathVel Γ.X) t u‖ = ‖pathVel Γ.X t 0‖)
    (hXper : ∀ t, Periodic (Γ.X t) 1)
    (hnu : ∀ t u, Γ.nu t u = Complex.I * ((pathVel Γ.X) t u / ((pathPerim Γ.X) t : ℂ)))
    (hkminP : 0 < kminP)
    (hKnmin : ∀ t σ, kminP ≤ pathKn Γ.X (pathPerim Γ.X) t σ)
    (hKnk : ∀ t σ, pathKn Γ.X (pathPerim Γ.X) t σ ≤ kh)
    (hshort : ∀ t, kh * pathPerim Γ.X t < 4 * Real.pi)
    (hslit : ∀ t, pathVel Γ.X t 0 ∈ Complex.slitPlane)
    (hmark : ∀ t, Γ.eta t 0 = 0) :
    ∃ P0 P1 : ℝ, 0 < P0 ∧ (∀ t, P0 ≤ pathPerim Γ.X t) ∧
      (∀ t, pathPerim Γ.X t ≤ P1) ∧
    ∃ dn δ : ℝ → ℝ → ℝ,
      (∀ t, Function.Periodic (dn t) 1) ∧
      (∀ t σ, dn t σ ∈ Icc (0 : ℝ) (Real.arcsin kh)) ∧
      (∀ t σ, HasDerivAt (dn t) ((pathPerim Γ.X) t * (pathKn Γ.X (pathPerim Γ.X) t σ - Real.sin (dn t σ))) σ) ∧
      (∀ t s, δ t s = dn t (s / (pathPerim Γ.X) t)) ∧
      ∀ (khat : ℝ),
        rearKappa1 kh ≤ khat →
        (∀ t, frameTangential (rearOwnVelocity Γ.X (pathVel Γ.X) (pathAcc Γ.X) (pathPerim Γ.X) δ (SelInvFrontChangeVarC2.rearArclengthInv δ)) (rearOwnAngle (angleOfPath (pathVel Γ.X) (pathAcc Γ.X) (pathPerim Γ.X)) δ (SelInvFrontChangeVarC2.rearArclengthInv δ)) t 0 = 0) →
        RearCostDensity.rearCostConst kh khat (rearKappa2 kh)
            (rearArclength (δ 0) ((pathPerim Γ.X) 0)) (jacobiSourceConst kh P0) * cost Γ ≤ 1 →
      dist (SelectedInverseMap.selInv kh q) (SelectedInverseMap.selInv kh p)
        ≤ selInvFrontModulus P1 kh (perim (SelectedInverseMap.selInv kh p))
            (perim (SelectedInverseMap.selInv kh q)) (kh / Real.sqrt (1 - kh ^ 2))
            (2 * kh / Real.sqrt (1 - kh ^ 2) ^ 3) (pathPv0 kh P0 khat (P1 * (kh / (1 - kh ^ 2)))) khat (jacobiSourceConst kh P0)
            (cost Γ) := by
  have hXdiff : Differentiable ℝ (uncurry Γ.X) := hXC6.differentiable (by norm_num)
  have hX2 : ContDiff ℝ (2 : ℕ) (uncurry Γ.X) := hXC6.of_le (by norm_num)
  have hVC : ContDiff ℝ ((1 + 1 : ℕ)) (uncurry (pathVel Γ.X)) :=
    contDiff_partialArc_self (n := 2) (hXC6.of_le (by norm_num))
  have hVdiff : Differentiable ℝ (uncurry (pathVel Γ.X)) := hVC.differentiable (by norm_num)
  have hAC : ContDiff ℝ (1 : ℕ) (uncurry (pathAcc Γ.X)) :=
    contDiff_partialArc_self (n := 1) hVC
  have hPpos : ∀ t, 0 < pathPerim Γ.X t :=
    fun t => norm_pos_iff.2 (Complex.slitPlane_ne_zero (hslit t))
  have hPne : ∀ t, pathPerim Γ.X t ≠ 0 := fun t => (hPpos t).ne'
  have hVper : ∀ t, Periodic (pathVel Γ.X t) 1 := periodic_partialArc hXdiff hXper
  have hAper : ∀ t, Periodic (pathAcc Γ.X t) 1 := periodic_partialArc hVdiff hVper
  have hslice : ∀ t : ℝ, Continuous fun u : ℝ => ((t, u) : ℝ × ℝ) :=
    fun t => continuous_const.prodMk continuous_id
  have hVcont : ∀ t, Continuous (pathVel Γ.X t) :=
    fun t => hVC.continuous.comp (hslice t)
  have hAcont : ∀ t, Continuous (pathAcc Γ.X t) :=
    fun t => hAC.continuous.comp (hslice t)
  have hAderiv : ∀ t u, HasDerivAt (pathVel Γ.X t) (pathAcc Γ.X t u) u :=
    fun t u => hasDerivAt_partialArc hVdiff t u
  have hlowc : ∀ t s, kminP ≤ curvOfPath (pathVel Γ.X) (pathAcc Γ.X) (pathPerim Γ.X) t s :=
    fun t s => by rw [curvOfPath_eq_pathKn hPne t s]; exact hKnmin t _
  have hhighc : ∀ t s, curvOfPath (pathVel Γ.X) (pathAcc Γ.X) (pathPerim Γ.X) t s ≤ kh :=
    fun t s => by rw [curvOfPath_eq_pathKn hPne t s]; exact hKnk t _
  have hKn0 : ∀ t σ, 0 ≤ pathKn Γ.X (pathPerim Γ.X) t σ :=
    fun t σ => le_trans hkminP.le (hKnmin t σ)
  have hturn : ∀ t, (∫ u in (0 : ℝ)..1,
      ((starRingEnd ℂ) ((pathVel Γ.X) t u) * (pathAcc Γ.X) t u).im / pathPerim Γ.X t ^ 2)
      = 2 * Real.pi :=
    fun t => turning_of_slice (hAderiv t) (hVper t) (hAper t) (hVcont t) (hAcont t)
      (fun u => hconst t u) (hPpos t) hkminP (hlowc t) (hhighc t) (hshort t)
  -- the two ends
  have hubp : ∀ u, ((starRingEnd ℂ) (p.2.1 u) * p.2.2 u).im ≤ kh * ‖p.2.1 u‖ ^ 3 :=
    fun u => curv_le_of_slice hX2 (hPne 0) rfl (hconst 0) (hKnk 0)
      (fun u => Γ.start u) hp.hasDerivAt_curve hp.hasDerivAt_vel u
  have hubq : ∀ u, ((starRingEnd ℂ) (q.2.1 u) * q.2.2 u).im ≤ kh * ‖q.2.1 u‖ ^ 3 :=
    fun u => curv_le_of_slice hX2 (hPne Γ.T) rfl (hconst Γ.T) (hKnk Γ.T)
      (fun u => Γ.finish u) hq.hasDerivAt_curve hq.hasDerivAt_vel u
  have hperimp : perim p = pathPerim Γ.X 0 := by
    show ‖p.2.1 0‖ = ‖pathVel Γ.X 0 0‖
    rw [pathVel_eq_of_slice hXdiff (fun u => Γ.start u) hp.hasDerivAt_curve 0]
  have hperimq : perim q = pathPerim Γ.X Γ.T := by
    show ‖q.2.1 0‖ = ‖pathVel Γ.X Γ.T 0‖
    rw [pathVel_eq_of_slice hXdiff (fun u => Γ.finish u) hq.hasDerivAt_curve 0]
  have hshortp : kh * perim p < 4 * Real.pi := by rw [hperimp]; exact hshort 0
  have hshortq : kh * perim q < 4 * Real.pi := by rw [hperimq]; exact hshort Γ.T
  have hturnp : ∃ Θ' K' : ℝ → ℝ,
      (∀ s, HasDerivAt (ev p) (Complex.exp (Complex.I * (Θ' s : ℂ))) s) ∧
      (∀ s, HasDerivAt Θ' (K' s) s) ∧
      (∀ s, Θ' (s + perim p) = Θ' s + 2 * Real.pi) := by
    obtain ⟨Θ₁, K₁, -, -, hX₁, hΘ₁, -, -⟩ := SelectedInverseTube.exists_front_data hc hp hubp
    exact ⟨Θ₁, K₁, hX₁, hΘ₁,
      turning_of_tubeMember_of_short hc hkmin hp hubp hshortp Θ₁ K₁ hX₁ hΘ₁⟩
  have hturnq : ∃ Θ' K' : ℝ → ℝ,
      (∀ s, HasDerivAt (ev q) (Complex.exp (Complex.I * (Θ' s : ℂ))) s) ∧
      (∀ s, HasDerivAt Θ' (K' s) s) ∧
      (∀ s, Θ' (s + perim q) = Θ' s + 2 * Real.pi) := by
    obtain ⟨Θ₁, K₁, -, -, hX₁, hΘ₁, -, -⟩ := SelectedInverseTube.exists_front_data hcq hq hubq
    exact ⟨Θ₁, K₁, hX₁, hΘ₁,
      turning_of_tubeMember_of_short hcq hkminq hq hubq hshortq Θ₁ K₁ hX₁ hΘ₁⟩
  exact SelInvPathBoundsFundamentalDriftC2.exists_bounds_dist_selInv_le_modulus_of_path_fundamental_drift_C2 Γ hc hkmin hp hturnp hcq hkminq hq
    hturnq hkh1 hXC6 hconst hXper hturn hnu hKn0 hKnk hslit hmark

end SelInvPathTurningFundamentalDriftC2
