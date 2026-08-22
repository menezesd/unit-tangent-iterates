import Mathlib
import UnitTangentIterates.SelInvPathGaugeC2

/-!
# The `C²` estimate with the bounds on the perimeter produced

`SelInvPathGaugeC2.dist_selInv_le_modulus_of_path_gauge_C2` still asks the
caller for two constants `P₀`, `P₁` bounding the perimeter of the slices from
below and from above along the whole path.  They need not be assumed.  The
perimeter of the slices is continuous in the time, and a normal path stands
still outside its time window (`PathDataTaylorBounds.path_P_rest`), so the
perimeter is constant there and its values are those attained on the compact
window; the extreme values are attained, and the lower one is positive as soon
as the slices are regular curves (`exists_pos_bounds_of_rest`).

Main result: `exists_bounds_dist_selInv_le_modulus_of_path_C2`, the same
estimate with `P₀` and `P₁` produced and no new hypothesis: the regularity of
the slices is already contained in the choice of a branch of the argument at the
marked point, the slit plane not containing the origin.
-/

noncomputable section

open Set Function Complex MeasureTheory MarkedSpace MarkedTopology PathMetric
  PathMetric.NormalPath RearTrack ArclengthInverse RearFamilyFrame RearOwnArclength
  RearOwnMotion

namespace SelInvPathBoundsC2

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
  PathDataTaylorBounds FrontDataRegularity RearOwnTangential

variable {kh : ℝ}

/-- **A positive continuous function that is constant in the time outside a
compact window is pinched between two positive constants.** -/
theorem exists_pos_bounds_of_rest {f : ℝ → ℝ} {T : ℝ} (hT : 0 ≤ T) (hc : Continuous f)
    (hpos : ∀ t, 0 < f t) (hrest : ∀ t, f t = f (clampT 0 T t)) :
    ∃ P0 P1 : ℝ, 0 < P0 ∧ (∀ t, P0 ≤ f t) ∧ (∀ t, f t ≤ P1) := by
  obtain ⟨a, -, hmin⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := T)).exists_isMinOn
    ⟨0, left_mem_Icc.mpr hT⟩ hc.continuousOn
  obtain ⟨b, -, hmax⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := T)).exists_isMaxOn
    ⟨0, left_mem_Icc.mpr hT⟩ hc.continuousOn
  refine ⟨f a, f b, hpos a, fun t => ?_, fun t => ?_⟩
  · rw [hrest t]; exact hmin (clampT_mem hT t)
  · rw [hrest t]; exact hmax (clampT_mem hT t)

/-- **The perimeter of the slices of a smooth normal path is pinched.**  It is
continuous, positive when the slices are regular, and constant outside the time
window of the path. -/
theorem exists_perim_bounds {p q : Data} (Γ : NormalPath p q)
    (hXC : ContDiff ℝ (2 : ℕ) (uncurry Γ.X)) (hreg : ∀ t, pathVel Γ.X t 0 ≠ 0) :
    ∃ P0 P1 : ℝ, 0 < P0 ∧ (∀ t, P0 ≤ pathPerim Γ.X t) ∧ (∀ t, pathPerim Γ.X t ≤ P1) := by
  have hV : ∀ t u, HasDerivAt (Γ.X t) (pathVel Γ.X t u) u :=
    fun t u => hasDerivAt_partialArc (hXC.differentiable (by norm_num)) t u
  have hcont : Continuous (pathPerim Γ.X) := by
    have h : Continuous (uncurry (partialArc Γ.X)) :=
      (contDiff_partialArc_self (n := 1) hXC).continuous
    exact (h.comp (continuous_id.prodMk continuous_const)).norm
  have hpos : ∀ t, 0 < pathPerim Γ.X t := fun t => norm_pos_iff.2 (hreg t)
  have hrest : ∀ t, pathPerim Γ.X t = pathPerim Γ.X (clampT 0 Γ.T t) := fun t => by
    show ‖pathVel Γ.X t 0‖ = ‖pathVel Γ.X (clampT 0 Γ.T t) 0‖
    rw [path_V_rest Γ hV t 0]
  exact exists_pos_bounds_of_rest Γ.T_pos.le hcont hpos hrest

/-- **The `C²` comparison of the two marked selected inverses, with the bounds
on the perimeter produced.**  The hypotheses are those of
`SelInvPathGaugeC2.dist_selInv_le_modulus_of_path_gauge_C2` with the two
constants pinching the perimeter of the slices removed; they are produced in
the conclusion instead. -/
theorem exists_bounds_dist_selInv_le_modulus_of_path_C2 {p q : Data} (Γ : NormalPath p q)
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
    (hkh1 : kh < 1)
    (hXC6 : ContDiff ℝ (6 : ℕ) (uncurry Γ.X))
    (hconst : ∀ t u, ‖(pathVel Γ.X) t u‖ = ‖pathVel Γ.X t 0‖)
    (hXper : ∀ t, Periodic (Γ.X t) 1)
    (hturn : ∀ t, (∫ u in (0 : ℝ)..1, ((starRingEnd ℂ) ((pathVel Γ.X) t u) * (pathAcc Γ.X) t u).im / (pathPerim Γ.X) t ^ 2)
      = 2 * Real.pi)
    (hnu : ∀ t u, Γ.nu t u = Complex.I * ((pathVel Γ.X) t u / ((pathPerim Γ.X) t : ℂ)))
    (hKn0 : ∀ t σ, 0 ≤ pathKn Γ.X (pathPerim Γ.X) t σ) (hKnk : ∀ t σ, pathKn Γ.X (pathPerim Γ.X) t σ ≤ kh)
    (hslit : ∀ t, pathVel Γ.X t 0 ∈ Complex.slitPlane)
    (hmark : ∀ t, Γ.eta t 0 = 0) :
    ∃ P0 P1 : ℝ, 0 < P0 ∧ (∀ t, P0 ≤ pathPerim Γ.X t) ∧
      (∀ t, pathPerim Γ.X t ≤ P1) ∧
    ∃ dn δ : ℝ → ℝ → ℝ,
      (∀ t, Function.Periodic (dn t) 1) ∧
      (∀ t σ, dn t σ ∈ Icc (0 : ℝ) (Real.arcsin kh)) ∧
      (∀ t σ, HasDerivAt (dn t) ((pathPerim Γ.X) t * (pathKn Γ.X (pathPerim Γ.X) t σ - Real.sin (dn t σ))) σ) ∧
      (∀ t s, δ t s = dn t (s / (pathPerim Γ.X) t)) ∧
      ∀ (Rb : ℝ → ℝ) (khat rr : ℝ),
        rearKappa1 kh ≤ khat →
        (∀ t x,
          |frameTangential (rearOwnVelocity Γ.X (pathVel Γ.X) (pathAcc Γ.X) (pathPerim Γ.X) δ (SelInvFrontChangeVarC2.rearArclengthInv δ)) (rearOwnAngle (angleOfPath (pathVel Γ.X) (pathAcc Γ.X) (pathPerim Γ.X)) δ (SelInvFrontChangeVarC2.rearArclengthInv δ)) t x| ≤ Rb t) →
        (∀ t, Rb t ≤ rr * Γ.m t) → 0 ≤ rr →
        RearCostDensity.rearCostConst kh khat (rearKappa2 kh)
            (rearArclength (δ 0) ((pathPerim Γ.X) 0)) (jacobiSourceConst kh P0) * cost Γ ≤ 1 →
      dist (SelectedInverseMap.selInv kh q) (SelectedInverseMap.selInv kh p)
        ≤ selInvFrontModulus P1 kh (perim (SelectedInverseMap.selInv kh p))
            (perim (SelectedInverseMap.selInv kh q)) (kh / Real.sqrt (1 - kh ^ 2))
            (2 * kh / Real.sqrt (1 - kh ^ 2) ^ 3) (pathPv0 kh P0 khat rr) khat (jacobiSourceConst kh P0)
            (cost Γ) := by
  obtain ⟨P0, P1, hP0, hPl, hPu⟩ :=
    exists_perim_bounds Γ (hXC6.of_le (by norm_num))
      (fun t => Complex.slitPlane_ne_zero (hslit t))
  exact ⟨P0, P1, hP0, hPl, hPu,
    dist_selInv_le_modulus_of_path_gauge_C2 Γ hc hkmin hp hturnp hcq hkminq hq hturnq
      hP0 hkh1 hXC6 hPl hPu hconst hXper hturn hnu hKn0 hKnk hslit hmark⟩

end SelInvPathBoundsC2
