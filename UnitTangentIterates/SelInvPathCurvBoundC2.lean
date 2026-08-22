import Mathlib
import UnitTangentIterates.SelInvPathModulusC2

/-!
# The `C²` estimate with the curvature bounds of the two ends discharged

`SelInvPathModulusC2.dist_selInv_le_modulus_of_path_C2` still asks separately
that the curvature of each of the two ends of the path be at most `κ̂`, and that
`κ̂` be nonnegative, although the same bound is already assumed for every slice
of the path in the normalized form `pathKn ≤ κ̂`.

The two ends *are* slices of the path: `Γ.start` and `Γ.finish` identify the
curve of the marked datum with the slice at time `0` and at the final time, and
a marked datum in the tube carries its own velocity and acceleration as the two
parameter derivatives of its curve, so those coincide with `pathVel` and
`pathAcc` there (`pathVel_eq_of_slice`, `pathAcc_eq_of_slice`).  The curvature
bound of the end is then exactly the normalized bound at that time
(`curv_le_of_slice`), and `0 ≤ κ̂` follows from `0 ≤ pathKn ≤ κ̂`.

Main result: `dist_selInv_le_modulus_of_path_curv_C2`.
-/

noncomputable section

open Set Function Complex MeasureTheory MarkedSpace MarkedTopology PathMetric
  PathMetric.NormalPath RearTrack ArclengthInverse RearFamilyFrame RearOwnArclength
  RearOwnMotion

namespace SelInvPathCurvBoundC2

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
  FrontDataRegularity RearOwnTangential

variable {P : ℝ → ℝ} {P0 P1 kh : ℝ}

/-- **A slice of the path carries the velocity of the marked datum it traces.**
The velocity recorded by a member of the tube is the derivative of its curve, so
it is the parameter derivative of the path at that time. -/
theorem pathVel_eq_of_slice {X : ℝ → ℝ → ℂ} (hX : Differentiable ℝ (uncurry X))
    {t : ℝ} {p : Data} (hslice : ∀ u, X t u = p.1 u)
    (hd : ∀ u, HasDerivAt (⇑p.1) (p.2.1 u) u) (u : ℝ) :
    pathVel X t u = p.2.1 u := by
  have hfun : X t = ⇑p.1 := funext hslice
  have h1 : HasDerivAt (X t) (p.2.1 u) u := by rw [hfun]; exact hd u
  exact (hasDerivAt_partialArc hX t u).unique h1

/-- **A slice of the path carries the acceleration of the marked datum it
traces.** -/
theorem pathAcc_eq_of_slice {X : ℝ → ℝ → ℂ} (hX : ContDiff ℝ (2 : ℕ) (uncurry X))
    {t : ℝ} {p : Data} (hslice : ∀ u, X t u = p.1 u)
    (hd : ∀ u, HasDerivAt (⇑p.1) (p.2.1 u) u)
    (hd2 : ∀ u, HasDerivAt (⇑p.2.1) (p.2.2 u) u) (u : ℝ) :
    pathAcc X t u = p.2.2 u := by
  have hX1 : Differentiable ℝ (uncurry X) := hX.differentiable (by norm_num)
  have hVd : Differentiable ℝ (uncurry (partialArc X)) :=
    (contDiff_partialArc_self (n := 1) hX).differentiable (by norm_num)
  have hfun : partialArc X t = ⇑p.2.1 :=
    funext fun u => pathVel_eq_of_slice hX1 hslice hd u
  have h1 : HasDerivAt (partialArc X t) (p.2.2 u) u := by rw [hfun]; exact hd2 u
  exact (hasDerivAt_partialArc hVd t u).unique h1

/-- **The curvature bound of an end of the path is the normalized curvature
bound at that time.** -/
theorem curv_le_of_slice {X : ℝ → ℝ → ℂ} {t : ℝ} {p : Data}
    (hX : ContDiff ℝ (2 : ℕ) (uncurry X)) (hPne : P t ≠ 0)
    (hPdef : P t = ‖pathVel X t 0‖) (hconst : ∀ u, ‖pathVel X t u‖ = ‖pathVel X t 0‖)
    (hKnk : ∀ σ, pathKn X P t σ ≤ kh)
    (hslice : ∀ u, X t u = p.1 u)
    (hd : ∀ u, HasDerivAt (⇑p.1) (p.2.1 u) u)
    (hd2 : ∀ u, HasDerivAt (⇑p.2.1) (p.2.2 u) u) (u : ℝ) :
    ((starRingEnd ℂ) (p.2.1 u) * p.2.2 u).im ≤ kh * ‖p.2.1 u‖ ^ 3 := by
  have hX1 : Differentiable ℝ (uncurry X) := hX.differentiable (by norm_num)
  have hV : pathVel X t u = p.2.1 u := pathVel_eq_of_slice hX1 hslice hd u
  have hA : pathAcc X t u = p.2.2 u := pathAcc_eq_of_slice hX hslice hd hd2 u
  have hPpos : 0 < P t := lt_of_le_of_ne (hPdef ▸ norm_nonneg _) (Ne.symm hPne)
  have hnorm : ‖p.2.1 u‖ = P t := by rw [← hV, hconst u, ← hPdef]
  have hk := hKnk u
  have hcancel : u * P t / P t = u := by field_simp
  rw [pathKn, curvOfPath, hcancel, hV, hA] at hk
  rw [div_le_iff₀ (by positivity)] at hk
  rw [hnorm]
  exact hk

/-- **The `C²` comparison of the two marked selected inverses, with the
curvature bounds of the two ends discharged.**  The hypotheses are those of
`SelInvPathModulusC2.dist_selInv_le_modulus_of_path_C2` with the two curvature
bounds of the ends and the nonnegativity of `κ̂` removed: all three follow from
the pinching `0 ≤ pathKn ≤ κ̂` of the slices of the path. -/
theorem dist_selInv_le_modulus_of_path_curv_C2 {p q : Data} (Γ : NormalPath p q)
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
  have hPne : ∀ t, P t ≠ 0 := fun t => ne_of_gt (lt_of_lt_of_le hP0 (hPl t))
  have hkh0 : 0 ≤ kh := le_trans (hKn0 0 0) (hKnk 0 0)
  have hX2 : ContDiff ℝ (2 : ℕ) (uncurry Γ.X) := hXC6.of_le (by norm_num)
  refine dist_selInv_le_modulus_of_path_C2 Γ hc hkmin hp ?_ hturnp hcq hkminq hq ?_ hturnq
    hP0 hkh0 hkh1 hXC6 hPl hPu hPdef hconst hXper hturn hnu hKn0 hKnk hslit hmark hetaC1
  · exact fun u => curv_le_of_slice hX2 (hPne 0) (hPdef 0) (hconst 0) (hKnk 0)
      (fun u => Γ.start u) hp.hasDerivAt_curve hp.hasDerivAt_vel u
  · exact fun u => curv_le_of_slice hX2 (hPne Γ.T) (hPdef Γ.T) (hconst Γ.T) (hKnk Γ.T)
      (fun u => Γ.finish u) hq.hasDerivAt_curve hq.hasDerivAt_vel u

end SelInvPathCurvBoundC2
