import Mathlib
import UnitTangentIterates.SelInvPathBoundsC2
import UnitTangentIterates.TurningNumberTube

/-!
# The `C²` estimate with the turning numbers discharged

`SelInvPathBoundsC2.exists_bounds_dist_selInv_le_modulus_of_path_C2` still
carries three global topological hypotheses: that the tangent angle of each
slice of the path increases by `2π` over one period, and that the tangent angle
of each of the two ends does.  None of them has to be assumed when the slices
are short and their curvature is pinched away from zero.

The turning of a closed slice is quantized in `2π`
(`FrontFromPath.exists_int_turning`), and the total curvature of a slice lies in
`(0, 4π)` as soon as `0 < kmin ≤ K ≤ κ̂` and `κ̂·L < 4π`; so the turning number
is one (`turning_of_slice`).  At the two ends the same argument is already
available in the form of `TurningNumberTube.turning_of_tubeMember_of_short`.

Main results: `turning_of_slice`, `dist_selInv_le_modulus_of_path_turning_C2`.
-/

noncomputable section

open Set Function Complex MeasureTheory MarkedSpace MarkedTopology PathMetric
  PathMetric.NormalPath RearTrack ArclengthInverse RearFamilyFrame RearOwnArclength
  RearOwnMotion

namespace SelInvPathTurningC2

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

/-- **A short slice of pinched curvature has turning number one.**  The total
turning of a closed slice is a multiple of `2π`, and it lies strictly between
`0` and `4π` when `0 < kmin ≤ K` and `κ̂·L < 4π`, so it is exactly `2π`. -/
theorem turning_of_slice {V A : ℝ → ℝ → ℂ} {P : ℝ → ℝ} {t kminP : ℝ}
    (hA : ∀ u, HasDerivAt (V t) (A t u) u)
    (hVper : Periodic (V t) 1) (hAper : Periodic (A t) 1)
    (hVcont : Continuous (V t)) (hAcont : Continuous (A t))
    (hspeed : ∀ u, ‖V t u‖ = P t) (hP : 0 < P t) (hkminP : 0 < kminP)
    (hlow : ∀ s, kminP ≤ curvOfPath V A P t s)
    (hhigh : ∀ s, curvOfPath V A P t s ≤ kh)
    (hshort : kh * P t < 4 * Real.pi) :
    (∫ u in (0 : ℝ)..1, ((starRingEnd ℂ) (V t u) * A t u).im / P t ^ 2) = 2 * Real.pi := by
  have hKc : Continuous (curvOfPath V A P t) := continuous_curvOfPath hVcont hAcont
  have hchange : (∫ x in (0 : ℝ)..(P t), curvOfPath V A P t x)
      = ∫ u in (0 : ℝ)..1, ((starRingEnd ℂ) (V t u) * A t u).im / P t ^ 2 := by
    have h := intervalIntegral.smul_integral_comp_mul_left (a := 0) (b := 1)
      (curvOfPath V A P t) (P t)
    simp only [mul_zero, mul_one, smul_eq_mul] at h
    rw [← h, ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr (fun u _ => ?_)
    have hu : P t * u / P t = u := by field_simp
    rw [curvOfPath, hu]
    field_simp
  set I : ℝ := ∫ x in (0 : ℝ)..(P t), curvOfPath V A P t x with hI
  have hIval : angleOfPath V A P t (0 + P t) - angleOfPath V A P t 0 = I := by
    simp [angleOfPath, hI]
  obtain ⟨n, hn⟩ := exists_int_turning hA hVper hAper hVcont hAcont hspeed hP
  have hIn : I = 2 * Real.pi * n := by
    have h0 := hn 0
    rw [← hIval]; linarith
  have hlb : kminP * P t ≤ I := by
    have := intervalIntegral.integral_mono_on (f := fun _ : ℝ => kminP)
      (g := curvOfPath V A P t) hP.le
      (intervalIntegrable_const (μ := MeasureTheory.volume) (c := kminP))
      (hKc.intervalIntegrable 0 (P t)) (fun x _ => hlow x)
    simpa [mul_comm] using this
  have hub : I ≤ kh * P t := by
    have := intervalIntegral.integral_mono_on (f := curvOfPath V A P t)
      (g := fun _ : ℝ => kh) hP.le (hKc.intervalIntegrable 0 (P t))
      (intervalIntegrable_const (μ := MeasureTheory.volume) (c := kh)) (fun x _ => hhigh x)
    simpa [mul_comm] using this
  have hpi : 0 < Real.pi := Real.pi_pos
  have hpos : 0 < I := lt_of_lt_of_le (by positivity) hlb
  have hn1 : n = 1 := by
    have h1 : (0 : ℝ) < 2 * Real.pi * n := by rw [← hIn]; exact hpos
    have h2 : 2 * Real.pi * (n : ℝ) < 4 * Real.pi := by rw [← hIn]; linarith
    have hnpos : (0 : ℤ) < n := by
      have : (0 : ℝ) < (n : ℝ) := by nlinarith
      exact_mod_cast this
    have hnlt : n < 2 := by
      have : (n : ℝ) < 2 := by nlinarith
      exact_mod_cast this
    omega
  rw [← hchange, hIn, hn1]
  push_cast; ring

/-- **The `C²` comparison of the two marked selected inverses, with the turning
numbers discharged.**  The hypotheses are those of
`SelInvPathBoundsC2.exists_bounds_dist_selInv_le_modulus_of_path_C2` with the
turning number of the slices and of the two ends removed, in exchange for a
strictly positive lower bound on the curvature of the slices and the length
threshold `κ̂·L < 4π`. -/
theorem dist_selInv_le_modulus_of_path_turning_C2 {p q : Data} (Γ : NormalPath p q)
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
  exact exists_bounds_dist_selInv_le_modulus_of_path_C2 Γ hc hkmin hp hturnp hcq hkminq hq
    hturnq hkh1 hXC6 hconst hXper hturn hnu hKn0 hKnk hslit hmark

end SelInvPathTurningC2
