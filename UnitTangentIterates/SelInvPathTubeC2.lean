import Mathlib
import UnitTangentIterates.SelInvPathTurningC2
import UnitTangentIterates.ConvexChordArcSpeed

/-!
# The `C²` estimate with the tube membership of the two ends produced

`SelInvPathTurningC2.dist_selInv_le_modulus_of_path_turning_C2` still asks the
caller for the tube membership of the two ends of the normal path, with three
constants each: a lower bound `c` for the speed, a lower bound `kmin` for the
curvature and a chord-arc constant `dlt`.  None of that has to be assumed.

A slice of the path is a closed curve of constant speed `pathPerim`, and its
curvature is pinched by the hypotheses of the estimate; so all the fields of
`MarkedSpace.IsTubeMember` but one are read off from the path.  The one that is
not — the quantitative chord-arc bound, the closed form of embeddedness — is
produced by `ConvexChordArcSpeed.chord_arc_of_convex_speed`: in the normalized
parameter the slice moves at the constant speed `L = pathPerim` and turns at the
rate `L·K`, pinched by `L·kminP` and `L·κ̂`, and it closes up after the parameter
increment one with total turning `2π`, so

`chordConstSpeed L (L·kminP) (L·κ̂) 1 · cyc u v ≤ ‖X u − X v‖`.

Main results: `curv_ge_of_slice`, `isTubeMember_of_slice` — a marked datum
traced by a slice of the path is a member of the tube, with all three constants
produced from the pinching — and `dist_selInv_le_modulus_of_path_tube_C2`, the
`C²` comparison of the two marked selected inverses with the two tube
memberships replaced by the statement that each end carries its velocity and its
acceleration as the derivatives of its curve.
-/

noncomputable section

open Set Function Complex MeasureTheory MarkedSpace MarkedTopology PathMetric
  PathMetric.NormalPath RearTrack ArclengthInverse RearFamilyFrame RearOwnArclength
  RearOwnMotion

namespace SelInvPathTubeC2

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
  SelInvPathBoundsC2 SelInvPathTurningC2 TurningNumberTube PathDataTaylorBounds
  FrontDataRegularity RearOwnTangential ConvexChordArcSpeed

variable {kh : ℝ}

/-- **The curvature lower bound of an end of the path is the normalized
curvature bound at that time.**  The mirror of
`SelInvPathCurvBoundC2.curv_le_of_slice`. -/
theorem curv_ge_of_slice {X : ℝ → ℝ → ℂ} {P : ℝ → ℝ} {t kminP : ℝ} {p : Data}
    (hX : ContDiff ℝ (2 : ℕ) (uncurry X)) (hPne : P t ≠ 0)
    (hPdef : P t = ‖pathVel X t 0‖) (hconst : ∀ u, ‖pathVel X t u‖ = ‖pathVel X t 0‖)
    (hKnmin : ∀ σ, kminP ≤ pathKn X P t σ)
    (hslice : ∀ u, X t u = p.1 u)
    (hd : ∀ u, HasDerivAt (⇑p.1) (p.2.1 u) u)
    (hd2 : ∀ u, HasDerivAt (⇑p.2.1) (p.2.2 u) u) (u : ℝ) :
    kminP * ‖p.2.1 u‖ ^ 3 ≤ ((starRingEnd ℂ) (p.2.1 u) * p.2.2 u).im := by
  have hX1 : Differentiable ℝ (uncurry X) := hX.differentiable (by norm_num)
  have hV : pathVel X t u = p.2.1 u := pathVel_eq_of_slice hX1 hslice hd u
  have hA : pathAcc X t u = p.2.2 u := pathAcc_eq_of_slice hX hslice hd hd2 u
  have hPpos : 0 < P t := lt_of_le_of_ne (hPdef ▸ norm_nonneg _) (Ne.symm hPne)
  have hnorm : ‖p.2.1 u‖ = P t := by rw [← hV, hconst u, ← hPdef]
  have hk := hKnmin u
  have hcancel : u * P t / P t = u := by field_simp
  rw [pathKn, curvOfPath, hcancel, hV, hA] at hk
  rw [le_div_iff₀ (by positivity)] at hk
  rw [hnorm]
  exact hk

/-- **A slice of a normal path is a member of the tube.**  A marked datum traced
by a slice of a path of closed constant-speed curves of pinched curvature and
turning number one is a member of the tube, of speed at least its own perimeter,
of curvature at least `kminP` and with the chord-arc constant produced by
`ConvexChordArcSpeed`. -/
theorem isTubeMember_of_slice {X : ℝ → ℝ → ℂ} {t kminP : ℝ} {p : Data}
    (hX : ContDiff ℝ (2 : ℕ) (uncurry X))
    (hXper : ∀ t, Periodic (X t) 1)
    (hconst : ∀ u, ‖pathVel X t u‖ = ‖pathVel X t 0‖)
    (hPpos : 0 < pathPerim X t)
    (hkminP : 0 < kminP)
    (hKnmin : ∀ σ, kminP ≤ pathKn X (pathPerim X) t σ)
    (hKnk : ∀ σ, pathKn X (pathPerim X) t σ ≤ kh)
    (hturn : (∫ u in (0 : ℝ)..1,
        ((starRingEnd ℂ) (pathVel X t u) * pathAcc X t u).im / pathPerim X t ^ 2)
      = 2 * Real.pi)
    (hslice : ∀ u, X t u = p.1 u)
    (hd : ∀ u, HasDerivAt (⇑p.1) (p.2.1 u) u)
    (hd2 : ∀ u, HasDerivAt (⇑p.2.1) (p.2.2 u) u) :
    IsTubeMember (perim p) kminP
      (chordConstSpeed (perim p) (perim p * kminP) (perim p * kh) 1) p := by
  have hX1 : Differentiable ℝ (uncurry X) := hX.differentiable (by norm_num)
  have hV : ∀ u, pathVel X t u = p.2.1 u := fun u => pathVel_eq_of_slice hX1 hslice hd u
  have hA : ∀ u, pathAcc X t u = p.2.2 u := fun u => pathAcc_eq_of_slice hX hslice hd hd2 u
  set L : ℝ := pathPerim X t with hLdef
  have hperim : perim p = L := by
    show ‖p.2.1 0‖ = L
    rw [← hV 0, hLdef]
    rfl
  have hspeed : ∀ u, ‖p.2.1 u‖ = L := by
    intro u
    rw [← hV u, hconst u, hLdef]
    rfl
  -- the tangent angle of the slice, read in the normalized parameter
  set theta : ℝ → ℝ := fun u => angleOfPath (pathVel X) (pathAcc X) (pathPerim X) t (L * u)
    with hthetadef
  have hVcont : Continuous (pathVel X t) := by
    have hVC : ContDiff ℝ ((1 : ℕ)) (uncurry (pathVel X)) :=
      contDiff_partialArc_self (n := 1) hX
    exact hVC.continuous.comp (continuous_const.prodMk continuous_id)
  have hAcont : Continuous (pathAcc X t) := by
    have hVC : ContDiff ℝ ((1 : ℕ)) (uncurry (pathVel X)) :=
      contDiff_partialArc_self (n := 1) hX
    have hAC : ContDiff ℝ ((0 : ℕ)) (uncurry (pathAcc X)) :=
      contDiff_partialArc_self (n := 0) hVC
    exact hAC.continuous.comp (continuous_const.prodMk continuous_id)
  have hVper : Periodic (pathVel X t) 1 := periodic_partialArc hX1 hXper t
  have hAper : Periodic (pathAcc X t) 1 := by
    have hVd : Differentiable ℝ (uncurry (pathVel X)) :=
      (contDiff_partialArc_self (n := 1) hX).differentiable (by norm_num)
    exact periodic_partialArc hVd (fun t => periodic_partialArc hX1 hXper t) t
  have hnormV : ∀ u, ‖pathVel X t u‖ = pathPerim X t := fun u => hconst u
  have hcurvcont : Continuous (curvOfPath (pathVel X) (pathAcc X) (pathPerim X) t) :=
    continuous_curvOfPath hVcont hAcont
  have hPne : pathPerim X t ≠ 0 := hPpos.ne'
  -- the derivative of the angle in the normalized parameter
  have hth : ∀ u, HasDerivAt theta (L * pathKn X (pathPerim X) t u) u := by
    intro u
    have hmul : HasDerivAt (fun u : ℝ => L * u) L u := by
      simpa using (hasDerivAt_id u).const_mul L
    have h := (hasDerivAt_angleOfPath (V := pathVel X) (A := pathAcc X) (P := pathPerim X)
      (t := t) hcurvcont (L * u)).comp u hmul
    have hval : curvOfPath (pathVel X) (pathAcc X) (pathPerim X) t (L * u)
        = pathKn X (pathPerim X) t u := by
      rw [pathKn]
      congr 1
      rw [hLdef]; ring
    rw [hval] at h
    simpa [mul_comm] using h
  -- the velocity in the direction of the angle
  have hexp : ∀ u, p.2.1 u = (L : ℂ) * Complex.exp ((theta u : ℂ) * Complex.I) := by
    intro u
    have hVd : Differentiable ℝ (uncurry (pathVel X)) :=
      (contDiff_partialArc_self (n := 1) hX).differentiable (by norm_num)
    have h := exp_angleOfPath (V := pathVel X) (A := pathAcc X) (P := pathPerim X) (t := t)
      (fun u => hasDerivAt_partialArc hVd t u)
      hAcont hVcont hnormV hPpos (L * u)
    have hcancel : L * u / pathPerim X t = u := by
      rw [hLdef]; field_simp
    rw [tangentOfPath, hcancel] at h
    have hLne : (L : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by rw [hLdef]; exact hPne)
    have h2 : Complex.exp ((theta u : ℂ) * Complex.I) = pathVel X t u / (L : ℂ) := by
      rw [mul_comm]
      rw [hLdef]
      exact h
    rw [← hV u, h2]
    field_simp
  refine ⟨hd, hd2, ?_, ?_, ?_, ?_, ?_⟩
  · intro u
    show p.1 (u + 1) = p.1 u
    rw [← hslice, ← hslice, hXper t u]
  · intro u v; rw [hspeed u, hspeed v]
  · intro u; rw [hperim, hspeed u]
  · intro u
    exact curv_ge_of_slice (P := pathPerim X) hX hPne rfl hconst hKnmin hslice hd hd2 u
  · intro u _ v _
    have hchord := chord_arc_of_convex_speed (X := ⇑p.1) (theta := theta)
      (w := fun u => L * pathKn X (pathPerim X) t u) (v := fun _ => L) (L := 1)
      (vmin := L) (wmin := L * kminP) (wmax := L * kh)
      (by norm_num)
      (fun u => by simpa [hexp u] using hd u)
      hth
      (fun u => by
        have := hKnmin u
        nlinarith [hPpos])
      (fun u => by
        have := hKnk u
        nlinarith [hPpos])
      (by positivity)
      (fun _ => le_rfl) hPpos
      (fun u => by
        show p.1 (u + 1) = p.1 u
        rw [← hslice, ← hslice, hXper t u])
      (fun u => by
        have hstep : L * (u + 1) = L * u + pathPerim X t := by rw [hLdef]; ring
        show angleOfPath (pathVel X) (pathAcc X) (pathPerim X) t (L * (u + 1))
          = angleOfPath (pathVel X) (pathAcc X) (pathPerim X) t (L * u) + 2 * Real.pi
        rw [hstep]
        exact angleOfPath_add_period hVper hAper hVcont hAcont hPpos hturn (L * u))
      u v
    rw [hperim]
    simpa [cyc] using hchord

/-- **The `C²` comparison of the two marked selected inverses, with the tube
membership of the two ends produced.**  The hypotheses are those of
`SelInvPathTurningC2.dist_selInv_le_modulus_of_path_turning_C2` with the two
tube memberships — and the six constants they carry — removed, in exchange for
the statement that each end of the path carries its velocity and its
acceleration as the derivatives of its curve. -/
theorem dist_selInv_le_modulus_of_path_tube_C2 {p q : Data} (Γ : NormalPath p q)
    {kminP : ℝ}
    (hpd : ∀ u, HasDerivAt (⇑p.1) (p.2.1 u) u)
    (hpd2 : ∀ u, HasDerivAt (⇑p.2.1) (p.2.2 u) u)
    (hqd : ∀ u, HasDerivAt (⇑q.1) (q.2.1 u) u)
    (hqd2 : ∀ u, HasDerivAt (⇑q.2.1) (q.2.2 u) u)
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
            (2 * kh / Real.sqrt (1 - kh ^ 2) ^ 3) (pathPv0 kh P0 khat rr) khat
            (jacobiSourceConst kh P0) (cost Γ) := by
  have hX2 : ContDiff ℝ (2 : ℕ) (uncurry Γ.X) := hXC6.of_le (by norm_num)
  have hXdiff : Differentiable ℝ (uncurry Γ.X) := hXC6.differentiable (by norm_num)
  have hVC : ContDiff ℝ ((1 : ℕ)) (uncurry (pathVel Γ.X)) :=
    contDiff_partialArc_self (n := 1) hX2
  have hVdiff : Differentiable ℝ (uncurry (pathVel Γ.X)) := hVC.differentiable (by norm_num)
  have hPpos : ∀ t, 0 < pathPerim Γ.X t :=
    fun t => norm_pos_iff.2 (Complex.slitPlane_ne_zero (hslit t))
  have hPne : ∀ t, pathPerim Γ.X t ≠ 0 := fun t => (hPpos t).ne'
  have hVper : ∀ t, Periodic (pathVel Γ.X t) 1 := periodic_partialArc hXdiff hXper
  have hAper : ∀ t, Periodic (pathAcc Γ.X t) 1 := periodic_partialArc hVdiff hVper
  have hslicec : ∀ t : ℝ, Continuous fun u : ℝ => ((t, u) : ℝ × ℝ) :=
    fun t => continuous_const.prodMk continuous_id
  have hVcont : ∀ t, Continuous (pathVel Γ.X t) := fun t => hVC.continuous.comp (hslicec t)
  have hAcont : ∀ t, Continuous (pathAcc Γ.X t) := fun t =>
    (contDiff_partialArc_self (n := 0) hVC).continuous.comp (hslicec t)
  have hAderiv : ∀ t u, HasDerivAt (pathVel Γ.X t) (pathAcc Γ.X t u) u :=
    fun t u => hasDerivAt_partialArc hVdiff t u
  have hlowc : ∀ t s, kminP ≤ curvOfPath (pathVel Γ.X) (pathAcc Γ.X) (pathPerim Γ.X) t s :=
    fun t s => by rw [curvOfPath_eq_pathKn hPne t s]; exact hKnmin t _
  have hhighc : ∀ t s, curvOfPath (pathVel Γ.X) (pathAcc Γ.X) (pathPerim Γ.X) t s ≤ kh :=
    fun t s => by rw [curvOfPath_eq_pathKn hPne t s]; exact hKnk t _
  have hturn : ∀ t, (∫ u in (0 : ℝ)..1,
      ((starRingEnd ℂ) ((pathVel Γ.X) t u) * (pathAcc Γ.X) t u).im / pathPerim Γ.X t ^ 2)
      = 2 * Real.pi :=
    fun t => turning_of_slice (hAderiv t) (hVper t) (hAper t) (hVcont t) (hAcont t)
      (fun u => hconst t u) (hPpos t) hkminP (hlowc t) (hhighc t) (hshort t)
  have hp : IsTubeMember (perim p) kminP
      (chordConstSpeed (perim p) (perim p * kminP) (perim p * kh) 1) p :=
    isTubeMember_of_slice hX2 hXper (hconst 0) (hPpos 0) hkminP (hKnmin 0) (hKnk 0)
      (hturn 0) (fun u => Γ.start u) hpd hpd2
  have hq : IsTubeMember (perim q) kminP
      (chordConstSpeed (perim q) (perim q * kminP) (perim q * kh) 1) q :=
    isTubeMember_of_slice hX2 hXper (hconst Γ.T) (hPpos Γ.T) hkminP (hKnmin Γ.T) (hKnk Γ.T)
      (hturn Γ.T) (fun u => Γ.finish u) hqd hqd2
  have hperimp : 0 < perim p := by
    show 0 < ‖p.2.1 0‖
    have := pathVel_eq_of_slice hXdiff (fun u => Γ.start u) hpd 0
    rw [← this]
    exact hPpos 0
  have hperimq : 0 < perim q := by
    show 0 < ‖q.2.1 0‖
    have := pathVel_eq_of_slice hXdiff (fun u => Γ.finish u) hqd 0
    rw [← this]
    exact hPpos Γ.T
  exact dist_selInv_le_modulus_of_path_turning_C2 Γ hperimp hkminP hp hperimq hkminP hq
    hkh1 hXC6 hconst hXper hnu hkminP hKnmin hKnk hshort hslit hmark

end SelInvPathTubeC2
