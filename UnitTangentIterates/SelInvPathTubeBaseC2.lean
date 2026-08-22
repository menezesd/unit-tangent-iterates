import Mathlib
import UnitTangentIterates.SelInvPathTurningBaseC2
import UnitTangentIterates.SelInvPathTubeFundamentalDriftC2

/-!
# The `C²` estimate with the tube membership of the two ends produced

`SelInvPathTurningBaseC2.dist_selInv_le_modulus_of_path_turning_base_C2` still asks the
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

This is the base-point form: besides the drift bound, the vanishing of the
tangential drift of the selected rears at the marked point is discharged too,
from the marked point of the path being at rest, `∀ t, Γ.eta t 0 = 0`.

Main result: `dist_selInv_le_modulus_of_path_tube_base_C2`.
-/

noncomputable section

open Set Function Complex MeasureTheory MarkedSpace MarkedTopology PathMetric
  PathMetric.NormalPath RearTrack ArclengthInverse RearFamilyFrame RearOwnArclength
  RearOwnMotion

namespace SelInvPathTubeBaseC2

open SelInvPathTubeFundamentalDriftC2

open SelInvPathTubeFundamentalC2

open SelInvPathTubeC2

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

/-- **The `C²` comparison of the two marked selected inverses, with the tube
membership of the two ends produced.**  The hypotheses are those of
`SelInvPathTurningBaseC2.dist_selInv_le_modulus_of_path_turning_base_C2` with the two
tube memberships — and the six constants they carry — removed, in exchange for
the statement that each end of the path carries its velocity and its
acceleration as the derivatives of its curve. -/
theorem dist_selInv_le_modulus_of_path_tube_base_C2 {p q : Data} (Γ : NormalPath p q)
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
      ∀ (khat : ℝ),
        rearKappa1 kh ≤ khat →
        RearCostDensity.rearCostConst kh khat (rearKappa2 kh)
            (rearArclength (δ 0) ((pathPerim Γ.X) 0)) (jacobiSourceConst kh P0) * cost Γ ≤ 1 →
      dist (SelectedInverseMap.selInv kh q) (SelectedInverseMap.selInv kh p)
        ≤ selInvFrontModulus P1 kh (perim (SelectedInverseMap.selInv kh p))
            (perim (SelectedInverseMap.selInv kh q)) (kh / Real.sqrt (1 - kh ^ 2))
            (2 * kh / Real.sqrt (1 - kh ^ 2) ^ 3) (pathPv0 kh P0 khat (P1 * (kh / (1 - kh ^ 2)))) khat
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
  exact SelInvPathTurningBaseC2.dist_selInv_le_modulus_of_path_turning_base_C2 Γ hperimp hkminP hp hperimq hkminP hq
    hkh1 hXC6 hconst hXper hnu hkminP hKnmin hKnk hshort hslit hmark

end SelInvPathTubeBaseC2
