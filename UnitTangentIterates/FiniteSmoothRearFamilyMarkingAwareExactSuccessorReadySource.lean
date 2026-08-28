import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareExactSuccessorGaugeGeometry
import UnitTangentIterates.RearOwnFrameSpatialC2OfMixed

/-!
# A ready exact successor source from selected C1 data

This module assembles the geometric and dynamical transports into a complete
`MarkingAwareSource`.  The genuinely quantitative inequalities are isolated
in `Bounds`; no smoothness or numerical estimate is postulated implicitly.
-/

noncomputable section

open Function Set RearTrack RearOwnArclength RearFamilyFrame

namespace FiniteSmoothRearFamilyMarkingAwareExactSuccessorReadySource

set_option maxHeartbeats 600000

open FiniteSmoothRearFamilyMarkingAwareSource
  FiniteSmoothRearFamilyMarkingAwareAppliedSource
  FiniteSmoothRearFamilyMarkingAwareSuccessorFront
  FiniteSmoothRearFamilyMarkingAwareExactSuccessorPreTransport
  FiniteSmoothRearFamilyMarkingAwareExactSuccessorGaugeTransport
  FiniteSmoothRearFamilyMarkingAwareExactSuccessorGaugeGeometry

variable {p q a b : MarkedSpace.Data} {Gamma : PathMetric.NormalPath p q}
  {P0 kh khat Qmax kap P0Next khatNext QmaxNext : ℝ}
  {A : MarkingAwareSource Gamma P0 kh khat Qmax}
  {E : Applied Gamma A}
  (W : ChosenPath Gamma A E.Phi a b)
  (S : ExactSelected A (kap := kap))
  (R : PreTransport S)
  (G : RearOwnFrameGaugeFlowReanchoring.Gauge (xi R))

private theorem rearNormal_continuous : Continuous (uncurry (rearNormal A)) := by
  cases A.frame_regularity with
  | joint hY hpsi =>
      exact (RearOwnTangential.contDiff_frameNormal hY hpsi).continuous
  | spatial C => exact C.normal.continuous0

theorem selectedSource_continuous (hkap0 : 0 ≤ kap) (hkap1 : kap < 1) :
    Continuous (uncurry S.source) := by
  have hp : Continuous (fun z : ℝ × ℝ => (z.1, S.sf z.1 z.2)) :=
    continuous_fst.prodMk S.sf_contDiff.continuous
  have hn := (rearNormal_continuous (A := A)).comp hp
  have hd := S.delta_contDiff.continuous.comp hp
  exact hn.div (Real.continuous_cos.comp hd) fun z =>
    S.cos_ne_zero hkap0 hkap1 z.1 (S.sf z.1 z.2)

theorem curvatureSpatial_continuous (hkap0 : 0 ≤ kap) (hkap1 : kap < 1) :
    Continuous (uncurry S.curvatureSpatial) := by
  have hp : Continuous (fun z : ℝ × ℝ => (z.1, S.sf z.1 z.2)) :=
    continuous_fst.prodMk S.sf_contDiff.continuous
  have hK := A.rear_curvature_contDiff.continuous.comp hp
  have hd := S.delta_contDiff.continuous.comp hp
  exact (hK.sub (Real.continuous_sin.comp hd)).div
    ((Real.continuous_cos.comp hd).pow 3) fun z => by
      exact pow_ne_zero 3 (S.cos_ne_zero hkap0 hkap1 z.1 (S.sf z.1 z.2))

theorem shiftedSource_continuous (hkap0 : 0 ≤ kap) (hkap1 : kap < 1) :
    Continuous (uncurry (shiftedSource R G)) := by
  have hp : Continuous (fun z : ℝ × ℝ => (z.1, z.2 + G.q z.1)) :=
    continuous_fst.prodMk
      (continuous_snd.add (G.contDiff.continuous.comp continuous_fst))
  change Continuous (fun z : ℝ × ℝ => S.source z.1 (z.2 + G.q z.1))
  exact (selectedSource_continuous (A := A) S hkap0 hkap1).comp hp

theorem shiftedCurvatureSpatial_continuous
    (hkap0 : 0 ≤ kap) (hkap1 : kap < 1) :
    Continuous (uncurry (shiftedCurvatureSpatial R G)) := by
  have hp : Continuous (fun z : ℝ × ℝ => (z.1, z.2 + G.q z.1)) :=
    continuous_fst.prodMk
      (continuous_snd.add (G.contDiff.continuous.comp continuous_fst))
  simpa only [uncurry, shiftedCurvatureSpatial,
    TimeDependentSpatialReanchoring.shift] using
      (curvatureSpatial_continuous (A := A) S hkap0 hkap1).comp hp

def spatialFrames (T : ShiftedTransport R G)
    (hkap0 : 0 ≤ kap) (hkap1 : kap < 1) :
    RearOwnFrameDrift.SpatialC2 (frameTangential (Ydot R G) (shiftedPsi R G)) ×
      RearOwnFrameDrift.SpatialC2 (frameNormal (Ydot R G) (shiftedPsi R G)) :=
  RearOwnFrameSpatialC2OfMixed.spatialC2
    T.Ydot_continuous
    (TimeDependentSpatialReanchoring.shift_contDiff S.psi_contDiff G.contDiff).continuous
    (TimeDependentSpatialReanchoring.shift_contDiff
      (S.kappa_contDiff hkap0 hkap1) G.contDiff).continuous
    T.rear_angle_time_continuous
    (shiftedSource_continuous S R G hkap0 hkap1)
    T.gS_continuous
    (shiftedCurvatureSpatial_continuous S R G hkap0 hkap1)
    (fun t x => by
      simpa [shiftedPsi, shiftedKappa, TimeDependentSpatialReanchoring.shift] using
        TimeDependentSpatialReanchoring.shift_spatial_deriv S.psi_spatial t x)
    T.rear_angle_time_deriv T.mixed T.jacobi T.gS_deriv
    T.curvatureSpatial_deriv

def geometricSpatialFrames (T : ShiftedTransport R G)
    (hkap0 : 0 ≤ kap) (hkap1 : kap < 1) :
    RearOwnFrameDrift.SpatialC2
        (frameTangential (Ydot R G)
          (rearOwnAngle (Theta S G.q) (delta S G.q) (sf S G.q))) ×
      RearOwnFrameDrift.SpatialC2
        (frameNormal (Ydot R G)
          (rearOwnAngle (Theta S G.q) (delta S G.q) (sf S G.q))) := by
  let C := spatialFrames S R G T hkap0 hkap1
  have hp : rearOwnAngle (Theta S G.q) (delta S G.q) (sf S G.q) =
      shiftedPsi R G := by
    funext t x
    exact psi_eq_shift S G.q t x
  refine ⟨?_, ?_⟩
  · exact
      { xi1 := C.1.xi1
        xi2 := C.1.xi2
        deriv1 := by simpa only [hp] using C.1.deriv1
        deriv2 := C.1.deriv2
        continuous0 := by simpa only [hp] using C.1.continuous0
        continuous1 := C.1.continuous1
        continuous2 := C.1.continuous2 }
  · exact
      { xi1 := C.2.xi1
        xi2 := C.2.xi2
        deriv1 := by simpa only [hp] using C.2.deriv1
        deriv2 := C.2.deriv2
        continuous0 := by simpa only [hp] using C.2.continuous0
        continuous1 := C.2.continuous1
        continuous2 := C.2.continuous2 }

structure Bounds (T : ShiftedTransport R G)
    (hkap0 : 0 ≤ kap) (hkap1 : kap < 1) where
  Kx : ℝ → ℝ
  Dd : ℝ → ℝ
  m : ℝ → ℝ
  kx : ℝ
  d : ℝ
  curvature_le : ∀ t s, |K S G.q t s| ≤ kap
  rear_period_pos : ∀ t,
    0 < rearArclength (delta S G.q t) (period A t)
  rear_period_le : ∀ t,
    rearArclength (delta S G.q t) (period A t) ≤ QmaxNext
  tangential1_bound : ∀ t x,
    |(geometricSpatialFrames S R G T hkap0 hkap1).1.xi1 t x| ≤
      GaugeMarkedDataOfRearFamily.rearKappa1 kap * m t
  tangential2_bound : ∀ t x,
    |(geometricSpatialFrames S R G T hkap0 hkap1).1.xi2 t x| ≤
      GaugeMarkedDataOfRearFamily.rearKappa2 kap * m t
  tangential_period_bound : ∀ t, ∀ x ∈ Icc (0 : ℝ)
      (rearArclength (delta S G.q t) (period A t)),
    |frameTangential (Ydot R G) (shiftedPsi R G) t x| ≤
      GaugeRearFamilyFromFront.rearDriftConst QmaxNext kap * W.Delta.m t
  rearKappa1_le : GaugeMarkedDataOfRearFamily.rearKappa1 kap ≤ khatNext
  Kx_bound : ∀ t x, |shiftedCurvatureSpatial R G t x| ≤ Kx t
  Kx_nonnegative : ∀ t, 0 ≤ Kx t
  Kx_le : ∀ t, Kx t ≤ kx
  gS_bound : ∀ t x, |gS R G t x| ≤ Dd t
  Dd_le : ∀ t, Dd t ≤ d * m t
  density_continuous : Continuous m
  density_nonnegative : ∀ t, 0 ≤ m t
  density_support : ∀ t ∉ Ioo (0 : ℝ) W.Delta.T, m t = 0
  density_domination : ∀ t,
    W.Delta.m t / Real.sqrt (1 - kap ^ 2) ≤ m t
  numerical_A : 2 + 2 * khatNext *
    GaugeRearFamilyFromFront.rearDriftConst QmaxNext kap ≤ 1 / P0Next
  numerical_K : (d + 2) + khatNext ^ 2 + 2 *
    GaugeRearFamilyFromFront.rearDriftConst QmaxNext kap * kx ≤
      1 / P0Next ^ 2 + khatNext ^ 2

theorem rearNormal_bound (t s : ℝ) :
    |rearNormal A t s| ≤ W.Delta.m t := by
  have hc : Continuous (E.Phi t) := continuous_iff_continuousAt.2 fun u =>
    (W.phi1_deriv t u).continuousAt
  have hs : Surjective (E.Phi t) :=
    surjective_of_continuous_quasiPeriodic
      ((MarkingAwareSource.successorFrontCore A).period_pos t) hc (W.shift t)
  obtain ⟨u, hu⟩ := hs s
  rw [← hu, ← W.eta_eq t u]
  exact W.Delta.abs_eta_le t u

private theorem etaF_bound (t s : ℝ) :
    |etaF S G.q t s| ≤ W.Delta.m t := by
  simpa [etaF, TimeDependentSpatialReanchoring.shift] using
    rearNormal_bound W t (s + sigma S G.q t)

def source (hkap0 : 0 ≤ kap) (hkap1 : kap < 1) (T : ShiftedTransport R G)
    (B : Bounds (P0Next := P0Next) (khatNext := khatNext)
      (QmaxNext := QmaxNext) W S R G T hkap0 hkap1) :
    MarkingAwareSource W.Delta P0Next kap khatNext QmaxNext := by
  let psi := rearOwnAngle (Theta S G.q) (delta S G.q) (sf S G.q)
  have hpsi : psi = shiftedPsi R G := by
    funext t x
    exact psi_eq_shift S G.q t x
  have hP : ContDiff ℝ 1 (period A) := by
    simpa [period] using
      SelInvDriftRigidity.contDiff_rearPeriod
        A.steering_contDiff A.period_contDiff
  exact
    { F := F S G.q
      Theta := Theta S G.q
      delta := delta S G.q
      K := K S G.q
      sf := sf S G.q
      P := period A
      P' := deriv (period A)
      Ydot := Ydot R G
      etaF := etaF S G.q
      alphaT := alphaT R G
      kT := kT R G
      Kx := B.Kx
      Dd := B.Dd
      gS := gS R G
      m := B.m
      kx := B.kx
      d := B.d
      kh_nonnegative := hkap0
      kh_lt_one := hkap1
      strip_nonnegative := delta_strip_nonnegative S G.q
      strip_le := delta_strip_le S G.q
      curvature_le := B.curvature_le
      front_frenet := front_frenet S G.q
      angle_frenet := angle_frenet S G.q
      steering := steering S G.q
      sf_deriv := sf_deriv S G.q
      sf_rightInverse := sf_rightInverse S G.q
      cos_ne_zero := fun t s => S.cos_ne_zero hkap0 hkap1 t
        (s + sigma S G.q t)
      rear_time_deriv := fun t x => by
        convert T.rear_time t x using 1
        funext r
        exact rear_eq_shift S G.q r x
      front_contDiff := front_contDiff S G.contDiff
      angle_contDiff := angle_contDiff S G.contDiff
      steering_contDiff := delta_contDiff S G.contDiff
      sf_contDiff := sf_contDiff S G.contDiff
      period_contDiff := hP
      period_deriv := fun t => (hP.differentiable (by norm_num) t).hasDerivAt
      frame_regularity := FrameRegularity.spatial
        { tangential := (geometricSpatialFrames S R G T hkap0 hkap1).1
          normal := (geometricSpatialFrames S R G T hkap0 hkap1).2
          tangential1_bound := B.tangential1_bound
          tangential2_bound := B.tangential2_bound
          tangential_period_bound := by simpa [psi, hpsi] using
            B.tangential_period_bound }
      rear_curvature_contDiff := by
        have heq : (fun t x => Real.tan (delta S G.q t (sf S G.q t x))) =
            shiftedKappa R G := by
          funext t x
          exact kappa_eq_shift S G.q t x
        rw [heq]
        exact TimeDependentSpatialReanchoring.shift_contDiff
          (S.kappa_contDiff hkap0 hkap1) G.contDiff
      steering_periodic := delta_periodic S G.q
      front_periodic := front_periodic S G.q
      angle_periodic := angle_periodic S G.q
      rear_period_pos := B.rear_period_pos
      rear_period_le := B.rear_period_le
      tangential_zero := by
        intro t
        have hz := (T.anchor_flow t).unique (hasDerivAt_const t (0 : ℝ))
        change frameTangential (Ydot R G) psi t 0 = 0
        rw [hpsi]
        linarith
      jacobi := by
        change ∀ t x, HasDerivAt
          (fun x' => frameNormal (Ydot R G) psi t x')
          (etaF S G.q t (sf S G.q t x) /
            Real.cos (delta S G.q t (sf S G.q t x)) -
              frameNormal (Ydot R G) psi t x) x
        rw [hpsi]
        intro t x
        convert T.jacobi t x using 1 <;>
          simp only [source_eq_shift S G.q]
      period_pos := (MarkingAwareSource.successorFrontCore A).period_pos
      phi := phi S E.Phi G.q
      phi1 := W.phi1
      phi2 := W.phi2
      eta_link := by
        intro t u
        rw [W.eta_eq]
        simp [phi, etaF, TimeDependentSpatialReanchoring.normalize,
          TimeDependentSpatialReanchoring.shift]
      phi_shift := TimeDependentSpatialReanchoring.normalize_shift W.shift
      phi_deriv := TimeDependentSpatialReanchoring.normalize_spatial_deriv
        W.phi1_deriv
      phi1_deriv := W.phi2_deriv
      phi1_continuous := W.phi1_continuous
      phi2_continuous := W.phi2_continuous
      etaF_bound := etaF_bound W S R G
      rearKappa1_le := B.rearKappa1_le
      rear_angle_time_deriv := by simpa [psi, hpsi] using
        T.rear_angle_time_deriv
      rear_curvature_time_deriv := by
        intro t x
        convert T.rear_curvature_time_deriv t x using 1
        funext r
        exact kappa_eq_shift S G.q r x
      rear_angle_time_continuous := T.rear_angle_time_continuous
      rear_curvature_time_continuous := T.rear_curvature_time_continuous
      rear_angle_time_spatial := T.rear_angle_time_spatial
      mixed_derivative := by simpa [psi, hpsi] using T.mixed
      Kx_bound := by
        intro t x
        simpa only [curvatureSpatial_eq_shift S G.q] using B.Kx_bound t x
      Kx_nonnegative := B.Kx_nonnegative
      Kx_le := B.Kx_le
      Kx_continuous := by
        simpa only [curvatureSpatial_eq_shift S G.q] using
          shiftedCurvatureSpatial_continuous S R G hkap0 hkap1
      gS_deriv := by
        intro t x
        convert T.gS_deriv t x using 1
        funext y
        exact source_eq_shift S G.q t y
      gS_bound := B.gS_bound
      Dd_le := B.Dd_le
      density_continuous := B.density_continuous
      density_nonnegative := B.density_nonnegative
      density_support := B.density_support
      density_domination := B.density_domination
      numerical_A := B.numerical_A
      numerical_K := B.numerical_K }

def compatibility (hkap0 : 0 ≤ kap) (hkap1 : kap < 1)
    (T : ShiftedTransport R G)
    (B : Bounds (P0Next := P0Next) (khatNext := khatNext)
      (QmaxNext := QmaxNext) W S R G T hkap0 hkap1) :
    FiniteSmoothRearFamilyMarkingAwareChosenExactAnalyticSuccessor.Compatibility W
      (source W S R G hkap0 hkap1 T B) where
  q := sigma S G.q
  period_eq := rfl
  etaF_eq := by
    intro t s
    simp [source, etaF, TimeDependentSpatialReanchoring.shift]
  phi_eq := by
    intro t u
    simp [source, phi, TimeDependentSpatialReanchoring.normalize]
  phi1_eq := by simp [source]
  phi2_eq := by simp [source]

/-- The source and all analytic slice facts assembled from the same chosen
path, with no independent successor sidecar. -/
def analyticSuccessor (hkap0 : 0 ≤ kap) (hkap1 : kap < 1)
    (T : ShiftedTransport R G)
    (B : Bounds (P0Next := P0Next) (khatNext := khatNext)
      (QmaxNext := QmaxNext) W S R G T hkap0 hkap1)
    {periodUpper : ℝ} (hP0 : 0 < P0Next)
    (hPlower : ∀ t, P0Next ≤ period A t)
    (hPupper : ∀ t, period A t ≤ periodUpper) :
    FiniteSmoothRearFamilyMarkingAwareCorrelatedRecursion.AnalyticSuccessor
      W.Delta A P0Next kap khatNext QmaxNext :=
  FiniteSmoothRearFamilyMarkingAwareChosenExactAnalyticSuccessor.ChosenPath.toExactAnalyticSuccessor W
    (source W S R G hkap0 hkap1 T B)
    (compatibility W S R G hkap0 hkap1 T B)
    hP0 hPlower hPupper

end FiniteSmoothRearFamilyMarkingAwareExactSuccessorReadySource
