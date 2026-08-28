import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareExactSuccessorReadySource
import UnitTangentIterates.SecondOrderBounds
import UnitTangentIterates.RearOwnTangentialCost

/-! # Automatic genuine gauge for an exact chosen successor -/

noncomputable section

open Function Set RearTrack RearOwnArclength RearFamilyFrame

namespace FiniteSmoothRearFamilyMarkingAwareExactSuccessorGaugeExistence

open FiniteSmoothRearFamilyMarkingAwareSource
  FiniteSmoothRearFamilyMarkingAwareAppliedSource
  FiniteSmoothRearFamilyMarkingAwareSuccessorFront
  FiniteSmoothRearFamilyMarkingAwareExactSuccessorPreTransport
  FiniteSmoothRearFamilyMarkingAwareExactSuccessorGaugeTransport
  FiniteSmoothRearFamilyMarkingAwareExactSuccessorReadySource

variable {p q a b : MarkedSpace.Data} {Gamma : PathMetric.NormalPath p q}
  {P0 kh khat Qmax kap : ℝ}
  {A : MarkingAwareSource Gamma P0 kh khat Qmax}
  {E : Applied Gamma A}
  (W : ChosenPath Gamma A E.Phi a b)
  (S : ExactSelected A (kap := kap))
  (R : PreTransport S)

def rawSpatialFrames (hkap0 : 0 ≤ kap) (hkap1 : kap < 1) :
    RearOwnFrameDrift.SpatialC2 (frameTangential R.Ydot S.psi) ×
      RearOwnFrameDrift.SpatialC2 (frameNormal R.Ydot S.psi) :=
  RearOwnFrameSpatialC2OfMixed.spatialC2
    R.Ydot_continuous S.psi_contDiff.continuous
    (S.kappa_contDiff hkap0 hkap1).continuous
    R.rear_angle_time_continuous
    (selectedSource_continuous (A := A) S hkap0 hkap1)
    R.gS_continuous
    (curvatureSpatial_continuous (A := A) S hkap0 hkap1)
    S.psi_spatial R.rear_angle_time_deriv R.mixed R.jacobi
    R.gS_deriv R.curvatureSpatial_deriv

theorem geometric_xi1_eq_raw
    (G : RearOwnFrameGaugeFlowReanchoring.Gauge (xi R))
    (T : FiniteSmoothRearFamilyMarkingAwareExactSuccessorGaugeTransport.ShiftedTransport R G)
    (hkap0 : 0 ≤ kap) (hkap1 : kap < 1) (t x : ℝ) :
    (geometricSpatialFrames S R G T hkap0 hkap1).1.xi1 t x =
      (rawSpatialFrames S R hkap0 hkap1).1.xi1 t (x + G.q t) := by
  change frameNormal (Ydot R G) (shiftedPsi R G) t x * shiftedKappa R G t x =
    frameNormal R.Ydot S.psi t (x + G.q t) * S.kappa t (x + G.q t)
  simp only [Ydot, shiftedPsi, xi]
  rw [RearOwnFrameGaugeFlowReanchoring.frameNormal_shiftedYdot]
  rfl

theorem geometric_xi2_eq_raw
    (G : RearOwnFrameGaugeFlowReanchoring.Gauge (xi R))
    (T : FiniteSmoothRearFamilyMarkingAwareExactSuccessorGaugeTransport.ShiftedTransport R G)
    (hkap0 : 0 ≤ kap) (hkap1 : kap < 1) (t x : ℝ) :
    (geometricSpatialFrames S R G T hkap0 hkap1).1.xi2 t x =
      (rawSpatialFrames S R hkap0 hkap1).1.xi2 t (x + G.q t) := by
  change (shiftedSource R G t x - frameNormal (Ydot R G) (shiftedPsi R G) t x) *
      shiftedKappa R G t x + frameNormal (Ydot R G) (shiftedPsi R G) t x *
        shiftedCurvatureSpatial R G t x =
    (S.source t (x + G.q t) - frameNormal R.Ydot S.psi t (x + G.q t)) *
      S.kappa t (x + G.q t) + frameNormal R.Ydot S.psi t (x + G.q t) *
        S.curvatureSpatial t (x + G.q t)
  simp only [Ydot, shiftedPsi, xi]
  rw [RearOwnFrameGaugeFlowReanchoring.frameNormal_shiftedYdot]
  rfl

private theorem gamma_pos (hkap0 : 0 ≤ kap) (hkap1 : kap < 1) :
    0 < Real.sqrt (1 - kap ^ 2) :=
  Real.sqrt_pos.mpr (by nlinarith)

theorem raw_frameNormal_bound (hkap0 : 0 ≤ kap) (hkap1 : kap < 1) :
    ∀ t x, |frameNormal R.Ydot S.psi t x| ≤
      W.Delta.m t / Real.sqrt (1 - kap ^ 2) := by
  have hperiodC : ContDiff ℝ 1 (period A) := by
    simpa [period] using SelInvDriftRigidity.contDiff_rearPeriod
      A.steering_contDiff A.period_contDiff
  have hperiodPos : ∀ t, 0 < rearArclength (S.delta t) (period A t) := by
    intro t
    exact SelectedInverseUnique.rearArclength_pos
      ((MarkingAwareSource.successorFrontCore A).period_pos t) hkap0 hkap1
      (S.delta_contDiff.continuous.comp
        (continuous_const.prodMk continuous_id))
      (fun s => ⟨S.strip_nonnegative t s, S.strip_le t s⟩)
  have hnormalPeriod : ∀ t, Periodic (frameNormal R.Ydot S.psi t)
      (rearArclength (S.delta t) (period A t)) := by
    intro t
    exact RearOwnDriftFundamental.periodic_frameNormal_rearOwn
      hkap0 hkap1 S.strip_nonnegative S.strip_le
      (fun a s => S.cos_ne_zero hkap0 hkap1 a s)
      (MarkingAwareSource.successorFrontCore A).front_frenet
      (MarkingAwareSource.successorFrontCore A).angle_frenet
      S.steering S.sf_deriv S.sf_rightInverse S.periodic
      (MarkingAwareSource.successorFrontCore A).front_periodic
      (MarkingAwareSource.successorFrontCore A).angle_periodic
      (ExactSelected.front_contDiff (A := A))
      (ExactSelected.angle_contDiff (A := A)) S.delta_contDiff S.sf_contDiff
      hperiodC R.rear_time t
  intro t x
  exact RearOwnTangentialCost.abs_frameNormal_le_slice
    hkap0 hkap1 S.strip_nonnegative S.strip_le hperiodPos hnormalPeriod
    R.jacobi (rearNormal_bound W) t x

theorem raw_xi1_bound (hkap0 : 0 ≤ kap) (hkap1 : kap < 1) :
    ∀ t x, |(rawSpatialFrames S R hkap0 hkap1).1.xi1 t x| ≤
      GaugeMarkedDataOfRearFamily.rearKappa1 kap * W.Delta.m t := by
  have hperiodC : ContDiff ℝ 1 (period A) := by
    simpa [period] using SelInvDriftRigidity.contDiff_rearPeriod
      A.steering_contDiff A.period_contDiff
  have hperiodPos : ∀ t, 0 < rearArclength (S.delta t) (period A t) := by
    intro t
    exact SelectedInverseUnique.rearArclength_pos
      ((MarkingAwareSource.successorFrontCore A).period_pos t) hkap0 hkap1
      (S.delta_contDiff.continuous.comp
        (continuous_const.prodMk continuous_id))
      (fun s => ⟨S.strip_nonnegative t s, S.strip_le t s⟩)
  have hnormalPeriod : ∀ t, Periodic (frameNormal R.Ydot S.psi t)
      (rearArclength (S.delta t) (period A t)) := by
    intro t
    exact RearOwnDriftFundamental.periodic_frameNormal_rearOwn
      hkap0 hkap1 S.strip_nonnegative S.strip_le
      (fun a s => S.cos_ne_zero hkap0 hkap1 a s)
      (MarkingAwareSource.successorFrontCore A).front_frenet
      (MarkingAwareSource.successorFrontCore A).angle_frenet
      S.steering S.sf_deriv S.sf_rightInverse S.periodic
      (MarkingAwareSource.successorFrontCore A).front_periodic
      (MarkingAwareSource.successorFrontCore A).angle_periodic
      (ExactSelected.front_contDiff (A := A))
      (ExactSelected.angle_contDiff (A := A)) S.delta_contDiff S.sf_contDiff
      hperiodC R.rear_time t
  have hnormal : ∀ t x, |frameNormal R.Ydot S.psi t x| ≤
      W.Delta.m t / Real.sqrt (1 - kap ^ 2) := by
    intro t x
    exact RearOwnTangentialCost.abs_frameNormal_le_slice
      hkap0 hkap1 S.strip_nonnegative S.strip_le hperiodPos hnormalPeriod
      R.jacobi (rearNormal_bound W) t x
  have hgammaSq : Real.sqrt (1 - kap ^ 2) ^ 2 = 1 - kap ^ 2 :=
    Real.sq_sqrt (by nlinarith)
  intro t x
  have heq : (rawSpatialFrames S R hkap0 hkap1).1.xi1 t x =
      frameNormal R.Ydot S.psi t x * S.kappa t x := rfl
  have htan := RearOwnTangential.abs_tan_le_strip hkap0 hkap1
    (S.strip_nonnegative t (S.sf t x)) (S.strip_le t (S.sf t x))
  have hm : |frameNormal R.Ydot S.psi t x| * |S.kappa t x| ≤
      (W.Delta.m t / Real.sqrt (1 - kap ^ 2)) *
        (kap / Real.sqrt (1 - kap ^ 2)) :=
    mul_le_mul (hnormal t x) (by simpa [ExactSelected.kappa] using htan)
      (abs_nonneg _) (div_nonneg (W.Delta.m_nonneg t)
        (Real.sqrt_nonneg _))
  rw [heq, abs_mul]
  calc
    _ ≤ (W.Delta.m t / Real.sqrt (1 - kap ^ 2)) *
        (kap / Real.sqrt (1 - kap ^ 2)) := hm
    _ = GaugeMarkedDataOfRearFamily.rearKappa1 kap * W.Delta.m t := by
      rw [GaugeMarkedDataOfRearFamily.rearKappa1]
      calc
        (W.Delta.m t / Real.sqrt (1 - kap ^ 2)) *
              (kap / Real.sqrt (1 - kap ^ 2)) =
            (kap / Real.sqrt (1 - kap ^ 2) ^ 2) * W.Delta.m t := by
              field_simp [ne_of_gt (gamma_pos hkap0 hkap1)]
              <;> ring
        _ = (kap / (1 - kap ^ 2)) * W.Delta.m t := by rw [hgammaSq]

theorem raw_xi2_bound (hkap0 : 0 ≤ kap) (hkap1 : kap < 1)
    (hcurv : ∀ t s, |curvature A t s| ≤ kap) :
    ∀ t x, |(rawSpatialFrames S R hkap0 hkap1).1.xi2 t x| ≤
      GaugeMarkedDataOfRearFamily.rearKappa2 kap * W.Delta.m t := by
  let g := Real.sqrt (1 - kap ^ 2)
  have hg : 0 < g := gamma_pos hkap0 hkap1
  have hg2 : g ^ 2 = 1 - kap ^ 2 := Real.sq_sqrt (by nlinarith)
  have hg4 : g ^ 4 = (1 - kap ^ 2) ^ 2 := by rw [show g ^ 4 = (g ^ 2) ^ 2 by ring, hg2]
  intro t x
  have hn := raw_frameNormal_bound W S R hkap0 hkap1 t x
  have hcos : g ≤ Real.cos (S.delta t (S.sf t x)) :=
    Shadowing.cos_ge_of_mem_strip
      (S.strip_nonnegative t (S.sf t x)) (S.strip_le t (S.sf t x))
  have hcpos : 0 < Real.cos (S.delta t (S.sf t x)) := hg.trans_le hcos
  have hsrc : |S.source t x| ≤ W.Delta.m t / g := by
    simp only [ExactSelected.source, abs_div, abs_of_pos hcpos]
    exact div_le_div₀ (W.Delta.m_nonneg t)
      (rearNormal_bound W t (S.sf t x)) hg hcos
  have htan := RearOwnTangential.abs_tan_le_strip hkap0 hkap1
    (S.strip_nonnegative t (S.sf t x)) (S.strip_le t (S.sf t x))
  have hkS : |S.curvatureSpatial t x| ≤ 2 * kap / g ^ 3 := by
    simpa [ExactSelected.curvatureSpatial, g] using
      RearOwnTangential.abs_curvDeriv_le_strip hkap0 hkap1
        (S.strip_nonnegative t (S.sf t x)) (S.strip_le t (S.sf t x))
        (hcurv t (S.sf t x))
  have hA : |S.source t x - frameNormal R.Ydot S.psi t x| ≤
      W.Delta.m t / g + W.Delta.m t / g :=
    (abs_sub _ _).trans (add_le_add hsrc hn)
  have heq : (rawSpatialFrames S R hkap0 hkap1).1.xi2 t x =
      (S.source t x - frameNormal R.Ydot S.psi t x) * S.kappa t x +
        frameNormal R.Ydot S.psi t x * S.curvatureSpatial t x := rfl
  rw [heq]
  calc
    _ ≤ |(S.source t x - frameNormal R.Ydot S.psi t x) * S.kappa t x| +
        |frameNormal R.Ydot S.psi t x * S.curvatureSpatial t x| := abs_add_le _ _
    _ ≤ (W.Delta.m t / g + W.Delta.m t / g) * (kap / g) +
        (W.Delta.m t / g) * (2 * kap / g ^ 3) := by
      rw [abs_mul, abs_mul]
      exact add_le_add
        (mul_le_mul hA (by simpa [ExactSelected.kappa, g] using htan)
          (abs_nonneg _) (add_nonneg (div_nonneg (W.Delta.m_nonneg t) hg.le)
            (div_nonneg (W.Delta.m_nonneg t) hg.le)))
        (mul_le_mul hn hkS (abs_nonneg _)
          (div_nonneg (W.Delta.m_nonneg t) hg.le))
    _ = GaugeMarkedDataOfRearFamily.rearKappa2 kap * W.Delta.m t := by
      rw [GaugeMarkedDataOfRearFamily.rearKappa2,
        RearOwnTangentialCostC2.gaugeGrowth2]
      have hne : g ≠ 0 := hg.ne'
      have hkey :
          (W.Delta.m t / g + W.Delta.m t / g) * (kap / g) +
              W.Delta.m t / g * (2 * kap / g ^ 3) =
            2 * W.Delta.m t * kap / g ^ 2 +
              2 * W.Delta.m t * kap / g ^ 4 := by
        field_simp
        ring
      rw [hkey, hg2, hg4]
      field_simp

/-- Compact support of the chosen density makes the spatial Lipschitz ceiling
global, so the genuine rear gauge exists without an extra gauge callback. -/
theorem exists_gauge (W : ChosenPath Gamma A E.Phi a b)
    (hkap0 : 0 ≤ kap) (hkap1 : kap < 1) :
    Nonempty (RearOwnFrameGaugeFlowReanchoring.Gauge
      (frameTangential R.Ydot S.psi)) := by
  obtain ⟨M, hM0, hM⟩ := SecondOrderBounds.exists_bound_of_vanishing_outside
    W.Delta.cont_m (fun t ht => W.Delta.m_stop t (fun h => ht ⟨h.1.le, h.2.le⟩))
  let L := GaugeMarkedDataOfRearFamily.rearKappa1 kap * M
  have hL : 0 ≤ L := mul_nonneg
    (GaugeMarkedDataOfRearFamily.rearKappa1_nonneg hkap0 hkap1) hM0
  apply RearOwnFrameGaugeFlowReanchoring.exists_gauge
    (rawSpatialFrames S R hkap0 hkap1).1 hL
  intro t x
  exact (raw_xi1_bound W S R hkap0 hkap1 t x).trans
    (mul_le_mul_of_nonneg_left ((le_abs_self _).trans (hM t))
      (GaugeMarkedDataOfRearFamily.rearKappa1_nonneg hkap0 hkap1))

end FiniteSmoothRearFamilyMarkingAwareExactSuccessorGaugeExistence
