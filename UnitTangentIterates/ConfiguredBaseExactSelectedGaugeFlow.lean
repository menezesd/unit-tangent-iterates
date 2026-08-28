import UnitTangentIterates.ConfiguredBaseExactSelectedPreTransport
import UnitTangentIterates.ConfiguredBaseProfiledSelectedRearGaugeReanchoring
import UnitTangentIterates.PathMetricSlowTest

/-!
# The genuine configured selected-rear gauge flow

This module constructs the rear gauge before any anchor-flow witness is
available.  The raw normal Jacobi equation bounds the raw normal velocity;
the spatial frame formula then bounds the derivative of the raw tangential
field by a constant multiple of the compactly supported path density.
-/

noncomputable section

open Function Set RearTrack PathMetric

namespace ConfiguredBaseExactSelectedGaugeFlow

open ConfiguredApproximateDefectPathActualTerminal
  ConfiguredBaseExactSelectedPreTransport
  ConfiguredBaseProfiledResidualConstructor
  ConfiguredBaseProfiledResidualConstructor.ExactSelected
  ConfiguredBaseProfiledSelectedRearReanchoring
  FiniteSmoothRearFamilyMarkingAwareSource
  RearFamilyFrame RearOwnArclength

variable {D : ConstructedConfiguredSequenceWeighted.Data}
  {Q : ℕ → MarkedSpace.Data} {n : ℕ} {A : RearCarrier D n}
  {H : ConfiguredActualSubunitCurvature.Certificate D}

def spatialFrames (W : Output D Q n A) (S : ExactSelected (n := n) H)
    (P : PreTransport W H S) :
    RearOwnFrameDrift.SpatialC2 (frameTangential P.Ydot (psiR W S)) ×
      RearOwnFrameDrift.SpatialC2 (frameNormal P.Ydot (psiR W S)) :=
  RearOwnFrameSpatialC2OfMixed.spatialC2
    P.Ydot_continuous (psiR_contDiff W S).continuous
    (rear_curvature_contDiff W S).continuous
    P.rear_angle_time_continuous (jacobiSource_continuous W S)
    P.gS_continuous (curvatureSpatial_continuous W S)
    (psiR_spatial W S) P.rear_angle_time_deriv P.mixed P.jacobi
    P.gS_deriv P.curvatureSpatial_deriv

def tangential (W : Output D Q n A) (S : ExactSelected (n := n) H)
    (P : PreTransport W H S) :
    RearOwnFrameDrift.SpatialC2 (frameTangential P.Ydot (psiR W S)) :=
  (spatialFrames W S P).1

private theorem gamma_pos : 0 < auditedGamma H := by
  have hk0 : 0 ≤ H.k0 :=
    (H.front_nonnegative 0 0).trans (H.front_le 0 0)
  exact Real.sqrt_pos.mpr (by nlinarith [H.k0_lt_one])

theorem raw_xi1_bound (W : Output D Q n A)
    (S : ExactSelected (n := n) H) (P : PreTransport W H S) :
    ∀ t x, |(tangential W S P).xi1 t x| ≤
      GaugeMarkedDataOfRearFamily.rearKappa1 H.k0 * W.increment.m t := by
  have hk0 : 0 ≤ H.k0 :=
    (H.front_nonnegative n 0).trans (H.front_le n 0)
  have hperiodPos : ∀ t, 0 < rearArclength (deltaR W S t)
      (ConfiguredBaseInterpolationShiftedFront.period W t) := by
    intro t
    exact SelectedInverseUnique.rearArclength_pos
      ((geometry W).period_pos t) hk0 H.k0_lt_one
      ((deltaR_contDiff W S).continuous.comp
        (continuous_const.prodMk continuous_id))
      (fun s ↦ ⟨deltaR_strip_nonnegative W S t s, deltaR_strip_le W S t s⟩)
  have hnormalPeriod : ∀ t, Periodic (frameNormal P.Ydot (psiR W S) t)
      (rearArclength (deltaR W S t)
        (ConfiguredBaseInterpolationShiftedFront.period W t)) := by
    intro t
    exact RearOwnDriftFundamental.periodic_frameNormal_rearOwn
      hk0 H.k0_lt_one (deltaR_strip_nonnegative W S) (deltaR_strip_le W S)
      (deltaR_cos_ne_zero W S) (geometry W).front_frenet
      (geometry W).angle_frenet (deltaR_steering W S) (sfR_deriv W S)
      (sfR_rightInverse W S) (deltaR_periodic W S)
      (geometry W).front_periodic (geometry W).angle_periodic
      (geometry W).front_contDiff (geometry W).angle_contDiff
      (deltaR_contDiff W S) (sfR_contDiff W S) (by
        simpa [ConfiguredBaseInterpolationShiftedFront.period] using
          (contDiff_const : ContDiff ℝ 1 (fun _ : ℝ ↦ 2 * D.Hs n)))
      P.rear_time t
  have hnormal : ∀ t x, |frameNormal P.Ydot (psiR W S) t x| ≤
      W.increment.m t / auditedGamma H := by
    intro t x
    exact RearOwnTangentialCost.abs_frameNormal_le_slice hk0 H.k0_lt_one
      (deltaR_strip_nonnegative W S) (deltaR_strip_le W S) hperiodPos
      hnormalPeriod P.jacobi (geometry W).etaF_bound t x
  have hgammaSq : auditedGamma H ^ 2 = 1 - H.k0 ^ 2 :=
    Real.sq_sqrt (by nlinarith [hk0, H.k0_lt_one])
  intro t x
  have heq : (tangential W S P).xi1 t x =
      frameNormal P.Ydot (psiR W S) t x * kappaR W S t x := rfl
  have htan := RearOwnTangential.abs_tan_le_strip hk0 H.k0_lt_one
    (deltaR_strip_nonnegative W S t (sfR W S t x))
    (deltaR_strip_le W S t (sfR W S t x))
  have hmul : |frameNormal P.Ydot (psiR W S) t x| * |kappaR W S t x| ≤
      (W.increment.m t / auditedGamma H) * (H.k0 / auditedGamma H) :=
    mul_le_mul (hnormal t x) (by simpa [kappaR] using htan)
      (abs_nonneg _) (div_nonneg (W.increment.m_nonneg t) (gamma_pos (H := H)).le)
  rw [heq, abs_mul]
  calc
    _ ≤ (W.increment.m t / auditedGamma H) *
        (H.k0 / auditedGamma H) := hmul
    _ = GaugeMarkedDataOfRearFamily.rearKappa1 H.k0 * W.increment.m t := by
      rw [GaugeMarkedDataOfRearFamily.rearKappa1, ← hgammaSq]
      field_simp [ne_of_gt (gamma_pos (H := H))]
      <;> ring

/-- The raw tangential field has the exact second-spatial-derivative bound
required by the marking-aware source.  This estimate is independent of the
subsequent gauge reanchoring. -/
theorem raw_xi2_bound (W : Output D Q n A)
    (S : ExactSelected (n := n) H) (P : PreTransport W H S) :
    ∀ t x, |(tangential W S P).xi2 t x| ≤
      GaugeMarkedDataOfRearFamily.rearKappa2 H.k0 * W.increment.m t := by
  have hk0 : 0 ≤ H.k0 :=
    (H.front_nonnegative n 0).trans (H.front_le n 0)
  have hperiodPos : ∀ t, 0 < rearArclength (deltaR W S t)
      (ConfiguredBaseInterpolationShiftedFront.period W t) := by
    intro t
    exact SelectedInverseUnique.rearArclength_pos
      ((geometry W).period_pos t) hk0 H.k0_lt_one
      ((deltaR_contDiff W S).continuous.comp
        (continuous_const.prodMk continuous_id))
      (fun s ↦ ⟨deltaR_strip_nonnegative W S t s, deltaR_strip_le W S t s⟩)
  have hnormalPeriod : ∀ t, Periodic (frameNormal P.Ydot (psiR W S) t)
      (rearArclength (deltaR W S t)
        (ConfiguredBaseInterpolationShiftedFront.period W t)) := by
    intro t
    exact RearOwnDriftFundamental.periodic_frameNormal_rearOwn
      hk0 H.k0_lt_one (deltaR_strip_nonnegative W S) (deltaR_strip_le W S)
      (deltaR_cos_ne_zero W S) (geometry W).front_frenet
      (geometry W).angle_frenet (deltaR_steering W S) (sfR_deriv W S)
      (sfR_rightInverse W S) (deltaR_periodic W S)
      (geometry W).front_periodic (geometry W).angle_periodic
      (geometry W).front_contDiff (geometry W).angle_contDiff
      (deltaR_contDiff W S) (sfR_contDiff W S) (by
        simpa [ConfiguredBaseInterpolationShiftedFront.period] using
          (contDiff_const : ContDiff ℝ 1 (fun _ : ℝ ↦ 2 * D.Hs n)))
      P.rear_time t
  have hnormal : ∀ t x, |frameNormal P.Ydot (psiR W S) t x| ≤
      W.increment.m t / auditedGamma H := by
    intro t x
    exact RearOwnTangentialCost.abs_frameNormal_le_slice hk0 H.k0_lt_one
      (deltaR_strip_nonnegative W S) (deltaR_strip_le W S) hperiodPos
      hnormalPeriod P.jacobi (geometry W).etaF_bound t x
  have hgammaSq : auditedGamma H ^ 2 = 1 - H.k0 ^ 2 :=
    Real.sq_sqrt (by nlinarith [hk0, H.k0_lt_one])
  intro t x
  let M := W.increment.m t
  let N := frameNormal P.Ydot (psiR W S) t x
  let J := jacobiSource W S t x
  let kap := kappaR W S t x
  let kapS := curvatureSpatial W S t x
  have hM0 : 0 ≤ M := W.increment.m_nonneg t
  have hMg : 0 ≤ M / auditedGamma H :=
    div_nonneg hM0 (gamma_pos (H := H)).le
  have hN : |N| ≤ M / auditedGamma H := hnormal t x
  have hJ : |J| ≤ M / auditedGamma H := by
    exact RearOwnTangential.abs_div_cos_le_strip hk0 H.k0_lt_one
      (deltaR_strip_nonnegative W S t (sfR W S t x))
      (deltaR_strip_le W S t (sfR W S t x))
      ((geometry W).etaF_bound t (sfR W S t x))
  have hkap : |kap| ≤ H.k0 / auditedGamma H := by
    exact RearOwnTangential.abs_tan_le_strip hk0 H.k0_lt_one
      (deltaR_strip_nonnegative W S t (sfR W S t x))
      (deltaR_strip_le W S t (sfR W S t x))
  have hkapS : |kapS| ≤ 2 * H.k0 / auditedGamma H ^ 3 := by
    exact RearOwnTangential.abs_curvDeriv_le_strip hk0 H.k0_lt_one
      (deltaR_strip_nonnegative W S t (sfR W S t x))
      (deltaR_strip_le W S t (sfR W S t x))
      ((geometry W).curvature_abs_le_of_actual H le_rfl t (sfR W S t x))
  have hmain : |(J - N) * kap + N * kapS| ≤
      (M / auditedGamma H + M / auditedGamma H) *
          (H.k0 / auditedGamma H) +
        (M / auditedGamma H) * (2 * H.k0 / auditedGamma H ^ 3) := by
    calc
      |(J - N) * kap + N * kapS| ≤
          |J - N| * |kap| + |N| * |kapS| := by
            simpa [abs_mul] using abs_add_le ((J - N) * kap) (N * kapS)
      _ ≤ (|J| + |N|) * |kap| + |N| * |kapS| := by
        gcongr
        exact abs_sub J N
      _ ≤ (M / auditedGamma H + M / auditedGamma H) *
            (H.k0 / auditedGamma H) +
          (M / auditedGamma H) * (2 * H.k0 / auditedGamma H ^ 3) := by
        gcongr
  rw [show (tangential W S P).xi2 t x =
      (J - N) * kap + N * kapS by rfl]
  calc
    |(J - N) * kap + N * kapS| ≤
        (M / auditedGamma H + M / auditedGamma H) *
            (H.k0 / auditedGamma H) +
          (M / auditedGamma H) * (2 * H.k0 / auditedGamma H ^ 3) := hmain
    _ = GaugeMarkedDataOfRearFamily.rearKappa2 H.k0 * M := by
      rw [GaugeMarkedDataOfRearFamily.rearKappa2,
        RearOwnTangentialCostC2.gaugeGrowth2, ← hgammaSq]
      field_simp [ne_of_gt (gamma_pos (H := H))]
      <;> ring

/-- The raw selected rear admits a genuine global gauge flow. -/
theorem exists_gauge (W : Output D Q n A) (S : ExactSelected (n := n) H)
    (P : PreTransport W H S) : Nonempty
    (RearOwnFrameGaugeFlowReanchoring.Gauge
      (frameTangential P.Ydot (psiR W S))) := by
  obtain ⟨M, hM0, hM⟩ := W.increment.exists_bound_m
  let L := GaugeMarkedDataOfRearFamily.rearKappa1 H.k0 * M
  have hkappa0 : 0 ≤ GaugeMarkedDataOfRearFamily.rearKappa1 H.k0 :=
    GaugeMarkedDataOfRearFamily.rearKappa1_nonneg
      ((H.front_nonnegative n 0).trans (H.front_le n 0)) H.k0_lt_one
  have hL : 0 ≤ L := mul_nonneg hkappa0 hM0
  apply RearOwnFrameGaugeFlowReanchoring.exists_gauge (tangential W S P) hL
  intro t x
  exact (raw_xi1_bound W S P t x).trans
    (mul_le_mul_of_nonneg_left (hM t) hkappa0)

/-- The non-circular analytic package retained for the final shifted transport. -/
structure GenuineReanchored (W : Output D Q n A)
    (H : ConfiguredActualSubunitCurvature.Certificate D)
    (S : ExactSelected (n := n) H) where
  preTransport : PreTransport W H S
  gauge : RearOwnFrameGaugeFlowReanchoring.Gauge
    (frameTangential preTransport.Ydot (psiR W S))

theorem exists_genuineReanchored (W : Output D Q n A)
    (S : ExactSelected (n := n) H) : Nonempty (GenuineReanchored W H S) := by
  let P : PreTransport W H S :=
    ConfiguredBaseExactSelectedPreTransport.exact W S
  exact ⟨⟨P, Classical.choice (exists_gauge W S P)⟩⟩

end ConfiguredBaseExactSelectedGaugeFlow
