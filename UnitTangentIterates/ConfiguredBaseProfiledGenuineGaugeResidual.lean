import UnitTangentIterates.ConfiguredBaseExactSelectedGaugeFlow
import UnitTangentIterates.ConfiguredBaseExactSelectedGaugeTransport

/-! # Final genuine-gauge configured residual -/

noncomputable section

open Function Set RearTrack

namespace ConfiguredBaseProfiledGenuineGaugeResidual

open ConfiguredApproximateDefectPathActualTerminal
  ConfiguredBaseInterpolationMarkingAwareSourceResidual
  ConfiguredBaseInterpolationShiftedFront
  ConfiguredBaseProfiledResidualConstructor
  ConfiguredBaseProfiledResidualConstructor.ExactSelected
  ConfiguredBaseExactSelectedPreTransport
  ConfiguredBaseExactSelectedGaugeTransport
  ConfiguredBaseProfiledSelectedRearReanchoring
  ConfiguredBaseProfiledSelectedRearGaugeReanchoring
  FiniteSmoothRearFamilyMarkingAwareSource
  RearFamilyFrame RearOwnArclength

variable {D : ConstructedConfiguredSequenceWeighted.Data}
  {Q : ℕ → MarkedSpace.Data} {n : ℕ} {A : RearCarrier D n}
  {H : ConfiguredActualSubunitCurvature.Certificate D}

abbrev geom (W : Output D Q n A) (S : ExactSelected (n := n) H)
    (P : PreTransport W H S)
    (G : RearOwnFrameGaugeFlowReanchoring.Gauge (xi P)) :=
  ConfiguredBaseProfiledSelectedRearGaugeReanchoring.geometry W S G.q G.contDiff

def spatialFrames (W : Output D Q n A) (S : ExactSelected (n := n) H)
    (P : PreTransport W H S)
    (G : RearOwnFrameGaugeFlowReanchoring.Gauge (xi P))
    (T : ShiftedTransport P G) :
    RearOwnFrameDrift.SpatialC2
        (frameTangential (Ydot P G)
          (rearOwnAngle (geom W S P G).Theta (delta W S G.q) (sf W S G.q))) ×
      RearOwnFrameDrift.SpatialC2
        (frameNormal (Ydot P G)
          (rearOwnAngle (geom W S P G).Theta (delta W S G.q) (sf W S G.q))) := by
  have hpsi : rearOwnAngle (geom W S P G).Theta (delta W S G.q)
      (sf W S G.q) = shiftedPsi P G := by
    funext t x
    exact psi_eq_shift W S G.q G.contDiff t x
  let R := ConfiguredBaseExactSelectedGaugeFlow.spatialFrames W S P
  let RT := RearOwnFrameDrift.SpatialC2.tangentialReanchorSpatialC2
    R.1 G.contDiff.continuous
  let RN := R.2.shift G.contDiff.continuous
  have htan : frameTangential (Ydot P G)
      (rearOwnAngle (geom W S P G).Theta (delta W S G.q) (sf W S G.q)) =
      RearOwnFrameDrift.SpatialC2.tangentialReanchor
        (frameTangential P.Ydot (psiR W S)) G.q := by
    rw [hpsi]
    funext t x
    exact RearOwnFrameGaugeFlowReanchoring.frameTangential_shiftedYdot
      P.Ydot (psiR W S) G.q t x
  have hnormal : frameNormal (Ydot P G)
      (rearOwnAngle (geom W S P G).Theta (delta W S G.q) (sf W S G.q)) =
      TimeDependentSpatialReanchoring.shift
        (frameNormal P.Ydot (psiR W S)) G.q := by
    rw [hpsi]
    funext t x
    exact RearOwnFrameGaugeFlowReanchoring.frameNormal_shiftedYdot
      P.Ydot (psiR W S) G.q t x
  refine ⟨?_, ?_⟩
  · exact
      { xi1 := RT.xi1
        xi2 := RT.xi2
        deriv1 := by simpa only [htan] using RT.deriv1
        deriv2 := RT.deriv2
        continuous0 := by simpa only [htan] using RT.continuous0
        continuous1 := RT.continuous1
        continuous2 := RT.continuous2 }
  · exact
      { xi1 := RN.xi1
        xi2 := RN.xi2
        deriv1 := by simpa only [hnormal] using RN.deriv1
        deriv2 := RN.deriv2
        continuous0 := by simpa only [hnormal] using RN.continuous0
        continuous1 := RN.continuous1
        continuous2 := RN.continuous2 }

structure Bounds (W : Output D Q n A) (P0 kh khat Qmax : ℝ)
    (S : ExactSelected (n := n) H) (P : PreTransport W H S)
    (G : RearOwnFrameGaugeFlowReanchoring.Gauge (xi P))
    (T : ShiftedTransport P G) where
  Kx : ℝ → ℝ
  Dd : ℝ → ℝ
  m : ℝ → ℝ
  kx : ℝ
  d : ℝ
  rear_period_pos : ∀ t, 0 < rearArclength (delta W S G.q t)
    (ConfiguredBaseInterpolationShiftedFront.period W t)
  rear_period_le : ∀ t, rearArclength (delta W S G.q t)
    (ConfiguredBaseInterpolationShiftedFront.period W t) ≤ Qmax
  tangential1_bound : ∀ t x, |(spatialFrames W S P G T).1.xi1 t x| ≤
    GaugeMarkedDataOfRearFamily.rearKappa1 kh * m t
  tangential2_bound : ∀ t x, |(spatialFrames W S P G T).1.xi2 t x| ≤
    GaugeMarkedDataOfRearFamily.rearKappa2 kh * m t
  tangential_period_bound : ∀ t, ∀ x ∈ Set.Icc (0 : ℝ)
      (rearArclength (delta W S G.q t)
        (ConfiguredBaseInterpolationShiftedFront.period W t)),
    |frameTangential (Ydot P G)
      (rearOwnAngle (geom W S P G).Theta (delta W S G.q) (sf W S G.q)) t x| ≤
      GaugeRearFamilyFromFront.rearDriftConst Qmax kh * W.increment.m t
  rearKappa1_le : GaugeMarkedDataOfRearFamily.rearKappa1 kh ≤ khat
  Kx_bound : ∀ t x, |((geom W S P G).K t (sf W S G.q t x) -
      Real.sin (delta W S G.q t (sf W S G.q t x))) /
      Real.cos (delta W S G.q t (sf W S G.q t x)) ^ 3| ≤ Kx t
  Kx_nonnegative : ∀ t, 0 ≤ Kx t
  Kx_le : ∀ t, Kx t ≤ kx
  gS_bound : ∀ t x, |gS P G t x| ≤ Dd t
  Dd_le : ∀ t, Dd t ≤ d * m t
  density_continuous : Continuous m
  density_nonnegative : ∀ t, 0 ≤ m t
  density_support : ∀ t ∉ Ioo 0 W.increment.T, m t = 0
  density_domination : ∀ t, W.increment.m t / Real.sqrt (1 - kh ^ 2) ≤ m t
  numerical_A : 2 + 2 * khat * GaugeRearFamilyFromFront.rearDriftConst Qmax kh ≤ 1 / P0
  numerical_K : d + 2 + khat ^ 2 + 2 *
    GaugeRearFamilyFromFront.rearDriftConst Qmax kh * kx ≤ 1 / P0 ^ 2 + khat ^ 2

namespace Bounds

/-- Enlarge only the cost density of an already constructed genuine-gauge
source.  All geometric fields and numerical constants are unchanged. -/
def scale (B : Bounds W P0 kh khat Qmax S P G T)
    (C : ℝ) (hC : 1 ≤ C) (hkh0 : 0 ≤ kh) (hkh1 : kh < 1)
    (hd0 : 0 ≤ B.d) : Bounds W P0 kh khat Qmax S P G T where
  Kx := B.Kx
  Dd := B.Dd
  m := fun t ↦ C * B.m t
  kx := B.kx
  d := B.d
  rear_period_pos := B.rear_period_pos
  rear_period_le := B.rear_period_le
  tangential1_bound := by
    intro t x
    exact (B.tangential1_bound t x).trans
      (mul_le_mul_of_nonneg_left
        (le_mul_of_one_le_left (B.density_nonnegative t) hC)
        (GaugeMarkedDataOfRearFamily.rearKappa1_nonneg
          hkh0 hkh1))
  tangential2_bound := by
    intro t x
    exact (B.tangential2_bound t x).trans
      (mul_le_mul_of_nonneg_left
        (le_mul_of_one_le_left (B.density_nonnegative t) hC)
        (GaugeMarkedDataOfRearFamily.rearKappa2_nonneg
          hkh0 hkh1))
  tangential_period_bound := B.tangential_period_bound
  rearKappa1_le := B.rearKappa1_le
  Kx_bound := B.Kx_bound
  Kx_nonnegative := B.Kx_nonnegative
  Kx_le := B.Kx_le
  gS_bound := B.gS_bound
  Dd_le := by
    intro t
    exact (B.Dd_le t).trans
      (mul_le_mul_of_nonneg_left
        (le_mul_of_one_le_left (B.density_nonnegative t) hC)
        hd0)
  density_continuous := continuous_const.mul B.density_continuous
  density_nonnegative := fun t ↦
    mul_nonneg (zero_le_one.trans hC) (B.density_nonnegative t)
  density_support := by
    intro t ht
    rw [B.density_support t ht, mul_zero]
  density_domination := by
    intro t
    exact (B.density_domination t).trans
      (le_mul_of_one_le_left (B.density_nonnegative t) hC)
  numerical_A := B.numerical_A
  numerical_K := B.numerical_K

end Bounds

private theorem auditedGamma_pos : 0 < auditedGamma H := by
  have hk0 : 0 ≤ H.k0 :=
    (H.front_nonnegative 0 0).trans (H.front_le 0 0)
  exact Real.sqrt_pos.mpr (by nlinarith [H.k0_lt_one])

private theorem auditedGamma_le_one : auditedGamma H ≤ 1 := by
  have hk0 : 0 ≤ H.k0 :=
    (H.front_nonnegative 0 0).trans (H.front_le 0 0)
  have hs : 0 ≤ 1 - H.k0 ^ 2 := by nlinarith [H.k0_lt_one]
  have hsq := Real.sq_sqrt hs
  have hg0 := Real.sqrt_nonneg (1 - H.k0 ^ 2)
  dsimp [auditedGamma]
  nlinarith [sq_nonneg H.k0]

private def auditedEtaS (W : Output D Q n A) : ℝ → ℝ → ℝ :=
  fun t s ↦ ProfiledInterpolationFields.enS
    (sourceK0 D n) (sourceK1 D n) D.model.thetaBase (D.Hs n)
    t (s + frontPhase W t)

private theorem auditedEtaS_deriv (W : Output D Q n A) (t s : ℝ) :
    HasDerivAt ((ConfiguredBaseProfiledSelectedRearReanchoring.geometry W).etaF t)
      (auditedEtaS W t s) s := by
  have hshift : HasDerivAt (fun x : ℝ ↦ x + frontPhase W t) 1 s := by
    simpa using (hasDerivAt_id s).add_const (frontPhase W t)
  have h := (W.sourceCertificate.en_space t (s + frontPhase W t)).comp s hshift
  simpa [ConfiguredBaseProfiledSelectedRearReanchoring.geometry,
    ConfiguredBaseProfiledSelectedRearReanchoring.etaF,
    ConfiguredBaseProfiledSelectedRearReanchoring.rawEtaF,
    auditedEtaS, TimeDependentSpatialReanchoring.shift] using h

/-- The complete scalar audit survives the genuine moving gauge because all
spatial estimates are invariant under translation and tangential
renormalization. -/
def auditedBounds (W : Output D Q n A) (P0 khat Qmax : ℝ)
    (H : ConfiguredActualSubunitCurvature.Certificate D)
    (S : ExactSelected (n := n) H) (P : PreTransport W H S)
    (G : RearOwnFrameGaugeFlowReanchoring.Gauge (xi P))
    (T : ShiftedTransport P G)
    (hperiod : ∀ t, ConfiguredBaseInterpolationShiftedFront.period W t ≤ Qmax)
    (hkhat : GaugeMarkedDataOfRearFamily.rearKappa1 H.k0 ≤ khat)
    (hnumA : 2 + 2 * khat *
      GaugeRearFamilyFromFront.rearDriftConst Qmax H.k0 ≤ 1 / P0)
    (hnumK : auditedJacobiSourceConst H + 2 + khat ^ 2 + 2 *
      GaugeRearFamilyFromFront.rearDriftConst Qmax H.k0 *
        SelInvFrontStripC2.stripCurvConst H.k0 ≤
          1 / P0 ^ 2 + khat ^ 2) :
    Bounds W P0 H.k0 khat Qmax S P G T := by
  have hk0 : 0 ≤ H.k0 :=
    (H.front_nonnegative n 0).trans (H.front_le n 0)
  have hgamma : 0 < auditedGamma H := auditedGamma_pos (H := H)
  have hgamma1 : auditedGamma H ≤ 1 := auditedGamma_le_one (H := H)
  have hdensity0 : ∀ t, 0 ≤ auditedDensity W H t := by
    intro t
    exact add_nonneg (div_nonneg (W.increment.m_nonneg t) hgamma.le)
      (mul_nonneg (abs_nonneg _) (W.sourceBounds.hm0 t))
  have hincrement_le : ∀ t, W.increment.m t ≤ auditedDensity W H t := by
    intro t
    have hdiv : W.increment.m t ≤ W.increment.m t / auditedGamma H := by
      rw [le_div_iff₀ hgamma]
      exact mul_le_of_le_one_right (W.increment.m_nonneg t) hgamma1
    exact hdiv.trans (le_add_of_nonneg_right
      (mul_nonneg (abs_nonneg _) (W.sourceBounds.hm0 t)))
  have hrearPeriodPos : ∀ t, 0 < rearArclength (delta W S G.q t)
      (ConfiguredBaseInterpolationShiftedFront.period W t) := by
    intro t
    exact SelectedInverseUnique.rearArclength_pos
      ((geom W S P G).period_pos t) hk0 H.k0_lt_one
      ((delta_contDiff W S G.contDiff).continuous.comp
        (continuous_const.prodMk continuous_id))
      (fun s ↦ ⟨delta_strip_nonnegative W S G.q t s,
        delta_strip_le W S G.q t s⟩)
  have htangential1 : ∀ t x,
      |(spatialFrames W S P G T).1.xi1 t x| ≤
        GaugeMarkedDataOfRearFamily.rearKappa1 H.k0 * auditedDensity W H t := by
    intro t x
    have hraw := ConfiguredBaseExactSelectedGaugeFlow.raw_xi1_bound
      W S P t (x + G.q t)
    exact hraw.trans (mul_le_mul_of_nonneg_left (hincrement_le t)
      (GaugeMarkedDataOfRearFamily.rearKappa1_nonneg hk0 H.k0_lt_one))
  have htangential2 : ∀ t x,
      |(spatialFrames W S P G T).1.xi2 t x| ≤
        GaugeMarkedDataOfRearFamily.rearKappa2 H.k0 * auditedDensity W H t := by
    intro t x
    have hraw := ConfiguredBaseExactSelectedGaugeFlow.raw_xi2_bound
      W S P t (x + G.q t)
    exact hraw.trans (mul_le_mul_of_nonneg_left (hincrement_le t)
      (GaugeMarkedDataOfRearFamily.rearKappa2_nonneg hk0 H.k0_lt_one))
  have htangentialZero : ∀ t, frameTangential (Ydot P G)
      (rearOwnAngle (geom W S P G).Theta (delta W S G.q) (sf W S G.q)) t 0 = 0 := by
    intro t
    have hpsi : rearOwnAngle (geom W S P G).Theta (delta W S G.q)
        (sf W S G.q) = shiftedPsi P G := by
      funext r x
      exact psi_eq_shift W S G.q G.contDiff r x
    rw [hpsi]
    exact RearOwnFrameGaugeFlowReanchoring.frameTangential_shiftedYdot_zero
      P.Ydot (psiR W S) G.q t
  have htangentialPeriod : ∀ t, ∀ x ∈ Icc (0 : ℝ)
      (rearArclength (delta W S G.q t)
        (ConfiguredBaseInterpolationShiftedFront.period W t)),
      |frameTangential (Ydot P G)
        (rearOwnAngle (geom W S P G).Theta (delta W S G.q) (sf W S G.q)) t x| ≤
        GaugeRearFamilyFromFront.rearDriftConst Qmax H.k0 * W.increment.m t := by
    intro t x hx
    have hraw : ∀ y, |(spatialFrames W S P G T).1.xi1 t y| ≤
        GaugeMarkedDataOfRearFamily.rearKappa1 H.k0 * W.increment.m t := by
      intro y
      exact ConfiguredBaseExactSelectedGaugeFlow.raw_xi1_bound
        W S P t (y + G.q t)
    have hfund := RearOwnDriftFundamental.abs_le_of_deriv_le_on_Icc
      (hrearPeriodPos t).le ((spatialFrames W S P G T).1.deriv1 t)
      (htangentialZero t) hraw hx
    have hcoef : rearArclength (delta W S G.q t)
          (ConfiguredBaseInterpolationShiftedFront.period W t) *
          (GaugeMarkedDataOfRearFamily.rearKappa1 H.k0 * W.increment.m t) ≤
        Qmax * (GaugeMarkedDataOfRearFamily.rearKappa1 H.k0 * W.increment.m t) :=
      mul_le_mul_of_nonneg_right
        ((ArclengthInverse.rearArclength_le_of_period
          ((delta_contDiff W S G.contDiff).continuous.comp
            (continuous_const.prodMk continuous_id))
          ((geom W S P G).period_pos t).le).trans (hperiod t))
        (mul_nonneg
          (GaugeMarkedDataOfRearFamily.rearKappa1_nonneg hk0 H.k0_lt_one)
          (W.increment.m_nonneg t))
    refine hfund.trans (hcoef.trans_eq ?_)
    simp [GaugeRearFamilyFromFront.rearDriftConst,
      GaugeMarkedDataOfRearFamily.rearKappa1]
    ring
  have hetas : ∀ t s, |auditedEtaS W t s| ≤ auditedDensity W H t := by
    intro t s
    calc
      |auditedEtaS W t s| ≤ W.sourceBounds.S1 t :=
        W.sourceBounds.hS1bd t (s + frontPhase W t)
      _ ≤ W.sourceBounds.c1 * W.sourceBounds.m t := W.sourceBounds.hS1m t
      _ ≤ |W.sourceBounds.c1| * W.sourceBounds.m t :=
        mul_le_mul_of_nonneg_right (le_abs_self W.sourceBounds.c1)
          (W.sourceBounds.hm0 t)
      _ ≤ auditedDensity W H t := le_add_of_nonneg_left
        (div_nonneg (W.increment.m_nonneg t) hgamma.le)
  have hgSraw : ∀ t x, |P.gS t x| ≤
      auditedJacobiSourceConst H * auditedDensity W H t := by
    intro t x
    apply RearJacobiSourceCost.abs_source_deriv_le hk0 H.k0_lt_one one_pos
      (auditedEtaS_deriv W t)
    · intro s
      exact ((ConfiguredBaseProfiledSelectedRearReanchoring.geometry W).etaF_bound
        t s).trans (hincrement_le t)
    · intro s
      simpa using hetas t s
    · exact deltaR_strip_nonnegative W S t
    · exact deltaR_strip_le W S t
    · exact deltaR_steering W S t
    · exact (ConfiguredBaseProfiledSelectedRearReanchoring.geometry W).curvature_abs_le_of_actual
        H le_rfl t
    · exact sfR_deriv W S t
    · exact P.gS_deriv t
  exact
    { Kx := fun _ ↦ SelInvFrontStripC2.stripCurvConst H.k0
      Dd := fun t ↦ auditedJacobiSourceConst H * auditedDensity W H t
      m := auditedDensity W H
      kx := SelInvFrontStripC2.stripCurvConst H.k0
      d := auditedJacobiSourceConst H
      rear_period_pos := hrearPeriodPos
      rear_period_le := fun t ↦
        (ArclengthInverse.rearArclength_le_of_period
          ((delta_contDiff W S G.contDiff).continuous.comp
            (continuous_const.prodMk continuous_id))
          ((geom W S P G).period_pos t).le).trans (hperiod t)
      tangential1_bound := htangential1
      tangential2_bound := htangential2
      tangential_period_bound := htangentialPeriod
      rearKappa1_le := hkhat
      Kx_bound := fun t x ↦ by
        simpa [SelInvFrontStripC2.stripCurvConst] using
          GaugeRearFamilyFromFront.abs_drift_le hk0 H.k0_lt_one
            ((geom W S P G).curvature_abs_le_of_actual H le_rfl t
              (sf W S G.q t x))
            (delta_strip_nonnegative W S G.q t (sf W S G.q t x))
            (delta_strip_le W S G.q t (sf W S G.q t x))
      Kx_nonnegative := fun _ ↦ SelInvFrontStripC2.stripCurvConst_nonneg hk0
      Kx_le := fun _ ↦ le_rfl
      gS_bound := fun t x ↦ by
        simpa [gS, TimeDependentSpatialReanchoring.shift] using
          hgSraw t (x + G.q t)
      Dd_le := fun _ ↦ le_rfl
      density_continuous :=
        W.increment.cont_m.div_const (auditedGamma H) |>.add
          (continuous_const.mul W.sourceBounds.hmc)
      density_nonnegative := hdensity0
      density_support := fun t ht ↦ by
        have ht' : t ∉ Ioo (0 : ℝ) 1 := by
          simpa [W.increment_time_one] using ht
        simp [auditedDensity, W.increment.m_stop t ht,
          W.sourceBounds.hmstop t ht']
      density_domination := fun t ↦ le_add_of_nonneg_right
        (mul_nonneg (abs_nonneg _) (W.sourceBounds.hm0 t))
      numerical_A := hnumA
      numerical_K := hnumK }

def residual (W : Output D Q n A) (P0 kh khat Qmax : ℝ)
    (H : ConfiguredActualSubunitCurvature.Certificate D) (hkh : H.k0 = kh)
    (S : ExactSelected (n := n) H) (P : PreTransport W H S)
    (G : RearOwnFrameGaugeFlowReanchoring.Gauge (xi P))
    (T : ShiftedTransport P G) (B : Bounds W P0 kh khat Qmax S P G T) :
    Residual W P0 kh khat Qmax := by
  subst kh
  let psi := rearOwnAngle (geom W S P G).Theta (delta W S G.q) (sf W S G.q)
  have hpsi : psi = shiftedPsi P G := by
    funext t x
    exact psi_eq_shift W S G.q G.contDiff t x
  exact
    { geometry := geom W S P G
      delta := delta W S G.q
      sf := sf W S G.q
      Ydot := Ydot P G
      alphaT := alphaT P G
      kT := kT P G
      Kx := B.Kx
      Dd := B.Dd
      gS := gS P G
      m := B.m
      kx := B.kx
      d := B.d
      kh_nonnegative := (H.front_nonnegative n 0).trans (H.front_le n 0)
      kh_lt_one := H.k0_lt_one
      strip_nonnegative := delta_strip_nonnegative W S G.q
      strip_le := delta_strip_le W S G.q
      steering := delta_steering W S G.q G.contDiff
      sf_deriv := sf_deriv W S G.q
      sf_rightInverse := sf_rightInverse W S G.q
      cos_ne_zero := fun t s ↦ ne_of_gt (SelectedPathData.cos_steering_pos
        ((H.front_nonnegative n 0).trans (H.front_le n 0)) H.k0_lt_one
        (delta_strip_nonnegative W S G.q t) (delta_strip_le W S G.q t) s)
      rear_time_deriv := fun t x ↦ by
        convert T.rear_time t x using 1
        funext r
        exact rearOwn_eq_shift W S G.q G.contDiff r x
      steering_contDiff := delta_contDiff W S G.contDiff
      sf_contDiff := sf_contDiff W S G.contDiff
      frame_regularity := FrameRegularity.spatial
        { tangential := (spatialFrames W S P G T).1
          normal := (spatialFrames W S P G T).2
          tangential1_bound := B.tangential1_bound
          tangential2_bound := B.tangential2_bound
          tangential_period_bound := B.tangential_period_bound }
      rear_curvature_contDiff := by
        have heq : (fun t x ↦ Real.tan (delta W S G.q t (sf W S G.q t x))) =
            TimeDependentSpatialReanchoring.shift (kappaR W S) G.q := by
          funext t x
          exact kappa_eq_shift W S G.q t x
        rw [heq]
        exact
          TimeDependentSpatialReanchoring.shift_contDiff
            (rear_curvature_contDiff W S) G.contDiff
      steering_periodic := delta_periodic W S G.q
      rear_period_pos := B.rear_period_pos
      rear_period_le := B.rear_period_le
      anchorPhi := fun _ _ ↦ 0
      anchor_zero := fun _ ↦ rfl
      anchor_flow := by simpa [psi, hpsi] using T.anchor_flow
      jacobi := by
        change ∀ t x, HasDerivAt
          (fun x' ↦ frameNormal (Ydot P G) psi t x')
          ((geom W S P G).etaF t (sf W S G.q t x) /
            Real.cos (delta W S G.q t (sf W S G.q t x)) -
              frameNormal (Ydot P G) psi t x) x
        rw [hpsi]
        intro t x
        convert T.jacobi t x using 1 <;>
          simp only [jacobiSource_eq_shift W S G.q G.contDiff]
      rearKappa1_le := B.rearKappa1_le
      rear_angle_time_deriv := by simpa [psi, hpsi] using T.rear_angle_time_deriv
      rear_curvature_time_deriv := by
        intro t x
        convert T.rear_curvature_time_deriv t x using 1
        funext r
        exact kappa_eq_shift W S G.q r x
      rear_angle_time_continuous := T.rear_angle_time_continuous
      rear_curvature_time_continuous := T.rear_curvature_time_continuous
      rear_angle_time_spatial := T.rear_angle_time_spatial
      mixed_derivative := by simpa [psi, hpsi] using T.mixed
      Kx_bound := B.Kx_bound
      Kx_nonnegative := B.Kx_nonnegative
      Kx_le := B.Kx_le
      Kx_continuous := by
        have heq : (fun t x ↦ ((geom W S P G).K t (sf W S G.q t x) -
            Real.sin (delta W S G.q t (sf W S G.q t x))) /
            Real.cos (delta W S G.q t (sf W S G.q t x)) ^ 3) =
            shiftedCurvatureSpatial P G := by
          funext t x
          exact curvatureSpatial_eq_shift W S G.q G.contDiff t x
        rw [heq]
        exact (curvatureSpatial_continuous W S).comp
          (continuous_fst.prodMk
            (continuous_snd.add (G.contDiff.continuous.comp continuous_fst)))
      gS_deriv := by
        intro t x
        convert T.gS_deriv t x using 1
        funext y
        exact jacobiSource_eq_shift W S G.q G.contDiff t y
      gS_bound := B.gS_bound
      Dd_le := B.Dd_le
      density_continuous := B.density_continuous
      density_nonnegative := B.density_nonnegative
      density_support := B.density_support
      density_domination := B.density_domination
      numerical_A := B.numerical_A
      numerical_K := B.numerical_K }

def baseSource (W : Output D Q n A) (P0 khat Qmax : ℝ)
    (H : ConfiguredActualSubunitCurvature.Certificate D)
    (S : ExactSelected (n := n) H) (P : PreTransport W H S)
    (G : RearOwnFrameGaugeFlowReanchoring.Gauge (xi P))
    (T : ShiftedTransport P G) (B : Bounds W P0 H.k0 khat Qmax S P G T) :
    MarkingAwareSource W.increment P0 H.k0 khat Qmax :=
  Residual.toSourceOfActual W P0 H.k0 khat Qmax
    (residual W P0 H.k0 khat Qmax H rfl S P G T B) H le_rfl

end ConfiguredBaseProfiledGenuineGaugeResidual
