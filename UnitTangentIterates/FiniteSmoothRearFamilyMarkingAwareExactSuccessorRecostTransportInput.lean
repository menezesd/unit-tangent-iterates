import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareExactSuccessorAutomaticBounds
import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareSourceRecostTransport

/-!
# Recost transport input for the automatic exact successor

The automatic exact-successor estimate originally bounds the tangential
period drift by the arbitrary majorant stored in the chosen raw path.  This
module records the stronger pointwise argument: any nonnegative majorant of
the chosen path's normal velocity suffices.  Applying it to the canonical
recost density supplies the `TransportInput` needed to move the theorem-
produced exact source onto that recost.
-/

noncomputable section

open Function Set RearTrack RearOwnArclength RearFamilyFrame

namespace FiniteSmoothRearFamilyMarkingAwareExactSuccessorRecostTransportInput

open FiniteSmoothRearFamilyMarkingAwareSource
  FiniteSmoothRearFamilyMarkingAwareAppliedSource
  FiniteSmoothRearFamilyMarkingAwareSuccessorFront
  FiniteSmoothRearFamilyMarkingAwareExactSuccessorPreTransport
  FiniteSmoothRearFamilyMarkingAwareExactSuccessorGaugeTransport
  FiniteSmoothRearFamilyMarkingAwareExactSuccessorGaugeGeometry
  FiniteSmoothRearFamilyMarkingAwareExactSuccessorReadySource
  FiniteSmoothRearFamilyMarkingAwareExactSuccessorGaugeExistence
  FiniteSmoothRearFamilyMarkingAwareExactSuccessorAutomaticBounds
  FiniteSmoothRearFamilyMarkingAwareSourceRecostTransport

variable {p q a b : MarkedSpace.Data} {Gamma : PathMetric.NormalPath p q}
  {P0 kh khat Qmax kap P0Next khatNext QmaxNext : ℝ}
  {A : MarkingAwareSource Gamma P0 kh khat Qmax}
  {E : Applied Gamma A}
  (W : ChosenPath Gamma A E.Phi a b)
  (S : ExactSelected A (kap := kap))
  (R : PreTransport S)

/-- The raw first spatial derivative only uses a pointwise majorant of the
chosen normal velocity; it does not intrinsically depend on `W.Delta.m`. -/
theorem raw_xi1_bound_of_eta_le
    (hkap0 : 0 ≤ kap) (hkap1 : kap < 1)
    (M : ℝ → ℝ) (hM0 : ∀ t, 0 ≤ M t)
    (heta : ∀ t u, |W.Delta.eta t u| ≤ M t) :
    ∀ t x, |(rawSpatialFrames S R hkap0 hkap1).1.xi1 t x| ≤
      GaugeMarkedDataOfRearFamily.rearKappa1 kap * M t := by
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
      (fun t s => S.cos_ne_zero hkap0 hkap1 t s)
      (MarkingAwareSource.successorFrontCore A).front_frenet
      (MarkingAwareSource.successorFrontCore A).angle_frenet
      S.steering S.sf_deriv S.sf_rightInverse S.periodic
      (MarkingAwareSource.successorFrontCore A).front_periodic
      (MarkingAwareSource.successorFrontCore A).angle_periodic
      (ExactSelected.front_contDiff (A := A))
      (ExactSelected.angle_contDiff (A := A)) S.delta_contDiff S.sf_contDiff
      hperiodC R.rear_time t
  have hrearNormal : ∀ t s, |rearNormal A t s| ≤ M t := by
    intro t s
    have hc : Continuous (E.Phi t) := continuous_iff_continuousAt.2 fun u =>
      (W.phi1_deriv t u).continuousAt
    have hs : Surjective (E.Phi t) :=
      surjective_of_continuous_quasiPeriodic
        ((MarkingAwareSource.successorFrontCore A).period_pos t) hc (W.shift t)
    obtain ⟨u, hu⟩ := hs s
    rw [← hu, ← W.eta_eq t u]
    exact heta t u
  have hnormal : ∀ t x, |frameNormal R.Ydot S.psi t x| ≤
      M t / Real.sqrt (1 - kap ^ 2) := by
    intro t x
    exact RearOwnTangentialCost.abs_frameNormal_le_slice
      hkap0 hkap1 S.strip_nonnegative S.strip_le hperiodPos hnormalPeriod
      R.jacobi hrearNormal t x
  have hgamma : 0 < Real.sqrt (1 - kap ^ 2) :=
    Real.sqrt_pos.mpr (by nlinarith)
  have hgammaSq : Real.sqrt (1 - kap ^ 2) ^ 2 = 1 - kap ^ 2 :=
    Real.sq_sqrt (by nlinarith)
  intro t x
  have heq : (rawSpatialFrames S R hkap0 hkap1).1.xi1 t x =
      frameNormal R.Ydot S.psi t x * S.kappa t x := rfl
  have htan := RearOwnTangential.abs_tan_le_strip hkap0 hkap1
    (S.strip_nonnegative t (S.sf t x)) (S.strip_le t (S.sf t x))
  have hm : |frameNormal R.Ydot S.psi t x| * |S.kappa t x| ≤
      (M t / Real.sqrt (1 - kap ^ 2)) *
        (kap / Real.sqrt (1 - kap ^ 2)) :=
    mul_le_mul (hnormal t x) (by simpa [ExactSelected.kappa] using htan)
      (abs_nonneg _) (div_nonneg (hM0 t) (Real.sqrt_nonneg _))
  rw [heq, abs_mul]
  calc
    _ ≤ (M t / Real.sqrt (1 - kap ^ 2)) *
        (kap / Real.sqrt (1 - kap ^ 2)) := hm
    _ = GaugeMarkedDataOfRearFamily.rearKappa1 kap * M t := by
      rw [GaugeMarkedDataOfRearFamily.rearKappa1]
      calc
        (M t / Real.sqrt (1 - kap ^ 2)) *
              (kap / Real.sqrt (1 - kap ^ 2)) =
            (kap / Real.sqrt (1 - kap ^ 2) ^ 2) * M t := by
              field_simp [hgamma.ne']
              <;> ring
        _ = (kap / (1 - kap ^ 2)) * M t := by rw [hgammaSq]

/-- The second raw spatial derivative has the same pointwise-majorant
strengthening. -/
theorem raw_xi2_bound_of_eta_le
    (hkap0 : 0 ≤ kap) (hkap1 : kap < 1)
    (hcurv : ∀ t s, |curvature A t s| ≤ kap)
    (M : ℝ → ℝ) (hM0 : ∀ t, 0 ≤ M t)
    (heta : ∀ t u, |W.Delta.eta t u| ≤ M t) :
    ∀ t x, |(rawSpatialFrames S R hkap0 hkap1).1.xi2 t x| ≤
      GaugeMarkedDataOfRearFamily.rearKappa2 kap * M t := by
  let g := Real.sqrt (1 - kap ^ 2)
  have hg : 0 < g := Real.sqrt_pos.mpr (by nlinarith)
  have hg2 : g ^ 2 = 1 - kap ^ 2 := Real.sq_sqrt (by nlinarith)
  have hg4 : g ^ 4 = (1 - kap ^ 2) ^ 2 := by
    rw [show g ^ 4 = (g ^ 2) ^ 2 by ring, hg2]
  have hrear : ∀ t s, |rearNormal A t s| ≤ M t := by
    intro t s
    have hc : Continuous (E.Phi t) := continuous_iff_continuousAt.2 fun u =>
      (W.phi1_deriv t u).continuousAt
    have hs : Surjective (E.Phi t) :=
      surjective_of_continuous_quasiPeriodic
        ((MarkingAwareSource.successorFrontCore A).period_pos t) hc (W.shift t)
    obtain ⟨u, hu⟩ := hs s
    rw [← hu, ← W.eta_eq t u]
    exact heta t u
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
      (fun t s => S.cos_ne_zero hkap0 hkap1 t s)
      (MarkingAwareSource.successorFrontCore A).front_frenet
      (MarkingAwareSource.successorFrontCore A).angle_frenet
      S.steering S.sf_deriv S.sf_rightInverse S.periodic
      (MarkingAwareSource.successorFrontCore A).front_periodic
      (MarkingAwareSource.successorFrontCore A).angle_periodic
      (ExactSelected.front_contDiff (A := A))
      (ExactSelected.angle_contDiff (A := A)) S.delta_contDiff S.sf_contDiff
      hperiodC R.rear_time t
  have hnormal : ∀ t x, |frameNormal R.Ydot S.psi t x| ≤ M t / g := by
    intro t x
    exact RearOwnTangentialCost.abs_frameNormal_le_slice
      hkap0 hkap1 S.strip_nonnegative S.strip_le hperiodPos hnormalPeriod
      R.jacobi hrear t x
  intro t x
  have hn := hnormal t x
  have hcos : g ≤ Real.cos (S.delta t (S.sf t x)) :=
    Shadowing.cos_ge_of_mem_strip
      (S.strip_nonnegative t (S.sf t x)) (S.strip_le t (S.sf t x))
  have hcpos : 0 < Real.cos (S.delta t (S.sf t x)) := hg.trans_le hcos
  have hsrc : |S.source t x| ≤ M t / g := by
    simp only [ExactSelected.source, abs_div, abs_of_pos hcpos]
    exact div_le_div₀ (hM0 t) (hrear t (S.sf t x)) hg hcos
  have htan := RearOwnTangential.abs_tan_le_strip hkap0 hkap1
    (S.strip_nonnegative t (S.sf t x)) (S.strip_le t (S.sf t x))
  have hkS : |S.curvatureSpatial t x| ≤ 2 * kap / g ^ 3 := by
    simpa [ExactSelected.curvatureSpatial, g] using
      RearOwnTangential.abs_curvDeriv_le_strip hkap0 hkap1
        (S.strip_nonnegative t (S.sf t x)) (S.strip_le t (S.sf t x))
        (hcurv t (S.sf t x))
  have hA : |S.source t x - frameNormal R.Ydot S.psi t x| ≤
      M t / g + M t / g := (abs_sub _ _).trans (add_le_add hsrc hn)
  have heq : (rawSpatialFrames S R hkap0 hkap1).1.xi2 t x =
      (S.source t x - frameNormal R.Ydot S.psi t x) * S.kappa t x +
        frameNormal R.Ydot S.psi t x * S.curvatureSpatial t x := rfl
  rw [heq]
  calc
    _ ≤ |(S.source t x - frameNormal R.Ydot S.psi t x) * S.kappa t x| +
        |frameNormal R.Ydot S.psi t x * S.curvatureSpatial t x| := abs_add_le _ _
    _ ≤ (M t / g + M t / g) * (kap / g) +
        (M t / g) * (2 * kap / g ^ 3) := by
      rw [abs_mul, abs_mul]
      exact add_le_add
        (mul_le_mul hA (by simpa [ExactSelected.kappa, g] using htan)
          (abs_nonneg _) (add_nonneg (div_nonneg (hM0 t) hg.le)
            (div_nonneg (hM0 t) hg.le)))
        (mul_le_mul hn hkS (abs_nonneg _) (div_nonneg (hM0 t) hg.le))
    _ = GaugeMarkedDataOfRearFamily.rearKappa2 kap * M t := by
      rw [GaugeMarkedDataOfRearFamily.rearKappa2,
        RearOwnTangentialCostC2.gaugeGrowth2]
      have hne : g ≠ 0 := hg.ne'
      have hkey :
          (M t / g + M t / g) * (kap / g) +
              M t / g * (2 * kap / g ^ 3) =
            2 * M t * kap / g ^ 2 + 2 * M t * kap / g ^ 4 := by
        field_simp
        ring
      rw [hkey, hg2, hg4]
      field_simp

/-- The raw Jacobi source derivative is controlled by any pointwise
majorant of the chosen normal velocity. -/
theorem raw_gS_bound_of_eta_le
    (hkap0 : 0 ≤ kap) (hkap1 : kap < 1)
    (hcurv : ∀ t s, |curvature A t s| ≤ kap)
    (M : ℝ → ℝ) (hM0 : ∀ t, 0 ≤ M t)
    (heta : ∀ t u, |W.Delta.eta t u| ≤ M t)
    (hetaDerivative : ∀ t s,
      |A.etaF t (A.sf t s) / Real.cos (A.delta t (A.sf t s)) -
        rearNormal A t s| ≤ derivativeConst (kh := kh) * M t) :
    ∀ t x, |R.gS t x| ≤ sourceConst (kh := kh) (kap := kap) * M t := by
  have hrear : ∀ t s, |rearNormal A t s| ≤ M t := by
    intro t s
    have hc : Continuous (E.Phi t) := continuous_iff_continuousAt.2 fun u =>
      (W.phi1_deriv t u).continuousAt
    have hs : Surjective (E.Phi t) :=
      surjective_of_continuous_quasiPeriodic
        ((MarkingAwareSource.successorFrontCore A).period_pos t) hc (W.shift t)
    obtain ⟨u, hu⟩ := hs s
    rw [← hu, ← W.eta_eq t u]
    exact heta t u
  intro t x
  apply RearJacobiSourceCost.abs_source_deriv_le hkap0 hkap1
    (one_div_pos.mpr (by
      dsimp [derivativeConst,
        FiniteSmoothRearFamilyMarkingAwareSmoothSource.intrinsicDerivativeConst]
      positivity))
    (fun s => by simpa [rearNormal] using A.jacobi t s)
    (hrear t)
    (fun s => by
      simpa [div_eq_mul_inv, mul_comm, derivativeConst] using hetaDerivative t s)
    (S.strip_nonnegative t) (S.strip_le t) (S.steering t)
    (hcurv t)
    (S.sf_deriv t) (R.gS_deriv t) x

/-- The exact source assembled by the automatic bounds satisfies precisely
the two side conditions needed to transport it to the canonical recost. -/
theorem automaticSource_transportInput
    (G : RearOwnFrameGaugeFlowReanchoring.Gauge (xi R))
    (T : ShiftedTransport R G)
    (hkap0 : 0 ≤ kap) (hkap1 : kap < 1)
    (C : Scalar (A := A) (kap := kap) (P0Next := P0Next)
      (khatNext := khatNext) (QmaxNext := QmaxNext))
    (hP0 : 0 < P0Next)
    (hC2 : PathMetric.C2NormalPathData W.Delta)
    (heta : Continuous (Function.uncurry W.Delta.eta))
    (heta1 : Continuous (Function.uncurry hC2.eta1))
    (heta2 : Continuous (Function.uncurry hC2.eta2)) :
    TransportInput
      (source W S R G hkap0 hkap1 T
        (bounds W S R G T hkap0 hkap1 C hP0))
      (CanonicalNormalPathRecost.recost W.Delta hC2 heta heta1 heta2) := by
  let B := bounds W S R G T hkap0 hkap1 C hP0
  let U := source W S R G hkap0 hkap1 T B
  let Delta' := CanonicalNormalPathRecost.recost W.Delta hC2 heta heta1 heta2
  have hperiodPos : ∀ t, 0 < rearArclength (delta S G.q t) (period A t) := by
    intro t
    exact SelectedInverseUnique.rearArclength_pos
      ((MarkingAwareSource.successorFrontCore A).period_pos t) hkap0 hkap1
      ((delta_contDiff S G.contDiff).continuous.comp
        (continuous_const.prodMk continuous_id))
      (fun s => ⟨delta_strip_nonnegative S G.q t s,
        delta_strip_le S G.q t s⟩)
  have hrearLe : ∀ t,
      rearArclength (delta S G.q t) (period A t) ≤ QmaxNext := by
    intro t
    exact (ArclengthInverse.rearArclength_le_of_period
      ((delta_contDiff S G.contDiff).continuous.comp
        (continuous_const.prodMk continuous_id))
      ((MarkingAwareSource.successorFrontCore A).period_pos t).le).trans
      (C.period_le t)
  refine
    { d_nonnegative := ?_
      tangential_period_bound := ?_ }
  · change 0 ≤ B.d
    change 0 ≤ sourceConst (kh := kh) (kap := kap)
    exact RearJacobiSourceCost.jacobiSourceConst_nonneg
      (one_div_pos.mpr (by
        dsimp [derivativeConst,
          FiniteSmoothRearFamilyMarkingAwareSmoothSource.intrinsicDerivativeConst]
        positivity))
  · intro t x hx
    change x ∈ Icc (0 : ℝ)
      (rearArclength (delta S G.q t) (period A t)) at hx
    let psi := rearOwnAngle (Theta S G.q) (delta S G.q) (sf S G.q)
    have hpsi : psi = shiftedPsi R G := by
      funext r y
      exact psi_eq_shift S G.q r y
    change |frameTangential (Ydot R G) psi t x| ≤
      GaugeRearFamilyFromFront.rearDriftConst QmaxNext kap * Delta'.m t
    rw [hpsi]
    let f : ℝ → ℝ := frameTangential (Ydot R G) (shiftedPsi R G) t
    let fp : ℝ → ℝ := fun y =>
      (spatialFrames S R G T hkap0 hkap1).1.xi1 t y
    have hd := RearOwnDriftFundamental.abs_le_of_deriv_le_on_Icc
      (f := f) (f' := fp)
      (le_of_lt (hperiodPos t))
      (fun y => (spatialFrames S R G T hkap0 hkap1).1.deriv1 t y)
      (by
        dsimp [f]
        simpa [Ydot, shiftedPsi, xi] using
          RearOwnFrameGaugeFlowReanchoring.frameTangential_shiftedYdot_zero
            R.Ydot S.psi G.q t)
      (fun y => by
        change |(geometricSpatialFrames S R G T hkap0 hkap1).1.xi1 t y| ≤
          GaugeMarkedDataOfRearFamily.rearKappa1 kap * Delta'.m t
        rw [geometric_xi1_eq_raw S R G T hkap0 hkap1]
        exact raw_xi1_bound_of_eta_le W S R hkap0 hkap1 Delta'.m
          Delta'.m_nonneg Delta'.abs_eta_le t (y + G.q t)) hx
    exact hd.trans (calc
      rearArclength (delta S G.q t) (period A t) *
            (GaugeMarkedDataOfRearFamily.rearKappa1 kap * Delta'.m t) ≤
          QmaxNext *
            (GaugeMarkedDataOfRearFamily.rearKappa1 kap * Delta'.m t) :=
        mul_le_mul_of_nonneg_right (hrearLe t)
          (mul_nonneg
            (GaugeMarkedDataOfRearFamily.rearKappa1_nonneg hkap0 hkap1)
            (Delta'.m_nonneg t))
      _ = GaugeRearFamilyFromFront.rearDriftConst QmaxNext kap *
          Delta'.m t := by
        simp [GaugeRearFamilyFromFront.rearDriftConst,
          GaugeMarkedDataOfRearFamily.rearKappa1]
        ring)

end FiniteSmoothRearFamilyMarkingAwareExactSuccessorRecostTransportInput
