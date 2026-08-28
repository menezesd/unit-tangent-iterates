import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareCompositionRecursiveAnalyticSuccessor
import UnitTangentIterates.MarkingAwareSourceSelectedRearData
import UnitTangentIterates.ConfiguredRecursiveEdgeSourceP0PhysicalBaseSourceAdapter
import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwarePresentedTerminalFrontData
import UnitTangentIterates.PhysicalRearKinematicsShift

/-! # Exact initial normalization for composition successors

The selected-inverse successor uses two spatial reanchorings.  Both fix zero:
the inverse arclength fixes zero, and the gauge flow is initialized at zero.
Consequently the new source has exactly the predecessor front at time zero.
Together with one physical rear certificate this identifies the complete
intrinsic initial `Data`, including its stored velocity and acceleration.
-/

noncomputable section

open Function MarkedSpace PathMetric RearOwnArclength RearTrack
  RearOwnHigherRegularity

namespace FiniteSmoothRearFamilyMarkingAwareCompositionInitialNormalization

open FiniteSmoothRearFamilyMarkingAwareSource
  FiniteSmoothRearFamilyMarkingAwareAppliedSource
  FiniteSmoothRearFamilyMarkingAwareSuccessorFront
  FiniteSmoothRearFamilyMarkingAwareExactSuccessorPreTransport
  FiniteSmoothRearFamilyMarkingAwareExactSuccessorGaugeTransport
  FiniteSmoothRearFamilyMarkingAwareExactSuccessorReadySource
  FiniteSmoothRearFamilyMarkingAwareExactSuccessorGaugeExistence
  FiniteSmoothRearFamilyMarkingAwareExactSelectedOfC1
  FiniteSmoothRearFamilyMarkingAwareRecursiveAnalyticSuccessor
  FiniteSmoothRearFamilyMarkingAwareCompositionRecursiveAnalyticSuccessor
  FiniteSmoothRearFamilyMarkingAwarePresentedTerminalGeometry

variable {p q a b rear frontData : Data} {Gamma : NormalPath p q}
  {P0 kh khat Qmax kap periodLower periodUpper khatNext QmaxNext Md MP : ℝ}
  {A : MarkingAwareSource Gamma P0 kh khat Qmax}
  {E : Applied Gamma A}

private theorem exactSelected_sf_zero
    (S : ExactSelected A (kap := kap))
    (hkap0 : 0 ≤ kap) (hkap1 : kap < 1) :
    S.sf 0 0 = 0 := by
  apply RearBaseDrift.sf_base_zero hkap0 hkap1
  · intro t
    have h : Continuous (fun x : ℝ => (t, x)) :=
      continuous_const.prodMk continuous_id
    simpa [uncurry] using S.delta_contDiff.continuous.comp h
  · exact S.strip_nonnegative
  · exact S.strip_le
  · exact S.sf_rightInverse

/-- The ready-source construction has no residual initial phase. -/
theorem readySource_front_zero
    (W : ChosenPath Gamma A E.Phi a b)
    (S : ExactSelected A (kap := kap))
    (R : PreTransport S)
    (G : RearOwnFrameGaugeFlowReanchoring.Gauge (xi R))
    (hkap0 : 0 ≤ kap) (hkap1 : kap < 1)
    (T : ShiftedTransport R G)
    (B : Bounds (P0Next := periodLower) (khatNext := khatNext)
      (QmaxNext := QmaxNext) W S R G T hkap0 hkap1) :
    (FiniteSmoothRearFamilyMarkingAwareExactSuccessorReadySource.source
      W S R G hkap0 hkap1 T B).F 0 = front A 0 := by
  funext x
  have hsf : S.sf 0 0 = 0 := exactSelected_sf_zero S hkap0 hkap1
  change TimeDependentSpatialReanchoring.shift (front A)
      (FiniteSmoothRearFamilyMarkingAwareExactSuccessorGaugeGeometry.sigma
        S G.q) 0 x = front A 0 x
  simp [TimeDependentSpatialReanchoring.shift,
    FiniteSmoothRearFamilyMarkingAwareExactSuccessorGaugeGeometry.sigma,
    G.initial, hsf]

/-- At terminal time the only marking change is the explicit normalized
spatial phase `sigma / rearPeriod`. -/
theorem readySource_unitTangentData_eq_shift_selectedRearData
    (W : ChosenPath Gamma A E.Phi a b)
    (S : ExactSelected A (kap := kap))
    (R : PreTransport S)
    (G : RearOwnFrameGaugeFlowReanchoring.Gauge (xi R))
    (hkap0 : 0 ≤ kap) (hkap1 : kap < 1)
    (T : ShiftedTransport R G)
    (Bnd : Bounds (P0Next := periodLower) (khatNext := khatNext)
      (QmaxNext := QmaxNext) W S R G T hkap0 hkap1) :
    let B := FiniteSmoothRearFamilyMarkingAwareExactSuccessorReadySource.source
      W S R G hkap0 hkap1 T Bnd
    unitTangentData B = MarkedShift.shiftData
      (FiniteSmoothRearFamilyMarkingAwareExactSuccessorGaugeGeometry.sigma
        S G.q W.Delta.T / period A W.Delta.T)
      (A.selectedRearData W.Delta.T) := by
  dsimp
  let B := FiniteSmoothRearFamilyMarkingAwareExactSuccessorReadySource.source
    W S R G hkap0 hkap1 T Bnd
  let sig := FiniteSmoothRearFamilyMarkingAwareExactSuccessorGaugeGeometry.sigma
    S G.q W.Delta.T
  have hL : period A W.Delta.T ≠ 0 :=
    (MarkingAwareSource.successorFrontCore A).period_pos W.Delta.T |>.ne'
  apply Prod.ext
  · apply BoundedContinuousFunction.ext
    intro u
    change TimeDependentSpatialReanchoring.shift (front A)
        (FiniteSmoothRearFamilyMarkingAwareExactSuccessorGaugeGeometry.sigma
          S G.q) W.Delta.T (period A W.Delta.T * u) =
      front A W.Delta.T
        (period A W.Delta.T *
          (u + sig / period A W.Delta.T))
    simp only [TimeDependentSpatialReanchoring.shift]
    congr 1
    field_simp [hL]
    ring
  · apply Prod.ext
    · apply BoundedContinuousFunction.ext
      intro u
      change (period A W.Delta.T : ℂ) * Complex.exp
          (Complex.I * (angle A W.Delta.T
            (period A W.Delta.T * u + sig) : ℂ)) =
        (period A W.Delta.T : ℂ) * rearOwnTangent A.Theta A.delta A.sf
          W.Delta.T (period A W.Delta.T *
            (u + sig / period A W.Delta.T))
      simp only [rearOwnTangent, angle, rearOwnAngle]
      congr 4
      field_simp [hL]
    · apply BoundedContinuousFunction.ext
      intro u
      change ((period A W.Delta.T : ℂ) ^ 2) *
          (Complex.I *
            ((curvature A W.Delta.T
              (period A W.Delta.T * u + sig) : ℝ) : ℂ) *
            Complex.exp (Complex.I *
              (angle A W.Delta.T
                (period A W.Delta.T * u + sig) : ℂ))) =
        (((period A W.Delta.T ^ 2 * Real.tan
            (A.delta W.Delta.T (A.sf W.Delta.T
              (period A W.Delta.T *
                (u + sig / period A W.Delta.T)))) : ℝ) : ℂ) *
          (Complex.I * rearOwnTangent A.Theta A.delta A.sf W.Delta.T
            (period A W.Delta.T *
              (u + sig / period A W.Delta.T))))
      simp only [curvature, rearOwnTangent, angle, rearOwnAngle]
      have hx : period A W.Delta.T *
          (u + sig / period A W.Delta.T) =
          period A W.Delta.T * u + sig := by
        field_simp [hL]
      rw [hx]
      push_cast
      ring

/-- Physical selected-inverse uniqueness identifies the complete affinely
marked rear data, not only its range. -/
theorem selectedRearData_zero_eq_physicalRear
    {c kmin dlt : ℝ}
    (B : MarkingAwareSource Gamma P0 kap khatNext QmaxNext)
    (K : PhysicalRearLimitKinematics kap rear frontData)
    (hF : B.F 0 = ev frontData) (hP : B.P 0 = perim frontData)
    (hrear : IsTubeMember c kmin dlt rear) :
    B.selectedRearData 0 = rear := by
  have hperiod : rearPeriod B 0 = perim rear :=
    ConfiguredRecursiveEdgeSourceP0PhysicalBaseSourceAdapter.rearPeriod_zero_eq_physicalRear_perim
      B K hF hP
  have hper_ne : perim rear ≠ 0 := by
    rw [← hperiod]
    exact (B.rear_period_pos 0).ne'
  have hcurve : ∀ u, (B.selectedRearData 0).1 u = rear.1 u := by
    intro u
    rw [MarkingAwareSource.selectedRearData_curve,
      MarkingAwareSource.selectedRearCurve]
    rw [ConfiguredRecursiveEdgeSourceP0PhysicalBaseSourceAdapter.rearOwn_zero_eq_physicalRear
      B K hF hP]
    simp [ev, hperiod, hper_ne]
  have hcurveFun : (⇑(B.selectedRearData 0).1) = rear.1 := funext hcurve
  have hvel : ∀ u, (B.selectedRearData 0).2.1 u = rear.2.1 u := by
    intro u
    have H := B.selectedRearData_curve_deriv 0 u
    rw [hcurveFun] at H
    exact H.unique (hrear.hasDerivAt_curve u)
  have hvelFun : (⇑(B.selectedRearData 0).2.1) = rear.2.1 := funext hvel
  have hacc : ∀ u, (B.selectedRearData 0).2.2 u = rear.2.2 u := by
    intro u
    have H := B.selectedRearData_velocity_deriv 0 u
    rw [hvelFun] at H
    exact H.unique (hrear.hasDerivAt_vel u)
  apply Prod.ext
  · exact BoundedContinuousFunction.ext hcurve
  · apply Prod.ext
    · exact BoundedContinuousFunction.ext hvel
    · exact BoundedContinuousFunction.ext hacc

/-- The normalized rear phase induced by shifting the physical front marking
by `frontPhase`. -/
def physicalRearPhase
    (K : PhysicalRearLimitKinematics kap rear frontData)
    (frontPhase : ℝ) : ℝ :=
  rearArclength
      (NormalizedSteeringPhysicalRescaling.deltaPhys K.steering
        (perim frontData))
      (perim frontData * frontPhase) / perim rear

theorem physicalRearPhase_sf
    {cR kR dR : ℝ}
    (K : PhysicalRearLimitKinematics kap rear frontData)
    (hkap0 : 0 ≤ kap) (hkap1 : kap < 1)
    (hcR : 0 < cR) (hrear : IsTubeMember cR kR dR rear)
    (frontPhase : ℝ) :
    K.sf (perim rear * physicalRearPhase K frontPhase) =
      perim frontData * frontPhase := by
  let dl := NormalizedSteeringPhysicalRescaling.deltaPhys K.steering
    (perim frontData)
  have hrearPos : 0 < perim rear := perim_pos hcR hrear
  have hmul : perim rear * physicalRearPhase K frontPhase =
      rearArclength dl (perim frontData * frontPhase) := by
    simpa [physicalRearPhase, dl] using
      (mul_div_cancel₀
        (rearArclength dl (perim frontData * frontPhase)) hrearPos.ne')
  rw [hmul]
  have hdlC : Continuous dl := by
    unfold dl NormalizedSteeringPhysicalRescaling.deltaPhys
    exact (Differentiable.continuous fun u =>
      K.steering.steering u |>.differentiableAt).comp
        (continuous_id.div_const _)
  have hmono : StrictMono (rearArclength dl) :=
    strictMono_rearArclength hdlC hkap1 hkap0
      (fun s => (NormalizedSteeringPhysicalRescaling.deltaPhys_mem
        K.steering (P := perim frontData) s).1)
      (fun s => (NormalizedSteeringPhysicalRescaling.deltaPhys_mem
        K.steering (P := perim frontData) s).2)
  apply hmono.injective
  exact K.arclength_rightInverse _

/-- Phase-aware form of physical selected-inverse uniqueness. -/
theorem selectedRearData_zero_eq_shift_physicalRear
    {cF kF dF cR kR dR : ℝ}
    (B : MarkingAwareSource Gamma P0 kap khatNext QmaxNext)
    (K : PhysicalRearLimitKinematics kap rear frontData)
    (hcF : 0 < cF) (hfront : IsTubeMember cF kF dF frontData)
    (hcR : 0 < cR) (hrear : IsTubeMember cR kR dR rear)
    (frontPhase : ℝ)
    (hF : B.F 0 = ev (MarkedShift.shiftData frontPhase frontData))
    (hP : B.P 0 = perim frontData) :
    B.selectedRearData 0 = MarkedShift.shiftData
      (physicalRearPhase K frontPhase) rear := by
  let rearPhase := physicalRearPhase K frontPhase
  let Ks := K.shift hcF hfront hcR hrear frontPhase rearPhase
    (physicalRearPhase_sf K B.kh_nonnegative B.kh_lt_one hcR hrear frontPhase)
  have hperiod : B.P 0 =
      perim (MarkedShift.shiftData frontPhase frontData) := by
    simpa [SelectedInverseShiftEquivariance.perim_shiftData hfront] using hP
  exact selectedRearData_zero_eq_physicalRear B Ks hF hperiod
    (MarkedShift.isTubeMember_shiftData hrear rearPhase)

/-- The explicit composition-scaled constructor retains exact initial physical
normalization whenever the predecessor front is the physical front of `rear`.
-/
theorem ofScaledReadySource_initial_eq_physicalRear
    (W : ChosenPath Gamma A E.Phi a b)
    (S : ExactSelected A (kap := kap))
    (R : PreTransport S)
    (G : RearOwnFrameGaugeFlowReanchoring.Gauge (xi R))
    (hkap0 : 0 ≤ kap) (hkap1 : kap < 1)
    (T : ShiftedTransport R G)
    (C : FiniteSmoothRearFamilyMarkingAwareExactSuccessorCompositionScale.Scalar
      (A := A) (kap := kap) (P0Next := periodLower)
      (khatNext := khatNext) (QmaxNext := QmaxNext) W)
    (hperiodLower : 0 < periodLower)
    (hPl : ∀ t, periodLower ≤ period A t)
    (hPu : ∀ t, period A t ≤ periodUpper)
    {c kmin dlt : ℝ}
    (K : PhysicalRearLimitKinematics kap rear frontData)
    (hF : front A 0 = ev frontData)
    (hP : period A 0 = perim frontData)
    (hrear : IsTubeMember c kmin dlt rear) :
    let X := ofScaledReadySource W S R G hkap0 hkap1 T C
      hperiodLower hPl hPu
    X.source.selectedRearData 0 = rear := by
  dsimp
  let D := FiniteSmoothRearFamilyMarkingAwareExactSuccessorCompositionScale.scaledBounds
    W S R G T hkap0 hkap1 C hperiodLower
  let B := FiniteSmoothRearFamilyMarkingAwareExactSuccessorReadySource.source
    W S R G hkap0 hkap1 T D
  have hfront : B.F 0 = ev frontData :=
    (readySource_front_zero W S R G hkap0 hkap1 T D).trans hF
  have hperiod : B.P 0 = perim frontData := by
    change period A 0 = perim frontData
    exact hP
  have H := selectedRearData_zero_eq_physicalRear B K hfront hperiod hrear
  simpa [ofScaledReadySource,
    FiniteSmoothRearFamilyMarkingAwareRecursiveAnalyticSuccessor.ofReadySource,
    D, B] using H

/-- A composition successor packaged together with its exact physical initial
rear.  Choosing this structure cannot erase the phase-normalization proof. -/
structure PhysicallyNormalizedCompositionSuccessor
    (Delta : NormalPath a b)
    (A : MarkingAwareSource Gamma P0 kh khat Qmax)
    (periodLower kap khatNext QmaxNext : ℝ) (rear : Data) where
  analytic : CompositionRecursiveAnalyticSuccessor Delta A periodLower kap
    khatNext QmaxNext
  initial_eq : analytic.source.selectedRearData 0 = rear

/-- Phase-aware normalized successor. -/
structure PhaseNormalizedCompositionSuccessor
    (Delta : NormalPath a b)
    (A : MarkingAwareSource Gamma P0 kh khat Qmax)
    (periodLower kap khatNext QmaxNext : ℝ) (rear : Data) where
  analytic : CompositionRecursiveAnalyticSuccessor Delta A periodLower kap
    khatNext QmaxNext
  phase : ℝ
  initial_eq : analytic.source.selectedRearData 0 =
    MarkedShift.shiftData phase rear

/-- The unconditional scaled chosen-path constructor, strengthened to retain
the exact physical initial rear. -/
theorem ChosenPath.exists_physicallyNormalizedCompositionSuccessor
    (W : ChosenPath Gamma A E.Phi a b)
    (hperiodLower : 0 < periodLower)
    (hkap0 : 0 ≤ kap) (hkap1 : kap < 1)
    (hPl : ∀ t, periodLower ≤ period A t)
    (hPu : ∀ t, period A t ≤ periodUpper)
    (hKnTbd : ∀ t u,
      |partialTime
        (SteeringVariablePeriodSelectedInverseJointC1.normalizedCurvature
          (curvature A) (period A)) t u| ≤ Md)
    (hPtbd : ∀ t,
      |SteeringVariablePeriodSelectedInverseJointC1.periodTime (period A) t| ≤ MP)
    (C : FiniteSmoothRearFamilyMarkingAwareExactSuccessorCompositionScale.Scalar
      (A := A) (kap := kap) (P0Next := periodLower)
      (khatNext := khatNext) (QmaxNext := QmaxNext) W)
    {c kmin dlt : ℝ}
    (K : PhysicalRearLimitKinematics kap rear frontData)
    (hF : front A 0 = ev frontData)
    (hP : period A 0 = perim frontData)
    (hrear : IsTubeMember c kmin dlt rear) :
    Nonempty (PhysicallyNormalizedCompositionSuccessor W.Delta A
      periodLower kap khatNext QmaxNext rear) := by
  obtain ⟨S⟩ := exists_exactSelected (A := A)
    hperiodLower hkap0 hkap1 hPl hPu
    (fun t s ↦ (le_abs_self (curvature A t s)).trans
      (C.toScalar.curvature_le t s))
    hKnTbd hPtbd
  let R : PreTransport S :=
    FiniteSmoothRearFamilyMarkingAwareExactSuccessorPreTransport.exact
      S hkap0 hkap1
  obtain ⟨G⟩ := exists_gauge S R W hkap0 hkap1
  let T : ShiftedTransport R G :=
    FiniteSmoothRearFamilyMarkingAwareExactSuccessorGaugeTransport.exact
      R G hkap0 hkap1
  let X := ofScaledReadySource W S R G hkap0 hkap1 T C
    hperiodLower hPl hPu
  refine ⟨⟨X, ?_⟩⟩
  exact ofScaledReadySource_initial_eq_physicalRear W S R G hkap0 hkap1
    T C hperiodLower hPl hPu K hF hP hrear

/-- Phase-aware unconditional constructor.  It is the form preserved by
recursive terminal reanchoring. -/
theorem ChosenPath.exists_phaseNormalizedCompositionSuccessor
    (W : ChosenPath Gamma A E.Phi a b)
    (hperiodLower : 0 < periodLower)
    (hkap0 : 0 ≤ kap) (hkap1 : kap < 1)
    (hPl : ∀ t, periodLower ≤ period A t)
    (hPu : ∀ t, period A t ≤ periodUpper)
    (hKnTbd : ∀ t u,
      |partialTime
        (SteeringVariablePeriodSelectedInverseJointC1.normalizedCurvature
          (curvature A) (period A)) t u| ≤ Md)
    (hPtbd : ∀ t,
      |SteeringVariablePeriodSelectedInverseJointC1.periodTime (period A) t| ≤ MP)
    (C : FiniteSmoothRearFamilyMarkingAwareExactSuccessorCompositionScale.Scalar
      (A := A) (kap := kap) (P0Next := periodLower)
      (khatNext := khatNext) (QmaxNext := QmaxNext) W)
    {cF kF dF cR kR dR : ℝ}
    (K : PhysicalRearLimitKinematics kap rear frontData)
    (hcF : 0 < cF) (hfront : IsTubeMember cF kF dF frontData)
    (hcR : 0 < cR) (hrear : IsTubeMember cR kR dR rear)
    (frontPhase : ℝ)
    (hF : front A 0 = ev (MarkedShift.shiftData frontPhase frontData))
    (hP : period A 0 = perim frontData) :
    Nonempty (PhaseNormalizedCompositionSuccessor W.Delta A
      periodLower kap khatNext QmaxNext rear) := by
  obtain ⟨S⟩ := exists_exactSelected (A := A)
    hperiodLower hkap0 hkap1 hPl hPu
    (fun t s ↦ (le_abs_self (curvature A t s)).trans
      (C.toScalar.curvature_le t s))
    hKnTbd hPtbd
  let R : PreTransport S :=
    FiniteSmoothRearFamilyMarkingAwareExactSuccessorPreTransport.exact
      S hkap0 hkap1
  obtain ⟨G⟩ := exists_gauge S R W hkap0 hkap1
  let T : ShiftedTransport R G :=
    FiniteSmoothRearFamilyMarkingAwareExactSuccessorGaugeTransport.exact
      R G hkap0 hkap1
  let D := FiniteSmoothRearFamilyMarkingAwareExactSuccessorCompositionScale.scaledBounds
    W S R G T hkap0 hkap1 C hperiodLower
  let B := FiniteSmoothRearFamilyMarkingAwareExactSuccessorReadySource.source
    W S R G hkap0 hkap1 T D
  let X := ofScaledReadySource W S R G hkap0 hkap1 T C
    hperiodLower hPl hPu
  let rearPhase := physicalRearPhase K frontPhase
  have hBF : B.F 0 = ev (MarkedShift.shiftData frontPhase frontData) :=
    (readySource_front_zero W S R G hkap0 hkap1 T D).trans hF
  have hBP : B.P 0 = perim frontData := by
    change period A 0 = perim frontData
    exact hP
  have H := selectedRearData_zero_eq_shift_physicalRear B K hcF hfront
    hcR hrear frontPhase hBF hBP
  refine ⟨⟨X, rearPhase, ?_⟩⟩
  simpa [X, ofScaledReadySource,
    FiniteSmoothRearFamilyMarkingAwareRecursiveAnalyticSuccessor.ofReadySource,
    D, B, rearPhase] using H

end FiniteSmoothRearFamilyMarkingAwareCompositionInitialNormalization
