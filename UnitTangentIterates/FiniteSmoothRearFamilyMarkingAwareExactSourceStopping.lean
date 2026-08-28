import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareExactSuccessorSelectionBounds
import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareChosenExactAnalyticSuccessor
import UnitTangentIterates.SelInvDriftRigidity

/-!
# Exact stopping of successor selection fields

For a source with a spatial frame certificate, stopping of its density kills
the spatial derivative of the tangential drift.  The anchored drift therefore
vanishes everywhere.  Together with the stopped normal component this kills
the full rear velocity.  Closing relations and the mixed identity then force
the intrinsic successor period and curvature time derivatives to vanish.
-/

noncomputable section

open Function Set Complex MarkedSpace PathMetric RearTrack RearOwnArclength
  RearFamilyFrame RearOwnHigherRegularity

namespace FiniteSmoothRearFamilyMarkingAwareExactSourceStopping

open FiniteSmoothRearFamilyMarkingAwareSource
  FiniteSmoothRearFamilyMarkingAwareSuccessorFront
  FiniteSmoothRearFamilyMarkingAwareExactSuccessorSelectionBounds

variable {p q : Data} {Gamma : NormalPath p q}
  {P0 kh khat Qmax : ℝ}
  (B : MarkingAwareSource Gamma P0 kh khat Qmax)

private def psi : ℝ → ℝ → ℝ :=
  rearOwnAngle B.Theta B.delta B.sf

private def xi : ℝ → ℝ → ℝ :=
  frameTangential B.Ydot (psi B)

private def eta : ℝ → ℝ → ℝ :=
  frameNormal B.Ydot (psi B)

private def tau : ℝ → ℝ → ℂ := fun t x ↦
  Complex.exp (Complex.I * (psi B t x : ℂ))

/-- Density stopping and the anchored spatial certificate kill tangential
drift at every arclength point. -/
theorem tangential_stopped
    (R : SpatialFrameRegularity Gamma B.Ydot B.Theta B.delta B.sf
      B.P B.m kh Qmax)
    {t : ℝ} (ht : t ∉ Ioo (0 : ℝ) Gamma.T) :
    xi B t = fun _ ↦ 0 := by
  have hm : B.m t = 0 := B.density_support t ht
  have hxi1 : ∀ x, R.tangential.xi1 t x = 0 := by
    intro x
    have h := R.tangential1_bound t x
    rw [hm, mul_zero] at h
    exact abs_eq_zero.mp (le_antisymm h (abs_nonneg _))
  have hdiff : Differentiable ℝ (xi B t) := fun x ↦
    (R.tangential.deriv1 t x).differentiableAt
  have hconst : ∀ x, xi B t x = xi B t 0 := fun x ↦
    is_const_of_deriv_eq_zero hdiff
      (fun y ↦ (R.tangential.deriv1 t y).deriv.trans (hxi1 y)) x 0
  funext x
  rw [hconst x]
  exact B.tangential_zero t

/-- Vanishing of both moving-frame components kills the full rear velocity. -/
theorem velocity_stopped
    (R : SpatialFrameRegularity Gamma B.Ydot B.Theta B.delta B.sf
      B.P B.m kh Qmax)
    (hnormal : ∀ t ∉ Ioo (0 : ℝ) Gamma.T, eta B t = fun _ ↦ 0)
    {t : ℝ} (ht : t ∉ Ioo (0 : ℝ) Gamma.T) :
    B.Ydot t = fun _ ↦ 0 := by
  have hxi := tangential_stopped B R ht
  have heta := hnormal t ht
  funext x
  have h := frame_reconstruct (B.Ydot t x) (psi B t x)
  change ((xi B t x : ℂ) + Complex.I * (eta B t x : ℂ)) * tau B t x =
    B.Ydot t x at h
  rw [hxi, heta] at h
  simpa using h.symm

private theorem period_contDiff : ContDiff ℝ 1 (period B) := by
  have hRA := RearOwnHigherRegularity.contDiff_rearArclengthFamily
    (n := 1) B.steering_contDiff
  exact hRA.comp (contDiff_id.prodMk B.period_contDiff)

/-- The derivative of the intrinsic successor period vanishes whenever the
source is stopped. -/
theorem periodTime_stopped
    (R : SpatialFrameRegularity Gamma B.Ydot B.Theta B.delta B.sf
      B.P B.m kh Qmax)
    (hnormal : ∀ t ∉ Ioo (0 : ℝ) Gamma.T, eta B t = fun _ ↦ 0)
    {t : ℝ} (ht : t ∉ Ioo (0 : ℝ) Gamma.T) :
    SteeringVariablePeriodSelectedInverseJointC1.periodTime (period B) t = 0 := by
  let Y := front B
  let Q := period B
  have C :=
    FiniteSmoothRearFamilyMarkingAwareSuccessorFront.MarkingAwareSource.successorFrontCore B
  have hYC : ContDiff ℝ 1 (uncurry Y) := by
    exact RearOwnArclength.contDiff_one_rearOwn B.front_contDiff B.angle_contDiff
      B.steering_contDiff B.sf_contDiff
  have hYx : ∀ r x, HasDerivAt (Y r) (tau B r x) x := C.front_frenet
  have htaune : ∀ r x, tau B r x ≠ 0 := fun _ _ ↦ Complex.exp_ne_zero _
  have htauper : ∀ r, Periodic (tau B r) (Q r) := by
    intro r x
    have hs := HasDerivAt.comp_add_const x (Q r) (hYx r (x + Q r))
    have hfun : (fun y ↦ Y r (y + Q r)) = Y r := funext (C.front_periodic r)
    rw [hfun] at hs
    exact hs.unique (hYx r x)
  have hYt : ∀ r x, HasDerivAt (fun s ↦ Y s x)
      ((xi B r x : ℂ) * tau B r x +
        (eta B r x : ℂ) * (Complex.I * tau B r x)) r := by
    intro r x
    convert B.rear_time_deriv r x using 1
    have h := frame_reconstruct (B.Ydot r x) (psi B r x)
    change ((xi B r x : ℂ) + Complex.I * (eta B r x : ℂ)) * tau B r x =
      B.Ydot r x at h
    rw [← h]
    ring
  have hQd : ∀ r, HasDerivAt Q
      (SteeringVariablePeriodSelectedInverseJointC1.periodTime Q r) r := by
    intro r
    simpa [SteeringVariablePeriodSelectedInverseJointC1.periodTime] using
      (period_contDiff B).differentiable (by norm_num) r |>.hasDerivAt
  have hclose : ∀ r x, Y r (x + Q r) = Y r x := C.front_periodic
  have hrel := (GaugeClosingRelations.closing_relations hYC hYx hYt htaune
    htauper hclose hQd t 0).1
  have hxi := tangential_stopped B R ht
  rw [hxi] at hrel
  dsimp [Q] at hrel ⊢
  linarith

/-- The mixed identity turns stopped velocity into stopped rear curvature time. -/
theorem curvatureTime_stopped
    (R : SpatialFrameRegularity Gamma B.Ydot B.Theta B.delta B.sf
      B.P B.m kh Qmax)
    (hnormal : ∀ t ∉ Ioo (0 : ℝ) Gamma.T, eta B t = fun _ ↦ 0)
    {t : ℝ} (ht : t ∉ Ioo (0 : ℝ) Gamma.T) :
    B.kT t = fun _ ↦ 0 := by
  have hY := velocity_stopped B R hnormal ht
  have hxi := tangential_stopped B R ht
  have heta := hnormal t ht
  have halpha : B.alphaT t = fun _ ↦ 0 := by
    funext x
    obtain ⟨Z, htan, hvel⟩ := B.mixed_derivative t x
    have hvel0 : HasDerivAt (fun _ : ℝ ↦ (0 : ℂ)) 0 x := hasDerivAt_const x 0
    have hfun : (fun y ↦
        (xi B t y : ℂ) * tau B t y +
          (eta B t y : ℂ) * (Complex.I * tau B t y)) = fun _ ↦ 0 := by
      funext y
      rw [hxi, heta]
      simp
    change HasDerivAt (fun y ↦
      (xi B t y : ℂ) * tau B t y +
        (eta B t y : ℂ) * (Complex.I * tau B t y)) Z x at hvel
    rw [hfun] at hvel
    have hZ : Z = 0 := hvel.unique hvel0
    have htan' : HasDerivAt (fun r ↦ tau B r x)
        (Complex.I * (B.alphaT t x : ℂ) * tau B t x) t := by
      have h1 : HasDerivAt (fun r ↦ Complex.I * ((psi B r x : ℝ) : ℂ))
          (Complex.I * ((B.alphaT t x : ℝ) : ℂ)) t :=
        (B.rear_angle_time_deriv t x).ofReal_comp.const_mul Complex.I
      simpa [tau, mul_comm, mul_assoc] using h1.cexp
    have hz : Complex.I * (B.alphaT t x : ℂ) * tau B t x = 0 := by
      rw [htan'.unique htan, hZ]
    have hn := congrArg norm hz
    simpa [tau] using hn
  funext x
  have hz : HasDerivAt (B.alphaT t) 0 x := by
    rw [halpha]
    exact hasDerivAt_const x 0
  exact (B.rear_angle_time_spatial t x).unique hz

/-- Exact stopping in the normalized coordinates consumed by the next
Taylor-free steering selection. -/
theorem normalizedCurvatureTime_stopped
    (R : SpatialFrameRegularity Gamma B.Ydot B.Theta B.delta B.sf
      B.P B.m kh Qmax)
    (hnormal : ∀ t ∉ Ioo (0 : ℝ) Gamma.T, eta B t = fun _ ↦ 0)
    {t : ℝ} (ht : t ∉ Ioo (0 : ℝ) Gamma.T) :
    partialTime
      (SteeringVariablePeriodSelectedInverseJointC1.normalizedCurvature
        (curvature B) (period B)) t = fun _ ↦ 0 := by
  have hPC := period_contDiff B
  have hkt := curvatureTime_stopped B R hnormal ht
  have hpt := periodTime_stopped B R hnormal ht
  funext u
  have hKnC :=
    SteeringVariablePeriodSelectedInverseJointC1.normalizedCurvature_contDiff_one
      B.rear_curvature_contDiff hPC
  have hd :=
    SteeringVariablePeriodSelectedInverseJointC1.hasDerivAt_normalizedCurvature_time
      B.rear_curvature_contDiff hPC t u
  have hcurv : SteeringVariablePeriodSelectedInverseJointC1.curvatureTime
      (curvature B) t (period B t * u) = 0 := by
    rw [SteeringVariablePeriodSelectedInverseJointC1.curvatureTime,
      FiniteSmoothRearFamilyMarkingAwareExactSelectedOfC1.curvatureTime_eq
        (A := B), hkt]
  have hd0 : HasDerivAt
      (fun r ↦ SteeringVariablePeriodSelectedInverseJointC1.normalizedCurvature
        (curvature B) (period B) r u) 0 t := by
    have hcurv' : SteeringVariablePeriodSelectedInverseJointC1.curvatureTime
        (fun r x ↦ Real.tan (B.delta r (B.sf r x))) t (period B t * u) = 0 := by
      simpa only [curvature] using hcurv
    rw [hcurv', hpt] at hd
    simpa only [curvature, zero_add, zero_mul, mul_zero] using hd
  simpa only [curvature] using
    (hasDerivAt_partialTime (hKnC.differentiable (by norm_num)) t u).unique hd0

/-- A spatial exact source with a stopped normal frame automatically carries
fresh finite bounds for the next selected-steering construction. -/
theorem exists_selectionBounds
    (R : SpatialFrameRegularity Gamma B.Ydot B.Theta B.delta B.sf
      B.P B.m kh Qmax)
    (hnormal : ∀ t ∉ Ioo (0 : ℝ) Gamma.T, eta B t = fun _ ↦ 0)
    (hP0 : 0 < P0)
    (hPl : ∀ t, P0 ≤ B.P t) :
    Nonempty (SelectionBounds B) := by
  apply SelectionBounds.ofExactSourceStopped B hP0 hPl
  · intro t ht
    exact normalizedCurvatureTime_stopped B R hnormal
      (fun h ↦ ht ⟨h.1.le, h.2.le⟩)
  · intro t ht
    exact periodTime_stopped B R hnormal
      (fun h ↦ ht ⟨h.1.le, h.2.le⟩)

end FiniteSmoothRearFamilyMarkingAwareExactSourceStopping
