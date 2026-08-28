import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareSeparatedAppliedSource
import UnitTangentIterates.InterpolationPathDist
import UnitTangentIterates.Bicycle

/-!
# Exact analytic sidecars from an actual chosen path

This module removes the independent analytic-slice callback from the exact
recursive branch.  Once a successor source has been assembled from the
intrinsic selected rear, its period, normal velocity, and marking agree with
the data retained by `ChosenPath`; all fields of `AnalyticSuccessorSliceFacts`
then follow automatically.
-/

noncomputable section

open Function Set MarkedSpace PathMetric RearTrack RearOwnArclength
  RearFamilyFrame

namespace FiniteSmoothRearFamilyMarkingAwareChosenExactAnalyticSuccessor

open FiniteSmoothRearFamilyMarkingAwareAppliedSource
  FiniteSmoothRearFamilyMarkingAwareSource
  FiniteSmoothRearFamilyMarkingAwareCorrelatedRecursion
  FiniteSmoothRearFamilyMarkingAwareSeparatedAppliedSource.Nonaffine

/-- The equalities an intrinsic successor-source constructor must satisfy.
They mention no analytic or quantitative sidecar. -/
structure Compatibility
    {p q a b : Data} {Gamma : NormalPath p q}
    {P0 kh khat Qmax periodLower kap khatNext QmaxNext : ℝ}
    {A : MarkingAwareSource Gamma P0 kh khat Qmax}
    {E : Applied Gamma A} (W : ChosenPath Gamma A E.Phi a b)
    (B : MarkingAwareSource W.Delta periodLower kap khatNext QmaxNext) where
  q : ℝ → ℝ
  period_eq : B.P = rearPeriod A
  etaF_eq : ∀ t s, B.etaF t s = rearNormal A t (s + q t)
  phi_eq : ∀ t u, B.phi t u = E.Phi t u - q t
  phi1_eq : B.phi1 = W.phi1
  phi2_eq : B.phi2 = W.phi2

theorem rearNormal_hasDeriv_deriv
    {p q : Data} {Gamma : NormalPath p q} {P0 kh khat Qmax : ℝ}
    (A : MarkingAwareSource Gamma P0 kh khat Qmax) (t x : ℝ) :
    HasDerivAt (rearNormal A t) (deriv (rearNormal A t) x) x := by
  cases A.frame_regularity with
  | joint hY hpsi =>
      let S := RearOwnFrameDrift.SpatialC2.ofContDiff
        (RearOwnTangential.contDiff_frameNormal hY hpsi)
      exact (S.deriv1 t x).congr_deriv (S.deriv1 t x).deriv.symm
  | spatial S =>
      exact (S.normal.deriv1 t x).congr_deriv
        (S.normal.deriv1 t x).deriv.symm

theorem rearNormal_deriv_continuous
    {p q : Data} {Gamma : NormalPath p q} {P0 kh khat Qmax : ℝ}
    (A : MarkingAwareSource Gamma P0 kh khat Qmax) (t : ℝ) :
    Continuous (deriv (rearNormal A t)) := by
  cases A.frame_regularity with
  | joint hY hpsi =>
      let S := RearOwnFrameDrift.SpatialC2.ofContDiff
        (RearOwnTangential.contDiff_frameNormal hY hpsi)
      have hC : Continuous (S.xi1 t) :=
        S.continuous1.comp (continuous_const.prodMk continuous_id)
      exact hC.congr fun x => (S.deriv1 t x).deriv.symm
  | spatial S =>
      have hC : Continuous (S.normal.xi1 t) :=
        S.normal.continuous1.comp (continuous_const.prodMk continuous_id)
      exact hC.congr fun x => (S.normal.deriv1 t x).deriv.symm

theorem rearNormal_deriv_joint_continuous
    {p q : Data} {Gamma : NormalPath p q} {P0 kh khat Qmax : ℝ}
    (A : MarkingAwareSource Gamma P0 kh khat Qmax) :
    Continuous (uncurry fun t x => deriv (rearNormal A t) x) := by
  cases A.frame_regularity with
  | joint hY hpsi =>
      let S := RearOwnFrameDrift.SpatialC2.ofContDiff
        (RearOwnTangential.contDiff_frameNormal hY hpsi)
      exact S.continuous1.congr fun z => (S.deriv1 z.1 z.2).deriv.symm
  | spatial S =>
      exact S.normal.continuous1.congr fun z =>
        (S.normal.deriv1 z.1 z.2).deriv.symm

theorem rearNormal_c2
    {p q : Data} {Gamma : NormalPath p q} {P0 kh khat Qmax : ℝ}
    (A : MarkingAwareSource Gamma P0 kh khat Qmax) (t : ℝ) :
    ContDiff ℝ (2 : ℕ) (rearNormal A t) := by
  cases A.frame_regularity with
  | joint hY hpsi =>
      have H := RearOwnTangential.contDiff_frameNormal hY hpsi
      exact H.comp (contDiff_const.prodMk contDiff_id)
  | spatial S =>
      exact InterpolationPathDist.contDiff_two_of_derivs
        (S.normal.deriv1 t) (S.normal.deriv2 t)
        (S.normal.continuous2.comp
          (continuous_const.prodMk continuous_id))

theorem rearNormal_periodic
    {p q : Data} {Gamma : NormalPath p q} {P0 kh khat Qmax : ℝ}
    (A : MarkingAwareSource Gamma P0 kh khat Qmax) (t : ℝ) :
    Periodic (rearNormal A t) (rearPeriod A t) := by
  simpa [rearNormal, rearPeriod] using
    RearOwnDriftFundamental.periodic_frameNormal_rearOwn
      A.kh_nonnegative A.kh_lt_one A.strip_nonnegative A.strip_le
      A.cos_ne_zero A.front_frenet A.angle_frenet A.steering A.sf_deriv
      A.sf_rightInverse A.steering_periodic A.front_periodic
      A.angle_periodic A.front_contDiff A.angle_contDiff
      A.steering_contDiff A.sf_contDiff A.period_contDiff
      A.rear_time_deriv t

/-- The rear normal of any exact source is stopped with its underlying normal
path.  This is a consequence of the zero Jacobi source and periodicity, not an
extra source field. -/
theorem normal_stopped_of_source
    {a b : Data} {Delta : NormalPath a b}
    {P0 kh khat Qmax : ℝ}
    (B : MarkingAwareSource Delta P0 kh khat Qmax)
    (t : ℝ) (ht : t ∉ Ioo (0 : ℝ) Delta.T) :
    rearNormal B t = fun _ => 0 := by
  have hm : Delta.m t = 0 := Delta.m_stop t ht
  have heta : ∀ s, B.etaF t s = 0 := by
    intro s
    have h := B.etaF_bound t s
    rw [hm] at h
    exact abs_eq_zero.mp (le_antisymm h (abs_nonneg _))
  have hper : Periodic (rearNormal B t) (rearPeriod B t) :=
    rearNormal_periodic B t
  funext x
  apply Bicycle.eq_zero_of_periodic_of_deriv_eq_neg_mul
    (P := rearPeriod B t) (a := fun _ => 1) (c := 1)
    (by simpa [rearPeriod] using B.rear_period_pos t) hper
  · intro y
    simpa [rearNormal, heta] using B.jacobi t y
  · norm_num
  · intro y
    norm_num

/-- Every analytic slice field is forced by compatibility with the actual
chosen path.  In particular, spatial differentiation of the new intrinsic
normal velocity comes from the old source's retained frame certificate, while
the marking bounds and boundedness are exactly those retained by `ChosenPath`.
-/
def sliceFacts
    {p q a b : Data} {Gamma : NormalPath p q}
    {P0 kh khat Qmax periodLower kap khatNext QmaxNext periodUpper : ℝ}
    {A : MarkingAwareSource Gamma P0 kh khat Qmax}
    {E : Applied Gamma A} (W : ChosenPath Gamma A E.Phi a b)
    (B : MarkingAwareSource W.Delta periodLower kap khatNext QmaxNext)
    (C : Compatibility W B)
    (hperiodLowerPos : 0 < periodLower)
    (hperiodLower : ∀ t, periodLower ≤ B.P t)
    (hperiodUpper : ∀ t, B.P t ≤ periodUpper) :
    AnalyticSuccessorSliceFacts B := by
  let H := chosenMarkingFacts W
  refine
    { periodUpper := periodUpper
      periodLower_pos := hperiodLowerPos
      period_lower := hperiodLower
      period_upper := hperiodUpper
      etaFs := fun t s => deriv (rearNormal A t) (s + C.q t)
      etaF_deriv := ?_
      etaFs_continuous := ?_
      etaF_periodic := ?_
      rearNormal_c2 := rearNormal_c2 B
      normal_stopped := normal_stopped_of_source B
      markingLower := chosenLower W
      markingUpper := chosenUpper W
      marking_increment := ?_
      markingLower_pos := H.lower_positive
      marking_lower := ?_
      markingUpper_nonnegative := H.upper_nonnegative
      marking_upper := ?_
      marked_bdd0 := H.marked_bdd0
      marked_bdd1 := H.marked_bdd1 }
  · intro t s
    have heq : B.etaF t = fun y => rearNormal A t (y + C.q t) :=
      funext (C.etaF_eq t)
    rw [heq]
    simpa [Function.comp_def] using
      (rearNormal_hasDeriv_deriv A t (s + C.q t)).comp s
        ((hasDerivAt_id s).add_const (C.q t))
  · intro t
    exact (rearNormal_deriv_continuous A t).comp
      (continuous_id.add continuous_const)
  · intro t
    rw [C.period_eq]
    intro s
    rw [C.etaF_eq, C.etaF_eq]
    convert rearNormal_periodic A t (s + C.q t) using 1 <;> ring
  · intro t
    have hs := B.phi_shift t 0
    have hs' : B.phi t 1 = B.phi t 0 + B.P t := by simpa using hs
    linarith
  · intro t ht u
    rw [C.phi1_eq]
    exact H.lower t ht u
  · intro t ht u
    rw [C.phi1_eq]
    exact H.upper t ht u

/-- The exact recursive analytic constructor with no arbitrary slice sidecar.
The remaining input is precisely the intrinsic successor source itself and its
three defining compatibility equalities. -/
def ChosenPath.toExactAnalyticSuccessor
    {p q a b : Data} {Gamma : NormalPath p q}
    {P0 kh khat Qmax periodLower kap khatNext QmaxNext periodUpper : ℝ}
    {A : MarkingAwareSource Gamma P0 kh khat Qmax}
    {E : Applied Gamma A} (W : ChosenPath Gamma A E.Phi a b)
    (B : MarkingAwareSource W.Delta periodLower kap khatNext QmaxNext)
    (C : Compatibility W B)
    (hperiodLowerPos : 0 < periodLower)
    (hperiodLower : ∀ t, periodLower ≤ B.P t)
    (hperiodUpper : ∀ t, B.P t ≤ periodUpper) :
    AnalyticSuccessor W.Delta A periodLower kap khatNext QmaxNext :=
  AnalyticSuccessor.exact B
    (sliceFacts W B C hperiodLowerPos hperiodLower hperiodUpper)

end FiniteSmoothRearFamilyMarkingAwareChosenExactAnalyticSuccessor
