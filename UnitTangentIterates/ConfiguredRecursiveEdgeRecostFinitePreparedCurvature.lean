import UnitTangentIterates.ConfiguredRecursiveEdgeRecostedPreCarrier
import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareExactSourceStopping
import UnitTangentIterates.ReachableVariableSpeedFrontCurvatureIntrinsicStable
import UnitTangentIterates.ConfiguredRecursiveEdgeRecostMultiplierHistoryClosing

/-!
# Prepared recursive-edge curvature bridge

This file isolates the two exact transports needed after an active-time
curvature estimate has been obtained on the chosen successor path:

* the chosen gauge marking is surjective, so a pointwise estimate after the
  marking is an intrinsic estimate;
* exact stopping makes successor curvature constant on both complementary
  time rays, so an estimate on the closed active interval holds for all real
  times.

Neither transport uses the front strip estimate or a predecessor curvature
bound.  In particular, the all-real conclusion is driven by the source's
`normal_stopped` certificate and the exact mixed-derivative stopping theorem.
-/

noncomputable section

open Function Set
open MarkedSpace PathMetric

namespace ConfiguredRecursiveEdgeRecostFinitePreparedCurvature

namespace AppliedSource

open FiniteSmoothRearFamilyMarkingAwareAppliedSource
open FiniteSmoothRearFamilyMarkingAwareSource
open FiniteSmoothRearFamilyMarkingAwareSuccessorFront

variable {p q a b : Data} {Gamma : NormalPath p q}
variable {P0 kh khat Qmax K : ℝ}
variable (A : MarkingAwareSource Gamma P0 kh khat Qmax)
variable {E : Applied Gamma A}

/-- The marking of every chosen successor slice is onto the intrinsic rear
arclength line.  This is the exact transport needed to remove the chosen
parameter from a curvature estimate. -/
theorem chosenMarking_surjective
    (W : ChosenPath Gamma A E.Phi a b) (t : ℝ) : Surjective (E.Phi t) := by
  apply surjective_of_continuous_quasiPeriodic
  · exact (MarkingAwareSource.successorFrontCore A).period_pos t
  · exact continuous_iff_continuousAt.2 fun u =>
      (W.phi1_deriv t u).continuousAt
  · exact W.shift t

/-- A strict curvature estimate in the chosen marking is an intrinsic strict
estimate on the entire rear-arclength line. -/
theorem intrinsic_abs_curvature_lt_of_chosen
    (W : ChosenPath Gamma A E.Phi a b)
    {t : ℝ}
    (h : ∀ u, |curvature A t (E.Phi t u)| < K) :
    ∀ s, |curvature A t s| < K := by
  intro s
  obtain ⟨u, rfl⟩ := chosenMarking_surjective A W t s
  exact h u

/-- The corresponding non-strict transport. -/
theorem intrinsic_abs_curvature_le_of_chosen
    (W : ChosenPath Gamma A E.Phi a b)
    {t : ℝ}
    (h : ∀ u, |curvature A t (E.Phi t u)| ≤ K) :
    ∀ s, |curvature A t s| ≤ K := by
  intro s
  obtain ⟨u, rfl⟩ := chosenMarking_surjective A W t s
  exact h u

end AppliedSource

namespace ExactStopping

open FiniteSmoothRearFamilyMarkingAwareCorrelatedRecursion
open FiniteSmoothRearFamilyMarkingAwareExactSourceStopping
open FiniteSmoothRearFamilyMarkingAwareSource
open FiniteSmoothRearFamilyMarkingAwareSuccessorFront

variable {p q : Data} {Gamma : NormalPath p q}
variable {P0 kh khat Qmax K : ℝ}
variable (A : MarkingAwareSource Gamma P0 kh khat Qmax)

/-- Successor curvature is constant on every convex set disjoint from the
active time interval.  The proof uses the stopped normal frame to make the
curvature time derivative exactly zero, then applies the mean-value bound on
the supplied convex set. -/
theorem successorCurvature_eq_on_stopped_convex
    (R : SpatialFrameRegularity Gamma A.Ydot A.Theta A.delta A.sf
      A.P A.m kh Qmax)
    (S : AnalyticSuccessorSliceFacts A)
    {U : Set ℝ} (hU : Convex ℝ U)
    (hout : ∀ r ∈ U, r ∉ Ioo (0 : ℝ) Gamma.T)
    {t r : ℝ} (ht : t ∈ U) (hr : r ∈ U) (x : ℝ) :
    curvature A t x = curvature A r x := by
  let k : ℝ → ℝ := fun z => curvature A z x
  have htime : ∀ z, HasDerivAt k (A.kT z x) z := by
    intro z
    simpa [k, curvature] using A.rear_curvature_time_deriv z x
  have hdiff : ∀ z ∈ U, DifferentiableAt ℝ k z :=
    fun z _ => (htime z).differentiableAt
  have hbound : ∀ z ∈ U, ‖deriv k z‖ ≤ 0 := by
    intro z hz
    have hk := curvatureTime_stopped A R S.normal_stopped
      (hout z hz)
    rw [(htime z).deriv, congrFun hk x]
    simp
  have h := Convex.norm_image_sub_le_of_norm_deriv_le hdiff hbound hU hr ht
  have hz : ‖k t - k r‖ ≤ 0 := by simpa using h
  have hz0 : ‖k t - k r‖ = 0 := le_antisymm hz (norm_nonneg _)
  exact sub_eq_zero.mp (norm_eq_zero.mp hz0)

/-- Curvature agrees with its initial value on the stopped left time ray. -/
theorem successorCurvature_eq_zero_of_nonpos
    (R : SpatialFrameRegularity Gamma A.Ydot A.Theta A.delta A.sf
      A.P A.m kh Qmax)
    (S : AnalyticSuccessorSliceFacts A) {t : ℝ} (ht : t ≤ 0) (x : ℝ) :
    curvature A t x = curvature A 0 x := by
  apply successorCurvature_eq_on_stopped_convex A R S (convex_Iic 0)
  · intro r hr hactive
    exact (not_lt_of_ge (mem_Iic.mp hr)) hactive.1
  · exact mem_Iic.mpr ht
  · exact mem_Iic.mpr le_rfl

/-- Curvature agrees with its terminal value on the stopped right time ray. -/
theorem successorCurvature_eq_terminal_of_ge
    (R : SpatialFrameRegularity Gamma A.Ydot A.Theta A.delta A.sf
      A.P A.m kh Qmax)
    (S : AnalyticSuccessorSliceFacts A) {t : ℝ} (ht : Gamma.T ≤ t) (x : ℝ) :
    curvature A t x = curvature A Gamma.T x := by
  apply successorCurvature_eq_on_stopped_convex A R S (convex_Ici Gamma.T)
  · intro r hr hactive
    exact (not_lt_of_ge (mem_Ici.mp hr)) hactive.2
  · exact mem_Ici.mpr ht
  · exact mem_Ici.mpr le_rfl

/-- An intrinsic estimate on the closed active interval extends to every real
time.  This is the all-real stopped-curvature closure used by prepared
recursion. -/
theorem all_real_abs_curvature_le_of_active
    (R : SpatialFrameRegularity Gamma A.Ydot A.Theta A.delta A.sf
      A.P A.m kh Qmax)
    (S : AnalyticSuccessorSliceFacts A)
    (hactive : ∀ t ∈ Icc (0 : ℝ) Gamma.T, ∀ s, |curvature A t s| ≤ K) :
    ∀ t s, |curvature A t s| ≤ K := by
  intro t s
  by_cases ht0 : 0 ≤ t
  · by_cases htT : t ≤ Gamma.T
    · exact hactive t ⟨ht0, htT⟩ s
    · rw [successorCurvature_eq_terminal_of_ge A R S (le_of_not_ge htT) s]
      exact hactive Gamma.T ⟨Gamma.T_pos.le, le_rfl⟩ s
  · rw [successorCurvature_eq_zero_of_nonpos A R S (le_of_not_ge ht0) s]
    exact hactive 0 ⟨le_rfl, Gamma.T_pos.le⟩ s

end ExactStopping

namespace ChosenStopped

open FiniteSmoothRearFamilyMarkingAwareAppliedSource
open FiniteSmoothRearFamilyMarkingAwareCorrelatedRecursion
open FiniteSmoothRearFamilyMarkingAwareSource
open FiniteSmoothRearFamilyMarkingAwareSuccessorFront

variable {p q a b : Data} {Gamma : NormalPath p q}
variable {P0 kh khat Qmax K : ℝ}
variable (A : MarkingAwareSource Gamma P0 kh khat Qmax)
variable {E : Applied Gamma A}

/-- A strict chosen-path estimate on the active interval gives the non-strict
all-real intrinsic estimate required by `PreparedStepData`. -/
theorem all_real_intrinsic_le_of_chosen_active_lt
    (W : ChosenPath Gamma A E.Phi a b)
    (R : SpatialFrameRegularity Gamma A.Ydot A.Theta A.delta A.sf
      A.P A.m kh Qmax)
    (S : AnalyticSuccessorSliceFacts A)
    (hactive : ∀ t ∈ Icc (0 : ℝ) Gamma.T,
      ∀ u, |curvature A t (E.Phi t u)| < K) :
    ∀ t s, |curvature A t s| ≤ K := by
  apply ExactStopping.all_real_abs_curvature_le_of_active A R S
  intro t ht s
  exact (AppliedSource.intrinsic_abs_curvature_lt_of_chosen A W
    (hactive t ht) s).le

/-- Non-strict active estimates admit the same stopped all-real closure. -/
theorem all_real_intrinsic_le_of_chosen_active_le
    (W : ChosenPath Gamma A E.Phi a b)
    (R : SpatialFrameRegularity Gamma A.Ydot A.Theta A.delta A.sf
      A.P A.m kh Qmax)
    (S : AnalyticSuccessorSliceFacts A)
    (hactive : ∀ t ∈ Icc (0 : ℝ) Gamma.T,
      ∀ u, |curvature A t (E.Phi t u)| ≤ K) :
    ∀ t s, |curvature A t s| ≤ K := by
  apply ExactStopping.all_real_abs_curvature_le_of_active A R S
  intro t ht
  exact AppliedSource.intrinsic_abs_curvature_le_of_chosen A W (hactive t ht)

end ChosenStopped

end ConfiguredRecursiveEdgeRecostFinitePreparedCurvature
