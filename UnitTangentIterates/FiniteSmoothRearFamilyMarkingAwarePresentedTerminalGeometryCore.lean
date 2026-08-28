import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareAppliedSource
import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareRegularitySum
import UnitTangentIterates.SelectedInverseRearOwnFloorFree
import UnitTangentIterates.SelectedInverseTube
import UnitTangentIterates.ConfiguredGaugeEndpointDefect
import UnitTangentIterates.LimitStrictnessHarnack

/-!
# Pre-output terminal geometry of an exact marking-aware source

This module constructs the ordinary marked terminal directly from the selected
rear at the terminal time.  No long-theorem `Output` is chosen.  The sole
extra geometric premise is nonnegativity of the terminal front curvature; it
is not a field of a generic `MarkingAwareSource`, but is available for the
configured convex sources.
-/

noncomputable section

set_option maxHeartbeats 4000000

open Function Set MarkedSpace PathMetric RearTrack RearOwnArclength

namespace FiniteSmoothRearFamilyMarkingAwarePresentedTerminalGeometry

open FiniteSmoothRearFamilyMarkingAwareSource
  FiniteSmoothRearFamilyMarkingAwareAppliedSource
  FiniteSmoothRearFamilyMarkingAwareRegularitySum
  FiniteSmoothRearFamilyMarkingAwareSuccessorFront
  GaugeMarkedDataOfRearFamily

variable {a b : Data} {Gamma : NormalPath a b}
  {P0 kh khat Qmax : ℝ}

def terminalPeriod (A : MarkingAwareSource Gamma P0 kh khat Qmax) : ℝ :=
  rearArclength (A.delta Gamma.T) (A.P Gamma.T)

def terminalCurve (A : MarkingAwareSource Gamma P0 kh khat Qmax) : ℝ → ℂ :=
  rearOwn A.F A.Theta A.delta A.sf Gamma.T

def terminalAngle (A : MarkingAwareSource Gamma P0 kh khat Qmax) : ℝ → ℝ :=
  rearOwnAngle A.Theta A.delta A.sf Gamma.T

def terminalCurvature (A : MarkingAwareSource Gamma P0 kh khat Qmax) : ℝ → ℝ :=
  fun x ↦ Real.tan (A.delta Gamma.T (A.sf Gamma.T x))

def terminalCurvatureSpatial
    (A : MarkingAwareSource Gamma P0 kh khat Qmax) : ℝ → ℝ :=
  fun x ↦
    (A.K Gamma.T (A.sf Gamma.T x) -
      Real.sin (A.delta Gamma.T (A.sf Gamma.T x))) /
        Real.cos (A.delta Gamma.T (A.sf Gamma.T x)) ^ 3

theorem terminalCurvature_deriv
    (A : MarkingAwareSource Gamma P0 kh khat Qmax) (x : ℝ) :
    HasDerivAt (terminalCurvature A) (terminalCurvatureSpatial A x) x := by
  exact RearOwnTangential.hasDerivAt_rearCurv_space
    A.steering A.sf_deriv A.cos_ne_zero Gamma.T x

theorem terminalCurvature_periodic
    (A : MarkingAwareSource Gamma P0 kh khat Qmax) :
    Periodic (terminalCurvature A) (terminalPeriod A) := by
  intro x
  have hdc : Continuous (A.delta Gamma.T) :=
    A.steering_contDiff.continuous.comp
      (continuous_const.prodMk continuous_id)
  rw [terminalCurvature, terminalPeriod,
    SelectedPathData.sf_add_rearPeriod A.kh_nonnegative A.kh_lt_one hdc
      (A.strip_nonnegative Gamma.T) (A.strip_le Gamma.T)
      (A.steering_periodic Gamma.T) (A.sf_rightInverse Gamma.T) x,
    A.steering_periodic Gamma.T]
  rfl

theorem terminalCurvature_nonnegative
    (A : MarkingAwareSource Gamma P0 kh khat Qmax) (x : ℝ) :
    0 ≤ terminalCurvature A x :=
  (MarkingAwareSource.successorFrontCore A).curvature_nonnegative Gamma.T x

theorem terminalCurvature_bound
    (A : MarkingAwareSource Gamma P0 kh khat Qmax) (x : ℝ) :
    |terminalCurvature A x| ≤ rearKappa1 kh := by
  exact abs_tan_le_rearKappa1 A.kh_nonnegative A.kh_lt_one
    (A.strip_nonnegative Gamma.T (A.sf Gamma.T x))
    (A.strip_le Gamma.T (A.sf Gamma.T x))

theorem terminal_front_curvature_nonzero
    (A : MarkingAwareSource Gamma P0 kh khat Qmax) :
    ∃ s, A.K Gamma.T s ≠ 0 := by
  by_contra h
  push_neg at h
  have hd : ∀ s, HasDerivAt (A.Theta Gamma.T) 0 s := by
    intro s
    simpa [h s] using A.angle_frenet Gamma.T s
  have hc : A.Theta Gamma.T (A.P Gamma.T) = A.Theta Gamma.T 0 :=
    is_const_of_deriv_eq_zero (fun s ↦ (hd s).differentiableAt)
      (fun s ↦ (hd s).deriv) (A.P Gamma.T) 0
  have hp := A.angle_periodic Gamma.T 0
  simp only [zero_add] at hp
  rw [hp] at hc
  linarith [Real.pi_pos]

theorem terminalCurvature_positive
    (A : MarkingAwareSource Gamma P0 kh khat Qmax)
    (hK0 : ∀ s, 0 ≤ A.K Gamma.T s) (x : ℝ) :
    0 < terminalCurvature A x := by
  have hdpos : ∀ s, 0 < A.delta Gamma.T s :=
    LowCurvatureAssembly.steering_pos_of_nonnegative_nonzero
      (A.period_pos Gamma.T) (A.steering_periodic Gamma.T)
      (A.steering Gamma.T) (A.strip_nonnegative Gamma.T) hK0
      (terminal_front_curvature_nonzero A)
  have hdlt : A.delta Gamma.T (A.sf Gamma.T x) < Real.pi / 2 :=
    lt_of_le_of_lt (A.strip_le Gamma.T (A.sf Gamma.T x))
      (Real.arcsin_lt_pi_div_two.mpr A.kh_lt_one)
  exact Real.tan_pos_of_pos_of_lt_pi_div_two
    (hdpos (A.sf Gamma.T x)) hdlt

theorem terminalCurve_embedded
    (A : MarkingAwareSource Gamma P0 kh khat Qmax)
    (hK0 : ∀ s, 0 ≤ A.K Gamma.T s) :
    InjOn (terminalCurve A) (Ico 0 (terminalPeriod A)) := by
  have hinjTrack : InjOn
      (rearTrack (A.F Gamma.T) (A.Theta Gamma.T) (A.delta Gamma.T))
      (Ico 0 (A.P Gamma.T)) := by
    simpa only [zero_add] using
      (RearTrackEmbedded.injOn_rearTrack_of_curvature_nonnegative
      (A.period_pos Gamma.T) A.kh_nonnegative A.kh_lt_one
      (A.front_frenet Gamma.T) (A.angle_frenet Gamma.T) hK0
      (terminal_front_curvature_nonzero A)
      (A.angle_periodic Gamma.T) (A.front_periodic Gamma.T)
      (A.steering_periodic Gamma.T)
      (fun s ↦ ⟨A.strip_nonnegative Gamma.T s, A.strip_le Gamma.T s⟩)
      (A.steering Gamma.T) 0)
  have hdc : Continuous (A.delta Gamma.T) :=
    A.steering_contDiff.continuous.comp
      (continuous_const.prodMk continuous_id)
  have hc : 0 < Real.sqrt (1 - kh ^ 2) := Real.sqrt_pos.2 (by
    nlinarith [A.kh_nonnegative, A.kh_lt_one])
  have hcos : ∀ s, Real.sqrt (1 - kh ^ 2) ≤ Real.cos (A.delta Gamma.T s) :=
    fun s ↦ Shadowing.cos_ge_of_mem_strip
      (A.strip_nonnegative Gamma.T s) (A.strip_le Gamma.T s)
  exact SelectedInverseRearOwn.injOn_rearOwn hc hdc hcos
    (A.sf_rightInverse Gamma.T) hinjTrack

theorem terminalCurve_oval
    (A : MarkingAwareSource Gamma P0 kh khat Qmax)
    (hK0 : ∀ s, 0 ≤ A.K Gamma.T s) :
    MainTheoremConditional.IsOval (terminalCurve A) := by
  have hKhi : ∀ s, A.K Gamma.T s ≤ kh := fun s ↦
    (le_abs_self _).trans (A.curvature_le Gamma.T s)
  have hdc : Continuous (A.delta Gamma.T) :=
    A.steering_contDiff.continuous.comp
      (continuous_const.prodMk continuous_id)
  exact SelectedInverseRearOwn.isOval_rearOwn_floor_free
    (A.period_pos Gamma.T) A.kh_lt_one (A.front_frenet Gamma.T)
    (A.angle_frenet Gamma.T) (A.front_periodic Gamma.T) hK0
    (terminal_front_curvature_nonzero A) hKhi hdc
    (A.steering_periodic Gamma.T)
    (fun s ↦ ⟨A.strip_nonnegative Gamma.T s, A.strip_le Gamma.T s⟩)
    (A.steering Gamma.T) (A.sf_rightInverse Gamma.T)
    (by simpa only [zero_add] using
      (RearTrackEmbedded.injOn_rearTrack_of_curvature_nonnegative
      (A.period_pos Gamma.T) A.kh_nonnegative A.kh_lt_one
      (A.front_frenet Gamma.T) (A.angle_frenet Gamma.T) hK0
      (terminal_front_curvature_nonzero A)
      (A.angle_periodic Gamma.T) (A.front_periodic Gamma.T)
      (A.steering_periodic Gamma.T)
      (fun s ↦ ⟨A.strip_nonnegative Gamma.T s, A.strip_le Gamma.T s⟩)
      (A.steering Gamma.T) 0))

end FiniteSmoothRearFamilyMarkingAwarePresentedTerminalGeometry
