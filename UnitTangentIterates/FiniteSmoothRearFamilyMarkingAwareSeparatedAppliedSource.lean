import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareAppliedSource
import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareCorrelatedRecursion
import UnitTangentIterates.GaugeGeometryVariableSeparatedFlowed
import UnitTangentIterates.GaugeNormalPathVariableSeparatedNonaffine

/-!
# Separated sidecar for a marking-aware long application

The ordinary marking-aware application remains unchanged.  This module adds
the sharp separated certificate when the source also satisfies the affine
alignment and slice hypotheses required by the existing separated gauge
theorem.  The sidecar uses the very same `Applied.Phi`, hence transports to
the same subsequently chosen path.
-/

noncomputable section

open Set Function MarkedSpace MarkedTopology PathMetric PathMetric.NormalPath
  RearTrack RearOwnArclength RearFamilyFrame

namespace FiniteSmoothRearFamilyMarkingAwareSeparatedAppliedSource

open FiniteSmoothRearFamilyMarkingAwareAppliedSource
  FiniteSmoothRearFamilyMarkingAwareSource
  GaugeMarkedDataOfRearFamily
  GaugeNormalPathSeparated

namespace Nonaffine

open GaugeNormalPathVariableSeparatedNonaffine

/-- Quantitative replacement for the false affine source-marking assertion.
The two boundedness fields are automatic from a retained `C2NormalPathData`,
but are kept here so this sidecar also applies to the lighter source API. -/
structure Facts
    {p q : Data} {Gamma : NormalPath p q}
    {P0 kh khat Qmax : ℝ} (A : MarkingAwareSource Gamma P0 kh khat Qmax)
    (P1 m M : ℝ) where
  P0_pos : 0 < P0
  period_lower : ∀ t, P0 ≤ A.P t
  period_upper : ∀ t, A.P t ≤ P1
  etaFs : ℝ → ℝ → ℝ
  etaF_deriv : ∀ t s, HasDerivAt (A.etaF t) (etaFs t s) s
  etaFs_continuous : ∀ t, Continuous (etaFs t)
  etaF_periodic : ∀ t, Periodic (A.etaF t) (A.P t)
  rearNormal_c2 : ∀ t, ContDiff ℝ (2 : ℕ) (rearNormal A t)
  normal_stopped : ∀ t ∉ Ioo (0 : ℝ) Gamma.T,
    rearNormal A t = fun _ ↦ 0
  marking_increment : ∀ t, A.phi t 1 - A.phi t 0 = A.P t
  marking_lower_positive : 0 < m
  marking_lower : ∀ t ∈ Ioo (0 : ℝ) Gamma.T, ∀ u, m ≤ A.phi1 t u
  marking_upper_nonnegative : 0 ≤ M
  marking_upper : ∀ t ∈ Ioo (0 : ℝ) Gamma.T, ∀ u, A.phi1 t u ≤ M
  marked_bdd0 : ∀ t, BddAbove (Set.range fun u ↦ |Gamma.eta t u|)
  marked_bdd1 : ∀ t, BddAbove
    (Set.range fun u ↦ |iteratedDeriv 1 (Gamma.eta t) u|)

def chosenLower
    {p q a b : Data} {Gamma : NormalPath p q}
    {P0 kh khat Qmax : ℝ} {A : MarkingAwareSource Gamma P0 kh khat Qmax}
    {E : Applied Gamma A} (W : ChosenPath Gamma A E.Phi a b) : ℝ :=
  rearPeriod A 0 * Real.exp (-(W.phiRateLip * Gamma.T))

def chosenUpper
    {p q a b : Data} {Gamma : NormalPath p q}
    {P0 kh khat Qmax : ℝ} {A : MarkingAwareSource Gamma P0 kh khat Qmax}
    {E : Applied Gamma A} (_W : ChosenPath Gamma A E.Phi a b) : ℝ :=
  GaugeFlowDerivCost.costP1 (rearPeriod A 0) khat
    (∫ t in (0 : ℝ)..Gamma.T, A.m t)

/-- The marking part of the next recursive separated sidecar, automatically
retained by the same chosen path. -/
structure ChosenMarkingFacts
    {p q a b : Data} {Gamma : NormalPath p q}
    {P0 kh khat Qmax : ℝ} {A : MarkingAwareSource Gamma P0 kh khat Qmax}
    {E : Applied Gamma A} (W : ChosenPath Gamma A E.Phi a b) : Prop where
  base : ∀ t, E.Phi t 0 = 0
  lower_positive : 0 < chosenLower W
  lower : ∀ t ∈ Ioo (0 : ℝ) W.Delta.T, ∀ u,
    chosenLower W ≤ W.phi1 t u
  upper_nonnegative : 0 ≤ chosenUpper W
  upper : ∀ t ∈ Ioo (0 : ℝ) W.Delta.T, ∀ u,
    W.phi1 t u ≤ chosenUpper W
  second : ∀ t u, |W.phi2 t u| ≤
    GaugeFlowDerivCost.costG1 (rearPeriod A 0) khat
      (GaugeMarkedDataOfRearFamily.rearKappa2 kh)
      (∫ t in (0 : ℝ)..Gamma.T, A.m t)
  marked_bdd0 : ∀ t, BddAbove (Set.range fun u ↦ |W.Delta.eta t u|)
  marked_bdd1 : ∀ t, BddAbove
    (Set.range fun u ↦ |iteratedDeriv 1 (W.Delta.eta t) u|)

theorem chosenMarkingFacts
    {p q a b : Data} {Gamma : NormalPath p q}
    {P0 kh khat Qmax : ℝ} {A : MarkingAwareSource Gamma P0 kh khat Qmax}
    {E : Applied Gamma A} (W : ChosenPath Gamma A E.Phi a b) :
    ChosenMarkingFacts W := by
  have hlower : ∀ t ∈ Ioo (0 : ℝ) W.Delta.T, ∀ u,
      chosenLower W ≤ W.phi1 t u := by
    intro t ht u
    have htGamma : t ≤ Gamma.T := by rw [← W.time_eq]; exact ht.2.le
    have hexp : Real.exp (-(W.phiRateLip * Gamma.T)) ≤
        Real.exp (-(W.phiRateLip * |t|)) := by
      apply Real.exp_le_exp.mpr
      rw [abs_of_pos ht.1]
      exact neg_le_neg (mul_le_mul_of_nonneg_left htGamma W.phiRateLip_nonnegative)
    exact (mul_le_mul_of_nonneg_left hexp (A.rear_period_pos 0).le).trans
      (W.phi1_lower t u)
  have hbdd1 : ∀ t, BddAbove
      (Set.range fun u ↦ |iteratedDeriv 1 (W.Delta.eta t) u|) := by
    intro t
    have hd : iteratedDeriv 1 (W.Delta.eta t) = W.c2.eta1 t := by
      rw [iteratedDeriv_one]
      funext u
      exact (W.c2.eta_deriv t u).deriv
    rw [hd]
    exact W.c2.eta1_bdd t
  exact {
    base := E.base
    lower_positive := mul_pos (A.rear_period_pos 0) (Real.exp_pos _)
    lower := hlower
    upper_nonnegative := (GaugeFlowDerivCost.costP1_pos (A.rear_period_pos 0)).le
    upper := fun t _ u ↦ W.phi1_upper t u
    second := W.phi2_abs
    marked_bdd0 := fun t ↦ ⟨W.Delta.m t, by
      rintro _ ⟨u, rfl⟩
      exact W.Delta.abs_eta_le t u⟩
    marked_bdd1 := hbdd1 }

/-- Slice geometry needed at the next level, with all marking information
removed.  The latter is preserved automatically by `chosenMarkingFacts`. -/
structure SuccessorSliceFacts
    {a b : Data} {Delta : NormalPath a b}
    {P0 kh khat Qmax : ℝ} (A : MarkingAwareSource Delta P0 kh khat Qmax)
    (P1 : ℝ) where
  P0_pos : 0 < P0
  period_lower : ∀ t, P0 ≤ A.P t
  period_upper : ∀ t, A.P t ≤ P1
  etaFs : ℝ → ℝ → ℝ
  etaF_deriv : ∀ t s, HasDerivAt (A.etaF t) (etaFs t s) s
  etaFs_continuous : ∀ t, Continuous (etaFs t)
  etaF_periodic : ∀ t, Periodic (A.etaF t) (A.P t)
  rearNormal_c2 : ∀ t, ContDiff ℝ (2 : ℕ) (rearNormal A t)
  normal_stopped : ∀ t ∉ Ioo (0 : ℝ) Delta.T,
    rearNormal A t = fun _ ↦ 0

/-- Exact analytic successors now retain precisely this source-tied package. -/
def SuccessorSliceFacts.ofAnalytic
    {a b : Data} {Delta : NormalPath a b}
    {periodLower kap khatNext QmaxNext : ℝ}
    {A : MarkingAwareSource Delta periodLower kap khatNext QmaxNext}
    (S : FiniteSmoothRearFamilyMarkingAwareCorrelatedRecursion.AnalyticSuccessorSliceFacts A) :
    SuccessorSliceFacts A S.periodUpper where
  P0_pos := S.periodLower_pos
  period_lower := S.period_lower
  period_upper := S.period_upper
  etaFs := S.etaFs
  etaF_deriv := S.etaF_deriv
  etaFs_continuous := S.etaFs_continuous
  etaF_periodic := S.etaF_periodic
  rearNormal_c2 := S.rearNormal_c2
  normal_stopped := S.normal_stopped

/-- A source-tied analytic sidecar, together with its configured global period
ceiling, is exactly the nonaffine input package. -/
def Facts.ofAnalytic
    {a b : Data} {Delta : NormalPath a b}
    {periodLower kap khatNext QmaxNext P1 : ℝ}
    {A : MarkingAwareSource Delta periodLower kap khatNext QmaxNext}
    (S : FiniteSmoothRearFamilyMarkingAwareCorrelatedRecursion.AnalyticSuccessorSliceFacts A)
    (hP1 : S.periodUpper ≤ P1) :
    Facts A P1 S.markingLower S.markingUpper where
  P0_pos := S.periodLower_pos
  period_lower := S.period_lower
  period_upper := fun t ↦ (S.period_upper t).trans hP1
  etaFs := S.etaFs
  etaF_deriv := S.etaF_deriv
  etaFs_continuous := S.etaFs_continuous
  etaF_periodic := S.etaF_periodic
  rearNormal_c2 := S.rearNormal_c2
  normal_stopped := S.normal_stopped
  marking_increment := S.marking_increment
  marking_lower_positive := S.markingLower_pos
  marking_lower := S.marking_lower
  marking_upper_nonnegative := S.markingUpper_nonnegative
  marking_upper := S.marking_upper
  marked_bdd0 := S.marked_bdd0
  marked_bdd1 := S.marked_bdd1

/-- Every source in a sliced correlated column therefore carries the exact
nonaffine facts required by row construction. -/
def Facts.ofSlicedColumn
    {Q current : ℕ → Data} {e : ℕ → ℕ → ℝ} {k n : ℕ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
    {period : ℕ → ℕ → ℝ} {diagonal kh Qmax : ℕ → ℝ}
    {K0 K1 K2 : ℝ}
    {S : FiniteSmoothRearFamilyMarkingAwareCorrelatedRecursion.CorrelatedColumn
      Q current e k P0 P1 khat G1 Cg C c dlt period diagonal kh Qmax K0 K1 K2}
    (H : FiniteSmoothRearFamilyMarkingAwareCorrelatedRecursion.SlicedCorrelatedColumn S) :
    Facts (S.source n) (P1 n) (H.slice n).markingLower (H.slice n).markingUpper :=
  Facts.ofAnalytic (H.slice n) (H.periodUpper_le n)

/-- Recursive preservation theorem.  For the actual successor source the two
marking equalities are definitional (`rfl`), so only new slice geometry remains
to be supplied. -/
def Facts.ofChosenSuccessor
    {p q a b : Data} {Gamma : NormalPath p q}
    {P0 kh khat Qmax P0' kh' khat' Qmax' P1' : ℝ}
    {A : MarkingAwareSource Gamma P0 kh khat Qmax}
    {E : Applied Gamma A} (W : ChosenPath Gamma A E.Phi a b)
    {A' : MarkingAwareSource W.Delta P0' kh' khat' Qmax'}
    (S : SuccessorSliceFacts A' P1')
    (hphi : A'.phi = E.Phi) (hphi1 : A'.phi1 = W.phi1) :
    Facts A' P1' (chosenLower W) (chosenUpper W) := by
  let H := chosenMarkingFacts W
  exact {
    P0_pos := S.P0_pos
    period_lower := S.period_lower
    period_upper := S.period_upper
    etaFs := S.etaFs
    etaF_deriv := S.etaF_deriv
    etaFs_continuous := S.etaFs_continuous
    etaF_periodic := S.etaF_periodic
    rearNormal_c2 := S.rearNormal_c2
    normal_stopped := S.normal_stopped
    marking_increment := fun t ↦ by
      have hs := A'.phi_shift t 0
      have hs' : A'.phi t 1 = A'.phi t 0 + A'.P t := by simpa using hs
      linarith
    marking_lower_positive := H.lower_positive
    marking_lower := fun t ht u ↦ by rw [hphi1]; exact H.lower t ht u
    marking_upper_nonnegative := H.upper_nonnegative
    marking_upper := fun t ht u ↦ by rw [hphi1]; exact H.upper t ht u
    marked_bdd0 := H.marked_bdd0
    marked_bdd1 := H.marked_bdd1 }

end Nonaffine

/-- Facts used only by the separated inverse-Jacobi estimate.  In particular,
`eta_link_affine` is intentionally explicit: the general marking-aware source
retains an arbitrary nonaffine source marking, for which this assertion is not
derivable. -/
structure SeparatedFacts
    {p q : Data} {Gamma : NormalPath p q}
    {P0 kh khat Qmax : ℝ} (A : MarkingAwareSource Gamma P0 kh khat Qmax)
    (P1 : ℝ) where
  P0_pos : 0 < P0
  period_lower : ∀ t, P0 ≤ A.P t
  period_upper : ∀ t, A.P t ≤ P1
  etaFs : ℝ → ℝ → ℝ
  etaF_deriv : ∀ t s, HasDerivAt (A.etaF t) (etaFs t s) s
  etaFs_continuous : ∀ t, Continuous (etaFs t)
  etaF_periodic : ∀ t, Periodic (A.etaF t) (A.P t)
  rearNormal_c2 : ∀ t, ContDiff ℝ (2 : ℕ) (rearNormal A t)
  eta_link_affine : ∀ t u, Gamma.eta t u = A.etaF t (A.P t * u)
  normal_stopped : ∀ t ∉ Ioo (0 : ℝ) Gamma.T,
    rearNormal A t = fun _ ↦ 0

/-- Component-separated data attached to one already-selected application.
No second gauge flow or path is chosen. -/
structure SeparatedApplied
    {p q : Data} {Gamma : NormalPath p q}
    {P0 kh khat Qmax : ℝ} {A : MarkingAwareSource Gamma P0 kh khat Qmax}
    (E : Applied Gamma A) where
  CW : ℝ
  C0 : ℝ
  C10 : ℝ
  C11 : ℝ
  C20 : ℝ
  C21 : ℝ
  C22 : ℝ
  flowed : FlowedBounds Gamma.eta
    (fun t u ↦ rearNormal A t (E.Phi t u)) CW C0 C10 C11 C20 C21 C22

/-- Invoke the existing variable-period separated gauge theorem on the exact
flow retained by `E`. -/
theorem exists_separatedApplied
    {p q : Data} {Gamma : NormalPath p q}
    {P0 kh khat Qmax P1 : ℝ}
    {A : MarkingAwareSource Gamma P0 kh khat Qmax}
    (E : Applied Gamma A) (S : SeparatedFacts A P1) :
    Nonempty (SeparatedApplied E) := by
  have hetaPer : ∀ t, Periodic (rearNormal A t) (rearPeriod A t) := by
    intro t
    simpa [rearNormal, rearPeriod] using
      RearOwnDriftFundamental.periodic_frameNormal_rearOwn
        A.kh_nonnegative A.kh_lt_one A.strip_nonnegative A.strip_le
        A.cos_ne_zero A.front_frenet A.angle_frenet A.steering A.sf_deriv
        A.sf_rightInverse A.steering_periodic A.front_periodic
        A.angle_periodic A.front_contDiff A.angle_contDiff
        A.steering_contDiff A.sf_contDiff A.period_contDiff A.rear_time_deriv t
  have hflowed := GaugeGeometryVariableSeparatedFlowed.flowedBounds Gamma
    E.frame.frame S.P0_pos A.kh_nonnegative A.kh_lt_one
    S.period_lower S.period_upper A.steering A.strip_nonnegative A.strip_le
    A.steering_periodic A.curvature_le S.etaF_deriv S.etaFs_continuous
    S.etaF_periodic A.sf_rightInverse A.jacobi (fun _ ↦ rfl)
    E.frame.period_deriv hetaPer S.rearNormal_c2 S.eta_link_affine
    E.frame.v_periodic E.frame.xi_quasiPeriodic E.frame.flow E.frame.initial
    S.normal_stopped
  let CW := GaugeNormalPath.gaugeCW P1 E.frame.frame.rateLip Gamma.T
    (rearPeriod A 0)
  let C0 := P1 /
    (1 - Real.exp (-(Real.sqrt (1 - kh ^ 2) * P0)))
  let C10 := flowFirst C0 E.frame.frame.rateLip Gamma.T (rearPeriod A 0)
  let C11 := flowFirst (1 / Real.sqrt (1 - kh ^ 2))
    E.frame.frame.rateLip Gamma.T (rearPeriod A 0)
  let C20 := flowSecond C0 E.frame.frame.rateLip Gamma.T (rearPeriod A 0) +
    flowDrift C0 E.frame.frame.rateLip E.frame.frame.rateBound2
      Gamma.T (rearPeriod A 0)
  let C21 := flowSecond
      (2 * kh ^ 2 / Real.sqrt (1 - kh ^ 2) ^ 3 +
        1 / Real.sqrt (1 - kh ^ 2))
      E.frame.frame.rateLip Gamma.T (rearPeriod A 0) +
    flowDrift (1 / Real.sqrt (1 - kh ^ 2)) E.frame.frame.rateLip
      E.frame.frame.rateBound2 Gamma.T (rearPeriod A 0)
  let C22 := flowSecond
    (1 / (P0 * Real.sqrt (1 - kh ^ 2) ^ 2))
    E.frame.frame.rateLip Gamma.T (rearPeriod A 0)
  refine ⟨{
    CW := CW
    C0 := C0
    C10 := C10
    C11 := C11
    C20 := C20
    C21 := C21
    C22 := C22
    flowed := ?_ }⟩
  simpa [CW, C0, C10, C11, C20, C21, C22] using hflowed

/-- The separated certificate for a genuinely nonaffine source marking. -/
theorem exists_nonaffineSeparatedApplied
    {p q : Data} {Gamma : NormalPath p q}
    {P0 kh khat Qmax P1 m M : ℝ}
    {A : MarkingAwareSource Gamma P0 kh khat Qmax}
    (E : Applied Gamma A) (S : Nonaffine.Facts A P1 m M) :
    Nonempty (SeparatedApplied E) := by
  open GaugeNormalPathVariableSeparatedNonaffine in
  have hetaPer : ∀ t, Periodic (rearNormal A t) (rearPeriod A t) := by
    intro t
    simpa [rearNormal, rearPeriod] using
      RearOwnDriftFundamental.periodic_frameNormal_rearOwn
        A.kh_nonnegative A.kh_lt_one A.strip_nonnegative A.strip_le
        A.cos_ne_zero A.front_frenet A.angle_frenet A.steering A.sf_deriv
        A.sf_rightInverse A.steering_periodic A.front_periodic
        A.angle_periodic A.front_contDiff A.angle_contDiff
        A.steering_contDiff A.sf_contDiff A.period_contDiff A.rear_time_deriv t
  have hslice := GaugeGeometrySeparatedSliceCertificate.certificate
    S.P0_pos A.kh_nonnegative A.kh_lt_one S.period_lower S.period_upper
    A.steering A.strip_nonnegative A.strip_le A.steering_periodic A.curvature_le
    S.etaF_deriv S.etaFs_continuous S.etaF_periodic A.sf_rightInverse
    A.jacobi hetaPer
  let BW := M / P0
  let B0 : ℝ := 1
  let B1 := P1 / m
  have hP1pos : 0 < P1 := S.P0_pos.trans_le ((S.period_lower 0).trans (S.period_upper 0))
  have hBW : 0 ≤ BW := div_nonneg S.marking_upper_nonnegative S.P0_pos.le
  have hB0 : 0 ≤ B0 := zero_le_one
  have hB1 : 0 ≤ B1 := div_nonneg hP1pos.le S.marking_lower_positive.le
  have hfront : ∀ t ∈ Ioo (0 : ℝ) Gamma.T,
      GaugeNormalPathVariableSeparatedNonaffine.FrontComparison
        (fun u ↦ A.etaF t (A.P t * u)) (Gamma.eta t) BW B0 B1 := by
    intro t ht
    have hPpos : 0 < A.P t := S.P0_pos.trans_le (S.period_lower t)
    have hphic : Continuous (A.phi t) :=
      Differentiable.continuous (fun u ↦ (A.phi_deriv t u).differentiableAt)
    have hsurj : Surjective (A.phi t) :=
      FiniteSmoothRearFamilyMarkingAwareSource.surjective_of_continuous_quasiPeriodic
        hPpos hphic (A.phi_shift t)
    have hmarked : (fun u ↦ A.etaF t (A.phi t u)) = Gamma.eta t := by
      funext u
      exact (A.eta_link t u).symm
    have hbdd0 : BddAbove (Set.range fun u ↦ |A.etaF t (A.phi t u)|) := by
      have heq : (fun u ↦ |A.etaF t (A.phi t u)|) =
          fun u ↦ |Gamma.eta t u| := congrArg (fun f u ↦ |f u|) hmarked
      rw [heq]
      exact S.marked_bdd0 t
    have hbdd1 : BddAbove (Set.range fun u ↦
        |iteratedDeriv 1 (fun v ↦ A.etaF t (A.phi t v)) u|) := by
      have heq : (fun u ↦ |iteratedDeriv 1 (fun v ↦ A.etaF t (A.phi t v)) u|) =
          fun u ↦ |iteratedDeriv 1 (Gamma.eta t) u| :=
        congrArg (fun f u ↦ |iteratedDeriv 1 f u|) hmarked
      rw [heq]
      exact S.marked_bdd1 t
    have H := GaugeNormalPathVariableSeparatedNonaffine.frontComparison_of_reparam
      hPpos S.marking_lower_positive (S.etaF_deriv t)
      (Differentiable.continuous fun s ↦ (S.etaF_deriv t s).differentiableAt)
      (A.phi_deriv t) (A.phi1_continuous t)
      (S.etaF_periodic t) (S.marking_increment t) (S.marking_lower t ht)
      (S.marking_upper t ht) hsurj
      hbdd0 hbdd1
    have hWcoef : M / A.P t ≤ BW := by
      dsimp [BW]
      exact div_le_div_of_nonneg_left S.marking_upper_nonnegative
        S.P0_pos (S.period_lower t)
    have h1coef : A.P t / m ≤ B1 := by
      dsimp [B1]
      exact div_le_div_of_nonneg_right (S.period_upper t)
        S.marking_lower_positive.le
    simpa [B0, hmarked] using
      GaugeNormalPathVariableSeparatedNonaffine.frontComparison_mono
        H hWcoef le_rfl h1coef
  let c0 := P1 / (1 - Real.exp (-(Real.sqrt (1 - kh ^ 2) * P0)))
  let a11 := 1 / Real.sqrt (1 - kh ^ 2)
  let a21 := 2 * kh ^ 2 / Real.sqrt (1 - kh ^ 2) ^ 3 +
    1 / Real.sqrt (1 - kh ^ 2)
  let a22 := 1 / (P0 * Real.sqrt (1 - kh ^ 2) ^ 2)
  have hroot : 0 < Real.sqrt (1 - kh ^ 2) := Real.sqrt_pos.2 (by
    nlinarith [A.kh_nonnegative, A.kh_lt_one])
  have hden : 0 < 1 - Real.exp (-(Real.sqrt (1 - kh ^ 2) * P0)) :=
    JacobiNormalized.one_sub_exp_pos (mul_pos hroot S.P0_pos)
  have hc0 : 0 ≤ c0 := by
    dsimp [c0]
    exact div_nonneg hP1pos.le hden.le
  have ha11 : 0 ≤ a11 := by dsimp [a11]; positivity
  have ha21 : 0 ≤ a21 := by
    dsimp [a21]
    exact add_nonneg
      (div_nonneg (mul_nonneg (by positivity) (sq_nonneg kh))
        (pow_nonneg hroot.le 3))
      (one_div_nonneg.mpr hroot.le)
  have ha22 : 0 ≤ a22 := by
    dsimp [a22]
    exact one_div_nonneg.mpr (mul_nonneg S.P0_pos.le (sq_nonneg _))
  have hflowed := GaugeNormalPathVariableSeparatedNonaffine.flowedBounds_of_frontComparison
    Gamma E.frame.frame A.rear_period_pos E.frame.period_deriv E.frame.v_periodic
    E.frame.xi_quasiPeriodic E.frame.flow E.frame.initial S.rearNormal_c2 hetaPer
    S.normal_stopped hP1pos.le hc0 hc0 ha11 hc0 ha21 ha22 hBW hB0 hB1 hfront
    (fun t _ ↦ hslice.w t) (fun t _ ↦ hslice.s0 t)
    (fun t _ ↦ hslice.separated t)
  refine ⟨{
    CW := GaugeNormalPath.gaugeCW (P1 * BW) E.frame.frame.rateLip Gamma.T
      (rearPeriod A 0)
    C0 := c0 * BW
    C10 := flowFirst (c0 * BW) E.frame.frame.rateLip Gamma.T (rearPeriod A 0)
    C11 := flowFirst (a11 * B0) E.frame.frame.rateLip Gamma.T (rearPeriod A 0)
    C20 := flowSecond (c0 * BW) E.frame.frame.rateLip Gamma.T (rearPeriod A 0) +
      flowDrift (c0 * BW) E.frame.frame.rateLip E.frame.frame.rateBound2
        Gamma.T (rearPeriod A 0)
    C21 := flowSecond (a21 * B0) E.frame.frame.rateLip Gamma.T (rearPeriod A 0) +
      flowDrift (a11 * B0) E.frame.frame.rateLip E.frame.frame.rateBound2
        Gamma.T (rearPeriod A 0)
    C22 := flowSecond (a22 * B1) E.frame.frame.rateLip Gamma.T (rearPeriod A 0)
    flowed := ?_ }⟩
  simpa [BW, B0, B1, c0, a11, a21, a22] using hflowed

/-- The separated certificate belongs to every endpoint specialization of the
same application, because `ChosenPath.eta_eq` identifies its velocity with
the sidecar's flowed velocity. -/
def SeparatedApplied.flowedChosen
    {p q a b : Data} {Gamma : NormalPath p q}
    {P0 kh khat Qmax : ℝ} {A : MarkingAwareSource Gamma P0 kh khat Qmax}
    {E : Applied Gamma A} (H : SeparatedApplied E)
    (R : ChosenPath Gamma A E.Phi a b) :
    FlowedBounds Gamma.eta R.Delta.eta
      H.CW H.C0 H.C10 H.C11 H.C20 H.C21 H.C22 := by
  have heta : R.Delta.eta = fun t u ↦ rearNormal A t (E.Phi t u) :=
    funext fun t ↦ funext fun u ↦ R.eta_eq t u
  simpa only [heta] using H.flowed

end FiniteSmoothRearFamilyMarkingAwareSeparatedAppliedSource
