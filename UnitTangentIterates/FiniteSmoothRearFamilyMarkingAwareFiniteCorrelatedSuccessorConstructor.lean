import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareFiniteCorrelatedSuccessorMass

/-!
# Concrete finite correlated successor witnesses

The only inputs below are the scalar and source-period estimates consumed by
the automatic exact-successor theorem.  The successor bundles themselves are
chosen from that theorem, not supplied as a callback.
-/

noncomputable section

open Set MarkedSpace PathMetric

namespace FiniteSmoothRearFamilyMarkingAwareFiniteCorrelatedPresentedColumn

open FiniteSmoothRearFamilyMarkingAwareAppliedSource
  FiniteSmoothRearFamilyMarkingAwareExactSelectedOfC1
  FiniteSmoothRearFamilyMarkingAwareExactSuccessorAutomaticBounds
  FiniteSmoothRearFamilyMarkingAwareExactSuccessorGaugeExistence
  FiniteSmoothRearFamilyMarkingAwareExactSuccessorGaugeTransport
  FiniteSmoothRearFamilyMarkingAwareExactSuccessorPreTransport
  FiniteSmoothRearFamilyMarkingAwareExactSuccessorReadySource
  FiniteSmoothRearFamilyMarkingAwareSource
  FiniteSmoothRearFamilyMarkingAwareSuccessorFront

/-- Strengthened exact-successor existence retaining the upper-period fact
which the older `Nonempty ExactSuccessorBundle` interface erased. -/
theorem ChosenPath.exists_exactSuccessorBundleWithPeriodUpper
    {p q a b : Data} {Gamma : NormalPath p q}
    {P0 kh khat Qmax periodLower periodUpper kap khatNext QmaxNext Md MP : ℝ}
    {A : MarkingAwareSource Gamma P0 kh khat Qmax}
    {E : Applied Gamma A}
    (W : ChosenPath Gamma A E.Phi a b)
    (hperiodLower : 0 < periodLower)
    (hkap0 : 0 ≤ kap) (hkap1 : kap < 1)
    (hPl : ∀ t, periodLower ≤ period A t)
    (hPu : ∀ t, period A t ≤ periodUpper)
    (hKnTbd : ∀ t u,
      |RearOwnHigherRegularity.partialTime
        (SteeringVariablePeriodSelectedInverseJointC1.normalizedCurvature
          (curvature A) (period A)) t u| ≤ Md)
    (hPtbd : ∀ t,
      |SteeringVariablePeriodSelectedInverseJointC1.periodTime (period A) t| ≤ MP)
    (C : Scalar (A := A) (kap := kap) (P0Next := periodLower)
      (khatNext := khatNext) (QmaxNext := QmaxNext)) :
    Nonempty {X :
      FiniteSmoothRearFamilyMarkingAwareGeometricExactFiniteTower.ExactSuccessorBundle
        W (periodLower := periodLower) (kap := kap)
          (khatNext := khatNext) (QmaxNext := QmaxNext) //
      X.slice.periodUpper ≤ periodUpper} := by
  obtain ⟨S⟩ := exists_exactSelected (A := A)
    hperiodLower hkap0 hkap1 hPl hPu
    (fun t s ↦ (le_abs_self (curvature A t s)).trans (C.curvature_le t s))
    hKnTbd hPtbd
  let R : PreTransport S :=
    FiniteSmoothRearFamilyMarkingAwareExactSuccessorPreTransport.exact
      S hkap0 hkap1
  obtain ⟨G⟩ := exists_gauge S R W hkap0 hkap1
  let T : ShiftedTransport R G :=
    FiniteSmoothRearFamilyMarkingAwareExactSuccessorGaugeTransport.exact
      R G hkap0 hkap1
  let B := bounds W S R G T hkap0 hkap1 C hperiodLower
  let A' := source W S R G hkap0 hkap1 T B
  let K := compatibility W S R G hkap0 hkap1 T B
  have hPl' : ∀ t, periodLower ≤ A'.P t := by
    intro t
    rw [K.period_eq]
    simpa [rearPeriod] using hPl t
  have hPu' : ∀ t, A'.P t ≤ periodUpper := by
    intro t
    rw [K.period_eq]
    simpa [rearPeriod] using hPu t
  let X :
      FiniteSmoothRearFamilyMarkingAwareGeometricExactFiniteTower.ExactSuccessorBundle
        W (periodLower := periodLower) (kap := kap)
          (khatNext := khatNext) (QmaxNext := QmaxNext) :=
    { source := A'
      density_eq := rfl
      recursive :=
        FiniteSmoothRearFamilyMarkingAwareRecursiveAnalyticSuccessor.ofReadySource
          W S R G hkap0 hkap1 T B hperiodLower hPl' hPu'
      recursive_source_eq := rfl
      compatibility := K
      slice :=
        FiniteSmoothRearFamilyMarkingAwareChosenExactAnalyticSuccessor.sliceFacts
          W A' K hperiodLower hPl' hPu' }
  exact ⟨⟨X, by rfl⟩⟩

/-- Minimal rowwise scalar hypotheses for the automatic exact successor. -/
structure SuccessorScalarData
    {Q current : ℕ → Data} {e : ℕ → ℕ → ℝ} {k : ℕ}
    {P0 P1 khat G1 Cg C kh Qmax : ℕ → ℝ} {c dlt : ℝ}
    {S : FiniteColumn Q current e k P0 P1 khat G1 Cg C c dlt kh Qmax}
    (H : ReadyColumn S) where
  Md : ℕ → ℝ
  MP : ℕ → ℝ
  periodLower_pos : ∀ n, 0 < P0 n
  kh_nonnegative : ∀ n, 0 ≤ kh n
  kh_lt_one : ∀ n, kh n < 1
  periodLower_le : ∀ n t, P0 n ≤ period (S.source (n + 1)) t
  periodUpper_le : ∀ n t, period (S.source (n + 1)) t ≤ P1 n
  normalizedCurvatureTime_le : ∀ n t u,
    |RearOwnHigherRegularity.partialTime
      (SteeringVariablePeriodSelectedInverseJointC1.normalizedCurvature
        (curvature (S.source (n + 1))) (period (S.source (n + 1)))) t u| ≤ Md n
  periodTime_le : ∀ n t,
    |SteeringVariablePeriodSelectedInverseJointC1.periodTime
      (period (S.source (n + 1))) t| ≤ MP n
  scalar : ∀ n,
    FiniteSmoothRearFamilyMarkingAwareExactSuccessorAutomaticBounds.Scalar
      (A := S.source (n + 1)) (kap := kh n) (P0Next := P0 n)
      (khatNext := khat n) (QmaxNext := Qmax n)

/-- The theorem-produced exact bundle for one row. -/
noncomputable def SuccessorScalarData.bundle
    {Q current : ℕ → Data} {e : ℕ → ℕ → ℝ} {k : ℕ}
    {P0 P1 khat G1 Cg C kh Qmax : ℕ → ℝ} {c dlt : ℝ}
    {S : FiniteColumn Q current e k P0 P1 khat G1 Cg C c dlt kh Qmax}
    {H : ReadyColumn S} (D : SuccessorScalarData H) (n : ℕ) :
    FiniteSmoothRearFamilyMarkingAwareGeometricExactFiniteTower.ExactSuccessorBundle
      (H.row (n + 1)).output.chosen
      (periodLower := P0 n) (kap := kh n)
      (khatNext := khat n) (QmaxNext := Qmax n) :=
  (Classical.choice
    (ChosenPath.exists_exactSuccessorBundleWithPeriodUpper
        (H.row (n + 1)).output.chosen
        (D.periodLower_pos n) (D.kh_nonnegative n) (D.kh_lt_one n)
        (D.periodLower_le n) (D.periodUpper_le n)
        (D.normalizedCurvatureTime_le n) (D.periodTime_le n) (D.scalar n))).1

/-- The complete family of retained exact successors is constructed from the
minimal scalar data. -/
noncomputable def SuccessorScalarData.successorBundles
    {Q current : ℕ → Data} {e : ℕ → ℕ → ℝ} {k : ℕ}
    {P0 P1 khat G1 Cg C kh Qmax : ℕ → ℝ} {c dlt : ℝ}
    {S : FiniteColumn Q current e k P0 P1 khat G1 Cg C c dlt kh Qmax}
    {H : ReadyColumn S} {B : RowBounds H} (D : SuccessorScalarData H) :
    SuccessorBundles H B where
  bundle := D.bundle
  periodUpper_le := fun n ↦ by
    exact (Classical.choice
      (ChosenPath.exists_exactSuccessorBundleWithPeriodUpper
        (H.row (n + 1)).output.chosen
        (D.periodLower_pos n) (D.kh_nonnegative n) (D.kh_lt_one n)
        (D.periodLower_le n) (D.periodUpper_le n)
        (D.normalizedCurvatureTime_le n) (D.periodTime_le n) (D.scalar n))).2

/-- First density inequality needed by the next presented-row constructor. -/
def DensityD1 (Z : FiniteSmoothRearFamilyMarkingAwareGeometricExactFiniteTower.State) : Prop :=
  ∀ t,
    2 * (Z.path.m t / Real.sqrt (1 - Z.kh ^ 2)) *
      GaugeFlowDerivCost.costP1
        (FiniteSmoothRearFamilyMarkingAwareAppliedSource.rearPeriod Z.source 0)
        (GaugeMarkedDataOfRearFamily.rearKappa1 Z.kh)
        (∫ s in (0 : ℝ)..Z.path.T, Z.source.m s) ≤ Z.source.m t

/-- Second density inequality needed by the next presented-row constructor. -/
def DensityD2 (Z : FiniteSmoothRearFamilyMarkingAwareGeometricExactFiniteTower.State) : Prop :=
  ∀ t,
    (Z.source.Dd t + 2 * (Z.path.m t / Real.sqrt (1 - Z.kh ^ 2))) *
        GaugeFlowDerivCost.costP1
          (FiniteSmoothRearFamilyMarkingAwareAppliedSource.rearPeriod Z.source 0)
          (GaugeMarkedDataOfRearFamily.rearKappa1 Z.kh)
          (∫ s in (0 : ℝ)..Z.path.T, Z.source.m s) ^ 2 +
      2 * (Z.path.m t / Real.sqrt (1 - Z.kh ^ 2)) *
        GaugeFlowDerivCost.costG1
          (FiniteSmoothRearFamilyMarkingAwareAppliedSource.rearPeriod Z.source 0)
          (GaugeMarkedDataOfRearFamily.rearKappa1 Z.kh)
          (GaugeMarkedDataOfRearFamily.rearKappa2 Z.kh)
          (∫ s in (0 : ℝ)..Z.path.T, Z.source.m s) ≤ Z.source.m t

/-- The three genuinely additional sidecars not retained by the generic
automatic bundle: composition-density domination, normalized-front
injectivity, and diagonal range/phase coherence. -/
structure SuccessorReadySidecars
    {Q current : ℕ → Data} {e : ℕ → ℕ → ℝ} {k : ℕ}
    {P0 P1 khat G1 Cg C kh Qmax : ℕ → ℝ} {c dlt : ℝ}
    {S : FiniteColumn Q current e k P0 P1 khat G1 Cg C c dlt kh Qmax}
    {H : ReadyColumn S} {B : RowBounds H} (X : SuccessorBundles H B) where
  density_d1 : ∀ n, DensityD1 (X.nextColumn.state n)
  density_d2 : ∀ n, DensityD2 (X.nextColumn.state n)
  front_injective : ∀ n, InjOn
    (FiniteSmoothRearFamilyMarkingAwarePresentedTerminalGeometry.normalizedFront
      (X.nextColumn.source n)) (Ico 0 1)
  initial_range_current : ∀ n,
    range ((X.nextColumn.source n).selectedRearData 0).1 =
      range (X.nextColumn.step.next n).1

/-- Construct the complete iterative readiness invariant.  Spatial frame,
terminal curvature, and terminal range are inherited from the retained
recursive analytic successor; no endpoint equality is asserted. -/
noncomputable def SuccessorBundles.nextReadyColumn
    {Q current : ℕ → Data} {e : ℕ → ℕ → ℝ} {k : ℕ}
    {P0 P1 khat G1 Cg C kh Qmax : ℕ → ℝ} {c dlt : ℝ}
    {S : FiniteColumn Q current e k P0 P1 khat G1 Cg C c dlt kh Qmax}
    {H : ReadyColumn S} {B : RowBounds H} (X : SuccessorBundles H B)
    (R : SuccessorReadySidecars X) : ReadyColumn X.nextColumn where
  ready := fun n ↦ by
    let U := X.bundle n
    have hspatial := U.recursive.spatial
    have hcurvature := U.recursive.terminalCurvature_nonnegative
    have hrange := U.recursive.terminalRange
    rw [U.recursive_source_eq] at hspatial hcurvature hrange
    exact
      { initial := (X.nextColumn.source n).selectedRearData 0
        spatial := by
          simpa [SuccessorBundles.nextColumn, ReadyColumn.successorStep] using hspatial
        terminalCurvature_nonnegative := by
          simpa [SuccessorBundles.nextColumn, ReadyColumn.successorStep] using hcurvature
        terminalRange := by
          simpa [SuccessorBundles.nextColumn, ReadyColumn.successorStep] using hrange
        initial_eq := rfl
        density_d1 := R.density_d1 n
        density_d2 := R.density_d2 n
        front_injective := R.front_injective n }
  initial_range_current := R.initial_range_current

end FiniteSmoothRearFamilyMarkingAwareFiniteCorrelatedPresentedColumn
