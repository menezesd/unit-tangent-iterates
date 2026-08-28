import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareFiniteCorrelatedSuccessorConstructor
import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareCompositionRecursiveAnalyticSuccessor

/-!
# Composition-scaled finite correlated successors

Unlike the raw automatic successor, this source density is multiplied by the
composition coefficient.  The resulting analytic successor retains the two
density inequalities required for iteration.
-/

noncomputable section

open Function Set MeasureTheory MarkedSpace PathMetric PathMetric.NormalPath

namespace FiniteSmoothRearFamilyMarkingAwareFiniteCorrelatedPresentedColumn

open FiniteSmoothRearFamilyMarkingAwareAppliedSource
  FiniteSmoothRearFamilyMarkingAwareCorrelatedRecursion
  FiniteSmoothRearFamilyMarkingAwareExactSelectedOfC1
  FiniteSmoothRearFamilyMarkingAwareExactSuccessorAutomaticBounds
  FiniteSmoothRearFamilyMarkingAwareExactSuccessorCompositionScale
  FiniteSmoothRearFamilyMarkingAwareExactSuccessorGaugeExistence
  FiniteSmoothRearFamilyMarkingAwareExactSuccessorGaugeTransport
  FiniteSmoothRearFamilyMarkingAwareExactSuccessorPreTransport
  FiniteSmoothRearFamilyMarkingAwareExactSuccessorReadySource
  FiniteSmoothRearFamilyMarkingAwareSource
  FiniteSmoothRearFamilyMarkingAwareSuccessorFront

/-- A retained composition-scaled successor. -/
structure ScaledSuccessorBundle
    {p q a b : Data} {Gamma : NormalPath p q}
    {P0 kh khat Qmax periodLower kap khatNext QmaxNext : ℝ}
    {A : MarkingAwareSource Gamma P0 kh khat Qmax}
    {E : Applied Gamma A} (W : ChosenPath Gamma A E.Phi a b) where
  source : MarkingAwareSource W.Delta periodLower kap khatNext QmaxNext
  coeff : ℝ
  density_eq : source.m = fun t ↦ coeff * density W (kap := kap) t
  analytic :
    FiniteSmoothRearFamilyMarkingAwareCompositionRecursiveAnalyticSuccessor.CompositionRecursiveAnalyticSuccessor
      W.Delta A periodLower kap khatNext QmaxNext
  analytic_source_eq : analytic.source = source
  compatibility :
    FiniteSmoothRearFamilyMarkingAwareChosenExactAnalyticSuccessor.Compatibility
      W source
  slice : AnalyticSuccessorSliceFacts source

/-- Explicit scaled construction retaining Compatibility and the density
identity erased by the older existential analytic interface. -/
theorem ChosenPath.exists_scaledSuccessorBundle
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
    (C : FiniteSmoothRearFamilyMarkingAwareExactSuccessorCompositionScale.Scalar
      (A := A) (kap := kap) (P0Next := periodLower)
      (khatNext := khatNext) (QmaxNext := QmaxNext) W) :
    Nonempty {X : ScaledSuccessorBundle W
      (periodLower := periodLower) (kap := kap)
      (khatNext := khatNext) (QmaxNext := QmaxNext) //
      X.slice.periodUpper ≤ periodUpper} := by
  obtain ⟨S⟩ := exists_exactSelected (A := A)
    hperiodLower hkap0 hkap1 hPl hPu
    (fun t s ↦ (le_abs_self (curvature A t s)).trans
      (C.toScalar.curvature_le t s)) hKnTbd hPtbd
  let R : PreTransport S :=
    FiniteSmoothRearFamilyMarkingAwareExactSuccessorPreTransport.exact
      S hkap0 hkap1
  obtain ⟨G⟩ := exists_gauge S R W hkap0 hkap1
  let T : ShiftedTransport R G :=
    FiniteSmoothRearFamilyMarkingAwareExactSuccessorGaugeTransport.exact
      R G hkap0 hkap1
  let B := scaledBounds W S R G T hkap0 hkap1 C hperiodLower
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
  let Y :=
    FiniteSmoothRearFamilyMarkingAwareCompositionRecursiveAnalyticSuccessor.ofScaledReadySource
      W S R G hkap0 hkap1 T C hperiodLower hPl hPu
  let X : ScaledSuccessorBundle W (periodLower := periodLower) (kap := kap)
      (khatNext := khatNext) (QmaxNext := QmaxNext) :=
    { source := A'
      coeff := C.coeff
      density_eq := rfl
      analytic := Y
      analytic_source_eq := rfl
      compatibility := K
      slice :=
        FiniteSmoothRearFamilyMarkingAwareChosenExactAnalyticSuccessor.sliceFacts
          W A' K hperiodLower hPl' hPu' }
  exact ⟨⟨X, by rfl⟩⟩

/-- Exact mass of the composition-scaled source. -/
theorem ScaledSuccessorBundle.sourceMass_eq
    {p q a b : Data} {Gamma : NormalPath p q}
    {P0 kh khat Qmax periodLower kap khatNext QmaxNext : ℝ}
    {A : MarkingAwareSource Gamma P0 kh khat Qmax}
    {E : Applied Gamma A} {W : ChosenPath Gamma A E.Phi a b}
    (X : ScaledSuccessorBundle W (periodLower := periodLower) (kap := kap)
      (khatNext := khatNext) (QmaxNext := QmaxNext)) :
    FiniteSmoothRearFamilyMarkingAwareTimeRescaleCostObstruction.sourceMass X.source =
      X.coeff / Real.sqrt (1 - kap ^ 2) * W.Delta.cost := by
  unfold FiniteSmoothRearFamilyMarkingAwareTimeRescaleCostObstruction.sourceMass
    PathMetric.NormalPath.cost
  rw [X.density_eq]
  simp only [density, div_eq_mul_inv]
  rw [show (fun t ↦ X.coeff * (W.Delta.m t *
      (Real.sqrt (1 - kap ^ 2))⁻¹)) =
      (fun t ↦ (X.coeff * (Real.sqrt (1 - kap ^ 2))⁻¹) *
        W.Delta.m t) by funext t; ring]
  rw [intervalIntegral.integral_const_mul]

/-- The exact polynomially weighted mass majorant. -/
def scaledSourceMassMajor (coeff kap : ℝ) (defect : ℕ → ℝ) (j : ℕ) : ℝ :=
  coeff / Real.sqrt (1 - kap ^ 2) * defect j

theorem scaledSourceMassMajor_summable (coeff kap : ℝ) {defect : ℕ → ℝ}
    (hdefect : Summable defect) :
    Summable (scaledSourceMassMajor coeff kap defect) := by
  apply (hdefect.mul_left (coeff / Real.sqrt (1 - kap ^ 2))).congr
  intro j
  rfl

/-- Rowwise scalar inputs for composition-scaled successors. -/
structure ScaledSuccessorScalarData
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
    FiniteSmoothRearFamilyMarkingAwareExactSuccessorCompositionScale.Scalar
      (A := S.source (n + 1)) (kap := kh n) (P0Next := P0 n)
      (khatNext := khat n) (QmaxNext := Qmax n)
      (H.row (n + 1)).output.chosen

noncomputable def ScaledSuccessorScalarData.bundle
    {Q current : ℕ → Data} {e : ℕ → ℕ → ℝ} {k n : ℕ}
    {P0 P1 khat G1 Cg C kh Qmax : ℕ → ℝ} {c dlt : ℝ}
    {S : FiniteColumn Q current e k P0 P1 khat G1 Cg C c dlt kh Qmax}
    {H : ReadyColumn S} (D : ScaledSuccessorScalarData H) :
    ScaledSuccessorBundle (H.row (n + 1)).output.chosen
      (periodLower := P0 n) (kap := kh n)
      (khatNext := khat n) (QmaxNext := Qmax n) :=
  (Classical.choice (ChosenPath.exists_scaledSuccessorBundle
    (H.row (n + 1)).output.chosen
    (D.periodLower_pos n) (D.kh_nonnegative n) (D.kh_lt_one n)
    (D.periodLower_le n) (D.periodUpper_le n)
    (D.normalizedCurvatureTime_le n) (D.periodTime_le n) (D.scalar n))).1

/-- A finite family of concrete scaled successors. -/
structure ScaledSuccessorBundles
    {Q current : ℕ → Data} {e : ℕ → ℕ → ℝ} {k : ℕ}
    {P0 P1 khat G1 Cg C kh Qmax : ℕ → ℝ} {c dlt : ℝ}
    {S : FiniteColumn Q current e k P0 P1 khat G1 Cg C c dlt kh Qmax}
    (H : ReadyColumn S) (B : RowBounds H) where
  bundle : ∀ n, ScaledSuccessorBundle (H.row (n + 1)).output.chosen
    (periodLower := P0 n) (kap := kh n)
    (khatNext := khat n) (QmaxNext := Qmax n)
  periodUpper_le : ∀ n, (bundle n).slice.periodUpper ≤ P1 n

noncomputable def ScaledSuccessorScalarData.bundles
    {Q current : ℕ → Data} {e : ℕ → ℕ → ℝ} {k : ℕ}
    {P0 P1 khat G1 Cg C kh Qmax : ℕ → ℝ} {c dlt : ℝ}
    {S : FiniteColumn Q current e k P0 P1 khat G1 Cg C c dlt kh Qmax}
    {H : ReadyColumn S} {B : RowBounds H} (D : ScaledSuccessorScalarData H) :
    ScaledSuccessorBundles H B where
  bundle := fun n ↦ D.bundle (n := n)
  periodUpper_le := fun n ↦
    (Classical.choice (ChosenPath.exists_scaledSuccessorBundle
      (H.row (n + 1)).output.chosen
      (D.periodLower_pos n) (D.kh_nonnegative n) (D.kh_lt_one n)
      (D.periodLower_le n) (D.periodUpper_le n)
      (D.normalizedCurvatureTime_le n) (D.periodTime_le n) (D.scalar n))).2

/-- The next column built from scaled successor sources. -/
noncomputable def ScaledSuccessorBundles.nextColumn
    {Q current : ℕ → Data} {e : ℕ → ℕ → ℝ} {k : ℕ}
    {P0 P1 khat G1 Cg C kh Qmax : ℕ → ℝ} {c dlt : ℝ}
    {S : FiniteColumn Q current e k P0 P1 khat G1 Cg C c dlt kh Qmax}
    {H : ReadyColumn S} {B : RowBounds H} (X : ScaledSuccessorBundles H B) :
    FiniteColumn Q H.nextCurrent e (k + 1) P0 P1 khat G1 Cg C c dlt kh Qmax where
  step := H.successorStep B
  source := fun n ↦ by
    simpa [ReadyColumn.successorStep] using (X.bundle n).source
  slice := fun n ↦ by
    simpa [ReadyColumn.successorStep] using (X.bundle n).slice
  periodUpper_le := fun n ↦ by
    simpa [ReadyColumn.successorStep] using X.periodUpper_le n

/-- Only non-density sidecars remain for scaled iteration. -/
structure ScaledSuccessorReadySidecars
    {Q current : ℕ → Data} {e : ℕ → ℕ → ℝ} {k : ℕ}
    {P0 P1 khat G1 Cg C kh Qmax : ℕ → ℝ} {c dlt : ℝ}
    {S : FiniteColumn Q current e k P0 P1 khat G1 Cg C c dlt kh Qmax}
    {H : ReadyColumn S} {B : RowBounds H} (X : ScaledSuccessorBundles H B) where
  front_injective : ∀ n, InjOn
    (FiniteSmoothRearFamilyMarkingAwarePresentedTerminalGeometry.normalizedFront
      (X.nextColumn.source n)) (Ico 0 1)
  initial_range_current : ∀ n,
    range ((X.nextColumn.source n).selectedRearData 0).1 =
      range (X.nextColumn.step.next n).1

noncomputable def ScaledSuccessorBundles.nextReadyColumn
    {Q current : ℕ → Data} {e : ℕ → ℕ → ℝ} {k : ℕ}
    {P0 P1 khat G1 Cg C kh Qmax : ℕ → ℝ} {c dlt : ℝ}
    {S : FiniteColumn Q current e k P0 P1 khat G1 Cg C c dlt kh Qmax}
    {H : ReadyColumn S} {B : RowBounds H} (X : ScaledSuccessorBundles H B)
    (R : ScaledSuccessorReadySidecars X) : ReadyColumn X.nextColumn where
  ready := fun n ↦ by
    have hspatial := (X.bundle n).analytic.spatial
    have hcurvature := (X.bundle n).analytic.terminalCurvature_nonnegative
    have hrange := (X.bundle n).analytic.terminalRange
    have hd1 := (X.bundle n).analytic.composition_d1
    have hd2 := (X.bundle n).analytic.composition_d2
    rw [(X.bundle n).analytic_source_eq] at hspatial hcurvature hrange hd1 hd2
    exact
      { initial := (X.nextColumn.source n).selectedRearData 0
        spatial := by
          simpa [ScaledSuccessorBundles.nextColumn, ReadyColumn.successorStep] using hspatial
        terminalCurvature_nonnegative := by
          simpa [ScaledSuccessorBundles.nextColumn, ReadyColumn.successorStep] using hcurvature
        terminalRange := by
          simpa [ScaledSuccessorBundles.nextColumn, ReadyColumn.successorStep] using hrange
        initial_eq := rfl
        density_d1 := by
          simpa [ScaledSuccessorBundles.nextColumn, ReadyColumn.successorStep] using hd1
        density_d2 := by
          simpa [ScaledSuccessorBundles.nextColumn, ReadyColumn.successorStep] using hd2
        front_injective := R.front_injective n }
  initial_range_current := R.initial_range_current

end FiniteSmoothRearFamilyMarkingAwareFiniteCorrelatedPresentedColumn
