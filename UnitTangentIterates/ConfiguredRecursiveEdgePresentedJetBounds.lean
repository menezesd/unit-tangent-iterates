import UnitTangentIterates.ConfiguredRecursiveEdgeSourceP0RowJetTail
import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwarePresentedJetBounds
import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwarePresentedNearIdentityClosure

/-!
# Actual chosen jets under the edge-indexed common tail

The edge recursion uses the source row `n+k` but its terminal period ceiling
belongs to the adjacent edge `n+k+1`.  This module records that exact index
shift and connects the actual chosen output to `edgeRowEps`.
-/

noncomputable section

open MarkedSpace PathMetric

namespace ConfiguredRecursiveEdgePresentedJetBounds

open ConfiguredApproximateDefectPathRowwise
  ConfiguredCombinedPhysicalDiagonalLargeSeparation
  ConfiguredRecursiveEdgeSourceP0RowJetTail
  ConfiguredRecursiveSourceP0ChosenJetMajorants
  ConfiguredRecursiveSourceP0RowJetTail
  FiniteSmoothRearFamilyMarkingAwareAppliedSource
  FiniteSmoothRearFamilyMarkingAwareChosenTerminal
  FiniteSmoothRearFamilyMarkingAwareCorrelatedRecursion
  FiniteSmoothRearFamilyMarkingAwarePresentedDirectSuccessor
  FiniteSmoothRearFamilyMarkingAwarePresentedJetBounds
  FiniteSmoothRearFamilyMarkingAwarePresentedNearIdentityClosure
  FiniteSmoothRearFamilyMarkingAwareSource
  GaugeMarkedDataOfRearFamily

/-- Exact row facts needed to compare one chosen edge terminal with the common
edge jet tail. -/
structure ChosenCertificate
    {a b p base : Data} {Gamma : NormalPath a b}
    {P0 kh khat Qmax bound : ℝ}
    {A : MarkingAwareSource Gamma P0 kh khat Qmax}
    {E : Applied Gamma A}
    {B : PresentedTerminalInputCore (p := p) (base := base) (bound := bound) E}
    (O : PresentedOutputCore E B)
    (D : ConstructedConfiguredSequenceWeighted.Data) (M : ℝ) (n k : ℕ) :
    Prop where
  kh_eq : kh = sourceKh
  qmax_le : Qmax ≤ ellCap D (n + k + 1)
  terminal_perim_ge_one : 1 ≤ perim base
  cost_le : O.chosen.Delta.cost ≤
    ConfiguredRecursiveEdgeSourceP0Growth.edgePhysicalDefect D (n + k)
  defect_le : ConfiguredRecursiveEdgeSourceP0Growth.edgePhysicalDefect D (n + k) ≤ M

theorem ChosenCertificate.jetError_le_edgeRowEps
    {a b p base : Data} {Gamma : NormalPath a b}
    {P0 kh khat Qmax bound : ℝ}
    {A : MarkingAwareSource Gamma P0 kh khat Qmax}
    {E : Applied Gamma A}
    {B : PresentedTerminalInputCore (p := p) (base := base) (bound := bound) E}
    {O : PresentedOutputCore E B}
    {D : ConstructedConfiguredSequenceWeighted.Data} {M : ℝ} {n k : ℕ}
    (R : ChosenCertificate O D M n k) :
    GaugeTerminalNearIdentityJets.JetBounds O.jets
      (PresentedOutputCore.richStage O 0 0 0) (edgeRowEps D M n k) := by
  have hell0 := (A.rear_period_pos 0).le
  have hell : rearPeriod A 0 ≤ ellCap D (n + k + 1) :=
    (A.rear_period_le 0).trans R.qmax_le
  have hcoeff : GaugeTerminalNearIdentityJets.jetLinearConst
      (rearPeriod A 0) (perim base)
      (rearKappa1 kh) (rearKappa2 kh) M ≤ rowJetCoeff D M (n + k + 1) := by
    simpa only [R.kh_eq] using
      jetLinearConst_le_rowJetCoeff D M (n + k + 1) hell0 hell
        R.terminal_perim_ge_one
  have hx : 0 ≤ ∫ t in (0 : ℝ)..Gamma.T, A.m t := by
    rw [← O.chosen.cost_eq]
    exact O.chosen.Delta.cost_nonneg
  have hxPhysical : (∫ t in (0 : ℝ)..Gamma.T, A.m t) ≤
      ConfiguredRecursiveEdgeSourceP0Growth.edgePhysicalDefect D (n + k) := by
    rw [← O.chosen.cost_eq]
    exact R.cost_le
  have hxM : (∫ t in (0 : ℝ)..Gamma.T, A.m t) ≤ M :=
    hxPhysical.trans R.defect_le
  have hk1 : 0 ≤ rearKappa1 kh :=
    rearKappa1_nonneg A.kh_nonnegative A.kh_lt_one
  have hk2 : 0 ≤ rearKappa2 kh :=
    rearKappa2_nonneg A.kh_nonnegative A.kh_lt_one
  have hrow : 0 ≤ rowJetCoeff D M (n + k + 1) :=
    (rowJetCoeffEnvelope D M).value_nonneg (n + k + 1)
  have hbound : GaugeTerminalNearIdentityJets.jetLinearConst
        (rearPeriod A 0) (perim base)
        (rearKappa1 kh) (rearKappa2 kh) M *
        (∫ t in (0 : ℝ)..Gamma.T, A.m t) ≤ edgeRowEps D M n k := by
    calc
    _ ≤ rowJetCoeff D M (n + k + 1) *
        ConfiguredRecursiveEdgeSourceP0Growth.edgePhysicalDefect D (n + k) :=
      mul_le_mul hcoeff hxPhysical hx hrow
    _ = edgeRowEps D M n k := by
      simp [edgeRowEps]
  exact ConfiguredGaugeJetDistortion.jetBounds_mono
    (FiniteSmoothRearFamilyMarkingAwarePresentedJetBounds.PresentedOutputCore.jetBounds_linear
      O hxM) hbound

/-- Install the actual chosen marking under the edge common-tail error. -/
def ChosenCertificate.nearIdentitySelection
    {Q current : ℕ → Data} {e : ℕ → ℕ → ℝ} {depth row : ℕ}
    {P0f P1 khatf G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
    {period : ℕ → ℕ → ℝ} {diagonal khf Qmaxf : ℕ → ℝ}
    {a MA NA : ℕ → ℕ → ℝ} {K0 K1 K2 : ℝ}
    {S : FiniteSmoothRearFamilyMarkingAwareCorrelatedRecursion.CorrelatedColumn
      Q current e depth P0f P1 khatf G1 Cg C c dlt
      period diagonal khf Qmaxf K0 K1 K2}
    {D : ConstructedConfiguredSequenceWeighted.Data} {M : ℝ}
    (W : PresentedRowSelection (n := row) (a := a) (MA := MA) (NA := NA)
      (K0 := K0) (K1 := K1) (K2 := K2) S)
    (R : ChosenCertificate W.output D M row (depth + 1)) :
    PresentedNearIdentitySelection
      (eps := edgeRowEps D M row (depth + 1)) W :=
  PresentedNearIdentitySelection.ofChosenJetBounds W R.jetError_le_edgeRowEps

/-- The common scalar tail bounds the actual marking selected in every row
and depth. -/
theorem ChosenCertificate.actual_jet_le_half
    {a b p base : Data} {Gamma : NormalPath a b}
    {P0 kh khat Qmax bound : ℝ}
    {A : MarkingAwareSource Gamma P0 kh khat Qmax}
    {E : Applied Gamma A}
    {B : PresentedTerminalInputCore (p := p) (base := base) (bound := bound) E}
    {O : PresentedOutputCore E B} {MA NA : ℝ}
    (J : ConfiguredRecursiveEdgeSourceP0RowJetTail.RowJetScalarOutput MA NA)
    {n k : ℕ}
    (R : ChosenCertificate O
      (ConstructedConfiguredInductiveTubeBudget.WeightedData.shift
        J.scalar.E.data J.scalar.large.N) J.scalar.Mend n k) :
    GaugeTerminalNearIdentityJets.JetBounds O.jets
      (PresentedOutputCore.richStage O 0 0 0) (1 / 2) :=
  ConfiguredGaugeJetDistortion.jetBounds_mono R.jetError_le_edgeRowEps
    (J.jet_half n k)

/-- Minimal edge jet facts not already stored by a presented selected row.
In particular, `terminal_perim_ge_one` is deliberately absent: it is a field
of the row itself. -/
structure PresentedRowJetCertificate
    {Q current : ℕ → Data} {e : ℕ → ℕ → ℝ} {depth row : ℕ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
    {period : ℕ → ℕ → ℝ} {diagonal kh Qmax : ℕ → ℝ}
    {a MA NA : ℕ → ℕ → ℝ} {K0 K1 K2 : ℝ}
    {S : CorrelatedColumn Q current e depth P0 P1 khat G1 Cg C c dlt
      period diagonal kh Qmax K0 K1 K2}
    (W : PresentedRowSelection (n := row) (a := a) (MA := MA) (NA := NA)
      (K0 := K0) (K1 := K1) (K2 := K2) S)
    (D : ConstructedConfiguredSequenceWeighted.Data) (M : ℝ) (k : ℕ) : Prop where
  kh_eq : kh row = sourceKh
  qmax_le : Qmax row ≤ ellCap D (row + k + 1)
  cost_le : W.output.chosen.Delta.cost ≤
    ConfiguredRecursiveEdgeSourceP0Growth.edgePhysicalDefect D (row + k)

def PresentedRowJetCertificate.chosenCertificate
    {Q current : ℕ → Data} {e : ℕ → ℕ → ℝ} {depth row : ℕ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
    {period : ℕ → ℕ → ℝ} {diagonal kh Qmax : ℕ → ℝ}
    {a MA NA : ℕ → ℕ → ℝ} {K0 K1 K2 : ℝ}
    {S : CorrelatedColumn Q current e depth P0 P1 khat G1 Cg C c dlt
      period diagonal kh Qmax K0 K1 K2}
    {W : PresentedRowSelection (n := row) (a := a) (MA := MA) (NA := NA)
      (K0 := K0) (K1 := K1) (K2 := K2) S}
    {D : ConstructedConfiguredSequenceWeighted.Data} {M : ℝ} {k : ℕ}
    (R : PresentedRowJetCertificate W D M k)
    (hdefect : ConfiguredRecursiveEdgeSourceP0Growth.edgePhysicalDefect
      D (row + k) ≤ M) :
    ChosenCertificate W.output D M row k where
  kh_eq := R.kh_eq
  qmax_le := R.qmax_le
  terminal_perim_ge_one := W.terminal_perim_ge_one
  cost_le := R.cost_le
  defect_le := hdefect

/-- A presented row provider retaining exactly the two facts needed downstream:
the chosen-output jet certificate and the analytic slice of its successor.
No independent marking-bound callback remains. -/
structure CertifiedPresentedRowProvider
    (Q : ℕ → Data) (e : ℕ → ℕ → ℝ)
    (P0 P1 khat G1 Cg C : ℕ → ℝ) (c dlt : ℝ)
    (period : ℕ → ℕ → ℝ) (diagonal kh Qmax : ℕ → ℝ)
    (a MA NA : ℕ → ℕ → ℝ) (K0 K1 K2 : ℝ)
    (D : ConstructedConfiguredSequenceWeighted.Data) (M : ℝ) where
  rows : PresentedRowProvider Q e P0 P1 khat G1 Cg C c dlt
    period diagonal kh Qmax a MA NA K0 K1 K2
  defect_le : ∀ j, ConfiguredRecursiveEdgeSourceP0Growth.edgePhysicalDefect D j ≤ M
  certificate : ∀ {current : ℕ → Data} {k : ℕ}
    (S : CorrelatedColumn Q current e k P0 P1 khat G1 Cg C c dlt
      period diagonal kh Qmax K0 K1 K2) (n : ℕ),
    PresentedRowJetCertificate ((rows.rows S).row n) D M (k + 1)
  mappedSlice : ∀ {current : ℕ → Data} {k : ℕ}
    (S : CorrelatedColumn Q current e k P0 P1 khat G1 Cg C c dlt
      period diagonal kh Qmax K0 K1 K2)
    (H : SlicedCorrelatedColumn S) (n : ℕ),
    AnalyticSuccessorSliceFacts ((rows.rows S).successor.mappedColumn.source n)
  mappedPeriodUpper_le : ∀ {current : ℕ → Data} {k : ℕ}
    (S : CorrelatedColumn Q current e k P0 P1 khat G1 Cg C c dlt
      period diagonal kh Qmax K0 K1 K2)
    (H : SlicedCorrelatedColumn S) (n : ℕ),
    (mappedSlice S H n).periodUpper ≤ P1 n

/-- Configured constructor: the scalar output supplies the global defect cap,
so the actual row construction retains only its rowwise cost/source facts and
the analytic successor slices. -/
def CertifiedPresentedRowProvider.ofScalar
    {Q : ℕ → Data} {e : ℕ → ℕ → ℝ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
    {period : ℕ → ℕ → ℝ} {diagonal kh Qmax : ℕ → ℝ}
    {a MA NA : ℕ → ℕ → ℝ} {K0 K1 K2 : ℝ} {MA0 NA0 : ℝ}
    (J : ConfiguredRecursiveEdgeSourceP0RowJetTail.RowJetScalarOutput MA0 NA0)
    (rows : PresentedRowProvider Q e P0 P1 khat G1 Cg C c dlt
      period diagonal kh Qmax a MA NA K0 K1 K2)
    (certificate : ∀ {current : ℕ → Data} {k : ℕ}
      (S : CorrelatedColumn Q current e k P0 P1 khat G1 Cg C c dlt
        period diagonal kh Qmax K0 K1 K2) (n : ℕ),
      PresentedRowJetCertificate ((rows.rows S).row n)
        (ConstructedConfiguredInductiveTubeBudget.WeightedData.shift
          J.scalar.E.data J.scalar.large.N) J.scalar.Mend (k + 1))
    (mappedSlice : ∀ {current : ℕ → Data} {k : ℕ}
      (S : CorrelatedColumn Q current e k P0 P1 khat G1 Cg C c dlt
        period diagonal kh Qmax K0 K1 K2)
      (H : SlicedCorrelatedColumn S) (n : ℕ),
      AnalyticSuccessorSliceFacts ((rows.rows S).successor.mappedColumn.source n))
    (mappedPeriodUpper_le : ∀ {current : ℕ → Data} {k : ℕ}
      (S : CorrelatedColumn Q current e k P0 P1 khat G1 Cg C c dlt
        period diagonal kh Qmax K0 K1 K2)
      (H : SlicedCorrelatedColumn S) (n : ℕ),
      (mappedSlice S H n).periodUpper ≤ P1 n) :
    CertifiedPresentedRowProvider Q e P0 P1 khat G1 Cg C c dlt
      period diagonal kh Qmax a MA NA K0 K1 K2
      (ConstructedConfiguredInductiveTubeBudget.WeightedData.shift
        J.scalar.E.data J.scalar.large.N) J.scalar.Mend where
  rows := rows
  defect_le := J.physicalDefect_le
  certificate := certificate
  mappedSlice := mappedSlice
  mappedPeriodUpper_le := mappedPeriodUpper_le

/-- The actual chosen jets install the near-identity sidecar automatically. -/
def CertifiedPresentedRowProvider.nearIdentitySlicedProvider
    {Q : ℕ → Data} {e : ℕ → ℕ → ℝ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
    {period : ℕ → ℕ → ℝ} {diagonal kh Qmax : ℕ → ℝ}
    {a MA NA : ℕ → ℕ → ℝ} {K0 K1 K2 : ℝ}
    {D : ConstructedConfiguredSequenceWeighted.Data} {M : ℝ}
    (G : CertifiedPresentedRowProvider Q e P0 P1 khat G1 Cg C c dlt
      period diagonal kh Qmax a MA NA K0 K1 K2 D M) :
    PresentedNearIdentitySlicedProvider Q e P0 P1 khat G1 Cg C c dlt
      period diagonal kh Qmax a MA NA K0 K1 K2 (edgeRowEps D M) where
  rows S _ := G.rows.rows S
  nearIdentity := by
    intro current k S H n
    exact ((G.certificate S n).chosenCertificate
      (G.defect_le (n + (k + 1)))).nearIdentitySelection
        ((G.rows.rows S).row n)
  mappedSlice := G.mappedSlice
  mappedPeriodUpper_le := G.mappedPeriodUpper_le

/-- Assemble the closure construction directly from an actual certified row
provider. -/
def CertifiedPresentedRowProvider.construction
    {Q : ℕ → Data} {e : ℕ → ℕ → ℝ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
    {period : ℕ → ℕ → ℝ} {diagonal kh Qmax : ℕ → ℝ}
    {a MA NA : ℕ → ℕ → ℝ} {K0 K1 K2 : ℝ}
    {D : ConstructedConfiguredSequenceWeighted.Data} {M : ℝ}
    (G : CertifiedPresentedRowProvider Q e P0 P1 khat G1 Cg C c dlt
      period diagonal kh Qmax a MA NA K0 K1 K2 D M)
    (current0 : ℕ → Data)
    (base : CorrelatedColumn Q current0 e 0 P0 P1 khat G1 Cg C c dlt
      period diagonal kh Qmax K0 K1 K2)
    (baseSlice : SlicedCorrelatedColumn base)
    (base_eq : ∀ n, base.column.step.next n = Q n) :
    Construction Q e P0 P1 khat G1 Cg C c dlt period diagonal kh Qmax
      a MA NA K0 K1 K2 (edgeRowEps D M) where
  current0 := current0
  base := base
  baseSlice := baseSlice
  base_eq := base_eq
  provider := G.nearIdentitySlicedProvider

/-- The common edge tail closes all row/depth marking bounds for the actual
chosen markings, with the fixed constants `1/2` and `3/2`. -/
def CertifiedPresentedRowProvider.markingBounds
    {Q : ℕ → Data} {e : ℕ → ℕ → ℝ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
    {period : ℕ → ℕ → ℝ} {diagonal kh Qmax : ℕ → ℝ}
    {a MA NA : ℕ → ℕ → ℝ} {K0 K1 K2 : ℝ}
    {MA0 NA0 : ℝ}
    (J : ConfiguredRecursiveEdgeSourceP0RowJetTail.RowJetScalarOutput MA0 NA0)
    (G : CertifiedPresentedRowProvider Q e P0 P1 khat G1 Cg C c dlt
      period diagonal kh Qmax a MA NA K0 K1 K2
      (ConstructedConfiguredInductiveTubeBudget.WeightedData.shift
        J.scalar.E.data J.scalar.large.N) J.scalar.Mend)
    (current0 : ℕ → Data)
    (base : CorrelatedColumn Q current0 e 0 P0 P1 khat G1 Cg C c dlt
      period diagonal kh Qmax K0 K1 K2)
    (baseSlice : SlicedCorrelatedColumn base)
    (base_eq : ∀ n, base.column.step.next n = Q n) :=
  let A := G.construction current0 base baseSlice base_eq
  A.markingBounds (fun n k ↦ J.jet_half n (k + 1))

end ConfiguredRecursiveEdgePresentedJetBounds
