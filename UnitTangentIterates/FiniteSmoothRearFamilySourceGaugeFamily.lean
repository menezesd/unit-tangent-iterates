import UnitTangentIterates.FiniteSmoothRearFamilyAnalyticSource

/-!
# Gauge certificates retaining the next analytic source

The generic recursive core quantifies over arbitrary certified columns.  A
side-car source attached only to the chosen recursion is therefore too weak:
it cannot define the global map provider.  This module stores the rowwise
analytic source in the column's gauge certificate itself and carries it across
one deterministic successor step.
-/

noncomputable section

open MarkedSpace PathMetric

namespace FiniteSmoothRearFamilySourceGaugeFamily

open EnrichedPhysicalChosenRichFamily
  FiniteSmoothRearFamilyAnalyticSource
  FiniteSmoothRearFamilyEnrichedMapProvider
  TriangularMarkedRecursiveChoiceVariableTerminalConstructor

/-- The existing physical gauge certificate together with the analytic source
for the path in the following row. -/
structure SourceGaugeCertificate
    {Q current : ℕ → Data} {e : ℕ → ℕ → ℝ} {k : ℕ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
    (period : ℕ → ℕ → ℝ) (K0 K1 K2 : ℝ)
    (kh Qmax : ℕ → ℝ)
    (T : ColumnStep Q current e k P0 P1 khat G1 Cg C c dlt) (n : ℕ) where
  physical : GaugeCertificate period K0 K1 K2 T n
  analytic : Source (T.richStage (n + 1)).stage.increment
    (P0 n) (kh n) (khat n) (Qmax n)

abbrev SourceGaugeFamily
    (period : ℕ → ℕ → ℝ) (K0 K1 K2 : ℝ)
    (kh Qmax : ℕ → ℝ) :
    EnrichedPhysicalChosenRichFamily.GaugeFamily
      Q e P0 P1 khat G1 Cg C c dlt :=
  fun T n => SourceGaugeCertificate period K0 K1 K2 kh Qmax T n

/-- Forget analytic sources only at the old physical-column boundary. -/
def eraseSources
    {Q current : ℕ → Data} {e : ℕ → ℕ → ℝ} {k : ℕ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
    {period : ℕ → ℕ → ℝ} {diagonal : ℕ → ℝ}
    {kh Qmax : ℕ → ℝ} {K0 K1 K2 : ℝ}
    (S : CertifiedColumn Q current e k P0 P1 khat G1 Cg C c dlt
      period diagonal (SourceGaugeFamily period K0 K1 K2 kh Qmax)) :
    CertifiedColumn Q current e k P0 P1 khat G1 Cg C c dlt
      period diagonal (GaugeFamily period K0 K1 K2) where
  step := S.step
  period_ge_one := S.period_ge_one
  components_nonnegative := S.components_nonnegative
  components_bound := S.components_bound
  gauge := fun n => (S.gauge n).physical

/-- A global row constructor on source-bearing certified columns.  The two
fields are outputs which concrete analytic theorems must construct; no source
is reconstructed after erasure. -/
structure Provider
    (Q : ℕ → Data) (e : ℕ → ℕ → ℝ)
    (P0 P1 khat G1 Cg C : ℕ → ℝ) (c dlt : ℝ)
    (period : ℕ → ℕ → ℝ) (diagonal : ℕ → ℝ)
    (kh Qmax Mtotal : ℕ → ℝ)
    (a MA NA : ℕ → ℕ → ℝ) (K0 K1 K2 : ℝ) where
  row : ∀ {current k}
    (S : CertifiedColumn Q current e k P0 P1 khat G1 Cg C c dlt
      period diagonal (SourceGaugeFamily period K0 K1 K2 kh Qmax)) (n : ℕ),
    RowImage period diagonal kh Qmax Mtotal a MA NA K0 K1 K2 S.step n
  successorSource : ∀ {current k}
    (S : CertifiedColumn Q current e k P0 P1 khat G1 Cg C c dlt
      period diagonal (SourceGaugeFamily period K0 K1 K2 kh Qmax)) (n : ℕ),
    Source ((row S (n + 1)).output.Delta)
      (P0 n) (kh n) (khat n) (Qmax n)

/-- One deterministic mapped column, retaining both its physical certificate
and the exact analytic source belonging to its next row. -/
def mappedColumn
    {Q : ℕ → Data} {e : ℕ → ℕ → ℝ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
    {period : ℕ → ℕ → ℝ} {diagonal : ℕ → ℝ}
    {kh Qmax Mtotal : ℕ → ℝ}
    {a MA NA : ℕ → ℕ → ℝ} {K0 K1 K2 : ℝ}
    (G : Provider Q e P0 P1 khat G1 Cg C c dlt period diagonal
      kh Qmax Mtotal a MA NA K0 K1 K2)
    {current : ℕ → Data} {k : ℕ}
    (S : CertifiedColumn Q current e k P0 P1 khat G1 Cg C c dlt
      period diagonal (SourceGaugeFamily period K0 K1 K2 kh Qmax)) :
    {T : CertifiedColumn Q S.step.next e (k + 1)
      P0 P1 khat G1 Cg C c dlt period diagonal
        (SourceGaugeFamily period K0 K1 K2 kh Qmax) //
      TransitionCertificate S T a MA NA K0 K1 K2} := by
  let S0 := eraseSources S
  let W := fun n => G.row S n
  let T0 := mappedColumnOfRows S0 W
  let T : CertifiedColumn Q S.step.next e (k + 1)
      P0 P1 khat G1 Cg C c dlt period diagonal
        (SourceGaugeFamily period K0 K1 K2 kh Qmax) :=
    { step := T0.val.step
      period_ge_one := T0.val.period_ge_one
      components_nonnegative := T0.val.components_nonnegative
      components_bound := T0.val.components_bound
      gauge := fun n =>
        { physical := T0.val.gauge n
          analytic := by
            simpa [T0, mappedColumnOfRows, W] using G.successorSource S n } }
  refine ⟨T, ?_⟩
  refine { transition := fun n => ?_ }
  simpa [T, T0, S0, eraseSources] using T0.property.transition n

end FiniteSmoothRearFamilySourceGaugeFamily
