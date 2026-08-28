import UnitTangentIterates.SelectedInverseApproximateMapPathRearFamilyAdapter
import UnitTangentIterates.EnrichedPhysicalChosenTransitionAdapter

/-!
# Enriched finite rear-family columns

This is the non-erasing adapter from the finite smooth rear-family producer to
the dependent chosen-column recursion.  Each row stores the exact producer
output used for its `RichStageData` and the exact physical gauge transition
from the preceding selected row.  The resulting `MapProvider` therefore makes
one column choice; it does not independently choose a path, terminal marking,
or Jacobi certificate.
-/

noncomputable section

open Function MarkedSpace MarkedTopology PathMetric PathMetric.NormalPath
  RearOwnArclength RearFamilyFrame NormalPathC2IncrementVariableSpeed

namespace FiniteSmoothRearFamilyEnrichedMapProvider

open SelectedInverseApproximateMapPath
  TriangularMarkedRecursiveChoiceVariableTerminalConstructor
  EnrichedPhysicalChosenRichFamily
  AnchoredJacobiStableTransition
  PhysicalArclengthJacobiTransition

/-- The complete output selected in one row of a successor column. -/
structure RowImage
    {Q current : ℕ → Data} {e : ℕ → ℕ → ℝ} {k : ℕ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
    (period : ℕ → ℕ → ℝ) (diagonal : ℕ → ℝ)
    (kh Qmax Mtotal : ℕ → ℝ)
    (a MA NA : ℕ → ℕ → ℝ) (K0 K1 K2 : ℝ)
    (S : ColumnStep Q current e k P0 P1 khat G1 Cg C c dlt) (n : ℕ) where
  rear : Data
  F : ℝ → ℝ → ℂ
  Theta : ℝ → ℝ → ℝ
  delta : ℝ → ℝ → ℝ
  sf : ℝ → ℝ → ℝ
  Ydot : ℝ → ℝ → ℂ
  Phi : ℝ → ℝ → ℝ
  periodValue : ℝ
  costValue : ℝ
  enriched : FiniteSmoothRearFamilyEnrichedOutput
    (S.richStage (n + 1)).stage.increment F Theta delta sf Ydot Phi
    periodValue costValue (P0 n) (kh n) (khat n) (S.next n) rear
  cost_le : costValue ≤ e n (k + 1)
  P1_le : GaugeFlowDerivCost.costP1 periodValue
      (khat n) costValue ≤ P1 n
  G1_le : GaugeFlowDerivCost.costG1 periodValue
      (khat n) (GaugeMarkedDataOfRearFamily.rearKappa2 (kh n))
      costValue ≤ G1 n
  Cg_le : (khat n) *
      GaugeFlowDerivCost.costG1 periodValue
        (khat n) (GaugeMarkedDataOfRearFamily.rearKappa2 (kh n))
        costValue +
      GaugeMarkedDataOfRearFamily.rearKappa2 (kh n) *
        GaugeFlowDerivCost.costP1 periodValue
          (khat n) costValue ^ 2 ≤ Cg n
  khat_nonnegative : 0 ≤ khat n
  period_ge_one : 1 ≤ period n (k + 1)
  components_nonnegative :
    (components (period n (k + 1))
      enriched.Delta.eta).Nonnegative
  components_bound : ComponentBound
    (components (period n (k + 1))
      enriched.Delta.eta)
    (diagonal (n + (k + 1)))
  physicalKinematics : PhysicalRearLimitKinematics (kh n)
    enriched.terminalBase
    (S.richStage (n + 1)).terminalBase
  raw : ℝ → ℝ → ℝ
  aRaw : ℝ
  mRaw : ℝ
  MRaw : ℝ
  NRaw : ℝ
  CW : ℝ
  C00 : ℝ
  C10 : ℝ
  C11 : ℝ
  C20 : ℝ
  C21 : ℝ
  C22 : ℝ
  a_eq : a n k = aRaw * (1 / mRaw)
  MA_eq : MA n k = MRaw
  NA_eq : NA n k = NRaw
  gaugeOutput : EnrichedPhysicalGaugeStage.Output
    (S.richStage (n + 1)).stage.increment.eta raw
    enriched.Delta.eta
    (period (n + 1) k) (period n (k + 1))
    aRaw mRaw MRaw NRaw CW C00 C10 C11 C20 C21 C22
    K0 K1 K2

/-- The exact enriched output selected by a row image. -/
def RowImage.output
    {Q current : ℕ → Data} {e : ℕ → ℕ → ℝ} {k : ℕ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
    {period : ℕ → ℕ → ℝ} {diagonal : ℕ → ℝ}
    {kh Qmax Mtotal : ℕ → ℝ}
    {a MA NA : ℕ → ℕ → ℝ} {K0 K1 K2 : ℝ}
    {S : ColumnStep Q current e k P0 P1 khat G1 Cg C c dlt}
    (W : RowImage period diagonal kh Qmax Mtotal a MA NA K0 K1 K2 S n) :=
  W.enriched

/-- The gauge certificate stored on a selected successor row. -/
structure MappedGaugeCertificate
    {Q current : ℕ → Data} {e : ℕ → ℕ → ℝ} {k : ℕ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
    (period : ℕ → ℕ → ℝ)
    (K0 K1 K2 : ℝ)
    (T : ColumnStep Q current e k P0 P1 khat G1 Cg C c dlt) (n : ℕ) where
  front : ℝ → ℝ → ℝ
  raw : ℝ → ℝ → ℝ
  sourceDepth : ℕ
  aRaw : ℝ
  mRaw : ℝ
  MRaw : ℝ
  NRaw : ℝ
  CW : ℝ
  C00 : ℝ
  C10 : ℝ
  C11 : ℝ
  C20 : ℝ
  C21 : ℝ
  C22 : ℝ
  output : EnrichedPhysicalGaugeStage.Output front raw
    (T.richStage n).stage.increment.eta
    (period (n + 1) sourceDepth) (period n k)
    aRaw mRaw MRaw NRaw CW C00 C10 C11 C20 C21 C22 K0 K1 K2
  terminalBase : Data
  terminalBase_eq : terminalBase = (T.richStage n).terminalBase
  terminalPhysical : ConfiguredGaugeEndpointDefect.TerminalPhysicalFacts
    terminalBase
  frontTerminalBase : Data
  kh : ℝ
  physicalKinematics : PhysicalRearLimitKinematics kh terminalBase
    frontTerminalBase

/-- Depth zero has no preceding transition.  It retains only the physical
ordinary representative belonging to the selected base rich stage. -/
structure BaseGaugeCertificate
    {Q current : ℕ → Data} {e : ℕ → ℕ → ℝ} {k : ℕ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
    (T : ColumnStep Q current e k P0 P1 khat G1 Cg C c dlt) (n : ℕ) where
  terminalBase : Data
  terminalBase_eq : terminalBase = (T.richStage n).terminalBase
  terminalPhysical : ConfiguredGaugeEndpointDefect.TerminalPhysicalFacts
    terminalBase

/-- One certificate family for both the physical diagonal and mapped
successors.  Only the mapped constructor carries a component transition. -/
inductive GaugeCertificate
    {Q current : ℕ → Data} {e : ℕ → ℕ → ℝ} {k : ℕ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
    (period : ℕ → ℕ → ℝ) (K0 K1 K2 : ℝ)
    (T : ColumnStep Q current e k P0 P1 khat G1 Cg C c dlt) (n : ℕ) : Type
  | base : BaseGaugeCertificate T n → GaugeCertificate period K0 K1 K2 T n
  | mapped : MappedGaugeCertificate period K0 K1 K2 T n →
      GaugeCertificate period K0 K1 K2 T n

abbrev GaugeFamily
    (period : ℕ → ℕ → ℝ) (K0 K1 K2 : ℝ) :
    EnrichedPhysicalChosenRichFamily.GaugeFamily Q e P0 P1 khat G1 Cg C c dlt :=
  fun T n => GaugeCertificate period K0 K1 K2 T n

/-- Rowwise finite smooth rear-family production. -/
structure Provider
    (Q : ℕ → Data) (e : ℕ → ℕ → ℝ)
    (P0 P1 khat G1 Cg C : ℕ → ℝ) (c dlt : ℝ)
    (period : ℕ → ℕ → ℝ) (diagonal : ℕ → ℝ)
    (kh Qmax Mtotal : ℕ → ℝ)
    (a MA NA : ℕ → ℕ → ℝ) (K0 K1 K2 : ℝ) where
  image : ∀ {current k}
    (S : CertifiedColumn Q current e k P0 P1 khat G1 Cg C c dlt
      period diagonal (GaugeFamily period K0 K1 K2)) n,
    RowImage period diagonal kh Qmax Mtotal a MA NA K0 K1 K2 S.step n

/-- Build the deterministic selected successor from an already correlated
row-image family.  This is the non-erasing core of `mappedColumn`; exposing it
separately lets a source-preserving recursion carry additional analytic data
without manufacturing a global provider for unrelated columns. -/
def mappedColumnOfRows
    {Q : ℕ → Data} {e : ℕ → ℕ → ℝ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
    {period : ℕ → ℕ → ℝ} {diagonal : ℕ → ℝ}
    {kh Qmax Mtotal : ℕ → ℝ}
    {a MA NA : ℕ → ℕ → ℝ} {K0 K1 K2 : ℝ}
    {k : ℕ} {current : ℕ → Data}
    (S : CertifiedColumn Q current e k P0 P1 khat G1 Cg C c dlt
      period diagonal (GaugeFamily period K0 K1 K2))
    (W : ∀ n, RowImage period diagonal kh Qmax Mtotal
      a MA NA K0 K1 K2 S.step n) :
    {T : CertifiedColumn Q S.step.next e (k + 1)
      P0 P1 khat G1 Cg C c dlt period diagonal
        (GaugeFamily period K0 K1 K2) //
      TransitionCertificate S T a MA NA K0 K1 K2} := by
  let next : ℕ → Data := fun n => (W n).rear
  let step : ColumnStep Q S.step.next e (k + 1) P0 P1 khat G1 Cg C c dlt :=
    { next := next
      richStage := fun n => by
        let E := (W n).output
        have hgeom := IsVariableSpeedNormalPath.mono E.Delta E.geometry
          (W n).khat_nonnegative (W n).P1_le (W n).G1_le (W n).Cg_le
        exact
          { stage :=
              { increment := E.Delta
                increment_geometry := hgeom
                increment_cost := E.cost_eq.le.trans (W n).cost_le
                rear_curve_deriv := E.terminal.rear_curve_deriv
                rear_vel_deriv := E.terminal.rear_vel_deriv
                rear_periodic := E.terminal.rear_periodic
                rear_curvature_nonnegative := E.terminal.rear_curvature_nonnegative
                range_edge := E.terminal.range_edge
                rear_harnack := E.terminal.rear_harnack }
            terminalBase := E.terminalBase
            lambda := E.lambda
            Lambda := E.Lambda
            marking := E.marking } }
  let cert : ∀ n, MappedGaugeCertificate period K0 K1 K2 step n := fun n =>
    { front := (S.step.richStage (n + 1)).stage.increment.eta
      raw := (W n).raw
      sourceDepth := k
      aRaw := (W n).aRaw
      mRaw := (W n).mRaw
      MRaw := (W n).MRaw
      NRaw := (W n).NRaw
      CW := (W n).CW
      C00 := (W n).C00
      C10 := (W n).C10
      C11 := (W n).C11
      C20 := (W n).C20
      C21 := (W n).C21
      C22 := (W n).C22
      output := by simpa [step] using (W n).gaugeOutput
      terminalBase := (W n).output.terminalBase
      terminalBase_eq := by rfl
      terminalPhysical := (W n).output.terminalPhysical
      frontTerminalBase := (S.step.richStage (n + 1)).terminalBase
      kh := kh n
      physicalKinematics := by
        simpa [step] using (W n).physicalKinematics }
  let T : CertifiedColumn Q S.step.next e (k + 1) P0 P1 khat G1 Cg C c dlt
      period diagonal (GaugeFamily period K0 K1 K2) :=
    { step := step
      period_ge_one := fun n => (W n).period_ge_one
      components_nonnegative := fun n => by
        simpa [step] using (W n).components_nonnegative
      components_bound := fun n => by
        simpa [step] using (W n).components_bound
      gauge := fun n => GaugeCertificate.mapped (cert n) }
  refine ⟨T, ?_⟩
  refine { transition := fun n => ?_ }
  have H := (cert n).output.transition
  simpa [T, step, cert, (W n).a_eq, (W n).MA_eq, (W n).NA_eq] using H

/-- The deterministic selected successor and its exact stored transition. -/
def mappedColumn
    {Q : ℕ → Data} {e : ℕ → ℕ → ℝ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
    {period : ℕ → ℕ → ℝ} {diagonal : ℕ → ℝ}
    {kh Qmax Mtotal : ℕ → ℝ}
    {a MA NA : ℕ → ℕ → ℝ} {K0 K1 K2 : ℝ}
    (G : Provider Q e P0 P1 khat G1 Cg C c dlt
      period diagonal kh Qmax Mtotal a MA NA K0 K1 K2)
    (k : ℕ) {current : ℕ → Data}
    (S : CertifiedColumn Q current e k P0 P1 khat G1 Cg C c dlt
      period diagonal (GaugeFamily period K0 K1 K2)) :
    {T : CertifiedColumn Q S.step.next e (k + 1)
      P0 P1 khat G1 Cg C c dlt period diagonal
        (GaugeFamily period K0 K1 K2) //
      TransitionCertificate S T a MA NA K0 K1 K2} := by
  let W : ∀ n, RowImage period diagonal kh Qmax Mtotal
      a MA NA K0 K1 K2 S.step n :=
    fun n => G.image S n
  let next : ℕ → Data := fun n => (W n).rear
  let step : ColumnStep Q S.step.next e (k + 1) P0 P1 khat G1 Cg C c dlt :=
    { next := next
      richStage := fun n => by
        let E := (W n).output
        have hgeom := IsVariableSpeedNormalPath.mono E.Delta E.geometry
          (W n).khat_nonnegative (W n).P1_le (W n).G1_le (W n).Cg_le
        exact
          { stage :=
              { increment := E.Delta
                increment_geometry := hgeom
                increment_cost := E.cost_eq.le.trans (W n).cost_le
                rear_curve_deriv := E.terminal.rear_curve_deriv
                rear_vel_deriv := E.terminal.rear_vel_deriv
                rear_periodic := E.terminal.rear_periodic
                rear_curvature_nonnegative := E.terminal.rear_curvature_nonnegative
                range_edge := E.terminal.range_edge
                rear_harnack := E.terminal.rear_harnack }
            terminalBase := E.terminalBase
            lambda := E.lambda
            Lambda := E.Lambda
            marking := E.marking } }
  let cert : ∀ n, MappedGaugeCertificate period K0 K1 K2 step n := fun n =>
    { front := (S.step.richStage (n + 1)).stage.increment.eta
      raw := (W n).raw
      sourceDepth := k
      aRaw := (W n).aRaw
      mRaw := (W n).mRaw
      MRaw := (W n).MRaw
      NRaw := (W n).NRaw
      CW := (W n).CW
      C00 := (W n).C00
      C10 := (W n).C10
      C11 := (W n).C11
      C20 := (W n).C20
      C21 := (W n).C21
      C22 := (W n).C22
      output := by simpa [step] using (W n).gaugeOutput
      terminalBase := (W n).output.terminalBase
      terminalBase_eq := by rfl
      terminalPhysical := (W n).output.terminalPhysical
      frontTerminalBase := (S.step.richStage (n + 1)).terminalBase
      kh := kh n
      physicalKinematics := by
        simpa [step] using (W n).physicalKinematics }
  let T : CertifiedColumn Q S.step.next e (k + 1) P0 P1 khat G1 Cg C c dlt
      period diagonal (GaugeFamily period K0 K1 K2) :=
    { step := step
      period_ge_one := fun n => (W n).period_ge_one
      components_nonnegative := fun n => by
        simpa [step] using (W n).components_nonnegative
      components_bound := fun n => by
        simpa [step] using (W n).components_bound
      gauge := fun n => GaugeCertificate.mapped (cert n) }
  refine ⟨T, ?_⟩
  refine { transition := fun n => ?_ }
  have H := (cert n).output.transition
  simpa [T, step, cert, (W n).a_eq, (W n).MA_eq, (W n).NA_eq] using H

/-- `mappedColumn` as the abstract nonempty successor interface. -/
def mapProvider
    {Q : ℕ → Data} {e : ℕ → ℕ → ℝ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
    {period : ℕ → ℕ → ℝ} {diagonal : ℕ → ℝ}
    {kh Qmax Mtotal : ℕ → ℝ}
    {a MA NA : ℕ → ℕ → ℝ} {K0 K1 K2 : ℝ}
    (G : Provider Q e P0 P1 khat G1 Cg C c dlt
      period diagonal kh Qmax Mtotal a MA NA K0 K1 K2) :
    EnrichedPhysicalChosenRichFamily.MapProvider Q e P0 P1 khat G1 Cg C c dlt
      period diagonal (GaugeFamily period K0 K1 K2)
      a MA NA K0 K1 K2 :=
  { map := fun k _ S => mappedColumn G k S }

end FiniteSmoothRearFamilyEnrichedMapProvider
