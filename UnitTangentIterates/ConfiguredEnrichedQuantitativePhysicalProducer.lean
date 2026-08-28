import UnitTangentIterates.EnrichedPhysicalQuantitativeCap
import UnitTangentIterates.ConfiguredEnrichedPhysicalProducer
import UnitTangentIterates.ConfiguredEnrichedCommonTubeCertificate

/-!
# Quantitative physical output of the deterministic enriched provider

This module is the quantitative boundary for a correlated enriched row
producer.  A mapped row retains only the two estimates which are not already
present in `RowImage`: the distance from the configured model to the selected
column and the distance from that column to the normalized physical terminal.
All ordinary terminal facts, curvature, endpoint convergence, and finite
physical kinematics are recovered from the deterministic selected output.
-/

noncomputable section

open Filter MarkedSpace PathMetric

namespace ConfiguredEnrichedQuantitativePhysicalProducer

open TriangularMarkedRecursiveChoiceVariableTerminalConstructor
  EnrichedPhysicalChosenRichFamily
  FiniteSmoothRearFamilyEnrichedMapProvider

variable {Q : ℕ → Data} {e : ℕ → ℕ → ℝ}
  {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
  {period : ℕ → ℕ → ℝ} {diagonal : ℕ → ℝ}
  {GaugeCertificate : GaugeFamily Q e P0 P1 khat G1 Cg C c dlt}
  {a MA NA : ℕ → ℕ → ℝ} {K0 K1 K2 : ℝ}

def orientedNumerator (p : Data) (u : ℝ) : ℝ :=
  ((starRingEnd ℂ) (p.2.1 u) * p.2.2 u).im

/-- The only quantitative information missing from an actual mapped
`RowImage`.  Its ordinary terminal and corrected physical transition are
already fields of `W`; they are intentionally not repeated here. -/
structure RowImageCap
    {Q current : ℕ → Data} {e : ℕ → ℕ → ℝ} {k n : ℕ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
    {period : ℕ → ℕ → ℝ} {diagonal : ℕ → ℝ}
    {kh Qmax Mtotal : ℕ → ℝ}
    {a MA NA : ℕ → ℕ → ℝ} {K0 K1 K2 : ℝ}
    {S : ColumnStep Q current e k P0 P1 khat G1 Cg C c dlt}
    (W : RowImage period diagonal kh Qmax Mtotal a MA NA K0 K1 K2 S n)
    (model : Data) (columnRadius endpointCoeff defect : ℝ) : Prop where
  column_dist : dist model W.rear ≤ columnRadius
  endpoint_dist : dist W.rear W.output.terminalBase ≤ endpointCoeff * defect
  terminal_curvature : ∀ u, 0 ≤ orientedNumerator W.output.terminalBase u

/-- The same two estimates, stated on every column actually selected by a
construction core.  Unlike the downstream certificate, this record contains
no redundant physical or convergence callbacks. -/
structure SelectedRowsCap
    (F : ConstructionCore Q e P0 P1 khat G1 Cg C c dlt period diagonal
      GaugeCertificate a MA NA K0 K1 K2)
    (baseConversion endpointConversion diagonal' : ℕ → ℝ) : Prop where
  column_dist : ∀ n k,
    dist (Q n) ((F.chosenColumn k).step.next n) ≤
      ExponentialDiagonalLargeSeparation.rowRadius
        baseConversion diagonal' n
  endpoint_dist : ∀ n k,
    dist ((F.chosenColumn k).step.next n)
      ((F.chosenColumn k).step.richStage n).terminalBase ≤
        endpointConversion n * diagonal' (n + k)
  terminal_curvature : ∀ n k u, 0 ≤
    orientedNumerator ((F.chosenColumn k).step.richStage n).terminalBase u

/-- Summability of the diagonal automatically gives convergence of every
fixed-row endpoint correction. -/
theorem shifted_diagonal_tendsto_zero
    {d : ℕ → ℝ} (hsum : Summable d) (E : ℝ) (n : ℕ) :
    Tendsto (fun k ↦ E * d (n + k)) atTop (nhds 0) := by
  have hadd : Tendsto (fun k : ℕ ↦ n + k) atTop atTop := by
    rw [tendsto_atTop]
    intro b
    filter_upwards [eventually_ge_atTop b] with k hk
    exact hk.trans (Nat.le_add_left k n)
  simpa using (tendsto_const_nhds.mul
    (hsum.tendsto_atTop_zero.comp hadd))

/-- Forget the row-image presentation and construct the complete downstream
quantitative cap.  Terminal physical facts and oriented curvature are
projected from the exact selected rich stage, not supplied by the caller. -/
def SelectedRowsCap.toCertificate
    {F : ConstructionCore Q e P0 P1 khat G1 Cg C c dlt period diagonal
      (fun {current} {k} ↦
        FiniteSmoothRearFamilyEnrichedMapProvider.GaugeCertificate
          period K0 K1 K2) a MA NA K0 K1 K2}
    {baseConversion endpointConversion diagonal' : ℕ → ℝ}
    (R : SelectedRowsCap F baseConversion endpointConversion diagonal')
    (hsum : Summable diagonal') (hd : ∀ j, 0 ≤ diagonal' j)
    (hE : ∀ n, 0 ≤ endpointConversion n) :
    EnrichedPhysicalQuantitativeCap.Certificate F
      baseConversion endpointConversion diagonal'
      (fun n k ↦ diagonal' (n + k)) where
  diagonal_summable := hsum
  diagonal_nonnegative := hd
  endpointConversion_nonnegative := hE
  stageCost_nonnegative := fun n k ↦ hd (n + k)
  stageCost_le := fun _ _ ↦ le_rfl
  column_dist := R.column_dist
  endpoint_dist := R.endpoint_dist
  endpoint_tendsto := fun n ↦ shifted_diagonal_tendsto_zero hsum _ n
  terminalPhysical := fun n k ↦ Classical.choice
    (FiniteSmoothRearFamilyEnrichedMapProvider.GaugeCertificate.terminalPhysical_nonempty
      ((F.chosenColumn k).gauge n))
  terminalCurvature := fun n k u ↦ by
    simpa [orientedNumerator] using R.terminal_curvature n k u

/-- The deterministic map provider identifies the selected successor with
the concrete `RowImage` returned by `G.image`.  Thus mapped row caps and the
two base-row estimates give caps for the whole selected recursion. -/
def selectedRowsCap_of_rowImages
    {D : ConstructedConfiguredSequenceWeighted.Data} {Q : ℕ → Data}
    {kh c dlt : ℝ}
    (S : ConfiguredModelPairSource.Input D Q kh c dlt)
    (hQ : ∀ n,
      perim (Q n) = 2 * D.Hs n ∧
      ev (Q n) = TwoCapPairsAssembly.front
        (D.kappas n) D.model.thetaBase (D.Hs n))
    (C : ℕ → ℝ) {MA0 NA0 : ℝ} (hH : 1 ≤ D.Hs 0)
    (khRow Qmax Mtotal : ℕ → ℝ)
    (a MA NA : ℕ → ℕ → ℝ) (K0 K1 K2 : ℝ)
    (G : Provider (ConfiguredGaugeFirstPhysicalSequence.alignedQ S hQ)
      (ConfiguredDiagonalStableRowDefectProvider.error D
        (ConfiguredPolynomialDiagonalStableRowDefectProvider.physicalCoeff D))
      (ConfiguredApproximateDefectPathRowwise.rowP0 D)
      (ConfiguredRowCeilingPolynomialEnvelopes.wideP1 D MA0)
      (fun _ ↦ D.kstar)
      (ConfiguredRowCeilingPolynomialEnvelopes.wideG1 D MA0 NA0)
      (ConfiguredRowCeilingPolynomialEnvelopes.wideCg D MA0 NA0)
      C c dlt
      (ConfiguredEnrichedConstructionCoreProvider.period D)
      (ConfiguredEnrichedConstructionCoreProvider.diagonal D)
      khRow Qmax Mtotal a MA NA K0 K1 K2)
    {baseConversion endpointConversion diagonal' : ℕ → ℝ}
    (hbaseColumn : ∀ n,
      dist (ConfiguredGaugeFirstPhysicalSequence.alignedQ S hQ n)
        (((ConfiguredEnrichedConstructionCoreProvider.constructionCore
          S hQ C hH khRow Qmax Mtotal a MA NA K0 K1 K2 G).chosenColumn 0).step.next n) ≤
        ExponentialDiagonalLargeSeparation.rowRadius
          baseConversion diagonal' n)
    (hbaseEndpoint : ∀ n,
      dist (((ConfiguredEnrichedConstructionCoreProvider.constructionCore
          S hQ C hH khRow Qmax Mtotal a MA NA K0 K1 K2 G).chosenColumn 0).step.next n)
        (((ConfiguredEnrichedConstructionCoreProvider.constructionCore
          S hQ C hH khRow Qmax Mtotal a MA NA K0 K1 K2 G).chosenColumn 0).step.richStage n).terminalBase ≤
          endpointConversion n * diagonal' n)
    (hbaseCurvature : ∀ n u, 0 ≤ orientedNumerator
      (((ConfiguredEnrichedConstructionCoreProvider.constructionCore
        S hQ C hH khRow Qmax Mtotal a MA NA K0 K1 K2 G).chosenColumn 0).step.richStage n).terminalBase u)
    (hmapped : ∀ k n, RowImageCap
      (G.image
        ((ConfiguredEnrichedConstructionCoreProvider.constructionCore
          S hQ C hH khRow Qmax Mtotal a MA NA K0 K1 K2 G).chosenColumn k) n)
      (ConfiguredGaugeFirstPhysicalSequence.alignedQ S hQ n)
      (ExponentialDiagonalLargeSeparation.rowRadius
        baseConversion diagonal' n)
      (endpointConversion n) (diagonal' (n + (k + 1)))) :
    SelectedRowsCap
      (ConfiguredEnrichedConstructionCoreProvider.constructionCore
        S hQ C hH khRow Qmax Mtotal a MA NA K0 K1 K2 G)
      baseConversion endpointConversion diagonal' := by
  let F := ConfiguredEnrichedConstructionCoreProvider.constructionCore
    S hQ C hH khRow Qmax Mtotal a MA NA K0 K1 K2 G
  refine ⟨?_, ?_, ?_⟩
  · intro n k
    cases k with
    | zero => exact hbaseColumn n
    | succ k =>
        have H := (hmapped k n).column_dist
        change dist (ConfiguredGaugeFirstPhysicalSequence.alignedQ S hQ n)
          (G.image (F.chosenColumn k) n).rear ≤ _
        exact H
  · intro n k
    cases k with
    | zero => simpa using hbaseEndpoint n
    | succ k =>
        have H := (hmapped k n).endpoint_dist
        change dist (G.image (F.chosenColumn k) n).rear
          (G.image (F.chosenColumn k) n).output.terminalBase ≤ _
        simpa [Nat.add_assoc] using H
  · intro n k u
    cases k with
    | zero => exact hbaseCurvature n u
    | succ k =>
        have H := (hmapped k n).terminal_curvature u
        change 0 ≤ orientedNumerator
          (G.image (F.chosenColumn k) n).output.terminalBase u
        exact H

/-- Full physical producer for the deterministic configured recursion.  The
finite pullback kinematics are supplied by the exact selected `RowImage`s;
the caller supplies no separate finite-physical or endpoint-convergence
package. -/
def physicalProducer_of_selectedRowsCap
    {D : ConstructedConfiguredSequenceWeighted.Data} {Q : ℕ → Data}
    {kh c dlt : ℝ}
    (S : ConfiguredModelPairSource.Input D Q kh c dlt)
    (hQ : ∀ n,
      perim (Q n) = 2 * D.Hs n ∧
      ev (Q n) = TwoCapPairsAssembly.front
        (D.kappas n) D.model.thetaBase (D.Hs n))
    (C : ℕ → ℝ) {MA0 NA0 : ℝ} (hH : 1 ≤ D.Hs 0)
    (khRow Qmax Mtotal : ℕ → ℝ)
    (a MA NA : ℕ → ℕ → ℝ) (K0 K1 K2 : ℝ)
    (G : Provider (ConfiguredGaugeFirstPhysicalSequence.alignedQ S hQ)
      (ConfiguredDiagonalStableRowDefectProvider.error D
        (ConfiguredPolynomialDiagonalStableRowDefectProvider.physicalCoeff D))
      (ConfiguredApproximateDefectPathRowwise.rowP0 D)
      (ConfiguredRowCeilingPolynomialEnvelopes.wideP1 D MA0)
      (fun _ ↦ D.kstar)
      (ConfiguredRowCeilingPolynomialEnvelopes.wideG1 D MA0 NA0)
      (ConfiguredRowCeilingPolynomialEnvelopes.wideCg D MA0 NA0)
      C c dlt
      (ConfiguredEnrichedConstructionCoreProvider.period D)
      (ConfiguredEnrichedConstructionCoreProvider.diagonal D)
      khRow Qmax Mtotal a MA NA K0 K1 K2)
    (hkh : ∀ n, khRow n = kh)
    {baseConversion endpointConversion diagonal' : ℕ → ℝ}
    (R : SelectedRowsCap
      (ConfiguredEnrichedConstructionCoreProvider.constructionCore
        S hQ C hH khRow Qmax Mtotal a MA NA K0 K1 K2 G)
      baseConversion endpointConversion diagonal')
    (hsum : Summable diagonal') (hd : ∀ j, 0 ≤ diagonal' j)
    (hE : ∀ n, 0 ≤ endpointConversion n)
    {c0 d0 A0 r rho upper : ℕ → ℝ}
    (B : VariableTerminalRowTubeAdapter.RowBudget
      (ConfiguredGaugeFirstPhysicalSequence.alignedQ S hQ)
      (ConfiguredApproximateDefectPathRowwise.rowP0 D)
      (ConfiguredRowCeilingPolynomialEnvelopes.wideP1 D MA0)
      (fun _ ↦ D.kstar)
      (ConfiguredRowCeilingPolynomialEnvelopes.wideG1 D MA0 NA0)
      (ConfiguredRowCeilingPolynomialEnvelopes.wideCg D MA0 NA0)
      c0 d0 A0 r rho upper c dlt)
    (hradius : ∀ n, r n =
      ExponentialDiagonalLargeSeparation.rowRadius
        (ConfiguredGaugeEndpointLinearRadius.combinedConversion
          baseConversion endpointConversion) diagonal' n)
    (hbaseModel : ∀ n, IsTubeMember (c0 n) 0 (d0 n)
      (ConfiguredGaugeFirstPhysicalSequence.alignedQ S hQ n))
    (hbaseCommon : ∀ n, IsTubeMember c 0 dlt
      (ConfiguredGaugeFirstPhysicalSequence.alignedQ S hQ n))
    (hbasePerim : ∀ n, c0 n ≤
      perim (ConfiguredGaugeFirstPhysicalSequence.alignedQ S hQ n))
    (hbaseAcc : ∀ n u,
      ‖(ConfiguredGaugeFirstPhysicalSequence.alignedQ S hQ n).2.2 u‖ ≤ A0 n) :
    EnrichedPhysicalStageProducerFromRowBudget.PhysicalProducer
      (ConfiguredEnrichedConstructionCoreProvider.constructionCore
        S hQ C hH khRow Qmax Mtotal a MA NA K0 K1 K2 G) kh c dlt := by
  let F := ConfiguredEnrichedConstructionCoreProvider.constructionCore
    S hQ C hH khRow Qmax Mtotal a MA NA K0 K1 K2 G
  let cap := R.toCertificate hsum hd hE
  exact cap.toPhysicalProducer_of_rowBudget B hradius hbaseModel hbaseCommon
    hbasePerim hbaseAcc
    (ConfiguredEnrichedPhysicalProducer.constructionCore_finite
      (kh0 := kh) S hQ C hH khRow Qmax Mtotal a MA NA K0 K1 K2 G hkh)

end ConfiguredEnrichedQuantitativePhysicalProducer
