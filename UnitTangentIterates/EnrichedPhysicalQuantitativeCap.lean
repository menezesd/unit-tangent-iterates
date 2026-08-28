import UnitTangentIterates.ConfiguredGaugeEndpointLinearRadius
import UnitTangentIterates.TerminalPhysicalRowBudgetTube
import UnitTangentIterates.EnrichedPhysicalStageProducerFromRowBudget

/-!
# Quantitative caps on the retained enriched physical rows

This is the narrow downstream interface left after a concrete enriched gauge
row has been produced.  It retains the model-to-column estimate and the
column-to-physical-marking estimate separately.  Their composition is the
paper's non-multiplicative combined radius.
-/

noncomputable section

open Filter Set MarkedSpace PathMetric

namespace EnrichedPhysicalQuantitativeCap

open EnrichedPhysicalChosenRichFamily
open EnrichedPhysicalStageProducerFromRowBudget
open VariableTerminalRowTubeAdapter

variable {Q : ℕ → Data} {e : ℕ → ℕ → ℝ}
  {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
  {period : ℕ → ℕ → ℝ} {diagonal : ℕ → ℝ}
  {GaugeCertificate : GaugeFamily Q e P0 P1 khat G1 Cg C c dlt}
  {a MA NA : ℕ → ℕ → ℝ} {K0 K1 K2 : ℝ}

/-- Quantitative information retained on the actual selected columns.  The
certificate deliberately does not postulate a `PhysicalProducer`: it records
the two estimates and ordinary physical facts from which that producer is
derived. -/
structure Certificate
    (F : ConstructionCore Q e P0 P1 khat G1 Cg C c dlt period diagonal
      (fun {current} {k} ↦ GaugeCertificate) a MA NA K0 K1 K2)
    (baseConversion endpointConversion diagonal' : ℕ → ℝ)
    (stageCost : ℕ → ℕ → ℝ) : Type where
  diagonal_summable : Summable diagonal'
  diagonal_nonnegative : ∀ j, 0 ≤ diagonal' j
  endpointConversion_nonnegative : ∀ n, 0 ≤ endpointConversion n
  stageCost_nonnegative : ∀ n k, 0 ≤ stageCost n k
  stageCost_le : ∀ n k, stageCost n k ≤ diagonal' (n + k)
  column_dist : ∀ n k,
    dist (Q n) ((F.chosenColumn k).step.next n) ≤
      ExponentialDiagonalLargeSeparation.rowRadius
        baseConversion diagonal' n
  endpoint_dist : ∀ n k,
    dist ((F.chosenColumn k).step.next n)
      ((F.chosenColumn k).step.richStage n).terminalBase ≤
        endpointConversion n * stageCost n k
  endpoint_tendsto : ∀ n,
    Tendsto (fun k ↦ endpointConversion n * stageCost n k)
      atTop (nhds 0)
  terminalPhysical : ∀ n k,
    ConfiguredGaugeEndpointDefect.TerminalPhysicalFacts
      ((F.chosenColumn k).step.richStage n).terminalBase
  terminalCurvature : ∀ n k u, 0 ≤
    ((starRingEnd ℂ)
      (((F.chosenColumn k).step.richStage n).terminalBase.2.1 u) *
      ((F.chosenColumn k).step.richStage n).terminalBase.2.2 u).im

/-- The two retained estimates give the exact combined physical radius used
by the large-separation construction. -/
theorem Certificate.combined_dist
    {F : ConstructionCore Q e P0 P1 khat G1 Cg C c dlt period diagonal
      (fun {current} {k} ↦ GaugeCertificate) a MA NA K0 K1 K2}
    {baseConversion endpointConversion diagonal' : ℕ → ℝ}
    {stageCost : ℕ → ℕ → ℝ}
    (R : Certificate F baseConversion endpointConversion diagonal' stageCost)
    (n k : ℕ) :
    dist (Q n) ((F.chosenColumn k).step.richStage n).terminalBase ≤
      ExponentialDiagonalLargeSeparation.rowRadius
        (ConfiguredGaugeEndpointLinearRadius.combinedConversion
          baseConversion endpointConversion) diagonal' n := by
  exact ConfiguredGaugeEndpointLinearRadius.terminalBase_dist_le_combinedRadius
    R.diagonal_summable R.diagonal_nonnegative
    R.endpointConversion_nonnegative R.stageCost_le
    (R.column_dist n k) (R.endpoint_dist n k)

/-- The physical marking-to-column distance is itself bounded by the combined
row radius. -/
theorem Certificate.endpoint_dist_le_combined
    {F : ConstructionCore Q e P0 P1 khat G1 Cg C c dlt period diagonal
      (fun {current} {k} ↦ GaugeCertificate) a MA NA K0 K1 K2}
    {baseConversion endpointConversion diagonal' : ℕ → ℝ}
    {stageCost : ℕ → ℕ → ℝ}
    (R : Certificate F baseConversion endpointConversion diagonal' stageCost)
    (n k : ℕ) :
    dist ((F.chosenColumn k).step.richStage n).terminalBase
        ((F.chosenColumn k).step.next n) ≤
      ExponentialDiagonalLargeSeparation.rowRadius
        (ConfiguredGaugeEndpointLinearRadius.combinedConversion
          baseConversion endpointConversion) diagonal' n := by
  have hsum :=
    ConfiguredGaugeEndpointLinearRadius.columnRadius_add_endpoint_le_combinedRadius
      (C := baseConversion) R.diagonal_summable R.diagonal_nonnegative
      R.endpointConversion_nonnegative R.stageCost_le n k
  have hbase0 : 0 ≤
      ExponentialDiagonalLargeSeparation.rowRadius
        baseConversion diagonal' n :=
    le_trans dist_nonneg (R.column_dist n k)
  rw [dist_comm]
  exact (R.endpoint_dist n k).trans (by linarith)

/-- A quantitative cap plus the configured row budget produces all fixed-row
tube, perimeter, acceleration, and endpoint bounds. -/
def Certificate.physicalBounds
    {F : ConstructionCore Q e P0 P1 khat G1 Cg C c dlt period diagonal
      (fun {current} {k} ↦ GaugeCertificate) a MA NA K0 K1 K2}
    {baseConversion endpointConversion diagonal' : ℕ → ℝ}
    {stageCost : ℕ → ℕ → ℝ}
    (R : Certificate F baseConversion endpointConversion diagonal' stageCost)
    {c0 d0 A0 r rho upper : ℕ → ℝ}
    (B : RowBudget Q P0 P1 khat G1 Cg c0 d0 A0 r rho upper c dlt)
    (hradius : ∀ n, r n =
      ExponentialDiagonalLargeSeparation.rowRadius
        (ConfiguredGaugeEndpointLinearRadius.combinedConversion
          baseConversion endpointConversion) diagonal' n)
    (hbaseModel : ∀ n, IsTubeMember (c0 n) 0 (d0 n) (Q n))
    (hbaseCommon : ∀ n, IsTubeMember c 0 dlt (Q n))
    (hbasePerim : ∀ n, c0 n ≤ perim (Q n))
    (hbaseAcc : ∀ n u, ‖(Q n).2.2 u‖ ≤ A0 n) :
    RichFamilyPhysicalMarkingIntegration.PhysicalRowBounds
      (EnrichedPhysicalHarnackClosure.retainedRows
        F.baseProvider F.mapProvider)
      (fun n k ↦ columns F.baseProvider F.mapProvider k n) c dlt := by
  let Lmin : ℕ → ℝ := fun n ↦ c0 n - r n
  let Ab : ℕ → ℝ := fun n ↦ A0 n + r n
  refine
    { Lmin := Lmin
      Lmax := upper
      Ab := Ab
      r := r
      Lmin_pos := B.local_speed_positive
      Ab_nonneg := fun n ↦ add_nonneg (B.acceleration_nonnegative n)
        (B.radius_nonnegative n)
      r_nonneg := B.radius_nonnegative
      physical_tube := ?_
      physical_perim_lower := ?_
      physical_perim_upper := ?_
      physical_acc := ?_
      endpoint_dist := ?_ }
  · intro n k
    cases k with
    | zero => simpa [EnrichedPhysicalHarnackClosure.retainedRows] using hbaseCommon n
    | succ k =>
        apply TerminalPhysicalRowBudgetTube.mem_of_rowBudget B n
          (hbaseModel n) (hbaseAcc n) (R.terminalPhysical n k)
          (R.terminalCurvature n k)
        rw [hradius n]
        exact R.combined_dist n k
  · intro n k
    cases k with
    | zero =>
        simp only [EnrichedPhysicalHarnackClosure.retainedRows]
        dsimp [Lmin]
        linarith [B.radius_nonnegative n, hbasePerim n]
    | succ k =>
        let Z := ((F.chosenColumn k).step.richStage n).terminalBase
        have hp := abs_perim_sub_le_dist (Q n) Z
        have hd : dist (Q n) Z ≤ r n := by
          rw [hradius n]
          exact R.combined_dist n k
        have hone : perim (Q n) - perim Z ≤ dist (Q n) Z :=
          (le_abs_self _).trans hp
        change c0 n - r n ≤ perim Z
        linarith [hone.trans hd, hbasePerim n]
  · intro n k
    cases k with
    | zero =>
        simp only [EnrichedPhysicalHarnackClosure.retainedRows]
        linarith [B.upper_speed n, B.radius_nonnegative n]
    | succ k =>
        let Z := ((F.chosenColumn k).step.richStage n).terminalBase
        have hp := abs_perim_sub_le_dist Z (Q n)
        have hd : dist Z (Q n) ≤ r n := by
          rw [dist_comm, hradius n]
          exact R.combined_dist n k
        have hone : perim Z - perim (Q n) ≤ dist Z (Q n) :=
          (le_abs_self _).trans hp
        change perim Z ≤ upper n
        linarith [hone.trans hd, B.upper_speed n]
  · intro n k u
    cases k with
    | zero =>
        simp only [EnrichedPhysicalHarnackClosure.retainedRows]
        dsimp [Ab]
        exact (hbaseAcc n u).trans
          (le_add_of_nonneg_right (B.radius_nonnegative n))
    | succ k =>
        let Z := ((F.chosenColumn k).step.richStage n).terminalBase
        have hd : dist Z (Q n) ≤ r n := by
          rw [dist_comm, hradius n]
          exact R.combined_dist n k
        have hdiff := VariableMarkedTubeLocalStability.dist_acc_apply_le Z (Q n) u
        have htri : ‖Z.2.2 u‖ ≤ ‖Z.2.2 u - (Q n).2.2 u‖ + ‖(Q n).2.2 u‖ := by
          conv_lhs => rw [← sub_add_cancel (Z.2.2 u) ((Q n).2.2 u)]
          exact norm_add_le _ _
        change ‖Z.2.2 u‖ ≤ A0 n + r n
        calc
          ‖Z.2.2 u‖ ≤ ‖Z.2.2 u - (Q n).2.2 u‖ + ‖(Q n).2.2 u‖ := htri
          _ ≤ r n + A0 n := add_le_add (hdiff.trans hd) (hbaseAcc n u)
          _ = A0 n + r n := add_comm _ _
  · intro n k
    cases k with
    | zero =>
        simp [EnrichedPhysicalHarnackClosure.retainedRows, columns_zero,
          B.radius_nonnegative n]
    | succ k =>
        simp only [EnrichedPhysicalHarnackClosure.retainedRows, columns_succ]
        rw [hradius n]
        exact R.endpoint_dist_le_combined n k

/-- The retained endpoint estimate also gives the exact endpoint-defect
certificate needed by the direct limit closure. -/
def Certificate.endpointDefect
    {F : ConstructionCore Q e P0 P1 khat G1 Cg C c dlt period diagonal
      (fun {current} {k} ↦ GaugeCertificate) a MA NA K0 K1 K2}
    {baseConversion endpointConversion diagonal' : ℕ → ℝ}
    {stageCost : ℕ → ℕ → ℝ}
    (R : Certificate F baseConversion endpointConversion diagonal' stageCost) :
    F.EndpointDefectCertificate := by
  apply ConfiguredGaugeEndpointDefect.coreEndpointDefectCertificate F
    R.endpoint_tendsto
  intro n k
  rw [dist_comm]
  exact R.endpoint_dist n k

/-- Once finite physical kinematics are available (automatic for the
deterministic configured provider), the cap constructs the complete downstream
physical producer. -/
def Certificate.toPhysicalProducer
    {F : ConstructionCore Q e P0 P1 khat G1 Cg C c dlt period diagonal
      (fun {current} {k} ↦ GaugeCertificate) a MA NA K0 K1 K2}
    {baseConversion endpointConversion diagonal' : ℕ → ℝ}
    {stageCost : ℕ → ℕ → ℝ}
    (R : Certificate F baseConversion endpointConversion diagonal' stageCost)
    {kh cb db : ℝ}
    (bounds : RichFamilyPhysicalMarkingIntegration.PhysicalRowBounds
      (EnrichedPhysicalHarnackClosure.retainedRows
        F.baseProvider F.mapProvider)
      (fun n k ↦ columns F.baseProvider F.mapProvider k n) cb db)
    (finite : FinitePullbackPhysicalRearKinematics kh
      (EnrichedPhysicalHarnackClosure.retainedRows
        F.baseProvider F.mapProvider)) :
    PhysicalProducer F kh cb db :=
  ⟨bounds, finite, R.endpointDefect⟩

/-- One-call downstream constructor: the scalar row budget and base model
geometry are the already-constructed configured data, while every fact about
the selected physical terminal comes only from `R`. -/
def Certificate.toPhysicalProducer_of_rowBudget
    {F : ConstructionCore Q e P0 P1 khat G1 Cg C c dlt period diagonal
      (fun {current} {k} ↦ GaugeCertificate) a MA NA K0 K1 K2}
    {baseConversion endpointConversion diagonal' : ℕ → ℝ}
    {stageCost : ℕ → ℕ → ℝ}
    (R : Certificate F baseConversion endpointConversion diagonal' stageCost)
    {c0 d0 A0 r rho upper : ℕ → ℝ}
    (B : RowBudget Q P0 P1 khat G1 Cg c0 d0 A0 r rho upper c dlt)
    (hradius : ∀ n, r n =
      ExponentialDiagonalLargeSeparation.rowRadius
        (ConfiguredGaugeEndpointLinearRadius.combinedConversion
          baseConversion endpointConversion) diagonal' n)
    (hbaseModel : ∀ n, IsTubeMember (c0 n) 0 (d0 n) (Q n))
    (hbaseCommon : ∀ n, IsTubeMember c 0 dlt (Q n))
    (hbasePerim : ∀ n, c0 n ≤ perim (Q n))
    (hbaseAcc : ∀ n u, ‖(Q n).2.2 u‖ ≤ A0 n)
    {kh : ℝ}
    (finite : FinitePullbackPhysicalRearKinematics kh
      (EnrichedPhysicalHarnackClosure.retainedRows
        F.baseProvider F.mapProvider)) :
    PhysicalProducer F kh c dlt :=
  R.toPhysicalProducer
    (R.physicalBounds B hradius hbaseModel hbaseCommon hbasePerim hbaseAcc)
    finite

end EnrichedPhysicalQuantitativeCap
