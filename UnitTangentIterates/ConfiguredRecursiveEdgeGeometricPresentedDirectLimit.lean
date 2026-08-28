import UnitTangentIterates.ConfiguredRecursiveEdgeGeometricPresentedCapstone

noncomputable section

open Function Set Filter Topology MarkedSpace PathMetric
open NormalPathC2IncrementVariableSpeed VariableMarkedTube
open RichFamilyPhysicalMarkingIntegration
open GaugeRearFamilyVariableTerminal

namespace ConfiguredRecursiveEdgeGeometricPresentedDirectLimit

open ConfiguredRecursiveEdgeGeometricPresentedCapstone
  FiniteSmoothRearFamilyMarkingAwareCompositionGeometricPresentedRecursion

variable {Q : ℕ → Data} {e : ℕ → ℕ → ℝ}
  {P0 P1 khat G1 Cg C kh Qmax : ℕ → ℝ} {c dlt : ℝ}

def dummyP0 : ℕ → ℝ := fun _ => 1
def dummyZero : ℕ → ℝ := fun _ => 0

@[simp] theorem dummy_rowC (n : ℕ) :
    TriangularMarkedPathSchemeVariableTerminal.rowC dummyP0 dummyZero
      dummyZero dummyZero dummyZero n = 1 := by
  norm_num [TriangularMarkedPathSchemeVariableTerminal.rowC, dummyP0,
    dummyZero, c2ConstVar, NormalPathC2Increment.velConst,
    accConstVar]

/-- The effective marked increment when the source floor and endpoint
coefficient are read at the diagonal index `n+k`. -/
def effectiveError (endpoint diagonal : ℕ → ℝ) (n k : ℕ) : ℝ :=
  (c2ConstVar (P0 (n + k)) (P1 n) (khat n) (G1 n) (Cg n) +
      endpoint n) * diagonal (n + k + 1)

/-- The shifted row path and endpoint cap give the concrete dynamic effective
increment used by the configured diagonal specialization. -/
theorem step_dist_le_effectiveError
    (F : Core Q e P0 P1 khat G1 Cg C kh Qmax c dlt)
    (endpoint diagonal : ℕ → ℝ)
    (herror : ∀ n k, e n (k + 1) = diagonal (n + k + 1))
    (tube : ∀ n k, IsVariableTubeMember c (C n) 0 dlt (coherentGrid F n k))
    {M : ℝ} (hM : 0 ≤ M)
    (caps : ∀ n k,
      GeometricPresentedRowCap ((F.rowFamilyAt k).row n) M
        (endpoint n) (diagonal (n + k + 1))) (n k : ℕ) :
    dist (coherentGrid F n k) (coherentGrid F n (k + 1)) ≤
      effectiveError (P0 := P0) (P1 := P1) (khat := khat) (G1 := G1)
        (Cg := Cg) endpoint diagonal n k := by
  let R := (F.rowFamilyAt k).row n
  have hpath : dist (coherentGrid F n k) (selectedGrid F n (k + 1)) ≤
      c2ConstVar (P0 (n + k)) (P1 n) (khat n) (G1 n) (Cg n) *
        (rowPath F n k).cost :=
    dist_le_cost_variableSpeed (rowPath F n k)
      (tube n k).hasDerivAt_curve
      (fun u => by
        have hi : HasDerivAt
            (fun y : ℝ => y + coherentPhase F n k) 1 u := by
          simpa using (hasDerivAt_id u).add_const (coherentPhase F n k)
        simpa [selectedGrid] using
          (R.output.stage.rear_curve_deriv
            (u + coherentPhase F n k)).scomp u hi)
      (tube n k).hasDerivAt_vel
      (fun u => by
        have hi : HasDerivAt
            (fun y : ℝ => y + coherentPhase F n k) 1 u := by
          simpa using (hasDerivAt_id u).add_const (coherentPhase F n k)
        simpa [selectedGrid] using
          (R.output.stage.rear_vel_deriv
            (u + coherentPhase F n k)).scomp u hi)
      (rowPath_geometry F n k)
  have hselected : dist (selectedGrid F n (k + 1))
      (coherentGrid F n (k + 1)) ≤
        endpoint n * diagonal (n + k + 1) := by
    rw [coherentGrid_succ_eq_shift_presented]
    change dist
      (MarkedShift.shiftData (coherentPhase F n k) R.output.jets.rear)
      (MarkedShift.shiftData (coherentPhase F n k) R.presented) ≤ _
    rw [dist_shiftData]
    simpa [R] using GeometricPresentedRowCap.endpoint_dist_le hM (caps n k)
  calc
    dist (coherentGrid F n k) (coherentGrid F n (k + 1)) ≤
        dist (coherentGrid F n k) (selectedGrid F n (k + 1)) +
          dist (selectedGrid F n (k + 1)) (coherentGrid F n (k + 1)) :=
      dist_triangle _ _ _
    _ ≤ c2ConstVar (P0 (n + k)) (P1 n) (khat n) (G1 n) (Cg n) *
          diagonal (n + k + 1) +
            endpoint n * diagonal (n + k + 1) :=
      add_le_add (hpath.trans (mul_le_mul_of_nonneg_left
        ((rowPath_cost_le F n k).trans_eq (herror n k))
        (c2ConstVar_nonneg _ _ _ _ _))) hselected
    _ = effectiveError (P0 := P0) (P1 := P1) (khat := khat) (G1 := G1)
        (Cg := Cg) endpoint diagonal n k := by
      simp [effectiveError]
      ring

/-- Direct metric compactness for the range-linked recursion.  The dummy
analytic parameters record that the supplied effective metric increment is
the summable error.  This form permits genuinely depth-dependent analytic
conversion factors. -/
theorem exists_limitOutput
    (F : Core Q e P0 P1 khat G1 Cg C kh Qmax c dlt)
    (w : ℕ → ℕ → ℝ)
    (error_nonnegative : ∀ n k, 0 ≤ w n k)
    (error_summable : ∀ n, Summable (w n))
    (tube : ∀ n k, IsVariableTubeMember c (C n) 0 dlt (coherentGrid F n k))
    (step_dist : ∀ n k,
      dist (coherentGrid F n k) (coherentGrid F n (k + 1)) ≤ w n k)
    {cb db : ℝ}
    (physical : PhysicalRowBounds (coherentGrid F) (coherentGrid F) cb db)
    (hcb : 0 < cb) (hdb : 0 < db)
    (hc : 0 < c) :
    Nonempty (TriangularMarkedPathSchemeVariableTerminal.LimitOutput
      (fun n => coherentGrid F n 0) (coherentGrid F)
      w
      dummyP0 dummyZero dummyZero dummyZero dummyZero C c dlt) := by
  have hrowCauchy : ∀ n, CauchySeq (coherentGrid F n) := by
    intro n
    exact cauchySeq_of_summable_dist
      (Summable.of_nonneg_of_le (fun _ => dist_nonneg) (step_dist n)
        (error_summable n))
  have hlim : ∀ n, ∃ x : Data,
      Tendsto (coherentGrid F n) atTop (nhds x) ∧
      ∀ k, dist (coherentGrid F n k) x ≤
        (1 : ℝ) * ShadowingTails.tail (w n) k := by
    intro n
    exact ShadowingTails.exists_limit_of_summable_increments
      (C := (1 : ℝ)) (error_summable n)
        (fun k => by simpa using step_dist n k)
  choose X hXlim hXdist using hlim
  have hXmem : ∀ n, IsVariableTubeMember c (C n) 0 dlt (X n) := fun n =>
    (isClosed_variableTube c (C n) 0 dlt).mem_of_tendsto (hXlim n)
      (Eventually.of_forall (tube n))
  have hshadow : ∀ n,
      dist (coherentGrid F n 0) (X n) ≤ ShadowingTails.tail (w n) 0 :=
    fun n => by simpa using hXdist n 0
  have hhaus : ∀ n, Metric.hausdorffDist (range (X n).1)
      (range (coherentGrid F n 0).1) ≤ ShadowingTails.tail (w n) 0 := by
    intro n
    apply CurveDistance.hausdorffDist_range_le
      (ShadowingTails.tail_nonneg (error_nonnegative n) 0)
    intro u
    exact (dist_apply_le (X n) (coherentGrid F n 0) u).trans
      (by simpa [dist_comm] using hshadow n)
  have hlength : ∀ n,
      |MarkedReparam.totalLength (fun u => (X n).2.1 u) -
        MarkedReparam.totalLength (fun u => (coherentGrid F n 0).2.1 u)| ≤
          ShadowingTails.tail (w n) 0 := fun n =>
    (VariableMarkedPhysicalLength.abs_totalLength_sub_le_dist
      (X n) (coherentGrid F n 0)).trans (by simpa [dist_comm] using hshadow n)
  have horbit : ∀ n, GeometricUnitTangentRangeEdge (X (n + 1)) (X n) := by
    intro n
    let Cedge := max (C n) (C (n + 1))
    exact range_geometricUnitTangent_closed_under_marked_limits hc
      (fun k => TriangularMarkedPathSchemeVariableTerminal.variableTube_mono_upper
        (tube (n + 1) k) (le_max_right _ _))
      (fun k => TriangularMarkedPathSchemeVariableTerminal.variableTube_mono_upper
        (tube n (k + 1)) (le_max_left _ _))
      (TriangularMarkedPathSchemeVariableTerminal.variableTube_mono_upper
        (hXmem (n + 1)) (le_max_right _ _))
      (TriangularMarkedPathSchemeVariableTerminal.variableTube_mono_upper
        (hXmem n) (le_max_left _ _))
      (hXlim (n + 1)) ((hXlim n).comp (tendsto_add_atTop_nat 1))
      (coherentGrid_edge F n)
  have hoval : ∀ n, IsGeometricOval (X n) := by
    intro n
    have hstrict :=
      GenericVariableTerminalDirectCapstoneRetainedStrictness.limitStrictnessDataH_of_rearStrictRowLimit
        hcb physical.physical_tube (gridFiniteStrictness F) (hXlim n)
    exact isGeometricOval_of_arclengthHarnack
      { q := X n
        c := cb
        dlt := db
        c_pos := hcb
        dlt_pos := hdb
        tube := (isClosed_tube cb 0 db).mem_of_tendsto (hXlim n)
          (Eventually.of_forall (physical.physical_tube n))
        same_range := rfl
        strictness := hstrict }
  exact ⟨
    { X := X
      row_cauchy := hrowCauchy
      row_limit := hXlim
      limit_tube := hXmem
      shadow_dist := by
        intro n
        simpa [coherentGrid_zero,
          GeometricPresentedConstructionCore.markedGrid_zero] using hshadow n
      shadow_totalLength := by simpa using hlength
      shadow_range := by simpa using hhaus
      range_orbit := horbit
      geometric_oval := hoval }⟩

/-- Identity physical markings on the arclength-marked grid. -/
def gridPhysicalMarkings
    (F : Core Q e P0 P1 khat G1 Cg C kh Qmax c dlt) :
    DirectPhysicalTerminalMarkingFamily (coherentGrid F) (coherentGrid F) where
  lambda := fun _ _ => 1
  Lambda := fun _ _ => 1
  marking := fun n k =>
    NormalizedTerminalMarkingComposition.NormalizedC2Marking.refl
      (coherentGrid F n k)

/-- Retained strictness and the identity physical marking orient every direct
metric limit, enabling the existing paper-facing closing theorem. -/
def paperFacingOutput_of_limitOutput
    (F : Core Q e P0 P1 khat G1 Cg C kh Qmax c dlt)
    {w : ℕ → ℕ → ℝ}
    (tube : ∀ n k, IsVariableTubeMember c (C n) 0 dlt (coherentGrid F n k))
    {cb db : ℝ}
    (physical : PhysicalRowBounds (coherentGrid F) (coherentGrid F) cb db)
    (hcb : 0 < cb) (hdb : 0 < db)
    (O : TriangularMarkedPathSchemeVariableTerminal.LimitOutput
      (fun n => coherentGrid F n 0) (coherentGrid F)
      w
      dummyP0 dummyZero dummyZero dummyZero dummyZero C c dlt)
    (hc : 0 < c) {direction : ℂ} (hdirection : ‖direction‖ = 1)
    {modelWidth H : ℝ}
    (hQbounded : Bornology.IsBounded (range ⇑(coherentGrid F 0 0).1))
    (hQwidth : Width.width (range ⇑(coherentGrid F 0 0).1) direction ≤ modelWidth)
    (hQlength : 2 * H ≤
      MarkedReparam.totalLength fun u => (coherentGrid F 0 0).2.1 u)
    (hgap : modelWidth + 2 * PaperFacingVariableTerminalOutput.shadowSize O <
      (2 * H - PaperFacingVariableTerminalOutput.shadowSize O) / Real.pi) :
    PaperFacingVariableTerminalOutput.Output O direction modelWidth H := by
  let M := gridPhysicalMarkings F
  let rowGeometry := geometricRowMarkingDataDirect M physical hc tube
  let markingBounds := rowGeometry.toRowwiseBounds
  let reps : ∀ n, OrientedArclengthRepresentative (O.X n) := by
    intro n
    let W := limitOrientedReparametrization_of_rowwise_bounds
      (markingBounds.lambda_pos n) (markingBounds.secondBound_nonneg n)
      (markingBounds.reparametrization n) (O.row_limit n) (O.row_limit n)
      (markingBounds.basepoint n) (markingBounds.psi_hasDerivAt n)
      (markingBounds.ddpsi n) (markingBounds.dpsi_hasDerivAt n)
      (markingBounds.ddpsi_bound n)
    have hbase : IsTubeMember cb 0 db (O.X n) :=
      (isClosed_tube cb 0 db).mem_of_tendsto (O.row_limit n)
        (Eventually.of_forall (physical.physical_tube n))
    exact orientedArclengthRepresentative_of_orientedReparametrization
      hcb hdb W.lambda_pos hbase W.reparametrization W.psi_hasDerivAt
      W.dpsi_continuous W.surjective
      (GenericVariableTerminalDirectCapstoneRetainedStrictness.limitStrictnessDataH_of_rearStrictRowLimit
        hcb physical.physical_tube (gridFiniteStrictness F) (O.row_limit n))
  exact PaperFacingVariableTerminalOutput.output_of_orientedRepresentatives
    O reps hdirection hQbounded hQwidth hQlength hgap

/-- Complete paper-facing output from the transition-free direct metric
construction. -/
theorem exists_paperFacingOutput
    (F : Core Q e P0 P1 khat G1 Cg C kh Qmax c dlt)
    (w : ℕ → ℕ → ℝ)
    (error_nonnegative : ∀ n k, 0 ≤ w n k)
    (error_summable : ∀ n, Summable (w n))
    (tube : ∀ n k, IsVariableTubeMember c (C n) 0 dlt (coherentGrid F n k))
    (step_dist : ∀ n k,
      dist (coherentGrid F n k) (coherentGrid F n (k + 1)) ≤ w n k)
    {cb db : ℝ}
    (physical : PhysicalRowBounds (coherentGrid F) (coherentGrid F) cb db)
    (hcb : 0 < cb) (hdb : 0 < db)
    (hc : 0 < c) {direction : ℂ} (hdirection : ‖direction‖ = 1)
    {modelWidth H : ℝ}
    (hQbounded : Bornology.IsBounded (range ⇑(coherentGrid F 0 0).1))
    (hQwidth : Width.width (range ⇑(coherentGrid F 0 0).1) direction ≤ modelWidth)
    (hQlength : 2 * H ≤
      MarkedReparam.totalLength fun u => (coherentGrid F 0 0).2.1 u)
    (hgap : ∀ O : TriangularMarkedPathSchemeVariableTerminal.LimitOutput
      (fun n => coherentGrid F n 0) (coherentGrid F)
      w
      dummyP0 dummyZero dummyZero dummyZero dummyZero C c dlt,
      modelWidth + 2 * PaperFacingVariableTerminalOutput.shadowSize O <
        (2 * H - PaperFacingVariableTerminalOutput.shadowSize O) / Real.pi) :
    Nonempty ((O : TriangularMarkedPathSchemeVariableTerminal.LimitOutput
      (fun n => coherentGrid F n 0) (coherentGrid F)
      w
      dummyP0 dummyZero dummyZero dummyZero dummyZero C c dlt) ×
      PaperFacingVariableTerminalOutput.Output O direction modelWidth H) := by
  obtain ⟨O⟩ := exists_limitOutput F w error_nonnegative error_summable
    tube step_dist physical hcb hdb hc
  exact ⟨O, paperFacingOutput_of_limitOutput F tube physical hcb hdb
    O hc hdirection hQbounded hQwidth hQlength (hgap O)⟩

end ConfiguredRecursiveEdgeGeometricPresentedDirectLimit
