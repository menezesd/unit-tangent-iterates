import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareCompositionGeometricPresentedRecursion
import UnitTangentIterates.ConfiguredRecursiveEdgePresentedCapstoneRetainedStrictness
import UnitTangentIterates.VariableSpeedNormalPathPhaseTransport
import UnitTangentIterates.ConfiguredCompatiblePhysicalRearSequence

/-!
# Phase-coherent transition-free presented rows

Successive source initials and presented terminal rears agree only up to a
cyclic change of marking.  The cumulative phase below cancels those changes
and produces an exact marked chain without strengthening range equality to
marked-data equality.
-/

noncomputable section

open Function Set Filter MarkedSpace PathMetric

namespace ConfiguredRecursiveEdgeGeometricPresentedCapstone

open FiniteSmoothRearFamilyMarkingAwareChosenTerminal
  FiniteSmoothRearFamilyMarkingAwareCompositionGeometricPresentedRecursion
  RichFamilyPhysicalMarkingIntegration

variable {Q : ℕ → Data} {e : ℕ → ℕ → ℝ}
  {P0 P1 khat G1 Cg C kh Qmax : ℕ → ℝ} {c dlt : ℝ}

abbrev Core (Q : ℕ → Data) (e : ℕ → ℕ → ℝ)
    (P0 P1 khat G1 Cg C kh Qmax : ℕ → ℝ) (c dlt : ℝ) :=
  GeometricPresentedConstructionCore Q e P0 P1 khat G1 Cg C kh Qmax c dlt

@[simp] theorem state_depth
    (F : Core Q e P0 P1 khat G1 Cg C kh Qmax c dlt) :
    ∀ k, (F.state k).depth = k
  | 0 => rfl
  | k + 1 => by
      simp [GeometricPresentedConstructionCore.state,
        GeometricPresentedState.next, state_depth F k]

/-- A common cyclic change of marking preserves the ambient marked metric. -/
theorem dist_shiftData (b : ℝ) (p q : Data) :
    dist (MarkedShift.shiftData b p) (MarkedShift.shiftData b q) = dist p q := by
  simp only [Prod.dist_eq]
  congr 1
  · rw [BoundedContinuousFunction.dist_eq_iSup,
      BoundedContinuousFunction.dist_eq_iSup]
    exact (Equiv.addRight b).surjective.iSup_comp
      (fun u => dist (p.1 u) (q.1 u))
  · congr 1
    · rw [BoundedContinuousFunction.dist_eq_iSup,
        BoundedContinuousFunction.dist_eq_iSup]
      exact (Equiv.addRight b).surjective.iSup_comp
        (fun u => dist (p.2.1 u) (q.2.1 u))
    · rw [BoundedContinuousFunction.dist_eq_iSup,
        BoundedContinuousFunction.dist_eq_iSup]
      exact (Equiv.addRight b).surjective.iSup_comp
        (fun u => dist (p.2.2 u) (q.2.2 u))

/-- A variable-speed tube is invariant under a cyclic change of marking. -/
def isVariableTubeMember_shiftData
    {c C kmin delta : ℝ} {p : Data}
    (hp : VariableMarkedTube.IsVariableTubeMember c C kmin delta p) (b : ℝ) :
    VariableMarkedTube.IsVariableTubeMember c C kmin delta
      (MarkedShift.shiftData b p) := by
  have hinner : ∀ u : ℝ, HasDerivAt (fun y : ℝ => y + b) 1 u := fun u => by
    simpa using (hasDerivAt_id u).add_const b
  have hfract : ∀ y : ℝ, p.1 (Int.fract y) = p.1 y := by
    intro y
    show p.1 (y - ⌊y⌋) = p.1 y
    simpa using hp.periodic.sub_int_mul_eq (x := y) ⌊y⌋
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro u
    simpa using (hp.hasDerivAt_curve (u + b)).scomp u (hinner u)
  · intro u
    simpa using (hp.hasDerivAt_vel (u + b)).scomp u (hinner u)
  · intro u
    simpa [add_right_comm] using hp.periodic (u + b)
  · intro u
    simpa using hp.speed_lb (u + b)
  · intro u
    simpa using hp.speed_ub (u + b)
  · intro u
    simpa using hp.curv_lb (u + b)
  · intro u hu v hv
    have hmem : ∀ y : ℝ, Int.fract y ∈ Set.Icc (0 : ℝ) 1 :=
      fun y => ⟨Int.fract_nonneg y, le_of_lt (Int.fract_lt_one y)⟩
    have hchord := hp.chord _ (hmem (u + b)) _ (hmem (v + b))
    have hcyc : cyc u v = cyc (Int.fract (u + b)) (Int.fract (v + b)) := by
      refine MarkedShift.cyc_eq_of_int_sub hu hv (hmem _) (hmem _)
        (n := ⌊u + b⌋ - ⌊v + b⌋) ?_
      simp only [Int.fract]
      push_cast
      ring
    rw [hcyc]
    simpa [hfract] using hchord

/-- Shifting a datum does not alter the range of its curve. -/
theorem range_shiftData (b : ℝ) (p : Data) :
    range (MarkedShift.shiftData b p).1 = range p.1 := by
  apply Set.Subset.antisymm
  · rintro z ⟨u, rfl⟩
    exact ⟨u + b, rfl⟩
  · rintro z ⟨u, rfl⟩
    refine ⟨u - b, ?_⟩
    simp only [MarkedShift.shiftData_curve]
    congr 1
    ring

/-- Shifting a datum does not alter the range of its normalized tangent. -/
theorem range_geometricUnitTangent_shiftData (b : ℝ) (p : Data) :
    range (VariableMarkedTube.geometricUnitTangent (MarkedShift.shiftData b p)) =
      range (VariableMarkedTube.geometricUnitTangent p) := by
  apply Set.Subset.antisymm
  · rintro z ⟨u, rfl⟩
    exact ⟨u + b, rfl⟩
  · rintro z ⟨u, rfl⟩
    refine ⟨u - b, ?_⟩
    simp [VariableMarkedTube.geometricUnitTangent]

/-- The cumulative correction which cancels every successor phase. -/
def coherentPhase
    (F : Core Q e P0 P1 khat G1 Cg C kh Qmax c dlt) (n : ℕ) : ℕ → ℝ
  | 0 => 0
  | k + 1 => coherentPhase F n k - (F.rowFamilyAt k).mappedInitial_phase n

/-- The recursive grid with all cyclic marking changes accumulated away. -/
def coherentGrid
    (F : Core Q e P0 P1 khat G1 Cg C kh Qmax c dlt) (n k : ℕ) : Data :=
  MarkedShift.shiftData (coherentPhase F n k) (F.markedGrid n k)

@[simp] theorem coherentGrid_zero
    (F : Core Q e P0 P1 khat G1 Cg C kh Qmax c dlt) (n : ℕ) :
    coherentGrid F n 0 = F.markedGrid n 0 := by
  simp [coherentGrid, coherentPhase]

/-- At positive depth the coherent grid is the preceding presented terminal
rear shifted by the preceding cumulative phase. -/
theorem coherentGrid_succ_eq_shift_presented
    (F : Core Q e P0 P1 khat G1 Cg C kh Qmax c dlt) (n k : ℕ) :
    coherentGrid F n (k + 1) =
      MarkedShift.shiftData (coherentPhase F n k)
        ((F.rowFamilyAt k).row n).presented := by
  rw [coherentGrid, F.markedGrid_succ_eq_phase n k,
    MarkedShift.shiftData_add]
  congr 1
  simp [coherentPhase]

/-- The shifted exact selected endpoint at each positive depth. -/
def selectedGrid
    (F : Core Q e P0 P1 khat G1 Cg C kh Qmax c dlt)
    (n : ℕ) : ℕ → Data
  | 0 => coherentGrid F n 0
  | k + 1 => MarkedShift.shiftData (coherentPhase F n k)
      ((F.rowFamilyAt k).row n).output.jets.rear

/-- Every row path shifts by the cumulative phase and therefore starts at the
coherent grid and ends at its shifted selected endpoint. -/
def rowPath
    (F : Core Q e P0 P1 khat G1 Cg C kh Qmax c dlt) (n k : ℕ) :
    NormalPath (coherentGrid F n k) (selectedGrid F n (k + 1)) :=
  MarkedShift.shiftPath (coherentPhase F n k)
    ((F.rowFamilyAt k).row n).output.chosen.Delta

theorem rowPath_cost_le
    (F : Core Q e P0 P1 khat G1 Cg C kh Qmax c dlt) (n k : ℕ) :
    (rowPath F n k).cost ≤ e n (k + 1) := by
  let R := (F.rowFamilyAt k).row n
  change R.output.chosen.Delta.cost ≤ e n (k + 1)
  rw [← R.output.stage_eq]
  simpa using R.output.stage.increment_cost

def rowPath_geometry
    (F : Core Q e P0 P1 khat G1 Cg C kh Qmax c dlt) (n k : ℕ) :
    NormalPathC2IncrementVariableSpeed.IsVariableSpeedNormalPath
      (P0 (n + k)) (P1 n) (khat n) (G1 n) (Cg n) (rowPath F n k) := by
  simpa [state_depth F k] using
    NormalPathC2IncrementVariableSpeed.isVariableSpeedNormalPath_shift
      ((F.rowFamilyAt k).row n).output.chosen.Delta
      ((F.rowFamilyAt k).row n).increment_geometry

/-- The coherent grid has the same parameter-invariant finite orbit as the
raw source grid. -/
theorem coherentGrid_edge
    (F : Core Q e P0 P1 khat G1 Cg C kh Qmax c dlt) (n k : ℕ) :
    VariableMarkedTube.GeometricUnitTangentRangeEdge
      (coherentGrid F (n + 1) k) (coherentGrid F n (k + 1)) := by
  unfold VariableMarkedTube.GeometricUnitTangentRangeEdge coherentGrid
  rw [range_shiftData, range_geometricUnitTangent_shiftData]
  exact F.markedGrid_edge n k

/-- Positive-depth coherent rows inherit terminal strictness through their
cyclic marking change. -/
def gridFiniteStrictness
    (F : Core Q e P0 P1 khat G1 Cg C kh Qmax c dlt) (n k : ℕ) :
    UnconditionalAssembly.LimitStrictnessDataH (coherentGrid F n (k + 1)) := by
  rw [coherentGrid_succ_eq_shift_presented]
  let R := (F.rowFamilyAt k).row n
  exact ConfiguredCompatiblePhysicalRearSequence.shiftLimitStrictnessDataH
    R.terminalInput.physical.cq_pos R.terminalInput.zero_floor_tube
    R.terminalInput.strict (coherentPhase F n k)

end ConfiguredRecursiveEdgeGeometricPresentedCapstone
