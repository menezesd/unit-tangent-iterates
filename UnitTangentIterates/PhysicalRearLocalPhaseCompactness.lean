import UnitTangentIterates.PhysicalRearTrackLimitClosure
import UnitTangentIterates.MarkedShift

/-!
# Fixed-row compactness of terminal front phases
-/

noncomputable section

open Filter Topology MarkedSpace Set

namespace PhysicalRearLocalPhaseCompactness

/-- A normalized form of the exact terminal-front sidecar retained by the
configured direct tower. -/
structure NormalizedPhaseSidecar
    (baseFront physicalFront : ℕ → Data) where
  phase : ℕ → Set.Icc (0 : ℝ) 1
  front_eq : ∀ k,
    physicalFront k = MarkedShift.shiftData (phase k : ℝ) (baseFront k)

/-- Every fixed row has a subsequence on which its normalized terminal phase
converges.  No coherence with other rows is required by the smoothness
bootstrap. -/
theorem exists_phase_subseq
    {baseFront physicalFront : ℕ → Data}
    (S : NormalizedPhaseSidecar baseFront physicalFront) :
    ∃ q : Set.Icc (0 : ℝ) 1, ∃ phi : ℕ → ℕ,
      StrictMono phi ∧ Tendsto (fun k => S.phase (phi k)) atTop (nhds q) := by
  have hmem : ∀ k, S.phase k ∈
      (Set.univ : Set (Set.Icc (0 : ℝ) 1)) :=
    fun k => Set.mem_univ _
  obtain ⟨q, -, phi, hphi, hq⟩ :=
    (isCompact_univ : IsCompact
      (Set.univ : Set (Set.Icc (0 : ℝ) 1))).tendsto_subseq hmem
  exact ⟨q, phi, hphi, by simpa [Function.comp_def] using hq⟩

/-- After phase extraction, the exact sidecar continues to identify every
physical front with the corresponding shifted displayed front. -/
theorem front_eq_along_phase_subseq
    {baseFront physicalFront : ℕ → Data}
    (S : NormalizedPhaseSidecar baseFront physicalFront) (phi : ℕ → ℕ) :
    ∀ k, physicalFront (phi k) =
      MarkedShift.shiftData (S.phase (phi k) : ℝ) (baseFront (phi k)) :=
  fun k => S.front_eq (phi k)

end PhysicalRearLocalPhaseCompactness
