import UnitTangentIterates.ConfiguredRecursiveEdgeSourceP0
import UnitTangentIterates.ConfiguredCombinedPhysicalDiagonalLargeSeparation

/-!
# Recursive edge cap for the configured physical row upper bound

The physical row budget is bounded by the shifted linear speed cap at its
current row.  Monotonicity of the configured separation upgrades this to the
successor-row cap used by recursive edge sources.
-/

noncomputable section

namespace ConfiguredRecursiveEdgeOutputUpperSpeedCap

open ConstructedConfiguredInductiveTubeBudget.WeightedData

/-- The configured physical row upper bound fits the recursive source's
successor-edge speed cap after the large-separation shift. -/
theorem outputUpper_le_edgeSpeedCap
    (D : ConstructedConfiguredSequenceWeighted.Data)
    {Cdiag diagonal : ℕ → ℝ} {Cw : ℝ}
    (L : ExponentialDiagonalLargeSeparation.Output D Cdiag diagonal Cw)
    (n : ℕ) :
    ConfiguredPhysicalDiagonalRowBudget.outputUpper D L n ≤
      ConfiguredRecursiveEdgeSourceP0.edgeSpeedCap (shift D L.N) n := by
  apply (ConfiguredCombinedPhysicalDiagonalLargeSeparation.outputUpper_le_cap
    D L n).trans
  have hstep := (shift D L.N).separation_step n
  have hdelta := (shift D L.N).deltaStep_pos
  unfold ConfiguredRecursiveEdgeSourceP0.edgeSpeedCap
    ConfiguredCombinedPhysicalDiagonalLargeSeparation.speedCap
  linarith

end ConfiguredRecursiveEdgeOutputUpperSpeedCap
