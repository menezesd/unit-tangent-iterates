import UnitTangentIterates.ConstantToVariableSpeed
import UnitTangentIterates.ApproximateDefect

/-!
# The variable-speed path distance
-/

noncomputable section

set_option maxHeartbeats 1000000

open Set Function MeasureTheory MarkedSpace PathMetric PathMetric.NormalPath
open NormalPathC2Increment NormalPathC2IncrementVariableSpeed

namespace PathMetric

/-- **The cost set of the variable-speed subclass.**

§96 found that the Jacobi rear map produces an `IsVariableSpeedNormalPath`, not a
constant-speed one.  The same is true on the defect side: the interpolation path
of `InterpolationPathDist.exists_normalPath_interp_with_gauge` has slices
`interpCurve … (Phi t u)` reparametrized by the gauge flow `Phi`, whose
`u`-derivative is not constant.  So both producers land in the variable-speed
class, and the distance the closing chain should be stated with is the infimum
over *that* class. -/
def costSetVS (P0 P1 khat G1 Cg : ℝ) (p q : Data) : Set ℝ :=
  {c | ∃ Γ : NormalPath p q, IsVariableSpeedNormalPath P0 P1 khat G1 Cg Γ ∧ cost Γ = c}

theorem bddBelow_costSetVS (P0 P1 khat G1 Cg : ℝ) (p q : Data) :
    BddBelow (costSetVS P0 P1 khat G1 Cg p q) := by
  refine ⟨0, ?_⟩; rintro c ⟨Γ, -, rfl⟩; exact Γ.cost_nonneg

/-- **The variable-speed path distance.** -/
def pathDistVS (P0 P1 khat G1 Cg : ℝ) (p q : Data) : ℝ :=
  sInf (costSetVS P0 P1 khat G1 Cg p q)

/-- A variable-speed path bounds the variable-speed distance by its cost.  This
is the entry point: exhibit one path, bound its cost. -/
theorem pathDistVS_le_cost {P0 P1 khat G1 Cg : ℝ} {p q : Data} (Γ : NormalPath p q)
    (h : IsVariableSpeedNormalPath P0 P1 khat G1 Cg Γ) :
    pathDistVS P0 P1 khat G1 Cg p q ≤ cost Γ :=
  csInf_le (bddBelow_costSetVS P0 P1 khat G1 Cg p q) ⟨Γ, h, rfl⟩

/-- **Near-minimizers stay in the variable-speed subclass**, exactly as in the
constant-speed case: the infimum is taken over the subclass to begin with. -/
theorem exists_variableSpeed_near_minimizer {P0 P1 khat G1 Cg : ℝ} {p q : Data}
    (hne : ∃ Γ : NormalPath p q, IsVariableSpeedNormalPath P0 P1 khat G1 Cg Γ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ Γ : NormalPath p q, IsVariableSpeedNormalPath P0 P1 khat G1 Cg Γ ∧
      cost Γ ≤ pathDistVS P0 P1 khat G1 Cg p q + ε := by
  obtain ⟨Γ₀, hΓ₀⟩ := hne
  have hnonempty : (costSetVS P0 P1 khat G1 Cg p q).Nonempty := ⟨cost Γ₀, Γ₀, hΓ₀, rfl⟩
  obtain ⟨c, hc, hclt⟩ := Real.lt_sInf_add_pos hnonempty hε
  obtain ⟨Γ, hΓ, rfl⟩ := hc
  exact ⟨Γ, hΓ, le_of_lt hclt⟩

/-- **The variable-speed distance is at most the constant-speed one**, when the
ceilings are nonnegative — because every constant-speed path is a variable-speed
path with vanishing `u`-derivatives (§96), so the constant-speed cost set is
contained in the variable-speed one. -/
theorem pathDistVS_le_pathDistCS {P0 P1 khat G1 Cg : ℝ} {p q : Data}
    (hk : 0 ≤ khat) (hG1 : 0 ≤ G1) (hCg : 0 ≤ Cg)
    (hne : (costSetCS P0 P1 khat p q).Nonempty) :
    pathDistVS P0 P1 khat G1 Cg p q ≤ pathDistCS P0 P1 khat p q := by
  refine csInf_le_csInf (bddBelow_costSetVS P0 P1 khat G1 Cg p q) hne ?_
  rintro c ⟨Γ, hΓ, rfl⟩
  exact ⟨Γ, isVariableSpeed_of_constantSpeed_mono Γ hΓ hk hG1 hCg, rfl⟩

end PathMetric
