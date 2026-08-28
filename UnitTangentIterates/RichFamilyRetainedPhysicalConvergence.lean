import UnitTangentIterates.RichFamilyRetainedPhysicalRows

/-!
# Convergence of retained physical rows from a vanishing marking defect

The depth-`k+1` retained physical datum is the terminal base stored by the
depth-`k` rich stage.  If these bases have marked distance tending to zero
from the corresponding variable terminal data, they have the same row limit.
-/

noncomputable section

open Filter Topology MarkedSpace

namespace RichFamilyRetainedPhysicalConvergence

open RichFamilyRetainedPhysicalRows
  TriangularMarkedRecursiveChoiceVariableTerminalConstructor

/-- A vanishing physical-base/terminal marking defect transfers convergence
of the variable terminal row to the retained physical row. -/
theorem tendsto_rows_of_terminalBase_dist
    {Q : ℕ → Data} {e : ℕ → ℕ → ℝ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
    (F : RichFamily Q e P0 P1 khat G1 Cg C c dlt)
    {X : ℕ → Data}
    (hterminal : ∀ n,
      Tendsto (fun k => F.P n (k + 1)) atTop (nhds (X n)))
    (hdefect : ∀ n,
      Tendsto
        (fun k => dist (F.richStage n k).terminalBase (F.P n (k + 1)))
        atTop (nhds 0)) :
    ∀ n, Tendsto (rows F n) atTop (nhds (X n)) := by
  intro n
  apply Metric.tendsto_atTop.2
  intro eps heps
  have heps2 : 0 < eps / 2 := by linarith
  obtain ⟨NP, hP⟩ := Metric.tendsto_atTop.1 (hterminal n) (eps / 2) heps2
  obtain ⟨ND, hD⟩ := Metric.tendsto_atTop.1 (hdefect n) (eps / 2) heps2
  refine ⟨max NP ND + 1, fun m hm => ?_⟩
  have hm0 : m ≠ 0 := by omega
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm0
  have hk : max NP ND ≤ k := by omega
  have hkP : NP ≤ k := le_trans (le_max_left _ _) hk
  have hkD : ND ≤ k := le_trans (le_max_right _ _) hk
  have hclose := hD k hkD
  rw [Real.dist_eq, sub_zero, abs_of_nonneg dist_nonneg] at hclose
  rw [rows_succ]
  calc
    dist (F.richStage n k).terminalBase (X n) ≤
        dist (F.richStage n k).terminalBase (F.P n (k + 1)) +
          dist (F.P n (k + 1)) (X n) := dist_triangle _ _ _
    _ < eps / 2 + eps / 2 := add_lt_add hclose (hP k hkP)
    _ = eps := by ring

end RichFamilyRetainedPhysicalConvergence
