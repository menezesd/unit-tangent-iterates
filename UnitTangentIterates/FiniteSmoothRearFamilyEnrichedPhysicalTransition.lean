import UnitTangentIterates.FiniteSmoothRearFamilyEnrichedMapProvider
import UnitTangentIterates.EnrichedGaugeFirstFinitePhysicalCertificate

/-!
# Physical certificates retained by deterministic enriched successors

The enriched map provider is deterministic, so the corrected ordinary-front
kinematics retained by its row images survives the column recursion without a
second choice.
-/

noncomputable section

open MarkedSpace PathMetric

namespace FiniteSmoothRearFamilyEnrichedMapProvider

open EnrichedPhysicalChosenRichFamily
  TriangularMarkedRecursiveChoiceVariableTerminalConstructor

/-- The exact mapped successor carries the physical transition from its
ordinary terminal base to the diagonally adjacent ordinary terminal base in
the source column. -/
theorem mappedColumn_physicalTransition
    {Q : ℕ → Data} {e : ℕ → ℕ → ℝ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
    {period : ℕ → ℕ → ℝ} {diagonal : ℕ → ℝ}
    {kh Qmax Mtotal : ℕ → ℝ}
    {a MA NA : ℕ → ℕ → ℝ} {K0 K1 K2 kh0 : ℝ}
    (G : Provider Q e P0 P1 khat G1 Cg C c dlt
      period diagonal kh Qmax Mtotal a MA NA K0 K1 K2)
    (hkh : ∀ n, kh n = kh0)
    (k : ℕ) {current : ℕ → Data}
    (S : CertifiedColumn Q current e k P0 P1 khat G1 Cg C c dlt
      period diagonal (GaugeFamily period K0 K1 K2)) :
    EnrichedGaugeFirstFinitePhysicalCertificate.PhysicalTransitionCertificate
      S (mappedColumn G k S).val kh0 := by
  refine ⟨fun n => ?_⟩
  refine ⟨?_⟩
  have H := (G.image S n).physicalKinematics
  simpa only [mappedColumn, hkh n] using H

end FiniteSmoothRearFamilyEnrichedMapProvider

