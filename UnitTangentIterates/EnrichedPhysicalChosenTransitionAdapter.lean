import UnitTangentIterates.EnrichedPhysicalChosenRichFamily

/-!
# Adapters into the enriched chosen-column invariant
-/

noncomputable section

open MarkedSpace PathMetric

namespace EnrichedPhysicalChosenRichFamily

open AnchoredJacobiStableTransition
  PhysicalArclengthJacobiTransition
  TriangularMarkedRecursiveChoiceVariableTerminalConstructor
  PathMetric.NormalPath

/-- A unit-time path of cost at most `d` has every physical component at most
`P*d` when `P >= 1`. -/
def ComponentBound.of_cost
    {p q : Data} (Gamma : NormalPath p q) (hT : Gamma.T = 1)
    (F : ControlledJunctionPathFunctionalBounds.FunctionalIntegrable Gamma.eta)
    {P d : ℝ} (hP : 1 ≤ P) (hd : cost Gamma ≤ d) :
    ComponentBound (components P Gamma.eta) (P * d) := by
  obtain ⟨hw, hs0, hs1, hs2⟩ :=
    components_le_perim_mul_cost Gamma hT F hP
  have hP0 : 0 ≤ P := zero_le_one.trans hP
  have hcost := mul_le_mul_of_nonneg_left hd hP0
  exact
    { w := hw.trans hcost
      s0 := hs0.trans hcost
      s1 := hs1.trans hcost
      s2 := hs2.trans hcost }

/-- The exact pre-erasure gauge output is already the transition required by
the chosen-column recursion.  The displayed equalities merely identify its
locally named junction coefficients with the global two-index arrays. -/
def TransitionCertificate.of_gaugeOutput
    {Q current : ℕ → Data} {e : ℕ → ℕ → ℝ} {k : ℕ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
    {period : ℕ → ℕ → ℝ} {diagonal : ℕ → ℝ}
    {GaugeCertificate : GaugeFamily Q e P0 P1 khat G1 Cg C c dlt}
    {S : CertifiedColumn Q current e k P0 P1 khat G1 Cg C c dlt
      period diagonal GaugeCertificate}
    {T : CertifiedColumn Q S.step.next e (k + 1)
      P0 P1 khat G1 Cg C c dlt period diagonal GaugeCertificate}
    {a MA NA : ℕ → ℕ → ℝ} {K0 K1 K2 : ℝ}
    {raw : ℕ → ℝ → ℝ → ℝ}
    {aRaw mRaw MRaw NRaw : ℕ → ℝ}
    {CW C00 C10 C11 C20 C21 C22 : ℕ → ℝ}
    (G : ∀ n, EnrichedPhysicalGaugeStage.Output
      (S.step.richStage (n + 1)).stage.increment.eta (raw n)
      (T.step.richStage n).stage.increment.eta
      (period (n + 1) k) (period n (k + 1))
      (aRaw n) (mRaw n) (MRaw n) (NRaw n)
      (CW n) (C00 n) (C10 n) (C11 n) (C20 n) (C21 n) (C22 n)
      K0 K1 K2)
    (ha : ∀ n, a n k = aRaw n * (1 / mRaw n))
    (hMA : ∀ n, MA n k = MRaw n)
    (hNA : ∀ n, NA n k = NRaw n) :
    TransitionCertificate S T a MA NA K0 K1 K2 where
  transition n := by
    rw [ha n, hMA n, hNA n]
    exact (G n).transition

end EnrichedPhysicalChosenRichFamily
