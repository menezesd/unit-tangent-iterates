import UnitTangentIterates.ConfiguredCommonTubeTransfer
import UnitTangentIterates.FiniteSmoothRearFamilyEnrichedMapProvider

/-!
# Fixed common tubes from enriched gauge certificates

The selected enriched gauge certificate already retains an ordinary physical
terminal.  This module projects that fact through both certificate
constructors and combines it with the configured common-tube transfer.
-/

noncomputable section

open MarkedSpace PathMetric

namespace FiniteSmoothRearFamilyEnrichedMapProvider.GaugeCertificate

open TriangularMarkedRecursiveChoiceVariableTerminalConstructor

/-- Both the base and mapped constructors retain physical facts for exactly
the terminal base stored in their selected rich stage. -/
theorem terminalPhysical_nonempty
    {Q current : ℕ → Data} {e : ℕ → ℕ → ℝ} {k : ℕ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
    {period : ℕ → ℕ → ℝ} {K0 K1 K2 : ℝ}
    {T : ColumnStep Q current e k P0 P1 khat G1 Cg C c dlt} {n : ℕ}
    (G : FiniteSmoothRearFamilyEnrichedMapProvider.GaugeCertificate
      period K0 K1 K2 T n) :
    Nonempty (ConfiguredGaugeEndpointDefect.TerminalPhysicalFacts
      (T.richStage n).terminalBase) := by
  cases G with
  | base W =>
      rw [← W.terminalBase_eq]
      exact ⟨W.terminalPhysical⟩
  | mapped W =>
      rw [← W.terminalBase_eq]
      exact ⟨W.terminalPhysical⟩

/-- An enriched selected terminal lies in the fixed configured tube once its
corrected curvature and its reserved model-distance estimate are available.
No comparison with the certificate's local tube constants is required. -/
theorem commonTube_of_dist
    {B : Data → Data} {Q : ℕ → Data} {C0 K c0 d0 dlt0 : ℝ}
    {d0row : ℕ → ℝ} {A0 rho : ℕ → ℝ}
    (R : PaperFaithfulLocalApproximatePullback.InductiveTubeBudget
      B Q C0 K d0row c0 d0 dlt0 A0 rho)
    {current : ℕ → Data} {e : ℕ → ℕ → ℝ} {k : ℕ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
    {period : ℕ → ℕ → ℝ} {K0 K1 K2 : ℝ}
    {T : ColumnStep Q current e k P0 P1 khat G1 Cg C c dlt} {n : ℕ}
    (G : FiniteSmoothRearFamilyEnrichedMapProvider.GaugeCertificate
      period K0 K1 K2 T n)
    {M : Data}
    (hmodel : IsTubeMember
      (c0 + PullbackTubeTailBudget.radius C0 K d0row n) 0 d0 M)
    (hmodel_acc : ∀ u, ‖M.2.2 u‖ ≤ A0 n)
    (hcurv : ∀ u, 0 ≤ ((starRingEnd ℂ)
      ((T.richStage n).terminalBase.2.1 u) *
      (T.richStage n).terminalBase.2.2 u).im)
    (hdist : dist M (T.richStage n).terminalBase ≤
      PullbackTubeTailBudget.radius C0 K d0row n) :
    IsTubeMember c0 0 dlt0 (T.richStage n).terminalBase :=
  ConfiguredCommonTubeTransfer.mem_of_terminalPhysical_and_dist R n
    hmodel hmodel_acc (Classical.choice G.terminalPhysical_nonempty) hcurv hdist

/-- The exact quantitative decomposition used by the configured producer:
column shadowing plus terminal marking defect fit inside the reserved model
radius. -/
theorem commonTube_of_column_and_endpoint
    {B : Data → Data} {Q : ℕ → Data} {C0 K c0 d0 dlt0 : ℝ}
    {d0row : ℕ → ℝ} {A0 rho : ℕ → ℝ}
    (R : PaperFaithfulLocalApproximatePullback.InductiveTubeBudget
      B Q C0 K d0row c0 d0 dlt0 A0 rho)
    {current : ℕ → Data} {e : ℕ → ℕ → ℝ} {k : ℕ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
    {period : ℕ → ℕ → ℝ} {K0 K1 K2 : ℝ}
    {T : ColumnStep Q current e k P0 P1 khat G1 Cg C c dlt} {n : ℕ}
    (G : FiniteSmoothRearFamilyEnrichedMapProvider.GaugeCertificate
      period K0 K1 K2 T n)
    {M : Data}
    (hmodel : IsTubeMember
      (c0 + PullbackTubeTailBudget.radius C0 K d0row n) 0 d0 M)
    (hmodel_acc : ∀ u, ‖M.2.2 u‖ ≤ A0 n)
    (hcurv : ∀ u, 0 ≤ ((starRingEnd ℂ)
      ((T.richStage n).terminalBase.2.1 u) *
      (T.richStage n).terminalBase.2.2 u).im)
    {rcolumn rendpoint : ℝ}
    (hcolumn : dist M (T.next n) ≤ rcolumn)
    (hendpoint : dist (T.next n)
      (T.richStage n).terminalBase ≤ rendpoint)
    (hfit : rcolumn + rendpoint ≤
      PullbackTubeTailBudget.radius C0 K d0row n) :
    IsTubeMember c0 0 dlt0 (T.richStage n).terminalBase := by
  apply G.commonTube_of_dist R hmodel hmodel_acc hcurv
  exact (dist_triangle _ (T.next n) _).trans
    ((add_le_add hcolumn hendpoint).trans hfit)

end FiniteSmoothRearFamilyEnrichedMapProvider.GaugeCertificate
