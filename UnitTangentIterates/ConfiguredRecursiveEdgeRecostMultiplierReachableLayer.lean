import UnitTangentIterates.ConfiguredRecursiveEdgeRecostMultiplierDiagonalRows
import UnitTangentIterates.ConfiguredRecursiveEdgeRecostMultiplierNormalizedCompletion
import UnitTangentIterates.ConfiguredRecursiveEdgeRecostMultiplierRowBudget
import UnitTangentIterates.ConfiguredRecursiveEdgePhysicalBaseFinalTailState

/-!
# Normalized reachable layers for the multiplier diagonal

The state in cell `(n,k)` uses the final gauge output shifted by `n+k`.
Thus the predecessor `(n+1,k)` and successor `(n,k+1)` have literally the
same scalar row after associativity, while the rowwise stage/source types are
never transported through an artificial column tail.
-/

noncomputable section

open Function Set MarkedSpace PathMetric
open scoped BigOperators

namespace ConfiguredRecursiveEdgeRecostMultiplierReachableLayer

open ConfiguredRecursiveEdgeRecostMultiplierClosing
  ConfiguredRecursiveEdgeRecostMultiplierDiagonalRows
  ConfiguredRecursiveEdgeRecostMultiplierNormalizedCompletion
  ConfiguredRecursiveEdgeRecostMultiplierPreCarrier
  ConfiguredRecursiveEdgeRecostMultiplierRowBudget
  ConfiguredRecursiveEdgeRecostedNormalizedReachableState
  ConfiguredRecursiveEdgeRecostedScaledPreCarrier
  FiniteSmoothRearFamilyMarkingAwareActualPullbackSynchronizedRows
  FiniteSmoothRearFamilyMarkingAwareAppliedSource
  FiniteSmoothRearFamilyMarkingAwareFullyPhysicalJacobi

variable {J : ConfiguredRecursiveEdgeSourceP0RowJetTail.RowJetScalarOutput
    ConfiguredRecursiveSourceP0FixedDistortion.choice.MA0
    ConfiguredRecursiveSourceP0FixedDistortion.choice.NA0}
  {O : GaugeOutput J} (R : RecostClosingOutput J O)

abbrev rowP1 (q : ℕ) : ℝ :=
  ConfiguredRecursiveEdgeSourceP0Growth.edgeP1 R.data
    ConfiguredRecursiveSourceP0FixedDistortion.choice.MA0 q

abbrev rowDefect (q : ℕ) : ℝ :=
  ConfiguredRecursiveEdgeSourceP0Growth.edgePhysicalDefect R.data (q + 1)

/-- Complete normalized successor at one synchronized diagonal. -/
noncomputable def nextState
    {k n : ℕ}
    {S : ∀ r, Stage
      (ConfiguredRecursiveEdgeRecostMultiplierDiagonalRows.Profiles.P0 R.data)
      (ConfiguredRecursiveEdgeRecostMultiplierDiagonalRows.Profiles.kh R.data)
      (ConfiguredRecursiveEdgeRecostMultiplierDiagonalRows.Profiles.khat R.data)
      (ConfiguredRecursiveEdgeRecostMultiplierDiagonalRows.Profiles.Qmax R.data) r k}
    {E0 C00 C10 C20 : ℕ → ℝ} {d0 : ℕ → ℕ → ℝ}
    (G : Step R.data S E0 C00 C10 C20 d0)
    (H : State
      ((ConfiguredRecursiveEdgePhysicalBaseFinalTailState.finalGaugeOutput R).shiftOutput
        (n + 1 + k))
      (S (n + 1)).asUnary (rowP1 R (n + 1 + k)) k
      (rowDefect R (n + 1 + k)))
    (hcur : (G.analytic n).eps ≤
      ((ConfiguredRecursiveEdgePhysicalBaseFinalTailState.finalGaugeOutput R).shiftOutput
        (n + 1 + k)).major (k + 1))
    (hupper : (G.analytic n).slice.periodUpper ≤ rowP1 R (n + (k + 1))) :
    State
      ((ConfiguredRecursiveEdgePhysicalBaseFinalTailState.finalGaugeOutput R).shiftOutput
        (n + (k + 1)))
      (G.next n).asUnary (rowP1 R (n + (k + 1))) (k + 1)
      (rowDefect R (n + (k + 1))) := by
  let C := ConfiguredRecursiveEdgeRecostMultiplierDiagonalRows.core (G.carrier (n + 1))
  let I := G.analytic n
  let A := H.nextAncestry C (unscaled I)
    ConfiguredRecursiveEdgeFinitePresentedFinalAssembly.distortionTotal_le_eighth hcur
  let X : State
      ((ConfiguredRecursiveEdgePhysicalBaseFinalTailState.finalGaugeOutput R).shiftOutput
        (n + 1 + k))
      (G.next n).asUnary (rowP1 R (n + (k + 1))) (k + 1)
      (rowDefect R (n + 1 + k)) :=
    { sourceFacts :=
        { slice := I.slice
          periodUpper_le := hupper
          functional := by
            have F :=
              FiniteSmoothRearFamilyMarkingAwareChosenExactFunctionalFacts.ChosenPath.functionalIntegrable_of_exactSource
                C.geometric.output.chosen
            simpa [I.path_eta] using F
          eps := I.eps
          jets := I.sourceJets
          eps_le_major := hcur }
      intrinsic := nextIntrinsic H C I
      periodFloor := fun t =>
        ConfiguredRecursiveEdgeRearPeriodFloor.one_le_rearPeriod t
      ancestry := by
        change ConfiguredRecursiveEdgeNonaffineChosenMajorEndpoints.ConcreteAncestry
          C.path (k + 1) (rowDefect R (n + 1 + k))
        exact A
      terminalJ_eq := by
        change A.terminalJ = I.source.phi1
        dsimp [A]
        rw [State.nextAncestry]
        exact terminal_phi1_eq_scaled I
      terminalP_eq := by
        change A.terminalP = I.source.P
        dsimp [A]
        rw [State.nextAncestry]
        exact terminal_period_eq_scaled I }
  convert X using 1 <;>
    simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

/-- A reachable synchronized layer, including the exact public-distance
prefix needed to derive the common tube of its successor. -/
structure Layer
    {k : ℕ}
    (S : ∀ n, Stage
      (ConfiguredRecursiveEdgeRecostMultiplierDiagonalRows.Profiles.P0 R.data)
      (ConfiguredRecursiveEdgeRecostMultiplierDiagonalRows.Profiles.kh R.data)
      (ConfiguredRecursiveEdgeRecostMultiplierDiagonalRows.Profiles.khat R.data)
      (ConfiguredRecursiveEdgeRecostMultiplierDiagonalRows.Profiles.Qmax R.data) n k) where
  normalized : ∀ n, State
    ((ConfiguredRecursiveEdgePhysicalBaseFinalTailState.finalGaugeOutput R).shiftOutput
      (n + k))
    (S n).asUnary (rowP1 R (n + k)) k (rowDefect R (n + k))
  dist_le : ∀ n, dist (base R n) (S n).displayed ≤
    Finset.sum (Finset.range k) (fun h => R.error n h)

namespace Layer

noncomputable def next
    {k : ℕ}
    {S : ∀ n, Stage
      (ConfiguredRecursiveEdgeRecostMultiplierDiagonalRows.Profiles.P0 R.data)
      (ConfiguredRecursiveEdgeRecostMultiplierDiagonalRows.Profiles.kh R.data)
      (ConfiguredRecursiveEdgeRecostMultiplierDiagonalRows.Profiles.khat R.data)
      (ConfiguredRecursiveEdgeRecostMultiplierDiagonalRows.Profiles.Qmax R.data) n k}
    {E0 C00 C10 C20 : ℕ → ℝ} {d0 : ℕ → ℕ → ℝ}
    (L : Layer R S) (G : Step R.data S E0 C00 C10 C20 d0)
    (hcur : ∀ n, (G.analytic n).eps ≤
      ((ConfiguredRecursiveEdgePhysicalBaseFinalTailState.finalGaugeOutput R).shiftOutput
        (n + 1 + k)).major (k + 1))
    (hupper : ∀ n,
      (G.analytic n).slice.periodUpper ≤ rowP1 R (n + (k + 1)))
    (hstep : ∀ n, (G.rawMetric n).edgeBudget ≤ R.error n k) :
    Layer R G.next where
  normalized n := nextState R G (L.normalized (n + 1)) (hcur n) (hupper n)
  dist_le n := by
    have hdist := (G.displayedDistance n).trans (hstep n)
    have htri := dist_triangle (base R n) (S n).displayed (G.next n).displayed
    calc
      dist (base R n) (G.next n).displayed ≤
          dist (base R n) (S n).displayed +
            dist (S n).displayed (G.next n).displayed := htri
      _ ≤ Finset.sum (Finset.range k) (fun h => R.error n h) + R.error n k :=
        add_le_add (L.dist_le n) hdist
      _ = Finset.sum (Finset.range (k + 1)) (fun h => R.error n h) := by
        rw [Finset.sum_range_succ]

end Layer

end ConfiguredRecursiveEdgeRecostMultiplierReachableLayer
