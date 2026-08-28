import UnitTangentIterates.FiniteNonaffineMajorNormalizedState
import UnitTangentIterates.ConfiguredRecursiveEdgeRecostMultiplierIntrinsicDiagonalRows
import UnitTangentIterates.ConfiguredRecursiveEdgeRecostMultiplierNormalizedCompletion
import UnitTangentIterates.ConfiguredRecursiveEdgeRearPeriodFloor

/-! # Diagonal reachable layers over explicit finite-history budgets -/

noncomputable section

open Function Set MarkedSpace PathMetric

namespace FiniteNonaffineMajorLayer

open ConfiguredRecursiveEdgeRecostMultiplierIntrinsicDiagonalRows
  ConfiguredRecursiveEdgeRecostMultiplierPreCarrier
  FiniteHistoryMajorBudget
  FiniteNonaffineMajorNormalizedState
  FiniteSmoothRearFamilyMarkingAwareFullyPhysicalJacobi

variable {Etotal : ℝ} {k n : ℕ} {S : ℕ → Node}
  (budget : ℕ → MajorBudget Etotal)
  (stateP1 defect : ℕ → ℝ)

/-- One diagonal successor keeps the predecessor's fixed history budget.
Only its used slot changes from `k` to `k+1`. -/
noncomputable def nextState
    (G : Step S k)
    (H : State (budget (n + 1 + k))
      (S := (S (n + 1)).stage)
      (P1 := stateP1 (n + 1 + k)) (depth := k)
      (edgeDefect := defect (n + 1 + k)))
    (hE : Etotal ≤ 1 / 8)
    (hcur : (G.analytic n).eps ≤ (budget (n + 1 + k)).major (k + 1))
    (hupper : (G.analytic n).slice.periodUpper ≤ stateP1 (n + (k + 1))) :
    State (budget (n + (k + 1)))
      (S := (G.next n).stage)
      (P1 := stateP1 (n + (k + 1))) (depth := k + 1)
      (edgeDefect := defect (n + (k + 1))) := by
  let C := G.pre (n + 1)
  let I := G.analytic n
  let H' : State (budget (n + (k + 1)))
      (S := (S (n + 1)).stage)
      (P1 := stateP1 (n + (k + 1))) (depth := k)
      (edgeDefect := defect (n + (k + 1))) := by
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using H
  have hcur' : I.eps ≤ (budget (n + (k + 1))).major (k + 1) := by
    simpa [I, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hcur
  exact
    { sourceFacts := by
        simpa only [Step.next_source] using
          ({ slice := I.slice
             periodUpper_le := hupper
             functional := by
               have F :=
                 FiniteSmoothRearFamilyMarkingAwareChosenExactFunctionalFacts.ChosenPath.functionalIntegrable_of_exactSource
                   C.geometric.output.chosen
               simpa [I.path_eta] using F
             eps := I.eps
             jets := I.sourceJets
             eps_le_major := hcur' } :
            SourceFacts (budget (n + (k + 1))) I.source
              (stateP1 (n + (k + 1))) (k + 1))
      intrinsic := by
        simpa only [Step.next_source] using (State.scaledNextIntrinsic C I)
      periodFloor := fun t =>
        ConfiguredRecursiveEdgeRearPeriodFloor.one_le_rearPeriod t
      ancestry := State.nextAncestry (budget (n + (k + 1))) H' C
        (unscaled I) hE hcur'
      terminalJ_eq :=
        ConfiguredRecursiveEdgeRecostMultiplierNormalizedCompletion.terminal_phi1_eq_scaled I
      terminalP_eq :=
        ConfiguredRecursiveEdgeRecostMultiplierNormalizedCompletion.terminal_period_eq_scaled I }

/-- A whole reached diagonal layer.  Row `n` at depth `k` uses the fixed
budget indexed by its invariant diagonal `n+k`. -/
structure Layer (k : ℕ) (S : ℕ → Node) where
  normalized : ∀ n, State (budget (n + k)) (S := (S n).stage)
    (P1 := stateP1 (n + k)) (depth := k)
    (edgeDefect := defect (n + k))

namespace Layer

noncomputable def next
    (L : Layer budget stateP1 defect k S) (G : Step S k)
    (hE : Etotal ≤ 1 / 8)
    (hcur : ∀ n,
      (G.analytic n).eps ≤ (budget (n + (k + 1))).major (k + 1))
    (hupper : ∀ n,
      (G.analytic n).slice.periodUpper ≤ stateP1 (n + (k + 1))) :
    Layer budget stateP1 defect (k + 1) G.next where
  normalized n := by
    apply nextState budget stateP1 defect G (L.normalized (n + 1)) hE
    · simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hcur n
    · exact hupper n

end Layer

end FiniteNonaffineMajorLayer
