import UnitTangentIterates.ConfiguredRecursiveEdgeRecostedScaledGeometricStep
import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareChosenExactFunctionalFacts

/-!
# Automatic regularity of reachable recosted geometric rows

Joint `C²` continuity of a theorem-produced chosen path is automatic from its
exact source.  Thus the only separate path datum needed by `Regularity` is the
normalization of the carrier time interval; canonical recosting preserves it.
-/

noncomputable section

open Function Set MarkedSpace PathMetric

namespace ConfiguredRecursiveEdgeRecostMultiplierRegularityClosure

open ConfiguredRecursiveEdgeRecostedGeometricState
  ConfiguredRecursiveEdgeRecostedScaledGeometricStep
  FiniteSmoothRearFamilyMarkingAwareChosenExactFunctionalFacts
  FiniteSmoothRearFamilyMarkingAwareCompositionGeometricCanonicalRow
  FiniteSmoothRearFamilyMarkingAwareRecostedGeometricPresentedRecursion

variable {Q : ℕ → Data} {e : ℕ → ℕ → ℝ}
  {P0 P1 G1 Cg C Qmax : ℕ → ℝ}
  {kappaHat c dlt kappa : ℝ}

/-- Exact-source chosen paths automatically have the three joint continuity
fields required by `Regularity`. -/
noncomputable def regularity_of_path_time_one
    (X : State Q e P0 P1 G1 Cg C Qmax kappaHat c dlt kappa)
    (hT : ∀ n, (X.column.path n).T = 1) (n : ℕ) : Regularity X n := by
  let O := output X.invariant n
  let H :=
    FiniteSmoothRearFamilyMarkingAwareChosenExactFunctionalFacts.ChosenPath.jointC2_of_exactSource
      O.chosen
  exact
    { eta_continuous := H.eta_continuous
      eta1_continuous := H.eta1_continuous
      eta2_continuous := H.eta2_continuous
      time_one := O.chosen.time_eq.trans (hT n) }

variable {X : State Q e P0 P1 G1 Cg C Qmax kappaHat c dlt kappa}

/-- A recosted successor carrier has the same terminal time as the preceding
chosen path. -/
theorem next_path_time_one (H : StepInput X) (n : ℕ) :
    (H.next.column.path n).T = 1 := by
  change
    (ConfiguredRecursiveEdgeRecostedPreCarrier.Core.path
      (core X (n + 1) (H.regularity (n + 1)))).T = 1
  simpa [ConfiguredRecursiveEdgeRecostedPreCarrier.Core.path,
    CanonicalNormalPathRecost.recost] using
      (H.regularity (n + 1)).time_one

/-- No additional regularity callback is needed after a chosen multiplier
step: exact-source joint continuity and the preceding time normalization close
all four fields. -/
noncomputable def regularity_next (H : StepInput X) (n : ℕ) :
    Regularity H.next n :=
  regularity_of_path_time_one H.next (next_path_time_one H) n

end ConfiguredRecursiveEdgeRecostMultiplierRegularityClosure
