import UnitTangentIterates.ConfiguredRecursiveEdgeRecostMultiplierPersistentProvenance
import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareChosenExactFunctionalFacts

/-!
# Automatic regularity of a recosted geometric successor

The exact chosen-path construction already supplies joint continuity of its
normal rate and first two spatial derivatives.  The mapped carrier is the
canonical recost of the preceding chosen path, so its time interval is also
the retained unit interval.  Consequently successor pre-carriers require no
new regularity callback.
-/

noncomputable section

open Function Set MarkedSpace PathMetric

namespace ConfiguredRecursiveEdgeRecostMultiplierAutomaticSuccessorRegularity

open ConfiguredRecursiveEdgeRecostedGeometricState
  ConfiguredRecursiveEdgeRecostedScaledGeometricStep
  FiniteSmoothRearFamilyMarkingAwareChosenExactFunctionalFacts
  FiniteSmoothRearFamilyMarkingAwareCompositionGeometricCanonicalRow

variable {Q : ℕ → Data} {e : ℕ → ℕ → ℝ}
  {P0 P1 G1 Cg C Qmax : ℕ → ℝ}
  {kappaHat c dlt kappa : ℝ}
  {X : State Q e P0 P1 G1 Cg C Qmax kappaHat c dlt kappa}

/-- Regularity of every newly selected canonical carrier is theorem-produced
from the exact source and the preceding unit-time recost. -/
noncomputable def successorRegularity (H : StepInput X) (n : ℕ) :
    Regularity H.next n := by
  let W := (H.next.geometricInput n).output.chosen
  let R :=
    FiniteSmoothRearFamilyMarkingAwareChosenExactFunctionalFacts.ChosenPath.jointC2_of_exactSource
      W
  refine
    { eta_continuous := R.eta_continuous
      eta1_continuous := R.eta1_continuous
      eta2_continuous := R.eta2_continuous
      time_one := ?_ }
  change W.Delta.T = 1
  rw [W.time_eq]
  change (H.family.carrier n).T = 1
  simpa [StepInput.family, ConfiguredRecursiveEdgeRecostedScaledGeometricStep.core,
    ConfiguredRecursiveEdgeRecostedPreCarrier.Core.path,
    CanonicalNormalPathRecost.recost] using (H.regularity (n + 1)).time_one

/-- The canonical successor pre-carrier, with no external regularity input. -/
noncomputable def successorPre (H : StepInput X) (n : ℕ) :
    ConfiguredRecursiveEdgeRecostedPreCarrier.Core (H.next.stage n) :=
  ConfiguredRecursiveEdgeRecostMultiplierPersistentProvenance.successorPre H
    (successorRegularity H) n

theorem exists_successorPre (H : StepInput X) (n : ℕ) :
    Nonempty (ConfiguredRecursiveEdgeRecostedPreCarrier.Core
      (H.next.stage n)) :=
  ⟨successorPre H n⟩

end ConfiguredRecursiveEdgeRecostMultiplierAutomaticSuccessorRegularity
