import UnitTangentIterates.ConfiguredRecursiveEdgeRecostedPreCarrier
import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareChosenExactFunctionalFacts

/-!
# Profile-independent native pre-carrier cores

This module deliberately lies below intrinsic step assembly.  A presented
terminal boundary on a natively typed stage determines its geometric input
and pre-carrier core without any reference to configured row profiles.
-/

noncomputable section

open Function Set MarkedSpace PathMetric

namespace ConfiguredRecursiveEdgeRecostMultiplierNativeCore

open ConfiguredRecursiveEdgeRecostedPreCarrier
  FiniteSmoothRearFamilyMarkingAwareActualPullbackStages
  FiniteSmoothRearFamilyMarkingAwareChosenExactFunctionalFacts
  FiniteSmoothRearFamilyMarkingAwareChosenTerminal

variable {P0 kh khat Qmax : ℕ → ℝ} {j : ℕ}
  {S : Stage P0 kh khat Qmax j}

/-- Minimal, natively typed input for a pre-carrier core. -/
structure Input (G : GeometricInput S) : Prop where
  raw_time_one : G.rawPath.T = 1

namespace Input

variable {G : GeometricInput S}

/-- Exact-source joint regularity of the native chosen path. -/
noncomputable def jointC2 (I : Input G) :
    FiniteSmoothRearFamilyMarkingAwareChosenExactFunctionalFacts.ChosenPath.JointC2
      G.output.chosen :=
  FiniteSmoothRearFamilyMarkingAwareChosenExactFunctionalFacts.ChosenPath.jointC2_of_exactSource
    G.output.chosen

theorem chosen_time_one (I : Input G) :
    G.output.chosen.Delta.T = 1 := by
  rw [← G.output.stage_eq]
  exact I.raw_time_one

/-- Reconstruct the pre-carrier field-by-field on the native target stage. -/
noncomputable def core (I : Input G) : Core S where
  geometric := G
  eta_continuous := I.jointC2.eta_continuous
  eta1_continuous := I.jointC2.eta1_continuous
  eta2_continuous := I.jointC2.eta2_continuous
  time_one := I.chosen_time_one

end Input

/-- Convenience constructor from a native geometric input and time theorem. -/
noncomputable def coreOfGeometricInput
    (G : GeometricInput S) (hT : G.rawPath.T = 1) : Core S :=
  (Input.mk hT).core

@[simp] theorem coreOfGeometricInput_geometric
    (G : GeometricInput S) (hT : G.rawPath.T = 1) :
    (coreOfGeometricInput G hT).geometric = G := rfl

/-- The exact presented terminal boundary retained by prepared recursion. -/
structure PresentedInput (S : Stage P0 kh khat Qmax j) where
  base : Data
  bound : ℝ
  terminal : PresentedTerminalInputCore
    (p := S.displayed) (base := base) (bound := bound) S.applied
  output : PresentedOutputCore S.applied terminal
  path_time_one : S.Gamma.T = 1

namespace PresentedInput

/-- Native geometric input assembled without a dependent stage cast. -/
noncomputable def geometricInput (B : PresentedInput S) : GeometricInput S where
  base := B.base
  bound := B.bound
  terminal := B.terminal
  output := B.output

theorem rawPath_time_one (B : PresentedInput S) :
    B.geometricInput.rawPath.T = 1 := by
  change (B.output.stage.increment).T = 1
  rw [B.output.stage_eq, B.output.chosen.time_eq]
  exact B.path_time_one

/-- Complete native pre-carrier reconstructed from the presented boundary. -/
noncomputable def core (B : PresentedInput S) : Core S :=
  coreOfGeometricInput B.geometricInput B.rawPath_time_one

@[simp] theorem core_geometric (B : PresentedInput S) :
    B.core.geometric = B.geometricInput := rfl

end PresentedInput

end ConfiguredRecursiveEdgeRecostMultiplierNativeCore
