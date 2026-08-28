import UnitTangentIterates.ConfiguredRecursiveEdgeRecostMultiplierNativeCore
import UnitTangentIterates.ConfiguredRecursiveEdgeRecostMultiplierRegularityClosure

/-!
# Native intrinsic nodes and cores from geometric states

Bundling scalar profiles with a stage in `Node` is the sound way to cross the
global/native boundary.  Equality of bare stages does not retain the hidden
profile indices, whereas equality of nodes does.  This module reconstructs a
native node, terminal boundary, geometric input, and pre-carrier directly from
a geometric invariant, and provides the ordinary-node-equality adapter used
by intrinsic `InputData`.
-/

noncomputable section

open Function Set MarkedSpace PathMetric

namespace ConfiguredRecursiveEdgeRecostMultiplierNativeStateCore

open ConfiguredRecursiveEdgeRecostMultiplierClosing
  ConfiguredRecursiveEdgeRecostMultiplierIntrinsicDiagonalRows
  ConfiguredRecursiveEdgeRecostMultiplierIntrinsicReachableLayer
  ConfiguredRecursiveEdgeRecostMultiplierIntrinsicStepAssembly
  ConfiguredRecursiveEdgeRecostMultiplierNativeCore
  ConfiguredRecursiveEdgeRecostMultiplierRegularityClosure
  ConfiguredRecursiveEdgeRecostedGeometricState
  ConfiguredRecursiveEdgeRecostedPreCarrier
  ConfiguredRecursiveEdgeRecostedScaledGeometricStep
  FiniteSmoothRearFamilyMarkingAwareCompositionGeometricCanonicalRow

variable {Q : ℕ → Data} {e : ℕ → ℕ → ℝ}
  {P0 P1 G1 Cg C Qmax : ℕ → ℝ}
  {kappaHat c dlt : ℝ}

abbrev GeometricState
    (Q : ℕ → Data) (e : ℕ → ℕ → ℝ)
    (P0 P1 G1 Cg C Qmax : ℕ → ℝ)
    (kappaHat c dlt : ℝ) :=
  State Q e P0 P1 G1 Cg C Qmax kappaHat c dlt
    ConfiguredCombinedPhysicalDiagonalLargeSeparation.sourceKh

/-- Row `n` rebuilt at intrinsic index zero.  Its fields are copied directly,
so no source or applied object is transported across a false index equality. -/
noncomputable def node
    (X : GeometricState Q e P0 P1 G1 Cg C Qmax kappaHat c dlt)
    (n : ℕ) : Node where
  P0 := P0 (n + X.depth)
  khat := kappaHat
  Qmax := Qmax (n + X.depth)
  stage :=
    { start := (X.stage n).start
      rear := (X.stage n).rear
      Gamma := (X.stage n).Gamma
      source := (X.stage n).source
      applied := (X.stage n).applied
      displayed := (X.stage n).displayed }

@[simp] theorem node_displayed
    (X : GeometricState Q e P0 P1 G1 Cg C Qmax kappaHat c dlt) (n : ℕ) :
    (node X n).stage.displayed = (X.stage n).displayed := rfl

@[simp] theorem node_Gamma
    (X : GeometricState Q e P0 P1 G1 Cg C Qmax kappaHat c dlt) (n : ℕ) :
    (node X n).stage.Gamma = (X.stage n).Gamma := rfl

/-- The canonical presented terminal theorem rebuilt on the native node. -/
noncomputable def presentedInput
    (X : GeometricState Q e P0 P1 G1 Cg C Qmax kappaHat c dlt)
    (hT : ∀ n, (X.column.path n).T = 1) (n : ℕ) :
    ConfiguredRecursiveEdgeRecostMultiplierNativeCore.PresentedInput
      (node X n).stage where
  base := (geometry X.invariant n).presented
  bound := e n (X.depth + 1)
  terminal := terminalInput X.invariant n
  path_time_one := hT n

/-- Native canonical geometric input. -/
noncomputable def geometricInput
    (X : GeometricState Q e P0 P1 G1 Cg C Qmax kappaHat c dlt)
    (hT : ∀ n, (X.column.path n).T = 1) (n : ℕ) :=
  (presentedInput X hT n).geometricInput

/-- Native canonical pre-carrier core. -/
noncomputable def core
    (X : GeometricState Q e P0 P1 G1 Cg C Qmax kappaHat c dlt)
    (hT : ∀ n, (X.column.path n).T = 1) (n : ℕ) :
    Core (node X n).stage :=
  (presentedInput X hT n).core

variable {X : GeometricState Q e P0 P1 G1 Cg C Qmax kappaHat c dlt}

/-- Presented input of a mapped successor, entirely theorem-produced from
its mapped invariant and automatic recost time normalization. -/
noncomputable def successorPresentedInput (H : StepInput X) (n : ℕ) :
    ConfiguredRecursiveEdgeRecostMultiplierNativeCore.PresentedInput
      (node H.next n).stage :=
  presentedInput H.next (next_path_time_one H) n

/-- Native successor core before alignment with an intrinsic `InputData`. -/
noncomputable def successorCore (H : StepInput X) (n : ℕ) :
    Core (node H.next n).stage :=
  (successorPresentedInput H n).core

variable {J : ConfiguredRecursiveEdgeSourceP0RowJetTail.RowJetScalarOutput
    ConfiguredRecursiveSourceP0FixedDistortion.choice.MA0
    ConfiguredRecursiveSourceP0FixedDistortion.choice.NA0}
  {O : GaugeOutput J} {R : RecostClosingOutput J O}
  {k : ℕ} {S : ℕ → Node} {L : Layer R k S}

/-- Internal bridge between a mapped geometric step and the intrinsic step
assembled from the same scaled sources.  Ordinary node equality, unlike stage
`HEq`, retains the hidden scalar profile indices. -/
structure InputAlignment (H : StepInput X) (I : InputData R L) : Prop where
  nextNode_eq : ∀ n, node H.next n = (I.step).next n

/-- Transport the callback-free presented boundary through the bundled node
equality. -/
noncomputable def successorPresentedInputOfAlignment
    (H : StepInput X) (I : InputData R L) (A : InputAlignment H I) (n : ℕ) :
    ConfiguredRecursiveEdgeRecostMultiplierNativeCore.PresentedInput
      ((I.step).next n).stage := by
  rw [← A.nextNode_eq n]
  exact successorPresentedInput H n

/-- Persistent next pre-core, definitionally typed for the intrinsic
successor recursion. -/
noncomputable def successorCoreOfAlignment
    (H : StepInput X) (I : InputData R L) (A : InputAlignment H I) (n : ℕ) :
    Core ((I.step).next n).stage :=
  (successorPresentedInputOfAlignment H I A n).core

end ConfiguredRecursiveEdgeRecostMultiplierNativeStateCore
