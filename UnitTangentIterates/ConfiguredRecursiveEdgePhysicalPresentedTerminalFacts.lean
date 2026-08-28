import UnitTangentIterates.ConfiguredRecursiveEdgeSourceP0PhysicalBaseSourceAdapter
import UnitTangentIterates.ConfiguredGaugeFirstTerminalPhysicalFacts
import UnitTangentIterates.PhysicalRearLimitKinematicClosure

/-! # Genuine-gauge terminal presentation for a configured edge -/

noncomputable section

open Function Set MarkedSpace PathMetric

namespace ConfiguredRecursiveEdgePhysicalPresentedTerminalFacts

open ConfiguredBaseProfiledEdgeSourceFamily
  ConfiguredBaseProfiledEdgeInitialGaugeSourceFamily
  ConfiguredCanonicalPairSource
  ConfiguredCombinedPhysicalDiagonalLargeSeparation
  ConfiguredGaugeEndpointDefect
  ConfiguredGaugeFirstPhysicalSequence
  ConfiguredGaugeFirstTerminalPhysicalFacts
  ConfiguredRecursiveEdgeSourceP0PhysicalBaseSourceAdapter
  FiniteSmoothRearFamilyMarkingAwarePhysicalCore
  RichStageDataPhaseRigidTransport

variable {MA NA : ℝ}

def normalizedTerminalPhase
    (O : ConfiguredRecursiveEdgeSourceP0ScalarStart.Output MA NA)
    (n : ℕ) : ℝ :=
  terminalRearPhase O n / perim (O.pair.input.carrier (n + 1)).data

/-- The ordinary constant-speed rear carrier marked at the terminal value of
the genuine rear gauge and displayed in the same Euclidean presentation as
the exact edge source. -/
def terminalData
    (O : ConfiguredRecursiveEdgeSourceP0ScalarStart.Output MA NA)
    (n : ℕ) : Data :=
  let A := presentation O n
  move A.translation A.rotation (normalizedTerminalPhase O n)
    (O.pair.input.carrier (n + 1)).data

/-- The successor front presentation compatible with the genuine terminal
rear phase.  It is deliberately not identified with the independently
normalized legacy successor presentation. -/
def successorPresentation
    (O : ConfiguredRecursiveEdgeSourceP0ScalarStart.Output MA NA)
    (n : ℕ) : Presentation O.pair.input (n + 2) :=
  ConfiguredGaugeFirstPhysicalSequence.next O.pair.input
    (presentation O n) (normalizedTerminalPhase O n)

def successorData
    (O : ConfiguredRecursiveEdgeSourceP0ScalarStart.Output MA NA)
    (n : ℕ) : Data :=
  (successorPresentation O n).data

theorem successor_tube
    (O : ConfiguredRecursiveEdgeSourceP0ScalarStart.Output MA NA)
    (n : ℕ) :
    IsTubeMember (commonC (data O)) 0 (commonDlt (data O))
      (successorData O n) := by
  unfold successorData Presentation.data move
  exact MarkedRigid.isTubeMember_rigidData
    (successorPresentation O n).rotation_norm
    (MarkedShift.isTubeMember_shiftData
      (O.pair.input.front_tube (n + 2)) (successorPresentation O n).phase)

/-- Exact selected-rear kinematics for the genuine terminal presentation. -/
noncomputable def physicalKinematics
    (O : ConfiguredRecursiveEdgeSourceP0ScalarStart.Output MA NA)
    (n : ℕ) :
    PhysicalRearLimitKinematics sourceKh (terminalData O n)
      (successorData O n) := by
  let K := Nonempty.some
    (ConfiguredGaugeFirstPhysicalSequence.physicalStep O.pair.input
      (presentation O n) (normalizedTerminalPhase O n))
  simpa [terminalData, successorData, successorPresentation] using K

noncomputable def stageComponents
    (O : ConfiguredRecursiveEdgeSourceP0ScalarStart.Output MA NA)
    (n : ℕ) :
    PhysicalRearLimitStageComponents (terminalData O n)
      (successorData O n) :=
  (physicalKinematics O n).toStageComponents sourceKh_nonnegative
    sourceKh_lt_one O.pair.input.c_pos (successor_tube O n)

/-- The complete ordinary endpoint package is invariant under the terminal
phase shift and the common unit rigid motion. -/
noncomputable def terminalPhysical
    (O : ConfiguredRecursiveEdgeSourceP0ScalarStart.Output MA NA)
    (n : ℕ) : TerminalPhysicalFacts (terminalData O n) :=
  let A := presentation O n
  moveFacts (carrierFacts (O.pair.input.carrier (n + 1)))
    A.translation A.rotation (normalizedTerminalPhase O n) A.rotation_norm

theorem terminal_perim
    (O : ConfiguredRecursiveEdgeSourceP0ScalarStart.Output MA NA)
    (n : ℕ) :
    perim (terminalData O n) = 2 * (data O).Hs (n + 1) :=
  (terminalPhysical O n).perim_eq

theorem terminal_tangent_range
    (O : ConfiguredRecursiveEdgeSourceP0ScalarStart.Output MA NA)
    (n : ℕ) :
    range (ev (successorData O n)) =
      range (UnitTangent.unitTangentMap (ev (terminalData O n))) :=
  (stageComponents O n).range_front_eq_unitTangent_rear

noncomputable def terminalStrict
    (O : ConfiguredRecursiveEdgeSourceP0ScalarStart.Output MA NA)
    (n : ℕ) :
    UnconditionalAssembly.LimitStrictnessDataH (terminalData O n) := by
  let R := (stageComponents O n).limitStrictness O.pair.input.c_pos
    (successor_tube O n)
  exact R.toH (fun s ↦ (R.curvature_deriv s).differentiableAt)

theorem terminal_dlt_pos
    (O : ConfiguredRecursiveEdgeSourceP0ScalarStart.Output MA NA)
    (n : ℕ) : 0 < (terminalPhysical O n).dlt := by
  simpa [terminalPhysical] using (O.pair.input.carrier (n + 1)).dlt_pos

theorem terminal_oval
    (O : ConfiguredRecursiveEdgeSourceP0ScalarStart.Output MA NA)
    (n : ℕ) : MainTheoremConditional.IsOval (ev (terminalData O n)) :=
  UnconditionalAssembly.isOval_ev_of_limitStrictnessDataH
    (terminalPhysical O n).cq_pos (terminal_dlt_pos O n)
    (terminalPhysical O n).tube (terminalStrict O n)

/-- Paper-facing terminal sidecar.  Its front presentation and every physical
fact are determined by the terminal value of the genuine gauge. -/
structure PresentedTerminalFacts
    (O : ConfiguredRecursiveEdgeSourceP0ScalarStart.Output MA NA)
    (n : ℕ) where
  physical : TerminalPhysicalFacts (terminalData O n)
  period_eq : perim (terminalData O n) = 2 * (data O).Hs (n + 1)
  strict : UnconditionalAssembly.LimitStrictnessDataH (terminalData O n)
  oval : MainTheoremConditional.IsOval (ev (terminalData O n))
  tangent_range : range (ev (successorData O n)) =
    range (UnitTangent.unitTangentMap (ev (terminalData O n)))

noncomputable def presentedTerminalFacts
    (O : ConfiguredRecursiveEdgeSourceP0ScalarStart.Output MA NA)
    (n : ℕ) : PresentedTerminalFacts O n where
  physical := terminalPhysical O n
  period_eq := terminal_perim O n
  strict := terminalStrict O n
  oval := terminal_oval O n
  tangent_range := terminal_tangent_range O n

end ConfiguredRecursiveEdgePhysicalPresentedTerminalFacts
