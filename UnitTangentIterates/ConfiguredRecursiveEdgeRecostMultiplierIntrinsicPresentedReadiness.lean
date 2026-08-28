import UnitTangentIterates.ConfiguredRecursiveEdgeRecostMultiplierIntrinsicCoherentReadiness
import UnitTangentIterates.ConfiguredRecursiveEdgeRecostMultiplierNativePresentedInput

/-!
# Presented readiness for coherent intrinsic multiplier layers

This extension leaves the shared analytic-readiness records unchanged.  It
retains the source-tied recursive certificate and sharp mapped-source cost
for every row.  Since coherent readiness already chooses the successor's
displayed datum to be the scaled source's selected rear at time zero, these
two retained fields automatically produce the native presented boundary and
pre-carrier core.
-/

noncomputable section

open Function Set MarkedSpace PathMetric

namespace ConfiguredRecursiveEdgeRecostMultiplierIntrinsicPresentedReadiness

open ConfiguredRecursiveEdgeRecostMultiplierClosing
  ConfiguredRecursiveEdgeRecostMultiplierIntrinsicAnalyticReadiness
  ConfiguredRecursiveEdgeRecostMultiplierIntrinsicCoherentReadiness
  ConfiguredRecursiveEdgeRecostMultiplierIntrinsicDiagonalRows
  ConfiguredRecursiveEdgeRecostMultiplierIntrinsicReachableLayer
  ConfiguredRecursiveEdgeRecostMultiplierIntrinsicStepAssembly
  ConfiguredRecursiveEdgeRecostMultiplierNativeCore
  ConfiguredRecursiveEdgeRecostMultiplierNativePresentedInput
  ConfiguredRecursiveEdgeRecostedPreCarrier
  ConfiguredRecursiveEdgeRecostedScaledPreCarrier

variable {J : ConfiguredRecursiveEdgeSourceP0RowJetTail.RowJetScalarOutput
    ConfiguredRecursiveSourceP0FixedDistortion.choice.MA0
    ConfiguredRecursiveSourceP0FixedDistortion.choice.NA0}
  {O : GaugeOutput J} (R : RecostClosingOutput J O)

/-- The exact additional data needed to turn coherent analytic readiness into
the next layer's native theorem-produced pre-carriers.  The mapped cost is
stated directly at the public successor cell. -/
structure PresentedReadiness {k : ℕ} {S : ℕ → Node}
    {L : Layer R k S} (H : CoherentReadiness R L) where
  recursiveFacts : ∀ n,
    ConfiguredRecursiveEdgeRecostedScaledPreCarrier.Input.RecursiveFacts
      ((H.inputData R).analytic n)
  mappedCost_le : ∀ n,
    (∫ t in (0 : ℝ)..((H.inputData R).pre (n + 1)).path.T,
      ((H.inputData R).analytic n).source.m t) ≤ R.error n (k + 1)

namespace PresentedReadiness

variable {k : ℕ} {S : ℕ → Node} {L : Layer R k S}
  {H : CoherentReadiness R L}

/-- The generic boundary facts specialized to coherent displayed data. -/
def boundaryFacts (P : PresentedReadiness R H) (n : ℕ) :
    BoundaryFacts (H.inputData R) n (R.error n (k + 1)) where
  recursiveFacts := P.recursiveFacts n
  displayed_eq := rfl
  cost_le := P.mappedCost_le n

/-- Native presented terminal input for every successor row. -/
def presentedInput (P : PresentedReadiness R H) (n : ℕ) :
    PresentedInput (((H.inputData R).step).next n).stage :=
  (P.boundaryFacts R n).presentedInput

/-- Native successor pre-carrier, with terminal geometry and flow bounds
constructed automatically. -/
noncomputable def core (P : PresentedReadiness R H) (n : ℕ) :
    Core (((H.inputData R).step).next n).stage :=
  (P.boundaryFacts R n).core

end PresentedReadiness

end ConfiguredRecursiveEdgeRecostMultiplierIntrinsicPresentedReadiness
