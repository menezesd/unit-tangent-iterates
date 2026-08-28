import UnitTangentIterates.ConfiguredRecursiveEdgeRecostMultiplierPreCarrier
import UnitTangentIterates.ConfiguredRecursiveEdgeRecostedNormalizedReachableState

/-!
# Normalized history completion for the multiplier recost source

The old and multiplier sources have different mass data.  They nevertheless
have the same recost carrier, period, and marking Jacobian.  We reuse the old
history construction only as a path/component certificate and record the two
terminal component identities explicitly.
-/

namespace ConfiguredRecursiveEdgeRecostMultiplierNormalizedCompletion

open ConfiguredRecursiveEdgeRecostMultiplierPreCarrier
open ConfiguredRecursiveEdgeRecostedNormalizedReachableState
open FiniteSmoothRearFamilyMarkingAwareActualPullbackStages
open FiniteSmoothRearFamilyMarkingAwareFullyPhysicalJacobi

noncomputable def completion
    {MA NA Etotal Dtarget : ℝ}
    {RJ : ConfiguredRecursiveEdgeSourceP0RowJetTail.RowJetScalarOutput MA NA}
    {O : ConfiguredRecursiveEdgeFiniteColumnGaugeMajorant.Output RJ Etotal Dtarget}
    {P0u khatu Qmaxu : ℕ → ℝ} {r depth : ℕ}
    {S : Stage P0u
      (fun _ => ConfiguredCombinedPhysicalDiagonalLargeSeparation.sourceKh)
      khatu Qmaxu r}
    {P1 edgeDefect p0 khat0 qmax0 : ℝ}
    (H : State O S P1 depth edgeDefect)
    (C : ConfiguredRecursiveEdgeRecostedPreCarrier.Core S)
    (I : ConfiguredRecursiveEdgeRecostedScaledPreCarrier.Input C p0
      ConfiguredCombinedPhysicalDiagonalLargeSeparation.sourceKh khat0 qmax0)
    (hE : Etotal ≤ 1 / 8)
    (hcur : I.eps ≤ O.major (depth + 1))
    (L : ℝ) (hL : 1 ≤ L) (hL2 : 2 ≤ L ^ 2)
    (hPL : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      FiniteSmoothRearFamilyMarkingAwareAppliedSource.rearPeriod S.source t ≤ L) :
    ConfiguredRecursiveEdgeRecostedPreCarrier.Completion C (unscaled I)
      Etotal configuredC0 configuredC1 configuredC2
      (L ^ 2 * (2 * edgeDefect)) :=
  H.completion C (unscaled I) hE hcur L hL hL2 hPL

theorem terminal_phi1_eq_scaled
    {P0u khu khatu Qmaxu : ℕ → ℝ} {j : ℕ}
    {S : Stage P0u khu khatu Qmaxu j}
    {C : ConfiguredRecursiveEdgeRecostedPreCarrier.Core S}
    {p0 kh0 khat0 qmax0 : ℝ}
    (I : ConfiguredRecursiveEdgeRecostedScaledPreCarrier.Input C
      p0 kh0 khat0 qmax0) :
    (unscaled I).source.phi1 = I.source.phi1 :=
  (source_phi1_eq_unscaled I).symm

theorem terminal_period_eq_scaled
    {P0u khu khatu Qmaxu : ℕ → ℝ} {j : ℕ}
    {S : Stage P0u khu khatu Qmaxu j}
    {C : ConfiguredRecursiveEdgeRecostedPreCarrier.Core S}
    {p0 kh0 khat0 qmax0 : ℝ}
    (I : ConfiguredRecursiveEdgeRecostedScaledPreCarrier.Input C
      p0 kh0 khat0 qmax0) :
    (unscaled I).source.P = I.source.P :=
  (source_period_eq_unscaled I).symm

/-- The multiplier changes only the source mass data.  The intrinsic-front
functional certificate therefore transports from the erased direct source. -/
noncomputable def nextIntrinsic
    {MA NA Etotal Dtarget : ℝ}
    {RJ : ConfiguredRecursiveEdgeSourceP0RowJetTail.RowJetScalarOutput MA NA}
    {O : ConfiguredRecursiveEdgeFiniteColumnGaugeMajorant.Output RJ Etotal Dtarget}
    {P0u khatu Qmaxu : ℕ → ℝ} {r depth : ℕ}
    {S : Stage P0u
      (fun _ => ConfiguredCombinedPhysicalDiagonalLargeSeparation.sourceKh)
      khatu Qmaxu r}
    {P1 edgeDefect p0 khat0 qmax0 : ℝ}
    (H : State O S P1 depth edgeDefect)
    (C : ConfiguredRecursiveEdgeRecostedPreCarrier.Core S)
    (I : ConfiguredRecursiveEdgeRecostedScaledPreCarrier.Input C p0
      ConfiguredCombinedPhysicalDiagonalLargeSeparation.sourceKh khat0 qmax0) :
    FiniteSmoothRearFamilyMarkingAwareNonaffineFullyPhysicalHistoryLink.IntrinsicFrontFunctionalFacts
      I.source := by
  let F := State.nextIntrinsic C (unscaled I)
  refine ⟨?_⟩
  simpa [ConfiguredRecursiveEdgeRecostedScaledPreCarrier.Input.source,
    ConfiguredRecursiveEdgeRecostedPreCarrier.Input.source, unscaled,
    FiniteSmoothRearFamilyMarkingAwareNonaffineFullyPhysicalHistoryLink.intrinsicFront,
    FiniteSmoothRearFamilyMarkingAwareExactSuccessorScaledDirectRecostSource.scaledDirectSource,
    FiniteSmoothRearFamilyMarkingAwareExactSuccessorDirectRecostSource.directSource,
    FiniteSmoothRearFamilyMarkingAwareExactSuccessorDirectRecostSource.rawSource] using
      F.functional

end ConfiguredRecursiveEdgeRecostMultiplierNormalizedCompletion
