import UnitTangentIterates.ConfiguredRecursiveEdgeGeometricPresentedPhysicalBounds
import UnitTangentIterates.ConfiguredRecursiveEdgeMixedConversionEnvelope
import UnitTangentIterates.PaperMainTheoremDirectProjection

/-!
# Configured transition-free geometric capstone

This file combines the canonical mixed conversion envelope, its weighted
large-separation shift, the geometric recursive core, physical row bounds and
the paper-facing closing argument.  No scalar conversion, summability, radius,
or closing-gap hypothesis remains in the public theorem.
-/

noncomputable section

open Function Set MarkedSpace PathMetric
open VariableTerminalRowTubeAdapter ExponentialDiagonalLargeSeparation
  ConfiguredGaugeEndpointLinearRadius

namespace ConfiguredRecursiveEdgeGeometricPresentedConfiguredCapstone

open ConstructedConfiguredInductiveTubeBudget.WeightedData
  ConfiguredRecursiveEdgeSourceP0
  ConfiguredRecursiveEdgeSourceP0Growth
  ConfiguredRecursiveEdgeWeightedEffectiveError
  ConfiguredRecursiveEdgeMixedConversionEnvelope
  ConfiguredRecursiveEdgeGeometricPresentedCapstone
  ConfiguredRecursiveEdgeGeometricPresentedDirectLimit
  ConfiguredRecursiveEdgeGeometricPresentedPhysicalBounds
  FiniteSmoothRearFamilyMarkingAwareCompositionGeometricPresentedRecursion

set_option maxHeartbeats 2000000

abbrev canonicalConversion
    (D : ConstructedConfiguredSequenceWeighted.Data)
    (MA NA khat kh M : ℝ)
    (hMA : 0 ≤ MA) (hNA : 0 ≤ NA) (hkhat : 0 ≤ khat)
    (hkh0 : 0 ≤ kh) (hkh1 : kh < 1) (hM : 0 ≤ M) : ℕ → ℝ :=
  mixedConversion D MA NA khat kh M hMA hNA hkhat hkh0 hkh1 hM

abbrev canonicalLarge
    (D : ConstructedConfiguredSequenceWeighted.Data)
    (MA NA khat kh M Cw : ℝ)
    (hMA : 0 ≤ MA) (hNA : 0 ≤ NA) (hkhat : 0 ≤ khat)
    (hkh0 : 0 ≤ kh) (hkh1 : kh < 1) (hM : 0 ≤ M) (hCw : 0 ≤ Cw) :=
  mixedWeightedOutput D MA NA khat kh M Cw
    hMA hNA hkhat hkh0 hkh1 hM hCw

abbrev shiftedData
    (D : ConstructedConfiguredSequenceWeighted.Data)
    (MA NA khat kh M Cw : ℝ)
    (hMA : 0 ≤ MA) (hNA : 0 ≤ NA) (hkhat : 0 ≤ khat)
    (hkh0 : 0 ≤ kh) (hkh1 : kh < 1) (hM : 0 ≤ M) (hCw : 0 ≤ Cw) :=
  shift D (canonicalLarge D MA NA khat kh M Cw
    hMA hNA hkhat hkh0 hkh1 hM hCw).N

abbrev canonicalError
    (D : ConstructedConfiguredSequenceWeighted.Data)
    (MA NA khat kh M Cw : ℝ)
    (hMA : 0 ≤ MA) (hNA : 0 ≤ NA) (hkhat : 0 ≤ khat)
    (hkh0 : 0 ≤ kh) (hkh1 : kh < 1) (hM : 0 ≤ M) (hCw : 0 ≤ Cw) :
    ℕ → ℕ → ℝ :=
  weightedError
    (canonicalConversion D MA NA khat kh M hMA hNA hkhat hkh0 hkh1 hM)
    (edgePhysicalDefect D)
    (canonicalLarge D MA NA khat kh M Cw
      hMA hNA hkhat hkh0 hkh1 hM hCw).N

/-- Complete configured capstone, conditional only on the concrete geometric
recursion and its geometric/base sidecars.  All dynamic scalar estimates are
constructed internally. -/
theorem exists_paperFacingOutput
    (D : ConstructedConfiguredSequenceWeighted.Data)
    {MA NA khat kh M Cw c dlt : ℝ}
    (hMA : 0 ≤ MA) (hNA : 0 ≤ NA) (hkhat : 0 ≤ khat)
    (hkh0 : 0 ≤ kh) (hkh1 : kh < 1) (hM : 0 ≤ M) (hCw : 0 ≤ Cw)
    {Q : ℕ → Data} {e : ℕ → ℕ → ℝ}
    {flowBound Qmax : ℕ → ℝ}
    (F : Core Q e
      (edgeSourceP0 (shiftedData D MA NA khat kh M Cw
        hMA hNA hkhat hkh0 hkh1 hM hCw))
      (edgeP1 (shiftedData D MA NA khat kh M Cw
        hMA hNA hkhat hkh0 hkh1 hM hCw) MA)
      (fun _ ↦ khat)
      (edgeG1 (shiftedData D MA NA khat kh M Cw
        hMA hNA hkhat hkh0 hkh1 hM hCw) MA NA)
      (edgeCgWithKhat (shiftedData D MA NA khat kh M Cw
        hMA hNA hkhat hkh0 hkh1 hM hCw) khat MA NA)
      flowBound (fun _ ↦ kh) Qmax c dlt)
    (herror : ∀ n k, e n (k + 1) =
      shiftSequence (edgePhysicalDefect D)
        (canonicalLarge D MA NA khat kh M Cw
          hMA hNA hkhat hkh0 hkh1 hM hCw).N (n + k + 1))
    {c0 d0 A0 rho upper : ℕ → ℝ}
    (B : RowBudget (fun n => F.markedGrid n 0)
      (edgeSourceP0 (shiftedData D MA NA khat kh M Cw
        hMA hNA hkhat hkh0 hkh1 hM hCw))
      (edgeP1 (shiftedData D MA NA khat kh M Cw
        hMA hNA hkhat hkh0 hkh1 hM hCw) MA)
      (fun _ ↦ khat)
      (edgeG1 (shiftedData D MA NA khat kh M Cw
        hMA hNA hkhat hkh0 hkh1 hM hCw) MA NA)
      (edgeCgWithKhat (shiftedData D MA NA khat kh M Cw
        hMA hNA hkhat hkh0 hkh1 hM hCw) khat MA NA)
      c0 d0 A0
      (fun n ↦ weightedRadius
        (canonicalConversion D MA NA khat kh M hMA hNA hkhat hkh0 hkh1 hM)
        (edgePhysicalDefect D)
        (canonicalLarge D MA NA khat kh M Cw
          hMA hNA hkhat hkh0 hkh1 hM hCw).N n)
      rho upper c dlt)
    (hbaseModel : ∀ n, IsTubeMember (c0 n) 0 (d0 n) (F.markedGrid n 0))
    (hbaseCommon : ∀ n, IsTubeMember c 0 dlt (F.markedGrid n 0))
    (hbasePerim : ∀ n, c0 n ≤ perim (F.markedGrid n 0))
    (hbaseAcc : ∀ n u, ‖(F.markedGrid n 0).2.2 u‖ ≤ A0 n)
    (markedTube : ∀ n k, VariableMarkedTube.IsVariableTubeMember
      c (flowBound n) 0 dlt (F.markedGrid n k))
    (caps : ∀ n k, GeometricPresentedRowCap ((F.rowFamilyAt k).row n) M
      (edgeEndpointConversion
        (shiftedData D MA NA khat kh M Cw
          hMA hNA hkhat hkh0 hkh1 hM hCw) kh M n)
      (shiftSequence (edgePhysicalDefect D)
        (canonicalLarge D MA NA khat kh M Cw
          hMA hNA hkhat hkh0 hkh1 hM hCw).N (n + k + 1)))
    (hc : 0 < c) (hdlt : 0 < dlt)
    {direction : ℂ} (hdirection : ‖direction‖ = 1)
    (hQbounded : Bornology.IsBounded (range ⇑(coherentGrid F 0 0).1))
    (hQwidth : Width.width (range ⇑(coherentGrid F 0 0).1) direction ≤ Cw)
    (hQlength : 2 * (shiftedData D MA NA khat kh M Cw
      hMA hNA hkhat hkh0 hkh1 hM hCw).Hs 0 ≤
      MarkedReparam.totalLength fun u => (coherentGrid F 0 0).2.1 u) :
    Nonempty ((O : TriangularMarkedPathSchemeVariableTerminal.LimitOutput
      (fun n => coherentGrid F n 0) (coherentGrid F)
      (canonicalError D MA NA khat kh M Cw
        hMA hNA hkhat hkh0 hkh1 hM hCw)
      dummyP0 dummyZero dummyZero dummyZero dummyZero flowBound c dlt) ×
      PaperFacingVariableTerminalOutput.Output O direction Cw
        ((shiftedData D MA NA khat kh M Cw
          hMA hNA hkhat hkh0 hkh1 hM hCw).Hs 0)) := by
  let Cmix := canonicalConversion D MA NA khat kh M
    hMA hNA hkhat hkh0 hkh1 hM
  let L := canonicalLarge D MA NA khat kh M Cw
    hMA hNA hkhat hkh0 hkh1 hM hCw
  let D' := shift D L.N
  let diagonal := shiftSequence (edgePhysicalDefect D) L.N
  let endpoint := edgeEndpointConversion D' kh M
  let w := weightedError Cmix (edgePhysicalDefect D) L.N
  have hspec := mixedConversion_spec D hMA hNA hkhat hkh0 hkh1 hM
  have hwnonnegative : ∀ n k, 0 ≤ w n k := fun n k =>
    weightedError_nonnegative hspec.2.1 (edgePhysicalDefect_nonnegative D) _ _ _
  have hwsummable : ∀ n, Summable (w n) := fun n =>
    weightedError_summable
      (summable_mixedWeightedSequence D hMA hNA hkhat hkh0 hkh1 hM) L.N n
  have coherentTube : ∀ n k, VariableMarkedTube.IsVariableTubeMember
      c (flowBound n) 0 dlt (coherentGrid F n k) := fun n k =>
    isVariableTubeMember_shiftData (markedTube n k) (coherentPhase F n k)
  have heffective := step_dist_le_effectiveError F endpoint diagonal
    (by simpa [endpoint, diagonal, D', L] using herror) coherentTube hM
    (by simpa [endpoint, diagonal, D', L] using caps)
  have hfactor : ∀ n k,
      NormalPathC2IncrementVariableSpeed.c2ConstVar
          (edgeSourceP0 D' (n + k)) (edgeP1 D' MA n) khat
          (edgeG1 D' MA NA n) (edgeCgWithKhat D' khat MA NA n) +
        endpoint n ≤ Cmix (L.N + n + k) := by
    intro n k
    change NormalPathC2IncrementVariableSpeed.c2ConstVar
          (edgeSourceP0 D (L.N + (n + k))) (edgeP1 D MA (L.N + n)) khat
          (edgeG1 D MA NA (L.N + n))
          (edgeCgWithKhat D khat MA NA (L.N + n)) +
        edgeEndpointConversion D kh M (L.N + n) ≤ Cmix (L.N + n + k)
    simpa [Cmix, Nat.add_assoc] using hspec.2.2.1 (L.N + n) k
  have hdom : ∀ n k,
      effectiveError
          (P0 := edgeSourceP0 D') (P1 := edgeP1 D' MA)
          (khat := fun _ ↦ khat) (G1 := edgeG1 D' MA NA)
          (Cg := edgeCgWithKhat D' khat MA NA) endpoint diagonal n k ≤
        w n k := by
    intro n k
    exact effectiveError_le_weightedError
      (P0 := edgeSourceP0 D') (P1 := edgeP1 D' MA)
      (khat := fun _ ↦ khat) (G1 := edgeG1 D' MA NA)
      (Cg := edgeCgWithKhat D' khat MA NA) (endpoint := endpoint)
      (C := Cmix) (d := edgePhysicalDefect D) L.N n k
      (edgePhysicalDefect_nonnegative D) hfactor
  have hstep : ∀ n k,
      dist (coherentGrid F n k) (coherentGrid F n (k + 1)) ≤ w n k :=
    fun n k => (heffective n k).trans (hdom n k)
  have hradius : ∀ n, ∑' k, w n k ≤
      weightedRadius Cmix (edgePhysicalDefect D) L.N n := fun _ => le_rfl
  apply exists_paperFacingOutput_of_rowBudget_and_caps F w
    hwnonnegative hwsummable hstep
    (by simpa [Cmix, L, D', w] using B) hradius hbaseModel hbaseCommon
    hbasePerim hbaseAcc markedTube hc hdlt hdirection hQbounded hQwidth
    hQlength
  intro O
  have hshadow : PaperFacingVariableTerminalOutput.shadowSize O =
      weightedRadius Cmix (edgePhysicalDefect D) L.N 0 := by
    rw [PaperFacingVariableTerminalOutput.shadowSize, dummy_rowC, one_mul,
      weightedRadius_eq_tail]
    apply tsum_congr
    intro k
    simp [w, weightedError, ShadowingTails.tail, Nat.add_assoc]
  rw [hshadow]
  simpa [weightedRadius_eq_tail, L, Cmix,
    ExponentialDiagonalLargeSeparation.rowRadius,
    ExponentialDiagonalLargeSeparation.rowError,
    ExponentialDiagonalLargeSeparation.shiftSequence,
    weightedSequence, ShadowingTails.tail, Nat.add_assoc] using L.width_gap

/-- Forget the marked compactness witness and expose exactly the ordinary
curve statement used in the paper. -/
theorem paperMain_of_nonempty_output
    {Q : ℕ → Data} {P : ℕ → ℕ → Data} {e : ℕ → ℕ → ℝ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
    {direction : ℂ} {modelWidth H : ℝ}
    (h : Nonempty ((O : TriangularMarkedPathSchemeVariableTerminal.LimitOutput
      Q P e P0 P1 khat G1 Cg C c dlt) ×
      PaperFacingVariableTerminalOutput.Output O direction modelWidth H)) :
    ∃ Gamma : ℕ → ℝ → ℂ, ∃ L : ℝ,
      0 < L ∧ Function.Periodic (Gamma 0) L ∧
      (∀ n, MainTheoremConditional.IsOval (Gamma n)) ∧
      (∀ n, range (Gamma (n + 1)) =
        range (UnitTangent.unitTangentMap (Gamma n))) ∧
      ¬ClosingArgument.IsCircleOfPerimeter (range (Gamma 0)) L := by
  obtain ⟨O, A⟩ := h
  exact PaperMainTheoremDirectProjection.of_output A

end ConfiguredRecursiveEdgeGeometricPresentedConfiguredCapstone
