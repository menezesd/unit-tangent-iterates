import UnitTangentIterates.ConfiguredCanonicalRearCarrier
import UnitTangentIterates.ConfiguredGaugeFirstPhysicalSequence

/-!
# Canonical configured pair source in the inductive common tube

This module joins the model fronts produced by the inductive tube budget to
the canonical configured rear carriers.  Both sides use the same honest
constants `Hs 0` and `chordBase / 2`.  The common rear tube is also transported
through the phase and rigid presentation used by the gauge-first base stage.
-/

noncomputable section

open MarkedSpace PathMetric

namespace ConfiguredCanonicalPairSource

open ConfiguredApproximateDefectPathActualTerminal
  ConfiguredGaugeFirstPhysicalSequence

def commonC (D : ConstructedConfiguredSequenceWeighted.Data) : ℝ := D.Hs 0

def commonDlt (D : ConstructedConfiguredSequenceWeighted.Data) : ℝ :=
  ConfiguredInductiveTubeBudget.chordBase D.model / 2

/-- A completely constructed pair-source input, retaining the common tube of
its canonical rear carriers. -/
structure Output
    (D : ConstructedConfiguredSequenceWeighted.Data) (Q : ℕ → Data)
    (kh C K : ℝ) (d : ℕ → ℝ) where
  carriers : ∀ n, RearCarrier D n
  carrier_common : ∀ n,
    IsTubeMember (commonC D) 0 (commonDlt D) (carriers n).data
  budget : PaperFaithfulLocalApproximatePullback.InductiveTubeBudget
    (SelectedInverseMap.selInv kh) Q C K d
    (commonC D) (ConfiguredInductiveTubeBudget.chordBase D.model)
    (commonDlt D) (ConfiguredInductiveTubeBudget.accBound D.model)
    (ConfiguredInductiveTubeBudget.rowRho D.model C K d)
  input : ConfiguredModelPairSource.Input D Q kh (commonC D) (commonDlt D)
  input_carrier : ∀ n, input.carrier n = carriers n

/-- The shifted scalar tube budget and the canonical `kH` orbit discharge the
entire configured pair-source input. -/
theorem exists_output
    (D : ConstructedConfiguredSequenceWeighted.Data) {Q : ℕ → Data}
    {kh C K : ℝ} {d : ℕ → ℝ}
    (hQ : ∀ n, perim (Q n) = 2 * D.Hs n ∧
      ev (Q n) = TwoCapPairsAssembly.front
        (D.kappas n) D.model.thetaBase (D.Hs n))
    (R : PaperFaithfulLocalApproximatePullback.InductiveTubeBudget
      (SelectedInverseMap.selInv kh) Q C K d
      (commonC D) (ConfiguredInductiveTubeBudget.chordBase D.model)
      (commonDlt D) (ConfiguredInductiveTubeBudget.accBound D.model)
      (ConfiguredInductiveTubeBudget.rowRho D.model C K d))
    (hkh0 : 0 ≤ kh) (hkh1 : kh < 1)
    (ha : D.model.a ≤ kh) :
    Nonempty (Output D Q kh C K d) := by
  obtain ⟨A, hA⟩ := ConfiguredCanonicalRearCarrier.exists_carriers D
  have hfront : ∀ n, IsTubeMember (commonC D) 0 (commonDlt D) (Q n) := by
    intro n
    have hs : commonC D ≤ commonC D + PullbackTubeTailBudget.radius C K d n :=
      le_add_of_nonneg_right (R.radius_nonneg n)
    have hd : commonDlt D ≤ ConfiguredInductiveTubeBudget.chordBase D.model := by
      have hkpos :=
        ConstructedConfiguredInductiveTubeBudget.configured_kstar_pos D.model
      have hnonneg : 0 ≤ ConfiguredInductiveTubeBudget.chordBase D.model := by
        rw [ConstructedConfiguredInductiveTubeBudget.chordBase_eq_min D.model hkpos]
        exact (lt_min D.separation_zero_pos
          (div_pos Real.pi_pos (mul_pos (by norm_num) hkpos))).le
      dsimp [commonDlt]
      linarith
    exact (R.model_mem n).mono hs hd
  let S : ConfiguredModelPairSource.Input D Q kh (commonC D) (commonDlt D) :=
    { carrier := A
      front_model := hQ
      front_tube := hfront
      c_pos := D.separation_zero_pos
      kh_nonneg := hkh0
      kh_lt_one := hkh1
      steering_cap_le := ha }
  exact ⟨⟨A, hA, R, S, fun _ => rfl⟩⟩

/-- The configured strip cap itself is the canonical selected-inverse cap.
This specialization removes the last arbitrary `kh`: unlike the independent
curvature majorant `D.kstar`, `D.model.a` is subunit by construction. -/
theorem exists_output_modelA
    (D : ConstructedConfiguredSequenceWeighted.Data) {Q : ℕ → Data}
    {C K : ℝ} {d : ℕ → ℝ}
    (hQ : ∀ n, perim (Q n) = 2 * D.Hs n ∧
      ev (Q n) = TwoCapPairsAssembly.front
        (D.kappas n) D.model.thetaBase (D.Hs n))
    (R : PaperFaithfulLocalApproximatePullback.InductiveTubeBudget
      (SelectedInverseMap.selInv D.model.a) Q C K d
      (commonC D) (ConfiguredInductiveTubeBudget.chordBase D.model)
      (commonDlt D) (ConfiguredInductiveTubeBudget.accBound D.model)
      (ConfiguredInductiveTubeBudget.rowRho D.model C K d)) :
    Nonempty (Output D Q D.model.a C K d) := by
  exact exists_output D hQ R
    (D.model.configs 0).ha0 (D.model.configs 0).ha1 (le_refl _)

namespace Output

variable {D : ConstructedConfiguredSequenceWeighted.Data} {Q : ℕ → Data}
  {kh C K : ℝ} {d : ℕ → ℝ} (O : Output D Q kh C K d)

/-- The actual terminal base selected by the gauge-first depth-zero provider
inherits the canonical common rear tube. -/
theorem chosenBaseTerminal_tube
    (hQ : ∀ n, perim (Q n) = 2 * D.Hs n ∧
      ev (Q n) = TwoCapPairsAssembly.front
        (D.kappas n) D.model.thetaBase (D.Hs n))
    (Krow : ℝ) (Cvar : ℕ → ℝ) (n : ℕ) :
    IsTubeMember (commonC D) 0 (commonDlt D)
      (Classical.choose
        (ConfiguredGaugeFirstPhysicalSequence.exists_richStage
          O.input hQ Krow Cvar n)).terminalBase := by
  let P := ConfiguredGaugeFirstPhysicalSequence.presentations
    (S := O.input) (hQ := hQ) n
  let r := ConfiguredGaugeFirstPhysicalSequence.rearPhase O.input hQ P
  have heq := Classical.choose_spec
    (ConfiguredGaugeFirstPhysicalSequence.exists_richStage
      O.input hQ Krow Cvar n)
  rw [heq.1]
  rw [O.input_carrier n]
  exact MarkedRigid.isTubeMember_rigidData P.rotation_norm
    (MarkedShift.isTubeMember_shiftData (O.carrier_common n) r)

end Output

end ConfiguredCanonicalPairSource
