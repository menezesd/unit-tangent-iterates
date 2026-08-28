import UnitTangentIterates.ConfiguredRecursiveSourceP0ScalarStart
import UnitTangentIterates.ConfiguredGaugeJetUniformShift

/-!
# A common scalar tail for large separation and gauge jets

The gauge-jet tail is chosen first.  The existing exponential diagonal theorem
is then applied to the shifted data and its shift is composed with the first
one.  Thus a single final index retains both all large-separation conclusions
and the uniform normalized jet bound `eps <= 1 / 2`.
-/

noncomputable section

open Function Set

namespace ConfiguredRecursiveSourceP0CombinedTailScalar

open ConfiguredCombinedPhysicalDiagonalLargeSeparation
  ConfiguredGaugeJetDistortion
  ConfiguredGaugeJetUniformShift
  ConfiguredPolynomialDiagonalStableRowDefectProvider
  ConfiguredRecursiveSourceP0Growth
  ConstructedConfiguredInductiveTubeBudget.WeightedData
  ExponentialDiagonalLargeSeparation

/-- An exponential large-separation output whose very same shift also makes
every configured gauge marking near the identity. -/
structure LargeOutput
    (D : ConstructedConfiguredSequenceWeighted.Data)
    (C d : ℕ → ℝ) (Cw Cjet : ℝ) where
  large : ExponentialDiagonalLargeSeparation.Output D C d Cw
  jet_half : ∀ n k, eps (shift D large.N) Cjet n k ≤ 1 / 2

/-- Add a prescribed jet tail before the tail selected by the existing
large-separation theorem.  No monotonicity of the opaque `Output` record is
assumed; all estimates are obtained by applying that theorem to shifted data. -/
theorem exists_largeOutput
    (D : ConstructedConfiguredSequenceWeighted.Data)
    (C d : ℕ → ℝ) {C0 A b gamma Cw Cjet : ℝ}
    (hC : ∀ n, 0 ≤ C n) (hC0 : 0 ≤ C0)
    (hA : 0 ≤ A) (hb : 0 < b) (hgamma : gamma < b)
    (hCgrowth : ∀ n, C n ≤ C0 * (1 + D.Hs n) ^ 2 *
      Real.exp (gamma * D.Hs n))
    (hd0 : ∀ n, 0 ≤ d n)
    (hdexp : ∀ n, d n ≤ A * Real.exp (-(b * D.Hs n)))
    (hCw : 0 ≤ Cw) (hCjet : 0 ≤ Cjet) :
    Nonempty (LargeOutput D C d Cw Cjet) := by
  obtain ⟨J⟩ := ConfiguredGaugeJetUniformShift.exists_output D hCjet
  let Ds := shift D J.N
  let Cs := shiftSequence C J.N
  let ds := shiftSequence d J.N
  have hCs : ∀ n, 0 ≤ Cs n := fun n ↦ hC (J.N + n)
  have hCgrowths : ∀ n, Cs n ≤
      C0 * (1 + Ds.Hs n) ^ 2 * Real.exp (gamma * Ds.Hs n) := by
    intro n
    simpa [Cs, Ds, shiftSequence] using hCgrowth (J.N + n)
  have hds : ∀ n, 0 ≤ ds n := fun n ↦ hd0 (J.N + n)
  have hdexps : ∀ n, ds n ≤ A * Real.exp (-(b * Ds.Hs n)) := by
    intro n
    simpa [ds, Ds, shiftSequence] using hdexp (J.N + n)
  obtain ⟨L⟩ := ExponentialDiagonalLargeSeparation.exists_output
    Ds Cs ds hCs hC0 hA hb hgamma hCgrowths hds hdexps hCw
  let N := J.N + L.N
  let final : ExponentialDiagonalLargeSeparation.Output D C d Cw :=
    { Mtotal := L.Mtotal
      Mtotal_pos := L.Mtotal_pos
      N := N
      separation_one := by
        simpa [N, Ds, shift, Nat.add_assoc] using L.separation_one
      stage_cap := by
        intro n k
        simpa [N, ds, shiftSequence, Nat.add_assoc] using L.stage_cap n k
      speed_tail := by
        intro n
        simpa [N, Ds, Cs, ds, shift, shiftSequence, Nat.add_assoc] using
          L.speed_tail n
      chord_tail := by
        intro n
        simpa [N, Ds, Cs, ds, shift, shiftSequence, Nat.add_assoc] using
          L.chord_tail n
      width_gap := by
        simpa [N, Ds, Cs, ds, shift, shiftSequence, Nat.add_assoc] using
          L.width_gap }
  refine ⟨{ large := final, jet_half := ?_ }⟩
  intro n k
  have H := J.half (L.N + n) k
  simpa [final, N, ConfiguredGaugeJetDistortion.eps,
    ConstructedRowDefectLargeSeparation.rowDefect_shift, Nat.add_assoc,
    Nat.add_left_comm, Nat.add_comm] using H

/-- Scalar/model data with a retained common jet and large-separation tail. -/
structure JetScalarOutput (MA NA Cjet : ℝ) where
  scalar : ConfiguredRecursiveSourceP0ScalarStart.Output MA NA
  jet_half : ∀ n k,
    eps (shift scalar.E.data scalar.large.N) Cjet n k ≤ 1 / 2

theorem exists_actualHalf_widthDataC3_and_largeOutput_of_eps
    {eps0 MA NA Cjet : ℝ}
    (heps : 0 < eps0) (heps10 : eps0 ≤ 1 / 10)
    (hMA : 0 ≤ MA) (hNA : 0 ≤ NA) (hCjet : 0 ≤ Cjet) :
    ∃ (E : ConstructedConfiguredSequenceWeighted.DataWithActualHalf)
      (direction : ℕ → ℂ) (Cw Mend : ℝ),
      0 ≤ Cw ∧ 0 < Mend ∧
      (∀ n, ‖direction n‖ = 1) ∧
      (∀ n, Width.width
        (range (TwoCapPairsAssembly.front (E.data.kappas n)
          E.data.model.thetaBase (E.data.Hs n))) (direction n) ≤ Cw) ∧
      (∀ n, physicalDefect E.data n < Mend) ∧
      ConstructedPulseWidth.C3Certificate E.data ∧
      Nonempty (LargeOutput E.data
        (mergedCombinedConversion E.data MA NA (analyticKhat E.data)
          sourceKh Mend)
        (physicalDefect E.data) Cw Cjet) := by
  obtain ⟨E, direction, Cw, hCw, hdir, hwidth, hC3⟩ :=
    ConstructedPulseWidth.exists_actualHalf_widthDataC3_of_eps heps heps10
  let D := E.data
  have hbeta : 0 < D.model.beta := (D.model.configs 0).hbeta0
  let gamma : ℝ := D.model.beta / 16
  let b : ℝ := D.model.beta / 8
  have hgamma : 0 < gamma := div_pos hbeta (by norm_num)
  have hb : 0 < b := div_pos hbeta (by norm_num)
  have hgamma_b : gamma < b := by
    dsimp [gamma, b]
    nlinarith
  obtain ⟨A, hA, hdexp⟩ := exists_physicalDefect_exp_bound D
  let Mend : ℝ := A * Real.exp (-(b * D.Hs 0)) + 1
  have hMend : 0 < Mend := by dsimp [Mend]; positivity
  have hdM : ∀ n, physicalDefect D n < Mend := by
    intro n
    have harg : -(b * D.Hs n) ≤ -(b * D.Hs 0) := by
      have hm := mul_le_mul_of_nonneg_left (D.separation_lower n) hb.le
      linarith
    have he := Real.exp_le_exp.mpr harg
    calc
      physicalDefect D n ≤ A * Real.exp (-(b * D.Hs n)) := by
        simpa [b] using hdexp n
      _ ≤ A * Real.exp (-(b * D.Hs 0)) :=
        mul_le_mul_of_nonneg_left he hA
      _ < Mend := by dsimp [Mend]; linarith
  obtain ⟨C0, hC0, hCgrowth⟩ :=
    exists_mergedCombinedConversion_growth_majorant D hMA hNA
      (analyticKhat_nonnegative D) sourceKh_nonnegative sourceKh_lt_one
      hMend.le hgamma
  refine ⟨E, direction, Cw, Mend, hCw, hMend, hdir, hwidth, hdM, hC3, ?_⟩
  exact exists_largeOutput D
    (mergedCombinedConversion D MA NA (analyticKhat D) sourceKh Mend)
    (physicalDefect D)
    (mergedCombinedConversion_nonnegative D sourceKh_nonnegative sourceKh_lt_one)
    hC0 hA hb hgamma_b hCgrowth (physicalDefect_nonneg D)
    (by intro n; simpa [b] using hdexp n) hCw hCjet

/-- Complete recursive scalar start whose single selected tail also satisfies
the uniform jet half bound. -/
theorem exists_jetScalarOutput_of_eps
    {eps0 MA NA Cjet : ℝ}
    (heps : 0 < eps0) (heps10 : eps0 ≤ 1 / 10)
    (hMA : 0 ≤ MA) (hNA : 0 ≤ NA) (hCjet : 0 ≤ Cjet) :
    Nonempty (JetScalarOutput MA NA Cjet) := by
  obtain ⟨E, direction, Cw, Mend, hCw, hMend, hdir, hwidth, hdM, hC3,
    ⟨L⟩⟩ := exists_actualHalf_widthDataC3_and_largeOutput_of_eps
      heps heps10 hMA hNA hCjet
  let Es := shiftActualHalf E L.large.N
  obtain ⟨Q, hQ, ⟨A⟩⟩ :=
    ConfiguredCanonicalPairSourceAutomatic.exists_output_of_cap Es.data
      sourceKh_nonnegative sourceKh_lt_one
      (Es.steering_le_half.trans half_le_sourceKh)
  let scalar : ConfiguredRecursiveSourceP0ScalarStart.Output MA NA :=
    { E := E
      direction := direction
      Cw := Cw
      Mend := Mend
      Cw_nonnegative := hCw
      Mend_positive := hMend
      direction_unit := hdir
      model_width := hwidth
      physicalDefect_lt := hdM
      smooth := hC3
      large := L.large
      Q := Q
      model_data := by simpa [Es] using hQ
      pair := by simpa [Es] using A }
  exact ⟨{ scalar := scalar, jet_half := by simpa [scalar] using L.jet_half }⟩

end ConfiguredRecursiveSourceP0CombinedTailScalar
