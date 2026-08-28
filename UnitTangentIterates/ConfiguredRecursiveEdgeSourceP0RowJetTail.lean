import UnitTangentIterates.ConfiguredRecursiveEdgeSourceP0ScalarStart
import UnitTangentIterates.ConfiguredRecursiveSourceP0RowJetTail

/-! # Common terminal-jet tail for the edge-indexed scalar output -/

noncomputable section

open Set MarkedSpace

namespace ConfiguredRecursiveEdgeSourceP0RowJetTail

open Filter
  ConfiguredCombinedPhysicalDiagonalLargeSeparation
  ConfiguredPolynomialDiagonalStableRowDefectProvider
  ConfiguredRecursiveEdgeSourceP0Growth
  ConfiguredRecursiveSourceP0RowJetTail
  ConstructedRowCPolynomialGrowth
  ConstructedConfiguredInductiveTubeBudget.WeightedData

def edgeRowEps (D : ConstructedConfiguredSequenceWeighted.Data)
    (M : ℝ) (n k : ℕ) : ℝ :=
  rowJetCoeff D M (n + k + 1) *
    edgePhysicalDefect D (n + k)

theorem edgeRowEps_shift
    (D : ConstructedConfiguredSequenceWeighted.Data)
    (M : ℝ) (N n k : ℕ) :
    edgeRowEps (shift D N) M n k = edgeRowEps D M (N + n) k := by
  unfold edgeRowEps
  simp only [edgePhysicalDefect, physicalDefect]
  rw [show ConfiguredApproximateDefectPathRowwise.rowDefect
      (shift D N) (n + k) =
      ConfiguredApproximateDefectPathRowwise.rowDefect D (N + (n + k)) from rfl]
  simp [physicalCoeff, rowJetCoeff, ellCap, shift, Nat.add_assoc]

theorem exists_shift_edgeRowEps_le_half
    (D : ConstructedConfiguredSequenceWeighted.Data) (M : ℝ) :
    ∃ N, ∀ n k, edgeRowEps (shift D N) M n k ≤ 1 / 2 := by
  let hjet := nextEnvelope D (rowJetCoeffEnvelope D M)
  let hphysical := physicalCoeffEnvelope D
  have hcoeff : PolynomialEnvelope D.Hs (fun j ↦
      rowJetCoeff D M (j + 1) * physicalCoeff D j) :=
    { coeff := hjet.coeff * hphysical.coeff
      degree := hjet.degree + hphysical.degree
      coeff_nonneg := mul_nonneg hjet.coeff_nonneg hphysical.coeff_nonneg
      value_nonneg := fun j ↦ mul_nonneg (hjet.value_nonneg j)
        (hphysical.value_nonneg j)
      bound := fun j ↦ by
        calc
          rowJetCoeff D M (j + 1) * physicalCoeff D j ≤
              (hjet.coeff * (1 + D.Hs j) ^ hjet.degree) *
                (hphysical.coeff * (1 + D.Hs j) ^ hphysical.degree) := by
            exact mul_le_mul (hjet.bound j) (hphysical.bound j)
              (hphysical.value_nonneg j)
              (mul_nonneg hjet.coeff_nonneg
                (pow_nonneg (by linarith [D.model.separation_pos j]) _))
          _ = (hjet.coeff * hphysical.coeff) *
              (1 + D.Hs j) ^ (hjet.degree + hphysical.degree) := by
            rw [pow_add]
            ring }
  have hsum : Summable (fun j ↦
      rowJetCoeff D M (j + 1) *
        edgePhysicalDefect D j) := by
    simpa [edgePhysicalDefect, physicalDefect, mul_assoc] using
      (summable_polynomial_mul_rowDefect D hcoeff)
  have ht := hsum.tendsto_atTop_zero
  have he := ht.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 he
  refine ⟨N, ?_⟩
  intro n k
  have H := hN (N + (n + k)) (Nat.le_add_right N (n + k))
  simpa [edgeRowEps, edgePhysicalDefect, physicalDefect, physicalCoeff,
    rowJetCoeff, ellCap, shift, Nat.add_assoc] using H.le

structure RowJetScalarOutput (MA NA : ℝ) where
  scalar : ConfiguredRecursiveEdgeSourceP0ScalarStart.Output MA NA
  one_le_Mend : 1 ≤ scalar.Mend
  jet_half : ∀ n k,
    edgeRowEps (shift scalar.E.data scalar.large.N) scalar.Mend n k ≤ 1 / 2
  composition_mass_one : ∀ n,
    edgeCompositionPhysicalDefect
      (shift scalar.E.data scalar.large.N) n ≤ 1
  composition_scaled_mass_one : ∀ n j, n ≤ j →
    edgeCompositionCoeff (shift scalar.E.data scalar.large.N) n /
        Real.sqrt (1 - sourceKh ^ 2) *
      edgeCompositionPhysicalDefect
        (shift scalar.E.data scalar.large.N) j ≤ 1

theorem exists_rowJetScalarOutput_of_eps
    {eps0 MA NA : ℝ} (heps : 0 < eps0) (heps10 : eps0 ≤ 1 / 10)
    (hMA : 0 ≤ MA) (hNA : 0 ≤ NA) :
    Nonempty (RowJetScalarOutput MA NA) := by
  obtain ⟨E, direction, Cw, hCw, hdir, hwidth, hC3⟩ :=
    ConstructedPulseWidth.exists_actualHalf_widthDataC3_of_eps heps heps10
  let D := E.data
  have hbeta : 0 < D.model.beta := (D.model.configs 0).hbeta0
  let b : ℝ := D.model.beta / 8
  have hb : 0 < b := div_pos hbeta (by norm_num)
  obtain ⟨A, hA, hedgeExp⟩ := exists_edgePhysicalDefect_exp_bound D
  let Mend : ℝ := A * Real.exp (-(b * D.Hs 0)) + 1
  have hMend : 0 < Mend := by dsimp [Mend]; positivity
  have hdM : ∀ n, edgePhysicalDefect D n < Mend := by
    intro n
    have harg : -(b * D.Hs n) ≤ -(b * D.Hs 0) := by
      have hm := mul_le_mul_of_nonneg_left (D.separation_lower n) hb.le
      linarith
    calc
      edgePhysicalDefect D n ≤ A * Real.exp (-(b * D.Hs n)) := hedgeExp n
      _ ≤ A * Real.exp (-(b * D.Hs 0)) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr harg) hA
      _ < Mend := by dsimp [Mend]; linarith
  obtain ⟨Njet, hjet⟩ :=
    exists_shift_edgeRowEps_le_half D Mend
  obtain ⟨Ncomp, hcomp⟩ :=
    exists_edgeCompositionPhysicalDefect_tail_le_one D
  obtain ⟨Nmass, hmass⟩ :=
    exists_edgeComposition_scaled_mass_tail_le_one D
  let N0 : ℕ := Njet + Ncomp + Nmass
  let Es := shiftActualHalf E N0
  let Ds := Es.data
  let CwRear := Cw + 2
  have hCwRear : 0 ≤ CwRear := by dsimp [CwRear]; linarith
  have hbetaS : 0 < Ds.model.beta := (Ds.model.configs 0).hbeta0
  let gammaS : ℝ := Ds.model.beta / 16
  let bS : ℝ := Ds.model.beta / 8
  have hbS : 0 < bS := div_pos hbetaS (by norm_num)
  have hgammaS_bS : gammaS < bS := by dsimp [gammaS, bS]; nlinarith
  obtain ⟨AS, hAS, hedgeExpS⟩ := exists_edgePhysicalDefect_exp_bound Ds
  obtain ⟨C0, hC0, hCgrowth⟩ :=
    exists_edgeCombinedConversion_growth_majorant Ds hMA hNA
      (analyticKhat_nonnegative Ds) sourceKh_nonnegative sourceKh_lt_one
      hMend.le (div_pos hbetaS (by norm_num : (0 : ℝ) < 16))
  obtain ⟨L⟩ := ExponentialDiagonalLargeSeparation.exists_output Ds
    (edgeCombinedConversion Ds MA NA (analyticKhat Ds) sourceKh Mend)
    (edgePhysicalDefect Ds)
    (edgeCombinedConversion_nonnegative Ds sourceKh_nonnegative sourceKh_lt_one)
    hC0 hAS hbS hgammaS_bS hCgrowth (edgePhysicalDefect_nonnegative Ds)
    (by intro n; simpa [bS] using hedgeExpS n) hCwRear
  let Ef := shiftActualHalf Es L.N
  obtain ⟨Q, hQ, ⟨Pair⟩⟩ :=
    ConfiguredCanonicalPairSourceAutomatic.exists_output_of_cap Ef.data
      sourceKh_nonnegative sourceKh_lt_one
      (Ef.steering_le_half.trans half_le_sourceKh)
  let directionS : ℕ → ℂ := fun n ↦ direction (N0 + n)
  let scalar : ConfiguredRecursiveEdgeSourceP0ScalarStart.Output MA NA :=
    { E := Es
      direction := directionS
      Cw := CwRear
      Mend := Mend
      Cw_nonnegative := hCwRear
      Mend_positive := hMend
      direction_unit := fun n ↦ hdir (N0 + n)
      model_width := fun n ↦ by
        have H := hwidth (N0 + n)
        simpa [CwRear, directionS, Es, Ds, shiftActualHalf, shift] using
          H.trans (by linarith : Cw ≤ Cw + 2)
      model_width_add_two := fun n ↦ by
        have H := hwidth (N0 + n)
        simpa [CwRear, directionS, Es, Ds, shiftActualHalf, shift] using
          (by linarith [H] :
            Width.width
              (range (TwoCapPairsAssembly.front (D.kappas (N0 + n))
                D.model.thetaBase (D.Hs (N0 + n)))) (direction (N0 + n)) + 2 ≤
              Cw + 2)
      physicalDefect_lt := fun n ↦ by
        simpa [Es, Ds, shiftActualHalf, shift, edgePhysicalDefect,
          Nat.add_assoc] using hdM (N0 + n)
      smooth := hC3.shift N0
      large := L
      Q := Q
      model_data := by simpa [Ef] using hQ
      pair := by simpa [Ef] using Pair }
  refine ⟨{
    scalar := scalar
    one_le_Mend := by
      dsimp [scalar, Mend]
      have h : 0 ≤ A * Real.exp (-(b * D.Hs 0)) :=
        mul_nonneg hA (Real.exp_pos _).le
      linarith
    jet_half := ?_
    composition_mass_one := ?_
    composition_scaled_mass_one := ?_ }⟩
  · intro n k
    change edgeRowEps (shift Ds L.N) Mend n k ≤ 1 / 2
    rw [edgeRowEps_shift]
    have hj := hjet ((Ncomp + Nmass) + (L.N + n)) k
    rw [edgeRowEps_shift] at hj
    change edgeRowEps (shift D N0) Mend (L.N + n) k ≤ 1 / 2
    rw [edgeRowEps_shift]
    simpa [Ds, Es, N0, shiftActualHalf, Nat.add_assoc] using hj
  · intro n
    rw [edgeCompositionPhysicalDefect_shift]
    apply hcomp (N0 + (L.N + n))
    dsimp [N0]
    omega
  · intro n j hnj
    rw [edgeCompositionCoeff_shift, edgeCompositionPhysicalDefect_shift]
    apply hmass (N0 + (L.N + n)) (N0 + (L.N + j))
    · dsimp [N0]
      omega
    · omega

theorem exists_fixed_rowJetScalarOutput_of_eps
    {eps0 : ℝ} (heps : 0 < eps0) (heps10 : eps0 ≤ 1 / 10) :
    Nonempty (RowJetScalarOutput
      ConfiguredRecursiveSourceP0FixedDistortion.choice.MA0
      ConfiguredRecursiveSourceP0FixedDistortion.choice.NA0) :=
  exists_rowJetScalarOutput_of_eps heps heps10
    ConfiguredRecursiveSourceP0FixedDistortion.choice.MA0_nonnegative
    ConfiguredRecursiveSourceP0FixedDistortion.choice.NA0_nonnegative

/-- The final scalar shift preserves the global physical-defect cap. -/
theorem RowJetScalarOutput.physicalDefect_le
    {MA NA : ℝ} (J : RowJetScalarOutput MA NA) (j : ℕ) :
    edgePhysicalDefect (shift J.scalar.E.data J.scalar.large.N) j ≤
      J.scalar.Mend := by
  have h := (J.scalar.physicalDefect_lt (J.scalar.large.N + j)).le
  simpa [edgePhysicalDefect, physicalDefect, physicalCoeff, shift,
    ConfiguredApproximateDefectPathRowwise.rowDefect, Nat.add_assoc] using h

end ConfiguredRecursiveEdgeSourceP0RowJetTail
