import UnitTangentIterates.ConfiguredRecursiveEdgeWeightedEffectiveError
import UnitTangentIterates.SelInvModulusLinear

/-!
# A growth envelope for mixed row/depth conversion constants

The triangular recursion uses the speed floor at `n + k`, but retains the
three flow ceilings of row `n`.  The configured conversion sequence therefore
cannot be used by a monotonicity argument directly.  This file bounds the
row ceilings by their polynomial envelopes at `n + k`, and only then applies
monotonicity of `c2ConstVar`.
-/

noncomputable section

open Real

namespace ConfiguredRecursiveEdgeMixedConversionEnvelope

set_option maxHeartbeats 2000000

open ConstructedConfiguredInductiveTubeBudget.WeightedData
  ConstructedRowCPolynomialGrowth
  ConstructedRowCPolynomialGrowthVariableP0
  ConfiguredRecursiveEdgeSourceP0
  ConfiguredRecursiveEdgeSourceP0Growth
  ConfiguredRecursiveEdgeWeightedEffectiveError
  NormalPathC2IncrementVariableSpeed

private def analyticWeight
    (D : ConstructedConfiguredSequenceWeighted.Data) (gamma : ℝ) (j : ℕ) : ℝ :=
  (1 + D.Hs j) ^ 2 * Real.exp (gamma * D.Hs j)

private theorem analyticWeight_nonnegative
    (D : ConstructedConfiguredSequenceWeighted.Data) (gamma : ℝ) (j : ℕ) :
    0 ≤ analyticWeight D gamma j := by
  exact mul_nonneg (sq_nonneg _) (Real.exp_pos _).le

private theorem analyticWeight_mono
    (D : ConstructedConfiguredSequenceWeighted.Data) {gamma : ℝ}
    (hgamma : 0 ≤ gamma) : Monotone (analyticWeight D gamma) := by
  have hH : Monotone D.Hs :=
    monotone_nat_of_le_succ fun j =>
      (le_add_of_nonneg_right D.deltaStep_pos.le).trans (D.separation_step j)
  intro i j hij
  have hHij := hH hij
  have hbasei : 0 ≤ 1 + D.Hs i := by
    linarith [(D.model.separation_pos i).le]
  have hbase : 1 + D.Hs i ≤ 1 + D.Hs j := by linarith
  have hpow : (1 + D.Hs i) ^ 2 ≤ (1 + D.Hs j) ^ 2 := by
    exact pow_le_pow_left₀ hbasei hbase 2
  have hexp : Real.exp (gamma * D.Hs i) ≤
      Real.exp (gamma * D.Hs j) := by
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hHij hgamma)
  exact mul_le_mul hpow hexp (Real.exp_pos _).le (sq_nonneg _)

private def envelopeValue {H f : ℕ → ℝ}
    (E : PolynomialEnvelope H f) (j : ℕ) : ℝ :=
  E.coeff * (1 + H j) ^ E.degree

private theorem envelopeValue_nonnegative {H f : ℕ → ℝ}
    (hH : ∀ j, 0 ≤ H j) (E : PolynomialEnvelope H f) (j : ℕ) :
    0 ≤ envelopeValue E j := by
  exact mul_nonneg E.coeff_nonneg (pow_nonneg (by linarith [hH j]) _)

private theorem bound_le_envelopeValue_of_le {H f : ℕ → ℝ}
    (hH : Monotone H) (hH0 : ∀ j, 0 ≤ H j)
    (E : PolynomialEnvelope H f) {i j : ℕ} (hij : i ≤ j) :
    f i ≤ envelopeValue E j := by
  calc
    f i ≤ E.coeff * (1 + H i) ^ E.degree := E.bound i
    _ ≤ E.coeff * (1 + H j) ^ E.degree := by
      apply mul_le_mul_of_nonneg_left _ E.coeff_nonneg
      exact pow_le_pow_left₀ (by linarith [hH0 i])
        (by linarith [hH hij]) E.degree
    _ = envelopeValue E j := rfl

/-- A single depth-indexed conversion dominates every mixed row/depth factor
and has the same arbitrarily small exponential growth allowed by the diagonal
argument. -/
theorem exists_mixedConversionEnvelope
    (D : ConstructedConfiguredSequenceWeighted.Data)
    {MA NA khat kh M gamma : ℝ}
    (hMA : 0 ≤ MA) (hNA : 0 ≤ NA) (hkhat : 0 ≤ khat)
    (hkh0 : 0 ≤ kh) (hkh1 : kh < 1) (hM : 0 ≤ M)
    (hgamma : 0 < gamma) :
    ∃ C : ℕ → ℝ, ∃ C0 : ℝ,
      0 ≤ C0 ∧
      (∀ j, 0 ≤ C j) ∧
      (∀ n k,
        c2ConstVar (edgeSourceP0 D (n + k)) (edgeP1 D MA n) khat
            (edgeG1 D MA NA n) (edgeCgWithKhat D khat MA NA n) +
          edgeEndpointConversion D kh M n ≤ C (n + k)) ∧
      ∀ j, C j ≤ C0 * analyticWeight D gamma j := by
  let EP := edgeP1Envelope D hMA
  let EG := edgeG1Envelope D hMA hNA
  let EC := edgeCgWithKhatEnvelope D hkhat hMA hNA
  let Pbar : ℕ → ℝ := envelopeValue EP
  let Gbar : ℕ → ℝ := envelopeValue EG
  let Cbar : ℕ → ℝ := envelopeValue EC
  have hH0 : ∀ j, 0 ≤ D.Hs j := fun j => (D.model.separation_pos j).le
  have hHmono : Monotone D.Hs :=
    monotone_nat_of_le_succ fun j =>
      (le_add_of_nonneg_right D.deltaStep_pos.le).trans (D.separation_step j)
  let hPbar : PolynomialEnvelope D.Hs Pbar :=
    { coeff := EP.coeff
      degree := EP.degree
      coeff_nonneg := EP.coeff_nonneg
      value_nonneg := envelopeValue_nonnegative hH0 EP
      bound := fun _ => le_rfl }
  let hGbar : PolynomialEnvelope D.Hs Gbar :=
    { coeff := EG.coeff
      degree := EG.degree
      coeff_nonneg := EG.coeff_nonneg
      value_nonneg := envelopeValue_nonnegative hH0 EG
      bound := fun _ => le_rfl }
  let hCbar : PolynomialEnvelope D.Hs Cbar :=
    { coeff := EC.coeff
      degree := EC.degree
      coeff_nonneg := EC.coeff_nonneg
      value_nonneg := envelopeValue_nonnegative hH0 EC
      bound := fun _ => le_rfl }
  obtain ⟨A, hA0, hAgrowth⟩ :=
    exists_c2ConstVar_growth_majorant_of_inverseEnvelope hH0
      (edgeSourceP0_pos D) (inverseEdgeSourceP0Envelope D) hPbar
      (ConfiguredRowCeilingPolynomialEnvelopes.constantKhatEnvelope D hkhat)
      hGbar hCbar hgamma
  obtain ⟨B, hB0, hBgrowth⟩ :=
    exists_edgeEndpointConversion_growth_majorant D hkh0 hkh1 hM hgamma
  let C : ℕ → ℝ := fun j =>
    c2ConstVar (edgeSourceP0 D j) (Pbar j) khat (Gbar j) (Cbar j) +
      B * analyticWeight D gamma j
  refine ⟨C, A + B, add_nonneg hA0 hB0, ?_, ?_, ?_⟩
  · intro j
    exact add_nonneg (c2ConstVar_nonneg _ _ _ _ _)
      (mul_nonneg hB0 (analyticWeight_nonnegative D gamma j))
  · intro n k
    have hnj : n ≤ n + k := Nat.le_add_right n k
    have hP : edgeP1 D MA n ≤ Pbar (n + k) :=
      bound_le_envelopeValue_of_le hHmono hH0 EP hnj
    have hG : edgeG1 D MA NA n ≤ Gbar (n + k) :=
      bound_le_envelopeValue_of_le hHmono hH0 EG hnj
    have hC : edgeCgWithKhat D khat MA NA n ≤ Cbar (n + k) :=
      bound_le_envelopeValue_of_le hHmono hH0 EC hnj
    have hc2 := SelInvModulusLinear.c2ConstVar_mono
      (edgeSourceP0_pos D (n + k)).le hkhat
      ((edgeP1Envelope D hMA).value_nonneg n) hP hG hC
    have hend : edgeEndpointConversion D kh M n ≤
        B * analyticWeight D gamma (n + k) := by
      have hn : edgeEndpointConversion D kh M n ≤
          B * analyticWeight D gamma n := by
        simpa [analyticWeight, mul_assoc] using hBgrowth n
      exact hn.trans (mul_le_mul_of_nonneg_left
        (analyticWeight_mono D hgamma.le hnj) hB0)
    exact add_le_add hc2 hend
  · intro j
    calc
      C j ≤ A * analyticWeight D gamma j +
          B * analyticWeight D gamma j := by
            dsimp [C]
            exact add_le_add
              (by simpa [analyticWeight, mul_assoc] using hAgrowth j) le_rfl
      _ = (A + B) * analyticWeight D gamma j := by ring

/-- The exact triangular effective error is summable for every configured
row, without replacing it by the generally nonmonotone edge conversion. -/
theorem summable_effectiveError
    (D : ConstructedConfiguredSequenceWeighted.Data)
    {MA NA khat kh M : ℝ}
    (hMA : 0 ≤ MA) (hNA : 0 ≤ NA) (hkhat : 0 ≤ khat)
    (hkh0 : 0 ≤ kh) (hkh1 : kh < 1) (hM : 0 ≤ M) (n : ℕ) :
    Summable
      (ConfiguredRecursiveEdgeGeometricPresentedDirectLimit.effectiveError
        (P0 := edgeSourceP0 D) (P1 := edgeP1 D MA) (khat := fun _ => khat)
        (G1 := edgeG1 D MA NA) (Cg := edgeCgWithKhat D khat MA NA)
        (edgeEndpointConversion D kh M) (edgePhysicalDefect D) n) := by
  have hbeta : 0 < D.model.beta := (D.model.configs 0).hbeta0
  let gamma : ℝ := D.model.beta / 16
  let b : ℝ := D.model.beta / 8
  have hgamma0 : 0 < gamma := div_pos hbeta (by norm_num)
  have hb : 0 < b := div_pos hbeta (by norm_num)
  have hgamma_b : gamma < b := by dsimp [gamma, b]; linarith
  obtain ⟨C, C0, hC0, hCnonnegative, hfactor, hCgrowth⟩ :=
    exists_mixedConversionEnvelope D hMA hNA hkhat hkh0 hkh1 hM hgamma0
  obtain ⟨A, hA, hddecay⟩ := exists_edgePhysicalDefect_exp_bound D
  have hs : Summable (weightedSequence C (edgePhysicalDefect D)) :=
    summable_weightedSequence_of_growth D C (edgePhysicalDefect D)
      hC0 hA hb hgamma_b hCnonnegative (by
        intro j
        simpa [analyticWeight, mul_assoc] using hCgrowth j)
      (edgePhysicalDefect_nonnegative D) (by
        intro j
        simpa [b] using hddecay j)
  have hnonnegative : ∀ k, 0 ≤
      ConfiguredRecursiveEdgeGeometricPresentedDirectLimit.effectiveError
        (P0 := edgeSourceP0 D) (P1 := edgeP1 D MA) (khat := fun _ => khat)
        (G1 := edgeG1 D MA NA) (Cg := edgeCgWithKhat D khat MA NA)
        (edgeEndpointConversion D kh M) (edgePhysicalDefect D) n k := by
    intro k
    exact mul_nonneg
      (add_nonneg (c2ConstVar_nonneg _ _ _ _ _)
        (edgeEndpointConversion_nonnegative D hkh0 hkh1 n))
      (edgePhysicalDefect_nonnegative D _)
  have hle : ∀ k,
      ConfiguredRecursiveEdgeGeometricPresentedDirectLimit.effectiveError
          (P0 := edgeSourceP0 D) (P1 := edgeP1 D MA) (khat := fun _ => khat)
          (G1 := edgeG1 D MA NA) (Cg := edgeCgWithKhat D khat MA NA)
          (edgeEndpointConversion D kh M) (edgePhysicalDefect D) n k ≤
        weightedError C (edgePhysicalDefect D) 0 n k := by
    intro k
    have hshift : ExponentialDiagonalLargeSeparation.shiftSequence
        (edgePhysicalDefect D) 0 = edgePhysicalDefect D := by
      funext j
      simp [ExponentialDiagonalLargeSeparation.shiftSequence]
    conv_lhs => rw [← hshift]
    exact effectiveError_le_weightedError
      (P0 := edgeSourceP0 D) (P1 := edgeP1 D MA) (khat := fun _ => khat)
      (G1 := edgeG1 D MA NA) (Cg := edgeCgWithKhat D khat MA NA)
      (endpoint := edgeEndpointConversion D kh M) (C := C)
      (d := edgePhysicalDefect D) 0 n k
      (edgePhysicalDefect_nonnegative D) (by
        intro i l
        simpa using hfactor i l)
  exact Summable.of_nonneg_of_le hnonnegative hle
    (weightedError_summable hs 0 n)

/-! ### Canonical scalar package -/

private theorem canonicalEnvelope_exists
    (D : ConstructedConfiguredSequenceWeighted.Data)
    {MA NA khat kh M : ℝ}
    (hMA : 0 ≤ MA) (hNA : 0 ≤ NA) (hkhat : 0 ≤ khat)
    (hkh0 : 0 ≤ kh) (hkh1 : kh < 1) (hM : 0 ≤ M) :
    ∃ C : ℕ → ℝ, ∃ C0 : ℝ,
      0 ≤ C0 ∧
      (∀ j, 0 ≤ C j) ∧
      (∀ n k,
        c2ConstVar (edgeSourceP0 D (n + k)) (edgeP1 D MA n) khat
            (edgeG1 D MA NA n) (edgeCgWithKhat D khat MA NA n) +
          edgeEndpointConversion D kh M n ≤ C (n + k)) ∧
      ∀ j, C j ≤ C0 * analyticWeight D (D.model.beta / 16) j :=
  exists_mixedConversionEnvelope D hMA hNA hkhat hkh0 hkh1 hM
    (div_pos (D.model.configs 0).hbeta0 (by norm_num))

/-- Canonical dominating conversion used by the transition-free configured
capstone. -/
noncomputable def mixedConversion
    (D : ConstructedConfiguredSequenceWeighted.Data)
    (MA NA khat kh M : ℝ)
    (hMA : 0 ≤ MA) (hNA : 0 ≤ NA) (hkhat : 0 ≤ khat)
    (hkh0 : 0 ≤ kh) (hkh1 : kh < 1) (hM : 0 ≤ M) : ℕ → ℝ :=
  Classical.choose (canonicalEnvelope_exists D hMA hNA hkhat hkh0 hkh1 hM)

noncomputable def mixedConversionCoeff
    (D : ConstructedConfiguredSequenceWeighted.Data)
    (MA NA khat kh M : ℝ)
    (hMA : 0 ≤ MA) (hNA : 0 ≤ NA) (hkhat : 0 ≤ khat)
    (hkh0 : 0 ≤ kh) (hkh1 : kh < 1) (hM : 0 ≤ M) : ℝ :=
  Classical.choose (Classical.choose_spec
    (canonicalEnvelope_exists D hMA hNA hkhat hkh0 hkh1 hM))

theorem mixedConversion_spec
    (D : ConstructedConfiguredSequenceWeighted.Data)
    {MA NA khat kh M : ℝ}
    (hMA : 0 ≤ MA) (hNA : 0 ≤ NA) (hkhat : 0 ≤ khat)
    (hkh0 : 0 ≤ kh) (hkh1 : kh < 1) (hM : 0 ≤ M) :
    0 ≤ mixedConversionCoeff D MA NA khat kh M
        hMA hNA hkhat hkh0 hkh1 hM ∧
    (∀ j, 0 ≤ mixedConversion D MA NA khat kh M
      hMA hNA hkhat hkh0 hkh1 hM j) ∧
    (∀ n k,
      c2ConstVar (edgeSourceP0 D (n + k)) (edgeP1 D MA n) khat
          (edgeG1 D MA NA n) (edgeCgWithKhat D khat MA NA n) +
        edgeEndpointConversion D kh M n ≤
      mixedConversion D MA NA khat kh M
        hMA hNA hkhat hkh0 hkh1 hM (n + k)) ∧
    ∀ j, mixedConversion D MA NA khat kh M
        hMA hNA hkhat hkh0 hkh1 hM j ≤
      mixedConversionCoeff D MA NA khat kh M
          hMA hNA hkhat hkh0 hkh1 hM *
        analyticWeight D (D.model.beta / 16) j :=
  Classical.choose_spec (Classical.choose_spec
    (canonicalEnvelope_exists D hMA hNA hkhat hkh0 hkh1 hM))

theorem summable_mixedWeightedSequence
    (D : ConstructedConfiguredSequenceWeighted.Data)
    {MA NA khat kh M : ℝ}
    (hMA : 0 ≤ MA) (hNA : 0 ≤ NA) (hkhat : 0 ≤ khat)
    (hkh0 : 0 ≤ kh) (hkh1 : kh < 1) (hM : 0 ≤ M) :
    Summable (weightedSequence
      (mixedConversion D MA NA khat kh M hMA hNA hkhat hkh0 hkh1 hM)
      (edgePhysicalDefect D)) := by
  let gamma : ℝ := D.model.beta / 16
  let b : ℝ := D.model.beta / 8
  have hbeta : 0 < D.model.beta := (D.model.configs 0).hbeta0
  have hgamma : gamma < b := by dsimp [gamma, b]; linarith
  have hb : 0 < b := div_pos hbeta (by norm_num)
  have hspec := mixedConversion_spec D hMA hNA hkhat hkh0 hkh1 hM
  obtain ⟨A, hA, hddecay⟩ := exists_edgePhysicalDefect_exp_bound D
  exact summable_weightedSequence_of_growth D _ _
    hspec.1 hA hb hgamma hspec.2.1 (by
      intro j
      simpa [gamma, analyticWeight, mul_assoc] using hspec.2.2.2 j)
    (edgePhysicalDefect_nonnegative D) (by
      intro j
      simpa [b] using hddecay j)

/-- The canonical mixed conversion multiplied by the physical defect admits a
fresh large-separation shift.  The output's radius is the full weighted tail. -/
theorem nonempty_mixedWeightedOutput
    (D : ConstructedConfiguredSequenceWeighted.Data)
    {MA NA khat kh M Cw : ℝ}
    (hMA : 0 ≤ MA) (hNA : 0 ≤ NA) (hkhat : 0 ≤ khat)
    (hkh0 : 0 ≤ kh) (hkh1 : kh < 1) (hM : 0 ≤ M) (hCw : 0 ≤ Cw) :
    Nonempty (ExponentialDiagonalLargeSeparation.Output D (fun _ ↦ 1)
      (weightedSequence
        (mixedConversion D MA NA khat kh M hMA hNA hkhat hkh0 hkh1 hM)
        (edgePhysicalDefect D)) Cw) := by
  let C := mixedConversion D MA NA khat kh M hMA hNA hkhat hkh0 hkh1 hM
  have hbetaModel : 0 < D.model.beta := (D.model.configs 0).hbeta0
  let gamma0 : ℝ := D.model.beta / 16
  let b0 : ℝ := D.model.beta / 8
  have hgamma0 : 0 < gamma0 := div_pos hbetaModel (by norm_num)
  have hb0 : 0 < b0 := div_pos hbetaModel (by norm_num)
  have hgamma0b0 : gamma0 < b0 := by dsimp [gamma0, b0]; linarith
  have hspec := mixedConversion_spec D hMA hNA hkhat hkh0 hkh1 hM
  obtain ⟨A, hA, hddecay⟩ := exists_edgePhysicalDefect_exp_bound D
  obtain ⟨beta, K, hbeta, hK, hweightedExp⟩ :=
    exists_weightedSequence_exp_bound_of_growth D C (edgePhysicalDefect D)
      (C0 := mixedConversionCoeff D MA NA khat kh M
        hMA hNA hkhat hkh0 hkh1 hM)
      (A := A) (b := b0) (gamma := gamma0)
      hspec.1 hA hb0 hgamma0b0 hspec.2.1 (by
        intro j
        simpa [C, gamma0, analyticWeight, mul_assoc] using hspec.2.2.2 j)
      (edgePhysicalDefect_nonnegative D) (by
        intro j
        simpa [b0] using hddecay j)
  let gamma : ℝ := beta / 2
  have hgamma : gamma < beta := by dsimp [gamma]; linarith
  apply ExponentialDiagonalLargeSeparation.exists_output D (fun _ ↦ 1)
    (weightedSequence C (edgePhysicalDefect D))
    (fun _ ↦ zero_le_one) zero_le_one hK hbeta hgamma
  · intro j
    have hH : 0 ≤ D.Hs j := (D.model.separation_pos j).le
    have hg0 : 0 ≤ gamma := (half_pos hbeta).le
    have hsquare : 1 ≤ (1 + D.Hs j) ^ 2 := by
      nlinarith [sq_nonneg (D.Hs j)]
    have hexp : 1 ≤ Real.exp (gamma * D.Hs j) := by
      rw [← Real.exp_zero]
      exact Real.exp_le_exp.mpr (mul_nonneg hg0 hH)
    simpa using mul_le_mul hsquare hexp zero_le_one (sq_nonneg (1 + D.Hs j))
  · intro j
    exact mul_nonneg (hspec.2.1 j) (edgePhysicalDefect_nonnegative D (j + 1))
  · exact hweightedExp
  · exact hCw

/-- Canonical large-separation output; downstream construction and closing
theorems can depend on its shift without quantifying any scalar sequence. -/
noncomputable def mixedWeightedOutput
    (D : ConstructedConfiguredSequenceWeighted.Data)
    (MA NA khat kh M Cw : ℝ)
    (hMA : 0 ≤ MA) (hNA : 0 ≤ NA) (hkhat : 0 ≤ khat)
    (hkh0 : 0 ≤ kh) (hkh1 : kh < 1) (hM : 0 ≤ M) (hCw : 0 ≤ Cw) :
    ExponentialDiagonalLargeSeparation.Output D (fun _ ↦ 1)
      (weightedSequence
        (mixedConversion D MA NA khat kh M hMA hNA hkhat hkh0 hkh1 hM)
        (edgePhysicalDefect D)) Cw :=
  Classical.choice
    (nonempty_mixedWeightedOutput D hMA hNA hkhat hkh0 hkh1 hM hCw)

end ConfiguredRecursiveEdgeMixedConversionEnvelope
