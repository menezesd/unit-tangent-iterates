import UnitTangentIterates.ConfiguredRecursiveSourceP0ChosenJetMajorants
import UnitTangentIterates.ConfiguredPolynomialDiagonalStableRowDefectProvider
import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareDirectSuccessor

/-!
# Polynomial row ceilings for chosen terminal jet errors

The normalized second marking jet contains `ell^2 / L`.  With the retained
configured estimates `ell = O(1 + H_n)` and `L >= 1`, its sound ceiling is
quadratic in the row separation, not a global constant.  Exponential decay of
the configured row defect absorbs this polynomial coefficient.
-/

noncomputable section

open Filter MarkedSpace PathMetric

namespace ConfiguredRecursiveSourceP0RowJetTail

open ConfiguredApproximateDefectPathRowwise
  ConfiguredCombinedPhysicalDiagonalLargeSeparation
  ConfiguredGaugeJetDistortion
  ConfiguredPolynomialDiagonalStableRowDefectProvider
  ConfiguredRecursiveSourceP0ChosenJetMajorants
  ConfiguredRecursiveSourceP0Growth
  ConstructedConfiguredInductiveTubeBudget.WeightedData
  ConstructedRowCPolynomialGrowth
  ExponentialDiagonalLargeSeparation
  FiniteSmoothRearFamilyMarkingAwareAppliedSource
  FiniteSmoothRearFamilyMarkingAwareChosenTerminal
  FiniteSmoothRearFamilyMarkingAwareCorrelatedRecursion
  FiniteSmoothRearFamilyMarkingAwareDirectSuccessor
  FiniteSmoothRearFamilyMarkingAwareSource
  GaugeMarkedDataOfRearFamily
  GaugeTerminalNearIdentityJets

/-- Quadratic row ceiling for the normalized first and second terminal
marking jets. -/
def rowJetCoeff (D : ConstructedConfiguredSequenceWeighted.Data)
    (M : ℝ) (n : ℕ) : ℝ :=
  max
    (ellCap D n * rearKappa1 sourceKh *
      (Real.exp (rearKappa1 sourceKh * M) + 1))
    ((ellCap D n) ^ 2 * Real.exp (2 * rearKappa1 sourceKh * M) *
      rearKappa2 sourceKh)

theorem rowJetCoeff_nonnegative
    (D : ConstructedConfiguredSequenceWeighted.Data) (M : ℝ) (n : ℕ) :
    0 ≤ rowJetCoeff D M n := by
  apply le_max_of_le_left
  have hcap : 0 ≤ ellCap D n := by
    unfold ellCap
    exact mul_nonneg (by norm_num)
      (add_nonneg zero_le_one (D.model.separation_pos n).le)
  exact mul_nonneg
    (mul_nonneg
      hcap
      (rearKappa1_nonneg sourceKh_nonnegative sourceKh_lt_one))
    (add_nonneg (Real.exp_pos _).le zero_le_one)

theorem rowJetCoeff_mono_add
    (D : ConstructedConfiguredSequenceWeighted.Data) (M : ℝ) (n k : ℕ) :
    rowJetCoeff D M n ≤ rowJetCoeff D M (n + k) := by
  have hHs : Monotone D.Hs :=
    monotone_nat_of_le_succ fun j ↦
      (le_add_of_nonneg_right D.deltaStep_pos.le).trans
        (D.separation_step j)
  have hH := hHs (Nat.le_add_right n k)
  have hcap : ellCap D n ≤ ellCap D (n + k) := by
    unfold ellCap
    linarith
  have hcap0 : 0 ≤ ellCap D n := by
    unfold ellCap
    exact mul_nonneg (by norm_num)
      (add_nonneg zero_le_one (D.model.separation_pos n).le)
  have hcap0' : 0 ≤ ellCap D (n + k) := by
    unfold ellCap
    exact mul_nonneg (by norm_num)
      (add_nonneg zero_le_one (D.model.separation_pos (n + k)).le)
  have hk1 := rearKappa1_nonneg sourceKh_nonnegative sourceKh_lt_one
  have hk2 := rearKappa2_nonneg sourceKh_nonnegative sourceKh_lt_one
  unfold rowJetCoeff
  apply max_le
  · apply (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hcap hk1)
      (add_nonneg (Real.exp_pos _).le zero_le_one)).trans
    exact le_max_left _ _
  · have hsq : ellCap D n ^ 2 ≤ ellCap D (n + k) ^ 2 :=
      (sq_le_sq₀ hcap0 hcap0').2 hcap
    apply (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hsq (Real.exp_pos _).le) hk2).trans
    exact le_max_right _ _

def rowJetCoeffEnvelope
    (D : ConstructedConfiguredSequenceWeighted.Data) (M : ℝ) :
    PolynomialEnvelope D.Hs (rowJetCoeff D M) where
  coeff :=
    3 * rearKappa1 sourceKh *
        (Real.exp (rearKappa1 sourceKh * M) + 1) +
      9 * Real.exp (2 * rearKappa1 sourceKh * M) * rearKappa2 sourceKh
  degree := 2
  coeff_nonneg := by
    exact add_nonneg
      (mul_nonneg
        (mul_nonneg (by norm_num)
          (rearKappa1_nonneg sourceKh_nonnegative sourceKh_lt_one))
        (add_nonneg (Real.exp_pos _).le zero_le_one))
      (mul_nonneg
        (mul_nonneg (by norm_num) (Real.exp_pos _).le)
        (rearKappa2_nonneg sourceKh_nonnegative sourceKh_lt_one))
  value_nonneg := rowJetCoeff_nonnegative D M
  bound n := by
    let z : ℝ := 1 + D.Hs n
    have hz1 : 1 ≤ z := by
      dsimp [z]
      linarith [(D.model.separation_pos n).le]
    have hz0 : 0 ≤ z := zero_le_one.trans hz1
    have hk1 := rearKappa1_nonneg sourceKh_nonnegative sourceKh_lt_one
    have hk2 := rearKappa2_nonneg sourceKh_nonnegative sourceKh_lt_one
    unfold rowJetCoeff ellCap
    apply max_le
    · have hterm : 0 ≤ 3 * rearKappa1 sourceKh *
          (Real.exp (rearKappa1 sourceKh * M) + 1) := by positivity
      calc
        3 * z * rearKappa1 sourceKh *
            (Real.exp (rearKappa1 sourceKh * M) + 1) =
            (3 * rearKappa1 sourceKh *
              (Real.exp (rearKappa1 sourceKh * M) + 1)) * z := by ring
        _ ≤ (3 * rearKappa1 sourceKh *
              (Real.exp (rearKappa1 sourceKh * M) + 1)) * z ^ 2 :=
          mul_le_mul_of_nonneg_left (by nlinarith [sq_nonneg (z - 1)]) hterm
        _ ≤ (3 * rearKappa1 sourceKh *
              (Real.exp (rearKappa1 sourceKh * M) + 1) +
            9 * Real.exp (2 * rearKappa1 sourceKh * M) *
              rearKappa2 sourceKh) * z ^ 2 := by
          exact mul_le_mul_of_nonneg_right
            (le_add_of_nonneg_right
              (mul_nonneg
                (mul_nonneg (by norm_num) (Real.exp_pos _).le) hk2))
            (sq_nonneg z)
    · calc
        (3 * z) ^ 2 * Real.exp (2 * rearKappa1 sourceKh * M) *
            rearKappa2 sourceKh =
            (9 * Real.exp (2 * rearKappa1 sourceKh * M) *
              rearKappa2 sourceKh) * z ^ 2 := by ring
        _ ≤ (3 * rearKappa1 sourceKh *
              (Real.exp (rearKappa1 sourceKh * M) + 1) +
            9 * Real.exp (2 * rearKappa1 sourceKh * M) *
              rearKappa2 sourceKh) * z ^ 2 := by
          exact mul_le_mul_of_nonneg_right
            (le_add_of_nonneg_left
              (mul_nonneg
                (mul_nonneg (by norm_num) hk1)
                (add_nonneg (Real.exp_pos _).le zero_le_one)))
            (sq_nonneg z)

/-- Row/depth error using the coefficient at the diagonal index.  This choice
makes shift compatibility exact and dominates the coefficient at row `n`. -/
def rowEps (D : ConstructedConfiguredSequenceWeighted.Data)
    (M : ℝ) (n k : ℕ) : ℝ :=
  rowJetCoeff D M (n + k) * rowDefect D (n + k)

theorem rowEps_nonnegative
    (D : ConstructedConfiguredSequenceWeighted.Data) (M : ℝ) (n k : ℕ) :
  0 ≤ rowEps D M n k :=
  mul_nonneg (rowJetCoeff_nonnegative D M (n + k))
    (ConstructedRowDefectLargeSeparation.rowDefect_nonneg D (n + k))

theorem rowEps_shift
    (D : ConstructedConfiguredSequenceWeighted.Data) (M : ℝ) (N n k : ℕ) :
    rowEps (shift D N) M n k = rowEps D M (N + n) k := by
  unfold rowEps
  rw [show ConfiguredApproximateDefectPathRowwise.rowDefect
      (shift D N) (n + k) =
      ConfiguredApproximateDefectPathRowwise.rowDefect D (N + (n + k)) from rfl]
  simp [rowJetCoeff, ellCap, shift, Nat.add_assoc]

theorem exists_shift_rowEps_le_half
    (D : ConstructedConfiguredSequenceWeighted.Data) (M : ℝ) :
    ∃ N, ∀ n k, rowEps (shift D N) M n k ≤ 1 / 2 := by
  have hsum : Summable (fun j ↦ rowJetCoeff D M j * rowDefect D j) :=
    summable_polynomial_mul_rowDefect D (rowJetCoeffEnvelope D M)
  have ht := hsum.tendsto_atTop_zero
  have he := ht.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 he
  refine ⟨N, ?_⟩
  intro n k
  have H := hN (N + (n + k)) (Nat.le_add_right N (n + k))
  simpa [rowEps, rowJetCoeff, ellCap,
    ConstructedRowDefectLargeSeparation.rowDefect_shift, Nat.add_assoc] using H.le

/-- The configured row ceiling dominates the actual terminal coefficient.
The only additional selected-terminal datum is the natural lower perimeter
bound `1 <= perim base`. -/
theorem jetLinearConst_le_rowJetCoeff
    (D : ConstructedConfiguredSequenceWeighted.Data) (M : ℝ) (n : ℕ)
    {ell L : ℝ}
    (hell0 : 0 ≤ ell) (hell : ell ≤ ellCap D n) (hL : 1 ≤ L) :
    jetLinearConst ell L (rearKappa1 sourceKh) (rearKappa2 sourceKh) M ≤
      rowJetCoeff D M n := by
  have hLpos : 0 < L := zero_lt_one.trans_le hL
  have hcap0 : 0 ≤ ellCap D n := by
    unfold ellCap
    exact mul_nonneg (by norm_num)
      (add_nonneg zero_le_one (D.model.separation_pos n).le)
  have hk1 := rearKappa1_nonneg sourceKh_nonnegative sourceKh_lt_one
  have hk2 := rearKappa2_nonneg sourceKh_nonnegative sourceKh_lt_one
  unfold jetLinearConst rowJetCoeff
  apply max_le
  · apply (div_le_iff₀ hLpos).2
    have hnum : ell * rearKappa1 sourceKh *
        (Real.exp (rearKappa1 sourceKh * M) + 1) ≤
        ellCap D n * rearKappa1 sourceKh *
          (Real.exp (rearKappa1 sourceKh * M) + 1) := by
      gcongr
    have htarget : 0 ≤ ellCap D n * rearKappa1 sourceKh *
        (Real.exp (rearKappa1 sourceKh * M) + 1) := by positivity
    have hmax : ellCap D n * rearKappa1 sourceKh *
        (Real.exp (rearKappa1 sourceKh * M) + 1) ≤
        max
          (ellCap D n * rearKappa1 sourceKh *
            (Real.exp (rearKappa1 sourceKh * M) + 1))
          ((ellCap D n) ^ 2 * Real.exp (2 * rearKappa1 sourceKh * M) *
            rearKappa2 sourceKh) := le_max_left _ _
    have hcoeff0 : 0 ≤ max
          (ellCap D n * rearKappa1 sourceKh *
            (Real.exp (rearKappa1 sourceKh * M) + 1))
          ((ellCap D n) ^ 2 * Real.exp (2 * rearKappa1 sourceKh * M) *
            rearKappa2 sourceKh) := le_max_of_le_left htarget
    exact hnum.trans (hmax.trans (by nlinarith))
  · apply (div_le_iff₀ hLpos).2
    have hsq : ell ^ 2 ≤ (ellCap D n) ^ 2 :=
      (sq_le_sq₀ hell0 hcap0).2 hell
    have hnum : ell ^ 2 * Real.exp (2 * rearKappa1 sourceKh * M) *
        rearKappa2 sourceKh ≤
        (ellCap D n) ^ 2 * Real.exp (2 * rearKappa1 sourceKh * M) *
          rearKappa2 sourceKh := by gcongr
    have htarget : 0 ≤ (ellCap D n) ^ 2 *
        Real.exp (2 * rearKappa1 sourceKh * M) * rearKappa2 sourceKh := by
      positivity
    have hmax : (ellCap D n) ^ 2 *
          Real.exp (2 * rearKappa1 sourceKh * M) * rearKappa2 sourceKh ≤
        max
          (ellCap D n * rearKappa1 sourceKh *
            (Real.exp (rearKappa1 sourceKh * M) + 1))
          ((ellCap D n) ^ 2 * Real.exp (2 * rearKappa1 sourceKh * M) *
            rearKappa2 sourceKh) := le_max_right _ _
    have hcoeff0 : 0 ≤ max
          (ellCap D n * rearKappa1 sourceKh *
            (Real.exp (rearKappa1 sourceKh * M) + 1))
          ((ellCap D n) ^ 2 * Real.exp (2 * rearKappa1 sourceKh * M) *
            rearKappa2 sourceKh) := le_max_of_le_right htarget
    exact hnum.trans (hmax.trans (by nlinarith))

/-- Exact provider-side certificate needed to put one chosen terminal under
the polynomial row jet tail. -/
structure ChosenCertificate
    {a b p base : Data} {Gamma : NormalPath a b}
    {P0 kh khat Qmax bound : ℝ}
    {A : MarkingAwareSource Gamma P0 kh khat Qmax}
    {E : Applied Gamma A}
    {B : TerminalInput (p := p) (base := base) (bound := bound) E}
    (O : Output E B)
    (D : ConstructedConfiguredSequenceWeighted.Data) (M : ℝ) (n k : ℕ) :
    Prop where
  kh_eq : kh = sourceKh
  qmax_le : Qmax ≤ ellCap D n
  terminal_perim_ge_one : 1 ≤ perim base
  cost_le : O.chosen.Delta.cost ≤ rowDefect D (n + k)
  defect_le : rowDefect D (n + k) ≤ M

theorem ChosenCertificate.jetError_le_rowEps
    {a b p base : Data} {Gamma : NormalPath a b}
    {P0 kh khat Qmax bound : ℝ}
    {A : MarkingAwareSource Gamma P0 kh khat Qmax}
    {E : Applied Gamma A}
    {B : TerminalInput (p := p) (base := base) (bound := bound) E}
    {O : Output E B}
    {D : ConstructedConfiguredSequenceWeighted.Data} {M : ℝ} {n k : ℕ}
    (R : ChosenCertificate O D M n k) :
    O.jetError ≤ rowEps D M n k := by
  have hell0 := (A.rear_period_pos 0).le
  have hell : rearPeriod A 0 ≤ ellCap D n :=
    (A.rear_period_le 0).trans R.qmax_le
  have hcoeff : jetLinearConst (rearPeriod A 0) (perim base)
      (rearKappa1 kh) (rearKappa2 kh) M ≤ rowJetCoeff D M n := by
    simpa only [R.kh_eq] using
      jetLinearConst_le_rowJetCoeff D M n hell0 hell
        R.terminal_perim_ge_one
  have H := O.jetError_le_configured_eps D n k R.cost_le R.defect_le hcoeff
  exact H.trans (mul_le_mul_of_nonneg_right
    (rowJetCoeff_mono_add D M n k)
    (ConstructedRowDefectLargeSeparation.rowDefect_nonneg D (n + k)))

/-- Recursive scalar output carrying the polynomial row jet tail selected at
the same index as all large-separation conclusions. -/
structure RowJetScalarOutput (MA NA : ℝ) where
  scalar : ConfiguredRecursiveSourceP0ScalarStart.Output MA NA
  jet_half : ∀ n k,
    rowEps (shift scalar.E.data scalar.large.N) scalar.Mend n k ≤ 1 / 2

/-- Construct the scalar output only after choosing the polynomial row-jet
tail, so its opaque width-gap certificate is retained at the same index. -/
theorem exists_rowJetScalarOutput_of_eps
    {eps0 MA NA : ℝ} (heps : 0 < eps0) (heps10 : eps0 ≤ 1 / 10)
    (hMA : 0 ≤ MA) (hNA : 0 ≤ NA) :
    Nonempty (RowJetScalarOutput MA NA) := by
  obtain ⟨E, direction, Cw, hCw, hdir, hwidth, hC3⟩ :=
    ConstructedPulseWidth.exists_actualHalf_widthDataC3_of_eps heps heps10
  let D := E.data
  have hbeta : 0 < D.model.beta := (D.model.configs 0).hbeta0
  let gamma : ℝ := D.model.beta / 16
  let b : ℝ := D.model.beta / 8
  have hb : 0 < b := div_pos hbeta (by norm_num)
  have hgamma_b : gamma < b := by dsimp [gamma, b]; nlinarith
  obtain ⟨A, hA, hdexp⟩ := exists_physicalDefect_exp_bound D
  let Mend : ℝ := A * Real.exp (-(b * D.Hs 0)) + 1
  have hMend : 0 < Mend := by dsimp [Mend]; positivity
  have hdM : ∀ n, physicalDefect D n < Mend := by
    intro n
    have harg : -(b * D.Hs n) ≤ -(b * D.Hs 0) := by
      have hm := mul_le_mul_of_nonneg_left (D.separation_lower n) hb.le
      linarith
    calc
      physicalDefect D n ≤ A * Real.exp (-(b * D.Hs n)) := by
        simpa [b] using hdexp n
      _ ≤ A * Real.exp (-(b * D.Hs 0)) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr harg) hA
      _ < Mend := by dsimp [Mend]; linarith
  obtain ⟨N0, hjet⟩ := exists_shift_rowEps_le_half D Mend
  let Es := shiftActualHalf E N0
  let Ds := Es.data
  have hbetaS : 0 < Ds.model.beta := (Ds.model.configs 0).hbeta0
  let gammaS : ℝ := Ds.model.beta / 16
  let bS : ℝ := Ds.model.beta / 8
  have hbS : 0 < bS := div_pos hbetaS (by norm_num)
  have hgammaS_bS : gammaS < bS := by dsimp [gammaS, bS]; nlinarith
  obtain ⟨AS, hAS, hdexpS⟩ := exists_physicalDefect_exp_bound Ds
  obtain ⟨C0, hC0, hCgrowth⟩ :=
    exists_mergedCombinedConversion_growth_majorant Ds hMA hNA
      (analyticKhat_nonnegative Ds) sourceKh_nonnegative sourceKh_lt_one
      hMend.le (div_pos hbetaS (by norm_num : (0 : ℝ) < 16))
  obtain ⟨L⟩ := ExponentialDiagonalLargeSeparation.exists_output Ds
    (mergedCombinedConversion Ds MA NA (analyticKhat Ds) sourceKh Mend)
    (physicalDefect Ds)
    (mergedCombinedConversion_nonnegative Ds sourceKh_nonnegative sourceKh_lt_one)
    hC0 hAS hbS hgammaS_bS hCgrowth (physicalDefect_nonneg Ds)
    (by intro n; simpa [bS] using hdexpS n) hCw
  let Ef := shiftActualHalf Es L.N
  obtain ⟨Q, hQ, ⟨Pair⟩⟩ :=
    ConfiguredCanonicalPairSourceAutomatic.exists_output_of_cap Ef.data
      sourceKh_nonnegative sourceKh_lt_one
      (Ef.steering_le_half.trans half_le_sourceKh)
  let directionS : ℕ → ℂ := fun n ↦ direction (N0 + n)
  let scalar : ConfiguredRecursiveSourceP0ScalarStart.Output MA NA :=
    { E := Es
      direction := directionS
      Cw := Cw
      Mend := Mend
      Cw_nonnegative := hCw
      Mend_positive := hMend
      direction_unit := fun n ↦ hdir (N0 + n)
      model_width := fun n ↦ by
        simpa [directionS, Es, Ds, shiftActualHalf, shift] using hwidth (N0 + n)
      physicalDefect_lt := fun n ↦ by
        simpa [Es, Ds, shiftActualHalf, shift] using hdM (N0 + n)
      smooth := hC3.shift N0
      large := L
      Q := Q
      model_data := by simpa [Ef] using hQ
      pair := by simpa [Ef] using Pair }
  refine ⟨{ scalar := scalar, jet_half := ?_ }⟩
  intro n k
  change rowEps (shift Ds L.N) Mend n k ≤ 1 / 2
  rw [rowEps_shift]
  simpa [Ds, Es, shiftActualHalf] using hjet (L.N + n) k

theorem exists_fixed_rowJetScalarOutput_of_eps
    {eps0 : ℝ} (heps : 0 < eps0) (heps10 : eps0 ≤ 1 / 10) :
    Nonempty (RowJetScalarOutput
      ConfiguredRecursiveSourceP0FixedDistortion.choice.MA0
      ConfiguredRecursiveSourceP0FixedDistortion.choice.NA0) :=
  exists_rowJetScalarOutput_of_eps heps heps10
    ConfiguredRecursiveSourceP0FixedDistortion.choice.MA0_nonnegative
    ConfiguredRecursiveSourceP0FixedDistortion.choice.NA0_nonnegative

/-- Consume the common scalar tail and one exact chosen-terminal certificate
to obtain the fixed recursive analytic ceilings. -/
theorem ChosenCertificate.nearIdentity_majorants_of_scalar
    {MA NA : ℝ} (S : RowJetScalarOutput MA NA)
    {a b p base : Data} {Gamma : NormalPath a b}
    {P0 kh khat Qmax bound : ℝ}
    {A : MarkingAwareSource Gamma P0 kh khat Qmax}
    {E : Applied Gamma A}
    {B : TerminalInput (p := p) (base := base) (bound := bound) E}
    {O : Output E B} {n k : ℕ}
    (R : ChosenCertificate O
      (shift S.scalar.E.data S.scalar.large.N) S.scalar.Mend n k)
    {rawP1 rawG1 rawCg : ℝ}
    (hkhat : 0 ≤ khat)
    (hP0 : 0 ≤ rawP1) (hG0 : 0 ≤ rawG1) (hCg0 : 0 ≤ rawCg)
    (hP : rawP1 ≤ rowP1 (shift S.scalar.E.data S.scalar.large.N) n)
    (hG : rawG1 ≤ rowG1 (shift S.scalar.E.data S.scalar.large.N) n)
    (hCg : rawCg ≤ rowCg (shift S.scalar.E.data S.scalar.large.N) n) :
    rawP1 * (1 + O.jetError) ≤
        ConfiguredRowCeilingPolynomialEnvelopes.wideP1
          (shift S.scalar.E.data S.scalar.large.N)
          ConfiguredRecursiveSourceP0FixedDistortion.choice.MA0 n ∧
      rawG1 * (1 + O.jetError) ^ 2 + rawP1 * O.jetError ≤
        ConfiguredRowCeilingPolynomialEnvelopes.wideG1
          (shift S.scalar.E.data S.scalar.large.N)
          ConfiguredRecursiveSourceP0FixedDistortion.choice.MA0
          ConfiguredRecursiveSourceP0FixedDistortion.choice.NA0 n ∧
      rawCg * (1 + O.jetError) ^ 2 + khat * rawP1 * O.jetError ≤
        ConfiguredRowCeilingPolynomialEnvelopes.wideCgWithKhat
          (shift S.scalar.E.data S.scalar.large.N) khat
          ConfiguredRecursiveSourceP0FixedDistortion.choice.MA0
          ConfiguredRecursiveSourceP0FixedDistortion.choice.NA0 n := by
  apply ConfiguredRecursiveSourceP0FixedDistortion.nearIdentity_majorants
  · exact hkhat
  · exact O.jetBounds.eps_nonnegative
  · exact R.jetError_le_rowEps.trans (S.jet_half n k)
  · exact hP0
  · exact hG0
  · exact hCg0
  · exact hP
  · exact hG
  · exact hCg

/-- A direct selected row together with the configured index bounds needed by
the polynomial jet tail.  The terminal perimeter lower bound is now retained
by `RowSelection` itself; this wrapper contains only configured specialization
facts. -/
structure ConfiguredRowSelection
    {Q current : ℕ → Data} {e : ℕ → ℕ → ℝ} {depth n : ℕ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
    {period : ℕ → ℕ → ℝ} {diagonal kh Qmax : ℕ → ℝ}
    {a MA NA : ℕ → ℕ → ℝ} {K0 K1 K2 : ℝ}
    (S : CorrelatedColumn Q current e depth P0 P1 khat G1 Cg C c dlt
      period diagonal kh Qmax K0 K1 K2)
    (W : RowSelection (n := n) (a := a) (MA := MA) (NA := NA)
      (K0 := K0) (K1 := K1) (K2 := K2) S)
    (D : ConstructedConfiguredSequenceWeighted.Data) (M : ℝ) : Prop where
  kh_eq : kh n = sourceKh
  qmax_le : Qmax n ≤ ellCap D n
  cost_le : W.output.chosen.Delta.cost ≤ rowDefect D (n + (depth + 1))
  defect_le : rowDefect D (n + (depth + 1)) ≤ M

def ConfiguredRowSelection.chosenCertificate
    {Q current : ℕ → Data} {e : ℕ → ℕ → ℝ} {depth n : ℕ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
    {period : ℕ → ℕ → ℝ} {diagonal kh Qmax : ℕ → ℝ}
    {a MA NA : ℕ → ℕ → ℝ} {K0 K1 K2 : ℝ}
    {S : CorrelatedColumn Q current e depth P0 P1 khat G1 Cg C c dlt
      period diagonal kh Qmax K0 K1 K2}
    {W : RowSelection (n := n) (a := a) (MA := MA) (NA := NA)
      (K0 := K0) (K1 := K1) (K2 := K2) S}
    {D : ConstructedConfiguredSequenceWeighted.Data} {M : ℝ}
    (R : ConfiguredRowSelection S W D M) :
    ChosenCertificate W.output D M n (depth + 1) where
  kh_eq := R.kh_eq
  qmax_le := R.qmax_le
  terminal_perim_ge_one := W.terminal_perim_ge_one
  cost_le := R.cost_le
  defect_le := R.defect_le

/-- All near-identity analytic inequalities for an actual selected row now
follow from its configured wrapper and the common scalar tail. -/
theorem ConfiguredRowSelection.nearIdentity_majorants
    {MA0 NA0 : ℝ} (J : RowJetScalarOutput MA0 NA0)
    {Q current : ℕ → Data} {e : ℕ → ℕ → ℝ} {depth n : ℕ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
    {period : ℕ → ℕ → ℝ} {diagonal kh Qmax : ℕ → ℝ}
    {a MA NA : ℕ → ℕ → ℝ} {K0 K1 K2 : ℝ}
    {S : CorrelatedColumn Q current e depth P0 P1 khat G1 Cg C c dlt
      period diagonal kh Qmax K0 K1 K2}
    {W : RowSelection (n := n) (a := a) (MA := MA) (NA := NA)
      (K0 := K0) (K1 := K1) (K2 := K2) S}
    (R : ConfiguredRowSelection S W
      (shift J.scalar.E.data J.scalar.large.N) J.scalar.Mend)
    {rawP1 rawG1 rawCg : ℝ}
    (hkhat0 : 0 ≤ khat n)
    (hP0 : 0 ≤ rawP1) (hG0 : 0 ≤ rawG1) (hCg0 : 0 ≤ rawCg)
    (hP : rawP1 ≤ rowP1 (shift J.scalar.E.data J.scalar.large.N) n)
    (hG : rawG1 ≤ rowG1 (shift J.scalar.E.data J.scalar.large.N) n)
    (hCg : rawCg ≤ rowCg (shift J.scalar.E.data J.scalar.large.N) n) :
    rawP1 * (1 + W.output.jetError) ≤
        ConfiguredRowCeilingPolynomialEnvelopes.wideP1
          (shift J.scalar.E.data J.scalar.large.N)
          ConfiguredRecursiveSourceP0FixedDistortion.choice.MA0 n ∧
      rawG1 * (1 + W.output.jetError) ^ 2 +
          rawP1 * W.output.jetError ≤
        ConfiguredRowCeilingPolynomialEnvelopes.wideG1
          (shift J.scalar.E.data J.scalar.large.N)
          ConfiguredRecursiveSourceP0FixedDistortion.choice.MA0
          ConfiguredRecursiveSourceP0FixedDistortion.choice.NA0 n ∧
      rawCg * (1 + W.output.jetError) ^ 2 +
          khat n * rawP1 * W.output.jetError ≤
        ConfiguredRowCeilingPolynomialEnvelopes.wideCgWithKhat
          (shift J.scalar.E.data J.scalar.large.N) (khat n)
          ConfiguredRecursiveSourceP0FixedDistortion.choice.MA0
          ConfiguredRecursiveSourceP0FixedDistortion.choice.NA0 n := by
  exact R.chosenCertificate.nearIdentity_majorants_of_scalar J hkhat0
    hP0 hG0 hCg0 hP hG hCg

end ConfiguredRecursiveSourceP0RowJetTail
