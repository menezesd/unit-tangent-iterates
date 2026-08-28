import UnitTangentIterates.ConfiguredRecursiveEdgeGeometricPresentedDirectLimit
import UnitTangentIterates.ConfiguredRecursiveEdgeSourceP0Growth
import UnitTangentIterates.ModelDefectSummable

/-!
# Weighted effective errors for triangular recursive rows

The source floor varies along `n+k`, so the analytic conversion must remain
inside the summation.  This file packages that weighted series and proves its
configured summability from explicit growth and decay majorants.
-/

noncomputable section

open Filter Real

namespace ConfiguredRecursiveEdgeWeightedEffectiveError

open ConstructedConfiguredInductiveTubeBudget.WeightedData
  ConfiguredRecursiveEdgeSourceP0Growth

def weightedSequence (C d : ℕ → ℝ) (j : ℕ) : ℝ :=
  C j * d (j + 1)

def weightedError (C d : ℕ → ℝ) (N n k : ℕ) : ℝ :=
  weightedSequence C d (N + n + k)

def weightedRadius (C d : ℕ → ℝ) (N n : ℕ) : ℝ :=
  ∑' k, weightedError C d N n k

/-- Polynomial-times-small-exponential conversion growth remains summable
when multiplied by the faster configured diagonal decay. -/
theorem exists_weightedSequence_exp_bound_of_growth
    (D : ConstructedConfiguredSequenceWeighted.Data)
    (C d : ℕ → ℝ) {C0 A b gamma : ℝ}
    (hC0 : 0 ≤ C0) (hA : 0 ≤ A) (hb : 0 < b) (hgamma : gamma < b)
    (hCnonnegative : ∀ j, 0 ≤ C j)
    (hCgrowth : ∀ j, C j ≤
      C0 * (1 + D.Hs j) ^ 2 * Real.exp (gamma * D.Hs j))
    (hdnonnegative : ∀ j, 0 ≤ d j)
    (hddecay : ∀ j, d j ≤ A * Real.exp (-(b * D.Hs j))) :
    ∃ beta K : ℝ, 0 < beta ∧ 0 ≤ K ∧ ∀ j,
      weightedSequence C d j ≤ K * Real.exp (-(beta * D.Hs j)) := by
  let eps : ℝ := (b - gamma) / 2
  have heps : 0 < eps := div_pos (sub_pos.mpr hgamma) (by norm_num)
  obtain ⟨E, hE0, hE⟩ :=
    ConstructedRowCPolynomialGrowth.exists_one_add_pow_le_exp 2 heps
  let K : ℝ := C0 * E * A
  have hK0 : 0 ≤ K := mul_nonneg (mul_nonneg hC0 hE0) hA
  have hbound : ∀ j, weightedSequence C d j ≤
      K * Real.exp (-(eps * D.Hs j)) := by
    intro j
    have hH0 : 0 ≤ D.Hs j := (D.model.separation_pos j).le
    have hCexp : C j ≤
        C0 * E * Real.exp ((gamma + eps) * D.Hs j) := by
      calc
        C j ≤ C0 * (1 + D.Hs j) ^ 2 *
            Real.exp (gamma * D.Hs j) := hCgrowth j
        _ ≤ C0 * (E * Real.exp (eps * D.Hs j)) *
            Real.exp (gamma * D.Hs j) := by
          gcongr
          exact hE (D.Hs j) hH0
        _ = C0 * E * Real.exp ((gamma + eps) * D.Hs j) := by
          rw [show (gamma + eps) * D.Hs j =
            eps * D.Hs j + gamma * D.Hs j by ring, Real.exp_add]
          ring
    have hnext : D.Hs j ≤ D.Hs (j + 1) := by
      have hs := D.separation_step j
      have hd := D.deltaStep_pos
      linarith
    have hdexp : d (j + 1) ≤ A * Real.exp (-(b * D.Hs j)) := by
      exact (hddecay (j + 1)).trans (mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.mpr (by
          have hm := mul_le_mul_of_nonneg_left hnext hb.le
          linarith)) hA)
    calc
      weightedSequence C d j = C j * d (j + 1) := rfl
      _ ≤ (C0 * E * Real.exp ((gamma + eps) * D.Hs j)) *
          (A * Real.exp (-(b * D.Hs j))) :=
        mul_le_mul hCexp hdexp (hdnonnegative (j + 1))
          (mul_nonneg (mul_nonneg hC0 hE0) (Real.exp_pos _).le)
      _ = K * Real.exp (-(eps * D.Hs j)) := by
        rw [show -(eps * D.Hs j) =
          (gamma + eps) * D.Hs j + -(b * D.Hs j) by
            dsimp [eps]; ring,
          Real.exp_add]
        dsimp [K]
        ring
  exact ⟨eps, K, heps, hK0, hbound⟩

theorem summable_weightedSequence_of_growth
    (D : ConstructedConfiguredSequenceWeighted.Data)
    (C d : ℕ → ℝ) {C0 A b gamma : ℝ}
    (hC0 : 0 ≤ C0) (hA : 0 ≤ A) (hb : 0 < b) (hgamma : gamma < b)
    (hCnonnegative : ∀ j, 0 ≤ C j)
    (hCgrowth : ∀ j, C j ≤
      C0 * (1 + D.Hs j) ^ 2 * Real.exp (gamma * D.Hs j))
    (hdnonnegative : ∀ j, 0 ≤ d j)
    (hddecay : ∀ j, d j ≤ A * Real.exp (-(b * D.Hs j))) :
    Summable (weightedSequence C d) := by
  obtain ⟨beta, K, hbeta, hK, hbound⟩ :=
    exists_weightedSequence_exp_bound_of_growth D C d hC0 hA hb hgamma
      hCnonnegative hCgrowth hdnonnegative hddecay
  have hmajor : Summable (fun j : ℕ ↦
      K * Real.exp (-(beta * D.Hs j))) :=
    (ModelDefectSummable.summable_exp_neg_of_growth hbeta D.deltaStep_pos
      D.separation_linear).mul_left K
  exact Summable.of_nonneg_of_le
    (fun j ↦ mul_nonneg (hCnonnegative j) (hdnonnegative (j + 1)))
    hbound hmajor

theorem weightedError_nonnegative
    {C d : ℕ → ℝ} (hC : ∀ j, 0 ≤ C j) (hd : ∀ j, 0 ≤ d j)
    (N n k : ℕ) : 0 ≤ weightedError C d N n k :=
  mul_nonneg (hC _) (hd _)

theorem weightedError_summable
    {C d : ℕ → ℝ} (hs : Summable (weightedSequence C d))
    (N n : ℕ) : Summable (weightedError C d N n) := by
  have hinj : Function.Injective (fun k : ℕ ↦ N + n + k) := by
    intro a b hab
    exact Nat.add_left_cancel hab
  simpa [weightedError] using hs.comp_injective hinj

theorem weightedRadius_eq_tail
    (C d : ℕ → ℝ) (N n : ℕ) :
    weightedRadius C d N n =
      ShadowingTails.tail (weightedSequence C d) (N + n) := by
  apply tsum_congr
  intro k
  simp [weightedRadius, weightedError, ShadowingTails.tail, Nat.add_assoc]

/-- Pointwise domination of the concrete dynamic marked error by the global
weighted conversion/defect sequence. -/
theorem effectiveError_le_weightedError
    {P0 P1 khat G1 Cg endpoint C d : ℕ → ℝ} (N n k : ℕ)
    (hd : ∀ j, 0 ≤ d j)
    (hfactor : ∀ n k,
      NormalPathC2IncrementVariableSpeed.c2ConstVar
          (P0 (n + k)) (P1 n) (khat n) (G1 n) (Cg n) + endpoint n ≤
        C (N + n + k)) :
    ConfiguredRecursiveEdgeGeometricPresentedDirectLimit.effectiveError
        (P0 := P0) (P1 := P1) (khat := khat) (G1 := G1) (Cg := Cg)
        endpoint (ExponentialDiagonalLargeSeparation.shiftSequence d N) n k ≤
      weightedError C d N n k := by
  unfold ConfiguredRecursiveEdgeGeometricPresentedDirectLimit.effectiveError
    weightedError weightedSequence ExponentialDiagonalLargeSeparation.shiftSequence
  have hind : N + (n + k + 1) = N + n + k + 1 := by omega
  rw [hind]
  exact mul_le_mul_of_nonneg_right (hfactor n k) (hd _)

/-- A further finite shift makes every row's full weighted radius smaller
than any prescribed positive reserve. -/
theorem exists_shift_weightedRadius_lt
    {C d : ℕ → ℝ} (hs : Summable (weightedSequence C d))
    (hnonnegative : ∀ j, 0 ≤ weightedSequence C d j)
    {reserve : ℝ} (hreserve : 0 < reserve) :
    ∃ N, ∀ n, weightedRadius C d N n < reserve := by
  have hevent := (ShadowingTails.tail_tendsto_zero
    (e := weightedSequence C d)).eventually
    (Metric.ball_mem_nhds (0 : ℝ) hreserve)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hevent
  refine ⟨N, fun n ↦ ?_⟩
  have hle := ShadowingTails.tail_antitone hs hnonnegative
    (Nat.le_add_right N n)
  have hbase := hN N le_rfl
  have hbase' : ShadowingTails.tail (weightedSequence C d) N < reserve := by
    simpa [Real.dist_eq, abs_of_nonneg
      (ShadowingTails.tail_nonneg hnonnegative N)] using hbase
  rw [weightedRadius_eq_tail]
  exact hle.trans_lt hbase'

/-- Configured specialization for the recursive edge conversion and physical
diagonal defect. -/
theorem summable_configuredWeightedSequence
    (D : ConstructedConfiguredSequenceWeighted.Data)
    {MA NA khat kh M : ℝ}
    (hMA : 0 ≤ MA) (hNA : 0 ≤ NA) (hkhat : 0 ≤ khat)
    (hkh0 : 0 ≤ kh) (hkh1 : kh < 1) (hM : 0 ≤ M) :
    Summable (weightedSequence
      (edgeCombinedConversion D MA NA khat kh M)
      (edgePhysicalDefect D)) := by
  have hbeta : 0 < D.model.beta := (D.model.configs 0).hbeta0
  let gamma : ℝ := D.model.beta / 16
  let b : ℝ := D.model.beta / 8
  have hgamma0 : 0 < gamma := by
    dsimp [gamma]
    exact div_pos hbeta (by norm_num)
  have hb : 0 < b := by dsimp [b]; exact div_pos hbeta (by norm_num)
  have hgamma : gamma < b := by dsimp [gamma, b]; linarith
  obtain ⟨C0, hC0, hCgrowth⟩ :=
    exists_edgeCombinedConversion_growth_majorant D hMA hNA hkhat
      hkh0 hkh1 hM hgamma0
  obtain ⟨A, hA, hddecay⟩ := exists_edgePhysicalDefect_exp_bound D
  exact summable_weightedSequence_of_growth D _ _
    (C0 := C0) (A := A) (b := b) (gamma := gamma) hC0 hA hb hgamma
    (edgeCombinedConversion_nonnegative D hkh0 hkh1) hCgrowth
    (edgePhysicalDefect_nonnegative D) (by
      intro n
      simpa [b] using hddecay n)

/-- A fresh large-separation output for the weighted diagonal.  Its row
radius is the full dynamic conversion tail rather than a fixed row factor
times the unweighted defect tail. -/
theorem exists_configuredWeightedOutput
    (D : ConstructedConfiguredSequenceWeighted.Data)
    {MA NA khat kh M Cw : ℝ}
    (hMA : 0 ≤ MA) (hNA : 0 ≤ NA) (hkhat : 0 ≤ khat)
    (hkh0 : 0 ≤ kh) (hkh1 : kh < 1) (hM : 0 ≤ M) (hCw : 0 ≤ Cw) :
    Nonempty (ExponentialDiagonalLargeSeparation.Output D (fun _ ↦ 1)
      (weightedSequence (edgeCombinedConversion D MA NA khat kh M)
        (edgePhysicalDefect D)) Cw) := by
  have hbetaModel : 0 < D.model.beta := (D.model.configs 0).hbeta0
  let gamma0 : ℝ := D.model.beta / 16
  let b0 : ℝ := D.model.beta / 8
  have hgamma0 : 0 < gamma0 := by
    dsimp [gamma0]
    exact div_pos hbetaModel (by norm_num)
  have hb0 : 0 < b0 := by
    dsimp [b0]
    exact div_pos hbetaModel (by norm_num)
  have hgamma0b0 : gamma0 < b0 := by dsimp [gamma0, b0]; linarith
  obtain ⟨C0, hC0, hCgrowth⟩ :=
    exists_edgeCombinedConversion_growth_majorant D hMA hNA hkhat
      hkh0 hkh1 hM hgamma0
  obtain ⟨A, hA, hddecay⟩ := exists_edgePhysicalDefect_exp_bound D
  obtain ⟨beta, K, hbeta, hK, hweightedExp⟩ :=
    exists_weightedSequence_exp_bound_of_growth D _ _
      (C0 := C0) (A := A) (b := b0) (gamma := gamma0)
      hC0 hA hb0 hgamma0b0
      (edgeCombinedConversion_nonnegative D hkh0 hkh1) hCgrowth
      (edgePhysicalDefect_nonnegative D) (by
        intro n
        simpa [b0] using hddecay n)
  let gamma : ℝ := beta / 2
  have hgamma : gamma < beta := by dsimp [gamma]; linarith
  apply ExponentialDiagonalLargeSeparation.exists_output D (fun _ ↦ 1)
    (weightedSequence (edgeCombinedConversion D MA NA khat kh M)
      (edgePhysicalDefect D))
    (fun _ ↦ zero_le_one) zero_le_one hK hbeta hgamma
  · intro n
    have hH : 0 ≤ D.Hs n := (D.model.separation_pos n).le
    have hgamma0' : 0 ≤ gamma := (half_pos hbeta).le
    have hsquare : 1 ≤ (1 + D.Hs n) ^ 2 := by nlinarith [sq_nonneg (D.Hs n)]
    have hexp : 1 ≤ Real.exp (gamma * D.Hs n) := by
      rw [← Real.exp_zero]
      exact Real.exp_le_exp.mpr (mul_nonneg hgamma0' hH)
    simpa using mul_le_mul hsquare hexp zero_le_one (sq_nonneg (1 + D.Hs n))
  · intro n
    exact mul_nonneg
      (edgeCombinedConversion_nonnegative D hkh0 hkh1 n)
      (edgePhysicalDefect_nonnegative D (n + 1))
  · exact hweightedExp
  · exact hCw

/-- The weighted output's speed reserve is exactly the dynamic weighted
radius required by the generic physical bounds adapter. -/
theorem weightedRadius_le_of_output
    {D : ConstructedConfiguredSequenceWeighted.Data} {C d : ℕ → ℝ}
    {Cw : ℝ}
    (L : ExponentialDiagonalLargeSeparation.Output D (fun _ ↦ 1)
      (weightedSequence C d) Cw) (n : ℕ) :
    weightedRadius C d L.N n ≤ (shift D L.N).Hs 0 := by
  simpa [weightedRadius, weightedError, weightedSequence,
    ExponentialDiagonalLargeSeparation.rowRadius,
    ExponentialDiagonalLargeSeparation.rowError,
    ExponentialDiagonalLargeSeparation.shiftSequence, ShadowingTails.tail,
    Nat.add_assoc] using L.speed_tail n

end ConfiguredRecursiveEdgeWeightedEffectiveError
