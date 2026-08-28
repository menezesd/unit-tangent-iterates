import UnitTangentIterates.ConfiguredApproximateDefectPathRowwiseCost
import UnitTangentIterates.ConstructedConfiguredInductiveTubeBudget
import UnitTangentIterates.WeightedDefectUniformCap
import UnitTangentIterates.ClosingGapThreshold

/-!
# Large-separation closure for the honest configured row defect

This module contains only scalar and configured-model choices.  It chooses a
uniform strict stage cap from weighted summability, discards a finite prefix,
and proves the two scalar tail inequalities needed by the local tube budget
together with the paper-facing width/perimeter gap.  No path, pullback map, or
provider data occur in the interface.
-/

noncomputable section

set_option maxHeartbeats 2000000

open Real Filter

namespace ConstructedRowDefectLargeSeparation

open ConfiguredApproximateDefectPathRowwise
open ConfiguredApproximateDefectPathRowwiseCost
open ConstructedConfiguredInductiveTubeBudget
open ConstructedConfiguredInductiveTubeBudget.WeightedData
open PathMetric.WeightedRecursiveDefect

/-- Uniform coefficient in the exponential majorant for the full configured
interpolation cost. -/
def rowDefectExpConst (D : ConstructedConfiguredSequenceWeighted.Data) : ℝ :=
  configuredCostConst D *
    ModelDefectSummable.modelDefectConst (2 * D.kd) D.kstar
      (edgeCoefficient D) (D.Hs 0) D.model.beta

/-- The coefficient of the weighted geometric row tail. -/
def rowTailCoefficient
    (D : ConstructedConfiguredSequenceWeighted.Data) (C K : ℝ) : ℝ :=
  C * rowDefectExpConst D /
    (1 - K * Real.exp (-((D.model.beta / 4) * D.deltaStep)))

/-- Recursive error sequence in one triangular row. -/
def rowError (D : ConstructedConfiguredSequenceWeighted.Data)
    (K : ℝ) (n k : ℕ) : ℝ :=
  K ^ k * rowDefect D (n + k)

/-- The honest row-dependent marked shadow radius.  The conversion constant
is frozen only within a row; it is not replaced by a global supremum. -/
def rowRadius (C : ℕ → ℝ)
    (D : ConstructedConfiguredSequenceWeighted.Data) (K : ℝ) (n : ℕ) : ℝ :=
  C n * ShadowingTails.tail (rowError D K n) 0

def shiftSequence (C : ℕ → ℝ) (N n : ℕ) : ℝ := C (N + n)

/-- Rowwise chord scale paired with the honest variable radius. -/
def rowRhoVariable
    {kappas : ℕ → ℝ → ℝ} {Hs eps : ℕ → ℝ}
    (model : UnconditionalAssembly.ConfiguredModelSequence kappas Hs eps)
    (r : ℕ → ℝ) (n : ℕ) : ℝ :=
  min (1 / 2)
    (Hs 0 / (2 * (ConfiguredInductiveTubeBudget.accBound model n + r n)))

theorem rowDefect_nonneg
    (D : ConstructedConfiguredSequenceWeighted.Data) (n : ℕ) :
    0 ≤ rowDefect D n := by
  unfold rowDefect rowDsup
  exact InterpolationPathDist.interpPathCost_nonneg D.kstar_nonneg D.kd_nonneg
    (CurvatureStabilityL1.l1Modulus_nonneg _ _ _)
    (D.model.separation_pos n).le (edgeEps_nonneg D n)

theorem rowDefectExpConst_nonneg
    (D : ConstructedConfiguredSequenceWeighted.Data) :
    0 ≤ rowDefectExpConst D := by
  unfold rowDefectExpConst
  exact mul_nonneg (configuredCostConst_nonneg D)
    (ModelDefectSummable.modelDefectConst_nonneg
      (edgeCoefficient_nonneg D) D.kstar_nonneg D.separation_zero_pos
      (D.model.configs 0).hbeta0)

/-- The actual interpolation cost has a fixed coefficient times a quarter-rate
exponential tail. -/
theorem rowDefect_le_exp
    (D : ConstructedConfiguredSequenceWeighted.Data) (n : ℕ) :
    rowDefect D n ≤ rowDefectExpConst D *
      Real.exp (-((D.model.beta / 4) * D.Hs n)) := by
  have hmodel : rowModelDefect D n ≤
      ModelDefectSummable.modelDefectConst (2 * D.kd) D.kstar
          (edgeCoefficient D) (D.Hs 0) D.model.beta *
        Real.exp (-((D.model.beta / 4) * D.Hs n)) := by
    simpa [rowModelDefect] using
      (ModelDefectSummable.model_defect_le
        (M := 2 * D.kd) (kb := D.kstar) (Cm := edgeCoefficient D)
        (P0 := D.Hs 0) (beta := D.model.beta)
        (Hs := D.Hs) (eps := edgeEps D) (P := D.Hs)
        (D.model.configs 0).hbeta0
        (mul_nonneg (by norm_num) D.kd_nonneg)
        (edgeCoefficient_nonneg D) D.kstar_nonneg
        D.separation_zero_pos D.separation_lower
        (fun i => (D.model.separation_pos i).le) (edgeEps_nonneg D)
        (edgeEps_le_exp_at_row D) n)
  calc
    rowDefect D n ≤ configuredCostConst D * rowModelDefect D n :=
      rowDefect_le_configuredCostConst D n
    _ ≤ configuredCostConst D *
        (ModelDefectSummable.modelDefectConst (2 * D.kd) D.kstar
          (edgeCoefficient D) (D.Hs 0) D.model.beta *
          Real.exp (-((D.model.beta / 4) * D.Hs n))) :=
      mul_le_mul_of_nonneg_left hmodel (configuredCostConst_nonneg D)
    _ = rowDefectExpConst D *
        Real.exp (-((D.model.beta / 4) * D.Hs n)) := by
      simp [rowDefectExpConst]
      ring

@[simp] theorem rowDefect_shift
    (D : ConstructedConfiguredSequenceWeighted.Data) (N n : ℕ) :
    rowDefect (shift D N) n = rowDefect D (N + n) := by
  rfl

/-- A shifted honest row tail is bounded by one fixed coefficient from the
unshifted configured sequence. -/
theorem shifted_radius_le_exp
    (D : ConstructedConfiguredSequenceWeighted.Data) {C K : ℝ}
    (hC : 0 ≤ C) (hK : 1 ≤ K)
    (hthreshold : K * Real.exp
      (-((D.model.beta / 4) * D.deltaStep)) < 1)
    (N n : ℕ) :
    PullbackTubeTailBudget.radius C K (rowDefect (shift D N)) n ≤
      rowTailCoefficient D C K *
        Real.exp (-((D.model.beta / 4) * (shift D N).Hs n)) := by
  let b : ℝ := D.model.beta / 4
  let q : ℝ := Real.exp (-(b * D.deltaStep))
  let A : ℝ := rowDefectExpConst D
  let R : ℝ := K * q
  have hb : 0 < b := by
    dsimp [b]
    linarith [(D.model.configs 0).hbeta0]
  have hK0 : 0 ≤ K := zero_le_one.trans hK
  have hA0 : 0 ≤ A := by simpa [A] using rowDefectExpConst_nonneg D
  have hq0 : 0 ≤ q := by dsimp [q]; positivity
  have hR0 : 0 ≤ R := by dsimp [R]; exact mul_nonneg hK0 hq0
  have hR1 : R < 1 := by simpa [R, q, b] using hthreshold
  have hsep : ∀ k : ℕ,
      D.Hs (N + n) + k * D.deltaStep ≤ D.Hs (N + n + k) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        have hs := D.separation_step (N + n + k)
        calc
          D.Hs (N + n) + (↑(k + 1) : ℝ) * D.deltaStep =
              (D.Hs (N + n) + (k : ℝ) * D.deltaStep) + D.deltaStep := by
            push_cast
            ring
          _ ≤ D.Hs (N + n + k) + D.deltaStep := by
            linarith only [ih]
          _ ≤ D.Hs (N + n + (k + 1)) := by
            simpa [Nat.add_assoc] using hs
  have hdgeo : ∀ k : ℕ, rowDefect (shift D N) (n + k) ≤
      A * Real.exp (-(b * (shift D N).Hs n)) * q ^ k := by
    intro k
    have hd := rowDefect_le_exp D (N + (n + k))
    have hexp : Real.exp (-(b * D.Hs (N + (n + k)))) ≤
        Real.exp (-(b * D.Hs (N + n))) * q ^ k := by
      have hle : Real.exp (-(b * D.Hs (N + (n + k)))) ≤
          Real.exp (-(b * (D.Hs (N + n) + k * D.deltaStep))) := by
        apply Real.exp_le_exp.mpr
        have hm := mul_le_mul_of_nonneg_left (hsep k) hb.le
        simpa [Nat.add_assoc] using neg_le_neg hm
      have heq : Real.exp (-(b * (D.Hs (N + n) + k * D.deltaStep))) =
          Real.exp (-(b * D.Hs (N + n))) * q ^ k := by
        dsimp [q]
        rw [← Real.exp_nat_mul, ← Real.exp_add]
        push_cast
        ring
      exact hle.trans_eq heq
    calc
      rowDefect (shift D N) (n + k) = rowDefect D (N + (n + k)) :=
        rowDefect_shift D N (n + k)
      _ ≤ A * Real.exp (-(b * D.Hs (N + (n + k)))) := by
        simpa [A, b] using hd
      _ ≤ A * (Real.exp (-(b * D.Hs (N + n))) * q ^ k) :=
        mul_le_mul_of_nonneg_left hexp hA0
      _ = A * Real.exp (-(b * (shift D N).Hs n)) * q ^ k := by
        change A * (Real.exp (-(b * D.Hs (N + n))) * q ^ k) =
          A * Real.exp (-(b * D.Hs (N + n))) * q ^ k
        ring
  have hweighted : Summable
      (weightedDefect K (rowDefect (shift D N))) :=
    summable_weighted_rowDefect (shift D N) hK0 (by
      simpa [b] using hthreshold)
  have hactual : Summable (fun k =>
      C * (K ^ k * rowDefect (shift D N) (n + k))) := by
    have hpull := summable_pullbackError_of_summable_weighted hK
      (rowDefect_nonneg (shift D N)) hweighted n
    simpa [pullbackError] using hpull.mul_left C
  have hmajor : Summable (fun k : ℕ =>
      (C * A * Real.exp (-(b * (shift D N).Hs n))) * R ^ k) :=
    (summable_geometric_of_lt_one hR0 hR1).mul_left _
  have hterm : ∀ k : ℕ,
      C * (K ^ k * rowDefect (shift D N) (n + k)) ≤
        (C * A * Real.exp (-(b * (shift D N).Hs n))) * R ^ k := by
    intro k
    have hm := mul_le_mul_of_nonneg_left (hdgeo k) (pow_nonneg hK0 k)
    have hmC := mul_le_mul_of_nonneg_left hm hC
    calc
      C * (K ^ k * rowDefect (shift D N) (n + k)) ≤
          C * (K ^ k *
            (A * Real.exp (-(b * (shift D N).Hs n)) * q ^ k)) := hmC
      _ = (C * A * Real.exp (-(b * (shift D N).Hs n))) * R ^ k := by
        dsimp [R]
        rw [mul_pow]
        ring
  have hsum := hactual.tsum_le_tsum hterm hmajor
  have hgeom : (∑' k : ℕ,
      (C * A * Real.exp (-(b * (shift D N).Hs n))) * R ^ k) =
      C * A / (1 - R) * Real.exp (-(b * (shift D N).Hs n)) := by
    rw [tsum_mul_left, tsum_geometric_of_lt_one hR0 hR1]
    field_simp [ne_of_gt (sub_pos.mpr hR1)]
  dsimp [PullbackTubeTailBudget.radius, ShadowingTails.tail]
  rw [hgeom] at hsum
  simpa [rowTailCoefficient, A, R, q, b] using hsum

/-- A polynomial/exponential row-growth majorant is absorbed by the remaining
quarter-rate defect decay. -/
theorem shifted_rowRadius_le_exp
    (D : ConstructedConfiguredSequenceWeighted.Data)
    (C : ℕ → ℝ) {C0 gamma K : ℝ}
    (hC : ∀ n, 0 ≤ C n) (hC0 : 0 ≤ C0)
    (hgamma : gamma < D.model.beta / 4)
    (hCgrowth : ∀ n, C n ≤ C0 * (1 + D.Hs n) ^ 2 *
      Real.exp (gamma * D.Hs n))
    (hK : 1 ≤ K)
    (hthreshold : K * Real.exp
      (-((D.model.beta / 4) * D.deltaStep)) < 1)
    (N n : ℕ) :
    rowRadius (shiftSequence C N) (shift D N) K n ≤
      (C0 * rowTailCoefficient D 1 K) *
        ((1 + (shift D N).Hs n) ^ 2 *
          Real.exp (-((D.model.beta / 4 - gamma) * (shift D N).Hs n))) := by
  let D' := shift D N
  let T := rowTailCoefficient D 1 K
  have htail := shifted_radius_le_exp D (C := 1) (K := K)
    (by norm_num) hK hthreshold N n
  have htail' : ShadowingTails.tail (rowError D' K n) 0 ≤
      T * Real.exp (-((D.model.beta / 4) * D'.Hs n)) := by
    simpa [PullbackTubeTailBudget.radius, rowError, D', T] using htail
  have htail0 : 0 ≤ ShadowingTails.tail (rowError D' K n) 0 := by
    apply ShadowingTails.tail_nonneg
    intro k
    exact mul_nonneg (pow_nonneg (zero_le_one.trans hK) k)
      (rowDefect_nonneg D' (n + k))
  have hT0 : 0 ≤ T := by
    dsimp [T, rowTailCoefficient]
    have hden : 0 ≤ 1 - K * Real.exp
        (-((D.model.beta / 4) * D.deltaStep)) :=
      (sub_pos.mpr hthreshold).le
    exact div_nonneg (mul_nonneg (by norm_num) (rowDefectExpConst_nonneg D)) hden
  have hCg := hCgrowth (N + n)
  have hprod := mul_le_mul hCg htail' htail0
    (mul_nonneg (mul_nonneg hC0 (sq_nonneg _)) (Real.exp_pos _).le)
  calc
    rowRadius (shiftSequence C N) D' K n =
        C (N + n) * ShadowingTails.tail (rowError D' K n) 0 := rfl
    _ ≤ (C0 * (1 + D.Hs (N + n)) ^ 2 *
          Real.exp (gamma * D.Hs (N + n))) *
        (T * Real.exp (-((D.model.beta / 4) * D'.Hs n))) := hprod
    _ = (C0 * T) * ((1 + D'.Hs n) ^ 2 *
          Real.exp (-((D.model.beta / 4 - gamma) * D'.Hs n))) := by
      rw [show D.Hs (N + n) = D'.Hs n from rfl]
      calc
        C0 * (1 + D'.Hs n) ^ 2 * Real.exp (gamma * D'.Hs n) *
              (T * Real.exp (-(D.model.beta / 4 * D'.Hs n))) =
            C0 * T * (1 + D'.Hs n) ^ 2 *
              (Real.exp (gamma * D'.Hs n) *
                Real.exp (-(D.model.beta / 4 * D'.Hs n))) := by ring
        _ = C0 * T * (1 + D'.Hs n) ^ 2 *
              Real.exp (gamma * D'.Hs n +
                -(D.model.beta / 4 * D'.Hs n)) := by rw [← Real.exp_add]
        _ = (C0 * T) * ((1 + D'.Hs n) ^ 2 *
              Real.exp (-((D.model.beta / 4 - gamma) * D'.Hs n))) := by ring
    _ = (C0 * rowTailCoefficient D 1 K) *
          ((1 + (shift D N).Hs n) ^ 2 *
            Real.exp (-((D.model.beta / 4 - gamma) * (shift D N).Hs n))) := rfl

/-- Scalar output needed downstream by the local recursive construction. -/
structure Output
    (D : ConstructedConfiguredSequenceWeighted.Data)
    (C : ℕ → ℝ) (K Cw : ℝ) where
  Mtotal : ℝ
  Mtotal_pos : 0 < Mtotal
  N : ℕ
  stage_cap : ∀ n k,
    K ^ k * rowDefect (shift D N) (n + k) < Mtotal
  speed_tail : ∀ n,
    rowRadius (shiftSequence C N) (shift D N) K n ≤
      (shift D N).Hs 0
  chord_tail : ∀ n,
    2 * rowRadius (shiftSequence C N) (shift D N) K n ≤
      (ConfiguredInductiveTubeBudget.chordBase (shift D N).model / 2) *
        rowRhoVariable (shift D N).model
          (rowRadius (shiftSequence C N) (shift D N) K) n
  width_gap : Cw + 2 *
      rowRadius (shiftSequence C N) (shift D N) K 0 <
    (2 * (shift D N).Hs 0 -
      rowRadius (shiftSequence C N) (shift D N) K 0) /
      Real.pi

/-- Weighted summability, configured linear growth, and the exponential honest
defect bound jointly produce a stage cap and a tail where all scalar local
tube budgets and the final paper gap hold. -/
theorem exists_output
    (D : ConstructedConfiguredSequenceWeighted.Data)
    (C : ℕ → ℝ) {C0 gamma K Cw : ℝ}
    (hC : ∀ n, 0 ≤ C n) (hC0 : 0 ≤ C0)
    (hgamma : gamma < D.model.beta / 4)
    (hCgrowth : ∀ n, C n ≤ C0 * (1 + D.Hs n) ^ 2 *
      Real.exp (gamma * D.Hs n))
    (hK : 1 ≤ K) (hCw : 0 ≤ Cw)
    (hthreshold : K * Real.exp
      (-((D.model.beta / 4) * D.deltaStep)) < 1) :
    Nonempty (Output D C K Cw) := by
  have hK0 : 0 ≤ K := zero_le_one.trans hK
  have hsum := summable_weighted_rowDefect D hK0 hthreshold
  obtain ⟨Mtotal, hMtotal, hcap⟩ :=
    exists_uniform_weighted_stage_cap hK (rowDefect_nonneg D) hsum
  let b : ℝ := D.model.beta / 4 - gamma
  let T : ℝ := C0 * rowTailCoefficient D 1 K
  have hb : 0 < b := by
    dsimp [b]
    exact sub_pos.mpr hgamma
  have hden : 0 < 1 - K * Real.exp
      (-((D.model.beta / 4) * D.deltaStep)) := sub_pos.mpr hthreshold
  have hT0 : 0 ≤ T := by
    dsimp [T, rowTailCoefficient]
    exact mul_nonneg hC0
      (div_nonneg (by simpa using rowDefectExpConst_nonneg D) hden.le)
  have hkpos : 0 < D.model.kstar := configured_kstar_pos D.model
  let b0 : ℝ := min 1 (Real.pi / (6 * D.model.kstar))
  have hb0 : 0 < b0 := by
    dsimp [b0]
    exact lt_min zero_lt_one
      (div_pos Real.pi_pos (mul_pos (by norm_num) hkpos))
  let E : ℝ := 32 * D.model.kstar * T + 8 * T ^ 2
  have hE0 : 0 ≤ E := by dsimp [E]; positivity
  have htail2 := MainThresholds.tendsto_tail_zero hb
  have htail4 := (MainThresholds.tendsto_tail_zero (half_pos hb)).pow 2
  have hTlim := htail2.const_mul T
  have hElim := htail4.const_mul E
  simp only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero] at htail4 hElim
  simp only [mul_zero] at hTlim
  have htarget : 0 < min 1 (b0 / 8) :=
    lt_min zero_lt_one (div_pos hb0 (by norm_num))
  have hevT : ∀ᶠ H : ℝ in atTop,
      T * ((1 + H) ^ 2 * Real.exp (-b * H)) < min 1 (b0 / 8) :=
    (tendsto_order.1 hTlim).2 _ htarget
  have hevE : ∀ᶠ H : ℝ in atTop,
      E * (((1 + H) ^ 2 * Real.exp (-(b / 2) * H)) ^ 2) < b0 :=
    (tendsto_order.1 hElim).2 _ hb0
  obtain ⟨HT, hHT⟩ := Filter.eventually_atTop.1 hevT
  obtain ⟨HE, hHE⟩ := Filter.eventually_atTop.1 hevE
  let Hgap : ℝ :=
    (Real.pi * Cw + (2 * Real.pi + 1)) / 2 + 1
  let Hmin : ℝ := max Hgap (max 1 (max HT HE))
  obtain ⟨N, hN⟩ := exists_shift_above D Hmin
  let D' := shift D N
  let r : ℕ → ℝ := rowRadius (shiftSequence C N) D' K
  have hstart : Hmin ≤ D'.Hs 0 := by simpa [D'] using hN
  have hstartGap : Hgap ≤ D'.Hs 0 :=
    (le_max_left Hgap (max 1 (max HT HE))).trans hstart
  have hstart1 : 1 ≤ D'.Hs 0 :=
    (le_max_of_le_right (le_max_left 1 (max HT HE))).trans hstart
  have hstartT : HT ≤ D'.Hs 0 :=
    (le_max_of_le_right (le_max_of_le_right (le_max_left HT HE))).trans hstart
  have hstartE : HE ≤ D'.Hs 0 :=
    (le_max_of_le_right (le_max_of_le_right (le_max_right HT HE))).trans hstart
  have hrow : ∀ n, r n ≤
      T * ((1 + D'.Hs n) ^ 2 * Real.exp (-b * D'.Hs n)) := by
    intro n
    convert shifted_rowRadius_le_exp D C hC hC0 hgamma hCgrowth hK
      hthreshold N n using 1 <;> dsimp [r, D', T, b] <;> ring
  have hlarge : ∀ n, 1 ≤ D'.Hs n := fun n =>
    hstart1.trans (D'.separation_lower n)
  have hsmallT : ∀ n,
      T * ((1 + D'.Hs n) ^ 2 * Real.exp (-b * D'.Hs n)) <
        min 1 (b0 / 8) := fun n =>
    hHT _ (hstartT.trans (D'.separation_lower n))
  have hsmallE : ∀ n,
      E * (((1 + D'.Hs n) ^ 2 *
        Real.exp (-(b / 2) * D'.Hs n)) ^ 2) < b0 :=
    fun n => hHE _ (hstartE.trans (D'.separation_lower n))
  have hexp1 : ∀ n, Real.exp (-b * D'.Hs n) ≤ 1 := by
    intro n
    exact Real.exp_le_one_iff.mpr
      (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hb.le)
        (le_trans zero_le_one (hlarge n)))
  have hspeed : ∀ n, r n ≤ D'.Hs 0 := by
    intro n
    exact (hrow n).trans
      ((hsmallT n).le.trans ((min_le_left _ _).trans hstart1))
  have hbaseLower : b0 ≤ ConfiguredInductiveTubeBudget.chordBase D'.model := by
    rw [chordBase_eq_min D'.model (configured_kstar_pos D'.model)]
    exact min_le_min hstart1 le_rfl
  have hradius0 : ∀ n, 0 ≤ r n := by
    intro n
    dsimp [r, rowRadius]
    exact mul_nonneg (hC (N + n)) (ShadowingTails.tail_nonneg (fun k =>
      mul_nonneg (pow_nonneg hK0 k) (rowDefect_nonneg D' (n + k))) 0)
  have hchord : ∀ n,
      2 * r n ≤
        (ConfiguredInductiveTubeBudget.chordBase D'.model / 2) *
          rowRhoVariable D'.model r n := by
    intro n
    let rn := r n
    let H := D'.Hs n
    let A := ConfiguredInductiveTubeBudget.accBound D'.model n
    have hr0 : 0 ≤ rn := hradius0 n
    have hH1 : 1 ≤ H := hlarge n
    have he0 : 0 < Real.exp (-b * H) := Real.exp_pos _
    have hrT : rn ≤ T * ((1 + H) ^ 2 * Real.exp (-b * H)) := hrow n
    have hrSmall : rn ≤ b0 / 8 :=
      hrT.trans ((hsmallT n).le.trans (min_le_right _ _))
    have hAeq : A = 4 * D'.model.kstar * H ^ 2 := by
      simp [A, H, ConfiguredInductiveTubeBudget.accBound]
      ring
    have hA0 : 0 ≤ A := by rw [hAeq]; positivity
    have hk' : D'.model.kstar = D.model.kstar := rfl
    have hpoly : H ^ 2 ≤ (1 + H) ^ 2 := by nlinarith [hH1]
    have he1 : Real.exp (-b * H) ≤ 1 := by simpa [H] using hexp1 n
    let profile4 : ℝ := ((1 + H) ^ 2 * Real.exp (-(b / 2) * H)) ^ 2
    have hprofile4 : profile4 = (1 + H) ^ 4 * Real.exp (-b * H) := by
      dsimp [profile4]
      have heq : Real.exp (-(b / 2) * H) ^ 2 = Real.exp (-b * H) := by
        rw [sq, ← Real.exp_add]
        congr 1
        ring
      rw [mul_pow, heq]
      ring
    have hexp_sq : Real.exp (-b * H) ^ 2 ≤ Real.exp (-b * H) := by
      nlinarith [he0.le, he1]
    have hpoly4 : H ^ 2 * (1 + H) ^ 2 * Real.exp (-b * H) ≤
        profile4 := by
      rw [hprofile4]
      have hm := mul_le_mul_of_nonneg_right hpoly
        (mul_nonneg (sq_nonneg (1 + H)) he0.le)
      nlinarith only [hm]
    have hAr : A * rn ≤
        4 * D.model.kstar * T * profile4 := by
      rw [hAeq, hk']
      calc
        4 * D.model.kstar * H ^ 2 * rn ≤
            4 * D.model.kstar * H ^ 2 *
              (T * ((1 + H) ^ 2 * Real.exp (-b * H))) :=
          mul_le_mul_of_nonneg_left hrT (by positivity)
        _ ≤ 4 * D.model.kstar * T * profile4 := by
          calc
            4 * D.model.kstar * H ^ 2 *
                (T * ((1 + H) ^ 2 * Real.exp (-b * H))) =
                (4 * D.model.kstar * T) *
                  (H ^ 2 * (1 + H) ^ 2 * Real.exp (-b * H)) := by ring
            _ ≤ (4 * D.model.kstar * T) *
                  profile4 :=
              mul_le_mul_of_nonneg_left hpoly4
                (mul_nonneg (mul_nonneg (by norm_num) hkpos.le) hT0)
    have hrr : rn ^ 2 ≤ T ^ 2 * profile4 := by
      calc
        rn ^ 2 ≤ (T * ((1 + H) ^ 2 * Real.exp (-b * H))) ^ 2 :=
          (sq_le_sq₀ hr0
            (mul_nonneg hT0 (mul_nonneg (sq_nonneg _) he0.le))).2 hrT
        _ = T ^ 2 * (1 + H) ^ 4 * Real.exp (-b * H) ^ 2 := by ring
        _ ≤ T ^ 2 * (1 + H) ^ 4 * Real.exp (-b * H) :=
          mul_le_mul_of_nonneg_left hexp_sq
            (mul_nonneg (sq_nonneg T) (by positivity))
        _ = T ^ 2 * profile4 := by rw [hprofile4]; ring
    have hquad : 8 * (A * rn) + 8 * rn ^ 2 < b0 := by
      have hbound : 8 * (A * rn) + 8 * rn ^ 2 ≤
          E * profile4 := by
        calc
          8 * (A * rn) + 8 * rn ^ 2 ≤
              8 * (4 * D.model.kstar * T *
                profile4) + 8 * (T ^ 2 * profile4) :=
            add_le_add (mul_le_mul_of_nonneg_left hAr (by norm_num))
              (mul_le_mul_of_nonneg_left hrr (by norm_num))
          _ = E * profile4 := by
            dsimp [E]
            ring
      exact hbound.trans_lt (by simpa [profile4, H] using hsmallE n)
    have hdenom : 0 < A + rn := add_pos_of_pos_of_nonneg (by
      rw [hAeq]
      exact mul_pos (mul_pos (by norm_num) hkpos)
        (sq_pos_of_pos (lt_of_lt_of_le zero_lt_one hH1))) hr0
    have hprod : 8 * rn * (A + rn) ≤
        ConfiguredInductiveTubeBudget.chordBase D'.model * D'.Hs 0 := by
      have hbH : b0 ≤
          ConfiguredInductiveTubeBudget.chordBase D'.model * D'.Hs 0 := by
        calc
          b0 ≤ ConfiguredInductiveTubeBudget.chordBase D'.model := hbaseLower
          _ ≤ ConfiguredInductiveTubeBudget.chordBase D'.model * D'.Hs 0 :=
            le_mul_of_one_le_right
              (le_trans hb0.le hbaseLower) hstart1
      calc
        8 * rn * (A + rn) = 8 * (A * rn) + 8 * rn ^ 2 := by ring
        _ ≤ b0 := hquad.le
        _ ≤ ConfiguredInductiveTubeBudget.chordBase D'.model * D'.Hs 0 := hbH
    unfold rowRhoVariable
    by_cases hbranch : (1 / 2 : ℝ) ≤
        D'.Hs 0 / (2 * (ConfiguredInductiveTubeBudget.accBound D'.model n + rn))
    · rw [min_eq_left hbranch]
      dsimp [rn] at hrSmall ⊢
      nlinarith
    · rw [min_eq_right (le_of_not_ge hbranch)]
      have hdenpos : 0 < 2 * (A + rn) := mul_pos (by norm_num) hdenom
      have heq :
          (ConfiguredInductiveTubeBudget.chordBase D'.model / 2) *
              (D'.Hs 0 / (2 * (A + rn))) =
            ((ConfiguredInductiveTubeBudget.chordBase D'.model / 2) * D'.Hs 0) /
              (2 * (A + rn)) := by ring
      rw [show ConfiguredInductiveTubeBudget.accBound D'.model n = A from rfl, heq]
      rw [le_div_iff₀ hdenpos]
      change 2 * rn * (2 * (A + rn)) ≤
        (ConfiguredInductiveTubeBudget.chordBase D'.model / 2) * D'.Hs 0
      calc
        2 * rn * (2 * (A + rn)) = (8 * rn * (A + rn)) / 2 := by ring
        _ ≤ (ConfiguredInductiveTubeBudget.chordBase D'.model * D'.Hs 0) / 2 :=
          div_le_div_of_nonneg_right hprod (by norm_num)
        _ = (ConfiguredInductiveTubeBudget.chordBase D'.model / 2) * D'.Hs 0 := by
          ring
  have hr0 := hradius0 0
  have hrOne : r 0 ≤ 1 :=
    (hrow 0).trans ((hsmallT 0).le.trans (min_le_left _ _))
  have hgapStart :
      (Real.pi * Cw + (2 * Real.pi + 1) *
        r 0) / 2 < D'.Hs 0 := by
    have hreq : Hgap ≤ D'.Hs 0 := hstartGap
    dsimp [Hgap] at hreq
    have hcoef : 0 ≤ 2 * Real.pi + 1 := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hrOne hcoef]
  have hgap := ClosingGap.width_gap_of_large hCw hr0 hgapStart
  refine ⟨{
    Mtotal := Mtotal
    Mtotal_pos := hMtotal
    N := N
    stage_cap := ?_
    speed_tail := ?_
    chord_tail := ?_
    width_gap := ?_
  }⟩
  · intro n k
    simpa [D', Nat.add_assoc] using hcap (N + n) k
  · simpa [D', r] using hspeed
  · simpa [D', r] using hchord
  · simpa [D', r] using hgap

end ConstructedRowDefectLargeSeparation
