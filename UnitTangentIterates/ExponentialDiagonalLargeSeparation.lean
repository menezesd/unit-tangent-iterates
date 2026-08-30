import UnitTangentIterates.ConstructedRowDefectLargeSeparation

/-!
# Large separation for an exponentially decaying diagonal defect

This is the scalar theorem needed when the stable component conversion is
row-dependent.  The recursive error is exactly `d (n+k)`.  No power is
introduced.  A direct exponential estimate on `d`, together with polynomial
growth of the row conversion, gives the same tube and closing budgets as the
configured fixed-factor theorem.
-/

noncomputable section

set_option maxHeartbeats 2000000

open Real Filter

namespace ExponentialDiagonalLargeSeparation

open ConstructedConfiguredInductiveTubeBudget
open ConstructedConfiguredInductiveTubeBudget.WeightedData
open ConstructedRowDefectLargeSeparation
open PathMetric.WeightedRecursiveDefect

def rowError (d : ℕ → ℝ) (n k : ℕ) : ℝ := d (n + k)

def rowRadius (C d : ℕ → ℝ) (n : ℕ) : ℝ :=
  C n * ShadowingTails.tail (rowError d n) 0

def shiftSequence (f : ℕ → ℝ) (N n : ℕ) : ℝ := f (N + n)

theorem shifted_tail_le_exp
    (D : ConstructedConfiguredSequenceWeighted.Data)
    {d : ℕ → ℝ} {A b : ℝ}
    (hA : 0 ≤ A) (hb : 0 < b) (hd0 : ∀ n, 0 ≤ d n)
    (hdexp : ∀ n, d n ≤ A * Real.exp (-(b * D.Hs n)))
    (N n : ℕ) :
    ShadowingTails.tail (rowError (shiftSequence d N) n) 0 ≤
      (A / (1 - Real.exp (-(b * D.deltaStep)))) *
        Real.exp (-(b * (shift D N).Hs n)) := by
  let q : ℝ := Real.exp (-(b * D.deltaStep))
  have hq0 : 0 ≤ q := (Real.exp_pos _).le
  have hq1 : q < 1 := by
    dsimp [q]
    rw [Real.exp_lt_one_iff]
    exact neg_neg_of_pos (mul_pos hb D.deltaStep_pos)
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
          _ ≤ D.Hs (N + n + k) + D.deltaStep := by linarith only [ih]
          _ ≤ D.Hs (N + n + (k + 1)) := by simpa [Nat.add_assoc] using hs
  have hdgeo : ∀ k : ℕ, shiftSequence d N (n + k) ≤
      A * Real.exp (-(b * (shift D N).Hs n)) * q ^ k := by
    intro k
    have he : Real.exp (-(b * D.Hs (N + (n + k)))) ≤
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
      shiftSequence d N (n + k) = d (N + (n + k)) := rfl
      _ ≤ A * Real.exp (-(b * D.Hs (N + (n + k)))) := hdexp _
      _ ≤ A * (Real.exp (-(b * D.Hs (N + n))) * q ^ k) :=
        mul_le_mul_of_nonneg_left he hA
      _ = A * Real.exp (-(b * (shift D N).Hs n)) * q ^ k := by
        change A * (Real.exp (-(b * D.Hs (N + n))) * q ^ k) =
          A * Real.exp (-(b * D.Hs (N + n))) * q ^ k
        ring
  have hactual : Summable (fun k ↦ shiftSequence d N (n + k)) := by
    exact Summable.of_nonneg_of_le
      (fun k ↦ hd0 (N + (n + k))) hdgeo
      ((summable_geometric_of_lt_one hq0 hq1).mul_left
        (A * Real.exp (-(b * (shift D N).Hs n))))
  have hmajor : Summable (fun k : ℕ ↦
      (A * Real.exp (-(b * (shift D N).Hs n))) * q ^ k) :=
    (summable_geometric_of_lt_one hq0 hq1).mul_left _
  have hsum := hactual.tsum_le_tsum hdgeo hmajor
  have hgeom : (∑' k : ℕ,
      (A * Real.exp (-(b * (shift D N).Hs n))) * q ^ k) =
      (A / (1 - q)) * Real.exp (-(b * (shift D N).Hs n)) := by
    rw [tsum_mul_left, tsum_geometric_of_lt_one hq0 hq1]
    field_simp [ne_of_gt (sub_pos.mpr hq1)]
  unfold ShadowingTails.tail rowError
  rw [hgeom] at hsum
  simpa [q, Nat.add_assoc] using hsum

theorem shifted_rowRadius_le_exp
    (D : ConstructedConfiguredSequenceWeighted.Data)
    (C d : ℕ → ℝ) {C0 A b gamma : ℝ}
    (hC : ∀ n, 0 ≤ C n) (hC0 : 0 ≤ C0)
    (hA : 0 ≤ A) (hb : 0 < b) (hgamma : gamma < b)
    (hCgrowth : ∀ n, C n ≤ C0 * (1 + D.Hs n) ^ 2 *
      Real.exp (gamma * D.Hs n))
    (hd0 : ∀ n, 0 ≤ d n)
    (hdexp : ∀ n, d n ≤ A * Real.exp (-(b * D.Hs n)))
    (N n : ℕ) :
    rowRadius (shiftSequence C N) (shiftSequence d N) n ≤
      (C0 * (A / (1 - Real.exp (-(b * D.deltaStep))))) *
        ((1 + (shift D N).Hs n) ^ 2 *
          Real.exp (-((b - gamma) * (shift D N).Hs n))) := by
  let T := A / (1 - Real.exp (-(b * D.deltaStep)))
  have htail := shifted_tail_le_exp D hA hb hd0 hdexp N n
  have htail0 : 0 ≤ ShadowingTails.tail
      (rowError (shiftSequence d N) n) 0 :=
    ShadowingTails.tail_nonneg (fun k ↦ hd0 (N + (n + k))) 0
  have hCg := hCgrowth (N + n)
  have hprod := mul_le_mul hCg htail htail0
    (mul_nonneg (mul_nonneg hC0 (sq_nonneg _)) (Real.exp_pos _).le)
  calc
    rowRadius (shiftSequence C N) (shiftSequence d N) n =
        C (N + n) * ShadowingTails.tail
          (rowError (shiftSequence d N) n) 0 := rfl
    _ ≤ (C0 * (1 + D.Hs (N + n)) ^ 2 *
          Real.exp (gamma * D.Hs (N + n))) *
        (T * Real.exp (-(b * (shift D N).Hs n))) := hprod
    _ = (C0 * T) * ((1 + (shift D N).Hs n) ^ 2 *
          Real.exp (-((b - gamma) * (shift D N).Hs n))) := by
      rw [show D.Hs (N + n) = (shift D N).Hs n from rfl]
      calc
        C0 * (1 + (shift D N).Hs n) ^ 2 *
              Real.exp (gamma * (shift D N).Hs n) *
              (T * Real.exp (-(b * (shift D N).Hs n))) =
            C0 * T * (1 + (shift D N).Hs n) ^ 2 *
              (Real.exp (gamma * (shift D N).Hs n) *
                Real.exp (-(b * (shift D N).Hs n))) := by ring
        _ = C0 * T * (1 + (shift D N).Hs n) ^ 2 *
              Real.exp (gamma * (shift D N).Hs n +
                -(b * (shift D N).Hs n)) := by rw [← Real.exp_add]
        _ = _ := by ring
    _ = _ := rfl

structure Output
    (D : ConstructedConfiguredSequenceWeighted.Data)
    (C d : ℕ → ℝ) (Cw : ℝ) where
  Mtotal : ℝ
  Mtotal_pos : 0 < Mtotal
  N : ℕ
  separation_one : 1 ≤ (WeightedData.shift D N).Hs 0
  stage_cap : ∀ n k, shiftSequence d N (n + k) < Mtotal
  speed_tail : ∀ n,
    rowRadius (shiftSequence C N) (shiftSequence d N) n ≤ (shift D N).Hs 0
  chord_tail : ∀ n,
    2 * rowRadius (shiftSequence C N) (shiftSequence d N) n ≤
      (ConfiguredInductiveTubeBudget.chordBase (shift D N).model / 2) *
        rowRhoVariable (shift D N).model
          (rowRadius (shiftSequence C N) (shiftSequence d N)) n
  width_gap : Cw +
      2 * rowRadius (shiftSequence C N) (shiftSequence d N) 0 <
    (2 * (shift D N).Hs 0 -
      rowRadius (shiftSequence C N) (shiftSequence d N) 0) / Real.pi
  radius_small : ∀ n,
    rowRadius (shiftSequence C N) (shiftSequence d N) n < 1 / 10

theorem exists_output
    (D : ConstructedConfiguredSequenceWeighted.Data)
    (C d : ℕ → ℝ) {C0 A b gamma Cw : ℝ}
    (hC : ∀ n, 0 ≤ C n) (hC0 : 0 ≤ C0)
    (hA : 0 ≤ A) (hb : 0 < b) (hgamma : gamma < b)
    (hCgrowth : ∀ n, C n ≤ C0 * (1 + D.Hs n) ^ 2 *
      Real.exp (gamma * D.Hs n))
    (hd0 : ∀ n, 0 ≤ d n)
    (hdexp : ∀ n, d n ≤ A * Real.exp (-(b * D.Hs n)))
    (hCw : 0 ≤ Cw) : Nonempty (Output D C d Cw) := by
  have hsum : Summable d := by
    let q := Real.exp (-(b * D.deltaStep))
    let A0 := A * Real.exp (-(b * D.Hs 0))
    have hq0 : 0 ≤ q := (Real.exp_pos _).le
    have hq1 : q < 1 := by
      dsimp [q]
      rw [Real.exp_lt_one_iff]
      exact neg_neg_of_pos (mul_pos hb D.deltaStep_pos)
    have hgeo : ∀ n, d n ≤ A0 * q ^ n := by
      intro n
      apply (hdexp n).trans
      have he : Real.exp (-(b * D.Hs n)) ≤
          Real.exp (-(b * (D.Hs 0 + n * D.deltaStep))) := by
        apply Real.exp_le_exp.mpr
        nlinarith [D.separation_linear n]
      calc
        A * Real.exp (-(b * D.Hs n)) ≤
            A * Real.exp (-(b * (D.Hs 0 + n * D.deltaStep))) :=
          mul_le_mul_of_nonneg_left he hA
        _ = A0 * q ^ n := by
          dsimp [A0, q]
          calc
            A * Real.exp (-(b * (D.Hs 0 + (n : ℝ) * D.deltaStep))) =
                A * (Real.exp (-(b * D.Hs 0)) *
                  Real.exp (-(b * ((n : ℝ) * D.deltaStep)))) := by
              rw [← Real.exp_add]
              congr 2
              ring
            _ = A * Real.exp (-(b * D.Hs 0)) *
                Real.exp ((n : ℝ) * -(b * D.deltaStep)) := by ring
            _ = _ := by rw [Real.exp_nat_mul]
    exact Summable.of_nonneg_of_le hd0 hgeo
      ((summable_geometric_of_lt_one hq0 hq1).mul_left A0)
  have hone : (1 : ℝ) ≤ 1 := le_rfl
  have hweighted : Summable (weightedDefect 1 d) := by
    convert hsum using 1
    funext n
    simp [weightedDefect]
  obtain ⟨Mtotal, hMtotal, hcap⟩ :=
    exists_uniform_weighted_stage_cap hone hd0 hweighted
  let b' := b - gamma
  let T := C0 * (A / (1 - Real.exp (-(b * D.deltaStep))))
  have hb' : 0 < b' := sub_pos.mpr hgamma
  have hden : 0 < 1 - Real.exp (-(b * D.deltaStep)) := by
    exact sub_pos.mpr (by
      rw [Real.exp_lt_one_iff]
      exact neg_neg_of_pos (mul_pos hb D.deltaStep_pos))
  have hT0 : 0 ≤ T := by
    dsimp [T]
    exact mul_nonneg hC0 (div_nonneg hA hden.le)
  have hkpos : 0 < D.model.kstar := configured_kstar_pos D.model
  let b0 : ℝ := min 1 (Real.pi / (6 * D.model.kstar))
  have hb0 : 0 < b0 := lt_min zero_lt_one
    (div_pos Real.pi_pos (mul_pos (by norm_num) hkpos))
  let E : ℝ := 32 * D.model.kstar * T + 8 * T ^ 2
  have hE0 : 0 ≤ E := by dsimp [E]; positivity
  have htail2 := MainThresholds.tendsto_tail_zero hb'
  have htail4 := (MainThresholds.tendsto_tail_zero (half_pos hb')).pow 2
  have hTlim := htail2.const_mul T
  have hElim := htail4.const_mul E
  simp only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero] at htail4 hElim
  simp only [mul_zero] at hTlim
  have htarget : 0 < min (1 / 10) (b0 / 8) :=
    lt_min (by norm_num) (div_pos hb0 (by norm_num))
  have hevT : ∀ᶠ H : ℝ in atTop,
      T * ((1 + H) ^ 2 * Real.exp (-b' * H)) < min (1 / 10) (b0 / 8) :=
    (tendsto_order.1 hTlim).2 _ htarget
  have hevE : ∀ᶠ H : ℝ in atTop,
      E * (((1 + H) ^ 2 * Real.exp (-(b' / 2) * H)) ^ 2) < b0 :=
    (tendsto_order.1 hElim).2 _ hb0
  obtain ⟨HT, hHT⟩ := Filter.eventually_atTop.1 hevT
  obtain ⟨HE, hHE⟩ := Filter.eventually_atTop.1 hevE
  let Hgap : ℝ := (Real.pi * Cw + (2 * Real.pi + 1)) / 2 + 1
  let Hmin : ℝ := max Hgap (max 1 (max HT HE))
  obtain ⟨N, hN⟩ := exists_shift_above D Hmin
  let D' := shift D N
  let r : ℕ → ℝ := rowRadius (shiftSequence C N) (shiftSequence d N)
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
      T * ((1 + D'.Hs n) ^ 2 * Real.exp (-b' * D'.Hs n)) := by
    intro n
    convert shifted_rowRadius_le_exp D C d hC hC0 hA hb hgamma
      hCgrowth hd0 hdexp N n using 1 <;> dsimp [r, D', T, b'] <;> ring
  have hlarge : ∀ n, 1 ≤ D'.Hs n := fun n =>
    hstart1.trans (D'.separation_lower n)
  have hsmallT : ∀ n,
      T * ((1 + D'.Hs n) ^ 2 * Real.exp (-b' * D'.Hs n)) <
        min (1 / 10) (b0 / 8) := fun n =>
    hHT _ (hstartT.trans (D'.separation_lower n))
  have hsmallE : ∀ n,
      E * (((1 + D'.Hs n) ^ 2 * Real.exp (-(b' / 2) * D'.Hs n)) ^ 2) < b0 :=
    fun n => hHE _ (hstartE.trans (D'.separation_lower n))
  have hexp1 : ∀ n, Real.exp (-b' * D'.Hs n) ≤ 1 := by
    intro n
    exact Real.exp_le_one_iff.mpr
      (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hb'.le)
        (zero_le_one.trans (hlarge n)))
  have hspeed : ∀ n, r n ≤ D'.Hs 0 := by
    intro n
    exact (hrow n).trans
      ((hsmallT n).le.trans
        ((min_le_left _ _).trans
          ((show (1 / 10 : ℝ) ≤ 1 by norm_num).trans hstart1)))
  have hbaseLower : b0 ≤ ConfiguredInductiveTubeBudget.chordBase D'.model := by
    rw [chordBase_eq_min D'.model (configured_kstar_pos D'.model)]
    exact min_le_min hstart1 le_rfl
  have hradius0 : ∀ n, 0 ≤ r n := by
    intro n
    exact mul_nonneg (hC (N + n))
      (ShadowingTails.tail_nonneg (fun k ↦ hd0 (N + (n + k))) 0)
  have hchord : ∀ n,
      2 * r n ≤ (ConfiguredInductiveTubeBudget.chordBase D'.model / 2) *
        rowRhoVariable D'.model r n := by
    intro n
    let rn := r n
    let H := D'.Hs n
    let Acc := ConfiguredInductiveTubeBudget.accBound D'.model n
    have hr0 : 0 ≤ rn := hradius0 n
    have hH1 : 1 ≤ H := hlarge n
    have he0 : 0 < Real.exp (-b' * H) := Real.exp_pos _
    have hrT : rn ≤ T * ((1 + H) ^ 2 * Real.exp (-b' * H)) := hrow n
    have hrSmall : rn ≤ b0 / 8 :=
      hrT.trans ((hsmallT n).le.trans (min_le_right _ _))
    have hAeq : Acc = 4 * D'.model.kstar * H ^ 2 := by
      simp [Acc, H, ConfiguredInductiveTubeBudget.accBound]
      ring
    have hA0' : 0 ≤ Acc := by rw [hAeq]; positivity
    have hk' : D'.model.kstar = D.model.kstar := rfl
    have hpoly : H ^ 2 ≤ (1 + H) ^ 2 := by nlinarith [hH1]
    have he1 : Real.exp (-b' * H) ≤ 1 := by simpa [H] using hexp1 n
    let profile4 : ℝ := ((1 + H) ^ 2 * Real.exp (-(b' / 2) * H)) ^ 2
    have hprofile4 : profile4 = (1 + H) ^ 4 * Real.exp (-b' * H) := by
      dsimp [profile4]
      have heq : Real.exp (-(b' / 2) * H) ^ 2 = Real.exp (-b' * H) := by
        rw [sq, ← Real.exp_add]
        congr 1
        ring
      rw [mul_pow, heq]
      ring
    have hexp_sq : Real.exp (-b' * H) ^ 2 ≤ Real.exp (-b' * H) := by
      nlinarith [he0.le, he1]
    have hpoly4 : H ^ 2 * (1 + H) ^ 2 * Real.exp (-b' * H) ≤ profile4 := by
      rw [hprofile4]
      have hm := mul_le_mul_of_nonneg_right hpoly
        (mul_nonneg (sq_nonneg (1 + H)) he0.le)
      nlinarith only [hm]
    have hAr : Acc * rn ≤ 4 * D.model.kstar * T * profile4 := by
      rw [hAeq, hk']
      calc
        4 * D.model.kstar * H ^ 2 * rn ≤
            4 * D.model.kstar * H ^ 2 *
              (T * ((1 + H) ^ 2 * Real.exp (-b' * H))) :=
          mul_le_mul_of_nonneg_left hrT (by positivity)
        _ ≤ 4 * D.model.kstar * T * profile4 := by
          calc
            _ = (4 * D.model.kstar * T) *
                (H ^ 2 * (1 + H) ^ 2 * Real.exp (-b' * H)) := by ring
            _ ≤ _ := mul_le_mul_of_nonneg_left hpoly4
              (mul_nonneg (mul_nonneg (by norm_num) hkpos.le) hT0)
    have hrr : rn ^ 2 ≤ T ^ 2 * profile4 := by
      calc
        rn ^ 2 ≤ (T * ((1 + H) ^ 2 * Real.exp (-b' * H))) ^ 2 :=
          (sq_le_sq₀ hr0
            (mul_nonneg hT0 (mul_nonneg (sq_nonneg _) he0.le))).2 hrT
        _ = T ^ 2 * (1 + H) ^ 4 * Real.exp (-b' * H) ^ 2 := by ring
        _ ≤ T ^ 2 * (1 + H) ^ 4 * Real.exp (-b' * H) :=
          mul_le_mul_of_nonneg_left hexp_sq
            (mul_nonneg (sq_nonneg T) (by positivity))
        _ = T ^ 2 * profile4 := by rw [hprofile4]; ring
    have hquad : 8 * (Acc * rn) + 8 * rn ^ 2 < b0 := by
      have hbound : 8 * (Acc * rn) + 8 * rn ^ 2 ≤ E * profile4 := by
        calc
          _ ≤ 8 * (4 * D.model.kstar * T * profile4) +
              8 * (T ^ 2 * profile4) :=
            add_le_add (mul_le_mul_of_nonneg_left hAr (by norm_num))
              (mul_le_mul_of_nonneg_left hrr (by norm_num))
          _ = E * profile4 := by dsimp [E]; ring
      exact hbound.trans_lt (by simpa [profile4, H] using hsmallE n)
    have hdenom : 0 < Acc + rn := add_pos_of_pos_of_nonneg (by
      rw [hAeq]
      exact mul_pos (mul_pos (by norm_num) hkpos)
        (sq_pos_of_pos (lt_of_lt_of_le zero_lt_one hH1))) hr0
    have hprod : 8 * rn * (Acc + rn) ≤
        ConfiguredInductiveTubeBudget.chordBase D'.model * D'.Hs 0 := by
      have hbH : b0 ≤ ConfiguredInductiveTubeBudget.chordBase D'.model *
          D'.Hs 0 := by
        calc
          b0 ≤ ConfiguredInductiveTubeBudget.chordBase D'.model := hbaseLower
          _ ≤ ConfiguredInductiveTubeBudget.chordBase D'.model * D'.Hs 0 :=
            le_mul_of_one_le_right (hbaseLower.trans' hb0.le) hstart1
      calc
        8 * rn * (Acc + rn) = 8 * (Acc * rn) + 8 * rn ^ 2 := by ring
        _ ≤ b0 := hquad.le
        _ ≤ ConfiguredInductiveTubeBudget.chordBase D'.model * D'.Hs 0 := hbH
    unfold rowRhoVariable
    by_cases hbranch : (1 / 2 : ℝ) ≤ D'.Hs 0 /
        (2 * (ConfiguredInductiveTubeBudget.accBound D'.model n + rn))
    · rw [min_eq_left hbranch]
      dsimp [rn] at hrSmall ⊢
      nlinarith
    · rw [min_eq_right (le_of_not_ge hbranch)]
      have hdenpos : 0 < 2 * (Acc + rn) := mul_pos (by norm_num) hdenom
      have heq : (ConfiguredInductiveTubeBudget.chordBase D'.model / 2) *
          (D'.Hs 0 / (2 * (Acc + rn))) =
          ((ConfiguredInductiveTubeBudget.chordBase D'.model / 2) * D'.Hs 0) /
            (2 * (Acc + rn)) := by ring
      rw [show ConfiguredInductiveTubeBudget.accBound D'.model n = Acc from rfl, heq]
      rw [le_div_iff₀ hdenpos]
      change 2 * rn * (2 * (Acc + rn)) ≤
        (ConfiguredInductiveTubeBudget.chordBase D'.model / 2) * D'.Hs 0
      calc
        2 * rn * (2 * (Acc + rn)) = (8 * rn * (Acc + rn)) / 2 := by ring
        _ ≤ (ConfiguredInductiveTubeBudget.chordBase D'.model * D'.Hs 0) / 2 :=
          div_le_div_of_nonneg_right hprod (by norm_num)
        _ = (ConfiguredInductiveTubeBudget.chordBase D'.model / 2) * D'.Hs 0 := by ring
  have hr0 := hradius0 0
  have hrOne : r 0 ≤ 1 :=
    (hrow 0).trans ((hsmallT 0).le.trans
      ((min_le_left _ _).trans (show (1 / 10 : ℝ) ≤ 1 by norm_num)))
  have hradiusSmall : ∀ n, r n < 1 / 10 := by
    intro n
    exact (hrow n).trans_lt ((hsmallT n).trans_le (min_le_left _ _))
  have hgapStart :
      (Real.pi * Cw + (2 * Real.pi + 1) * r 0) / 2 < D'.Hs 0 := by
    have hreq : Hgap ≤ D'.Hs 0 := hstartGap
    dsimp [Hgap] at hreq
    have hcoef : 0 ≤ 2 * Real.pi + 1 := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hrOne hcoef]
  have hgap := ClosingGap.width_gap_of_large hCw hr0 hgapStart
  refine ⟨{
    Mtotal := Mtotal
    Mtotal_pos := hMtotal
    N := N
    separation_one := hstart1
    stage_cap := ?_
    speed_tail := hspeed
    chord_tail := hchord
    width_gap := hgap
    radius_small := hradiusSmall }⟩
  intro n k
  simpa [weightedDefect, shiftSequence, Nat.add_assoc] using hcap (N + n) k

end ExponentialDiagonalLargeSeparation
