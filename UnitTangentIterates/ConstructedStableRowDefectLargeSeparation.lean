import UnitTangentIterates.ConfiguredScaledStableRowDefectProvider
import UnitTangentIterates.ConstructedRowDefectLargeSeparation

/-!
# Large separation for the stable configured defect

The existing scalar large-separation theorem is reused at amplification factor
one after absorbing the single stable Jacobi constant into the row conversion
coefficient.  Thus the resulting stage error is
`Cstable * rowDefect D (n + k)` and no weighted threshold is assumed.
-/

noncomputable section

open Real

namespace ConstructedStableRowDefectLargeSeparation

open ConfiguredApproximateDefectPathRowwise
open ConstructedConfiguredInductiveTubeBudget.WeightedData

/-- Stable marked shadow radius in row `n`. -/
def rowRadius (A : ℕ → ℝ)
    (D : ConstructedConfiguredSequenceWeighted.Data)
    (Cstable : ℝ) (n : ℕ) : ℝ :=
  A n * ShadowingTails.tail
    (ConfiguredScaledStableRowDefectProvider.error D Cstable n) 0

/-- Absorbing `Cstable` into the conversion coefficient identifies the stable
radius with the old factor-one radius. -/
theorem rowRadius_eq_weight_one
    (A : ℕ → ℝ) (D : ConstructedConfiguredSequenceWeighted.Data)
    (Cstable : ℝ) (n : ℕ) :
    rowRadius A D Cstable n =
      ConstructedRowDefectLargeSeparation.rowRadius
        (fun m => Cstable * A m) D 1 n := by
  rw [rowRadius,
    ConfiguredScaledStableRowDefectProvider.tail_eq_scale]
  unfold ConstructedRowDefectLargeSeparation.rowRadius
  rw [ConfiguredStableRowDefectProvider.error_eq_weight_one]
  have htail : ShadowingTails.tail
      (ConfiguredRowDefectProvider.error D 1 n) 0 =
      ShadowingTails.tail
        (ConstructedRowDefectLargeSeparation.rowError D 1 n) 0 := by
    congr 1
  rw [htail]
  ring

/-- Scalar output needed by the stable recursive construction. -/
structure Output
    (D : ConstructedConfiguredSequenceWeighted.Data)
    (A : ℕ → ℝ) (Cstable Cw : ℝ) where
  Mtotal : ℝ
  Mtotal_pos : 0 < Mtotal
  N : ℕ
  stage_cap : ∀ n k,
    ConfiguredScaledStableRowDefectProvider.error (shift D N) Cstable n k <
      Mtotal
  speed_tail : ∀ n,
    rowRadius (ConstructedRowDefectLargeSeparation.shiftSequence A N)
      (shift D N) Cstable n ≤
      (shift D N).Hs 0
  chord_tail : ∀ n,
    2 * rowRadius (ConstructedRowDefectLargeSeparation.shiftSequence A N)
        (shift D N) Cstable n ≤
      (ConfiguredInductiveTubeBudget.chordBase (shift D N).model / 2) *
        ConstructedRowDefectLargeSeparation.rowRhoVariable
          (shift D N).model
          (rowRadius
            (ConstructedRowDefectLargeSeparation.shiftSequence A N)
            (shift D N) Cstable) n
  width_gap : Cw +
      2 * rowRadius (ConstructedRowDefectLargeSeparation.shiftSequence A N)
        (shift D N) Cstable 0 <
    (2 * (shift D N).Hs 0 -
      rowRadius (ConstructedRowDefectLargeSeparation.shiftSequence A N)
        (shift D N) Cstable 0) / Real.pi

/-- Polynomial/exponential growth of the actual common conversion ceilings is
enough for all stable scalar budgets after discarding a finite prefix.  The
factor-one threshold is proved from the configured model and is not an input. -/
theorem exists_output
    (D : ConstructedConfiguredSequenceWeighted.Data)
    (A : ℕ → ℝ) {Cstable A0 gamma Cw : ℝ}
    (hCstable : 0 ≤ Cstable)
    (hA : ∀ n, 0 ≤ A n) (hA0 : 0 ≤ A0)
    (hgamma : gamma < D.model.beta / 4)
    (hAgrowth : ∀ n, A n ≤ A0 * (1 + D.Hs n) ^ 2 *
      Real.exp (gamma * D.Hs n))
    (hCw : 0 ≤ Cw) :
    Nonempty (Output D A Cstable Cw) := by
  let As : ℕ → ℝ := fun n => Cstable * A n
  have hAs : ∀ n, 0 ≤ As n := fun n => mul_nonneg hCstable (hA n)
  have hAs0 : 0 ≤ Cstable * A0 := mul_nonneg hCstable hA0
  have hAsGrowth : ∀ n, As n ≤
      (Cstable * A0) * (1 + D.Hs n) ^ 2 *
        Real.exp (gamma * D.Hs n) := by
    intro n
    have h := mul_le_mul_of_nonneg_left (hAgrowth n) hCstable
    simpa [As, mul_assoc] using h
  obtain ⟨O⟩ := ConstructedRowDefectLargeSeparation.exists_output
    D As hAs hAs0 hgamma hAsGrowth (K := 1) le_rfl hCw
      (ConfiguredStableRowDefectProvider.unweighted_threshold D)
  let Mstable : ℝ := Cstable * O.Mtotal + 1
  have hMstable : 0 < Mstable := by
    dsimp [Mstable]
    nlinarith [mul_nonneg hCstable O.Mtotal_pos.le]
  have hradiusEq :
      rowRadius
          (ConstructedRowDefectLargeSeparation.shiftSequence A O.N)
          (shift D O.N) Cstable =
        ConstructedRowDefectLargeSeparation.rowRadius
          (ConstructedRowDefectLargeSeparation.shiftSequence As O.N)
          (shift D O.N) 1 := by
    funext n
    rw [rowRadius_eq_weight_one]
    congr 2
  refine ⟨{
    Mtotal := Mstable
    Mtotal_pos := hMstable
    N := O.N
    stage_cap := ?_
    speed_tail := ?_
    chord_tail := ?_
    width_gap := ?_ }⟩
  · intro n k
    by_cases hzero : Cstable = 0
    · simp [ConfiguredScaledStableRowDefectProvider.error, hzero,
        hMstable]
    · have hpos : 0 < Cstable := lt_of_le_of_ne hCstable (Ne.symm hzero)
      have hcap : rowDefect (shift D O.N) (n + k) < O.Mtotal := by
        simpa using O.stage_cap n k
      have hmul := mul_lt_mul_of_pos_left hcap hpos
      dsimp [ConfiguredScaledStableRowDefectProvider.error, Mstable]
      linarith
  · intro n
    rw [hradiusEq]
    exact O.speed_tail n
  · intro n
    rw [hradiusEq]
    exact O.chord_tail n
  · rw [hradiusEq]
    exact O.width_gap

end ConstructedStableRowDefectLargeSeparation
