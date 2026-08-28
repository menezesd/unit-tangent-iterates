import UnitTangentIterates.ModelPeriodContinuity
import UnitTangentIterates.ModelPeriodGrowth
import UnitTangentIterates.PaperHairpinConfig

/-! # Canonical large-separation recurrence -/

noncomputable section

open Real

namespace UnitTangentIterates.CanonicalSeparationRecurrence

open ModelPeriodContinuity

/-- A canonical rear-cell certificate gives the lower half-period estimate as
soon as the front separation dominates the fixed endpoint budget. -/
theorem half_le_rearPeriod_of_rearCell
    {y : ℝ → ℝ} {H B : ℝ}
    (hHB : 4 * B ≤ H)
    (d : PaperHairpinConfig.RearCellData y H (rearPeriod y H) B) :
    H / 2 ≤ rearPeriod y H := by
  have h := d.period_lower
  dsimp [ModelPeriodContinuity.rearPeriod] at h ⊢
  linarith

/-- Positive square mass makes the rear period strictly smaller than the
front period.  This is the strict-growth input for the canonical recurrence. -/
theorem rearPeriod_lt_of_positive_square_mass
    {y : ℝ → ℝ} {C alpha Km H : ℝ}
    (halpha : 0 < alpha) (hH : 0 < H)
    (hyc : Continuous y) (hy0 : ∀ s, 0 ≤ y s)
    (hyKm : ∀ s, y s ≤ Km)
    (hyb : ∀ s, |y s| ≤ C * Real.exp (-alpha * |s|))
    (hsqint : MeasureTheory.Integrable fun s => y s ^ 2)
    (hsqpos : 0 < ∫ s, y s ^ 2)
    (hYle : ∀ s, |ModelOrbitDefect.periodizedPulse y H s| ≤ 1) :
    rearPeriod y H < H := by
  have h := ModelPeriodGrowth.rearPeriod_le_sub
    (y := y) (C := C) (alpha := alpha) (Km := Km)
    halpha hyc hy0 hyKm hyb hsqint hH hYle
  linarith

/-- Uniform canonical rear-cell and strip certificates provide exactly the
two tail estimates consumed by `exists_strict_sequence`. -/
theorem tail_recurrence_bounds
    {y : ℝ → ℝ} {C alpha Km B H0 : ℝ}
    (halpha : 0 < alpha) (hH0 : 0 < H0) (hB : 4 * B ≤ H0)
    (hyc : Continuous y) (hy0 : ∀ s, 0 ≤ y s)
    (hyKm : ∀ s, y s ≤ Km)
    (hyb : ∀ s, |y s| ≤ C * Real.exp (-alpha * |s|))
    (hsqint : MeasureTheory.Integrable fun s => y s ^ 2)
    (hsqpos : 0 < ∫ s, y s ^ 2)
    (hrear : ∀ H, H0 ≤ H →
      PaperHairpinConfig.RearCellData y H (rearPeriod y H) B)
    (hYle : ∀ H, H0 ≤ H → ∀ s,
      |ModelOrbitDefect.periodizedPulse y H s| ≤ 1) :
    (∀ H, H0 ≤ H → H / 2 ≤ rearPeriod y H) ∧
      ∀ H, H0 ≤ H → rearPeriod y H < H := by
  constructor
  · intro H hH
    exact half_le_rearPeriod_of_rearCell (hB.trans hH) (hrear H hH)
  · intro H hH
    exact rearPeriod_lt_of_positive_square_mass halpha (hH0.trans_le hH)
      hyc hy0 hyKm hyb hsqint hsqpos (hYle H hH)

/-- A continuous rear-period map which lies in `[H/2,H)` on a tail admits an
infinite strictly increasing sequence satisfying the paper recurrence
`Q(H_{n+1}) = H_n`. -/
theorem exists_strict_sequence
    {y y' : ℝ → ℝ} {C alpha H0 : ℝ}
    (halpha : 0 < alpha) (hH0 : 0 < H0)
    (hyc : Continuous y)
    (hyderiv : ∀ x, HasDerivAt y (y' x) x)
    (hyb : ∀ x, |y x| ≤ C * Real.exp (-alpha * |x|))
    (hy'b : ∀ x, |y' x| ≤ C * Real.exp (-alpha * |x|))
    (hlower : ∀ H, H0 ≤ H → H / 2 ≤ rearPeriod y H)
    (hstrict : ∀ H, H0 ≤ H → rearPeriod y H < H) :
    ∃ Hs : ℕ → ℝ,
      Hs 0 = H0 ∧
      (∀ n, H0 ≤ Hs n) ∧
      (∀ n, Hs n < Hs (n + 1)) ∧
      ∀ n, rearPeriod y (Hs (n + 1)) = Hs n := by
  have step : ∀ t, H0 ≤ t → ∃ H,
      t < H ∧ H ≤ 2 * t ∧ rearPeriod y H = t := by
    intro t ht
    have ht0 : 0 < t := lt_of_lt_of_le hH0 ht
    have h2base : H0 ≤ 2 * t := by linarith
    have hge : t ≤ rearPeriod y (2 * t) := by
      convert hlower (2 * t) h2base using 1 <;> ring
    obtain ⟨H, htH, hH2, hQ⟩ := exists_rearPeriod_eq
      (y' := y') halpha hyc hyderiv hyb hy'b hge ht0
    have hHbase : H0 ≤ H := ht.trans htH
    have hlt : t < H := by
      have := hstrict H hHbase
      rwa [hQ] at this
    exact ⟨H, hlt, hH2, hQ⟩
  choose next0 hnext0 using step
  -- totalize the step map so that it can be iterated
  let next : ℝ → ℝ := fun t => if h : H0 ≤ t then next0 t h else t
  have hnext : ∀ t, H0 ≤ t →
      t < next t ∧ next t ≤ 2 * t ∧ rearPeriod y (next t) = t := by
    intro t ht
    simp only [next, dif_pos ht]
    exact hnext0 t ht
  let Hs : ℕ → ℝ := fun n => next^[n] H0
  have hbase : ∀ n, H0 ≤ Hs n := by
    intro n
    induction n with
    | zero => exact le_rfl
    | succ n ih =>
        rw [show Hs (n + 1) = next (Hs n) by simp [Hs, Function.iterate_succ_apply']]
        exact ih.trans (hnext (Hs n) ih).1.le
  refine ⟨Hs, by simp [Hs], hbase, ?_, ?_⟩
  · intro n
    rw [show Hs (n + 1) = next (Hs n) by simp [Hs, Function.iterate_succ_apply']]
    exact (hnext (Hs n) (hbase n)).1
  · intro n
    rw [show Hs (n + 1) = next (Hs n) by simp [Hs, Function.iterate_succ_apply']]
    exact (hnext (Hs n) (hbase n)).2.2

end UnitTangentIterates.CanonicalSeparationRecurrence
