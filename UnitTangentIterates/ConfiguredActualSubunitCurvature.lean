import UnitTangentIterates.ConfiguredUniformSubunitCurvature
import UnitTangentIterates.WideHairpinLocalBounds
import UnitTangentIterates.ConstructedConfiguredInductiveTubeBudget

/-!
# Actual curvature ceilings, independent of matching constants

`ConfiguredModelSequence.kstar` is allowed to be a coarse constant used in the
matching estimate.  The selected inverse only needs a bound for the actual
front and rear curvatures.  This module records that separate invariant.
-/

noncomputable section

open Real Set HairpinRelative

namespace ConfiguredActualSubunitCurvature

/-- The isolated barrier hairpin has intrinsic curvature at most `1/20` once
the width parameter is at most `1/40`. -/
theorem isolated_curvature_le_one_twenty
    {eps : ℝ} {f : ℝ → ℝ} (heps : 0 < eps) (heps40 : eps ≤ 1 / 40)
    (hfl : ∀ t ∈ Icc (0 : ℝ) Real.pi, Barriers.fMinus eps t ≤ f t)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) Real.pi) :
    curvField f t ≤ 1 / 20 := by
  have heps10 : eps ≤ 1 / 10 := heps40.trans (by norm_num)
  exact (WideHairpinLocalBounds.curvField_le_two_mul_on heps heps10 hfl ht).trans
    (by linarith)

/-- A direct subunit certificate for the actual configured orbit.  It does
not constrain the coarse matching constant `D.kstar`. -/
structure Certificate (D : ConstructedConfiguredSequenceWeighted.Data) where
  k0 : ℝ
  k0_lt_one : k0 < 1
  front_nonnegative : ∀ n s, 0 ≤ D.kappas n s
  front_le : ∀ n s, D.kappas n s ≤ k0
  rear_nonnegative : ∀ n s, 0 ≤ (D.model.configs n).kH s
  rear_le : ∀ n s, (D.model.configs n).kH s ≤ k0

namespace Certificate

variable {D : ConstructedConfiguredSequenceWeighted.Data} (C : Certificate D)

/-- The stopped-curvature estimate propagates the actual model ceiling to the
first recursive tube ceiling. -/
theorem curvature_lt_kbar_of_model_path
    {p q : MarkedSpace.Data} (n : ℕ) (Gamma : PathMetric.NormalPath p q)
    (hT : Gamma.T = 1) {kappa : ℝ → ℝ → ℝ}
    (hbdd : ∀ t, BddAbove (Set.range fun u =>
      |iteratedDeriv 2 (Gamma.eta t) u|))
    (hderiv : ∀ t x, HasDerivAt (fun r => kappa r x)
      (iteratedDeriv 2 (Gamma.eta t) x + (kappa t x) ^ 2 * Gamma.eta t x) t)
    (hint : ∀ x, IntervalIntegrable
      (fun r => iteratedDeriv 2 (Gamma.eta r) x +
        (kappa r x) ^ 2 * Gamma.eta r x) MeasureTheory.volume 0 1)
    (hnonneg : ∀ r x, 0 ≤ kappa r x)
    (hinit : ∀ x, kappa 0 x = D.kappas n x)
    (hsmall : (1 + TubeConstants.kbar C.k0 ^ 2) *
      PathMetric.NormalPath.cost Gamma < TubeConstants.kbar C.k0 - C.k0) :
    ∀ t ∈ Icc (0 : ℝ) 1, ∀ u, kappa t u < TubeConstants.kbar C.k0 := by
  apply TubeInvariance.curvature_lt_of_cost Gamma hT hbdd hderiv hint hnonneg
    (fun x => ?_) hsmall
  rw [hinit x]
  exact C.front_le n x

/-- Both recursive ceilings derived from the actual model bound remain
strictly below one. -/
theorem derived_ceilings_lt_one :
    TubeConstants.kbar C.k0 < 1 ∧ TubeConstants.khat C.k0 < 1 := by
  constructor
  · unfold TubeConstants.kbar
    linarith [C.k0_lt_one]
  · unfold TubeConstants.khat
    linarith [C.k0_lt_one]

/-- The actual-curvature certificate is invariant under deleting a finite
prefix of the configured sequence. -/
def shift (N : ℕ) :
    Certificate
      (ConstructedConfiguredInductiveTubeBudget.WeightedData.shift D N) where
  k0 := C.k0
  k0_lt_one := C.k0_lt_one
  front_nonnegative := by
    intro n s
    simpa [ConstructedConfiguredInductiveTubeBudget.WeightedData.shift] using
      C.front_nonnegative (N + n) s
  front_le := by
    intro n s
    simpa [ConstructedConfiguredInductiveTubeBudget.WeightedData.shift] using
      C.front_le (N + n) s
  rear_nonnegative := by
    intro n s
    simpa [ConstructedConfiguredInductiveTubeBudget.WeightedData.shift] using
      C.rear_nonnegative (N + n) s
  rear_le := by
    intro n s
    simpa [ConstructedConfiguredInductiveTubeBudget.WeightedData.shift] using
      C.rear_le (N + n) s

@[simp] theorem shift_k0 (N : ℕ) : (C.shift N).k0 = C.k0 := rfl

end Certificate

/-- The exact rear formula is subunit whenever the actual periodized steering
pulse has square below `1/2`.  This avoids the coarse `Config.hkstar` bound. -/
theorem rear_curvature_lt_one_of_periodizedPulse_sq_lt_half
    {alpha beta a au C CU CK DU DU2 D Km Kd B theta0 kstar kd eps0 H P : ℝ}
    (c : ModelOrbitDefect.Config alpha beta a au C CU CK DU DU2 D Km Kd B
      theta0 kstar kd eps0 H P)
    (hY : ∀ s, (c.Y s) ^ 2 < 1 / 2) :
    ∀ r, c.kH r < 1 := by
  intro r
  rw [c.kH_eq, c.tan_dl]
  have hY0 := c.Y_nonneg (c.sf r)
  have hsq := hY (c.sf r)
  have hrad : 0 < 1 - (c.Y (c.sf r)) ^ 2 := by linarith
  have hsqrt : 0 < Real.sqrt (1 - (c.Y (c.sf r)) ^ 2) := Real.sqrt_pos.2 hrad
  rw [div_lt_one hsqrt]
  exact (Real.lt_sqrt hY0).2 (by linarith)

/-- Backwards-compatible strengthened weighted data carrying the correct
actual-orbit ceiling. -/
structure WeightedDataWithActualCeiling where
  data : ConstructedConfiguredSequenceWeighted.Data
  actualCeiling : Certificate data

/-- The constructed half-ceiling package is exactly an actual-curvature
certificate; positivity comes from the configured construction, not from the
coarse matching ceiling. -/
def ofDataWithActualHalf
    (E : ConstructedConfiguredSequenceWeighted.DataWithActualHalf) :
    Certificate E.data where
  k0 := 1 / 2
  k0_lt_one := by norm_num
  front_nonnegative := fun n s => (E.data.model_curvature_pos n s).le
  front_le := E.front_le_half
  rear_nonnegative := fun n s => (E.data.model.configs n).kH_nonneg s
  rear_le := E.rear_le_half

/-- The canonical half certificate for a shifted strengthened sequence. -/
def ofShiftedDataWithActualHalf
    (E : ConstructedConfiguredSequenceWeighted.DataWithActualHalf) (N : ℕ) :
    Certificate
      (ConstructedConfiguredInductiveTubeBudget.WeightedData.shift E.data N) :=
  ofDataWithActualHalf
    (ConstructedConfiguredInductiveTubeBudget.WeightedData.shiftActualHalf E N)

/-- A TeX-faithful actual subunit ceiling is constructed above every
prescribed initial separation. -/
theorem exists_weightedDataWithActualCeiling_above_of_eps
    (Hrequired : ℝ) {eps : ℝ} (heps : 0 < eps) (heps10 : eps ≤ 1 / 10) :
    ∃ E : WeightedDataWithActualCeiling, Hrequired ≤ E.data.Hs 0 := by
  obtain ⟨D, hD⟩ :=
    ConstructedConfiguredSequenceWeighted.exists_dataWithActualHalf_above_of_eps
      Hrequired heps heps10
  exact ⟨⟨D.data, ofDataWithActualHalf D⟩, hD⟩

/-- The unthresholded compatibility façade. -/
theorem exists_weightedDataWithActualCeiling_of_eps
    {eps : ℝ} (heps : 0 < eps) (heps10 : eps ≤ 1 / 10) :
    Nonempty WeightedDataWithActualCeiling := by
  obtain ⟨E, -⟩ :=
    exists_weightedDataWithActualCeiling_above_of_eps 0 heps heps10
  exact ⟨E⟩

end ConfiguredActualSubunitCurvature
