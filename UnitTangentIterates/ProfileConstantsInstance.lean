import UnitTangentIterates.PaperHairpinConfig

/-!
# The profile-constants record is consistent

`PaperHairpinConfig.ProfileConstants` bundles seventeen conditions relating the
shape constants of the configured-model development.  Every downstream theorem
takes it as a hypothesis, and nothing in the development had ever exhibited an
instance — so in principle the record could have been contradictory, and every
theorem depending on it vacuous.

It is not.  `exists_profileConstants` constructs an instance from the shape data
alone.  The point is structural: each of the seventeen conditions is either a
sign condition on the given data, or a *lower bound* on one of the five
constants `CK, Km, Kd, kstar, kd`, so they can all be met by taking those five
large enough.  The witness here takes each to be the largest of its lower
bounds (and `kd` at least one, since it must be strictly positive).
-/


noncomputable section

set_option maxHeartbeats 4000000

open Set Real

namespace PaperHairpinConfig

/-- **`ProfileConstants` is satisfiable.**  Given the shape data
`alpha, beta, a, au, CU, DU, DU2, D` with the sign and strip conditions, the
remaining constants `CK, Km, Kd, kstar, kd` can be chosen — each condition is a
lower bound on one of them. -/
theorem exists_profileConstants {alpha beta a au CU DU DU2 D : ℝ}
    (hbeta : 0 < beta) (hbetalt : beta < alpha / 2)
    (hD : 0 ≤ D) (hDU : 0 ≤ DU) (hDU2 : 0 ≤ DU2)
    (ha0 : 0 ≤ a) (ha1 : a < 1) (hau0 : 0 ≤ au) (hau1 : au < 1) :
    ∃ CK Km Kd kstar kd : ℝ,
      ProfileConstants (alpha := alpha) (beta := beta) (a := a) (au := au)
        (CU := CU) (CK := CK) (DU := DU) (DU2 := DU2) (D := D)
        (Km := Km) (Kd := Kd) (kstar := kstar) (kd := kd) := by
  refine ⟨(1 + FrontPeriodization.G au * DU) * CU,
    (1 + FrontPeriodization.G au * DU) * au,
    DU * au + FrontPeriodization.lipConst au * (DU ^ 2 * au ^ 2)
      + FrontPeriodization.G au * (DU2 * au),
    max ((1 + FrontPeriodization.G au * DU) * au) (a / Real.sqrt (1 - a ^ 2)),
    max (max (((1 + FrontPeriodization.G a * D) * a + a)
        / Real.sqrt (1 - a ^ 2) ^ 3)
      (DU * au + FrontPeriodization.lipConst au * (DU ^ 2 * au ^ 2)
        + FrontPeriodization.G au * (DU2 * au))) 1, ?_⟩
  exact
    { derivative_nonneg := hD
      beta_pos := hbeta
      beta_lt := hbetalt
      prior_derivative_nonneg := hDU
      prior_second_nonneg := hDU2
      prior_strip_nonneg := hau0
      current_strip_nonneg := ha0
      current_strip_lt := ha1
      prior_strip_lt := hau1
      isolated_sup := le_refl _
      isolated_decay := le_refl _
      prior_model_sup := le_max_left _ _
      rear_derivative_pos := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
      current_rear_sup := le_max_right _ _
      current_rear_deriv := le_trans (le_max_left _ _) (le_max_left _ _)
      prior_deriv_sup := le_trans (le_max_right _ _) (le_max_left _ _)
      isolated_deriv_sup := le_refl _ }

end PaperHairpinConfig
