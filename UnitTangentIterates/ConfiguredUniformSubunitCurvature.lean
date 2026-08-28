import UnitTangentIterates.ConstructedConfiguredSequenceWeighted
import UnitTangentIterates.PaperHairpinQuantitativeData
import UnitTangentIterates.ProfileConstantsInstance
import UnitTangentIterates.TubeConstants
import UnitTangentIterates.TubeInvariance

/-!
# A uniform subunit curvature ceiling

The selected-rear construction needs one curvature ceiling strictly below
one.  Increasing the cap separation does not improve the two profile-level
lower bounds imposed on `ProfileConstants.kstar`.  This file isolates the
exact additional wide-profile inequality and proves the consequences needed
by the configured model and stopped-curvature argument.

For the barrier-wide choice `a = au = 2 * eps`, `eps <= 1 / 10` already makes
the current-rear bound `a / sqrt (1 - a^2)` strictly smaller than one.  The
only remaining profile obstruction is

`(1 + G (2 * eps) * relativeConst 1) * (2 * eps) < 1`.

This is precisely the quantitative dependence on the barrier parameter that
is not supplied by the current hairpin existence theorem.
-/

noncomputable section

open Real Set

namespace PaperHairpinConfig

/-- Profile constants can be chosen with a prescribed subunit curvature
ceiling once both profile-level curvature expressions lie below it. -/
theorem exists_profileConstants_with_subunit_kstar
    {alpha beta a au CU DU DU2 D k0 : ℝ}
    (hbeta : 0 < beta) (hbetalt : beta < alpha / 2)
    (hD : 0 ≤ D) (hDU : 0 ≤ DU) (hDU2 : 0 ≤ DU2)
    (ha0 : 0 ≤ a) (ha1 : a < 1) (hau0 : 0 ≤ au) (hau1 : au < 1)
    (hprior : (1 + FrontPeriodization.G au * DU) * au ≤ k0)
    (hcurrent : a / Real.sqrt (1 - a ^ 2) ≤ k0)
    (hk0 : k0 < 1) :
    ∃ CK Km Kd kd : ℝ,
      ProfileConstants (alpha := alpha) (beta := beta) (a := a) (au := au)
        (CU := CU) (CK := CK) (DU := DU) (DU2 := DU2) (D := D)
        (Km := Km) (Kd := Kd) (kstar := k0) (kd := kd) ∧ k0 < 1 := by
  let priorDeriv : ℝ := DU * au +
    FrontPeriodization.lipConst au * (DU ^ 2 * au ^ 2) +
    FrontPeriodization.G au * (DU2 * au)
  let currentDeriv : ℝ := ((1 + FrontPeriodization.G a * D) * a + a) /
    Real.sqrt (1 - a ^ 2) ^ 3
  refine ⟨(1 + FrontPeriodization.G au * DU) * CU,
    (1 + FrontPeriodization.G au * DU) * au, priorDeriv,
    max (max currentDeriv priorDeriv) 1, ?_⟩
  refine ⟨{
      derivative_nonneg := hD
      beta_pos := hbeta
      beta_lt := hbetalt
      prior_derivative_nonneg := hDU
      prior_second_nonneg := hDU2
      prior_strip_nonneg := hau0
      current_strip_nonneg := ha0
      current_strip_lt := ha1
      prior_strip_lt := hau1
      isolated_sup := le_rfl
      isolated_decay := le_rfl
      prior_model_sup := hprior
      rear_derivative_pos := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
      current_rear_sup := hcurrent
      current_rear_deriv := le_trans (le_max_left _ _) (le_max_left _ _)
      prior_deriv_sup := le_trans (le_max_right _ _) (le_max_left _ _)
      isolated_deriv_sup := le_rfl }, hk0⟩

end PaperHairpinConfig

namespace PaperHairpinQuantitativeData.Data

/-- The wide-hairpin profile has a subunit `kstar` provided the one remaining
periodized-front expression is subunit.  The selected-current-rear expression
is discharged solely from `eps <= 1/10`. -/
theorem exists_profileConstants_of_wide_with_subunit_kstar
    {f theta x : ℝ → ℝ} {M Delta beta0 C0 Ht eps : ℝ}
    {P Pp : ℝ → ℝ}
    (d : PaperHairpinQuantitativeData.Data f theta x M Delta beta0 C0 Ht P Pp)
    (heps : 0 < eps) (heps' : eps ≤ 1 / 10)
    (hprior :
      (1 + FrontPeriodization.G (2 * eps) * d.relativeConst 1) * (2 * eps) < 1) :
    ∃ alpha beta a au CU CK DU DU2 D Km Kd kstar kd : ℝ,
      PaperHairpinConfig.ProfileConstants
        (alpha := alpha) (beta := beta) (a := a) (au := au)
        (CU := CU) (CK := CK) (DU := DU) (DU2 := DU2) (D := D)
        (Km := Km) (Kd := Kd) (kstar := kstar) (kd := kd) ∧ kstar < 1 := by
  let alpha : ℝ := 1 / M
  let beta : ℝ := alpha / 4
  let a : ℝ := 2 * eps
  let au : ℝ := 2 * eps
  let CU : ℝ := d.decayConst 0
  let DU : ℝ := d.relativeConst 1
  let DU2 : ℝ := d.relativeConst 2
  let D : ℝ := d.relativeConst 1
  let prior : ℝ := (1 + FrontPeriodization.G au * DU) * au
  let current : ℝ := a / Real.sqrt (1 - a ^ 2)
  let kstar : ℝ := max prior current
  have hM : 0 < M := d.M_pos
  have halpha : 0 < alpha := by
    dsimp [alpha]
    exact div_pos one_pos hM
  have hbeta : 0 < beta := by
    dsimp [beta]
    linarith
  have hbetalt : beta < alpha / 2 := by
    dsimp [beta]
    linarith
  have ha0 : 0 ≤ a := by dsimp [a]; positivity
  have hau0 : 0 ≤ au := by dsimp [au]; positivity
  have ha_le : a ≤ 1 / 5 := by
    dsimp [a]
    linarith
  have hau_le : au ≤ 1 / 5 := by
    dsimp [au]
    linarith
  have ha1 : a < 1 := lt_of_le_of_lt ha_le (by norm_num)
  have hau1 : au < 1 := lt_of_le_of_lt hau_le (by norm_num)
  have ha_sq_le : a ^ 2 ≤ (1 / 5 : ℝ) ^ 2 :=
    (sq_le_sq₀ ha0 (by norm_num)).2 ha_le
  have hrad : 0 < 1 - a ^ 2 := by nlinarith
  have hsqrt : 0 < Real.sqrt (1 - a ^ 2) := Real.sqrt_pos.2 hrad
  have ha_sqrt : a < Real.sqrt (1 - a ^ 2) :=
    (Real.lt_sqrt ha0).2 (by nlinarith)
  have hcurrent_lt : current < 1 := by
    dsimp [current]
    exact (div_lt_one hsqrt).2 ha_sqrt
  have hprior_lt : prior < 1 := by simpa [prior, au, DU] using hprior
  have hkstar : kstar < 1 := by
    simpa [kstar] using (max_lt hprior_lt hcurrent_lt)
  obtain ⟨CK, Km, Kd, kd, profile, -⟩ :=
    PaperHairpinConfig.exists_profileConstants_with_subunit_kstar
      (alpha := alpha) (beta := beta) (a := a) (au := au)
      (CU := CU) (DU := DU) (DU2 := DU2) (D := D) (k0 := kstar)
      hbeta hbetalt (d.relativeConst_nonneg 1) (d.relativeConst_nonneg 1)
      (d.relativeConst_nonneg 2) ha0 ha1 hau0 hau1
      (le_max_left _ _) (le_max_right _ _) hkstar
  exact ⟨alpha, beta, a, au, CU, CK, DU, DU2, D, Km, Kd, kstar, kd,
    profile, hkstar⟩

end PaperHairpinQuantitativeData.Data

namespace ConstructedConfiguredSequenceWeighted

/-- A configured sequence has the paper's low-curvature margin when its
retained global model bound lies below a fixed `k0 < 1`. -/
structure SubunitCurvatureCeiling (D : Data) where
  k0 : ℝ
  kstar_le : D.kstar ≤ k0
  k0_lt_one : k0 < 1

namespace SubunitCurvatureCeiling

variable {D : Data} (S : SubunitCurvatureCeiling D)

/-- Every configured model edge is nonnegative and bounded by the common
subunit ceiling. -/
theorem modelCurvature_mem (n : ℕ) (s : ℝ) :
    0 ≤ ModelOrbitDefect.modelCurvature (D.model.configs n).yu
        (D.model.configs n).yu' (D.Hs n) s ∧
      ModelOrbitDefect.modelCurvature (D.model.configs n).yu
        (D.model.configs n).yu' (D.Hs n) s ≤ S.k0 := by
  constructor
  · exact (D.model.configs n).KP_nonneg s
  · calc
      ModelOrbitDefect.modelCurvature (D.model.configs n).yu
          (D.model.configs n).yu' (D.Hs n) s
          ≤ D.model.kstar := (D.model.configs n).KP_le s
      _ = D.kstar := D.model_kstar
      _ ≤ S.k0 := S.kstar_le

/-- The named model curvature `D.kappas n` obeys the same uniform ceiling. -/
theorem kappas_mem (n : ℕ) (s : ℝ) :
    0 ≤ D.kappas n s ∧ D.kappas n s ≤ S.k0 := by
  rw [D.model.curvature_eq n]
  exact S.modelCurvature_mem n s

/-- The intermediate and propagated ceilings used by the stopped-curvature
argument are both strictly below one. -/
theorem derived_ceilings_lt_one :
    TubeConstants.kbar S.k0 < 1 ∧ TubeConstants.khat S.k0 < 1 := by
  constructor
  · unfold TubeConstants.kbar
    linarith [S.k0_lt_one]
  · unfold TubeConstants.khat
    linarith [S.k0_lt_one]

/-- A normal path starting at a configured model edge stays below the first
uniform ceiling when its cost fits the model-to-tube margin. -/
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
    (hsmall : (1 + TubeConstants.kbar S.k0 ^ 2) * PathMetric.NormalPath.cost Gamma <
      TubeConstants.kbar S.k0 - S.k0) :
    ∀ t ∈ Icc (0 : ℝ) 1, ∀ u, kappa t u < TubeConstants.kbar S.k0 := by
  apply TubeInvariance.curvature_lt_of_cost Gamma hT hbdd hderiv hint hnonneg
    (fun x => ?_) hsmall
  rw [hinit x]
  exact (S.kappas_mem n x).2

/-- Once a recursive front is bounded by `kbar`, one further controlled normal
path stays below the final common ceiling `khat < 1`. -/
theorem curvature_lt_khat_of_recursive_path
    {p q : MarkedSpace.Data} (Gamma : PathMetric.NormalPath p q)
    (hT : Gamma.T = 1) {kappa : ℝ → ℝ → ℝ}
    (hbdd : ∀ t, BddAbove (Set.range fun u =>
      |iteratedDeriv 2 (Gamma.eta t) u|))
    (hderiv : ∀ t x, HasDerivAt (fun r => kappa r x)
      (iteratedDeriv 2 (Gamma.eta t) x + (kappa t x) ^ 2 * Gamma.eta t x) t)
    (hint : ∀ x, IntervalIntegrable
      (fun r => iteratedDeriv 2 (Gamma.eta r) x +
        (kappa r x) ^ 2 * Gamma.eta r x) MeasureTheory.volume 0 1)
    (hnonneg : ∀ r x, 0 ≤ kappa r x)
    (hinit : ∀ x, kappa 0 x ≤ TubeConstants.kbar S.k0)
    (hsmall : (1 + TubeConstants.khat S.k0 ^ 2) * PathMetric.NormalPath.cost Gamma <
      TubeConstants.khat S.k0 - TubeConstants.kbar S.k0) :
    ∀ t ∈ Icc (0 : ℝ) 1, ∀ u, kappa t u < TubeConstants.khat S.k0 := by
  exact TubeInvariance.curvature_lt_of_cost Gamma hT hbdd hderiv hint hnonneg
    hinit hsmall

end SubunitCurvatureCeiling

end ConstructedConfiguredSequenceWeighted
