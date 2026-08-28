import UnitTangentIterates.CanonicalConsecutiveBasicAdapters

/-! # Canonical consecutive hairpin configuration wrapper -/


open scoped ContDiff
open ShiftedCurvatureJetMajorant
open PaperHairpinQuantitativeData
open PaperHairpinQuantitativeData.ConsecutiveData

namespace PaperHairpinConfig.PaperHairpinData

/-- The strongest canonical same-profile Config constructor currently
supported by the paper APIs.  Profile-side analytic, phase, normalization,
continuity and current-mass fields are discharged.  The remaining arguments
are precisely the separation-dependent geometric certificates. -/
theorem exists_threshold_toConfig_of_canonical_consecutive
    {f theta x g gp yp : ℝ → ℝ} {M Delta beta0 Cq Ht : ℝ} {Pfun Pp : ℝ → ℝ}
    {alpha beta a au C CU CK DU DU2 D Km Kd B theta0 kstar kd eps0 : ℝ}
    (c : ConsecutiveData f theta x g gp yp M Delta beta0 Cq Ht Pfun Pp)
    (d : CanonicalTranslatorLocalPhase.InteriorPhaseData f theta x g gp)
    (hf : ContDiff ℝ ∞ f)
    (hfpos : ∀ t, 0 < f t)
    (profile : ProfileConstants (alpha := alpha) (beta := beta) (a := a)
      (au := au) (CU := CU) (CK := CK) (DU := DU) (DU2 := DU2) (D := D)
      (Km := Km) (Kd := Kd) (kstar := kstar) (kd := kd))
    (heps : 0 < eps0) (halpha : 0 ≤ alpha)
    (hdec0 : ∀ s, |currentPulse f theta x s| ≤ C * Real.exp (-alpha * |s|))
    (hdec1 : ∀ s, |yp s| ≤ C * Real.exp (-alpha * |s|))
    (hCU : C * Real.exp (alpha * |phase f theta g|) ≤ CU)
    (hD : c.quantitative.relativeConst 1 ≤ D)
    (hDU : c.quantitative.relativeConst 1 ≤ DU)
    (hDU2 : c.quantitative.relativeConst 2 ≤ DU2) :
    ∃ Hs : ℝ, 0 ≤ Hs ∧ ∀ Hnext Hcurr b : ℝ,
      Hs ≤ Hnext →
      (∀ u, (∑' m : ℤ, shift (phase f theta g) (currentPulse f theta x)
        (u - m * Hcurr)) ≤ au) →
      PeriodizedStripData (currentPulse f theta x) alpha C Hnext b →
      b + 4 * C * Real.exp (-(alpha / 2) * Hnext) ≤ a →
      CurvaturePositivityData (previousPulse f theta x g)
        (previousPulseDeriv f theta g yp) Hcurr →
      RearCellData (currentPulse f theta x) Hnext Hcurr B →
      Nonempty {cfg : ModelOrbitDefect.Config alpha beta a au C CU CK DU DU2 D
          Km Kd B theta0 kstar kd eps0 Hnext Hcurr //
        cfg.y = currentPulse f theta x ∧ cfg.yu = previousPulse f theta x g ∧
          cfg.yu' = previousPulseDeriv f theta g yp} := by
  obtain ⟨Hs, hHs0, hbuild⟩ :=
    exists_threshold_toConfig_of_consecutive (C := C) (B := B) (theta0 := theta0)
      profile heps
  refine ⟨Hs, hHs0, ?_⟩
  intro Hnext Hcurr b hH hpriorStrip hstrip hbudget hpositive hrear
  obtain ⟨y2, hanalytic⟩ := c.pulsePairAnalyticData_of_quantitative
    (c.currentPulse_nonneg hfpos) halpha hdec0 hdec1 hCU hD hDU hDU2 hpriorStrip
  exact hbuild Hnext Hcurr b (currentPulse f theta x) yp
    (previousPulse f theta x g) (previousPulseDeriv f theta g yp)
    (shift (phase f theta g) y2) x hH hanalytic hstrip hbudget hpositive
    hrear.period_def hrear.left_endpoint hrear.right_endpoint hrear.period_lower
    (c.quantitative.smooth_pulse 0).continuous d.x_zero (c.current_x_deriv hf hfpos)
    (CanonicalTranslatorLocalPhase.canonical_local_phase c d)
    c.currentPulse_massData c.previousPulse_massData

/-- Variant of the canonical constructor in which the positivity certificate
is assembled from the paper's large-period inequalities.  Thus the caller
supplies only the genuinely geometric lower comparison; summability of the
isolated curvature is discharged by the canonical pulse package. -/
theorem exists_threshold_toConfig_of_canonical_consecutive_of_lower
    {f theta x g gp yp : ℝ → ℝ} {M Delta beta0 Cq Ht : ℝ} {Pfun Pp : ℝ → ℝ}
    {alpha beta a au C CU CK DU DU2 D Km Kd B theta0 kstar kd eps0 : ℝ}
    (c : ConsecutiveData f theta x g gp yp M Delta beta0 Cq Ht Pfun Pp)
    (d : CanonicalTranslatorLocalPhase.InteriorPhaseData f theta x g gp)
    (hf : ContDiff ℝ ∞ f) (hfpos : ∀ t, 0 < f t)
    (profile : ProfileConstants (alpha := alpha) (beta := beta) (a := a)
      (au := au) (CU := CU) (CK := CK) (DU := DU) (DU2 := DU2) (D := D)
      (Km := Km) (Kd := Kd) (kstar := kstar) (kd := kd))
    (heps : 0 < eps0) (halpha : 0 < alpha)
    (hdec0 : ∀ s, |currentPulse f theta x s| ≤ C * Real.exp (-alpha * |s|))
    (hdec1 : ∀ s, |yp s| ≤ C * Real.exp (-alpha * |s|))
    (hCU : C * Real.exp (alpha * |phase f theta g|) ≤ CU)
    (hD : c.quantitative.relativeConst 1 ≤ D)
    (hDU : c.quantitative.relativeConst 1 ≤ DU)
    (hDU2 : c.quantitative.relativeConst 2 ≤ DU2)
    {Hnext Hcurr b b0 : ℝ}
    (hbase : ∀ u, (∑' m : ℤ, shift (phase f theta g)
      (currentPulse f theta x) (u - m * Hcurr)) ≤ au)
    (hstrip : PeriodizedStripData (currentPulse f theta x) alpha C Hnext b)
    (hbudget : b + 4 * C * Real.exp (-(alpha / 2) * Hnext) ≤ a)
    (hb0 : 0 < b0)
    (hlower : ∀ s, b0 * previousPulse f theta x g s ≤
      ModelOrbitDefect.hairpinCurvature (previousPulse f theta x g)
        (previousPulseDeriv f theta g yp) s)
    (hq : Real.exp (-alpha * Hcurr) ≤ 1 / 2)
    (hsep : 8 * FrontPeriodization.lipConst au * DU * CU *
      Real.exp (-(alpha / 2) * Hcurr) ≤ b0)
    (hHcurr : 0 < Hcurr)
    (hrear : RearCellData (currentPulse f theta x) Hnext Hcurr B)
    (hHnext : 0 ≤ Hnext) :
    ∃ Hs : ℝ, 0 ≤ Hs ∧ (Hs ≤ Hnext →
      Nonempty {cfg : ModelOrbitDefect.Config alpha beta a au C CU CK DU DU2 D
          Km Kd B theta0 kstar kd eps0 Hnext Hcurr //
        cfg.y = currentPulse f theta x ∧ cfg.yu = previousPulse f theta x g ∧
          cfg.yu' = previousPulseDeriv f theta g yp}) := by
  obtain ⟨y2, han⟩ := c.pulsePairAnalyticData_of_quantitative
    (c.currentPulse_nonneg hfpos) halpha.le hdec0 hdec1 hCU hD hDU hDU2 hbase
  have hsum := han.previousHairpinCurvature_summable halpha hHcurr
    profile.prior_derivative_nonneg profile.prior_strip_lt
  have hpositive : CurvaturePositivityData (previousPulse f theta x g)
      (previousPulseDeriv f theta g yp) Hcurr :=
    CurvaturePositivityData.of_large_period halpha hHcurr hq han.previous_nonneg
      han.previous_decay profile.prior_derivative_nonneg han.previous_relative
      profile.prior_strip_nonneg profile.prior_strip_lt han.previous_periodized_strip
      hb0.le hlower hsum hsep
  obtain ⟨Hs, hHs, hbuild⟩ := exists_threshold_toConfig_of_canonical_consecutive
    c d hf hfpos profile heps halpha.le hdec0 hdec1 hCU hD hDU hDU2
  exact ⟨Hs, hHs, fun hH => hbuild Hnext Hcurr b hH hbase hstrip hbudget
    hpositive hrear⟩

/-- Canonical version of the preceding constructor: the positive lower
comparison constant is produced from the fixed translator profile. -/
theorem exists_lowerConstant_and_threshold_toConfig_of_canonical_consecutive
    {f theta x g gp yp : ℝ → ℝ} {M Delta beta0 Cq Ht : ℝ} {Pfun Pp : ℝ → ℝ}
    {alpha beta a au C CU CK DU DU2 D Km Kd B theta0 kstar kd eps0 : ℝ}
    (c : ConsecutiveData f theta x g gp yp M Delta beta0 Cq Ht Pfun Pp)
    (d : CanonicalTranslatorLocalPhase.InteriorPhaseData f theta x g gp)
    (hf : ContDiff ℝ ∞ f) (hfpos : ∀ t, 0 < f t)
    (profile : ProfileConstants (alpha := alpha) (beta := beta) (a := a)
      (au := au) (CU := CU) (CK := CK) (DU := DU) (DU2 := DU2) (D := D)
      (Km := Km) (Kd := Kd) (kstar := kstar) (kd := kd))
    (heps : 0 < eps0) (halpha : 0 < alpha)
    (hdec0 : ∀ s, |currentPulse f theta x s| ≤ C * Real.exp (-alpha * |s|))
    (hdec1 : ∀ s, |yp s| ≤ C * Real.exp (-alpha * |s|))
    (hCU : C * Real.exp (alpha * |phase f theta g|) ≤ CU)
    (hD : c.quantitative.relativeConst 1 ≤ D)
    (hDU : c.quantitative.relativeConst 1 ≤ DU)
    (hDU2 : c.quantitative.relativeConst 2 ≤ DU2)
    {Hnext Hcurr b : ℝ}
    (hbase : ∀ u, (∑' m : ℤ, shift (phase f theta g)
      (currentPulse f theta x) (u - m * Hcurr)) ≤ au)
    (hstrip : PeriodizedStripData (currentPulse f theta x) alpha C Hnext b)
    (hbudget : b + 4 * C * Real.exp (-(alpha / 2) * Hnext) ≤ a)
    (hq : Real.exp (-alpha * Hcurr) ≤ 1 / 2)
    (hHcurr : 0 < Hcurr)
    (hrear : RearCellData (currentPulse f theta x) Hnext Hcurr B)
    (hHnext : 0 ≤ Hnext) :
    ∃ b0 : ℝ, 0 < b0 ∧
      (8 * FrontPeriodization.lipConst au * DU * CU *
        Real.exp (-(alpha / 2) * Hcurr) ≤ b0 →
      ∃ Hs : ℝ, 0 ≤ Hs ∧ (Hs ≤ Hnext →
        Nonempty {cfg : ModelOrbitDefect.Config alpha beta a au C CU CK DU DU2 D
            Km Kd B theta0 kstar kd eps0 Hnext Hcurr //
          cfg.y = currentPulse f theta x ∧ cfg.yu = previousPulse f theta x g ∧
            cfg.yu' = previousPulseDeriv f theta g yp})) := by
  obtain ⟨b0, hb0, hlower⟩ := c.exists_previous_lower_comparison d hf hfpos
  refine ⟨b0, hb0, fun hsep => ?_⟩
  exact exists_threshold_toConfig_of_canonical_consecutive_of_lower
    c d hf hfpos profile heps halpha hdec0 hdec1 hCU hD hDU hDU2
    hbase hstrip hbudget hb0 hlower hq hsep hHcurr hrear hHnext

/-- All positivity inequalities and the general Config smallness inequalities
are absorbed into one separation threshold.  What remains are the exact
periodized-strip and rear-cell certificates, since these encode the chosen
relation between two consecutive periods rather than mere largeness. -/
theorem exists_separationThreshold_toConfig_of_canonical_consecutive
    {f theta x g gp yp : ℝ → ℝ} {M Delta beta0 Cq Ht : ℝ} {Pfun Pp : ℝ → ℝ}
    {alpha beta a au C CU CK DU DU2 D Km Kd B theta0 kstar kd eps0 : ℝ}
    (c : ConsecutiveData f theta x g gp yp M Delta beta0 Cq Ht Pfun Pp)
    (d : CanonicalTranslatorLocalPhase.InteriorPhaseData f theta x g gp)
    (hf : ContDiff ℝ ∞ f) (hfpos : ∀ t, 0 < f t)
    (profile : ProfileConstants (alpha := alpha) (beta := beta) (a := a)
      (au := au) (CU := CU) (CK := CK) (DU := DU) (DU2 := DU2) (D := D)
      (Km := Km) (Kd := Kd) (kstar := kstar) (kd := kd))
    (heps : 0 < eps0) (halpha : 0 < alpha)
    (hdec0 : ∀ s, |currentPulse f theta x s| ≤ C * Real.exp (-alpha * |s|))
    (hdec1 : ∀ s, |yp s| ≤ C * Real.exp (-alpha * |s|))
    (hCU : C * Real.exp (alpha * |phase f theta g|) ≤ CU)
    (hD : c.quantitative.relativeConst 1 ≤ D)
    (hDU : c.quantitative.relativeConst 1 ≤ DU)
    (hDU2 : c.quantitative.relativeConst 2 ≤ DU2) :
    ∃ Hstar : ℝ, 0 ≤ Hstar ∧ ∀ Hnext Hcurr b : ℝ,
      Hstar ≤ Hnext → Hstar ≤ Hcurr →
      (∀ u, (∑' m : ℤ, shift (phase f theta g)
        (currentPulse f theta x) (u - m * Hcurr)) ≤ au) →
      PeriodizedStripData (currentPulse f theta x) alpha C Hnext b →
      b + 4 * C * Real.exp (-(alpha / 2) * Hnext) ≤ a →
      RearCellData (currentPulse f theta x) Hnext Hcurr B →
      Nonempty {cfg : ModelOrbitDefect.Config alpha beta a au C CU CK DU DU2 D
          Km Kd B theta0 kstar kd eps0 Hnext Hcurr //
        cfg.y = currentPulse f theta x ∧ cfg.yu = previousPulse f theta x g ∧
          cfg.yu' = previousPulseDeriv f theta g yp} := by
  obtain ⟨b0, hb0, hlower⟩ := c.exists_previous_lower_comparison d hf hfpos
  obtain ⟨Hp, hHp0, hHp⟩ :=
    FrontPeriodizationPositivity.exists_largePeriod_positivity_threshold
      (a := au) (D := DU) (C := CU)
      halpha hb0 profile.prior_strip_nonneg profile.prior_strip_lt
      profile.prior_derivative_nonneg (by
        have h0 := (abs_nonneg (currentPulse f theta x 0)).trans (hdec0 0)
        simp only [abs_zero, neg_mul, mul_zero, neg_zero, Real.exp_zero,
          mul_one] at h0
        have hexp : (0 : ℝ) ≤ Real.exp (alpha * |phase f theta g|) :=
          (Real.exp_pos _).le
        linarith [mul_nonneg h0 hexp, hCU])
  obtain ⟨Hc, hHc0, hbuild⟩ := exists_threshold_toConfig_of_canonical_consecutive
    c d hf hfpos profile heps halpha.le hdec0 hdec1 hCU hD hDU hDU2
  refine ⟨max Hp Hc, le_trans hHp0.le (le_max_left Hp Hc), ?_⟩
  intro Hnext Hcurr b hnext hcurr hbase hstrip hbudget hrear
  have hp := hHp Hcurr (le_trans (le_max_left Hp Hc) hcurr)
  have hc : Hc ≤ Hnext := le_trans (le_max_right Hp Hc) hnext
  obtain ⟨y2, han⟩ := c.pulsePairAnalyticData_of_quantitative
    (c.currentPulse_nonneg hfpos) halpha.le hdec0 hdec1 hCU hD hDU hDU2 hbase
  have hsum := han.previousHairpinCurvature_summable halpha hp.1
    profile.prior_derivative_nonneg profile.prior_strip_lt
  have hpositive : CurvaturePositivityData (previousPulse f theta x g)
      (previousPulseDeriv f theta g yp) Hcurr :=
    CurvaturePositivityData.of_large_period halpha hp.1 hp.2.1
      han.previous_nonneg han.previous_decay profile.prior_derivative_nonneg
      han.previous_relative profile.prior_strip_nonneg profile.prior_strip_lt
      han.previous_periodized_strip hb0.le hlower hsum hp.2.2
  exact hbuild Hnext Hcurr b hc hbase hstrip hbudget hpositive hrear

end PaperHairpinConfig.PaperHairpinData

