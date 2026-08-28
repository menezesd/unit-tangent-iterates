import UnitTangentIterates.ConstructedModelGeometry
import UnitTangentIterates.FrontPeriodizationPositivity

/-!
# Strict positivity upgrade for constructed model geometry

The existing large-period threshold is applied with `b₀ / 2`, leaving a
strict comparison margin.  Pointwise positivity of the isolated pulse then
makes the periodized pulse positive, so the standard periodization-error
argument gives strictly positive model curvature.

The final section records all downstream consequences.  A pointwise-positive
configured sequence automatically has an `n`-dependent positive curvature
floor by compactness of one period; no uniform floor is used.
-/

noncomputable section

open scoped ContDiff
open Real Set Function
open ModelOrbitDefect UnconditionalAssembly ConstructedModelGeometry
open PaperHairpinConfig PaperHairpinQuantitativeData
open PaperHairpinQuantitativeData.ConsecutiveData

namespace StrictConstructedModelGeometry

/-- The steering pulse is strictly positive at every interior angle. -/
theorem pulseField_pos_interior
    {f : ℝ → ℝ} {t : ℝ}
    (hfpos : ∀ z ∈ Ioo (0 : ℝ) π, 0 < f z)
    (ht : t ∈ Ioo (0 : ℝ) π) :
    0 < HairpinRelative.pulseField f t := by
  exact div_pos (HairpinRelative.curvField_pos_interior hfpos ht)
    (HairpinRelative.sqrt_one_add_sq_pos _)

/-- The prior pulse used by every canonical edge is a translate of the same
strictly positive interior pulse. -/
theorem previousPulse_pos_interior
    {f theta x g : ℝ → ℝ}
    (hfpos : ∀ z ∈ Ioo (0 : ℝ) π, 0 < f z)
    (hmem : ∀ u, theta u ∈ Ioo (0 : ℝ) π) :
    ∀ s, 0 < PaperHairpinQuantitativeData.ConsecutiveData.previousPulse
      f theta x g s := by
  intro s
  exact pulseField_pos_interior hfpos
    (hmem (x (s - PaperHairpinQuantitativeData.ConsecutiveData.phase f theta g)))

/-- The existing non-strict threshold can always be chosen with a strict
overlap margin. -/
theorem exists_largePeriod_strict_positivity_threshold
    {alpha a D C b0 : ℝ} (halpha : 0 < alpha) (hb0 : 0 < b0)
    (ha0 : 0 ≤ a) (ha1 : a < 1) (hD : 0 ≤ D) (hC : 0 ≤ C) :
    ∃ P0 : ℝ, 0 < P0 ∧ ∀ P ≥ P0,
      0 < P ∧ exp (-alpha * P) ≤ 1 / 2 ∧
        8 * FrontPeriodization.lipConst a * D * C *
          exp (-(alpha / 2) * P) < b0 := by
  obtain ⟨P0, hP0, hthreshold⟩ :=
    FrontPeriodizationPositivity.exists_largePeriod_positivity_threshold
      halpha (half_pos hb0) ha0 ha1 hD hC
  refine ⟨P0, hP0, fun P hP => ?_⟩
  obtain ⟨hPpos, hq, hsep⟩ := hthreshold P hP
  exact ⟨hPpos, hq, lt_of_le_of_lt hsep (half_lt_self hb0)⟩

/-- Strict version of the elementary lower-comparison/error argument. -/
theorem periodized_front_pos_of_error
    {y Kstar KP : ℝ → ℝ} {P b0 E : ℝ}
    (hy0 : ∀ s, 0 ≤ y s) (hypos : ∀ s, 0 < y s)
    (hE : E < b0)
    (hlower : ∀ s, b0 * y s ≤ Kstar s)
    (hySumm : ∀ r, Summable fun m : ℤ => y (r - m * P))
    (hKSumm : ∀ r, Summable fun m : ℤ => Kstar (r - m * P))
    (herr : ∀ r,
      |KP r - ∑' m : ℤ, Kstar (r - m * P)|
        ≤ E * ∑' m : ℤ, y (r - m * P)) :
    ∀ r, 0 < KP r := by
  intro r
  have hzero : y r ≤ ∑' m : ℤ, y (r - m * P) := by
    simpa using (hySumm r).le_tsum 0 (fun m _ => hy0 (r - m * P))
  have hYpos : 0 < ∑' m : ℤ, y (r - m * P) :=
    lt_of_lt_of_le (hypos r) hzero
  have hsum : b0 * (∑' m : ℤ, y (r - m * P)) ≤
      ∑' m : ℤ, Kstar (r - m * P) :=
    FrontPeriodizationPositivity.tsum_lower_comparison
      (hySumm r) (hKSumm r) hlower
  have herrLower : -(E * ∑' m : ℤ, y (r - m * P)) ≤
      KP r - ∑' m : ℤ, Kstar (r - m * P) :=
    neg_le_of_abs_le (herr r)
  have hcoeff : E * (∑' m : ℤ, y (r - m * P)) <
      b0 * ∑' m : ℤ, y (r - m * P) :=
    mul_lt_mul_of_pos_right hE hYpos
  linarith

/-- Strict large-period positivity for the model curvature. -/
theorem modelCurvature_pos_of_large_period
    {y yd : ℝ → ℝ} {C alpha P D a b0 : ℝ}
    (halpha : 0 < alpha) (hP : 0 < P)
    (hq : exp (-alpha * P) ≤ 1 / 2)
    (hy0 : ∀ s, 0 ≤ y s) (hypos : ∀ s, 0 < y s)
    (hyb : ∀ s, y s ≤ C * exp (-alpha * |s|))
    (hD : 0 ≤ D) (hyd : ∀ s, |yd s| ≤ D * y s)
    (ha0 : 0 ≤ a) (ha1 : a < 1)
    (hYa : ∀ u, (∑' m : ℤ, y (u - m * P)) ≤ a)
    (hlower : ∀ s, b0 * y s ≤ hairpinCurvature y yd s)
    (hKSumm : ∀ r, Summable fun m : ℤ =>
      hairpinCurvature y yd (r - m * P))
    (hsep : 8 * FrontPeriodization.lipConst a * D * C *
      exp (-(alpha / 2) * P) < b0) :
    ∀ r, 0 < modelCurvature y yd P r := by
  have habs : ∀ s, |y s| ≤ C * exp (-alpha * |s|) := fun s => by
    rw [abs_of_nonneg (hy0 s)]
    exact hyb s
  have hySumm : ∀ r, Summable fun m : ℤ => y (r - m * P) := fun r =>
    FrontPeriodizationIntegral.summable_translates halpha hP habs r
  have hcell : ∀ u, |u| ≤ P / 2 → 0 < modelCurvature y yd P u := by
    intro u hu
    have hover := FrontPeriodizationPositivity.overlapDensity_le_cell
      halpha hP hq hy0 hyb hu
    have herr0 := FrontPeriodizationIntegral.front_error_tsum_le
      (y := y) (yp := yd) (C := C) (alpha := alpha) (P := P) (D := D) (a := a)
      halpha hP hy0 hyb hD hyd ha0 ha1 hYa u
    have hLip0 : 0 ≤ FrontPeriodization.lipConst a :=
      FrontPeriodization.lipConst_nonneg ha0 ha1
    have hfac0 : 0 ≤ FrontPeriodization.lipConst a * D := mul_nonneg hLip0 hD
    have herrRaw :
        |modelCurvature y yd P u -
            ∑' m : ℤ, hairpinCurvature y yd (u - m * P)|
          ≤ FrontPeriodization.lipConst a * D *
              ∑' m : ℤ, y (u - m * P) *
                ((∑' j : ℤ, y (u - j * P)) - y (u - m * P)) := by
      simpa [modelCurvature, periodizedPulse, hairpinCurvature] using herr0
    have herr :
        |modelCurvature y yd P u -
            ∑' m : ℤ, hairpinCurvature y yd (u - m * P)|
          ≤ (8 * FrontPeriodization.lipConst a * D * C *
              exp (-(alpha / 2) * P)) *
              ∑' m : ℤ, y (u - m * P) := by
      have hmul := mul_le_mul_of_nonneg_left hover hfac0
      exact herrRaw.trans (by
        calc
          FrontPeriodization.lipConst a * D *
                ∑' m : ℤ, y (u - m * P) *
                  ((∑' j : ℤ, y (u - j * P)) - y (u - m * P))
              ≤ FrontPeriodization.lipConst a * D *
                  (8 * C * exp (-(alpha / 2) * P) *
                    ∑' m : ℤ, y (u - m * P)) := hmul
          _ = (8 * FrontPeriodization.lipConst a * D * C *
                exp (-(alpha / 2) * P)) *
                ∑' m : ℤ, y (u - m * P) := by ring)
    have hzero : y u ≤ ∑' m : ℤ, y (u - m * P) := by
      simpa using (hySumm u).le_tsum 0 (fun m _ => hy0 (u - m * P))
    have hYpos : 0 < ∑' m : ℤ, y (u - m * P) :=
      lt_of_lt_of_le (hypos u) hzero
    have hsum : b0 * (∑' m : ℤ, y (u - m * P)) ≤
        ∑' m : ℤ, hairpinCurvature y yd (u - m * P) :=
      FrontPeriodizationPositivity.tsum_lower_comparison
        (hySumm u) (hKSumm u) hlower
    have herrLower := neg_le_of_abs_le herr
    have hcoeff :
        (8 * FrontPeriodization.lipConst a * D * C *
            exp (-(alpha / 2) * P)) * (∑' m : ℤ, y (u - m * P)) <
          b0 * ∑' m : ℤ, y (u - m * P) :=
      mul_lt_mul_of_pos_right hsep hYpos
    linarith
  have hper : Periodic (modelCurvature y yd P) P := by
    simpa [modelCurvature, periodizedPulse] using
      PeriodizedTurning.periodic_frontCurv y yd P
  intro r
  obtain ⟨v, hv, heq⟩ := hper.exists_mem_Ico₀ hP r
  rw [show modelCurvature y yd P r = modelCurvature y yd P v from heq]
  rcases le_or_gt v (P / 2) with huv | huv
  · exact hcell v (by rw [abs_of_nonneg hv.1]; exact huv)
  · have hshift := hper (v - P)
    simp only [sub_add_cancel] at hshift
    rw [hshift]
    refine hcell (v - P) ?_
    rw [abs_le]
    constructor <;> linarith [hv.2]

/-- Sibling of the canonical configured-sequence capstone which starts beyond
a strict positivity threshold and retains pointwise positivity of every model
curvature.  The old public capstone is unchanged. -/
theorem exists_strict_configuredModelSequence_above
    {f theta x g gp yp : ℝ → ℝ} {M Delta beta0 Cq Ht : ℝ} {Pfun Pp : ℝ → ℝ}
    {alpha beta a au C CU CK DU DU2 D Km Kd B theta0 kstar kd eps0 b : ℝ}
    (Hrequired : ℝ)
    (c : ConsecutiveData f theta x g gp yp M Delta beta0 Cq Ht Pfun Pp)
    (d : CanonicalTranslatorLocalPhase.InteriorPhaseData f theta x g gp)
    {At Mt D1 m Am : ℝ}
    (hf : ContDiffOn ℝ ∞ f (Ioo 0 π))
    (hfpos : ∀ t ∈ Ioo (0 : ℝ) π, 0 < f t)
    (hMt : 0 < Mt) (hD1 : 0 ≤ D1)
    (hdecayK : ∀ u, HairpinRelative.curvField f (theta u) ≤
      At * exp (-|u| / Mt))
    (hrelK : ∀ u, |deriv (fun r => HairpinRelative.curvField f (theta r)) u| ≤
      D1 * HairpinRelative.curvField f (theta u))
    (hm : 0 < m) (hmA : m ≤ Am)
    (hl : ∀ t, m ≤ f (theta t)) (hu : ∀ t, f (theta t) ≤ Am)
    (profile : ProfileConstants (alpha := alpha) (beta := beta) (a := a)
      (au := au) (CU := CU) (CK := CK) (DU := DU) (DU2 := DU2) (D := D)
      (Km := Km) (Kd := Kd) (kstar := kstar) (kd := kd))
    (heps : 0 < eps0) (halpha : 0 < alpha)
    (hdec0 : ∀ s, |currentPulse f theta x s| ≤ C * exp (-alpha * |s|))
    (hdec1 : ∀ s, |yp s| ≤ C * exp (-alpha * |s|))
    (hCU : C * exp (alpha * |phase f theta g|) ≤ CU)
    (hD : c.quantitative.relativeConst 1 ≤ D)
    (hDU : c.quantitative.relativeConst 1 ≤ DU)
    (hDU2 : c.quantitative.relativeConst 2 ≤ DU2)
    (hb0 : 0 ≤ b) (hbmin : b < min a au)
    (hsup : ∀ s, currentPulse f theta x s ≤ b)
    (hB : (1 + b) / 2 * π ≤ B)
    (hkd0 : 0 ≤ kd)
    (hmatch0 : 0 ≤ matchConst a C CK CU DU Km Kd au alpha beta B) :
    ∃ (Hs : ℕ → ℝ) (kappas : ℕ → ℝ → ℝ) (deltaStep : ℝ),
      0 < deltaStep ∧ Hrequired ≤ Hs 0 ∧
      (∀ n : ℕ, Hs 0 + n * deltaStep ≤ Hs n) ∧
      (∀ n, Hs n + deltaStep ≤ Hs (n + 1)) ∧
      (∀ n, Hs n < Hs (n + 1)) ∧
      (∀ n, ModelPeriodContinuity.rearPeriod (currentPulse f theta x)
        (Hs (n + 1)) = Hs n) ∧
      (∃ model : ConfiguredModelSequence kappas Hs (fun _ => eps0),
        model.kd = kd ∧ model.kstar = kstar ∧
        (∀ n, ContDiff ℝ 3
          (modelCurvature (model.configs n).yu (model.configs n).yu' (Hs n))) ∧
        (∀ n, ContDiff ℝ 3 (model.configs n).kH) ∧
        (∀ n s, modelCurvature (model.configs n).y (model.configs n).yd
          (Hs (n + 1)) s = kappas (n + 1) (s + phase f theta g)) ∧
        model.a = a ∧ model.au = au) ∧
      (∀ n s, 0 < kappas n s) ∧
      (∀ n, kappas n = modelCurvature
        (previousPulse f theta x g) (previousPulseDeriv f theta g yp) (Hs n)) ∧
      Summable (fun n : ℕ =>
        CurvatureStabilityL1.l1Modulus (2 * kd)
          (matchConst a C CK CU DU Km Kd au alpha beta B *
            exp (-(beta * Hs (n + 1)))) (Hs n) *
          (1 : ℝ) ^ 2 * (1 + kstar * (1 : ℝ))) := by
  let y := currentPulse f theta x
  let yu := previousPulse f theta x g
  let ypu := previousPulseDeriv f theta g yp
  have hy0 : ∀ s, 0 ≤ y s := c.currentPulse_nonneg_interior hfpos
  have hydec : ∀ s, y s ≤ C * exp (-alpha * |s|) := fun s =>
    (le_abs_self _).trans (hdec0 s)
  have hyc : Continuous y := (c.quantitative.smooth_pulse 0).continuous
  obtain ⟨Hstrip, hHstrip0, hstrip⟩ :=
    PeriodizedStripData.exists_threshold halpha
      (lt_trans (lt_of_lt_of_le hbmin (min_le_left a au)) profile.current_strip_lt)
      hy0 hydec hsup
  obtain ⟨Hbudget, hHbudget0, hbudget⟩ :=
    exists_simultaneous_strip_budget_threshold halpha hbmin
  obtain ⟨Hpaper, hHpaper0, hpaper⟩ :=
    PaperHairpinData.exists_threshold_toPaperHairpinData_of_canonical_consecutive
      c d hf hfpos profile heps halpha.le hdec0 hdec1 hCU hD hDU hDU2
  obtain ⟨bpos, hbpos, hlower⟩ :=
    c.exists_previous_lower_comparison_interior d hf hfpos hMt hD1 hdecayK
      hrelK hm hmA hl hu
  have hC0 : 0 ≤ C := Periodization.const_nonneg hy0 hydec
  have hCU0 : 0 ≤ CU := by
    have he : 0 < exp (alpha * |phase f theta g|) := exp_pos _
    nlinarith [hCU]
  obtain ⟨Hpositive, hHpositive0, hpositive⟩ :=
    exists_largePeriod_strict_positivity_threshold halpha hbpos
      profile.prior_strip_nonneg profile.prior_strip_lt
      profile.prior_derivative_nonneg hCU0
  let Hrear := PerimeterHairpinPulse.threshold alpha C b
  let Hmin := max Hrequired (max 1 (max Hstrip (max Hbudget (max Hpaper
    (max Hpositive (max Hrear (4 * B)))))))
  have hrequired_le : Hrequired ≤ Hmin := le_max_left _ _
  have hstrip_le : Hstrip ≤ Hmin :=
    le_max_of_le_right (le_max_of_le_right (le_max_left _ _))
  have hbudget_le : Hbudget ≤ Hmin :=
    le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_left _ _)))
  have hpaper_le : Hpaper ≤ Hmin :=
    le_max_of_le_right (le_max_of_le_right (le_max_of_le_right
      (le_max_of_le_right (le_max_left _ _))))
  have hpositive_le : Hpositive ≤ Hmin :=
    le_max_of_le_right (le_max_of_le_right (le_max_of_le_right
      (le_max_of_le_right (le_max_of_le_right (le_max_left _ _)))))
  have hrear_le : Hrear ≤ Hmin :=
    le_max_of_le_right (le_max_of_le_right (le_max_of_le_right
      (le_max_of_le_right (le_max_of_le_right
        (le_max_of_le_right (le_max_left _ _))))))
  obtain ⟨Hs, -, deltaStep, hdelta, hstart, hlinear, hstep, hinc, hrec, -, hsum⟩ :=
    UnitTangentIterates.CanonicalConfiguredModelCapstone.exists_configuredModelSequence_above
      (theta0 := theta0) Hmin c d hf hfpos hMt hD1 hdecayK hrelK hm hmA hl hu profile heps
      halpha hdec0 hdec1 hCU hD hDU hDU2 hb0 hbmin hsup hB hkd0 hmatch0
  have hmono : Monotone Hs := monotone_nat_of_le_succ fun n => (hinc n).le
  have hbase : ∀ n, Hmin ≤ Hs n := fun n => hstart.trans (hmono (Nat.zero_le n))
  have rearData : ∀ H, Hmin ≤ H → RearCellData y H
      (ModelPeriodContinuity.rearPeriod y H) B := by
    intro H hH
    simpa [y] using PaperHairpinConfig.rearCell_of_quantitative_tail
      c halpha (lt_trans hbmin
        (lt_of_le_of_lt (min_le_left a au) profile.current_strip_lt))
      hydec hsup (hrear_le.trans hH) hB hfpos
  let edgeData : ∀ n, PaperHairpinData (alpha := alpha) (beta := beta)
      (a := a) (au := au) (C := C) (CU := CU) (CK := CK) (DU := DU)
      (DU2 := DU2) (D := D) (Km := Km) (Kd := Kd) (B := B)
      (theta0 := theta0) (kstar := kstar) (kd := kd) (eps0 := eps0)
      (H := Hs (n + 1)) (P := Hs n) y yu ypu := fun n => Nonempty.some (by
    have hn := hbase n
    have hn1 := hbase (n + 1)
    have hsCurr := hstrip (Hs n) (hstrip_le.trans hn)
    have hsNext := hstrip (Hs (n + 1)) (hstrip_le.trans hn1)
    have hbCurr := (hbudget (Hs n) (hbudget_le.trans hn)).2
    have hbNext := (hbudget (Hs (n + 1)) (hbudget_le.trans hn1)).1
    have hprior := previous_strip_of_current_strip (g := g) hsCurr hbCurr
    obtain ⟨y2, han⟩ := c.pulsePairAnalyticData_of_quantitative hy0 halpha.le
      hdec0 hdec1 hCU hD hDU hDU2 hprior
    have hp := hpositive (Hs n) (hpositive_le.trans hn)
    have hsumK := han.previousHairpinCurvature_summable halpha hp.1
      profile.prior_derivative_nonneg profile.prior_strip_lt
    have hpos : CurvaturePositivityData yu ypu (Hs n) :=
      CurvaturePositivityData.of_large_period halpha hp.1 hp.2.1
        han.previous_nonneg han.previous_decay profile.prior_derivative_nonneg
        han.previous_relative profile.prior_strip_nonneg profile.prior_strip_lt
        han.previous_periodized_strip hbpos.le hlower hsumK hp.2.2.le
    have hr := rearData (Hs (n + 1)) hn1
    have hr' : RearCellData y (Hs (n + 1)) (Hs n) B := by
      have hrecY : ModelPeriodContinuity.rearPeriod y (Hs (n + 1)) = Hs n := by
        simpa [y] using hrec n
      rw [hrecY] at hr
      exact hr
    exact hpaper (Hs (n + 1)) (Hs n) b (hpaper_le.trans hn1)
      hprior hsNext hbNext hpos hr')
  let kappas : ℕ → ℝ → ℝ := fun n =>
    modelCurvature (edgeData n).toConfig.1.yu
      (edgeData n).toConfig.1.yu' (Hs n)
  let model : ConfiguredModelSequence kappas Hs (fun _ => eps0) :=
    UnitTangentIterates.CanonicalConfiguredModelSequence.ofPaperHairpinData
      edgeData (fun n => hmono (Nat.zero_le n))
  let y1 : ℝ → ℝ := iteratedDeriv 1 y
  let y2 : ℝ → ℝ := iteratedDeriv 2 y
  let y3 : ℝ → ℝ := iteratedDeriv 3 y
  let y4 : ℝ → ℝ := iteratedDeriv 4 y
  have hiter {n j : ℕ} (hn : ContDiff ℝ n y) (hj : j < n) (s : ℝ) :
      HasDerivAt (iteratedDeriv j y) (iteratedDeriv (j + 1) y s) s := by
    have hd := hn.differentiable_iteratedDeriv j (by exact_mod_cast hj)
    rw [iteratedDeriv_succ]
    exact (hd s).hasDerivAt
  have hy01 : ∀ s, HasDerivAt y (y1 s) s := fun s => by
    have h := hiter (c.quantitative.smooth_pulse 2) (show 0 < 2 by norm_num) s
    simpa [y, y1, iteratedDeriv_zero] using h
  have hy12 : ∀ s, HasDerivAt y1 (y2 s) s := fun s => by
    simpa [y1, y2] using
      hiter (c.quantitative.smooth_pulse 3) (show 1 < 3 by norm_num) s
  have hy23 : ∀ s, HasDerivAt y2 (y3 s) s := fun s => by
    simpa [y2, y3] using
      hiter (c.quantitative.smooth_pulse 4) (show 2 < 4 by norm_num) s
  have hy34 : ∀ s, HasDerivAt y3 (y4 s) s := fun s => by
    simpa [y3, y4] using
      hiter (c.quantitative.smooth_pulse 5) (show 3 < 5 by norm_num) s
  have hy3c : Continuous y3 := Differentiable.continuous fun s =>
    (hiter (c.quantitative.smooth_pulse 5) (show 3 < 5 by norm_num) s).differentiableAt
  have hy4c : Continuous y4 := Differentiable.continuous fun s =>
    (hiter (c.quantitative.smooth_pulse 6) (show 4 < 6 by norm_num) s).differentiableAt
  have hyp_eq : yp = y1 := by
    funext s
    exact (c.pulse_deriv s).unique (hy01 s)
  let Cjet : ℝ := max (c.quantitative.decayConst 0)
    (max (c.quantitative.decayConst 1)
      (max (c.quantitative.decayConst 2)
        (max (c.quantitative.decayConst 3) (c.quantitative.decayConst 4))))
  have hCjet : 0 ≤ Cjet :=
    (c.quantitative.decayConst_nonneg 0).trans (le_max_left _ _)
  have hdecayJet (j : ℕ) (hj : j ≤ 4)
      (hjC : c.quantitative.decayConst j ≤ Cjet) : ∀ s,
      |iteratedDeriv j y s| ≤ Cjet * exp (-(M⁻¹) * |s|) := by
    intro s
    calc
      |iteratedDeriv j y s| ≤
          c.quantitative.decayConst j * exp (-|s| / M) := by
        simpa [y] using c.quantitative.decay j (hj.trans (by norm_num)) s
      _ ≤ Cjet * exp (-|s| / M) :=
        mul_le_mul_of_nonneg_right hjC (exp_pos _).le
      _ = Cjet * exp (-(M⁻¹) * |s|) := by ring
  have hyb0 : ∀ s, |y s| ≤ Cjet * exp (-(M⁻¹) * |s|) := by
    intro s
    simpa [iteratedDeriv_zero] using
      hdecayJet 0 (by norm_num) (le_max_left _ _) s
  have hyb1 : ∀ s, |y1 s| ≤ Cjet * exp (-(M⁻¹) * |s|) :=
    hdecayJet 1 (by norm_num) (le_max_of_le_right (le_max_left _ _))
  have hyb2 : ∀ s, |y2 s| ≤ Cjet * exp (-(M⁻¹) * |s|) :=
    hdecayJet 2 (by norm_num)
      (le_max_of_le_right (le_max_of_le_right (le_max_left _ _)))
  have hyb3 : ∀ s, |y3 s| ≤ Cjet * exp (-(M⁻¹) * |s|) :=
    hdecayJet 3 (by norm_num)
      (le_max_of_le_right (le_max_of_le_right
        (le_max_of_le_right (le_max_left _ _))))
  have hyb4 : ∀ s, |y4 s| ≤ Cjet * exp (-(M⁻¹) * |s|) :=
    hdecayJet 4 (by norm_num)
      (le_max_of_le_right (le_max_of_le_right
        (le_max_of_le_right (le_max_right _ _))))
  have hsmooth : ∀ n,
      ContDiff ℝ 3
        (modelCurvature (model.configs n).yu (model.configs n).yu' (Hs n)) ∧
      ContDiff ℝ 3 (model.configs n).kH := by
    intro n
    apply ModelOrbitDefect.Config.contDiff_three_endpoints_of_common_pulse
      (gamma := M⁻¹) (Cjet := Cjet) (q := phase f theta g)
      (model.configs n) (inv_pos.mpr c.quantitative.M_pos) hCjet
      hy01 hy12 hy23 hy34 hy3c hy4c hyb0 hyb1 hyb2 hyb3 hyb4
    · change (edgeData n).toConfig.1.y = y
      exact (edgeData n).toConfig.2.1
    · change (edgeData n).toConfig.1.yu = fun s => y (s - phase f theta g)
      simpa [y, yu, previousPulse] using (edgeData n).toConfig.2.2.1
    · change (edgeData n).toConfig.1.yu' = fun s => y1 (s - phase f theta g)
      simpa [ypu, previousPulseDeriv, hyp_eq] using (edgeData n).toConfig.2.2.2
  have hyupos : ∀ s, 0 < yu s := by
    simpa [yu] using previousPulse_pos_interior hfpos d.angle_mem
  have hkpos : ∀ n s, 0 < kappas n s := by
    intro n s
    have hn := hbase n
    have hsCurr := hstrip (Hs n) (hstrip_le.trans hn)
    have hbCurr := (hbudget (Hs n) (hbudget_le.trans hn)).2
    have hprior := previous_strip_of_current_strip (g := g) hsCurr hbCurr
    obtain ⟨y2, han⟩ := c.pulsePairAnalyticData_of_quantitative hy0 halpha.le
      hdec0 hdec1 hCU hD hDU hDU2 hprior
    have hp := hpositive (Hs n) (hpositive_le.trans hn)
    have hsumK := han.previousHairpinCurvature_summable halpha hp.1
      profile.prior_derivative_nonneg profile.prior_strip_lt
    have hstrict := modelCurvature_pos_of_large_period halpha hp.1 hp.2.1
      han.previous_nonneg hyupos han.previous_decay
      profile.prior_derivative_nonneg han.previous_relative
      profile.prior_strip_nonneg profile.prior_strip_lt
      han.previous_periodized_strip hlower hsumK hp.2.2 s
    simpa [kappas, (edgeData n).toConfig.2.2.1,
      (edgeData n).toConfig.2.2.2] using hstrict
  have hkappa : ∀ n, kappas n = modelCurvature yu ypu (Hs n) := by
    intro n
    funext s
    simp [kappas, (edgeData n).toConfig.2.2.1,
      (edgeData n).toConfig.2.2.2]
  have hcurrent : ∀ n s,
      modelCurvature (model.configs n).y (model.configs n).yd
          (Hs (n + 1)) s =
        kappas (n + 1) (s + phase f theta g) := by
    intro n s
    have hyEq : (model.configs n).y = y := by
      exact (edgeData n).toConfig.2.1
    have hydEq : (model.configs n).yd = yp := by
      funext t
      have hd := (model.configs n).hyderiv t
      rw [hyEq] at hd
      exact hd.unique (c.pulse_deriv t)
    rw [hyEq, hydEq, hkappa (n + 1)]
    have hm := ShiftedCurvatureJetMajorant.modelCurvature_shift y yp
      (Hs (n + 1)) (phase f theta g) (s + phase f theta g)
    simpa [yu, ypu, previousPulse, previousPulseDeriv,
      ShiftedCurvatureJetMajorant.shift] using hm.symm
  have hmodel : ∃ model : ConfiguredModelSequence kappas Hs (fun _ => eps0),
      model.kd = kd ∧ model.kstar = kstar ∧
      (∀ n, ContDiff ℝ 3
        (modelCurvature (model.configs n).yu (model.configs n).yu' (Hs n))) ∧
      (∀ n, ContDiff ℝ 3 (model.configs n).kH) ∧
      (∀ n s, modelCurvature (model.configs n).y (model.configs n).yd
        (Hs (n + 1)) s = kappas (n + 1) (s + phase f theta g)) ∧
      model.a = a ∧ model.au = au := by
    exact ⟨model, rfl, rfl, fun n => (hsmooth n).1, fun n => (hsmooth n).2,
      hcurrent, rfl, rfl⟩
  exact ⟨Hs, kappas, deltaStep, hdelta, hrequired_le.trans hstart,
    hlinear, hstep, hinc, hrec, hmodel, hkpos, hkappa, hsum⟩

/-- A continuous positive periodic function has a positive global floor. -/
theorem exists_positive_floor_of_periodic
    {kappa : ℝ → ℝ} {H : ℝ} (hH : 0 < H)
    (hk : Continuous kappa) (hper : Periodic kappa H)
    (hpos : ∀ s, 0 < kappa s) :
    ∃ kmin : ℝ, 0 < kmin ∧ ∀ s, kmin ≤ kappa s := by
  obtain ⟨s0, hs0, hmin⟩ :=
    isCompact_Icc.exists_isMinOn (nonempty_Icc.2 hH.le) hk.continuousOn
  refine ⟨kappa s0, hpos s0, ?_⟩
  intro s
  obtain ⟨u, hu, heq⟩ := hper.exists_mem_Ico₀ hH s
  rw [heq]
  exact hmin ⟨hu.1, hu.2.le⟩

/-- Pointwise strict positivity is the sole extra model-sequence statement
needed for all strict exact-pair geometry. -/
theorem strictExactPairCertificates_of_curvature_pos
    {kappas : ℕ → ℝ → ℝ} {Hs eps : ℕ → ℝ}
    (m : ConfiguredModelSequence kappas Hs eps)
    (hpos : ∀ n s, 0 < kappas n s) :
    ∀ n, ∃ delta : ℝ → ℝ,
      StrictExactPairCertificate (kappas n) delta (Hs n) m.thetaBase m.au := by
  choose kmin hkminpos hkmin using fun n =>
    exists_positive_floor_of_periodic (m.separation_pos n)
      (m.curvature_continuous n) (m.curvature_periodic n) (hpos n)
  exact strictExactPairCertificates_of_levelwiseFloor m
    { kmin_pos := hkminpos, lower := hkmin }

/-- The strict configured-sequence capstone with the pulse bounds discharged
from the paper's interior barrier data. -/
theorem exists_strict_configuredModelSequence_of_interior_barrier
    {f g gp : ℝ → ℝ} {theta x : ℝ → ℝ} {m Am A M Dp : ℝ}
    {alpha beta a au C CU CK DU DU2 D Km Kd B theta0 kstar kd eps0 b : ℝ}
    (hf : ContDiffOn ℝ ∞ f (Ioo 0 π)) (hm : 0 < m)
    (hlow : ∀ t ∈ Ioo (0 : ℝ) π, m ≤ f t)
    (hupp : ∀ t ∈ Ioo (0 : ℝ) π, f t ≤ Am) (hmA : m ≤ Am)
    (hdb : ∀ t ∈ Ioo (0 : ℝ) π, |deriv (HairpinRelative.pulseField f) t| ≤ Dp)
    (hmem : ∀ u, theta u ∈ Ioo 0 π)
    (hval : ∀ u, Hairpin.hairpinArclength f (π / 2) (theta u) = u)
    (hderiv : ∀ u, HasDerivAt theta (HairpinRelative.curvField f (theta u)) u)
    (hxinv : ∀ s, HairpinRelative.frontArclength f theta (x s) = s)
    (hw : ∀ s, HasDerivAt (fun r => theta (x r))
      (HairpinRelative.pulseField f (theta (x s))) s)
    (hsm : StrictMono theta)
    (hsurj : ∀ z ∈ Ioo (0 : ℝ) π, ∃ u, theta u = z)
    (hA : 0 ≤ A) (hM : 0 < M)
    (hdecay : ∀ u, HairpinRelative.curvField f (theta u) ≤
      A * exp (-|u| / M))
    (relativeConst : ℕ → ℝ) (hrc0 : ∀ j, 0 ≤ relativeConst j)
    (hrel : ∀ j ≤ 4, ∀ s,
      |iteratedDeriv j (fun r => HairpinRelative.pulseField f (theta (x r))) s| ≤
        relativeConst j * HairpinRelative.pulseField f (theta (x s)))
    (translator : TranslatorData f g gp)
    (d : CanonicalTranslatorLocalPhase.InteriorPhaseData f theta x g gp)
    (profile : ProfileConstants (alpha := alpha) (beta := beta) (a := a)
      (au := au) (CU := CU) (CK := CK) (DU := DU) (DU2 := DU2) (D := D)
      (Km := Km) (Kd := Kd) (kstar := kstar) (kd := kd))
    (heps : 0 < eps0) (halpha : 0 < alpha) (halphaM : alpha ≤ 1 / M)
    (hC0 : relativeConst 0 * (A * exp (A ^ 2 / 2)) ≤ C)
    (hC1 : relativeConst 1 * (A * exp (A ^ 2 / 2)) ≤ C)
    (hCU : C * exp (alpha * |ConsecutiveData.phase f theta g|) ≤ CU)
    (hD : relativeConst 1 ≤ D)
    (hDU : relativeConst 1 ≤ DU)
    (hDU2 : relativeConst 2 ≤ DU2)
    (hb0 : 0 ≤ b) (hbmin : b < min a au)
    (hbarrier : 1 / sqrt (1 + m ^ 2) ≤ b)
    (hB : (1 + b) / 2 * π ≤ B)
    (hkd0 : 0 ≤ kd) :
    ∃ (Hs : ℕ → ℝ) (kappas : ℕ → ℝ → ℝ) (deltaStep : ℝ),
      0 < deltaStep ∧
      (∀ n : ℕ, Hs 0 + n * deltaStep ≤ Hs n) ∧
      (∀ n, Hs n < Hs (n + 1)) ∧
      (∀ n, ModelPeriodContinuity.rearPeriod
        (fun s => HairpinRelative.pulseField f (theta (x s)))
        (Hs (n + 1)) = Hs n) ∧
      Nonempty (ConfiguredModelSequence kappas Hs (fun _ => eps0)) ∧
      (∀ n s, 0 < kappas n s) ∧
      Summable (fun n : ℕ =>
        CurvatureStabilityL1.l1Modulus (2 * kd)
          (matchConst a C CK CU DU Km Kd au alpha beta B *
            exp (-(beta * Hs (n + 1)))) (Hs n) *
          (1 : ℝ) ^ 2 * (1 + kstar * (1 : ℝ))) := by
  have hfpos : ∀ t ∈ Ioo (0 : ℝ) π, 0 < f t := fun t ht =>
    lt_of_lt_of_le hm (hlow t ht)
  have hbb : (1 : ℝ) / sqrt (1 + m ^ 2) < 1 :=
    HairpinRelative.one_div_sqrt_one_add_sq_lt_one hm
  have hbb0 : (0 : ℝ) ≤ 1 / sqrt (1 + m ^ 2) := by positivity
  have hyb : ∀ t ∈ Ioo (0 : ℝ) π,
      |HairpinRelative.pulseField f t| ≤ 1 / sqrt (1 + m ^ 2) := by
    intro t ht
    rw [abs_of_nonneg (HairpinRelative.pulseField_nonneg_interior hfpos ht)]
    exact HairpinRelative.pulseField_le_of_barrier hm (hlow t ht) ht
  have hDp0 : 0 ≤ Dp := le_trans (abs_nonneg _) (hdb _ (hmem 0))
  have hD1 : (0 : ℝ) ≤ Dp / sqrt (1 - (1 / sqrt (1 + m ^ 2)) ^ 2) ^ 3 := by
    positivity
  have hrelK := HairpinRelative.relK_of_pulse_deriv_bound hf hfpos hbb0 hbb
    hyb hdb hmem hderiv
  have hC : 0 ≤ C :=
    le_trans (mul_nonneg (hrc0 0) (by positivity)) hC0
  have hCU0 : 0 ≤ CU :=
    le_trans (mul_nonneg hC (exp_pos _).le) hCU
  have hmatch0 : 0 ≤ matchConst a C CK CU DU Km Kd au alpha beta B :=
    PaperHairpinConfig.matchConst_nonneg profile halpha hC hCU0
  have hdecayJ : ∀ j ≤ 4, ∀ s : ℝ,
      |iteratedDeriv j (fun r => HairpinRelative.pulseField f (theta (x r))) s| ≤
        relativeConst j * (A * exp (A ^ 2 / 2)) * exp (-|s| / M) :=
    fun j hj s => (PaperHairpinQuantitativeData.data_of_interior hf hm hlow hmem
      hval hderiv hxinv hw hsm hsurj hA hM hdecay relativeConst hrc0 hrel).decay
        j hj s
  have hexp : ∀ s : ℝ, exp (-|s| / M) ≤ exp (-alpha * |s|) := by
    intro s
    apply exp_le_exp.mpr
    have h1 : alpha * |s| ≤ 1 / M * |s| :=
      mul_le_mul_of_nonneg_right halphaM (abs_nonneg s)
    have h2 : -|s| / M = -(1 / M * |s|) := by ring
    rw [h2]
    linarith [h1]
  have hstep : ∀ j : ℕ, j ≤ 4 →
      relativeConst j * (A * exp (A ^ 2 / 2)) ≤ C → ∀ s : ℝ,
      |iteratedDeriv j (fun r => HairpinRelative.pulseField f (theta (x r))) s| ≤
        C * exp (-alpha * |s|) := by
    intro j hj hle s
    have hD0 : 0 ≤ relativeConst j * (A * exp (A ^ 2 / 2)) :=
      mul_nonneg (hrc0 j) (by positivity)
    exact le_trans (hdecayJ j hj s)
      (mul_le_mul hle (hexp s) (exp_pos _).le (le_trans hD0 hle))
  have hdec0 : ∀ s,
      |HairpinRelative.pulseField f (theta (x s))| ≤ C * exp (-alpha * |s|) := by
    intro s
    have h := hstep 0 (by norm_num) hC0 s
    rwa [iteratedDeriv_zero] at h
  have hdec1 : ∀ s,
      |iteratedDeriv 1 (fun r => HairpinRelative.pulseField f (theta (x r))) s| ≤
        C * exp (-alpha * |s|) := hstep 1 (by norm_num) hC1
  have hsup : ∀ s, HairpinRelative.pulseField f (theta (x s)) ≤ b := fun s =>
    le_trans (HairpinRelative.pulseField_le_of_barrier hm
      (hlow _ (hmem (x s))) (hmem (x s))) hbarrier
  have hl : ∀ t, m ≤ f (theta t) := fun t => hlow _ (hmem t)
  have hu : ∀ t, f (theta t) ≤ Am := fun t => hupp _ (hmem t)
  obtain ⟨Hs, kappas, deltaStep, hdelta, -, hlinear, -, hinc, hrec,
    ⟨model, -, -⟩, hkpos, -, hsum⟩ :=
    exists_strict_configuredModelSequence_above (theta0 := theta0) 0
    (PaperHairpinQuantitativeData.consecutiveData_of_interior hf hm hlow hmem
      hval hderiv hxinv hw hsm hsurj hA hM hdecay relativeConst hrc0 hrel translator)
    d hf hfpos hM hD1 hdecay hrelK hm hmA hl hu profile heps halpha hdec0 hdec1
    hCU hD hDU hDU2 hb0 hbmin hsup hB hkd0 hmatch0
  exact ⟨Hs, kappas, deltaStep, hdelta, hlinear, hinc, hrec,
    ⟨model⟩, hkpos, hsum⟩

/-- The fully constructed epsilon-profile has a configured sequence whose
curvature is strictly positive at every level and every parameter value. -/
theorem exists_strict_configuredModelSequence_of_eps {eps : ℝ}
    (heps : 0 < eps) (heps10 : eps ≤ 1 / 10) :
    ∃ (kappas : ℕ → ℝ → ℝ) (Hs : ℕ → ℝ)
      (deltaStep kd kstar cst beta : ℝ),
      0 < deltaStep ∧ (∀ n, Hs n < Hs (n + 1)) ∧
      Nonempty (ConfiguredModelSequence kappas Hs (fun _ => (1 : ℝ))) ∧
      (∀ n s, 0 < kappas n s) ∧
      Summable (fun n : ℕ =>
        CurvatureStabilityL1.l1Modulus (2 * kd)
          (cst * exp (-(beta * Hs (n + 1)))) (Hs n) *
          (1 : ℝ) ^ 2 * (1 + kstar * (1 : ℝ))) := by
  obtain ⟨f, g, gp, theta, x, m, Am, hbar, hm, hmA, hlow, hupp, hfinf, hsm,
    hsurj, hdecay, d⟩ :=
    exists_interiorPhaseData_of_eps heps heps10
  have hfpos : ∀ t ∈ Ioo (0 : ℝ) π, 0 < f t := fun t ht =>
    lt_of_lt_of_le hm (hlow t ht)
  have hMpos : (0 : ℝ) < Am := lt_of_lt_of_le hm hmA
  have hA : (0 : ℝ) ≤ 2 / m := by positivity
  obtain ⟨relativeConst, hrc0, hrel⟩ :=
    hrelj_of_interior d hm hmA hfinf hlow hupp hdecay hMpos hsurj
  have htrans : TranslatorData f g gp :=
    { angle_shift := d.shift
      maps_angle := d.image_mem
      profile_deriv_identity := d.translator_identity
      angle_deriv := d.translator_deriv }
  obtain ⟨-, -, hyC⟩ :=
    HairpinInteriorRegularity.contDiff_nat_hairpin_coordinates hfinf hfpos
      d.angle_mem d.angle_deriv d.state_deriv
  have hYd : ∀ s, HasDerivAt
      (fun r => HairpinRelative.pulseField f (theta (x r)))
      (iteratedDeriv 1 (fun r => HairpinRelative.pulseField f (theta (x r))) s) s :=
    fun s => by
      have h := hasDerivAt_iteratedDeriv (hyC 2) (show 0 < 2 by norm_num) s
      rwa [iteratedDeriv_zero] at h
  obtain ⟨Dp, hDp, h1⟩ :=
    rel_pulse_one_of_interior' d hm hmA hfinf hlow hupp hdecay hMpos hYd
  have hdb : ∀ t ∈ Ioo (0 : ℝ) π,
      |deriv (HairpinRelative.pulseField f) t| ≤ Dp := by
    intro t ht
    have h := abs_coeff_pulse_le_of_flow hfinf hfpos
      d.angle_mem d.angle_deriv d.inverse_value hsurj d.state_deriv h1 t ht
    rwa [HairpinRelative.coeff_one] at h
  set b := 1 / sqrt (1 + m ^ 2) with hbdef
  have hb0 : (0 : ℝ) ≤ b := by positivity
  have hb1 : b < 1 := HairpinRelative.one_div_sqrt_one_add_sq_lt_one hm
  set aa := (b + 1) / 2 with haadef
  have hba : b < aa := by simp [haadef]; linarith
  have ha0 : (0 : ℝ) ≤ aa := by simp [haadef]; linarith
  have ha1 : aa < 1 := by simp [haadef]; linarith
  set alpha := 1 / Am with halphadef
  have halpha : 0 < alpha := by positivity
  set A := 2 / m with hAdef
  set C := max (relativeConst 0 * (A * exp (A ^ 2 / 2)))
    (relativeConst 1 * (A * exp (A ^ 2 / 2))) with hCdef
  set CU := C * exp (alpha * |ConsecutiveData.phase f theta g|) with hCUdef
  obtain ⟨CK, Km, Kd, kstar, kd, profile⟩ :=
    PaperHairpinConfig.exists_profileConstants (alpha := alpha) (beta := alpha / 4)
      (a := aa) (au := aa) (CU := CU) (DU := relativeConst 1)
      (DU2 := relativeConst 2) (D := relativeConst 1) (by positivity)
      (by linarith) (hrc0 1) (hrc0 1) (hrc0 2) ha0 ha1 ha0 ha1
  obtain ⟨Hs, kappas, deltaStep, hdelta, -, hinc, -, hmodel, hkpos, hsum⟩ :=
    exists_strict_configuredModelSequence_of_interior_barrier
      (theta0 := 0) (b := b) (B := (1 + b) / 2 * π) (eps0 := 1)
      hfinf hm hlow hupp hmA hdb d.angle_mem d.angle_value d.angle_deriv
      d.inverse_value d.state_deriv hsm hsurj hA hMpos hdecay relativeConst
      hrc0 hrel htrans d profile one_pos halpha (by rw [halphadef])
      (le_max_left _ _) (le_max_right _ _) (le_refl _) (le_refl _) (le_refl _)
      (le_refl _) hb0 (by simp [hba]) (le_refl _) (le_refl _)
      profile.rear_derivative_pos.le
  exact ⟨kappas, Hs, deltaStep, kd, kstar,
    matchConst aa C CK CU (relativeConst 1) Km Kd aa alpha (alpha / 4)
      ((1 + b) / 2 * π),
    alpha / 4, hdelta, hinc, hmodel, hkpos, hsum⟩

/-- Final strict geometric output of the constructed epsilon profile: every
level is an exact two-cap pair with the unit-tangent identities, strictly
increasing turning angles, and embedded front and rear caps. -/
theorem exists_strict_constructedModelGeometry_of_eps {eps : ℝ}
    (heps : 0 < eps) (heps10 : eps ≤ 1 / 10) :
    ∃ (kappas : ℕ → ℝ → ℝ) (Hs : ℕ → ℝ)
      (deltaStep kd kstar cst beta : ℝ),
      ∃ model : ConfiguredModelSequence kappas Hs (fun _ => (1 : ℝ)),
      0 < deltaStep ∧ (∀ n, Hs n < Hs (n + 1)) ∧
      (∀ n s, 0 < kappas n s) ∧
      (∀ n, ∃ delta : ℝ → ℝ,
        StrictExactPairCertificate (kappas n) delta (Hs n)
          model.thetaBase model.au) ∧
      Summable (fun n : ℕ =>
        CurvatureStabilityL1.l1Modulus (2 * kd)
          (cst * exp (-(beta * Hs (n + 1)))) (Hs n) *
          (1 : ℝ) ^ 2 * (1 + kstar * (1 : ℝ))) := by
  obtain ⟨kappas, Hs, deltaStep, kd, kstar, cst, beta, hdelta, hinc,
    ⟨model⟩, hkpos, hsum⟩ := exists_strict_configuredModelSequence_of_eps heps heps10
  have hcert : ∀ n, ∃ delta : ℝ → ℝ,
      StrictExactPairCertificate (kappas n) delta (Hs n)
        model.thetaBase model.au :=
    strictExactPairCertificates_of_curvature_pos model hkpos
  exact ⟨kappas, Hs, deltaStep, kd, kstar, cst, beta, model, hdelta, hinc,
    hkpos, hcert, hsum⟩

end StrictConstructedModelGeometry
