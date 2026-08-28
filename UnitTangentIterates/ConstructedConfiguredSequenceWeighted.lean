import UnitTangentIterates.ConstructedConfiguredSequence
import UnitTangentIterates.MatchConstNonneg
import UnitTangentIterates.StrictConstructedModelGeometry
import UnitTangentIterates.WeightedMarkedDefectThreshold
import UnitTangentIterates.ActualFrontCurvatureLargePeriod

/-!
# Strengthened constructed configured sequence

The original constructed-sequence theorem keeps its public existential
interface.  This sibling result retains the sign and linear-growth data needed
by the approximate weighted closing theorem.
-/

noncomputable section

set_option maxHeartbeats 4000000

open Set Real HairpinRelative PaperHairpinQuantitativeData PaperHairpinConfig
open FrontPeriodization ModelOrbitDefect
open scoped ContDiff

namespace ConstructedConfiguredSequenceWeighted

/-- Constructed sequence data with the quantitative facts needed by weighted
pullback summability.  Here `beta` is the marked-distance decay exponent; the
curvature matching estimate has exponent `2 * beta`. -/
structure Data where
  kappas : ℕ → ℝ → ℝ
  Hs : ℕ → ℝ
  deltaStep : ℝ
  kd : ℝ
  kstar : ℝ
  matchCoefficient : ℝ
  beta : ℝ
  deltaStep_pos : 0 < deltaStep
  beta_pos : 0 < beta
  matchCoefficient_nonneg : 0 ≤ matchCoefficient
  kd_nonneg : 0 ≤ kd
  kstar_nonneg : 0 ≤ kstar
  separation_zero_pos : 0 < Hs 0
  separation_lower : ∀ n, Hs 0 ≤ Hs n
  separation_linear : ∀ n : ℕ, Hs 0 + n * deltaStep ≤ Hs n
  separation_step : ∀ n, Hs n + deltaStep ≤ Hs (n + 1)
  model : UnconditionalAssembly.ConfiguredModelSequence
    kappas Hs (fun _ => (1 : ℝ))
  model_kd : model.kd = kd
  model_kstar : model.kstar = kstar
  model_KP_C2 : ∀ n, ContDiff ℝ 2
    (ModelOrbitDefect.modelCurvature (model.configs n).yu
      (model.configs n).yu' (Hs n))
  model_kH_C2 : ∀ n, ContDiff ℝ 2 (model.configs n).kH
  phase : ℝ
  model_current_curvature_eq_next_shift : ∀ n s,
    ModelOrbitDefect.modelCurvature (model.configs n).y
      (model.configs n).yd (Hs (n + 1)) s =
      kappas (n + 1) (s + phase)
  model_curvature_pos : ∀ n s, 0 < kappas n s

/-- Constructed weighted data with a ceiling on the actual front and rear
curvatures.  The coarse `data.kstar` remains available only for matching and
cost estimates. -/
structure DataWithActualHalf where
  data : Data
  steering_le_half : data.model.a ≤ 1 / 2
  front_le_half : ∀ n s, data.kappas n s ≤ 1 / 2
  rear_le_half : ∀ n s, (data.model.configs n).kH s ≤ 1 / 2

/-- **The epsilon construction above an arbitrary initial separation.**
The lower threshold is retained in the conclusion so later analytic
requirements can be imposed without rebuilding or altering the matching
constants. -/
theorem exists_dataWithActualHalf_above_of_eps (Hrequired : ℝ) {eps : ℝ}
    (heps : 0 < eps) (heps10 : eps ≤ 1 / 10) :
    ∃ E : DataWithActualHalf, Hrequired ≤ E.data.Hs 0 := by
  obtain ⟨f, g, gp, theta, x, m, Am, hbar, hm, hmA, hlow, hupp, hfinf, hsm,
    hsurj, hdecay, d⟩ := exists_interiorPhaseData_of_eps heps heps10
  have hfpos : ∀ t ∈ Ioo (0 : ℝ) Real.pi, 0 < f t := fun t ht =>
    lt_of_lt_of_le hm (hlow t ht)
  have hMpos : (0 : ℝ) < Am := lt_of_lt_of_le hm hmA
  have hA : (0 : ℝ) ≤ 2 / m := by positivity
  obtain ⟨relativeConst, hrc0, hrel⟩ := hrelj_of_interior d hm hmA hfinf hlow
    hupp hdecay hMpos hsurj
  have htrans : TranslatorData f g gp :=
    { angle_shift := d.shift
      maps_angle := d.image_mem
      profile_deriv_identity := d.translator_identity
      angle_deriv := d.translator_deriv }
  obtain ⟨-, -, hyC⟩ :=
    HairpinInteriorRegularity.contDiff_nat_hairpin_coordinates hfinf hfpos
      d.angle_mem d.angle_deriv d.state_deriv
  have hYd : ∀ s, HasDerivAt (fun r => pulseField f (theta (x r)))
      (iteratedDeriv 1 (fun r => pulseField f (theta (x r))) s) s := fun s => by
    have h := hasDerivAt_iteratedDeriv (hyC 2) (show 0 < 2 by norm_num) s
    rwa [iteratedDeriv_zero] at h
  let yp0 : ℝ → ℝ := iteratedDeriv 1 (fun r => pulseField f (theta (x r)))
  let consecutive : ConsecutiveData f theta x g gp yp0 Am 0 0 0 0
      (fun _ => 0) (fun _ => 0) :=
    { quantitative := data_of_interior hfinf hm hlow d.angle_mem d.angle_value
        d.angle_deriv d.inverse_value d.state_deriv hsm hsurj hA hMpos hdecay
        relativeConst hrc0 hrel
      translator := htrans
      pulse_deriv := by simpa [yp0] using hYd }
  obtain ⟨Dp, hDp, h1⟩ := rel_pulse_one_of_interior' d hm hmA hfinf hlow hupp
    hdecay hMpos hYd
  have hdb : ∀ t ∈ Ioo (0 : ℝ) Real.pi, |deriv (pulseField f) t| ≤ Dp := by
    intro t ht
    have h := abs_coeff_pulse_le_of_flow hfinf hfpos d.angle_mem d.angle_deriv
      d.inverse_value hsurj d.state_deriv h1 t ht
    rwa [coeff_one] at h
  let b : ℝ := 1 / Real.sqrt (1 + m ^ 2)
  have hb0 : (0 : ℝ) ≤ b := by dsimp [b]; positivity
  have hb1 : b < 1 := by
    dsimp [b]
    exact one_div_sqrt_one_add_sq_lt_one hm
  let aa : ℝ := 2 * eps
  have hba : b < aa := by
    have hsqrt : m < Real.sqrt (1 + m ^ 2) := by
      rw [lt_sqrt (by positivity)]
      nlinarith
    have hprod : 1 < 2 * eps * m := by
      have hmprod := mul_le_mul_of_nonneg_left hbar
        (by positivity : 0 ≤ 2 * eps)
      have hinv : eps * eps⁻¹ = 1 := by field_simp
      nlinarith [sq_nonneg eps]
    have hprod' : 1 < 2 * eps * Real.sqrt (1 + m ^ 2) := by
      have := mul_lt_mul_of_pos_left hsqrt (by positivity : 0 < 2 * eps)
      linarith
    dsimp [b, aa]
    rw [div_lt_iff₀ (HairpinRelative.sqrt_one_add_sq_pos m)]
    simpa [mul_comm] using hprod'
  have ha0 : (0 : ℝ) ≤ aa := by dsimp [aa]; positivity
  have ha1 : aa < 1 := by dsimp [aa]; linarith
  let alpha : ℝ := 1 / Am
  have halpha : 0 < alpha := by dsimp [alpha]; positivity
  let A : ℝ := 2 / m
  let C : ℝ := max (relativeConst 0 * (A * Real.exp (A ^ 2 / 2)))
    (relativeConst 1 * (A * Real.exp (A ^ 2 / 2)))
  have hC0 : 0 ≤ C := by
    dsimp [C]
    exact le_trans (mul_nonneg (hrc0 0) (by positivity)) (le_max_left _ _)
  let CU : ℝ := C * Real.exp (alpha * |ConsecutiveData.phase f theta g|)
  have hCU0 : 0 ≤ CU := by dsimp [CU]; positivity
  obtain ⟨CK, Km, Kd, kstar, kd, profile⟩ :=
    exists_profileConstants (alpha := alpha) (beta := alpha / 4) (a := aa)
      (au := aa) (CU := CU) (DU := relativeConst 1) (DU2 := relativeConst 2)
      (D := relativeConst 1) (by positivity) (by linarith) (hrc0 1) (hrc0 1)
      (hrc0 2) ha0 ha1 ha0 ha1
  let beta : ℝ := alpha / 8
  have hbeta : 0 < beta := by dsimp [beta]; positivity
  let cst : ℝ := ModelOrbitDefect.matchConst aa C CK CU (relativeConst 1)
    Km Kd aa alpha (alpha / 4) ((1 + b) / 2 * Real.pi)
  have hcst : 0 ≤ cst := by
    dsimp [cst]
    exact matchConst_nonneg profile halpha hC0 hCU0
  have hkstar : 0 ≤ kstar :=
    le_trans (div_nonneg ha0 (Real.sqrt_nonneg _)) profile.current_rear_sup
  have hkd : 0 ≤ kd := profile.rear_derivative_pos.le
  have hbb : (1 : ℝ) / Real.sqrt (1 + m ^ 2) < 1 :=
    one_div_sqrt_one_add_sq_lt_one hm
  have hbb0 : (0 : ℝ) ≤ 1 / Real.sqrt (1 + m ^ 2) := by positivity
  have hyb : ∀ t ∈ Ioo (0 : ℝ) Real.pi,
      |pulseField f t| ≤ 1 / Real.sqrt (1 + m ^ 2) := by
    intro t ht
    rw [abs_of_nonneg (pulseField_nonneg_interior hfpos ht)]
    exact pulseField_le_of_barrier hm (hlow t ht) ht
  have hDp0 : (0 : ℝ) ≤ Dp := le_trans (abs_nonneg _) (hdb _ (d.angle_mem 0))
  have hD1 : (0 : ℝ) ≤
      Dp / Real.sqrt (1 - (1 / Real.sqrt (1 + m ^ 2)) ^ 2) ^ 3 := by
    positivity
  have hrelK := relK_of_pulse_deriv_bound hfinf hfpos hbb0 hbb hyb hdb
    d.angle_mem d.angle_deriv
  have hdecayJ : ∀ j ≤ 4, ∀ s : ℝ,
      |iteratedDeriv j (fun r => pulseField f (theta (x r))) s| ≤
        relativeConst j * (A * Real.exp (A ^ 2 / 2)) * Real.exp (-|s| / Am) :=
    fun j hj s => (data_of_interior hfinf hm hlow d.angle_mem d.angle_value
      d.angle_deriv d.inverse_value d.state_deriv hsm hsurj hA hMpos hdecay
      relativeConst hrc0 hrel).decay j hj s
  have hexp : ∀ s : ℝ, Real.exp (-|s| / Am) ≤
      Real.exp (-alpha * |s|) := by
    intro s
    apply Real.exp_le_exp.mpr
    dsimp [alpha]
    have heq : -|s| / Am = -(1 / Am) * |s| := by ring
    rw [heq]
  have hdecStep : ∀ j : ℕ, j ≤ 4 →
      relativeConst j * (A * Real.exp (A ^ 2 / 2)) ≤ C → ∀ s : ℝ,
      |iteratedDeriv j (fun r => pulseField f (theta (x r))) s| ≤
        C * Real.exp (-alpha * |s|) := by
    intro j hj hle s
    exact le_trans (hdecayJ j hj s)
      (mul_le_mul hle (hexp s) (Real.exp_pos _).le
        (le_trans (mul_nonneg (hrc0 j) (by positivity)) hle))
  have hdec0 : ∀ s,
      |pulseField f (theta (x s))| ≤ C * Real.exp (-alpha * |s|) := by
    intro s
    have h := hdecStep 0 (by norm_num) (le_max_left _ _) s
    simpa [iteratedDeriv_zero] using h
  have hdec1 : ∀ s,
      |iteratedDeriv 1 (fun r => pulseField f (theta (x r))) s| ≤
        C * Real.exp (-alpha * |s|) :=
    hdecStep 1 (by norm_num) (le_max_right _ _)
  let q := ConsecutiveData.phase f theta g
  let yu : ℝ → ℝ := ConsecutiveData.previousPulse f theta x g
  let ypu : ℝ → ℝ := ConsecutiveData.previousPulseDeriv f theta g yp0
  let Kstar : ℝ → ℝ := fun s => curvField f (theta s)
  have hyu0 : ∀ s, 0 ≤ yu s := by
    intro s
    exact pulseField_nonneg_interior hfpos (d.angle_mem (x (s - q)))
  have hyub : ∀ s, yu s ≤ CU * Real.exp (-alpha * |s|) := by
    intro s
    have h := hdec0 (s - q)
    have habs : -|s - q| ≤ -|s| + |q| := by
      have ht := abs_add_le (s - q) q
      rw [sub_add_cancel] at ht
      linarith
    calc
      yu s ≤ C * Real.exp (-alpha * |s - q|) := by
        rw [show yu s = pulseField f (theta (x (s - q))) by rfl]
        exact (le_abs_self _).trans h
      _ ≤ C * Real.exp (alpha * |q| - alpha * |s|) := by
        gcongr
        nlinarith
      _ = CU * Real.exp (-alpha * |s|) := by
        dsimp [CU, q]
        rw [show alpha * |ConsecutiveData.phase f theta g| - alpha * |s| =
          alpha * |ConsecutiveData.phase f theta g| + (-alpha * |s|) by ring,
          Real.exp_add]
        ring
  have hypub : ∀ s, |ypu s| ≤ relativeConst 1 * yu s := by
    intro s
    simpa [ypu, yp0, yu, ConsecutiveData.previousPulse,
      ConsecutiveData.previousPulseDeriv, q] using hrel 1 (by norm_num) (s - q)
  have hsupU : ∀ s, yu s ≤ b := by
    intro s
    exact pulseField_le_of_barrier hm (hlow _ (d.angle_mem (x (s - q))))
      (d.angle_mem (x (s - q)))
  have hKstar : ∀ s, Kstar s = yu s + G (yu s) * ypu s := by
    intro s
    simpa [Kstar, yu, ypu, yp0, ConsecutiveData.previousPulse,
      ConsecutiveData.previousPulseDeriv, q, hairpinCurvature] using
      (CanonicalTranslatorLocalPhase.front_curvature_identity_shifted
        d d.x_zero consecutive.pulse_deriv s)
  have hK0 : ∀ s, 0 ≤ Kstar s := by
    intro s
    exact div_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi
      (d.angle_mem s).1.le (d.angle_mem s).2.le)
      (hfpos _ (d.angle_mem s)).le
  have hKb : ∀ s, Kstar s ≤ (2 / m) * Real.exp (-alpha * |s|) := by
    intro s
    simpa [Kstar, alpha, div_eq_mul_inv, mul_comm] using hdecay s
  have hKiso : ∀ s, Kstar s ≤ 2 * eps := by
    intro s
    have hgap0 : 0 < eps⁻¹ - eps :=
      lt_trans zero_lt_one (BarrierEstimates.m_gt_one heps heps10)
    have hft : eps⁻¹ - eps ≤ f (theta s) :=
      hbar.trans (hlow _ (d.angle_mem s))
    have hfp : 0 < f (theta s) := lt_of_lt_of_le hgap0 hft
    calc
      Kstar s = Real.sin (theta s) / f (theta s) := rfl
      _ ≤ 1 / f (theta s) :=
        div_le_div_of_nonneg_right (Real.sin_le_one _) hfp.le
      _ ≤ 1 / (eps⁻¹ - eps) := one_div_le_one_div_of_le hgap0 hft
      _ ≤ 2 * eps := WideHairpinSmallness.inv_gap_le_two_mul heps heps10
  obtain ⟨HstripActual, -, hstripActual⟩ :=
    PeriodizedStripData.exists_threshold halpha hb1 hyu0 hyub hsupU
  obtain ⟨HbudgetActual, -, hbudgetActual⟩ :=
    exists_simultaneous_strip_budget_threshold
      (a := aa) (au := aa) halpha (by simpa using hba)
  let HstripAll := max HstripActual HbudgetActual
  have hYaActual : ∀ H, HstripAll ≤ H → ∀ u,
      (∑' j : ℤ, yu (u - j * H)) ≤ aa := by
    intro H hH u
    have hs := hstripActual H ((le_max_left _ _).trans hH)
    exact (le_abs_self _).trans (by
      simpa [periodizedPulse] using hs.periodized_abs_le
        (hbudgetActual H ((le_max_right _ _).trans hH)).1 u)
  obtain ⟨Hfront, -, hfront⟩ :=
    ActualFrontCurvatureLargePeriod.exists_threshold_modelCurvature_le
      (y := yu) (yp := ypu) (Kstar := Kstar) (C := CU) (CK := 2 / m)
      (alpha := alpha) (a := aa) (D := relativeConst 1)
      (kiso := 2 * eps) (kh := 1 / 2) (Hstrip := HstripAll)
      halpha hyu0 hyub (hrc0 1) hypub ha0 ha1 hYaActual hKstar hK0 hKb
      hKiso (by linarith)
  let Hactual := max Hrequired Hfront
  have hl : ∀ t, m ≤ f (theta t) := fun t => hlow _ (d.angle_mem t)
  have hu : ∀ t, f (theta t) ≤ Am := fun t => hupp _ (d.angle_mem t)
  obtain ⟨Hs, kappas, deltaStep, hdelta, hstart, hlinear, hstep, -, -,
    ⟨model, hmodel_kd, hmodel_kstar, hmodel_KP_C2, hmodel_kH_C2,
      hmodel_current, hmodel_a, hmodel_au⟩,
    hkpos, hkappa, -⟩ :=
    StrictConstructedModelGeometry.exists_strict_configuredModelSequence_above
      (theta0 := 0) Hactual consecutive
      d hfinf hfpos hMpos hD1 hdecay hrelK hm hmA hl hu profile one_pos
      halpha hdec0 hdec1 (by dsimp [CU]; exact le_rfl) (le_refl _)
      (le_refl _) (le_refl _) hb0 (by simpa using hba)
      (fun s => le_trans (pulseField_le_of_barrier hm
        (hlow _ (d.angle_mem (x s))) (d.angle_mem (x s))) (by simpa [b]))
      (le_refl _) profile.rear_derivative_pos.le hcst
  have hH0 : 0 < Hs 0 := model.separation_pos 0
  let Dseq : Data :=
    { kappas := kappas
      Hs := Hs
      deltaStep := deltaStep
      kd := kd
      kstar := kstar
      matchCoefficient := cst
      beta := beta
      deltaStep_pos := hdelta
      beta_pos := hbeta
      matchCoefficient_nonneg := hcst
      kd_nonneg := hkd
      kstar_nonneg := hkstar
      separation_zero_pos := hH0
      separation_lower := model.separation_mono
      separation_linear := hlinear
      separation_step := hstep
      model := model
      model_kd := hmodel_kd
      model_kstar := hmodel_kstar
      model_KP_C2 := fun n => (hmodel_KP_C2 n).of_le (by norm_num)
      model_kH_C2 := fun n => (hmodel_kH_C2 n).of_le (by norm_num)
      phase := ConsecutiveData.phase f theta g
      model_current_curvature_eq_next_shift := hmodel_current
      model_curvature_pos := hkpos }
  have hfrontHalf : ∀ n s, Dseq.kappas n s ≤ 1 / 2 := by
    intro n s
    have hHn : Hfront ≤ Hs n :=
      (le_max_right Hrequired Hfront).trans
        (hstart.trans (model.separation_mono n))
    rw [show Dseq.kappas n = modelCurvature yu ypu (Hs n) by
      simpa [Dseq, yu, ypu, yp0] using hkappa n]
    exact hfront (Hs n) hHn s
  have hrearHalf : ∀ n s, (Dseq.model.configs n).kH s ≤ 1 / 2 := by
    intro n s
    let cfg := Dseq.model.configs n
    have hY0 := cfg.Y_nonneg (cfg.sf s)
    have hYle : cfg.Y (cfg.sf s) ≤ aa :=
      (le_abs_self _).trans (by simpa [Dseq, hmodel_a] using cfg.hYa (cfg.sf s))
    have haa : aa ≤ 1 / 5 := by dsimp [aa]; linarith
    have hrad : 0 < 1 - cfg.Y (cfg.sf s) ^ 2 := by
      nlinarith [cfg.ha1, cfg.ha0]
    have hsqrt : 2 * cfg.Y (cfg.sf s) ≤
        Real.sqrt (1 - cfg.Y (cfg.sf s) ^ 2) := by
      refine (Real.le_sqrt (by positivity) (by positivity)).mpr ?_
      nlinarith
    rw [show (Dseq.model.configs n).kH s = cfg.kH s by rfl,
      cfg.kH_eq, cfg.tan_dl, div_le_iff₀ (Real.sqrt_pos.2 hrad)]
    nlinarith
  have hsteeringHalf : Dseq.model.a ≤ 1 / 2 := by
    simpa [Dseq, hmodel_a, aa] using (show 2 * eps ≤ (1 : ℝ) / 2 by linarith)
  refine ⟨⟨Dseq, hsteeringHalf, hfrontHalf, hrearHalf⟩, ?_⟩
  exact (le_max_left Hrequired Hfront).trans hstart

/-- The compatibility projection retaining only the requested lower
separation. -/
theorem exists_data_above_of_eps (Hrequired : ℝ) {eps : ℝ} (heps : 0 < eps)
    (heps10 : eps ≤ 1 / 10) : ∃ D : Data, Hrequired ≤ D.Hs 0 := by
  obtain ⟨E, hE⟩ := exists_dataWithActualHalf_above_of_eps Hrequired heps heps10
  exact ⟨E.data, hE⟩

/-- **The epsilon construction with all weighted-closing signs retained.** -/
theorem exists_data_of_eps {eps : ℝ} (heps : 0 < eps)
    (heps10 : eps ≤ 1 / 10) : Nonempty Data := by
  obtain ⟨D, -⟩ := exists_data_above_of_eps 0 heps heps10
  exact ⟨D⟩

/-- The constructed data feed directly into the sharp weighted canonical
marked-defect theorem for every admissible transport factor `K`. -/
theorem Data.summable_weightedCanonicalMarkedDefect
    (D : Data) {K : ℝ} (hK : 0 ≤ K)
    (hthreshold : K * Real.exp (-(D.beta * D.deltaStep)) < 1) :
    Summable
      (PathMetric.WeightedRecursiveDefect.weightedDefect K
        (PathMetric.WeightedMarkedDefectThreshold.canonicalMarkedDefect
          D.matchCoefficient 1 D.kstar D.kd D.beta D.Hs)) := by
  exact
    PathMetric.WeightedMarkedDefectThreshold.summable_weighted_canonicalMarkedDefect
      hK D.beta_pos D.deltaStep_pos D.matchCoefficient_nonneg (by norm_num)
      D.kstar_nonneg D.kd_nonneg D.separation_zero_pos D.separation_lower
      D.separation_linear hthreshold

end ConstructedConfiguredSequenceWeighted
