import UnitTangentIterates.CanonicalConfiguredModelSequence
import UnitTangentIterates.CanonicalConsecutiveGeometricCertificates
import UnitTangentIterates.CanonicalPulseTailAdapters
import UnitTangentIterates.ModelOrbitDefectMarked
import UnitTangentIterates.ModelOrbitConfigSmooth

/-! # Canonical configured model sequence capstone -/

noncomputable section

namespace UnitTangentIterates

open scoped ContDiff
open ShiftedCurvatureJetMajorant PaperHairpinQuantitativeData
open PaperHairpinConfig ModelPeriodContinuity ModelOrbitDefect
open PaperHairpinQuantitativeData.ConsecutiveData

namespace CanonicalConfiguredModelCapstone

/-- A tail of a configured model sequence is again configured. -/
def shiftConfiguredModelSequence
    {kappas : ℕ → ℝ → ℝ} {Hs eps : ℕ → ℝ}
    (model : UnconditionalAssembly.ConfiguredModelSequence kappas Hs eps)
    (N : ℕ) (hHs : Monotone Hs) :
    UnconditionalAssembly.ConfiguredModelSequence
      (fun n => kappas (N + n)) (fun n => Hs (N + n)) (fun n => eps (N + n)) where
  alpha := model.alpha
  beta := model.beta
  a := model.a
  au := model.au
  C := model.C
  CU := model.CU
  CK := model.CK
  DU := model.DU
  DU2 := model.DU2
  D := model.D
  Km := model.Km
  Kd := model.Kd
  Bcell := model.Bcell
  thetaBase := model.thetaBase
  kstar := model.kstar
  kd := model.kd
  configs := fun n => by
    simpa [Nat.add_assoc] using model.configs (N + n)
  config_from_paper := fun n => by
    simpa [Nat.add_assoc] using model.config_from_paper (N + n)
  curvature_eq := fun n => by
    simpa using model.curvature_eq (N + n)
  separation_mono := fun n => hHs (Nat.le_add_right N n)

/-- From one fixed canonical quantitative profile, all sufficiently large
separations admit a strictly increasing recurrence sequence carrying actual
paper witnesses and hence a configured model sequence. -/
theorem exists_configuredModelSequence_with_step
    {f theta x g gp yp : ℝ → ℝ} {M Delta beta0 Cq Ht : ℝ} {Pfun Pp : ℝ → ℝ}
    {alpha beta a au C CU CK DU DU2 D Km Kd B theta0 kstar kd eps0 b : ℝ}
    {At Mt D1 m Am : ℝ}
    (c : ConsecutiveData f theta x g gp yp M Delta beta0 Cq Ht Pfun Pp)
    (d : CanonicalTranslatorLocalPhase.InteriorPhaseData f theta x g gp)
    (hf : ContDiffOn ℝ ∞ f (Set.Ioo 0 Real.pi))
    (hfpos : ∀ t ∈ Set.Ioo (0:ℝ) Real.pi, 0 < f t)
    (hMt : 0 < Mt) (hD1 : 0 ≤ D1)
    (hdecayK : ∀ u, HairpinRelative.curvField f (theta u) ≤
      At * Real.exp (-|u| / Mt))
    (hrelK : ∀ u, |deriv (fun r => HairpinRelative.curvField f (theta r)) u| ≤
      D1 * HairpinRelative.curvField f (theta u))
    (hm : 0 < m) (hmA : m ≤ Am)
    (hl : ∀ t, m ≤ f (theta t)) (hu : ∀ t, f (theta t) ≤ Am)
    (profile : ProfileConstants (alpha := alpha) (beta := beta) (a := a)
      (au := au) (CU := CU) (CK := CK) (DU := DU) (DU2 := DU2) (D := D)
      (Km := Km) (Kd := Kd) (kstar := kstar) (kd := kd))
    (heps : 0 < eps0) (halpha : 0 < alpha)
    (hdec0 : ∀ s, |ConsecutiveData.currentPulse f theta x s| ≤
      C * Real.exp (-alpha * |s|))
    (hdec1 : ∀ s, |yp s| ≤ C * Real.exp (-alpha * |s|))
    (hCU : C * Real.exp (alpha * |ConsecutiveData.phase f theta g|) ≤ CU)
    (hD : c.quantitative.relativeConst 1 ≤ D)
    (hDU : c.quantitative.relativeConst 1 ≤ DU)
    (hDU2 : c.quantitative.relativeConst 2 ≤ DU2)
    (hb0 : 0 ≤ b) (hbmin : b < min a au)
    (hsup : ∀ s, ConsecutiveData.currentPulse f theta x s ≤ b)
    (hB : (1 + b) / 2 * Real.pi ≤ B)
    (hkd0 : 0 ≤ kd)
    (hmatch0 : 0 ≤ matchConst a C CK CU DU Km Kd au alpha beta B) :
    ∃ (Hs : ℕ → ℝ) (kappas : ℕ → ℝ → ℝ) (deltaStep : ℝ),
      0 < deltaStep ∧
      (∀ n : ℕ, Hs 0 + n * deltaStep ≤ Hs n) ∧
      (∀ n, Hs n + deltaStep ≤ Hs (n + 1)) ∧
      (∀ n, Hs n < Hs (n + 1)) ∧
      (∀ n, rearPeriod (ConsecutiveData.currentPulse f theta x) (Hs (n + 1)) = Hs n) ∧
      ∃ model : UnconditionalAssembly.ConfiguredModelSequence
          kappas Hs (fun _ => eps0),
        model.kstar = kstar ∧ model.kd = kd ∧
        (∀ n, ContDiff ℝ 3
          (modelCurvature (model.configs n).yu (model.configs n).yu' (Hs n))) ∧
        (∀ n, ContDiff ℝ 3 (model.configs n).kH) ∧
        Summable (fun n : ℕ =>
        CurvatureStabilityL1.l1Modulus (2 * kd)
          (matchConst a C CK CU DU Km Kd au alpha beta B *
            Real.exp (-(beta * Hs (n + 1)))) (Hs n) *
          (1 : ℝ) ^ 2 * (1 + kstar * (1 : ℝ))) := by
  let y := ConsecutiveData.currentPulse f theta x
  let yu := ConsecutiveData.previousPulse f theta x g
  let ypu := ConsecutiveData.previousPulseDeriv f theta g yp
  have hy0 : ∀ s, 0 ≤ y s := c.currentPulse_nonneg_interior hfpos
  have hydec : ∀ s, y s ≤ C * Real.exp (-alpha * |s|) := fun s =>
    (le_abs_self _).trans (hdec0 s)
  have hyc : Continuous y := (c.quantitative.smooth_pulse 0).continuous
  obtain ⟨hsqint, hsqpos⟩ := c.currentPulse_massData.integrable_sq_and_integral_sq_pos
    hyc hy0 hb0 hsup
  obtain ⟨Hstrip, hHstrip0, hstrip⟩ :=
    PeriodizedStripData.exists_threshold halpha
      (lt_trans (lt_of_lt_of_le hbmin (min_le_left a au)) profile.current_strip_lt)
      hy0 hydec hsup
  obtain ⟨Hbudget, hHbudget0, hbudget⟩ :=
    exists_simultaneous_strip_budget_threshold halpha hbmin
  obtain ⟨Hpaper, hHpaper0, hpaper⟩ :=
    PaperHairpinData.exists_threshold_toPaperHairpinData_of_canonical_consecutive
      c d hf hfpos profile heps halpha.le hdec0 hdec1 hCU hD hDU hDU2
  obtain ⟨bpos, hbpos, hlower⟩ := c.exists_previous_lower_comparison_interior d hf hfpos hMt hD1 hdecayK hrelK hm hmA hl hu
  have hC0 : 0 ≤ C := Periodization.const_nonneg hy0 hydec
  have hCU0 : 0 ≤ CU := by
    have := hCU
    have he : 0 < Real.exp (alpha * |ConsecutiveData.phase f theta g|) := Real.exp_pos _
    nlinarith
  obtain ⟨Hpositive, hHpositive0, hpositive⟩ :=
    FrontPeriodizationPositivity.exists_largePeriod_positivity_threshold
      halpha hbpos profile.prior_strip_nonneg profile.prior_strip_lt
      profile.prior_derivative_nonneg hCU0
  let Hrear := PerimeterHairpinPulse.threshold alpha C b
  let H0 := max 1 (max Hstrip (max Hbudget (max Hpaper
    (max Hpositive (max Hrear (4 * B))))))
  have hH0 : 0 < H0 := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hstrip_le : Hstrip ≤ H0 := le_max_of_le_right (le_max_left _ _)
  have hbudget_le : Hbudget ≤ H0 :=
    le_max_of_le_right (le_max_of_le_right (le_max_left _ _))
  have hpaper_le : Hpaper ≤ H0 :=
    le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_left _ _)))
  have hpositive_le : Hpositive ≤ H0 :=
    le_max_of_le_right (le_max_of_le_right (le_max_of_le_right
      (le_max_of_le_right (le_max_left _ _))))
  have hrear_le : Hrear ≤ H0 :=
    le_max_of_le_right (le_max_of_le_right (le_max_of_le_right
      (le_max_of_le_right (le_max_of_le_right (le_max_left _ _)))))
  have hB_le : 4 * B ≤ H0 :=
    le_max_of_le_right (le_max_of_le_right (le_max_of_le_right
      (le_max_of_le_right (le_max_of_le_right (le_max_right _ _)))))
  have rearData : ∀ H, H0 ≤ H → RearCellData y H (rearPeriod y H) B := by
    intro H hH
    simpa [y, rearPeriod] using PaperHairpinConfig.rearCell_of_quantitative_tail
      c halpha (lt_trans hbmin
        (lt_of_le_of_lt (min_le_left a au) profile.current_strip_lt))
      hydec hsup (hrear_le.trans hH) hB hfpos
  have hYle : ∀ H, H0 ≤ H → ∀ s,
      |ModelOrbitDefect.periodizedPulse y H s| ≤ 1 := by
    intro H hH s
    exact (PeriodizedStripData.periodized_abs_lt_one
      (hstrip H (hstrip_le.trans hH)) s).le
  obtain ⟨hhalf, hstrict⟩ := CanonicalSeparationRecurrence.tail_recurrence_bounds
    halpha hH0 hB_le hyc hy0 hsup hdec0 hsqint hsqpos rearData hYle
  obtain ⟨Hs, hHs0, hHsbase, hinc, hrec⟩ :=
    CanonicalSeparationRecurrence.exists_strict_sequence
      halpha hH0 hyc c.pulse_deriv hdec0 hdec1 hhalf hstrict
  let deltaStep : ℝ := (∫ s, y s ^ 2) / 2
  have hdeltaStep : 0 < deltaStep := by
    dsimp [deltaStep]
    linarith
  have hstep : ∀ n, Hs n + deltaStep ≤ Hs (n + 1) := by
    intro n
    have hgrow := ModelPeriodGrowth.rearPeriod_le_sub
      (y := y) (C := C) (alpha := alpha) (Km := b) halpha hyc hy0 hsup
      hdec0 hsqint (lt_of_lt_of_le hH0 (hHsbase (n + 1)))
      (hYle (Hs (n + 1)) (hHsbase (n + 1)))
    rw [hrec n] at hgrow
    show Hs n + (∫ s, y s ^ 2) / 2 ≤ Hs (n + 1)
    linarith [hgrow]
  have hlinear : ∀ n : ℕ, Hs 0 + n * deltaStep ≤ Hs n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        have hs := hstep n
        push_cast
        push_cast at ih
        nlinarith
  have edgeData : ∀ n, PaperHairpinData (alpha := alpha) (beta := beta)
      (a := a) (au := au) (C := C) (CU := CU) (CK := CK) (DU := DU)
      (DU2 := DU2) (D := D) (Km := Km) (Kd := Kd) (B := B)
      (theta0 := theta0) (kstar := kstar) (kd := kd) (eps0 := eps0)
      (H := Hs (n + 1)) (P := Hs n) y yu ypu := fun n => Nonempty.some (by
    have hn := hHsbase n
    have hn1 := hHsbase (n + 1)
    have hsCurr := hstrip (Hs n) (hstrip_le.trans hn)
    have hsNext := hstrip (Hs (n + 1)) (hstrip_le.trans hn1)
    have hbCurr := (hbudget (Hs n) (hbudget_le.trans hn)).2
    have hbNext := (hbudget (Hs (n + 1)) (hbudget_le.trans hn1)).1
    have hprior := previous_strip_of_current_strip (g := g) hsCurr hbCurr
    obtain ⟨y2, han⟩ := c.pulsePairAnalyticData_of_quantitative hy0 halpha.le
      hdec0 hdec1 hCU hD hDU hDU2 hprior
    have hp := hpositive (Hs n) (hpositive_le.trans hn)
    have hsum := han.previousHairpinCurvature_summable halpha hp.1
      profile.prior_derivative_nonneg profile.prior_strip_lt
    have hpos : CurvaturePositivityData yu ypu (Hs n) :=
      CurvaturePositivityData.of_large_period halpha hp.1 hp.2.1
        han.previous_nonneg han.previous_decay profile.prior_derivative_nonneg
        han.previous_relative profile.prior_strip_nonneg profile.prior_strip_lt
        han.previous_periodized_strip hbpos.le hlower hsum hp.2.2
    have hr := rearData (Hs (n + 1)) hn1
    have hr' : RearCellData y (Hs (n + 1)) (Hs n) B := by
      simpa [hrec n] using hr
    exact hpaper (Hs (n + 1)) (Hs n) b (hpaper_le.trans hn1)
      hprior hsNext hbNext hpos hr')
  let kappas : ℕ → ℝ → ℝ := fun n =>
    ModelOrbitDefect.modelCurvature (edgeData n).toConfig.1.yu
      (edgeData n).toConfig.1.yu' (Hs n)
  let model : UnconditionalAssembly.ConfiguredModelSequence
      kappas Hs (fun _ => eps0) :=
    CanonicalConfiguredModelSequence.ofPaperHairpinData edgeData
      (fun n => (monotone_nat_of_le_succ fun k => (hinc k).le) (Nat.zero_le n))
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
    have h := hiter (c.quantitative.smooth_pulse 2)
      (show 0 < 2 by norm_num) s
    simpa [y, y1, iteratedDeriv_zero] using h
  have hy12 : ∀ s, HasDerivAt y1 (y2 s) s := fun s => by
    simpa [y1, y2] using hiter
      (c.quantitative.smooth_pulse 3) (show 1 < 3 by norm_num) s
  have hy23 : ∀ s, HasDerivAt y2 (y3 s) s := fun s => by
    simpa [y2, y3] using hiter
      (c.quantitative.smooth_pulse 4) (show 2 < 4 by norm_num) s
  have hy34 : ∀ s, HasDerivAt y3 (y4 s) s := fun s => by
    simpa [y3, y4] using hiter
      (c.quantitative.smooth_pulse 5) (show 3 < 5 by norm_num) s
  have hy3c : Continuous y3 := by
    exact (Differentiable.continuous fun s =>
      (hiter (c.quantitative.smooth_pulse 5)
        (show 3 < 5 by norm_num) s).differentiableAt)
  have hy4c : Continuous y4 := by
    exact (Differentiable.continuous fun s =>
      (hiter (c.quantitative.smooth_pulse 6)
        (show 4 < 6 by norm_num) s).differentiableAt)
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
      |iteratedDeriv j y s| ≤ Cjet * Real.exp (-(M⁻¹) * |s|) := by
    intro s
    calc
      |iteratedDeriv j y s| ≤
          c.quantitative.decayConst j * Real.exp (-|s| / M) := by
        simpa [y] using c.quantitative.decay j (hj.trans (by norm_num)) s
      _ ≤ Cjet * Real.exp (-|s| / M) :=
        mul_le_mul_of_nonneg_right hjC (Real.exp_pos _).le
      _ = Cjet * Real.exp (-(M⁻¹) * |s|) := by ring
  have hyb0 : ∀ s, |y s| ≤ Cjet * Real.exp (-(M⁻¹) * |s|) := by
    intro s
    simpa [iteratedDeriv_zero] using
      hdecayJet 0 (by norm_num) (le_max_left _ _) s
  have hyb1 : ∀ s, |y1 s| ≤ Cjet * Real.exp (-(M⁻¹) * |s|) :=
    hdecayJet 1 (by norm_num) (le_max_of_le_right (le_max_left _ _))
  have hyb2 : ∀ s, |y2 s| ≤ Cjet * Real.exp (-(M⁻¹) * |s|) :=
    hdecayJet 2 (by norm_num)
      (le_max_of_le_right (le_max_of_le_right (le_max_left _ _)))
  have hyb3 : ∀ s, |y3 s| ≤ Cjet * Real.exp (-(M⁻¹) * |s|) :=
    hdecayJet 3 (by norm_num)
      (le_max_of_le_right (le_max_of_le_right
        (le_max_of_le_right (le_max_left _ _))))
  have hyb4 : ∀ s, |y4 s| ≤ Cjet * Real.exp (-(M⁻¹) * |s|) :=
    hdecayJet 4 (by norm_num)
      (le_max_of_le_right (le_max_of_le_right
        (le_max_of_le_right (le_max_right _ _))))
  have hsmooth : ∀ n,
      ContDiff ℝ 3
        (modelCurvature (model.configs n).yu (model.configs n).yu' (Hs n)) ∧
      ContDiff ℝ 3 (model.configs n).kH := by
    intro n
    apply ModelOrbitDefect.Config.contDiff_three_endpoints_of_common_pulse
      (gamma := M⁻¹) (Cjet := Cjet) (q := ConsecutiveData.phase f theta g)
      (model.configs n) (inv_pos.mpr c.quantitative.M_pos) hCjet
      hy01 hy12 hy23 hy34 hy3c hy4c hyb0 hyb1 hyb2 hyb3 hyb4
    · change (edgeData n).toConfig.1.y = y
      exact (edgeData n).toConfig.2.1
    · change (edgeData n).toConfig.1.yu =
        fun s => y (s - ConsecutiveData.phase f theta g)
      simpa [y, yu, ConsecutiveData.previousPulse] using
        (edgeData n).toConfig.2.2.1
    · change (edgeData n).toConfig.1.yu' =
        fun s => y1 (s - ConsecutiveData.phase f theta g)
      simpa [ypu, ConsecutiveData.previousPulseDeriv, hyp_eq] using
        (edgeData n).toConfig.2.2.2
  have hsummable := ModelOrbitDefectMarked.summable_markedDefect
    profile.beta_pos hdeltaStep hmatch0 hkd0 hH0 hHsbase hlinear
    (L := (1 : ℝ)) (kstar := kstar)
  exact ⟨Hs, kappas, deltaStep, hdeltaStep, hlinear, hstep, hinc, hrec,
    model, rfl, rfl, fun n => (hsmooth n).1, fun n => (hsmooth n).2, hsummable⟩

/-- Original capstone projection, retaining its established public interface. -/
theorem exists_configuredModelSequence
    {f theta x g gp yp : ℝ → ℝ} {M Delta beta0 Cq Ht : ℝ} {Pfun Pp : ℝ → ℝ}
    {alpha beta a au C CU CK DU DU2 D Km Kd B theta0 kstar kd eps0 b : ℝ}
    (c : ConsecutiveData f theta x g gp yp M Delta beta0 Cq Ht Pfun Pp)
    (d : CanonicalTranslatorLocalPhase.InteriorPhaseData f theta x g gp)
    {At Mt D1 m Am : ℝ}
    (hf : ContDiffOn ℝ ∞ f (Set.Ioo 0 Real.pi))
    (hfpos : ∀ t ∈ Set.Ioo (0:ℝ) Real.pi, 0 < f t)
    (hMt : 0 < Mt) (hD1 : 0 ≤ D1)
    (hdecayK : ∀ u, HairpinRelative.curvField f (theta u) ≤
      At * Real.exp (-|u| / Mt))
    (hrelK : ∀ u, |deriv (fun r => HairpinRelative.curvField f (theta r)) u| ≤
      D1 * HairpinRelative.curvField f (theta u))
    (hm : 0 < m) (hmA : m ≤ Am)
    (hl : ∀ t, m ≤ f (theta t)) (hu : ∀ t, f (theta t) ≤ Am)
    (profile : ProfileConstants (alpha := alpha) (beta := beta) (a := a)
      (au := au) (CU := CU) (CK := CK) (DU := DU) (DU2 := DU2) (D := D)
      (Km := Km) (Kd := Kd) (kstar := kstar) (kd := kd))
    (heps : 0 < eps0) (halpha : 0 < alpha)
    (hdec0 : ∀ s, |ConsecutiveData.currentPulse f theta x s| ≤
      C * Real.exp (-alpha * |s|))
    (hdec1 : ∀ s, |yp s| ≤ C * Real.exp (-alpha * |s|))
    (hCU : C * Real.exp (alpha * |ConsecutiveData.phase f theta g|) ≤ CU)
    (hD : c.quantitative.relativeConst 1 ≤ D)
    (hDU : c.quantitative.relativeConst 1 ≤ DU)
    (hDU2 : c.quantitative.relativeConst 2 ≤ DU2)
    (hb0 : 0 ≤ b) (hbmin : b < min a au)
    (hsup : ∀ s, ConsecutiveData.currentPulse f theta x s ≤ b)
    (hB : (1 + b) / 2 * Real.pi ≤ B)
    (hkd0 : 0 ≤ kd)
    (hmatch0 : 0 ≤ matchConst a C CK CU DU Km Kd au alpha beta B) :
    ∃ (Hs : ℕ → ℝ) (kappas : ℕ → ℝ → ℝ) (deltaStep : ℝ),
      0 < deltaStep ∧
      (∀ n : ℕ, Hs 0 + n * deltaStep ≤ Hs n) ∧
      (∀ n, Hs n < Hs (n + 1)) ∧
      (∀ n, rearPeriod (ConsecutiveData.currentPulse f theta x) (Hs (n + 1)) = Hs n) ∧
      Nonempty (UnconditionalAssembly.ConfiguredModelSequence
        kappas Hs (fun _ => eps0)) ∧
      Summable (fun n : ℕ =>
        CurvatureStabilityL1.l1Modulus (2 * kd)
          (matchConst a C CK CU DU Km Kd au alpha beta B *
            Real.exp (-(beta * Hs (n + 1)))) (Hs n) *
          (1 : ℝ) ^ 2 * (1 + kstar * (1 : ℝ))) := by
  obtain ⟨Hs, kappas, deltaStep, hdelta, hlinear, -, hinc, hrec,
    model, -, -, -, -, hsum⟩ :=
    exists_configuredModelSequence_with_step (theta0 := theta0)
      c d hf hfpos hMt hD1 hdecayK hrelK hm hmA hl hu profile heps halpha
      hdec0 hdec1 hCU hD hDU hDU2 hb0 hbmin hsup hB hkd0 hmatch0
  exact ⟨Hs, kappas, deltaStep, hdelta, hlinear, hinc, hrec, ⟨model⟩, hsum⟩

/-- The canonical configured sequence may be started beyond an arbitrary
lower separation threshold by discarding a finite prefix. -/
theorem exists_configuredModelSequence_above
    {f theta x g gp yp : ℝ → ℝ} {M Delta beta0 Cq Ht : ℝ} {Pfun Pp : ℝ → ℝ}
    {alpha beta a au C CU CK DU DU2 D Km Kd B theta0 kstar kd eps0 b : ℝ}
    (Hmin : ℝ)
    (c : ConsecutiveData f theta x g gp yp M Delta beta0 Cq Ht Pfun Pp)
    (d : CanonicalTranslatorLocalPhase.InteriorPhaseData f theta x g gp)
    {At Mt D1 m Am : ℝ}
    (hf : ContDiffOn ℝ ∞ f (Set.Ioo 0 Real.pi))
    (hfpos : ∀ t ∈ Set.Ioo (0:ℝ) Real.pi, 0 < f t)
    (hMt : 0 < Mt) (hD1 : 0 ≤ D1)
    (hdecayK : ∀ u, HairpinRelative.curvField f (theta u) ≤
      At * Real.exp (-|u| / Mt))
    (hrelK : ∀ u, |deriv (fun r => HairpinRelative.curvField f (theta r)) u| ≤
      D1 * HairpinRelative.curvField f (theta u))
    (hm : 0 < m) (hmA : m ≤ Am)
    (hl : ∀ t, m ≤ f (theta t)) (hu : ∀ t, f (theta t) ≤ Am)
    (profile : ProfileConstants (alpha := alpha) (beta := beta) (a := a)
      (au := au) (CU := CU) (CK := CK) (DU := DU) (DU2 := DU2) (D := D)
      (Km := Km) (Kd := Kd) (kstar := kstar) (kd := kd))
    (heps : 0 < eps0) (halpha : 0 < alpha)
    (hdec0 : ∀ s, |ConsecutiveData.currentPulse f theta x s| ≤
      C * Real.exp (-alpha * |s|))
    (hdec1 : ∀ s, |yp s| ≤ C * Real.exp (-alpha * |s|))
    (hCU : C * Real.exp (alpha * |ConsecutiveData.phase f theta g|) ≤ CU)
    (hD : c.quantitative.relativeConst 1 ≤ D)
    (hDU : c.quantitative.relativeConst 1 ≤ DU)
    (hDU2 : c.quantitative.relativeConst 2 ≤ DU2)
    (hb0 : 0 ≤ b) (hbmin : b < min a au)
    (hsup : ∀ s, ConsecutiveData.currentPulse f theta x s ≤ b)
    (hB : (1 + b) / 2 * Real.pi ≤ B)
    (hkd0 : 0 ≤ kd)
    (hmatch0 : 0 ≤ matchConst a C CK CU DU Km Kd au alpha beta B) :
    ∃ (Hs : ℕ → ℝ) (kappas : ℕ → ℝ → ℝ) (deltaStep : ℝ),
      0 < deltaStep ∧ Hmin ≤ Hs 0 ∧
      (∀ n : ℕ, Hs 0 + n * deltaStep ≤ Hs n) ∧
      (∀ n, Hs n + deltaStep ≤ Hs (n + 1)) ∧
      (∀ n, Hs n < Hs (n + 1)) ∧
      (∀ n, rearPeriod (ConsecutiveData.currentPulse f theta x) (Hs (n + 1)) = Hs n) ∧
      Nonempty (UnconditionalAssembly.ConfiguredModelSequence
        kappas Hs (fun _ => eps0)) ∧
      Summable (fun n : ℕ =>
        CurvatureStabilityL1.l1Modulus (2 * kd)
          (matchConst a C CK CU DU Km Kd au alpha beta B *
            Real.exp (-(beta * Hs (n + 1)))) (Hs n) *
          (1 : ℝ) ^ 2 * (1 + kstar * (1 : ℝ))) := by
  obtain ⟨Hs, kappas, deltaStep, hdelta, hlinear, hstep, hinc, hrec,
    model, -, -, -, -, hsum⟩ :=
    exists_configuredModelSequence_with_step (theta0 := theta0)
      c d hf hfpos hMt hD1 hdecayK hrelK hm hmA hl hu profile heps halpha
      hdec0 hdec1 hCU hD hDU hDU2 hb0 hbmin hsup hB hkd0 hmatch0
  have hmono : Monotone Hs :=
    monotone_nat_of_le_succ fun n => by linarith [hstep n]
  obtain ⟨N : ℕ, hN⟩ := exists_nat_ge ((Hmin - Hs 0) / deltaStep)
  have hminN : Hmin ≤ Hs N := by
    have hmul := mul_le_mul_of_nonneg_right hN hdelta.le
    rw [div_mul_cancel₀ _ hdelta.ne'] at hmul
    have hgrow := hlinear N
    linarith
  let Hs' : ℕ → ℝ := fun n => Hs (N + n)
  let kappas' : ℕ → ℝ → ℝ := fun n => kappas (N + n)
  have hstep' : ∀ n, Hs' n + deltaStep ≤ Hs' (n + 1) := by
    intro n
    simpa [Hs', Nat.add_assoc] using hstep (N + n)
  have hlinear' : ∀ n : ℕ, Hs' 0 + n * deltaStep ≤ Hs' n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        have hs := hstep' n
        push_cast
        push_cast at ih
        nlinarith
  have hinc' : ∀ n, Hs' n < Hs' (n + 1) := by
    intro n
    simpa [Hs', Nat.add_assoc] using hinc (N + n)
  have hrec' : ∀ n, rearPeriod (ConsecutiveData.currentPulse f theta x)
      (Hs' (n + 1)) = Hs' n := by
    intro n
    simpa [Hs', Nat.add_assoc] using hrec (N + n)
  have hmodel' : Nonempty (UnconditionalAssembly.ConfiguredModelSequence
      kappas' Hs' (fun _ => eps0)) := by
    refine ⟨?_⟩
    simpa [kappas', Hs'] using shiftConfiguredModelSequence model N hmono
  have hsum' : Summable (fun n : ℕ =>
      CurvatureStabilityL1.l1Modulus (2 * kd)
        (matchConst a C CK CU DU Km Kd au alpha beta B *
          Real.exp (-(beta * Hs' (n + 1)))) (Hs' n) *
        (1 : ℝ) ^ 2 * (1 + kstar * (1 : ℝ))) := by
    simpa [Hs', Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      (summable_nat_add_iff (f := fun n : ℕ =>
        CurvatureStabilityL1.l1Modulus (2 * kd)
          (matchConst a C CK CU DU Km Kd au alpha beta B *
            Real.exp (-(beta * Hs (n + 1)))) (Hs n) *
          (1 : ℝ) ^ 2 * (1 + kstar * (1 : ℝ))) N).mpr hsum
  exact ⟨Hs', kappas', deltaStep, hdelta, by simpa [Hs'] using hminN,
    hlinear', hstep', hinc', hrec', hmodel', hsum'⟩

end CanonicalConfiguredModelCapstone

end UnitTangentIterates
