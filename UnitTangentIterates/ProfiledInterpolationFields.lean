import Mathlib
import UnitTangentIterates.InterpolationFrenetProfiled
import UnitTangentIterates.InterpolationGaugeSmoothSpecialized
import UnitTangentIterates.InterpolationSecondOrder

/-! # Canonical qualitative fields of the profiled interpolation -/

noncomputable section

open Function

namespace ProfiledInterpolationFields

open CurvatureInterpolation InterpolationNormal InterpolationEstimate
  InterpolationSecondOrder InterpolationGauge PathMetricCircle

/-- The profile reaches the closed unit interval, so the gauge cutoff is one
on its range.  `PathMetricCircle` exports the two one-sided bounds. -/
theorem B_mem_Icc (t : ℝ) : B t ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨B_nonneg t, B_le_one t⟩

def Y (k0 k1 : ℝ → ℝ) (theta0 L : ℝ) (t s : ℝ) : ℂ :=
  interpCurve (kappaInterp k0 k1 (B t)) theta0 L s

def alpha (k0 k1 : ℝ → ℝ) (theta0 : ℝ) (t s : ℝ) : ℝ :=
  tangentAngle (kappaInterp k0 k1 (B t)) theta0 s

def kappa (k0 k1 : ℝ → ℝ) (t s : ℝ) : ℝ :=
  kappaInterp k0 k1 (B t) s

def en (k0 k1 : ℝ → ℝ) (theta0 L : ℝ) (t s : ℝ) : ℝ :=
  w t * normalVel k0 k1 theta0 L (B t) s

def enS (k0 k1 : ℝ → ℝ) (theta0 L : ℝ) (t s : ℝ) : ℝ :=
  w t * normalVelDeriv k0 k1 theta0 L (B t) s

def enSS (k0 k1 k0' k1' : ℝ → ℝ) (theta0 L : ℝ) (t s : ℝ) : ℝ :=
  w t * normalVelSecondDeriv k0 k1 k0' k1' theta0 L (B t) s

/-- The field whose flow cancels the tangential part of the profiled motion. -/
def h (k0 k1 : ℝ → ℝ) (theta0 L : ℝ) (t s : ℝ) : ℝ :=
  w t * gaugeField k0 k1 theta0 L (B t) s

def hx (k0 k1 : ℝ → ℝ) (theta0 L : ℝ) (t s : ℝ) : ℝ :=
  w t * (-(timeCut (B t) *
    (kappaInterp k0 k1 (B t) s * normalVel k0 k1 theta0 L (B t) s)))

def hxx (k0 k1 k0' k1' : ℝ → ℝ) (theta0 L : ℝ) (t s : ℝ) : ℝ :=
  w t * gaugeFieldStateSecond k0 k1 k0' k1' theta0 L (B t) s

def PhiB (Phi : ℝ → ℝ → ℝ) (t u : ℝ) : ℝ := Phi (B t) u

def alphaT (k0 k1 : ℝ → ℝ) (t s : ℝ) : ℝ :=
  w t * angleShift k0 k1 s

def kT (k0 k1 : ℝ → ℝ) (t s : ℝ) : ℝ :=
  w t * (k1 s - k0 s)

def kX (k0' k1' : ℝ → ℝ) (t s : ℝ) : ℝ :=
  (1 - B t) * k0' s + B t * k1' s

/-- The qualitative, sign-sensitive block consumed by the non-fundamental
normal-rate construction.  Quantitative ceilings are deliberately absent. -/
structure Certificate
    (k0 k1 k0' k1' : ℝ → ℝ) (theta0 L : ℝ)
    (Phi : ℝ → ℝ → ℝ) : Prop where
  Y_C1 : ContDiff ℝ 1 (uncurry (Y k0 k1 theta0 L))
  tangent : ∀ t s, HasDerivAt (Y k0 k1 theta0 L t)
    (Complex.exp (Complex.I * (alpha k0 k1 theta0 t s : ℂ))) s
  motion : ∀ t s, HasDerivAt (fun r => Y k0 k1 theta0 L r s)
    (((-h k0 k1 theta0 L t s : ℝ) : ℂ) *
        Complex.exp (Complex.I * (alpha k0 k1 theta0 t s : ℂ)) +
      (en k0 k1 theta0 L t s : ℂ) *
        (Complex.I * Complex.exp
          (Complex.I * (alpha k0 k1 theta0 t s : ℂ)))) t
  angle_space : ∀ t s, HasDerivAt (alpha k0 k1 theta0 t)
    (kappa k0 k1 t s) s
  field_flow : ∀ u t, HasDerivAt (fun r => PhiB Phi r u)
    (h k0 k1 theta0 L t (PhiB Phi t u)) t
  field_space : ∀ t s, HasDerivAt (h k0 k1 theta0 L t)
    (hx k0 k1 theta0 L t s) s
  field_space2 : ∀ t s, HasDerivAt (hx k0 k1 theta0 L t)
    (hxx k0 k1 k0' k1' theta0 L t s) s
  field_cont : Continuous (uncurry (h k0 k1 theta0 L))
  field1_cont : Continuous (uncurry (hx k0 k1 theta0 L))
  field2_cont : Continuous (uncurry (hxx k0 k1 k0' k1' theta0 L))
  angle_C1 : ContDiff ℝ 1 (uncurry (alpha k0 k1 theta0))
  kappa_C1 : ContDiff ℝ 1 (uncurry (kappa k0 k1))
  angle_time : ∀ t s, HasDerivAt (fun r => alpha k0 k1 theta0 r s)
    (alphaT k0 k1 t s) t
  kappa_time : ∀ t s, HasDerivAt (fun r => kappa k0 k1 r s)
    (kT k0 k1 t s) t
  kappa_space : ∀ t s, HasDerivAt (kappa k0 k1 t) (kX k0' k1' t s) s
  alphaT_space : ∀ t s, HasDerivAt (alphaT k0 k1 t) (kT k0 k1 t s) s
  alphaT_cont : Continuous (uncurry (alphaT k0 k1))
  kT_cont : Continuous (uncurry (kT k0 k1))
  kX_cont : Continuous (uncurry (kX k0' k1'))
  mixed : ∀ t s, ∃ W : ℂ,
    HasDerivAt
      (fun r => Complex.exp (Complex.I * (alpha k0 k1 theta0 r s : ℂ))) W t ∧
    HasDerivAt
      (fun x => (w t : ℂ) * interpVelocity k0 k1 theta0 L (B t) x) W s
  en_cont : Continuous (uncurry (en k0 k1 theta0 L))
  en_space : ∀ t s, HasDerivAt (en k0 k1 theta0 L t)
    (enS k0 k1 theta0 L t s) s
  en_space2 : ∀ t s, HasDerivAt (enS k0 k1 theta0 L t)
    (enSS k0 k1 k0' k1' theta0 L t s) s
  kappa_periodic : ∀ t, Periodic (kappa k0 k1 t) (2 * L)
  angle_closing : ∀ t s,
    alpha k0 k1 theta0 t (s + 2 * L) =
      alpha k0 k1 theta0 t s + 2 * Real.pi
  phi_initial : ∀ u, PhiB Phi 0 u = 2 * L * u
  phi_translation : ∀ t u, PhiB Phi t (u + 1) = PhiB Phi t u + 2 * L

theorem en_space_deriv
    {k0 k1 : ℝ → ℝ} {theta0 L t s : ℝ}
    (hk0 : Continuous k0) (hk1 : Continuous k1) :
    HasDerivAt (en k0 k1 theta0 L t) (enS k0 k1 theta0 L t s) s := by
  simpa [en, enS] using
    (InterpolationEstimate.hasDerivAt_normalVel
      (θ₀ := theta0) (L := L) hk0 hk1 (B t) s).const_mul (w t)

theorem enS_space_deriv
    {k0 k1 k0' k1' : ℝ → ℝ} {theta0 L t s : ℝ}
    (hk0 : Continuous k0) (hk1 : Continuous k1)
    (hd0 : ∀ x, HasDerivAt k0 (k0' x) x)
    (hd1 : ∀ x, HasDerivAt k1 (k1' x) x) :
    HasDerivAt (enS k0 k1 theta0 L t)
      (enSS k0 k1 k0' k1' theta0 L t s) s := by
  simpa [enS, enSS] using
    (InterpolationSecondOrder.hasDerivAt_normalVelDeriv
      (θ₀ := theta0) (L := L) hk0 hk1 hd0 hd1 (B t) s).const_mul (w t)

/-- On the profiled interval the first field derivative is exactly
`-kappa * en`; no cutoff-envelope loss occurs. -/
theorem hx_eq_neg_kappa_mul_en
    {k0 k1 : ℝ → ℝ} {theta0 L t s : ℝ} :
    hx k0 k1 theta0 L t s =
      -(kappa k0 k1 t s * en k0 k1 theta0 L t s) := by
  have hcut : timeCut (B t) = 1 := timeCut_eq_one (B_mem_Icc t)
  simp only [hx, kappa, en, hcut, one_mul]
  ring

/-- The second field derivative is the differentiated sharp identity. -/
theorem hxx_eq_neg_kX_mul_en_add_kappa_mul_enS
    {k0 k1 k0' k1' : ℝ → ℝ} {theta0 L t s : ℝ} :
    hxx k0 k1 k0' k1' theta0 L t s =
      -(kX k0' k1' t s * en k0 k1 theta0 L t s +
        kappa k0 k1 t s * enS k0 k1 theta0 L t s) := by
  have hcut : timeCut (B t) = 1 := timeCut_eq_one (B_mem_Icc t)
  simp only [hxx, InterpolationGauge.gaugeFieldStateSecond, kX, en, kappa, enS,
    hcut, one_mul]
  ring

theorem abs_hx_le
    {k0 k1 : ℝ → ℝ} {theta0 L kstar m t s : ℝ}
    (hk : |kappa k0 k1 t s| ≤ kstar)
    (hen : |en k0 k1 theta0 L t s| ≤ m)
    (hk0 : 0 ≤ kstar) (hm0 : 0 ≤ m) :
    |hx k0 k1 theta0 L t s| ≤ kstar * m := by
  rw [hx_eq_neg_kappa_mul_en, abs_neg, abs_mul]
  exact mul_le_mul hk hen (abs_nonneg _) hk0

theorem abs_hxx_le
    {k0 k1 k0' k1' : ℝ → ℝ} {theta0 L kstar Kx m m1 t s : ℝ}
    (hkX : |kX k0' k1' t s| ≤ Kx)
    (hk : |kappa k0 k1 t s| ≤ kstar)
    (hen : |en k0 k1 theta0 L t s| ≤ m)
    (henS : |enS k0 k1 theta0 L t s| ≤ m1)
    (hKx0 : 0 ≤ Kx) (hk0 : 0 ≤ kstar) :
    |hxx k0 k1 k0' k1' theta0 L t s| ≤ Kx * m + kstar * m1 := by
  rw [hxx_eq_neg_kX_mul_en_add_kappa_mul_enS, abs_neg]
  calc
    |_ * en k0 k1 theta0 L t s +
        kappa k0 k1 t s * enS k0 k1 theta0 L t s|
        ≤ |kX k0' k1' t s| * |en k0 k1 theta0 L t s| +
          |kappa k0 k1 t s| * |enS k0 k1 theta0 L t s| := by
      simpa [abs_mul] using abs_add_le
        (kX k0' k1' t s * en k0 k1 theta0 L t s)
        (kappa k0 k1 t s * enS k0 k1 theta0 L t s)
    _ ≤ Kx * m + kstar * m1 :=
      add_le_add (mul_le_mul hkX hen (abs_nonneg _) hKx0)
        (mul_le_mul hk henS (abs_nonneg _) hk0)

/-- The profiled raw velocity is exactly the tangential/normal frame
expression used by `GaugeMarkedDataOfNormalRate`. -/
theorem profiled_frame_decomp
    {k0 k1 : ℝ → ℝ} {theta0 L t s : ℝ} :
    (w t : ℂ) * interpVelocity k0 k1 theta0 L (B t) s =
      ((-h k0 k1 theta0 L t s : ℝ) : ℂ) *
          Complex.exp (Complex.I * (alpha k0 k1 theta0 t s : ℂ)) +
        (en k0 k1 theta0 L t s : ℂ) *
          (Complex.I * Complex.exp
            (Complex.I * (alpha k0 k1 theta0 t s : ℂ))) := by
  have hcut : timeCut (B t) = 1 := timeCut_eq_one (B_mem_Icc t)
  rw [show Complex.exp (Complex.I * (alpha k0 k1 theta0 t s : ℂ)) =
      tau (alpha k0 k1 theta0 t s) by simp [tau, mul_comm]]
  rw [frame_decomp (interpVelocity k0 k1 theta0 L (B t) s)
    (alpha k0 k1 theta0 t s)]
  simp only [h, en, alpha, gaugeField, hcut, one_mul, normalVel, tangentVel]
  push_cast
  ring

/-- Convert the mixed witness retained by `Certificate` to the exact expanded
frame expression required by the non-fundamental normal-rate constructor. -/
theorem Certificate.mixed_expanded
    {k0 k1 k0' k1' : ℝ → ℝ} {theta0 L : ℝ}
    {Phi : ℝ → ℝ → ℝ}
    (C : Certificate k0 k1 k0' k1' theta0 L Phi) (t s : ℝ) :
    ∃ W : ℂ,
      HasDerivAt
        (fun r => Complex.exp
          (Complex.I * (alpha k0 k1 theta0 r s : ℂ))) W t ∧
      HasDerivAt
        (fun x =>
          ((-h k0 k1 theta0 L t x : ℝ) : ℂ) *
              Complex.exp (Complex.I * (alpha k0 k1 theta0 t x : ℂ)) +
            (en k0 k1 theta0 L t x : ℂ) *
              (Complex.I * Complex.exp
                (Complex.I * (alpha k0 k1 theta0 t x : ℂ)))) W s := by
  obtain ⟨W, htime, hspace⟩ := C.mixed t s
  refine ⟨W, htime, ?_⟩
  exact hspace.congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun x => profiled_frame_decomp.symm)

/-- Canonical qualitative certificate for the stopped curvature interpolation. -/
theorem exists_certificate
    {k0 k1 k0' k1' : ℝ → ℝ} {theta0 L : ℝ}
    {Phi : ℝ → ℝ → ℝ}
    (hk0 : ContDiff ℝ 2 k0) (hk1 : ContDiff ℝ 2 k1)
    (hk0'c : Continuous k0') (hk1'c : Continuous k1')
    (hd0 : ∀ x, HasDerivAt k0 (k0' x) x)
    (hd1 : ∀ x, HasDerivAt k1 (k1' x) x)
    (hper0 : Periodic k0 L) (hper1 : Periodic k1 L)
    (htot0 : (∫ x in (0 : ℝ)..L, k0 x) = Real.pi)
    (htot1 : (∫ x in (0 : ℝ)..L, k1 x) = Real.pi)
    (hPhid : ∀ u a, HasDerivAt (fun r => Phi r u)
      (gaugeField k0 k1 theta0 L a (Phi a u)) a)
    (hPhi0 : ∀ u, Phi 0 u = 2 * L * u)
    (htrans : ∀ a u, Phi a (u + 1) = Phi a u + 2 * L) :
    Certificate k0 k1 k0' k1' theta0 L Phi := by
  have hk0one : ContDiff ℝ 1 k0 := hk0.of_le (by norm_num)
  have hk1one : ContDiff ℝ 1 k1 := hk1.of_le (by norm_num)
  have hk0c := hk0.continuous
  have hk1c := hk1.continuous
  have hB1 : ContDiff ℝ 1 B := by
    refine contDiff_one_iff_deriv.2 ⟨fun t => (hasDerivAt_B t).differentiableAt, ?_⟩
    have heq : deriv B = w := funext fun t => (hasDerivAt_B t).deriv
    rw [heq]
    exact continuous_w
  have hpair : ContDiff ℝ 1 (fun p : ℝ × ℝ => (B p.1, p.2)) :=
    (hB1.comp contDiff_fst).prodMk contDiff_snd
  have hrawC2 : ContDiff ℝ 2
      (uncurry fun a s => interpCurve (kappaInterp k0 k1 a) theta0 L s) := by
    simpa using InterpolationSmooth.contDiff_succ_uncurry_interpCurve
      (n := 1) (theta0 := theta0) (L := L) hk0 hk1
  have hrawMixed : ∀ a s, ∃ W : ℂ,
      HasDerivAt
        (fun r => Complex.exp
          (Complex.I * (tangentAngle (kappaInterp k0 k1 r) theta0 s : ℂ))) W a ∧
      HasDerivAt (interpVelocity k0 k1 theta0 L a) W s :=
    fun a s => InterpolationFrenetEvolution.exists_mixed_interpCurve hk0c hk1c hrawC2 a s
  obtain ⟨hangT, hkT', halphaTS, hangTc, hkTc, hkXc, hmixed⟩ :=
    InterpolationFrenetProfiled.frame_time_block_comp
      (kX := fun t s => (1 - t) * k0' s + t * k1' s)
      hasDerivAt_B continuous_B continuous_w
      (InterpolationFrenetEvolution.hasDerivAt_tangentAngle_time hk0c hk1c)
      (fun a s => InterpolationFrenetEvolution.hasDerivAt_kappaInterp_time a s)
      (fun _ s => InterpolationFrenetEvolution.hasDerivAt_angleShift hk0c hk1c s)
      ((continuous_angleShift hk0c hk1c).comp continuous_snd)
      ((hk1c.comp continuous_snd).sub (hk0c.comp continuous_snd))
      (by
        show Continuous (fun p : ℝ × ℝ => (1 - p.1) * k0' p.2 + p.1 * k1' p.2)
        exact ((continuous_const.sub continuous_fst).mul
            (hk0'c.comp continuous_snd)).add
          (continuous_fst.mul (hk1'c.comp continuous_snd))) hrawMixed
  have hYC1 : ContDiff ℝ 1 (uncurry (Y k0 k1 theta0 L)) := by
    have h := (contDiff_one_interpCurve (θ₀ := theta0) (L := L) hk0c hk1c).comp hpair
    convert h using 1
  refine
    { Y_C1 := hYC1
      tangent := by
        intro t s
        simpa only [Y, alpha, Complex.ofReal_one, one_mul] using
          hasDerivAt_interpCurve_space (θ₀ := theta0) (L := L) hk0c hk1c (B t) s
      motion := by
        intro t s
        have hr := (hasDerivAt_interpCurve_param (θ₀ := theta0) (L := L)
          hk0c hk1c s (B t)).scomp t (hasDerivAt_B t)
        have hr2 : HasDerivAt (fun r => Y k0 k1 theta0 L r s)
            (w t • interpVelocity k0 k1 theta0 L (B t) s) t := hr
        rw [Complex.real_smul, profiled_frame_decomp] at hr2
        exact hr2
      angle_space := by
        intro t s
        simpa [alpha, kappa] using
          hasDerivAt_tangentAngle (continuous_kappaInterp hk0c hk1c) s
      field_flow := by
        intro u t
        simpa [PhiB, h, smul_eq_mul] using (hPhid u (B t)).scomp t (hasDerivAt_B t)
      field_space := by
        intro t s
        simpa [h, hx] using
          (hasDerivAt_gaugeField (θ₀ := theta0) (L := L) hk0c hk1c (B t) s).const_mul (w t)
      field_space2 := by
        intro t s
        exact (hasDerivAt_gaugeField_stateDeriv (theta0 := theta0) (L := L)
          hk0c hk1c hd0 hd1 (B t) s).const_mul (w t)
      field_cont := by
        show Continuous fun p : ℝ × ℝ =>
          w p.1 * gaugeField k0 k1 theta0 L (B p.1) p.2
        have hBp : Continuous fun p : ℝ × ℝ => (B p.1, p.2) :=
          (continuous_B.comp continuous_fst).prodMk continuous_snd
        have htv : Continuous fun p : ℝ × ℝ =>
            tangentVel k0 k1 theta0 L (B p.1) p.2 := by
          have h := (continuous_uncurry_tangentVel (θ₀ := theta0) (L := L)
            hk0c hk1c).comp hBp
          convert h using 1
        have hcut : Continuous fun p : ℝ × ℝ => timeCut (B p.1) :=
          continuous_timeCut.comp' (continuous_B.comp' continuous_fst)
        simp only [gaugeField]
        exact (continuous_w.comp continuous_fst).mul (hcut.mul htv).neg
      field1_cont := by
        show Continuous fun p : ℝ × ℝ =>
          w p.1 * (-(timeCut (B p.1) *
            (kappaInterp k0 k1 (B p.1) p.2 * normalVel k0 k1 theta0 L (B p.1) p.2)))
        have hBp : Continuous fun p : ℝ × ℝ => (B p.1, p.2) :=
          (continuous_B.comp continuous_fst).prodMk continuous_snd
        have hnv : Continuous fun p : ℝ × ℝ =>
            normalVel k0 k1 theta0 L (B p.1) p.2 := by
          have h := (continuous_uncurry_normalVel (θ₀ := theta0) (L := L)
            hk0c hk1c).comp hBp
          convert h using 1
        have hka : Continuous fun p : ℝ × ℝ => kappaInterp k0 k1 (B p.1) p.2 := by
          have h := (continuous_uncurry_kappaInterp hk0c hk1c).comp hBp
          convert h using 1
        have hcut : Continuous fun p : ℝ × ℝ => timeCut (B p.1) :=
          continuous_timeCut.comp' (continuous_B.comp' continuous_fst)
        exact (continuous_w.comp continuous_fst).mul (hcut.mul (hka.mul hnv)).neg
      field2_cont := by
        exact (continuous_w.comp continuous_fst).mul
          ((continuous_uncurry_gaugeFieldStateSecond hk0c hk1c hk0'c hk1'c).comp
            ((continuous_B.comp continuous_fst).prodMk continuous_snd))
      angle_C1 := by
        exact (InterpolationSmooth.contDiff_succ_uncurry_tangentAngle
          (n := 0) (theta0 := theta0) hk0one hk1one).comp hpair
      kappa_C1 := by
        exact (InterpolationSmooth.contDiff_succ_uncurry_kappaInterp
          (n := 0) hk0one hk1one).comp hpair
      angle_time := by simpa [alpha, alphaT] using hangT
      kappa_time := by simpa [kappa, kT] using hkT'
      kappa_space := by
        intro t s
        simpa [kappa, kX] using
          InterpolationSecondOrder.hasDerivAt_kappaInterp hd0 hd1 (B t) s
      alphaT_space := by simpa [alphaT, kT] using halphaTS
      alphaT_cont := by simpa [alphaT] using hangTc
      kT_cont := by simpa [kT] using hkTc
      kX_cont := by simpa [kX] using hkXc
      mixed := by simpa [alpha] using hmixed
      en_cont := by
        show Continuous fun p : ℝ × ℝ =>
          w p.1 * normalVel k0 k1 theta0 L (B p.1) p.2
        have hBp : Continuous fun p : ℝ × ℝ => (B p.1, p.2) :=
          (continuous_B.comp continuous_fst).prodMk continuous_snd
        have hnv : Continuous fun p : ℝ × ℝ =>
            normalVel k0 k1 theta0 L (B p.1) p.2 := by
          have h := (continuous_uncurry_normalVel (θ₀ := theta0) (L := L)
            hk0c hk1c).comp hBp
          convert h using 1
        exact (continuous_w.comp continuous_fst).mul hnv
      en_space := fun t s => en_space_deriv hk0c hk1c
      en_space2 := fun t s => enS_space_deriv hk0c hk1c hd0 hd1
      kappa_periodic := fun t => by
        have h := periodic_kappaInterp (t := B t) hper0 hper1
        have h2 : Function.Periodic (kappaInterp k0 k1 (B t)) (2 * L) := by
          simpa [two_mul] using h.add_period h
        simpa [kappa] using h2
      angle_closing := by
        intro t s
        have hhalf := tangentAngle_add_halfPeriod (θ₀ := theta0)
          (continuous_kappaInterp hk0c hk1c)
          (periodic_kappaInterp (t := B t) hper0 hper1)
          (integral_kappaInterp (t := B t) hk0c hk1c htot0 htot1)
        rw [show s + 2 * L = (s + L) + L by ring]
        simp only [alpha]
        rw [hhalf (s + L), hhalf s]
        ring
      phi_initial := by
        intro u
        simpa [PhiB, B_zero] using hPhi0 u
      phi_translation := by
        intro t u
        simpa [PhiB] using htrans (B t) u }

end ProfiledInterpolationFields
