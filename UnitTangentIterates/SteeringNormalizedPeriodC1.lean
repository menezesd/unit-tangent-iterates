import Mathlib
import UnitTangentIterates.SelectedSteeringFamily
import UnitTangentIterates.SteeringNormalizedPeriod
import UnitTangentIterates.SteeringVariablePeriodSelectedInverseJointC1

/-!
# First-order dependence of normalized selected steering

The quadratic Taylor bounds in `SteeringNormalizedPeriod` are convenient for
quantitative estimates but unnecessary for qualitative `C¹` dependence.  This
file replaces them by uniform convergence of first difference quotients, the
property supplied by joint `C¹` regularity on the compact unit circle.
-/

noncomputable section

open Function Set Real

namespace SteeringNormalizedPeriodC1

open BoundedLinearBound PeriodicGreen RearOwnHigherRegularity SteeringNormalizedPeriod
  SteeringVariablePeriod

variable {K Kd delta : ℝ → ℝ → ℝ} {Pf Pd : ℝ → ℝ}
  {P0 P1 kap Md MP : ℝ}

/-- Pairwise continuity estimate for two normalized selected steering slices.
Only estimates for the pair in question are used. -/
theorem abs_delta_sub_le_pair
    (hP0 : 0 < P0) (hkap0 : 0 ≤ kap) (hkap1 : kap < 1)
    (hPl : ∀ a, P0 ≤ Pf a) (hPu : ∀ a, Pf a ≤ P1)
    (hKcont : Continuous (uncurry K))
    (hsol : ∀ a s, HasDerivAt (delta a) (Pf a * (K a s - Real.sin (delta a s))) s)
    (hstrip : ∀ a s, delta a s ∈ Icc (0 : ℝ) (arcsin kap))
    (hKbd : ∀ a s, |K a s| ≤ kap) {a b A B : ℝ}
    (hKpair : ∀ x, |K b x - K a x| ≤ A)
    (hPpair : |Pf b - Pf a| ≤ B) (s : ℝ) :
    |delta b s - delta a s| ≤ (P1 * A + 2 * B) / dissip P0 kap := by
  have hd := dissip_pos hP0 hkap0 hkap1
  have hKa : Continuous (K a) := hKcont.comp (continuous_const.prodMk continuous_id)
  have hKb : Continuous (K b) := hKcont.comp (continuous_const.prodMk continuous_id)
  have hPbpos : 0 < Pf b := lt_of_lt_of_le hP0 (hPl b)
  let f : ℝ → ℝ := fun x => Pf b * (K b x - K a x) +
    (Pf b - Pf a) * (K a x - Real.sin (delta a x))
  have hfcont : Continuous f :=
    (continuous_const.mul (hKb.sub hKa)).add
      (continuous_const.mul (hKa.sub
        (Real.continuous_sin.comp (continuous_delta_slice hsol a))))
  have hAnn : 0 ≤ A := le_trans (abs_nonneg _) (hKpair 0)
  have hBnn : 0 ≤ B := le_trans (abs_nonneg _) hPpair
  have hfbd : ∀ x, |f x| ≤ P1 * A + 2 * B := by
    intro x
    have h1 : |Pf b * (K b x - K a x)| ≤ P1 * A := by
      rw [abs_mul, abs_of_pos hPbpos]
      exact mul_le_mul (hPu b) (hKpair x) (abs_nonneg _)
        (le_trans hPbpos.le (hPu b))
    have hKx := hKbd a x
    have hs1 := Real.neg_one_le_sin (delta a x)
    have hs2 := Real.sin_le_one (delta a x)
    have hfield : |K a x - Real.sin (delta a x)| ≤ 2 := by
      rw [abs_le] at hKx ⊢
      constructor <;> linarith [hKx.1, hKx.2]
    have h2 : |(Pf b - Pf a) * (K a x - Real.sin (delta a x))| ≤ 2 * B := by
      rw [abs_mul]
      calc |Pf b - Pf a| * |K a x - Real.sin (delta a x)| ≤ B * 2 :=
            mul_le_mul hPpair hfield (abs_nonneg _) hBnn
        _ = 2 * B := by ring
    exact le_trans (abs_add_le _ _) (add_le_add h1 h2)
  have hode : ∀ x, HasDerivAt (fun y => delta b y - delta a y)
      (f x - (Pf b * avgCos delta b a x) * (delta b x - delta a x)) x := by
    intro x
    have h := (hsol b x).sub (hsol a x)
    refine h.congr_deriv ?_
    have hid := sin_sub_eq_avgCos_mul delta b a x
    simp only [f]
    nlinarith [hid]
  have hAcont : Continuous fun x => Pf b * avgCos delta b a x :=
    continuous_const.mul
      (continuous_avgCos_of_slices (fun r => continuous_delta_slice hsol r) b a)
  have hAge : ∀ x, dissip P0 kap ≤ Pf b * avgCos delta b a x := by
    intro x
    have h1 := avgCos_ge hstrip b a x
    have h2 : 0 ≤ Real.sqrt (1 - kap ^ 2) := Real.sqrt_nonneg _
    rw [dissip]
    exact mul_le_mul (hPl b) h1 h2 (le_trans hP0.le (hPl b))
  have hbounded : ∀ x, |delta b x - delta a x| ≤ 2 :=
    fun x => SteeringVariablePeriod.abs_delta_sub_le_two hstrip b a x
  exact abs_le_of_bounded_dissipative hd hAcont hfcont hAge hode hbounded hfbd s

/-- Identification of the parameter derivative from uniform convergence of
the first difference quotients.  This is the Taylor-free analytic core. -/
theorem hasDerivAt_param_of_uniform_difference_quotients
    (hP0 : 0 < P0) (hkap0 : 0 ≤ kap) (hkap1 : kap < 1)
    (hPl : ∀ a, P0 ≤ Pf a) (hPu : ∀ a, Pf a ≤ P1)
    (hKcont : Continuous (uncurry K)) (hKdcont : Continuous (uncurry Kd))
    (hsol : ∀ a s, HasDerivAt (delta a) (Pf a * (K a s - Real.sin (delta a s))) s)
    (hstrip : ∀ a s, delta a s ∈ Icc (0 : ℝ) (arcsin kap))
    (hper : ∀ a, Function.Periodic (delta a) 1)
    (hKper : ∀ a, Function.Periodic (K a) 1)
    (hKdper : ∀ a, Function.Periodic (Kd a) 1)
    (hKbd : ∀ a s, |K a s| ≤ kap)
    (hKdbd : ∀ a s, |Kd a s| ≤ Md) (hPdbd : ∀ a, |Pd a| ≤ MP)
    (hKconv : ∀ a ε, 0 < ε → ∃ ρ > 0, ∀ h, h ≠ 0 → |h| < ρ →
      ∀ x, |(K (a + h) x - K a x) / h - Kd a x| ≤ ε)
    (hPconv : ∀ a ε, 0 < ε → ∃ ρ > 0, ∀ h, h ≠ 0 → |h| < ρ →
      |(Pf (a + h) - Pf a) / h - Pd a| ≤ ε)
    (a s : ℝ) :
    HasDerivAt (fun b => delta b s) (variation K Kd delta Pf Pd a s) a := by
  have hd : 0 < dissip P0 kap := dissip_pos hP0 hkap0 hkap1
  have hMd : 0 ≤ Md := le_trans (abs_nonneg _) (hKdbd a 0)
  have hMP : 0 ≤ MP := le_trans (abs_nonneg _) (hPdbd a)
  have hP1 : 0 < P1 := lt_of_lt_of_le (lt_of_lt_of_le hP0 (hPl a)) (hPu a)
  let W : ℝ := varBound P0 P1 kap Md MP
  let L : ℝ := (P1 * (Md + 1) + 2 * (MP + 1)) / dissip P0 kap
  have hwbd : ∀ x, |variation K Kd delta Pf Pd a x| ≤ W := fun x =>
    abs_variation_le hP0 hkap0 hkap1 hPl hPu hKcont hKdcont hsol hstrip hper
      hKper hKdper hKbd hKdbd hPdbd a x
  have hW : 0 ≤ W := le_trans (abs_nonneg _) (hwbd 0)
  have hL : 0 ≤ L := by
    dsimp [L]
    positivity
  have hkey : ∀ ε > 0, ∃ ρ > 0, ∀ h, h ≠ 0 → |h| < ρ →
      ∀ x, |(delta (a + h) x - delta a x) / h -
        variation K Kd delta Pf Pd a x| ≤ ε := by
    intro ε hε
    let eps0 : ℝ := ε * dissip P0 kap / (4 * (P1 + 3))
    have heps0 : 0 < eps0 := by
      dsimp [eps0]
      positivity
    obtain ⟨rK, hrK, hKr⟩ := hKconv a eps0 heps0
    obtain ⟨rP, hrP, hPr⟩ := hPconv a eps0 heps0
    obtain ⟨rK1, hrK1, hKr1⟩ := hKconv a 1 one_pos
    obtain ⟨rP1, hrP1, hPr1⟩ := hPconv a 1 one_pos
    let C : ℝ := Md * (MP + 1) + W * (P1 * L + MP + 1)
    have hC : 0 ≤ C := by
      dsimp [C]
      positivity
    let rC : ℝ := ε * dissip P0 kap / (2 * (C + 1))
    have hrC : 0 < rC := by
      dsimp [rC]
      positivity
    refine ⟨min rK (min rP (min rK1 (min rP1 rC))),
      lt_min hrK (lt_min hrP (lt_min hrK1 (lt_min hrP1 hrC))), ?_⟩
    intro h hh hsmall x
    have hsK : |h| < rK := lt_of_lt_of_le hsmall (min_le_left _ _)
    have hsP : |h| < rP := lt_of_lt_of_le hsmall
      (le_trans (min_le_right _ _) (min_le_left _ _))
    have hsK1 : |h| < rK1 := lt_of_lt_of_le hsmall
      (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _)))
    have hsP1 : |h| < rP1 := lt_of_lt_of_le hsmall
      (le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
        (le_trans (min_le_right _ _) (min_le_left _ _))))
    have hsC : |h| < rC := lt_of_lt_of_le hsmall
      (le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
        (le_trans (min_le_right _ _) (min_le_right _ _))))
    let b : ℝ := a + h
    have hbsub : b - a = h := by dsimp [b]; ring
    have hKq : ∀ y, |(K b y - K a y) / h - Kd a y| ≤ eps0 := by
      intro y
      exact hKr h hh hsK y
    have hPq : |(Pf b - Pf a) / h - Pd a| ≤ eps0 := hPr h hh hsP
    have hKq1 : ∀ y, |(K b y - K a y) / h| ≤ Md + 1 := by
      intro y
      calc |(K b y - K a y) / h|
          = |((K b y - K a y) / h - Kd a y) + Kd a y| := by congr 1 <;> ring
        _ ≤ |(K b y - K a y) / h - Kd a y| + |Kd a y| := abs_add_le _ _
        _ ≤ 1 + Md := add_le_add (hKr1 h hh hsK1 y) (hKdbd a y)
        _ = Md + 1 := by ring
    have hPq1 : |(Pf b - Pf a) / h| ≤ MP + 1 := by
      calc |(Pf b - Pf a) / h|
          = |((Pf b - Pf a) / h - Pd a) + Pd a| := by congr 1 <;> ring
        _ ≤ |(Pf b - Pf a) / h - Pd a| + |Pd a| := abs_add_le _ _
        _ ≤ 1 + MP := add_le_add (hPr1 h hh hsP1) (hPdbd a)
        _ = MP + 1 := by ring
    have hKpair : ∀ y, |K b y - K a y| ≤ (Md + 1) * |h| := by
      intro y
      have heq : K b y - K a y = ((K b y - K a y) / h) * h := by
        field_simp
      rw [heq, abs_mul]
      exact mul_le_mul_of_nonneg_right (hKq1 y) (abs_nonneg h)
    have hPpair : |Pf b - Pf a| ≤ (MP + 1) * |h| := by
      have heq : Pf b - Pf a = ((Pf b - Pf a) / h) * h := by
        field_simp
      rw [heq, abs_mul]
      exact mul_le_mul_of_nonneg_right hPq1 (abs_nonneg h)
    have hdeltabd : ∀ y, |delta b y - delta a y| ≤ L * |h| := by
      intro y
      have hbnd := abs_delta_sub_le_pair hP0 hkap0 hkap1 hPl hPu hKcont hsol
        hstrip hKbd hKpair hPpair y
      dsimp [L]
      calc |delta b y - delta a y|
          ≤ (P1 * ((Md + 1) * |h|) + 2 * ((MP + 1) * |h|)) /
              dissip P0 kap := hbnd
        _ = (P1 * (Md + 1) + 2 * (MP + 1)) / dissip P0 kap * |h| := by ring
    let w : ℝ → ℝ := variation K Kd delta Pf Pd a
    let z : ℝ → ℝ := fun y => (delta b y - delta a y) / h - w y
    let F : ℝ → ℝ := fun y =>
      Pf b * ((K b y - K a y) / h - Kd a y) +
      Kd a y * (Pf b - Pf a) +
      ((Pf b - Pf a) / h - Pd a) * (K a y - Real.sin (delta a y)) +
      w y * (Pf a * Real.cos (delta a y) - Pf b * avgCos delta b a y)
    have hwcont : Continuous w :=
      continuous_variation hP0 hkap0 hkap1 hPl hKcont hKdcont hsol hstrip hper
        hKper hKdper a
    have hKa : Continuous (K a) := hKcont.comp (continuous_const.prodMk continuous_id)
    have hKb : Continuous (K b) := hKcont.comp (continuous_const.prodMk continuous_id)
    have hKda : Continuous (Kd a) := hKdcont.comp (continuous_const.prodMk continuous_id)
    have hda : Continuous (delta a) := continuous_delta_slice hsol a
    have hdb : Continuous (delta b) := continuous_delta_slice hsol b
    have havg : Continuous (avgCos delta b a) :=
      continuous_avgCos_of_slices (fun r => continuous_delta_slice hsol r) b a
    have hFcont : Continuous F := by
      dsimp [F]
      have ht1 : Continuous fun y => Pf b * ((K b y - K a y) / h - Kd a y) :=
        continuous_const.mul (((hKb.sub hKa).div_const h).sub hKda)
      have ht2 : Continuous fun y => Kd a y * (Pf b - Pf a) :=
        hKda.mul continuous_const
      have ht3 : Continuous fun y => ((Pf b - Pf a) / h - Pd a) *
          (K a y - Real.sin (delta a y)) :=
        continuous_const.mul (hKa.sub (Real.continuous_sin.comp hda))
      have ht4 : Continuous fun y => w y *
          (Pf a * Real.cos (delta a y) - Pf b * avgCos delta b a y) :=
        hwcont.mul ((continuous_const.mul (Real.continuous_cos.comp hda)).sub
          (continuous_const.mul havg))
      exact ((ht1.add ht2).add ht3).add ht4
    have hzode : ∀ y, HasDerivAt z
        (F y - (Pf b * avgCos delta b a y) * z y) y := by
      intro y
      have hq := ((hsol b y).sub (hsol a y)).div_const h
      have hw := hasDerivAt_variation (Pd := Pd) hP0 hkap0 hkap1 hPl hKcont hKdcont hsol
        hstrip hper hKper hKdper a y
      have hz := hq.sub hw
      refine hz.congr_deriv ?_
      have hid := sin_sub_eq_avgCos_mul delta b a y
      simp only [z, F, w, coef, source]
      field_simp [hh]
      linear_combination (-Pf b) * hid
    have hzbd : ∀ y, |z y| ≤ 2 / |h| + W := by
      intro y
      have hdelta2 := SteeringVariablePeriod.abs_delta_sub_le_two hstrip b a y
      have hqabs : |(delta b y - delta a y) / h| ≤ 2 / |h| := by
        rw [abs_div]
        exact div_le_div_of_nonneg_right hdelta2 (abs_nonneg h)
      exact le_trans (abs_sub _ _) (add_le_add hqabs (hwbd y))
    have hFbd : ∀ y, |F y| ≤ ε * dissip P0 kap := by
      intro y
      have hPbpos : 0 < Pf b := lt_of_lt_of_le hP0 (hPl b)
      have h1 : |Pf b * ((K b y - K a y) / h - Kd a y)| ≤ P1 * eps0 := by
        rw [abs_mul, abs_of_pos hPbpos]
        exact mul_le_mul (hPu b) (hKq y) (abs_nonneg _)
          (le_trans hPbpos.le (hPu b))
      have h2 : |Kd a y * (Pf b - Pf a)| ≤ Md * (MP + 1) * |h| := by
        rw [abs_mul]
        calc |Kd a y| * |Pf b - Pf a| ≤ Md * ((MP + 1) * |h|) :=
              mul_le_mul (hKdbd a y) hPpair (abs_nonneg _) hMd
          _ = Md * (MP + 1) * |h| := by ring
      have hfield : |K a y - Real.sin (delta a y)| ≤ 2 := by
        have hk := hKbd a y
        have hs1 := Real.neg_one_le_sin (delta a y)
        have hs2 := Real.sin_le_one (delta a y)
        rw [abs_le] at hk ⊢
        constructor <;> linarith [hk.1, hk.2]
      have h3 : |((Pf b - Pf a) / h - Pd a) *
          (K a y - Real.sin (delta a y))| ≤ 2 * eps0 := by
        rw [abs_mul]
        calc |(Pf b - Pf a) / h - Pd a| * |K a y - Real.sin (delta a y)|
            ≤ eps0 * 2 := mul_le_mul hPq hfield (abs_nonneg _) heps0.le
          _ = 2 * eps0 := by ring
      have hcoef : |Pf a * Real.cos (delta a y) - Pf b * avgCos delta b a y|
          ≤ (P1 * L + MP + 1) * |h| := by
        have hsplit : Pf a * Real.cos (delta a y) - Pf b * avgCos delta b a y =
            Pf a * (Real.cos (delta a y) - avgCos delta b a y) +
              (Pf a - Pf b) * avgCos delta b a y := by ring
        have hc : |Real.cos (delta a y) - avgCos delta b a y| ≤ L * |h| := by
          calc |Real.cos (delta a y) - avgCos delta b a y|
              = |avgCos delta b a y - Real.cos (delta a y)| := abs_sub_comm _ _
            _ ≤ |delta b y - delta a y| := abs_avgCos_sub_cos_le delta b a y
            _ ≤ L * |h| := hdeltabd y
        have hpapos : 0 < Pf a := lt_of_lt_of_le hP0 (hPl a)
        have hc1 : |Pf a * (Real.cos (delta a y) - avgCos delta b a y)|
            ≤ P1 * (L * |h|) := by
          rw [abs_mul, abs_of_pos hpapos]
          exact mul_le_mul (hPu a) hc (abs_nonneg _) (le_trans hpapos.le (hPu a))
        have hc2 : |(Pf a - Pf b) * avgCos delta b a y| ≤ (MP + 1) * |h| := by
          rw [abs_mul]
          have havgb := abs_avgCos_le_one hstrip b a y
          have hp' : |Pf a - Pf b| ≤ (MP + 1) * |h| := by
            rw [abs_sub_comm]
            exact hPpair
          calc |Pf a - Pf b| * |avgCos delta b a y| ≤ ((MP + 1) * |h|) * 1 :=
                mul_le_mul hp' havgb (abs_nonneg _) (by positivity)
            _ = (MP + 1) * |h| := by ring
        rw [hsplit]
        calc |Pf a * (Real.cos (delta a y) - avgCos delta b a y) +
              (Pf a - Pf b) * avgCos delta b a y| ≤
              |Pf a * (Real.cos (delta a y) - avgCos delta b a y)| +
                |(Pf a - Pf b) * avgCos delta b a y| := abs_add_le _ _
          _ ≤ P1 * (L * |h|) + (MP + 1) * |h| := add_le_add hc1 hc2
          _ = (P1 * L + MP + 1) * |h| := by ring
      have h4 : |w y * (Pf a * Real.cos (delta a y) - Pf b * avgCos delta b a y)|
          ≤ W * (P1 * L + MP + 1) * |h| := by
        rw [abs_mul]
        calc |w y| * |Pf a * Real.cos (delta a y) - Pf b * avgCos delta b a y|
            ≤ W * ((P1 * L + MP + 1) * |h|) :=
              mul_le_mul (hwbd y) hcoef (abs_nonneg _) hW
          _ = W * (P1 * L + MP + 1) * |h| := by ring
      have hsum : |F y| ≤ (P1 + 2) * eps0 + C * |h| := by
        dsimp [F]
        calc |Pf b * ((K b y - K a y) / h - Kd a y) + Kd a y * (Pf b - Pf a) +
              ((Pf b - Pf a) / h - Pd a) * (K a y - Real.sin (delta a y)) +
              w y * (Pf a * Real.cos (delta a y) - Pf b * avgCos delta b a y)|
            ≤ |Pf b * ((K b y - K a y) / h - Kd a y)| +
                |Kd a y * (Pf b - Pf a)| +
                |((Pf b - Pf a) / h - Pd a) * (K a y - Real.sin (delta a y))| +
                |w y * (Pf a * Real.cos (delta a y) - Pf b * avgCos delta b a y)| := by
                  linarith [abs_add_le
                    (Pf b * ((K b y - K a y) / h - Kd a y) + Kd a y * (Pf b - Pf a) +
                      ((Pf b - Pf a) / h - Pd a) * (K a y - Real.sin (delta a y)))
                    (w y * (Pf a * Real.cos (delta a y) - Pf b * avgCos delta b a y)),
                    abs_add_le
                      (Pf b * ((K b y - K a y) / h - Kd a y) + Kd a y * (Pf b - Pf a))
                      (((Pf b - Pf a) / h - Pd a) * (K a y - Real.sin (delta a y))),
                    abs_add_le (Pf b * ((K b y - K a y) / h - Kd a y))
                      (Kd a y * (Pf b - Pf a))]
          _ ≤ P1 * eps0 + Md * (MP + 1) * |h| + 2 * eps0 +
              W * (P1 * L + MP + 1) * |h| := by linarith [h1, h2, h3, h4]
          _ = (P1 + 2) * eps0 + C * |h| := by dsimp [C]; ring
      have hepspart : (P1 + 2) * eps0 ≤ ε * dissip P0 kap / 4 := by
        calc (P1 + 2) * eps0 ≤ (P1 + 3) * eps0 :=
              mul_le_mul_of_nonneg_right (by linarith) heps0.le
          _ = ε * dissip P0 kap / 4 := by
            dsimp [eps0]
            field_simp
      have hCpart : C * |h| ≤ ε * dissip P0 kap / 2 := by
        have hlt : C * |h| ≤ C * rC :=
          mul_le_mul_of_nonneg_left hsC.le hC
        have hCr : C * rC ≤ ε * dissip P0 kap / 2 := by
          dsimp [rC]
          rw [mul_div_assoc']
          rw [div_le_iff₀ (by positivity : 0 < 2 * (C + 1))]
          nlinarith [mul_pos hε hd]
        exact hlt.trans hCr
      linarith [hsum, mul_pos hε hd]
    have hAge : ∀ y, dissip P0 kap ≤ Pf b * avgCos delta b a y := by
      intro y
      have h1 := avgCos_ge hstrip b a y
      have h2 : 0 ≤ Real.sqrt (1 - kap ^ 2) := Real.sqrt_nonneg _
      rw [dissip]
      exact mul_le_mul (hPl b) h1 h2 (le_trans hP0.le (hPl b))
    have hzcontCoef : Continuous fun y => Pf b * avgCos delta b a y :=
      continuous_const.mul havg
    have hzmax := abs_le_of_bounded_dissipative (u := z)
      (a := fun y => Pf b * avgCos delta b a y) (f := F)
      (c := dissip P0 kap) (M := ε * dissip P0 kap) (B := 2 / |h| + W)
      hd hzcontCoef hFcont hAge hzode hzbd hFbd x
    have hsimp : (ε * dissip P0 kap) / dissip P0 kap = ε := by
      field_simp
    rw [hsimp] at hzmax
    exact hzmax
  rw [hasDerivAt_iff_tendsto_slope_zero, Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  obtain ⟨ρ, hρ, hr⟩ := hkey (ε / 2) (by linarith)
  refine ⟨ρ, hρ, ?_⟩
  intro h hh hdist
  have habs : |h| < ρ := by simpa [Real.dist_eq] using hdist
  have hb := hr h hh habs s
  have heq : h⁻¹ • (delta (a + h) s - delta a s) =
      (delta (a + h) s - delta a s) / h := by
    rw [smul_eq_mul]
    ring
  rw [Real.dist_eq, heq]
  linarith

/-- A global bound on the canonical time derivative gives the corresponding
global Lipschitz estimate, slice by slice. -/
theorem abs_time_sub_le_of_partialTime_bound {f : ℝ → ℝ → ℝ} {M : ℝ}
    (hf : ContDiff ℝ 1 (uncurry f)) (hM : ∀ t x, |partialTime f t x| ≤ M)
    (a b x : ℝ) : |f a x - f b x| ≤ M * |a - b| := by
  have hfdiff : Differentiable ℝ (uncurry f) := hf.differentiable (by norm_num)
  let g : ℝ → ℝ := fun t => f t x
  have hg : ∀ t ∈ uIcc b a, HasDerivWithinAt g (partialTime f t x) (uIcc b a) t := by
    intro t _
    exact (hasDerivAt_partialTime hfdiff t x).hasDerivWithinAt
  have hgbd : ∀ t ∈ uIcc b a, ‖partialTime f t x‖ ≤ M := by
    intro t _
    simpa [Real.norm_eq_abs] using hM t x
  have hmvt := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hg hgbd
    (convex_uIcc b a) Set.left_mem_uIcc Set.right_mem_uIcc
  simpa [g, Real.norm_eq_abs] using hmvt

/-- Joint `C¹` data supply the exact selected variation without any Taylor
remainder hypothesis. -/
theorem hasDerivAt_param_of_contDiff_one
    (hP0 : 0 < P0) (hkap0 : 0 ≤ kap) (hkap1 : kap < 1)
    (hPl : ∀ a, P0 ≤ Pf a) (hPu : ∀ a, Pf a ≤ P1)
    (hK : ContDiff ℝ 1 (uncurry K)) (hP : ContDiff ℝ 1 Pf)
    (hsol : ∀ a s, HasDerivAt (delta a) (Pf a * (K a s - Real.sin (delta a s))) s)
    (hstrip : ∀ a s, delta a s ∈ Icc (0 : ℝ) (arcsin kap))
    (hper : ∀ a, Function.Periodic (delta a) 1)
    (hKper : ∀ a, Function.Periodic (K a) 1)
    (hKbd : ∀ a s, |K a s| ≤ kap)
    (hKtbd : ∀ a s, |partialTime K a s| ≤ Md)
    (hPtbd : ∀ a, |SteeringVariablePeriodSelectedInverseJointC1.periodTime Pf a| ≤ MP)
    (a s : ℝ) :
    HasDerivAt (fun b => delta b s)
      (variation K (partialTime K) delta Pf
        (SteeringVariablePeriodSelectedInverseJointC1.periodTime Pf) a s) a := by
  have hKtc : Continuous (uncurry (partialTime K)) :=
    (contDiff_partialTime_self (n := 0) hK).continuous
  have hKtper : ∀ t, Function.Periodic (partialTime K t) 1 :=
    SteeringVariablePeriodSelectedInverseJointC1.partialTime_periodic_of_periodic hK hKper
  have hKconv :=
    SteeringVariablePeriodSelectedInverseJointC1.uniform_time_difference_quotient hK hKper
  have hPconv :=
    SteeringVariablePeriodSelectedInverseJointC1.uniform_period_difference_quotient hP
  exact hasDerivAt_param_of_uniform_difference_quotients hP0 hkap0 hkap1 hPl hPu
    hK.continuous hKtc hsol hstrip hper hKper hKtper hKbd hKtbd hPtbd
    hKconv hPconv a s

/-- **Selected steering and rear-arclength inverse from joint `C¹` curvature
and period data.**  The exact steering variation is the periodic Green
solution of the normalized linearized equation; both the steering and the
produced inverse family are jointly `C¹`. -/
theorem exists_selected_inverse_of_contDiff_one
    (hP0 : 0 < P0) (hkap0 : 0 ≤ kap) (hkap1 : kap < 1)
    (hPl : ∀ a, P0 ≤ Pf a) (hPu : ∀ a, Pf a ≤ P1)
    (hK : ContDiff ℝ 1 (uncurry K)) (hP : ContDiff ℝ 1 Pf)
    (hsol : ∀ a s, HasDerivAt (delta a) (Pf a * (K a s - Real.sin (delta a s))) s)
    (hstrip : ∀ a s, delta a s ∈ Icc (0 : ℝ) (arcsin kap))
    (hper : ∀ a, Function.Periodic (delta a) 1)
    (hKper : ∀ a, Function.Periodic (K a) 1)
    (hKbd : ∀ a s, |K a s| ≤ kap)
    (hKtbd : ∀ a s, |partialTime K a s| ≤ Md)
    (hPtbd : ∀ a, |SteeringVariablePeriodSelectedInverseJointC1.periodTime Pf a| ≤ MP) :
    ContDiff ℝ 1 (uncurry delta) ∧
      ∃ sf : ℝ → ℝ → ℝ,
        (∀ t x, RearTrack.rearArclength (delta t) (sf t x) = x) ∧
        ContDiff ℝ 1 (uncurry sf) := by
  let Kt : ℝ → ℝ → ℝ := partialTime K
  let Pt : ℝ → ℝ := SteeringVariablePeriodSelectedInverseJointC1.periodTime Pf
  let dT : ℝ → ℝ → ℝ := variation K Kt delta Pf Pt
  have hKlip : ∀ a b s, |K a s - K b s| ≤ Md * |a - b| :=
    fun a b s => abs_time_sub_le_of_partialTime_bound hK hKtbd a b s
  have hPlip : ∀ a b, |Pf a - Pf b| ≤ MP * |a - b| := by
    intro a b
    have hPdiff : Differentiable ℝ Pf := hP.differentiable (by norm_num)
    let Q : ℝ → ℝ → ℝ := fun t _ => Pf t
    have hQ : ContDiff ℝ 1 (uncurry Q) := hP.comp contDiff_fst
    have hQt : ∀ t x, |partialTime Q t x| ≤ MP := by
      intro t x
      have heq : partialTime Q t x = Pt t :=
        (hasDerivAt_partialTime (hQ.differentiable (by norm_num)) t x).unique (by
          simpa [Q, Pt, SteeringVariablePeriodSelectedInverseJointC1.periodTime] using
            (hPdiff t).hasDerivAt)
      rw [heq]
      exact hPtbd t
    simpa [Q] using abs_time_sub_le_of_partialTime_bound hQ hQt a b 0
  have hdelta : Continuous (uncurry delta) :=
    SteeringNormalizedPeriod.continuous_uncurry_delta hP0 hkap0 hkap1 hPl hPu
      hK.continuous hsol hstrip hKbd hKlip hPlip
  have hdT : ∀ t s, HasDerivAt (fun r => delta r s) (dT t s) t := by
    intro t s
    exact hasDerivAt_param_of_contDiff_one hP0 hkap0 hkap1 hPl hPu hK hP hsol
      hstrip hper hKper hKbd hKtbd hPtbd t s
  have hKtc : Continuous (uncurry Kt) := by
    exact (contDiff_partialTime_self (n := 0) hK).continuous
  have hPtc : Continuous Pt := by
    simpa [Pt, SteeringVariablePeriodSelectedInverseJointC1.periodTime] using
      hP.continuous_deriv_one
  have hcoefc : Continuous (uncurry fun t s => coef delta Pf t s) := by
    exact (hP.continuous.comp continuous_fst).mul (Real.continuous_cos.comp hdelta)
  have hsourcec : Continuous (uncurry fun t s => source K Kt delta Pf Pt t s) := by
    exact ((hPtc.comp continuous_fst).mul
      (hK.continuous.sub (Real.continuous_sin.comp hdelta))).add
      ((hP.continuous.comp continuous_fst).mul hKtc)
  have hdTc : Continuous (uncurry dT) := by
    have hpos : ∀ t, 0 < prim (coef delta Pf t) 1 := fun t =>
      prim_coef_pos hP0 hkap0 hkap1 hPl hsol hstrip t
    exact PeriodicGreenJoint.continuous_periodicGreen_param hcoefc hsourcec hpos
  have hspacec : Continuous
      (uncurry fun t s => Pf t * (K t s - Real.sin (delta t s))) :=
    (hP.continuous.comp continuous_fst).mul
      (hK.continuous.sub (Real.continuous_sin.comp hdelta))
  have hdeltaC1 : ContDiff ℝ 1 (uncurry delta) :=
    JointC1.contDiff_one_of_continuous_partials hdT hsol hdTc hspacec
  obtain ⟨sf, hsf⟩ := SelectedChangeOfVariable.exists_sf_family hkap0 hkap1 hdelta
    (fun t s => (hstrip t s).1) (fun t s => (hstrip t s).2)
  have hsfC1 : ContDiff ℝ 1 (uncurry sf) :=
    SelectedChangeOfVariable.contDiff_one_sf hkap0 hkap1 hdelta hdT hdTc
      (fun t s => (hstrip t s).1) (fun t s => (hstrip t s).2) hsf
  exact ⟨hdeltaC1, sf, hsf, hsfC1⟩

/-- **Existence of the complete normalized selected data at `C¹`.**  For a
jointly `C¹`, `1`-periodic normalized curvature in the selected tube and a
jointly `C¹` positive period factor, this produces the selected steering, its
rear-arclength inverse, their joint `C¹` certificates, and identifies the
steering time derivative with the exact periodic Green variation. -/
theorem exists_selected_with_inverse_of_contDiff_one
    (hP0 : 0 < P0) (hkap0 : 0 ≤ kap) (hkap1 : kap < 1)
    (hPl : ∀ a, P0 ≤ Pf a) (hPu : ∀ a, Pf a ≤ P1)
    (hK : ContDiff ℝ 1 (uncurry K)) (hP : ContDiff ℝ 1 Pf)
    (hKper : ∀ a, Function.Periodic (K a) 1)
    (hK0 : ∀ a s, 0 ≤ K a s) (hKk : ∀ a s, K a s ≤ kap)
    (hKtbd : ∀ a s, |partialTime K a s| ≤ Md)
    (hPtbd : ∀ a, |SteeringVariablePeriodSelectedInverseJointC1.periodTime Pf a| ≤ MP) :
    ∃ delta sf : ℝ → ℝ → ℝ,
      (∀ t, Function.Periodic (delta t) 1) ∧
      (∀ t s, delta t s ∈ Icc (0 : ℝ) (arcsin kap)) ∧
      (∀ t s, HasDerivAt (delta t)
        (Pf t * (K t s - Real.sin (delta t s))) s) ∧
      (∀ t x, RearTrack.rearArclength (delta t) (sf t x) = x) ∧
      ContDiff ℝ 1 (uncurry delta) ∧
      ContDiff ℝ 1 (uncurry sf) ∧
      ∀ t s, HasDerivAt (fun r => delta r s)
        (variation K (partialTime K) delta Pf
          (SteeringVariablePeriodSelectedInverseJointC1.periodTime Pf) t s) t := by
  let Kphys : ℝ → ℝ → ℝ := fun t s => K t (s / Pf t)
  have hPpos : ∀ t, 0 < Pf t := fun t => lt_of_lt_of_le hP0 (hPl t)
  have hKslice : ∀ t, Continuous (Kphys t) := fun t =>
    (hK.continuous.comp (continuous_const.prodMk continuous_id)).comp
      (continuous_id.div_const (Pf t))
  have hKphysper : ∀ t, Function.Periodic (Kphys t) (Pf t) := by
    intro t s
    dsimp [Kphys]
    have hpne := (hPpos t).ne'
    convert hKper t (s / Pf t) using 1
    field_simp
  have hKphys0 : ∀ t s, 0 ≤ Kphys t s := fun t s => hK0 t (s / Pf t)
  have hKphysk : ∀ t s, Kphys t s ≤ kap := fun t s => hKk t (s / Pf t)
  obtain ⟨deltaPhys, sf0, hperPhys, hs0Phys, hs1Phys, hsolPhys, _hsf0, -⟩ :=
    SelectedSteeringFamily.exists_selected_steering_family
      hkap0 hkap1 hPpos hKslice hKphysper hKphys0 hKphysk
  let delta : ℝ → ℝ → ℝ := fun t u => deltaPhys t (Pf t * u)
  have hper : ∀ t, Function.Periodic (delta t) 1 := by
    intro t u
    dsimp [delta]
    convert hperPhys t (Pf t * u) using 1 <;> ring
  have hs0 : ∀ t s, 0 ≤ delta t s := fun t s => hs0Phys t (Pf t * s)
  have hs1 : ∀ t s, delta t s ≤ arcsin kap := fun t s => hs1Phys t (Pf t * s)
  have hsol : ∀ t s, HasDerivAt (delta t)
      (Pf t * (K t s - Real.sin (delta t s))) s := by
    intro t s
    have hinner : HasDerivAt (fun u : ℝ => Pf t * u) (Pf t) s := by
      simpa using (hasDerivAt_id s).const_mul (Pf t)
    have hcomp := (hsolPhys t (Pf t * s)).comp s hinner
    have hKval : Kphys t (Pf t * s) = K t s := by
      dsimp [Kphys]
      field_simp [(hPpos t).ne']
    have hder : (Kphys t (Pf t * s) - Real.sin (deltaPhys t (Pf t * s))) * Pf t =
        Pf t * (K t s - Real.sin (deltaPhys t (Pf t * s))) := by
      rw [hKval]
      ring
    simpa [delta, Function.comp_def] using hcomp.congr_deriv hder
  have hstrip : ∀ t s, delta t s ∈ Icc (0 : ℝ) (arcsin kap) :=
    fun t s => ⟨hs0 t s, hs1 t s⟩
  have hKbd : ∀ t s, |K t s| ≤ kap := by
    intro t s
    rw [abs_of_nonneg (hK0 t s)]
    exact hKk t s
  obtain ⟨hdeltaC1, sf, hsf, hsfC1⟩ :=
    exists_selected_inverse_of_contDiff_one hP0 hkap0 hkap1 hPl hPu hK hP
      hsol hstrip hper hKper hKbd hKtbd hPtbd
  refine ⟨delta, sf, hper, hstrip, hsol, hsf, hdeltaC1, hsfC1, ?_⟩
  intro t s
  exact hasDerivAt_param_of_contDiff_one hP0 hkap0 hkap1 hPl hPu hK hP hsol
    hstrip hper hKper hKbd hKtbd hPtbd t s

/-- **Physical variable-period selected steering and inverse at `C¹`.**
The curvature is supplied in physical arclength with moving period `Pf(t)`.
The proof normalizes to the unit circle, applies the Taylor-free theorem above,
and rescales back. -/
theorem exists_physical_selected_with_inverse_of_contDiff_one
    {Kphys : ℝ → ℝ → ℝ}
    (hP0 : 0 < P0) (hkap0 : 0 ≤ kap) (hkap1 : kap < 1)
    (hPl : ∀ a, P0 ≤ Pf a) (hPu : ∀ a, Pf a ≤ P1)
    (hK : ContDiff ℝ 1 (uncurry Kphys)) (hP : ContDiff ℝ 1 Pf)
    (hKper : ∀ a, Function.Periodic (Kphys a) (Pf a))
    (hK0 : ∀ a s, 0 ≤ Kphys a s) (hKk : ∀ a s, Kphys a s ≤ kap)
    (hKnTbd : ∀ a u,
      |partialTime
        (SteeringVariablePeriodSelectedInverseJointC1.normalizedCurvature Kphys Pf) a u| ≤ Md)
    (hPtbd : ∀ a, |SteeringVariablePeriodSelectedInverseJointC1.periodTime Pf a| ≤ MP) :
    ∃ delta sf : ℝ → ℝ → ℝ,
      (∀ t, Function.Periodic (delta t) (Pf t)) ∧
      (∀ t s, delta t s ∈ Icc (0 : ℝ) (arcsin kap)) ∧
      (∀ t s, HasDerivAt (delta t)
        (Kphys t s - Real.sin (delta t s)) s) ∧
      (∀ t x, RearTrack.rearArclength (delta t) (sf t x) = x) ∧
      ContDiff ℝ 1 (uncurry delta) ∧
      ContDiff ℝ 1 (uncurry sf) ∧
      ∀ t s, HasDerivAt (partialTime delta t)
        (-Real.cos (delta t s) * partialTime delta t s + partialTime Kphys t s) s := by
  let Kn := SteeringVariablePeriodSelectedInverseJointC1.normalizedCurvature Kphys Pf
  have hKn : ContDiff ℝ 1 (uncurry Kn) :=
    SteeringVariablePeriodSelectedInverseJointC1.normalizedCurvature_contDiff_one hK hP
  have hKnper : ∀ t, Function.Periodic (Kn t) 1 :=
    SteeringVariablePeriodSelectedInverseJointC1.normalizedCurvature_periodic hKper
  have hKn0 : ∀ t u, 0 ≤ Kn t u := fun t u => hK0 t (Pf t * u)
  have hKnk : ∀ t u, Kn t u ≤ kap := fun t u => hKk t (Pf t * u)
  obtain ⟨dn, sfn, hdnper, hdnstrip, hdnsol, _hsfn, hdnC1, _hsfnC1, hdnT⟩ :=
    exists_selected_with_inverse_of_contDiff_one hP0 hkap0 hkap1 hPl hPu hKn hP
      hKnper hKn0 hKnk hKnTbd hPtbd
  let delta : ℝ → ℝ → ℝ := fun t s => dn t (s / Pf t)
  have hPpos : ∀ t, 0 < Pf t := fun t => lt_of_lt_of_le hP0 (hPl t)
  have hdeltaC1 : ContDiff ℝ 1 (uncurry delta) := by
    exact SteeringNormalizedPeriod.contDiff_arclength_of_normalized hdnC1 hP hPpos
  have hdper : ∀ t, Function.Periodic (delta t) (Pf t) := by
    intro t s
    dsimp [delta]
    have hpne := (hPpos t).ne'
    convert hdnper t (s / Pf t) using 1
    field_simp
  have hdstrip : ∀ t s, delta t s ∈ Icc (0 : ℝ) (arcsin kap) :=
    fun t s => hdnstrip t (s / Pf t)
  have hdsol : ∀ t s, HasDerivAt (delta t)
      (Kphys t s - Real.sin (delta t s)) s := by
    intro t s
    have hpne := (hPpos t).ne'
    have hinner : HasDerivAt (fun y : ℝ => y / Pf t) (1 / Pf t) s := by
      simpa using (hasDerivAt_id s).div_const (Pf t)
    have hcomp := (hdnsol t (s / Pf t)).comp s hinner
    have hKnval : Kn t (s / Pf t) = Kphys t s := by
      dsimp [Kn, SteeringVariablePeriodSelectedInverseJointC1.normalizedCurvature]
      field_simp [hpne]
    have hder : Pf t * (Kn t (s / Pf t) - Real.sin (dn t (s / Pf t))) *
          (1 / Pf t) = Kphys t s - Real.sin (dn t (s / Pf t)) := by
      rw [hKnval]
      field_simp [hpne]
    simpa [delta, Function.comp_def] using hcomp.congr_deriv hder
  obtain ⟨sf, hsf⟩ := SelectedChangeOfVariable.exists_sf_family hkap0 hkap1
    hdeltaC1.continuous (fun t s => (hdstrip t s).1) (fun t s => (hdstrip t s).2)
  have hsfC1 : ContDiff ℝ 1 (uncurry sf) := by
    simpa using RearOwnHigherRegularity.contDiff_sf (n := 0) hkap0 hkap1 hdeltaC1
      (fun t s => (hdstrip t s).1) (fun t s => (hdstrip t s).2) hsf
  let Knt : ℝ → ℝ → ℝ := partialTime Kn
  let Pt : ℝ → ℝ := SteeringVariablePeriodSelectedInverseJointC1.periodTime Pf
  let wn : ℝ → ℝ → ℝ := variation Kn Knt dn Pf Pt
  let deltaT : ℝ → ℝ → ℝ := fun t s =>
    wn t (s / Pf t) - (s * Pt t / Pf t) *
      (Kphys t s - Real.sin (delta t s))
  have hdeltaTime : ∀ t s, HasDerivAt (fun r => delta r s) (deltaT t s) t := by
    intro t s
    have hpne := (hPpos t).ne'
    have hPdiff : Differentiable ℝ Pf := hP.differentiable (by norm_num)
    have hinner : HasDerivAt (fun r => s / Pf r)
        (-(s * Pt t / Pf t ^ 2)) t := by
      have hp := (hPdiff t).hasDerivAt
      have hc : HasDerivAt (fun _ : ℝ => s) 0 t := hasDerivAt_const t s
      have hq := hc.div hp hpne
      refine hq.congr_deriv ?_
      dsimp [Pt, SteeringVariablePeriodSelectedInverseJointC1.periodTime]
      field_simp [hpne]
      ring
    have hmove := RearOwnPathDistIntrinsic.hasDerivAt_moving_point
      (hdnC1.differentiable (by norm_num)) hinner
    have hpart : partialTime dn t (s / Pf t) = wn t (s / Pf t) :=
      (hasDerivAt_partialTime (hdnC1.differentiable (by norm_num)) t (s / Pf t)).unique
        (hdnT t (s / Pf t))
    have harc : partialArc dn t (s / Pf t) =
        Pf t * (Kn t (s / Pf t) - Real.sin (dn t (s / Pf t))) :=
      (hasDerivAt_partialArc (hdnC1.differentiable (by norm_num)) t (s / Pf t)).unique
        (hdnsol t (s / Pf t))
    have hKnval : Kn t (s / Pf t) = Kphys t s := by
      dsimp [Kn, SteeringVariablePeriodSelectedInverseJointC1.normalizedCurvature]
      field_simp [hpne]
    refine hmove.congr_deriv ?_
    simp only [delta, deltaT, smul_eq_mul]
    rw [hpart, harc, hKnval]
    field_simp [hpne]
    ring
  have hdeltaT_eq : ∀ t s, partialTime delta t s = deltaT t s := by
    intro t s
    exact (hasDerivAt_partialTime (hdeltaC1.differentiable (by norm_num)) t s).unique
      (hdeltaTime t s)
  have hKntc : Continuous (uncurry Knt) :=
    (contDiff_partialTime_self (n := 0) hKn).continuous
  have hKntper : ∀ t, Function.Periodic (Knt t) 1 :=
    SteeringVariablePeriodSelectedInverseJointC1.partialTime_periodic_of_periodic hKn hKnper
  have hsteeringTimeSpatial : ∀ t s, HasDerivAt (partialTime delta t)
      (-Real.cos (delta t s) * partialTime delta t s + partialTime Kphys t s) s := by
    intro t s
    have hpne := (hPpos t).ne'
    have hinner : HasDerivAt (fun y : ℝ => y / Pf t) (1 / Pf t) s := by
      simpa using (hasDerivAt_id s).div_const (Pf t)
    have hwn0 := SteeringNormalizedPeriod.hasDerivAt_variation
      (Pd := Pt) hP0 hkap0 hkap1 hPl hKn.continuous hKntc hdnsol hdnstrip
      hdnper hKnper hKntper t (s / Pf t)
    have hwn : HasDerivAt (fun y => wn t (y / Pf t))
        ((source Kn Knt dn Pf Pt t (s / Pf t) -
          coef dn Pf t (s / Pf t) * wn t (s / Pf t)) * (1 / Pf t)) s := by
      simpa [wn, Function.comp_def] using hwn0.comp s hinner
    have hc : HasDerivAt (fun y : ℝ => y * Pt t / Pf t) (Pt t / Pf t) s := by
      convert ((hasDerivAt_id s).mul_const (Pt t)).div_const (Pf t) using 1 <;> ring
    have hfield : HasDerivAt
        (fun y => Kphys t y - Real.sin (delta t y))
        (partialArc Kphys t s - Real.cos (delta t s) *
          (Kphys t s - Real.sin (delta t s))) s := by
      have hkx := hasDerivAt_partialArc (hK.differentiable (by norm_num)) t s
      have hsine := (hdsol t s).sin
      exact (hkx.sub hsine).congr_deriv (by ring)
    have hdtExplicit : HasDerivAt (deltaT t)
        ((source Kn Knt dn Pf Pt t (s / Pf t) -
            coef dn Pf t (s / Pf t) * wn t (s / Pf t)) * (1 / Pf t) -
          ((Pt t / Pf t) * (Kphys t s - Real.sin (delta t s)) +
            (s * Pt t / Pf t) *
              (partialArc Kphys t s - Real.cos (delta t s) *
                (Kphys t s - Real.sin (delta t s))))) s := by
      have hp := hc.mul hfield
      simpa [deltaT] using hwn.sub hp
    have hKnTime :=
      SteeringVariablePeriodSelectedInverseJointC1.hasDerivAt_normalizedCurvature_time
        hK hP t (s / Pf t)
    have hKntval : Knt t (s / Pf t) = partialTime Kphys t s +
        partialArc Kphys t s * (Pt t * (s / Pf t)) := by
      have hcanon := hasDerivAt_partialTime (hKn.differentiable (by norm_num))
        t (s / Pf t)
      have hder :
          SteeringVariablePeriodSelectedInverseJointC1.curvatureTime Kphys t
                (Pf t * (s / Pf t)) +
              SteeringVariablePeriodSelectedInverseJointC1.curvatureSpace Kphys t
                (Pf t * (s / Pf t)) *
                (SteeringVariablePeriodSelectedInverseJointC1.periodTime Pf t *
                  (s / Pf t)) =
            partialTime Kphys t s + partialArc Kphys t s * (Pt t * (s / Pf t)) := by
        dsimp [SteeringVariablePeriodSelectedInverseJointC1.curvatureTime,
          SteeringVariablePeriodSelectedInverseJointC1.curvatureSpace, Pt,
          SteeringVariablePeriodSelectedInverseJointC1.periodTime]
        field_simp [hpne]
      exact hcanon.unique (by simpa [Kn] using hKnTime.congr_deriv hder)
    have hdeltaTfun : partialTime delta t = deltaT t := funext (hdeltaT_eq t)
    rw [← hdeltaTfun] at hdtExplicit
    refine hdtExplicit.congr_deriv ?_
    simp only [source, coef]
    have hKnval : Kn t (s / Pf t) = Kphys t s := by
      dsimp [Kn, SteeringVariablePeriodSelectedInverseJointC1.normalizedCurvature]
      field_simp [hpne]
    have hdnval : dn t (s / Pf t) = delta t s := rfl
    rw [hKnval, hdnval, hKntval, hdeltaT_eq t s]
    dsimp [deltaT]
    field_simp [hpne]
    ring
  exact ⟨delta, sf, hdper, hdstrip, hdsol, hsf, hdeltaC1, hsfC1,
    hsteeringTimeSpatial⟩

end SteeringNormalizedPeriodC1
