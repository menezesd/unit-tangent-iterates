import Mathlib
import UnitTangentIterates.PerimeterInteriorTerm
import UnitTangentIterates.LeibnizRuleLocal
import UnitTangentIterates.FrontPeriodizationIntegral

/-!
# The Leibniz rule for the perimeter defect, produced

`UnitTangentIterates/PerimeterInteriorTerm.lean` gives the derivative clause
`P'(H) = 1 + O(e^{-β'H})` of the proposition *Exact two-cap pairs* of
*A Noncircular Oval with Convex Unit-Tangent Iterates* with all three terms of
the Leibniz rule produced from the pulse, the Leibniz rule itself — the
differentiation of the centred cell integral in the period — being the only
remaining hypothesis.

This file discharges it.  For `g(H, u) = Φ(Y_H(u))` with
`Y_H(u) = ∑_{m∈ℤ} y(u - mH)` the periodization of an exponentially localized
pulse:

* `g H` is continuous for every positive period;
* the derivative in the period, `Φ'(Y_H)∂_H Y_H`, is bounded uniformly for
  periods above `H₀/2` and `|u|` in a window, so `g` is Lipschitz in the period
  there;
* the same uniform bound dominates the difference quotients of the
  fixed-endpoint integral, so differentiation under the integral sign applies.

Feeding these into `LeibnizRuleLocal.hasDerivAt_centred_integral_local` produces
the Leibniz rule, and hence the derivative clause with **no** hypothesis beyond
the pulse and the identification of the perimeter defect with the cell
integral.

Main results:

* `continuous_tsum_weighted_translates` : continuity of `∑_m (-m)F(· - mP)`;
* `abs_tsum_deriv_le_of_period` : `|∂_P Y_P(u)| ≤ 8Ce^{α|u|}e^{-αP₀}` for every
  period `P ≥ P₀`;
* `continuous_defect_integrand`, `continuous_interior_integrand` : continuity
  in `u` of the two integrands;
* `abs_Phi_periodization_sub_le` : the Lipschitz bound in the period;
* `hasDerivAt_param_integral` : differentiation under the integral sign;
* `hasDerivAt_centred_integral_of_pulse` : **the Leibniz rule** for the defect;
* `hasDerivAt_perimeter_of_pulse_leibniz` : the derivative clause
  `|P'(H₀) - 1| ≤ (25C² + (a/√(1-a²))·8C/((α/2-β')e))e^{-β'H₀}` with the
  Leibniz rule discharged.
-/

noncomputable section

open Real Set MeasureTheory Filter Topology

namespace PerimeterLeibnizProduced

open PerimeterAsymptotics PerimeterAsymptoticsProduced PerimeterInteriorTerm

/-! ### Continuity of the weighted periodization -/

/-- The polynomially weighted periodization of a continuous, exponentially
decaying function is continuous. -/
theorem continuous_tsum_weighted_translates {F : ℝ → ℝ} {C alpha P : ℝ}
    (halpha : 0 < alpha) (hP : 0 < P) (hF : Continuous F)
    (hFb : ∀ s, |F s| ≤ C * Real.exp (-alpha * |s|)) :
    Continuous (fun u => ∑' m : ℤ, (-(m : ℝ)) * F (u - m * P)) := by
  have hC : 0 ≤ C := PeriodizationDeriv.const_nonneg hFb
  have hq0 : (0:ℝ) ≤ Real.exp (-alpha * P) := (Real.exp_pos _).le
  have hq1 : Real.exp (-alpha * P) < 1 := Real.exp_lt_one_iff.mpr (by nlinarith)
  rw [continuous_iff_continuousAt]
  intro x
  have hnb : Ioo (x - 1) (x + 1) ∈ nhds x := Ioo_mem_nhds (by linarith) (by linarith)
  refine ContinuousOn.continuousAt ?_ hnb
  refine continuousOn_tsum (u := fun m : ℤ =>
      (C * Real.exp (alpha * (|x| + 1))) * ((m.natAbs : ℝ) * (Real.exp (-alpha * P)) ^ m.natAbs))
    (fun m => (continuous_const.mul
      (hF.comp (continuous_id.sub continuous_const))).continuousOn) ?_ ?_
  · exact PeriodizationDeriv.summable_natAbs_geometric hq0 hq1
  · intro m u hu
    have hux : |u| ≤ |x| + 1 := by
      rcases hu with ⟨h1, h2⟩
      rcases abs_cases u with ⟨he, _⟩ | ⟨he, _⟩ <;>
        rcases abs_cases x with ⟨he', _⟩ | ⟨he', _⟩ <;> rw [he, he'] <;> linarith
    have hshift := PeriodizationDeriv.abs_shift_le (w := F) (C := C) (a := alpha)
      (H₀ := P) (H := P) (s := u) halpha hFb hP le_rfl m
    have hmabs : |(-(m : ℝ))| = (m.natAbs : ℝ) := by
      rw [abs_neg, ← Int.cast_abs, Int.abs_eq_natAbs]; norm_num
    have hexp : Real.exp (alpha * |u|) ≤ Real.exp (alpha * (|x| + 1)) :=
      Real.exp_le_exp.mpr (by nlinarith)
    have hpow : (0:ℝ) ≤ (Real.exp (-alpha * P)) ^ m.natAbs := by positivity
    calc ‖(-(m : ℝ)) * F (u - m * P)‖ = (m.natAbs : ℝ) * |F (u - m * P)| := by
          rw [Real.norm_eq_abs, abs_mul, hmabs]
      _ ≤ (m.natAbs : ℝ) * ((C * Real.exp (alpha * |u|)) * (Real.exp (-alpha * P)) ^ m.natAbs) :=
          mul_le_mul_of_nonneg_left hshift (Nat.cast_nonneg _)
      _ ≤ (m.natAbs : ℝ)
            * ((C * Real.exp (alpha * (|x| + 1))) * (Real.exp (-alpha * P)) ^ m.natAbs) := by
          refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hexp hC) hpow
      _ = (C * Real.exp (alpha * (|x| + 1))) * ((m.natAbs : ℝ)
            * (Real.exp (-alpha * P)) ^ m.natAbs) := by ring

/-! ### A bound on the derivative in the period, uniform over periods -/

variable {y yp : ℝ → ℝ} {C a alpha H0 : ℝ}

/-- **The derivative of the periodization in the period**, bounded uniformly
over all periods `P ≥ P₀`. -/
theorem abs_tsum_deriv_le_of_period {P0 P u : ℝ} (halpha : 0 < alpha) (hP0 : 0 < P0)
    (hP : P0 ≤ P) (hq : Real.exp (-alpha * P0) ≤ 1 / 2)
    (hypb : ∀ x, |yp x| ≤ C * Real.exp (-alpha * |x|)) :
    |∑' m : ℤ, (-(m : ℝ)) * yp (u - m * P)|
      ≤ 8 * C * Real.exp (alpha * |u|) * Real.exp (-alpha * P0) := by
  have hC : 0 ≤ C := PeriodizationDeriv.const_nonneg hypb
  set q : ℝ := Real.exp (-alpha * P0) with hqdef
  have hq0 : (0 : ℝ) ≤ q := (Real.exp_pos _).le
  have hq1 : q < 1 := by linarith
  set K : ℝ := C * Real.exp (alpha * |u|) with hKdef
  have hK0 : 0 ≤ K := by positivity
  have hsum : Summable (fun m : ℤ => K * ((m.natAbs : ℝ) * q ^ m.natAbs)) :=
    PeriodizationDeriv.summable_natAbs_geometric hq0 hq1
  have hterm : ∀ m : ℤ, ‖(-(m : ℝ)) * yp (u - m * P)‖ ≤ K * ((m.natAbs : ℝ) * q ^ m.natAbs) := by
    intro m
    have hshift := PeriodizationDeriv.abs_shift_le (w := yp) (C := C) (a := alpha)
      (H₀ := P0) (H := P) (s := u) halpha hypb hP0 hP m
    have hmabs : |(-(m : ℝ))| = (m.natAbs : ℝ) := by
      rw [abs_neg, ← Int.cast_abs, Int.abs_eq_natAbs]; norm_num
    calc ‖(-(m : ℝ)) * yp (u - m * P)‖ = (m.natAbs : ℝ) * |yp (u - m * P)| := by
          rw [Real.norm_eq_abs, abs_mul, hmabs]
      _ ≤ (m.natAbs : ℝ) * (K * q ^ m.natAbs) :=
          mul_le_mul_of_nonneg_left hshift (Nat.cast_nonneg _)
      _ = K * ((m.natAbs : ℝ) * q ^ m.natAbs) := by ring
  have hbound : |∑' m : ℤ, (-(m : ℝ)) * yp (u - m * P)|
      ≤ ∑' m : ℤ, K * ((m.natAbs : ℝ) * q ^ m.natAbs) := by
    simpa [Real.norm_eq_abs] using tsum_of_norm_bounded hsum.hasSum hterm
  calc |∑' m : ℤ, (-(m : ℝ)) * yp (u - m * P)|
      ≤ ∑' m : ℤ, K * ((m.natAbs : ℝ) * q ^ m.natAbs) := hbound
    _ = K * ∑' m : ℤ, ((m.natAbs : ℝ) * q ^ m.natAbs) := tsum_mul_left
    _ ≤ K * (8 * q) := mul_le_mul_of_nonneg_left (tsum_natAbs_geom_le hq0 hq) hK0
    _ = 8 * C * Real.exp (alpha * |u|) * Real.exp (-alpha * P0) := by rw [hKdef, hqdef]; ring

/-! ### Continuity of the two integrands -/

/-- The defect integrand of the periodized profile is continuous. -/
theorem continuous_defect_integrand {P : ℝ} (halpha : 0 < alpha) (hP : 0 < P)
    (hy : Continuous y) (hyb : ∀ x, |y x| ≤ C * Real.exp (-alpha * |x|)) :
    Continuous (fun u => Phi (∑' m : ℤ, y (u - m * P))) := by
  have hY := FrontPeriodizationIntegral.continuous_tsum_translates
    (F := y) (C := C) (alpha := alpha) (P := P) halpha hP hy hyb
  have hPhi : Continuous Phi := by
    unfold Phi
    fun_prop
  exact hPhi.comp hY

/-- The interior integrand `Φ'(Y_P)∂_P Y_P` is continuous. -/
theorem continuous_interior_integrand {P : ℝ} (halpha : 0 < alpha) (hP : 0 < P)
    (hy : Continuous y) (hyp : Continuous yp)
    (hyb : ∀ x, |y x| ≤ C * Real.exp (-alpha * |x|))
    (hypb : ∀ x, |yp x| ≤ C * Real.exp (-alpha * |x|))
    (ha1 : a < 1) (hYa : ∀ u : ℝ, |∑' m : ℤ, y (u - m * P)| ≤ a) :
    Continuous (fun u => (∑' m : ℤ, y (u - m * P))
      / Real.sqrt (1 - (∑' m : ℤ, y (u - m * P)) ^ 2)
      * ∑' m : ℤ, (-(m : ℝ)) * yp (u - m * P)) := by
  have hY := FrontPeriodizationIntegral.continuous_tsum_translates
    (F := y) (C := C) (alpha := alpha) (P := P) halpha hP hy hyb
  have hD := continuous_tsum_weighted_translates (F := yp) (C := C) (alpha := alpha) (P := P)
    halpha hP hyp hypb
  have hden : Continuous (fun u => Real.sqrt (1 - (∑' m : ℤ, y (u - m * P)) ^ 2)) := by
    fun_prop
  have hne : ∀ u, Real.sqrt (1 - (∑' m : ℤ, y (u - m * P)) ^ 2) ≠ 0 := by
    intro u
    have hle := hYa u
    have hlt : (∑' m : ℤ, y (u - m * P)) ^ 2 < 1 := by
      have h1 : |∑' m : ℤ, y (u - m * P)| < 1 := lt_of_le_of_lt hle ha1
      nlinarith [abs_nonneg (∑' m : ℤ, y (u - m * P)), sq_abs (∑' m : ℤ, y (u - m * P))]
    exact ne_of_gt (Real.sqrt_pos.mpr (by linarith))
  exact (hY.div hden hne).mul hD

/-! ### The Lipschitz bound in the period -/

/-- `|Φ'(z)| ≤ a/√(1-a²)` on `|z| ≤ a < 1`. -/
theorem abs_Phi_deriv_le {z : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) (hz : |z| ≤ a) :
    |z / Real.sqrt (1 - z ^ 2)| ≤ a / Real.sqrt (1 - a ^ 2) := by
  have ha2 : a ^ 2 < 1 := by nlinarith
  have hda : 0 < Real.sqrt (1 - a ^ 2) := Real.sqrt_pos.mpr (by linarith)
  have hz2 : z ^ 2 ≤ a ^ 2 := by
    have := abs_le.mp hz
    nlinarith [this.1, this.2]
  have hdz : Real.sqrt (1 - a ^ 2) ≤ Real.sqrt (1 - z ^ 2) := Real.sqrt_le_sqrt (by linarith)
  have hdz0 : 0 < Real.sqrt (1 - z ^ 2) := lt_of_lt_of_le hda hdz
  rw [abs_div, abs_of_pos hdz0]
  gcongr

/-- The uniform bound on the derivative in the period, on the window
`|u| ≤ H₀` and over all periods above `H₀/2`. -/
theorem abs_interior_integrand_le_window {P u : ℝ} (halpha : 0 < alpha) (hH0 : 0 < H0)
    (hthr : Real.exp (-alpha * (H0 / 2)) ≤ 1 / 2)
    (hypb : ∀ x, |yp x| ≤ C * Real.exp (-alpha * |x|))
    (ha0 : 0 ≤ a) (ha1 : a < 1)
    (hP : H0 / 2 < P) (hu : |u| ≤ H0)
    (hYa : |∑' m : ℤ, y (u - m * P)| ≤ a) :
    |(∑' m : ℤ, y (u - m * P)) / Real.sqrt (1 - (∑' m : ℤ, y (u - m * P)) ^ 2)
        * ∑' m : ℤ, (-(m : ℝ)) * yp (u - m * P)|
      ≤ a / Real.sqrt (1 - a ^ 2)
          * (8 * C * Real.exp (alpha * H0) * Real.exp (-alpha * (H0 / 2))) := by
  have hC : 0 ≤ C := PeriodizationDeriv.const_nonneg hypb
  have hfac := abs_Phi_deriv_le ha0 ha1 hYa
  have hD := abs_tsum_deriv_le_of_period (yp := yp) (C := C) (alpha := alpha)
    (P0 := H0 / 2) (P := P) (u := u) halpha (by linarith) hP.le hthr hypb
  have hexp : Real.exp (alpha * |u|) ≤ Real.exp (alpha * H0) :=
    Real.exp_le_exp.mpr (by nlinarith)
  have hD' : |∑' m : ℤ, (-(m : ℝ)) * yp (u - m * P)|
      ≤ 8 * C * Real.exp (alpha * H0) * Real.exp (-alpha * (H0 / 2)) := by
    refine hD.trans ?_
    have h1 : 8 * C * Real.exp (alpha * |u|) ≤ 8 * C * Real.exp (alpha * H0) :=
      mul_le_mul_of_nonneg_left hexp (by positivity)
    exact mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
  have hpos : 0 ≤ a / Real.sqrt (1 - a ^ 2) := by positivity
  rw [abs_mul]
  exact mul_le_mul hfac hD' (abs_nonneg _) hpos

/-- **The defect integrand is Lipschitz in the period**, uniformly on the
window `|u| ≤ H₀`, for periods above `H₀/2`. -/
theorem abs_Phi_periodization_sub_le {P u : ℝ} (halpha : 0 < alpha) (hH0 : 0 < H0)
    (hthr : Real.exp (-alpha * (H0 / 2)) ≤ 1 / 2)
    (hy : ∀ x, HasDerivAt y (yp x) x)
    (hyb : ∀ x, |y x| ≤ C * Real.exp (-alpha * |x|))
    (hypb : ∀ x, |yp x| ≤ C * Real.exp (-alpha * |x|))
    (ha0 : 0 ≤ a) (ha1 : a < 1)
    (hYa : ∀ Q : ℝ, H0 / 2 < Q → ∀ v : ℝ, |∑' m : ℤ, y (v - m * Q)| ≤ a)
    (hu : |u| ≤ H0) (hP : H0 / 2 < P) :
    |Phi (∑' m : ℤ, y (u - m * P)) - Phi (∑' m : ℤ, y (u - m * H0))|
      ≤ a / Real.sqrt (1 - a ^ 2)
          * (8 * C * Real.exp (alpha * H0) * Real.exp (-alpha * (H0 / 2))) * |P - H0| := by
  set M : ℝ := a / Real.sqrt (1 - a ^ 2)
    * (8 * C * Real.exp (alpha * H0) * Real.exp (-alpha * (H0 / 2))) with hM
  have hderiv : ∀ t ∈ Ioi (H0 / 2),
      HasDerivWithinAt (fun r : ℝ => Phi (∑' m : ℤ, y (u - m * r)))
        ((∑' m : ℤ, y (u - m * t)) / Real.sqrt (1 - (∑' m : ℤ, y (u - m * t)) ^ 2)
          * ∑' m : ℤ, (-(m : ℝ)) * yp (u - m * t)) (Ioi (H0 / 2)) t := by
    intro t ht
    have hlt : |∑' m : ℤ, y (u - m * t)| < 1 :=
      lt_of_le_of_lt (hYa t ht u) ha1
    exact (PerimeterInteriorTerm.hasDerivAt_Phi_periodization (y := y) (yp := yp) (C := C)
      (alpha := alpha) (H₀ := H0 / 2) (H := t) (s := u) halpha (by linarith) ht hy hyb hypb
      hlt).hasDerivWithinAt
  have hbd : ∀ t ∈ Ioi (H0 / 2),
      ‖(∑' m : ℤ, y (u - m * t)) / Real.sqrt (1 - (∑' m : ℤ, y (u - m * t)) ^ 2)
        * ∑' m : ℤ, (-(m : ℝ)) * yp (u - m * t)‖ ≤ M := by
    intro t ht
    rw [Real.norm_eq_abs]
    exact abs_interior_integrand_le_window halpha hH0 hthr hypb ha0 ha1 ht hu (hYa t ht u)
  have hmain := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hderiv hbd (convex_Ioi _)
    (by simp only [mem_Ioi]; linarith : H0 ∈ Ioi (H0 / 2)) hP
  simpa [Real.norm_eq_abs] using hmain

/-! ### Differentiation under the integral sign -/

/-- **The fixed-endpoint cell integral is differentiable in the period**, with
the derivative obtained by differentiating under the integral sign. -/
theorem hasDerivAt_param_integral (halpha : 0 < alpha) (hH0 : 0 < H0)
    (hthr : Real.exp (-alpha * (H0 / 2)) ≤ 1 / 2)
    (hy : ∀ x, HasDerivAt y (yp x) x) (hyp : Continuous yp)
    (hyb : ∀ x, |y x| ≤ C * Real.exp (-alpha * |x|))
    (hypb : ∀ x, |yp x| ≤ C * Real.exp (-alpha * |x|))
    (ha0 : 0 ≤ a) (ha1 : a < 1)
    (hYa : ∀ Q : ℝ, H0 / 2 < Q → ∀ v : ℝ, |∑' m : ℤ, y (v - m * Q)| ≤ a) :
    HasDerivAt (fun P => ∫ u in (-(H0 / 2))..(H0 / 2), Phi (∑' m : ℤ, y (u - m * P)))
      (∫ u in (-(H0 / 2))..(H0 / 2),
        (∑' m : ℤ, y (u - m * H0)) / Real.sqrt (1 - (∑' m : ℤ, y (u - m * H0)) ^ 2)
          * ∑' m : ℤ, (-(m : ℝ)) * yp (u - m * H0)) H0 := by
  have hycont : Continuous y := by
    rw [continuous_iff_continuousAt]
    exact fun x => (hy x).continuousAt
  set M : ℝ := a / Real.sqrt (1 - a ^ 2)
    * (8 * C * Real.exp (alpha * H0) * Real.exp (-alpha * (H0 / 2))) with hM
  have hs : Ioi (H0 / 2) ∈ 𝓝 H0 := isOpen_Ioi.mem_nhds (by simp only [mem_Ioi]; linarith)
  have hFcont : ∀ P ∈ Ioi (H0 / 2), Continuous (fun u => Phi (∑' m : ℤ, y (u - m * P))) := by
    intro P hP
    exact continuous_defect_integrand (C := C) halpha (by simp only [mem_Ioi] at hP; linarith)
      hycont hyb
  have hF'cont : Continuous (fun u => (∑' m : ℤ, y (u - m * H0))
      / Real.sqrt (1 - (∑' m : ℤ, y (u - m * H0)) ^ 2)
      * ∑' m : ℤ, (-(m : ℝ)) * yp (u - m * H0)) :=
    continuous_interior_integrand (C := C) (a := a) halpha hH0 hycont hyp hyb hypb ha1
      (hYa H0 (by linarith))
  have hmeas : ∀ᶠ P in 𝓝 H0, AEStronglyMeasurable
      (fun u => Phi (∑' m : ℤ, y (u - m * P))) (volume.restrict (uIoc (-(H0 / 2)) (H0 / 2))) := by
    filter_upwards [hs] with P hP
    exact (hFcont P hP).aestronglyMeasurable
  have hint : IntervalIntegrable (fun u => Phi (∑' m : ℤ, y (u - m * H0))) volume
      (-(H0 / 2)) (H0 / 2) := (hFcont H0 (by simp only [mem_Ioi]; linarith)).intervalIntegrable _ _
  have hbound : ∀ᵐ t : ℝ, t ∈ uIoc (-(H0 / 2)) (H0 / 2) → ∀ P ∈ Ioi (H0 / 2),
      ‖(∑' m : ℤ, y (t - m * P)) / Real.sqrt (1 - (∑' m : ℤ, y (t - m * P)) ^ 2)
        * ∑' m : ℤ, (-(m : ℝ)) * yp (t - m * P)‖ ≤ M := by
    refine Filter.Eventually.of_forall (fun t ht P hP => ?_)
    have hle : -(H0 / 2) ≤ H0 / 2 := by linarith
    rw [uIoc_of_le hle] at ht
    have htabs : |t| ≤ H0 := by
      rw [abs_le]; constructor <;> [linarith [ht.1]; linarith [ht.2]]
    rw [Real.norm_eq_abs]
    exact abs_interior_integrand_le_window halpha hH0 hthr hypb ha0 ha1 hP htabs (hYa P hP t)
  have hderiv : ∀ᵐ t : ℝ, t ∈ uIoc (-(H0 / 2)) (H0 / 2) → ∀ P ∈ Ioi (H0 / 2),
      HasDerivAt (fun P => Phi (∑' m : ℤ, y (t - m * P)))
        ((∑' m : ℤ, y (t - m * P)) / Real.sqrt (1 - (∑' m : ℤ, y (t - m * P)) ^ 2)
          * ∑' m : ℤ, (-(m : ℝ)) * yp (t - m * P)) P := by
    refine Filter.Eventually.of_forall (fun t _ P hP => ?_)
    have hlt : |∑' m : ℤ, y (t - m * P)| < 1 := lt_of_le_of_lt (hYa P hP t) ha1
    exact PerimeterInteriorTerm.hasDerivAt_Phi_periodization (y := y) (yp := yp) (C := C)
      (alpha := alpha) (H₀ := H0 / 2) (H := P) (s := t) halpha (by linarith) hP hy hyb hypb hlt
  exact (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (bound := fun _ => M) hs hmeas hint hF'cont.aestronglyMeasurable hbound
    (intervalIntegrable_const) hderiv).2

/-! ### The Leibniz rule and the derivative clause -/

/-- **The Leibniz rule for the perimeter defect.**  For the periodization of an
exponentially localized pulse whose periodizations stay below `a < 1`, the
centred cell integral of the defect integrand is differentiable in the period,
with the paper's three terms. -/
theorem hasDerivAt_centred_integral_of_pulse (halpha : 0 < alpha) (hH0 : 0 < H0)
    (hthr : Real.exp (-alpha * (H0 / 2)) ≤ 1 / 2)
    (hy : ∀ x, HasDerivAt y (yp x) x) (hyp : Continuous yp)
    (hyb : ∀ x, |y x| ≤ C * Real.exp (-alpha * |x|))
    (hypb : ∀ x, |yp x| ≤ C * Real.exp (-alpha * |x|))
    (ha0 : 0 ≤ a) (ha1 : a < 1)
    (hYa : ∀ Q : ℝ, H0 / 2 < Q → ∀ v : ℝ, |∑' m : ℤ, y (v - m * Q)| ≤ a) :
    HasDerivAt (fun H => ∫ u in (-(H / 2))..(H / 2), Phi (∑' m : ℤ, y (u - m * H)))
      (Phi (∑' m : ℤ, y (H0 / 2 - m * H0)) / 2
        + Phi (∑' m : ℤ, y (-(H0 / 2) - m * H0)) / 2
        + ∫ u in (-(H0 / 2))..(H0 / 2),
            (∑' m : ℤ, y (u - m * H0)) / Real.sqrt (1 - (∑' m : ℤ, y (u - m * H0)) ^ 2)
              * ∑' m : ℤ, (-(m : ℝ)) * yp (u - m * H0)) H0 := by
  have hC : 0 ≤ C := PeriodizationDeriv.const_nonneg hypb
  have hycont : Continuous y := by
    rw [continuous_iff_continuousAt]
    exact fun x => (hy x).continuousAt
  have hs : Ioi (H0 / 2) ∈ 𝓝 H0 := isOpen_Ioi.mem_nhds (by simp only [mem_Ioi]; linarith)
  refine LeibnizRuleLocal.hasDerivAt_centred_integral_local
    (g := fun H u => Phi (∑' m : ℤ, y (u - m * H)))
    (gH := fun u => (∑' m : ℤ, y (u - m * H0))
      / Real.sqrt (1 - (∑' m : ℤ, y (u - m * H0)) ^ 2)
      * ∑' m : ℤ, (-(m : ℝ)) * yp (u - m * H0))
    (L := a / Real.sqrt (1 - a ^ 2)
      * (8 * C * Real.exp (alpha * H0) * Real.exp (-alpha * (H0 / 2))))
    hH0 (by positivity)
    (continuous_defect_integrand (C := C) halpha hH0 hycont hyb) ?_ ?_
    (hasDerivAt_param_integral halpha hH0 hthr hy hyp hyb hypb ha0 ha1 hYa)
  · filter_upwards [hs] with H hH
    exact continuous_defect_integrand (C := C) halpha
      (by simp only [mem_Ioi] at hH; linarith) hycont hyb
  · filter_upwards [hs] with H hH
    intro u hu
    exact abs_Phi_periodization_sub_le halpha hH0 hthr hy hyb hypb ha0 ha1 hYa hu hH

/-- **`P'(H₀) = 1 + O(e^{-β'H₀})`, with the Leibniz rule discharged.**  For a
nonnegative pulse `y` with `|y|, |y'| ≤ Ce^{-α|·|}` whose periodizations stay
below `a < 1`, if the perimeter defect is the centred cell integral of
`Φ(Y_H)`, then for every `β' < α/2`

`|P'(H₀) - 1| ≤ (25C² + (a/√(1-a²))·8C/((α/2-β')e))e^{-β'H₀}`,

no hypothesis beyond the pulse and that identification being assumed. -/
theorem hasDerivAt_perimeter_of_pulse_leibniz {P : ℝ → ℝ} {beta' : ℝ}
    (halpha : 0 < alpha) (hH0 : 0 < H0) (hb : beta' < alpha / 2)
    (hthr : Real.exp (-alpha * (H0 / 2)) ≤ 1 / 2)
    (hy : ∀ x, HasDerivAt y (yp x) x) (hyp : Continuous yp)
    (hy0 : ∀ x, 0 ≤ y x)
    (hyb : ∀ x, |y x| ≤ C * Real.exp (-alpha * |x|))
    (hypb : ∀ x, |yp x| ≤ C * Real.exp (-alpha * |x|))
    (ha0 : 0 ≤ a) (ha1 : a < 1)
    (hYa : ∀ Q : ℝ, H0 / 2 < Q → ∀ v : ℝ, |∑' m : ℤ, y (v - m * Q)| ≤ a)
    (hid : ∀ H, H - P H = ∫ u in (-(H / 2))..(H / 2), Phi (∑' m : ℤ, y (u - m * H))) :
    ∃ p : ℝ, HasDerivAt P p H0 ∧
      |p - 1| ≤ (25 * C ^ 2
        + a / Real.sqrt (1 - a ^ 2) * (8 * C) / ((alpha / 2 - beta') * Real.exp 1))
          * Real.exp (-beta' * H0) := by
  have hq : Real.exp (-alpha * H0) ≤ 1 / 2 := by
    refine le_trans (Real.exp_le_exp.mpr ?_) hthr
    nlinarith
  have hyb' : ∀ x, y x ≤ C * Real.exp (-alpha * |x|) := fun x =>
    le_trans (le_abs_self _) (hyb x)
  exact PerimeterInteriorTerm.hasDerivAt_perimeter_of_pulse_full
    (y := y) (yp := yp) (C := C) (a := a) (alpha := alpha) (H := H0) (beta' := beta')
    (P := P) (g := fun H u => Phi (∑' m : ℤ, y (u - m * H)))
    (gH := fun u => (∑' m : ℤ, y (u - m * H0))
      / Real.sqrt (1 - (∑' m : ℤ, y (u - m * H0)) ^ 2)
      * ∑' m : ℤ, (-(m : ℝ)) * yp (u - m * H0))
    halpha hH0 hb hq hy0 hyb' hypb ha0 ha1 (hYa H0 (by linarith))
    (fun _ _ => rfl) (fun _ => rfl) hid
    (hasDerivAt_centred_integral_of_pulse halpha hH0 hthr hy hyp hyb hypb ha0 ha1 hYa)

end PerimeterLeibnizProduced
