import Mathlib
import UnitTangentIterates.ModelOrbitDefect
import UnitTangentIterates.Periodization

/-!
# Positivity from the front-periodization error

This file isolates the last order argument in the proof of the proposition
*Exact two-cap pairs*.  If the isolated front curvature satisfies

`Kstar >= b0 * y`

and the error between the periodized front curvature and the periodization of
`Kstar` is at most `E` times the periodized pulse, then `E <= b0` implies that
the periodized front curvature is nonnegative.  This is the precise interface
between the lower comparison `HairpinRelative.hairpin_curv_ge_pulse` and the
pointwise relative-overlap estimate in the paper.
-/

noncomputable section

open Real

namespace FrontPeriodizationPositivity

/-- A constant multiple of an exponentially decreasing function is eventually
smaller than any positive number. -/
theorem eventually_const_mul_exp_neg_le {A c b : ℝ} (hc : 0 < c) (hb : 0 < b) :
    ∀ᶠ P in Filter.atTop, A * Real.exp (-c * P) ≤ b := by
  have harg : Filter.Tendsto (fun P : ℝ => -c * P) Filter.atTop Filter.atBot :=
    tendsto_const_nhds.neg_mul_atTop (show (-c : ℝ) < 0 by linarith) Filter.tendsto_id
  have hexp : Filter.Tendsto (fun P : ℝ => Real.exp (-c * P)) Filter.atTop (nhds 0) :=
    Real.tendsto_exp_atBot.comp harg
  have hmul := hexp.const_mul A
  simp only [mul_zero] at hmul
  exact ((tendsto_order.1 hmul).2 b hb).mono fun P hP => hP.le

/-- **An explicit positivity coefficient is small for every sufficiently
large period.**  The returned threshold simultaneously gives the geometric
series hypothesis used by `Periodization.periodization_error_le` and the
coefficient inequality used by the front-curvature positivity theorem. -/
theorem exists_largePeriod_positivity_threshold
    {alpha a D C b0 : ℝ} (halpha : 0 < alpha) (hb0 : 0 < b0)
    (_ha0 : 0 ≤ a) (_ha1 : a < 1) (_hD : 0 ≤ D) (_hC : 0 ≤ C) :
    ∃ P0 : ℝ, 0 < P0 ∧ ∀ P ≥ P0,
      0 < P ∧ Real.exp (-alpha * P) ≤ 1 / 2 ∧
        8 * FrontPeriodization.lipConst a * D * C *
          Real.exp (-(alpha / 2) * P) ≤ b0 := by
  have hqev : ∀ᶠ P : ℝ in Filter.atTop, Real.exp (-alpha * P) ≤ 1 / 2 := by
    simpa using eventually_const_mul_exp_neg_le (A := 1) (c := alpha) (b := 1 / 2)
      halpha (by norm_num)
  have hce : 0 < alpha / 2 := by linarith
  have hsepev : ∀ᶠ P : ℝ in Filter.atTop,
      (8 * FrontPeriodization.lipConst a * D * C) *
        Real.exp (-(alpha / 2) * P) ≤ b0 :=
    eventually_const_mul_exp_neg_le hce hb0
  have hev : ∀ᶠ P : ℝ in Filter.atTop,
      0 < P ∧ Real.exp (-alpha * P) ≤ 1 / 2 ∧
        8 * FrontPeriodization.lipConst a * D * C *
          Real.exp (-(alpha / 2) * P) ≤ b0 := by
    filter_upwards [Filter.Ioi_mem_atTop (0 : ℝ), hqev, hsepev] with P hP hqP hsepP
    refine ⟨hP, hqP, ?_⟩
    simpa [mul_assoc] using hsepP
  obtain ⟨Q, hQ⟩ := Filter.eventually_atTop.1 hev
  refine ⟨max Q 1, by positivity, fun P hP => ?_⟩
  exact hQ P (le_trans (le_max_left Q 1) hP)

/-- **Pointwise relative overlap on the centered period cell.**  If a
nonnegative pulse has the exponential bound `y(s) <= C exp(-alpha |s|)`, then
the ordered overlap density is at most

`8 C exp(-(alpha/2)P) Y_P`.

The factor `8` comes from the existing tail estimate
`Y_P-y <= 4 C exp(-(alpha/2)P)` and the elementary inequality that the ordered
overlap is at most twice the noncentral mass times the total mass. -/
theorem overlapDensity_le_cell {y : ℝ → ℝ} {C alpha P u : ℝ}
    (halpha : 0 < alpha) (hP : 0 < P)
    (hq : Real.exp (-alpha * P) ≤ 1 / 2)
    (hy0 : ∀ s, 0 ≤ y s)
    (hyb : ∀ s, y s ≤ C * Real.exp (-alpha * |s|))
    (hu : |u| ≤ P / 2) :
    (∑' m : ℤ, y (u - m * P) *
        ((∑' j : ℤ, y (u - j * P)) - y (u - m * P)))
      ≤ 8 * C * Real.exp (-(alpha / 2) * P) *
        ∑' j : ℤ, y (u - j * P) := by
  have hC : 0 ≤ C := Periodization.const_nonneg hy0 hyb
  have habs : ∀ s, |y s| ≤ C * Real.exp (-alpha * |s|) := fun s => by
    rw [abs_of_nonneg (hy0 s)]
    exact hyb s
  set q : ℤ → ℝ := fun m => y (u - m * P) with hqdef
  set Y : ℝ := ∑' m : ℤ, q m with hYdef
  have hsq : Summable q :=
    FrontPeriodizationIntegral.summable_translates halpha hP habs u
  have hq0 : ∀ m, 0 ≤ q m := fun m => hy0 _
  have hqY : ∀ m, q m ≤ Y := fun m => hsq.le_tsum m (fun j _ => hq0 j)
  have hY0 : 0 ≤ Y := le_trans (hq0 0) (hqY 0)
  have hsq2 : Summable (fun m => q m ^ 2) := by
    refine Summable.of_nonneg_of_le (fun m => sq_nonneg (q m)) (fun m => ?_)
      (hsq.mul_left Y)
    have := hqY m
    nlinarith [hq0 m]
  have hover : Summable (fun m => q m * (Y - q m)) := by
    have heq : (fun m => q m * (Y - q m)) = fun m => Y * q m - q m ^ 2 := by
      funext m
      ring
    rw [heq]
    exact (hsq.mul_left Y).sub hsq2
  have hover_le : (∑' m : ℤ, q m * (Y - q m)) ≤
      (Y - q 0) * (2 * Y) := by
    have hsumSq : q 0 ^ 2 ≤ ∑' m : ℤ, q m ^ 2 :=
      hsq2.le_tsum 0 (fun m _ => sq_nonneg (q m))
    have hsum : (∑' m : ℤ, q m * (Y - q m))
        = Y ^ 2 - ∑' m : ℤ, q m ^ 2 := by
      calc
        (∑' m : ℤ, q m * (Y - q m))
            = ∑' m : ℤ, (Y * q m - q m ^ 2) := by
                apply tsum_congr
                intro m
                ring
        _ = (∑' m : ℤ, Y * q m) - ∑' m : ℤ, q m ^ 2 :=
              (hsq.mul_left Y).tsum_sub hsq2
        _ = Y ^ 2 - ∑' m : ℤ, q m ^ 2 := by
              rw [tsum_mul_left, hYdef]
              ring
    rw [hsum]
    have hq0Y := hqY 0
    nlinarith [hq0 0]
  have htail : Y - q 0 ≤ 4 * C * Real.exp (-(alpha / 2) * P) := by
    have herr := Periodization.periodization_error_le (z := y) (C := C) (a := alpha)
      (H := P) (s := u) halpha hy0 hyb hP hq hu
    have hzero : q 0 = y u := by simp [hqdef]
    rw [hYdef, hzero]
    exact (le_abs_self _).trans herr
  have htail0 : 0 ≤ Y - q 0 := sub_nonneg.mpr (hqY 0)
  have htwoY : 0 ≤ 2 * Y := by positivity
  calc
    (∑' m : ℤ, y (u - m * P) *
        ((∑' j : ℤ, y (u - j * P)) - y (u - m * P)))
        = ∑' m : ℤ, q m * (Y - q m) := by simp only [hqdef, hYdef]
    _ ≤ (Y - q 0) * (2 * Y) := hover_le
    _ ≤ (4 * C * Real.exp (-(alpha / 2) * P)) * (2 * Y) :=
      mul_le_mul_of_nonneg_right htail htwoY
    _ = 8 * C * Real.exp (-(alpha / 2) * P) *
        ∑' j : ℤ, y (u - j * P) := by rw [← hYdef]; ring

/-- The periodization of a pointwise lower comparison is the corresponding
lower comparison between the two periodized series. -/
theorem tsum_lower_comparison {y Kstar : ℝ → ℝ} {P b0 r : ℝ}
    (hy : Summable fun m : ℤ => y (r - m * P))
    (hK : Summable fun m : ℤ => Kstar (r - m * P))
    (hlower : ∀ s, b0 * y s ≤ Kstar s) :
    b0 * (∑' m : ℤ, y (r - m * P)) ≤ ∑' m : ℤ, Kstar (r - m * P) := by
  rw [← tsum_mul_left]
  exact (hy.mul_left b0).tsum_le_tsum (fun m => hlower _) hK

/-- **Front positivity from lower comparison and relative error.**

This is the inequality

`KP >= sum Kstar - E Y >= (b0 - E) Y >= 0`

used in the TeX proof. -/
theorem periodized_front_nonneg_of_error
    {y Kstar KP : ℝ → ℝ} {P b0 E : ℝ}
    (hy0 : ∀ s, 0 ≤ y s) (hb0 : 0 ≤ b0) (hE : E ≤ b0)
    (hlower : ∀ s, b0 * y s ≤ Kstar s)
    (hySumm : ∀ r, Summable fun m : ℤ => y (r - m * P))
    (hKSumm : ∀ r, Summable fun m : ℤ => Kstar (r - m * P))
    (herr : ∀ r,
      |KP r - ∑' m : ℤ, Kstar (r - m * P)|
        ≤ E * ∑' m : ℤ, y (r - m * P)) :
    ∀ r, 0 ≤ KP r := by
  intro r
  have hY0 : 0 ≤ ∑' m : ℤ, y (r - m * P) := tsum_nonneg fun m => hy0 _
  have hsum : b0 * (∑' m : ℤ, y (r - m * P))
      ≤ ∑' m : ℤ, Kstar (r - m * P) :=
    tsum_lower_comparison (hySumm r) (hKSumm r) hlower
  have herrLower : -(E * ∑' m : ℤ, y (r - m * P))
      ≤ KP r - ∑' m : ℤ, Kstar (r - m * P) :=
    neg_le_of_abs_le (herr r)
  have hcoeff : E * (∑' m : ℤ, y (r - m * P))
      ≤ b0 * ∑' m : ℤ, y (r - m * P) :=
    mul_le_mul_of_nonneg_right hE hY0
  linarith

/-- The paper's geometric positivity branch, stated directly with the
curvatures used by `ModelOrbitDefect.Config.hcurvNonnegU`. -/
theorem hairpin_and_modelCurvature_nonneg_of_error
    {y yd : ℝ → ℝ} {P b0 E : ℝ}
    (hy0 : ∀ s, 0 ≤ y s) (hb0 : 0 ≤ b0) (hE : E ≤ b0)
    (hlower : ∀ s, b0 * y s ≤ ModelOrbitDefect.hairpinCurvature y yd s)
    (hySumm : ∀ r, Summable fun m : ℤ => y (r - m * P))
    (hKSumm : ∀ r, Summable fun m : ℤ =>
      ModelOrbitDefect.hairpinCurvature y yd (r - m * P))
    (herr : ∀ r,
      |ModelOrbitDefect.modelCurvature y yd P r
          - ∑' m : ℤ, ModelOrbitDefect.hairpinCurvature y yd (r - m * P)|
        ≤ E * ModelOrbitDefect.periodizedPulse y P r) :
    (∀ s, 0 ≤ ModelOrbitDefect.hairpinCurvature y yd s) ∧
      ∀ r, 0 ≤ ModelOrbitDefect.modelCurvature y yd P r := by
  constructor
  · intro s
    exact le_trans (mul_nonneg hb0 (hy0 s)) (hlower s)
  · apply periodized_front_nonneg_of_error hy0 hb0 hE hlower hySumm hKSumm
    simpa [ModelOrbitDefect.periodizedPulse] using herr

/-- **Large separation makes both curvatures nonnegative.**  This is the
positivity paragraph of the proposition *Exact two-cap pairs*, with an
explicit sufficient separation inequality.  The assumptions are precisely
the exponential localization and relative derivative data consumed by the
front-periodization estimate, the strip bound needed by `G`, and the
hairpin lower comparison `Kstar >= b0*y`.

The conclusion has exactly the type of the geometric (second) branch of
`ModelOrbitDefect.Config.hcurvNonnegU`. -/
theorem hairpin_and_modelCurvature_nonneg_of_large_period
    {y yd : ℝ → ℝ} {C alpha P D a b0 : ℝ}
    (halpha : 0 < alpha) (hP : 0 < P)
    (hq : Real.exp (-alpha * P) ≤ 1 / 2)
    (hy0 : ∀ s, 0 ≤ y s)
    (hyb : ∀ s, y s ≤ C * Real.exp (-alpha * |s|))
    (hD : 0 ≤ D) (hyd : ∀ s, |yd s| ≤ D * y s)
    (ha0 : 0 ≤ a) (ha1 : a < 1)
    (hYa : ∀ u, (∑' m : ℤ, y (u - m * P)) ≤ a)
    (hb0 : 0 ≤ b0)
    (hlower : ∀ s, b0 * y s ≤ ModelOrbitDefect.hairpinCurvature y yd s)
    (hKSumm : ∀ r, Summable fun m : ℤ =>
      ModelOrbitDefect.hairpinCurvature y yd (r - m * P))
    (hsep : 8 * FrontPeriodization.lipConst a * D * C *
      Real.exp (-(alpha / 2) * P) ≤ b0) :
    (∀ s, 0 ≤ ModelOrbitDefect.hairpinCurvature y yd s) ∧
      ∀ r, 0 ≤ ModelOrbitDefect.modelCurvature y yd P r := by
  have hC : 0 ≤ C := Periodization.const_nonneg hy0 hyb
  have habs : ∀ s, |y s| ≤ C * Real.exp (-alpha * |s|) := fun s => by
    rw [abs_of_nonneg (hy0 s)]
    exact hyb s
  have hySumm : ∀ r, Summable fun m : ℤ => y (r - m * P) := fun r =>
    FrontPeriodizationIntegral.summable_translates halpha hP habs r
  have hisolated : ∀ s, 0 ≤ ModelOrbitDefect.hairpinCurvature y yd s := fun s =>
    le_trans (mul_nonneg hb0 (hy0 s)) (hlower s)
  refine ⟨hisolated, ?_⟩
  have hcell : ∀ u, |u| ≤ P / 2 → 0 ≤ ModelOrbitDefect.modelCurvature y yd P u := by
    intro u hu
    have hover := overlapDensity_le_cell halpha hP hq hy0 hyb hu
    have herr0 := FrontPeriodizationIntegral.front_error_tsum_le
      (y := y) (yp := yd) (C := C) (alpha := alpha) (P := P) (D := D) (a := a)
      halpha hP hy0 hyb hD hyd ha0 ha1 hYa u
    have hLip0 : 0 ≤ FrontPeriodization.lipConst a :=
      FrontPeriodization.lipConst_nonneg ha0 ha1
    have hfac0 : 0 ≤ FrontPeriodization.lipConst a * D := mul_nonneg hLip0 hD
    have herrRaw :
        |ModelOrbitDefect.modelCurvature y yd P u
            - ∑' m : ℤ, ModelOrbitDefect.hairpinCurvature y yd (u - m * P)|
          ≤ FrontPeriodization.lipConst a * D *
              ∑' m : ℤ, y (u - m * P) *
                ((∑' j : ℤ, y (u - j * P)) - y (u - m * P)) := by
      simpa [ModelOrbitDefect.modelCurvature, ModelOrbitDefect.periodizedPulse,
        ModelOrbitDefect.hairpinCurvature] using herr0
    have herr :
        |ModelOrbitDefect.modelCurvature y yd P u
            - ∑' m : ℤ, ModelOrbitDefect.hairpinCurvature y yd (u - m * P)|
          ≤ (8 * FrontPeriodization.lipConst a * D * C *
              Real.exp (-(alpha / 2) * P)) *
              ∑' m : ℤ, y (u - m * P) := by
      have hmul := mul_le_mul_of_nonneg_left hover hfac0
      refine herrRaw.trans ?_
      calc
        FrontPeriodization.lipConst a * D *
              ∑' m : ℤ, y (u - m * P) *
                ((∑' j : ℤ, y (u - j * P)) - y (u - m * P))
            ≤ FrontPeriodization.lipConst a * D *
                (8 * C * Real.exp (-(alpha / 2) * P) *
                  ∑' m : ℤ, y (u - m * P)) := hmul
        _ = (8 * FrontPeriodization.lipConst a * D * C *
              Real.exp (-(alpha / 2) * P)) *
              ∑' m : ℤ, y (u - m * P) := by ring
    have hY0 : 0 ≤ ∑' m : ℤ, y (u - m * P) := tsum_nonneg fun m => hy0 _
    have hsum : b0 * (∑' m : ℤ, y (u - m * P)) ≤
        ∑' m : ℤ, ModelOrbitDefect.hairpinCurvature y yd (u - m * P) :=
      tsum_lower_comparison (hySumm u) (hKSumm u) hlower
    have herrLower := neg_le_of_abs_le herr
    have hcoeff := mul_le_mul_of_nonneg_right hsep hY0
    linarith
  have hper : Function.Periodic (ModelOrbitDefect.modelCurvature y yd P) P := by
    simpa [ModelOrbitDefect.modelCurvature, ModelOrbitDefect.periodizedPulse] using
      PeriodizedTurning.periodic_frontCurv y yd P
  intro r
  obtain ⟨v, hv, heq⟩ := hper.exists_mem_Ico₀ hP r
  rw [show ModelOrbitDefect.modelCurvature y yd P r =
    ModelOrbitDefect.modelCurvature y yd P v from heq]
  rcases le_or_gt v (P / 2) with h | h
  · exact hcell v (by rw [abs_of_nonneg hv.1]; exact h)
  · have hshift := hper (v - P)
    simp only [sub_add_cancel] at hshift
    rw [hshift]
    refine hcell (v - P) ?_
    rw [abs_le]
    constructor <;> linarith [hv.2]

/-- **Eventually, the paper's geometric positivity branch holds.**  This
packages the analytic statement "choose the cap separation sufficiently
large" in the form needed during construction of `ModelOrbitDefect.Config`.
The strip bound and summability of the curvature translates remain explicit
inputs because they belong to the surrounding periodized-pulse package. -/
theorem exists_threshold_hairpin_and_modelCurvature_nonneg
    {y yd : ℝ → ℝ} {C alpha D a b0 : ℝ}
    (halpha : 0 < alpha) (hb0 : 0 < b0)
    (hy0 : ∀ s, 0 ≤ y s)
    (hyb : ∀ s, y s ≤ C * Real.exp (-alpha * |s|))
    (hD : 0 ≤ D) (hyd : ∀ s, |yd s| ≤ D * y s)
    (ha0 : 0 ≤ a) (ha1 : a < 1)
    (hlower : ∀ s, b0 * y s ≤ ModelOrbitDefect.hairpinCurvature y yd s) :
    ∃ P0 : ℝ, 0 < P0 ∧ ∀ P ≥ P0,
      (∀ u, (∑' m : ℤ, y (u - m * P)) ≤ a) →
      (∀ r, Summable fun m : ℤ =>
        ModelOrbitDefect.hairpinCurvature y yd (r - m * P)) →
      ((∀ s, 0 ≤ ModelOrbitDefect.hairpinCurvature y yd s) ∧
        ∀ r, 0 ≤ ModelOrbitDefect.modelCurvature y yd P r) := by
  have hC : 0 ≤ C := Periodization.const_nonneg hy0 hyb
  obtain ⟨P0, hP0, hthreshold⟩ :=
    exists_largePeriod_positivity_threshold halpha hb0 ha0 ha1 hD hC
  refine ⟨P0, hP0, fun P hPP hYa hKSumm => ?_⟩
  obtain ⟨hP, hq, hsep⟩ := hthreshold P hPP
  exact hairpin_and_modelCurvature_nonneg_of_large_period halpha hP hq hy0 hyb
    hD hyd ha0 ha1 hYa hb0.le hlower hKSumm hsep

end FrontPeriodizationPositivity
