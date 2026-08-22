import Mathlib
import UnitTangentIterates.ModelOrbitDefect
import UnitTangentIterates.PeriodizationDeriv

/-!
# The rear period depends continuously on the separation

The rear period of the model front of separation `H` built from a pulse `y` is

`Q(H) = ∫₀^H cos δ_H,  δ_H = arcsin Y_H,  Y_H(s) = ∑_{m ∈ ℤ} y(s - mH)`,

the rear arclength of one front period.  The recursion `Q(H_{n+1}) = H_n` of the
lemma *Large-separation threshold* asks that `Q` take every large value, so it
asks first of all that `Q` be continuous.

`PeriodizationDeriv.hasDerivAt_periodization_period` differentiates the
periodization in the period, so `H ↦ Y_H(s)` is continuous for each fixed `s`;
the integrand is bounded by one and the domain of integration moves
continuously, so dominated convergence gives the continuity of `Q`
(`continuousAt_rearPeriod`).  Since `H - π/2 ≤ Q(H) ≤ H` for the pulses at hand,
the intermediate value theorem then solves the recursion
(`exists_rearPeriod_eq`).

-/

noncomputable section

open Real MeasureTheory Filter Topology Set

namespace ModelPeriodContinuity

open ModelOrbitDefect

variable {y y' : ℝ → ℝ} {C alpha : ℝ}

/-- The rear period of the model front of separation `H`. -/
def rearPeriod (y : ℝ → ℝ) (H : ℝ) : ℝ := modelRearArclength (periodizedPulse y H) H

/-- **The periodization is continuous in the period**, at every positive period
and at every fixed point of the line. -/
theorem continuousAt_periodization (ha : 0 < alpha)
    (hz : ∀ x, HasDerivAt y (y' x) x)
    (hzb : ∀ x, |y x| ≤ C * Real.exp (-alpha * |x|))
    (hz'b : ∀ x, |y' x| ≤ C * Real.exp (-alpha * |x|))
    {Hstar : ℝ} (hH : 0 < Hstar) (s : ℝ) :
    ContinuousAt (fun t => ∑' m : ℤ, y (s - m * t)) Hstar :=
  (PeriodizationDeriv.hasDerivAt_periodization_period (H₀ := Hstar / 2) (s := s) ha
    (by linarith) hz hzb hz'b (by linarith)).continuousAt

/-- The speed of the rear at a point of the front, as a function of the
separation. -/
private def speedAt (y : ℝ → ℝ) (s H : ℝ) : ℝ :=
  Real.cos (modelSteering (periodizedPulse y H) s)

private theorem continuousAt_speedAt (ha : 0 < alpha)
    (hz : ∀ x, HasDerivAt y (y' x) x)
    (hzb : ∀ x, |y x| ≤ C * Real.exp (-alpha * |x|))
    (hz'b : ∀ x, |y' x| ≤ C * Real.exp (-alpha * |x|))
    {Hstar : ℝ} (hH : 0 < Hstar) (s : ℝ) :
    ContinuousAt (fun H => speedAt y s H) Hstar := by
  have h := continuousAt_periodization (y' := y') ha hz hzb hz'b hH s
  exact ((Real.continuous_cos.comp Real.continuous_arcsin).continuousAt).comp h

private theorem abs_speedAt_le (s H : ℝ) : |speedAt y s H| ≤ 1 :=
  Real.abs_cos_le_one _

/-- The rear period as the integral of an indicator over the line. -/
private theorem rearPeriod_eq_integral {H : ℝ} (hH : 0 ≤ H) :
    rearPeriod y H = ∫ s, Set.indicator (Set.Ioc (0:ℝ) H) (fun u => speedAt y u H) s := by
  have hmeas : MeasurableSet (Set.Ioc (0:ℝ) H) := measurableSet_Ioc
  rw [MeasureTheory.integral_indicator hmeas]
  rw [rearPeriod, modelRearArclength, RearTrack.rearArclength,
    intervalIntegral.integral_of_le hH]
  rfl

/-- **The rear period is continuous in the separation.** -/
theorem continuousAt_rearPeriod (ha : 0 < alpha) (hyc : Continuous y)
    (hz : ∀ x, HasDerivAt y (y' x) x)
    (hzb : ∀ x, |y x| ≤ C * Real.exp (-alpha * |x|))
    (hz'b : ∀ x, |y' x| ≤ C * Real.exp (-alpha * |x|))
    {Hstar : ℝ} (hH : 0 < Hstar) :
    ContinuousAt (rearPeriod y) Hstar := by
  -- the continuity of every periodization involved
  have hYcont : ∀ H : ℝ, 0 < H → Continuous (periodizedPulse y H) := by
    intro H hHpos
    exact PeriodizedTurning.continuous_periodization (alpha := alpha) (P := H) (C := C)
      ha hHpos hyc hzb
  -- the integrand, as a function of the separation
  set F : ℝ → ℝ → ℝ := fun H s =>
    Set.indicator (Set.Ioc (0:ℝ) H) (fun u => speedAt y u H) s with hFdef
  set bound : ℝ → ℝ := Set.indicator (Set.Ioc (0:ℝ) (Hstar + 1)) (fun _ => (1:ℝ))
    with hbdef
  have hmeasF : ∀ H : ℝ, 0 < H → AEStronglyMeasurable (F H) volume := by
    intro H hHpos
    refine (Continuous.aestronglyMeasurable ?_).indicator measurableSet_Ioc
    exact Real.continuous_cos.comp (Real.continuous_arcsin.comp (hYcont H hHpos))
  have hboundint : Integrable bound volume := by
    rw [hbdef]
    exact (integrableOn_const (measure_Ioc_lt_top).ne).integrable_indicator measurableSet_Ioc
  -- the rear period is the integral of `F H`
  have hQ : ∀ H : ℝ, 0 < H → rearPeriod y H = ∫ s, F H s :=
    fun H hHpos => rearPeriod_eq_integral hHpos.le
  have hlim : Tendsto (fun H => ∫ s, F H s) (𝓝 Hstar) (𝓝 (∫ s, F Hstar s)) := by
    refine MeasureTheory.tendsto_integral_filter_of_dominated_convergence bound ?_ ?_
      hboundint ?_
    · filter_upwards [eventually_gt_nhds hH] with H hHpos using hmeasF H hHpos
    · filter_upwards [eventually_lt_nhds (show Hstar < Hstar + 1 by linarith)] with H hHlt
      refine Filter.Eventually.of_forall fun s => ?_
      by_cases hs : s ∈ Set.Ioc (0:ℝ) H
      · have hs' : s ∈ Set.Ioc (0:ℝ) (Hstar + 1) := ⟨hs.1, le_of_lt (lt_of_le_of_lt hs.2 hHlt)⟩
        rw [hFdef, hbdef]
        simp only [Set.indicator_of_mem hs, Set.indicator_of_mem hs']
        exact abs_speedAt_le s H
      · rw [hFdef]
        simp only [Set.indicator_of_notMem hs, norm_zero]
        rw [hbdef]
        by_cases hs2 : s ∈ Set.Ioc (0:ℝ) (Hstar + 1)
        · simp [Set.indicator_of_mem hs2]
        · simp [Set.indicator_of_notMem hs2]
    · have hne : ∀ᵐ s : ℝ, s ≠ Hstar := by
        have hz0 : volume ({Hstar} : Set ℝ) = 0 := by simp
        filter_upwards [MeasureTheory.compl_mem_ae_iff.mpr hz0] with s hs
        simpa using hs
      filter_upwards [hne] with s hsne
      by_cases hs0 : 0 < s
      swap
      · push_neg at hs0
        have h0 : ∀ H : ℝ, F H s = 0 := by
          intro H
          rw [hFdef]
          exact Set.indicator_of_notMem (fun hmem => absurd hmem.1 (not_lt.mpr hs0)) _
        simp only [h0]
        exact tendsto_const_nhds
      rcases lt_trichotomy s Hstar with hlt | heq | hgt
      · have heq' : ∀ᶠ H in 𝓝 Hstar, F H s = speedAt y s H := by
          filter_upwards [eventually_gt_nhds hlt] with H hHs
          have hmem : s ∈ Set.Ioc (0:ℝ) H := ⟨hs0, hHs.le⟩
          simp only [hFdef, Set.indicator_of_mem hmem]
        have hFstar : F Hstar s = speedAt y s Hstar := by
          have hmem : s ∈ Set.Ioc (0:ℝ) Hstar := ⟨hs0, hlt.le⟩
          simp only [hFdef, Set.indicator_of_mem hmem]
        rw [hFstar]
        refine Tendsto.congr' (Filter.EventuallyEq.symm heq') ?_
        exact continuousAt_speedAt (y' := y') ha hz hzb hz'b hH s
      · exact absurd heq hsne
      · have heq' : ∀ᶠ H in 𝓝 Hstar, F H s = 0 := by
          filter_upwards [eventually_lt_nhds hgt] with H hHs
          have hmem : s ∉ Set.Ioc (0:ℝ) H := fun hm => absurd hm.2 (not_le.mpr hHs)
          simp only [hFdef, Set.indicator_of_notMem hmem]
        have hFstar : F Hstar s = 0 := by
          have hmem : s ∉ Set.Ioc (0:ℝ) Hstar := fun hm => absurd hm.2 (not_le.mpr hgt)
          simp only [hFdef, Set.indicator_of_notMem hmem]
        rw [hFstar]
        exact Tendsto.congr' (Filter.EventuallyEq.symm heq') tendsto_const_nhds
  -- transport the limit back to the rear period
  have hev : rearPeriod y =ᶠ[𝓝 Hstar] fun H => ∫ s, F H s := by
    filter_upwards [eventually_gt_nhds hH] with H hHpos using hQ H hHpos
  rw [ContinuousAt, hQ Hstar hH]
  exact Tendsto.congr' (Filter.EventuallyEq.symm hev) hlim

/-- **The rear period is at most the front period.** -/
theorem rearPeriod_le (ha : 0 < alpha) (hyc : Continuous y)
    (hzb : ∀ x, |y x| ≤ C * Real.exp (-alpha * |x|)) {H : ℝ} (hH : 0 < H) :
    rearPeriod y H ≤ H := by
  have hYc : Continuous (periodizedPulse y H) :=
    PeriodizedTurning.continuous_periodization (alpha := alpha) (P := H) (C := C)
      ha hH hyc hzb
  exact ArclengthInverse.rearArclength_le_of_period
    (δ := modelSteering (periodizedPulse y H)) (continuous_modelSteering hYc) hH.le

/-- **The recursion `Q(H') = H` of the lemma *Large-separation threshold* is
solvable**: the rear period takes every value `t > 0`, at a separation between
`t` and `2t`. -/
theorem exists_rearPeriod_eq (ha : 0 < alpha) (hyc : Continuous y)
    (hz : ∀ x, HasDerivAt y (y' x) x)
    (hzb : ∀ x, |y x| ≤ C * Real.exp (-alpha * |x|))
    (hz'b : ∀ x, |y' x| ≤ C * Real.exp (-alpha * |x|))
    {t : ℝ} (hge : t ≤ rearPeriod y (2 * t)) (ht : 0 < t) :
    ∃ H, t ≤ H ∧ H ≤ 2 * t ∧ rearPeriod y H = t := by
  have hcont : ContinuousOn (rearPeriod y) (Set.Icc t (2 * t)) := fun x hx =>
    (continuousAt_rearPeriod (y' := y') ha hyc hz hzb hz'b
      (lt_of_lt_of_le ht hx.1)).continuousWithinAt
  have h1 : rearPeriod y t ≤ t := rearPeriod_le ha hyc hzb ht
  obtain ⟨H, hH, hHeq⟩ :=
    intermediate_value_Icc (by linarith : t ≤ 2 * t) hcont (Set.mem_Icc.mpr ⟨h1, hge⟩)
  exact ⟨H, hH.1, hH.2, hHeq⟩

end ModelPeriodContinuity
