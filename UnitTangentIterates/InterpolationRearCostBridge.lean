import Mathlib
import UnitTangentIterates.RearOwnTangentialCost
import UnitTangentIterates.JacobiNormalRateBounds
import UnitTangentIterates.RearCostDensity
import UnitTangentIterates.InterpolationFrame
import UnitTangentIterates.SelectedInverseSteeringSmooth
import UnitTangentIterates.InterpolationEstimate
import UnitTangentIterates.SelectedInversePathGeometry

/-!
# Quantitative cost bridge for interpolation-selected rears

This file packages the estimates which are independent of the remaining
construction of the concrete interpolation steering family.  Once its inverse
Jacobi equation and source derivative bound are supplied, the normal-rate
`S₀,S₁,S₂` estimates follow.  Choosing the rear density proportional to the
front cost density by `rearCostConst` then discharges all three fixed-point
inequalities used by the gauge-marked tube construction.
-/

noncomputable section

namespace InterpolationRearCostBridge

open Set
open CurvatureInterpolation InterpolationNormal InterpolationEstimate
  SelectedInversePathGeometry

/-- Normalize a source bound by a common stopped time profile.  No division
by the density is used, so zeros at the stopped endpoints cause no issue. -/
theorem source_bound_of_common_profile
    {gS : ℝ → ℝ → ℝ} {w : ℝ → ℝ} {D C d : ℝ}
    (hw : ∀ t, 0 ≤ w t)
    (hgS : ∀ t x, |gS t x| ≤ D * w t)
    (hDC : D ≤ d * C) :
    ∀ t x, |gS t x| ≤ d * (C * w t) := by
  intro t x
  calc
    |gS t x| ≤ D * w t := hgS t x
    _ ≤ (d * C) * w t := mul_le_mul_of_nonneg_right hDC (hw t)
    _ = d * (C * w t) := by ring

theorem source_bound_of_common_profile_eq_density
    {gS : ℝ → ℝ → ℝ} {w mF : ℝ → ℝ} {D C d : ℝ}
    (hw : ∀ t, 0 ≤ w t) (hmF : ∀ t, mF t = C * w t)
    (hgS : ∀ t x, |gS t x| ≤ D * w t)
    (hDC : D ≤ d * C) :
    ∀ t x, |gS t x| ≤ d * mF t := by
  intro t x
  rw [hmF t]
  exact source_bound_of_common_profile hw hgS hDC t x

/-- Shape of the spatial derivative of the transported, profiled front-normal
source. -/
def profiledSourceShape
    (N NS delta K sf : ℝ → ℝ → ℝ) (t x : ℝ) : ℝ :=
  NS t (sf t x) / Real.cos (delta t (sf t x)) ^ 2 +
    N t (sf t x) * Real.sin (delta t (sf t x)) *
      (K t (sf t x) - Real.sin (delta t (sf t x))) /
        Real.cos (delta t (sf t x)) ^ 3

/-- The source derivative factors through the time profile before any bounds
are taken. -/
theorem hasDerivAt_profiled_source
    {N NS delta K sf : ℝ → ℝ → ℝ} {w t x : ℝ}
    (hN : HasDerivAt (N t) (NS t (sf t x)) (sf t x))
    (hd : HasDerivAt (delta t)
      (K t (sf t x) - Real.sin (delta t (sf t x))) (sf t x))
    (hsf : HasDerivAt (sf t)
      (1 / Real.cos (delta t (sf t x))) x)
    (hcos : Real.cos (delta t (sf t x)) ≠ 0) :
    HasDerivAt
      (fun y => w * N t (sf t y) / Real.cos (delta t (sf t y)))
      (w * profiledSourceShape N NS delta K sf t x) x := by
  have hNc := hN.comp x hsf
  have hdc := hd.comp x hsf
  have hcosd := hdc.cos
  have hquot := (hNc.const_mul w).div hcosd hcos
  apply hquot.congr_deriv
  simp only [profiledSourceShape, Function.comp_apply]
  field_simp
  ring

/-- Explicit global envelope for the profiled source shape. -/
theorem abs_profiledSourceShape_le
    {N NS delta K sf : ℝ → ℝ → ℝ}
    {t x v0 NSmax Nmax kh Kx : ℝ}
    (hv0 : 0 < v0)
    (hcos : v0 ≤ Real.cos (delta t (sf t x)))
    (hNS : |NS t (sf t x)| ≤ NSmax)
    (hN : |N t (sf t x)| ≤ Nmax)
    (hsin : |Real.sin (delta t (sf t x))| ≤ kh)
    (hKx : |(K t (sf t x) - Real.sin (delta t (sf t x))) /
      Real.cos (delta t (sf t x)) ^ 3| ≤ Kx)
    (hNS0 : 0 ≤ NSmax) (hN0 : 0 ≤ Nmax) (hkh0 : 0 ≤ kh) (hKx0 : 0 ≤ Kx) :
    |profiledSourceShape N NS delta K sf t x| ≤
      NSmax / v0 ^ 2 + Nmax * kh * Kx := by
  have hcpos : 0 < Real.cos (delta t (sf t x)) := hv0.trans_le hcos
  have hc2 : v0 ^ 2 ≤ Real.cos (delta t (sf t x)) ^ 2 := by nlinarith
  have hfirst : |NS t (sf t x) / Real.cos (delta t (sf t x)) ^ 2| ≤
      NSmax / v0 ^ 2 := by
    rw [abs_div, abs_of_nonneg (sq_nonneg (Real.cos (delta t (sf t x))))]
    exact div_le_div₀ hNS0 hNS (by positivity) hc2
  have hsecond : |N t (sf t x) * Real.sin (delta t (sf t x)) *
      (K t (sf t x) - Real.sin (delta t (sf t x))) /
        Real.cos (delta t (sf t x)) ^ 3| ≤ Nmax * kh * Kx := by
    rw [show N t (sf t x) * Real.sin (delta t (sf t x)) *
        (K t (sf t x) - Real.sin (delta t (sf t x))) /
          Real.cos (delta t (sf t x)) ^ 3 =
      N t (sf t x) * Real.sin (delta t (sf t x)) *
        ((K t (sf t x) - Real.sin (delta t (sf t x))) /
          Real.cos (delta t (sf t x)) ^ 3) by ring]
    rw [abs_mul, abs_mul]
    exact mul_le_mul (mul_le_mul hN hsin (abs_nonneg _) hN0) hKx
      (abs_nonneg _) (mul_nonneg hN0 hkh0)
  exact (abs_add_le _ _).trans (add_le_add hfirst hsecond)

/-- Convex interpolation preserves a common positive curvature strip. -/
theorem kappaInterp_mem_common_strip {k0 k1 : ℝ → ℝ} {kh t s : ℝ}
    (hk0pos : ∀ x, 0 < k0 x) (hk1pos : ∀ x, 0 < k1 x)
    (hk0le : ∀ x, k0 x ≤ kh) (hk1le : ∀ x, k1 x ≤ kh)
    (ht : t ∈ Icc (0 : ℝ) 1) :
    kappaInterp k0 k1 t s ∈ Icc (0 : ℝ) kh :=
  ⟨(kappaInterp_pos hk0pos hk1pos ht s).le,
    kappaInterp_le hk0le hk1le ht s⟩

/-- Every slice of the explicit curvature interpolation on `t ∈ [0,1]`
admits its periodic selected steering in the same common strip. -/
theorem exists_selectedSteering_kappaInterp
    {k0 k1 : ℝ → ℝ} {P kh : ℝ}
    (hP : 0 < P) (hkh0 : 0 ≤ kh) (hkh1 : kh < 1)
    (hk0c : Continuous k0) (hk1c : Continuous k1)
    (hk0per : Function.Periodic k0 P) (hk1per : Function.Periodic k1 P)
    (hk0pos : ∀ s, 0 < k0 s) (hk1pos : ∀ s, 0 < k1 s)
    (hk0le : ∀ s, k0 s ≤ kh) (hk1le : ∀ s, k1 s ≤ kh) :
    ∀ t ∈ Icc (0 : ℝ) 1, ∃ delta : ℝ → ℝ,
      Function.Periodic delta P ∧
      (∀ s, delta s ∈ Icc (0 : ℝ) (Real.arcsin kh)) ∧
      (∀ s, HasDerivAt delta
        (kappaInterp k0 k1 t s - Real.sin (delta s)) s) := by
  intro t ht
  have hKc : Continuous (kappaInterp k0 k1 t) :=
    continuous_kappaInterp hk0c hk1c
  have hKper : Function.Periodic (kappaInterp k0 k1 t) P := fun s => by
    simp [kappaInterp, hk0per s, hk1per s]
  obtain ⟨delta, hper, hstrip, -, hode⟩ :=
    SteeringExistence.exists_periodic_steering hP hKc hKper hkh0 hkh1.le
      (fun s => (kappaInterp_mem_common_strip hk0pos hk1pos hk0le hk1le ht).1)
      (fun s => (kappaInterp_mem_common_strip hk0pos hk1pos hk0le hk1le ht).2)
  exact ⟨delta, hper, hstrip, hode⟩

/-- The pointwise normal-rate estimates and their comparisons with the front
cost density. -/
structure JacobiCostCertificate
    (en enS enSS : ℝ → ℝ → ℝ) (S0 D m : ℝ → ℝ) (c d : ℝ) : Prop where
  normal0 : ∀ t x, |en t x| ≤ S0 t
  normal1 : ∀ t x, |enS t x| ≤ 2 * S0 t
  normal2 : ∀ t x, |enSS t x| ≤ D t + 2 * S0 t
  cost0 : ∀ t, S0 t ≤ c * m t
  cost1 : ∀ t, 2 * S0 t ≤ 2 * c * m t
  cost2 : ∀ t, D t + 2 * S0 t ≤ (d + 2 * c) * m t

/-- Construct the complete Jacobi cost certificate from the inverse Jacobi ODE
and one derivative bound for its source. -/
theorem JacobiCostCertificate.of_inverseJacobi
    {en enS enSS g gS : ℝ → ℝ → ℝ} {S0 D m : ℝ → ℝ} {c d : ℝ}
    (hgS : ∀ t x, HasDerivAt (g t) (gS t x) x)
    (hjacobi : ∀ t x, HasDerivAt (en t) (g t x - en t x) x)
    (henS : ∀ t x, HasDerivAt (en t) (enS t x) x)
    (henSS : ∀ t x, HasDerivAt (enS t) (enSS t x) x)
    (hgbd : ∀ t x, |g t x| ≤ S0 t) (henbd : ∀ t x, |en t x| ≤ S0 t)
    (hgSbd : ∀ t x, |gS t x| ≤ D t)
    (hS0m : ∀ t, S0 t ≤ c * m t) (hDm : ∀ t, D t ≤ d * m t) :
    JacobiCostCertificate en enS enSS S0 D m c d := by
  rcases JacobiNormalRateBounds.jacobi_normal_rate_bounds
    hgS hjacobi henS henSS hgbd henbd hgSbd with ⟨h0, h1, h2⟩
  rcases JacobiNormalRateBounds.jacobi_cost_constants hS0m hDm with ⟨hc0, hc1, hc2⟩
  exact ⟨h0, h1, h2, hc0, hc1, hc2⟩

/-- The three nonlinear density inequalities required by the rear-family tube
construction. -/
structure RearDensityCertificate
    (kh khat kappa2 ell dd mF Dd M : ℝ) : Prop where
  dominates_normal : mF / Real.sqrt (1 - kh ^ 2) ≤
    RearCostDensity.rearCostConst kh khat kappa2 ell dd * mF
  first_flow : 2 * (mF / Real.sqrt (1 - kh ^ 2)) *
      GaugeFlowDerivCost.costP1 ell khat M ≤
    RearCostDensity.rearCostConst kh khat kappa2 ell dd * mF
  second_flow :
    (Dd + 2 * (mF / Real.sqrt (1 - kh ^ 2))) *
        GaugeFlowDerivCost.costP1 ell khat M ^ 2 +
      2 * (mF / Real.sqrt (1 - kh ^ 2)) *
        GaugeFlowDerivCost.costG1 ell khat kappa2 M ≤
    RearCostDensity.rearCostConst kh khat kappa2 ell dd * mF

/-- `rearCostConst` simultaneously discharges all rear-density inequalities as
soon as the total chosen density is at most one. -/
theorem RearDensityCertificate.of_rearCostConst
    {kh khat kappa2 ell dd mF Dd M : ℝ}
    (hmF : 0 ≤ mF) (hell : 0 ≤ ell) (hkhat : 0 ≤ khat)
    (hk2 : 0 ≤ kappa2) (hDd : Dd ≤ dd * mF) (hDd0 : 0 ≤ Dd)
    (hM0 : 0 ≤ M) (hM : M ≤ 1) :
    RearDensityCertificate kh khat kappa2 ell dd mF Dd M := by
  exact ⟨RearCostDensity.mge_of_rearCostConst hmF,
    RearCostDensity.supA_of_rearCostConst hmF hell hkhat hM,
    RearCostDensity.supB_of_rearCostConst hmF hell hkhat hk2 hDd hDd0 hM0 hM⟩

/-- The genuinely family-specific bounds left after the preceding two
certificates.  These are the quantities to be supplied from the concrete C⁴
curvature interpolation and selected-steering construction. -/
structure ConcreteInterpolationBounds
    (Kx Rb m : ℝ → ℝ) (kx r : ℝ) : Prop where
  Kx_nonneg : ∀ t, 0 ≤ Kx t
  Kx_uniform : ∀ t, Kx t ≤ kx
  tangential_cost : ∀ t, Rb t ≤ r * m t
  tangential_constant_nonneg : 0 ≤ r
  density_nonneg : ∀ t, 0 ≤ m t

/-- The interval-restricted form actually used by the interpolation path. -/
structure ConcreteInterpolationBoundsOn
    (Kx Rb m : ℝ → ℝ) (T kx r : ℝ) : Prop where
  Kx_nonneg : ∀ t ∈ Icc (0 : ℝ) T, 0 ≤ Kx t
  Kx_uniform : ∀ t ∈ Icc (0 : ℝ) T, Kx t ≤ kx
  tangential_cost : ∀ t ∈ Icc (0 : ℝ) T, Rb t ≤ r * m t
  tangential_constant_nonneg : 0 ≤ r
  density_nonneg : ∀ t ∈ Icc (0 : ℝ) T, 0 ≤ m t

namespace ConcreteInterpolationBoundsOn

/-- Uniform `Kx` envelope for a selected steering family in the strip `kh`. -/
def selectedKxBound (kh : ℝ) : ℝ :=
  2 * kh / Real.sqrt (1 - kh ^ 2) ^ 3

/-- The explicit selected-rear curvature-source bound.  This applies
pointwise to the curvature interpolation once its curvature and selected
steering remain in the common strip. -/
theorem abs_selectedKx_le {kh Kv d : ℝ}
    (hkh0 : 0 ≤ kh) (hkh1 : kh < 1)
    (hd0 : 0 ≤ d) (hd1 : d ≤ Real.arcsin kh) (hK : |Kv| ≤ kh) :
    |(Kv - Real.sin d) / Real.cos d ^ 3| ≤ selectedKxBound kh :=
  RearOwnTangential.abs_curvDeriv_le_strip hkh0 hkh1 hd0 hd1 hK

theorem selectedKxBound_nonneg {kh : ℝ} (hkh0 : 0 ≤ kh) (hkh1 : kh < 1) :
    0 ≤ selectedKxBound kh := by
  have hs : 0 < 1 - kh ^ 2 := by nlinarith
  unfold selectedKxBound
  positivity

/-- Continuity on the compact interpolation-time interval produces a uniform
`Kx` constant.  A positive continuous cost density similarly turns a bounded
tangential rate into a uniform multiple of that density. -/
theorem exists_of_compact {Kx Rb m : ℝ → ℝ} {T : ℝ}
    (hT : 0 ≤ T) (hKc : Continuous Kx) (hRc : Continuous Rb) (hmc : Continuous m)
    (hK0 : ∀ t ∈ Icc (0 : ℝ) T, 0 ≤ Kx t)
    (hmpos : ∀ t ∈ Icc (0 : ℝ) T, 0 < m t) :
    ∃ kx r : ℝ, ConcreteInterpolationBoundsOn Kx Rb m T kx r := by
  have hne : (Icc (0 : ℝ) T).Nonempty := ⟨0, ⟨le_rfl, hT⟩⟩
  obtain ⟨tk, htk, hKmax⟩ :=
    isCompact_Icc.exists_isMaxOn hne hKc.continuousOn
  have hratioC : ContinuousOn (fun t => Rb t / m t) (Icc (0 : ℝ) T) :=
    hRc.continuousOn.div hmc.continuousOn (fun t ht => (hmpos t ht).ne')
  obtain ⟨tr, htr, hrmax⟩ :=
    isCompact_Icc.exists_isMaxOn hne hratioC
  refine ⟨Kx tk, max 0 (Rb tr / m tr), ⟨hK0, ?_, ?_, le_max_left _ _, ?_⟩⟩
  · intro t ht
    exact hKmax ht
  · intro t ht
    have hratio : Rb t / m t ≤ max 0 (Rb tr / m tr) :=
      (hrmax ht).trans (le_max_right _ _)
    rw [div_le_iff₀ (hmpos t ht)] at hratio
    exact hratio
  · intro t ht
    exact (hmpos t ht).le

/-- The canonical tangential envelope supplied by the selected-rear gauge-rate
estimate. -/
def tangentialEnvelope (kh v0 : ℝ) (m : ℝ → ℝ) : ℝ → ℝ :=
  fun t => kh / ((1 - kh ^ 2) * v0) * m t

/-- Rewrite the actual gauge-rate estimate produced by
`RearOwnTangentialCost.abs_gaugeRate_le_cost_density` in terms of the canonical
envelope used by this bridge. -/
theorem gaugeRate_le_tangentialEnvelope
    {xi v : ℝ → ℝ → ℝ} {kh v0 : ℝ} {m : ℝ → ℝ}
    (h : ∀ t x,
      |GaugeRate.gaugeRate xi v t x| ≤
        (kh / ((1 - kh ^ 2) * v0) * m t) * |x|) :
    ∀ t x, |GaugeRate.gaugeRate xi v t x| ≤
      tangentialEnvelope kh v0 m t * |x| := by
  simpa [tangentialEnvelope] using h

theorem tangentialEnvelope_cost {kh v0 T : ℝ} {m : ℝ → ℝ}
    (hkh0 : 0 ≤ kh) (hkh1 : kh < 1) (hv0 : 0 < v0)
    (hm0 : ∀ t ∈ Icc (0 : ℝ) T, 0 ≤ m t) :
    ∀ t ∈ Icc (0 : ℝ) T,
      tangentialEnvelope kh v0 m t ≤
        (kh / ((1 - kh ^ 2) * v0)) * m t := by
  intro t ht
  rfl

theorem tangentialEnvelope_constant_nonneg {kh v0 : ℝ}
    (hkh0 : 0 ≤ kh) (hkh1 : kh < 1) (hv0 : 0 < v0) :
    0 ≤ kh / ((1 - kh ^ 2) * v0) := by
  have hs : 0 < 1 - kh ^ 2 := by nlinarith
  positivity

/-- Explicit interval certificate for the selected-rear interpolation.  The
`Kx` and tangential envelopes are fixed algebraic multiples, so continuity and
compact maximization are unnecessary once the strip is known. -/
theorem explicit_selectedSteering_bounds {kh v0 T : ℝ} {m : ℝ → ℝ}
    (hkh0 : 0 ≤ kh) (hkh1 : kh < 1) (hv0 : 0 < v0)
    (hm0 : ∀ t ∈ Icc (0 : ℝ) T, 0 ≤ m t) :
    ConcreteInterpolationBoundsOn
      (fun _ => selectedKxBound kh) (tangentialEnvelope kh v0 m) m T
      (selectedKxBound kh) (kh / ((1 - kh ^ 2) * v0)) := by
  refine ⟨fun _ _ => selectedKxBound_nonneg hkh0 hkh1,
    fun _ _ => le_rfl, ?_, tangentialEnvelope_constant_nonneg hkh0 hkh1 hv0, hm0⟩
  intro t ht
  exact le_rfl

end ConcreteInterpolationBoundsOn

/-- Global source-shape bound for the explicit curvature interpolation. -/
theorem abs_interpolation_profiledSourceShape_le
    {k0 k1 : ℝ → ℝ} {theta0 L kh t : ℝ} {delta sf : ℝ → ℝ → ℝ}
    (hk0 : Continuous k0) (hk1 : Continuous k1)
    (hper0 : Function.Periodic k0 L) (hper1 : Function.Periodic k1 L)
    (htot0 : (∫ r in (0 : ℝ)..L, k0 r) = Real.pi)
    (htot1 : (∫ r in (0 : ℝ)..L, k1 r) = Real.pi)
    (hL : 0 < L) (hkh0 : 0 ≤ kh) (hkh1 : kh < 1)
    (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (hk0nn : ∀ r, 0 ≤ k0 r) (hk1nn : ∀ r, 0 ≤ k1 r)
    (hk0le : ∀ r, k0 r ≤ kh) (hk1le : ∀ r, k1 r ≤ kh)
    (hstrip0 : ∀ s, 0 ≤ delta t s)
    (hstrip1 : ∀ s, delta t s ≤ Real.arcsin kh) (x : ℝ) :
    |profiledSourceShape
      (normalVel k0 k1 theta0 L) (normalVelDeriv k0 k1 theta0 L)
      delta (fun a s => kappaInterp k0 k1 a s) sf t x| ≤
      ((1 + (3 / 2 : ℝ) * kh * L) * curvDist k0 k1 L) /
          Real.sqrt (1 - kh ^ 2) ^ 2 +
        ((3 / 2 : ℝ) * L * curvDist k0 k1 L) * kh *
          ConcreteInterpolationBoundsOn.selectedKxBound kh := by
  let v0 := Real.sqrt (1 - kh ^ 2)
  have hv0 : 0 < v0 := Real.sqrt_pos.mpr (by nlinarith)
  apply abs_profiledSourceShape_le hv0
  · exact Shadowing.cos_ge_of_mem_strip (hstrip0 _) (hstrip1 _)
  · exact abs_normalVelDeriv_le hk0 hk1 hper0 hper1 htot0 htot1 hL ht
      hk0nn hk1nn hk0le hk1le _
  · exact abs_normalVel_le hk0 hk1 hper0 hper1 htot0 htot1 hL _ _
  · exact abs_sin_le_of_mem_strip hkh0 hkh1.le (hstrip0 _) (hstrip1 _)
  · apply ConcreteInterpolationBoundsOn.abs_selectedKx_le hkh0 hkh1
      (hstrip0 _) (hstrip1 _)
    have hKnn : 0 ≤ kappaInterp k0 k1 t (sf t x) := by
      simp only [kappaInterp]
      exact add_nonneg
        (mul_nonneg (by linarith [ht.2]) (hk0nn _))
        (mul_nonneg ht.1 (hk1nn _))
    rw [abs_of_nonneg hKnn]
    exact kappaInterp_le hk0le hk1le ht _
  · have hcd : (0:ℝ) ≤ curvDist k0 k1 L := integral_abs_sub_nonneg hk0 hk1 hL.le
    have hfac : (0:ℝ) ≤ 1 + (3 / 2 : ℝ) * kh * L := by positivity
    exact mul_nonneg hfac hcd
  · have hcd : (0:ℝ) ≤ curvDist k0 k1 L := integral_abs_sub_nonneg hk0 hk1 hL.le
    have hfac : (0:ℝ) ≤ (3 / 2 : ℝ) * L := by positivity
    exact mul_nonneg hfac hcd
  · exact hkh0
  · exact ConcreteInterpolationBoundsOn.selectedKxBound_nonneg hkh0 hkh1

/-- The explicit interpolation source shape, multiplied by any nonnegative
common time profile, is controlled by a density with the same profile. -/
theorem interpolation_profiled_source_bound
    {k0 k1 : ℝ → ℝ} {theta0 L kh t w C d : ℝ}
    {delta sf : ℝ → ℝ → ℝ}
    (hk0 : Continuous k0) (hk1 : Continuous k1)
    (hper0 : Function.Periodic k0 L) (hper1 : Function.Periodic k1 L)
    (htot0 : (∫ r in (0 : ℝ)..L, k0 r) = Real.pi)
    (htot1 : (∫ r in (0 : ℝ)..L, k1 r) = Real.pi)
    (hL : 0 < L) (hkh0 : 0 ≤ kh) (hkh1 : kh < 1)
    (ht : t ∈ Set.Icc (0 : ℝ) 1) (hw : 0 ≤ w)
    (hk0nn : ∀ r, 0 ≤ k0 r) (hk1nn : ∀ r, 0 ≤ k1 r)
    (hk0le : ∀ r, k0 r ≤ kh) (hk1le : ∀ r, k1 r ≤ kh)
    (hstrip0 : ∀ s, 0 ≤ delta t s)
    (hstrip1 : ∀ s, delta t s ≤ Real.arcsin kh)
    (hDC :
      ((1 + (3 / 2 : ℝ) * kh * L) * curvDist k0 k1 L) /
            Real.sqrt (1 - kh ^ 2) ^ 2 +
          ((3 / 2 : ℝ) * L * curvDist k0 k1 L) * kh *
            ConcreteInterpolationBoundsOn.selectedKxBound kh ≤ d * C) :
    ∀ x,
      |w * profiledSourceShape
        (normalVel k0 k1 theta0 L) (normalVelDeriv k0 k1 theta0 L)
        delta (fun a s => kappaInterp k0 k1 a s) sf t x| ≤
        d * (C * w) := by
  exact source_bound_of_common_profile
    (gS := fun _ x => w * profiledSourceShape
      (normalVel k0 k1 theta0 L) (normalVelDeriv k0 k1 theta0 L)
      delta (fun a s => kappaInterp k0 k1 a s) sf t x)
    (w := fun _ => w) (D :=
      ((1 + (3 / 2 : ℝ) * kh * L) * curvDist k0 k1 L) /
          Real.sqrt (1 - kh ^ 2) ^ 2 +
        ((3 / 2 : ℝ) * L * curvDist k0 k1 L) * kh *
          ConcreteInterpolationBoundsOn.selectedKxBound kh)
    (fun _ => hw)
    (fun _ y => by
      rw [abs_mul, abs_of_nonneg hw, mul_comm]
      exact mul_le_mul_of_nonneg_right
        (abs_interpolation_profiledSourceShape_le hk0 hk1 hper0 hper1
          htot0 htot1 hL hkh0 hkh1 ht hk0nn hk1nn hk0le hk1le
          hstrip0 hstrip1 y) hw)
    hDC 0

end InterpolationRearCostBridge
