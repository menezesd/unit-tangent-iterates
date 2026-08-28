import Mathlib
import UnitTangentIterates.InterpolationFrame
import UnitTangentIterates.GaugeDensities
import UnitTangentIterates.PathMetric
import UnitTangentIterates.PathMetricCircle

/-!
# The curvature interpolation as a path of the marked path metric

The lemma *Curvature interpolation* of *A Noncircular Oval with Convex
Unit-Tangent Iterates* joins two marked ovals of the same half-perimeter by an
explicit path of curves, and bounds the path functionals `W, S₀, S₁` of that
path by the `L¹` distance of the two curvatures.  The pieces are in place:

* `CurvatureInterpolation.lean` builds the path and
  `InterpolationEstimate.lean`, `InterpolationSecondOrder.lean` bound its
  arclength densities, including the second-order one that the path metric of
  `PathMetric.lean` also asks for;
* `InterpolationGauge.lean` reparametrizes it by the flow of its tangential
  rate, so that it moves with purely normal velocity in a gauge parameter of
  period one;
* `InterpolationFrame.lean` bundles the two arclength bounds for that rate, so
  that `GaugeDensities.gauge_densities_le` compares the densities in the gauge
  parameter with the arclength densities.

This file assembles them into a `PathMetric.NormalPath`, and so bounds the
**path pseudodistance** of the two curves.  The time is reparametrized by the
profile `B` of `PathMetricCircle.lean`, whose speed `w` vanishes at both ends
of the time interval, so that the path comes to rest at its ends as a normal
path must; since `∫₀¹ w = 1`, this costs nothing.

Main results:

* `exists_normalPath_interp` : the curvature interpolation as a normal path of
  the marked path metric, with cost density `w · interpPathCost`;
* `pathDist_le_interpPathCost` : consequently
  `pathDist p q ≤ interpPathCost`, an explicit constant built from `L`, the
  curvature bounds and the `L¹` distance `ε` of the two curvatures, for the
  curve of `κ⁰` in its normalized arclength and the curve of `κ¹` read in a
  reparametrization of period one;
* `pathDist_le_interpPathCost_instance` : the hypotheses are not vacuous;
* `exists_delta_pathDist_le` : since the cost is continuous in the two
  smallness parameters and vanishes with them, two ovals whose curvatures are
  close in `L¹` and in the sup norm are close in the path pseudodistance.
-/

noncomputable section

open Real MeasureTheory Set MarkedSpace MarkedTopology PathMetric

namespace InterpolationPathDist

open CurvatureInterpolation InterpolationNormal InterpolationEstimate
  InterpolationSecondOrder InterpolationGauge InterpolationFrame
  UniformFrameBounds PathMetricCircle

variable {k0 k1 k0' k1' : ℝ → ℝ} {θ₀ L : ℝ}

/-! ### Two elementary lemmas -/

/-- A function with two continuous derivatives is `C²`. -/
theorem contDiff_two_of_derivs {f f1 f2 : ℝ → ℝ}
    (h1 : ∀ x, HasDerivAt f (f1 x) x) (h2 : ∀ x, HasDerivAt f1 (f2 x) x)
    (hc : Continuous f2) : ContDiff ℝ (2 : ℕ) f := by
  have hd : Differentiable ℝ f := fun x => (h1 x).differentiableAt
  have hd1 : Differentiable ℝ f1 := fun x => (h2 x).differentiableAt
  have hderiv : deriv f = f1 := funext fun x => (h1 x).deriv
  have hderiv1 : deriv f1 = f2 := funext fun x => (h2 x).deriv
  have hf1 : ContDiff ℝ (1 : ℕ) f1 := by
    rw [Nat.cast_one, contDiff_one_iff_deriv]
    exact ⟨hd1, by rw [hderiv1]; exact hc⟩
  have h2' : ContDiff ℝ ((1 : WithTop ℕ∞) + 1) f := by
    rw [contDiff_succ_iff_deriv]
    refine ⟨hd, by simp, ?_⟩
    rw [hderiv]
    simpa using hf1
  norm_num at h2' ⊢
  exact h2'

/-- The sup norm of a function bounded by `M`. -/
theorem supNorm_le_of_forall {f : ℝ → ℝ} {M : ℝ} (h : ∀ x, |f x| ≤ M) (hM : 0 ≤ M) :
    supNorm f ≤ M :=
  Real.iSup_le h hM

/-! ### The time profile -/

theorem B_eq_zero_of_nonpos {t : ℝ} (ht : t ≤ 0) : B t = 0 := by
  have : (∫ x in (0:ℝ)..t, w x) = ∫ _x in (0:ℝ)..t, (0:ℝ) := by
    refine intervalIntegral.integral_congr (fun x hx => ?_)
    rw [uIcc_of_ge ht] at hx
    exact w_eq_zero (fun hmem => absurd (lt_of_lt_of_le hmem.1 hx.2) (lt_irrefl 0))
  simpa [B] using this

theorem B_eq_one_of_one_le {t : ℝ} (ht : 1 ≤ t) : B t = 1 := by
  have hzero : (∫ x in (1:ℝ)..t, w x) = 0 := by
    have : (∫ x in (1:ℝ)..t, w x) = ∫ _x in (1:ℝ)..t, (0:ℝ) := by
      refine intervalIntegral.integral_congr (fun x hx => ?_)
      rw [uIcc_of_le ht] at hx
      exact w_eq_zero (fun hmem => absurd (lt_of_le_of_lt hx.1 hmem.2) (lt_irrefl 1))
    simpa using this
  have hadd : (∫ x in (0:ℝ)..(1:ℝ), w x) + (∫ x in (1:ℝ)..t, w x) = ∫ x in (0:ℝ)..t, w x :=
    intervalIntegral.integral_add_adjacent_intervals
      (continuous_w.intervalIntegrable _ _) (continuous_w.intervalIntegrable _ _)
  have : B t = (∫ x in (0:ℝ)..(1:ℝ), w x) + (∫ x in (1:ℝ)..t, w x) := by rw [hadd]; rfl
  rw [this, hzero, integral_w, add_zero]

theorem B_mem_Icc (t : ℝ) : B t ∈ Icc (0:ℝ) 1 := by
  rcases le_or_gt t 0 with ht | ht
  · rw [B_eq_zero_of_nonpos ht]; exact ⟨le_rfl, zero_le_one⟩
  rcases le_or_gt 1 t with ht1 | ht1
  · rw [B_eq_one_of_one_le ht1]; exact ⟨zero_le_one, le_rfl⟩
  refine ⟨intervalIntegral.integral_nonneg ht.le (fun x _ => w_nonneg x), ?_⟩
  have hadd : (∫ x in (0:ℝ)..t, w x) + (∫ x in t..(1:ℝ), w x) = ∫ x in (0:ℝ)..(1:ℝ), w x :=
    intervalIntegral.integral_add_adjacent_intervals
      (continuous_w.intervalIntegrable _ _) (continuous_w.intervalIntegrable _ _)
  have hrest : 0 ≤ ∫ x in t..(1:ℝ), w x :=
    intervalIntegral.integral_nonneg ht1.le (fun x _ => w_nonneg x)
  have h1 : (∫ x in (0:ℝ)..(1:ℝ), w x) = 1 := integral_w
  have : B t = (∫ x in (0:ℝ)..t, w x) := rfl
  rw [this]
  linarith [hadd, hrest, h1]

/-! ### The endpoints of the interpolation -/

@[simp] theorem kappaInterp_zero_fun : kappaInterp k0 k1 0 = k0 := by
  funext r; simp [kappaInterp]

@[simp] theorem kappaInterp_one_fun : kappaInterp k0 k1 1 = k1 := by
  funext r; simp [kappaInterp]

/-! ### The scaled normal velocity of a slice -/

/-- The normal velocity of the interpolation at the path parameter `a`, scaled
by the time profile `c`: the arclength density of the normal path below. -/
def scaledEta (k0 k1 : ℝ → ℝ) (θ₀ L c a : ℝ) : ℝ → ℝ :=
  fun s => c * normalVel k0 k1 θ₀ L a s

theorem hasDerivAt_scaledEta (hk0 : Continuous k0) (hk1 : Continuous k1) (c a s : ℝ) :
    HasDerivAt (scaledEta k0 k1 θ₀ L c a) (c * normalVelDeriv k0 k1 θ₀ L a s) s :=
  (hasDerivAt_normalVel (θ₀ := θ₀) (L := L) hk0 hk1 a s).const_mul c

theorem hasDerivAt_scaledEtaDeriv (hk0 : Continuous k0) (hk1 : Continuous k1)
    (hd0 : ∀ r, HasDerivAt k0 (k0' r) r) (hd1 : ∀ r, HasDerivAt k1 (k1' r) r) (c a s : ℝ) :
    HasDerivAt (fun x => c * normalVelDeriv k0 k1 θ₀ L a x)
      (c * normalVelSecondDeriv k0 k1 k0' k1' θ₀ L a s) s :=
  (hasDerivAt_normalVelDeriv (θ₀ := θ₀) (L := L) hk0 hk1 hd0 hd1 a s).const_mul c

theorem deriv_scaledEta (hk0 : Continuous k0) (hk1 : Continuous k1) (c a : ℝ) :
    deriv (scaledEta k0 k1 θ₀ L c a) = fun s => c * normalVelDeriv k0 k1 θ₀ L a s :=
  funext fun s => (hasDerivAt_scaledEta hk0 hk1 c a s).deriv

theorem deriv_deriv_scaledEta (hk0 : Continuous k0) (hk1 : Continuous k1)
    (hd0 : ∀ r, HasDerivAt k0 (k0' r) r) (hd1 : ∀ r, HasDerivAt k1 (k1' r) r) (c a : ℝ) :
    deriv (deriv (scaledEta k0 k1 θ₀ L c a))
      = fun s => c * normalVelSecondDeriv k0 k1 k0' k1' θ₀ L a s := by
  rw [deriv_scaledEta hk0 hk1 c a]
  exact funext fun s => (hasDerivAt_scaledEtaDeriv (k0' := k0') (k1' := k1') hk0 hk1 hd0 hd1
    c a s).deriv

theorem contDiff_two_scaledEta (hk0 : Continuous k0) (hk1 : Continuous k1)
    (hk0'c : Continuous k0') (hk1'c : Continuous k1')
    (hd0 : ∀ r, HasDerivAt k0 (k0' r) r) (hd1 : ∀ r, HasDerivAt k1 (k1' r) r) (c a : ℝ) :
    ContDiff ℝ (2 : ℕ) (scaledEta k0 k1 θ₀ L c a) := by
  refine contDiff_two_of_derivs (f1 := fun s => c * normalVelDeriv k0 k1 θ₀ L a s)
    (f2 := fun s => c * normalVelSecondDeriv k0 k1 k0' k1' θ₀ L a s)
    (fun s => hasDerivAt_scaledEta hk0 hk1 c a s)
    (fun s => hasDerivAt_scaledEtaDeriv (k0' := k0') (k1' := k1') hk0 hk1 hd0 hd1 c a s) ?_
  have hcont : Continuous fun s => normalVelSecondDeriv k0 k1 k0' k1' θ₀ L a s := by
    have h := continuous_uncurry_normalVelSecondDeriv (θ₀ := θ₀) (L := L) hk0 hk1 hk0'c hk1'c
    exact h.comp (continuous_const.prodMk continuous_id)
  exact continuous_const.mul hcont

theorem periodic_scaledEta (hk0 : Continuous k0) (hk1 : Continuous k1)
    (hper0 : Function.Periodic k0 L) (hper1 : Function.Periodic k1 L)
    (htot0 : (∫ r in (0:ℝ)..L, k0 r) = Real.pi)
    (htot1 : (∫ r in (0:ℝ)..L, k1 r) = Real.pi) (c a : ℝ) :
    Function.Periodic (scaledEta k0 k1 θ₀ L c a) (2 * L) := by
  have hper := normalVel_periodic (θ₀ := θ₀) (L := L) hk0 hk1 hper0 hper1 htot0 htot1 a
  intro s
  simp only [scaledEta]
  rw [show s + 2 * L = s + L + L by ring, hper (s + L), hper s]

/-! ### The arclength densities of the scaled normal velocity -/

section Densities

variable (hk0 : Continuous k0) (hk1 : Continuous k1)
  (hper0 : Function.Periodic k0 L) (hper1 : Function.Periodic k1 L)
  (htot0 : (∫ r in (0:ℝ)..L, k0 r) = Real.pi)
  (htot1 : (∫ r in (0:ℝ)..L, k1 r) = Real.pi) (hL : 0 < L)

include hk0 hk1 hper0 hper1 htot0 htot1 hL

theorem supNorm_scaledEta_le {c a : ℝ} (hc : 0 ≤ c) :
    supNorm (scaledEta k0 k1 θ₀ L c a) ≤ c * ((3/2) * L * curvDist k0 k1 L) := by
  have heps : 0 ≤ curvDist k0 k1 L := integral_abs_sub_nonneg hk0 hk1 hL.le
  refine supNorm_le_of_forall (fun s => ?_) (by positivity)
  rw [scaledEta, abs_mul, abs_of_nonneg hc]
  exact mul_le_mul_of_nonneg_left
    (abs_normalVel_le (θ₀ := θ₀) hk0 hk1 hper0 hper1 htot0 htot1 hL a s) hc

theorem supNorm_deriv_scaledEta_le {kstar c a : ℝ} (hc : 0 ≤ c) (ha : a ∈ Icc (0:ℝ) 1)
    (hk0nn : ∀ r, 0 ≤ k0 r) (hk1nn : ∀ r, 0 ≤ k1 r)
    (hk0le : ∀ r, k0 r ≤ kstar) (hk1le : ∀ r, k1 r ≤ kstar) :
    supNorm (deriv (scaledEta k0 k1 θ₀ L c a))
      ≤ c * ((1 + (3/2) * kstar * L) * curvDist k0 k1 L) := by
  have heps : 0 ≤ curvDist k0 k1 L := integral_abs_sub_nonneg hk0 hk1 hL.le
  have hkstar : 0 ≤ kstar := le_trans (hk0nn 0) (hk0le 0)
  rw [deriv_scaledEta hk0 hk1 c a]
  refine supNorm_le_of_forall (fun s => ?_) (by positivity)
  rw [abs_mul, abs_of_nonneg hc]
  exact mul_le_mul_of_nonneg_left
    (abs_normalVelDeriv_le (θ₀ := θ₀) hk0 hk1 hper0 hper1 htot0 htot1 hL ha
      hk0nn hk1nn hk0le hk1le s) hc

theorem supNorm_deriv2_scaledEta_le {kstar dsup kd c a : ℝ} (hc : 0 ≤ c) (ha : a ∈ Icc (0:ℝ) 1)
    (hd0 : ∀ r, HasDerivAt k0 (k0' r) r) (hd1 : ∀ r, HasDerivAt k1 (k1' r) r)
    (hd : ∀ r, |k1 r - k0 r| ≤ dsup)
    (hkd0 : ∀ r, |k0' r| ≤ kd) (hkd1 : ∀ r, |k1' r| ≤ kd)
    (hk0nn : ∀ r, 0 ≤ k0 r) (hk1nn : ∀ r, 0 ≤ k1 r)
    (hk0le : ∀ r, k0 r ≤ kstar) (hk1le : ∀ r, k1 r ≤ kstar) :
    supNorm (deriv (deriv (scaledEta k0 k1 θ₀ L c a)))
      ≤ c * (dsup + (kd + kstar ^ 2) * ((3/2) * L * curvDist k0 k1 L)) := by
  have heps : 0 ≤ curvDist k0 k1 L := integral_abs_sub_nonneg hk0 hk1 hL.le
  have hkstar : 0 ≤ kstar := le_trans (hk0nn 0) (hk0le 0)
  have hkd : 0 ≤ kd := le_trans (abs_nonneg _) (hkd0 0)
  have hdsup : 0 ≤ dsup := le_trans (abs_nonneg _) (hd 0)
  rw [deriv_deriv_scaledEta (k0' := k0') (k1' := k1') hk0 hk1 hd0 hd1 c a]
  refine supNorm_le_of_forall (fun s => ?_) (by positivity)
  rw [abs_mul, abs_of_nonneg hc]
  exact mul_le_mul_of_nonneg_left
    (abs_normalVelSecondDeriv_le (θ₀ := θ₀) hk0 hk1 hper0 hper1 htot0 htot1 hL ha
      hd hkd0 hkd1 hk0nn hk1nn hk0le hk1le s) hc

theorem integral_abs_scaledEta_le {c a : ℝ} (hc : 0 ≤ c) :
    (∫ s in (0:ℝ)..(2 * L), |scaledEta k0 k1 θ₀ L c a s|)
      ≤ c * (2 * L * ((3/2) * L * curvDist k0 k1 L)) := by
  have hrw : (∫ s in (0:ℝ)..(2 * L), |scaledEta k0 k1 θ₀ L c a s|)
      = c * ∫ s in (0:ℝ)..(2 * L), |normalVel k0 k1 θ₀ L a s| := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr (fun s _ => ?_)
    rw [scaledEta, abs_mul, abs_of_nonneg hc]
  rw [hrw]
  exact mul_le_mul_of_nonneg_left
    (normalVel_L1_le (θ₀ := θ₀) hk0 hk1 hper0 hper1 htot0 htot1 hL a) hc

end Densities

/-! ### The normal path -/

/-- The sup bound `E = (3/2)Lε` for the normal velocity of the interpolation. -/
def costE (L eps : ℝ) : ℝ := (3/2) * L * eps

/-- The sup bound `(1 + (3/2)κ_*L)ε` for its first arclength derivative. -/
def costG1 (kstar L eps : ℝ) : ℝ := (1 + (3/2) * kstar * L) * eps

/-- The sup bound `d + (k' + κ_*²)E` for its second arclength derivative. -/
def costG2 (kstar kd dsup L eps : ℝ) : ℝ := dsup + (kd + kstar ^ 2) * costE L eps

/-- The distortion factor `2L·e^{R₁}` of the gauge flow over the time
interval. -/
def costFac (kstar L eps : ℝ) : ℝ := 2 * L * Real.exp (rate1Bound kstar L eps)

/-- The `L¹` term of the cost. -/
def costTermW (kstar L eps : ℝ) : ℝ := Real.exp (rate1Bound kstar L eps) * costE L eps

/-- The first-order term of the cost. -/
def costTermS1 (kstar L eps : ℝ) : ℝ := costG1 kstar L eps * costFac kstar L eps

/-- The second-order term of the cost. -/
def costTermS2 (kstar kd dsup L eps : ℝ) : ℝ :=
  costG2 kstar kd dsup L eps * costFac kstar L eps ^ 2
    + costG1 kstar L eps
        * (rate2Bound kstar kd L eps * (2 * L) ^ 2
            * Real.exp (2 * rate1Bound kstar L eps))

/-- **The cost of the curvature-interpolation path**: the sum of the four gauge
densities of its normal velocity, in terms of the half-perimeter `L`, the
curvature bounds `κ_*`, `k'`, `d` and the `L¹` distance `ε` of the two
curvatures. -/
def interpPathCost (kstar kd dsup L eps : ℝ) : ℝ :=
  costE L eps + costTermW kstar L eps + costTermS1 kstar L eps
    + costTermS2 kstar kd dsup L eps

section CostBounds

variable {kstar kd dsup L eps : ℝ}

theorem costE_nonneg (hL : 0 ≤ L) (heps : 0 ≤ eps) : 0 ≤ costE L eps := by
  unfold costE; positivity

theorem costG1_nonneg (hkstar : 0 ≤ kstar) (hL : 0 ≤ L) (heps : 0 ≤ eps) :
    0 ≤ costG1 kstar L eps := by
  unfold costG1; positivity

theorem costFac_nonneg (hL : 0 ≤ L) : 0 ≤ costFac kstar L eps := by
  unfold costFac; positivity

theorem costTermW_nonneg (hL : 0 ≤ L) (heps : 0 ≤ eps) : 0 ≤ costTermW kstar L eps := by
  have h := costE_nonneg hL heps
  unfold costTermW
  positivity

theorem costTermS1_nonneg (hkstar : 0 ≤ kstar) (hL : 0 ≤ L) (heps : 0 ≤ eps) :
    0 ≤ costTermS1 kstar L eps :=
  mul_nonneg (costG1_nonneg hkstar hL heps) (costFac_nonneg hL)

theorem costG2_nonneg (hkd : 0 ≤ kd) (hdsup : 0 ≤ dsup) (hL : 0 ≤ L) (heps : 0 ≤ eps) :
    0 ≤ costG2 kstar kd dsup L eps := by
  have h := costE_nonneg (L := L) (eps := eps) hL heps
  unfold costG2
  positivity

theorem costTermS2_nonneg (hkstar : 0 ≤ kstar) (hkd : 0 ≤ kd) (hdsup : 0 ≤ dsup)
    (hL : 0 ≤ L) (heps : 0 ≤ eps) : 0 ≤ costTermS2 kstar kd dsup L eps := by
  have h2 : 0 ≤ rate2Bound kstar kd L eps := rate2Bound_nonneg hkstar hkd hL heps
  have hG2 := costG2_nonneg (kstar := kstar) hkd hdsup hL heps
  have hG1 := costG1_nonneg hkstar hL heps
  have hfac := costFac_nonneg (kstar := kstar) (eps := eps) hL
  unfold costTermS2
  positivity

theorem interpPathCost_nonneg (hkstar : 0 ≤ kstar) (hkd : 0 ≤ kd) (hdsup : 0 ≤ dsup)
    (hL : 0 ≤ L) (heps : 0 ≤ eps) : 0 ≤ interpPathCost kstar kd dsup L eps := by
  have h1 := costE_nonneg hL heps
  have h2 := costTermW_nonneg (kstar := kstar) hL heps
  have h3 := costTermS1_nonneg hkstar hL heps
  have h4 := costTermS2_nonneg hkstar hkd hdsup hL heps
  unfold interpPathCost
  linarith

theorem costE_le_interpPathCost (hkstar : 0 ≤ kstar) (hkd : 0 ≤ kd) (hdsup : 0 ≤ dsup)
    (hL : 0 ≤ L) (heps : 0 ≤ eps) : costE L eps ≤ interpPathCost kstar kd dsup L eps := by
  have h2 := costTermW_nonneg (kstar := kstar) hL heps
  have h3 := costTermS1_nonneg hkstar hL heps
  have h4 := costTermS2_nonneg hkstar hkd hdsup hL heps
  unfold interpPathCost
  linarith

theorem costTermW_le_interpPathCost (hkstar : 0 ≤ kstar) (hkd : 0 ≤ kd) (hdsup : 0 ≤ dsup)
    (hL : 0 ≤ L) (heps : 0 ≤ eps) :
    costTermW kstar L eps ≤ interpPathCost kstar kd dsup L eps := by
  have h1 := costE_nonneg hL heps
  have h3 := costTermS1_nonneg hkstar hL heps
  have h4 := costTermS2_nonneg hkstar hkd hdsup hL heps
  unfold interpPathCost
  linarith

theorem costTermS1_le_interpPathCost (hkstar : 0 ≤ kstar) (hkd : 0 ≤ kd) (hdsup : 0 ≤ dsup)
    (hL : 0 ≤ L) (heps : 0 ≤ eps) :
    costTermS1 kstar L eps ≤ interpPathCost kstar kd dsup L eps := by
  have h1 := costE_nonneg hL heps
  have h2 := costTermW_nonneg (kstar := kstar) hL heps
  have h4 := costTermS2_nonneg hkstar hkd hdsup hL heps
  unfold interpPathCost
  linarith

theorem costTermS2_le_interpPathCost (hkstar : 0 ≤ kstar) (hL : 0 ≤ L) (heps : 0 ≤ eps) :
    costTermS2 kstar kd dsup L eps ≤ interpPathCost kstar kd dsup L eps := by
  have h1 := costE_nonneg hL heps
  have h2 := costTermW_nonneg (kstar := kstar) hL heps
  have h3 := costTermS1_nonneg hkstar hL heps
  unfold interpPathCost
  linarith

end CostBounds

/-- The moving curve of the normal path: the interpolation at the path
parameter `B t`, read in the gauge parameter. -/
def pathCurve (k0 k1 : ℝ → ℝ) (θ₀ L : ℝ) (Phi : ℝ → ℝ → ℝ) (t u : ℝ) : ℂ :=
  interpCurve (kappaInterp k0 k1 (B t)) θ₀ L (Phi (B t) u)

/-- Its normal velocity. -/
def pathEta (k0 k1 : ℝ → ℝ) (θ₀ L : ℝ) (Phi : ℝ → ℝ → ℝ) (t u : ℝ) : ℝ :=
  scaledEta k0 k1 θ₀ L (w t) (B t) (Phi (B t) u)

/-- Its unit normal. -/
def pathNu (k0 k1 : ℝ → ℝ) (θ₀ : ℝ) (Phi : ℝ → ℝ → ℝ) (t u : ℝ) : ℂ :=
  NormalGaugeFrame.frameNormalVector
    (tangentAngle (kappaInterp k0 k1 (B t)) θ₀ (Phi (B t) u))

set_option maxHeartbeats 1000000 in
/-- **The curvature interpolation is a normal path of the marked path metric.**

Two curvatures which are nonnegative, bounded by `κ_*`, `L`-periodic, of total
turning `π` over a half period, and `C¹` with derivatives bounded by `k'` and
with `|κ¹ − κ⁰| ≤ d`, define two closed centrally symmetric unit-speed curves.
The curvature interpolation joining them, reparametrized by the flow of its
tangential rate and run with the time profile of `PathMetricCircle.lean`, is a
normal path of the path metric of `PathMetric.lean`, of cost at most
`interpPathCost`.  The terminal curve is the curve of `κ¹` read in the gauge
parameter `ψ`, a reparametrization of period one (`ψ(u+1) = ψ(u) + 2L`). -/
theorem normalPath_interp_of_gauge_full {kstar kd dsup : ℝ}
    (hk0 : Continuous k0) (hk1 : Continuous k1)
    (hk0'c : Continuous k0') (hk1'c : Continuous k1')
    (hper0 : Function.Periodic k0 L) (hper1 : Function.Periodic k1 L)
    (htot0 : (∫ r in (0:ℝ)..L, k0 r) = Real.pi)
    (htot1 : (∫ r in (0:ℝ)..L, k1 r) = Real.pi) (hL : 0 < L)
    (hd0 : ∀ r, HasDerivAt k0 (k0' r) r) (hd1 : ∀ r, HasDerivAt k1 (k1' r) r)
    (hd : ∀ r, |k1 r - k0 r| ≤ dsup)
    (hkd0 : ∀ r, |k0' r| ≤ kd) (hkd1 : ∀ r, |k1' r| ≤ kd)
    (hk0nn : ∀ r, 0 ≤ k0 r) (hk1nn : ∀ r, 0 ≤ k1 r)
    (hk0le : ∀ r, k0 r ≤ kstar) (hk1le : ∀ r, k1 r ≤ kstar)
    (Phi : ℝ → ℝ → ℝ)
    (hPhi0 : ∀ u, Phi 0 u = 2 * L * u)
    (hPhid : ∀ u t, HasDerivAt (fun r => Phi r u)
      (gaugeField k0 k1 θ₀ L t (Phi t u)) t)
    (hPhinormal : ∀ t ∈ Icc (0 : ℝ) 1, ∀ u,
      HasDerivAt (fun r => interpCurve (kappaInterp k0 k1 r) θ₀ L (Phi r u))
        ((normalVel k0 k1 θ₀ L t (Phi t u) : ℂ) *
          NormalGaugeFrame.frameNormalVector
            (tangentAngle (kappaInterp k0 k1 t) θ₀ (Phi t u))) t)
    (p q : Data) (hp : ∀ u, p.1 u = interpCurve k0 θ₀ L (2 * L * u))
    (hq : ∀ u, q.1 u = interpCurve k1 θ₀ L (Phi 1 u)) :
    ∃ Γ : NormalPath p q, Γ.T = 1 ∧
      Γ.X = pathCurve k0 k1 θ₀ L Phi ∧
      Γ.eta = pathEta k0 k1 θ₀ L Phi ∧
      Γ.m = (fun t => w t * interpPathCost kstar kd dsup L (curvDist k0 k1 L)) ∧
      NormalPath.cost Γ ≤ interpPathCost kstar kd dsup L (curvDist k0 k1 L) := by
  classical
  have heps : 0 ≤ curvDist k0 k1 L := integral_abs_sub_nonneg hk0 hk1 hL.le
  have hkstar : 0 ≤ kstar := le_trans (hk0nn 0) (hk0le 0)
  have hkd : 0 ≤ kd := le_trans (abs_nonneg _) (hkd0 0)
  have hdsup : 0 ≤ dsup := le_trans (abs_nonneg _) (hd 0)
  have hR1nn : 0 ≤ rate1Bound kstar L (curvDist k0 k1 L) :=
    rate1Bound_nonneg hkstar hL.le heps
  have hCnn : 0 ≤ interpPathCost kstar kd dsup L (curvDist k0 k1 L) :=
    interpPathCost_nonneg hkstar hkd hdsup hL.le heps
  have hCE := costE_le_interpPathCost (kstar := kstar) (kd := kd) (dsup := dsup)
    hkstar hkd hdsup hL.le heps
  have hCW := costTermW_le_interpPathCost (kd := kd) (dsup := dsup) hkstar hkd hdsup hL.le heps
  have hCS1 := costTermS1_le_interpPathCost (kd := kd) (dsup := dsup) hkstar hkd hdsup hL.le heps
  have hCS2 := costTermS2_le_interpPathCost (kd := kd) (dsup := dsup) hkstar hL.le heps
  -- the frame bundle of the interpolation
  set D := interpFrame k0 k1 k0' k1' θ₀ L kstar kd hk0 hk1 hk0'c hk1'c hper0 hper1 htot0 htot1
    hL hd0 hd1 hk0nn hk1nn hk0le hk1le hkd0 hkd1 with hD_def
  have hDxi : D.xi = xiCut k0 k1 θ₀ L := rfl
  have hDv : D.v = fun _ _ => (1:ℝ) := rfl
  have hDlip : D.rateLip = rate1Bound kstar L (curvDist k0 k1 L) := rfl
  have hDb2 : D.rateBound2 = rate2Bound kstar kd L (curvDist k0 k1 L) := rfl
  have hQ : (0:ℝ) < 2 * L := by linarith
  have hxiper : ∀ a, Function.Periodic (D.xi a) (2 * L) := fun a => by
    rw [hDxi]; exact periodic_xiCut hk0 hk1 hper0 hper1 htot0 htot1 a
  have hvper : ∀ a, Function.Periodic (D.v a) (2 * L) := fun a s => by rw [hDv]
  have hPhid' : ∀ u t, HasDerivAt (fun r => Phi r u)
      (GaugeRate.gaugeRate D.xi D.v t (Phi t u)) t := by
    intro u t
    rw [hDxi, hDv, gaugeRate_interpFrame]
    exact hPhid u t
  -- the four densities at each time
  have hdens : ∀ t : ℝ,
      supNorm (fun u => scaledEta k0 k1 θ₀ L (w t) (B t) (Phi (B t) u))
          ≤ w t * interpPathCost kstar kd dsup L (curvDist k0 k1 L) ∧
      supNorm (iteratedDeriv 1 fun u => scaledEta k0 k1 θ₀ L (w t) (B t) (Phi (B t) u))
          ≤ w t * interpPathCost kstar kd dsup L (curvDist k0 k1 L) ∧
      supNorm (iteratedDeriv 2 fun u => scaledEta k0 k1 θ₀ L (w t) (B t) (Phi (B t) u))
          ≤ w t * interpPathCost kstar kd dsup L (curvDist k0 k1 L) ∧
      (∫ u in (0:ℝ)..1, |scaledEta k0 k1 θ₀ L (w t) (B t) (Phi (B t) u)|)
          ≤ w t * interpPathCost kstar kd dsup L (curvDist k0 k1 L) := by
    intro t
    have hwnn : 0 ≤ w t := w_nonneg t
    have hBmem : B t ∈ Icc (0:ℝ) 1 := B_mem_Icc t
    have habs : |B t| ≤ 1 := by rw [abs_of_nonneg hBmem.1]; exact hBmem.2
    have habs0 : 0 ≤ |B t| := abs_nonneg _
    have hexp1 : Real.exp (D.rateLip * |B t|)
        ≤ Real.exp (rate1Bound kstar L (curvDist k0 k1 L)) := by
      rw [hDlip]
      exact Real.exp_le_exp.mpr (by nlinarith)
    have hexp2 : Real.exp (2 * D.rateLip * |B t|)
        ≤ Real.exp (2 * rate1Bound kstar L (curvDist k0 k1 L)) := by
      rw [hDlip]
      exact Real.exp_le_exp.mpr (by nlinarith)
    obtain ⟨hg0, hg1, hg2, hgL1⟩ := GaugeDensities.gauge_densities_le D hQ hxiper hvper
      hPhid' hPhi0 (eta := scaledEta k0 k1 θ₀ L (w t) (B t))
      (contDiff_two_scaledEta hk0 hk1 hk0'c hk1'c hd0 hd1 (w t) (B t))
      (periodic_scaledEta hk0 hk1 hper0 hper1 htot0 htot1 (w t) (B t)) (B t)
    -- the arclength densities
    have hs0 : supNorm (scaledEta k0 k1 θ₀ L (w t) (B t)) ≤ w t * costE L (curvDist k0 k1 L) := by
      unfold costE
      exact supNorm_scaledEta_le hk0 hk1 hper0 hper1 htot0 htot1 hL hwnn
    have hs1 : supNorm (deriv (scaledEta k0 k1 θ₀ L (w t) (B t)))
        ≤ w t * costG1 kstar L (curvDist k0 k1 L) := by
      unfold costG1
      exact supNorm_deriv_scaledEta_le hk0 hk1 hper0 hper1 htot0 htot1 hL hwnn hBmem
        hk0nn hk1nn hk0le hk1le
    have hs2 : supNorm (deriv (deriv (scaledEta k0 k1 θ₀ L (w t) (B t))))
        ≤ w t * costG2 kstar kd dsup L (curvDist k0 k1 L) := by
      unfold costG2 costE
      exact supNorm_deriv2_scaledEta_le (k0' := k0') (k1' := k1') hk0 hk1 hper0 hper1 htot0 htot1
        hL hwnn hBmem hd0 hd1 hd hkd0 hkd1 hk0nn hk1nn hk0le hk1le
    have hsL1 : (∫ s in (0:ℝ)..(2 * L), |scaledEta k0 k1 θ₀ L (w t) (B t) s|)
        ≤ w t * (2 * L * costE L (curvDist k0 k1 L)) := by
      unfold costE
      exact integral_abs_scaledEta_le hk0 hk1 hper0 hper1 htot0 htot1 hL hwnn
    have hEnn : 0 ≤ costE L (curvDist k0 k1 L) := costE_nonneg hL.le heps
    have hG1nn : 0 ≤ costG1 kstar L (curvDist k0 k1 L) :=
      costG1_nonneg hkstar hL.le heps
    have hG2nn : 0 ≤ costG2 kstar kd dsup L (curvDist k0 k1 L) :=
      costG2_nonneg hkd hdsup hL.le heps
    have hfacnn : 0 ≤ costFac kstar L (curvDist k0 k1 L) := costFac_nonneg hL.le
    have hfac1 : 2 * L * Real.exp (D.rateLip * |B t|) ≤ costFac kstar L (curvDist k0 k1 L) := by
      unfold costFac
      exact mul_le_mul_of_nonneg_left hexp1 (by linarith)
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact le_trans hg0 (le_trans hs0 (mul_le_mul_of_nonneg_left hCE hwnn))
    · refine le_trans hg1 ?_
      have hmul : supNorm (deriv (scaledEta k0 k1 θ₀ L (w t) (B t)))
            * (2 * L * Real.exp (D.rateLip * |B t|))
          ≤ (w t * costG1 kstar L (curvDist k0 k1 L)) * costFac kstar L (curvDist k0 k1 L) :=
        mul_le_mul hs1 hfac1 (by positivity) (by positivity)
      refine le_trans hmul ?_
      have hrw : (w t * costG1 kstar L (curvDist k0 k1 L)) * costFac kstar L (curvDist k0 k1 L)
          = w t * costTermS1 kstar L (curvDist k0 k1 L) := by unfold costTermS1; ring
      rw [hrw]
      exact mul_le_mul_of_nonneg_left hCS1 hwnn
    · refine le_trans hg2 ?_
      have hfacsq : (2 * L * Real.exp (D.rateLip * |B t|)) ^ 2
          ≤ costFac kstar L (curvDist k0 k1 L) ^ 2 := by
        have h1 : 0 ≤ 2 * L * Real.exp (D.rateLip * |B t|) := by positivity
        nlinarith [hfac1, h1, hfacnn]
      have hA : supNorm (deriv (deriv (scaledEta k0 k1 θ₀ L (w t) (B t))))
            * (2 * L * Real.exp (D.rateLip * |B t|)) ^ 2
          ≤ (w t * costG2 kstar kd dsup L (curvDist k0 k1 L))
              * costFac kstar L (curvDist k0 k1 L) ^ 2 :=
        mul_le_mul hs2 hfacsq (by positivity) (by positivity)
      have hR2nn : 0 ≤ rate2Bound kstar kd L (curvDist k0 k1 L) :=
        rate2Bound_nonneg hkstar hkd hL.le heps
      have hfac2 : D.rateBound2 * (2 * L) ^ 2 * |B t| * Real.exp (2 * D.rateLip * |B t|)
          ≤ rate2Bound kstar kd L (curvDist k0 k1 L) * (2 * L) ^ 2
              * Real.exp (2 * rate1Bound kstar L (curvDist k0 k1 L)) := by
        rw [hDb2]
        have hAnn : 0 ≤ rate2Bound kstar kd L (curvDist k0 k1 L) * (2 * L) ^ 2 :=
          mul_nonneg hR2nn (sq_nonneg _)
        have h1 : rate2Bound kstar kd L (curvDist k0 k1 L) * (2 * L) ^ 2 * |B t|
            ≤ rate2Bound kstar kd L (curvDist k0 k1 L) * (2 * L) ^ 2 :=
          mul_le_of_le_one_right hAnn habs
        calc rate2Bound kstar kd L (curvDist k0 k1 L) * (2 * L) ^ 2 * |B t|
                * Real.exp (2 * D.rateLip * |B t|)
            ≤ rate2Bound kstar kd L (curvDist k0 k1 L) * (2 * L) ^ 2
                * Real.exp (2 * D.rateLip * |B t|) :=
              mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
          _ ≤ rate2Bound kstar kd L (curvDist k0 k1 L) * (2 * L) ^ 2
                * Real.exp (2 * rate1Bound kstar L (curvDist k0 k1 L)) :=
              mul_le_mul_of_nonneg_left hexp2 (by positivity)
      have hB' : supNorm (deriv (scaledEta k0 k1 θ₀ L (w t) (B t)))
            * (D.rateBound2 * (2 * L) ^ 2 * |B t| * Real.exp (2 * D.rateLip * |B t|))
          ≤ (w t * costG1 kstar L (curvDist k0 k1 L))
              * (rate2Bound kstar kd L (curvDist k0 k1 L) * (2 * L) ^ 2
                  * Real.exp (2 * rate1Bound kstar L (curvDist k0 k1 L))) :=
        mul_le_mul hs1 hfac2 (by positivity) (by positivity)
      refine le_trans (add_le_add hA hB') ?_
      have hrw : (w t * costG2 kstar kd dsup L (curvDist k0 k1 L))
              * costFac kstar L (curvDist k0 k1 L) ^ 2
            + (w t * costG1 kstar L (curvDist k0 k1 L))
              * (rate2Bound kstar kd L (curvDist k0 k1 L) * (2 * L) ^ 2
                  * Real.exp (2 * rate1Bound kstar L (curvDist k0 k1 L)))
          = w t * costTermS2 kstar kd dsup L (curvDist k0 k1 L) := by
        unfold costTermS2; ring
      rw [hrw]
      exact mul_le_mul_of_nonneg_left hCS2 hwnn
    · refine le_trans hgL1 ?_
      have hfac : Real.exp (D.rateLip * |B t|) / (2 * L)
          ≤ Real.exp (rate1Bound kstar L (curvDist k0 k1 L)) / (2 * L) := by
        gcongr
      have hmul : (Real.exp (D.rateLip * |B t|) / (2 * L))
            * ∫ s in (0:ℝ)..(2 * L), |scaledEta k0 k1 θ₀ L (w t) (B t) s|
          ≤ (Real.exp (rate1Bound kstar L (curvDist k0 k1 L)) / (2 * L))
              * (w t * (2 * L * costE L (curvDist k0 k1 L))) := by
        exact mul_le_mul hfac hsL1
          (intervalIntegral.integral_nonneg hQ.le (fun s _ => abs_nonneg _)) (by positivity)
      refine le_trans hmul ?_
      have hrw : (Real.exp (rate1Bound kstar L (curvDist k0 k1 L)) / (2 * L))
            * (w t * (2 * L * costE L (curvDist k0 k1 L)))
          = w t * costTermW kstar L (curvDist k0 k1 L) := by
        unfold costTermW
        field_simp
      rw [hrw]
      exact mul_le_mul_of_nonneg_left hCW hwnn
  -- the normal path
  refine ⟨{ T := 1
            T_pos := one_pos
            X := pathCurve k0 k1 θ₀ L Phi
            eta := pathEta k0 k1 θ₀ L Phi
            nu := pathNu k0 k1 θ₀ Phi
            m := fun t => w t * interpPathCost kstar kd dsup L (curvDist k0 k1 L)
            start := ?_
            finish := ?_
            hasDerivAt_time := ?_
            cont_vel := ?_
            norm_nu := ?_
            cont_m := ?_
            m_nonneg := ?_
            m_stop := ?_
            abs_eta_le := ?_
            le_m_L1 := ?_
            le_m_sup := ?_ }, rfl, rfl, rfl, rfl, ?_⟩
  · -- the initial curve
    intro u
    rw [hp u, pathCurve, B_zero, kappaInterp_zero_fun, hPhi0]
  · -- the terminal curve
    intro u
    rw [hq u, pathCurve, B_one, kappaInterp_one_fun]
  · -- the path moves along its normal
    intro t u
    have hBd : HasDerivAt B (w t) t := hasDerivAt_B t
    have hY := hPhinormal (B t) (B_mem_Icc t) u
    have hcomp := hY.scomp t hBd
    have hrw : (w t) • ((normalVel k0 k1 θ₀ L (B t) (Phi (B t) u) : ℂ)
          * NormalGaugeFrame.frameNormalVector
              (tangentAngle (kappaInterp k0 k1 (B t)) θ₀ (Phi (B t) u)))
        = ((pathEta k0 k1 θ₀ L Phi t u : ℝ) : ℂ) * pathNu k0 k1 θ₀ Phi t u := by
      simp only [pathEta, pathNu, scaledEta, Complex.real_smul]
      push_cast
      ring
    rw [← hrw]
    exact hcomp
  · -- the velocity is continuous in the time
    intro u
    have hBdiff : Differentiable ℝ B := fun t => (hasDerivAt_B t).differentiableAt
    have hBc : Continuous B := hBdiff.continuous
    have hPhidiff : Differentiable ℝ fun a : ℝ => Phi a u :=
      fun a => (hPhid u a).differentiableAt
    have hPhic : Continuous fun a : ℝ => Phi a u := hPhidiff.continuous
    have hPhiB : Continuous fun t : ℝ => Phi (B t) u := hPhic.comp hBc
    have hpair : Continuous fun t : ℝ => ((B t, Phi (B t) u) : ℝ × ℝ) := hBc.prodMk hPhiB
    have heta : Continuous fun t : ℝ => normalVel k0 k1 θ₀ L (B t) (Phi (B t) u) := by
      have h := (continuous_uncurry_normalVel (θ₀ := θ₀) (L := L) hk0 hk1).comp hpair
      simpa [Function.comp_def] using h
    have hang : Continuous fun t : ℝ =>
        tangentAngle (kappaInterp k0 k1 (B t)) θ₀ (Phi (B t) u) := by
      have h := (continuous_uncurry_tangentAngle (θ₀ := θ₀) hk0 hk1).comp hpair
      simpa [Function.comp_def] using h
    have hnu : Continuous fun t : ℝ => pathNu k0 k1 θ₀ Phi t u := by
      have hf : Continuous fun psi : ℝ => NormalGaugeFrame.frameNormalVector psi := by
        unfold NormalGaugeFrame.frameNormalVector; fun_prop
      exact hf.comp hang
    have hetaC : Continuous fun t : ℝ => ((pathEta k0 k1 θ₀ L Phi t u : ℝ) : ℂ) := by
      have hr : Continuous fun t : ℝ => pathEta k0 k1 θ₀ L Phi t u := by
        simp only [pathEta, scaledEta]
        exact continuous_w.mul heta
      exact Complex.continuous_ofReal.comp hr
    exact hetaC.mul hnu
  · -- the normal is a unit vector
    intro t u
    exact NormalGaugeFrame.norm_frameNormalVector _
  · exact continuous_w.mul continuous_const
  · intro t; exact mul_nonneg (w_nonneg t) hCnn
  · intro t ht; rw [w_eq_zero ht, zero_mul]
  · -- the cost density dominates the normal speed
    intro t u
    have hwnn : 0 ≤ w t := w_nonneg t
    have h := abs_normalVel_le (θ₀ := θ₀) hk0 hk1 hper0 hper1 htot0 htot1 hL (B t)
      (Phi (B t) u)
    calc |pathEta k0 k1 θ₀ L Phi t u| = w t * |normalVel k0 k1 θ₀ L (B t) (Phi (B t) u)| := by
          rw [pathEta, scaledEta, abs_mul, abs_of_nonneg hwnn]
      _ ≤ w t * costE L (curvDist k0 k1 L) := by
          refine mul_le_mul_of_nonneg_left ?_ hwnn
          unfold costE
          exact h
      _ ≤ w t * interpPathCost kstar kd dsup L (curvDist k0 k1 L) :=
          mul_le_mul_of_nonneg_left hCE hwnn
  · -- the `L¹` density
    intro t
    exact (hdens t).2.2.2
  · -- the sup densities
    intro t j hj
    interval_cases j
    · simpa [iteratedDeriv_zero] using (hdens t).1
    · exact (hdens t).2.1
    · exact (hdens t).2.2.1
  · -- the cost
    show (∫ t in (0:ℝ)..(1:ℝ), w t * interpPathCost kstar kd dsup L (curvDist k0 k1 L))
        ≤ interpPathCost kstar kd dsup L (curvDist k0 k1 L)
    rw [intervalIntegral.integral_mul_const, integral_w, one_mul]

/-- Backwards-compatible projection of `normalPath_interp_of_gauge_full`. -/
theorem normalPath_interp_of_gauge {kstar kd dsup : ℝ}
    (hk0 : Continuous k0) (hk1 : Continuous k1)
    (hk0'c : Continuous k0') (hk1'c : Continuous k1')
    (hper0 : Function.Periodic k0 L) (hper1 : Function.Periodic k1 L)
    (htot0 : (∫ r in (0:ℝ)..L, k0 r) = Real.pi)
    (htot1 : (∫ r in (0:ℝ)..L, k1 r) = Real.pi) (hL : 0 < L)
    (hd0 : ∀ r, HasDerivAt k0 (k0' r) r) (hd1 : ∀ r, HasDerivAt k1 (k1' r) r)
    (hd : ∀ r, |k1 r - k0 r| ≤ dsup)
    (hkd0 : ∀ r, |k0' r| ≤ kd) (hkd1 : ∀ r, |k1' r| ≤ kd)
    (hk0nn : ∀ r, 0 ≤ k0 r) (hk1nn : ∀ r, 0 ≤ k1 r)
    (hk0le : ∀ r, k0 r ≤ kstar) (hk1le : ∀ r, k1 r ≤ kstar)
    (Phi : ℝ → ℝ → ℝ)
    (hPhi0 : ∀ u, Phi 0 u = 2 * L * u)
    (hPhid : ∀ u t, HasDerivAt (fun r => Phi r u)
      (gaugeField k0 k1 θ₀ L t (Phi t u)) t)
    (hPhinormal : ∀ t ∈ Icc (0 : ℝ) 1, ∀ u,
      HasDerivAt (fun r => interpCurve (kappaInterp k0 k1 r) θ₀ L (Phi r u))
        ((normalVel k0 k1 θ₀ L t (Phi t u) : ℂ) *
          NormalGaugeFrame.frameNormalVector
            (tangentAngle (kappaInterp k0 k1 t) θ₀ (Phi t u))) t)
    (p q : Data) (hp : ∀ u, p.1 u = interpCurve k0 θ₀ L (2 * L * u))
    (hq : ∀ u, q.1 u = interpCurve k1 θ₀ L (Phi 1 u)) :
    ∃ Γ : NormalPath p q, Γ.T = 1 ∧
      Γ.eta = pathEta k0 k1 θ₀ L Phi ∧
      NormalPath.cost Γ ≤ interpPathCost kstar kd dsup L (curvDist k0 k1 L) := by
  obtain ⟨Gamma, hT, -, heta, -, hcost⟩ := normalPath_interp_of_gauge_full
    hk0 hk1 hk0'c hk1'c hper0 hper1 htot0 htot1 hL hd0 hd1 hd
    hkd0 hkd1 hk0nn hk1nn hk0le hk1le Phi hPhi0 hPhid hPhinormal p q hp hq
  exact ⟨Gamma, hT, heta, hcost⟩

/-- Strengthened interpolation constructor retaining the complete gauge flow
and the definitional normal-rate equality. -/
theorem exists_normalPath_interp_with_gauge {kstar kd dsup : ℝ}
    (hk0 : Continuous k0) (hk1 : Continuous k1)
    (hk0'c : Continuous k0') (hk1'c : Continuous k1')
    (hper0 : Function.Periodic k0 L) (hper1 : Function.Periodic k1 L)
    (htot0 : (∫ r in (0:ℝ)..L, k0 r) = Real.pi)
    (htot1 : (∫ r in (0:ℝ)..L, k1 r) = Real.pi) (hL : 0 < L)
    (hd0 : ∀ r, HasDerivAt k0 (k0' r) r) (hd1 : ∀ r, HasDerivAt k1 (k1' r) r)
    (hd : ∀ r, |k1 r - k0 r| ≤ dsup)
    (hkd0 : ∀ r, |k0' r| ≤ kd) (hkd1 : ∀ r, |k1' r| ≤ kd)
    (hk0nn : ∀ r, 0 ≤ k0 r) (hk1nn : ∀ r, 0 ≤ k1 r)
    (hk0le : ∀ r, k0 r ≤ kstar) (hk1le : ∀ r, k1 r ≤ kstar) :
    ∃ Phi : ℝ → ℝ → ℝ,
      (∀ u, Phi 0 u = 2 * L * u) ∧
      (∀ u t, HasDerivAt (fun r => Phi r u)
        (gaugeField k0 k1 θ₀ L t (Phi t u)) t) ∧
      (∀ t u, Phi t (u + 1) = Phi t u + 2 * L) ∧
      (∀ t, Continuous fun u => Phi t u) ∧
      (∀ t, Function.Periodic
        (fun u => interpCurve (kappaInterp k0 k1 t) θ₀ L (Phi t u)) 1) ∧
      (∀ t ∈ Icc (0 : ℝ) 1, ∀ u,
        HasDerivAt (fun r => interpCurve (kappaInterp k0 k1 r) θ₀ L (Phi r u))
          ((normalVel k0 k1 θ₀ L t (Phi t u) : ℂ) *
            NormalGaugeFrame.frameNormalVector
              (tangentAngle (kappaInterp k0 k1 t) θ₀ (Phi t u))) t) ∧
      ∀ p q : Data, (∀ u, p.1 u = interpCurve k0 θ₀ L (2 * L * u)) →
        (∀ u, q.1 u = interpCurve k1 θ₀ L (Phi 1 u)) →
        ∃ Γ : NormalPath p q, Γ.T = 1 ∧
          Γ.eta = pathEta k0 k1 θ₀ L Phi ∧
          NormalPath.cost Γ ≤ interpPathCost kstar kd dsup L (curvDist k0 k1 L) := by
  obtain ⟨Phi, hPhi0, hPhid, hPhitrans, hPhicont, hPhiper, hPhinormal⟩ :=
    exists_interpolation_gauge_flow (θ₀ := θ₀) (kstar := kstar)
      hk0 hk1 hper0 hper1 htot0 htot1 hL hk0nn hk1nn hk0le hk1le
  refine ⟨Phi, hPhi0, hPhid, hPhitrans, hPhicont, hPhiper, hPhinormal, ?_⟩
  intro p q hp hq
  exact normalPath_interp_of_gauge hk0 hk1 hk0'c hk1'c hper0 hper1
    htot0 htot1 hL hd0 hd1 hd hkd0 hkd1 hk0nn hk1nn hk0le hk1le
    Phi hPhi0 hPhid hPhinormal p q hp hq

/-- Backwards-compatible projection of
`exists_normalPath_interp_with_gauge`, retaining the original API. -/
theorem exists_normalPath_interp {kstar kd dsup : ℝ}
    (hk0 : Continuous k0) (hk1 : Continuous k1)
    (hk0'c : Continuous k0') (hk1'c : Continuous k1')
    (hper0 : Function.Periodic k0 L) (hper1 : Function.Periodic k1 L)
    (htot0 : (∫ r in (0:ℝ)..L, k0 r) = Real.pi)
    (htot1 : (∫ r in (0:ℝ)..L, k1 r) = Real.pi) (hL : 0 < L)
    (hd0 : ∀ r, HasDerivAt k0 (k0' r) r) (hd1 : ∀ r, HasDerivAt k1 (k1' r) r)
    (hd : ∀ r, |k1 r - k0 r| ≤ dsup)
    (hkd0 : ∀ r, |k0' r| ≤ kd) (hkd1 : ∀ r, |k1' r| ≤ kd)
    (hk0nn : ∀ r, 0 ≤ k0 r) (hk1nn : ∀ r, 0 ≤ k1 r)
    (hk0le : ∀ r, k0 r ≤ kstar) (hk1le : ∀ r, k1 r ≤ kstar) :
    ∃ psi : ℝ → ℝ, Continuous psi ∧ (∀ u, psi (u + 1) = psi u + 2 * L) ∧
      ∀ p q : Data, (∀ u, p.1 u = interpCurve k0 θ₀ L (2 * L * u)) →
        (∀ u, q.1 u = interpCurve k1 θ₀ L (psi u)) →
        ∃ Γ : NormalPath p q, Γ.T = 1 ∧
          NormalPath.cost Γ ≤ interpPathCost kstar kd dsup L (curvDist k0 k1 L) := by
  obtain ⟨Phi, hPhi0, hPhid, hPhitrans, hPhicont, hPhiper, hPhinormal, hpath⟩ :=
    exists_normalPath_interp_with_gauge (θ₀ := θ₀) (kstar := kstar)
      hk0 hk1 hk0'c hk1'c hper0 hper1 htot0 htot1 hL hd0 hd1 hd
      hkd0 hkd1 hk0nn hk1nn hk0le hk1le
  refine ⟨Phi 1, hPhicont 1, hPhitrans 1, ?_⟩
  intro p q hp hq
  obtain ⟨Γ, hT, heta, hcost⟩ := hpath p q hp hq
  exact ⟨Γ, hT, hcost⟩

/-! ### The path pseudodistance -/

/-- **The marked path distance of two ovals is at most `interpPathCost`.**
Under the hypotheses of `exists_normalPath_interp` the curvature interpolation
is an admissible normal path, so the pseudodistance of the two marked curves is
bounded by its cost: an explicit constant built from the half-perimeter `L`, the
curvature bounds and the `L¹` distance of the two curvatures. -/
theorem pathDist_le_interpPathCost {kstar kd dsup : ℝ}
    (hk0 : Continuous k0) (hk1 : Continuous k1)
    (hk0'c : Continuous k0') (hk1'c : Continuous k1')
    (hper0 : Function.Periodic k0 L) (hper1 : Function.Periodic k1 L)
    (htot0 : (∫ r in (0:ℝ)..L, k0 r) = Real.pi)
    (htot1 : (∫ r in (0:ℝ)..L, k1 r) = Real.pi) (hL : 0 < L)
    (hd0 : ∀ r, HasDerivAt k0 (k0' r) r) (hd1 : ∀ r, HasDerivAt k1 (k1' r) r)
    (hd : ∀ r, |k1 r - k0 r| ≤ dsup)
    (hkd0 : ∀ r, |k0' r| ≤ kd) (hkd1 : ∀ r, |k1' r| ≤ kd)
    (hk0nn : ∀ r, 0 ≤ k0 r) (hk1nn : ∀ r, 0 ≤ k1 r)
    (hk0le : ∀ r, k0 r ≤ kstar) (hk1le : ∀ r, k1 r ≤ kstar) :
    ∃ psi : ℝ → ℝ, Continuous psi ∧ (∀ u, psi (u + 1) = psi u + 2 * L) ∧
      ∀ p q : Data, (∀ u, p.1 u = interpCurve k0 θ₀ L (2 * L * u)) →
        (∀ u, q.1 u = interpCurve k1 θ₀ L (psi u)) →
        pathDist p q ≤ interpPathCost kstar kd dsup L (curvDist k0 k1 L) := by
  obtain ⟨psi, hcont, htrans, hmain⟩ := exists_normalPath_interp (θ₀ := θ₀) (kstar := kstar)
    (kd := kd) (dsup := dsup) hk0 hk1 hk0'c hk1'c hper0 hper1 htot0 htot1 hL hd0 hd1 hd
    hkd0 hkd1 hk0nn hk1nn hk0le hk1le
  refine ⟨psi, hcont, htrans, fun p q hp hq => ?_⟩
  obtain ⟨Γ, -, hcost⟩ := hmain p q hp hq
  exact le_trans (pathDist_le_cost Γ) hcost

/-! ### Non-vacuity -/

/-- A continuous curve of period one is a marked curve: it is bounded, so it
defines an element of `MarkedSpace.Data`. -/
theorem exists_data_of_periodic_curve {g : ℝ → ℂ} (hg : Continuous g)
    (hper : Function.Periodic g 1) : ∃ p : Data, ∀ u, p.1 u = g u := by
  obtain ⟨x, -, hmax⟩ := (isCompact_Icc (a := (0:ℝ)) (b := 1)).exists_isMaxOn
    ⟨0, by norm_num⟩ hg.norm.continuousOn
  have hbd : ∀ u, ‖g u‖ ≤ ‖g x‖ := by
    intro u
    obtain ⟨y, hy, hxy⟩ := hper.exists_mem_Ico₀ one_pos u
    rw [hxy]
    exact hmax ⟨hy.1, hy.2.le⟩
  exact ⟨(BoundedContinuousFunction.ofNormedAddCommGroup g hg _ hbd, 0, 0), fun _ => rfl⟩

/-- **The bound is not vacuous.**  The circle of curvature `1/2` and the oval of
curvature `1/2 + (cos s)/4`, the two curves of `InterpolationEstimate.lean`,
satisfy every hypothesis of `pathDist_le_interpPathCost`, and both of the marked
curves it speaks of exist. -/
theorem pathDist_le_interpPathCost_instance :
    ∃ (psi : ℝ → ℝ) (p q : Data),
      (∀ u, psi (u + 1) = psi u + 2 * (2 * Real.pi)) ∧
      (∀ u, p.1 u = interpCurve kcirc 0 (2 * Real.pi) (2 * (2 * Real.pi) * u)) ∧
      (∀ u, q.1 u = interpCurve kwave 0 (2 * Real.pi) (psi u)) ∧
      pathDist p q
        ≤ interpPathCost (3/4) (1/4) (1/4) (2 * Real.pi) (curvDist kcirc kwave (2 * Real.pi)) := by
  have hpi : (0:ℝ) < 2 * Real.pi := by positivity
  obtain ⟨psi, hcont, htrans, hmain⟩ :=
    pathDist_le_interpPathCost (θ₀ := 0) (kstar := 3/4) (kd := 1/4) (dsup := 1/4)
      continuous_kcirc continuous_kwave continuous_const (by unfold kwave'; fun_prop)
      kcirc_periodic kwave_periodic kcirc_total kwave_total hpi
      hasDerivAt_kcirc hasDerivAt_kwave
      (fun r => by
        have h1 := Real.neg_one_le_cos r
        have h2 := Real.cos_le_one r
        rw [abs_le]
        constructor <;> simp only [kcirc, kwave] <;> linarith)
      (fun r => by norm_num)
      (fun r => by
        have h1 := Real.neg_one_le_sin r
        have h2 := Real.sin_le_one r
        rw [abs_le]
        constructor <;> simp only [kwave'] <;> linarith)
      kcirc_nonneg kwave_nonneg kcirc_le kwave_le
  -- both curves are continuous and of period one
  have hXcd : Differentiable ℝ (interpCurve kcirc 0 (2 * Real.pi)) := fun s =>
    (hasDerivAt_interpCurve (θ₀ := 0) (L := 2 * Real.pi) continuous_kcirc s).differentiableAt
  have hXwd : Differentiable ℝ (interpCurve kwave 0 (2 * Real.pi)) := fun s =>
    (hasDerivAt_interpCurve (θ₀ := 0) (L := 2 * Real.pi) continuous_kwave s).differentiableAt
  have hXc : Continuous (interpCurve kcirc 0 (2 * Real.pi)) := hXcd.continuous
  have hXw : Continuous (interpCurve kwave 0 (2 * Real.pi)) := hXwd.continuous
  have hXcper : Function.Periodic (interpCurve kcirc 0 (2 * Real.pi)) (2 * (2 * Real.pi)) :=
    interpCurve_periodic (θ₀ := 0) continuous_kcirc kcirc_periodic kcirc_total
  have hXwper : Function.Periodic (interpCurve kwave 0 (2 * Real.pi)) (2 * (2 * Real.pi)) :=
    interpCurve_periodic (θ₀ := 0) continuous_kwave kwave_periodic kwave_total
  obtain ⟨p, hp⟩ := exists_data_of_periodic_curve
    (g := fun u => interpCurve kcirc 0 (2 * Real.pi) (2 * (2 * Real.pi) * u))
    (hXc.comp (continuous_const.mul continuous_id)) (fun u => by
      have : 2 * (2 * Real.pi) * (u + 1) = 2 * (2 * Real.pi) * u + 2 * (2 * Real.pi) := by ring
      simp only [this]
      exact hXcper _)
  obtain ⟨q, hq⟩ := exists_data_of_periodic_curve
    (g := fun u => interpCurve kwave 0 (2 * Real.pi) (psi u))
    (hXw.comp hcont) (fun u => by
      simp only [htrans u]
      exact hXwper _)
  exact ⟨psi, p, q, htrans, hp, hq, hmain p q hp hq⟩

/-! ### Continuity of the bound in the curvature -/

/-- The cost vanishes when the two curvatures agree. -/
theorem interpPathCost_zero (kstar kd L : ℝ) : interpPathCost kstar kd 0 L 0 = 0 := by
  simp [interpPathCost, costE, costG1, costG2, costFac, costTermW, costTermS1, costTermS2]

/-- The cost is a continuous function of the two smallness parameters: the `L¹`
distance `ε` of the curvatures and the sup distance `d`. -/
theorem continuous_interpPathCost (kstar kd L : ℝ) :
    Continuous fun x : ℝ × ℝ => interpPathCost kstar kd x.2 L x.1 := by
  simp only [interpPathCost, costTermW, costTermS1, costTermS2, costG1, costG2, costFac,
    costE, rate1Bound, rate2Bound]
  fun_prop

/-- **Two ovals whose curvatures are close are close in the marked path
metric.**  For a fixed half-perimeter `L` and fixed curvature ceilings `κ_*` and
`k'`, and for every tolerance `η > 0`, there is a `δ > 0` such that any two
admissible curvatures whose `L¹` distance and whose sup distance are both below
`δ` define marked ovals at path pseudodistance at most `η`. -/
theorem exists_delta_pathDist_le {kstar kd : ℝ} (hL : 0 < L) {eta : ℝ} (heta : 0 < eta) :
    ∃ delta > 0, ∀ (j0 j1 j0' j1' : ℝ → ℝ) (a0 : ℝ),
      Continuous j0 → Continuous j1 → Continuous j0' → Continuous j1' →
      Function.Periodic j0 L → Function.Periodic j1 L →
      (∫ r in (0:ℝ)..L, j0 r) = Real.pi → (∫ r in (0:ℝ)..L, j1 r) = Real.pi →
      (∀ r, HasDerivAt j0 (j0' r) r) → (∀ r, HasDerivAt j1 (j1' r) r) →
      (∀ r, |j0' r| ≤ kd) → (∀ r, |j1' r| ≤ kd) →
      (∀ r, 0 ≤ j0 r) → (∀ r, 0 ≤ j1 r) → (∀ r, j0 r ≤ kstar) → (∀ r, j1 r ≤ kstar) →
      curvDist j0 j1 L < delta → (∀ r, |j1 r - j0 r| < delta) →
      ∃ psi : ℝ → ℝ, Continuous psi ∧ (∀ u, psi (u + 1) = psi u + 2 * L) ∧
        ∀ p q : Data, (∀ u, p.1 u = interpCurve j0 a0 L (2 * L * u)) →
          (∀ u, q.1 u = interpCurve j1 a0 L (psi u)) → pathDist p q ≤ eta := by
  have htend : Filter.Tendsto (fun x : ℝ × ℝ => interpPathCost kstar kd x.2 L x.1)
      (nhds ((0:ℝ), (0:ℝ))) (nhds 0) := by
    have h := (continuous_interpPathCost kstar kd L).tendsto ((0:ℝ), (0:ℝ))
    rwa [interpPathCost_zero] at h
  obtain ⟨r, hr, hball⟩ := Metric.tendsto_nhds_nhds.mp htend eta heta
  refine ⟨r / 2, by positivity, ?_⟩
  intro j0 j1 j0' j1' a0 hj0 hj1 hj0' hj1' hper0 hper1 htot0 htot1 hd0 hd1 hkd0 hkd1
    hj0nn hj1nn hj0le hj1le heps hdlt
  obtain ⟨psi, hcont, htrans, hmain⟩ :=
    pathDist_le_interpPathCost (θ₀ := a0) (kstar := kstar) (kd := kd) (dsup := r / 2)
      hj0 hj1 hj0' hj1' hper0 hper1 htot0 htot1 hL hd0 hd1
      (fun x => (hdlt x).le) hkd0 hkd1 hj0nn hj1nn hj0le hj1le
  refine ⟨psi, hcont, htrans, fun p q hp hq => le_trans (hmain p q hp hq) ?_⟩
  have hepsnn : 0 ≤ curvDist j0 j1 L := integral_abs_sub_nonneg hj0 hj1 hL.le
  have hdist : dist ((curvDist j0 j1 L, r / 2) : ℝ × ℝ) ((0:ℝ), (0:ℝ)) < r := by
    rw [Prod.dist_eq]
    refine max_lt ?_ ?_
    · rw [Real.dist_eq, sub_zero, abs_of_nonneg hepsnn]
      linarith
    · rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity : (0:ℝ) ≤ r / 2)]
      linarith
  have h := hball hdist
  rw [Real.dist_eq, sub_zero] at h
  exact le_trans (le_abs_self _) h.le

end InterpolationPathDist
