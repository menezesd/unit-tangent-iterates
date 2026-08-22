import Mathlib
import UnitTangentIterates.InterpolationPathDist
import UnitTangentIterates.CurvatureStabilityL1

/-!
# The path-distance bound from an `L¹` comparison of curvatures alone

`InterpolationPathDist.exists_delta_pathDist_le` bounds the marked path
pseudodistance of two ovals in terms of **two** smallness parameters: the `L¹`
distance `ε` of their curvatures and their sup distance `d`.  The theorem
*Curvature-measure matching* of *A Noncircular Oval with Convex Unit-Tangent
Iterates*, which is what feeds such a bound, produces only the `L¹` estimate.

The sup distance is not an independent datum, though: the two curvatures are
already assumed to have derivatives bounded by `k'`, and a function with a
bounded derivative whose `L¹` norm over a period is small is uniformly small —
this is `SupFromL1.abs_le_of_intervalIntegral_abs_le`, extended to the whole
line for periodic data in `CurvatureStabilityL1.abs_sub_le_of_periodic`.  Here
the two are composed:

* `sup_lt_of_curvDist_lt` — for `L`-periodic curvatures with `|κ'| ≤ k'` the
  `L¹` bound `ε` gives the uniform bound `max(√(4k'ε), 4ε/L)`, so that a small
  enough `L¹` distance forces the sup distance below any prescribed threshold;
* `exists_delta_pathDist_le_of_L1` — consequently, for a fixed half-perimeter
  `L`, curvature ceiling `κ_*` and derivative ceiling `k' > 0`, and for every
  tolerance `η > 0` there is a `δ > 0` such that **the `L¹` distance of the two
  curvatures alone** being below `δ` puts the two marked ovals at path
  pseudodistance at most `η`;
* `exists_threshold_pathDist_le_exp` — the form in which the matching estimate
  `∫|k_H − K_P| ≤ Ce^{−βH}` is consumed: beyond an explicit threshold in the
  separation `H` the two marked ovals are at path pseudodistance at most `η`.
-/

noncomputable section

open Real MeasureTheory Set MarkedSpace MarkedTopology PathMetric

namespace InterpolationPathDistL1

open CurvatureInterpolation InterpolationEstimate InterpolationSecondOrder
  InterpolationPathDist

variable {L : ℝ}

/-! ### From the `L¹` distance to the sup distance -/

/-- **The uniform bound produced by the `L¹` distance.**  Two `L`-periodic
curvatures with `|jᵢ'| ≤ k'` differ everywhere by at most
`l1Modulus (2k') ε L = max(√(4k'ε), 4ε/L)`, where `ε` is their `L¹` distance
over one period. -/
theorem sup_le_of_curvDist {j0 j1 j0' j1' : ℝ → ℝ} {kd : ℝ}
    (hL : 0 < L) (hkd : 0 < kd)
    (hper0 : Function.Periodic j0 L) (hper1 : Function.Periodic j1 L)
    (hd0 : ∀ r, HasDerivAt j0 (j0' r) r) (hd1 : ∀ r, HasDerivAt j1 (j1' r) r)
    (hkd0 : ∀ r, |j0' r| ≤ kd) (hkd1 : ∀ r, |j1' r| ≤ kd) (r : ℝ) :
    |j1 r - j0 r| ≤ CurvatureStabilityL1.l1Modulus (2 * kd) (curvDist j0 j1 L) L := by
  have hint : (∫ x in (0:ℝ)..(0 + L), |j1 x - j0 x|) ≤ curvDist j0 j1 L := by
    rw [zero_add]
    exact le_of_eq rfl
  exact CurvatureStabilityL1.abs_sub_le_of_periodic (k₁ := j1) (k₂ := j0)
    (k₁' := j1') (k₂' := j0') (c := 0) (P := L) (M := 2 * kd)
    hL (by positivity) hper1 hper0 hd1 hd0
    (fun x => by simpa using hkd1 x) (fun x => by simpa using hkd0 x) hint r


/-- **A small `L¹` distance of two periodic curvatures with bounded derivatives
forces a small sup distance.**  If `|jᵢ'| ≤ k'` and the `L¹` distance over one
period is smaller than `min (d²/(4k')) (dL/4)`, then the two curvatures differ
everywhere by less than `d`. -/
theorem sup_lt_of_curvDist_lt {j0 j1 j0' j1' : ℝ → ℝ} {kd d : ℝ}
    (hL : 0 < L) (hkd : 0 < kd) (hd : 0 < d)
    (hper0 : Function.Periodic j0 L) (hper1 : Function.Periodic j1 L)
    (hd0 : ∀ r, HasDerivAt j0 (j0' r) r) (hd1 : ∀ r, HasDerivAt j1 (j1' r) r)
    (hkd0 : ∀ r, |j0' r| ≤ kd) (hkd1 : ∀ r, |j1' r| ≤ kd)
    (hsmall : curvDist j0 j1 L < min (d ^ 2 / (4 * kd)) (d * L / 4)) (r : ℝ) :
    |j1 r - j0 r| < d := by
  have hc0 : Continuous j0 := Differentiable.continuous fun x => (hd0 x).differentiableAt
  have hc1 : Continuous j1 := Differentiable.continuous fun x => (hd1 x).differentiableAt
  have hbound := sup_le_of_curvDist hL hkd hper0 hper1 hd0 hd1 hkd0 hkd1 r
  rw [CurvatureStabilityL1.l1Modulus] at hbound
  set eps : ℝ := curvDist j0 j1 L with heps
  have hepsnn : 0 ≤ eps := InterpolationNormal.integral_abs_sub_nonneg hc0 hc1 hL.le
  have h1 : Real.sqrt (2 * (2 * kd) * eps) < d := by
    have hlt : 2 * (2 * kd) * eps < d ^ 2 := by
      have h := lt_of_lt_of_le hsmall (min_le_left _ _)
      rw [lt_div_iff₀ (by positivity : (0:ℝ) < 4 * kd)] at h
      nlinarith
    calc Real.sqrt (2 * (2 * kd) * eps) < Real.sqrt (d ^ 2) :=
          Real.sqrt_lt_sqrt (mul_nonneg (by positivity) hepsnn) hlt
      _ = d := Real.sqrt_sq hd.le
  have h2 : 4 * eps / L < d := by
    have h := lt_of_lt_of_le hsmall (min_le_right _ _)
    rw [div_lt_iff₀ hL]
    nlinarith
  exact lt_of_le_of_lt hbound (max_lt h1 h2)

/-! ### The path-distance bound -/

/-- **The explicit path-distance bound with the sup distance eliminated.**  The
bound of `InterpolationPathDist.pathDist_le_interpPathCost` holds with the sup
distance `d` replaced by the modulus `l1Modulus (2k') ε L` produced by the `L¹`
distance `ε` of the two curvatures, so that the whole constant depends on the
`L¹` distance alone. -/
theorem pathDist_le_interpPathCost_of_L1 {k0 k1 k0' k1' : ℝ → ℝ} {θ₀ kstar kd : ℝ}
    (hk0 : Continuous k0) (hk1 : Continuous k1)
    (hk0'c : Continuous k0') (hk1'c : Continuous k1')
    (hper0 : Function.Periodic k0 L) (hper1 : Function.Periodic k1 L)
    (htot0 : (∫ r in (0:ℝ)..L, k0 r) = Real.pi)
    (htot1 : (∫ r in (0:ℝ)..L, k1 r) = Real.pi) (hL : 0 < L) (hkd : 0 < kd)
    (hd0 : ∀ r, HasDerivAt k0 (k0' r) r) (hd1 : ∀ r, HasDerivAt k1 (k1' r) r)
    (hkd0 : ∀ r, |k0' r| ≤ kd) (hkd1 : ∀ r, |k1' r| ≤ kd)
    (hk0nn : ∀ r, 0 ≤ k0 r) (hk1nn : ∀ r, 0 ≤ k1 r)
    (hk0le : ∀ r, k0 r ≤ kstar) (hk1le : ∀ r, k1 r ≤ kstar) :
    ∃ psi : ℝ → ℝ, Continuous psi ∧ (∀ u, psi (u + 1) = psi u + 2 * L) ∧
      ∀ p q : Data, (∀ u, p.1 u = interpCurve k0 θ₀ L (2 * L * u)) →
        (∀ u, q.1 u = interpCurve k1 θ₀ L (psi u)) →
        pathDist p q ≤ interpPathCost kstar kd
          (CurvatureStabilityL1.l1Modulus (2 * kd) (curvDist k0 k1 L) L) L (curvDist k0 k1 L) :=
  InterpolationPathDist.pathDist_le_interpPathCost (θ₀ := θ₀) (kstar := kstar) (kd := kd)
    hk0 hk1 hk0'c hk1'c hper0 hper1 htot0 htot1 hL hd0 hd1
    (fun r => sup_le_of_curvDist hL hkd hper0 hper1 hd0 hd1 hkd0 hkd1 r)
    hkd0 hkd1 hk0nn hk1nn hk0le hk1le


/-- **Two ovals whose curvatures are close in `L¹` are close in the marked path
metric.**  For a fixed half-perimeter `L`, curvature ceiling `κ_*` and
derivative ceiling `k' > 0`, and for every tolerance `η > 0`, there is a `δ > 0`
such that any two admissible curvatures whose `L¹` distance is below `δ` define
marked ovals at path pseudodistance at most `η`.  Unlike
`InterpolationPathDist.exists_delta_pathDist_le`, no bound on the sup distance
is assumed: it is produced from the derivative bound. -/
theorem exists_delta_pathDist_le_of_L1 {kstar kd : ℝ} (hL : 0 < L) (hkd : 0 < kd)
    {eta : ℝ} (heta : 0 < eta) :
    ∃ delta > 0, ∀ (j0 j1 j0' j1' : ℝ → ℝ) (a0 : ℝ),
      Continuous j0 → Continuous j1 → Continuous j0' → Continuous j1' →
      Function.Periodic j0 L → Function.Periodic j1 L →
      (∫ r in (0:ℝ)..L, j0 r) = Real.pi → (∫ r in (0:ℝ)..L, j1 r) = Real.pi →
      (∀ r, HasDerivAt j0 (j0' r) r) → (∀ r, HasDerivAt j1 (j1' r) r) →
      (∀ r, |j0' r| ≤ kd) → (∀ r, |j1' r| ≤ kd) →
      (∀ r, 0 ≤ j0 r) → (∀ r, 0 ≤ j1 r) → (∀ r, j0 r ≤ kstar) → (∀ r, j1 r ≤ kstar) →
      curvDist j0 j1 L < delta →
      ∃ psi : ℝ → ℝ, Continuous psi ∧ (∀ u, psi (u + 1) = psi u + 2 * L) ∧
        ∀ p q : Data, (∀ u, p.1 u = interpCurve j0 a0 L (2 * L * u)) →
          (∀ u, q.1 u = interpCurve j1 a0 L (psi u)) → pathDist p q ≤ eta := by
  obtain ⟨d, hd, hmain⟩ :=
    InterpolationPathDist.exists_delta_pathDist_le (kstar := kstar) (kd := kd) hL heta
  refine ⟨min d (min (d ^ 2 / (4 * kd)) (d * L / 4)), by positivity, ?_⟩
  intro j0 j1 j0' j1' a0 hj0 hj1 hj0' hj1' hper0 hper1 htot0 htot1 hdd0 hdd1 hkd0 hkd1
    hj0nn hj1nn hj0le hj1le hsmall
  refine hmain j0 j1 j0' j1' a0 hj0 hj1 hj0' hj1' hper0 hper1 htot0 htot1 hdd0 hdd1
    hkd0 hkd1 hj0nn hj1nn hj0le hj1le (lt_of_lt_of_le hsmall (min_le_left _ _)) ?_
  exact fun r => sup_lt_of_curvDist_lt hL hkd hd hper0 hper1 hdd0 hdd1 hkd0 hkd1
    (lt_of_lt_of_le hsmall (min_le_right _ _)) r

/-- **The exponential form.**  If the `L¹` distance of the two curvatures obeys
the matching estimate `ε(H) ≤ Ce^{−βH}` with `β > 0`, then beyond a threshold in
the separation `H` the two marked ovals are at path pseudodistance at most `η`. -/
theorem exists_threshold_pathDist_le_exp {kstar kd C beta : ℝ} (hL : 0 < L) (hkd : 0 < kd)
    (hC : 0 < C) (hbeta : 0 < beta) {eta : ℝ} (heta : 0 < eta) :
    ∃ H₀ : ℝ, ∀ H ≥ H₀, ∀ (j0 j1 j0' j1' : ℝ → ℝ) (a0 : ℝ),
      Continuous j0 → Continuous j1 → Continuous j0' → Continuous j1' →
      Function.Periodic j0 L → Function.Periodic j1 L →
      (∫ r in (0:ℝ)..L, j0 r) = Real.pi → (∫ r in (0:ℝ)..L, j1 r) = Real.pi →
      (∀ r, HasDerivAt j0 (j0' r) r) → (∀ r, HasDerivAt j1 (j1' r) r) →
      (∀ r, |j0' r| ≤ kd) → (∀ r, |j1' r| ≤ kd) →
      (∀ r, 0 ≤ j0 r) → (∀ r, 0 ≤ j1 r) → (∀ r, j0 r ≤ kstar) → (∀ r, j1 r ≤ kstar) →
      curvDist j0 j1 L ≤ C * Real.exp (-(beta * H)) →
      ∃ psi : ℝ → ℝ, Continuous psi ∧ (∀ u, psi (u + 1) = psi u + 2 * L) ∧
        ∀ p q : Data, (∀ u, p.1 u = interpCurve j0 a0 L (2 * L * u)) →
          (∀ u, q.1 u = interpCurve j1 a0 L (psi u)) → pathDist p q ≤ eta := by
  obtain ⟨delta, hdelta, hmain⟩ :=
    exists_delta_pathDist_le_of_L1 (kstar := kstar) (kd := kd) hL hkd heta
  refine ⟨Real.log (2 * C / delta) / beta, ?_⟩
  intro H hH j0 j1 j0' j1' a0 hj0 hj1 hj0' hj1' hper0 hper1 htot0 htot1 hdd0 hdd1 hkd0 hkd1
    hj0nn hj1nn hj0le hj1le hexp
  refine hmain j0 j1 j0' j1' a0 hj0 hj1 hj0' hj1' hper0 hper1 htot0 htot1 hdd0 hdd1
    hkd0 hkd1 hj0nn hj1nn hj0le hj1le (lt_of_le_of_lt hexp ?_)
  -- `C e^{−βH} < δ` beyond the threshold
  have hlog : Real.log (2 * C / delta) ≤ beta * H := by
    rw [ge_iff_le, div_le_iff₀ hbeta] at hH
    linarith [hH, mul_comm H beta]
  have hexplt : Real.exp (-(beta * H)) ≤ delta / (2 * C) := by
    have h1 : Real.exp (Real.log (2 * C / delta)) ≤ Real.exp (beta * H) :=
      Real.exp_le_exp.mpr hlog
    rw [Real.exp_log (by positivity)] at h1
    have h3 : 1 / Real.exp (beta * H) ≤ 1 / (2 * C / delta) :=
      one_div_le_one_div_of_le (by positivity) h1
    have h4 : 1 / (2 * C / delta) = delta / (2 * C) := by field_simp
    rw [Real.exp_neg, ← one_div]
    rw [h4] at h3
    exact h3
  calc C * Real.exp (-(beta * H)) ≤ C * (delta / (2 * C)) :=
        mul_le_mul_of_nonneg_left hexplt hC.le
    _ = delta / 2 := by field_simp
    _ < delta := by linarith

/-! ### Non-vacuity -/

/-- The oval of curvature `1/2 + c cos s`, of half-perimeter `2π`; for `c = 0`
it is the circle of curvature `1/2`. -/
def kwaveAmp (c : ℝ) : ℝ → ℝ := fun s => 1 / 2 + c * Real.cos s

/-- Its derivative. -/
def kwaveAmpDeriv (c : ℝ) : ℝ → ℝ := fun s => -(c * Real.sin s)

theorem continuous_kwaveAmp (c : ℝ) : Continuous (kwaveAmp c) := by
  unfold kwaveAmp; fun_prop

theorem continuous_kwaveAmpDeriv (c : ℝ) : Continuous (kwaveAmpDeriv c) := by
  unfold kwaveAmpDeriv; fun_prop

theorem hasDerivAt_kwaveAmp (c r : ℝ) : HasDerivAt (kwaveAmp c) (kwaveAmpDeriv c r) r := by
  have h : HasDerivAt (fun s : ℝ => 1 / 2 + c * Real.cos s) (0 + c * -Real.sin r) r :=
    (hasDerivAt_const r (1/2 : ℝ)).add ((Real.hasDerivAt_cos r).const_mul c)
  have heq : (0 + c * -Real.sin r) = kwaveAmpDeriv c r := by
    simp [kwaveAmpDeriv]
  rw [heq] at h
  exact h

theorem kwaveAmp_periodic (c : ℝ) : Function.Periodic (kwaveAmp c) (2 * Real.pi) := fun x => by
  simp [kwaveAmp, Real.cos_add_two_pi]

theorem kwaveAmp_total (c : ℝ) : (∫ r in (0:ℝ)..(2 * Real.pi), kwaveAmp c r) = Real.pi := by
  have h : (∫ r in (0:ℝ)..(2 * Real.pi), kwaveAmp c r)
      = (∫ _ in (0:ℝ)..(2 * Real.pi), (1/2 : ℝ))
        + ∫ r in (0:ℝ)..(2 * Real.pi), c * Real.cos r := by
    rw [← intervalIntegral.integral_add intervalIntegrable_const
      (Continuous.intervalIntegrable (by fun_prop) _ _)]
    rfl
  rw [h, intervalIntegral.integral_const_mul, integral_cos]
  simp
  ring

/-- **The `L¹` bound is not vacuous.**  For every tolerance `η > 0` there is an
amplitude `c > 0` for which the circle of curvature `1/2` and the *genuinely
noncircular* oval of curvature `1/2 + c cos s`, both of half-perimeter `2π`,
satisfy every hypothesis of `exists_delta_pathDist_le_of_L1`, and the two marked
curves it speaks of exist and are at path pseudodistance at most `η`. -/
theorem exists_delta_pathDist_le_of_L1_instance {eta : ℝ} (heta : 0 < eta) :
    ∃ (c : ℝ) (psi : ℝ → ℝ) (p q : Data), 0 < c ∧ kwaveAmp c 0 ≠ kcirc 0 ∧
      (∀ u, psi (u + 1) = psi u + 2 * (2 * Real.pi)) ∧
      (∀ u, p.1 u = interpCurve kcirc 0 (2 * Real.pi) (2 * (2 * Real.pi) * u)) ∧
      (∀ u, q.1 u = interpCurve (kwaveAmp c) 0 (2 * Real.pi) (psi u)) ∧
      pathDist p q ≤ eta := by
  have hpi : (0:ℝ) < 2 * Real.pi := by positivity
  obtain ⟨delta, hdelta, hmain⟩ :=
    exists_delta_pathDist_le_of_L1 (kstar := 3/4) (kd := 1/4) (L := 2 * Real.pi)
      hpi (by norm_num) heta
  set c : ℝ := min (1/4) (delta / (4 * Real.pi)) with hc
  have hcpos : 0 < c := lt_min (by norm_num) (by positivity)
  have hcle : c ≤ 1/4 := min_le_left _ _
  have hcsmall : 2 * Real.pi * c < delta := by
    have h : c ≤ delta / (4 * Real.pi) := min_le_right _ _
    have hmul : 2 * Real.pi * c ≤ 2 * Real.pi * (delta / (4 * Real.pi)) :=
      mul_le_mul_of_nonneg_left h hpi.le
    have heq : 2 * Real.pi * (delta / (4 * Real.pi)) = delta / 2 := by
      field_simp
      ring
    rw [heq] at hmul
    linarith
  -- the `L¹` distance of the two curvatures is at most `2πc`
  have hL1 : curvDist kcirc (kwaveAmp c) (2 * Real.pi) < delta := by
    have hmono : (∫ r in (0:ℝ)..(2 * Real.pi), |kwaveAmp c r - kcirc r|)
        ≤ ∫ _ in (0:ℝ)..(2 * Real.pi), c := by
      refine intervalIntegral.integral_mono_on hpi.le
        (((continuous_kwaveAmp c).sub continuous_kcirc).abs.intervalIntegrable _ _)
        intervalIntegrable_const ?_
      intro r _
      have h1 := Real.neg_one_le_cos r
      have h2 := Real.cos_le_one r
      rw [abs_le]
      constructor <;> simp only [kwaveAmp, kcirc] <;> nlinarith [hcpos.le]
    have hconst : (∫ _ in (0:ℝ)..(2 * Real.pi), c) = 2 * Real.pi * c := by simp
    have hle : curvDist kcirc (kwaveAmp c) (2 * Real.pi) ≤ 2 * Real.pi * c := by
      rw [← hconst]
      exact hmono
    linarith
  obtain ⟨psi, hcont, htrans, hbound⟩ :=
    hmain kcirc (kwaveAmp c) (fun _ => 0) (kwaveAmpDeriv c) 0
      continuous_kcirc (continuous_kwaveAmp c) continuous_const (continuous_kwaveAmpDeriv c)
      kcirc_periodic (kwaveAmp_periodic c) kcirc_total (kwaveAmp_total c)
      hasDerivAt_kcirc (hasDerivAt_kwaveAmp c)
      (fun r => by norm_num)
      (fun r => by
        have h1 := Real.neg_one_le_sin r
        have h2 := Real.sin_le_one r
        rw [abs_le]
        constructor <;> simp only [kwaveAmpDeriv] <;> nlinarith [hcpos.le])
      kcirc_nonneg
      (fun r => by
        have h1 := Real.neg_one_le_cos r
        simp only [kwaveAmp]
        nlinarith [hcpos.le])
      kcirc_le
      (fun r => by
        have h2 := Real.cos_le_one r
        simp only [kwaveAmp]
        nlinarith [hcpos.le])
      hL1
  -- both curves are continuous and of period one
  have hXcd : Differentiable ℝ (interpCurve kcirc 0 (2 * Real.pi)) := fun s =>
    (hasDerivAt_interpCurve (θ₀ := 0) (L := 2 * Real.pi) continuous_kcirc s).differentiableAt
  have hXwd : Differentiable ℝ (interpCurve (kwaveAmp c) 0 (2 * Real.pi)) := fun s =>
    (hasDerivAt_interpCurve (θ₀ := 0) (L := 2 * Real.pi) (continuous_kwaveAmp c) s).differentiableAt
  have hXcper : Function.Periodic (interpCurve kcirc 0 (2 * Real.pi)) (2 * (2 * Real.pi)) :=
    interpCurve_periodic (θ₀ := 0) continuous_kcirc kcirc_periodic kcirc_total
  have hXwper : Function.Periodic (interpCurve (kwaveAmp c) 0 (2 * Real.pi))
      (2 * (2 * Real.pi)) :=
    interpCurve_periodic (θ₀ := 0) (continuous_kwaveAmp c) (kwaveAmp_periodic c)
      (kwaveAmp_total c)
  obtain ⟨p, hp⟩ := exists_data_of_periodic_curve
    (g := fun u => interpCurve kcirc 0 (2 * Real.pi) (2 * (2 * Real.pi) * u))
    (hXcd.continuous.comp (continuous_const.mul continuous_id)) (fun u => by
      have h : 2 * (2 * Real.pi) * (u + 1) = 2 * (2 * Real.pi) * u + 2 * (2 * Real.pi) := by ring
      simp only [h]
      exact hXcper _)
  obtain ⟨q, hq⟩ := exists_data_of_periodic_curve
    (g := fun u => interpCurve (kwaveAmp c) 0 (2 * Real.pi) (psi u))
    (hXwd.continuous.comp hcont) (fun u => by
      simp only [htrans u]
      exact hXwper _)
  refine ⟨c, psi, p, q, hcpos, ?_, htrans, hp, hq, hbound p q hp hq⟩
  simp only [kwaveAmp, kcirc, Real.cos_zero, mul_one]
  linarith

end InterpolationPathDistL1
