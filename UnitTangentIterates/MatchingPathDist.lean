import Mathlib
import UnitTangentIterates.MatchingComplete
import UnitTangentIterates.InterpolationPathDistSummable

/-!
# The matching estimate in the marked path pseudodistance

`MatchingComplete.curvature_measure_matching_complete` proves the theorem
*Curvature-measure matching* of *A Noncircular Oval with Convex Unit-Tangent
Iterates* in the form

```
  ∫_{J_H} |k_H − K_P| ≤ C e^{−βH} ,
```

an `L¹` comparison of the two curvatures over **one fundamental interval**
`J_H = [x_H(−H/2), x_H(−H/2) + P]`, of length `P`.
`MatchingMarkedDistance.lean` feeds that estimate into the sup metric of the
space of marked curves; this file feeds it instead into the **marked geometric
path pseudodistance** `PathMetric.pathDist`, which is the metric in which the
selected inverse of the paper is non-expansive.

The passage is `InterpolationPathDistSummable.pathDist_le_interpCostL1`: two
`P`-periodic curvatures, nonnegative, bounded by `κ_*`, with derivatives bounded
by `k'` and total turning `π` over one period, define two marked ovals of
half-perimeter `P` at path pseudodistance at most

`interpCostL1 κ_* k' P ε₀ ε = A·ε + B·(√(4k'ε) + 4ε/P)`,

`ε` being the `L¹` distance `curvDist` of the two curvatures over `[0, P]`.
The one piece of glue needed is that the window of the matching estimate is not
`[0, P]`: for `P`-periodic curvatures the `L¹` distance over any window of
length `P` is the same (`curvDist_eq_of_periodic`), so the matching estimate
bounds `curvDist` itself (`curvDist_le_of_matching`).

Results:

* `curvDist_eq_of_periodic`, `curvDist_le_window` — the `L¹` distance over one
  fundamental interval **is** `curvDist`;
* `interpCostL1_mono` — the cost bound is monotone in the `L¹` distance, so the
  matching estimate may be substituted for it;
* `curvDist_le_of_matching` — the matching configuration bounds `curvDist` by
  `C e^{−βH}` with the explicit constant of the matching theorem;
* `pathDist_le_of_matching` — hence the two marked ovals carrying the two
  curvatures of a matching configuration are at path pseudodistance at most
  `interpCostL1 κ_* k' P ε₀ (Ce^{−βH})`;
* `tendsto_interpCostL1_exp`, `exists_threshold_interpCostL1_le` — that bound
  tends to `0` as the separation `H` grows, so beyond an explicit threshold the
  two ovals are at path pseudodistance below any prescribed tolerance.

As in `MatchingMarkedDistance.lean`, the statement of `pathDist_le_of_matching`
carries two blocks of hypotheses — those of the matching estimate and those of
the two curvatures as curvatures of ovals — whose *joint* satisfiability is not
checked here; the identification of the two marked curves of a matching
configuration with the `n`-th model and the selected inverse of the `(n+1)`-st
is exactly what the project still lacks, so the paper's main theorem remains
**not** formalized.
-/

noncomputable section

open Real MeasureTheory Set Function MarkedSpace PathMetric

namespace MatchingPathDist

open FrontPeriodization MatchingExponential MatchingComplete
  CurvatureInterpolation InterpolationEstimate InterpolationPathDist
  InterpolationPathDistL1 InterpolationPathDistSummable

/-! ### The `L¹` distance over an arbitrary window of one period -/

/-- For two `P`-periodic curvatures the `L¹` distance over the window
`[c, c + P]` is the `L¹` distance `curvDist` over `[0, P]`. -/
theorem curvDist_eq_of_periodic {k0 k1 : ℝ → ℝ} {P : ℝ}
    (hper0 : Periodic k0 P) (hper1 : Periodic k1 P) (c : ℝ) :
    (∫ u in c..(c + P), |k0 u - k1 u|) = curvDist k0 k1 P := by
  have hper : Periodic (fun u => |k0 u - k1 u|) P := by
    intro u
    simp only [hper0 u, hper1 u]
  have h := hper.intervalIntegral_add_eq c 0
  rw [curvDist]
  simp_rw [abs_sub_comm]
  simpa using h

/-- The matching estimate, given over one fundamental interval, bounds the `L¹`
distance `curvDist` of the two `P`-periodic curvatures. -/
theorem curvDist_le_window {k0 k1 : ℝ → ℝ} {P c eps : ℝ}
    (hper0 : Periodic k0 P) (hper1 : Periodic k1 P)
    (h : (∫ u in c..(c + P), |k0 u - k1 u|) ≤ eps) :
    curvDist k0 k1 P ≤ eps := by
  rwa [curvDist_eq_of_periodic hper0 hper1 c] at h

/-! ### Monotonicity of the cost bound -/

/-- The explicit cost bound `interpCostL1` is monotone in the `L¹` distance. -/
theorem interpCostL1_mono {kstar kd L eps0 e1 e2 : ℝ} (hkstar : 0 ≤ kstar) (hkd : 0 ≤ kd)
    (hL : 0 < L) (heps0 : 0 ≤ eps0) (h12 : e1 ≤ e2) :
    interpCostL1 kstar kd L eps0 e1 ≤ interpCostL1 kstar kd L eps0 e2 := by
  have hA : 0 ≤ costEpsCoeff kstar kd L eps0 := costEpsCoeff_nonneg hkstar hkd hL.le heps0
  have hB : 0 ≤ costSupCoeff kstar L eps0 := costSupCoeff_nonneg
  have hsqrt : Real.sqrt (4 * kd * e1) ≤ Real.sqrt (4 * kd * e2) := by
    apply Real.sqrt_le_sqrt
    have : (0:ℝ) ≤ 4 * kd := by linarith
    nlinarith
  have hdiv : 4 * e1 / L ≤ 4 * e2 / L := by gcongr
  unfold interpCostL1
  have h1 : costEpsCoeff kstar kd L eps0 * e1 ≤ costEpsCoeff kstar kd L eps0 * e2 :=
    mul_le_mul_of_nonneg_left h12 hA
  have h2 : costSupCoeff kstar L eps0 * (Real.sqrt (4 * kd * e1) + 4 * e1 / L)
      ≤ costSupCoeff kstar L eps0 * (Real.sqrt (4 * kd * e2) + 4 * e2 / L) :=
    mul_le_mul_of_nonneg_left (by linarith) hB
  linarith

/-! ### The matching estimate as a bound for `curvDist` -/

/-- **The matching configuration bounds the `L¹` distance of the two
curvatures.**  All the hypotheses of
`MatchingComplete.curvature_measure_matching_complete` are kept, and the two
curvatures are moreover assumed `P`-periodic; then their `L¹` distance over one
period is at most `C e^{−βH}`, `C` the explicit constant of the matching
theorem. -/
theorem curvDist_le_of_matching
    {Y y xH x Kstar Kstar' kH Kbar KP yu yu' : ℝ → ℝ}
    {a au C CU CK DU alpha beta H P B Km Kd : ℝ}
    (ha : 0 < alpha) (hy0 : ∀ s, 0 ≤ y s) (hyb : ∀ s, y s ≤ C * Real.exp (-alpha * |s|))
    (hH : 0 < H) (hq2 : Real.exp (-alpha * H) ≤ 1 / 2)
    (hYdef : ∀ s, Y s = ∑' m : ℤ, y (s - m * H))
    (ha0 : 0 ≤ a) (ha1 : a < 1)
    (hY : Continuous Y) (hy : Continuous y)
    (hYa : ∀ s, |Y s| ≤ a) (hya : ∀ s, |y s| ≤ a)
    (hxH : ∀ t, HasDerivAt xH (Real.sqrt (1 - (Y t) ^ 2)) t)
    (hx : ∀ t, HasDerivAt x (Real.sqrt (1 - (y t) ^ 2)) t)
    (h0 : xH 0 = x 0)
    (hid : ∀ t, y t = Real.sqrt (1 - (y t) ^ 2) * Kstar (x t))
    (hK : ∀ u, |Kstar u| ≤ Km) (hKderiv : ∀ u, HasDerivAt Kstar (Kstar' u) u)
    (hKd' : ∀ u, |Kstar' u| ≤ Kd) (hKcont : Continuous Kstar)
    (hbeta0 : 0 < beta) (hbeta : beta < alpha / 2)
    (hk : ∀ t, kH (xH t) * Real.sqrt (1 - (Y t) ^ 2) = Y t)
    (hkcont : Continuous fun u => |kH u - Kbar u|)
    (hKbar : ∀ u, Kbar u = Kstar u + ∑' j : {j : ℤ // j ≠ 0}, Kstar (u - (j : ℤ) * P))
    (hD : IntervalIntegrable
      (fun s => Real.sqrt (1 - (Y s) ^ 2) *
        ∑' j : {j : ℤ // j ≠ 0}, Kstar (xH s - (j : ℤ) * P)) volume (-(H / 2)) (H / 2))
    (hi0 : IntervalIntegrable (fun u => |kH u - KP u|) volume (xH (-(H / 2))) (xH (H / 2)))
    (hi2 : IntervalIntegrable (fun u => |Kbar u - KP u|) volume (xH (-(H / 2))) (xH (H / 2)))
    (hPeriod : xH (H / 2) = xH (-(H / 2)) + P) (hPpos : 0 < P)
    (hKint : Integrable Kstar) (hK0 : ∀ u, 0 ≤ Kstar u)
    (hKbd : ∀ s, |Kstar s| ≤ CK * Real.exp (-alpha * |s|))
    (hp : xH (-(H / 2)) ≤ 0) (hqe : 0 ≤ xH (-(H / 2)) + P)
    (hpB : xH (-(H / 2)) ≤ -(H / 2) + B) (hqB : H / 2 - B ≤ xH (-(H / 2)) + P)
    (hhalf : Real.exp (-(beta * P)) ≤ 1 / 2)
    (hyu : Continuous yu) (hyu' : Continuous yu')
    (hyu0 : ∀ s, 0 ≤ yu s) (hyub : ∀ s, yu s ≤ CU * Real.exp (-alpha * |s|))
    (hDU : 0 ≤ DU) (hyu'b : ∀ s, |yu' s| ≤ DU * yu s)
    (hau0 : 0 ≤ au) (hau1 : au < 1) (hYau : ∀ u, (∑' m : ℤ, yu (u - m * P)) ≤ au)
    (hKstaru : ∀ s, Kstar s = yu s + G (yu s) * yu' s)
    (hKPu : ∀ u, KP u = (∑' m : ℤ, yu (u - m * P))
      + G (∑' m : ℤ, yu (u - m * P)) * (∑' m : ℤ, yu' (u - m * P)))
    (hPH : H - 2 * B ≤ P)
    (hperp : Periodic kH P) (hperq : Periodic KP P) :
    curvDist kH KP P
      ≤ (pulseConst C Km Kd (a / Real.sqrt (1 - a ^ 2)) alpha beta
          + rearTailConst CK alpha B + frontConst au CU DU alpha beta B)
        * Real.exp (-(beta * H)) := by
  have hmatch := curvature_measure_matching_complete ha hy0 hyb hH hq2 hYdef ha0 ha1 hY hy
    hYa hya hxH hx h0 hid hK hKderiv hKd' hKcont hbeta0 hbeta hk hkcont hKbar hD hi0 hi2
    hPeriod hPpos hKint hK0 hKbd hp hqe hpB hqB hhalf hyu hyu' hyu0 hyub hDU hyu'b hau0
    hau1 hYau hKstaru hKPu hPH
  rw [hPeriod] at hmatch
  exact curvDist_le_window hperp hperq hmatch

/-! ### The path-distance bound -/

/-- **The matching estimate in the marked path pseudodistance.**  All the
hypotheses of the matching theorem are kept, and the two curvatures are carried
by two marked ovals of half-perimeter `P`: both curvatures are `P`-periodic,
nonnegative, bounded by `κ_*`, of total turning `π` over one period and with
derivatives bounded by `k'`.  Then the two marked curves are at path
pseudodistance at most `interpCostL1 κ_* k' P ε₀ (Ce^{−βH})`, `C` being the
explicit constant of the matching theorem. -/
theorem pathDist_le_of_matching
    {Y y xH x Kstar Kstar' kH Kbar KP yu yu' : ℝ → ℝ}
    {a au C CU CK DU alpha beta H P B Km Kd : ℝ}
    (ha : 0 < alpha) (hy0 : ∀ s, 0 ≤ y s) (hyb : ∀ s, y s ≤ C * Real.exp (-alpha * |s|))
    (hH : 0 < H) (hq2 : Real.exp (-alpha * H) ≤ 1 / 2)
    (hYdef : ∀ s, Y s = ∑' m : ℤ, y (s - m * H))
    (ha0 : 0 ≤ a) (ha1 : a < 1)
    (hY : Continuous Y) (hy : Continuous y)
    (hYa : ∀ s, |Y s| ≤ a) (hya : ∀ s, |y s| ≤ a)
    (hxH : ∀ t, HasDerivAt xH (Real.sqrt (1 - (Y t) ^ 2)) t)
    (hx : ∀ t, HasDerivAt x (Real.sqrt (1 - (y t) ^ 2)) t)
    (h0 : xH 0 = x 0)
    (hid : ∀ t, y t = Real.sqrt (1 - (y t) ^ 2) * Kstar (x t))
    (hK : ∀ u, |Kstar u| ≤ Km) (hKderiv : ∀ u, HasDerivAt Kstar (Kstar' u) u)
    (hKd' : ∀ u, |Kstar' u| ≤ Kd) (hKcont : Continuous Kstar)
    (hbeta0 : 0 < beta) (hbeta : beta < alpha / 2)
    (hk : ∀ t, kH (xH t) * Real.sqrt (1 - (Y t) ^ 2) = Y t)
    (hkcont : Continuous fun u => |kH u - Kbar u|)
    (hKbar : ∀ u, Kbar u = Kstar u + ∑' j : {j : ℤ // j ≠ 0}, Kstar (u - (j : ℤ) * P))
    (hD : IntervalIntegrable
      (fun s => Real.sqrt (1 - (Y s) ^ 2) *
        ∑' j : {j : ℤ // j ≠ 0}, Kstar (xH s - (j : ℤ) * P)) volume (-(H / 2)) (H / 2))
    (hi0 : IntervalIntegrable (fun u => |kH u - KP u|) volume (xH (-(H / 2))) (xH (H / 2)))
    (hi2 : IntervalIntegrable (fun u => |Kbar u - KP u|) volume (xH (-(H / 2))) (xH (H / 2)))
    (hPeriod : xH (H / 2) = xH (-(H / 2)) + P) (hPpos : 0 < P)
    (hKint : Integrable Kstar) (hK0 : ∀ u, 0 ≤ Kstar u)
    (hKbd : ∀ s, |Kstar s| ≤ CK * Real.exp (-alpha * |s|))
    (hp : xH (-(H / 2)) ≤ 0) (hqe : 0 ≤ xH (-(H / 2)) + P)
    (hpB : xH (-(H / 2)) ≤ -(H / 2) + B) (hqB : H / 2 - B ≤ xH (-(H / 2)) + P)
    (hhalf : Real.exp (-(beta * P)) ≤ 1 / 2)
    (hyu : Continuous yu) (hyu' : Continuous yu')
    (hyu0 : ∀ s, 0 ≤ yu s) (hyub : ∀ s, yu s ≤ CU * Real.exp (-alpha * |s|))
    (hDU : 0 ≤ DU) (hyu'b : ∀ s, |yu' s| ≤ DU * yu s)
    (hau0 : 0 ≤ au) (hau1 : au < 1) (hYau : ∀ u, (∑' m : ℤ, yu (u - m * P)) ≤ au)
    (hKstaru : ∀ s, Kstar s = yu s + G (yu s) * yu' s)
    (hKPu : ∀ u, KP u = (∑' m : ℤ, yu (u - m * P))
      + G (∑' m : ℤ, yu (u - m * P)) * (∑' m : ℤ, yu' (u - m * P)))
    (hPH : H - 2 * B ≤ P)
    -- the two curvatures as curvatures of marked ovals of half-perimeter `P`
    {kH' KP' : ℝ → ℝ} {theta0 kstar kd eps0 : ℝ}
    (hkHc : Continuous kH) (hKPc : Continuous KP)
    (hkH'c : Continuous kH') (hKP'c : Continuous KP')
    (hperp : Periodic kH P) (hperq : Periodic KP P)
    (htot0 : (∫ r in (0:ℝ)..P, kH r) = Real.pi)
    (htot1 : (∫ r in (0:ℝ)..P, KP r) = Real.pi)
    (hkd : 0 < kd) (hkstar : 0 ≤ kstar)
    (hd0 : ∀ r, HasDerivAt kH (kH' r) r) (hd1 : ∀ r, HasDerivAt KP (KP' r) r)
    (hkd0 : ∀ r, |kH' r| ≤ kd) (hkd1 : ∀ r, |KP' r| ≤ kd)
    (hk0nn : ∀ r, 0 ≤ kH r) (hk1nn : ∀ r, 0 ≤ KP r)
    (hk0le : ∀ r, kH r ≤ kstar) (hk1le : ∀ r, KP r ≤ kstar)
    (heps0 : (pulseConst C Km Kd (a / Real.sqrt (1 - a ^ 2)) alpha beta
        + rearTailConst CK alpha B + frontConst au CU DU alpha beta B)
      * Real.exp (-(beta * H)) ≤ eps0) :
    ∃ psi : ℝ → ℝ, Continuous psi ∧ (∀ u, psi (u + 1) = psi u + 2 * P) ∧
      ∀ p q : Data, (∀ u, p.1 u = interpCurve kH theta0 P (2 * P * u)) →
        (∀ u, q.1 u = interpCurve KP theta0 P (psi u)) →
        pathDist p q ≤ interpCostL1 kstar kd P eps0
          ((pulseConst C Km Kd (a / Real.sqrt (1 - a ^ 2)) alpha beta
              + rearTailConst CK alpha B + frontConst au CU DU alpha beta B)
            * Real.exp (-(beta * H))) := by
  have hcurv : curvDist kH KP P
      ≤ (pulseConst C Km Kd (a / Real.sqrt (1 - a ^ 2)) alpha beta
          + rearTailConst CK alpha B + frontConst au CU DU alpha beta B)
        * Real.exp (-(beta * H)) :=
    curvDist_le_of_matching ha hy0 hyb hH hq2 hYdef ha0 ha1 hY hy hYa hya hxH hx h0 hid
      hK hKderiv hKd' hKcont hbeta0 hbeta hk hkcont hKbar hD hi0 hi2 hPeriod hPpos hKint
      hK0 hKbd hp hqe hpB hqB hhalf hyu hyu' hyu0 hyub hDU hyu'b hau0 hau1 hYau hKstaru
      hKPu hPH hperp hperq
  have hcurvnn : 0 ≤ curvDist kH KP P :=
    InterpolationNormal.integral_abs_sub_nonneg hkHc hKPc hPpos.le
  have heps0nn : 0 ≤ eps0 := le_trans (le_trans hcurvnn hcurv) heps0
  obtain ⟨psi, hcont, htrans, hbound⟩ :=
    pathDist_le_interpCostL1 (θ₀ := theta0) (kstar := kstar) (kd := kd) (eps0 := eps0)
      hkHc hKPc hkH'c hKP'c hperp hperq htot0 htot1 hPpos hkd hkstar hd0 hd1 hkd0 hkd1
      hk0nn hk1nn hk0le hk1le (le_trans hcurv heps0)
  refine ⟨psi, hcont, htrans, fun p q hp hq => le_trans (hbound p q hp hq) ?_⟩
  exact interpCostL1_mono hkstar hkd.le hPpos heps0nn hcurv

/-! ### The bound vanishes as the separation grows -/

/-- The cost bound produced by an exponentially small `L¹` distance tends to
zero as the separation `H` grows. -/
theorem tendsto_interpCostL1_exp {kstar kd L eps0 C beta : ℝ}
    (hL : 0 < L) (hbeta : 0 < beta) :
    Filter.Tendsto (fun H : ℝ => interpCostL1 kstar kd L eps0 (C * Real.exp (-(beta * H))))
      Filter.atTop (nhds 0) := by
  have hexp : Filter.Tendsto (fun H : ℝ => C * Real.exp (-(beta * H)))
      Filter.atTop (nhds 0) := by
    have hmul : Filter.Tendsto (fun H : ℝ => beta * H) Filter.atTop Filter.atTop :=
      Filter.Tendsto.const_mul_atTop hbeta Filter.tendsto_id
    have h2 : Filter.Tendsto (fun H : ℝ => -(beta * H)) Filter.atTop Filter.atBot :=
      Filter.tendsto_neg_atTop_atBot.comp hmul
    have h1 : Filter.Tendsto (fun H : ℝ => Real.exp (-(beta * H))) Filter.atTop (nhds 0) :=
      Real.tendsto_exp_atBot.comp h2
    simpa using h1.const_mul C
  have hcont : ContinuousAt (fun e : ℝ => interpCostL1 kstar kd L eps0 e) 0 := by
    unfold interpCostL1
    fun_prop (disch := exact hL.ne')
  have h := hcont.tendsto.comp hexp
  have hzero : interpCostL1 kstar kd L eps0 0 = 0 := by
    simp [interpCostL1]
  rw [hzero] at h
  exact h

/-- **Beyond an explicit threshold in the separation the cost bound is below any
prescribed tolerance.**  Combined with `pathDist_le_of_matching`, this puts the
two marked ovals of a matching configuration of large separation at path
pseudodistance at most `η`. -/
theorem exists_threshold_interpCostL1_le {kstar kd L eps0 C beta eta : ℝ}
    (hL : 0 < L) (hbeta : 0 < beta) (heta : 0 < eta) :
    ∃ H₀ : ℝ, ∀ H ≥ H₀,
      interpCostL1 kstar kd L eps0 (C * Real.exp (-(beta * H))) ≤ eta := by
  have h := tendsto_interpCostL1_exp (kstar := kstar) (kd := kd) (L := L) (eps0 := eps0)
    (C := C) hL hbeta
  have hev : ∀ᶠ H : ℝ in Filter.atTop,
      interpCostL1 kstar kd L eps0 (C * Real.exp (-(beta * H))) ≤ eta :=
    h.eventually (eventually_le_nhds heta)
  obtain ⟨H₀, hH₀⟩ := Filter.eventually_atTop.1 hev
  exact ⟨H₀, hH₀⟩

end MatchingPathDist
