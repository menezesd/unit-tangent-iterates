import Mathlib
import UnitTangentIterates.MarkedSpace

/-!
# The chord-arc bound of an embedded closed curve

Membership in the tube of marked curves of *A Noncircular Oval with Convex
Unit-Tangent Iterates* (`MarkedSpace.lean`) asks for the quantitative
chord-arc bound

```
  delta · cyc u v ≤ ‖X u − X v‖ ,      cyc u v = min |u−v| (1 − |u−v|) ,
```

which is a closed (uniform) form of embeddedness.  Everywhere in the project so
far it has been carried as a hypothesis.  This file **produces** it: a closed
`C¹` curve of period one whose speed is bounded below and which is injective on
one period satisfies such a bound for some constant `delta > 0`.

The proof is the usual two-scale argument:

* `exists_unif_bound` : a continuous periodic velocity is uniformly continuous
  on the whole line;
* `norm_sub_ge_of_close` : hence at scales where the velocity varies by less
  than half of its lower bound, the chord is at least `(c/2)|x−y|` — the
  near-diagonal estimate;
* `exists_chord_arc` : away from the diagonal `‖X u − X v‖` is a positive
  continuous function on a compact set, so it has a positive minimum; combining
  the two scales gives the chord-arc bound.
-/

noncomputable section

open Set Function

namespace ChordArc

/-- The cyclic distance is symmetric. -/
theorem cyc_comm (u v : ℝ) : MarkedSpace.cyc u v = MarkedSpace.cyc v u := by
  simp [MarkedSpace.cyc, abs_sub_comm]

/-- For parameters in `[0,1]` the cyclic distance is nonnegative. -/
theorem cyc_nonneg {u v : ℝ} (hu : u ∈ Icc (0:ℝ) 1) (hv : v ∈ Icc (0:ℝ) 1) :
    0 ≤ MarkedSpace.cyc u v := by
  have habs : |u - v| ≤ 1 := by
    rw [abs_le]
    constructor <;> [linarith [hu.1, hu.2, hv.1, hv.2]; linarith [hu.1, hu.2, hv.1, hv.2]]
  exact le_min (abs_nonneg _) (by linarith)

/-- The cyclic distance is at most one. -/
theorem cyc_le_one (u v : ℝ) : MarkedSpace.cyc u v ≤ 1 := by
  have : MarkedSpace.cyc u v ≤ 1 - |u - v| := min_le_right _ _
  linarith [abs_nonneg (u - v)]

/-- A continuous periodic function is uniformly continuous on the whole line:
for every `e > 0` there is a scale `d₀ ∈ (0,1]` at which `V` varies by at most
`e`. -/
theorem exists_unif_bound {V : ℝ → ℂ} (hVc : Continuous V) (hVper : Periodic V 1)
    {e : ℝ} (he : 0 < e) :
    ∃ d0 : ℝ, 0 < d0 ∧ d0 ≤ 1 ∧ ∀ x y : ℝ, |x - y| ≤ d0 → ‖V x - V y‖ ≤ e := by
  have hcpt : IsCompact (Icc (-1 : ℝ) 2) := isCompact_Icc
  have huc : UniformContinuousOn V (Icc (-1 : ℝ) 2) :=
    hcpt.uniformContinuousOn_of_continuous hVc.continuousOn
  rw [Metric.uniformContinuousOn_iff] at huc
  obtain ⟨d, hd, hdle⟩ := huc e he
  refine ⟨min (d / 2) 1, by positivity, min_le_right _ _, ?_⟩
  intro x y hxy
  -- shift both points by the integer `⌊x⌋`, using periodicity
  set n : ℤ := ⌊x⌋ with hn
  have hVshift : ∀ z : ℝ, V (z - n) = V z := by
    intro z
    simpa using (Function.Periodic.sub_int_mul_eq (x := z) hVper n)
  have hx' : x - n ∈ Icc (-1 : ℝ) 2 := by
    have h1 := Int.floor_le x
    have h2 := Int.lt_floor_add_one x
    constructor <;> [linarith; linarith]
  have hxyle : |x - y| ≤ 1 := le_trans hxy (min_le_right _ _)
  have hy' : y - n ∈ Icc (-1 : ℝ) 2 := by
    have h1 := Int.floor_le x
    have h2 := Int.lt_floor_add_one x
    have := abs_le.mp hxyle
    constructor <;> [linarith [this.1, this.2]; linarith [this.1, this.2]]
  have hdist : dist (x - n) (y - n) < d := by
    rw [Real.dist_eq]
    have : x - (n : ℝ) - (y - n) = x - y := by ring
    rw [this]
    exact lt_of_le_of_lt hxy (lt_of_le_of_lt (min_le_left _ _) (by linarith))
  have h := hdle _ hx' _ hy' hdist
  rw [dist_eq_norm, hVshift x, hVshift y] at h
  exact h.le

/-- **The near-diagonal estimate.**  If the velocity varies by at most `c/2` at
scale `d₀` and has norm at least `c`, then the chord over a parameter interval
of length at most `d₀` is at least `(c/2)` times that length. -/
theorem norm_sub_ge_of_close {g V : ℝ → ℂ} {c d0 : ℝ}
    (hg : ∀ u, HasDerivAt g (V u) u) (hVc : Continuous V)
    (hspeed : ∀ u, c ≤ ‖V u‖)
    (hunif : ∀ x y : ℝ, |x - y| ≤ d0 → ‖V x - V y‖ ≤ c / 2)
    (x y : ℝ) (hxy : |x - y| ≤ d0) : c / 2 * |x - y| ≤ ‖g x - g y‖ := by
  -- reduce to `y ≤ x`
  wlog hle : y ≤ x generalizing x y
  · have h := this y x (by rwa [abs_sub_comm]) (le_of_not_ge hle)
    rwa [abs_sub_comm, norm_sub_rev] at h
  have hint : IntervalIntegrable V MeasureTheory.volume y x :=
    hVc.intervalIntegrable _ _
  have hFTC : (∫ w in y..x, V w) = g x - g y :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun w _ => hg w) hint
  have hsplit : (∫ w in y..x, V w)
      = (∫ w in y..x, (V w - V y)) + (x - y) • V y := by
    rw [intervalIntegral.integral_sub hint (intervalIntegrable_const)]
    simp [intervalIntegral.integral_const, sub_smul]
  have hbound : ‖∫ w in y..x, (V w - V y)‖ ≤ c / 2 * |x - y| := by
    refine intervalIntegral.norm_integral_le_of_norm_le_const ?_
    intro w hw
    have hw' : w ∈ Ioc y x := by rwa [Set.uIoc_of_le hle] at hw
    refine hunif w y ?_
    have h1 : |w - y| = w - y := abs_of_nonneg (by linarith [hw'.1.le])
    have h2 : |x - y| = x - y := abs_of_nonneg (by linarith)
    rw [h1]
    have := hw'.2
    rw [h2] at hxy
    linarith
  have hnormsmul : ‖(x - y) • V y‖ = |x - y| * ‖V y‖ := by
    rw [norm_smul, Real.norm_eq_abs]
  have hlow : c * |x - y| ≤ ‖(x - y) • V y‖ := by
    rw [hnormsmul, mul_comm]
    exact mul_le_mul_of_nonneg_left (hspeed y) (abs_nonneg _)
  have hkey : ‖g x - g y‖ ≥ ‖(x - y) • V y‖ - ‖∫ w in y..x, (V w - V y)‖ := by
    rw [← hFTC, hsplit]
    have := norm_sub_norm_le ((x - y) • V y) (-(∫ w in y..x, (V w - V y)))
    simp only [norm_neg, sub_neg_eq_add] at this
    calc ‖(x - y) • V y‖ - ‖∫ w in y..x, (V w - V y)‖
        ≤ ‖(x - y) • V y + ∫ w in y..x, (V w - V y)‖ := this
      _ = ‖(∫ w in y..x, (V w - V y)) + (x - y) • V y‖ := by rw [add_comm]
  linarith

/-- **Quantitative stability of a prescribed chord constant.**  The near
diagonal is controlled by the speed and a velocity modulus, while away from
the diagonal the old chord estimate absorbs the uniform positional error. -/
theorem chord_arc_stable {g₀ g V : ℝ → ℂ} {c d₀ dlt rho eps : ℝ}
    (hg : ∀ u, HasDerivAt g (V u) u) (hVc : Continuous V)
    (hVper : Periodic V 1) (hgper : Periodic g 1)
    (hspeed : ∀ u, c ≤ ‖V u‖)
    (hunif : ∀ x y, |x - y| ≤ rho → ‖V x - V y‖ ≤ c / 2)
    (hbase : ∀ u ∈ Icc (0 : ℝ) 1, ∀ v ∈ Icc (0 : ℝ) 1,
      d₀ * MarkedSpace.cyc u v ≤ ‖g₀ u - g₀ v‖)
    (hclose : ∀ u, ‖g u - g₀ u‖ ≤ eps)
    (hrho : 0 < rho) (hrhohalf : rho ≤ 1 / 2)
    (hdlt0 : 0 ≤ dlt) (hdltc : dlt ≤ c / 2)
    (hmargin : 2 * eps ≤ (d₀ - dlt) * rho) :
    ∀ u ∈ Icc (0 : ℝ) 1, ∀ v ∈ Icc (0 : ℝ) 1,
      dlt * MarkedSpace.cyc u v ≤ ‖g u - g v‖ := by
  intro u hu v hv
  by_cases hfar : rho ≤ MarkedSpace.cyc u v
  · have hb := hbase u hu v hv
    have herr : ‖g₀ u - g₀ v‖ ≤ ‖g u - g v‖ + 2 * eps := by
      calc
        ‖g₀ u - g₀ v‖ = ‖(g₀ u - g u) + (g u - g v) + (g v - g₀ v)‖ := by congr 1 <;> ring
        _ ≤ ‖g₀ u - g u‖ + ‖g u - g v‖ + ‖g v - g₀ v‖ := by
          exact (norm_add_le (g₀ u - g u + (g u - g v)) (g v - g₀ v)).trans
            (add_le_add_left (norm_add_le (g₀ u - g u) (g u - g v)) ‖g v - g₀ v‖)
        _ ≤ eps + ‖g u - g v‖ + eps := by
          gcongr
          · simpa [norm_sub_rev] using hclose u
          · exact hclose v
        _ = ‖g u - g v‖ + 2 * eps := by ring
    have hcyc0 := cyc_nonneg hu hv
    have heps0 : 0 ≤ eps := (norm_nonneg (g u - g₀ u)).trans (hclose u)
    have hcoef0 : 0 ≤ d₀ - dlt := by
      by_contra hcoef
      have hmneg : (d₀ - dlt) * rho < 0 :=
        mul_neg_of_neg_of_pos (lt_of_not_ge hcoef) hrho
      linarith
    have hgap : 2 * eps ≤ (d₀ - dlt) * MarkedSpace.cyc u v := by
      exact hmargin.trans (mul_le_mul_of_nonneg_left hfar hcoef0)
    linarith
  · have hnear : MarkedSpace.cyc u v < rho := lt_of_not_ge hfar
    rw [MarkedSpace.cyc] at hnear ⊢
    have habsle : |u - v| ≤ 1 := by
      rw [abs_le]
      constructor <;> linarith [hu.1, hu.2, hv.1, hv.2]
    have hwrapnonneg : 0 ≤ 1 - |u - v| := by linarith
    rcases le_or_gt |u - v| (1 - |u - v|) with hdir | hwrap
    · rw [min_eq_left hdir] at hnear ⊢
      exact (mul_le_mul_of_nonneg_right hdltc (abs_nonneg _)).trans
        (norm_sub_ge_of_close hg hVc hspeed hunif u v hnear.le)
    · rw [min_eq_right hwrap.le] at hnear ⊢
      rcases le_total u v with huv | huv
      · have habs : |u - v| = v - u := by rw [abs_sub_comm]; exact abs_of_nonneg (by linarith)
        have hshift : |u + 1 - v| = 1 - |u - v| := by
          rw [habs, abs_of_nonneg (by linarith [hu.1, hv.2] : 0 ≤ u + 1 - v)]
          ring
        have hn := norm_sub_ge_of_close hg hVc hspeed hunif (u + 1) v (by
          rw [hshift]; exact hnear.le)
        rw [hshift, hgper u] at hn
        exact (mul_le_mul_of_nonneg_right hdltc hwrapnonneg).trans hn
      · have habs : |u - v| = u - v := abs_of_nonneg (by linarith)
        have hshift : |u - (v + 1)| = 1 - |u - v| := by
          rw [abs_of_nonpos (by linarith [hv.1, hu.2] : u - (v + 1) ≤ 0), habs]
          ring
        have hn := norm_sub_ge_of_close hg hVc hspeed hunif u (v + 1) (by
          rw [hshift]; exact hnear.le)
        rw [hshift, hgper v] at hn
        exact (mul_le_mul_of_nonneg_right hdltc hwrapnonneg).trans hn

/-- Acceleration-bounded form of `chord_arc_stable`. -/
theorem chord_arc_stable_of_acc_bound
    {g₀ g V Afield : ℝ → ℂ} {c A d₀ dlt rho eps : ℝ}
    (hg : ∀ u, HasDerivAt g (V u) u)
    (hVd : ∀ u, HasDerivAt V (Afield u) u)
    (hVper : Periodic V 1) (hgper : Periodic g 1)
    (hspeed : ∀ u, c ≤ ‖V u‖) (hAbd : ∀ u, ‖Afield u‖ ≤ A)
    (hbase : ∀ u ∈ Icc (0 : ℝ) 1, ∀ v ∈ Icc (0 : ℝ) 1,
      d₀ * MarkedSpace.cyc u v ≤ ‖g₀ u - g₀ v‖)
    (hclose : ∀ u, ‖g u - g₀ u‖ ≤ eps)
    (hA0 : 0 ≤ A) (hrho : 0 < rho) (hrhohalf : rho ≤ 1 / 2)
    (hArho : A * rho ≤ c / 2) (hdlt0 : 0 ≤ dlt)
    (hdltc : dlt ≤ c / 2) (hmargin : 2 * eps ≤ (d₀ - dlt) * rho) :
    ∀ u ∈ Icc (0 : ℝ) 1, ∀ v ∈ Icc (0 : ℝ) 1,
      dlt * MarkedSpace.cyc u v ≤ ‖g u - g v‖ := by
  have hVc : Continuous V :=
    continuous_iff_continuousAt.mpr fun u => (hVd u).continuousAt
  have hunif : ∀ x y, |x - y| ≤ rho → ‖V x - V y‖ ≤ c / 2 := by
    intro x y hxy
    have hLip := Convex.norm_image_sub_le_of_norm_deriv_le
      (fun z _ => (hVd z).differentiableAt)
      (fun z _ => by rw [(hVd z).deriv]; exact hAbd z) convex_univ
      (Set.mem_univ x) (Set.mem_univ y)
    have hnorm : ‖y - x‖ ≤ rho := by
      simpa [Real.norm_eq_abs, abs_sub_comm] using hxy
    simpa [norm_sub_rev] using
      hLip.trans ((mul_le_mul_of_nonneg_left hnorm hA0).trans hArho)
  exact chord_arc_stable hg hVc hVper hgper hspeed hunif hbase hclose
    hrho hrhohalf hdlt0 hdltc hmargin

/-- Away from the diagonal the chord is bounded below: on the compact set of
pairs of parameters in `[0,1]` at cyclic distance at least `eps`, the
continuous function `‖g u − g v‖` is positive, hence has a positive minimum. -/
theorem exists_min_far {g : ℝ → ℂ} (hgc : Continuous g) (hper : Periodic g 1)
    (hinj : InjOn g (Ico 0 1)) {eps : ℝ} (heps : 0 < eps) (heps2 : eps ≤ 1 / 2) :
    ∃ m : ℝ, 0 < m ∧ ∀ u ∈ Icc (0 : ℝ) 1, ∀ v ∈ Icc (0 : ℝ) 1,
      eps ≤ MarkedSpace.cyc u v → m ≤ ‖g u - g v‖ := by
  -- injectivity in the closed interval, in the cyclic form
  have hinj' : ∀ u ∈ Icc (0 : ℝ) 1, ∀ v ∈ Icc (0 : ℝ) 1, g u = g v →
      MarkedSpace.cyc u v = 0 := by
    have hred : ∀ u ∈ Icc (0 : ℝ) 1, ∃ u' ∈ Ico (0 : ℝ) 1, g u' = g u ∧
        ∀ w ∈ Icc (0 : ℝ) 1, MarkedSpace.cyc u' w = MarkedSpace.cyc u w := by
      intro u hu
      rcases eq_or_lt_of_le hu.2 with h | h
      · subst h
        refine ⟨0, ⟨le_refl _, one_pos⟩, ?_, ?_⟩
        · simpa using (hper 0).symm
        · intro w hw
          have h1 : |(0 : ℝ) - w| = w := by
            rw [zero_sub, abs_neg, abs_of_nonneg hw.1]
          have h2 : |(1 : ℝ) - w| = 1 - w := abs_of_nonneg (by linarith [hw.2])
          simp only [MarkedSpace.cyc, h1, h2]
          rw [min_comm]
          congr 1
          ring
      · exact ⟨u, ⟨hu.1, h⟩, rfl, fun _ _ => rfl⟩
    intro u hu v hv huv
    obtain ⟨u', hu', hgu', hcu'⟩ := hred u hu
    obtain ⟨v', hv', hgv', hcv'⟩ := hred v hv
    have huv' : u' = v' := hinj hu' hv' (by rw [hgu', hgv', huv])
    calc MarkedSpace.cyc u v = MarkedSpace.cyc u' v := (hcu' v hv).symm
      _ = MarkedSpace.cyc v u' := cyc_comm _ _
      _ = MarkedSpace.cyc v' u' := (hcv' u' (Ico_subset_Icc_self hu')).symm
      _ = 0 := by rw [huv']; simp [MarkedSpace.cyc]
  set S : Set (ℝ × ℝ) := {q | q.1 ∈ Icc (0:ℝ) 1 ∧ q.2 ∈ Icc (0:ℝ) 1 ∧
    eps ≤ MarkedSpace.cyc q.1 q.2} with hS
  have hcyccont : Continuous fun q : ℝ × ℝ => MarkedSpace.cyc q.1 q.2 := by
    unfold MarkedSpace.cyc
    fun_prop
  have hScompact : IsCompact S := by
    have hclosed : IsClosed S := by
      have h1 : IsClosed {q : ℝ × ℝ | q.1 ∈ Icc (0:ℝ) 1} :=
        (isClosed_Icc).preimage continuous_fst
      have h2 : IsClosed {q : ℝ × ℝ | q.2 ∈ Icc (0:ℝ) 1} :=
        (isClosed_Icc).preimage continuous_snd
      have h3 : IsClosed {q : ℝ × ℝ | eps ≤ MarkedSpace.cyc q.1 q.2} :=
        isClosed_le continuous_const hcyccont
      exact (h1.inter (h2.inter h3))
    have hsub : S ⊆ (Icc (0:ℝ) 1) ×ˢ (Icc (0:ℝ) 1) := by
      rintro ⟨u, v⟩ ⟨h1, h2, -⟩
      exact ⟨h1, h2⟩
    exact IsCompact.of_isClosed_subset ((isCompact_Icc).prod isCompact_Icc) hclosed hsub
  have hne : S.Nonempty := by
    refine ⟨(0, 1/2), ⟨⟨le_refl _, zero_le_one⟩, ⟨by norm_num, by norm_num⟩, ?_⟩⟩
    have : MarkedSpace.cyc 0 (1/2) = 1/2 := by
      simp [MarkedSpace.cyc]
      norm_num
    rw [this]; exact heps2
  have hcont : ContinuousOn (fun q : ℝ × ℝ => ‖g q.1 - g q.2‖) S :=
    (((hgc.comp continuous_fst).sub (hgc.comp continuous_snd)).norm).continuousOn
  obtain ⟨q0, hq0S, hq0min⟩ := hScompact.exists_isMinOn hne hcont
  refine ⟨‖g q0.1 - g q0.2‖, ?_, ?_⟩
  · rcases hq0S with ⟨h1, h2, h3⟩
    have hne' : g q0.1 ≠ g q0.2 := by
      intro hEq
      have := hinj' q0.1 h1 q0.2 h2 hEq
      linarith
    simpa [sub_eq_zero] using hne'
  · intro u hu v hv hcyc
    exact hq0min (show (u, v) ∈ S from ⟨hu, hv, hcyc⟩)

/-- **The chord-arc bound of an embedded closed curve.**  A closed `C¹` curve of
period one, with continuous velocity of norm at least `c > 0`, injective on one
period, satisfies the quantitative chord-arc bound of the tube of marked curves
for some constant `delta > 0`. -/
theorem exists_chord_arc {g V : ℝ → ℂ} {c : ℝ} (hc : 0 < c)
    (hg : ∀ u, HasDerivAt g (V u) u) (hVc : Continuous V) (hVper : Periodic V 1)
    (hper : Periodic g 1) (hspeed : ∀ u, c ≤ ‖V u‖) (hinj : InjOn g (Ico 0 1)) :
    ∃ d : ℝ, 0 < d ∧ ∀ u ∈ Icc (0 : ℝ) 1, ∀ v ∈ Icc (0 : ℝ) 1,
      d * MarkedSpace.cyc u v ≤ ‖g u - g v‖ := by
  obtain ⟨d0, hd0pos, hd0le, hd0⟩ := exists_unif_bound hVc hVper (e := c / 2) (by linarith)
  set eps : ℝ := min d0 (1 / 2) with heps
  have hepspos : 0 < eps := lt_min hd0pos (by norm_num)
  have hgc : Continuous g := Differentiable.continuous fun u => (hg u).differentiableAt
  obtain ⟨m, hmpos, hm⟩ := exists_min_far hgc hper hinj hepspos (min_le_right _ _)
  refine ⟨min (c / 2) m, lt_min (by linarith) hmpos, ?_⟩
  intro u hu v hv
  rcases le_or_gt eps (MarkedSpace.cyc u v) with hfar | hnear
  · -- far from the diagonal: use the minimum
    have hcycle : MarkedSpace.cyc u v ≤ 1 := cyc_le_one u v
    have h1 : min (c / 2) m ≤ m := min_le_right _ _
    have h2 : 0 ≤ MarkedSpace.cyc u v := le_trans hepspos.le hfar
    have h3 : m ≤ ‖g u - g v‖ := hm u hu v hv hfar
    nlinarith
  · -- near the diagonal: two cases according to which term realizes `cyc`
    have hkey : c / 2 * MarkedSpace.cyc u v ≤ ‖g u - g v‖ := by
      rcases le_or_gt |u - v| (1 - |u - v|) with hcase | hcase
      · have hcyc : MarkedSpace.cyc u v = |u - v| := min_eq_left hcase
        have hle : |u - v| ≤ d0 := by
          rw [hcyc] at hnear
          exact le_trans hnear.le (min_le_left _ _)
        rw [hcyc]
        exact norm_sub_ge_of_close hg hVc hspeed hd0 u v hle
      · have hcyc : MarkedSpace.cyc u v = 1 - |u - v| := min_eq_right hcase.le
        -- one of the parameters is near `0`, the other near `1`: shift by one period
        rcases le_total u v with huv | huv
        · have habs : |u - v| = v - u := by rw [abs_sub_comm]; exact abs_of_nonneg (by linarith)
          have hshift : |u + 1 - v| = 1 - |u - v| := by
            rw [habs]
            rw [abs_of_nonneg (by linarith [hu.1, hv.2] : (0:ℝ) ≤ u + 1 - v)]
            ring
          have hle : |u + 1 - v| ≤ d0 := by
            rw [hshift, ← hcyc]
            exact le_trans hnear.le (min_le_left _ _)
          have h := norm_sub_ge_of_close hg hVc hspeed hd0 (u + 1) v hle
          rw [hshift] at h
          rw [hcyc, ← hper u]
          exact h
        · have habs : |u - v| = u - v := abs_of_nonneg (by linarith)
          have hshift : |u - (v + 1)| = 1 - |u - v| := by
            rw [habs]
            rw [abs_of_nonpos (by linarith [hu.2, hv.1] : u - (v + 1) ≤ 0)]
            ring
          have hle : |u - (v + 1)| ≤ d0 := by
            rw [hshift, ← hcyc]
            exact le_trans hnear.le (min_le_left _ _)
          have h := norm_sub_ge_of_close hg hVc hspeed hd0 u (v + 1) hle
          rw [hshift] at h
          rw [hcyc, ← hper v]
          exact h
    have hmin : min (c / 2) m * MarkedSpace.cyc u v ≤ c / 2 * MarkedSpace.cyc u v := by
      have hnonneg : 0 ≤ MarkedSpace.cyc u v := cyc_nonneg hu hv
      exact mul_le_mul_of_nonneg_right (min_le_left _ _) hnonneg
    linarith

end ChordArc
