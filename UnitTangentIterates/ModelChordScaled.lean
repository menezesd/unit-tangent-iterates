import UnitTangentIterates.ModelChordFloorFree

/-!
# The tube's chord field for the model, floor-free

`main_theorem_of_model_floor_free` takes its chord hypothesis in the scaled form

```
  dlt·(2H₀)/(2Hₙ)·cyc(x,y) ≤ ‖front n x − front n y‖ ,
```

and §56 supplies `min(cyc/2, π/(12·kap)) ≤ ‖·‖` for the model.  This file makes
the placement.

`chord_arc_front_scaled` : with

```
  dlt = min(1/2, π/(12·kap·H₀))
```

the scaled bound holds for every `n` and every pair in `[0, 2Hₙ]`.  Both
branches are elementary once the shapes are right:

* `dlt·(2H₀)/(2Hₙ) ≤ 1/2` because `dlt ≤ 1/2` and `H₀ ≤ Hₙ`;
* `dlt·(2H₀)/(2Hₙ)·cyc ≤ dlt·H₀ ≤ π/(12·kap)` because `cyc ≤ Hₙ` and
  `dlt ≤ π/(12·kap·H₀)`.

So the chord input of the floor-free closing chain is now *constructed* for the
two-cap model rather than derived from a curvature floor — which §47 proved
impossible.
-/

noncomputable section

set_option maxHeartbeats 4000000

open Set Real Function

namespace TwoCapPairsAssembly

/-- **The tube's chord field for the model, floor-free.**  With
`dlt = min(1/2, π/(12·kap·H₀))` the scaled bound
`dlt·(2H₀)/(2Hₙ)·cyc(x,y) ≤ ‖·‖` holds, uniformly in `n`. -/
theorem chord_arc_front_scaled {kappas : ℕ → ℝ → ℝ} {theta0 : ℕ → ℝ}
    {Hs : ℕ → ℝ} {kap : ℝ}
    (hH : ∀ n, 0 < Hs n) (hmono : ∀ n, Hs 0 ≤ Hs n)
    (hk : ∀ n, Continuous (kappas n)) (hper : ∀ n, Periodic (kappas n) (Hs n))
    (htotal : ∀ n, (∫ r in (0:ℝ)..(Hs n), kappas n r) = π)
    (hk0 : ∀ n s, 0 ≤ kappas n s) (hkap : ∀ n s, kappas n s ≤ kap)
    (hkap0 : 0 < kap) :
    ∀ n, ∀ x ∈ Icc (0:ℝ) (2 * Hs n), ∀ y ∈ Icc (0:ℝ) (2 * Hs n),
      min (1/2) (π / (12 * kap * Hs 0)) * (2 * Hs 0) / (2 * Hs n)
          * min |x - y| (2 * Hs n - |x - y|)
        ≤ ‖front (kappas n) (theta0 n) (Hs n) x
            - front (kappas n) (theta0 n) (Hs n) y‖ := by
  intro n x hx y hy
  set H := Hs n with hHdef
  set dlt := min (1/2 : ℝ) (π / (12 * kap * Hs 0)) with hdltdef
  have hH0 : 0 < Hs 0 := hH 0
  have hHn : 0 < H := hH n
  have hHle : Hs 0 ≤ H := hmono n
  have hdlt0 : 0 < dlt := by
    apply lt_min (by norm_num)
    positivity
  have hdlt1 : dlt ≤ 1 / 2 := min_le_left _ _
  have hdlt2 : dlt ≤ π / (12 * kap * Hs 0) := min_le_right _ _
  -- the core comparison, for an ordered pair
  have key : ∀ u v : ℝ, u ≤ v → v - u ≤ 2 * H →
      dlt * (2 * Hs 0) / (2 * H) * min (v - u) (2 * H - (v - u))
        ≤ ‖front (kappas n) (theta0 n) H v - front (kappas n) (theta0 n) H u‖ := by
    intro u v huv hlt
    have hbound := chord_front_cyclic (theta0 := theta0 n) hHn (hk n) (hper n)
      (htotal n) (hk0 n) (hkap n) hkap0 huv hlt
    refine le_trans ?_ hbound
    set c := min (v - u) (2 * H - (v - u)) with hcdef
    have hc0 : 0 ≤ c := le_min (by linarith) (by linarith)
    have hcH : c ≤ H := by
      rcases le_or_gt (v - u) H with h | h
      · exact le_trans (min_le_left _ _) h
      · exact le_trans (min_le_right _ _) (by linarith)
    refine le_min ?_ ?_
    · have h1 : dlt * (2 * Hs 0) / (2 * H) ≤ 1 / 2 := by
        rw [div_le_iff₀ (by positivity)]
        nlinarith [hdlt1, hHle, hdlt0.le, hH0]
      have := mul_le_mul_of_nonneg_right h1 hc0
      linarith [this]
    · have hEq : dlt * (2 * Hs 0) / (2 * H) * c = (dlt * Hs 0) * (c / H) := by
        field_simp
      have hcH1 : c / H ≤ 1 := by rw [div_le_one hHn]; exact hcH
      have hdH0 : (0:ℝ) ≤ dlt * Hs 0 := mul_nonneg hdlt0.le hH0.le
      have h2 : dlt * (2 * Hs 0) / (2 * H) * c ≤ dlt * Hs 0 := by
        rw [hEq]
        nlinarith [hcH1, hdH0, div_nonneg hc0 hHn.le]
      have h3 : dlt * Hs 0 ≤ π / (12 * kap) := by
        have hm := mul_le_mul_of_nonneg_right hdlt2 hH0.le
        calc dlt * Hs 0 ≤ π / (12 * kap * Hs 0) * Hs 0 := hm
          _ = π / (12 * kap) := by field_simp
      linarith
  rcases le_total x y with hxy | hxy
  · have habs : |x - y| = y - x := by rw [abs_sub_comm, abs_of_nonneg (by linarith)]
    rw [habs, norm_sub_rev]
    exact key x y hxy (by simp only [hHdef] at hx hy ⊢; linarith [hx.1, hy.2])
  · have habs : |x - y| = x - y := abs_of_nonneg (by linarith)
    rw [habs]
    exact key y x hxy (by simp only [hHdef] at hx hy ⊢; linarith [hy.1, hx.2])

end TwoCapPairsAssembly
