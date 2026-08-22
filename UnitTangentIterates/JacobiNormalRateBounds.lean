import Mathlib

/-!
# The sup bounds on the normal rate of a family of rears, from the Jacobi ODE

`GaugeMarkedDataOfNormalRate.gaugeMarkedData_of_normal_rate` asks for bounds

```
  |η| ≤ S₀ ,   |∂_sη| ≤ S₁ ,   |∂_s²η| ≤ S₂
```

on the normal rate of the moving family and on its first two arclength
derivatives.  For a family of *rears* the normal rate is not free: it solves the
inverse Jacobi ODE

```
  ∂_sη = g − η ,        g = sec δ · η_F ∘ s_f ,
```

whose inhomogeneity `g` is the normal velocity of the front, read in the rear
arclength.  The maximum principle already bounds `η` itself by the sup norm of
`g` (`SelectedRear.periodic_linear_sup_bound`, used throughout the rear-track
files); the two remaining bounds are then immediate from the ODE, differentiated
once:

```
  |∂_sη| ≤ |g| + |η| ≤ 2 S₀ ,     |∂_s²η| ≤ |∂_sg| + |∂_sη| ≤ D + 2 S₀ .
```

This file records that step, in the form the construction of the gauge-marked
data consumes: `jacobi_normal_rate_bounds` produces the three bounds, and
`jacobi_cost_constants` turns them into the three comparisons with a cost
density together with the numerical constants `c₀, c₁, c₂` the two conditions
of the construction are stated with.

Main results: `jacobi_normal_rate_bounds`, `jacobi_cost_constants`.
-/

noncomputable section

namespace JacobiNormalRateBounds

variable {en enS enSS g gS : ℝ → ℝ → ℝ} {S0 D m : ℝ → ℝ}

/-- The first arclength derivative of the normal rate is `g − η`: the inverse
Jacobi ODE, read through the uniqueness of the derivative. -/
theorem enS_eq (hjacobi : ∀ t x, HasDerivAt (en t) (g t x - en t x) x)
    (henS : ∀ t x, HasDerivAt (en t) (enS t x) x) (t x : ℝ) :
    enS t x = g t x - en t x := (henS t x).unique (hjacobi t x)

/-- The second arclength derivative of the normal rate is `∂_sg − ∂_sη`. -/
theorem enSS_eq (hgS : ∀ t x, HasDerivAt (g t) (gS t x) x)
    (hjacobi : ∀ t x, HasDerivAt (en t) (g t x - en t x) x)
    (henS : ∀ t x, HasDerivAt (en t) (enS t x) x)
    (henSS : ∀ t x, HasDerivAt (enS t) (enSS t x) x) (t x : ℝ) :
    enSS t x = gS t x - enS t x := by
  have hEq : enS t = fun y => g t y - en t y := funext fun y => enS_eq hjacobi henS t y
  have hd : HasDerivAt (enS t) (gS t x - (g t x - en t x)) x := by
    rw [hEq]
    exact (hgS t x).sub (hjacobi t x)
  have h := (henSS t x).unique hd
  rw [h, enS_eq hjacobi henS t x]

/-- **The three sup bounds on the normal rate of a family of rears.**  From the
inverse Jacobi ODE, from the bound `S₀` shared by the normal rate and by the
inhomogeneity — the latter being what the maximum principle provides — and from
a bound `D` on the arclength derivative of the inhomogeneity. -/
theorem jacobi_normal_rate_bounds
    (hgS : ∀ t x, HasDerivAt (g t) (gS t x) x)
    (hjacobi : ∀ t x, HasDerivAt (en t) (g t x - en t x) x)
    (henS : ∀ t x, HasDerivAt (en t) (enS t x) x)
    (henSS : ∀ t x, HasDerivAt (enS t) (enSS t x) x)
    (hgbd : ∀ t x, |g t x| ≤ S0 t) (henbd : ∀ t x, |en t x| ≤ S0 t)
    (hgSbd : ∀ t x, |gS t x| ≤ D t) :
    (∀ t x, |en t x| ≤ S0 t) ∧ (∀ t x, |enS t x| ≤ 2 * S0 t) ∧
      (∀ t x, |enSS t x| ≤ D t + 2 * S0 t) := by
  have h1 : ∀ t x, |enS t x| ≤ 2 * S0 t := by
    intro t x
    rw [enS_eq hjacobi henS t x]
    calc |g t x - en t x| ≤ |g t x| + |en t x| := abs_sub _ _
      _ ≤ S0 t + S0 t := add_le_add (hgbd t x) (henbd t x)
      _ = 2 * S0 t := by ring
  refine ⟨henbd, h1, ?_⟩
  intro t x
  rw [enSS_eq hgS hjacobi henS henSS t x]
  calc |gS t x - enS t x| ≤ |gS t x| + |enS t x| := abs_sub _ _
    _ ≤ D t + 2 * S0 t := add_le_add (hgSbd t x) (h1 t x)

/-- **The three comparisons with the cost density.**  If the sup norm of the
inhomogeneity of the Jacobi ODE and of its arclength derivative are dominated by
the multiples `c·m` and `d·m` of the cost density, the three bounds of
`jacobi_normal_rate_bounds` are dominated by `c·m`, `2c·m` and `(d + 2c)·m` —
the constants `c₀, c₁, c₂` with which the numerical conditions of the
construction of the gauge-marked data are then read. -/
theorem jacobi_cost_constants {c d : ℝ}
    (hS0m : ∀ t, S0 t ≤ c * m t) (hDm : ∀ t, D t ≤ d * m t) :
    (∀ t, S0 t ≤ c * m t) ∧ (∀ t, 2 * S0 t ≤ 2 * c * m t) ∧
      (∀ t, D t + 2 * S0 t ≤ (d + 2 * c) * m t) := by
  refine ⟨hS0m, fun t => by have := hS0m t; linarith, fun t => ?_⟩
  calc D t + 2 * S0 t ≤ d * m t + 2 * (c * m t) := by
        have h0 := hS0m t
        have hd := hDm t
        linarith
    _ = (d + 2 * c) * m t := by ring

end JacobiNormalRateBounds
