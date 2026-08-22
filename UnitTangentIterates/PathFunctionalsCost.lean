import Mathlib
import UnitTangentIterates.PathFunctionalsReparam

/-!
# The path functionals of a whole path under a family of reparametrizations

`PathFunctionalsReparam.lean` compares the *densities* of the functionals
`W, S₀, S₁, S₂` at one time of a path.  This file integrates those comparisons
in the time, so that the functionals themselves — as defined in
`MarkedTopology.lean` — are compared for a family `φ_t` of reparametrizations
with uniform bounds `|φ_t'| ≤ M`, `|φ_t''| ≤ N`, `φ_t' ≥ m > 0`:

```
  S₀(η ∘ φ) ≤ S₀(η),
  S₁(η ∘ φ) ≤ M S₁(η),
  S₂(η ∘ φ) ≤ M² S₂(η) + N S₁(η),
  W(η ∘ φ)  ≤ m⁻¹ ∫₀¹ ∫_{φ_t(0)}^{φ_t(L)} |η_t|.
```

The integrability of the densities in the time is carried as a hypothesis:
nothing in the definition of the functionals guarantees it.

Main results: `S_zero_comp_le`, `S_one_comp_le`, `S_two_comp_le`,
`W_comp_le`.
-/

noncomputable section

open Set MeasureTheory MarkedTopology PathFunctionalsReparam

namespace PathFunctionalsCost

variable {eta eta1 eta2 phi phi1 phi2 : ℝ → ℝ → ℝ}

/-- `S₁` computed from a pointwise derivative. -/
theorem S_one_eq (heta1 : ∀ t x, HasDerivAt (eta t) (eta1 t x) x) :
    S 1 eta = ∫ t in (0:ℝ)..1, supNorm (eta1 t) := by
  refine intervalIntegral.integral_congr (fun t _ => ?_)
  rw [iteratedDeriv_one]
  congr 1
  funext x
  exact (heta1 t x).deriv

/-- `S₂` computed from pointwise derivatives. -/
theorem S_two_eq (heta1 : ∀ t x, HasDerivAt (eta t) (eta1 t x) x)
    (heta2 : ∀ t x, HasDerivAt (eta1 t) (eta2 t x) x) :
    S 2 eta = ∫ t in (0:ℝ)..1, supNorm (eta2 t) := by
  refine intervalIntegral.integral_congr (fun t _ => ?_)
  rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
  congr 1
  have h1 : deriv (eta t) = eta1 t := by
    funext x; exact (heta1 t x).deriv
  rw [h1]
  funext x
  exact (heta2 t x).deriv

/-- **`S₀` does not grow under a family of reparametrizations.** -/
theorem S_zero_comp_le (hbdd : ∀ t ∈ Icc (0:ℝ) 1, BddAbove (Set.range fun x => |eta t x|))
    (hint1 : IntervalIntegrable (fun t => supNorm fun u => eta t (phi t u)) volume 0 1)
    (hint2 : IntervalIntegrable (fun t => supNorm (eta t)) volume 0 1) :
    S 0 (fun t u => eta t (phi t u)) ≤ S 0 eta := by
  rw [S_zero, S_zero]
  exact intervalIntegral.integral_mono_on (by norm_num) hint1 hint2
    (fun t ht => supNorm_comp_le (hbdd t ht) _)

/-- **`S₁` grows at most by the uniform bound for `φ_t'`.** -/
theorem S_one_comp_le {M : ℝ} (heta1 : ∀ t x, HasDerivAt (eta t) (eta1 t x) x)
    (hphi1 : ∀ t u, HasDerivAt (phi t) (phi1 t u) u)
    (hbdd1 : ∀ t ∈ Icc (0:ℝ) 1, BddAbove (Set.range fun x => |eta1 t x|))
    (hM : ∀ t ∈ Icc (0:ℝ) 1, ∀ u, |phi1 t u| ≤ M)
    (hint1 : IntervalIntegrable
      (fun t => supNorm (iteratedDeriv 1 fun u => eta t (phi t u))) volume 0 1)
    (hint2 : IntervalIntegrable (fun t => supNorm (eta1 t)) volume 0 1) :
    S 1 (fun t u => eta t (phi t u)) ≤ M * S 1 eta := by
  have hstep : (∫ t in (0:ℝ)..1, supNorm (iteratedDeriv 1 fun u => eta t (phi t u)))
      ≤ ∫ t in (0:ℝ)..1, supNorm (eta1 t) * M := by
    refine intervalIntegral.integral_mono_on (by norm_num) hint1
      (hint2.mul_const M) (fun t ht => ?_)
    exact supNorm_iteratedDeriv_one_comp_le (heta1 t) (hphi1 t) (hbdd1 t ht) (hM t ht)
  calc S 1 (fun t u => eta t (phi t u))
      = ∫ t in (0:ℝ)..1, supNorm (iteratedDeriv 1 fun u => eta t (phi t u)) := rfl
    _ ≤ ∫ t in (0:ℝ)..1, supNorm (eta1 t) * M := hstep
    _ = M * S 1 eta := by
        rw [S_one_eq heta1, intervalIntegral.integral_mul_const, mul_comm]

/-- **`S₂` grows at most by the uniform bounds for `φ_t'` and `φ_t''`.** -/
theorem S_two_comp_le {M N : ℝ} (heta1 : ∀ t x, HasDerivAt (eta t) (eta1 t x) x)
    (heta2 : ∀ t x, HasDerivAt (eta1 t) (eta2 t x) x)
    (hphi1 : ∀ t u, HasDerivAt (phi t) (phi1 t u) u)
    (hphi2 : ∀ t u, HasDerivAt (phi1 t) (phi2 t u) u)
    (hbdd1 : ∀ t ∈ Icc (0:ℝ) 1, BddAbove (Set.range fun x => |eta1 t x|))
    (hbdd2 : ∀ t ∈ Icc (0:ℝ) 1, BddAbove (Set.range fun x => |eta2 t x|))
    (hM : ∀ t ∈ Icc (0:ℝ) 1, ∀ u, |phi1 t u| ≤ M)
    (hN : ∀ t ∈ Icc (0:ℝ) 1, ∀ u, |phi2 t u| ≤ N)
    (hint1 : IntervalIntegrable
      (fun t => supNorm (iteratedDeriv 2 fun u => eta t (phi t u))) volume 0 1)
    (hint2 : IntervalIntegrable (fun t => supNorm (eta1 t)) volume 0 1)
    (hint3 : IntervalIntegrable (fun t => supNorm (eta2 t)) volume 0 1) :
    S 2 (fun t u => eta t (phi t u)) ≤ M ^ 2 * S 2 eta + N * S 1 eta := by
  have hstep : (∫ t in (0:ℝ)..1, supNorm (iteratedDeriv 2 fun u => eta t (phi t u)))
      ≤ ∫ t in (0:ℝ)..1, (supNorm (eta2 t) * M ^ 2 + supNorm (eta1 t) * N) := by
    refine intervalIntegral.integral_mono_on (by norm_num) hint1
      ((hint3.mul_const (M ^ 2)).add (hint2.mul_const N)) (fun t ht => ?_)
    exact supNorm_iteratedDeriv_two_comp_le (heta1 t) (heta2 t) (hphi1 t) (hphi2 t)
      (hbdd1 t ht) (hbdd2 t ht) (hM t ht) (hN t ht)
  calc S 2 (fun t u => eta t (phi t u))
      = ∫ t in (0:ℝ)..1, supNorm (iteratedDeriv 2 fun u => eta t (phi t u)) := rfl
    _ ≤ ∫ t in (0:ℝ)..1, (supNorm (eta2 t) * M ^ 2 + supNorm (eta1 t) * N) := hstep
    _ = M ^ 2 * S 2 eta + N * S 1 eta := by
        rw [intervalIntegral.integral_add ((hint3.mul_const (M ^ 2)))
          (hint2.mul_const N), intervalIntegral.integral_mul_const,
          intervalIntegral.integral_mul_const, S_two_eq heta1 heta2, S_one_eq heta1]
        ring

/-- **The `L¹` functional under a family of reparametrizations.** -/
theorem W_comp_le {m L : ℝ} (hm : 0 < m) (hL : 0 ≤ L)
    (hetac : ∀ t ∈ Icc (0:ℝ) 1, Continuous (eta t))
    (hphi1 : ∀ t u, HasDerivAt (phi t) (phi1 t u) u)
    (hphi1c : ∀ t, Continuous (phi1 t))
    (hlow : ∀ t ∈ Icc (0:ℝ) 1, ∀ u, m ≤ phi1 t u)
    (hint1 : IntervalIntegrable
      (fun t => ∫ u in (0:ℝ)..L, |eta t (phi t u)|) volume 0 1)
    (hint2 : IntervalIntegrable
      (fun t => ∫ x in (phi t 0)..(phi t L), |eta t x|) volume 0 1) :
    W (fun t u => eta t (phi t u)) L
      ≤ (1 / m) * ∫ t in (0:ℝ)..1, ∫ x in (phi t 0)..(phi t L), |eta t x| := by
  have hstep : (∫ t in (0:ℝ)..1, ∫ u in (0:ℝ)..L, |eta t (phi t u)|)
      ≤ ∫ t in (0:ℝ)..1, (1 / m) * ∫ x in (phi t 0)..(phi t L), |eta t x| := by
    refine intervalIntegral.integral_mono_on (by norm_num) hint1
      (hint2.const_mul (1 / m)) (fun t ht => ?_)
    exact integral_abs_comp_le hm hL (hetac t ht) (hphi1 t) (hphi1c t) (hlow t ht)
  calc W (fun t u => eta t (phi t u)) L
      = ∫ t in (0:ℝ)..1, ∫ u in (0:ℝ)..L, |eta t (phi t u)| := rfl
    _ ≤ ∫ t in (0:ℝ)..1, (1 / m) * ∫ x in (phi t 0)..(phi t L), |eta t x| := hstep
    _ = (1 / m) * ∫ t in (0:ℝ)..1, ∫ x in (phi t 0)..(phi t L), |eta t x| := by
        rw [intervalIntegral.integral_const_mul]

end PathFunctionalsCost
