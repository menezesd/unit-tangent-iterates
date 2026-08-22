import Mathlib
import UnitTangentIterates.MarkedTopology

/-!
# The path functionals under a reparametrization

The functionals `W`, `S₀`, `S₁`, `S₂` of `MarkedTopology.lean` are computed for
a normal velocity read in one particular parameter.  When a moving family of
curves is put in **normal gauge** the parameter is transported by a flow
(`NormalGaugeFamily.lean`), so the normal velocity is read in a *reparametrized*
variable, and the functionals have to be compared with those computed in the
original one.  This file contains that comparison, for a single slice.

For a reparametrization `φ` with `|φ'| ≤ M`, `|φ''| ≤ N` and `φ' ≥ m > 0`:

```
  ‖η ∘ φ‖_∞      ≤ ‖η‖_∞,
  ‖(η ∘ φ)'‖_∞   ≤ M ‖η'‖_∞,
  ‖(η ∘ φ)''‖_∞  ≤ M² ‖η''‖_∞ + N ‖η'‖_∞,
  ∫_a^b |η ∘ φ|  ≤ m⁻¹ ∫_{φ a}^{φ b} |η|.
```

Main results:

* `supNorm_comp_le`, `supNorm_deriv_comp_le`, `supNorm_deriv2_comp_le` — the
  three sup-norm comparisons;
* `integral_abs_comp_le` — the `L¹` comparison, by the change of variables
  `x = φ(u)`.
-/

noncomputable section

open Set MeasureTheory MarkedTopology

namespace PathFunctionalsReparam

variable {eta eta1 eta2 phi phi1 phi2 : ℝ → ℝ}

/-! ### The chain rule for the two derivatives -/

/-- The first derivative of `η ∘ φ`. -/
theorem deriv_comp_eq (heta1 : ∀ x, HasDerivAt eta (eta1 x) x)
    (hphi1 : ∀ u, HasDerivAt phi (phi1 u) u) :
    deriv (fun u => eta (phi u)) = fun u => eta1 (phi u) * phi1 u := by
  funext u
  exact ((heta1 (phi u)).comp u (hphi1 u)).deriv

/-- The second derivative of `η ∘ φ`. -/
theorem deriv2_comp_eq (heta1 : ∀ x, HasDerivAt eta (eta1 x) x)
    (heta2 : ∀ x, HasDerivAt eta1 (eta2 x) x)
    (hphi1 : ∀ u, HasDerivAt phi (phi1 u) u)
    (hphi2 : ∀ u, HasDerivAt phi1 (phi2 u) u) :
    deriv (deriv (fun u => eta (phi u)))
      = fun u => eta2 (phi u) * phi1 u ^ 2 + eta1 (phi u) * phi2 u := by
  rw [deriv_comp_eq heta1 hphi1]
  funext u
  have hc : HasDerivAt (fun u' => eta1 (phi u')) (eta2 (phi u) * phi1 u) u :=
    (heta2 (phi u)).comp u (hphi1 u)
  have h : HasDerivAt (fun u' => eta1 (phi u') * phi1 u')
      (eta2 (phi u) * phi1 u ^ 2 + eta1 (phi u) * phi2 u) u := by
    refine (hc.mul (hphi2 u)).congr_deriv ?_
    ring
  exact h.deriv

/-! ### The sup-norm comparisons -/

/-- The sup norm does not grow under a reparametrization. -/
theorem supNorm_comp_le (hbdd : BddAbove (Set.range fun x => |eta x|)) (phi : ℝ → ℝ) :
    supNorm (fun u => eta (phi u)) ≤ supNorm eta :=
  Real.iSup_le (fun u => le_supNorm hbdd (phi u)) (supNorm_nonneg eta)

/-- The sup norm of the first derivative grows at most by the sup of `|φ'|`. -/
theorem supNorm_deriv_comp_le {M : ℝ}
    (heta1 : ∀ x, HasDerivAt eta (eta1 x) x)
    (hphi1 : ∀ u, HasDerivAt phi (phi1 u) u)
    (hbdd1 : BddAbove (Set.range fun x => |eta1 x|)) (hM : ∀ u, |phi1 u| ≤ M) :
    supNorm (deriv fun u => eta (phi u)) ≤ supNorm eta1 * M := by
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hM 0)
  rw [deriv_comp_eq heta1 hphi1]
  refine Real.iSup_le (fun u => ?_) (mul_nonneg (supNorm_nonneg _) hM0)
  rw [abs_mul]
  exact mul_le_mul (le_supNorm hbdd1 (phi u)) (hM u) (abs_nonneg _) (supNorm_nonneg _)

/-- The sup norm of the second derivative, by the chain rule. -/
theorem supNorm_deriv2_comp_le {M N : ℝ}
    (heta1 : ∀ x, HasDerivAt eta (eta1 x) x)
    (heta2 : ∀ x, HasDerivAt eta1 (eta2 x) x)
    (hphi1 : ∀ u, HasDerivAt phi (phi1 u) u)
    (hphi2 : ∀ u, HasDerivAt phi1 (phi2 u) u)
    (hbdd1 : BddAbove (Set.range fun x => |eta1 x|))
    (hbdd2 : BddAbove (Set.range fun x => |eta2 x|))
    (hM : ∀ u, |phi1 u| ≤ M) (hN : ∀ u, |phi2 u| ≤ N) :
    supNorm (deriv (deriv fun u => eta (phi u)))
      ≤ supNorm eta2 * M ^ 2 + supNorm eta1 * N := by
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hM 0)
  have hN0 : 0 ≤ N := le_trans (abs_nonneg _) (hN 0)
  rw [deriv2_comp_eq heta1 heta2 hphi1 hphi2]
  refine Real.iSup_le (fun u => ?_)
    (add_nonneg (mul_nonneg (supNorm_nonneg _) (by positivity))
      (mul_nonneg (supNorm_nonneg _) hN0))
  have h1 : |eta2 (phi u) * phi1 u ^ 2| ≤ supNorm eta2 * M ^ 2 := by
    rw [abs_mul, abs_pow]
    refine mul_le_mul (le_supNorm hbdd2 (phi u)) ?_ (by positivity) (supNorm_nonneg _)
    nlinarith [abs_nonneg (phi1 u), hM u]
  have h2 : |eta1 (phi u) * phi2 u| ≤ supNorm eta1 * N := by
    rw [abs_mul]
    exact mul_le_mul (le_supNorm hbdd1 (phi u)) (hN u) (abs_nonneg _) (supNorm_nonneg _)
  calc |eta2 (phi u) * phi1 u ^ 2 + eta1 (phi u) * phi2 u|
      ≤ |eta2 (phi u) * phi1 u ^ 2| + |eta1 (phi u) * phi2 u| := abs_add_le _ _
    _ ≤ supNorm eta2 * M ^ 2 + supNorm eta1 * N := by linarith

/-- The comparison of `S₁`'s density, in the form used by `MarkedTopology.S`. -/
theorem supNorm_iteratedDeriv_one_comp_le {M : ℝ}
    (heta1 : ∀ x, HasDerivAt eta (eta1 x) x)
    (hphi1 : ∀ u, HasDerivAt phi (phi1 u) u)
    (hbdd1 : BddAbove (Set.range fun x => |eta1 x|)) (hM : ∀ u, |phi1 u| ≤ M) :
    supNorm (iteratedDeriv 1 fun u => eta (phi u)) ≤ supNorm eta1 * M := by
  rw [iteratedDeriv_one]
  exact supNorm_deriv_comp_le heta1 hphi1 hbdd1 hM

/-- The comparison of `S₂`'s density, in the form used by `MarkedTopology.S`. -/
theorem supNorm_iteratedDeriv_two_comp_le {M N : ℝ}
    (heta1 : ∀ x, HasDerivAt eta (eta1 x) x)
    (heta2 : ∀ x, HasDerivAt eta1 (eta2 x) x)
    (hphi1 : ∀ u, HasDerivAt phi (phi1 u) u)
    (hphi2 : ∀ u, HasDerivAt phi1 (phi2 u) u)
    (hbdd1 : BddAbove (Set.range fun x => |eta1 x|))
    (hbdd2 : BddAbove (Set.range fun x => |eta2 x|))
    (hM : ∀ u, |phi1 u| ≤ M) (hN : ∀ u, |phi2 u| ≤ N) :
    supNorm (iteratedDeriv 2 fun u => eta (phi u))
      ≤ supNorm eta2 * M ^ 2 + supNorm eta1 * N := by
  rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
  exact supNorm_deriv2_comp_le heta1 heta2 hphi1 hphi2 hbdd1 hbdd2 hM hN

/-! ### The `L¹` comparison -/

/-- **The `L¹` norm under a reparametrization.**  If `φ' ≥ m > 0`, the integral
of `|η ∘ φ|` over `[a, b]` is at most `m⁻¹` times the integral of `|η|` over the
image interval. -/
theorem integral_abs_comp_le {m a b : ℝ} (hm : 0 < m) (hab : a ≤ b)
    (heta : Continuous eta)
    (hphi1 : ∀ u, HasDerivAt phi (phi1 u) u) (hphi1c : Continuous phi1)
    (hlow : ∀ u, m ≤ phi1 u) :
    (∫ u in a..b, |eta (phi u)|) ≤ (1 / m) * ∫ x in (phi a)..(phi b), |eta x| := by
  have hphid : Differentiable ℝ phi := fun u => (hphi1 u).differentiableAt
  have hphic : Continuous phi := hphid.continuous
  have hcomp : Continuous fun u => |eta (phi u)| := (heta.comp hphic).abs
  -- the change of variables
  have hchange : (∫ u in a..b, phi1 u • |eta (phi u)|) = ∫ x in (phi a)..(phi b), |eta x| :=
    intervalIntegral.integral_comp_smul_deriv (f := phi) (f' := phi1) (g := fun x => |eta x|)
      (fun x _ => hphi1 x) hphi1c.continuousOn heta.abs
  have hmono : (∫ u in a..b, |eta (phi u)|)
      ≤ ∫ u in a..b, (1 / m) * (phi1 u * |eta (phi u)|) := by
    refine intervalIntegral.integral_mono_on hab (hcomp.intervalIntegrable _ _)
      (((continuous_const.mul (hphi1c.mul hcomp))).intervalIntegrable _ _) (fun u _ => ?_)
    have hkey : m * |eta (phi u)| ≤ phi1 u * |eta (phi u)| :=
      mul_le_mul_of_nonneg_right (hlow u) (abs_nonneg _)
    have hm' : (0 : ℝ) < 1 / m := by positivity
    calc |eta (phi u)| = (1 / m) * (m * |eta (phi u)|) := by field_simp
      _ ≤ (1 / m) * (phi1 u * |eta (phi u)|) := mul_le_mul_of_nonneg_left hkey hm'.le
  calc (∫ u in a..b, |eta (phi u)|)
      ≤ ∫ u in a..b, (1 / m) * (phi1 u * |eta (phi u)|) := hmono
    _ = (1 / m) * ∫ u in a..b, phi1 u * |eta (phi u)| := by
        rw [intervalIntegral.integral_const_mul]
    _ = (1 / m) * ∫ x in (phi a)..(phi b), |eta x| := by
        rw [← hchange]
        simp [smul_eq_mul]

end PathFunctionalsReparam
