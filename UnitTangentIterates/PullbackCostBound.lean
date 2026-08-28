import UnitTangentIterates.SliceToPathBound

/-!
# The pullback constructor's output, bounded

§71 listed "the construction of `𝔅Γ` itself" as the one remaining item.  It is
not missing.  `GaugeRearFamilyFromFront.exists_variableSpeed_normalPath_of_rearFamily_from_front`
already builds it: from a front path `Γ`, the selected-rear family, and a cost
density `m`, it returns

```
  ∃ Γ' : NormalPath a b,  Γ'.T = Γ.T  ∧  …  ∧  cost Γ' = ∫₀^{Γ.T} m t  ∧  … ,
```

together with the variable-speed certificate.

This file connects that output to the per-path bound.
`cost_le_of_cost_eq_integral` : with the slicewise Jacobi bound on `m` (§71
supplies it from the three gains), the constructor's cost is at most `C · cost Γ`;
`pathDist_le_of_cost_eq_integral` is the same for the pseudodistance, which is
the shape §65 reduces `hmap` to.

So the per-path Jacobi bound has no missing ingredient.  What separates it from
a theorem is the instantiation: the constructor takes some forty hypotheses
about the front family, the steering angle, the rear arclength and their
regularity, and those have to be supplied for the model orbit.
-/

noncomputable section

set_option maxHeartbeats 4000000

open Set Real MeasureTheory MarkedSpace

namespace PathMetric

open NormalPath

/-- **The constructor's output, bounded.**  `GaugeRearFamilyFromFront`'s
constructor returns a pullback path whose cost is exactly `∫₀^T m`, for the cost
density `m` it was handed.  Combined with the slicewise Jacobi bound on `m`,
that gives the per-path bound directly. -/
theorem cost_le_of_cost_eq_integral {p q p' q' : Data} {C : ℝ} {m : ℝ → ℝ}
    (hC : 0 ≤ C) (Γ : NormalPath p q) (Γ' : NormalPath p' q')
    (hcost : cost Γ' = ∫ t in (0:ℝ)..Γ.T, m t) (hT0 : 0 ≤ Γ.T)
    (hmi : IntervalIntegrable m volume 0 Γ.T)
    (hgi : IntervalIntegrable (fun t => C * Γ.m t) volume 0 Γ.T)
    (hm : ∀ t, m t ≤ C * ∫ u in (0:ℝ)..1, |Γ.eta t u|) :
    cost Γ' ≤ C * cost Γ := by
  have hstep : ∀ t, m t ≤ C * Γ.m t := fun t =>
    le_trans (hm t) (mul_le_mul_of_nonneg_left (Γ.le_m_L1 t) hC)
  rw [hcost, cost]
  refine le_trans (intervalIntegral.integral_mono_on hT0 hmi hgi
    (fun t _ => hstep t)) ?_
  rw [intervalIntegral.integral_const_mul]

/-- And hence the pseudodistance bound that `hmap` is reduced to. -/
theorem pathDist_le_of_cost_eq_integral {p q p' q' : Data} {C : ℝ} {m : ℝ → ℝ}
    (hC : 0 ≤ C) (Γ : NormalPath p q) (Γ' : NormalPath p' q')
    (hcost : cost Γ' = ∫ t in (0:ℝ)..Γ.T, m t) (hT0 : 0 ≤ Γ.T)
    (hmi : IntervalIntegrable m volume 0 Γ.T)
    (hgi : IntervalIntegrable (fun t => C * Γ.m t) volume 0 Γ.T)
    (hm : ∀ t, m t ≤ C * ∫ u in (0:ℝ)..1, |Γ.eta t u|) :
    pathDist p' q' ≤ C * cost Γ :=
  le_trans (pathDist_le_cost Γ')
    (cost_le_of_cost_eq_integral hC Γ Γ' hcost hT0 hmi hgi hm)

end PathMetric
