import Mathlib

/-!
# The frame-data bounds of a family moving in a gauge

The data `GaugeFlowVariableSpeedPath.GaugeMarkedData` asks, besides the field of
the gauge flow, for two comparisons with the cost density of the path:

```
  A t + κ̂ · R_b t ≤ (1/P₀) · m t ,
  K_t t + K_x t · R_b t ≤ (1/P₀² + κ̂²) · m t ,
```

where `A` bounds the time derivative of the tangent angle of the slices, `K_t`
the time derivative of their curvature, `K_x` the arclength derivative of the
curvature and `R_b` the field itself.  This file produces the two left-hand
sides from the *normal-flow relations* of a family of curves carried in their
own arclength and moving with tangential rate `ξ` and normal rate `η`:

```
  ∂_tα = ∂_sη + k ξ ,        ∂_t k = ∂_s²η + k² η + ξ ∂_s k ,
```

so that the tangent angle and the curvature move at rates bounded by the sup
norms `S₀`, `S₁`, `S₂` of the normal rate and of its first two arclength
derivatives, together with the size of the tangential rate — and these are
exactly the quantities that the cost density of a normal path dominates.

The two relations themselves are derived from the motion of the family, from the
equality of the mixed partial derivatives and from the identity `∂_sξ = kη` that
says the arclength parametrization is preserved (`angleRate_eq`,
`curvRate_eq`).

Main results: `angleRate_eq`, `curvRate_eq`, `abs_angleRate_le`,
`abs_curvRate_le`, and the two cost comparisons `angleRate_le_cost`,
`curvRate_le_cost`.
-/

noncomputable section

namespace GaugeFrameTimeBounds

/-! ### The two normal-flow relations -/

/-- **The tangent angle turns at the rate `∂_sη + kξ`.**  For a family carried in
its own arclength, moving with tangential rate `ξ` and normal rate `η`, the
mixed partial derivative of the position is on one side the time derivative of
the unit tangent and on the other the arclength derivative of the velocity;
with `∂_sξ = kη` — the identity that preserves the arclength parametrization —
the two give `∂_tα = ∂_sη + kξ`. -/
theorem angleRate_eq {alpha k xi eta etaS alphaT : ℝ → ℝ → ℝ} {W : ℂ} (t s : ℝ)
    (halphaS : ∀ x, HasDerivAt (alpha t) (k t x) x)
    (hetaS : ∀ x, HasDerivAt (eta t) (etaS t x) x)
    (hxiS : ∀ x, HasDerivAt (xi t) (k t x * eta t x) x)
    (halphaT : HasDerivAt (fun r => alpha r s) (alphaT t s) t)
    (htangent : HasDerivAt (fun r => Complex.exp (Complex.I * (alpha r s : ℂ))) W t)
    (hvel : HasDerivAt (fun x => (xi t x : ℂ) * Complex.exp (Complex.I * (alpha t x : ℂ))
        + (eta t x : ℂ) * (Complex.I * Complex.exp (Complex.I * (alpha t x : ℂ)))) W s) :
    alphaT t s = etaS t s + k t s * xi t s := by
  -- the time derivative of the unit tangent
  have hT : HasDerivAt (fun r => Complex.exp (Complex.I * (alpha r s : ℂ)))
      (Complex.I * ((alphaT t s : ℝ) : ℂ) * Complex.exp (Complex.I * (alpha t s : ℂ))) t := by
    have h1 : HasDerivAt (fun r => Complex.I * ((alpha r s : ℝ) : ℂ))
        (Complex.I * ((alphaT t s : ℝ) : ℂ)) t := halphaT.ofReal_comp.const_mul Complex.I
    simpa [mul_comm, mul_assoc] using h1.cexp
  -- the arclength derivative of the velocity
  have hexp : ∀ x, HasDerivAt (fun y => Complex.exp (Complex.I * (alpha t y : ℂ)))
      (Complex.I * ((k t x : ℝ) : ℂ) * Complex.exp (Complex.I * (alpha t x : ℂ))) x := by
    intro x
    have h1 : HasDerivAt (fun y => Complex.I * ((alpha t y : ℝ) : ℂ))
        (Complex.I * ((k t x : ℝ) : ℂ)) x := (halphaS x).ofReal_comp.const_mul Complex.I
    simpa [mul_comm, mul_assoc] using h1.cexp
  have hV : HasDerivAt (fun x => (xi t x : ℂ) * Complex.exp (Complex.I * (alpha t x : ℂ))
      + (eta t x : ℂ) * (Complex.I * Complex.exp (Complex.I * (alpha t x : ℂ))))
      (Complex.I * ((etaS t s + k t s * xi t s : ℝ) : ℂ)
        * Complex.exp (Complex.I * (alpha t s : ℂ))) s := by
    have h1 := ((hxiS s).ofReal_comp.mul (hexp s))
    have h2 := ((hetaS s).ofReal_comp.mul ((hexp s).const_mul Complex.I))
    have h := h1.add h2
    refine h.congr_deriv ?_
    push_cast
    linear_combination ((k t s : ℂ) * (eta t s : ℂ)
      * Complex.exp (Complex.I * (alpha t s : ℂ))) * Complex.I_sq
  -- the two agree, and the exponential does not vanish
  have heq : Complex.I * ((alphaT t s : ℝ) : ℂ) * Complex.exp (Complex.I * (alpha t s : ℂ))
      = Complex.I * ((etaS t s + k t s * xi t s : ℝ) : ℂ)
        * Complex.exp (Complex.I * (alpha t s : ℂ)) := by
    rw [hT.unique htangent, hvel.unique hV]
  have hne : Complex.exp (Complex.I * (alpha t s : ℂ)) ≠ 0 := Complex.exp_ne_zero _
  have hIne : (Complex.I : ℂ) ≠ 0 := Complex.I_ne_zero
  have hcast : ((alphaT t s : ℝ) : ℂ) = ((etaS t s + k t s * xi t s : ℝ) : ℂ) :=
    mul_left_cancel₀ hIne (mul_right_cancel₀ hne heq)
  exact_mod_cast hcast

/-- **The curvature moves at the rate `∂_s²η + k²η + ξ ∂_s k`.**  Differentiating
the angle relation in the arclength, with `∂_sξ = kη` again. -/
theorem curvRate_eq {k xi eta etaS etaSS kX alphaT kT : ℝ → ℝ → ℝ} (t s : ℝ)
    (hrel : ∀ x, alphaT t x = etaS t x + k t x * xi t x)
    (hetaSS : ∀ x, HasDerivAt (etaS t) (etaSS t x) x)
    (hkX : ∀ x, HasDerivAt (k t) (kX t x) x)
    (hxiS : ∀ x, HasDerivAt (xi t) (k t x * eta t x) x)
    (halphaTS : HasDerivAt (alphaT t) (kT t s) s) :
    kT t s = etaSS t s + k t s ^ 2 * eta t s + xi t s * kX t s := by
  have hsum : HasDerivAt (fun x => etaS t x + k t x * xi t x)
      (etaSS t s + (kX t s * xi t s + k t s * (k t s * eta t s))) s :=
    (hetaSS s).add ((hkX s).mul (hxiS s))
  have hcongr : HasDerivAt (alphaT t)
      (etaSS t s + (kX t s * xi t s + k t s * (k t s * eta t s))) s := by
    refine hsum.congr_of_eventuallyEq ?_
    exact Filter.Eventually.of_forall fun x => hrel x
  have h := halphaTS.unique hcongr
  rw [h]
  ring

/-- The bound for the time derivative of the tangent angle: the first arclength
derivative of the normal rate, plus the curvature times the tangential rate. -/
def angleRateBound (S1 Rb : ℝ → ℝ) (khat : ℝ) : ℝ → ℝ := fun t => S1 t + khat * Rb t

/-- The bound for the time derivative of the curvature: the second arclength
derivative of the normal rate, plus the square of the curvature times the normal
rate, plus the tangential rate times the arclength derivative of the
curvature. -/
def curvRateBound (S0 S2 Rb Kx : ℝ → ℝ) (khat : ℝ) : ℝ → ℝ :=
  fun t => S2 t + khat ^ 2 * S0 t + Rb t * Kx t

theorem angleRateBound_nonneg {S1 Rb : ℝ → ℝ} {khat : ℝ} (hS1 : ∀ t, 0 ≤ S1 t)
    (hRb : ∀ t, 0 ≤ Rb t) (hkhat : 0 ≤ khat) (t : ℝ) : 0 ≤ angleRateBound S1 Rb khat t :=
  add_nonneg (hS1 t) (mul_nonneg hkhat (hRb t))

theorem curvRateBound_nonneg {S0 S2 Rb Kx : ℝ → ℝ} {khat : ℝ} (hS0 : ∀ t, 0 ≤ S0 t)
    (hS2 : ∀ t, 0 ≤ S2 t) (hRb : ∀ t, 0 ≤ Rb t) (hKx : ∀ t, 0 ≤ Kx t) (t : ℝ) :
    0 ≤ curvRateBound S0 S2 Rb Kx khat t :=
  add_nonneg (add_nonneg (hS2 t) (mul_nonneg (sq_nonneg khat) (hS0 t)))
    (mul_nonneg (hRb t) (hKx t))

/-! ### The two pointwise bounds -/

/-- **The tangent angle turns at the rate `∂_sη + kξ`**, hence at most
`S₁ + κ̂ R_b`. -/
theorem abs_angleRate_le {alphaT etaS k xi : ℝ → ℝ → ℝ} {S1 Rb : ℝ → ℝ} {khat : ℝ}
    (t x : ℝ) (hrel : alphaT t x = etaS t x + k t x * xi t x)
    (hetaS : |etaS t x| ≤ S1 t) (hk : |k t x| ≤ khat) (hxi : |xi t x| ≤ Rb t) :
    |alphaT t x| ≤ angleRateBound S1 Rb khat t := by
  have hkhat : 0 ≤ khat := le_trans (abs_nonneg _) hk
  calc |alphaT t x| = |etaS t x + k t x * xi t x| := by rw [hrel]
    _ ≤ |etaS t x| + |k t x * xi t x| := abs_add_le _ _
    _ = |etaS t x| + |k t x| * |xi t x| := by rw [abs_mul]
    _ ≤ S1 t + khat * Rb t :=
        add_le_add hetaS (mul_le_mul hk hxi (abs_nonneg _) hkhat)
    _ = angleRateBound S1 Rb khat t := rfl

/-- **The curvature moves at the rate `∂_s²η + k²η + ξ ∂_s k`**, hence at most
`S₂ + κ̂² S₀ + R_b K_x`. -/
theorem abs_curvRate_le {kT etaSS eta k xi kX : ℝ → ℝ → ℝ} {S0 S2 Rb Kx : ℝ → ℝ} {khat : ℝ}
    (t x : ℝ) (hrel : kT t x = etaSS t x + k t x ^ 2 * eta t x + xi t x * kX t x)
    (hetaSS : |etaSS t x| ≤ S2 t) (heta : |eta t x| ≤ S0 t) (hk : |k t x| ≤ khat)
    (hxi : |xi t x| ≤ Rb t) (hkX : |kX t x| ≤ Kx t) :
    |kT t x| ≤ curvRateBound S0 S2 Rb Kx khat t := by
  have hkhat : 0 ≤ khat := le_trans (abs_nonneg _) hk
  have hRb : 0 ≤ Rb t := le_trans (abs_nonneg _) hxi
  have hsq : |k t x ^ 2| ≤ khat ^ 2 := by
    rw [abs_pow]
    nlinarith [abs_nonneg (k t x)]
  calc |kT t x| = |etaSS t x + k t x ^ 2 * eta t x + xi t x * kX t x| := by rw [hrel]
    _ ≤ |etaSS t x + k t x ^ 2 * eta t x| + |xi t x * kX t x| := abs_add_le _ _
    _ ≤ (|etaSS t x| + |k t x ^ 2 * eta t x|) + |xi t x| * |kX t x| := by
        rw [abs_mul]
        exact add_le_add (abs_add_le _ _) le_rfl
    _ = (|etaSS t x| + |k t x ^ 2| * |eta t x|) + |xi t x| * |kX t x| := by rw [abs_mul]
    _ ≤ (S2 t + khat ^ 2 * S0 t) + Rb t * Kx t :=
        add_le_add (add_le_add hetaSS
          (mul_le_mul hsq heta (abs_nonneg _) (sq_nonneg khat)))
          (mul_le_mul hxi hkX (abs_nonneg _) hRb)
    _ = curvRateBound S0 S2 Rb Kx khat t := by rw [curvRateBound]

/-! ### The two comparisons with the cost density -/

/-- **The angle comparison.**  If the first arclength derivative of the normal
rate and the tangential rate are dominated by the multiples `c₁ m` and `r m` of
the cost density, and the numerical condition `c₁ + 2κ̂ r ≤ 1/P₀` holds, then the
left-hand side of the angle hypothesis of a gauge-marked family is at most
`(1/P₀)·m`. -/
theorem angleRate_le_cost {S1 Rb m : ℝ → ℝ} {khat c1 r P0 : ℝ}
    (hS1 : ∀ t, S1 t ≤ c1 * m t) (hRbm : ∀ t, Rb t ≤ r * m t) (hm : ∀ t, 0 ≤ m t)
    (hkhat : 0 ≤ khat) (hnum : c1 + 2 * khat * r ≤ 1 / P0) (t : ℝ) :
    angleRateBound S1 Rb khat t + khat * Rb t ≤ 1 / P0 * m t := by
  have h1 : angleRateBound S1 Rb khat t + khat * Rb t = S1 t + 2 * khat * Rb t := by
    rw [angleRateBound]; ring
  have h2 : S1 t + 2 * khat * Rb t ≤ c1 * m t + 2 * khat * (r * m t) := by
    have hkk : 0 ≤ 2 * khat := by linarith
    exact add_le_add (hS1 t) (mul_le_mul_of_nonneg_left (hRbm t) hkk)
  have h3 : c1 * m t + 2 * khat * (r * m t) = (c1 + 2 * khat * r) * m t := by ring
  calc angleRateBound S1 Rb khat t + khat * Rb t = S1 t + 2 * khat * Rb t := h1
    _ ≤ c1 * m t + 2 * khat * (r * m t) := h2
    _ = (c1 + 2 * khat * r) * m t := h3
    _ ≤ 1 / P0 * m t := mul_le_mul_of_nonneg_right hnum (hm t)

/-- **The curvature comparison.**  If the normal rate and its second arclength
derivative are dominated by `c₀ m` and `c₂ m`, the tangential rate by `r m`, the
arclength derivative of the curvature is at most `k_x`, and the numerical
condition `c₂ + κ̂² c₀ + 2 r k_x ≤ 1/P₀² + κ̂²` holds, then the left-hand side of
the curvature hypothesis of a gauge-marked family is at most
`(1/P₀² + κ̂²)·m`. -/
theorem curvRate_le_cost {S0 S2 Rb Kx m : ℝ → ℝ} {khat c0 c2 r kx P0 : ℝ}
    (hS0 : ∀ t, S0 t ≤ c0 * m t) (hS2 : ∀ t, S2 t ≤ c2 * m t) (hRbm : ∀ t, Rb t ≤ r * m t)
    (hKx : ∀ t, Kx t ≤ kx) (hKxnn : ∀ t, 0 ≤ Kx t)
    (hm : ∀ t, 0 ≤ m t) (hr : 0 ≤ r)
    (hnum : c2 + khat ^ 2 * c0 + 2 * r * kx ≤ 1 / P0 ^ 2 + khat ^ 2) (t : ℝ) :
    curvRateBound S0 S2 Rb Kx khat t + Kx t * Rb t ≤ (1 / P0 ^ 2 + khat ^ 2) * m t := by
  have hkx0 : 0 ≤ kx := le_trans (hKxnn t) (hKx t)
  have hprod : Rb t * Kx t ≤ (r * m t) * kx :=
    mul_le_mul (hRbm t) (hKx t) (hKxnn t) (mul_nonneg hr (hm t))
  have hsplit : curvRateBound S0 S2 Rb Kx khat t + Kx t * Rb t
      = S2 t + khat ^ 2 * S0 t + 2 * (Rb t * Kx t) := by
    rw [curvRateBound]; ring
  calc curvRateBound S0 S2 Rb Kx khat t + Kx t * Rb t
      = S2 t + khat ^ 2 * S0 t + 2 * (Rb t * Kx t) := hsplit
    _ ≤ c2 * m t + khat ^ 2 * (c0 * m t) + 2 * ((r * m t) * kx) := by
        refine add_le_add (add_le_add (hS2 t)
          (mul_le_mul_of_nonneg_left (hS0 t) (sq_nonneg khat))) ?_
        linarith
    _ = (c2 + khat ^ 2 * c0 + 2 * r * kx) * m t := by ring
    _ ≤ (1 / P0 ^ 2 + khat ^ 2) * m t := mul_le_mul_of_nonneg_right hnum (hm t)

end GaugeFrameTimeBounds
