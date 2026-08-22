import Mathlib
import UnitTangentIterates.UnitTangent
import UnitTangentIterates.MainTheoremConditional

/-!
# The speed and the curvature of the unit-tangent transform

For a curve `γ` parametrized by arclength, with tangent angle `θ` and curvature
`k = θ'`, the unit-tangent transform `𝒯γ = γ + γ'` satisfies

`(𝒯γ)'(s) = (1 + i k(s)) e^{iθ(s)} = √(1 + k(s)²) · e^{i(θ(s) + arctan k(s))}`.

Thus `𝒯γ` is **never** parametrized by arclength when the curvature does not
vanish: its speed is `√(1 + k²) > 1`.  Its tangent angle is `θ + arctan k`, and
its curvature — the derivative of that angle with respect to *its own*
arclength — is

`K = (k' + k + k³)/(1 + k²)^{3/2}`,

which is the quantity denoted `K` in the paper.

Main results:

* `hasDerivAt_unitTangentMap`, `norm_deriv_unitTangentMap` : the derivative and
  the speed of the transform;
* `deriv_unitTangentMap_polar` : the polar form of the derivative, exhibiting
  `θ + arctan k` as the tangent angle of the transform;
* `hasDerivAt_transform_angle`, `transform_curvature_eq` : the derivative of
  that angle and the resulting curvature formula;
* `not_isOval_unitTangentMap` : consequently, the unit-tangent transform of an
  oval is **not** an oval in the sense of `MainTheoremConditional.IsOval`
  (which builds in the unit-speed parametrization).  Statements combining
  `IsOval (X n)` with the exact equality `𝒯(X n) = X (n+1)` are therefore
  vacuous; the correct orbit condition is equality of the *images*, i.e.
  equality up to reparametrization.
-/

noncomputable section

open Set Function

namespace UnitTangentSpeed

variable {γ : ℝ → ℂ} {θ k k' : ℝ → ℝ}

/-- The derivative of the unit-tangent transform of an arclength-parametrized
curve with tangent angle `θ` and curvature `k`: `(𝒯γ)' = (1 + ik)e^{iθ}`. -/
theorem hasDerivAt_unitTangentMap
    (hγ : ∀ s, HasDerivAt γ (Complex.exp (Complex.I * (θ s : ℂ))) s)
    (hθ : ∀ s, HasDerivAt θ (k s) s) (s : ℝ) :
    HasDerivAt (UnitTangent.unitTangentMap γ)
      ((1 + Complex.I * (k s : ℂ)) * Complex.exp (Complex.I * (θ s : ℂ))) s := by
  have hfun : UnitTangent.unitTangentMap γ
      = fun t => γ t + Complex.exp (Complex.I * (θ t : ℂ)) := by
    funext t
    simp [UnitTangent.unitTangentMap, (hγ t).deriv]
  have hinner : ∀ t : ℝ, HasDerivAt (fun u : ℝ => Complex.I * (θ u : ℂ))
      (Complex.I * (k t : ℂ)) t := fun t => ((hθ t).ofReal_comp).const_mul Complex.I
  have hexp : HasDerivAt (fun u : ℝ => Complex.exp (Complex.I * (θ u : ℂ)))
      (Complex.exp (Complex.I * (θ s : ℂ)) * (Complex.I * (k s : ℂ))) s := (hinner s).cexp
  have := (hγ s).add hexp
  rw [hfun]
  convert this using 1
  ring

/-- The speed of the unit-tangent transform is `√(1 + k²)`. -/
theorem norm_deriv_unitTangentMap
    (hγ : ∀ s, HasDerivAt γ (Complex.exp (Complex.I * (θ s : ℂ))) s)
    (hθ : ∀ s, HasDerivAt θ (k s) s) (s : ℝ) :
    ‖deriv (UnitTangent.unitTangentMap γ) s‖ = Real.sqrt (1 + k s ^ 2) := by
  rw [(hasDerivAt_unitTangentMap hγ hθ s).deriv, norm_mul, Complex.norm_exp]
  have h1 : (1 : ℂ) + Complex.I * (k s : ℂ) = ((1 : ℝ) : ℂ) + ((k s : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [h1, Complex.norm_add_mul_I]
  norm_num

/-- The polar form of the derivative of the transform: speed `√(1 + k²)` and
tangent angle `θ + arctan k`. -/
theorem deriv_unitTangentMap_polar
    (hγ : ∀ s, HasDerivAt γ (Complex.exp (Complex.I * (θ s : ℂ))) s)
    (hθ : ∀ s, HasDerivAt θ (k s) s) (s : ℝ) :
    deriv (UnitTangent.unitTangentMap γ) s
      = (Real.sqrt (1 + k s ^ 2) : ℂ) *
          Complex.exp (Complex.I * ((θ s + Real.arctan (k s) : ℝ) : ℂ)) := by
  rw [(hasDerivAt_unitTangentMap hγ hθ s).deriv]
  have hpos : (0 : ℝ) < Real.sqrt (1 + k s ^ 2) := Real.sqrt_pos.mpr (by positivity)
  have hcos : Real.cos (Real.arctan (k s)) = 1 / Real.sqrt (1 + k s ^ 2) := by
    rw [Real.cos_arctan]
  have hsin : Real.sin (Real.arctan (k s)) = k s / Real.sqrt (1 + k s ^ 2) := by
    rw [Real.sin_arctan]
  have hsq : (Real.sqrt (1 + k s ^ 2) : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt hpos
  rw [Complex.ofReal_add]
  rw [show Complex.I * ((θ s : ℂ) + ((Real.arctan (k s) : ℝ) : ℂ))
      = Complex.I * (θ s : ℂ) + Complex.I * (Real.arctan (k s) : ℂ) by ring,
    Complex.exp_add]
  have hkey : Complex.exp (Complex.I * (Real.arctan (k s) : ℂ))
      = (Real.cos (Real.arctan (k s)) : ℂ) + (Real.sin (Real.arctan (k s)) : ℂ) * Complex.I := by
    rw [mul_comm, Complex.exp_mul_I]
    simp
  rw [hkey, hcos, hsin]
  push_cast
  field_simp

/-- The tangent angle of the transform, `θ + arctan k`, has derivative
`k + k'/(1 + k²)` with respect to the arclength of the original curve. -/
theorem hasDerivAt_transform_angle
    (hθ : ∀ s, HasDerivAt θ (k s) s) (hk : ∀ s, HasDerivAt k (k' s) s) (s : ℝ) :
    HasDerivAt (fun t => θ t + Real.arctan (k t)) (k s + k' s / (1 + k s ^ 2)) s := by
  have h := (Real.hasDerivAt_arctan (k s)).comp s (hk s)
  have h' : HasDerivAt (fun t => Real.arctan (k t)) (k' s / (1 + k s ^ 2)) s := by
    convert h using 1
    field_simp
  exact (hθ s).add h'

/-- The curvature of the transform, i.e. the derivative of its tangent angle
with respect to *its own* arclength, is `(k' + k + k³)/(1 + k²)^{3/2}`. -/
theorem transform_curvature_eq (a b : ℝ) :
    (a + b / (1 + a ^ 2)) / Real.sqrt (1 + a ^ 2)
      = (b + a + a ^ 3) / ((1 + a ^ 2) * Real.sqrt (1 + a ^ 2)) := by
  have hpos : (0 : ℝ) < 1 + a ^ 2 := by positivity
  have hs : (0 : ℝ) < Real.sqrt (1 + a ^ 2) := Real.sqrt_pos.mpr hpos
  field_simp
  ring

/-- **The unit-tangent transform of an oval is never an oval.**  An oval is
parametrized by arclength and has positive curvature `k`, so the transform has
speed `√(1 + k²) > 1`; it can therefore not be parametrized by arclength.  In
particular, hypotheses that combine `IsOval (X n)` with the exact identity
`𝒯(X n) = X (n + 1)` are contradictory: the right orbit condition is equality
of images, `range (X (n+1)) = range (𝒯 (X n))`. -/
theorem not_isOval_unitTangentMap (h : MainTheoremConditional.IsOval γ) :
    ¬ MainTheoremConditional.IsOval (UnitTangent.unitTangentMap γ) := by
  obtain ⟨-, -, -, -, θ, hγ, k, hθ, hk⟩ := h
  rintro ⟨-, -, -, -, φ, hφ, -, -, -⟩
  have h1 : ‖deriv (UnitTangent.unitTangentMap γ) 0‖ = 1 := by
    rw [(hφ 0).deriv, Complex.norm_exp]
    simp
  have h2 := norm_deriv_unitTangentMap hγ hθ 0
  rw [h1] at h2
  have h3 : (1 : ℝ) < Real.sqrt (1 + k 0 ^ 2) := by
    have : (1 : ℝ) < 1 + k 0 ^ 2 := by nlinarith [hk 0]
    calc (1 : ℝ) = Real.sqrt 1 := by simp
      _ < Real.sqrt (1 + k 0 ^ 2) := Real.sqrt_lt_sqrt (by norm_num) this
  linarith

/-- The image of the arclength parametrization of a circle is the circle. -/
theorem range_circleCurve {c : ℂ} {r : ℝ} (hr : 0 < r) :
    range (UnitTangent.circleCurve c r) = Metric.sphere c r := by
  ext z
  simp only [mem_range, Metric.mem_sphere, Complex.dist_eq]
  constructor
  · rintro ⟨s, rfl⟩
    simp [UnitTangent.circleCurve, Complex.norm_exp, abs_of_pos hr]
  · intro hz
    refine ⟨r * Complex.arg (z - c), ?_⟩
    have hs : ((r * Complex.arg (z - c) : ℝ) : ℂ) / (r : ℂ)
        = (Complex.arg (z - c) : ℂ) := by
      have : (r : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hr
      push_cast
      field_simp
    simp only [UnitTangent.circleCurve, hs]
    have hkey := Complex.norm_mul_exp_arg_mul_I (z - c)
    rw [hz] at hkey
    rw [show Complex.I * (Complex.arg (z - c) : ℂ)
        = (Complex.arg (z - c) : ℂ) * Complex.I from mul_comm _ _, hkey]
    ring

/-- The unit-tangent image of the circle of radius `r` is the image of the
circle of radius `√(r² + 1)`: the orbit condition **up to reparametrization**
is satisfied by circles. -/
theorem range_unitTangentMap_circleCurve_eq {c : ℂ} {r : ℝ} (hr : 0 < r) :
    range (UnitTangent.unitTangentMap (UnitTangent.circleCurve c r))
      = range (UnitTangent.circleCurve c (Real.sqrt (r ^ 2 + 1))) := by
  rw [UnitTangent.range_unitTangentMap_circleCurve hr,
    range_circleCurve (Real.sqrt_pos.mpr (by positivity))]

/-- **The corrected orbit condition is not vacuous.**  There is a sequence of
ovals `X` with `range (X (n+1)) = range (𝒯 (X n))` for every `n`: the circles of
radii `√(r² + n)`.  (Of course all of them are circles; the content of the
paper's theorem is that a *noncircular* such orbit exists.) -/
theorem exists_range_orbit_of_ovals {c : ℂ} {r : ℝ} (hr : 0 < r) :
    ∃ X : ℕ → ℝ → ℂ, (∀ n, MainTheoremConditional.IsOval (X n)) ∧
      ∀ n, range (X (n + 1)) = range (UnitTangent.unitTangentMap (X n)) := by
  have hpos : ∀ n : ℕ, 0 < Real.sqrt (r ^ 2 + n) := fun n =>
    Real.sqrt_pos.mpr (by positivity)
  refine ⟨fun n => UnitTangent.circleCurve c (Real.sqrt (r ^ 2 + n)),
    fun n => MainTheoremConditional.isOval_circleCurve (hpos n), fun n => ?_⟩
  rw [range_unitTangentMap_circleCurve_eq (hpos n)]
  congr 2
  rw [Real.sq_sqrt (by positivity)]
  push_cast
  ring_nf

private lemma quotient_algebra (S x y : ℝ) (hS : 0 < S) (h : S ^ 2 = 1 + x ^ 2) :
    y / ((1 + x ^ 2) * S) = (y * S - x * (1 / (2 * S) * (2 * x * y))) / S ^ 2 := by
  have hne : S ≠ 0 := ne_of_gt hS
  rw [← h]
  field_simp
  linear_combination (-y) * h

/-- The derivative of `u = k/√(1+k²)`, the sine of the angle `arctan k`. -/
theorem hasDerivAt_u (hk : ∀ s, HasDerivAt k (k' s) s) (s : ℝ) :
    HasDerivAt (fun t => k t / Real.sqrt (1 + k t ^ 2))
      (k' s / ((1 + k s ^ 2) * Real.sqrt (1 + k s ^ 2))) s := by
  have hpos : (0 : ℝ) < 1 + k s ^ 2 := by positivity
  have hsp : (0 : ℝ) < Real.sqrt (1 + k s ^ 2) := Real.sqrt_pos.mpr hpos
  have hinner : HasDerivAt (fun t => 1 + k t ^ 2) (2 * k s * k' s) s := by
    have := ((hk s).pow 2).const_add 1
    convert this using 1
    ring
  have hsqrt : HasDerivAt (fun t => Real.sqrt (1 + k t ^ 2))
      (1 / (2 * Real.sqrt (1 + k s ^ 2)) * (2 * k s * k' s)) s :=
    (Real.hasDerivAt_sqrt (ne_of_gt hpos)).comp s hinner
  have h := (hk s).div hsqrt (ne_of_gt hsp)
  convert h using 1
  exact quotient_algebra _ _ _ hsp (Real.sq_sqrt hpos.le)

/-- **The curvature of the unit-tangent transform is `u' + u`**, with
`u = k/√(1+k²)`: this is the quantity `K` appearing in the paper's convexity
criterion `UnitTangent.curvature_pos_of_next_track_convex`. -/
theorem transform_curvature_eq_deriv_u_add_u (hk : ∀ s, HasDerivAt k (k' s) s) (s : ℝ) :
    (k s + k' s / (1 + k s ^ 2)) / Real.sqrt (1 + k s ^ 2)
      = deriv (fun t => k t / Real.sqrt (1 + k t ^ 2)) s
        + k s / Real.sqrt (1 + k s ^ 2) := by
  have hpos : (0 : ℝ) < 1 + k s ^ 2 := by positivity
  have hsp : (0 : ℝ) < Real.sqrt (1 + k s ^ 2) := Real.sqrt_pos.mpr hpos
  rw [(hasDerivAt_u hk s).deriv]
  field_simp
  ring

/-- **Lemma 2.2 in terms of the curvature of the transform.**  If a closed curve
has nonnegative, not identically vanishing curvature `k`, and the curvature of
its unit-tangent transform, `K = (k + k'/(1+k²))/√(1+k²)`, is nonnegative, then
`k > 0` everywhere: the curve is strictly convex.  This is
`UnitTangent.curvature_pos_of_next_track_convex` with the hypothesis expressed
through the geometric curvature of the transform. -/
theorem curvature_pos_of_transform_curvature_nonneg {L : ℝ} (hL : 0 < L)
    (hper : Periodic k L) (hk : ∀ s, HasDerivAt k (k' s) s) (hnn : ∀ s, 0 ≤ k s)
    (hK : ∀ s, 0 ≤ (k s + k' s / (1 + k s ^ 2)) / Real.sqrt (1 + k s ^ 2))
    (hne : ∃ x, k x ≠ 0) : ∀ x, 0 < k x := by
  refine UnitTangent.curvature_pos_of_next_track_convex hL hper
    (fun s => (hk s).differentiableAt) hnn (fun s => ?_) hne
  have h := hK s
  rwa [transform_curvature_eq_deriv_u_add_u hk s] at h

end UnitTangentSpeed
