import Mathlib
import UnitTangentIterates.PathMetric
import UnitTangentIterates.NormalFlow
import UnitTangentIterates.MarkedTopology

/-!
# The `C²` increment of a normal path, bounded by its cost

The lemma *Completeness of summable normal paths* of the paper *A Noncircular
Oval with Convex Unit-Tangent Iterates* concludes convergence of a sequence of
marked curves from the summability of the path functionals `S₀ + S₁ + S₂` of
the paths joining them.  `MarkedTopology.limit_of_summable_normal_paths` is
that conclusion, but it takes the increments of the curve, of its velocity and
of its acceleration as given.  This file produces those increments from the
**cost of the path**, which is the quantity the pseudodistance of
`PathMetric.lean` is built from and which dominates all four functionals of the
paper.

The mechanism is the normal-flow identities of `NormalFlow.lean`,

```
  (log g)_t = -κ η ,      τ_t = η_s ν ,      κ_t = η_ss + κ² η ,
```

integrated in time against the cost density `m` of the path.  Along a path
whose slices are constant-speed closed curves — the parametrization the marked
curves of this project carry — the speed `g` is the arclength period `P t`, the
velocity is `V = P e^{iθ}` and the acceleration is `A = i P² κ e^{iθ}`, so the
three increments of the marked datum are controlled by those of `P`, `θ` and
`κ`:

* `abs_period_sub_le` : `|P T − P 0| ≤ κ̂ P₁ · cost Γ`;
* `abs_angle_sub_le` : `|θ T u − θ 0 u| ≤ cost Γ / P₀`;
* `abs_curv_sub_le` : `|κ T u − κ 0 u| ≤ (1/P₀² + κ̂²) · cost Γ`;
* `norm_vel_sub_le`, `norm_acc_sub_le` : the resulting bounds for the velocity
  and the acceleration of the two ends;
* `dist_le_cost` : **the marked distance of the two ends of a normal path is at
  most `c₂(P₀,P₁,κ̂) · cost Γ`**, with the explicit constant `c2Const`.

The bounds on the time derivatives are stated in the form the normal-flow
identities give them, with the passage from the arclength derivatives `η_s`,
`η_ss` of the paper to the derivatives in the normalized parameter — which is
what the cost density of a normal path dominates — folded into the constants:
`η_s = η_u/g` and `η_ss = η_uu/g²` with `g ≥ P₀`.
-/

noncomputable section

open Set Function Complex MeasureTheory Filter Topology
open MarkedSpace PathMetric PathMetric.NormalPath

namespace NormalPathC2Increment

/-! ### Two elementary estimates -/

/-- **Integrating a derivative bounded by a multiple of the cost density.**  If
`|f'| ≤ C·m` pointwise, then `f` moves by at most `C` times the integral of
`m`. -/
theorem abs_sub_le_of_deriv_le {T C : ℝ} {f f' m : ℝ → ℝ} (hT : 0 ≤ T)
    (hf : ∀ t, HasDerivAt f (f' t) t) (hf'c : Continuous f') (hmc : Continuous m)
    (hbd : ∀ t, |f' t| ≤ C * m t) :
    |f T - f 0| ≤ C * ∫ t in (0:ℝ)..T, m t := by
  have hFTC : (∫ t in (0:ℝ)..T, f' t) = f T - f 0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hf t)
      (hf'c.intervalIntegrable _ _)
  rw [← hFTC]
  calc |∫ t in (0:ℝ)..T, f' t| ≤ ∫ t in (0:ℝ)..T, |f' t| :=
        intervalIntegral.abs_integral_le_integral_abs hT
    _ ≤ ∫ t in (0:ℝ)..T, C * m t :=
        intervalIntegral.integral_mono_on hT (hf'c.abs.intervalIntegrable _ _)
          ((continuous_const.mul hmc).intervalIntegrable _ _) (fun t _ => hbd t)
    _ = C * ∫ t in (0:ℝ)..T, m t := intervalIntegral.integral_const_mul _ _

/-- The unit tangent moves by at most the increment of the tangent angle. -/
theorem norm_exp_I_sub_le (a b : ℝ) :
    ‖Complex.exp (Complex.I * (a : ℂ)) - Complex.exp (Complex.I * (b : ℂ))‖ ≤ |a - b| := by
  have hderiv : ∀ x : ℝ, HasDerivAt (fun y : ℝ => Complex.exp (Complex.I * (y : ℂ)))
      (Complex.I * Complex.exp (Complex.I * (x : ℂ))) x := by
    intro x
    have h1 : HasDerivAt (fun y : ℝ => Complex.I * (y : ℂ)) Complex.I x := by
      simpa using (Complex.ofRealCLM.hasDerivAt (x := x)).const_mul Complex.I
    simpa [mul_comm] using h1.cexp
  have hbound : ∀ x ∈ (univ : Set ℝ),
      ‖Complex.I * Complex.exp (Complex.I * (x : ℂ))‖ ≤ 1 := by
    intro x _
    rw [norm_mul, Complex.norm_I, one_mul]
    have : ‖Complex.exp (Complex.I * (x : ℂ))‖ = 1 := by
      rw [Complex.norm_exp]
      simp
    rw [this]
  have := (convex_univ (𝕜 := ℝ) (E := ℝ)).norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun y : ℝ => Complex.exp (Complex.I * (y : ℂ)))
    (f' := fun x : ℝ => Complex.I * Complex.exp (Complex.I * (x : ℂ)))
    (fun x _ => (hderiv x).hasDerivWithinAt) hbound (mem_univ b) (mem_univ a)
  simpa [Real.norm_eq_abs] using this

/-! ### The setting -/

variable {p q : Data} {P Pd : ℝ → ℝ} {theta kappa etas kt : ℝ → ℝ → ℝ}
  {P0 P1 khat : ℝ}

/-- **The increment of the arclength period.**  The speed equation
`(log g)_t = −κη` bounds the change of the period of the slices by
`κ̂ P₁ · cost Γ`. -/
theorem abs_period_sub_le (Γ : NormalPath p q)
    (hPd : ∀ t, HasDerivAt P (Pd t) t) (hPdc : Continuous Pd)
    (hPdbd : ∀ t, |Pd t| ≤ khat * P1 * Γ.m t) :
    |P Γ.T - P 0| ≤ khat * P1 * cost Γ :=
  abs_sub_le_of_deriv_le Γ.T_pos.le hPd hPdc Γ.cont_m hPdbd

/-- **The increment of the tangent angle.**  The tangent equation `τ_t = η_s ν`
bounds the change of the tangent angle by `cost Γ / P₀`. -/
theorem abs_angle_sub_le (Γ : NormalPath p q)
    (hthetat : ∀ t u, HasDerivAt (fun r => theta r u) (etas t u) t)
    (hetasc : ∀ u, Continuous fun t => etas t u)
    (hetas : ∀ t u, |etas t u| ≤ (1 / P0) * Γ.m t) (u : ℝ) :
    |theta Γ.T u - theta 0 u| ≤ (1 / P0) * cost Γ :=
  abs_sub_le_of_deriv_le Γ.T_pos.le (fun t => hthetat t u) (hetasc u) Γ.cont_m
    (fun t => hetas t u)

/-- **The increment of the curvature.**  The curvature equation
`κ_t = η_ss + κ²η` bounds the change of the curvature by
`(1/P₀² + κ̂²) · cost Γ`. -/
theorem abs_curv_sub_le (Γ : NormalPath p q)
    (hkappat : ∀ t u, HasDerivAt (fun r => kappa r u) (kt t u) t)
    (hktc : ∀ u, Continuous fun t => kt t u)
    (hkt : ∀ t u, |kt t u| ≤ (1 / P0 ^ 2 + khat ^ 2) * Γ.m t) (u : ℝ) :
    |kappa Γ.T u - kappa 0 u| ≤ (1 / P0 ^ 2 + khat ^ 2) * cost Γ :=
  abs_sub_le_of_deriv_le Γ.T_pos.le (fun t => hkappat t u) (hktc u) Γ.cont_m
    (fun t => hkt t u)

/-! ### The frame of a slice -/

/-- The velocity of the end of a normal path whose slices are constant-speed
curves of tangent angle `θ`: `V = P e^{iθ}`. -/
theorem vel_eq_of_slice {c kmin dlt : ℝ} (Γ : NormalPath p q) (t : ℝ)
    {r : Data} (hr : IsTubeMember c kmin dlt r) (hXr : Γ.X t = ⇑r.1)
    (hXu : ∀ u, HasDerivAt (Γ.X t) ((P t : ℂ) * Complex.exp (Complex.I * (theta t u : ℂ))) u)
    (u : ℝ) :
    r.2.1 u = (P t : ℂ) * Complex.exp (Complex.I * (theta t u : ℂ)) := by
  have h1 : HasDerivAt (⇑r.1) ((P t : ℂ) * Complex.exp (Complex.I * (theta t u : ℂ))) u := by
    rw [← hXr]; exact hXu u
  exact (hr.hasDerivAt_curve u).unique h1

/-- The acceleration of the end of a normal path whose slices are constant-speed
curves of tangent angle `θ` and curvature `κ`: `A = i P² κ e^{iθ}`. -/
theorem acc_eq_of_slice {c kmin dlt : ℝ} (Γ : NormalPath p q) (t : ℝ)
    {r : Data} (hr : IsTubeMember c kmin dlt r) (hXr : Γ.X t = ⇑r.1)
    (hXu : ∀ u, HasDerivAt (Γ.X t) ((P t : ℂ) * Complex.exp (Complex.I * (theta t u : ℂ))) u)
    (hthetau : ∀ u, HasDerivAt (theta t) (P t * kappa t u) u) (u : ℝ) :
    r.2.2 u
      = Complex.I * ((P t ^ 2 * kappa t u : ℝ) : ℂ)
          * Complex.exp (Complex.I * (theta t u : ℂ)) := by
  have hveq : ⇑r.2.1 = fun v => (P t : ℂ) * Complex.exp (Complex.I * (theta t v : ℂ)) :=
    funext fun v => vel_eq_of_slice Γ t hr hXr hXu v
  have hexp : HasDerivAt (fun v => Complex.exp (Complex.I * (theta t v : ℂ)))
      (Complex.I * ((P t * kappa t u : ℝ) : ℂ)
        * Complex.exp (Complex.I * (theta t u : ℂ))) u := by
    have h1 : HasDerivAt (fun v => Complex.I * ((theta t v : ℝ) : ℂ))
        (Complex.I * ((P t * kappa t u : ℝ) : ℂ)) u :=
      (Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt u (hthetau u)).const_mul Complex.I
    simpa [mul_comm] using h1.cexp
  have h2 : HasDerivAt (⇑r.2.1)
      (Complex.I * ((P t ^ 2 * kappa t u : ℝ) : ℂ)
        * Complex.exp (Complex.I * (theta t u : ℂ))) u := by
    rw [hveq]
    have := hexp.const_mul ((P t : ℝ) : ℂ)
    convert this using 1
    push_cast
    ring
  exact (hr.hasDerivAt_vel u).unique h2

/-! ### The marked distance of the two ends -/

/-- The constant of the velocity increment. -/
def velConst (P0 P1 khat : ℝ) : ℝ := khat * P1 + P1 * (1 / P0)

/-- The constant of the acceleration increment. -/
def accConst (P0 P1 khat : ℝ) : ℝ :=
  P1 ^ 2 * (1 / P0 ^ 2 + khat ^ 2) + 2 * khat ^ 2 * P1 ^ 2 + khat * P1 ^ 2 * (1 / P0)

/-- The constant of the marked distance of the two ends of a normal path. -/
def c2Const (P0 P1 khat : ℝ) : ℝ := max 1 (max (velConst P0 P1 khat) (accConst P0 P1 khat))

theorem one_le_c2Const (P0 P1 khat : ℝ) : 1 ≤ c2Const P0 P1 khat := le_max_left _ _

theorem c2Const_nonneg (P0 P1 khat : ℝ) : 0 ≤ c2Const P0 P1 khat :=
  le_trans zero_le_one (one_le_c2Const P0 P1 khat)

/-- **The velocity increment of a normal path.** -/
theorem norm_vel_sub_le {c kmin dlt cq kminq dltq : ℝ} (Γ : NormalPath p q)
    (hp : IsTubeMember c kmin dlt p) (hq : IsTubeMember cq kminq dltq q)
    (hXu : ∀ t u, HasDerivAt (Γ.X t)
      ((P t : ℂ) * Complex.exp (Complex.I * (theta t u : ℂ))) u)
    (hPd : ∀ t, HasDerivAt P (Pd t) t) (hPdc : Continuous Pd)
    (hPdbd : ∀ t, |Pd t| ≤ khat * P1 * Γ.m t)
    (hthetat : ∀ t u, HasDerivAt (fun r => theta r u) (etas t u) t)
    (hetasc : ∀ u, Continuous fun t => etas t u)
    (hetas : ∀ t u, |etas t u| ≤ (1 / P0) * Γ.m t)
    (hPu : ∀ t, 0 ≤ P t) (hPub : ∀ t, P t ≤ P1) (u : ℝ) :
    ‖q.2.1 u - p.2.1 u‖ ≤ velConst P0 P1 khat * cost Γ := by
  have hcost : 0 ≤ cost Γ := Γ.cost_nonneg
  have hvp := vel_eq_of_slice (P := P) (theta := theta) Γ 0 hp (funext Γ.start) (hXu 0) u
  have hvq := vel_eq_of_slice (P := P) (theta := theta) Γ Γ.T hq (funext Γ.finish) (hXu Γ.T) u
  rw [hvp, hvq]
  have hsplit : (P Γ.T : ℂ) * Complex.exp (Complex.I * (theta Γ.T u : ℂ))
      - (P 0 : ℂ) * Complex.exp (Complex.I * (theta 0 u : ℂ))
      = ((P Γ.T - P 0 : ℝ) : ℂ) * Complex.exp (Complex.I * (theta Γ.T u : ℂ))
        + (P 0 : ℂ) * (Complex.exp (Complex.I * (theta Γ.T u : ℂ))
            - Complex.exp (Complex.I * (theta 0 u : ℂ))) := by
    push_cast; ring
  rw [hsplit]
  have he1 : ‖Complex.exp (Complex.I * (theta Γ.T u : ℂ))‖ = 1 := by
    rw [Complex.norm_exp]; simp
  have hP := abs_period_sub_le (P1 := P1) (khat := khat) Γ hPd hPdc hPdbd
  have hth := abs_angle_sub_le (P0 := P0) Γ hthetat hetasc hetas u
  have hexp := norm_exp_I_sub_le (theta Γ.T u) (theta 0 u)
  have hstep1 : ‖((P Γ.T - P 0 : ℝ) : ℂ) * Complex.exp (Complex.I * (theta Γ.T u : ℂ))‖
      ≤ khat * P1 * cost Γ := by
    rw [norm_mul, he1, mul_one, Complex.norm_real, Real.norm_eq_abs]
    exact hP
  have hstep2 : ‖(P 0 : ℂ) * (Complex.exp (Complex.I * (theta Γ.T u : ℂ))
      - Complex.exp (Complex.I * (theta 0 u : ℂ)))‖ ≤ P1 * ((1 / P0) * cost Γ) := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hPu 0)]
    have h1 : ‖Complex.exp (Complex.I * (theta Γ.T u : ℂ))
        - Complex.exp (Complex.I * (theta 0 u : ℂ))‖ ≤ (1 / P0) * cost Γ :=
      le_trans hexp hth
    exact mul_le_mul (hPub 0) h1 (norm_nonneg _) (le_trans (hPu 0) (hPub 0))
  calc ‖((P Γ.T - P 0 : ℝ) : ℂ) * Complex.exp (Complex.I * (theta Γ.T u : ℂ))
        + (P 0 : ℂ) * (Complex.exp (Complex.I * (theta Γ.T u : ℂ))
            - Complex.exp (Complex.I * (theta 0 u : ℂ)))‖
      ≤ khat * P1 * cost Γ + P1 * ((1 / P0) * cost Γ) :=
        le_trans (norm_add_le _ _) (add_le_add hstep1 hstep2)
    _ = velConst P0 P1 khat * cost Γ := by rw [velConst]; ring

/-- **The acceleration increment of a normal path.** -/
theorem norm_acc_sub_le {c kmin dlt cq kminq dltq : ℝ} (Γ : NormalPath p q)
    (hp : IsTubeMember c kmin dlt p) (hq : IsTubeMember cq kminq dltq q)
    (hXu : ∀ t u, HasDerivAt (Γ.X t)
      ((P t : ℂ) * Complex.exp (Complex.I * (theta t u : ℂ))) u)
    (hthetau : ∀ t u, HasDerivAt (theta t) (P t * kappa t u) u)
    (hPd : ∀ t, HasDerivAt P (Pd t) t) (hPdc : Continuous Pd)
    (hPdbd : ∀ t, |Pd t| ≤ khat * P1 * Γ.m t)
    (hthetat : ∀ t u, HasDerivAt (fun r => theta r u) (etas t u) t)
    (hetasc : ∀ u, Continuous fun t => etas t u)
    (hetas : ∀ t u, |etas t u| ≤ (1 / P0) * Γ.m t)
    (hkappat : ∀ t u, HasDerivAt (fun r => kappa r u) (kt t u) t)
    (hktc : ∀ u, Continuous fun t => kt t u)
    (hkt : ∀ t u, |kt t u| ≤ (1 / P0 ^ 2 + khat ^ 2) * Γ.m t)
    (hkap : ∀ t u, |kappa t u| ≤ khat)
    (hPu : ∀ t, 0 ≤ P t) (hPub : ∀ t, P t ≤ P1) (u : ℝ) :
    ‖q.2.2 u - p.2.2 u‖ ≤ accConst P0 P1 khat * cost Γ := by
  have hcost : 0 ≤ cost Γ := Γ.cost_nonneg
  have hap := acc_eq_of_slice (P := P) (theta := theta) (kappa := kappa) Γ 0 hp
    (funext Γ.start) (hXu 0) (hthetau 0) u
  have haq := acc_eq_of_slice (P := P) (theta := theta) (kappa := kappa) Γ Γ.T hq
    (funext Γ.finish) (hXu Γ.T) (hthetau Γ.T) u
  rw [hap, haq]
  set a : ℝ := P Γ.T
  set b : ℝ := P 0
  set x : ℝ := kappa Γ.T u
  set y : ℝ := kappa 0 u
  have hsplit : Complex.I * ((a ^ 2 * x : ℝ) : ℂ) * Complex.exp (Complex.I * (theta Γ.T u : ℂ))
      - Complex.I * ((b ^ 2 * y : ℝ) : ℂ) * Complex.exp (Complex.I * (theta 0 u : ℂ))
      = Complex.I * ((a ^ 2 * x - b ^ 2 * y : ℝ) : ℂ)
          * Complex.exp (Complex.I * (theta Γ.T u : ℂ))
        + Complex.I * ((b ^ 2 * y : ℝ) : ℂ)
            * (Complex.exp (Complex.I * (theta Γ.T u : ℂ))
              - Complex.exp (Complex.I * (theta 0 u : ℂ))) := by
    push_cast; ring
  rw [hsplit]
  have he1 : ‖Complex.exp (Complex.I * (theta Γ.T u : ℂ))‖ = 1 := by
    rw [Complex.norm_exp]; simp
  have hP := abs_period_sub_le (P1 := P1) (khat := khat) Γ hPd hPdc hPdbd
  have hth := abs_angle_sub_le (P0 := P0) Γ hthetat hetasc hetas u
  have hK := abs_curv_sub_le (P0 := P0) (khat := khat) Γ hkappat hktc hkt u
  have hexp := norm_exp_I_sub_le (theta Γ.T u) (theta 0 u)
  have hkhat0 : 0 ≤ khat := le_trans (abs_nonneg _) (hkap 0 0)
  have hP1 : 0 ≤ P1 := le_trans (hPu 0) (hPub 0)
  -- the increment of `P²κ`
  have hprod : |a ^ 2 * x - b ^ 2 * y|
      ≤ P1 ^ 2 * ((1 / P0 ^ 2 + khat ^ 2) * cost Γ)
        + 2 * khat ^ 2 * P1 ^ 2 * cost Γ := by
    have hid : a ^ 2 * x - b ^ 2 * y = a ^ 2 * (x - y) + (a ^ 2 - b ^ 2) * y := by ring
    have h1 : |a ^ 2 * (x - y)| ≤ P1 ^ 2 * ((1 / P0 ^ 2 + khat ^ 2) * cost Γ) := by
      rw [abs_mul, abs_of_nonneg (sq_nonneg a)]
      have ha2 : a ^ 2 ≤ P1 ^ 2 := by nlinarith [hPu Γ.T, hPub Γ.T]
      have hxy : |x - y| ≤ (1 / P0 ^ 2 + khat ^ 2) * cost Γ := hK
      have hxy0 : (0:ℝ) ≤ (1 / P0 ^ 2 + khat ^ 2) * cost Γ := le_trans (abs_nonneg _) hK
      nlinarith [sq_nonneg a, abs_nonneg (x - y)]
    have h2 : |(a ^ 2 - b ^ 2) * y| ≤ 2 * khat ^ 2 * P1 ^ 2 * cost Γ := by
      rw [abs_mul]
      have hab : |a ^ 2 - b ^ 2| ≤ 2 * P1 * (khat * P1 * cost Γ) := by
        have hid2 : a ^ 2 - b ^ 2 = (a - b) * (a + b) := by ring
        rw [hid2, abs_mul]
        have h3 : |a + b| ≤ 2 * P1 := by
          rw [abs_of_nonneg (by linarith [hPu Γ.T, hPu 0] : (0:ℝ) ≤ a + b)]
          linarith [hPub Γ.T, hPub 0]
        have h4 : (0:ℝ) ≤ khat * P1 * cost Γ := le_trans (abs_nonneg _) hP
        nlinarith [abs_nonneg (a - b), abs_nonneg (a + b)]
      have hy : |y| ≤ khat := hkap 0 u
      have h5 : (0:ℝ) ≤ 2 * P1 * (khat * P1 * cost Γ) := by positivity
      nlinarith [abs_nonneg (a ^ 2 - b ^ 2), abs_nonneg y]
    calc |a ^ 2 * x - b ^ 2 * y| = |a ^ 2 * (x - y) + (a ^ 2 - b ^ 2) * y| := by rw [hid]
      _ ≤ |a ^ 2 * (x - y)| + |(a ^ 2 - b ^ 2) * y| := abs_add_le _ _
      _ ≤ _ := add_le_add h1 h2
  have hstep1 : ‖Complex.I * ((a ^ 2 * x - b ^ 2 * y : ℝ) : ℂ)
      * Complex.exp (Complex.I * (theta Γ.T u : ℂ))‖
      ≤ P1 ^ 2 * ((1 / P0 ^ 2 + khat ^ 2) * cost Γ) + 2 * khat ^ 2 * P1 ^ 2 * cost Γ := by
    rw [norm_mul, norm_mul, he1, mul_one, Complex.norm_I, one_mul, Complex.norm_real,
      Real.norm_eq_abs]
    exact hprod
  have hstep2 : ‖Complex.I * ((b ^ 2 * y : ℝ) : ℂ)
      * (Complex.exp (Complex.I * (theta Γ.T u : ℂ))
        - Complex.exp (Complex.I * (theta 0 u : ℂ)))‖
      ≤ khat * P1 ^ 2 * ((1 / P0) * cost Γ) := by
    rw [norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
    have hb : |b ^ 2 * y| ≤ P1 ^ 2 * khat := by
      rw [abs_mul, abs_of_nonneg (sq_nonneg b)]
      have hb2 : b ^ 2 ≤ P1 ^ 2 := by nlinarith [hPu 0, hPub 0]
      nlinarith [abs_nonneg y, hkap 0 u, sq_nonneg b]
    have hd : ‖Complex.exp (Complex.I * (theta Γ.T u : ℂ))
        - Complex.exp (Complex.I * (theta 0 u : ℂ))‖ ≤ (1 / P0) * cost Γ :=
      le_trans hexp hth
    have hd0 : (0:ℝ) ≤ (1 / P0) * cost Γ := le_trans (abs_nonneg _) hth
    have hb0 : (0:ℝ) ≤ P1 ^ 2 * khat := by positivity
    nlinarith [abs_nonneg (b ^ 2 * y), norm_nonneg (Complex.exp (Complex.I * (theta Γ.T u : ℂ))
      - Complex.exp (Complex.I * (theta 0 u : ℂ)))]
  calc ‖Complex.I * ((a ^ 2 * x - b ^ 2 * y : ℝ) : ℂ)
          * Complex.exp (Complex.I * (theta Γ.T u : ℂ))
        + Complex.I * ((b ^ 2 * y : ℝ) : ℂ)
            * (Complex.exp (Complex.I * (theta Γ.T u : ℂ))
              - Complex.exp (Complex.I * (theta 0 u : ℂ)))‖
      ≤ (P1 ^ 2 * ((1 / P0 ^ 2 + khat ^ 2) * cost Γ) + 2 * khat ^ 2 * P1 ^ 2 * cost Γ)
          + khat * P1 ^ 2 * ((1 / P0) * cost Γ) :=
        le_trans (norm_add_le _ _) (add_le_add hstep1 hstep2)
    _ = accConst P0 P1 khat * cost Γ := by rw [accConst]; ring

/-! ### The path in the form the completeness lemma consumes -/

/-- **A normal path with constant-speed slices, in the normal gauge.**  The
geometric data of the path: the arclength period `P` of the slices, their
tangent angle `θ` and their curvature `κ`, together with the normal-flow
identities of `NormalFlow.lean` in the form of bounds against the cost density
of the path — the speed equation `(log g)_t = −κη` for `P`, the tangent
equation `τ_t = η_s ν` for `θ` and the curvature equation `κ_t = η_ss + κ²η`
for `κ`.  The arclength derivatives `η_s = η_u/g`, `η_ss = η_uu/g²` of the
paper are dominated by the cost density divided by `P₀`, resp. `P₀²`, which is
where the two constants come from. -/
def IsConstantSpeedNormalPath (P0 P1 khat : ℝ) {p q : Data} (Γ : NormalPath p q) : Prop :=
  ∃ P Pd : ℝ → ℝ, ∃ theta kappa etas kt : ℝ → ℝ → ℝ,
    (∀ t, 0 ≤ P t) ∧ (∀ t, P t ≤ P1) ∧ (∀ t u, |kappa t u| ≤ khat) ∧
    (∀ t u, HasDerivAt (Γ.X t) ((P t : ℂ) * Complex.exp (Complex.I * (theta t u : ℂ))) u) ∧
    (∀ t u, HasDerivAt (theta t) (P t * kappa t u) u) ∧
    (∀ t, HasDerivAt P (Pd t) t) ∧ Continuous Pd ∧
    (∀ t, |Pd t| ≤ khat * P1 * Γ.m t) ∧
    (∀ t u, HasDerivAt (fun r => theta r u) (etas t u) t) ∧
    (∀ u, Continuous fun t => etas t u) ∧
    (∀ t u, |etas t u| ≤ (1 / P0) * Γ.m t) ∧
    (∀ t u, HasDerivAt (fun r => kappa r u) (kt t u) t) ∧
    (∀ u, Continuous fun t => kt t u) ∧
    (∀ t u, |kt t u| ≤ (1 / P0 ^ 2 + khat ^ 2) * Γ.m t)

/-- **The marked distance of the two ends of a normal path is at most its
cost**, up to the explicit constant `c2Const P₀ P₁ κ̂` of the tube data.  This
is the estimate the lemma *Completeness of summable normal paths* needs: it
turns summability of the costs into summability of the `C²` increments. -/
theorem dist_le_cost {c kmin dlt cq kminq dltq : ℝ} (Γ : NormalPath p q)
    (hp : IsTubeMember c kmin dlt p) (hq : IsTubeMember cq kminq dltq q)
    (hΓ : IsConstantSpeedNormalPath P0 P1 khat Γ) :
    dist p q ≤ c2Const P0 P1 khat * cost Γ := by
  obtain ⟨P, Pd, theta, kappa, etas, kt, hPu, hPub, hkap, hXu, hthetau, hPd, hPdc, hPdbd,
    hthetat, hetasc, hetas, hkappat, hktc, hkt⟩ := hΓ
  have hcost : 0 ≤ cost Γ := Γ.cost_nonneg
  have hc2 : 0 ≤ c2Const P0 P1 khat := c2Const_nonneg P0 P1 khat
  have hbound : 0 ≤ c2Const P0 P1 khat * cost Γ := mul_nonneg hc2 hcost
  have h1 : dist p.1 q.1 ≤ c2Const P0 P1 khat * cost Γ := by
    refine (BoundedContinuousFunction.dist_le hbound).2 fun u => ?_
    rw [dist_eq_norm, ← norm_neg]
    have h := Γ.norm_sub_le_cost u
    have : -(p.1 u - q.1 u) = q.1 u - p.1 u := by ring
    rw [this]
    calc ‖q.1 u - p.1 u‖ ≤ cost Γ := h
      _ ≤ c2Const P0 P1 khat * cost Γ := by nlinarith [one_le_c2Const P0 P1 khat]
  have h2 : dist p.2.1 q.2.1 ≤ c2Const P0 P1 khat * cost Γ := by
    refine (BoundedContinuousFunction.dist_le hbound).2 fun u => ?_
    rw [dist_eq_norm, ← norm_neg]
    have : -(p.2.1 u - q.2.1 u) = q.2.1 u - p.2.1 u := by ring
    rw [this]
    have h := norm_vel_sub_le (P := P) (Pd := Pd) (theta := theta) (etas := etas)
      (P0 := P0) (P1 := P1) (khat := khat) Γ hp hq hXu hPd hPdc hPdbd hthetat hetasc hetas
      hPu hPub u
    refine le_trans h (mul_le_mul_of_nonneg_right ?_ hcost)
    exact le_trans (le_max_left _ _) (le_max_right _ _)
  have h3 : dist p.2.2 q.2.2 ≤ c2Const P0 P1 khat * cost Γ := by
    refine (BoundedContinuousFunction.dist_le hbound).2 fun u => ?_
    rw [dist_eq_norm, ← norm_neg]
    have : -(p.2.2 u - q.2.2 u) = q.2.2 u - p.2.2 u := by ring
    rw [this]
    have h := norm_acc_sub_le (P := P) (Pd := Pd) (theta := theta) (kappa := kappa)
      (etas := etas) (kt := kt) (P0 := P0) (P1 := P1) (khat := khat) Γ hp hq hXu hthetau
      hPd hPdc hPdbd hthetat hetasc hetas hkappat hktc hkt hkap hPu hPub u
    refine le_trans h (mul_le_mul_of_nonneg_right ?_ hcost)
    exact le_trans (le_max_right _ _) (le_max_right _ _)
  rw [Prod.dist_eq, Prod.dist_eq]
  exact max_le h1 (max_le h2 h3)

end NormalPathC2Increment
