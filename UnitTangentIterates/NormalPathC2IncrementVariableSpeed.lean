import Mathlib
import UnitTangentIterates.NormalPathC2Increment

/-!
# The `C²` increment of a normal path whose slices are **not** constant-speed

`NormalPathC2Increment.dist_le_cost` bounds the marked distance of the two ends
of a normal path by its cost, but only for a path whose slices are constant-speed
closed curves (`IsConstantSpeedNormalPath`), and only for ends that are members
of the tube.  Both restrictions come from the same place: a member of the tube
*is* a constant-speed parametrization, and the velocity and the acceleration of
a slice were then read off as `V = P e^{iθ}` and `A = i P² κ e^{iθ}`.

The parametrizations produced by a gauge marking are normalized but not affine,
so their slices have a variable speed `g(t,u)` and are not members of the tube;
this is what stops the comparison of the two marked selected inverses from being
a `C²` one.  This file removes both restrictions.  For a family with

```
  ∂_u X = g e^{iθ} ,      ∂_u θ = g κ ,
```

the velocity and the acceleration of a slice are

```
  V = g e^{iθ} ,          A = (g_u + i g² κ) e^{iθ} ,
```

so the three increments of the marked datum are controlled by those of `g`,
`g_u`, `θ` and `κ`, each of which is integrated in time against the cost density
of the path exactly as in the constant-speed case.  The ends are no longer asked
to be members of the tube: only that their velocity and acceleration components
are the derivatives of their curve, which is what a marked datum means.

* `abs_speed_sub_le`, `abs_speedDeriv_sub_le` : the increments of the speed and
  of its parameter derivative;
* `vel_eq_of_slice`, `acc_eq_of_slice` : the frame of a slice of variable speed;
* `norm_vel_sub_le`, `norm_acc_sub_le` : the velocity and acceleration
  increments;
* `dist_le_cost_variableSpeed` : **the marked distance of the two ends is at
  most `c2ConstVar P₀ P₁ κ̂ G₁ C_g · cost Γ`**.

With `g t u = P t` (so `g_u = 0`, and `G₁ = C_g = 0`) the constant reduces to the
constant `c2Const` of the constant-speed case (`accConstVar_zero_zero`).
-/

noncomputable section

open Set Function Complex MeasureTheory
open MarkedSpace PathMetric PathMetric.NormalPath

namespace NormalPathC2IncrementVariableSpeed

open NormalPathC2Increment

variable {p q : Data} {g gu gt gut theta kappa etas kt : ℝ → ℝ → ℝ}
  {P0 P1 khat G1 Cg : ℝ}

/-! ### The increments of the speed and of its parameter derivative -/

/-- **The increment of the speed.**  The speed equation `(log g)_t = −κη`
bounds the change of the speed of a slice by `κ̂ P₁ · cost Γ`. -/
theorem abs_speed_sub_le (Γ : NormalPath p q)
    (hgt : ∀ t u, HasDerivAt (fun r => g r u) (gt t u) t)
    (hgtc : ∀ u, Continuous fun t => gt t u)
    (hgtbd : ∀ t u, |gt t u| ≤ khat * P1 * Γ.m t) (u : ℝ) :
    |g Γ.T u - g 0 u| ≤ khat * P1 * cost Γ :=
  abs_sub_le_of_deriv_le Γ.T_pos.le (fun t => hgt t u) (hgtc u) Γ.cont_m
    (fun t => hgtbd t u)

/-- **The increment of the parameter derivative of the speed**, from a bound
`C_g · m` for its time derivative. -/
theorem abs_speedDeriv_sub_le (Γ : NormalPath p q)
    (hgut : ∀ t u, HasDerivAt (fun r => gu r u) (gut t u) t)
    (hgutc : ∀ u, Continuous fun t => gut t u)
    (hgutbd : ∀ t u, |gut t u| ≤ Cg * Γ.m t) (u : ℝ) :
    |gu Γ.T u - gu 0 u| ≤ Cg * cost Γ :=
  abs_sub_le_of_deriv_le Γ.T_pos.le (fun t => hgut t u) (hgutc u) Γ.cont_m
    (fun t => hgutbd t u)

/-! ### The frame of a slice of variable speed -/

/-- The velocity of a slice of a normal path whose slices have speed `g` and
tangent angle `θ`: `V = g e^{iθ}`. -/
theorem vel_eq_of_slice (Γ : NormalPath p q) (t : ℝ) {r : Data}
    (hrd : ∀ u, HasDerivAt (⇑r.1) (r.2.1 u) u) (hXr : Γ.X t = ⇑r.1)
    (hXu : ∀ u, HasDerivAt (Γ.X t) ((g t u : ℂ) * Complex.exp (Complex.I * (theta t u : ℂ))) u)
    (u : ℝ) :
    r.2.1 u = (g t u : ℂ) * Complex.exp (Complex.I * (theta t u : ℂ)) := by
  have h1 : HasDerivAt (⇑r.1) ((g t u : ℂ) * Complex.exp (Complex.I * (theta t u : ℂ))) u := by
    rw [← hXr]; exact hXu u
  exact (hrd u).unique h1

/-- The acceleration of a slice of a normal path whose slices have speed `g`,
tangent angle `θ` and curvature `κ`: `A = (g_u + i g² κ) e^{iθ}`. -/
theorem acc_eq_of_slice (Γ : NormalPath p q) (t : ℝ) {r : Data}
    (hrd : ∀ u, HasDerivAt (⇑r.1) (r.2.1 u) u) (hrv : ∀ u, HasDerivAt (⇑r.2.1) (r.2.2 u) u)
    (hXr : Γ.X t = ⇑r.1)
    (hXu : ∀ u, HasDerivAt (Γ.X t) ((g t u : ℂ) * Complex.exp (Complex.I * (theta t u : ℂ))) u)
    (hgu : ∀ u, HasDerivAt (g t) (gu t u) u)
    (hthetau : ∀ u, HasDerivAt (theta t) (g t u * kappa t u) u) (u : ℝ) :
    r.2.2 u
      = ((gu t u : ℂ) + Complex.I * ((g t u ^ 2 * kappa t u : ℝ) : ℂ))
          * Complex.exp (Complex.I * (theta t u : ℂ)) := by
  have hveq : ⇑r.2.1 = fun v => (g t v : ℂ) * Complex.exp (Complex.I * (theta t v : ℂ)) :=
    funext fun v => vel_eq_of_slice (g := g) (theta := theta) Γ t hrd hXr hXu v
  have hexp : HasDerivAt (fun v => Complex.exp (Complex.I * (theta t v : ℂ)))
      (Complex.I * ((g t u * kappa t u : ℝ) : ℂ)
        * Complex.exp (Complex.I * (theta t u : ℂ))) u := by
    have h1 : HasDerivAt (fun v => Complex.I * ((theta t v : ℝ) : ℂ))
        (Complex.I * ((g t u * kappa t u : ℝ) : ℂ)) u :=
      (Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt u (hthetau u)).const_mul Complex.I
    simpa [mul_comm] using h1.cexp
  have hgc : HasDerivAt (fun v => ((g t v : ℝ) : ℂ)) ((gu t u : ℂ)) u :=
    Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt u (hgu u)
  have h2 : HasDerivAt (⇑r.2.1)
      (((gu t u : ℂ) + Complex.I * ((g t u ^ 2 * kappa t u : ℝ) : ℂ))
        * Complex.exp (Complex.I * (theta t u : ℂ))) u := by
    rw [hveq]
    have := hgc.mul hexp
    convert this using 1
    push_cast
    ring
  exact (hrv u).unique h2

/-! ### The constants -/

/-- The constant of the acceleration increment for slices of variable speed:
the increment of `g_u`, the increment of `g²κ`, and the rotation of the frame
weighted by the size `G₁ + P₁²κ̂` of the acceleration at the initial time. -/
def accConstVar (P0 P1 khat G1 Cg : ℝ) : ℝ :=
  Cg + (P1 ^ 2 * (1 / P0 ^ 2 + khat ^ 2) + 2 * khat ^ 2 * P1 ^ 2)
    + (G1 + P1 ^ 2 * khat) * (1 / P0)

/-- The constant of the marked distance of the two ends of a normal path with
slices of variable speed. -/
def c2ConstVar (P0 P1 khat G1 Cg : ℝ) : ℝ :=
  max 1 (max (velConst P0 P1 khat) (accConstVar P0 P1 khat G1 Cg))

theorem one_le_c2ConstVar (P0 P1 khat G1 Cg : ℝ) : 1 ≤ c2ConstVar P0 P1 khat G1 Cg :=
  le_max_left _ _

theorem c2ConstVar_nonneg (P0 P1 khat G1 Cg : ℝ) : 0 ≤ c2ConstVar P0 P1 khat G1 Cg :=
  le_trans zero_le_one (one_le_c2ConstVar P0 P1 khat G1 Cg)

/-- With constant-speed slices (`g_u = 0`, so `G₁ = C_g = 0`) the constant is
the constant `accConst` of `NormalPathC2Increment`. -/
theorem accConstVar_zero_zero (P0 P1 khat : ℝ) :
    accConstVar P0 P1 khat 0 0 = accConst P0 P1 khat := by
  rw [accConstVar, accConst]; ring

theorem c2ConstVar_zero_zero (P0 P1 khat : ℝ) :
    c2ConstVar P0 P1 khat 0 0 = c2Const P0 P1 khat := by
  rw [c2ConstVar, c2Const, accConstVar_zero_zero]

/-! ### The two increments and the marked distance -/

/-- **The velocity increment of a normal path with slices of variable speed.**
The constant is the same as in the constant-speed case. -/
theorem norm_vel_sub_le (Γ : NormalPath p q)
    (hpd : ∀ u, HasDerivAt (⇑p.1) (p.2.1 u) u) (hqd : ∀ u, HasDerivAt (⇑q.1) (q.2.1 u) u)
    (hXu : ∀ t u, HasDerivAt (Γ.X t)
      ((g t u : ℂ) * Complex.exp (Complex.I * (theta t u : ℂ))) u)
    (hgt : ∀ t u, HasDerivAt (fun r => g r u) (gt t u) t)
    (hgtc : ∀ u, Continuous fun t => gt t u)
    (hgtbd : ∀ t u, |gt t u| ≤ khat * P1 * Γ.m t)
    (hthetat : ∀ t u, HasDerivAt (fun r => theta r u) (etas t u) t)
    (hetasc : ∀ u, Continuous fun t => etas t u)
    (hetas : ∀ t u, |etas t u| ≤ (1 / P0) * Γ.m t)
    (hgnn : ∀ t u, 0 ≤ g t u) (hgub : ∀ t u, g t u ≤ P1) (u : ℝ) :
    ‖q.2.1 u - p.2.1 u‖ ≤ velConst P0 P1 khat * cost Γ := by
  have hcost : 0 ≤ cost Γ := Γ.cost_nonneg
  have hvp := vel_eq_of_slice (g := g) (theta := theta) Γ 0 hpd (funext Γ.start) (hXu 0) u
  have hvq := vel_eq_of_slice (g := g) (theta := theta) Γ Γ.T hqd (funext Γ.finish) (hXu Γ.T) u
  rw [hvp, hvq]
  have hsplit : (g Γ.T u : ℂ) * Complex.exp (Complex.I * (theta Γ.T u : ℂ))
      - (g 0 u : ℂ) * Complex.exp (Complex.I * (theta 0 u : ℂ))
      = ((g Γ.T u - g 0 u : ℝ) : ℂ) * Complex.exp (Complex.I * (theta Γ.T u : ℂ))
        + (g 0 u : ℂ) * (Complex.exp (Complex.I * (theta Γ.T u : ℂ))
            - Complex.exp (Complex.I * (theta 0 u : ℂ))) := by
    push_cast; ring
  rw [hsplit]
  have he1 : ‖Complex.exp (Complex.I * (theta Γ.T u : ℂ))‖ = 1 := by
    rw [Complex.norm_exp]; simp
  have hgi := abs_speed_sub_le (g := g) (gt := gt) (P1 := P1) (khat := khat) Γ hgt hgtc hgtbd u
  have hth := abs_angle_sub_le (P0 := P0) Γ hthetat hetasc hetas u
  have hexp := norm_exp_I_sub_le (theta Γ.T u) (theta 0 u)
  have hstep1 : ‖((g Γ.T u - g 0 u : ℝ) : ℂ) * Complex.exp (Complex.I * (theta Γ.T u : ℂ))‖
      ≤ khat * P1 * cost Γ := by
    rw [norm_mul, he1, mul_one, Complex.norm_real, Real.norm_eq_abs]
    exact hgi
  have hstep2 : ‖(g 0 u : ℂ) * (Complex.exp (Complex.I * (theta Γ.T u : ℂ))
      - Complex.exp (Complex.I * (theta 0 u : ℂ)))‖ ≤ P1 * ((1 / P0) * cost Γ) := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hgnn 0 u)]
    have h1 : ‖Complex.exp (Complex.I * (theta Γ.T u : ℂ))
        - Complex.exp (Complex.I * (theta 0 u : ℂ))‖ ≤ (1 / P0) * cost Γ :=
      le_trans hexp hth
    exact mul_le_mul (hgub 0 u) h1 (norm_nonneg _) (le_trans (hgnn 0 u) (hgub 0 u))
  calc ‖((g Γ.T u - g 0 u : ℝ) : ℂ) * Complex.exp (Complex.I * (theta Γ.T u : ℂ))
        + (g 0 u : ℂ) * (Complex.exp (Complex.I * (theta Γ.T u : ℂ))
            - Complex.exp (Complex.I * (theta 0 u : ℂ)))‖
      ≤ khat * P1 * cost Γ + P1 * ((1 / P0) * cost Γ) :=
        le_trans (norm_add_le _ _) (add_le_add hstep1 hstep2)
    _ = velConst P0 P1 khat * cost Γ := by rw [velConst]; ring

/-- **The acceleration increment of a normal path with slices of variable
speed.** -/
theorem norm_acc_sub_le (Γ : NormalPath p q)
    (hpd : ∀ u, HasDerivAt (⇑p.1) (p.2.1 u) u) (hqd : ∀ u, HasDerivAt (⇑q.1) (q.2.1 u) u)
    (hpv : ∀ u, HasDerivAt (⇑p.2.1) (p.2.2 u) u) (hqv : ∀ u, HasDerivAt (⇑q.2.1) (q.2.2 u) u)
    (hXu : ∀ t u, HasDerivAt (Γ.X t)
      ((g t u : ℂ) * Complex.exp (Complex.I * (theta t u : ℂ))) u)
    (hgu : ∀ t u, HasDerivAt (g t) (gu t u) u)
    (hthetau : ∀ t u, HasDerivAt (theta t) (g t u * kappa t u) u)
    (hgt : ∀ t u, HasDerivAt (fun r => g r u) (gt t u) t)
    (hgtc : ∀ u, Continuous fun t => gt t u)
    (hgtbd : ∀ t u, |gt t u| ≤ khat * P1 * Γ.m t)
    (hgut : ∀ t u, HasDerivAt (fun r => gu r u) (gut t u) t)
    (hgutc : ∀ u, Continuous fun t => gut t u)
    (hgutbd : ∀ t u, |gut t u| ≤ Cg * Γ.m t)
    (hthetat : ∀ t u, HasDerivAt (fun r => theta r u) (etas t u) t)
    (hetasc : ∀ u, Continuous fun t => etas t u)
    (hetas : ∀ t u, |etas t u| ≤ (1 / P0) * Γ.m t)
    (hkappat : ∀ t u, HasDerivAt (fun r => kappa r u) (kt t u) t)
    (hktc : ∀ u, Continuous fun t => kt t u)
    (hkt : ∀ t u, |kt t u| ≤ (1 / P0 ^ 2 + khat ^ 2) * Γ.m t)
    (hkap : ∀ t u, |kappa t u| ≤ khat)
    (hgnn : ∀ t u, 0 ≤ g t u) (hgub : ∀ t u, g t u ≤ P1)
    (hguB : ∀ t u, |gu t u| ≤ G1) (u : ℝ) :
    ‖q.2.2 u - p.2.2 u‖ ≤ accConstVar P0 P1 khat G1 Cg * cost Γ := by
  have hcost : 0 ≤ cost Γ := Γ.cost_nonneg
  have hap := acc_eq_of_slice (g := g) (gu := gu) (theta := theta) (kappa := kappa) Γ 0
    hpd hpv (funext Γ.start) (hXu 0) (hgu 0) (hthetau 0) u
  have haq := acc_eq_of_slice (g := g) (gu := gu) (theta := theta) (kappa := kappa) Γ Γ.T
    hqd hqv (funext Γ.finish) (hXu Γ.T) (hgu Γ.T) (hthetau Γ.T) u
  rw [hap, haq]
  set a : ℝ := g Γ.T u with ha
  set b : ℝ := g 0 u with hb
  set x : ℝ := kappa Γ.T u with hx
  set y : ℝ := kappa 0 u with hy
  set e : ℝ := gu Γ.T u with he
  set f : ℝ := gu 0 u with hf
  have hsplit : ((e : ℂ) + Complex.I * ((a ^ 2 * x : ℝ) : ℂ))
        * Complex.exp (Complex.I * (theta Γ.T u : ℂ))
      - ((f : ℂ) + Complex.I * ((b ^ 2 * y : ℝ) : ℂ))
        * Complex.exp (Complex.I * (theta 0 u : ℂ))
      = (((e - f : ℝ) : ℂ) + Complex.I * ((a ^ 2 * x - b ^ 2 * y : ℝ) : ℂ))
          * Complex.exp (Complex.I * (theta Γ.T u : ℂ))
        + ((f : ℂ) + Complex.I * ((b ^ 2 * y : ℝ) : ℂ))
            * (Complex.exp (Complex.I * (theta Γ.T u : ℂ))
              - Complex.exp (Complex.I * (theta 0 u : ℂ))) := by
    push_cast; ring
  rw [hsplit]
  have he1 : ‖Complex.exp (Complex.I * (theta Γ.T u : ℂ))‖ = 1 := by
    rw [Complex.norm_exp]; simp
  have hgi := abs_speed_sub_le (g := g) (gt := gt) (P1 := P1) (khat := khat) Γ hgt hgtc hgtbd u
  have hgui := abs_speedDeriv_sub_le (gu := gu) (gut := gut) (Cg := Cg) Γ hgut hgutc hgutbd u
  have hth := abs_angle_sub_le (P0 := P0) Γ hthetat hetasc hetas u
  have hK := abs_curv_sub_le (P0 := P0) (khat := khat) Γ hkappat hktc hkt u
  have hexp := norm_exp_I_sub_le (theta Γ.T u) (theta 0 u)
  have hkhat0 : 0 ≤ khat := le_trans (abs_nonneg _) (hkap 0 0)
  have hP1 : 0 ≤ P1 := le_trans (hgnn 0 u) (hgub 0 u)
  have hG1 : 0 ≤ G1 := le_trans (abs_nonneg _) (hguB 0 u)
  -- the increment of `g²κ`
  have hprod : |a ^ 2 * x - b ^ 2 * y|
      ≤ P1 ^ 2 * ((1 / P0 ^ 2 + khat ^ 2) * cost Γ)
        + 2 * khat ^ 2 * P1 ^ 2 * cost Γ := by
    have hid : a ^ 2 * x - b ^ 2 * y = a ^ 2 * (x - y) + (a ^ 2 - b ^ 2) * y := by ring
    have h1 : |a ^ 2 * (x - y)| ≤ P1 ^ 2 * ((1 / P0 ^ 2 + khat ^ 2) * cost Γ) := by
      rw [abs_mul, abs_of_nonneg (sq_nonneg a)]
      have ha2 : a ^ 2 ≤ P1 ^ 2 := by nlinarith [hgnn Γ.T u, hgub Γ.T u]
      have hxy0 : (0:ℝ) ≤ (1 / P0 ^ 2 + khat ^ 2) * cost Γ := le_trans (abs_nonneg _) hK
      nlinarith [sq_nonneg a, abs_nonneg (x - y)]
    have h2 : |(a ^ 2 - b ^ 2) * y| ≤ 2 * khat ^ 2 * P1 ^ 2 * cost Γ := by
      rw [abs_mul]
      have hab : |a ^ 2 - b ^ 2| ≤ 2 * P1 * (khat * P1 * cost Γ) := by
        have hid2 : a ^ 2 - b ^ 2 = (a - b) * (a + b) := by ring
        rw [hid2, abs_mul]
        have h3 : |a + b| ≤ 2 * P1 := by
          rw [abs_of_nonneg (by linarith [hgnn Γ.T u, hgnn 0 u] : (0:ℝ) ≤ a + b)]
          linarith [hgub Γ.T u, hgub 0 u]
        have h4 : (0:ℝ) ≤ khat * P1 * cost Γ := le_trans (abs_nonneg _) hgi
        nlinarith [abs_nonneg (a - b), abs_nonneg (a + b)]
      have hyb : |y| ≤ khat := hkap 0 u
      have h5 : (0:ℝ) ≤ 2 * P1 * (khat * P1 * cost Γ) := by positivity
      nlinarith [abs_nonneg (a ^ 2 - b ^ 2), abs_nonneg y]
    calc |a ^ 2 * x - b ^ 2 * y| = |a ^ 2 * (x - y) + (a ^ 2 - b ^ 2) * y| := by rw [hid]
      _ ≤ |a ^ 2 * (x - y)| + |(a ^ 2 - b ^ 2) * y| := abs_add_le _ _
      _ ≤ _ := add_le_add h1 h2
  have hstep1 : ‖(((e - f : ℝ) : ℂ) + Complex.I * ((a ^ 2 * x - b ^ 2 * y : ℝ) : ℂ))
      * Complex.exp (Complex.I * (theta Γ.T u : ℂ))‖
      ≤ Cg * cost Γ
        + (P1 ^ 2 * ((1 / P0 ^ 2 + khat ^ 2) * cost Γ) + 2 * khat ^ 2 * P1 ^ 2 * cost Γ) := by
    rw [norm_mul, he1, mul_one]
    refine le_trans (norm_add_le _ _) (add_le_add ?_ ?_)
    · rw [Complex.norm_real, Real.norm_eq_abs]
      exact hgui
    · rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
      exact hprod
  have hstep2 : ‖((f : ℂ) + Complex.I * ((b ^ 2 * y : ℝ) : ℂ))
      * (Complex.exp (Complex.I * (theta Γ.T u : ℂ))
        - Complex.exp (Complex.I * (theta 0 u : ℂ)))‖
      ≤ (G1 + P1 ^ 2 * khat) * ((1 / P0) * cost Γ) := by
    rw [norm_mul]
    have hb1 : ‖(f : ℂ) + Complex.I * ((b ^ 2 * y : ℝ) : ℂ)‖ ≤ G1 + P1 ^ 2 * khat := by
      refine le_trans (norm_add_le _ _) (add_le_add ?_ ?_)
      · rw [Complex.norm_real, Real.norm_eq_abs]
        exact hguB 0 u
      · rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul,
          abs_of_nonneg (sq_nonneg b)]
        have hb2 : b ^ 2 ≤ P1 ^ 2 := by nlinarith [hgnn 0 u, hgub 0 u]
        nlinarith [abs_nonneg y, hkap 0 u, sq_nonneg b]
    have hd : ‖Complex.exp (Complex.I * (theta Γ.T u : ℂ))
        - Complex.exp (Complex.I * (theta 0 u : ℂ))‖ ≤ (1 / P0) * cost Γ :=
      le_trans hexp hth
    have hd0 : (0:ℝ) ≤ (1 / P0) * cost Γ := le_trans (abs_nonneg _) hth
    have hb0 : (0:ℝ) ≤ G1 + P1 ^ 2 * khat := by positivity
    exact mul_le_mul hb1 hd (norm_nonneg _) hb0
  calc ‖(((e - f : ℝ) : ℂ) + Complex.I * ((a ^ 2 * x - b ^ 2 * y : ℝ) : ℂ))
          * Complex.exp (Complex.I * (theta Γ.T u : ℂ))
        + ((f : ℂ) + Complex.I * ((b ^ 2 * y : ℝ) : ℂ))
            * (Complex.exp (Complex.I * (theta Γ.T u : ℂ))
              - Complex.exp (Complex.I * (theta 0 u : ℂ)))‖
      ≤ (Cg * cost Γ
            + (P1 ^ 2 * ((1 / P0 ^ 2 + khat ^ 2) * cost Γ) + 2 * khat ^ 2 * P1 ^ 2 * cost Γ))
          + (G1 + P1 ^ 2 * khat) * ((1 / P0) * cost Γ) :=
        le_trans (norm_add_le _ _) (add_le_add hstep1 hstep2)
    _ = accConstVar P0 P1 khat G1 Cg * cost Γ := by rw [accConstVar]; ring

/-- **The geometric data of a family of closed curves of variable speed moving
in normal gauge**, against a cost density `m`: the speed `g` of the slices with
its parameter derivative `g_u`, their tangent angle `θ` and their curvature `κ`,
together with the normal-flow identities in the form of bounds against `m`. -/
def IsVariableSpeedFamily (P0 P1 khat G1 Cg : ℝ) (X : ℝ → ℝ → ℂ) (m : ℝ → ℝ) : Prop :=
  ∃ g gu gt gut theta kappa etas kt : ℝ → ℝ → ℝ,
    (∀ t u, 0 ≤ g t u) ∧ (∀ t u, g t u ≤ P1) ∧ (∀ t u, |gu t u| ≤ G1) ∧
    (∀ t u, |kappa t u| ≤ khat) ∧
    (∀ t u, HasDerivAt (X t) ((g t u : ℂ) * Complex.exp (Complex.I * (theta t u : ℂ))) u) ∧
    (∀ t u, HasDerivAt (g t) (gu t u) u) ∧
    (∀ t u, HasDerivAt (theta t) (g t u * kappa t u) u) ∧
    (∀ t u, HasDerivAt (fun r => g r u) (gt t u) t) ∧
    (∀ u, Continuous fun t => gt t u) ∧ (∀ t u, |gt t u| ≤ khat * P1 * m t) ∧
    (∀ t u, HasDerivAt (fun r => gu r u) (gut t u) t) ∧
    (∀ u, Continuous fun t => gut t u) ∧ (∀ t u, |gut t u| ≤ Cg * m t) ∧
    (∀ t u, HasDerivAt (fun r => theta r u) (etas t u) t) ∧
    (∀ u, Continuous fun t => etas t u) ∧ (∀ t u, |etas t u| ≤ (1 / P0) * m t) ∧
    (∀ t u, HasDerivAt (fun r => kappa r u) (kt t u) t) ∧
    (∀ u, Continuous fun t => kt t u) ∧
    (∀ t u, |kt t u| ≤ (1 / P0 ^ 2 + khat ^ 2) * m t)

/-- **A normal path whose slices are closed curves of variable speed**: its
moving curve is such a family, against its own cost density. -/
def IsVariableSpeedNormalPath (P0 P1 khat G1 Cg : ℝ) {p q : Data} (Γ : NormalPath p q) : Prop :=
  IsVariableSpeedFamily P0 P1 khat G1 Cg Γ.X Γ.m

/-- Enlarging the speed, speed-derivative, and mixed-derivative ceilings
preserves a variable-speed certificate. -/
theorem IsVariableSpeedNormalPath.mono
    {P1 P1' G1 G1' Cg Cg' : ℝ} (Γ : NormalPath p q)
    (h : IsVariableSpeedNormalPath P0 P1 khat G1 Cg Γ)
    (hk : 0 ≤ khat) (hP1 : P1 ≤ P1') (hG1 : G1 ≤ G1')
    (hCg : Cg ≤ Cg') :
    IsVariableSpeedNormalPath P0 P1' khat G1' Cg' Γ := by
  obtain ⟨g, gu, gt, gut, theta, kappa, etas, kt, hgnn, hgub, hguB, hkap,
    hXu, hgud, hthetau, hgt, hgtc, hgtbd, hgut, hgutc, hgutbd,
    hthetat, hetasc, hetas, hkappat, hktc, hkt⟩ := h
  refine ⟨g, gu, gt, gut, theta, kappa, etas, kt, hgnn,
    (fun t u => (hgub t u).trans hP1),
    (fun t u => (hguB t u).trans hG1), hkap, hXu, hgud, hthetau,
    hgt, hgtc, ?_, hgut, hgutc, ?_, hthetat, hetasc, hetas,
    hkappat, hktc, hkt⟩
  · intro t u
    exact (hgtbd t u).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hP1 hk) (Γ.m_nonneg t))
  · intro t u
    exact (hgutbd t u).trans
      (mul_le_mul_of_nonneg_right hCg (Γ.m_nonneg t))

/-- **The marked distance of the two ends of a normal path with slices of
variable speed is at most its cost**, up to the explicit constant
`c2ConstVar P₀ P₁ κ̂ G₁ C_g`.  Neither end has to be a member of the tube: only
that its velocity and acceleration components are the derivatives of its curve,
which is what makes it a marked datum.  This is the estimate the comparison of
the two marked selected inverses needs at the terminal end, where the curve is
read in a gauge marking and so is not carried in a constant-speed parameter. -/
theorem dist_le_cost_variableSpeed (Γ : NormalPath p q)
    (hpd : ∀ u, HasDerivAt (⇑p.1) (p.2.1 u) u) (hqd : ∀ u, HasDerivAt (⇑q.1) (q.2.1 u) u)
    (hpv : ∀ u, HasDerivAt (⇑p.2.1) (p.2.2 u) u) (hqv : ∀ u, HasDerivAt (⇑q.2.1) (q.2.2 u) u)
    (hΓ : IsVariableSpeedNormalPath P0 P1 khat G1 Cg Γ) :
    dist p q ≤ c2ConstVar P0 P1 khat G1 Cg * cost Γ := by
  obtain ⟨g, gu, gt, gut, theta, kappa, etas, kt, hgnn, hgub, hguB, hkap, hXu, hgud, hthetau,
    hgt, hgtc, hgtbd, hgut, hgutc, hgutbd, hthetat, hetasc, hetas, hkappat, hktc, hkt⟩ := hΓ
  have hcost : 0 ≤ cost Γ := Γ.cost_nonneg
  have hc2 : 0 ≤ c2ConstVar P0 P1 khat G1 Cg := c2ConstVar_nonneg P0 P1 khat G1 Cg
  have hbound : 0 ≤ c2ConstVar P0 P1 khat G1 Cg * cost Γ := mul_nonneg hc2 hcost
  have h1 : dist p.1 q.1 ≤ c2ConstVar P0 P1 khat G1 Cg * cost Γ := by
    refine (BoundedContinuousFunction.dist_le hbound).2 fun u => ?_
    rw [dist_eq_norm, ← norm_neg]
    have h := Γ.norm_sub_le_cost u
    have hneg : -(p.1 u - q.1 u) = q.1 u - p.1 u := by ring
    rw [hneg]
    calc ‖q.1 u - p.1 u‖ ≤ cost Γ := h
      _ ≤ c2ConstVar P0 P1 khat G1 Cg * cost Γ := by
          nlinarith [one_le_c2ConstVar P0 P1 khat G1 Cg]
  have h2 : dist p.2.1 q.2.1 ≤ c2ConstVar P0 P1 khat G1 Cg * cost Γ := by
    refine (BoundedContinuousFunction.dist_le hbound).2 fun u => ?_
    rw [dist_eq_norm, ← norm_neg]
    have hneg : -(p.2.1 u - q.2.1 u) = q.2.1 u - p.2.1 u := by ring
    rw [hneg]
    have h := norm_vel_sub_le (g := g) (gt := gt) (theta := theta) (etas := etas)
      (P0 := P0) (P1 := P1) (khat := khat) Γ hpd hqd hXu hgt hgtc hgtbd hthetat hetasc hetas
      hgnn hgub u
    refine le_trans h (mul_le_mul_of_nonneg_right ?_ hcost)
    exact le_trans (le_max_left _ _) (le_max_right _ _)
  have h3 : dist p.2.2 q.2.2 ≤ c2ConstVar P0 P1 khat G1 Cg * cost Γ := by
    refine (BoundedContinuousFunction.dist_le hbound).2 fun u => ?_
    rw [dist_eq_norm, ← norm_neg]
    have hneg : -(p.2.2 u - q.2.2 u) = q.2.2 u - p.2.2 u := by ring
    rw [hneg]
    have h := norm_acc_sub_le (g := g) (gu := gu) (gt := gt) (gut := gut) (theta := theta)
      (kappa := kappa) (etas := etas) (kt := kt) (P0 := P0) (P1 := P1) (khat := khat)
      (G1 := G1) (Cg := Cg) Γ hpd hqd hpv hqv hXu hgud hthetau hgt hgtc hgtbd hgut hgutc
      hgutbd hthetat hetasc hetas hkappat hktc hkt hkap hgnn hgub hguB u
    refine le_trans h (mul_le_mul_of_nonneg_right ?_ hcost)
    exact le_trans (le_max_right _ _) (le_max_right _ _)
  rw [Prod.dist_eq, Prod.dist_eq]
  exact max_le h1 (max_le h2 h3)

/-- **A path with constant-speed slices is one with variable-speed slices**,
with `g t u = P t`, `g_u = 0` and both extra constants `0`.  In particular the
hypothesis block of `dist_le_cost_variableSpeed` is satisfiable, and the
estimate contains the constant-speed one. -/
theorem isVariableSpeedNormalPath_of_constantSpeed {P0 P1 khat : ℝ} (Γ : NormalPath p q)
    (hΓ : NormalPathC2Increment.IsConstantSpeedNormalPath P0 P1 khat Γ) :
    IsVariableSpeedNormalPath P0 P1 khat 0 0 Γ := by
  obtain ⟨P, Pd, theta, kappa, etas, kt, hPu, hPub, hkap, hXu, hthetau, hPd, hPdc, hPdbd,
    hthetat, hetasc, hetas, hkappat, hktc, hkt⟩ := hΓ
  refine ⟨fun t _ => P t, fun _ _ => 0, fun t _ => Pd t, fun _ _ => 0, theta, kappa, etas, kt,
    fun t _ => hPu t, fun t _ => hPub t, fun _ _ => by norm_num, hkap, hXu,
    fun t u => hasDerivAt_const u (P t), hthetau, fun t _ => hPd t, fun _ => hPdc,
    fun t _ => hPdbd t, fun t u => hasDerivAt_const t (0 : ℝ), fun _ => continuous_const,
    fun t _ => ?_, hthetat, hetasc, hetas, hkappat, hktc, hkt⟩
  simp

/-- The constant-speed estimate `NormalPathC2Increment.dist_le_cost`, recovered
from the variable-speed one. -/
theorem dist_le_cost_of_constantSpeed {c kmin dlt cq kminq dltq : ℝ} (Γ : NormalPath p q)
    (hp : IsTubeMember c kmin dlt p) (hq : IsTubeMember cq kminq dltq q)
    (hΓ : NormalPathC2Increment.IsConstantSpeedNormalPath P0 P1 khat Γ) :
    dist p q ≤ c2Const P0 P1 khat * cost Γ := by
  rw [← c2ConstVar_zero_zero]
  exact dist_le_cost_variableSpeed Γ (fun u => hp.hasDerivAt_curve u)
    (fun u => hq.hasDerivAt_curve u) (fun u => hp.hasDerivAt_vel u)
    (fun u => hq.hasDerivAt_vel u) (isVariableSpeedNormalPath_of_constantSpeed Γ hΓ)

end NormalPathC2IncrementVariableSpeed
