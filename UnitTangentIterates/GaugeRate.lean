import Mathlib
import UnitTangentIterates.FlowDerivative

/-!
# The tangential rate of the normal gauge, as a field of the flow

The gauge flow of `NormalGaugeFamily.lean` is the flow of the **tangential
rate** `h(a,x) = −ξ(a,x)/v(a,x)`, where `v` is the speed of the slice and `ξ`
the tangential component of its velocity.  `FlowDerivative.lean` needs of that
field: joint continuity, a global Lipschitz constant in `x`, and two space
derivatives which are jointly continuous and bounded.

This file supplies them from bounds on the frame data.  Writing `w = 1/v`,

`h = −ξw`,  `∂ₓh = −(ξ₁w + ξw')`,  `∂ₓ²h = −(ξ₂w + 2ξ₁w' + ξw'')`,

with `w' = −v₁/v²` and `w'' = (2v₁² − v v₂)/v³`, so that with
`|ξ| ≤ A₀, |ξ₁| ≤ A₁, |ξ₂| ≤ A₂`, `v₀ ≤ |v| ≤ V₁`, `|v₁| ≤ B₁`, `|v₂| ≤ B₂`:

`|∂ₓh| ≤ A₁/v₀ + A₀B₁/v₀²`,
`|∂ₓ²h| ≤ A₂/v₀ + 2A₁B₁/v₀² + A₀(V₁B₂ + 2B₁²)/v₀³`.

Main results:

* `hasDerivAt_gaugeRate`, `hasDerivAt_gaugeRate1` — the two space derivatives;
* `abs_gaugeRate1_le`, `abs_gaugeRate2_le` — the two bounds;
* `lipschitzWith_gaugeRate` — the global Lipschitz constant in `x`;
* `gaugeRate_flow_hypotheses` — the whole bundle required by
  `FlowDerivative.lean`, collected.
-/

noncomputable section

open Set Function

namespace GaugeRate

variable {xi xi1 xi2 v v1 v2 : ℝ → ℝ → ℝ}

/-- The tangential rate `−ξ/v` of the normal gauge. -/
def gaugeRate (xi v : ℝ → ℝ → ℝ) (a x : ℝ) : ℝ := -(xi a x / v a x)

/-- Its derivative in the space variable. -/
def gaugeRate1 (xi xi1 v v1 : ℝ → ℝ → ℝ) (a x : ℝ) : ℝ :=
  -(xi1 a x / v a x) + xi a x * v1 a x / v a x ^ 2

/-- Its second derivative in the space variable. -/
def gaugeRate2 (xi xi1 xi2 v v1 v2 : ℝ → ℝ → ℝ) (a x : ℝ) : ℝ :=
  -(xi2 a x / v a x) + 2 * (xi1 a x * v1 a x) / v a x ^ 2
    + xi a x * (v a x * v2 a x - 2 * v1 a x ^ 2) / v a x ^ 3

/-! ### The two space derivatives -/

/-- The first space derivative of the tangential rate. -/
theorem hasDerivAt_gaugeRate (hxi : ∀ a x, HasDerivAt (xi a) (xi1 a x) x)
    (hv : ∀ a x, HasDerivAt (v a) (v1 a x) x) (hvne : ∀ a x, v a x ≠ 0) (a x : ℝ) :
    HasDerivAt (gaugeRate xi v a) (gaugeRate1 xi xi1 v v1 a x) x := by
  have hd := ((hxi a x).div (hv a x) (hvne a x)).neg
  refine hd.congr_deriv ?_
  rw [gaugeRate1]
  field_simp
  ring

/-- The second space derivative of the tangential rate. -/
theorem hasDerivAt_gaugeRate1 (hxi : ∀ a x, HasDerivAt (xi a) (xi1 a x) x)
    (hxi1 : ∀ a x, HasDerivAt (xi1 a) (xi2 a x) x)
    (hv : ∀ a x, HasDerivAt (v a) (v1 a x) x)
    (hv1 : ∀ a x, HasDerivAt (v1 a) (v2 a x) x)
    (hvne : ∀ a x, v a x ≠ 0) (a x : ℝ) :
    HasDerivAt (gaugeRate1 xi xi1 v v1 a) (gaugeRate2 xi xi1 xi2 v v1 v2 a x) x := by
  have hsq : HasDerivAt (fun y => v a y ^ 2) (2 * v a x * v1 a x) x := by
    have := (hv a x).pow 2
    simpa [pow_one, mul_comm, mul_left_comm, mul_assoc] using this
  have hsqne : v a x ^ 2 ≠ 0 := pow_ne_zero _ (hvne a x)
  have h1 : HasDerivAt (fun y => -(xi1 a y / v a y))
      (-((xi2 a x * v a x - xi1 a x * v1 a x) / v a x ^ 2)) x :=
    ((hxi1 a x).div (hv a x) (hvne a x)).neg
  have h2 : HasDerivAt (fun y => xi a y * v1 a y / v a y ^ 2)
      (((xi1 a x * v1 a x + xi a x * v2 a x) * v a x ^ 2
        - xi a x * v1 a x * (2 * v a x * v1 a x)) / (v a x ^ 2) ^ 2) x :=
    (((hxi a x).mul (hv1 a x)).div hsq hsqne)
  refine (h1.add h2).congr_deriv ?_
  rw [gaugeRate2]
  field_simp
  ring

/-! ### The bounds -/

section Bounds

variable {A0 A1 A2 B1 B2 V1 v0 : ℝ}

/-- The bound for the first space derivative. -/
theorem abs_gaugeRate1_le (hv0 : 0 < v0) (hvlow : ∀ a x, v0 ≤ |v a x|)
    (hA0 : ∀ a x, |xi a x| ≤ A0) (hA1 : ∀ a x, |xi1 a x| ≤ A1)
    (hB1 : ∀ a x, |v1 a x| ≤ B1) (a x : ℝ) :
    |gaugeRate1 xi xi1 v v1 a x| ≤ A1 / v0 + A0 * B1 / v0 ^ 2 := by
  have hA0' : 0 ≤ A0 := le_trans (abs_nonneg _) (hA0 a x)
  have hB1' : 0 ≤ B1 := le_trans (abs_nonneg _) (hB1 a x)
  have hvx : v0 ≤ |v a x| := hvlow a x
  have hterm1 : |(-(xi1 a x / v a x))| ≤ A1 / v0 := by
    rw [abs_neg, abs_div]
    have hA1' : 0 ≤ A1 := le_trans (abs_nonneg _) (hA1 a x)
    gcongr
    exact hA1 a x
  have hterm2 : |xi a x * v1 a x / v a x ^ 2| ≤ A0 * B1 / v0 ^ 2 := by
    rw [abs_div, abs_mul, abs_pow]
    gcongr
    all_goals first | exact hA0 a x | exact hB1 a x
  calc |gaugeRate1 xi xi1 v v1 a x|
      ≤ |(-(xi1 a x / v a x))| + |xi a x * v1 a x / v a x ^ 2| := abs_add_le _ _
    _ ≤ A1 / v0 + A0 * B1 / v0 ^ 2 := by linarith

/-- The bound for the second space derivative. -/
theorem abs_gaugeRate2_le (hv0 : 0 < v0) (hvlow : ∀ a x, v0 ≤ |v a x|)
    (hvup : ∀ a x, |v a x| ≤ V1)
    (hA0 : ∀ a x, |xi a x| ≤ A0) (hA1 : ∀ a x, |xi1 a x| ≤ A1)
    (hA2 : ∀ a x, |xi2 a x| ≤ A2)
    (hB1 : ∀ a x, |v1 a x| ≤ B1) (hB2 : ∀ a x, |v2 a x| ≤ B2) (a x : ℝ) :
    |gaugeRate2 xi xi1 xi2 v v1 v2 a x|
      ≤ A2 / v0 + 2 * (A1 * B1) / v0 ^ 2 + A0 * (V1 * B2 + 2 * B1 ^ 2) / v0 ^ 3 := by
  have hA0' : 0 ≤ A0 := le_trans (abs_nonneg _) (hA0 a x)
  have hA1' : 0 ≤ A1 := le_trans (abs_nonneg _) (hA1 a x)
  have hB1' : 0 ≤ B1 := le_trans (abs_nonneg _) (hB1 a x)
  have hB2' : 0 ≤ B2 := le_trans (abs_nonneg _) (hB2 a x)
  have hV1' : 0 ≤ V1 := le_trans (abs_nonneg _) (hvup a x)
  have hvx : v0 ≤ |v a x| := hvlow a x
  have hterm1 : |(-(xi2 a x / v a x))| ≤ A2 / v0 := by
    rw [abs_neg, abs_div]
    have hA2' : 0 ≤ A2 := le_trans (abs_nonneg _) (hA2 a x)
    gcongr
    exact hA2 a x
  have hterm2 : |2 * (xi1 a x * v1 a x) / v a x ^ 2| ≤ 2 * (A1 * B1) / v0 ^ 2 := by
    rw [abs_div, abs_mul, abs_mul, abs_pow, abs_two]
    gcongr
    all_goals first | exact hA1 a x | exact hB1 a x
  have hterm3 : |xi a x * (v a x * v2 a x - 2 * v1 a x ^ 2) / v a x ^ 3|
      ≤ A0 * (V1 * B2 + 2 * B1 ^ 2) / v0 ^ 3 := by
    rw [abs_div, abs_mul, abs_pow]
    have hnum : |v a x * v2 a x - 2 * v1 a x ^ 2| ≤ V1 * B2 + 2 * B1 ^ 2 := by
      have h1 : |v a x * v2 a x| ≤ V1 * B2 := by
        rw [abs_mul]
        exact mul_le_mul (hvup a x) (hB2 a x) (abs_nonneg _) hV1'
      have h2 : |2 * v1 a x ^ 2| ≤ 2 * B1 ^ 2 := by
        rw [abs_mul, abs_two, abs_pow]
        have : |v1 a x| ^ 2 ≤ B1 ^ 2 := by nlinarith [abs_nonneg (v1 a x), hB1 a x]
        linarith
      calc |v a x * v2 a x - 2 * v1 a x ^ 2|
          ≤ |v a x * v2 a x| + |2 * v1 a x ^ 2| := abs_sub _ _
        _ ≤ V1 * B2 + 2 * B1 ^ 2 := by linarith
    gcongr
    exact hA0 a x
  calc |gaugeRate2 xi xi1 xi2 v v1 v2 a x|
      ≤ |(-(xi2 a x / v a x)) + 2 * (xi1 a x * v1 a x) / v a x ^ 2|
          + |xi a x * (v a x * v2 a x - 2 * v1 a x ^ 2) / v a x ^ 3| := abs_add_le _ _
    _ ≤ (|(-(xi2 a x / v a x))| + |2 * (xi1 a x * v1 a x) / v a x ^ 2|)
          + |xi a x * (v a x * v2 a x - 2 * v1 a x ^ 2) / v a x ^ 3| := by
        have := abs_add_le (-(xi2 a x / v a x)) (2 * (xi1 a x * v1 a x) / v a x ^ 2)
        linarith
    _ ≤ A2 / v0 + 2 * (A1 * B1) / v0 ^ 2 + A0 * (V1 * B2 + 2 * B1 ^ 2) / v0 ^ 3 := by
        linarith

end Bounds

/-! ### Continuity and the Lipschitz constant -/

/-- The tangential rate is jointly continuous. -/
theorem continuous_gaugeRate (hxic : Continuous (uncurry xi))
    (hvc : Continuous (uncurry v)) (hvne : ∀ a x, v a x ≠ 0) :
    Continuous (uncurry (gaugeRate xi v)) :=
  (hxic.div hvc fun p => hvne p.1 p.2).neg

/-- The first space derivative is jointly continuous. -/
theorem continuous_gaugeRate1 (hxic : Continuous (uncurry xi))
    (hxi1c : Continuous (uncurry xi1)) (hvc : Continuous (uncurry v))
    (hv1c : Continuous (uncurry v1)) (hvne : ∀ a x, v a x ≠ 0) :
    Continuous (uncurry (gaugeRate1 xi xi1 v v1)) := by
  have hden : ∀ p : ℝ × ℝ, v p.1 p.2 ^ 2 ≠ 0 := fun p => pow_ne_zero _ (hvne p.1 p.2)
  exact ((hxi1c.div hvc fun p => hvne p.1 p.2).neg).add
    ((hxic.mul hv1c).div (hvc.pow 2) hden)

/-- The second space derivative is jointly continuous. -/
theorem continuous_gaugeRate2 (hxic : Continuous (uncurry xi))
    (hxi1c : Continuous (uncurry xi1)) (hxi2c : Continuous (uncurry xi2))
    (hvc : Continuous (uncurry v)) (hv1c : Continuous (uncurry v1))
    (hv2c : Continuous (uncurry v2)) (hvne : ∀ a x, v a x ≠ 0) :
    Continuous (uncurry (gaugeRate2 xi xi1 xi2 v v1 v2)) := by
  have hden2 : ∀ p : ℝ × ℝ, v p.1 p.2 ^ 2 ≠ 0 := fun p => pow_ne_zero _ (hvne p.1 p.2)
  have hden3 : ∀ p : ℝ × ℝ, v p.1 p.2 ^ 3 ≠ 0 := fun p => pow_ne_zero _ (hvne p.1 p.2)
  exact (((hxi2c.div hvc fun p => hvne p.1 p.2).neg).add
      (((continuous_const.mul (hxi1c.mul hv1c)).div (hvc.pow 2) hden2))).add
    ((hxic.mul ((hvc.mul hv2c).sub (continuous_const.mul (hv1c.pow 2)))).div
      (hvc.pow 3) hden3)

variable {A0 A1 A2 B1 B2 V1 v0 : ℝ}

/-- The tangential rate is globally Lipschitz in the space variable, with the
constant given by the bound for its derivative. -/
theorem lipschitzWith_gaugeRate (hxi : ∀ a x, HasDerivAt (xi a) (xi1 a x) x)
    (hv : ∀ a x, HasDerivAt (v a) (v1 a x) x) (hvne : ∀ a x, v a x ≠ 0)
    (hv0 : 0 < v0) (hvlow : ∀ a x, v0 ≤ |v a x|)
    (hA0 : ∀ a x, |xi a x| ≤ A0) (hA1 : ∀ a x, |xi1 a x| ≤ A1)
    (hB1 : ∀ a x, |v1 a x| ≤ B1) (a : ℝ) :
    LipschitzWith (Real.toNNReal (A1 / v0 + A0 * B1 / v0 ^ 2)) (gaugeRate xi v a) := by
  have hnn : 0 ≤ A1 / v0 + A0 * B1 / v0 ^ 2 :=
    le_trans (abs_nonneg _) (abs_gaugeRate1_le hv0 hvlow hA0 hA1 hB1 a 0)
  refine lipschitzWith_of_nnnorm_deriv_le
    (fun x => (hasDerivAt_gaugeRate hxi hv hvne a x).differentiableAt) (fun x => ?_)
  rw [(hasDerivAt_gaugeRate hxi hv hvne a x).deriv]
  have hb := abs_gaugeRate1_le hv0 hvlow hA0 hA1 hB1 a x
  rw [← NNReal.coe_le_coe, coe_nnnorm, Real.coe_toNNReal _ hnn, Real.norm_eq_abs]
  exact hb

/-! ### The hypotheses from bounds on the rate itself

The bounds above pass through the bound `A₀` for the tangential component,
which is *not* available for a family of closed curves whose length changes:
the closing relation makes `ξ` drift by `Q'(t)` over each arclength period.  Its
arclength derivatives remain periodic, so the two derivatives of the rate are
still bounded, and that is all the flow needs.  The statements below therefore
take bounds for `∂ₓh` and `∂ₓ²h` directly. -/

/-- The tangential rate is globally Lipschitz in the space variable, with any
bound for its space derivative. -/
theorem lipschitzWith_gaugeRate_of_bound {L : ℝ} (hL : 0 ≤ L)
    (hxi : ∀ a x, HasDerivAt (xi a) (xi1 a x) x)
    (hv : ∀ a x, HasDerivAt (v a) (v1 a x) x) (hvne : ∀ a x, v a x ≠ 0)
    (hb : ∀ a x, |gaugeRate1 xi xi1 v v1 a x| ≤ L) (a : ℝ) :
    LipschitzWith (Real.toNNReal L) (gaugeRate xi v a) := by
  refine lipschitzWith_of_nnnorm_deriv_le
    (fun x => (hasDerivAt_gaugeRate hxi hv hvne a x).differentiableAt) (fun x => ?_)
  rw [(hasDerivAt_gaugeRate hxi hv hvne a x).deriv]
  rw [← NNReal.coe_le_coe, coe_nnnorm, Real.coe_toNNReal _ hL, Real.norm_eq_abs]
  exact hb a x

/-- **The tangential rate satisfies the hypotheses of `FlowDerivative.lean`,
from bounds on the rate itself.**  No bound for the tangential component `ξ` is
required — only for the two space derivatives of the rate `−ξ/v`. -/
theorem gaugeRate_flow_hypotheses_of_bounds {L K2 : ℝ} (hL : 0 ≤ L)
    (hxi : ∀ a x, HasDerivAt (xi a) (xi1 a x) x)
    (hxi1 : ∀ a x, HasDerivAt (xi1 a) (xi2 a x) x)
    (hv : ∀ a x, HasDerivAt (v a) (v1 a x) x)
    (hv1 : ∀ a x, HasDerivAt (v1 a) (v2 a x) x)
    (hvne : ∀ a x, v a x ≠ 0)
    (hxic : Continuous (uncurry xi)) (hxi1c : Continuous (uncurry xi1))
    (hxi2c : Continuous (uncurry xi2)) (hvc : Continuous (uncurry v))
    (hv1c : Continuous (uncurry v1)) (hv2c : Continuous (uncurry v2))
    (hb1 : ∀ a x, |gaugeRate1 xi xi1 v v1 a x| ≤ L)
    (hb2 : ∀ a x, |gaugeRate2 xi xi1 xi2 v v1 v2 a x| ≤ K2) :
    (∀ a, LipschitzWith (Real.toNNReal L) (gaugeRate xi v a)) ∧
      Continuous (uncurry (gaugeRate xi v)) ∧
      (∀ a x, HasDerivAt (gaugeRate xi v a) (gaugeRate1 xi xi1 v v1 a x) x) ∧
      Continuous (uncurry (gaugeRate1 xi xi1 v v1)) ∧
      (∀ a x, HasDerivAt (gaugeRate1 xi xi1 v v1 a) (gaugeRate2 xi xi1 xi2 v v1 v2 a x) x) ∧
      Continuous (uncurry (gaugeRate2 xi xi1 xi2 v v1 v2)) ∧
      (∀ a x, |gaugeRate2 xi xi1 xi2 v v1 v2 a x| ≤ K2) :=
  ⟨fun a => lipschitzWith_gaugeRate_of_bound hL hxi hv hvne hb1 a,
   continuous_gaugeRate hxic hvc hvne,
   hasDerivAt_gaugeRate hxi hv hvne,
   continuous_gaugeRate1 hxic hxi1c hvc hv1c hvne,
   hasDerivAt_gaugeRate1 hxi hxi1 hv hv1 hvne,
   continuous_gaugeRate2 hxic hxi1c hxi2c hvc hv1c hv2c hvne,
   hb2⟩

/-- **The tangential rate satisfies the hypotheses of `FlowDerivative.lean`**:
it is jointly continuous, globally Lipschitz in the space variable with an
explicit constant, and has two jointly continuous space derivatives, the second
of which is bounded. -/
theorem gaugeRate_flow_hypotheses
    (hxi : ∀ a x, HasDerivAt (xi a) (xi1 a x) x)
    (hxi1 : ∀ a x, HasDerivAt (xi1 a) (xi2 a x) x)
    (hv : ∀ a x, HasDerivAt (v a) (v1 a x) x)
    (hv1 : ∀ a x, HasDerivAt (v1 a) (v2 a x) x)
    (hvne : ∀ a x, v a x ≠ 0)
    (hxic : Continuous (uncurry xi)) (hxi1c : Continuous (uncurry xi1))
    (hxi2c : Continuous (uncurry xi2)) (hvc : Continuous (uncurry v))
    (hv1c : Continuous (uncurry v1)) (hv2c : Continuous (uncurry v2))
    (hv0 : 0 < v0) (hvlow : ∀ a x, v0 ≤ |v a x|) (hvup : ∀ a x, |v a x| ≤ V1)
    (hA0 : ∀ a x, |xi a x| ≤ A0) (hA1 : ∀ a x, |xi1 a x| ≤ A1)
    (hA2 : ∀ a x, |xi2 a x| ≤ A2)
    (hB1 : ∀ a x, |v1 a x| ≤ B1) (hB2 : ∀ a x, |v2 a x| ≤ B2) :
    (∀ a, LipschitzWith (Real.toNNReal (A1 / v0 + A0 * B1 / v0 ^ 2)) (gaugeRate xi v a)) ∧
      Continuous (uncurry (gaugeRate xi v)) ∧
      (∀ a x, HasDerivAt (gaugeRate xi v a) (gaugeRate1 xi xi1 v v1 a x) x) ∧
      Continuous (uncurry (gaugeRate1 xi xi1 v v1)) ∧
      (∀ a x, HasDerivAt (gaugeRate1 xi xi1 v v1 a) (gaugeRate2 xi xi1 xi2 v v1 v2 a x) x) ∧
      Continuous (uncurry (gaugeRate2 xi xi1 xi2 v v1 v2)) ∧
      (∀ a x, |gaugeRate2 xi xi1 xi2 v v1 v2 a x|
        ≤ A2 / v0 + 2 * (A1 * B1) / v0 ^ 2 + A0 * (V1 * B2 + 2 * B1 ^ 2) / v0 ^ 3) :=
  ⟨fun a => lipschitzWith_gaugeRate hxi hv hvne hv0 hvlow hA0 hA1 hB1 a,
   continuous_gaugeRate hxic hvc hvne,
   hasDerivAt_gaugeRate hxi hv hvne,
   continuous_gaugeRate1 hxic hxi1c hvc hv1c hvne,
   hasDerivAt_gaugeRate1 hxi hxi1 hv hv1 hvne,
   continuous_gaugeRate2 hxic hxi1c hxi2c hvc hv1c hv2c hvne,
   fun a x => abs_gaugeRate2_le hv0 hvlow hvup hA0 hA1 hA2 hB1 hB2 a x⟩

end GaugeRate
