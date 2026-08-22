import Mathlib
import UnitTangentIterates.JacobiArclength

/-!
# The arclength Jacobi estimates with constants uniform along the path

`JacobiArclength.jacobi_estimates_arclength` produces, at one time of the path,
the four inverse Jacobi estimates with the rear in arclength and the front in
its normalized parameter.  Its constants

```
  arcW P = P,  arc0 = P/(1-e^{-ℓ₀}),  arc1 = 1/c + P/(1-e^{-ℓ₀}),
  arc2 = 1/(Pc²) + 2κ̂²/c³ + 1/c + P/(1-e^{-ℓ₀})
```

still depend on the front period `P`, which varies along the path;
`GaugeNormalPath.exists_normalPath_of_gauge_jacobi` wants one set of constants
for all times.  Two-sided bounds `P₀ ≤ P ≤ P₁` for the front period make the
constants uniform: each of the four is monotone in `P` — increasing through the
term `P/(1-e^{-ℓ₀})`, decreasing through the term `1/(Pc²)` — so replacing `P`
by `P₁` in the increasing terms and by `P₀` in the decreasing one dominates them
all, in the same style as `SelectedInversePathGeometry.uconst*`.

The estimates are also restated against the front slice `η_N` of the path
directly, using the link `η_N(u) = η_F(P u)` between the normalized front
velocity and its arclength version.

Main result: `jacobi_estimates_arclength_uniform`.
-/

noncomputable section

open MeasureTheory MarkedTopology

namespace JacobiArclengthUniform

open JacobiArclength JacobiNormalized

/-! ### The uniform constants -/

/-- The uniform `L¹` constant: the largest front period. -/
def uarcW (P1 : ℝ) : ℝ := P1

/-- The uniform `L¹ → L^∞` constant. -/
def uarc0 (P1 l0 : ℝ) : ℝ := P1 / (1 - Real.exp (-l0))

/-- The uniform first-order constant. -/
def uarc1 (P1 l0 c : ℝ) : ℝ := 1 / c + P1 / (1 - Real.exp (-l0))

/-- The uniform second-order constant: the term `1/(Pc²)` is decreasing in `P`,
so it is the *smallest* period that enters it. -/
def uarc2 (P0 P1 l0 c kh : ℝ) : ℝ :=
  1 / (P0 * c ^ 2) + 2 * kh ^ 2 / c ^ 3 + 1 / c + P1 / (1 - Real.exp (-l0))

theorem uarcW_nonneg {P1 : ℝ} (hP1 : 0 < P1) : 0 ≤ uarcW P1 := hP1.le

theorem uarc0_nonneg {P1 l0 : ℝ} (hP1 : 0 < P1) (hl0 : 0 < l0) : 0 ≤ uarc0 P1 l0 := by
  have := one_sub_exp_pos hl0
  unfold uarc0; positivity

theorem uarc1_nonneg {P1 l0 c : ℝ} (hP1 : 0 < P1) (hl0 : 0 < l0) (hc : 0 < c) :
    0 ≤ uarc1 P1 l0 c := by
  have := one_sub_exp_pos hl0
  unfold uarc1; positivity

theorem uarc2_nonneg {P0 P1 l0 c kh : ℝ} (hP0 : 0 < P0) (hP1 : 0 < P1) (hl0 : 0 < l0)
    (hc : 0 < c) : 0 ≤ uarc2 P0 P1 l0 c kh := by
  have := one_sub_exp_pos hl0
  unfold uarc2; positivity

/-! ### Monotonicity in the front period -/

theorem arcW_le_uarcW {P P1 : ℝ} (h : P ≤ P1) : arcW P ≤ uarcW P1 := h

theorem arc0_le_uarc0 {P P1 l0 : ℝ} (hl0 : 0 < l0) (h : P ≤ P1) :
    arc0 P l0 ≤ uarc0 P1 l0 := by
  have hexp := one_sub_exp_pos hl0
  unfold arc0 uarc0
  exact div_le_div_of_nonneg_right h hexp.le

theorem arc1_le_uarc1 {P P1 l0 c : ℝ} (hl0 : 0 < l0) (h : P ≤ P1) :
    arc1 P l0 c ≤ uarc1 P1 l0 c := by
  have := arc0_le_uarc0 hl0 h
  unfold arc1 uarc1 arc0 uarc0 at *
  linarith

theorem arc2_le_uarc2 {P P0 P1 l0 c kh : ℝ} (hP0 : 0 < P0) (hl0 : 0 < l0) (hc : 0 < c)
    (h0 : P0 ≤ P) (h1 : P ≤ P1) : arc2 P l0 c kh ≤ uarc2 P0 P1 l0 c kh := by
  have hexp := one_sub_exp_pos hl0
  have hP : 0 < P := lt_of_lt_of_le hP0 h0
  have hc2 : (0:ℝ) < c ^ 2 := by positivity
  have hlow : 1 / (P * c ^ 2) ≤ 1 / (P0 * c ^ 2) := by
    apply one_div_le_one_div_of_le (by positivity)
    exact mul_le_mul_of_nonneg_right h0 hc2.le
  have hhigh : P / (1 - Real.exp (-l0)) ≤ P1 / (1 - Real.exp (-l0)) :=
    div_le_div_of_nonneg_right h1 hexp.le
  unfold arc2 uarc2
  linarith

/-! ### The uniform estimates -/

/-- **The arclength Jacobi estimates with constants uniform along the path.**

The four estimates of `JacobiArclength.jacobi_estimates_arclength`, with the
front period `P` — which varies along the path — replaced by the two-sided
bounds `P₀ ≤ P ≤ P₁`, and with the right-hand sides written against the
normalized front slice `etaN` through the link `etaN u = etaF (P u)`.  The
resulting constants no longer mention `P`, so the same four numbers serve at
every time of the path, which is what
`GaugeNormalPath.exists_normalPath_of_gauge_jacobi` consumes. -/
theorem jacobi_estimates_arclength_uniform {l P P0 P1 l0 c kh SF0 SF1 : ℝ}
    {etaR etaR1 etaR2 etaF etaN : ℝ → ℝ}
    (hP0 : 0 < P0) (h0 : P0 ≤ P) (h1 : P ≤ P1) (hl0 : 0 < l0) (hc : 0 < c)
    (hR1 : ∀ x, HasDerivAt etaR (etaR1 x) x) (hR2 : ∀ x, HasDerivAt etaR1 (etaR2 x) x)
    (hSF0 : 0 ≤ SF0)
    (hW : (∫ x in (0:ℝ)..l, |etaR x|) ≤ ∫ s in (0:ℝ)..P, |etaF s|)
    (hS0 : ∀ x, |etaR x| ≤ (1 - Real.exp (-l0))⁻¹ * ∫ s in (0:ℝ)..P, |etaF s|)
    (hS1 : ∀ x, |etaR1 x|
      ≤ SF0 / c + (1 - Real.exp (-l0))⁻¹ * ∫ s in (0:ℝ)..P, |etaF s|)
    (hS2 : ∀ x, |etaR2 x| ≤ SF1 / c ^ 2 + 2 * kh ^ 2 * SF0 / c ^ 3
      + (SF0 / c + (1 - Real.exp (-l0))⁻¹ * ∫ s in (0:ℝ)..P, |etaF s|))
    (hnorm0 : SF0 ≤ supNorm etaN)
    (hnorm1 : P * SF1 ≤ supNorm (iteratedDeriv 1 etaN))
    (hlink : ∀ u, etaN u = etaF (P * u)) :
    (∫ x in (0:ℝ)..l, |etaR x|) ≤ uarcW P1 * ∫ u in (0:ℝ)..1, |etaN u|
      ∧ supNorm etaR ≤ uarc0 P1 l0 * ∫ u in (0:ℝ)..1, |etaN u|
      ∧ supNorm (deriv etaR) ≤ uarc1 P1 l0 c * ((∫ u in (0:ℝ)..1, |etaN u|)
          + supNorm etaN)
      ∧ supNorm (deriv (deriv etaR)) ≤ uarc2 P0 P1 l0 c kh
          * ((∫ u in (0:ℝ)..1, |etaN u|) + supNorm etaN
            + supNorm (iteratedDeriv 1 etaN)) := by
  have hP : 0 < P := lt_of_lt_of_le hP0 h0
  have hetaN : etaN = fun u => etaF (P * u) := funext hlink
  subst hetaN
  obtain ⟨e1, e2, e3, e4⟩ :=
    jacobi_estimates_arclength (l := l) (kh := kh) hP hl0 hc hR1 hR2 hSF0 hW hS0 hS1 hS2
      hnorm0 hnorm1
  have hWnn : (0:ℝ) ≤ ∫ u in (0:ℝ)..1, |etaF (P * u)| :=
    intervalIntegral.integral_nonneg zero_le_one (fun u _ => abs_nonneg _)
  have hS0nn : (0:ℝ) ≤ supNorm (fun u => etaF (P * u)) := supNorm_nonneg _
  have hS1nn : (0:ℝ) ≤ supNorm (iteratedDeriv 1 fun u => etaF (P * u)) := supNorm_nonneg _
  refine ⟨e1.trans (mul_le_mul_of_nonneg_right (arcW_le_uarcW h1) hWnn),
    e2.trans (mul_le_mul_of_nonneg_right (arc0_le_uarc0 hl0 h1) hWnn),
    e3.trans (mul_le_mul_of_nonneg_right (arc1_le_uarc1 hl0 h1) (by linarith)),
    e4.trans (mul_le_mul_of_nonneg_right (arc2_le_uarc2 hP0 hl0 hc h0 h1) (by linarith))⟩

end JacobiArclengthUniform
