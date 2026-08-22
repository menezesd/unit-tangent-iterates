import Mathlib
import UnitTangentIterates.TubePullbackLimit
import UnitTangentIterates.MarkedSchemeTheoremRange

/-!
# The closing argument from the path-cost form of the shadowing scheme

`MarkedSchemeTheoremRange.main_theorem_on_marked_space_range` runs the closing
step of *A Noncircular Oval with Convex Unit-Tangent Iterates* from an abstract
dynamical hypothesis: the selected inverse is **non-expansive for the marked
metric**.  That is not what the paper's *Inverse Jacobi estimates* provide;
what they provide is a bound for the **cost of the image of a normal path**.

`TubePullbackLimit.exists_shadowing_limit` runs the scheme from exactly that
hypothesis.  This file feeds its output into the closing argument, so that the
conclusion — a sequence of ovals `Xₙ` with
`range X_{n+1} = range (𝒯 Xₙ)` whose initial member is not a circle — rests on

* the selected inverse taking a constant-speed normal path to a constant-speed
  normal path of cost at most `K ≤ 1` times as large,
* defect paths of summable cost joining the models to the images of their
  successors,
* tube membership of the terminal pullbacks and continuity of the map,

instead of on non-expansiveness in the marked metric.  The width gap is asked
against the explicit quantity `c2Const P₀ P₁ κ̂ · r₀`, the shadowing radius the
scheme produces.

As everywhere in this project, the two dynamical inputs — the path-cost bound
for the selected inverse and the model pseudo-orbit — are hypotheses, not
theorems; nothing here should be read as a verification of the paper's main
theorem.
-/

noncomputable section

open Set Filter Topology Function MarkedSpace PathMetric PathMetric.NormalPath
open NormalPathC2Increment

namespace MarkedSchemePathTheorem

/-- **The closing argument from the path-cost form of the scheme.**  With the
hypotheses of `TubePullbackLimit.exists_shadowing_limit`, a left inverse `T`
realizing the unit-tangent transform up to reparametrization, and the width gap
of the paper's large-separation lemma against the shadowing radius
`Csh = c2Const P₀ P₁ κ̂ · r₀`, there is a sequence of ovals `Xₙ` with
`range X_{n+1} = range (𝒯 Xₙ)` whose initial member is not a circle. -/
theorem main_theorem_of_path_scheme {c kmin dlt : ℝ} (hc : 0 < c) (hkmin : 0 < kmin)
    (hdlt : 0 < dlt)
    {B T : Data → Data} {Q : ℕ → Data} {d : ℕ → ℝ}
    {K P0 P1 khat Cw H : ℝ} {dir : ℂ}
    (hK : 0 ≤ K) (hK1 : K ≤ 1) (hd : ∀ n, 0 ≤ d n) (hs : Summable d)
    (hmap : ∀ (p q : Data) (Γ : NormalPath p q), IsConstantSpeedNormalPath P0 P1 khat Γ →
      ∃ Δ : NormalPath (B p) (B q),
        cost Δ ≤ K * cost Γ ∧ IsConstantSpeedNormalPath P0 P1 khat Δ)
    (hdefect : ∀ n, ∃ Λ : NormalPath (Q n) (B (Q (n + 1))),
      cost Λ ≤ d n ∧ IsConstantSpeedNormalPath P0 P1 khat Λ)
    (hmem : ∀ n k, IsTubeMember c kmin dlt (TubePullbackLimit.pullback B Q n k))
    (hBcont : Continuous B) (hT : ∀ p, T (B p) = p)
    (hTev : ∀ p : Data, range (ev (T p)) = range (UnitTangent.unitTangentMap (ev p)))
    (hPerQ : perim (Q 0) = 2 * H) (hdir : ‖dir‖ = 1)
    (hQw : Width.width (range (ev (Q 0))) dir ≤ Cw)
    (hgap : Cw + 2 * (c2Const P0 P1 khat * ShadowingTails.tail d 0)
      < (2 * H - c2Const P0 P1 khat * ShadowingTails.tail d 0) / Real.pi) :
    ∃ (X : ℕ → ℝ → ℂ) (LX : ℝ),
      (∀ n, MainTheoremConditional.IsOval (X n)) ∧
      (∀ n, range (X (n + 1)) = range (UnitTangent.unitTangentMap (X n))) ∧
      0 < LX ∧ Periodic (X 0) LX ∧
      ¬ ClosingArgument.IsCircleOfPerimeter (range (X 0)) LX := by
  obtain ⟨Z, hZmem, -, horb, -, hpoint, -, hper⟩ :=
    TubePullbackLimit.exists_shadowing_limit hK hK1 hd hs hmap hdefect hmem hBcont
  -- the model is the zeroth pullback
  have hQ0 : IsTubeMember c kmin dlt (Q 0) := by
    have := hmem 0 0
    rwa [TubePullbackLimit.pullback_zero] at this
  set r0 : ℝ := ShadowingTails.tail d 0 with hr0def
  set Csh : ℝ := c2Const P0 P1 khat * r0 with hCshdef
  have hr0 : 0 ≤ r0 := ShadowingTails.tail_nonneg hd 0
  have hCsh : 0 ≤ Csh := mul_nonneg (c2Const_nonneg P0 P1 khat) hr0
  refine ⟨fun n => ev (Z n), perim (Z 0),
    fun n => isOval_ev hc hkmin hdlt (hZmem n), ?_, perim_pos hc (hZmem 0),
    periodic_ev hc (hZmem 0), ?_⟩
  · -- the orbit condition, up to reparametrization
    intro n
    have hTZ : T (Z n) = Z (n + 1) :=
      TubePullbackLimit.forward_orbit_of_inverse_orbit hT horb n
    show range (ev (Z (n + 1))) = range (UnitTangent.unitTangentMap (ev (Z n)))
    rw [← hTZ, hTev (Z n)]
  · -- the closing width argument, in the normalized parameter
    have hdist : ∀ u, dist ((Z 0).1 u) ((Q 0).1 u) ≤ Csh := by
      intro u
      have h1 : ‖(Z 0).1 u - (Q 0).1 u‖ ≤ r0 := hpoint 0 u
      have h2 : r0 ≤ Csh := by
        have := one_le_c2Const P0 P1 khat
        nlinarith
      rw [dist_eq_norm]
      linarith
    have hperZ : 2 * H - Csh ≤ perim (Z 0) := by
      have h := hper 0
      rw [hPerQ] at h
      have := (abs_le.mp h).1
      linarith
    have hrangeZ : range (ev (Z 0)) = range (⇑(Z 0).1) := range_ev hc (hZmem 0)
    have hrangeQ : range (ev (Q 0)) = range (⇑(Q 0).1) := range_ev hc hQ0
    rw [hrangeZ]
    rw [hrangeQ] at hQw
    exact CurveDistance.not_isCircleOfPerimeter_of_dist_le (H := H)
      (Z 0).1.continuous (hZmem 0).periodic one_pos
      (Q 0).1.continuous hQ0.periodic one_pos
      hdir hCsh hdist hQw hperZ hgap

/-- **The closing argument with an expanding inverse step and geometric
defects.**  The cost factor `K` of one inverse step is no longer asked to be at
most one: it is enough that the defects decay geometrically, `dₙ ≤ Dθⁿ` with
`Kθ < 1`, the shadowing radius then being `r₀ = D/(1 − Kθ)`. -/
theorem main_theorem_of_path_scheme_geom {c kmin dlt : ℝ} (hc : 0 < c) (hkmin : 0 < kmin)
    (hdlt : 0 < dlt)
    {B T : Data → Data} {Q : ℕ → Data} {d : ℕ → ℝ}
    {K D th P0 P1 khat Cw H : ℝ} {dir : ℂ}
    (hK : 0 ≤ K) (hD : 0 ≤ D) (hth : 0 ≤ th) (hKth : K * th < 1)
    (hd : ∀ n, 0 ≤ d n) (hdgeo : ∀ n, d n ≤ D * th ^ n)
    (hmap : ∀ (p q : Data) (Γ : NormalPath p q), IsConstantSpeedNormalPath P0 P1 khat Γ →
      ∃ Δ : NormalPath (B p) (B q),
        cost Δ ≤ K * cost Γ ∧ IsConstantSpeedNormalPath P0 P1 khat Δ)
    (hdefect : ∀ n, ∃ Λ : NormalPath (Q n) (B (Q (n + 1))),
      cost Λ ≤ d n ∧ IsConstantSpeedNormalPath P0 P1 khat Λ)
    (hmem : ∀ n k, IsTubeMember c kmin dlt (TubePullbackLimit.pullback B Q n k))
    (hBcont : Continuous B) (hT : ∀ p, T (B p) = p)
    (hTev : ∀ p : Data, range (ev (T p)) = range (UnitTangent.unitTangentMap (ev p)))
    (hPerQ : perim (Q 0) = 2 * H) (hdir : ‖dir‖ = 1)
    (hQw : Width.width (range (ev (Q 0))) dir ≤ Cw)
    (hgap : Cw + 2 * (c2Const P0 P1 khat * (D * (1 - K * th)⁻¹))
      < (2 * H - c2Const P0 P1 khat * (D * (1 - K * th)⁻¹)) / Real.pi) :
    ∃ (X : ℕ → ℝ → ℂ) (LX : ℝ),
      (∀ n, MainTheoremConditional.IsOval (X n)) ∧
      (∀ n, range (X (n + 1)) = range (UnitTangent.unitTangentMap (X n))) ∧
      0 < LX ∧ Periodic (X 0) LX ∧
      ¬ ClosingArgument.IsCircleOfPerimeter (range (X 0)) LX := by
  obtain ⟨Z, hZmem, -, horb, -, hpoint, -, hper⟩ :=
    TubePullbackLimit.exists_shadowing_limit_geom hK hD hth hKth hd hdgeo hmap hdefect
      hmem hBcont
  have hQ0 : IsTubeMember c kmin dlt (Q 0) := by
    have := hmem 0 0
    rwa [TubePullbackLimit.pullback_zero] at this
  set r0 : ℝ := D * (1 - K * th)⁻¹ with hr0def
  set Csh : ℝ := c2Const P0 P1 khat * r0 with hCshdef
  have hinv : 0 ≤ (1 - K * th)⁻¹ := by
    have : 0 < 1 - K * th := by linarith
    positivity
  have hr0 : 0 ≤ r0 := mul_nonneg hD hinv
  have hCsh : 0 ≤ Csh := mul_nonneg (c2Const_nonneg P0 P1 khat) hr0
  have hrad : D * th ^ 0 * (1 - K * th)⁻¹ = r0 := by rw [pow_zero, mul_one]
  refine ⟨fun n => ev (Z n), perim (Z 0),
    fun n => isOval_ev hc hkmin hdlt (hZmem n), ?_, perim_pos hc (hZmem 0),
    periodic_ev hc (hZmem 0), ?_⟩
  · intro n
    have hTZ : T (Z n) = Z (n + 1) :=
      TubePullbackLimit.forward_orbit_of_inverse_orbit hT horb n
    show range (ev (Z (n + 1))) = range (UnitTangent.unitTangentMap (ev (Z n)))
    rw [← hTZ, hTev (Z n)]
  · have hdist : ∀ u, dist ((Z 0).1 u) ((Q 0).1 u) ≤ Csh := by
      intro u
      have h1 : ‖(Z 0).1 u - (Q 0).1 u‖ ≤ r0 := by
        have := hpoint 0 u
        rwa [hrad] at this
      have h2 : r0 ≤ Csh := by
        have := one_le_c2Const P0 P1 khat
        nlinarith
      rw [dist_eq_norm]
      linarith
    have hperZ : 2 * H - Csh ≤ perim (Z 0) := by
      have h := hper 0
      rw [hrad, hPerQ] at h
      have := (abs_le.mp h).1
      linarith
    have hrangeZ : range (ev (Z 0)) = range (⇑(Z 0).1) := range_ev hc (hZmem 0)
    have hrangeQ : range (ev (Q 0)) = range (⇑(Q 0).1) := range_ev hc hQ0
    rw [hrangeZ]
    rw [hrangeQ] at hQw
    exact CurveDistance.not_isCircleOfPerimeter_of_dist_le (H := H)
      (Z 0).1.continuous (hZmem 0).periodic one_pos
      (Q 0).1.continuous hQ0.periodic one_pos
      hdir hCsh hdist hQw hperZ hgap

end MarkedSchemePathTheorem
