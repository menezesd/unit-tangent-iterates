import UnitTangentIterates.MarkedSchemePathTheorem
import UnitTangentIterates.UnconditionalAssemblyRemainder

/-!
# The path-scheme closing theorem, without a curvature floor

§60 left the tube maps `B`, `T` as the one input that is a construction rather
than a placement.  The obstacle there was the *shape* of the hypothesis: the
range-form closing theorem asks for `dist (B x) (B y) ≤ dist x y` in the ambient
marked metric, while what the Jacobi estimates give is a bound on **path cost**
— and `dist ≤ pathDist`, so the path bound does not imply the ambient one.

`MarkedSchemePathTheorem.main_theorem_of_path_scheme` already takes the path
form:

```
  hmap : ∀ p q Γ, IsConstantSpeedNormalPath … Γ →
    ∃ Δ : NormalPath (B p) (B q), cost Δ ≤ K · cost Γ ∧ …      (K ≤ 1)
```

which is exactly the paper's `lem:jacobi` — `W(𝔅Γ) ≤ W(Γ)` together with the
`S_j` gains, as `JacobiPathGains` proves them.

What it also carried was the curvature floor.  This file removes it, by the same
substitution as §49: `isOval_ev` gives way to
`isOval_ev_of_limitStrictnessData`, and the tube is taken with `kmin = 0`.

`main_theorem_of_path_scheme_floor_free` therefore has **neither** obstruction:
no curvature floor, and no ambient-nonexpansiveness requirement.

`main_theorem_of_path_scheme_geom_floor_free` is the same for the geometric
variant, and it matters more than it looks.  The plain version asks `K ≤ 1` — a
*universal* contraction constant for the inverse step over the whole tube, which
is what the session log had recorded as gap (a).  The geometric version does not
ask for it: `K` may exceed one, provided the defects decay geometrically with
`Kθ < 1`.  Since the model defects decay like `e^{−βHₙ}` while the Jacobi
constant grows only polynomially in the perimeter, that is the right trade.
-/

noncomputable section

set_option maxHeartbeats 4000000

open Set Filter Topology Function MarkedSpace PathMetric PathMetric.NormalPath

open NormalPathC2Increment

namespace MarkedSchemePathTheorem

theorem main_theorem_of_path_scheme_floor_free {c dlt : ℝ} (hc : 0 < c)
    (hdlt : 0 < dlt)
    (hstrict : ∀ p : Data, IsTubeMember c 0 dlt p →
      Nonempty (UnconditionalAssembly.LimitStrictnessData p))
    {B T : Data → Data} {Q : ℕ → Data} {d : ℕ → ℝ}
    {K P0 P1 khat Cw H : ℝ} {dir : ℂ}
    (hK : 0 ≤ K) (hK1 : K ≤ 1) (hd : ∀ n, 0 ≤ d n) (hs : Summable d)
    (hmap : ∀ (p q : Data) (Γ : NormalPath p q), IsConstantSpeedNormalPath P0 P1 khat Γ →
      ∃ Δ : NormalPath (B p) (B q),
        cost Δ ≤ K * cost Γ ∧ IsConstantSpeedNormalPath P0 P1 khat Δ)
    (hdefect : ∀ n, ∃ Λ : NormalPath (Q n) (B (Q (n + 1))),
      cost Λ ≤ d n ∧ IsConstantSpeedNormalPath P0 P1 khat Λ)
    (hmem : ∀ n k, IsTubeMember c 0 dlt (TubePullbackLimit.pullback B Q n k))
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
  have hQ0 : IsTubeMember c 0 dlt (Q 0) := by
    have := hmem 0 0
    rwa [TubePullbackLimit.pullback_zero] at this
  set r0 : ℝ := ShadowingTails.tail d 0 with hr0def
  set Csh : ℝ := c2Const P0 P1 khat * r0 with hCshdef
  have hr0 : 0 ≤ r0 := ShadowingTails.tail_nonneg hd 0
  have hCsh : 0 ≤ Csh := mul_nonneg (c2Const_nonneg P0 P1 khat) hr0
  refine ⟨fun n => ev (Z n), perim (Z 0),
    fun n => UnconditionalAssembly.isOval_ev_of_limitStrictnessData hc hdlt
      (hZmem n) (hstrict _ (hZmem n)).some, ?_, perim_pos hc (hZmem 0),
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

theorem main_theorem_of_path_scheme_geom_floor_free {c dlt : ℝ} (hc : 0 < c)
    (hdlt : 0 < dlt)
    (hstrict : ∀ p : Data, IsTubeMember c 0 dlt p →
      Nonempty (UnconditionalAssembly.LimitStrictnessData p))
    {B T : Data → Data} {Q : ℕ → Data} {d : ℕ → ℝ}
    {K D th P0 P1 khat Cw H : ℝ} {dir : ℂ}
    (hK : 0 ≤ K) (hD : 0 ≤ D) (hth : 0 ≤ th) (hKth : K * th < 1)
    (hd : ∀ n, 0 ≤ d n) (hdgeo : ∀ n, d n ≤ D * th ^ n)
    (hmap : ∀ (p q : Data) (Γ : NormalPath p q), IsConstantSpeedNormalPath P0 P1 khat Γ →
      ∃ Δ : NormalPath (B p) (B q),
        cost Δ ≤ K * cost Γ ∧ IsConstantSpeedNormalPath P0 P1 khat Δ)
    (hdefect : ∀ n, ∃ Λ : NormalPath (Q n) (B (Q (n + 1))),
      cost Λ ≤ d n ∧ IsConstantSpeedNormalPath P0 P1 khat Λ)
    (hmem : ∀ n k, IsTubeMember c 0 dlt (TubePullbackLimit.pullback B Q n k))
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
  have hQ0 : IsTubeMember c 0 dlt (Q 0) := by
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
    fun n => UnconditionalAssembly.isOval_ev_of_limitStrictnessData hc hdlt
      (hZmem n) (hstrict _ (hZmem n)).some, ?_, perim_pos hc (hZmem 0),
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
