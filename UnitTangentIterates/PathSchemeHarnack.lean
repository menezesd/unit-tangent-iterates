import UnitTangentIterates.PathSchemeFloorFree
import UnitTangentIterates.LimitStrictnessFromApproximants

/-!
# The path-scheme closing theorems on the `C2` strictness hypothesis

`PathSchemeFloorFree` removed the curvature floor but still asked for
`LimitStrictnessData`, whose `next_nonnegative` field is a *differential*
condition on the limiting curvature and therefore forces `C3` regularity of the
limit.  The manifest recorded that as the last missing paper theorem, and the
arclength-correspondence audit as its consequence.

`LimitStrictnessDataH` replaces that field by the paper's bounded-shift Harnack
inequality, which is implied by it at every finite stage
(`UnitTangent.harnack_of_next_nonneg`) and, unlike it, survives pointwise limits
(`UnitTangent.harnack_of_tendsto`).  This file restates both closing theorems on
that hypothesis.  The proofs are those of `PathSchemeFloorFree` with the single
substitution `isOval_ev_of_limitStrictnessData -> isOval_ev_of_limitStrictnessDataH`;
everything else in the closing argument is untouched, which is the point — the
shadowing limit, the orbit transfer and the width contradiction never needed the
third derivative.
-/

noncomputable section

set_option maxHeartbeats 4000000

open Set Filter Topology Function MarkedSpace PathMetric PathMetric.NormalPath

open NormalPathC2Increment

namespace MarkedSchemePathTheorem

theorem main_theorem_of_path_scheme_harnack {c dlt : ℝ} (hc : 0 < c)
    (hdlt : 0 < dlt)
    (hstrict : ∀ p : Data, IsTubeMember c 0 dlt p →
      Nonempty (UnconditionalAssembly.LimitStrictnessDataH p))
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
    fun n => UnconditionalAssembly.isOval_ev_of_limitStrictnessDataH hc hdlt
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

theorem main_theorem_of_path_scheme_geom_harnack {c dlt : ℝ} (hc : 0 < c)
    (hdlt : 0 < dlt)
    (hstrict : ∀ p : Data, IsTubeMember c 0 dlt p →
      Nonempty (UnconditionalAssembly.LimitStrictnessDataH p))
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
    fun n => UnconditionalAssembly.isOval_ev_of_limitStrictnessDataH hc hdlt
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
