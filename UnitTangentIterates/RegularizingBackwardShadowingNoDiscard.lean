import UnitTangentIterates.RegularizingBackwardShadowingTerminalTails
import UnitTangentIterates.ShadowingScheme
import UnitTangentIterates.TubeConstants

/-!
# No-discard and uniqueness clauses for regularizing backward shadowing

This file packages two claim-level parts of `thm:shadow` independently of the
configured recursive grid.

* `noDiscardCertificate` gives the explicit positive `etaStar` and propagates
  its two curvature margins to every tail.
* `OrbitInShrinkingBalls.unique` is the exact uniqueness argument for inverse
  orbits in closed shrinking metric tubes.  Applying it to the physical
  selected inverse still requires a non-expansiveness theorem in the chosen
  marked metric; that hypothesis is intentionally visible here.
-/

noncomputable section

open Filter Topology Set

namespace RegularizingBackwardShadowingNoDiscard

/-- The paper's explicit no-discard threshold is strictly positive. -/
theorem etaStar_pos {Cint Ctube Cinc k0 : ℝ}
    (hCint : 0 < Cint) (hCtube : 0 < Ctube) (hCinc : 0 < Cinc)
    (hk : k0 < 1) :
    0 < TubeConstants.etaStar Cint Ctube Cinc k0 := by
  have hchain := TubeConstants.kappa_chain hk
  have hleft : 0 < (TubeConstants.kbar k0 - k0) / Ctube :=
    div_pos (sub_pos.mpr hchain.1) hCtube
  have hright : 0 < (TubeConstants.khat k0 - TubeConstants.kbar k0) / Cinc :=
    div_pos (sub_pos.mpr hchain.2.1) hCinc
  unfold TubeConstants.etaStar
  exact mul_pos (one_div_pos.mpr (mul_pos (by norm_num) hCint)) (lt_min hleft hright)

/-- All levelwise smallness margins supplied by the paper's `etaStar`. -/
structure NoDiscardCertificate
    (e : ℕ → ℝ) (Cint Ctube Cinc k0 : ℝ) : Prop where
  threshold_pos : 0 < TubeConstants.etaStar Cint Ctube Cinc k0
  endpoint_margin : ∀ n,
    Ctube * (Cint * ShadowingTails.tail e n) <
      TubeConstants.kbar k0 - k0
  increment_margin : ∀ n,
    Cinc * (Cint * ShadowingTails.tail e n) <
      TubeConstants.khat k0 - TubeConstants.kbar k0

/-- If the initial defect tail is below `etaStar`, no prefix must be discarded:
both tube margins hold at every subsequent level because nonnegative tails are
antitone. -/
theorem noDiscardCertificate
    {e : ℕ → ℝ} {Cint Ctube Cinc k0 : ℝ}
    (hCint : 0 < Cint) (hCtube : 0 < Ctube) (hCinc : 0 < Cinc)
    (hk : k0 < 1) (he0 : ∀ n, 0 ≤ e n) (hesum : Summable e)
    (hsmall : ShadowingTails.tail e 0 ≤
      TubeConstants.etaStar Cint Ctube Cinc k0) :
    NoDiscardCertificate e Cint Ctube Cinc k0 := by
  refine ⟨etaStar_pos hCint hCtube hCinc hk, ?_, ?_⟩
  · intro n
    have htail : ShadowingTails.tail e n ≤ ShadowingTails.tail e 0 :=
      ShadowingTails.tail_antitone hesum he0 (Nat.zero_le n)
    exact (TubeConstants.etaStar_bounds hCint hCtube hCinc hk
      (htail.trans hsmall)).1
  · intro n
    have htail : ShadowingTails.tail e n ≤ ShadowingTails.tail e 0 :=
      ShadowingTails.tail_antitone hesum he0 (Nat.zero_le n)
    exact (TubeConstants.etaStar_bounds hCint hCtube hCinc hk
      (htail.trans hsmall)).2

section Uniqueness

variable {M : Type*} [MetricSpace M]

/-- An exact inverse orbit lying in the closed metric tubes of radii `r n`
about the pseudo-orbit `Q`. -/
structure OrbitInShrinkingBalls
    (B : M → M) (Q : ℕ → M) (r : ℕ → ℝ) (X : ℕ → M) : Prop where
  inverse_orbit : ∀ n, B (X (n + 1)) = X n
  mem_closedBall : ∀ n, X n ∈ Metric.closedBall (Q n) (r n)

namespace OrbitInShrinkingBalls

theorem dist_le {B : M → M} {Q : ℕ → M} {r : ℕ → ℝ} {X : ℕ → M}
    (H : OrbitInShrinkingBalls B Q r X) (n : ℕ) :
    dist (X n) (Q n) ≤ r n := by
  simpa [Metric.mem_closedBall, dist_comm] using H.mem_closedBall n

/-- Uniqueness in the closures of shrinking tubes.  This is the paper's final
uniqueness argument once the selected inverse is known to be non-expansive in
the metric defining those tubes. -/
theorem unique
    {B : M → M} {Q : ℕ → M} {r : ℕ → ℝ} {X Y : ℕ → M}
    (hB : ∀ x y, dist (B x) (B y) ≤ dist x y)
    (hr : Tendsto r atTop (nhds 0))
    (hX : OrbitInShrinkingBalls B Q r X)
    (hY : OrbitInShrinkingBalls B Q r Y) :
    X = Y :=
  ShadowingScheme.shadowing_orbit_unique hB hX.inverse_orbit hY.inverse_orbit
    hX.dist_le hY.dist_le hr

end OrbitInShrinkingBalls
end Uniqueness

end RegularizingBackwardShadowingNoDiscard
