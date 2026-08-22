import Mathlib
import UnitTangentIterates.MarkedSpace
import UnitTangentIterates.MainTheoremScheme

/-!
# The closing argument on the constructed space of marked curves

`MainTheoremScheme.lean` states the closing step of *A Noncircular Oval with
Convex Unit-Tangent Iterates* from the hypotheses of the shadowing scheme, in
an **abstract** complete metric space `M` of marked ovals: the space, its
Lipschitz evaluation and perimeter, and the fact that its members are ovals
were all assumptions there.

`MarkedSpace.lean` constructs such a space concretely — the tube
`tube c kmin delta` of closed `C²` curves of constant speed at least `c`,
curvature at least `kmin` and chord-arc constant `delta`, in the normalized
parameter — and proves that it is complete, that evaluation and the perimeter
are `1`-Lipschitz on it and that each of its members is an oval.  This file
runs the closing argument **on that space**, so that the only remaining
hypotheses are the dynamical ones:

* a non-expansive continuous selected inverse `B` on the tube with a left
  inverse `T` realizing the unit-tangent transform on curves;
* a model pseudo-orbit `Q` in the tube with summable defects, of perimeter
  `2H` and transverse width at most `C_W`;
* the width gap of the paper's large-separation lemma.

`main_theorem_on_marked_space` then produces an orbit of ovals
`𝒯Xₙ = X_{n+1}` in the tube whose initial member is not a circle.  The
construction of `B` and of the model orbit `Q` is still not carried out; what
this file removes from `MainTheoremScheme.main_theorem_of_scheme` is every
hypothesis about the space itself.
-/

noncomputable section

open Set Filter Topology Function

namespace MarkedSpace

/-- **The closing argument on the constructed space of marked curves.**  On the
tube of `MarkedSpace.lean` — a complete metric space of ovals — a non-expansive
selected inverse `B` with left inverse `T` realizing the unit-tangent transform,
and a model pseudo-orbit `Q` with summable defects, perimeter `2H` and width at
most `C_W`, produce an orbit of ovals `𝒯Xₙ = X_{n+1}` whose initial member is
not a circle.

NOTE (see `UnitTangentIterates/UnitTangentSpeed.lean`).  The orbit condition is
stated here as the identity of *parametrized* curves
`UnitTangent.unitTangentMap (X n) = X (n+1)`.  For a unit-speed curve of
curvature `k` the transform has speed `√(1 + k²) > 1`, so by
`UnitTangentSpeed.not_isOval_unitTangentMap` no oval has an oval as its
unit-tangent image: the combination of `IsOval (X n)` with that identity is
contradictory, and hypotheses of this shape can never be met.  The
geometrically correct statement asks only for equality of the images,
`range (X (n+1)) = range (UnitTangent.unitTangentMap (X n))`, i.e. equality up
to reparametrization; the corrected form of the closing argument is
`MarkedSpace.main_theorem_on_marked_space_range` in
`UnitTangentIterates/MarkedSchemeTheoremRange.lean`.
-/
theorem main_theorem_on_marked_space {c kmin delta : ℝ} (hc : 0 < c) (hkmin : 0 < kmin)
    (hdelta : 0 < delta)
    {B T : tube c kmin delta → tube c kmin delta} {Q : ℕ → tube c kmin delta} {e : ℕ → ℝ}
    {Cw Csh H : ℝ} {dir : ℂ}
    (hB : ∀ x y, dist (B x) (B y) ≤ dist x y) (hBcont : Continuous B)
    (hT : ∀ x, T (B x) = x)
    (hTev : ∀ m : tube c kmin delta,
      ev ((T m : Data)) = UnitTangent.unitTangentMap (ev ((m : Data))))
    (hsum : Summable e)
    (hdef : ∀ n, dist (Q n) (B (Q (n + 1))) ≤ e n)
    (hCsh : 1 ≤ Csh)
    (hPerQ : perim ((Q 0 : tube c kmin delta) : Data) = 2 * H)
    (hdir : ‖dir‖ = 1)
    (hQw : Width.width (range (ev ((Q 0 : tube c kmin delta) : Data))) dir ≤ Cw)
    (hgap : Cw + 2 * (Csh * ShadowingTails.tail e 0)
      < (2 * H - Csh * ShadowingTails.tail e 0) / Real.pi) :
    ∃ (X : ℕ → ℝ → ℂ) (LX : ℝ),
      (∀ n, MainTheoremConditional.IsOval (X n)) ∧
      (∀ n, UnitTangent.unitTangentMap (X n) = X (n + 1)) ∧
      0 < LX ∧ Periodic (X 0) LX ∧
      ¬ ClosingArgument.IsCircleOfPerimeter (range (X 0)) LX := by
  -- the defects are nonnegative, hence so are the tails
  have he : ∀ n, 0 ≤ e n := fun n => le_trans dist_nonneg (hdef n)
  have hr0 : 0 ≤ ShadowingTails.tail e 0 := ShadowingTails.tail_nonneg he 0
  -- the shadowing scheme produces the exact orbit
  obtain ⟨Z, -, horbT, hshadow, hLip, -⟩ :=
    ShadowingScheme.exists_shadowing_orbit_all (T := T) hB hBcont hT hsum hdef
  refine ⟨fun n => ev ((Z n : Data)), perim ((Z 0 : tube c kmin delta) : Data),
    fun n => isOval_ev hc hkmin hdelta (Z n).2, ?_,
    perim_pos hc (Z 0).2, periodic_ev hc (Z 0).2, ?_⟩
  · intro n
    rw [← hTev (Z n), horbT n]
  · -- the closing width argument, run in the normalized parameter
    set d : ℝ := Csh * ShadowingTails.tail e 0 with hd
    have hd0 : 0 ≤ d := mul_nonneg (le_trans zero_le_one hCsh) hr0
    have hdist : ∀ u, dist (((Z 0 : tube c kmin delta) : Data).1 u)
        (((Q 0 : tube c kmin delta) : Data).1 u) ≤ d := by
      intro u
      have h1 := dist_apply_le ((Z 0 : tube c kmin delta) : Data)
        ((Q 0 : tube c kmin delta) : Data) u
      have h2 : dist (Z 0) (Q 0) ≤ ShadowingTails.tail e 0 := hshadow 0
      have h3 : dist ((Z 0 : tube c kmin delta) : Data) ((Q 0 : tube c kmin delta) : Data)
          = dist (Z 0) (Q 0) := (Subtype.dist_eq _ _).symm
      rw [dist_eq_norm]
      nlinarith [dist_nonneg (x := Z 0) (y := Q 0)]
    -- the perimeter of the orbit is close to that of the model
    have hper : 2 * H - d ≤ perim ((Z 0 : tube c kmin delta) : Data) := by
      have h := hLip (fun m => perim ((m : Data))) 1 zero_le_one
        (fun x y => by
          have h1 := abs_perim_sub_le_dist ((x : Data)) ((y : Data))
          have h2 : dist ((x : Data)) ((y : Data)) = dist x y := (Subtype.dist_eq _ _).symm
          rw [one_mul, ← h2]
          exact h1) 0
      rw [hPerQ, one_mul] at h
      have h1 : -(ShadowingTails.tail e 0)
          ≤ perim ((Z 0 : tube c kmin delta) : Data) - 2 * H := (abs_le.mp h).1
      have h2 : ShadowingTails.tail e 0 ≤ d := by
        rw [hd]
        nlinarith
      linarith
    -- the width argument on the images of the normalized parametrizations
    have hrangeZ : range (ev ((Z 0 : tube c kmin delta) : Data))
        = range (⇑((Z 0 : tube c kmin delta) : Data).1) := range_ev hc (Z 0).2
    have hrangeQ : range (ev ((Q 0 : tube c kmin delta) : Data))
        = range (⇑((Q 0 : tube c kmin delta) : Data).1) := range_ev hc (Q 0).2
    rw [hrangeZ]
    rw [hrangeQ] at hQw
    exact CurveDistance.not_isCircleOfPerimeter_of_dist_le (H := H)
      ((Z 0 : tube c kmin delta) : Data).1.continuous (Z 0).2.periodic one_pos
      ((Q 0 : tube c kmin delta) : Data).1.continuous (Q 0).2.periodic one_pos
      hdir hd0 hdist hQw hper hgap

end MarkedSpace
