import UnitTangentIterates.MarkedSchemeTheoremRange
import UnitTangentIterates.UnconditionalAssemblyRemainder

/-!
# The closing theorem without a curvature floor

§§47–48 showed that `main_theorem_on_marked_space_range`'s hypothesis
`0 < kmin` cannot be met by the construction: total turning `π` on separations
that grow without bound forces the curvature infimum to zero.

This file restates the theorem on the floor-free tube.  The floor was used in
exactly one place — `isOval_ev`, to know the limits are ovals — and
`UnconditionalAssembly.isOval_ev_of_limitStrictnessData` already supplies that
conclusion from `IsTubeMember c 0 dlt` plus `LimitStrictnessData`, where strict
positivity of the curvature is *derived* from convexity of the next
unit-tangent track rather than assumed.

So `main_theorem_on_marked_space_range_floor_free` takes the tube with
`kmin = 0` — the closed condition `0 ≤ κ` — together with the strictness data,
and concludes exactly what the original did.  Nothing else in the proof changes;
the shadowing scheme and the closing width argument never looked at the floor.
-/

noncomputable section

set_option maxHeartbeats 4000000

open Set Filter Topology Function

namespace MarkedSpace

theorem main_theorem_on_marked_space_range_floor_free {c delta : ℝ}
    (hc : 0 < c) (hdelta : 0 < delta)
    (hstrict : ∀ p : tube c 0 delta,
      Nonempty (UnconditionalAssembly.LimitStrictnessData ((p : Data))))
    {B T : tube c 0 delta → tube c 0 delta} {Q : ℕ → tube c 0 delta} {e : ℕ → ℝ}
    {Cw Csh H : ℝ} {dir : ℂ}
    (hB : ∀ x y, dist (B x) (B y) ≤ dist x y) (hBcont : Continuous B)
    (hT : ∀ x, T (B x) = x)
    (hTev : ∀ m : tube c 0 delta,
      range (ev ((T m : Data))) = range (UnitTangent.unitTangentMap (ev ((m : Data)))))
    (hsum : Summable e)
    (hdef : ∀ n, dist (Q n) (B (Q (n + 1))) ≤ e n)
    (hCsh : 1 ≤ Csh)
    (hPerQ : perim ((Q 0 : tube c 0 delta) : Data) = 2 * H)
    (hdir : ‖dir‖ = 1)
    (hQw : Width.width (range (ev ((Q 0 : tube c 0 delta) : Data))) dir ≤ Cw)
    (hgap : Cw + 2 * (Csh * ShadowingTails.tail e 0)
      < (2 * H - Csh * ShadowingTails.tail e 0) / Real.pi) :
    ∃ (X : ℕ → ℝ → ℂ) (LX : ℝ),
      (∀ n, MainTheoremConditional.IsOval (X n)) ∧
      (∀ n, range (X (n + 1)) = range (UnitTangent.unitTangentMap (X n))) ∧
      0 < LX ∧ Periodic (X 0) LX ∧
      ¬ ClosingArgument.IsCircleOfPerimeter (range (X 0)) LX := by
  -- the defects are nonnegative, hence so are the tails
  have he : ∀ n, 0 ≤ e n := fun n => le_trans dist_nonneg (hdef n)
  have hr0 : 0 ≤ ShadowingTails.tail e 0 := ShadowingTails.tail_nonneg he 0
  -- the shadowing scheme produces the exact orbit
  obtain ⟨Z, -, horbT, hshadow, hLip, -⟩ :=
    ShadowingScheme.exists_shadowing_orbit_all (T := T) hB hBcont hT hsum hdef
  refine ⟨fun n => ev ((Z n : Data)), perim ((Z 0 : tube c 0 delta) : Data),
    fun n => UnconditionalAssembly.isOval_ev_of_limitStrictnessData hc hdelta
      (Z n).2 (hstrict (Z n)).some, ?_,
    perim_pos hc (Z 0).2, periodic_ev hc (Z 0).2, ?_⟩
  · intro n
    show range (ev ((Z (n + 1) : tube c 0 delta) : Data))
      = range (UnitTangent.unitTangentMap (ev ((Z n : tube c 0 delta) : Data)))
    rw [← horbT n, hTev (Z n)]
  · -- the closing width argument, run in the normalized parameter
    set d : ℝ := Csh * ShadowingTails.tail e 0 with hd
    have hd0 : 0 ≤ d := mul_nonneg (le_trans zero_le_one hCsh) hr0
    have hdist : ∀ u, dist (((Z 0 : tube c 0 delta) : Data).1 u)
        (((Q 0 : tube c 0 delta) : Data).1 u) ≤ d := by
      intro u
      have h1 := dist_apply_le ((Z 0 : tube c 0 delta) : Data)
        ((Q 0 : tube c 0 delta) : Data) u
      have h2 : dist (Z 0) (Q 0) ≤ ShadowingTails.tail e 0 := hshadow 0
      have h3 : dist ((Z 0 : tube c 0 delta) : Data) ((Q 0 : tube c 0 delta) : Data)
          = dist (Z 0) (Q 0) := (Subtype.dist_eq _ _).symm
      rw [dist_eq_norm]
      nlinarith [dist_nonneg (x := Z 0) (y := Q 0)]
    -- the perimeter of the orbit is close to that of the model
    have hper : 2 * H - d ≤ perim ((Z 0 : tube c 0 delta) : Data) := by
      have h := hLip (fun m => perim ((m : Data))) 1 zero_le_one
        (fun x y => by
          have h1 := abs_perim_sub_le_dist ((x : Data)) ((y : Data))
          have h2 : dist ((x : Data)) ((y : Data)) = dist x y := (Subtype.dist_eq _ _).symm
          rw [one_mul, ← h2]
          exact h1) 0
      rw [hPerQ, one_mul] at h
      have h1 : -(ShadowingTails.tail e 0)
          ≤ perim ((Z 0 : tube c 0 delta) : Data) - 2 * H := (abs_le.mp h).1
      have h2 : ShadowingTails.tail e 0 ≤ d := by
        rw [hd]
        nlinarith
      linarith
    -- the width argument on the images of the normalized parametrizations
    have hrangeZ : range (ev ((Z 0 : tube c 0 delta) : Data))
        = range (⇑((Z 0 : tube c 0 delta) : Data).1) := range_ev hc (Z 0).2
    have hrangeQ : range (ev ((Q 0 : tube c 0 delta) : Data))
        = range (⇑((Q 0 : tube c 0 delta) : Data).1) := range_ev hc (Q 0).2
    rw [hrangeZ]
    rw [hrangeQ] at hQw
    exact CurveDistance.not_isCircleOfPerimeter_of_dist_le (H := H)
      ((Z 0 : tube c 0 delta) : Data).1.continuous (Z 0).2.periodic one_pos
      ((Q 0 : tube c 0 delta) : Data).1.continuous (Q 0).2.periodic one_pos
      hdir hd0 hdist hQw hper hgap
end MarkedSpace
