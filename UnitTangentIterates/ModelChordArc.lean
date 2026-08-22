import Mathlib
import UnitTangentIterates.ConvexChordArc
import UnitTangentIterates.TwoCapPairsAssembly

/-!
# The chord-arc bound of the model fronts, produced

The model curves of the last section of *A Noncircular Oval with Convex
Unit-Tangent Iterates* are the fronts of the exact two-cap pairs, the closed
curves of prescribed curvature built in `CurvatureInterpolation.lean` and
`TwoCapPairsAssembly.lean`.  Putting them into one tube of marked curves
(`TwoCapModelOrbit.lean`) has so far required a **hypothesis**: a quantitative
chord-arc bound, uniform along the family.

`ConvexChordArc.chord_arc_of_convex` now produces such a bound from the
curvature pinching alone, and this file applies it to the model fronts:

* `front_chord_arc` — the front of an admissible curvature (continuous,
  `H`-periodic, pinched by `0 < kmin ≤ κ ≤ kap`, of total turning `π` over one
  period) satisfies the chord-arc bound with the constant
  `ConvexChordArc.chordConst kmin kap (2H)`, which depends only on the pinching
  and the length;
* `modelChordConst` and `model_chord_arc` — for a whole family of such
  curvatures with separations at least `H₀`, one constant works in the
  normalized parameter: the family satisfies the hypothesis `hchord` of
  `TwoCapModelOrbit.lean` and of the closing argument with
  `dlt = min(H₀, 2h₀)/(2H₀) > 0`, `h₀` being the transverse gain of the
  pinching.

So the chord-arc hypothesis of the model orbit is no longer an assumption; see
`MainTheoremModelChord.lean` for the closing argument with it discharged.
-/

noncomputable section

open Real Set Function

namespace ModelChordArc

open TwoCapPairsAssembly CurvatureInterpolation

/-- **The chord-arc bound of a model front.**  The front of a continuous
`H`-periodic curvature pinched by `0 < kmin ≤ κ ≤ kap`, of total turning `π`
over one period, is a closed convex curve of length `2H`, so it obeys the
chord-arc bound of `ConvexChordArc.chord_arc_of_convex`. -/
theorem front_chord_arc {kappa : ℝ → ℝ} {H theta0 kmin kap : ℝ} (hH : 0 < H)
    (hk : Continuous kappa) (hper : Periodic kappa H)
    (hkminpos : 0 < kmin) (hkmin : ∀ s, kmin ≤ kappa s) (hkap : ∀ s, kappa s ≤ kap)
    (htotal : (∫ r in (0:ℝ)..H, kappa r) = π) (x y : ℝ) :
    ConvexChordArc.chordConst kmin kap (2 * H) * min |x - y| (2 * H - |x - y|)
      ≤ ‖front kappa theta0 H x - front kappa theta0 H y‖ := by
  refine ConvexChordArc.chord_arc_of_convex (theta := frontAngle kappa theta0) (kappa := kappa)
    (by linarith) (fun s => ?_) (fun s => hasDerivAt_tangentAngle hk s) hkmin hkap hkminpos
    (front_periodic hk hper htotal) (fun s => ?_) x y
  · have h := front_hasDerivAt (kappa := kappa) (theta0 := theta0) (H := H) hk s
    rwa [mul_comm] at h
  · have h1 := frontAngle_add_halfPeriod (kappa := kappa) (theta0 := theta0) hk hper htotal s
    have h2 := frontAngle_add_halfPeriod (kappa := kappa) (theta0 := theta0) hk hper htotal (s + H)
    have hs : s + 2 * H = s + H + H := by ring
    rw [hs, h2, h1]
    ring

/-- The chord-arc constant of a family of model fronts of separations at least
`H₀`, in the arclength of the first: `min(H₀, 2h₀)/(2H₀)`. -/
def modelChordConst (kmin kap H0 : ℝ) : ℝ :=
  min H0 (2 * ConvexChordArc.hZero kmin kap) / (2 * H0)

/-- The constant is positive. -/
theorem modelChordConst_pos {kmin kap H0 : ℝ} (hkminpos : 0 < kmin) (hle : kmin ≤ kap)
    (hH0 : 0 < H0) : 0 < modelChordConst kmin kap H0 := by
  have h := ConvexChordArc.hZero_pos hkminpos hle
  rw [modelChordConst]
  have : 0 < min H0 (2 * ConvexChordArc.hZero kmin kap) := lt_min hH0 (by linarith)
  positivity

/-- **The uniform chord-arc bound of the family of model fronts.**  This is
exactly the hypothesis `hchord` of `TwoCapModelOrbit.lean` and of the closing
argument, with `dlt = modelChordConst kmin kap H₀`. -/
theorem model_chord_arc {kappas : ℕ → ℝ → ℝ} {Hs theta0 : ℕ → ℝ} {kmin kap : ℝ}
    (hH : ∀ n, 0 < Hs n) (hmono : ∀ n, Hs 0 ≤ Hs n) (hkminpos : 0 < kmin)
    (hk : ∀ n, Continuous (kappas n)) (hper : ∀ n, Periodic (kappas n) (Hs n))
    (hkmin : ∀ n s, kmin ≤ kappas n s) (hkap : ∀ n s, kappas n s ≤ kap)
    (htotal : ∀ n, (∫ r in (0:ℝ)..(Hs n), kappas n r) = π) :
    ∀ n, ∀ x ∈ Icc (0:ℝ) (2 * Hs n), ∀ y ∈ Icc (0:ℝ) (2 * Hs n),
      modelChordConst kmin kap (Hs 0) * (2 * Hs 0) / (2 * Hs n)
          * min |x - y| (2 * Hs n - |x - y|)
        ≤ ‖front (kappas n) (theta0 n) (Hs n) x - front (kappas n) (theta0 n) (Hs n) y‖ := by
  intro n x hx y hy
  have hHn : 0 < Hs n := hH n
  have hH0 : 0 < Hs 0 := hH 0
  have hle : kmin ≤ kap := le_trans (hkmin 0 0) (hkap 0 0)
  have hz := ConvexChordArc.hZero_pos hkminpos hle
  set h0 : ℝ := ConvexChordArc.hZero kmin kap with hh0
  -- the cyclic distance is nonnegative
  have hm0 : 0 ≤ min |x - y| (2 * Hs n - |x - y|) := by
    refine le_min (abs_nonneg _) ?_
    have hxy : |x - y| ≤ 2 * Hs n := by
      rw [abs_le]
      constructor <;> [linarith [hx.1, hx.2, hy.1, hy.2]; linarith [hx.1, hx.2, hy.1, hy.2]]
    linarith
  -- the constant of the family is at most the constant of the `n`-th curve
  have hconst : modelChordConst kmin kap (Hs 0) * (2 * Hs 0) / (2 * Hs n)
      ≤ ConvexChordArc.chordConst kmin kap (2 * Hs n) := by
    have hrw : modelChordConst kmin kap (Hs 0) * (2 * Hs 0) / (2 * Hs n)
        = min (Hs 0) (2 * h0) / (2 * Hs n) := by
      rw [modelChordConst, hh0]
      field_simp
    rw [hrw, ConvexChordArc.chordConst]
    refine le_min ?_ ?_
    · have h1 : min (Hs 0) (2 * h0) ≤ Hs 0 := min_le_left _ _
      have h2 : Hs 0 ≤ Hs n := hmono n
      rw [div_le_iff₀ (by positivity)]
      linarith
    · have h1 : min (Hs 0) (2 * h0) ≤ 2 * h0 := min_le_right _ _
      rw [div_le_div_iff_of_pos_right (by positivity)]
      linarith
  have hfront := front_chord_arc (theta0 := theta0 n) (hH n) (hk n) (hper n) hkminpos
    (hkmin n) (hkap n) (htotal n) x y
  calc modelChordConst kmin kap (Hs 0) * (2 * Hs 0) / (2 * Hs n)
        * min |x - y| (2 * Hs n - |x - y|)
      ≤ ConvexChordArc.chordConst kmin kap (2 * Hs n) * min |x - y| (2 * Hs n - |x - y|) :=
        mul_le_mul_of_nonneg_right hconst hm0
    _ ≤ _ := hfront

/-- **The model front is embedded.**  Its curvature is pinched by
`0 < kmin ≤ κ ≤ kap` and it turns by `2π` over its period `2H`, so the chord-arc
bound of `ConvexChordArc.injOn_of_convex` makes it injective on one period.
This is the embeddedness hypothesis `hinj` carried by `TwoCapMarked.lean`. -/
theorem injOn_front {kappa : ℝ → ℝ} {H theta0 kmin kap : ℝ} (hH : 0 < H)
    (hk : Continuous kappa) (hper : Periodic kappa H)
    (hkminpos : 0 < kmin) (hkmin : ∀ s, kmin ≤ kappa s) (hkap : ∀ s, kappa s ≤ kap)
    (htotal : (∫ r in (0:ℝ)..H, kappa r) = π) :
    InjOn (front kappa theta0 H) (Ico 0 (2 * H)) := by
  refine ConvexChordArc.injOn_of_convex (theta := frontAngle kappa theta0) (kappa := kappa)
    (by linarith) (fun s => ?_) (fun s => hasDerivAt_tangentAngle hk s) hkmin hkap hkminpos
    (front_periodic hk hper htotal) (fun s => ?_)
  · have h := front_hasDerivAt (kappa := kappa) (theta0 := theta0) (H := H) hk s
    rwa [mul_comm] at h
  · have h1 := frontAngle_add_halfPeriod (kappa := kappa) (theta0 := theta0) hk hper htotal s
    have h2 := frontAngle_add_halfPeriod (kappa := kappa) (theta0 := theta0) hk hper htotal (s + H)
    have hs : s + 2 * H = s + H + H := by ring
    rw [hs, h2, h1]
    ring

end ModelChordArc
