import UnitTangentIterates.ChordFloorFree
import UnitTangentIterates.ChordArc

/-!
# A uniform chord-arc constant from a curvature ceiling
-/

noncomputable section

set_option maxHeartbeats 1000000

open Set Function Real

namespace ConvexChordArc

/-- **The uniform chord bound of a closed convex curve of total turning `2π`.**

`chord_bound_floor_free` needs the arc `[x,y]` to turn by at most `π`.  That is
not automatic — the turning of a short arc can be almost all of the `2π` — but
it never fails on *both* an arc and its complement, and the two subtend the same
chord.  So one of the two applications always goes through, and the resulting
constant depends only on the curvature ceiling `kap` and the period `L`:

  `min (cyclic gap / 2) (π / (12 kap)) ≤ ‖X y - X x‖`.

This is the uniformity the orbit argument needs: no compactness, no appeal to
injectivity, and nothing depending on the individual curve. -/
theorem chord_uniform_of_turning {X : ℝ → ℂ} {theta kappa : ℝ → ℝ} {kap L x y : ℝ}
    (hkap0 : 0 < kap)
    (hX : ∀ s, HasDerivAt X (Complex.exp ((theta s : ℂ) * Complex.I)) s)
    (hth : ∀ s, HasDerivAt theta (kappa s) s)
    (hk0 : ∀ s, 0 ≤ kappa s) (hkap : ∀ s, kappa s ≤ kap)
    (hper : Periodic X L)
    (hturn : ∀ s, theta (s + L) = theta s + 2 * π)
    (hxy : x ≤ y) (hyx : y - x ≤ L) :
    min (min (y - x) (L - (y - x)) / 2) (π / (12 * kap)) ≤ ‖X y - X x‖ := by
  rcases le_or_gt (theta y - theta x) π with hc | hc
  · -- the arc itself turns by at most `π`
    refine le_trans ?_ (chord_bound_floor_free hX hth hk0 hkap hkap0 hxy hc)
    refine min_le_min ?_ (le_refl _)
    linarith [min_le_left (y - x) (L - (y - x))]
  · -- the complementary arc turns by at most `π`, and subtends the same chord
    have hxy' : y ≤ x + L := by linarith
    have hturn' : theta (x + L) - theta y ≤ π := by
      rw [hturn x]; linarith
    have hchord := chord_bound_floor_free hX hth hk0 hkap hkap0 hxy' hturn'
    have hXeq : X (x + L) = X x := hper x
    rw [hXeq] at hchord
    have hnorm : ‖X x - X y‖ = ‖X y - X x‖ := norm_sub_rev _ _
    rw [hnorm] at hchord
    refine le_trans ?_ hchord
    refine min_le_min ?_ (le_refl _)
    have : min (y - x) (L - (y - x)) ≤ L - (y - x) := min_le_right _ _
    have hEq : x + L - y = L - (y - x) := by ring
    rw [hEq]
    linarith

end ConvexChordArc

namespace Marked

open MarkedSpace

theorem cyc_le_half (u v : ℝ) : MarkedSpace.cyc u v ≤ 1 / 2 := by
  rcases le_or_gt |u - v| (1 / 2) with h | h
  · exact le_trans (min_le_left _ _) h
  · exact le_trans (min_le_right _ _) (by linarith)

/-- **A uniform chord-arc constant for a member of the tube.**  Any tube member
whose arclength curvature is nonnegative, bounded above by `kap`, and of total
turning `2π` over a period satisfies the tube's chord-arc bound with the
constant `min (perim p / 2) (π / (6 kap))` — a function of the perimeter and the
curvature ceiling only.

`ChordArc.exists_chord_arc` also produces a chord constant, but by compactness,
so the constant it produces depends on the individual curve.  Along an orbit
that is not enough: the closing chain needs one `dlt` valid at every level. -/
theorem chord_of_tube_curvature_ceiling {c dlt kap : ℝ} (hc : 0 < c) {p : Data}
    (hp : IsTubeMember c 0 dlt p) (hkap0 : 0 < kap) {Theta K : ℝ → ℝ}
    (hX : ∀ s, HasDerivAt (ev p) (Complex.exp ((Theta s : ℂ) * Complex.I)) s)
    (hth : ∀ s, HasDerivAt Theta (K s) s)
    (hk0 : ∀ s, 0 ≤ K s) (hkap : ∀ s, K s ≤ kap)
    (hturn : ∀ s, Theta (s + perim p) = Theta s + 2 * π) :
    ∀ u ∈ Icc (0:ℝ) 1, ∀ v ∈ Icc (0:ℝ) 1,
      min (perim p / 2) (π / (6 * kap)) * MarkedSpace.cyc u v ≤ ‖p.1 u - p.1 v‖ := by
  set L : ℝ := perim p with hLdef
  have hLpos : 0 < L := perim_pos hc hp
  have hperX : Periodic (ev p) L := periodic_ev hc hp
  have hev : ∀ w : ℝ, ev p (L * w) = p.1 w := by
    intro w
    simp only [ev]
    rw [mul_comm, mul_div_assoc, div_self (ne_of_gt hLpos), mul_one]
  -- the statement is symmetric in `u` and `v`, so assume `u ≤ v`
  have key : ∀ u v : ℝ, u ∈ Icc (0:ℝ) 1 → v ∈ Icc (0:ℝ) 1 → u ≤ v →
      min (L / 2) (π / (6 * kap)) * MarkedSpace.cyc u v ≤ ‖p.1 u - p.1 v‖ := by
    intro u v hu hv huv
    have hxy : L * u ≤ L * v := by nlinarith [hLpos]
    have hgap : L * v - L * u ≤ L := by nlinarith [hu.1, hv.2, hLpos]
    have hmain := ConvexChordArc.chord_uniform_of_turning hkap0 hX hth hk0 hkap
      hperX hturn hxy hgap
    rw [hev, hev] at hmain
    -- the cyclic gap in arclength is `L` times the cyclic gap in the parameter
    have habs : |u - v| = v - u := by rw [abs_sub_comm, abs_of_nonneg (by linarith)]
    have hmin : min (L * v - L * u) (L - (L * v - L * u))
        = L * MarkedSpace.cyc u v := by
      rw [MarkedSpace.cyc, habs, mul_min_of_nonneg _ _ hLpos.le]
      ring_nf
    rw [hmin] at hmain
    refine le_trans ?_ (le_trans hmain (le_of_eq (norm_sub_rev _ _)))
    have hcyc0 : 0 ≤ MarkedSpace.cyc u v := ChordArc.cyc_nonneg hu hv
    refine le_min ?_ ?_
    · have : min (L / 2) (π / (6 * kap)) ≤ L / 2 := min_le_left _ _
      nlinarith
    · have h1 : min (L / 2) (π / (6 * kap)) ≤ π / (6 * kap) := min_le_right _ _
      have h2 : MarkedSpace.cyc u v ≤ 1 / 2 := cyc_le_half u v
      have h3 : (0:ℝ) < 6 * kap := by linarith
      have h4 : min (L / 2) (π / (6 * kap)) * MarkedSpace.cyc u v
          ≤ (π / (6 * kap)) * (1 / 2) := by
        refine le_trans (mul_le_mul_of_nonneg_right h1 hcyc0) ?_
        exact mul_le_mul_of_nonneg_left h2 (by positivity)
      have h5 : (π / (6 * kap)) * (1 / 2) = π / (12 * kap) := by field_simp; ring
      linarith [h4, h5.le, h5.ge]
  intro u hu v hv
  rcases le_total u v with h | h
  · exact key u v hu hv h
  · rw [norm_sub_rev, ChordArc.cyc_comm]
    exact key v u hv hu h

end Marked
