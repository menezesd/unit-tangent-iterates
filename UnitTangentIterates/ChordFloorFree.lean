import UnitTangentIterates.ConvexChordArc

/-!
# The chord bound without a curvature floor

§§47–48 showed that `ConvexChordArc.chord_far` cannot be used on the route the
construction produces: its conclusion `(ρ/2)·sin(kmin·ρ/2)` vanishes with the
floor, and no positive floor is available.  This file replaces it.

The split is by **turning** rather than by arclength, which is what makes the
floor unnecessary:

* `chord_small_turning` — if the tangent turns by at most `π/3`, projecting on
  the tangent direction at `x` gives `(y−x)/2 ≤ ‖X y − X x‖`.  Neither a floor
  nor a ceiling is used.
* `chord_far_of_turning` — if it turns by at least `π/3` (and at most `π`),
  projecting on the *normal* at `x` gives `π/(12·kap)`.  The sub-arc on which
  the tangent has turned between `π/6` and `π/3` has length at least
  `π/(6·kap)` because the curvature is at most `kap`, and on it the projected
  speed is at least `sin(π/6) = 1/2`.
* `chord_bound_floor_free` — the two combined:

  ```
    min((y−x)/2, π/(12·kap)) ≤ ‖X y − X x‖ .
  ```

The floor is replaced by the curvature *ceiling* `kap`, which the construction
supplies: a ceiling forces the turning to take a definite length to happen, and
that length is what the normal projection integrates over.
-/

noncomputable section

set_option maxHeartbeats 4000000

open Set Real

namespace ConvexChordArc


/-- **The chord far from the diagonal, without a curvature floor.**  If the
tangent turns by at least `π/3` and at most `π` between `x` and `y`, the chord
is at least `π/(12·kap)`.  The floor is replaced by the turning hypothesis: the
sub-arc on which the tangent has turned between `π/6` and `π/3` has length at
least `π/(6·kap)`, and on it the projected speed is at least `1/2`. -/
theorem chord_far_of_turning {X : ℝ → ℂ} {theta kappa : ℝ → ℝ} {kap x y : ℝ}
    (hX : ∀ s, HasDerivAt X (Complex.exp ((theta s : ℂ) * Complex.I)) s)
    (hth : ∀ s, HasDerivAt theta (kappa s) s)
    (hk0 : ∀ s, 0 ≤ kappa s) (hkap : ∀ s, kappa s ≤ kap) (hkap0 : 0 < kap)
    (hxy : x ≤ y) (hturn : π / 3 ≤ theta y - theta x)
    (hpi : theta y - theta x ≤ π) :
    π / (12 * kap) ≤ ‖X y - X x‖ := by
  have hmono := theta_monotone hth hk0
  have hcont : Continuous theta :=
    Differentiable.continuous fun u => (hth u).differentiableAt
  set alpha : ℝ := theta x + π / 2 with halpha
  set p : ℝ → ℝ := fun r => (X r * Complex.exp (-(alpha : ℂ) * Complex.I)).re
    with hpdef
  have hp : ∀ u, HasDerivAt p (Real.cos (theta u - alpha)) u := fun u =>
    ConvexFromTurning.hasDerivAt_projection (hX u)
  have hsin : ∀ u, Real.cos (theta u - alpha) = Real.sin (theta u - theta x) := by
    intro u
    have h : theta u - alpha = (theta u - theta x) - π / 2 := by rw [halpha]; ring
    rw [h, Real.cos_sub_pi_div_two]
  have hpi6 : (0:ℝ) < π / 6 := by positivity
  -- locate the sub-arc on which the tangent has turned between π/6 and π/3
  have hmemA : theta x + π / 6 ∈ Icc (theta x) (theta y) := by
    constructor <;> [linarith [hpi6]; linarith [hturn, Real.pi_pos]]
  have hmemB : theta x + π / 3 ∈ Icc (theta x) (theta y) := by
    constructor <;> [linarith [Real.pi_pos]; linarith [hturn]]
  obtain ⟨a, haI, hA⟩ := intermediate_value_Icc hxy hcont.continuousOn hmemA
  obtain ⟨b, hbI, hB⟩ := intermediate_value_Icc hxy hcont.continuousOn hmemB
  have hab : a ≤ b := by
    by_contra hcon
    push_neg at hcon
    have := hmono hcon.le
    rw [hA, hB] at this
    linarith [Real.pi_pos]
  -- the sub-arc is long, because the curvature is at most `kap`
  have hlen : π / (6 * kap) ≤ b - a := by
    have hd := theta_sub_bounds (kmin := 0) hth (fun s => hk0 s) hkap hab
    have h1 : theta b - theta a = π / 6 := by rw [hA, hB]; ring
    have h2 : theta b - theta a ≤ kap * (b - a) := hd.2
    rw [h1] at h2
    rw [div_le_iff₀ (by positivity)]
    linarith [h2]
  -- on the sub-arc the projected speed is at least 1/2
  have hhalf : ∀ u ∈ Icc a b, (1:ℝ) / 2 ≤ Real.cos (theta u - alpha) := by
    intro u hu
    rw [hsin u]
    have h1 : π / 6 ≤ theta u - theta x := by
      have := hmono hu.1; rw [hA] at this; linarith
    have h2 : theta u - theta x ≤ π / 3 := by
      have := hmono hu.2; rw [hB] at this; linarith
    have hle : Real.sin (π / 6) ≤ Real.sin (theta u - theta x) := by
      apply Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [Real.pi_pos])
        (by linarith [Real.pi_pos]) h1
    rwa [Real.sin_pi_div_six] at hle
  -- the projection is nondecreasing on all of `[x,y]`
  have hnonneg : ∀ u ∈ Icc x y, (0:ℝ) ≤ Real.cos (theta u - alpha) := by
    intro u hu
    rw [hsin u]
    exact Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hmono hu.1])
      (by linarith [hmono hu.2])
  have hxa : x ≤ a := haI.1
  have hby : b ≤ y := hbI.2
  have h1 : (0:ℝ) * (a - x) ≤ p a - p x :=
    sub_ge_of_deriv_ge hxa hp (fun u hu => hnonneg u ⟨hu.1, le_trans hu.2 haI.2⟩)
  have h2 : (1/2 : ℝ) * (b - a) ≤ p b - p a := sub_ge_of_deriv_ge hab hp hhalf
  have h3 : (0:ℝ) * (y - b) ≤ p y - p b :=
    sub_ge_of_deriv_ge hby hp (fun u hu =>
      hnonneg u ⟨le_trans (le_trans hxa hab) hu.1, hu.2⟩)
  have hproj := projection_sub_le_norm_sub (X := X) alpha x y
  have hkey : π / (12 * kap) ≤ p y - p x := by
    have : π / (12 * kap) ≤ (1/2 : ℝ) * (b - a) := by
      rw [div_le_iff₀ (by positivity)] at hlen ⊢
      nlinarith [hlen, hkap0]
    linarith [h1, h2, h3, this]
  linarith [hproj, hkey]

/-- **The chord when the tangent turns little.**  If the tangent turns by at
most `π/3`, the projection on the tangent direction at `x` already gives half
the arclength.  No curvature floor and no ceiling are used. -/
theorem chord_small_turning {X : ℝ → ℂ} {theta kappa : ℝ → ℝ} {x y : ℝ}
    (hX : ∀ s, HasDerivAt X (Complex.exp ((theta s : ℂ) * Complex.I)) s)
    (hth : ∀ s, HasDerivAt theta (kappa s) s)
    (hk0 : ∀ s, 0 ≤ kappa s) (hxy : x ≤ y)
    (hturn : theta y - theta x ≤ π / 3) :
    (y - x) / 2 ≤ ‖X y - X x‖ := by
  have hmono := theta_monotone hth hk0
  set alpha : ℝ := theta x with halpha
  set p : ℝ → ℝ := fun r => (X r * Complex.exp (-(alpha : ℂ) * Complex.I)).re
    with hpdef
  have hp : ∀ u, HasDerivAt p (Real.cos (theta u - alpha)) u := fun u =>
    ConvexFromTurning.hasDerivAt_projection (hX u)
  have hhalf : ∀ u ∈ Icc x y, (1:ℝ) / 2 ≤ Real.cos (theta u - alpha) := by
    intro u hu
    have h1 : (0:ℝ) ≤ theta u - alpha := by
      rw [halpha]; linarith [hmono hu.1]
    have h2 : theta u - alpha ≤ π / 3 := by
      rw [halpha]; linarith [hmono hu.2]
    have hle : Real.cos (π / 3) ≤ Real.cos (theta u - alpha) := by
      apply Real.cos_le_cos_of_nonneg_of_le_pi h1 (by linarith [Real.pi_pos]) h2
    rwa [Real.cos_pi_div_three] at hle
  have hkey := sub_ge_of_deriv_ge hxy hp hhalf
  have hproj := projection_sub_le_norm_sub (X := X) alpha x y
  linarith [hproj, hkey]

/-- **The floor-free chord bound.**  Combining the two turning regimes: for any
convex arc on which the tangent turns by at most `π`, the chord is at least
`min((y−x)/2, π/(12·kap))`. -/
theorem chord_bound_floor_free {X : ℝ → ℂ} {theta kappa : ℝ → ℝ} {kap x y : ℝ}
    (hX : ∀ s, HasDerivAt X (Complex.exp ((theta s : ℂ) * Complex.I)) s)
    (hth : ∀ s, HasDerivAt theta (kappa s) s)
    (hk0 : ∀ s, 0 ≤ kappa s) (hkap : ∀ s, kappa s ≤ kap) (hkap0 : 0 < kap)
    (hxy : x ≤ y) (hpi : theta y - theta x ≤ π) :
    min ((y - x) / 2) (π / (12 * kap)) ≤ ‖X y - X x‖ := by
  rcases le_or_gt (theta y - theta x) (π / 3) with hc | hc
  · exact le_trans (min_le_left _ _) (chord_small_turning hX hth hk0 hxy hc)
  · exact le_trans (min_le_right _ _)
      (chord_far_of_turning hX hth hk0 hkap hkap0 hxy hc.le hpi)

end ConvexChordArc
