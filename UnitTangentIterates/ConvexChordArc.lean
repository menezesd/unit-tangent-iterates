import Mathlib
import UnitTangentIterates.ConvexFromTurning

/-!
# A quantitative chord-arc bound for a closed convex curve

Membership in the tube of marked curves of *A Noncircular Oval with Convex
Unit-Tangent Iterates* asks for a quantitative chord-arc bound, a closed form of
embeddedness, and everywhere in this project so far that bound has either been
carried as a hypothesis or produced from embeddedness with a constant depending
on the curve (`ChordArc.lean`).

This file **produces** it, with an explicit constant depending only on the
curvature pinching.  Let `X` be a closed unit-speed curve of period `L` whose
tangent angle `θ` satisfies `0 < kmin ≤ θ' ≤ kmax` and turns by `2π` over one
period.  Put

`ρ = π/(2 kmax)`,  `h₀ = (ρ/2)·sin(kmin ρ/2) > 0`.

Then for all parameters `x, y` of one period

`min(1/2, 2h₀/L) · min(|x−y|, L−|x−y|) ≤ ‖X x − X y‖`.

The proof is the two-scale argument the geometry dictates:

* `chord_near` — near the diagonal the tangent has turned by less than `π/3`,
  so the projection of the chord on the bisecting direction already gives
  `‖X y − X x‖ ≥ (y−x)/2`;
* `chord_far` — for two points joined by an arc of turning at most `π`, the
  distance to the tangent line at the first point increases along that arc, and
  after the arclength `ρ` it is at least `h₀`; the chord is at least that
  distance;
* `chord_arc_of_convex` — one of the two arcs joining two points of a closed
  curve of total turning `2π` has turning at most `π`, and the short arc always
  does, so the two cases cover all pairs.

The constant in the **normalized** parameter (in which the period is one) is
`min(L/2, 2h₀)`, which is bounded below by `min(2ρ, 2h₀)`, independently of the
length: a family of closed curves with one curvature pinching has one chord-arc
constant in the normalized parameter, however long its members are.  That is
exactly the uniformity a single tube of marked curves needs.
-/

noncomputable section

open Real Set

namespace ConvexChordArc

/-- The arclength scale `ρ = π/(2 kmax)` on which the tangent of a curve of
curvature at most `kmax` turns by at most `π/2`. -/
def rhoOf (kmax : ℝ) : ℝ := π / (2 * kmax)

/-- The transverse gain `h₀ = (ρ/2)·sin(kmin ρ/2)`: the distance from the
tangent line reached after the arclength `ρ`. -/
def hZero (kmin kmax : ℝ) : ℝ := rhoOf kmax / 2 * Real.sin (kmin * rhoOf kmax / 2)

/-- The chord-arc constant of a closed convex curve of length `L` with curvature
pinched by `kmin` and `kmax`. -/
def chordConst (kmin kmax L : ℝ) : ℝ := min (1/2) (2 * hZero kmin kmax / L)

/-- The transverse gain is positive. -/
theorem hZero_pos {kmin kmax : ℝ} (hkmin : 0 < kmin) (hle : kmin ≤ kmax) :
    0 < hZero kmin kmax := by
  have hkmax : 0 < kmax := lt_of_lt_of_le hkmin hle
  have hrho : 0 < rhoOf kmax := by rw [rhoOf]; positivity
  have hsin : 0 < Real.sin (kmin * rhoOf kmax / 2) := by
    have h1 : 0 < kmin * rhoOf kmax / 2 := by positivity
    have h2 : kmax * rhoOf kmax = π / 2 := by
      rw [rhoOf]; field_simp
    have h3 : kmin * rhoOf kmax ≤ kmax * rhoOf kmax :=
      mul_le_mul_of_nonneg_right hle hrho.le
    have : kmin * rhoOf kmax / 2 < π := by nlinarith [pi_pos]
    exact Real.sin_pos_of_pos_of_lt_pi h1 this
  rw [hZero]
  positivity

/-- The chord-arc constant is positive. -/
theorem chordConst_pos {kmin kmax L : ℝ} (hkmin : 0 < kmin) (hle : kmin ≤ kmax) (hL : 0 < L) :
    0 < chordConst kmin kmax L := by
  have := hZero_pos hkmin hle
  rw [chordConst]
  exact lt_min (by norm_num) (by positivity)

/-- The projection of a complex number on a unit direction is at most its
modulus. -/
theorem re_mul_exp_le_norm (a : ℝ) (z : ℂ) :
    (z * Complex.exp (-(a : ℂ) * Complex.I)).re ≤ ‖z‖ := by
  have h1 : (z * Complex.exp (-(a : ℂ) * Complex.I)).re
      ≤ ‖z * Complex.exp (-(a : ℂ) * Complex.I)‖ := Complex.re_le_norm _
  have h2 : ‖z * Complex.exp (-(a : ℂ) * Complex.I)‖ = ‖z‖ := by
    rw [norm_mul]
    have hc : (-(a : ℂ) * Complex.I) = ((-a : ℝ) : ℂ) * Complex.I := by push_cast; ring
    rw [hc, Complex.norm_exp_ofReal_mul_I, mul_one]
  linarith [h1, h2.le, h2.ge]

/-- The chord dominates the increment of the projection on any direction. -/
theorem projection_sub_le_norm_sub {X : ℝ → ℂ} (alpha x y : ℝ) :
    (X y * Complex.exp (-(alpha : ℂ) * Complex.I)).re
        - (X x * Complex.exp (-(alpha : ℂ) * Complex.I)).re
      ≤ ‖X y - X x‖ := by
  have h := re_mul_exp_le_norm alpha (X y - X x)
  rwa [sub_mul, Complex.sub_re] at h

/-- A lower bound for the derivative on an interval is a lower bound for the
increment. -/
theorem sub_ge_of_deriv_ge {p p' : ℝ → ℝ} {x y c : ℝ} (hxy : x ≤ y)
    (hp : ∀ u, HasDerivAt p (p' u) u) (hc : ∀ u ∈ Icc x y, c ≤ p' u) :
    c * (y - x) ≤ p y - p x := by
  have hcont : Continuous p := by
    have : Differentiable ℝ p := fun u => (hp u).differentiableAt
    exact this.continuous
  have hmono : MonotoneOn (fun u => p u - c * u) (Icc x y) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (f' := fun u => p' u - c) (convex_Icc x y)
      (by fun_prop) (fun u _ => ?_) (fun u hu => ?_)
    · have hd : HasDerivAt (fun u => p u - c * u) (p' u - c) u := by
        simpa using (hp u).sub ((hasDerivAt_id u).const_mul c)
      exact hd.hasDerivWithinAt
    · have hmem : u ∈ Icc x y := interior_subset hu
      linarith [hc u hmem]
  have h := hmono (left_mem_Icc.2 hxy) (right_mem_Icc.2 hxy) hxy
  simp only at h
  linarith

/-- The tangent angle of a curve of nonnegative curvature is monotone. -/
theorem theta_monotone {theta kappa : ℝ → ℝ} (hth : ∀ s, HasDerivAt theta (kappa s) s)
    (hk : ∀ s, 0 ≤ kappa s) : Monotone theta := by
  have hd : ∀ u ∈ interior (univ : Set ℝ), HasDerivWithinAt theta (kappa u) (interior univ) u :=
    fun u _ => (hth u).hasDerivWithinAt
  have hcont : Continuous theta := by
    have : Differentiable ℝ theta := fun u => (hth u).differentiableAt
    exact this.continuous
  have := monotoneOn_of_hasDerivWithinAt_nonneg (D := (univ : Set ℝ)) convex_univ
    hcont.continuousOn hd (fun u _ => hk u)
  intro a b hab
  exact this (mem_univ a) (mem_univ b) hab

/-- The turning over an interval is between `kmin` and `kmax` times its
length. -/
theorem theta_sub_bounds {theta kappa : ℝ → ℝ} {kmin kmax x y : ℝ}
    (hth : ∀ s, HasDerivAt theta (kappa s) s)
    (hkmin : ∀ s, kmin ≤ kappa s) (hkmax : ∀ s, kappa s ≤ kmax) (hxy : x ≤ y) :
    kmin * (y - x) ≤ theta y - theta x ∧ theta y - theta x ≤ kmax * (y - x) := by
  constructor
  · exact sub_ge_of_deriv_ge hxy hth (fun u _ => hkmin u)
  · have h : -kmax * (y - x) ≤ (-theta y) - (-theta x) :=
      sub_ge_of_deriv_ge hxy (fun s => (hth s).neg) (fun u _ => by
        have := hkmax u
        linarith)
    linarith

/-- **The chord near the diagonal.**  If the tangent turns by at most `2π/3`
between `x` and `y`, the chord is at least half the arclength. -/
theorem chord_near {X : ℝ → ℂ} {theta kappa : ℝ → ℝ} {kmax x y : ℝ}
    (hX : ∀ s, HasDerivAt X (Complex.exp ((theta s : ℂ) * Complex.I)) s)
    (hth : ∀ s, HasDerivAt theta (kappa s) s) (hk0 : ∀ s, 0 ≤ kappa s)
    (hkmax : ∀ s, kappa s ≤ kmax) (hxy : x ≤ y) (hd : kmax * (y - x) ≤ 2 * π / 3) :
    (y - x) / 2 ≤ ‖X y - X x‖ := by
  set tb : ℝ := (theta x + theta y) / 2 with htb
  have hmono := theta_monotone hth hk0
  have hturn : theta y - theta x ≤ 2 * π / 3 :=
    le_trans (theta_sub_bounds (kmin := 0) hth hk0 hkmax hxy).2 hd
  have hcos : ∀ u ∈ Icc x y, (1 : ℝ) / 2 ≤ Real.cos (theta u - tb) := by
    intro u hu
    have h1 : theta x ≤ theta u := hmono hu.1
    have h2 : theta u ≤ theta y := hmono hu.2
    have habs : |theta u - tb| ≤ π / 3 := by
      rw [abs_le]
      constructor <;> [skip; skip] <;> simp only [htb] <;> linarith
    have hpi : (0:ℝ) ≤ |theta u - tb| := abs_nonneg _
    have hle : Real.cos (π / 3) ≤ Real.cos |theta u - tb| :=
      Real.cos_le_cos_of_nonneg_of_le_pi hpi (by linarith [pi_pos]) habs
    rwa [Real.cos_abs, Real.cos_pi_div_three] at hle
  have hp : ∀ u, HasDerivAt (fun r => (X r * Complex.exp (-(tb : ℂ) * Complex.I)).re)
      (Real.cos (theta u - tb)) u := fun u => ConvexFromTurning.hasDerivAt_projection (hX u)
  have hinc := sub_ge_of_deriv_ge (c := (1:ℝ)/2) hxy hp hcos
  have hproj := projection_sub_le_norm_sub (X := X) tb x y
  linarith

/-- **The chord far from the diagonal.**  If the tangent turns by at most `π`
between `x` and `y` and the arclength is at least `ρ`, the chord is at least
`h₀ = (ρ/2)·sin(kmin ρ/2)`: the distance to the tangent line at `X x` grows
along the arc. -/
theorem chord_far {X : ℝ → ℂ} {theta kappa : ℝ → ℝ} {kmin kmax rho x y : ℝ}
    (hX : ∀ s, HasDerivAt X (Complex.exp ((theta s : ℂ) * Complex.I)) s)
    (hth : ∀ s, HasDerivAt theta (kappa s) s)
    (hkmin : ∀ s, kmin ≤ kappa s) (hkmax : ∀ s, kappa s ≤ kmax)
    (hkminpos : 0 < kmin) (hrho : 0 < rho) (hrhomax : kmax * rho ≤ π / 2)
    (hxy : x + rho ≤ y) (hturn : theta y - theta x ≤ π) :
    rho / 2 * Real.sin (kmin * rho / 2) ≤ ‖X y - X x‖ := by
  have hkmax0 : 0 < kmax := lt_of_lt_of_le hkminpos (le_trans (hkmin 0) (hkmax 0))
  have hk0 : ∀ s, 0 ≤ kappa s := fun s => le_trans hkminpos.le (hkmin s)
  have hmono := theta_monotone hth hk0
  set alpha : ℝ := theta x + π / 2 with halpha
  have hp : ∀ u, HasDerivAt (fun r => (X r * Complex.exp (-(alpha : ℂ) * Complex.I)).re)
      (Real.cos (theta u - alpha)) u := fun u => ConvexFromTurning.hasDerivAt_projection (hX u)
  have hsin : ∀ u, Real.cos (theta u - alpha) = Real.sin (theta u - theta x) := by
    intro u
    have : theta u - alpha = (theta u - theta x) - π / 2 := by rw [halpha]; ring
    rw [this, Real.cos_sub_pi_div_two]
  set p : ℝ → ℝ := fun r => (X r * Complex.exp (-(alpha : ℂ) * Complex.I)).re with hpdef
  -- on `[x, y]` the projection is nondecreasing
  have hnonneg : ∀ u ∈ Icc x y, (0:ℝ) ≤ Real.cos (theta u - alpha) := by
    intro u hu
    rw [hsin u]
    have h1 : 0 ≤ theta u - theta x := by linarith [hmono hu.1]
    have h2 : theta u - theta x ≤ π := by linarith [hmono hu.2]
    exact Real.sin_nonneg_of_nonneg_of_le_pi h1 h2
  -- the middle piece of the arc has a positive integrand
  have hmid : ∀ u ∈ Icc (x + rho / 2) (x + rho),
      Real.sin (kmin * rho / 2) ≤ Real.cos (theta u - alpha) := by
    intro u hu
    rw [hsin u]
    have hxu : x ≤ u := by linarith [hu.1]
    have hb := theta_sub_bounds hth hkmin hkmax hxu
    have h1 : kmin * rho / 2 ≤ theta u - theta x := by
      have : kmin * (rho / 2) ≤ kmin * (u - x) := by
        have : rho / 2 ≤ u - x := by linarith [hu.1]
        exact mul_le_mul_of_nonneg_left this hkminpos.le
      linarith [hb.1]
    have h2 : theta u - theta x ≤ π / 2 := by
      have hux : u - x ≤ rho := by linarith [hu.2]
      have : kmax * (u - x) ≤ kmax * rho := mul_le_mul_of_nonneg_left hux hkmax0.le
      linarith [hb.2]
    have h3 : kmin * rho / 2 ≤ π / 2 := le_trans h1 h2
    have h4 : (0:ℝ) ≤ kmin * rho / 2 := by positivity
    exact Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [pi_pos]) h2 h1
  have hstep1 : Real.sin (kmin * rho / 2) * ((x + rho) - (x + rho / 2))
      ≤ p (x + rho) - p (x + rho / 2) :=
    sub_ge_of_deriv_ge (by linarith) hp hmid
  have hstep0 : (0:ℝ) * ((x + rho / 2) - x) ≤ p (x + rho / 2) - p x :=
    sub_ge_of_deriv_ge (by linarith) hp (fun u hu => hnonneg u ⟨hu.1, by linarith [hu.2]⟩)
  have hstep2 : (0:ℝ) * (y - (x + rho)) ≤ p y - p (x + rho) :=
    sub_ge_of_deriv_ge (by linarith) hp (fun u hu => hnonneg u ⟨by linarith [hu.1], hu.2⟩)
  have hproj := projection_sub_le_norm_sub (X := X) alpha x y
  have : rho / 2 * Real.sin (kmin * rho / 2) ≤ p y - p x := by
    have h1 : Real.sin (kmin * rho / 2) * (rho / 2) ≤ p (x + rho) - p (x + rho / 2) := by
      have : (x + rho) - (x + rho / 2) = rho / 2 := by ring
      rwa [this] at hstep1
    nlinarith [hstep0, hstep2]
  linarith [hproj]

/-- **The chord-arc bound of a closed convex curve.**  For a closed unit-speed
curve of period `L`, curvature pinched by `0 < kmin ≤ κ ≤ kmax` and total
turning `2π`, the chord is at least `min(1/2, 2h₀/L)` times the cyclic
arclength, with `ρ = π/(2kmax)` and `h₀ = (ρ/2)·sin(kmin ρ/2)`. -/
theorem chord_arc_of_convex {X : ℝ → ℂ} {theta kappa : ℝ → ℝ} {L kmin kmax : ℝ}
    (hL : 0 < L)
    (hX : ∀ s, HasDerivAt X (Complex.exp ((theta s : ℂ) * Complex.I)) s)
    (hth : ∀ s, HasDerivAt theta (kappa s) s)
    (hkmin : ∀ s, kmin ≤ kappa s) (hkmax : ∀ s, kappa s ≤ kmax) (hkminpos : 0 < kmin)
    (hXper : Function.Periodic X L)
    (hturnL : ∀ s, theta (s + L) = theta s + 2 * π) (x y : ℝ) :
    chordConst kmin kmax L * min |x - y| (L - |x - y|) ≤ ‖X x - X y‖ := by
  simp only [chordConst, hZero, rhoOf]
  have hkmax0 : 0 < kmax := lt_of_lt_of_le hkminpos (le_trans (hkmin 0) (hkmax 0))
  set rho : ℝ := π / (2 * kmax) with hrhodef
  have hrho : 0 < rho := by positivity
  have hrhomax : kmax * rho ≤ π / 2 := by
    have hval : kmax * rho = π / 2 := by
      rw [hrhodef]
      field_simp
    linarith
  set h0 : ℝ := rho / 2 * Real.sin (kmin * rho / 2) with hh0def
  have hsinpos : 0 < Real.sin (kmin * rho / 2) := by
    have h1 : 0 < kmin * rho / 2 := by positivity
    have h2 : kmin * rho / 2 < π := by
      have : kmin * rho ≤ kmax * rho := mul_le_mul_of_nonneg_right
        (le_trans (hkmin 0) (hkmax 0)) hrho.le
      nlinarith [pi_pos]
    exact Real.sin_pos_of_pos_of_lt_pi h1 h2
  have hh0 : 0 < h0 := by rw [hh0def]; positivity
  set dl : ℝ := min (1/2) (2 * h0 / L) with hdldef
  have hdl0 : 0 < dl := lt_min (by norm_num) (by positivity)
  -- the general two-point estimate, for `x ≤ y`
  have key : ∀ a b : ℝ, a ≤ b → dl * min (b - a) (L - (b - a)) ≤ ‖X b - X a‖ := by
    intro a b hab
    set d : ℝ := b - a with hd
    have hd0 : 0 ≤ d := by simp [hd]; linarith
    rcases le_or_gt (min d (L - d)) 0 with hneg | hpos
    · have : dl * min d (L - d) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hdl0.le hneg
      exact le_trans this (norm_nonneg _)
    -- the cyclic distance is at most `L/2`
    have hcycle : min d (L - d) ≤ L / 2 := by
      rcases le_total d (L - d) with h | h
      · have : min d (L - d) = d := min_eq_left h
        rw [this]; linarith
      · have : min d (L - d) = L - d := min_eq_right h
        rw [this]; linarith
    have hdL : d ≤ L := by
      by_contra hc
      push_neg at hc
      have : L - d < 0 := by linarith
      have : min d (L - d) < 0 := lt_of_le_of_lt (min_le_right _ _) this
      linarith
    rcases le_or_gt (min d (L - d)) rho with hsmall | hbig
    · -- near the diagonal: the shorter arc has turning at most `π/2`
      rcases le_total d (L - d) with hle | hle
      · have hdle : d ≤ rho := by rw [min_eq_left hle] at hsmall; exact hsmall
        have hnear := chord_near (X := X) (theta := theta) (kappa := kappa) hX hth
          (fun s => le_trans hkminpos.le (hkmin s)) hkmax hab
          (by
            have : kmax * d ≤ kmax * rho := mul_le_mul_of_nonneg_left hdle hkmax0.le
            nlinarith [pi_pos])
        have hmin : min d (L - d) = d := min_eq_left hle
        rw [hmin, ← hd] at *
        calc dl * d ≤ (1/2) * d := by
              have := min_le_left (1/2 : ℝ) (2 * h0 / L)
              nlinarith
          _ ≤ ‖X b - X a‖ := by rw [hd] at hnear ⊢; linarith [hnear]
      · -- the shorter arc is the complementary one
        have hdle : L - d ≤ rho := by rw [min_eq_right hle] at hsmall; exact hsmall
        have hnear := chord_near (X := X) (theta := theta) (kappa := kappa) hX hth
          (fun s => le_trans hkminpos.le (hkmin s)) hkmax
          (show b ≤ a + L by linarith)
          (by
            have : kmax * ((a + L) - b) ≤ kmax * rho := by
              have : (a + L) - b ≤ rho := by rw [hd] at hdle; linarith
              exact mul_le_mul_of_nonneg_left this hkmax0.le
            nlinarith [pi_pos])
        have hXa : X (a + L) = X a := hXper a
        rw [hXa] at hnear
        have hmin : min d (L - d) = L - d := min_eq_right hle
        rw [hmin]
        have hnorm : ‖X a - X b‖ = ‖X b - X a‖ := norm_sub_rev _ _
        have : (L - d) / 2 ≤ ‖X b - X a‖ := by
          rw [← hnorm]
          have : (a + L) - b = L - d := by rw [hd]; ring
          rwa [this] at hnear
        calc dl * (L - d) ≤ (1/2) * (L - d) := by
              have := min_le_left (1/2 : ℝ) (2 * h0 / L)
              nlinarith [min_le_right d (L - d), hpos]
          _ ≤ ‖X b - X a‖ := by linarith
    · -- far from the diagonal: one of the two arcs has turning at most `π`
      have hfar : h0 ≤ ‖X b - X a‖ := by
        rcases le_total (theta b - theta a) π with hturn | hturn
        · have hd_rho : a + rho ≤ b := by
            have : rho ≤ d := le_trans hbig.le (min_le_left _ _)
            rw [hd] at this; linarith
          exact chord_far hX hth hkmin hkmax hkminpos hrho hrhomax hd_rho hturn
        · have hturn2 : theta (a + L) - theta b ≤ π := by
            rw [hturnL a]; linarith
          have hd_rho : b + rho ≤ a + L := by
            have : rho ≤ L - d := le_trans hbig.le (min_le_right _ _)
            rw [hd] at this; linarith
          have h := chord_far (x := b) (y := a + L) hX hth hkmin hkmax hkminpos hrho hrhomax
            hd_rho hturn2
          rw [hXper a] at h
          rw [norm_sub_rev] at h
          exact h
      have : dl * min d (L - d) ≤ (2 * h0 / L) * (L / 2) := by
        have h1 : dl ≤ 2 * h0 / L := min_le_right _ _
        have h2 : min d (L - d) ≤ L / 2 := hcycle
        have h3 : (0:ℝ) ≤ 2 * h0 / L := by positivity
        nlinarith [hpos]
      have hval : (2 * h0 / L) * (L / 2) = h0 := by field_simp
      rw [hval] at this
      linarith
  rcases le_total x y with hxy | hxy
  · have h := key x y hxy
    have habs : |x - y| = y - x := by rw [abs_sub_comm]; exact abs_of_nonneg (by linarith)
    rw [habs, norm_sub_rev]
    exact h
  · have h := key y x hxy
    have habs : |x - y| = x - y := abs_of_nonneg (by linarith)
    rw [habs]
    exact h

/-- **A closed convex curve with pinched curvature is embedded.**  Distinct
parameters of one period have positive cyclic distance, so the chord-arc bound
makes the curve injective there. -/
theorem injOn_of_convex {X : ℝ → ℂ} {theta kappa : ℝ → ℝ} {L kmin kmax : ℝ}
    (hL : 0 < L)
    (hX : ∀ s, HasDerivAt X (Complex.exp ((theta s : ℂ) * Complex.I)) s)
    (hth : ∀ s, HasDerivAt theta (kappa s) s)
    (hkmin : ∀ s, kmin ≤ kappa s) (hkmax : ∀ s, kappa s ≤ kmax) (hkminpos : 0 < kmin)
    (hXper : Function.Periodic X L)
    (hturnL : ∀ s, theta (s + L) = theta s + 2 * π) :
    Set.InjOn X (Ico 0 L) := by
  have hle : kmin ≤ kmax := le_trans (hkmin 0) (hkmax 0)
  have hc : 0 < chordConst kmin kmax L := chordConst_pos hkminpos hle hL
  intro x hx y hy hxy
  by_contra hne
  have hpos : 0 < min |x - y| (L - |x - y|) := by
    refine lt_min (abs_pos.2 (sub_ne_zero.2 hne)) ?_
    have h1 : |x - y| < L := by
      rw [abs_lt]
      constructor <;> [linarith [hx.1, hx.2, hy.1, hy.2]; linarith [hx.1, hx.2, hy.1, hy.2]]
    linarith
  have h := chord_arc_of_convex hL hX hth hkmin hkmax hkminpos hXper hturnL x y
  rw [hxy, sub_self, norm_zero] at h
  nlinarith

/-! ### The bound is not vacuous -/

/-- **The chord-arc bound for the unit circle.**  Every hypothesis of
`chord_arc_of_convex` holds for `x ↦ e^{ix}`, of tangent angle `x + π/2`,
curvature one and period `2π`. -/
theorem chord_arc_circle (x y : ℝ) :
    chordConst 1 1 (2 * π) * min |x - y| (2 * π - |x - y|)
      ≤ ‖Complex.exp ((x : ℂ) * Complex.I) - Complex.exp ((y : ℂ) * Complex.I)‖ := by
  have hexp : ∀ s : ℝ, Complex.exp (((s + π / 2 : ℝ) : ℂ) * Complex.I)
      = Complex.exp ((s : ℂ) * Complex.I) * Complex.I := by
    intro s
    have hsplit : ((s + π / 2 : ℝ) : ℂ) * Complex.I
        = (s : ℂ) * Complex.I + ((π / 2 : ℝ) : ℂ) * Complex.I := by push_cast; ring
    rw [hsplit, Complex.exp_add]
    congr 1
    rw [Complex.exp_mul_I]
    push_cast
    simp
  refine chord_arc_of_convex (X := fun s : ℝ => Complex.exp ((s : ℂ) * Complex.I))
    (theta := fun s => s + π / 2) (kappa := fun _ => 1) (kmin := 1) (kmax := 1)
    (by positivity) (fun s => ?_) (fun s => ?_) (fun _ => le_rfl) (fun _ => le_rfl)
    (by norm_num) (fun s => ?_) (fun s => by ring) x y
  · have h1 : HasDerivAt (fun s : ℝ => (s : ℂ) * Complex.I) Complex.I s := by
      simpa using (Complex.ofRealCLM.hasDerivAt (x := s)).mul_const Complex.I
    have h2 := h1.cexp
    rw [hexp s]
    simpa using h2
  · simpa using (hasDerivAt_id s).add_const (π / 2)
  · show Complex.exp (((s + 2 * π : ℝ) : ℂ) * Complex.I) = Complex.exp ((s : ℂ) * Complex.I)
    have hsplit : ((s + 2 * π : ℝ) : ℂ) * Complex.I
        = (s : ℂ) * Complex.I + (2 * π : ℂ) * Complex.I := by push_cast; ring
    rw [hsplit, Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]

end ConvexChordArc
