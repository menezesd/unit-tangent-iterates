import Mathlib
import UnitTangentIterates.ConvexChordArc

/-!
# The chord-arc bound of a closed convex curve, at variable speed

`ConvexChordArc.lean` produces a quantitative chord-arc bound for a closed
*unit-speed* curve with pinched curvature.  The curves that arise in this
project as **rear tracks** are not unit speed: the rear track `R` of a front `F`
with steering angle `δ` satisfies `R_s = cos δ · e^{iΨ}`, `Ψ_s = sin δ`, so it
is parametrized by the *front* arclength and moves at the speed `cos δ ≤ 1`.

This file repeats the two-scale argument of `ConvexChordArc.lean` for a curve

`X_s = v(s) · e^{iθ(s)}`,  `θ_s = w(s)`,  `0 < vmin ≤ v`,  `0 < wmin ≤ w ≤ wmax`,

closed of period `L` and of total turning `2π`.  With

`ρ = π/(2 wmax)`,  `h₀ = vmin·(ρ/2)·sin(wmin ρ/2)`,

the conclusion is

`min(vmin/2, 2h₀/L) · min(|x−y|, L−|x−y|) ≤ ‖X x − X y‖`,

and in particular `X` is injective on one period (`injOn_of_convex_speed`).

Note that `w` is the turning rate *in the given parameter*; the curvature in the
arclength parameter is `w/v`.  Both bounds are what the rear track supplies
directly, so the statement is used as it stands.
-/

noncomputable section

open Real Set

namespace ConvexChordArcSpeed

open ConvexChordArc

/-- The transverse gain of a curve of speed at least `vmin` and turning rate in
`[wmin, wmax]`: the distance from the tangent line reached after the parameter
increment `ρ = π/(2 wmax)`. -/
def hZeroSpeed (vmin wmin wmax : ℝ) : ℝ := vmin * hZero wmin wmax

/-- The chord-arc constant of a closed convex curve of period `L`, speed at
least `vmin` and turning rate pinched by `wmin` and `wmax`. -/
def chordConstSpeed (vmin wmin wmax L : ℝ) : ℝ :=
  min (vmin / 2) (2 * hZeroSpeed vmin wmin wmax / L)

theorem hZeroSpeed_pos {vmin wmin wmax : ℝ} (hv : 0 < vmin) (hwmin : 0 < wmin)
    (hle : wmin ≤ wmax) : 0 < hZeroSpeed vmin wmin wmax :=
  mul_pos hv (hZero_pos hwmin hle)

theorem chordConstSpeed_pos {vmin wmin wmax L : ℝ} (hv : 0 < vmin) (hwmin : 0 < wmin)
    (hle : wmin ≤ wmax) (hL : 0 < L) : 0 < chordConstSpeed vmin wmin wmax L := by
  have := hZeroSpeed_pos hv hwmin hle
  exact lt_min (by positivity) (by positivity)

/-- The scalar projection of a curve of speed `v` on the direction `e^{iα}` has
derivative `v·cos(θ − α)`. -/
theorem hasDerivAt_projection_speed {X : ℝ → ℂ} {theta v : ℝ → ℝ} {alpha s : ℝ}
    (hX : HasDerivAt X ((v s : ℂ) * Complex.exp ((theta s : ℂ) * Complex.I)) s) :
    HasDerivAt (fun r => (X r * Complex.exp (-(alpha : ℂ) * Complex.I)).re)
      (v s * Real.cos (theta s - alpha)) s := by
  have hmul : HasDerivAt (fun r => X r * Complex.exp (-(alpha : ℂ) * Complex.I))
      ((v s : ℂ) * Complex.exp ((theta s : ℂ) * Complex.I)
        * Complex.exp (-(alpha : ℂ) * Complex.I)) s := hX.mul_const _
  have hre := Complex.reCLM.hasFDerivAt.comp_hasDerivAt s hmul
  have hval : ((v s : ℂ) * Complex.exp ((theta s : ℂ) * Complex.I) *
      Complex.exp (-(alpha : ℂ) * Complex.I)).re = v s * Real.cos (theta s - alpha) := by
    rw [mul_assoc, ← Complex.exp_add]
    have hsum : ((theta s : ℂ) * Complex.I) + (-(alpha : ℂ) * Complex.I)
        = ((theta s - alpha : ℝ) : ℂ) * Complex.I := by
      push_cast
      ring
    rw [hsum, Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]
  have hre' : HasDerivAt (fun r => (X r * Complex.exp (-(alpha : ℂ) * Complex.I)).re)
      (((v s : ℂ) * Complex.exp ((theta s : ℂ) * Complex.I) *
        Complex.exp (-(alpha : ℂ) * Complex.I)).re) s := hre
  rwa [hval] at hre'

/-- **The chord near the diagonal, at variable speed.** -/
theorem chord_near_speed {X : ℝ → ℂ} {theta w v : ℝ → ℝ} {wmax vmin x y : ℝ}
    (hX : ∀ s, HasDerivAt X ((v s : ℂ) * Complex.exp ((theta s : ℂ) * Complex.I)) s)
    (hth : ∀ s, HasDerivAt theta (w s) s) (hw0 : ∀ s, 0 ≤ w s)
    (hwmax : ∀ s, w s ≤ wmax) (hv : ∀ s, vmin ≤ v s) (hvmin : 0 ≤ vmin)
    (hxy : x ≤ y) (hd : wmax * (y - x) ≤ 2 * π / 3) :
    vmin * (y - x) / 2 ≤ ‖X y - X x‖ := by
  set tb : ℝ := (theta x + theta y) / 2 with htb
  have hmono := theta_monotone hth hw0
  have hturn : theta y - theta x ≤ 2 * π / 3 :=
    le_trans (theta_sub_bounds (kmin := 0) hth hw0 hwmax hxy).2 hd
  have hcos : ∀ u ∈ Icc x y, vmin / 2 ≤ v u * Real.cos (theta u - tb) := by
    intro u hu
    have h1 : theta x ≤ theta u := hmono hu.1
    have h2 : theta u ≤ theta y := hmono hu.2
    have habs : |theta u - tb| ≤ π / 3 := by
      rw [abs_le]
      constructor <;> simp only [htb] <;> linarith
    have hpi : (0:ℝ) ≤ |theta u - tb| := abs_nonneg _
    have hle : Real.cos (π / 3) ≤ Real.cos |theta u - tb| :=
      Real.cos_le_cos_of_nonneg_of_le_pi hpi (by linarith [pi_pos]) habs
    rw [Real.cos_abs, Real.cos_pi_div_three] at hle
    nlinarith [hv u]
  have hp : ∀ u, HasDerivAt (fun r => (X r * Complex.exp (-(tb : ℂ) * Complex.I)).re)
      (v u * Real.cos (theta u - tb)) u := fun u => hasDerivAt_projection_speed (hX u)
  have hinc := sub_ge_of_deriv_ge (c := vmin / 2) hxy hp hcos
  have hproj := projection_sub_le_norm_sub (X := X) tb x y
  linarith

/-- **The chord far from the diagonal, at variable speed.** -/
theorem chord_far_speed {X : ℝ → ℂ} {theta w v : ℝ → ℝ} {wmin wmax vmin rho x y : ℝ}
    (hX : ∀ s, HasDerivAt X ((v s : ℂ) * Complex.exp ((theta s : ℂ) * Complex.I)) s)
    (hth : ∀ s, HasDerivAt theta (w s) s)
    (hwmin : ∀ s, wmin ≤ w s) (hwmax : ∀ s, w s ≤ wmax)
    (hv : ∀ s, vmin ≤ v s) (hvmin : 0 ≤ vmin)
    (hwminpos : 0 < wmin) (hrho : 0 < rho) (hrhomax : wmax * rho ≤ π / 2)
    (hxy : x + rho ≤ y) (hturn : theta y - theta x ≤ π) :
    vmin * (rho / 2 * Real.sin (wmin * rho / 2)) ≤ ‖X y - X x‖ := by
  have hwmax0 : 0 < wmax := lt_of_lt_of_le hwminpos (le_trans (hwmin 0) (hwmax 0))
  have hw0 : ∀ s, 0 ≤ w s := fun s => le_trans hwminpos.le (hwmin s)
  have hmono := theta_monotone hth hw0
  set alpha : ℝ := theta x + π / 2 with halpha
  have hp : ∀ u, HasDerivAt (fun r => (X r * Complex.exp (-(alpha : ℂ) * Complex.I)).re)
      (v u * Real.cos (theta u - alpha)) u := fun u => hasDerivAt_projection_speed (hX u)
  have hsin : ∀ u, Real.cos (theta u - alpha) = Real.sin (theta u - theta x) := by
    intro u
    have : theta u - alpha = (theta u - theta x) - π / 2 := by rw [halpha]; ring
    rw [this, Real.cos_sub_pi_div_two]
  set p : ℝ → ℝ := fun r => (X r * Complex.exp (-(alpha : ℂ) * Complex.I)).re with hpdef
  have hnonneg : ∀ u ∈ Icc x y, (0:ℝ) ≤ v u * Real.cos (theta u - alpha) := by
    intro u hu
    rw [hsin u]
    have h1 : 0 ≤ theta u - theta x := by linarith [hmono hu.1]
    have h2 : theta u - theta x ≤ π := by linarith [hmono hu.2]
    have := Real.sin_nonneg_of_nonneg_of_le_pi h1 h2
    nlinarith [hv u]
  have hmid : ∀ u ∈ Icc (x + rho / 2) (x + rho),
      vmin * Real.sin (wmin * rho / 2) ≤ v u * Real.cos (theta u - alpha) := by
    intro u hu
    rw [hsin u]
    have hxu : x ≤ u := by linarith [hu.1]
    have hb := theta_sub_bounds hth hwmin hwmax hxu
    have h1 : wmin * rho / 2 ≤ theta u - theta x := by
      have : wmin * (rho / 2) ≤ wmin * (u - x) := by
        have : rho / 2 ≤ u - x := by linarith [hu.1]
        exact mul_le_mul_of_nonneg_left this hwminpos.le
      linarith [hb.1]
    have h2 : theta u - theta x ≤ π / 2 := by
      have hux : u - x ≤ rho := by linarith [hu.2]
      have : wmax * (u - x) ≤ wmax * rho := mul_le_mul_of_nonneg_left hux hwmax0.le
      linarith [hb.2]
    have h4 : (0:ℝ) ≤ wmin * rho / 2 := by positivity
    have hs := Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [pi_pos]) h2 h1
    have hsnn : (0:ℝ) ≤ Real.sin (wmin * rho / 2) :=
      Real.sin_nonneg_of_nonneg_of_le_pi h4 (by linarith [pi_pos])
    nlinarith [hv u]
  have hstep1 : vmin * Real.sin (wmin * rho / 2) * ((x + rho) - (x + rho / 2))
      ≤ p (x + rho) - p (x + rho / 2) :=
    sub_ge_of_deriv_ge (by linarith) hp hmid
  have hstep0 : (0:ℝ) * ((x + rho / 2) - x) ≤ p (x + rho / 2) - p x :=
    sub_ge_of_deriv_ge (by linarith) hp (fun u hu => hnonneg u ⟨hu.1, by linarith [hu.2]⟩)
  have hstep2 : (0:ℝ) * (y - (x + rho)) ≤ p y - p (x + rho) :=
    sub_ge_of_deriv_ge (by linarith) hp (fun u hu => hnonneg u ⟨by linarith [hu.1], hu.2⟩)
  have hproj := projection_sub_le_norm_sub (X := X) alpha x y
  have hkey : vmin * (rho / 2 * Real.sin (wmin * rho / 2)) ≤ p y - p x := by
    have h1 : vmin * Real.sin (wmin * rho / 2) * (rho / 2) ≤ p (x + rho) - p (x + rho / 2) := by
      have hxx : (x + rho) - (x + rho / 2) = rho / 2 := by ring
      rwa [hxx] at hstep1
    nlinarith [hstep0, hstep2]
  linarith [hproj]

/-- **The chord-arc bound of a closed convex curve at variable speed.**  For a
closed curve of period `L` with `X_s = v e^{iθ}`, `θ_s = w`, `0 < vmin ≤ v`,
`0 < wmin ≤ w ≤ wmax` and total turning `2π`, the chord is at least
`min(vmin/2, 2h₀/L)` times the cyclic parameter distance, with
`ρ = π/(2 wmax)` and `h₀ = vmin·(ρ/2)·sin(wmin ρ/2)`. -/
theorem chord_arc_of_convex_speed {X : ℝ → ℂ} {theta w v : ℝ → ℝ} {L vmin wmin wmax : ℝ}
    (hL : 0 < L)
    (hX : ∀ s, HasDerivAt X ((v s : ℂ) * Complex.exp ((theta s : ℂ) * Complex.I)) s)
    (hth : ∀ s, HasDerivAt theta (w s) s)
    (hwmin : ∀ s, wmin ≤ w s) (hwmax : ∀ s, w s ≤ wmax) (hwminpos : 0 < wmin)
    (hv : ∀ s, vmin ≤ v s) (hvminpos : 0 < vmin)
    (hXper : Function.Periodic X L)
    (hturnL : ∀ s, theta (s + L) = theta s + 2 * π) (x y : ℝ) :
    chordConstSpeed vmin wmin wmax L * min |x - y| (L - |x - y|) ≤ ‖X x - X y‖ := by
  simp only [chordConstSpeed, hZeroSpeed, hZero, rhoOf]
  have hwmax0 : 0 < wmax := lt_of_lt_of_le hwminpos (le_trans (hwmin 0) (hwmax 0))
  set rho : ℝ := π / (2 * wmax) with hrhodef
  have hrho : 0 < rho := by positivity
  have hrhomax : wmax * rho ≤ π / 2 := by
    have hval : wmax * rho = π / 2 := by
      rw [hrhodef]
      field_simp
    linarith
  set h0 : ℝ := vmin * (rho / 2 * Real.sin (wmin * rho / 2)) with hh0def
  have hsinpos : 0 < Real.sin (wmin * rho / 2) := by
    have h1 : 0 < wmin * rho / 2 := by positivity
    have h2 : wmin * rho / 2 < π := by
      have : wmin * rho ≤ wmax * rho := mul_le_mul_of_nonneg_right
        (le_trans (hwmin 0) (hwmax 0)) hrho.le
      nlinarith [pi_pos]
    exact Real.sin_pos_of_pos_of_lt_pi h1 h2
  have hh0 : 0 < h0 := by rw [hh0def]; positivity
  set dl : ℝ := min (vmin / 2) (2 * h0 / L) with hdldef
  have hdl0 : 0 < dl := lt_min (by positivity) (by positivity)
  have key : ∀ a b : ℝ, a ≤ b → dl * min (b - a) (L - (b - a)) ≤ ‖X b - X a‖ := by
    intro a b hab
    set d : ℝ := b - a with hd
    have hd0 : 0 ≤ d := by simp [hd]; linarith
    rcases le_or_gt (min d (L - d)) 0 with hneg | hpos
    · have : dl * min d (L - d) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hdl0.le hneg
      exact le_trans this (norm_nonneg _)
    have hcycle : min d (L - d) ≤ L / 2 := by
      rcases le_total d (L - d) with h | h
      · have : min d (L - d) = d := min_eq_left h
        rw [this]; linarith
      · have : min d (L - d) = L - d := min_eq_right h
        rw [this]; linarith
    have hdL : d ≤ L := by
      by_contra hc
      push_neg at hc
      have h1 : L - d < 0 := by linarith
      have : min d (L - d) < 0 := lt_of_le_of_lt (min_le_right _ _) h1
      linarith
    rcases le_or_gt (min d (L - d)) rho with hsmall | hbig
    · rcases le_total d (L - d) with hle | hle
      · have hdle : d ≤ rho := by rw [min_eq_left hle] at hsmall; exact hsmall
        have hnear := chord_near_speed (X := X) (theta := theta) (w := w) (v := v) hX hth
          (fun s => le_trans hwminpos.le (hwmin s)) hwmax hv hvminpos.le hab
          (by
            have : wmax * d ≤ wmax * rho := mul_le_mul_of_nonneg_left hdle hwmax0.le
            nlinarith [pi_pos])
        have hmin : min d (L - d) = d := min_eq_left hle
        rw [hmin, ← hd] at *
        calc dl * d ≤ (vmin / 2) * d := by
              have := min_le_left (vmin / 2) (2 * h0 / L)
              nlinarith
          _ ≤ ‖X b - X a‖ := by rw [hd] at hnear ⊢; linarith [hnear]
      · have hdle : L - d ≤ rho := by rw [min_eq_right hle] at hsmall; exact hsmall
        have hnear := chord_near_speed (X := X) (theta := theta) (w := w) (v := v) hX hth
          (fun s => le_trans hwminpos.le (hwmin s)) hwmax hv hvminpos.le
          (show b ≤ a + L by linarith)
          (by
            have : wmax * ((a + L) - b) ≤ wmax * rho := by
              have : (a + L) - b ≤ rho := by rw [hd] at hdle; linarith
              exact mul_le_mul_of_nonneg_left this hwmax0.le
            nlinarith [pi_pos])
        have hXa : X (a + L) = X a := hXper a
        rw [hXa] at hnear
        have hmin : min d (L - d) = L - d := min_eq_right hle
        rw [hmin]
        have hnorm : ‖X a - X b‖ = ‖X b - X a‖ := norm_sub_rev _ _
        have hfin : vmin * (L - d) / 2 ≤ ‖X b - X a‖ := by
          rw [← hnorm]
          have hxx : (a + L) - b = L - d := by rw [hd]; ring
          rwa [hxx] at hnear
        calc dl * (L - d) ≤ (vmin / 2) * (L - d) := by
              have := min_le_left (vmin / 2) (2 * h0 / L)
              nlinarith [min_le_right d (L - d), hpos]
          _ ≤ ‖X b - X a‖ := by linarith
    · have hfar : h0 ≤ ‖X b - X a‖ := by
        rcases le_total (theta b - theta a) π with hturn | hturn
        · have hd_rho : a + rho ≤ b := by
            have : rho ≤ d := le_trans hbig.le (min_le_left _ _)
            rw [hd] at this; linarith
          exact chord_far_speed hX hth hwmin hwmax hv hvminpos.le hwminpos hrho hrhomax
            hd_rho hturn
        · have hturn2 : theta (a + L) - theta b ≤ π := by
            rw [hturnL a]; linarith
          have hd_rho : b + rho ≤ a + L := by
            have : rho ≤ L - d := le_trans hbig.le (min_le_right _ _)
            rw [hd] at this; linarith
          have h := chord_far_speed (x := b) (y := a + L) hX hth hwmin hwmax hv hvminpos.le
            hwminpos hrho hrhomax hd_rho hturn2
          rw [hXper a] at h
          rw [norm_sub_rev] at h
          exact h
      have hb : dl * min d (L - d) ≤ (2 * h0 / L) * (L / 2) := by
        have h1 : dl ≤ 2 * h0 / L := min_le_right _ _
        have h2 : min d (L - d) ≤ L / 2 := hcycle
        have h3 : (0:ℝ) ≤ 2 * h0 / L := by positivity
        nlinarith [hpos]
      have hval : (2 * h0 / L) * (L / 2) = h0 := by field_simp
      rw [hval] at hb
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

/-- **A closed convex curve of positive speed and pinched turning is
embedded.** -/
theorem injOn_of_convex_speed {X : ℝ → ℂ} {theta w v : ℝ → ℝ} {L vmin wmin wmax : ℝ}
    (hL : 0 < L)
    (hX : ∀ s, HasDerivAt X ((v s : ℂ) * Complex.exp ((theta s : ℂ) * Complex.I)) s)
    (hth : ∀ s, HasDerivAt theta (w s) s)
    (hwmin : ∀ s, wmin ≤ w s) (hwmax : ∀ s, w s ≤ wmax) (hwminpos : 0 < wmin)
    (hv : ∀ s, vmin ≤ v s) (hvminpos : 0 < vmin)
    (hXper : Function.Periodic X L)
    (hturnL : ∀ s, theta (s + L) = theta s + 2 * π) :
    Set.InjOn X (Ico 0 L) := by
  have hle : wmin ≤ wmax := le_trans (hwmin 0) (hwmax 0)
  have hc : 0 < chordConstSpeed vmin wmin wmax L := chordConstSpeed_pos hvminpos hwminpos hle hL
  intro x hx y hy hxy
  by_contra hne
  have hpos : 0 < min |x - y| (L - |x - y|) := by
    refine lt_min (abs_pos.2 (sub_ne_zero.2 hne)) ?_
    have h1 : |x - y| < L := by
      rw [abs_lt]
      constructor <;> [linarith [hx.1, hx.2, hy.1, hy.2]; linarith [hx.1, hx.2, hy.1, hy.2]]
    linarith
  have h := chord_arc_of_convex_speed hL hX hth hwmin hwmax hwminpos hv hvminpos hXper hturnL x y
  rw [hxy, sub_self, norm_zero] at h
  nlinarith

end ConvexChordArcSpeed
