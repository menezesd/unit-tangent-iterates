import Mathlib
import UnitTangentIterates.MarkedSpace
import UnitTangentIterates.MarkedReparam

/-!
# Closed regular curves are marked curves

`MarkedSpace.lean` constructs the space of marked curves of *A Noncircular
Oval with Convex Unit-Tangent Iterates* as a tube of closed `C²` curves
**already carried in the normalized parameter**, and `MarkedReparam.lean`
reparametrizes an arbitrary closed regular `C²` curve at constant speed.  This
file joins the two: a closed regular `C²` curve with curvature at least `kmin`
and a chord-arc bound is, after reparametrization, a member of the tube, with
the same image and with perimeter its length.

The chord-arc hypothesis is the standard one: the chord `‖g x − g y‖` is at
least `delta` times the arclength distance between the parameters on the closed
curve, `min(|ℓ(x)−ℓ(y)|, L−|ℓ(x)−ℓ(y)|)`.

Main results:

* `exists_bound_of_periodic` : a continuous periodic function is bounded;
* `mem_tube_of_regular_closed_curve` : **a closed regular `C²` curve with
  positive curvature and a chord-arc bound is a marked curve**.
-/

noncomputable section

open Set Function Filter Topology
open scoped BoundedContinuousFunction

namespace MarkedSpace

/-- A continuous periodic function is bounded. -/
theorem exists_bound_of_periodic {f : ℝ → ℂ} (hf : Continuous f) (hp : Periodic f 1) :
    ∃ C, ∀ x, ‖f x‖ ≤ C := by
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    hf.continuousOn
  refine ⟨C, fun x => ?_⟩
  obtain ⟨y, hy, hxy⟩ := hp.exists_mem_Ico₀ one_pos x
  rw [hxy]
  exact hC y (Ico_subset_Icc_self hy)

/-- **A closed regular `C²` curve is a marked curve.**  If `g` is a closed
curve of period one with velocity `V`, acceleration `A`, speed at least
`c > 0`, curvature at least `kmin`, and satisfies the chord-arc bound with
constant `delta`, then its constant-speed reparametrization is a member of the
tube of marked curves, with the same image, and its perimeter is the length of
`g`. -/
theorem mem_tube_of_regular_closed_curve {g V A : ℝ → ℂ} {c kmin delta : ℝ} (hc : 0 < c)
    (hg : ∀ u, HasDerivAt g (V u) u) (hV : ∀ u, HasDerivAt V (A u) u) (hAc : Continuous A)
    (hgper : Periodic g 1) (hVper : Periodic V 1) (hAper : Periodic A 1)
    (hspeed : ∀ u, c ≤ ‖V u‖)
    (hcurv : ∀ u, kmin * ‖V u‖ ^ 3 ≤ ((starRingEnd ℂ) (V u) * A u).im)
    (hchord : ∀ x y, delta * min |MarkedReparam.arcLength V x - MarkedReparam.arcLength V y|
        (MarkedReparam.totalLength V
          - |MarkedReparam.arcLength V x - MarkedReparam.arcLength V y|) ≤ ‖g x - g y‖) :
    ∃ p : Data, IsTubeMember (MarkedReparam.totalLength V) kmin
        (delta * MarkedReparam.totalLength V) p ∧
      range (⇑p.1) = range g ∧ perim p = MarkedReparam.totalLength V := by
  obtain ⟨psi, Y, W, B, L, hLeq, hLpos, hYderiv, hWderiv, hBcont, hYper, hWper, hBper, hWnorm,
    hrange, hYeq, hpsiarc, hcurveq⟩ :=
    MarkedReparam.exists_constant_speed_reparam hc hg hV hAc hgper hVper hAper hspeed
  have hYcont : Continuous Y := continuous_iff_continuousAt.2 fun u => (hYderiv u).continuousAt
  have hWcont : Continuous W := continuous_iff_continuousAt.2 fun u => (hWderiv u).continuousAt
  obtain ⟨CY, hCY⟩ := exists_bound_of_periodic hYcont hYper
  obtain ⟨CB, hCB⟩ := exists_bound_of_periodic hBcont hBper
  -- the marked data
  refine ⟨(BoundedContinuousFunction.ofNormedAddCommGroup Y hYcont CY hCY,
    BoundedContinuousFunction.ofNormedAddCommGroup W hWcont L (fun u => le_of_eq (hWnorm u)),
    BoundedContinuousFunction.ofNormedAddCommGroup B hBcont CB hCB), ?_, ?_, ?_⟩
  · refine ⟨hYderiv, hWderiv, hYper, ?_, ?_, ?_, ?_⟩
    · intro u v
      show ‖W u‖ = ‖W v‖
      rw [hWnorm u, hWnorm v]
    · intro u
      show MarkedReparam.totalLength V ≤ ‖W u‖
      rw [hWnorm u, ← hLeq]
    · intro u
      show kmin * ‖W u‖ ^ 3 ≤ ((starRingEnd ℂ) (W u) * B u).im
      rw [hWnorm u]
      have hp : 0 < ‖V (psi u)‖ := lt_of_lt_of_le hc (hspeed (psi u))
      have hp3 : 0 < ‖V (psi u)‖ ^ 3 := by positivity
      have hkey := hcurveq u
      have hcu := hcurv (psi u)
      have hle : kmin * L ^ 3 * ‖V (psi u)‖ ^ 3 ≤ L ^ 3 * ((starRingEnd ℂ) (V (psi u))
          * A (psi u)).im := by
        have h1 : 0 < L ^ 3 := by positivity
        nlinarith
      rw [← hkey] at hle
      exact le_of_mul_le_mul_right (by linarith) hp3
    · intro u hu v hv
      show delta * MarkedReparam.totalLength V * cyc u v ≤ ‖Y u - Y v‖
      have hxy := hchord (psi u) (psi v)
      rw [hpsiarc u, hpsiarc v] at hxy
      have habs : |L * u - L * v| = L * |u - v| := by
        rw [show L * u - L * v = L * (u - v) by ring, abs_mul, abs_of_pos hLpos]
      rw [habs] at hxy
      have hmin : min (L * |u - v|) (MarkedReparam.totalLength V - L * |u - v|)
          = L * cyc u v := by
        rw [← hLeq, cyc, mul_min_of_nonneg _ _ (le_of_lt hLpos)]
        congr 1
        ring
      rw [hmin] at hxy
      have hY : ‖Y u - Y v‖ = ‖g (psi u) - g (psi v)‖ := by rw [hYeq u, hYeq v]
      rw [hY, ← hLeq]
      calc delta * L * cyc u v = delta * (L * cyc u v) := by ring
        _ ≤ ‖g (psi u) - g (psi v)‖ := hxy
  · show range Y = range g
    exact hrange
  · show ‖W 0‖ = MarkedReparam.totalLength V
    rw [hWnorm 0, hLeq]

end MarkedSpace
