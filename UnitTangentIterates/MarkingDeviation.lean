import Mathlib
import UnitTangentIterates.PathMetric

/-!
# The marking defect at the terminal end of a path-distance bound

The path-distance bounds for the selected rears of a normal path of fronts
(`SelectedInverseRearOwnTerminal.lean` and the files built on it) compare the
marked selected inverse `selInv κ̂ p` of the initial curve of the path with the
marked selected inverse of the terminal curve **read in the gauge marking**:
their conclusion is a bound for `pathDist (selInv κ̂ p) q'` for any marked curve
`q'` whose curve is

```
  q'.1 u = (selInv κ̂ q).1 (Φ_T u / perim (selInv κ̂ q)) ,
```

`Φ` being the gauge flow produced by the assembly.  The gauge marking `Φ_T` is
a normalized parameter of the terminal slice but need not be the affine marking
`u ↦ perim (selInv κ̂ q) · u`, so the terminal curve of the bound is a
*reparametrization* of `selInv κ̂ q`.  `SelectedInverseRearOwnShift.lean`
removes the reparametrization by rigidity, at the price of assuming `q'` to be
a member of the tube — that is, to be carried in a constant-speed parameter.

This file measures the defect instead of assuming it away.  All the statements
are elementary and general:

* `norm_sub_le_of_norm_deriv_le` — a curve whose speed is at most `L` moves at
  most `L|a − b|` between two parameters;
* `abs_sub_le_integral_of_hasDerivAt` and `abs_flow_displacement_le` — the
  displacement of a flow line over `[0, T]` is at most the time integral of a
  bound for the field, in particular at most `ρ·T` for a constant bound, and
  `abs_flow_displacement_le_affine` — the Grönwall bound when the field only
  grows affinely, `|R(t,x)| ≤ ε₀ + K|x|`, which is the shape of the tangential
  rate of a family of closed curves written in its own arclength;
* `abs_marking_defect_le` and `abs_marking_defect_le_affine` — a marking
  flowed from the affine marking of period `L₀` and translating by `L₁` over
  one period deviates from the affine marking of period `L₁` by at most that
  displacement plus `|L₀ − L₁|`;
* `norm_sub_le_of_marking` — if the marking `φ` deviates from the affine
  marking by at most `ε`, then the reparametrized curve is uniformly within `ε`
  of the constant-speed curve it reparametrizes;
* `norm_sub_le_pathDist_add_marking` and `dist_fst_le_pathDist_add_marking` —
  hence a bound `pathDist a q' ≤ B` together with a marking defect `ε` bounds
  the uniform distance of the *curves* of `a` and of the reparametrized `b` by
  `B + ε`, with no hypothesis on the parametrization of `q'`.

As `pathDist` is an infimum over a possibly empty set of costs, the last two
statements carry the existence of a normal path joining the two curves as an
explicit hypothesis, exactly as `PathMetric.dist_fst_le_pathDist` does.
-/

noncomputable section

open Set MeasureTheory MarkedSpace PathMetric PathMetric.NormalPath

namespace MarkingDeviation

/-! ### Elementary displacement bounds -/

/-- A curve whose speed is bounded by `L` moves at most `L|a − b|` between the
parameters `b` and `a`. -/
theorem norm_sub_le_of_norm_deriv_le {c v : ℝ → ℂ} {L : ℝ}
    (hc : ∀ x, HasDerivAt c (v x) x) (hv : ∀ x, ‖v x‖ ≤ L) (a b : ℝ) :
    ‖c a - c b‖ ≤ L * |a - b| := by
  have h := (convex_univ (𝕜 := ℝ) (E := ℝ)).norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := c) (f' := v) (C := L) (fun x _ => (hc x).hasDerivWithinAt) (fun x _ => hv x)
    (mem_univ b) (mem_univ a)
  simpa [Real.norm_eq_abs] using h

/-- **The displacement of a flow line is at most the integral of a bound for
its velocity.** -/
theorem abs_sub_le_integral_of_hasDerivAt {f w rho : ℝ → ℝ}
    (hf : ∀ t, HasDerivAt f (w t) t) (hw : Continuous w)
    (hb : ∀ t, |w t| ≤ rho t) (hrho : Continuous rho) {T : ℝ} (hT : 0 ≤ T) :
    |f T - f 0| ≤ ∫ t in (0:ℝ)..T, rho t := by
  have hwi : IntervalIntegrable w volume 0 T := hw.intervalIntegrable 0 T
  have hint : (∫ t in (0:ℝ)..T, w t) = f T - f 0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hf t) hwi
  rw [← hint]
  have hri : IntervalIntegrable rho volume 0 T := hrho.intervalIntegrable 0 T
  have h := intervalIntegral.norm_integral_le_of_norm_le (f := w) (g := rho) hT
    (Filter.Eventually.of_forall (fun t _ => by simpa [Real.norm_eq_abs] using hb t)) hri
  simpa [Real.norm_eq_abs] using h

/-- **The displacement of a gauge flow line over `[0, T]`**, from a bound `ρ`
for the field of the flow. -/
theorem abs_flow_displacement_le {Phi : ℝ → ℝ → ℝ} {R : ℝ → ℝ → ℝ} {rho : ℝ → ℝ} (u : ℝ)
    (hd : ∀ t, HasDerivAt (fun r => Phi r u) (R t (Phi t u)) t)
    (hc : Continuous fun t => R t (Phi t u))
    (hb : ∀ t, |R t (Phi t u)| ≤ rho t) (hrho : Continuous rho) {T : ℝ} (hT : 0 ≤ T) :
    |Phi T u - Phi 0 u| ≤ ∫ t in (0:ℝ)..T, rho t :=
  abs_sub_le_integral_of_hasDerivAt (f := fun r => Phi r u)
    (w := fun t => R t (Phi t u)) hd hc hb hrho hT

/-- The same with a constant bound for the field of the flow. -/
theorem abs_flow_displacement_le_const {Phi : ℝ → ℝ → ℝ} {R : ℝ → ℝ → ℝ} {rho : ℝ} (u : ℝ)
    (hd : ∀ t, HasDerivAt (fun r => Phi r u) (R t (Phi t u)) t)
    (hb : ∀ t x, |R t x| ≤ rho) {T : ℝ} (hT : 0 ≤ T) :
    |Phi T u - Phi 0 u| ≤ rho * T := by
  have h := (convex_Icc (0 : ℝ) T).norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun r => Phi r u) (f' := fun t => R t (Phi t u)) (C := rho)
    (fun t _ => (hd t).hasDerivWithinAt)
    (fun t _ => by simpa [Real.norm_eq_abs] using hb t (Phi t u))
    (left_mem_Icc.2 hT) (right_mem_Icc.2 hT)
  simpa [Real.norm_eq_abs, abs_of_nonneg hT] using h

/-! ### Fields of affine growth -/

/-- Monotonicity of the Grönwall bound in its inhomogeneous term. -/
theorem gronwallBound_mono_eps {K x e₁ e₂ : ℝ} (hK : 0 ≤ K) (hx : 0 ≤ x) (h : e₁ ≤ e₂) :
    gronwallBound 0 K e₁ x ≤ gronwallBound 0 K e₂ x := by
  rcases eq_or_lt_of_le hK with h0 | h0
  · rw [← h0, gronwallBound_K0, gronwallBound_K0]
    simpa using mul_le_mul_of_nonneg_right h hx
  · rw [gronwallBound_of_K_ne_0 h0.ne', gronwallBound_of_K_ne_0 h0.ne']
    have hexp : 1 ≤ Real.exp (K * x) := Real.one_le_exp (by positivity)
    have hd : e₁ / K ≤ e₂ / K := by gcongr
    simp only [zero_mul, zero_add]
    exact mul_le_mul_of_nonneg_right hd (by linarith)

/-- **The displacement of a flow line of a field of affine growth.**  If the
field is bounded by `ε₀ + K|x|` — the shape of the tangential rate of a family
of closed curves written in its own arclength, whose drift over each period is
controlled by the curvature — then the displacement over `[0, T]` obeys the
Grönwall bound. -/
theorem abs_flow_displacement_le_affine {Phi : ℝ → ℝ → ℝ} {R : ℝ → ℝ → ℝ}
    {K eps0 T : ℝ} (u : ℝ)
    (hd : ∀ t, HasDerivAt (fun r => Phi r u) (R t (Phi t u)) t)
    (hb : ∀ t x, |R t x| ≤ eps0 + K * |x|) (hK : 0 ≤ K) (hT : 0 ≤ T) :
    |Phi T u - Phi 0 u| ≤ gronwallBound 0 K (eps0 + K * |Phi 0 u|) T := by
  set g : ℝ → ℝ := fun t => Phi t u - Phi 0 u with hg
  have hgd : ∀ t, HasDerivAt g (R t (Phi t u)) t := fun t => (hd t).sub_const _
  have hcont : ContinuousOn g (Icc 0 T) :=
    Continuous.continuousOn (continuous_iff_continuousAt.2 fun t =>
      (hgd t).differentiableAt.continuousAt)
  have hbound : ∀ t ∈ Ico (0:ℝ) T, ‖R t (Phi t u)‖ ≤ K * ‖g t‖ + (eps0 + K * |Phi 0 u|) := by
    intro t _
    have h1 : |R t (Phi t u)| ≤ eps0 + K * |Phi t u| := hb t (Phi t u)
    have h2 : |Phi t u| ≤ |g t| + |Phi 0 u| := by
      have hgt : Phi t u = g t + Phi 0 u := by simp [hg]
      rw [hgt]
      exact abs_add_le _ _
    have h3 := mul_le_mul_of_nonneg_left h2 hK
    simp only [Real.norm_eq_abs]
    linarith
  have h0 : ‖g 0‖ ≤ (0 : ℝ) := by simp [hg]
  have h := norm_le_gronwallBound_of_norm_deriv_right_le (f := g) (δ := 0)
    (f' := fun t => R t (Phi t u)) hcont
    (fun t _ => (hgd t).hasDerivWithinAt) h0 hbound T (right_mem_Icc.2 hT)
  simpa [hg, Real.norm_eq_abs] using h

/-! ### The defect of a gauge marking -/

/-- **The defect of a gauge marking.**  Let `Φ` be the flow of a field bounded
by `ρ(t)` along each of its lines, started from the affine marking `u ↦ L₀·u`, and suppose that at the
final time it is quasi-periodic with period `L₁`, `Φ_T(u+1) = Φ_T(u) + L₁` (as
the gauge flow of a family of closed curves is, the flow translating by the
current arclength period).  Then `Φ_T` deviates from the affine marking
`u ↦ L₁·u` by at most the displacement of the flow plus the change of the
period. -/
theorem abs_marking_defect_le {Phi : ℝ → ℝ → ℝ} {R : ℝ → ℝ → ℝ} {rho : ℝ → ℝ}
    {L0 L1 T : ℝ}
    (hd : ∀ u t, HasDerivAt (fun r => Phi r u) (R t (Phi t u)) t)
    (hc : ∀ u, Continuous fun t => R t (Phi t u))
    (hb : ∀ u t, |R t (Phi t u)| ≤ rho t) (hrho : Continuous rho) (hT : 0 ≤ T)
    (h0 : ∀ u, Phi 0 u = L0 * u) (hper : ∀ u, Phi T (u + 1) = Phi T u + L1) (u : ℝ) :
    |Phi T u - L1 * u| ≤ (∫ t in (0:ℝ)..T, rho t) + |L0 - L1| := by
  set g : ℝ → ℝ := fun x => Phi T x - L1 * x with hg
  have hgper : Function.Periodic g 1 := by
    intro x
    simp only [hg, hper x]
    ring
  have hfract : g (Int.fract u) = g u := by
    have h2 := hgper.sub_int_mul_eq (x := u) ⌊u⌋
    rw [Int.fract, show u - (⌊u⌋ : ℝ) = u - (⌊u⌋ : ℝ) * 1 by ring]
    exact h2
  have hr0 : 0 ≤ Int.fract u := Int.fract_nonneg u
  have hr1 : Int.fract u ≤ 1 := (Int.fract_lt_one u).le
  have hflow : |Phi T (Int.fract u) - Phi 0 (Int.fract u)| ≤ ∫ t in (0:ℝ)..T, rho t :=
    abs_flow_displacement_le (Int.fract u) (fun t => hd (Int.fract u) t) (hc _)
      (hb (Int.fract u)) hrho hT
  have haff : |Phi 0 (Int.fract u) - L1 * Int.fract u| ≤ |L0 - L1| := by
    rw [h0 (Int.fract u), show L0 * Int.fract u - L1 * Int.fract u
      = (L0 - L1) * Int.fract u by ring, abs_mul, abs_of_nonneg hr0]
    exact mul_le_of_le_one_right (abs_nonneg _) hr1
  have hsplit : |g (Int.fract u)| ≤ (∫ t in (0:ℝ)..T, rho t) + |L0 - L1| := by
    have hdecomp : g (Int.fract u) = (Phi T (Int.fract u) - Phi 0 (Int.fract u))
        + (Phi 0 (Int.fract u) - L1 * Int.fract u) := by simp [hg]
    rw [hdecomp]
    exact le_trans (abs_add_le _ _) (add_le_add hflow haff)
  have hgu : g u = Phi T u - L1 * u := rfl
  rw [← hgu, ← hfract]
  exact hsplit

/-- **The defect of a gauge marking flowed by a field of affine growth.**  The
displacement term of `abs_marking_defect_le` is bounded through Grönwall by the
data of the field alone. -/
theorem abs_marking_defect_le_affine {Phi : ℝ → ℝ → ℝ} {R : ℝ → ℝ → ℝ}
    {L0 L1 K eps0 T : ℝ}
    (hd : ∀ u t, HasDerivAt (fun r => Phi r u) (R t (Phi t u)) t)
    (hb : ∀ t x, |R t x| ≤ eps0 + K * |x|) (hK : 0 ≤ K) (hT : 0 ≤ T)
    (h0 : ∀ u, Phi 0 u = L0 * u) (hper : ∀ u, Phi T (u + 1) = Phi T u + L1) (u : ℝ) :
    |Phi T u - L1 * u| ≤ gronwallBound 0 K (eps0 + K * |L0|) T + |L0 - L1| := by
  set g : ℝ → ℝ := fun x => Phi T x - L1 * x with hg
  have hgper : Function.Periodic g 1 := by
    intro x
    simp only [hg, hper x]
    ring
  have hfract : g (Int.fract u) = g u := by
    have h2 := hgper.sub_int_mul_eq (x := u) ⌊u⌋
    rw [Int.fract, show u - (⌊u⌋ : ℝ) = u - (⌊u⌋ : ℝ) * 1 by ring]
    exact h2
  have hr0 : 0 ≤ Int.fract u := Int.fract_nonneg u
  have hr1 : Int.fract u ≤ 1 := (Int.fract_lt_one u).le
  have hstart : |Phi 0 (Int.fract u)| ≤ |L0| := by
    rw [h0 (Int.fract u), abs_mul, abs_of_nonneg hr0]
    exact mul_le_of_le_one_right (abs_nonneg _) hr1
  have hflow : |Phi T (Int.fract u) - Phi 0 (Int.fract u)|
      ≤ gronwallBound 0 K (eps0 + K * |L0|) T := by
    refine le_trans (abs_flow_displacement_le_affine (Int.fract u)
      (fun t => hd (Int.fract u) t) hb hK hT) ?_
    exact gronwallBound_mono_eps hK hT (by nlinarith [abs_nonneg (Phi 0 (Int.fract u))])
  have haff : |Phi 0 (Int.fract u) - L1 * Int.fract u| ≤ |L0 - L1| := by
    rw [h0 (Int.fract u), show L0 * Int.fract u - L1 * Int.fract u
      = (L0 - L1) * Int.fract u by ring, abs_mul, abs_of_nonneg hr0]
    exact mul_le_of_le_one_right (abs_nonneg _) hr1
  have hsplit : |g (Int.fract u)| ≤ gronwallBound 0 K (eps0 + K * |L0|) T + |L0 - L1| := by
    have hdecomp : g (Int.fract u) = (Phi T (Int.fract u) - Phi 0 (Int.fract u))
        + (Phi 0 (Int.fract u) - L1 * Int.fract u) := by simp [hg]
    rw [hdecomp]
    exact le_trans (abs_add_le _ _) (add_le_add hflow haff)
  have hgu : g u = Phi T u - L1 * u := rfl
  rw [← hgu, ← hfract]
  exact hsplit

/-- **Non-vacuity of the defect bound**, on the marking translated at constant
rate: `Φ_t(u) = L·u + c·t` is the flow of the constant field `c`, starts at the
affine marking of period `L` and translates by `L` over one period, and the
bound of `abs_marking_defect_le` is exactly its defect `|c|·T`. -/
theorem abs_marking_defect_le_translation {L c T : ℝ} (hT : 0 ≤ T) (u : ℝ) :
    |(L * u + c * T) - L * u| ≤ (∫ _t in (0:ℝ)..T, |c|) + |L - L| := by
  have h := abs_marking_defect_le (Phi := fun t x => L * x + c * t) (R := fun _ _ => c)
    (rho := fun _ => |c|) (L0 := L) (L1 := L) (T := T)
    (fun x t => by simpa using ((hasDerivAt_id t).const_mul c).const_add (L * x))
    (fun _ => continuous_const) (fun _ _ => le_rfl) continuous_const hT
    (fun x => by ring) (fun x => by ring) u
  simpa using h

/-! ### The marking defect -/

/-- **A curve read in a marking close to the affine one is close to the curve.**
If `b` is carried in a parameter of constant speed `L` and `q'` is `b` read in
the marking `φ`, then `q'` and `b` differ by at most the deviation of `φ` from
the affine marking `u ↦ L·u`. -/
theorem norm_sub_le_of_marking {b q' : Data} {phi : ℝ → ℝ} {L eps : ℝ} (hL : 0 < L)
    (hderiv : ∀ x, HasDerivAt (⇑b.1) (b.2.1 x) x) (hspeed : ∀ x, ‖b.2.1 x‖ = L)
    (hq' : ∀ u, q'.1 u = b.1 (phi u / L)) (hdev : ∀ u, |phi u - L * u| ≤ eps) (u : ℝ) :
    ‖q'.1 u - b.1 u‖ ≤ eps := by
  have h := norm_sub_le_of_norm_deriv_le (c := ⇑b.1) (v := ⇑b.2.1) (L := L) hderiv
    (fun x => (hspeed x).le) (phi u / L) u
  have hval : phi u / L - u = (phi u - L * u) / L := by field_simp
  rw [hval, abs_div, abs_of_pos hL, mul_div_cancel₀ _ hL.ne'] at h
  rw [hq' u]
  exact le_trans h (hdev u)

/-! ### The uniform bound at the terminal end -/

/-- **The path-distance bound and the marking defect bound the uniform distance
of the two curves.**  If `a` and `q'` are joined by a normal path of cost at
most `B`, and `q'` is the constant-speed curve `b` read in a marking deviating
from the affine one by at most `ε`, then the curves of `a` and `b` differ by at
most `B + ε` at every parameter. -/
theorem norm_sub_le_pathDist_add_marking {a b q' : Data} {phi : ℝ → ℝ} {L eps B : ℝ}
    (hL : 0 < L) (hderiv : ∀ x, HasDerivAt (⇑b.1) (b.2.1 x) x) (hspeed : ∀ x, ‖b.2.1 x‖ = L)
    (hq' : ∀ u, q'.1 u = b.1 (phi u / L)) (hdev : ∀ u, |phi u - L * u| ≤ eps)
    (hne : Nonempty (NormalPath a q')) (hB : pathDist a q' ≤ B) (u : ℝ) :
    ‖b.1 u - a.1 u‖ ≤ B + eps := by
  have h1 : ‖q'.1 u - a.1 u‖ ≤ B := le_trans (norm_sub_le_pathDist hne u) hB
  have h2 : ‖b.1 u - q'.1 u‖ ≤ eps := by
    rw [← norm_neg]
    simpa using norm_sub_le_of_marking hL hderiv hspeed hq' hdev u
  calc ‖b.1 u - a.1 u‖ = ‖(b.1 u - q'.1 u) + (q'.1 u - a.1 u)‖ := by ring_nf
    _ ≤ ‖b.1 u - q'.1 u‖ + ‖q'.1 u - a.1 u‖ := norm_add_le _ _
    _ ≤ B + eps := by linarith

/-- The same in the sup metric of the space of marked curves. -/
theorem dist_fst_le_pathDist_add_marking {a b q' : Data} {phi : ℝ → ℝ} {L eps B : ℝ}
    (hL : 0 < L) (hderiv : ∀ x, HasDerivAt (⇑b.1) (b.2.1 x) x) (hspeed : ∀ x, ‖b.2.1 x‖ = L)
    (hq' : ∀ u, q'.1 u = b.1 (phi u / L)) (hdev : ∀ u, |phi u - L * u| ≤ eps)
    (hne : Nonempty (NormalPath a q')) (hB : pathDist a q' ≤ B) (hB0 : 0 ≤ B)
    (heps : 0 ≤ eps) :
    dist a.1 b.1 ≤ B + eps := by
  refine (BoundedContinuousFunction.dist_le (by linarith)).2 (fun u => ?_)
  rw [dist_eq_norm, norm_sub_rev]
  exact norm_sub_le_pathDist_add_marking hL hderiv hspeed hq' hdev hne hB u

end MarkingDeviation
