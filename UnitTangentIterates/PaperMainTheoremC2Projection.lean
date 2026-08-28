import UnitTangentIterates.PaperFacingVariableTerminalOutput

/-!
# A sound C2 paper-facing projection

The legacy final projection intentionally forgets the marked representative.
Consequently it also forgets both the `C2` regularity carried by the closed
tube and the fact that its displayed period is a simple arclength period.
This module retains those two facts without changing any existing API.

It does not claim smoothness of all orders.  The selected-rear regularity gain
has not yet been iterated along the limiting orbit.
-/

noncomputable section

open Function Set

namespace PaperMainTheoremC2Projection

open MarkedSpace VariableMarkedTube

/-- A parameter-independent predicate saying that the image of a curve is a
circle. -/
def IsCircleRange (gamma : ℝ → ℂ) : Prop :=
  ∃ (center : ℂ) (radius : ℝ),
    0 < radius ∧ range gamma = Metric.sphere center radius

/-- A parameter-independent geometric noncircularity predicate. -/
def IsNoncircular (gamma : ℝ → ℂ) : Prop :=
  ¬ IsCircleRange gamma

/-- The physical arclength representative of any marked `C2` tube member is
`C2`. -/
theorem contDiff_two_ev_of_tube
    {c kmin dlt : ℝ} (hc : 0 < c) {p : Data}
    (hp : IsTubeMember c kmin dlt p) :
    ContDiff ℝ (2 : ℕ) (ev p) := by
  let L := perim p
  have hLpos : 0 < L := perim_pos hc hp
  have hLne : L ≠ 0 := ne_of_gt hLpos
  let V : ℝ → ℂ := fun s => p.2.1 (s / L) / L
  let A : ℝ → ℂ := fun s => p.2.2 (s / L) / L ^ 2
  have hinner : ∀ s : ℝ,
      HasDerivAt (fun x : ℝ => x / L) (1 / L) s := by
    intro s
    simpa [div_eq_mul_inv, one_div] using (hasDerivAt_id s).div_const L
  have hev : ∀ s, HasDerivAt (ev p) (V s) s := by
    intro s
    have h := (hp.hasDerivAt_curve (s / L)).scomp s (hinner s)
    simpa [ev, V, L, Function.comp_def, div_eq_mul_inv, one_div,
      smul_eq_mul, mul_comm, hLne] using h
  have hV : ∀ s, HasDerivAt V (A s) s := by
    intro s
    have h0 := (hp.hasDerivAt_vel (s / L)).scomp s (hinner s)
    have h := h0.div_const L
    simpa [V, A, Function.comp_def, div_eq_mul_inv, one_div, smul_eq_mul,
      pow_two, mul_comm, mul_left_comm, mul_assoc, hLne] using h
  have hAcont : Continuous A := by
    have hcomp : Continuous fun s : ℝ => p.2.2 (s / L) :=
      p.2.2.continuous.comp (continuous_id.div_const L)
    exact hcomp.div_const _
  have hderivV : deriv V = A := by
    funext s
    exact (hV s).deriv
  have hVC1 : ContDiff ℝ (1 : WithTop ℕ∞) V := by
    rw [contDiff_one_iff_deriv]
    refine ⟨fun s => (hV s).differentiableAt, ?_⟩
    rw [hderivV]
    exact hAcont
  have hderivEv : deriv (ev p) = V := by
    funext s
    exact (hev s).deriv
  have hC2 : ContDiff ℝ (((1 : ℕ) : WithTop ℕ∞) + 1) (ev p) := by
    rw [contDiff_succ_iff_deriv]
    refine ⟨fun s => (hev s).differentiableAt, by simp, ?_⟩
    rw [hderivEv]
    exact hVC1
  exact_mod_cast hC2

/-- The perimeter of a positive-chord tube member is an injective period of
its arclength representative. -/
theorem injOn_ev_simple_period
    {c kmin dlt : ℝ} (hc : 0 < c) (hdlt : 0 < dlt) {p : Data}
    (hp : IsTubeMember c kmin dlt p) :
    InjOn (ev p) (Ico 0 (perim p)) := by
  have hL : 0 < perim p := perim_pos hc hp
  intro s hs t ht hst
  have hsmem : s / perim p ∈ Ico (0 : ℝ) 1 := by
    constructor
    · exact div_nonneg hs.1 hL.le
    · exact (div_lt_one hL).2 hs.2
  have htmem : t / perim p ∈ Ico (0 : ℝ) 1 := by
    constructor
    · exact div_nonneg ht.1 hL.le
    · exact (div_lt_one hL).2 ht.2
  have hzero :
      ‖p.1 (s / perim p) - p.1 (t / perim p)‖ = 0 := by
    have h : p.1 (s / perim p) = p.1 (t / perim p) := hst
    rw [h, sub_self, norm_zero]
  have hchord := hp.chord (s / perim p) (Ico_subset_Icc_self hsmem)
    (t / perim p) (Ico_subset_Icc_self htmem)
  rw [hzero] at hchord
  have hcyc : MarkedSpace.cyc (s / perim p) (t / perim p) ≤ 0 := by
    nlinarith
  have heq := MarkedSpace.cyc_eq_zero_iff hsmem htmem hcyc
  field_simp at heq
  exact heq

/-- Strengthen an existing paper-facing output when its retained ordinary
curves are identified with the supplied oriented arclength representatives.

The displayed `L` is now not merely a period: it is the representative's
positive perimeter and the curve is injective on `[0,L)`.  Thus the final
`IsCircleOfPerimeter` clause can no longer be satisfied vacuously by choosing
a multiple of a circle's simple period. -/
theorem of_output_of_representatives
    {Q : ℕ → Data} {P : ℕ → ℕ → Data}
    {e : ℕ → ℕ → ℝ} {P0 P1 khat G1 Cg C : ℕ → ℝ}
    {c dlt : ℝ}
    {O : TriangularMarkedPathSchemeVariableTerminal.LimitOutput
      Q P e P0 P1 khat G1 Cg C c dlt}
    {direction : ℂ} {modelWidth H : ℝ}
    (R : ∀ n, OrientedArclengthRepresentative (O.X n))
    (A : PaperFacingVariableTerminalOutput.Output O direction modelWidth H)
    (hGamma : A.Gamma = fun n => ev (R n).q) :
    ∃ Gamma : ℕ → ℝ → ℂ, ∃ L : ℝ,
      0 < L ∧ Periodic (Gamma 0) L ∧
      InjOn (Gamma 0) (Ico 0 L) ∧
      (∀ n, MainTheoremConditional.IsOval (Gamma n)) ∧
      (∀ n, ContDiff ℝ (2 : ℕ) (Gamma n)) ∧
      (∀ n, range (Gamma (n + 1)) =
        range (UnitTangent.unitTangentMap (Gamma n))) ∧
      ¬ ClosingArgument.IsCircleOfPerimeter (range (Gamma 0)) L := by
  let L := perim (R 0).q
  refine ⟨A.Gamma, L, perim_pos (R 0).c_pos (R 0).tube, ?_, ?_,
    A.oval, ?_, A.range_orbit, ?_⟩
  · rw [hGamma]
    exact periodic_ev (R 0).c_pos (R 0).tube
  · rw [hGamma]
    exact injOn_ev_simple_period (R 0).c_pos (R 0).dlt_pos (R 0).tube
  · intro n
    rw [hGamma]
    exact contDiff_two_ev_of_tube (R n).c_pos (R n).tube
  · have hlength := (R 0).physical_length
    simpa [L, hlength] using A.noncircle

end PaperMainTheoremC2Projection
