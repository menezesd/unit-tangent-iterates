import UnitTangentIterates.UnconditionalAssemblyRemainder
import UnitTangentIterates.StrictConvexityHarnack

/-!
# The strictness data in integrated form

§77 showed that strict convexity follows from the *integrated* inequality
`e^{a−b}u(a) ≤ u(b)` with no differentiability, and that the integrated form
passes to limits while the differential one does not.  This file restates the
strictness data accordingly.

`LimitStrictnessDataH` is `LimitStrictnessData` with the field `k'` and the
condition `next_nonnegative` removed, and `curvature_harnack` in their place.
`isOval_ev_of_limitStrictnessDataH` proves the same conclusion — the marked
limit is an oval — from it, and `LimitStrictnessData.toH` converts whenever the
curvature is differentiable, so nothing is lost for the smooth model curves.

**This closes the regularity gap of §76.**  The manifest's objection was that
`LimitStrictnessData` "needs a derivative of the limiting curvature
(`HasDerivAt k k'`), hence the corresponding curve regularity is effectively
`C³`", while the normal-path limit delivers `C²`.  `LimitStrictnessDataH` needs
no such derivative: every one of its fields is either a `C²` datum or an
inequality closed under limits.

What still has to be supplied for the limit is the Harnack inequality itself —
but by `harnack_of_tendsto` (§77) that follows from the same inequality for the
approximating model curves, which `LimitStrictnessData.toH` provides since those
are smooth.
-/

noncomputable section

set_option maxHeartbeats 4000000

open Set Function Filter Topology Metric CurvatureStabilityL1
open MarkedSpace ModelOrbitDefect PaperHairpinConfig
namespace UnconditionalAssembly

/-- **The strictness data in integrated form.**  Identical to
`LimitStrictnessData` except that the derivative `k'` and the differential
condition `next_nonnegative` are replaced by the integrated inequality, which
needs no derivative and passes to limits (§77). -/
structure LimitStrictnessDataH (p : MarkedSpace.Data) where
  theta : ℝ → ℝ
  k : ℝ → ℝ
  curve_deriv : ∀ s, HasDerivAt (MarkedSpace.ev p)
    (Complex.exp (Complex.I * (theta s : ℂ))) s
  angle_deriv : ∀ s, HasDerivAt theta (k s) s
  curvature_periodic : Function.Periodic k (MarkedSpace.perim p)
  curvature_nonnegative : ∀ s, 0 ≤ k s
  curvature_harnack : ∀ a b : ℝ, a ≤ b →
    Real.exp (a - b) * (k a / Real.sqrt (1 + k a ^ 2))
      ≤ k b / Real.sqrt (1 + k b ^ 2)
  curvature_nonzero : ∃ s, k s ≠ 0

theorem isOval_ev_of_limitStrictnessDataH
    {p : MarkedSpace.Data} {c dlt : ℝ}
    (hc : 0 < c) (hdlt : 0 < dlt)
    (hp : MarkedSpace.IsTubeMember c 0 dlt p)
    (d : LimitStrictnessDataH p) : MainTheoremConditional.IsOval (ev p) := by
  let L := perim p
  have hL : 0 < L := MarkedSpace.perim_pos hc hp
  have hpos : ∀ s, 0 < d.k s :=
    UnitTangent.curvature_pos_of_harnack hL d.curvature_periodic
      d.curvature_nonnegative d.curvature_harnack d.curvature_nonzero
  have hinj : InjOn (ev p) (Ico 0 L) := by
    intro s hs t ht hst
    have hsmem : s / L ∈ Ico (0 : ℝ) 1 := by
      constructor
      · exact div_nonneg hs.1 hL.le
      · exact (div_lt_one hL).2 hs.2
    have htmem : t / L ∈ Ico (0 : ℝ) 1 := by
      constructor
      · exact div_nonneg ht.1 hL.le
      · exact (div_lt_one hL).2 ht.2
    have hzero : ‖p.1 (s / L) - p.1 (t / L)‖ = 0 := by
      have h : p.1 (s / L) = p.1 (t / L) := hst
      rw [h, sub_self, norm_zero]
    have hchord := hp.chord (s / L) (Ico_subset_Icc_self hsmem) (t / L)
      (Ico_subset_Icc_self htmem)
    rw [hzero] at hchord
    have hcyc : MarkedSpace.cyc (s / L) (t / L) ≤ 0 := by
      by_contra h
      push_neg at h
      nlinarith
    have heq := MarkedSpace.cyc_eq_zero_iff hsmem htmem hcyc
    field_simp at heq
    exact heq
  exact ⟨L, hL, MarkedSpace.periodic_ev hc hp, hinj, d.theta,
    d.curve_deriv, d.k, d.angle_deriv, hpos⟩
/-- **The differential form yields the integrated one.**  Any
`LimitStrictnessData` whose curvature is differentiable converts, so nothing is
lost for the smooth model curves; what is gained is that the integrated form
survives the passage to a `C²` limit. -/
def LimitStrictnessData.toH {p : MarkedSpace.Data} (d : LimitStrictnessData p)
    (hdiff : Differentiable ℝ d.k) : LimitStrictnessDataH p where
  theta := d.theta
  k := d.k
  curve_deriv := d.curve_deriv
  angle_deriv := d.angle_deriv
  curvature_periodic := d.curvature_periodic
  curvature_nonnegative := d.curvature_nonnegative
  curvature_harnack := by
    refine UnitTangent.harnack_of_next_nonneg hdiff (fun x => ?_)
    have h := d.next_nonnegative x
    rwa [UnitTangentSpeed.transform_curvature_eq_deriv_u_add_u d.curvature_deriv x]
      at h
  curvature_nonzero := d.curvature_nonzero

end UnconditionalAssembly
