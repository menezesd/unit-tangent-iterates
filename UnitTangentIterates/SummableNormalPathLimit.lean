import Mathlib
import UnitTangentIterates.NormalPathC2Increment

/-!
# Completeness of summable normal paths, in the space of marked curves

The lemma *Completeness of summable normal paths* of the paper *A Noncircular
Oval with Convex Unit-Tangent Iterates* says that marked curves joined by paths
whose functionals `S₀ + S₁ + S₂` are summable converge in marked geometric `C²`
to a regular `C²` curve.

`MarkedTopology.limit_of_summable_normal_paths` is that conclusion for a
sequence of curves whose `C²` increments are already known to be summable, and
`NormalPathC2Increment.dist_le_cost` produces those increments from the cost of
the paths.  This file joins the two in the space of marked curves of
`MarkedSpace.lean`, where the conclusion is sharper than mere convergence of
the data: the tube is closed, so the limit is itself a **marked curve** — a
closed regular `C²` curve of constant speed, positive curvature and the same
chord-arc constant.

Main results:

* `exists_limit_of_summable_dist` — summable marked distances give a limit in
  the tube;
* `exists_limit_of_summable_costs` — **the lemma itself**: a sequence of marked
  curves joined by normal paths with constant-speed slices whose costs are
  summable converges, in the marked geometric `C²` topology, to a marked curve;
* `markedC2_tendsto_of_summable_costs` — the same convergence written with the
  uniform convergence of the curve, of the velocity and of the acceleration
  displayed.
-/

noncomputable section

open Set Function Filter Topology MarkedSpace PathMetric PathMetric.NormalPath
open NormalPathC2Increment

namespace SummableNormalPathLimit

/-- **Summable marked distances give a limit in the tube.**  The space of
marked curves is a closed subset of a complete space, so a sequence with
summable consecutive distances converges to a marked curve of the same tube. -/
theorem exists_limit_of_summable_dist {c kmin dlt : ℝ} {p : ℕ → Data} {d : ℕ → ℝ}
    (hmem : ∀ n, IsTubeMember c kmin dlt (p n)) (hsum : Summable d)
    (hstep : ∀ n, dist (p n) (p (n + 1)) ≤ d n) :
    ∃ plim : Data, IsTubeMember c kmin dlt plim ∧ Tendsto p atTop (𝓝 plim) := by
  have hcauchy : CauchySeq p := cauchySeq_of_dist_le_of_summable d hstep hsum
  obtain ⟨plim, hlim⟩ := cauchySeq_tendsto_of_complete hcauchy
  refine ⟨plim, ?_, hlim⟩
  exact (isClosed_tube c kmin dlt).mem_of_tendsto hlim
    (Eventually.of_forall fun n => hmem n)

/-- **Completeness of summable normal paths.**  Let `pₙ` be marked curves of one
tube, joined by normal paths `Γₙ` whose slices are constant-speed closed curves
of curvature at most `κ̂` and arclength period at most `P₁`, in the normal gauge
— the hypothesis `IsConstantSpeedNormalPath P₀ P₁ κ̂`, which is the normal-flow
identities of `NormalFlow.lean` written against the cost density.  If the costs
of the paths are summable, then the curves converge to a marked curve of the
same tube: a closed regular `C²` curve of constant speed at least `c`,
curvature at least `kmin` and the same chord-arc constant. -/
theorem exists_limit_of_summable_costs {c kmin dlt P0 P1 khat : ℝ} {p : ℕ → Data}
    (Γ : ∀ n, NormalPath (p n) (p (n + 1)))
    (hmem : ∀ n, IsTubeMember c kmin dlt (p n))
    (hgeom : ∀ n, IsConstantSpeedNormalPath P0 P1 khat (Γ n))
    (hsum : Summable fun n => cost (Γ n)) :
    ∃ plim : Data, IsTubeMember c kmin dlt plim ∧ Tendsto p atTop (𝓝 plim) := by
  refine exists_limit_of_summable_dist hmem
    (hsum.mul_left (c2Const P0 P1 khat)) (fun n => ?_)
  exact dist_le_cost (Γ n) (hmem n) (hmem (n + 1)) (hgeom n)

/-- **The limit in the marked geometric `C²` topology.**  The convergence of
`exists_limit_of_summable_costs`, written out: the curves, their velocities and
their accelerations converge uniformly, the limit is a closed curve of constant
speed at least `c` whose derivatives are the limiting velocity and
acceleration, so it is a regular `C²` curve. -/
theorem markedC2_tendsto_of_summable_costs {c kmin dlt P0 P1 khat : ℝ} {p : ℕ → Data}
    (Γ : ∀ n, NormalPath (p n) (p (n + 1)))
    (hmem : ∀ n, IsTubeMember c kmin dlt (p n))
    (hgeom : ∀ n, IsConstantSpeedNormalPath P0 P1 khat (Γ n))
    (hsum : Summable fun n => cost (Γ n)) :
    ∃ plim : Data,
      TendstoUniformly (fun n => ⇑(p n).1) (⇑plim.1) atTop ∧
      TendstoUniformly (fun n => ⇑(p n).2.1) (⇑plim.2.1) atTop ∧
      TendstoUniformly (fun n => ⇑(p n).2.2) (⇑plim.2.2) atTop ∧
      (∀ u, HasDerivAt (⇑plim.1) (plim.2.1 u) u) ∧
      (∀ u, HasDerivAt (⇑plim.2.1) (plim.2.2 u) u) ∧
      Periodic (⇑plim.1) 1 ∧ (∀ u, c ≤ ‖plim.2.1 u‖) := by
  obtain ⟨plim, hplim, hlim⟩ := exists_limit_of_summable_costs Γ hmem hgeom hsum
  refine ⟨plim, ?_, ?_, ?_, hplim.hasDerivAt_curve, hplim.hasDerivAt_vel, hplim.periodic,
    hplim.speed_lb⟩
  · exact BoundedContinuousFunction.tendsto_iff_tendstoUniformly.1
      ((continuous_fst.tendsto plim).comp hlim)
  · exact BoundedContinuousFunction.tendsto_iff_tendstoUniformly.1
      (((continuous_fst.comp continuous_snd).tendsto plim).comp hlim)
  · exact BoundedContinuousFunction.tendsto_iff_tendstoUniformly.1
      (((continuous_snd.comp continuous_snd).tendsto plim).comp hlim)

end SummableNormalPathLimit
