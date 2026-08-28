import UnitTangentIterates.MarkedUnitTangentRangeClosure
import UnitTangentIterates.TubeArclengthAngle

/-!
# A closed tube for nonaffine markings

Gauge paths naturally end at variable-speed markings.  This file keeps the
closed geometric conditions used by compactness while dropping only the
constant-speed equation from `MarkedSpace.IsTubeMember`.
-/

noncomputable section

open Set Function Filter Topology

namespace VariableMarkedTube

open MarkedSpace

/-- A closed `C2` variable-speed tube.  Both speed bounds are retained because
they are stable under marked convergence and are exactly the bi-Lipschitz
control furnished by a gauge flow. -/
structure IsVariableTubeMember
    (c C kmin delta : ℝ) (p : Data) : Prop where
  hasDerivAt_curve : ∀ u, HasDerivAt (⇑p.1) (p.2.1 u) u
  hasDerivAt_vel : ∀ u, HasDerivAt (⇑p.2.1) (p.2.2 u) u
  periodic : Periodic (⇑p.1) 1
  speed_lb : ∀ u, c ≤ ‖p.2.1 u‖
  speed_ub : ∀ u, ‖p.2.1 u‖ ≤ C
  curv_lb : ∀ u,
    kmin * ‖p.2.1 u‖ ^ 3 ≤
      ((starRingEnd ℂ) (p.2.1 u) * p.2.2 u).im
  chord : ∀ u ∈ Icc (0 : ℝ) 1, ∀ v ∈ Icc (0 : ℝ) 1,
    delta * cyc u v ≤ ‖p.1 u - p.1 v‖

def variableTube (c C kmin delta : ℝ) : Set Data :=
  {p | IsVariableTubeMember c C kmin delta p}

/-- The variable-speed tube is closed in marked `C2` data. -/
theorem isClosed_variableTube (c C kmin delta : ℝ) :
    IsClosed (variableTube c C kmin delta) := by
  apply IsSeqClosed.isClosed
  intro pn p hmem hlim
  have h1 : TendstoUniformly (fun n => ⇑(pn n).1) (⇑p.1) atTop :=
    BoundedContinuousFunction.tendsto_iff_tendstoUniformly.1
      ((continuous_fst.tendsto p).comp hlim)
  have h2 : TendstoUniformly (fun n => ⇑(pn n).2.1) (⇑p.2.1) atTop :=
    BoundedContinuousFunction.tendsto_iff_tendstoUniformly.1
      (((continuous_fst.comp continuous_snd).tendsto p).comp hlim)
  have h3 : TendstoUniformly (fun n => ⇑(pn n).2.2) (⇑p.2.2) atTop :=
    BoundedContinuousFunction.tendsto_iff_tendstoUniformly.1
      (((continuous_snd.comp continuous_snd).tendsto p).comp hlim)
  have hp1 : ∀ u, Tendsto (fun n => (pn n).1 u) atTop (𝓝 (p.1 u)) :=
    fun u => h1.tendsto_at u
  have hp2 : ∀ u, Tendsto (fun n => (pn n).2.1 u) atTop (𝓝 (p.2.1 u)) :=
    fun u => h2.tendsto_at u
  have hp3 : ∀ u, Tendsto (fun n => (pn n).2.2 u) atTop (𝓝 (p.2.2 u)) :=
    fun u => h3.tendsto_at u
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun u => GeometricLimit.hasDerivAt_of_uniform_limit
      (fun n u => (hmem n).hasDerivAt_curve u) h2 hp1 u
  · exact fun u => GeometricLimit.hasDerivAt_of_uniform_limit
      (fun n u => (hmem n).hasDerivAt_vel u) h3 hp2 u
  · intro u
    refine tendsto_nhds_unique (hp1 (u + 1)) ?_
    simpa [(hmem _).periodic u] using hp1 u
  · intro u
    have hu : Tendsto (fun n => ‖(pn n).2.1 u‖) atTop
        (𝓝 ‖p.2.1 u‖) := (continuous_norm.tendsto _).comp (hp2 u)
    exact ge_of_tendsto hu (Eventually.of_forall fun n => (hmem n).speed_lb u)
  · intro u
    have hu : Tendsto (fun n => ‖(pn n).2.1 u‖) atTop
        (𝓝 ‖p.2.1 u‖) := (continuous_norm.tendsto _).comp (hp2 u)
    exact le_of_tendsto hu (Eventually.of_forall fun n => (hmem n).speed_ub u)
  · intro u
    have hlhs : Tendsto (fun n => kmin * ‖(pn n).2.1 u‖ ^ 3) atTop
        (𝓝 (kmin * ‖p.2.1 u‖ ^ 3)) :=
      ((continuous_const.mul ((continuous_norm.comp continuous_id).pow 3)).tendsto _).comp
        (hp2 u)
    have hrhs : Tendsto
        (fun n => ((starRingEnd ℂ) ((pn n).2.1 u) * (pn n).2.2 u).im) atTop
        (𝓝 (((starRingEnd ℂ) (p.2.1 u) * p.2.2 u).im)) := by
      have hc : Continuous fun z : ℂ × ℂ => ((starRingEnd ℂ) z.1 * z.2).im :=
        Complex.continuous_im.comp
          ((Complex.continuous_conj.comp continuous_fst).mul continuous_snd)
      exact (hc.tendsto _).comp ((hp2 u).prodMk_nhds (hp3 u))
    exact le_of_tendsto_of_tendsto' hlhs hrhs
      (fun n => (hmem n).curv_lb u)
  · intro u hu v hv
    have hrhs : Tendsto (fun n => ‖(pn n).1 u - (pn n).1 v‖) atTop
        (𝓝 ‖p.1 u - p.1 v‖) :=
      (continuous_norm.tendsto _).comp ((hp1 u).sub (hp1 v))
    exact ge_of_tendsto hrhs
      (Eventually.of_forall fun n => (hmem n).chord u hu v hv)

instance completeSpace_variableTube (c C kmin delta : ℝ) :
    CompleteSpace (variableTube c C kmin delta) :=
  haveI : IsClosed (variableTube c C kmin delta) :=
    isClosed_variableTube c C kmin delta
  IsClosed.completeSpace_coe

theorem periodic_vel {c C kmin delta : ℝ} {p : Data}
    (hp : IsVariableTubeMember c C kmin delta p) : Periodic (⇑p.2.1) 1 :=
  MarkedSpace.periodic_of_hasDerivAt hp.hasDerivAt_curve hp.periodic

theorem periodic_acc {c C kmin delta : ℝ} {p : Data}
    (hp : IsVariableTubeMember c C kmin delta p) : Periodic (⇑p.2.2) 1 :=
  MarkedSpace.periodic_of_hasDerivAt hp.hasDerivAt_vel (periodic_vel hp)

/-- The parameter-invariant unit-tangent transform in a variable marking. -/
def geometricUnitTangent (p : Data) (u : ℝ) : ℂ :=
  p.1 u + p.2.1 u / (‖p.2.1 u‖ : ℂ)

def geometricUnitTangentOnUnit (p : Data) : Icc (0 : ℝ) 1 → ℂ :=
  fun u => geometricUnitTangent p u.1

theorem periodic_geometricUnitTangent {c C kmin delta : ℝ} {p : Data}
    (hp : IsVariableTubeMember c C kmin delta p) :
    Periodic (geometricUnitTangent p) 1 := by
  intro u
  simp [geometricUnitTangent, hp.periodic u, periodic_vel hp u]

theorem range_positionOnUnit {c C kmin delta : ℝ} {p : Data}
    (hp : IsVariableTubeMember c C kmin delta p) :
    range (MarkedSpace.positionOnUnit p) = range (⇑p.1) := by
  rw [← hp.periodic.image_Icc one_pos 0]
  ext z
  simp [MarkedSpace.positionOnUnit]

theorem range_geometricUnitTangentOnUnit {c C kmin delta : ℝ} {p : Data}
    (hp : IsVariableTubeMember c C kmin delta p) :
    range (geometricUnitTangentOnUnit p) = range (geometricUnitTangent p) := by
  rw [← (periodic_geometricUnitTangent hp).image_Icc one_pos 0]
  ext z
  simp [geometricUnitTangentOnUnit]

theorem continuousAt_geometricUnitTangent_pair {p : Data}
    {u : Icc (0 : ℝ) 1} (hV : p.2.1 u.1 ≠ 0) :
    ContinuousAt
      (fun q : Data × Icc (0 : ℝ) 1 =>
        geometricUnitTangent q.1 q.2.1) (p, u) := by
  have hu : Continuous fun q : Data × Icc (0 : ℝ) 1 => q.2.1 :=
    continuous_subtype_val.comp continuous_snd
  have hpos : Continuous fun q : Data × Icc (0 : ℝ) 1 => q.1.1 q.2.1 :=
    continuous_eval.comp ((continuous_fst.comp continuous_fst).prodMk hu)
  have hvel : Continuous fun q : Data × Icc (0 : ℝ) 1 => q.1.2.1 q.2.1 :=
    continuous_eval.comp
      ((continuous_fst.comp (continuous_snd.comp continuous_fst)).prodMk hu)
  have hden : Continuous fun q : Data × Icc (0 : ℝ) 1 =>
      (‖q.1.2.1 q.2.1‖ : ℂ) :=
    Complex.continuous_ofReal.comp hvel.norm
  have hden0 : (‖p.2.1 u.1‖ : ℂ) ≠ 0 := by
    exact_mod_cast (norm_ne_zero_iff.mpr hV)
  exact hpos.continuousAt.add
    (hvel.continuousAt.div hden.continuousAt hden0)

theorem tendsto_geometricUnitTangentOnUnit
    {P : ℕ → Data} {p : Data}
    {uN : ℕ → Icc (0 : ℝ) 1} {u : Icc (0 : ℝ) 1}
    (hP : Tendsto P atTop (nhds p)) (hu : Tendsto uN atTop (nhds u))
    (hp : p.2.1 u.1 ≠ 0) :
    Tendsto (fun n => geometricUnitTangentOnUnit (P n) (uN n)) atTop
      (nhds (geometricUnitTangentOnUnit p u)) := by
  have hpair : Tendsto (fun n => (P n, uN n)) atTop (nhds (p, u)) := by
    simpa only [nhds_prod_eq] using hP.prodMk hu
  exact (continuousAt_geometricUnitTangent_pair hp).tendsto.comp hpair

/-- Exact geometric unit-tangent range edges are closed under simultaneous
marked convergence in a common positive-speed variable tube. -/
theorem range_geometricUnitTangent_closed_under_marked_limits
    {c C kmin dlt : ℝ} (hc : 0 < c)
    {frontN rearN : ℕ → Data} {front rear : Data}
    (hfrontN : ∀ n, IsVariableTubeMember c C kmin dlt (frontN n))
    (hrearN : ∀ n, IsVariableTubeMember c C kmin dlt (rearN n))
    (hfront : IsVariableTubeMember c C kmin dlt front)
    (hrear : IsVariableTubeMember c C kmin dlt rear)
    (hfrontConv : Tendsto frontN atTop (nhds front))
    (hrearConv : Tendsto rearN atTop (nhds rear))
    (hfinite : ∀ n, range (⇑(frontN n).1) =
      range (geometricUnitTangent (rearN n))) :
    range (⇑front.1) = range (geometricUnitTangent rear) := by
  have hnormalized : ∀ n,
      range (MarkedSpace.positionOnUnit (frontN n)) =
        range (geometricUnitTangentOnUnit (rearN n)) := by
    intro n
    rw [range_positionOnUnit (hfrontN n),
      range_geometricUnitTangentOnUnit (hrearN n)]
    exact hfinite n
  have hfrontFixed : ∀ u, Tendsto
      (fun n => MarkedSpace.positionOnUnit (frontN n) u) atTop
      (nhds (MarkedSpace.positionOnUnit front u)) := fun u =>
    MarkedSpace.tendsto_positionOnUnit hfrontConv tendsto_const_nhds
  have hrearMoving : ∀ (phi : ℕ → ℕ), StrictMono phi →
      ∀ (uN : ℕ → Icc (0 : ℝ) 1) u, Tendsto uN atTop (nhds u) →
      Tendsto (fun n => geometricUnitTangentOnUnit (rearN (phi n)) (uN n)) atTop
        (nhds (geometricUnitTangentOnUnit rear u)) := by
    intro phi hphi uN u hu
    apply tendsto_geometricUnitTangentOnUnit
      (hrearConv.comp hphi.tendsto_atTop) hu
    exact norm_ne_zero_iff.mp
      (ne_of_gt (lt_of_lt_of_le hc (hrear.speed_lb u.1)))
  have hrearFixed : ∀ u, Tendsto
      (fun n => geometricUnitTangentOnUnit (rearN n) u) atTop
      (nhds (geometricUnitTangentOnUnit rear u)) := fun u => by
    apply tendsto_geometricUnitTangentOnUnit hrearConv tendsto_const_nhds
    exact norm_ne_zero_iff.mp
      (ne_of_gt (lt_of_lt_of_le hc (hrear.speed_lb u.1)))
  have hfrontMoving : ∀ (phi : ℕ → ℕ), StrictMono phi →
      ∀ (uN : ℕ → Icc (0 : ℝ) 1) u, Tendsto uN atTop (nhds u) →
      Tendsto (fun n => MarkedSpace.positionOnUnit (frontN (phi n)) (uN n)) atTop
        (nhds (MarkedSpace.positionOnUnit front u)) := by
    intro phi hphi uN u hu
    exact MarkedSpace.tendsto_positionOnUnit
      (hfrontConv.comp hphi.tendsto_atTop) hu
  have hforward : range (MarkedSpace.positionOnUnit front) ⊆
      range (geometricUnitTangentOnUnit rear) :=
    MarkedSpace.range_subset_of_seqCompact_limits
      hfrontFixed hrearMoving hnormalized
  have hbackward : range (geometricUnitTangentOnUnit rear) ⊆
      range (MarkedSpace.positionOnUnit front) :=
    MarkedSpace.range_subset_of_seqCompact_limits hrearFixed hfrontMoving
      (fun n => (hnormalized n).symm)
  rw [range_positionOnUnit hfront,
    range_geometricUnitTangentOnUnit hrear] at hforward hbackward
  exact Set.Subset.antisymm hforward hbackward

/-- Every ordinary tube member is a variable tube member, with its perimeter
as both the pointwise lower and upper speed. -/
theorem ofTubeMember {c kmin dlt : ℝ} {p : Data}
    (hp : IsTubeMember c kmin dlt p) :
    IsVariableTubeMember c (perim p) kmin dlt p where
  hasDerivAt_curve := hp.hasDerivAt_curve
  hasDerivAt_vel := hp.hasDerivAt_vel
  periodic := hp.periodic
  speed_lb := hp.speed_lb
  speed_ub := fun u => (norm_vel_eq_perim hp u).le
  curv_lb := hp.curv_lb
  chord := hp.chord

end VariableMarkedTube
