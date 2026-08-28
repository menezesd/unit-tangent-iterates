import UnitTangentIterates.MarkedDistanceCurvature
import UnitTangentIterates.UnitTangent

/-!
# Closedness of the unit-tangent range relation

In normalized marked coordinates the unit-tangent image of `p` is the range
of `u ↦ p(u) + p'(u) / perim p`.  This presentation is jointly continuous in
the marked datum and in the compact parameter `u ∈ [0,1]`.  Consequently the
relation `range front = range (unitTangentMap rear)` is closed under marked
convergence inside a common positive-speed tube.
-/

noncomputable section

open Filter Function Set Topology

namespace MarkedSpace

/-- The unit-tangent transform written in the normalized marked parameter. -/
def normalizedUnitTangent (p : Data) (u : ℝ) : ℂ :=
  p.1 u + p.2.1 u / perim p

/-- Position and normalized unit tangent restricted to one compact period. -/
def positionOnUnit (p : Data) : Set.Icc (0 : ℝ) 1 → ℂ := fun u => p.1 u.1

def normalizedUnitTangentOnUnit (p : Data) : Set.Icc (0 : ℝ) 1 → ℂ :=
  fun u => normalizedUnitTangent p u.1

/-- The derivative of the physical arclength parametrization in marked
coordinates. -/
theorem hasDerivAt_ev_of_tube {c kmin dlt : ℝ} (hc : 0 < c) {p : Data}
    (hp : IsTubeMember c kmin dlt p) (s : ℝ) :
    HasDerivAt (ev p) (p.2.1 (s / perim p) / perim p) s := by
  have hP : perim p ≠ 0 := ne_of_gt (perim_pos hc hp)
  have hinner : HasDerivAt (fun t : ℝ => t / perim p) (1 / perim p) s := by
    simpa [div_eq_mul_inv, one_div] using (hasDerivAt_id s).div_const (perim p)
  have h := (hp.hasDerivAt_curve (s / perim p)).scomp s hinner
  simpa [ev, Function.comp_def, div_eq_mul_inv, one_div, smul_eq_mul,
    mul_comm, hP] using h

@[simp] theorem unitTangentMap_ev_apply {c kmin dlt : ℝ} (hc : 0 < c)
    {p : Data} (hp : IsTubeMember c kmin dlt p) (s : ℝ) :
    UnitTangent.unitTangentMap (ev p) s =
      normalizedUnitTangent p (s / perim p) := by
  rw [UnitTangent.unitTangentMap, (hasDerivAt_ev_of_tube hc hp s).deriv]
  rfl

/-- The physical unit-tangent image equals the normalized marked image. -/
theorem range_unitTangentMap_ev_eq_normalized {c kmin dlt : ℝ} (hc : 0 < c)
    {p : Data} (hp : IsTubeMember c kmin dlt p) :
    range (UnitTangent.unitTangentMap (ev p)) = range (normalizedUnitTangent p) := by
  have hP : perim p ≠ 0 := ne_of_gt (perim_pos hc hp)
  apply Set.Subset.antisymm
  · rintro z ⟨s, rfl⟩
    exact ⟨s / perim p, (unitTangentMap_ev_apply hc hp s).symm⟩
  · rintro z ⟨u, rfl⟩
    refine ⟨perim p * u, ?_⟩
    rw [unitTangentMap_ev_apply hc hp]
    congr 1
    field_simp [hP]

/-- The normalized unit-tangent expression is period one. -/
theorem periodic_normalizedUnitTangent {c kmin dlt : ℝ} {p : Data}
    (hp : IsTubeMember c kmin dlt p) :
    Periodic (normalizedUnitTangent p) 1 := by
  intro u
  simp [normalizedUnitTangent, hp.periodic u, periodic_vel hp u]

/-- Restricting the marked position to `[0,1]` does not change its range. -/
theorem range_positionOnUnit {c kmin dlt : ℝ} {p : Data}
    (hp : IsTubeMember c kmin dlt p) :
    range (positionOnUnit p) = range (⇑p.1) := by
  rw [← hp.periodic.image_Icc one_pos 0]
  ext z
  simp [positionOnUnit]

/-- Restricting the normalized unit-tangent expression to `[0,1]` does not
change its range. -/
theorem range_normalizedUnitTangentOnUnit {c kmin dlt : ℝ} {p : Data}
    (hp : IsTubeMember c kmin dlt p) :
    range (normalizedUnitTangentOnUnit p) = range (normalizedUnitTangent p) := by
  rw [← (periodic_normalizedUnitTangent hp).image_Icc one_pos 0]
  ext z
  simp [normalizedUnitTangentOnUnit]

/-- Joint continuity of the normalized unit-tangent expression at every
positive-perimeter marked datum. -/
theorem continuousAt_normalizedUnitTangent_pair {p : Data}
    {u : Set.Icc (0 : ℝ) 1} (hP : perim p ≠ 0) :
    ContinuousAt
      (fun q : Data × Set.Icc (0 : ℝ) 1 =>
        normalizedUnitTangent q.1 q.2.1) (p, u) := by
  have hu : Continuous fun q : Data × Set.Icc (0 : ℝ) 1 => q.2.1 :=
    continuous_subtype_val.comp continuous_snd
  have hpos : Continuous fun q : Data × Set.Icc (0 : ℝ) 1 => q.1.1 q.2.1 :=
    continuous_eval.comp
      ((continuous_fst.comp continuous_fst).prodMk hu)
  have hvel : Continuous fun q : Data × Set.Icc (0 : ℝ) 1 => q.1.2.1 q.2.1 :=
    continuous_eval.comp
      ((continuous_fst.comp (continuous_snd.comp continuous_fst)).prodMk hu)
  have hvel0 : Continuous fun q : Data => q.2.1 0 :=
    continuous_eval_const 0 |>.comp (continuous_fst.comp continuous_snd)
  have hper : Continuous fun q : Data × Set.Icc (0 : ℝ) 1 => (perim q.1 : ℂ) :=
    Complex.continuous_ofReal.comp (hvel0.norm.comp continuous_fst)
  have hPc : (perim p : ℂ) ≠ 0 := by exact_mod_cast hP
  exact hpos.continuousAt.add (hvel.continuousAt.div hper.continuousAt hPc)

/-- Moving normalized unit-tangent evaluations converge under simultaneous
marked-data and parameter convergence. -/
theorem tendsto_normalizedUnitTangentOnUnit
    {P : ℕ → Data} {p : Data}
    {uN : ℕ → Set.Icc (0 : ℝ) 1} {u : Set.Icc (0 : ℝ) 1}
    (hP : Tendsto P atTop (nhds p)) (hu : Tendsto uN atTop (nhds u))
    (hp : perim p ≠ 0) :
    Tendsto (fun n => normalizedUnitTangentOnUnit (P n) (uN n)) atTop
      (nhds (normalizedUnitTangentOnUnit p u)) := by
  have hpair : Tendsto (fun n => (P n, uN n)) atTop (nhds (p, u)) := by
    simpa only [nhds_prod_eq] using hP.prodMk hu
  exact (continuousAt_normalizedUnitTangent_pair hp).tendsto.comp hpair

/-- Moving position evaluations converge under simultaneous marked-data and
parameter convergence. -/
theorem tendsto_positionOnUnit
    {P : ℕ → Data} {p : Data}
    {uN : ℕ → Set.Icc (0 : ℝ) 1} {u : Set.Icc (0 : ℝ) 1}
    (hP : Tendsto P atTop (nhds p)) (hu : Tendsto uN atTop (nhds u)) :
    Tendsto (fun n => positionOnUnit (P n) (uN n)) atTop
      (nhds (positionOnUnit p u)) := by
  have hfun : Tendsto (fun n => (P n).1) atTop (nhds p.1) :=
    (continuous_fst.tendsto p).comp hP
  have huval : Tendsto (fun n => (uN n).1) atTop (nhds u.1) :=
    continuous_subtype_val.continuousAt.tendsto.comp hu
  have hpair : Tendsto (fun n => ((P n).1, (uN n).1)) atTop
      (nhds (p.1, u.1)) := by
    simpa only [nhds_prod_eq] using hfun.prodMk huval
  simpa only [positionOnUnit, Function.comp_apply] using
    continuous_eval.continuousAt.tendsto.comp hpair

/-- A range inclusion survives compact-parameter convergence. -/
theorem range_subset_of_seqCompact_limits
    {U Z : Type*} [TopologicalSpace U] [SeqCompactSpace U]
    [TopologicalSpace Z] [T2Space Z]
    {fN gN : ℕ → U → Z} {f g : U → Z}
    (hf : ∀ u, Tendsto (fun n => fN n u) atTop (nhds (f u)))
    (hg : ∀ (phi : ℕ → ℕ), StrictMono phi → ∀ (uN : ℕ → U) u,
      Tendsto uN atTop (nhds u) →
      Tendsto (fun n => gN (phi n) (uN n)) atTop (nhds (g u)))
    (hrange : ∀ n, range (fN n) = range (gN n)) :
    range f ⊆ range g := by
  rintro _ ⟨u, rfl⟩
  have hex : ∀ n, ∃ v, gN n v = fN n u := by
    intro n
    simpa only [Set.mem_range] using (show fN n u ∈ range (gN n) by
      rw [← hrange n]
      exact ⟨u, rfl⟩)
  choose vN hvN using hex
  obtain ⟨v, phi, hphi, hv⟩ := SeqCompactSpace.tendsto_subseq vN
  have hf' := (hf u).comp hphi.tendsto_atTop
  have hg' := hg phi hphi (vN ∘ phi) v hv
  refine ⟨v, ?_⟩
  apply tendsto_nhds_unique hg'
  have hf'' : Tendsto (fun n => fN (phi n) u) atTop (nhds (f u)) := by
    simpa only [Function.comp_apply] using hf'
  exact hf''.congr' (Eventually.of_forall fun n => (hvN (phi n)).symm)

/-- **Closed unit-tangent range relation.**  Exact finite unit-tangent range
relations pass to simultaneous marked limits in a common positive-speed tube.
No steering phase, inverse-arclength selection, or curvature convergence is
needed for this range-level conclusion. -/
theorem range_unitTangentMap_closed_under_marked_limits
    {c kmin dlt : ℝ} (hc : 0 < c)
    {frontN rearN : ℕ → Data} {front rear : Data}
    (hfrontN : ∀ n, IsTubeMember c kmin dlt (frontN n))
    (hrearN : ∀ n, IsTubeMember c kmin dlt (rearN n))
    (hfront : IsTubeMember c kmin dlt front)
    (hrear : IsTubeMember c kmin dlt rear)
    (hfrontConv : Tendsto frontN atTop (nhds front))
    (hrearConv : Tendsto rearN atTop (nhds rear))
    (hfinite : ∀ n, range (ev (frontN n)) =
      range (UnitTangent.unitTangentMap (ev (rearN n)))) :
    range (ev front) = range (UnitTangent.unitTangentMap (ev rear)) := by
  have hnormalized : ∀ n,
      range (positionOnUnit (frontN n)) =
        range (normalizedUnitTangentOnUnit (rearN n)) := by
    intro n
    calc
      range (positionOnUnit (frontN n)) = range (ev (frontN n)) := by
        rw [range_positionOnUnit (hfrontN n), range_ev hc (hfrontN n)]
      _ = range (UnitTangent.unitTangentMap (ev (rearN n))) := hfinite n
      _ = range (normalizedUnitTangentOnUnit (rearN n)) := by
        rw [range_unitTangentMap_ev_eq_normalized hc (hrearN n),
          range_normalizedUnitTangentOnUnit (hrearN n)]
  have hfrontFixed : ∀ u, Tendsto
      (fun n => positionOnUnit (frontN n) u) atTop
      (nhds (positionOnUnit front u)) := fun u =>
    tendsto_positionOnUnit hfrontConv tendsto_const_nhds
  have hrearMoving : ∀ (phi : ℕ → ℕ), StrictMono phi →
      ∀ (uN : ℕ → Set.Icc (0 : ℝ) 1) u,
      Tendsto uN atTop (nhds u) → Tendsto
        (fun n => normalizedUnitTangentOnUnit (rearN (phi n)) (uN n)) atTop
        (nhds (normalizedUnitTangentOnUnit rear u)) := fun phi hphi uN u hu =>
    tendsto_normalizedUnitTangentOnUnit
      (hrearConv.comp hphi.tendsto_atTop) hu
      (ne_of_gt (perim_pos hc hrear))
  have hrearFixed : ∀ u, Tendsto
      (fun n => normalizedUnitTangentOnUnit (rearN n) u) atTop
      (nhds (normalizedUnitTangentOnUnit rear u)) := fun u =>
    tendsto_normalizedUnitTangentOnUnit hrearConv tendsto_const_nhds
      (ne_of_gt (perim_pos hc hrear))
  have hfrontMoving : ∀ (phi : ℕ → ℕ), StrictMono phi →
      ∀ (uN : ℕ → Set.Icc (0 : ℝ) 1) u,
      Tendsto uN atTop (nhds u) → Tendsto
        (fun n => positionOnUnit (frontN (phi n)) (uN n)) atTop
        (nhds (positionOnUnit front u)) := fun phi hphi uN u hu =>
    tendsto_positionOnUnit (hfrontConv.comp hphi.tendsto_atTop) hu
  have hforward : range (positionOnUnit front) ⊆
      range (normalizedUnitTangentOnUnit rear) :=
    range_subset_of_seqCompact_limits hfrontFixed hrearMoving hnormalized
  have hbackward : range (normalizedUnitTangentOnUnit rear) ⊆
      range (positionOnUnit front) :=
    range_subset_of_seqCompact_limits hrearFixed hfrontMoving
      (fun n => (hnormalized n).symm)
  apply Set.Subset.antisymm
  · calc
      range (ev front) = range (positionOnUnit front) :=
        (range_ev hc hfront).trans (range_positionOnUnit hfront).symm
      _ ⊆ range (normalizedUnitTangentOnUnit rear) := hforward
      _ = range (UnitTangent.unitTangentMap (ev rear)) :=
        (range_normalizedUnitTangentOnUnit hrear).trans
          (range_unitTangentMap_ev_eq_normalized hc hrear).symm
  · calc
      range (UnitTangent.unitTangentMap (ev rear)) =
          range (normalizedUnitTangentOnUnit rear) :=
        (range_unitTangentMap_ev_eq_normalized hc hrear).trans
          (range_normalizedUnitTangentOnUnit hrear).symm
      _ ⊆ range (positionOnUnit front) := hbackward
      _ = range (ev front) :=
        (range_positionOnUnit hfront).trans (range_ev hc hfront).symm

end MarkedSpace
