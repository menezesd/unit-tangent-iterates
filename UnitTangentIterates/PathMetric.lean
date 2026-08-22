import Mathlib
import UnitTangentIterates.MarkedSpace
import UnitTangentIterates.MarkedTopology

/-!
# The marked geometric path pseudometric on the tube of curves

In the section *Regularizing backward shadowing* of the paper *A Noncircular
Oval with Convex Unit-Tangent Iterates*, two marked curves are compared not by
a sup norm but through the **normal paths** joining them: a path of curves
written in normal gauge, `X_t = η ν`, is assigned the functionals

```
  W(Γ)   = ∫ ‖η_t‖_{L¹} dt,     S_j(Γ) = ∫ ‖∂_s^j η_t‖_{L^∞} dt,
```

(see `MarkedTopology.W` and `MarkedTopology.S`), and the geometric distance of
two curves is the infimum of the cost of the normal paths joining them.  This
file builds that pseudodistance.

All the functionals are taken in the normalized parameter of `MarkedSpace`, in
which every curve has period one; thus the `L¹` density below is `∫₀¹ |η_t|`
over one period of the normalized parameter rather than over one period of
arclength.

A `NormalPath p q` is a normal path from the curve of `p` to the curve of `q`,
together with a continuous **cost density** `m` dominating the densities of the
paper's functionals — the `L¹` norm of `η_t` and the sup norms of `∂_s^j η_t`
for `j ≤ 2` — and vanishing outside the time interval, so that the path comes
to rest at its ends and paths can be concatenated.  Its cost is `∫₀^T m`, an
upper bound for `W + S₀ + S₁ + S₂` up to the normalization of the time
interval.  The pseudodistance `pathDist p q` is the infimum of these costs.

Main results:

* `NormalPath.const`, `NormalPath.reverse`, `NormalPath.concat` : the three
  structural operations on normal paths, with `cost_const`, `cost_reverse` and
  `cost_concat`;
* `NormalPath.norm_sub_le_cost` : along a normal path a point of the curve
  moves at most the cost of the path;
* `NormalPath.W_le_cost`, `NormalPath.S_le_cost` : the cost dominates the
  paper's path functionals `W`, `S₀`, `S₁`, `S₂`;
* `pathDist_nonneg`, `pathDist_self`, `pathDist_comm`, `pathDist_triangle` :
  the pseudometric axioms;
* `norm_sub_le_pathDist` : the path pseudodistance dominates the pointwise
  distance of the curves, hence is finer than the sup metric of `MarkedSpace`;
* `pathDist_le_of_maps_paths` : the criterion for a map of marked curves (the
  selected inverse, in the paper) to be non-expansive for `pathDist`: it
  suffices that it takes normal paths to normal paths of no greater cost.
-/

noncomputable section

open Set MeasureTheory MarkedSpace

namespace PathMetric

/-! ### Two elementary lemmas -/

theorem iteratedDeriv_zero_fun (j : ℕ) : iteratedDeriv j (fun _ : ℝ => (0 : ℝ)) = fun _ => 0 := by
  induction j with
  | zero => simp
  | succ n ih => funext x; simp

theorem supNorm_neg (f : ℝ → ℝ) :
    MarkedTopology.supNorm (fun u => -f u) = MarkedTopology.supNorm f := by
  simp [MarkedTopology.supNorm]

/-- Gluing two derivatives at a point where both velocities vanish. -/
theorem hasDerivAt_glue {f g vf vg : ℝ → ℂ} {a : ℝ}
    (hf : ∀ t, HasDerivAt f (vf t) t) (hg : ∀ t, HasDerivAt g (vg t) t)
    (hval : f a = g a) (hva : vf a = 0) (hvb : vg a = 0) (t : ℝ) :
    HasDerivAt (fun s => if s ≤ a then f s else g s) (if t ≤ a then vf t else vg t) t := by
  rcases lt_trichotomy t a with h | h | h
  · have hmem : Iio a ∈ nhds t := Iio_mem_nhds h
    have heq : (fun s => if s ≤ a then f s else g s) =ᶠ[nhds t] f :=
      Filter.eventuallyEq_of_mem hmem (fun s hs => if_pos (le_of_lt hs))
    rw [if_pos h.le]
    exact (hf t).congr_of_eventuallyEq heq
  · subst h
    rw [if_pos le_rfl, hva]
    have h1 : HasDerivWithinAt (fun s => if s ≤ t then f s else g s) 0 (Iic t) t := by
      refine HasDerivWithinAt.congr ?_ (fun s hs => if_pos hs) (if_pos le_rfl)
      simpa [hva] using (hf t).hasDerivWithinAt (s := Iic t)
    have h2 : HasDerivWithinAt (fun s => if s ≤ t then f s else g s) 0 (Ici t) t := by
      refine HasDerivWithinAt.congr ?_ (fun s hs => ?_) (by rw [if_pos le_rfl, hval])
      · simpa [hvb] using (hg t).hasDerivWithinAt (s := Ici t)
      · rcases eq_or_lt_of_le (mem_Ici.1 hs) with rfl | hlt
        · rw [if_pos le_rfl, hval]
        · rw [if_neg (not_le.mpr hlt)]
    have := h1.union h2
    rw [Iic_union_Ici, hasDerivWithinAt_univ] at this
    exact this
  · have hmem : Ioi a ∈ nhds t := Ioi_mem_nhds h
    have heq : (fun s => if s ≤ a then f s else g s) =ᶠ[nhds t] g :=
      Filter.eventuallyEq_of_mem hmem (fun s hs => if_neg (not_le.mpr hs))
    rw [if_neg (not_le.mpr h)]
    exact (hg t).congr_of_eventuallyEq heq

/-! ### Normal paths -/

/-- A **normal path** from the marked curve `p` to the marked curve `q`: a
family `X t` of curves in the normalized parameter, moving with purely normal
velocity `η ν` (`‖ν‖ = 1`), defined for times `t ∈ [0, T]`, starting at the
curve of `p` and ending at the curve of `q`.

The field `m` is a continuous cost density dominating the densities of the
paper's path functionals `W`, `S₀`, `S₁`, `S₂`; it is required to vanish
outside the open time interval, so that the path comes to rest at both ends and
normal paths can be concatenated. -/
structure NormalPath (p q : Data) where
  /-- the duration of the path. -/
  T : ℝ
  /-- the duration is positive. -/
  T_pos : 0 < T
  /-- the moving curve, in the normalized parameter. -/
  X : ℝ → ℝ → ℂ
  /-- the normal speed. -/
  eta : ℝ → ℝ → ℝ
  /-- the unit normal. -/
  nu : ℝ → ℝ → ℂ
  /-- the cost density. -/
  m : ℝ → ℝ
  /-- the path starts at `p`. -/
  start : ∀ u, X 0 u = p.1 u
  /-- the path ends at `q`. -/
  finish : ∀ u, X T u = q.1 u
  /-- the path is in normal gauge: `X_t = η ν`. -/
  hasDerivAt_time : ∀ t u, HasDerivAt (fun r => X r u) ((eta t u : ℂ) * nu t u) t
  /-- the velocity depends continuously on the time. -/
  cont_vel : ∀ u, Continuous fun t => (eta t u : ℂ) * nu t u
  /-- `ν` is a unit vector. -/
  norm_nu : ∀ t u, ‖nu t u‖ = 1
  /-- the cost density is continuous. -/
  cont_m : Continuous m
  /-- the cost density is nonnegative. -/
  m_nonneg : ∀ t, 0 ≤ m t
  /-- the path is at rest outside its time interval. -/
  m_stop : ∀ t ∉ Ioo (0 : ℝ) T, m t = 0
  /-- the cost density dominates the normal speed. -/
  abs_eta_le : ∀ t u, |eta t u| ≤ m t
  /-- the cost density dominates the `L¹` density of `W`. -/
  le_m_L1 : ∀ t, (∫ u in (0:ℝ)..1, |eta t u|) ≤ m t
  /-- the cost density dominates the densities of `S₀`, `S₁` and `S₂`. -/
  le_m_sup : ∀ t, ∀ j ≤ 2, MarkedTopology.supNorm (iteratedDeriv j (eta t)) ≤ m t

namespace NormalPath

variable {p q r : Data}

/-- The cost of a normal path: the time integral of its cost density. -/
def cost (Γ : NormalPath p q) : ℝ := ∫ t in (0:ℝ)..Γ.T, Γ.m t

theorem eta_stop (Γ : NormalPath p q) {t : ℝ} (ht : t ∉ Ioo (0:ℝ) Γ.T) (u : ℝ) :
    Γ.eta t u = 0 :=
  abs_eq_zero.mp (le_antisymm (by simpa [Γ.m_stop t ht] using Γ.abs_eta_le t u) (abs_nonneg _))

theorem vel_stop (Γ : NormalPath p q) {t : ℝ} (ht : t ∉ Ioo (0:ℝ) Γ.T) (u : ℝ) :
    ((Γ.eta t u : ℂ) * Γ.nu t u) = 0 := by
  rw [Γ.eta_stop ht u]; simp

theorem cost_nonneg (Γ : NormalPath p q) : 0 ≤ cost Γ :=
  intervalIntegral.integral_nonneg Γ.T_pos.le (fun t _ => Γ.m_nonneg t)

/-- **Displacement along a normal path.**  Each point of the curve moves by at
most the cost of the path. -/
theorem norm_sub_le_cost (Γ : NormalPath p q) (u : ℝ) : ‖q.1 u - p.1 u‖ ≤ cost Γ := by
  have hV : IntervalIntegrable (fun t => (Γ.eta t u : ℂ) * Γ.nu t u) volume 0 Γ.T :=
    (Γ.cont_vel u).intervalIntegrable 0 Γ.T
  have hint : (∫ t in (0:ℝ)..Γ.T, (Γ.eta t u : ℂ) * Γ.nu t u) = Γ.X Γ.T u - Γ.X 0 u :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => Γ.hasDerivAt_time t u) hV
  rw [← Γ.finish u, ← Γ.start u, ← hint]
  refine intervalIntegral.norm_integral_le_of_norm_le Γ.T_pos.le
    (Filter.Eventually.of_forall (fun t _ => ?_)) (Γ.cont_m.intervalIntegrable 0 Γ.T)
  rw [norm_mul, Γ.norm_nu t u, Complex.norm_real, Real.norm_eq_abs, mul_one]
  exact Γ.abs_eta_le t u

/-- **The cost dominates the functional `W` of the paper**, for a path run over
the unit time interval. -/
theorem W_le_cost (Γ : NormalPath p q) (hT : Γ.T = 1) : MarkedTopology.W Γ.eta 1 ≤ cost Γ := by
  have hcost : cost Γ = ∫ t in (0:ℝ)..1, Γ.m t := by rw [cost, hT]
  by_cases hint : IntervalIntegrable (fun t => ∫ u in (0:ℝ)..1, |Γ.eta t u|) volume 0 1
  · rw [MarkedTopology.W, hcost]
    exact intervalIntegral.integral_mono_on (by norm_num) hint
      (Γ.cont_m.intervalIntegrable 0 1) (fun t _ => Γ.le_m_L1 t)
  · rw [MarkedTopology.W, intervalIntegral.integral_undef hint]
    exact Γ.cost_nonneg

/-- **The cost dominates the functionals `S₀`, `S₁` and `S₂` of the paper**, for
a path run over the unit time interval. -/
theorem S_le_cost (Γ : NormalPath p q) (hT : Γ.T = 1) {j : ℕ} (hj : j ≤ 2) :
    MarkedTopology.S j Γ.eta ≤ cost Γ := by
  have hcost : cost Γ = ∫ t in (0:ℝ)..1, Γ.m t := by rw [cost, hT]
  by_cases hint : IntervalIntegrable
      (fun t => MarkedTopology.supNorm (iteratedDeriv j (Γ.eta t))) volume 0 1
  · rw [MarkedTopology.S, hcost]
    exact intervalIntegral.integral_mono_on (by norm_num) hint
      (Γ.cont_m.intervalIntegrable 0 1) (fun t _ => Γ.le_m_sup t j hj)
  · rw [MarkedTopology.S, intervalIntegral.integral_undef hint]
    exact Γ.cost_nonneg

/-! ### The three structural operations -/

/-- The constant normal path at a marked curve, of cost zero. -/
def const (p : Data) : NormalPath p p where
  T := 1
  T_pos := one_pos
  X := fun _ u => p.1 u
  eta := fun _ _ => 0
  nu := fun _ _ => 1
  m := fun _ => 0
  start := fun _ => rfl
  finish := fun _ => rfl
  hasDerivAt_time := fun t u => by simpa using hasDerivAt_const t (p.1 u)
  cont_vel := fun _ => by simpa using continuous_const
  norm_nu := fun _ _ => by simp
  cont_m := continuous_const
  m_nonneg := fun _ => le_rfl
  m_stop := fun _ _ => rfl
  abs_eta_le := fun _ _ => by simp
  le_m_L1 := fun _ => by simp
  le_m_sup := fun _ j _ => by
    rw [iteratedDeriv_zero_fun j]
    simp [MarkedTopology.supNorm]

@[simp] theorem cost_const (p : Data) : cost (const p) = 0 := by simp [cost, const]

/-- The reversal of a normal path. -/
def reverse (Γ : NormalPath p q) : NormalPath q p where
  T := Γ.T
  T_pos := Γ.T_pos
  X := fun t u => Γ.X (Γ.T - t) u
  eta := fun t u => -Γ.eta (Γ.T - t) u
  nu := fun t u => Γ.nu (Γ.T - t) u
  m := fun t => Γ.m (Γ.T - t)
  start := fun u => by simpa using Γ.finish u
  finish := fun u => by simpa using Γ.start u
  hasDerivAt_time := by
    intro t u
    have h := (Γ.hasDerivAt_time (Γ.T - t) u).scomp t ((hasDerivAt_id t).const_sub Γ.T)
    simpa [Complex.real_smul] using h
  cont_vel := fun u => by
    have hsub : Continuous fun t : ℝ => Γ.T - t := continuous_const.sub continuous_id
    have h := ((Γ.cont_vel u).comp hsub).neg
    simpa [Function.comp_def] using h
  norm_nu := fun t u => Γ.norm_nu _ u
  cont_m := Γ.cont_m.comp (continuous_const.sub continuous_id)
  m_nonneg := fun t => Γ.m_nonneg _
  m_stop := by
    intro t ht
    refine Γ.m_stop _ (fun hmem => ht ⟨?_, ?_⟩)
    · linarith [hmem.2]
    · linarith [hmem.1]
  abs_eta_le := fun t u => by simpa using Γ.abs_eta_le (Γ.T - t) u
  le_m_L1 := fun t => by simpa using Γ.le_m_L1 (Γ.T - t)
  le_m_sup := fun t j hj => by
    have hfun : (fun u => -Γ.eta (Γ.T - t) u) = -(Γ.eta (Γ.T - t)) := rfl
    have hder : iteratedDeriv j (fun u => -Γ.eta (Γ.T - t) u)
        = fun u => -iteratedDeriv j (Γ.eta (Γ.T - t)) u := by
      funext x; rw [hfun, iteratedDeriv_neg]
    rw [hder, supNorm_neg]
    exact Γ.le_m_sup (Γ.T - t) j hj

theorem cost_reverse (Γ : NormalPath p q) : cost (reverse Γ) = cost Γ := by
  simp only [cost, reverse]
  rw [intervalIntegral.integral_comp_sub_left (fun x => Γ.m x) Γ.T]
  simp

/-- The concatenation of two normal paths. -/
def concat (Γ : NormalPath p q) (Δ : NormalPath q r) : NormalPath p r where
  T := Γ.T + Δ.T
  T_pos := add_pos Γ.T_pos Δ.T_pos
  X := fun t u => if t ≤ Γ.T then Γ.X t u else Δ.X (t - Γ.T) u
  eta := fun t u => if t ≤ Γ.T then Γ.eta t u else Δ.eta (t - Γ.T) u
  nu := fun t u => if t ≤ Γ.T then Γ.nu t u else Δ.nu (t - Γ.T) u
  m := fun t => if t ≤ Γ.T then Γ.m t else Δ.m (t - Γ.T)
  start := fun u => by rw [if_pos Γ.T_pos.le]; exact Γ.start u
  finish := fun u => by
    rw [if_neg (by linarith [Δ.T_pos] : ¬ (Γ.T + Δ.T ≤ Γ.T))]
    simpa using Δ.finish u
  hasDerivAt_time := by
    intro t u
    have hval : Γ.X Γ.T u = Δ.X (Γ.T - Γ.T) u := by
      rw [sub_self, Δ.start u]; exact Γ.finish u
    have hva : (Γ.eta Γ.T u : ℂ) * Γ.nu Γ.T u = 0 := Γ.vel_stop (by simp) u
    have hvb : (Δ.eta (Γ.T - Γ.T) u : ℂ) * Δ.nu (Γ.T - Γ.T) u = 0 := by
      rw [sub_self]; exact Δ.vel_stop (by simp) u
    have h := hasDerivAt_glue (f := fun s => Γ.X s u) (g := fun s => Δ.X (s - Γ.T) u)
      (vf := fun s => (Γ.eta s u : ℂ) * Γ.nu s u)
      (vg := fun s => (Δ.eta (s - Γ.T) u : ℂ) * Δ.nu (s - Γ.T) u)
      (fun s => Γ.hasDerivAt_time s u)
      (fun s => by
        simpa using (Δ.hasDerivAt_time (s - Γ.T) u).scomp s ((hasDerivAt_id s).sub_const Γ.T))
      hval hva hvb t
    convert h using 1
    split_ifs <;> rfl
  cont_vel := by
    intro u
    have hfun : (fun t => ((if t ≤ Γ.T then Γ.eta t u else Δ.eta (t - Γ.T) u : ℝ) : ℂ) *
        (if t ≤ Γ.T then Γ.nu t u else Δ.nu (t - Γ.T) u)) =
        fun t => if t ≤ Γ.T then ((Γ.eta t u : ℂ) * Γ.nu t u)
          else ((Δ.eta (t - Γ.T) u : ℂ) * Δ.nu (t - Γ.T) u) := by
      funext t; split_ifs <;> rfl
    rw [hfun]
    refine Continuous.if_le (Γ.cont_vel u)
      ((Δ.cont_vel u).comp (continuous_id.sub continuous_const)) continuous_id
      continuous_const (fun x hx => ?_)
    subst hx
    rw [Γ.vel_stop (by simp) u]
    simp only [sub_self]
    exact (Δ.vel_stop (by simp) u).symm
  norm_nu := fun t u => by split_ifs with h; exacts [Γ.norm_nu t u, Δ.norm_nu _ u]
  cont_m := by
    refine Continuous.if_le Γ.cont_m (Δ.cont_m.comp (continuous_id.sub continuous_const))
      continuous_id continuous_const (fun x hx => ?_)
    subst hx
    rw [Γ.m_stop _ (by simp)]
    simp only [sub_self]
    exact (Δ.m_stop _ (by simp)).symm
  m_nonneg := fun t => by split_ifs with h; exacts [Γ.m_nonneg t, Δ.m_nonneg _]
  m_stop := by
    intro t ht
    rw [mem_Ioo, not_and_or, not_lt, not_lt] at ht
    by_cases h : t ≤ Γ.T
    · rw [if_pos h]
      refine Γ.m_stop t (fun hmem => ?_)
      rcases ht with ht | ht
      · linarith [hmem.1]
      · linarith [Δ.T_pos, hmem.2]
    · rw [if_neg h]
      push_neg at h
      refine Δ.m_stop _ (fun hmem => ?_)
      rcases ht with ht | ht
      · linarith [Γ.T_pos]
      · linarith [hmem.2]
  abs_eta_le := fun t u => by split_ifs with h; exacts [Γ.abs_eta_le t u, Δ.abs_eta_le _ u]
  le_m_L1 := by
    intro t
    by_cases h : t ≤ Γ.T
    · simp only [if_pos h]; exact Γ.le_m_L1 t
    · simp only [if_neg h]; exact Δ.le_m_L1 _
  le_m_sup := by
    intro t j hj
    by_cases h : t ≤ Γ.T
    · simp only [if_pos h]; exact Γ.le_m_sup t j hj
    · simp only [if_neg h]; exact Δ.le_m_sup _ j hj

theorem cost_concat (Γ : NormalPath p q) (Δ : NormalPath q r) :
    cost (concat Γ Δ) = cost Γ + cost Δ := by
  have hcont : Continuous (concat Γ Δ).m := (concat Γ Δ).cont_m
  have hsplit : (∫ t in (0:ℝ)..(Γ.T + Δ.T), (concat Γ Δ).m t)
      = (∫ t in (0:ℝ)..Γ.T, (concat Γ Δ).m t) + ∫ t in Γ.T..(Γ.T + Δ.T), (concat Γ Δ).m t :=
    (intervalIntegral.integral_add_adjacent_intervals (hcont.intervalIntegrable _ _)
      (hcont.intervalIntegrable _ _)).symm
  have h1 : (∫ t in (0:ℝ)..Γ.T, (concat Γ Δ).m t) = cost Γ := by
    refine intervalIntegral.integral_congr (fun t ht => ?_)
    rw [uIcc_of_le Γ.T_pos.le] at ht
    exact if_pos ht.2
  have h2 : (∫ t in Γ.T..(Γ.T + Δ.T), (concat Γ Δ).m t) = cost Δ := by
    have hc : (∫ t in Γ.T..(Γ.T + Δ.T), (concat Γ Δ).m t)
        = ∫ t in Γ.T..(Γ.T + Δ.T), Δ.m (t - Γ.T) := by
      refine intervalIntegral.integral_congr (fun t ht => ?_)
      rw [uIcc_of_le (by linarith [Δ.T_pos] : Γ.T ≤ Γ.T + Δ.T)] at ht
      rw [show (concat Γ Δ).m t = if t ≤ Γ.T then Γ.m t else Δ.m (t - Γ.T) from rfl]
      by_cases hlt : Γ.T < t
      · rw [if_neg (not_le.mpr hlt)]
      · have hte : t = Γ.T := le_antisymm (not_lt.mp hlt) ht.1
        subst hte
        rw [if_pos le_rfl, sub_self, Γ.m_stop _ (by simp), Δ.m_stop _ (by simp)]
    rw [hc, intervalIntegral.integral_comp_sub_right (fun x => Δ.m x) Γ.T]
    simp [cost]
  rw [show cost (concat Γ Δ) = ∫ t in (0:ℝ)..(Γ.T + Δ.T), (concat Γ Δ).m t from rfl, hsplit, h1, h2]

end NormalPath

/-! ### The path pseudodistance -/

open NormalPath

/-- The set of costs of the normal paths from `p` to `q`. -/
def costSet (p q : Data) : Set ℝ := {c | ∃ Γ : NormalPath p q, cost Γ = c}

theorem bddBelow_costSet (p q : Data) : BddBelow (costSet p q) := by
  refine ⟨0, ?_⟩
  rintro c ⟨Γ, rfl⟩
  exact Γ.cost_nonneg

/-- **The marked geometric path pseudodistance**: the infimum of the costs of
the normal paths joining two marked curves. -/
def pathDist (p q : Data) : ℝ := sInf (costSet p q)

theorem pathDist_nonneg (p q : Data) : 0 ≤ pathDist p q := by
  refine Real.sInf_nonneg ?_
  rintro c ⟨Γ, rfl⟩
  exact Γ.cost_nonneg

theorem pathDist_le_cost {p q : Data} (Γ : NormalPath p q) : pathDist p q ≤ cost Γ :=
  csInf_le (bddBelow_costSet p q) ⟨Γ, rfl⟩

@[simp] theorem pathDist_self (p : Data) : pathDist p p = 0 :=
  le_antisymm (by simpa using pathDist_le_cost (const p)) (pathDist_nonneg p p)

theorem costSet_comm (p q : Data) : costSet p q = costSet q p := by
  have h : ∀ a b : Data, costSet a b ⊆ costSet b a := by
    rintro a b c ⟨Γ, rfl⟩
    exact ⟨reverse Γ, cost_reverse Γ⟩
  exact Subset.antisymm (h p q) (h q p)

theorem pathDist_comm (p q : Data) : pathDist p q = pathDist q p := by
  unfold pathDist; rw [costSet_comm]

/-- **The triangle inequality** for the path pseudodistance, for curves joined
by normal paths. -/
theorem pathDist_triangle {p q r : Data} (hpq : Nonempty (NormalPath p q))
    (hqr : Nonempty (NormalPath q r)) :
    pathDist p r ≤ pathDist p q + pathDist q r := by
  refine le_of_forall_pos_le_add (fun ε hε => ?_)
  have hne1 : (costSet p q).Nonempty := ⟨cost hpq.some, ⟨hpq.some, rfl⟩⟩
  have hne2 : (costSet q r).Nonempty := ⟨cost hqr.some, ⟨hqr.some, rfl⟩⟩
  obtain ⟨c₁, ⟨Γ, rfl⟩, h₁⟩ := exists_lt_of_csInf_lt hne1
    (show pathDist p q < pathDist p q + ε / 2 by linarith)
  obtain ⟨c₂, ⟨Δ, rfl⟩, h₂⟩ := exists_lt_of_csInf_lt hne2
    (show pathDist q r < pathDist q r + ε / 2 by linarith)
  have hle := pathDist_le_cost (concat Γ Δ)
  rw [cost_concat] at hle
  linarith

/-- **The path pseudodistance dominates the pointwise distance of the curves**:
it is finer than the sup metric of the space of marked curves. -/
theorem norm_sub_le_pathDist {p q : Data} (h : Nonempty (NormalPath p q)) (u : ℝ) :
    ‖q.1 u - p.1 u‖ ≤ pathDist p q := by
  refine le_csInf ⟨cost h.some, ⟨h.some, rfl⟩⟩ ?_
  rintro c ⟨Γ, rfl⟩
  exact Γ.norm_sub_le_cost u

/-- **The path pseudodistance dominates the sup distance of the two curves.**
The curve components are compared in the sup metric of `MarkedSpace`. -/
theorem dist_fst_le_pathDist {p q : Data} (h : Nonempty (NormalPath p q)) :
    dist p.1 q.1 ≤ pathDist p q := by
  refine (BoundedContinuousFunction.dist_le (pathDist_nonneg p q)).2 (fun u => ?_)
  rw [dist_eq_norm, norm_sub_rev]
  exact norm_sub_le_pathDist h u

/-- **A criterion for non-expansiveness.**  A map of marked curves which takes
every normal path from `p` to `q` to a normal path of no greater cost does not
increase the path pseudodistance. -/
theorem pathDist_le_of_maps_paths {F : Data → Data} {p q : Data}
    (h : ∀ Γ : NormalPath p q, ∃ Γ' : NormalPath (F p) (F q), cost Γ' ≤ cost Γ)
    (hne : Nonempty (NormalPath p q)) :
    pathDist (F p) (F q) ≤ pathDist p q := by
  refine le_csInf ⟨cost hne.some, ⟨hne.some, rfl⟩⟩ ?_
  rintro c ⟨Γ, rfl⟩
  obtain ⟨Γ', hΓ'⟩ := h Γ
  exact le_trans (pathDist_le_cost Γ') hΓ'

/-- **A Lipschitz criterion.**  A map of marked curves which takes every normal
path from `p` to `q` to a normal path of cost at most `C` times as large is
`C`-Lipschitz for the path pseudodistance.  This is the shape of the paper's
lemma *Inverse Jacobi estimates*, whose scalar cores are formalized in
`JacobiEstimates.lean`: the selected inverse multiplies the path functionals by
constants depending only on the curvature bound. -/
theorem pathDist_le_mul_of_maps_paths {F : Data → Data} {p q : Data} {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ Γ : NormalPath p q, ∃ Γ' : NormalPath (F p) (F q), cost Γ' ≤ C * cost Γ)
    (hne : Nonempty (NormalPath p q)) :
    pathDist (F p) (F q) ≤ C * pathDist p q := by
  have hS : (costSet p q).Nonempty := ⟨cost hne.some, ⟨hne.some, rfl⟩⟩
  refine le_of_forall_pos_le_add (fun ε hε => ?_)
  have hCpos : 0 < C + 1 := by linarith
  have hεpos : 0 < ε / (C + 1) := by positivity
  obtain ⟨c, ⟨Γ, rfl⟩, hc⟩ := exists_lt_of_csInf_lt hS
    (show pathDist p q < pathDist p q + ε / (C + 1) by linarith)
  obtain ⟨Γ', hΓ'⟩ := h Γ
  have h1 : pathDist (F p) (F q) ≤ C * cost Γ := le_trans (pathDist_le_cost Γ') hΓ'
  have h2 : C * cost Γ ≤ C * (pathDist p q + ε / (C + 1)) :=
    mul_le_mul_of_nonneg_left hc.le hC
  have h3 : C * (ε / (C + 1)) ≤ ε := by
    rw [mul_div_assoc', div_le_iff₀ hCpos]
    nlinarith
  nlinarith [h1, h2, h3]

end PathMetric
