import Mathlib
import UnitTangentIterates.PathMetric
import UnitTangentIterates.MarkedReparamRigidity

/-!
# Shifting the marking, and the marked distance taken modulo the marking

A marked curve of `MarkedSpace.lean` is a curve *together with a base point*:
the value of the parameter at which the curve is marked.  The gauge flow which
carries a normal path of fronts to the normal path of its selected rears moves
that base point along the curve, so the terminal curve of the path-distance
bound is the marked selected inverse of the terminal front with its marking
shifted (`SelectedInverseRearOwnShift.lean`).

This file provides the two notions needed to state such a bound.

* `shiftData b p` — the marked curve `p` with its marking shifted by `b`, that
  is, the curve `u ↦ p(u + b)` with its velocity and acceleration;
* `eq_shiftData_of_curve` — a member of the tube whose curve is the shifted
  curve of another member *is* that shift;
* `shiftPathOf`, `shiftPath` — a normal path may be shifted with its ends, at
  the same cost, so that `pathDist_shiftData`: the path pseudodistance is
  invariant under a common shift of the markings;
* `pathDistShift` — the path pseudodistance taken modulo the marking, the
  infimum over the shifts of the second curve, together with its pseudometric
  axioms `pathDistShift_nonneg`, `pathDistShift_self`, `pathDistShift_comm` and
  `pathDistShift_triangle`.
-/

noncomputable section

open Set Function MarkedSpace

namespace MarkedShift

/-- The translation `u ↦ u + b`, as a continuous map. -/
def shiftMap (b : ℝ) : C(ℝ, ℝ) := ContinuousMap.mk (fun u => u + b) (by fun_prop)

/-- **The marked curve with its marking shifted by `b`.** -/
def shiftData (b : ℝ) (p : Data) : Data :=
  (p.1.compContinuous (shiftMap b), p.2.1.compContinuous (shiftMap b),
    p.2.2.compContinuous (shiftMap b))

@[simp] theorem shiftData_curve (b : ℝ) (p : Data) (u : ℝ) :
    (shiftData b p).1 u = p.1 (u + b) := rfl

@[simp] theorem shiftData_vel (b : ℝ) (p : Data) (u : ℝ) :
    (shiftData b p).2.1 u = p.2.1 (u + b) := rfl

@[simp] theorem shiftData_acc (b : ℝ) (p : Data) (u : ℝ) :
    (shiftData b p).2.2 u = p.2.2 (u + b) := rfl

@[simp] theorem shiftData_zero (p : Data) : shiftData 0 p = p := by
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> ext u <;> simp

/-- **A member of the tube tracing a shift of another member is that shift.**
The velocity and the acceleration of a member of the tube are the derivatives
of its curve, so they are determined by it. -/
theorem eq_shiftData_of_curve {cR kR dR c k d : ℝ} {R q : Data}
    (hR : IsTubeMember cR kR dR R) (hq : IsTubeMember c k d q) {b : ℝ}
    (h : ∀ u, q.1 u = R.1 (u + b)) : q = shiftData b R := by
  have hinner : ∀ u : ℝ, HasDerivAt (fun y : ℝ => y + b) 1 u := fun u => by
    simpa using (hasDerivAt_id u).add_const b
  have h1 : ⇑q.1 = ⇑(shiftData b R).1 := funext h
  have h2 : ∀ u, q.2.1 u = (shiftData b R).2.1 u := by
    intro u
    have hqd : HasDerivAt (⇑q.1) (q.2.1 u) u := hq.hasDerivAt_curve u
    have hsd : HasDerivAt (⇑q.1) (R.2.1 (u + b)) u := by
      rw [h1]
      simpa using (hR.hasDerivAt_curve (u + b)).scomp u (hinner u)
    rw [hqd.unique hsd, shiftData_vel]
  have h2' : ⇑q.2.1 = ⇑(shiftData b R).2.1 := funext h2
  have h3 : ∀ u, q.2.2 u = (shiftData b R).2.2 u := by
    intro u
    have hqd : HasDerivAt (⇑q.2.1) (q.2.2 u) u := hq.hasDerivAt_vel u
    have hsd : HasDerivAt (⇑q.2.1) (R.2.2 (u + b)) u := by
      rw [h2']
      simpa using (hR.hasDerivAt_vel (u + b)).scomp u (hinner u)
    rw [hqd.unique hsd, shiftData_acc]
  exact Prod.ext (BoundedContinuousFunction.ext fun u => h u)
    (Prod.ext (BoundedContinuousFunction.ext fun u => h2 u)
      (BoundedContinuousFunction.ext fun u => h3 u))

/-! ### The path pseudodistance modulo the marking -/

/-- **The path pseudodistance taken modulo the marking**: the infimum, over the
shifts of the marking of the second curve, of the path pseudodistance of
`PathMetric.lean`. -/
def pathDistShift (p q : Data) : ℝ := ⨅ b : ℝ, PathMetric.pathDist p (shiftData b q)

theorem bddBelow_pathDist_shift (p q : Data) :
    BddBelow (range fun b : ℝ => PathMetric.pathDist p (shiftData b q)) :=
  ⟨0, by rintro x ⟨b, rfl⟩; exact PathMetric.pathDist_nonneg _ _⟩

theorem pathDistShift_nonneg (p q : Data) : 0 ≤ pathDistShift p q :=
  le_ciInf fun _ => PathMetric.pathDist_nonneg _ _

/-- The distance modulo the marking is at most the distance to any shift. -/
theorem pathDistShift_le (p q : Data) (b : ℝ) :
    pathDistShift p q ≤ PathMetric.pathDist p (shiftData b q) :=
  ciInf_le (bddBelow_pathDist_shift p q) b

/-- The distance modulo the marking is at most the marked distance. -/
theorem pathDistShift_le_pathDist (p q : Data) :
    pathDistShift p q ≤ PathMetric.pathDist p q := by
  simpa using pathDistShift_le p q 0

/-! ### The shift of a member of the tube -/

/-- The cyclic distance of `MarkedSpace` depends only on the difference of its
arguments modulo one, as long as both pairs lie in `[0,1]`. -/
theorem cyc_eq_of_int_sub {u v u' v' : ℝ} (hu : u ∈ Icc (0:ℝ) 1) (hv : v ∈ Icc (0:ℝ) 1)
    (hu' : u' ∈ Icc (0:ℝ) 1) (hv' : v' ∈ Icc (0:ℝ) 1) {n : ℤ}
    (h : (u - v) - (u' - v') = n) : cyc u v = cyc u' v' := by
  have key : ∀ d : ℝ, 0 ≤ d → d ≤ 1 → min |d| (1 - |d|) = min |d - 1| (1 - |d - 1|) := by
    intro d h0 h1
    rw [abs_of_nonneg h0, abs_of_nonpos (by linarith : d - 1 ≤ 0)]
    have h2 : -(d - 1) = 1 - d := by ring
    rw [h2, min_comm]
    congr 1
    ring
  obtain ⟨hu0, hu1⟩ := hu
  obtain ⟨hv0, hv1⟩ := hv
  obtain ⟨hu'0, hu'1⟩ := hu'
  obtain ⟨hv'0, hv'1⟩ := hv'
  have hn1 : (-2 : ℝ) ≤ (n : ℝ) := by rw [← h]; linarith
  have hn2 : ((n : ℝ)) ≤ 2 := by rw [← h]; linarith
  have hn1' : (-2 : ℤ) ≤ n := by exact_mod_cast hn1
  have hn2' : n ≤ (2 : ℤ) := by exact_mod_cast hn2
  simp only [cyc]
  interval_cases n
  · -- `d = d' - 2`, possible only for `d = -1`, `d' = 1`
    have hd : u - v = -1 := by push_cast at h; linarith
    have hd' : u' - v' = 1 := by push_cast at h; linarith
    rw [hd, hd']
    norm_num
  · -- `d = d' - 1`
    have hd : u - v = (u' - v') - 1 := by push_cast at h; linarith
    rw [hd, ← key (u' - v') (by linarith [h]) (by linarith)]
  · rw [show u - v = u' - v' by push_cast at h; linarith]
  · -- `d = d' + 1`
    have hd : u' - v' = (u - v) - 1 := by push_cast at h; linarith
    rw [hd, ← key (u - v) (by push_cast at h; linarith) (by linarith)]
  · have hd : u - v = 1 := by push_cast at h; linarith
    have hd' : u' - v' = -1 := by push_cast at h; linarith
    rw [hd, hd']
    norm_num

/-- **The shift of a member of the tube is a member of the tube**, with the
same constants. -/
theorem isTubeMember_shiftData {c kmin delta : ℝ} {p : Data}
    (hp : IsTubeMember c kmin delta p) (b : ℝ) :
    IsTubeMember c kmin delta (shiftData b p) := by
  have hinner : ∀ u : ℝ, HasDerivAt (fun y : ℝ => y + b) 1 u := fun u => by
    simpa using (hasDerivAt_id u).add_const b
  have hfract : ∀ y : ℝ, p.1 (Int.fract y) = p.1 y := by
    intro y
    show p.1 (y - ⌊y⌋) = p.1 y
    simpa using hp.periodic.sub_int_mul_eq (x := y) ⌊y⌋
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro u
    simpa using (hp.hasDerivAt_curve (u + b)).scomp u (hinner u)
  · intro u
    simpa using (hp.hasDerivAt_vel (u + b)).scomp u (hinner u)
  · intro u
    simpa [add_right_comm] using hp.periodic (u + b)
  · intro u v
    simpa using hp.speed_const (u + b) (v + b)
  · intro u
    simpa using hp.speed_lb (u + b)
  · intro u
    simpa using hp.curv_lb (u + b)
  · intro u hu v hv
    have hmem : ∀ y : ℝ, Int.fract y ∈ Icc (0:ℝ) 1 :=
      fun y => ⟨Int.fract_nonneg y, le_of_lt (Int.fract_lt_one y)⟩
    have hchord := hp.chord _ (hmem (u + b)) _ (hmem (v + b))
    have hcyc : cyc u v = cyc (Int.fract (u + b)) (Int.fract (v + b)) := by
      refine cyc_eq_of_int_sub hu hv (hmem _) (hmem _) (n := ⌊u + b⌋ - ⌊v + b⌋) ?_
      simp only [Int.fract]
      push_cast
      ring
    rw [hcyc]
    simpa [hfract] using hchord

/-! ### Shifting a normal path -/

open PathMetric PathMetric.NormalPath in
/-- **A normal path may be shifted with its ends.**  Shifting the marking of
every slice of a normal path by `b` gives a normal path between any marked
curves whose curves are the shifts by `b` of the ends, with the same cost
density, hence the same cost. -/
def shiftPathOf {p q p' q' : Data} (b : ℝ) (Γ : NormalPath p q)
    (hp : ∀ u, p'.1 u = p.1 (u + b)) (hq : ∀ u, q'.1 u = q.1 (u + b)) :
    NormalPath p' q' where
  T := Γ.T
  T_pos := Γ.T_pos
  X := fun t u => Γ.X t (u + b)
  eta := fun t u => Γ.eta t (u + b)
  nu := fun t u => Γ.nu t (u + b)
  m := Γ.m
  start := fun u => by rw [Γ.start (u + b), hp u]
  finish := fun u => by rw [Γ.finish (u + b), hq u]
  hasDerivAt_time := fun t u => Γ.hasDerivAt_time t (u + b)
  cont_vel := fun u => Γ.cont_vel (u + b)
  norm_nu := fun t u => Γ.norm_nu t (u + b)
  cont_m := Γ.cont_m
  m_nonneg := Γ.m_nonneg
  m_stop := Γ.m_stop
  abs_eta_le := fun t u => Γ.abs_eta_le t (u + b)
  le_m_L1 := by
    intro t
    by_cases hint : IntervalIntegrable (fun u => |Γ.eta t (u + b)|) MeasureTheory.volume 0 1
    · have hle : (∫ u in (0:ℝ)..1, |Γ.eta t (u + b)|) ≤ ∫ _u in (0:ℝ)..1, Γ.m t :=
        intervalIntegral.integral_mono_on (by norm_num) hint
          intervalIntegrable_const (fun u _ => Γ.abs_eta_le t (u + b))
      simpa using hle
    · rw [intervalIntegral.integral_undef hint]
      exact Γ.m_nonneg t
  le_m_sup := by
    intro t j hj
    have h : MarkedTopology.supNorm (iteratedDeriv j (fun u => Γ.eta t (u + b)))
        = MarkedTopology.supNorm (iteratedDeriv j (Γ.eta t)) := by
      rw [iteratedDeriv_comp_add_const]
      exact (Equiv.addRight b).surjective.iSup_comp
        (fun v => |iteratedDeriv j (Γ.eta t) v|)
    rw [h]
    exact Γ.le_m_sup t j hj

open PathMetric PathMetric.NormalPath in
@[simp] theorem cost_shiftPathOf {p q p' q' : Data} (b : ℝ) (Γ : NormalPath p q)
    (hp : ∀ u, p'.1 u = p.1 (u + b)) (hq : ∀ u, q'.1 u = q.1 (u + b)) :
    cost (shiftPathOf b Γ hp hq) = cost Γ := rfl

open PathMetric PathMetric.NormalPath in
/-- The normal path with both ends shifted by `b`. -/
def shiftPath {p q : Data} (b : ℝ) (Γ : NormalPath p q) :
    NormalPath (shiftData b p) (shiftData b q) :=
  shiftPathOf b Γ (fun _ => rfl) (fun _ => rfl)

open PathMetric PathMetric.NormalPath in
@[simp] theorem cost_shiftPath {p q : Data} (b : ℝ) (Γ : NormalPath p q) :
    cost (shiftPath b Γ) = cost Γ := rfl

open PathMetric in
/-- **The path pseudodistance is invariant under a common shift of the
markings.** -/
theorem pathDist_shiftData (b : ℝ) (p q : Data) :
    pathDist (shiftData b p) (shiftData b q) = pathDist p q := by
  have hset : costSet (shiftData b p) (shiftData b q) = costSet p q := by
    refine Set.Subset.antisymm ?_ ?_
    · rintro z ⟨Γ, rfl⟩
      exact ⟨shiftPathOf (-b) Γ (fun u => by simp) (fun u => by simp), rfl⟩
    · rintro z ⟨Γ, rfl⟩
      exact ⟨shiftPath b Γ, rfl⟩
  unfold pathDist
  rw [hset]

open PathMetric in
theorem shiftData_add (b c : ℝ) (p : Data) :
    shiftData b (shiftData c p) = shiftData (b + c) p := by
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> ext u <;> simp [add_assoc]

/-! ### The pseudometric axioms modulo the marking -/

open PathMetric in
@[simp] theorem pathDistShift_self (p : Data) : pathDistShift p p = 0 :=
  le_antisymm (by simpa using pathDistShift_le p p 0) (pathDistShift_nonneg p p)

open PathMetric in
theorem pathDistShift_comm (p q : Data) : pathDistShift p q = pathDistShift q p := by
  have key : ∀ x y : Data, pathDistShift x y ≤ pathDistShift y x := by
    intro x y
    refine le_ciInf fun b => ?_
    have h : pathDist y (shiftData b x) = pathDist x (shiftData (-b) y) := by
      have h1 : pathDist y (shiftData b x)
          = pathDist (shiftData (-b) y) (shiftData (-b) (shiftData b x)) :=
        (pathDist_shiftData (-b) y (shiftData b x)).symm
      have h2 : shiftData (-b) (shiftData b x) = x := by
        refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> ext u <;> simp
      rw [h1, h2, pathDist_comm]
    rw [h]
    exact pathDistShift_le x y (-b)
  exact le_antisymm (key p q) (key q p)

open PathMetric in
/-- **The triangle inequality modulo the marking**, for curves joined by normal
paths after a shift. -/
theorem pathDistShift_triangle {p q r : Data}
    (hpq : ∀ b : ℝ, Nonempty (NormalPath p (shiftData b q)))
    (hqr : ∀ b : ℝ, Nonempty (NormalPath q (shiftData b r))) :
    pathDistShift p r ≤ pathDistShift p q + pathDistShift q r := by
  have hstep : ∀ b₁ b₂ : ℝ,
      pathDistShift p r ≤ pathDist p (shiftData b₁ q) + pathDist q (shiftData b₂ r) := by
    intro b₁ b₂
    have h1 : pathDist (shiftData b₁ q) (shiftData b₁ (shiftData b₂ r))
        = pathDist q (shiftData b₂ r) := pathDist_shiftData b₁ q (shiftData b₂ r)
    have htri : pathDist p (shiftData (b₁ + b₂) r)
        ≤ pathDist p (shiftData b₁ q) + pathDist (shiftData b₁ q) (shiftData (b₁ + b₂) r) := by
      refine pathDist_triangle (hpq b₁) ?_
      rw [← shiftData_add b₁ b₂ r]
      exact ⟨shiftPath b₁ (hqr b₂).some⟩
    have h2 : pathDist (shiftData b₁ q) (shiftData (b₁ + b₂) r) = pathDist q (shiftData b₂ r) := by
      rw [← shiftData_add b₁ b₂ r, h1]
    rw [h2] at htri
    exact le_trans (pathDistShift_le p r (b₁ + b₂)) htri
  have h1 : ∀ b₂ : ℝ,
      pathDistShift p r - pathDist q (shiftData b₂ r) ≤ pathDistShift p q := by
    intro b₂
    refine le_ciInf fun b₁ => ?_
    have := hstep b₁ b₂
    linarith
  have h2 : pathDistShift p r - pathDistShift p q ≤ pathDistShift q r := by
    refine le_ciInf fun b₂ => ?_
    have := h1 b₂
    linarith
  linarith

open PathMetric PathMetric.NormalPath in
/-- **From a bound on every normal path to a bound in the pseudodistance
modulo the marking.**  If the distance modulo the marking of two curves is at
most `K` times the cost of *every* normal path from `p` to `q`, it is at most
`K` times their path pseudodistance. -/
theorem pathDistShift_le_of_forall_cost {p q x y : Data} {K : ℝ} (hK : 0 ≤ K)
    (hne : Nonempty (NormalPath p q))
    (h : ∀ Γ : NormalPath p q, pathDistShift x y ≤ K * cost Γ) :
    pathDistShift x y ≤ K * pathDist p q := by
  rcases eq_or_lt_of_le hK with rfl | hKpos
  · simpa using h hne.some
  · have hle : pathDistShift x y / K ≤ pathDist p q := by
      refine le_csInf ⟨cost hne.some, ⟨hne.some, rfl⟩⟩ ?_
      rintro z ⟨Γ, rfl⟩
      rw [div_le_iff₀ hKpos]
      have hΓ := h Γ
      linarith [hΓ, mul_comm K (cost Γ)]
    rw [div_le_iff₀ hKpos] at hle
    linarith

end MarkedShift
