import Mathlib
import UnitTangentIterates.PathMetric

/-!
# Rigid motions of marked curves, and the path pseudodistance modulo a rigid motion

The comparison of two curves in *A Noncircular Oval with Convex Unit-Tangent
Iterates* is a comparison of their **curvatures**: the theorem *Curvature-measure
matching* bounds the `L¹` distance of the curvature of the rear of a two-cap
pair and the periodized curvature of the model, and the lemma *Compatible
markings* (`RigidMotions.lean`) then aligns the two curves by a rigid motion.
A curvature determines its curve only up to such a motion, so a statement about
the curves themselves has to be either taken modulo the rigid motions or stated
for one particular normalization.

This file provides the first option for the path pseudodistance of
`PathMetric.lean`.

* `rigidData a w p` — the marked curve `p` moved by `z ↦ a + wz`, with its
  velocity and acceleration; `rigidData_comp` composes two such motions and
  `isTubeMember_rigidData` shows that a member of the tube is carried to a
  member of the tube with the same constants when `‖w‖ = 1`;
* `PathMetric.NormalPath.congrEnds`, `pathDist_congr` — the path pseudodistance
  depends only on the *curves* of its two arguments;
* `rigidPathOf`, `pathDist_rigidData` — a normal path may be moved with its
  ends at the same cost, so the path pseudodistance is invariant under a common
  rigid motion of the two curves;
* `pathDistRigid` — the path pseudodistance taken modulo a rigid motion, the
  infimum over the motions of the second curve, with its pseudometric axioms
  `pathDistRigid_nonneg`, `pathDistRigid_self`, `pathDistRigid_comm`,
  `pathDistRigid_triangle`, and `pathDistRigid_le_pathDist`;
* `pathDistRigid_le_of_rigid_images` — **two curves that are rigid images of
  two curves at path pseudodistance `d` are at pseudodistance at most `d`
  modulo a rigid motion**, the two motions being unrelated.
-/

noncomputable section

open Set Function MarkedSpace PathMetric
open scoped BoundedContinuousFunction

namespace MarkedRigid

/-- The rotations of the plane form a nonempty index set. -/
instance : Nonempty {w : ℂ // ‖w‖ = 1} := ⟨⟨1, by simp⟩⟩

/-! ### Rigid motions of the data -/

/-- **The marked curve `p` moved by the rigid motion `z ↦ a + wz`** (a genuine
rigid motion of the plane when `‖w‖ = 1`), together with its velocity and its
acceleration. -/
def rigidData (a w : ℂ) (p : Data) : Data :=
  (BoundedContinuousFunction.const ℝ a + w • p.1, w • p.2.1, w • p.2.2)

@[simp] theorem rigidData_curve (a w : ℂ) (p : Data) (u : ℝ) :
    (rigidData a w p).1 u = a + w * p.1 u := rfl

@[simp] theorem rigidData_vel (a w : ℂ) (p : Data) (u : ℝ) :
    (rigidData a w p).2.1 u = w * p.2.1 u := rfl

@[simp] theorem rigidData_acc (a w : ℂ) (p : Data) (u : ℝ) :
    (rigidData a w p).2.2 u = w * p.2.2 u := rfl

@[simp] theorem rigidData_id (p : Data) : rigidData 0 1 p = p := by
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> ext u <;> simp

/-- Two rigid motions compose. -/
theorem rigidData_comp (a w b v : ℂ) (p : Data) :
    rigidData a w (rigidData b v p) = rigidData (a + w * b) (w * v) p := by
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> ext u <;> simp [mul_add, mul_assoc, add_assoc]

/-- The inverse motion undoes `rigidData a w`. -/
theorem rigidData_inv {w : ℂ} (hw : w ≠ 0) (a : ℂ) (p : Data) :
    rigidData (-(w⁻¹ * a)) w⁻¹ (rigidData a w p) = p := by
  rw [rigidData_comp]
  simp [inv_mul_cancel₀ hw]

/-- **A rigid motion carries the tube to itself.** -/
theorem isTubeMember_rigidData {c kmin delta : ℝ} {p : Data} {a w : ℂ} (hw : ‖w‖ = 1)
    (hp : IsTubeMember c kmin delta p) : IsTubeMember c kmin delta (rigidData a w p) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro u
    exact ((hp.hasDerivAt_curve u).const_mul w).const_add a
  · intro u
    exact (hp.hasDerivAt_vel u).const_mul w
  · intro u
    show a + w * p.1 (u + 1) = a + w * p.1 u
    rw [hp.periodic u]
  · intro u v
    show ‖w * p.2.1 u‖ = ‖w * p.2.1 v‖
    rw [norm_mul, norm_mul, hp.speed_const u v]
  · intro u
    show c ≤ ‖w * p.2.1 u‖
    rw [norm_mul, hw, one_mul]
    exact hp.speed_lb u
  · intro u
    have hnorm : ‖w * p.2.1 u‖ = ‖p.2.1 u‖ := by simp [hw]
    have hconj : ((starRingEnd ℂ) (w * p.2.1 u) * (w * p.2.2 u))
        = (‖w‖ ^ 2 : ℝ) * ((starRingEnd ℂ) (p.2.1 u) * p.2.2 u) := by
      have : ((starRingEnd ℂ) w * w) = ((‖w‖ ^ 2 : ℝ) : ℂ) := by
        rw [Complex.conj_mul']
        norm_cast
      calc ((starRingEnd ℂ) (w * p.2.1 u) * (w * p.2.2 u))
          = ((starRingEnd ℂ) w * w) * ((starRingEnd ℂ) (p.2.1 u) * p.2.2 u) := by
            simp [map_mul]; ring
        _ = ((‖w‖ ^ 2 : ℝ) : ℂ) * ((starRingEnd ℂ) (p.2.1 u) * p.2.2 u) := by rw [this]
        _ = (‖w‖ ^ 2 : ℝ) * ((starRingEnd ℂ) (p.2.1 u) * p.2.2 u) := by norm_cast
    have := hp.curv_lb u
    simp only [rigidData_vel, rigidData_acc, hnorm, hconj, hw]
    simpa using this
  · intro u hu v hv
    have h := hp.chord u hu v hv
    have hsub : (a + w * p.1 u) - (a + w * p.1 v) = w * (p.1 u - p.1 v) := by ring
    simp only [rigidData_curve, hsub, norm_mul, hw, one_mul]
    exact h

/-! ### The path pseudodistance depends only on the curves -/

namespace NormalPathRigid

open PathMetric.NormalPath

/-- A normal path between two marked curves is a normal path between any marked
curves with the same **curves**: the other two components of the data play no
part in the definition. -/
def congrEnds {p q p' q' : Data} (Γ : NormalPath p q)
    (hp : ∀ u, p'.1 u = p.1 u) (hq : ∀ u, q'.1 u = q.1 u) : NormalPath p' q' :=
  { Γ with
    start := fun u => by rw [hp u]; exact Γ.start u
    finish := fun u => by rw [hq u]; exact Γ.finish u }

@[simp] theorem cost_congrEnds {p q p' q' : Data} (Γ : NormalPath p q)
    (hp : ∀ u, p'.1 u = p.1 u) (hq : ∀ u, q'.1 u = q.1 u) :
    cost (congrEnds Γ hp hq) = cost Γ := rfl

/-- **A normal path may be moved by a rigid motion together with its ends**, at
the same cost. -/
def rigidPathOf {p q p' q' : Data} {a w : ℂ} (hw : ‖w‖ = 1) (Γ : NormalPath p q)
    (hp : ∀ u, p'.1 u = a + w * p.1 u) (hq : ∀ u, q'.1 u = a + w * q.1 u) :
    NormalPath p' q' where
  T := Γ.T
  T_pos := Γ.T_pos
  X := fun t u => a + w * Γ.X t u
  eta := Γ.eta
  nu := fun t u => w * Γ.nu t u
  m := Γ.m
  start := fun u => by rw [hp u, Γ.start u]
  finish := fun u => by rw [hq u, Γ.finish u]
  hasDerivAt_time := fun t u => by
    have h := ((Γ.hasDerivAt_time t u).const_mul w).const_add a
    convert h using 1
    ring
  cont_vel := fun u => by
    have h : Continuous fun t => w * ((Γ.eta t u : ℂ) * Γ.nu t u) :=
      (Γ.cont_vel u).const_smul w
    exact h.congr (fun t => by ring)
  norm_nu := fun t u => by rw [norm_mul, hw, Γ.norm_nu t u, one_mul]
  cont_m := Γ.cont_m
  m_nonneg := Γ.m_nonneg
  m_stop := Γ.m_stop
  abs_eta_le := Γ.abs_eta_le
  le_m_L1 := Γ.le_m_L1
  le_m_sup := Γ.le_m_sup

@[simp] theorem cost_rigidPathOf {p q p' q' : Data} {a w : ℂ} (hw : ‖w‖ = 1)
    (Γ : NormalPath p q) (hp : ∀ u, p'.1 u = a + w * p.1 u)
    (hq : ∀ u, q'.1 u = a + w * q.1 u) : cost (rigidPathOf hw Γ hp hq) = cost Γ := rfl

end NormalPathRigid

open NormalPathRigid

/-- **The path pseudodistance depends only on the curves.** -/
theorem pathDist_congr {p q p' q' : Data} (hp : ∀ u, p'.1 u = p.1 u)
    (hq : ∀ u, q'.1 u = q.1 u) : pathDist p' q' = pathDist p q := by
  have hset : costSet p' q' = costSet p q := by
    refine Set.Subset.antisymm ?_ ?_
    · rintro z ⟨Γ, rfl⟩
      exact ⟨congrEnds Γ (fun u => (hp u).symm) (fun u => (hq u).symm), rfl⟩
    · rintro z ⟨Γ, rfl⟩
      exact ⟨congrEnds Γ hp hq, rfl⟩
  unfold pathDist
  rw [hset]

/-- **The path pseudodistance is invariant under a common rigid motion.** -/
theorem pathDist_rigidData {a w : ℂ} (hw : ‖w‖ = 1) (p q : Data) :
    pathDist (rigidData a w p) (rigidData a w q) = pathDist p q := by
  have hw0 : w ≠ 0 := by
    intro h
    rw [h] at hw
    simp at hw
  have hwinv : ‖w⁻¹‖ = 1 := by simp [hw]
  have hset : costSet (rigidData a w p) (rigidData a w q) = costSet p q := by
    refine Set.Subset.antisymm ?_ ?_
    · rintro z ⟨Γ, rfl⟩
      refine ⟨rigidPathOf (a := -(w⁻¹ * a)) hwinv Γ ?_ ?_, rfl⟩ <;>
        · intro u
          show _ = -(w⁻¹ * a) + w⁻¹ * (a + w * _)
          rw [mul_add, ← mul_assoc, inv_mul_cancel₀ hw0, one_mul, neg_add_cancel_left]
          rfl
    · rintro z ⟨Γ, rfl⟩
      exact ⟨rigidPathOf (a := a) hw Γ (fun _ => rfl) (fun _ => rfl), rfl⟩
  unfold pathDist
  rw [hset]

/-! ### The pseudodistance modulo a rigid motion -/

/-- **The path pseudodistance taken modulo a rigid motion**: the infimum, over
the rigid motions of the second curve, of the path pseudodistance. -/
def pathDistRigid (p q : Data) : ℝ :=
  ⨅ z : ℂ × {w : ℂ // ‖w‖ = 1}, pathDist p (rigidData z.1 z.2.1 q)

theorem bddBelow_pathDist_rigid (p q : Data) :
    BddBelow (range fun z : ℂ × {w : ℂ // ‖w‖ = 1} => pathDist p (rigidData z.1 z.2.1 q)) :=
  ⟨0, by rintro x ⟨z, rfl⟩; exact pathDist_nonneg _ _⟩

theorem pathDistRigid_nonneg (p q : Data) : 0 ≤ pathDistRigid p q :=
  le_ciInf fun _ => pathDist_nonneg _ _

/-- The distance modulo a rigid motion is at most the distance to any rigid
image. -/
theorem pathDistRigid_le (p q : Data) (a : ℂ) {w : ℂ} (hw : ‖w‖ = 1) :
    pathDistRigid p q ≤ pathDist p (rigidData a w q) :=
  ciInf_le (bddBelow_pathDist_rigid p q) (a, ⟨w, hw⟩)

theorem pathDistRigid_le_pathDist (p q : Data) : pathDistRigid p q ≤ pathDist p q := by
  simpa using pathDistRigid_le p q 0 (w := 1) (by simp)

@[simp] theorem pathDistRigid_self (p : Data) : pathDistRigid p p = 0 :=
  le_antisymm (by simpa using pathDistRigid_le_pathDist p p) (pathDistRigid_nonneg p p)

theorem pathDistRigid_comm (p q : Data) : pathDistRigid p q = pathDistRigid q p := by
  have key : ∀ x y : Data, pathDistRigid x y ≤ pathDistRigid y x := by
    intro x y
    refine le_ciInf fun z => ?_
    obtain ⟨a, w, hw⟩ := z
    have hw0 : w ≠ 0 := by
      intro h; rw [h] at hw; simp at hw
    have hwinv : ‖w⁻¹‖ = 1 := by simp [hw]
    have h : pathDist y (rigidData a w x) = pathDist x (rigidData (-(w⁻¹ * a)) w⁻¹ y) := by
      have h1 : pathDist y (rigidData a w x)
          = pathDist (rigidData (-(w⁻¹ * a)) w⁻¹ y)
              (rigidData (-(w⁻¹ * a)) w⁻¹ (rigidData a w x)) :=
        (pathDist_rigidData hwinv _ _).symm
      rw [h1, rigidData_inv hw0, pathDist_comm]
    rw [h]
    exact pathDistRigid_le x y _ hwinv
  exact le_antisymm (key p q) (key q p)

/-- **The triangle inequality modulo a rigid motion**, for curves joined by
normal paths after a motion. -/
theorem pathDistRigid_triangle {p q r : Data}
    (hpq : ∀ (a : ℂ) (w : {w : ℂ // ‖w‖ = 1}), Nonempty (NormalPath p (rigidData a w.1 q)))
    (hqr : ∀ (a : ℂ) (w : {w : ℂ // ‖w‖ = 1}), Nonempty (NormalPath q (rigidData a w.1 r))) :
    pathDistRigid p r ≤ pathDistRigid p q + pathDistRigid q r := by
  have hstep : ∀ (a₁ : ℂ) (w₁ : {w : ℂ // ‖w‖ = 1}) (a₂ : ℂ) (w₂ : {w : ℂ // ‖w‖ = 1}),
      pathDistRigid p r
        ≤ pathDist p (rigidData a₁ w₁.1 q) + pathDist q (rigidData a₂ w₂.1 r) := by
    intro a₁ w₁ a₂ w₂
    have hmove : pathDist (rigidData a₁ w₁.1 q) (rigidData a₁ w₁.1 (rigidData a₂ w₂.1 r))
        = pathDist q (rigidData a₂ w₂.1 r) := pathDist_rigidData w₁.2 _ _
    have hne : Nonempty (NormalPath (rigidData a₁ w₁.1 q)
        (rigidData a₁ w₁.1 (rigidData a₂ w₂.1 r))) := by
      obtain ⟨Γ⟩ := hqr a₂ w₂
      exact ⟨rigidPathOf (a := a₁) w₁.2 Γ (fun _ => rfl) (fun _ => rfl)⟩
    have htri : pathDist p (rigidData a₁ w₁.1 (rigidData a₂ w₂.1 r))
        ≤ pathDist p (rigidData a₁ w₁.1 q)
          + pathDist (rigidData a₁ w₁.1 q) (rigidData a₁ w₁.1 (rigidData a₂ w₂.1 r)) :=
      pathDist_triangle (hpq a₁ w₁) hne
    rw [hmove] at htri
    refine le_trans ?_ htri
    rw [rigidData_comp]
    exact pathDistRigid_le p r _ (by rw [norm_mul, w₁.2, w₂.2, one_mul])
  have h1 : ∀ (a₂ : ℂ) (w₂ : {w : ℂ // ‖w‖ = 1}),
      pathDistRigid p r - pathDist q (rigidData a₂ w₂.1 r) ≤ pathDistRigid p q := by
    intro a₂ w₂
    refine le_ciInf fun z => ?_
    have := hstep z.1 z.2 a₂ w₂
    linarith
  have h2 : pathDistRigid p r - pathDistRigid p q ≤ pathDistRigid q r := by
    refine le_ciInf fun z => ?_
    have := h1 z.1 z.2
    linarith
  linarith

/-! ### Comparing two rigid images -/

/-- **Two curves that are rigid images of two curves at path pseudodistance `d`
are at pseudodistance at most `d` modulo a rigid motion**, the two motions being
unrelated.  This is the form in which a bound proved for one normalization of
the curves — the reconstruction from the curvature, say — is transported to
arbitrary representatives. -/
theorem pathDistRigid_le_of_rigid_images {p q p' q' : Data} {a₁ w₁ a₂ w₂ : ℂ}
    (hw₁ : ‖w₁‖ = 1) (hw₂ : ‖w₂‖ = 1)
    (hp : ∀ u, p'.1 u = a₁ + w₁ * p.1 u) (hq : ∀ u, q'.1 u = a₂ + w₂ * q.1 u) :
    pathDistRigid p' q' ≤ pathDist p q := by
  have hw₂0 : w₂ ≠ 0 := by
    intro h; rw [h] at hw₂; simp at hw₂
  set w : ℂ := w₁ * w₂⁻¹ with hwdef
  have hw : ‖w‖ = 1 := by
    rw [hwdef, norm_mul, hw₁, norm_inv, hw₂]
    norm_num
  set a : ℂ := a₁ - w * a₂ with hadef
  have hcurve : ∀ u, (rigidData a w q').1 u = a₁ + w₁ * q.1 u := by
    intro u
    rw [rigidData_curve, hq u, hadef, hwdef]
    field_simp
    ring
  calc pathDistRigid p' q' ≤ pathDist p' (rigidData a w q') := pathDistRigid_le p' q' a hw
    _ = pathDist (rigidData a₁ w₁ p) (rigidData a₁ w₁ q) :=
        pathDist_congr (p := rigidData a₁ w₁ p) (q := rigidData a₁ w₁ q)
          (fun u => hp u) (fun u => hcurve u)
    _ = pathDist p q := pathDist_rigidData hw₁ p q

end MarkedRigid
