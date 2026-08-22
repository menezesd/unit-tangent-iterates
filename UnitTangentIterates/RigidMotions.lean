import Mathlib
import UnitTangentIterates.UnitTangent

/-!
# Rigid motions, markings and phase shifts

This file formalizes the lemma *Compatible markings* of the paper
*A Noncircular Oval with Convex Unit-Tangent Iterates*.

Plane curves are modelled as maps `ℝ → ℂ`, as in `UnitTangentIterates.UnitTangent`;
a rigid motion is `z ↦ a * z + b` with `‖a‖ = 1`, and a change of the marked
phase is a shift `s ↦ s + c` of the arclength parameter.

The content of the lemma is that

* the unit-tangent transform commutes with rigid motions, so a rotation of a
  rear–front pair `𝒯R = F` again produces such a pair
  (`unitTangentMap_rigidMotion`, `rigidMotion_pair`);
* arclength and intrinsic curvature are rotation invariant
  (`norm_deriv_rigidMotion`, `curvature_rigidMotion`);
* an arclength shift commutes with `𝒯` as well and changes neither speed nor
  curvature (`unitTangentMap_shift`, `norm_deriv_shift`, `curvature_shift`);
* there is a *unique* rotation carrying a given marked unit tangent to another
  one (`existsUnique_rotation_of_marked_tangent`), which is the normalization
  used to compare consecutive model curves.
-/

noncomputable section

open Complex

namespace RigidMotions

open UnitTangent

variable {γ : ℝ → ℂ} {T : ℝ → ℂ} {a b : ℂ}

/-- The image of a curve under the rigid motion `z ↦ a z + b`. -/
def move (a b : ℂ) (γ : ℝ → ℂ) : ℝ → ℂ := fun s => a * γ s + b

lemma hasDerivAt_move (hγ : ∀ s, HasDerivAt γ (T s) s) (a b : ℂ) (s : ℝ) :
    HasDerivAt (move a b γ) (a * T s) s :=
  ((hγ s).const_mul a).add_const b

lemma deriv_move (hγ : ∀ s, HasDerivAt γ (T s) s) (a b : ℂ) (s : ℝ) :
    deriv (move a b γ) s = a * T s :=
  (hasDerivAt_move hγ a b s).deriv

/-- **The unit-tangent transform commutes with rigid motions.** -/
theorem unitTangentMap_rigidMotion (hγ : ∀ s, HasDerivAt γ (T s) s) (a b : ℂ) (s : ℝ) :
    unitTangentMap (move a b γ) s = a * unitTangentMap γ s + b := by
  simp only [unitTangentMap, move, deriv_move hγ a b s, (hγ s).deriv]
  ring

/-- A rotated rear–front pair is again a rear–front pair: if `𝒯R = F` then
`𝒯(aR + b) = aF + b`. -/
theorem rigidMotion_pair {R F : ℝ → ℂ} {TR : ℝ → ℂ}
    (hR : ∀ s, HasDerivAt R (TR s) s) (hRF : unitTangentMap R = F) (a b : ℂ) :
    unitTangentMap (move a b R) = move a b F := by
  funext s
  rw [unitTangentMap_rigidMotion hR a b s, hRF, move]

/-- Arclength is rotation invariant: a rotation preserves the speed. -/
theorem norm_deriv_rigidMotion (hγ : ∀ s, HasDerivAt γ (T s) s) (ha : ‖a‖ = 1) (b : ℂ) (s : ℝ) :
    ‖deriv (move a b γ) s‖ = ‖deriv γ s‖ := by
  rw [deriv_move hγ a b s, (hγ s).deriv, norm_mul, ha, one_mul]

/-- Intrinsic curvature is rotation invariant.  For a unit-speed curve the
curvature `k` is defined by `γ'' = i k γ'`; this relation is preserved by every
rigid motion, with the same `k`. -/
theorem curvature_rigidMotion {k : ℝ → ℝ} (hγ : ∀ s, HasDerivAt γ (T s) s)
    (hT : ∀ s, HasDerivAt T (Complex.I * (k s : ℂ) * T s) s) (a b : ℂ) (s : ℝ) :
    HasDerivAt (deriv (move a b γ)) (Complex.I * (k s : ℂ) * deriv (move a b γ) s) s := by
  have hfun : deriv (move a b γ) = fun s => a * T s := by
    funext u; exact deriv_move hγ a b u
  rw [hfun]
  refine ((hT s).const_mul a).congr_deriv ?_
  show a * (Complex.I * (k s : ℂ) * T s) = Complex.I * (k s : ℂ) * (a * T s)
  ring

/-! ### Arclength shifts -/

/-- A constant shift of the arclength parameter. -/
def shift (c : ℝ) (γ : ℝ → ℂ) : ℝ → ℂ := fun s => γ (s + c)

lemma hasDerivAt_shift (hγ : ∀ s, HasDerivAt γ (T s) s) (c : ℝ) (s : ℝ) :
    HasDerivAt (shift c γ) (T (s + c)) s := by
  have h : HasDerivAt (fun u : ℝ => u + c) 1 s := by
    simpa using (hasDerivAt_id s).add_const c
  simpa [shift] using (hγ (s + c)).scomp s h

/-- The unit-tangent transform commutes with a shift of the marked phase. -/
theorem unitTangentMap_shift (hγ : ∀ s, HasDerivAt γ (T s) s) (c : ℝ) (s : ℝ) :
    unitTangentMap (shift c γ) s = unitTangentMap γ (s + c) := by
  simp only [unitTangentMap, shift, (hasDerivAt_shift hγ c s).deriv, (hγ (s + c)).deriv]

/-- A shift of the marked phase does not change the speed. -/
theorem norm_deriv_shift (hγ : ∀ s, HasDerivAt γ (T s) s) (c : ℝ) (s : ℝ) :
    ‖deriv (shift c γ) s‖ = ‖deriv γ (s + c)‖ := by
  rw [(hasDerivAt_shift hγ c s).deriv, (hγ (s + c)).deriv]

/-- A shift of the marked phase does not change the curvature either: it only
reparametrizes it. -/
theorem curvature_shift {k : ℝ → ℝ} (hγ : ∀ s, HasDerivAt γ (T s) s)
    (hT : ∀ s, HasDerivAt T (Complex.I * (k s : ℂ) * T s) s) (c : ℝ) (s : ℝ) :
    HasDerivAt (deriv (shift c γ)) (Complex.I * (k (s + c) : ℂ) * deriv (shift c γ) s) s := by
  have hfun : deriv (shift c γ) = fun u => T (u + c) := by
    funext u; exact (hasDerivAt_shift hγ c u).deriv
  rw [hfun]
  have h : HasDerivAt (fun u : ℝ => u + c) 1 s := by
    simpa using (hasDerivAt_id s).add_const c
  simpa using (hT (s + c)).scomp s h

/-! ### The marking normalization -/

/-- **There is a unique rotation matching two marked unit tangents.**  Given the
marked unit tangent `u` of one curve and the marked unit tangent `v` of another,
exactly one rotation `a` (`‖a‖ = 1`) satisfies `a * u = v`. -/
theorem existsUnique_rotation_of_marked_tangent {u v : ℂ} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    ∃! a : ℂ, ‖a‖ = 1 ∧ a * u = v := by
  have hu0 : u ≠ 0 := by
    intro h; rw [h] at hu; simp at hu
  refine ⟨v / u, ⟨?_, ?_⟩, ?_⟩
  · rw [norm_div, hu, hv, div_one]
  · field_simp
  · rintro a ⟨-, hau⟩
    rw [← hau, mul_div_assoc, div_self hu0, mul_one]

end RigidMotions
