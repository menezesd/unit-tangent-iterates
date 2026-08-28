import UnitTangentIterates.RigidMotions

/-! # Paper-facing compatible marking normalization -/

namespace RigidMotions

/-- **Compatible markings.**  A rear-front pair has a unique common rotation
matching its chosen rear tangent to a prescribed marked unit tangent.  That
rotation preserves the pair relation, speed, and intrinsic curvature. -/
theorem existsUnique_compatible_marking
    {R F TR : ℝ → ℂ} {k : ℝ → ℝ} {s0 : ℝ} {v : ℂ}
    (hR : ∀ s, HasDerivAt R (TR s) s)
    (hTR : ∀ s, HasDerivAt TR (Complex.I * (k s : ℂ) * TR s) s)
    (hpair : UnitTangent.unitTangentMap R = F)
    (hu : ‖TR s0‖ = 1) (hv : ‖v‖ = 1) :
    ∃! a : ℂ,
      ‖a‖ = 1 ∧ a * TR s0 = v ∧
      UnitTangent.unitTangentMap (move a 0 R) = move a 0 F ∧
      (∀ s, ‖deriv (move a 0 R) s‖ = ‖deriv R s‖) ∧
      ∀ s, HasDerivAt (deriv (move a 0 R))
        (Complex.I * (k s : ℂ) * deriv (move a 0 R) s) s := by
  obtain ⟨a, ha, hauniq⟩ := existsUnique_rotation_of_marked_tangent hu hv
  refine ⟨a, ⟨ha.1, ha.2, rigidMotion_pair hR hpair a 0,
    fun s => norm_deriv_rigidMotion hR ha.1 0 s,
    fun s => curvature_rigidMotion hR hTR a 0 s⟩, ?_⟩
  intro z hz
  exact hauniq z ⟨hz.1, hz.2.1⟩

/-- A constant change of marked arclength phase preserves speed and merely
translates the intrinsic curvature function. -/
theorem compatible_phase_shift
    {R TR : ℝ → ℂ} {k : ℝ → ℝ}
    (hR : ∀ s, HasDerivAt R (TR s) s)
    (hTR : ∀ s, HasDerivAt TR (Complex.I * (k s : ℂ) * TR s) s)
    (q s : ℝ) :
    ‖deriv (shift q R) s‖ = ‖deriv R (s + q)‖ ∧
      HasDerivAt (deriv (shift q R))
        (Complex.I * (k (s + q) : ℂ) * deriv (shift q R) s) s :=
  ⟨norm_deriv_shift hR q s, curvature_shift hR hTR q s⟩

end RigidMotions
