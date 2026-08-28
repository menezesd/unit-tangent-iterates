import UnitTangentIterates.PathFromInfimum
import UnitTangentIterates.MarkedRigid

/-!
# From rigid path-distance bounds to actual paths

`ModelOrbitDefect.pathDistRigid_selInv_model_orbit` bounds `pathDistRigid`,
which infimizes over **two** things: the rigid motions, and the normal paths.
§63 handled the second; this file handles the first.

`exists_rigid_path_of_pathDistRigid_le` : a bound `pathDistRigid p q ≤ B`
produces, for every `ε > 0`, a rigid motion `z` together with a normal path from
`p` to the moved `q` of cost at most `B + ε`.

The rigid motion is not an artefact to be removed: it is the content of the
paper's `lem:compatible-markings`, which says the whole rear–front pair may be
rotated so the marked tangents agree, and that this changes neither `W` nor the
`S_j`.  The infimum over rigid motions in `pathDistRigid` is the formal version
of "rotate the later pair to match"; extracting a witness is extracting the
rotation the lemma promises.
-/

noncomputable section

set_option maxHeartbeats 4000000

open Set Real MarkedSpace PathMetric


namespace MarkedRigid

open PathMetric.NormalPath

/-- **From a rigid path-distance bound to an actual path.**  `pathDistRigid`
infimizes over rigid motions as well as over paths, so a bound on it produces a
rigid motion together with a path of nearly that cost. -/
theorem exists_rigid_path_of_pathDistRigid_le {p q : MarkedSpace.Data}
    {B eps : ℝ} (heps : 0 < eps)
    (hne : ∀ z : ℂ × {w : ℂ // ‖w‖ = 1},
      Nonempty (NormalPath p (rigidData z.1 z.2.1 q)))
    (h : pathDistRigid p q ≤ B) :
    ∃ (z : ℂ × {w : ℂ // ‖w‖ = 1})
      (Γ : NormalPath p (rigidData z.1 z.2.1 q)), cost Γ ≤ B + eps := by
  have hlt : (⨅ z : ℂ × {w : ℂ // ‖w‖ = 1},
      pathDist p (rigidData z.1 z.2.1 q)) < B + eps / 2 := by
    have := h
    rw [pathDistRigid] at this
    linarith
  obtain ⟨z, hz⟩ := exists_lt_of_ciInf_lt hlt
  obtain ⟨Γ, hΓ⟩ := exists_path_of_pathDist_le (by linarith : (0:ℝ) < eps / 2)
    (hne z) hz.le
  exact ⟨z, Γ, by linarith⟩

end MarkedRigid
