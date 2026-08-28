import UnitTangentIterates.PhysicalArclengthJacobiTransition

/-!
# Canonical scalar domination by explicit maxima

The physical transition has one purely scalar boundary.  This module packages
the least convenient explicit rowwise ceilings; a configured construction
only has to dominate these three functions uniformly.
-/

noncomputable section

namespace PhysicalArclengthCanonicalDomination

open PhysicalArclengthJacobiTransition

def a (PF PR CW : ℝ) : ℝ := max 0 (PR * CW / PF)

def K0 (PF c0 : ℝ) : ℝ := max 0 (c0 / PF)

def K1 (PF PR c1 : ℝ) : ℝ :=
  max 0 (max ((c1 / PR) / PF) (c1 / PR))

def K2 (PF PR c2 : ℝ) : ℝ :=
  let x := c2 / PR ^ 2
  max 0 (max (x / PF) (max x (x * PF)))

theorem domination
    {PF PR CW c0 c1 c2 : ℝ} (hPF : 0 < PF) (hPR : 0 < PR) :
    Domination PF PR (a PF PR CW) CW c0 c1 c2
      (K0 PF c0) (K1 PF PR c1) (K2 PF PR c2) := by
  let x1 := c1 / PR
  let x2 := c2 / PR ^ 2
  refine
    { PF_pos := hPF
      PR_pos := hPR
      a_nonnegative := le_max_left _ _
      C0_nonnegative := le_max_left _ _
      C1_nonnegative := le_max_left _ _
      C2_nonnegative := le_max_left _ _
      w := ?_
      s0 := ?_
      s1w := ?_
      s1s := ?_
      s2w := ?_
      s2s := ?_
      s2d := ?_ }
  · apply (div_le_iff₀ hPF).mp
    exact le_max_right _ _
  · apply (div_le_iff₀ hPF).mp
    exact le_max_right _ _
  · change x1 ≤ K1 PF PR c1 * PF
    apply (div_le_iff₀ hPF).mp
    exact (le_max_left (x1 / PF) x1).trans (le_max_right 0 _)
  · change x1 ≤ K1 PF PR c1
    exact (le_max_right (x1 / PF) x1).trans (le_max_right 0 _)
  · change x2 ≤ K2 PF PR c2 * PF
    apply (div_le_iff₀ hPF).mp
    exact (le_max_left (x2 / PF) (max x2 (x2 * PF))).trans
      (le_max_right 0 _)
  · change x2 ≤ K2 PF PR c2
    exact ((le_max_left x2 (x2 * PF)).trans
      (le_max_right (x2 / PF) _)).trans (le_max_right 0 _)
  · change x2 * PF ≤ K2 PF PR c2
    exact ((le_max_right x2 (x2 * PF)).trans
      (le_max_right (x2 / PF) _)).trans (le_max_right 0 _)

end PhysicalArclengthCanonicalDomination
