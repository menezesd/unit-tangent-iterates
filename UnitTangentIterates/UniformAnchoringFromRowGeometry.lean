import UnitTangentIterates.NormalizedMarkingControlledJunction
import UnitTangentIterates.RowwiseNormalizedMarkingGeometryBounds

/-!
# Uniform anchoring bounds from row geometry

The fixed junction bounds are consequences of the rowwise speed, perimeter,
and acceleration estimates.  This isolates the remaining large-separation
work to three scalar inequalities.
-/

noncomputable section

open Function MarkedSpace

namespace UniformAnchoringFromRowGeometry

open VariableMarkedTube
  NormalizedTerminalMarkingComposition
  NormalizedMarkingControlledJunction
  RowwiseNormalizedMarkingGeometryBounds

theorem uniformAnchoringBounds_of_row_geometry
    {base rear : Data}
    {lambda Lambda cb db c C dlt Lmin Lmax Ab Ap : ℝ}
    (M : NormalizedC2Marking base rear lambda Lambda)
    (hLmin : 0 < Lmin) (hc : 0 < c) (hAb : 0 ≤ Ab)
    (hbase : IsTubeMember cb 0 db base)
    (hperimLower : Lmin ≤ perim base)
    (hperimUpper : perim base ≤ Lmax)
    (hrear : IsVariableTubeMember c C 0 dlt rear)
    (hbaseAcc : ∀ u, ‖base.2.2 u‖ ≤ Ab)
    (hrearAcc : ∀ u, ‖rear.2.2 u‖ ≤ Ap)
    (hlower : (1 / 2 : ℝ) ≤ c / Lmax)
    (hupper : C / Lmin ≤ 2)
    (hsecond : (Ap + (C / Lmin) ^ 2 * Ab) / Lmin ≤ 1) :
    UniformAnchoringBounds M where
  lower := fun u => hlower.trans
    (NormalizedC2Marking.dpsi_lower_of_perim_bounds M hLmin hc hbase
      hperimLower hperimUpper hrear u)
  upper := fun u =>
    (NormalizedC2Marking.dpsi_upper_of_perim_bounds M hLmin hc hbase
      hperimLower hperimUpper hrear u).trans hupper
  second := fun u =>
    (NormalizedC2Marking.abs_ddpsi_le_of_row_bounds M hLmin hc hAb hbase
      hperimLower hperimUpper hbaseAcc hrear hrearAcc u).trans hsecond

end UniformAnchoringFromRowGeometry

