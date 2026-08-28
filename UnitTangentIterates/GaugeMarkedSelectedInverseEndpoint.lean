import Mathlib
import UnitTangentIterates.InterpolationSelectedRearEndpoints
import UnitTangentIterates.GaugeFlowMarkedData
import UnitTangentIterates.PathMetric

/-!
# The geometric selected-inverse endpoint in a gauge marking

The gauge flow generally produces a nonaffine marking.  It therefore does not
produce literal equality in `MarkedSpace.Data`, whose normalized parameter is
part of the datum.  What it does preserve is the underlying curve and, when
the flow fixes zero, its marked basepoint.  This file records that exact
endpoint statement.
-/

noncomputable section

open Function Set MarkedSpace

namespace GaugeMarkedSelectedInverseEndpoint

/-- A continuous quasi-periodic increasing marking of positive period is onto.
This is the endpoint surjectivity supplied by the gauge-flow spatial
monotonicity and period-transport identities. -/
theorem surjective_of_continuous_strictMono_quasiPeriodic
    {Phi : ℝ → ℝ} {Q : ℝ} (hQ : 0 < Q) (hcont : Continuous Phi)
    (hmono : StrictMono Phi) (htrans : ∀ u, Phi (u + 1) = Phi u + Q)
    (hzero : Phi 0 = 0) : Surjective Phi := by
  have hnat : ∀ n : ℕ, Phi (n : ℝ) = (n : ℝ) * Q := by
    intro n
    induction n with
    | zero => simpa using hzero
    | succ n ih =>
        rw [Nat.cast_succ, htrans, ih]
        ring
  have hneg : ∀ n : ℕ, Phi (-(n : ℝ)) = -(n : ℝ) * Q := by
    intro n
    induction n with
    | zero => simpa using hzero
    | succ n ih =>
        have ht := htrans (-((n + 1 : ℕ) : ℝ))
        have heq : -((n + 1 : ℕ) : ℝ) + 1 = -(n : ℝ) := by
          push_cast
          ring
        rw [heq, ih] at ht
        push_cast at ht ⊢
        linarith
  intro x
  obtain ⟨n, hn⟩ := exists_nat_ge (|x| / Q)
  have hnQ : |x| ≤ (n : ℝ) * Q := by
    rw [div_le_iff₀ hQ] at hn
    exact hn
  have hxmem : x ∈ Icc (Phi (-(n : ℝ))) (Phi (n : ℝ)) := by
    rw [hneg, hnat]
    exact ⟨by linarith [neg_abs_le x], by linarith [le_abs_self x]⟩
  have hle : (-(n : ℝ)) ≤ (n : ℝ) := by
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have hiv := intermediate_value_Icc (a := -(n : ℝ)) (b := (n : ℝ)) hle hcont.continuousOn
  obtain ⟨u, -, hu⟩ := hiv hxmem
  exact ⟨u, hu⟩

/-- Surjectivity of the normalized terminal marking follows immediately from
surjectivity of the marking and positivity of its transported period. -/
theorem surjective_normalized_of_quasiPeriodic
    {Phi : ℝ → ℝ} {Q : ℝ} (hQ : 0 < Q) (hcont : Continuous Phi)
    (hmono : StrictMono Phi) (htrans : ∀ u, Phi (u + 1) = Phi u + Q)
    (hzero : Phi 0 = 0) : Surjective (fun u => Phi u / Q) := by
  have hsurj := surjective_of_continuous_strictMono_quasiPeriodic hQ hcont hmono htrans hzero
  intro v
  obtain ⟨u, hu⟩ := hsurj (Q * v)
  refine ⟨u, ?_⟩
  show Phi u / Q = v
  rw [hu]
  field_simp [hQ.ne']

/-- A surjective reparametrization preserves the image of a marked curve, and
a reparametrization fixing zero preserves its marked basepoint. -/
theorem same_range_and_basepoint_of_gauge_marking
    {b q' : Data} {psi : ℝ → ℝ}
    (hq : ∀ u, q'.1 u = b.1 (psi u))
    (hpsi : Surjective psi) (hpsi0 : psi 0 = 0) :
    range q'.1 = range b.1 ∧ q'.1 0 = b.1 0 := by
  constructor
  · apply Set.Subset.antisymm
    · rintro z ⟨u, rfl⟩
      exact ⟨psi u, (hq u).symm⟩
    · rintro z ⟨v, rfl⟩
      obtain ⟨u, hu⟩ := hpsi v
      exact ⟨u, by rw [hq u, hu]⟩
  · rw [hq, hpsi0]

/-- **A gauge-marked endpoint represents the same geometric selected inverse.**

Here `b = selInv kap p` is the canonical affinely marked selected inverse,
while `q'` is the datum produced using the terminal gauge marking.  Surjectivity
of the normalized gauge marking gives equality of curve images; fixing zero
gives equality of marked basepoints.  No affine-marking assertion is made. -/
theorem gauge_marked_endpoint_same_selectedInverse_geometry
    {p q' : Data} {kap Q : ℝ} {Phi : ℝ → ℝ}
    (hQ : 0 < Q)
    (hq : ∀ u, q'.1 u = (SelectedInverseMap.selInv kap p).1 (Phi u / Q))
    (hsurj : Surjective (fun u => Phi u / Q))
    (hbase : Phi 0 = 0) :
    range q'.1 = range (SelectedInverseMap.selInv kap p).1 ∧
      q'.1 0 = (SelectedInverseMap.selInv kap p).1 0 := by
  apply same_range_and_basepoint_of_gauge_marking hq hsurj
  rw [hbase, zero_div]

/-- Literal equality of the position components requires invariance under the
whole terminal marking.  This condition is automatic for the affine marking,
but it is not a consequence of monotonicity, quasi-periodicity, and basepoint
fixing for a general gauge flow. -/
theorem gauge_marked_position_eq_iff
    {b q' : Data} {psi : ℝ → ℝ} (hq : ∀ u, q'.1 u = b.1 (psi u)) :
    q'.1 = b.1 ↔ ∀ u, b.1 (psi u) = b.1 u := by
  constructor
  · intro heq u
    rw [← hq u, heq]
  · intro h
    ext u
    rw [hq u, h u]

/-- **Zero marked path distance forces equality of the parameterized
positions.**  Thus equality of image and marked basepoint cannot by itself
give zero `pathDist` for a genuinely nonaffine gauge marking. -/
theorem position_eq_of_pathDist_eq_zero
    {p q : Data} (hpath : Nonempty (PathMetric.NormalPath p q))
    (hdist : PathMetric.pathDist p q = 0) : q.1 = p.1 := by
  ext u
  have h := PathMetric.norm_sub_le_pathDist hpath u
  rw [hdist] at h
  have hz : q.1 u - p.1 u = 0 :=
    norm_eq_zero.mp (le_antisymm h (norm_nonneg (q.1 u - p.1 u)))
  exact sub_eq_zero.mp hz

end GaugeMarkedSelectedInverseEndpoint
