import UnitTangentIterates.ConfiguredRecursiveEdgeRecostedCompositionInvariant
import UnitTangentIterates.ConfiguredRecursiveEdgeRecostMultiplierScaledDiagonal

/-!
# Relabeling the geometric invariant by the multiplier recost allowance

The recursive source at depth `k + 1` belongs to diagonal `n + k`.  This
module records that indexing once and reuses the general phantom-error
transport of the geometric invariant.
-/

noncomputable section

open Function Set MarkedSpace PathMetric

namespace ConfiguredRecursiveEdgeRecostMultiplierCompositionInvariant

open ConfiguredRecursiveEdgeRecostMultiplierScaledDiagonal
  ConfiguredRecursiveEdgeRecostedCompositionInvariant
  FiniteSmoothRearFamilyMarkingAwareCompositionGeometricPresentedRecursion

def errorTable
    (D : ConstructedConfiguredSequenceWeighted.Data)
    (E0 C0 C1 C2 : ℝ) (n depth : ℕ) : ℝ :=
  multiplierRecostSourceAllowance D E0 C0 C1 C2 (n + (depth - 1))

@[simp] theorem errorTable_succ
    (D : ConstructedConfiguredSequenceWeighted.Data)
    (E0 C0 C1 C2 : ℝ) (n k : ℕ) :
    errorTable D E0 C0 C1 C2 n (k + 1) =
      multiplierRecostSourceAllowance D E0 C0 C1 C2 (n + k) := by
  simp [errorTable]

/-- The physical base source and the positive-depth multiplier sources have
different truthful mass estimates.  Depth one is therefore retained from the
configured base; from depth two onward the table is exactly the multiplier
allowance of the successor diagonal. -/
def hybridErrorTable
    (baseError : ℕ → ℝ)
    (D : ConstructedConfiguredSequenceWeighted.Data)
    (E0 C0 C1 C2 : ℝ) (n depth : ℕ) : ℝ :=
  if depth = 1 then baseError n else errorTable D E0 C0 C1 C2 n depth

@[simp] theorem hybridErrorTable_one
    (baseError : ℕ → ℝ)
    (D : ConstructedConfiguredSequenceWeighted.Data)
    (E0 C0 C1 C2 : ℝ) (n : ℕ) :
    hybridErrorTable baseError D E0 C0 C1 C2 n 1 = baseError n := by
  simp [hybridErrorTable]

@[simp] theorem hybridErrorTable_add_two
    (baseError : ℕ → ℝ)
    (D : ConstructedConfiguredSequenceWeighted.Data)
    (E0 C0 C1 C2 : ℝ) (n k : ℕ) :
    hybridErrorTable baseError D E0 C0 C1 C2 n (k + 2) =
      multiplierRecostSourceAllowance D E0 C0 C1 C2 (n + k + 1) := by
  simp [hybridErrorTable, errorTable, Nat.add_assoc]

variable {Q current : ℕ → Data} {e : ℕ → ℕ → ℝ} {k : ℕ}
  {P0 P1 khat G1 Cg C kh Qmax : ℕ → ℝ} {c dlt : ℝ}

/-- Preserve the complete reachable invariant while replacing its phantom
error table by the truthful multiplier source allowance. -/
def withMultiplierAllowance
    (D : ConstructedConfiguredSequenceWeighted.Data) (E0 C0 C1 C2 : ℝ)
    (S : GeometricCorrelatedColumn Q current e k P0 P1 khat G1 Cg C c dlt
      kh Qmax)
    (H : GeometricCompositionInvariant S)
    (hcost : ∀ n,
      (∫ t in (0 : ℝ)..(S.path n).T, (S.source n).m t) ≤
        multiplierRecostSourceAllowance D E0 C0 C1 C2 (n + k)) :
    GeometricCompositionInvariant
      (relabelColumn
        (e' := errorTable D E0 C0 C1 C2) S) :=
  relabelInvariant S H (by
    intro n
    simpa using hcost n)

/-- Install a physical depth-zero invariant without changing its proved mass
bound.  Later mapped invariants use `hybridErrorTable_add_two` and hence see
only the multiplier allowance. -/
def withHybridBase
    (baseError : ℕ → ℝ)
    (D : ConstructedConfiguredSequenceWeighted.Data) (E0 C0 C1 C2 : ℝ)
    (S : GeometricCorrelatedColumn Q current e 0 P0 P1 khat G1 Cg C c dlt
      kh Qmax)
    (H : GeometricCompositionInvariant S)
    (hcost : ∀ n,
      (∫ t in (0 : ℝ)..(S.path n).T, (S.source n).m t) ≤ baseError n) :
    GeometricCompositionInvariant
      (relabelColumn
        (e' := hybridErrorTable baseError D E0 C0 C1 C2) S) :=
  relabelInvariant S H (by
    intro n
    simpa using hcost n)

end ConfiguredRecursiveEdgeRecostMultiplierCompositionInvariant
