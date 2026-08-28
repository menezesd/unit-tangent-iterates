import UnitTangentIterates.ConfiguredRecursiveEdgeRecostedRawMetricDiagonalRows

/-!
# Dependent recursion for truthful recosted diagonal rows

The older `Rows` record asks for a step on every hypothetical stage family.
That is stronger than the paper construction: the physical ancestry and the
next exact source exist only along the recursively reachable family.  This
module records precisely that reachable recursion and permits an arbitrary
dependent certificate to be carried from one depth to the next.
-/

noncomputable section

open Function Set MarkedSpace PathMetric

namespace ConfiguredRecursiveEdgeRecostedReachableRows

open ConfiguredRecursiveEdgeRecostedRawMetricDiagonalRows
  FiniteSmoothRearFamilyMarkingAwareActualPullbackSynchronizedRows

variable {D : ConstructedConfiguredSequenceWeighted.Data}
  {E0 C00 C10 C20 : ℕ → ℝ} {d0 : ℕ → ℕ → ℝ}

/-- A truthful all-depth row family.  Its step is stored only at its actual
reachable stage family. -/
structure Rows
    (D : ConstructedConfiguredSequenceWeighted.Data)
    (E0 C00 C10 C20 : ℕ → ℝ) (d0 : ℕ → ℕ → ℝ) where
  stages : ∀ k n, Stage
    (Profiles.P0 D) (Profiles.kh D) (Profiles.khat D) (Profiles.Qmax D) n k
  step : ∀ k, Step D (stages k) E0 C00 C10 C20 d0
  stages_succ : ∀ k n, stages (k + 1) n = (step k).next n
  base_range : ∀ n,
    range (stages 0 n).rear.1 = range (stages 0 (n + 1)).displayed.1

namespace Rows

def P (R : Rows D E0 C00 C10 C20 d0) (n k : ℕ) : Data :=
  (R.stages k n).displayed

def edgeBudget (R : Rows D E0 C00 C10 C20 d0) (n k : ℕ) : ℝ :=
  ((R.step k).rawMetric n).edgeBudget

def rawBound (R : Rows D E0 C00 C10 C20 d0) (n k : ℕ) : ℝ :=
  ((R.step k).rawMetric n).rawBound

def endpointCap (R : Rows D E0 C00 C10 C20 d0) (n k : ℕ) : ℝ :=
  ((R.step k).carrier n).geometric.endpointCap

def recostPath (R : Rows D E0 C00 C10 C20 d0) (n k : ℕ) :
    NormalPath (R.P n k) ((R.step k).carrier n).geometric.output.jets.rear :=
  ((R.step k).carrier n).path

def rangeEdge (R : Rows D E0 C00 C10 C20 d0) (n k : ℕ) :=
  ((R.step k).carrier n).geometric.output.stage.range_edge

theorem P_succ (R : Rows D E0 C00 C10 C20 d0) (n k : ℕ) :
    R.P n (k + 1) = ((R.step k).next n).displayed := by
  rw [P, R.stages_succ]

theorem stepDistance (R : Rows D E0 C00 C10 C20 d0) (n k : ℕ) :
    dist (R.P n k) (R.P n (k + 1)) ≤ R.edgeBudget n k := by
  rw [P_succ]
  exact (R.step k).displayedDistance n

theorem recostPath_terminal_range
    (R : Rows D E0 C00 C10 C20 d0) (n k : ℕ) :
    range ((R.recostPath n k).X (R.recostPath n k).T) =
      range ((R.step k).carrier n).geometric.output.jets.rear.1 :=
  ((R.step k).carrier n).terminal_range

theorem endpointCap_nonnegative
    (R : Rows D E0 C00 C10 C20 d0) (n k : ℕ) :
    0 ≤ R.endpointCap n k :=
  ((R.step k).carrier n).geometric.endpointCap_nonnegative

end Rows

/-- One reachable layer together with its dependent construction certificate. -/
structure Layer
    (Aux : ∀ k, (∀ n, Stage
      (Profiles.P0 D) (Profiles.kh D) (Profiles.khat D) (Profiles.Qmax D) n k) → Type)
    (k : ℕ) where
  stages : ∀ n, Stage
    (Profiles.P0 D) (Profiles.kh D) (Profiles.khat D) (Profiles.Qmax D) n k
  aux : Aux k stages

/-- A paper-faithful dependent successor.  In the concrete construction,
`Aux` carries source facts and the normalized nonaffine ancestry. -/
structure Builder
    (D : ConstructedConfiguredSequenceWeighted.Data)
    (E0 C00 C10 C20 : ℕ → ℝ) (d0 : ℕ → ℕ → ℝ)
    (Aux : ∀ k, (∀ n, Stage
      (Profiles.P0 D) (Profiles.kh D) (Profiles.khat D) (Profiles.Qmax D) n k) → Type) where
  base : Layer Aux 0
  base_range : ∀ n,
    range (base.stages n).rear.1 = range (base.stages (n + 1)).displayed.1
  nextStep : ∀ k (L : Layer Aux k),
    Step D L.stages E0 C00 C10 C20 d0
  nextAux : ∀ k (L : Layer Aux k),
    Aux (k + 1) (fun n => (nextStep k L).next n)

namespace Builder

def layers
    {Aux : ∀ k, (∀ n, Stage
      (Profiles.P0 D) (Profiles.kh D) (Profiles.khat D) (Profiles.Qmax D) n k) → Type}
    (B : Builder D E0 C00 C10 C20 d0 Aux) : ∀ k, Layer Aux k
  | 0 => B.base
  | k + 1 =>
      { stages := fun n => (B.nextStep k (B.layers k)).next n
        aux := B.nextAux k (B.layers k) }

def rows
    {Aux : ∀ k, (∀ n, Stage
      (Profiles.P0 D) (Profiles.kh D) (Profiles.khat D) (Profiles.Qmax D) n k) → Type}
    (B : Builder D E0 C00 C10 C20 d0 Aux) : Rows D E0 C00 C10 C20 d0 where
  stages k := (B.layers k).stages
  step k := B.nextStep k (B.layers k)
  stages_succ := by intros; rfl
  base_range := B.base_range

@[simp] theorem rows_stages_zero
    {Aux : ∀ k, (∀ n, Stage
      (Profiles.P0 D) (Profiles.kh D) (Profiles.khat D) (Profiles.Qmax D) n k) → Type}
    (B : Builder D E0 C00 C10 C20 d0 Aux) (n : ℕ) :
    (B.rows.stages 0 n) = B.base.stages n := rfl

@[simp] theorem rows_stages_succ
    {Aux : ∀ k, (∀ n, Stage
      (Profiles.P0 D) (Profiles.kh D) (Profiles.khat D) (Profiles.Qmax D) n k) → Type}
    (B : Builder D E0 C00 C10 C20 d0 Aux) (k n : ℕ) :
    B.rows.stages (k + 1) n = (B.nextStep k (B.layers k)).next n := rfl

end Builder

end ConfiguredRecursiveEdgeRecostedReachableRows
