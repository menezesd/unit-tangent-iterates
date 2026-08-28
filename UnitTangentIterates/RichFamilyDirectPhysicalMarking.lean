import UnitTangentIterates.RichFamilyPhysicalMarkingIntegration
import UnitTangentIterates.TriangularMarkedRecursiveChoiceVariableTerminalConstructor
import UnitTangentIterates.ConfiguredPhysicalRowBounds

/-!
# Direct physical markings extracted from rich recursive stages

Each rich stage already carries the normalized marking from its canonical
physical terminal base to the actual gauge-marked rear.  No cumulative
composition is needed; only the alignment of that retained base with the
configured finite pullback must be supplied.
-/

noncomputable section

open MarkedSpace
open Filter Topology PathMetric

namespace RichFamilyDirectPhysicalMarking

open NormalizedTerminalMarkingComposition
open RichFamilyPhysicalMarkingIntegration
open TriangularMarkedRecursiveChoiceVariableTerminalConstructor

/-- Extract the direct normalized marking at every row and depth.  Depth zero
is the common configured base.  At successor depth, `richStage n k` supplies
the marking directly once its retained `terminalBase` is identified with the
canonical physical pullback at depth `k+1`. -/
def directFamily_of_richFamily
    {Q : ℕ → Data} {e : ℕ → ℕ → ℝ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
    (F : RichFamily Q e P0 P1 khat G1 Cg C c dlt)
    (B : ℕ → ℕ → Data)
    (hzero : ∀ n, B n 0 = F.P n 0)
    (halign : ∀ n k, (F.richStage n k).terminalBase = B n (k + 1)) :
    DirectPhysicalTerminalMarkingFamily B F.P where
  lambda n
    | 0 => 1
    | k + 1 => (F.richStage n k).lambda
  Lambda n
    | 0 => 1
    | k + 1 => (F.richStage n k).Lambda
  marking n
    | 0 => by
        simpa only [hzero n] using NormalizedC2Marking.refl (B n 0)
    | k + 1 => by
        simpa only [halign n k] using (F.richStage n k).marking

/-- Configured physical bounds, rich-stage alignment, and the two row limits
directly produce oriented representatives of every terminal limit. -/
def orientedRepresentatives_of_configuredPackage
    {kappas : ℕ → ℝ → ℝ} {Hs eps : ℕ → ℝ}
    {model : UnconditionalAssembly.ConfiguredModelSequence kappas Hs eps}
    {kh C0 K : ℝ} {d : ℕ → ℝ} {Q : ℕ → Data}
    {e : ℕ → ℕ → ℝ} {P0 P1 khat G1 Cg Ct : ℕ → ℝ}
    {c dlt ct dt : ℝ}
    (F : RichFamily Q e P0 P1 khat G1 Cg Ct ct dt)
    {rend : ℕ → ℝ}
    (Z : ConfiguredPhysicalRowBounds.Package model kh C0 K d Q F.P rend c dlt)
    (hzero : ∀ n, TubePullbackLimit.pullback
      (SelectedInverseMap.selInv kh) Q n 0 = F.P n 0)
    (halign : ∀ n k, (F.richStage n k).terminalBase =
      TubePullbackLimit.pullback (SelectedInverseMap.selInv kh) Q n (k + 1))
    (hct : 0 < ct) (hkh0 : 0 ≤ kh) (hkh1 : kh < 1) (hdlt : 0 < dlt)
    (hterminalTube : ∀ n k,
      VariableMarkedTube.IsVariableTubeMember ct (Ct n) 0 dt (F.P n k))
    {X Y : ℕ → Data}
    (hX : ∀ n, Tendsto
      (fun k => TubePullbackLimit.pullback
        (SelectedInverseMap.selInv kh) Q n k) atTop (nhds (X n)))
    (hY : ∀ n, Tendsto (F.P n) atTop (nhds (Y n))) :
    ∀ n, VariableMarkedTube.OrientedArclengthRepresentative (Y n) :=
  ConfiguredPhysicalRowBounds.orientedRepresentatives_of_package Z
    (directFamily_of_richFamily F
      (fun n k => TubePullbackLimit.pullback
        (SelectedInverseMap.selInv kh) Q n k) hzero halign)
    hct hkh0 hkh1 hdlt hterminalTube hX hY

end RichFamilyDirectPhysicalMarking
