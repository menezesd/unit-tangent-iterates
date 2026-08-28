import UnitTangentIterates.FiniteSmoothRearFamilyChosenTerminal

/-!
# Explicit physical fronts at nonaffinely marked rear-family endpoints

The endpoint of a marked normal path and the ordinary physical front used by
the selected-rear kinematics need not be the same `Data`: they can be distinct
markings of the same geometric curve.  This certificate keeps those roles
separate.  In particular, no definitional rewrite or `simpa` is used to turn a
gauge endpoint into the ordinary physical representative.
-/

noncomputable section

open Set MarkedSpace PathMetric

namespace FiniteSmoothRearFamilyPhysicalFront

/-- A marked endpoint aligned with an explicit ordinary physical front.
`range_eq` records the marking-independent geometric identification, while
`kinematics` is stated only for the ordinary representative. -/
structure Certificate (kh : ℝ) (terminalBase markedEndpoint : Data) where
  physicalFront : Data
  range_eq : range (ev markedEndpoint) = range (ev physicalFront)
  kinematics : PhysicalRearLimitKinematics kh terminalBase physicalFront

/-- The affine/identical-marking case embeds into the marking-aware boundary.
This is a compatibility constructor, not a transport theorem. -/
def Certificate.ofSame
    {kh : ℝ} {terminalBase front : Data}
    (K : PhysicalRearLimitKinematics kh terminalBase front) :
    Certificate kh terminalBase front :=
  { physicalFront := front
    range_eq := rfl
    kinematics := K }

/-- The legacy chosen-terminal input is the special case in which its endpoint
already is the ordinary physical front. -/
def ofTerminalInput
    {a b p base : Data} {Gamma : PathMetric.NormalPath a b}
    {P0 kh khat Qmax P1 bound : ℝ}
    {A : FiniteSmoothRearFamilyAnalyticSource.Source Gamma P0 kh khat Qmax}
    {E : FiniteSmoothRearFamilyAppliedSource.Applied Gamma A P1}
    (B : FiniteSmoothRearFamilyChosenTerminal.TerminalInput
      (p := p) (base := base) (bound := bound) E) :
    Certificate kh base b :=
  Certificate.ofSame B.physicalKinematics

/-- A theorem-shaped sibling input for future terminal assembly.  The marked
endpoint is intentionally explicit and may differ from `physicalFront`. -/
structure TerminalPhysicalFront
    {a b : Data} (Gamma : PathMetric.NormalPath a b)
    (kh : ℝ) (terminalBase : Data) where
  markedEndpoint : Data
  endpoint_eq : markedEndpoint = b
  aligned : Certificate kh terminalBase markedEndpoint

end FiniteSmoothRearFamilyPhysicalFront
