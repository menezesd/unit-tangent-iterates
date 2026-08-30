import UnitTangentIterates.ConfiguredRecursiveEdgeRecostMultiplierClosingExistence
import UnitTangentIterates.ConfiguredRecursiveEdgeRecostMultiplierHistoryClosing
import UnitTangentIterates.ConfiguredRecursiveEdgeRecostFinitePreparedChosenChainUnconditionalMain

/-! # Unconditional paper main theorem -/

namespace PaperMainTheoremUnconditional

/-- The genuine noncircular paper conclusion, with all construction inputs
produced internally. -/
theorem mainConclusion :
    PaperMainTheoremGenuineNoncircularStatement.MainConclusion := by
  obtain ⟨P⟩ :=
    ConfiguredRecursiveEdgeRecostMultiplierClosingExistence.exists_concreteClosingPackage
  obtain ⟨H⟩ :=
    ConfiguredRecursiveEdgeRecostMultiplierHistoryClosing.nonempty P.closing
  exact
    ConfiguredRecursiveEdgeRecostFinitePreparedChosenChainUnconditionalMain.mainConclusion
      (K0 := 0) (K1 := 0) (K2 := 0) H

end PaperMainTheoremUnconditional
