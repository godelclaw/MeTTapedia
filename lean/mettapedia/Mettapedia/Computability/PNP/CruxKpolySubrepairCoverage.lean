import Mettapedia.Computability.PNP.CruxKpolySubrepairCoverageCore
import Mettapedia.Computability.PNP.CruxKpolySubrepairCoverageActualLocal
import Mettapedia.Computability.PNP.CruxKpolySubrepairCoverageBitFallback
import Mettapedia.Computability.PNP.CruxKpolySubrepairCoverageRecovery
import Mettapedia.Computability.PNP.CruxKpolySubrepairCoverageFiniteImage
import Mettapedia.Computability.PNP.CruxKpolySubrepairCoverageObservedSupport

/-!
# PNP `Kpoly` subrepair coverage ledger

Covered-subrepair list and exactness theorem for the `Kpoly` subrepair class
taxonomy.  The coverage list is assembled from semantic chunks so later audits
can discuss exact-visible, actual-local, bit-fallback, recovery, finite-image,
and observed-support coverage separately without changing this public import.
-/

namespace Mettapedia.Computability.PNP

/-- The exact narrow `Kpoly` subrepairs covered by the current stack. -/
def currentPNPKpolyCoveredSubrepairs : List PNPKpolySubrepairClass :=
  currentPNPKpolyCoreCoveredSubrepairs ++
    currentPNPKpolyActualLocalCoveredSubrepairs ++
    currentPNPKpolyBitFallbackCoveredSubrepairs ++
    currentPNPKpolyRecoveryCoveredSubrepairs ++
    currentPNPKpolyFiniteImageCoveredSubrepairs ++
    currentPNPKpolyObservedSupportCoveredSubrepairs

/-- The narrow `Kpoly` subrepair coverage list is exact. -/
theorem currentPNPKpolyCoveredSubrepairs_exact
    (repair : PNPKpolySubrepairClass) :
    repair ∈ currentPNPKpolyCoveredSubrepairs := by
  cases repair with
  | core kind =>
      cases kind <;> decide
  | actualLocal kind =>
      cases kind <;> decide
  | bitFallback kind =>
      cases kind <;> decide
  | recovery kind =>
      cases kind <;> decide
  | finiteImage kind =>
      cases kind <;> decide
  | observedSupport kind =>
      cases kind <;> decide

end Mettapedia.Computability.PNP
