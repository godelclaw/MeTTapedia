import Mettapedia.Computability.PNP.CruxKpolySubrepairClassCore
import Mettapedia.Computability.PNP.CruxKpolySubrepairClassActualLocal
import Mettapedia.Computability.PNP.CruxKpolySubrepairClassBitFallback
import Mettapedia.Computability.PNP.CruxKpolySubrepairClassRecovery
import Mettapedia.Computability.PNP.CruxKpolySubrepairClassFiniteImage
import Mettapedia.Computability.PNP.CruxKpolySubrepairClassObservedSupport
/-!
# PNP `Kpoly` subrepair class sum type

The flat historical taxonomy is represented as a sum of semantic subrepair
class families.  The legacy constructor-like names are provided by
`CruxKpolySubrepairClass`.
-/

namespace Mettapedia.Computability.PNP

/-- Narrow `Kpoly` subrepair classes already covered by the current exact-visible
stack, grouped by their semantic role.  These are useful local closures, not a
proof of the broad manuscript-specific `Kpoly` compression bridge. -/
inductive PNPKpolySubrepairClass where
  /-- Core exact-visible, raw `(a,b)`, shared `(a,b)`, and first actual-local sparse-threshold subrepair classes. -/
  | core (kind : PNPKpolyCoreSubrepairClass)
  /-- Actual-local support, observed-support, plug-in, bounded-sample, and structured fallback subrepair classes before the bit-coded fallback layer. -/
  | actualLocal (kind : PNPKpolyActualLocalSubrepairClass)
  /-- Bit-coded bounded-sample fallback boundary and obstruction subrepair classes. -/
  | bitFallback (kind : PNPKpolyBitFallbackSubrepairClass)
  /-- Actual-local recovery-threshold, payload, pairwise-agreement, and region-mass subrepair classes. -/
  | recovery (kind : PNPKpolyRecoverySubrepairClass)
  /-- Finite predictor-image, representative-index, quotient-code, factor-transport, pullback, product-bound, and fielded-switching bridge subrepair classes. -/
  | finiteImage (kind : PNPKpolyFiniteImageSubrepairClass)
  /-- Observed-output support, decoder, query, adaptive-query, and one-block subrepair classes. -/
  | observedSupport (kind : PNPKpolyObservedSupportSubrepairClass)
  deriving DecidableEq, Repr

end Mettapedia.Computability.PNP
