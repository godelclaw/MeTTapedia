import Mettapedia.Computability.PNP.CruxLocalRouteCoverageAtomicBudget
import Mettapedia.Computability.PNP.CruxLocalRouteCoverageDecoder
import Mettapedia.Computability.PNP.CruxLocalRouteCoverageEvidenceTrace
import Mettapedia.Computability.PNP.CruxLocalRouteCoverageFielded
import Mettapedia.Computability.PNP.CruxLocalRouteCoverageFiniteEnvelope

/-!
# PNP local route coverage

Compatibility import for the local PNP crux packet route-coverage anchors.
The actual route families live in semantic modules:
fielded v13 routes, finite-kernel/envelope routes, CNF decoder repair,
evidence/trace capture, and atomic evidence budgets.  Packet assembly,
covered/uncovered lists, and next-target bookkeeping live in `CruxLocalPacketStatus`.
-/
