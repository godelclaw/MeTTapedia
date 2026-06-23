import Mettapedia.Computability.PNP.CruxLocalPacketStatus

/-!
# PNP local crux packet compatibility surface

The local PNP route-coverage propositions now live in
`CruxLocalRouteCoverage`; packet/list/status bookkeeping lives in
`CruxLocalPacketStatus`.  This module preserves the historical
`CruxLocalPacket` import path while downstream modules are narrowed.
-/
