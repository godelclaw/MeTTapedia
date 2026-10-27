import Mettapedia.OSLF.NativeTypes.Instances.Normalized.Meaning
import Mettapedia.OSLF.NativeTypes.Instances.Normalized.ClassChecking
import Mettapedia.OSLF.NativeTypes.Instances.Normalized.Controls
import Mettapedia.OSLF.NativeTypes.Instances.Normalized.AuthoredControls
import Mettapedia.OSLF.NativeTypes.Instances.Normalized.RhoControls
import Mettapedia.OSLF.NativeTypes.Instances.Normalized.RhoFamilyControls

/-!
# Certified normalized native execution

The generic adapter derives native answers over the exact selected equality
from a certified normal form, local firing coherence and finite primitive
coverage. Semantic controls and an authored conditional-equation instance
exercise admission, preserved receipt packets and interrupted evaluation.
The rho COMM instance includes the quote-drop model equation. Its family
controls distinguish that name equation from an authored process-Drop event.

TODO (integration with the front door): this driver has no front-door reading yet. Its operational relation is the
generated plan's primitive receipts (`GeneralOccurrenceSemantics`), not the reference relation the front door reads
(`OSLF/MeTTaIL/ReferenceStep*`). A `DriverBridge.Faithful` reading needs the two to agree on the driver's admitted
terms, which is the occurrence-semantics lane's work; with that agreement this driver reads at the front door as the
local, λ, Partrec and ρ drivers do. The same agreement reads its dynamic relations, which the front door answers through
the services' relation environment (`GeneratedLogic/ServedRelations`): the plan resolves a dynamic request with its
output schemas uninstantiated, the reference relation instantiates what is bound.
-/
