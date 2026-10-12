import Mettapedia.Languages.HOLLight.SourceProfile
import Mettapedia.Languages.HOLLight.Rules
import Mettapedia.Languages.HOLLight.DefinitionAdapters
import Mettapedia.Languages.HOLLight.ExportReplay
import Mettapedia.Languages.HOLLight.IncrementalExecution
import Mettapedia.Languages.HOLLight.ModelInterpretation
import Mettapedia.Languages.HOLLight.StandardTheoryInterpretation
import Mettapedia.Languages.HOLLight.ProofSystem
import Mettapedia.Languages.HOLLight.FirstOrder.GraphSimulation
import Mettapedia.Languages.HOLLight.FirstOrder.Validation
import Mettapedia.Languages.HOLLight.InferenceCompiler

/-!
# HOL Light: kernel, theories, replay and inference-presentation hosting

The pinned source kernel retains its ten inference operations and actual
substitution and beta-admission conventions. Axiom policies describe separate
object theories; the kernel's existing graph checker retains chronological
sharing and rejects forward references.

`FirstOrder.Validation` admits the kernel's first-order rendering for arbitrary
finite axiom lists. `PrimitiveTransport` connects the primitive checker to the
shared equational kernel without adding eta. `InferenceCompiler` generates a
finite schematic HOL theory from an admitted constructor-and-metavariable rule
presentation and replays its derivations through the actual kernel.

`Logic.HOL.Embedding.InferenceRules` and `InferenceRuleInstances` supply the
independent finite-theory preservation and reflection laws. The source's
canonical argument values may contain binders; this is distinct from allowing
binders in the source rule schemas.

`FirstOrder.GraphSimulation` gives the reverse translation to MM0 with retained
saved proofs and polynomial certificate-size bounds. Its declared translation
clock is distinct from the execution-backed realizations formalized in
`GSLT.LanguageDef.ProofSystemExecution`.
-/
