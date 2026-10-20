import Mettapedia.OSLF.MeTTaIL.Complete.Deep
import Mettapedia.OSLF.MeTTaIL.Complete.Exhaustion
import Mettapedia.OSLF.MeTTaIL.Complete.Rounds
import Mettapedia.OSLF.MeTTaIL.Complete.DeepRoot
import Mettapedia.OSLF.MeTTaIL.Complete.Step
import Mettapedia.OSLF.MeTTaIL.Complete.Run
import Mettapedia.OSLF.MeTTaIL.Complete.EquationJob
import Mettapedia.OSLF.MeTTaIL.Complete.Inversion
import Mettapedia.OSLF.MeTTaIL.Complete.Predecessors
import Mettapedia.OSLF.MeTTaIL.Complete.Classes
import Mettapedia.OSLF.MeTTaIL.Complete.ClassesChecked
import Mettapedia.OSLF.MeTTaIL.Complete.Explore
import Mettapedia.OSLF.MeTTaIL.Complete.Settled
import Mettapedia.OSLF.MeTTaIL.Complete.Graph
import Mettapedia.OSLF.MeTTaIL.Complete.Presented
import Mettapedia.OSLF.MeTTaIL.Complete.Coherence
import Mettapedia.OSLF.MeTTaIL.Complete.CanonicalCoherence
import Mettapedia.OSLF.MeTTaIL.Complete.LawCoherence
import Mettapedia.OSLF.MeTTaIL.Complete.DescentCoherence
import Mettapedia.OSLF.MeTTaIL.Complete.RhoPresented
import Mettapedia.OSLF.MeTTaIL.Complete.QuoteDropCoherence
import Mettapedia.OSLF.MeTTaIL.Complete.RhoQuoteDrop
import Mettapedia.OSLF.MeTTaIL.Complete.RhoReference
import Mettapedia.OSLF.MeTTaIL.Complete.WrapperCoherence
import Mettapedia.OSLF.MeTTaIL.Complete.RhoWrappers
import Mettapedia.OSLF.MeTTaIL.Complete.RhoCompleteness
import Mettapedia.OSLF.MeTTaIL.Complete.ChainCoherence
import Mettapedia.OSLF.MeTTaIL.Complete.Termination
import Mettapedia.OSLF.MeTTaIL.Complete.Controls
import Mettapedia.OSLF.MeTTaIL.Complete.ClassesControls

/-!
# The complete GSLT machine

For an admitted GSLT plan, its steps modulo equations are searched by one resumable search that is
sound, complete in the limit, and exact once certified (`Complete.Classes`). Rule premises may
recurse through any rule; recursion is searched by iterative deepening over the scheduled
structural-descent machine, certified when no branch was cut (`Complete.Deep`,
`Complete.Exhaustion`). Equality classes are explored forwards by equation jobs and backwards by
matching equation sides against the term (`Complete.Predecessors`), never by enumerating terms.
Whole runs follow one path (`Classes.run_chain`, `Classes.done_no_step`) or every path fairly
(`Complete.Explore`), visiting each state once and stopping once settled (`Complete.Settled`);
the transitions found form the explored graph (`Complete.Graph`). Steps modulo equality in the
model, including the declared collection and scope-extrusion laws, are the presented GSLT
(`Complete.Presented`); normalized runs are chains of its steps. The explorer that commits the
sorted normal form of the declared collection laws is complete for the presented GSLT when
firings are coherent with the laws (`Complete.Coherence`), in particular for admissible plans
without and with declared collection laws (`Complete.CanonicalCoherence`, `Complete.LawCoherence`),
also with reduction inside collections of a flattening kind (`Complete.DescentCoherence`). The rho
calculus is explored completely modulo its declared parallel laws
(`Complete.RhoPresented.rho_explores`). A reflective presentation's name equation `@(*n) = n`
expands without bound, so the explorer commits its normal form before the sorted normal form; it
is then complete modulo the model with the name equation (`Complete.QuoteDropCoherence`), and so
is rho's (`Complete.RhoQuoteDrop.rho_explores_quoteDrop`). Every step of that model is a reduction
of the reference rho calculus (`Complete.RhoReference.step_reduces`). With the two wrapper laws of
the declared collection algebra, a singleton collection is its element and the empty one its unit;
the explorer that commits the model's canonical form is complete modulo the whole algebra and the
name equation (`Complete.WrapperCoherence`), and so is rho's
(`Complete.RhoWrappers.rho_explores_wrappers`), whose equality is then the reference structural
congruence on object terms (`Complete.RhoReference.sc_iff_modelCanon`). Every step of the established
rho calculus is a step of that model, so every process it reaches is explored up to structural
congruence (`Complete.RhoCompleteness.established_explored`). When a canonical form holds a redex
several times, as a sum of products does, a firing is matched by a chain of committed firings and the
explorer stays complete (`Complete.ChainCoherence.explores_of_chain`).
Runs commit targets in standard, canonical, reflective or model form (`Complete.Normalized.Commit`);
every published target passes the well-sortedness check (`Complete.ClassesChecked`).
-/
