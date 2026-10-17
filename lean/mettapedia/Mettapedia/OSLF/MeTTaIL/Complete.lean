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
import Mettapedia.OSLF.MeTTaIL.Complete.Explore
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
(`Complete.Explore`).
-/
