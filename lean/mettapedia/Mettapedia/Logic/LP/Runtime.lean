import Mettapedia.Logic.LP.RuntimeTerm
import Mettapedia.Logic.LP.StandardizeApart
import Mettapedia.Logic.LP.RuntimeMaterialize
import Mettapedia.Logic.LP.RuntimeUnification
import Mettapedia.Logic.LP.RuntimeReadback
import Mettapedia.Logic.LP.RuntimeRestoration
import Mettapedia.Logic.LP.RuntimeUnifierSoundness
import Mettapedia.Logic.LP.RuntimeMaterializeSoundness
import Mettapedia.Logic.LP.RuntimeUnificationSoundness
import Mettapedia.Logic.LP.RuntimeQueryConservation
import Mettapedia.Logic.LP.RuntimeBranchInvariant

/-!
# Executable logic-programming runtime

Terms are materialized into a shared graph with explicit allocation, variable
identity, and a binding trail. Ordered query execution retains activation
scopes, choice checkpoints, cut boundaries, exceptions, and persistent state.
The unifier's finite-readback theorem covers compound terms. Query answers are
connected to scoped SLD and the least Herbrand model in the function-free
fragment. Rational-tree successes retain a separate finite-readback boundary.
-/
