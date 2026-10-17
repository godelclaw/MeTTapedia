import Mettapedia.Languages.MeTTa.EquationKernel.Judgment
import Mettapedia.Languages.MeTTa.EquationKernel.Certificate
import Mettapedia.Languages.MeTTa.EquationKernel.Execution
import Mettapedia.Languages.MeTTa.EquationKernel.Hygiene
import Mettapedia.Languages.MeTTa.EquationKernel.Matching
import Mettapedia.Languages.MeTTa.EquationKernel.SpaceCheck
import Mettapedia.Languages.MeTTa.EquationKernel.Sealed
import Mettapedia.Languages.MeTTa.EquationKernel.Wire
import Mettapedia.Languages.MeTTa.EquationKernel.Controls

/-!
# The equation-application kernel

The dialect-neutral judgment of MeTTa equations: `Reaches space a b` holds
when finitely many applications of equations `(= l r)` stored in the space
lead from `a` to `b`. Two kernels decide its evidence: a certificate checker
(`Certificate`) and sealed theorems minted only by the kernel rules
(`Sealed`), with recording and minting between them. `Hygiene` states
alpha-invariance and fresh instances, and that a supplied unifier licenses
rewriting the instantiated subject. `SpaceCheck` models the checker that
reads certificates from a space and shares a claim table. `Matching` computes
left-side bindings, so a step needs only its citation, position and
right-only bindings. `Wire` renders the
data read by the MeTTa checker, and `Controls` holds the worked examples.
-/
