import Mettapedia.Logic.Arithmetic.PresburgerBubble
import Mettapedia.Logic.Arithmetic.PresburgerHenkin
import Mettapedia.Logic.Arithmetic.BuchiAutomaton
import Mettapedia.Logic.Arithmetic.ExS1S
import Mettapedia.Logic.Arithmetic.BuchiRecurrence
import Mettapedia.Logic.Arithmetic.FourierMotzkin
import Mettapedia.Logic.Arithmetic.RabinTree
import Mettapedia.Logic.Arithmetic.ReachCertificate

/-!
# Arithmetic

Standard-semantics bubbles for arithmetic.

`PresburgerBubble` decides every closed sentence of `(ℕ, 0, 1, +, <)` by
Cooper quantifier elimination. `PresburgerHenkin` embeds that language into
higher-order logic and shows that, on every such sentence, truth in every
admissible premodel on `ULift ℕ` agrees with truth in the standard model.

`BuchiAutomaton` is nondeterministic Büchi automata on ω-words, with union,
intersection, projection, emptiness decided by a lasso, and complementation.
`accepts_complement` says the rank-and-breakpoint automaton accepts a word
exactly when the source rejects it. `ExS1S` decides every closed monadic
second-order sentence over `(ℕ, succ)`: `decideMSO_iff` agrees with the
standard model, and `compileMSO_iff` agrees with automaton acceptance.
`execCompile_iff` is that acceptance statement for the Boolean compiler, whose
states are codes and whose negation is `finComplement`. `execDecide_iff` says
the Boolean emptiness search returns true exactly when the closed sentence holds.
`lassoChecker_of_check` says a retained run of `Lasso.check` finishes with that
check. `execCompile_sat_iff_checkedLasso` says a closed sentence holds exactly
when some such run accepts the Boolean compiler's automaton.
`control_exec_succ_lasso_check` kernel-checks an explicit lasso on `execCompile`
of `∃x. ∃y. succ(x, y)`.
`BuchiRecurrence` identifies that acceptance condition with the recurrence
already used for memoryless controllers. `rootCheck_retained_lasso` turns an
accepted finite root certificate into a retained lasso run on that controller's
automaton. The older `exS1SBubble` decides
existential sentences in a four-atom fragment. `toMSO_iff` says a formula
built from an arbitrary finite nondeterministic Büchi automaton holds of an
ω-word exactly when that automaton accepts the word.

`FourierMotzkin` decides every closed sentence of rational linear inequalities
in every ordered field. A quantifier-free matrix is put in disjunctive normal
form and each conjunction loses its outermost variable by one Fourier–Motzkin
pass. The older `Sentence` entry still returns no verdict on a disjunction or
a universal sentence. Tarski elimination for polynomial inequalities is stated
there as an open goal.

`RabinTree` states Rabin automata on the infinite binary tree. Acceptance
along a branch reuses `InfinitelyOftenAccepting`. Emptiness, and the
equivalence with monadic second-order logic of two successors, are stated
there as open goals.

`ReachCertificate` checks a finite trace for may-reachability and a
natural-number ranking for inevitability. Liveness of an ω-word is a checked
lasso of a Büchi automaton, named there and proved in `BuchiAutomaton`.
-/
