import Mettapedia.Logic.EvidenceKinds.Dependencies
import Mettapedia.Logic.EvidenceKinds.Verdicts
import Mettapedia.Logic.EvidenceKinds.Instances
import Mettapedia.Logic.EvidenceKinds.Beliefs
import Mettapedia.Logic.EvidenceKinds.Feedback
import Mettapedia.Logic.EvidenceKinds.Race
import Mettapedia.Logic.EvidenceKinds.Knowledge

/-!
# Evidence kinds and their lawful combination

Results say where they come from: proved under stated assumptions and a conversion profile, an
admitted run, tested, believed with PLN evidence, hypothesized, trusted, or unknown.

* `Dependencies`: a derived result is a claim under a dependency set whose atoms have sorts
  (assumption, profile, executor lane, hypothesis, trust promise). Proved, admitted run,
  hypothesized and trusted are one shape, told apart by the sorts that remain. The laws of
  combination are forced by the meaning: the union for premises, one alternative's set for
  alternatives, inclusion for strength; discharge is the only way an atom leaves.
* `Verdicts`: established, refuted, unknown; strong Kleene tables are the most informative sound
  ones; unknown becomes refuted only by a refutation.
* `Instances`: tests as instance results (coverage turns them into a proof) and as identified
  observations (the ledger contract).
* `Beliefs`: the stamp guard of PLN revision is the ledger contract; derived beliefs rest on their
  premises; a proof is not a count; the multiset world-model judgment does not bound use, the
  linear one does.
* `Feedback`: lineage and why-provenance through rules; deletion exact on every rule set with
  why-provenance; feedback through `whenever` rules refused by lineage; counts inflate on a cycle.
* `Race`: racing proofs publish the closing proof's dependency set; rejected proofs and exhausted
  checks are not refutations of the goal.
* `Knowledge`: one store per shape, merged componentwise; verdicts are readers' policies over
  granted atoms; counts are a valuation of the ledger.
-/
