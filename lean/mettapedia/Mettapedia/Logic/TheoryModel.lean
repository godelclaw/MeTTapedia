import Mettapedia.Logic.TheoryModel.Basic
import Mettapedia.Logic.TheoryModel.Consistency
import Mettapedia.Logic.TheoryModel.Weakness
import Mettapedia.Logic.TheoryModel.Universe
import Mettapedia.Logic.TheoryModel.Forgetting
import Mettapedia.Logic.TheoryModel.IdentityProofs
import Mettapedia.Logic.TheoryModel.IdentityCarve
import Mettapedia.Logic.TheoryModel.ArrowIdentification
import Mettapedia.Logic.TheoryModel.ClassifyingBridge
import Mettapedia.Logic.TheoryModel.WeaknessMeasures
import Mettapedia.Logic.TheoryModel.InstitutionBridge
import Mettapedia.Logic.TheoryModel.DegenerateTop
import Mettapedia.Logic.TheoryModel.WeakestCorrect

/-!
# Theories and models

* `Basic`: the order-reversing Galois connection between theories and classes
  of structures for an arbitrary satisfaction relation, its closure operators,
  the anti-isomorphism of closed theories and elementary classes, adding
  axioms, and translations preserving satisfaction.
* `Consistency`: a theory is consistent when it has a model; for two sentences
  this is a common model, which is the consistency of gradual types when
  concretization is the satisfaction relation.
* `Weakness`: weakest admissible theories are theories of largest admissible
  classes; entailment constraints give the consequence closure, region
  constraints the elementary interior, which need not be elementary.
* `Universe`: universes hosting models, monotonicity in the universe, and
  faithful hosting.
* `Forgetting`: coarsening an observer weakens its observed theory; its Galois
  connection with languages, which is not an insertion and is a coinsertion
  exactly for separating languages; identifications imposed as axioms
  strengthen, and equational consequence is equivalence closure.
* `IdentityProofs`: identity proofs with and without identification of
  parallel proofs, a ladder of universes, a univalent structure, larger Lean
  universes, and forgetting versus identifying proofs.
* `IdentityCarve`: carving a universe by axioms computes the consequences of the
  enlarged theory, and the carved closed theories are a Galois insertion into the
  ambient ones; the groupoid-valued universe hosts the groupoid laws faithfully and
  its h-set fragment validates exactly the theory of `uipLaws`; Mathlib groupoids,
  the extensional identity of presheaves, and presheaves of groupoids.
* `ArrowIdentification`: functors and identifications of parallel arrows;
  consequences are generated congruences, thin targets are unfaithful.
* `ClassifyingBridge`: equations of a binding signature and their term
  arrows, through the classifying construction and `satisfyingEquivalence`.
* `WeaknessMeasures`: Bennett, quantale, credal and prior readings of the
  weakness of a theory, and Bennett's extensions as model classes.
* `InstitutionBridge`: institution consequence as `theoryOf ∘ models`, and a
  comorphism is conservative on a theory exactly when its universe of reducts
  hosts the theory faithfully.
* `DegenerateTop`: the models of the theory of all sentences are the degenerate
  structures, which no axiom carves away; consistency is vacuous when one
  exists; a consistent theory in a second language changes no consequence of
  the first, so "every type inhabited" is conservative; what transfers from a
  top to its fragments; weakness across a declared translation.
* `WeakestCorrect`: among candidates correct on the observed structures, the
  chance of admitting every future requirement is ordered by the size of the
  model class under a uniform future, and monotone in it under an exchangeable
  one.
-/
