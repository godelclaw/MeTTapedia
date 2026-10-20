import Mettapedia.Logic.HOL.SevenVirtues.UniformSyntax
import Mettapedia.Logic.HOL.SevenVirtues.Typing
import Mettapedia.Logic.HOL.SevenVirtues.StandardModels
import Mettapedia.Logic.HOL.SevenVirtues.Expressiveness
import Mettapedia.Logic.HOL.SevenVirtues.Peano
import Mettapedia.Logic.HOL.SevenVirtues.Completeness
import Mettapedia.Logic.HOL.SevenVirtues.GeneralModels
import Mettapedia.Logic.HOL.SevenVirtues.OrderedField
import Mettapedia.Logic.HOL.SevenVirtues.Choice
import Mettapedia.Logic.HOL.SevenVirtues.Implementations
import Mettapedia.Logic.HOL.SevenVirtues.Finiteness
import Mettapedia.Logic.HOL.SevenVirtues.DedekindInfinityForms
import Mettapedia.Logic.HOL.SevenVirtues.FirstOrderFaithfulness
import Mettapedia.Logic.HOL.SevenVirtues.KernelConservativity
import Mettapedia.Logic.HOL.Semantics.KripkeVaryingCanonical
import Mettapedia.Logic.HOL.Semantics.HenkinWitnessService
import Mettapedia.Logic.HOL.Semantics.BethHenkin
import Mettapedia.Logic.HOL.Semantics.BethFrame
import Mettapedia.Logic.HOL.Semantics.BethTree
import Mettapedia.Logic.HOL.Semantics.BethTreeControls
import Mettapedia.Logic.HOL.Semantics.TermEnumeration
import Mettapedia.Logic.HOL.Semantics.KripkeHenkinOfFrame

/-!
# Farmer's seven virtues of simple type theory

W. M. Farmer, *The Seven Virtues of Simple Type Theory*, Journal of Applied
Logic 6(3):267–286, 2008, lists seven virtues. Each is read here as theorems
about the Church-style calculus of `Mettapedia.Logic.HOL`.

1. *A simple and highly uniform syntax.* Variables, constants, application,
   abstraction and equality suffice: `UniformSyntax.eqExpand` replaces every
   logical constructor by its HOL Light definition, the result denotes the same
   value in every Henkin model (`UniformSyntax.denote_eqExpand`), and the
   calculus proves `t = eqExpand t` without excluded middle
   (`UniformSyntax.provable_eq_eqExpand`). Without equality there is no
   sentence (`UniformSyntax.no_lambda_sentence`). Raw Church-style terms have
   unique, decidable types (`Typing.typing_unique`, `Typing.typable_iff`).
2. *A semantics based on a few established ideas.* General models are full
   exactly when they are full in Andrews' sense, when their equality is literal
   equality, and when they are standard models
   (`HenkinModelFacts.fullDomains_iff_andrewsFull`,
   `HenkinModelFacts.fullDomains_iff_eqv_eq`,
   `HenkinModelFacts.fullDomains_iff_standard`); standard models with
   corresponding bases and constants satisfy the same sentences
   (`standard_models_iff`).
3. *High expressiveness.* One sentence defines infinity of a base type in
   standard models (`models_dedekindInfinite_iff`) and its negation finiteness
   (`models_finite_iff`); the tree's three statements of Dedekind infinity (this
   sentence, HOL Light's `ONE_ONE f /\ ~(ONTO f)`, and the semantic witness
   `HasDedekindInfiniteBase`) agree in full-domain models
   (`DedekindInfinityForms.models_infinityFormula_iff_models_dedekindInfinite`);
   no first-order theory defines finiteness and no
   first-order sentence defines infinity (`FirstOrder.no_theory_of_finite`,
   `FirstOrder.no_sentence_of_infinite`). First-order logic embeds
   faithfully: first-order consequence is consequence over standard models of
   the translated theory with an inhabited individual type
   (`FirstOrderFaithfulness.faithful`, Farmer's Theorem 2 for first-order
   logic), and the inhabitation sentence is needed
   (`FirstOrderFaithfulness.inhabitation_needed`).
4. *Categorical theories of infinite structures.* Peano's axioms have exactly
   one full model up to isomorphism (`Peano.categorical`), all full models
   satisfy the same sentences (`Peano.semanticallyComplete`), and they force an
   infinite base (`Peano.infinite_of_models`); without induction categoricity
   fails (`Peano.not_categorical_without_induction`), and first-order theories
   with infinite models are never categorical (`FirstOrder.not_categorical`).
   The complete ordered field is categorical too, with the real numbers as its
   full model (`OrderedField.categorical`, `OrderedField.full_model_is_real`);
   a primitive inverse with an unconstrained value at `0` would break this
   (`OrderedField.inverse_expansions_not_isomorphic`).
5. *A simple, elegant, powerful proof system.* The natural-deduction calculus
   with one excluded-middle axiom is sound and complete for extensional Henkin
   models over countable signatures with closed inhabitants
   (`provable_iff_valid`, `consistent_iff_satisfiable`); without that axiom it
   is incomplete (`incomplete_without_excludedMiddle`). For standard models no
   finitary calculus is strongly complete
   (`Nonstandard.no_strongly_complete_finitary_calculus`). Without the axiom
   the calculus is complete for Heyting-valued models
   (`HeytingSem.provable_iff_heytingConsequence_param_free`) and, over
   countable signatures with a closed term at each base type, for
   varying-domain Kripke models
   (`KripkeVarying.Canonical.provable_iff_consequence`); it is not complete
   for constant-domain Kripke models, which validate the constant-domain
   sentence (`KripkeHenkin.not_complete`, `constantDomain_not_derivable`).
   The enumeration data of the varying-domain proof is exactly a fair service
   of the Henkin witness obligations, computable from enumerations of bodies
   and pairs (`provable_of_consequence_of_services`,
   `witnessServiceOfEnumerations`).  With constant domains, forcing
   disjunction and the existential on covers gives a Beth semantics that is
   sound and complete (`provable_iff_bethConsequence_param_free`) and refutes
   the constant-domain sentence (`realLine_not_forces_constantDomain`); its
   local sets form a frame, giving completeness for frame-valued models
   (`provable_iff_frameConsequence_param_free`).  For Beth's tree models with
   bars, completeness comes from the canonical tree of Henkin runs and needs
   fair schedules of disjunctions and existentials
   (`BethTree.provable_of_treeBethConsequence_of_services`); with a starving
   schedule the disjunction clause fails (`BethTree.Controls.starving_or_clause_fails`).
   For encodable signatures the schedules are computable
   (`TermEnumeration.provable_iff_treeBethConsequence_of_encodable`).
6. *General models carry first-order model theory and separate standard from
   nonstandard models.* Compactness (`compactness`) and downward
   Löwenheim–Skolem (`exists_countable_model`) hold for general models;
   Peano's axioms have a nonstandard general model
   (`Nonstandard.exists_nonstandard_model`, `Nonstandard.not_categorical`),
   standard semantics is not compact (`Nonstandard.standard_not_compact`) and
   standard consequence differs from general consequence
   (`Nonstandard.consequence_differs`). One sentence separates standard and
   general validity: choice holds in every full model with a nonempty base and
   fails in an extensional permutation model (`Choice.choice_separates`), so
   neither it nor its negation is derivable (`Choice.choice_not_provable`,
   `Choice.not_choice_not_provable`), even with the axiom of descriptions
   (`Choice.choice_not_provable_with_description`). In that model the infinite set of atoms
   satisfies the sentence `finite ι` (`Choice.permutationModel_finite_but_infinite`):
   the atoms are Dedekind-finite but not Kuratowski-finite
   (`Choice.permutationModel_dedekind_not_kuratowski`), so Dedekind finiteness
   does not derive Kuratowski finiteness
   (`Choice.dedekind_imp_kuratowski_not_provable`), while in full models both
   mean finiteness (`models_kuratowskiFinite_iff_models_finite`).
   The complete ordered field has a countable general model
   (`exists_countable_real_model`).
7. *Practical extensions that can be implemented.* The HOL Light, MM0-hosted
   HOL Light and Megalodon checkers of this library are sound for Henkin
   models (collected in `SevenVirtues.Implementations`), and the HOL Light
   Boolean definitions mean the intended connectives in every Henkin model
   (`UniformSyntax.denote_conjunction_general`). The HOL Light kernel without
   axioms proves nothing beyond the calculus: an accepted proof graph has a
   translation derivable without excluded middle
   (`KernelConservativity.checker_translatedProvable`).
-/
