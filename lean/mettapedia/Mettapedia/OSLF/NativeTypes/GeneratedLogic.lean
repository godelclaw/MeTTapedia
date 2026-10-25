import Mettapedia.OSLF.NativeTypes.GeneratedLogic.Formula
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.Semantics
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.Substitution
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.Reference
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.Transfer
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.Invariance
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.Generated
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.Controls
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.Finite
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.FiniteControls
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.CertificateEquations
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.Certificates
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.CertificateControls
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.EquationControls
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.Exploration
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.BoundedMorphism
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.ClosedExploration
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.Search
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.SearchControls
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.ClosedControls
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.Verdicts
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.VerdictControls
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.Equivalence
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.EquivalenceControls
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.StructuralEquivalence
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.StructuralControls
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.HigherOrder
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.HigherOrderControls
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.SyntacticEmbeddings
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.MuEmbedding
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.FrontDoorEmbeddings
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.DriverBridge
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.EmbeddingControls
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.VerdictCatalogue
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.VerdictCatalogueControls
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.CountingControls
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.Completeness
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.CompletenessControls
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.AcceptanceMatrix
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.CanonicalRegions
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.CompletenessModulo
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.Resumption
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.Persistence
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.CanonicalRegionControls
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.CanonicalUnwrapControls
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.SubstitutionControls
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.BagCanonicalForms
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.PetriControls
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.ProtocolControls
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.CalculusPresentation
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.CalculusControls
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.RegexControls
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.InstanceControls
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.AlgebraCanonicalForms
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.PiCanonicalForms
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.PiControls
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.Readings
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetReadings

/-!
# The native type language a language generates

- `Formula`: the formulas, in negation normal form with an involutive dual: structural formers from
  constructors, collection kinds and binders; modalities from steps, labelled by rule and by site;
  counting modalities, which count distinct terms one step away; types, singletons and quantifiers over
  a type; least and greatest fixed points.
- `Semantics`: satisfaction in a native structure over a carrier; the dual is negation.
- `Substitution`: renaming and substituting fixed-point variables, with their meaning; substituting closed
  formulas for free atoms closes a formula with the same truth.
- `Reference`: the native structure of a language, its terms read modulo its equations.
- `Transfer`: existential formulas hold at images of a homomorphism, universal ones come back.
- `Invariance`: formulas are monotone, and closed formulas hold alike at equivalent terms.
- `Generated`: Φ(L), the formulas whose formers the language provides, closed under the dual.
- `Controls`: positive and negative examples of each.
- `Finite`: an exact evaluator on finite structures, with fixed points by iteration.
- `CertificateEquations`: finite checks that a certificate's model respects the language's equations
  (bag, set and algebra laws, and first-order authored equations).
- `Certificates`: a valid finite-model certificate maps the language's structure into a finite one, so
  the evaluator's verdicts there are theorems about the language.
- `Exploration`: a listed region of terms sits inside the language, so existential formulas that hold
  there hold in the language, and universal formulas whose dual holds there fail.
- `BoundedMorphism`: along a homomorphism whose image's steps and shapes come from the source, every
  forward formula is preserved and reflected.
- `ClosedExploration`: a closed region (complete successor lists, all parts, no duplicates) decides every
  forward formula exactly: stuckness, ∀∃ alternations and counting of results included.
- `CanonicalRegions`: closed regions modulo equations. Along a step morphism every behavioural formula is
  preserved and reflected; canonical forms that meet their contract, with coherence, make a closed region
  of canonical terms decide those formulas exactly for the language read modulo its equations.
- `BagCanonicalForms`: canonical forms for bags, every bag sorted bottom up, on object terms with no set
  whose bags are sorted at a bag carrier. They meet the contract in a language with no authored equation
  and no collection algebra, and rules whose premises are guards (relation queries with no arguments) are
  coherent with them: matching commutes with sorting, and instantiation respects it.
- `CalculusPresentation`: a proof calculus read as rewriting on goal stacks. A rule whose conclusion fixes
  its instance is the rewrite `[conclusion, ...rest] ⇒ [premises, ...rest]`; on proper goal lists the
  presentation's steps are exactly resolution steps by such rules, and where only such rules conclude,
  derivability is the formula "some run reaches the empty stack".
- `Search`: certificates as codes with Kraft lengths; Levin search over them; `ask`, which answers
  proved or refuted with its evidence, or open with a proved lower bound on the complexity of any
  certificate that would decide the question. Given canonical forms, it also weighs closed canonical
  regions.
- `Completeness`: on an equation-free language, a term whose closure under steps and parts is finite and
  completely listed gets an answer from `ask` for every forward formula, proved or refuted, never open.
- `CompletenessModulo`: given canonical forms, a term whose canonical closure is finite and completely
  listed gets an answer from `ask` for every behavioural formula, proved or refuted, never open.
- `Resumption`: the work of a question (three regions and two searches) kept as progress; resuming it
  reads only what it keeps, gives the progress of the longer question, and answers as the front door
  does with all the rounds.
- `Persistence`: more rounds never undo an answer: proved stays proved and refuted stays refuted, since
  each kind of evidence persists. The portfolio is fair: when any one kind of evidence decides the
  question, the front door answers then and at every later round.
- `AcceptanceMatrix`: the front door's answers over a grid of terms and formulas for λ with full β, and
  over the constants of a language with an equation, with the kind of evidence that settled each.
- `Verdicts`: one verdict type, displayed evidence about a proposition, into which `ask`, the shared
  proof-carrying outcome and the strategies' own verdicts map with their soundness.
- `VerdictCatalogue`: the remaining verdict types (checking, admission, backward past boxes, MM2 batches,
  focus and discovery sessions, native queries, the OSLF checker) read the same way; a negative answer
  without a soundness theorem makes no claim. The OSLF checker's verdicts are verdicts about the
  generated formulas its formulas embed as.
- `Equivalence`: the equivalence native types induce. All of Φ(L) separates a language's states exactly
  up to its equations; the behavioural fragment induces forward-backward bisimilarity on finitely
  branching structures (Hennessy–Milner, with past steps and fixed points).
- `StructuralEquivalence`: the first-order fragment induces structural bisimilarity, which also matches
  decompositions, splits, members, bodies and atoms.
- `HigherOrder`: every formula is a predicate of higher-order logic over a native structure's relations,
  built from equality, abstraction and application, with the same truth in the standard model; a
  formula of Φ(L) mentions only L's own relations.
- `SyntacticEmbeddings`, `MuEmbedding`, `FrontDoorEmbeddings`: the other formula languages embed with
  their meanings. These are the structural-modal formulas, the original OSLF formulas, the modal
  μ-calculus over any labelled transition system a structure realizes, the front-door formulas with
  their queries, and the propositional codes. Negation is translated by polarity, atoms become paired
  free variables, and fixed points need their variables at the polarity of their binders.
- `DriverBridge`: the driver-based front door read in the generated logic. Given a faithful rendering of
  a driver's GSLT into the reference structure and its tests as closed formulas, a driver formula's
  meaning is the truth of a closed generated formula; the generated front door's answers settle it, and
  in an equation-free language it decides every driver formula on a finite closure.
- `FiniteControls`, `CertificateControls`, `SearchControls`, `EquivalenceControls`, `StructuralControls`,
  `HigherOrderControls`, `EmbeddingControls`, `VerdictCatalogueControls`, `CountingControls`,
  `CompletenessControls`, `CanonicalRegionControls`, `CanonicalUnwrapControls`, `SubstitutionControls`,
  `PetriControls`, `ProtocolControls`, `CalculusControls`, `RegexControls`, `InstanceControls`:
  fixed points on small structures; full β under binders, proved safe by a two-value certificate;
  asking with evidence from both sides; bisimilar but distinct, past steps that separate, shapes that
  separate, copies that agree; translations true and false where their formulas are, a primitive
  conjunction outside the basis, and a missing rule outside the signature; embedded formulas that hold
  and fail where their originals do, and `μX. ¬X`, whose reading changes without positivity; the OSLF
  checker proving a generated formula; determinism decided by closed regions, where two steps to the same
  term count once; every forward formula about a finite term decided in ten rounds; a constant with no
  step as written that steps modulo an equation, decided through canonical forms by the front door, and
  canonical forms that mislead without coherence; an equation with a metavariable whose rule fires on
  terms that are not canonical, coherent because canonical forms simulate steps; an atom closed by
  substitution, true and false where the closed formula is; the authored Petri net and guarded workflow,
  decided modulo their bag laws, with steps to different presentations of one marking counted once, and
  sets left out because their matches read repetitions; GödelClaw's reconciliation and display tables,
  total and deterministic, with an absorbing finished state, and not composed without a congruence;
  derivations found and refuted by the front door in HOL Light's kernel, NARS revision and PLN evidence,
  where disjoint sources license revision and overlapping ones do not; regular expressions matched by
  big-step derivative rules, with letters compared by a relation environment; the tree's λ-calculus and
  TinyML as written, where a closed region of one term proves that Ω runs forever.
-/
