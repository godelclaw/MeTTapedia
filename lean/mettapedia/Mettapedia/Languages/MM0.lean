import Mettapedia.Languages.MM0.SyntaxSpec
import Mettapedia.Languages.MM0.ArtifactBundle
import Mettapedia.Languages.MM0.MeTTa
import Mettapedia.Languages.MM0.Kernel.DefinitionFreeConversion
import Mettapedia.Languages.MM0.Kernel.VacuousDummies
import Mettapedia.Languages.MM0.Translation.FirstOrderTyping
import Mettapedia.Languages.MM0.Translation.FirstOrderConversion
import Mettapedia.Languages.MM0.Translation.FirstOrderRules
import Mettapedia.Languages.MM0.Translation.FirstOrderBasePresentation
import Mettapedia.Languages.MM0.Translation.FirstOrderAdmission
import Mettapedia.Languages.MM0.Translation.FirstOrderSession
import Mettapedia.Languages.MM0.Translation.FirstOrderControls
import Mettapedia.Languages.MM0.Translation.FirstOrderFragmentControls
import Mettapedia.Languages.MM0.Translation.FirstOrderPropositionalMeaning
import Mettapedia.Languages.MM0.Translation.FirstOrderHOLMeaning
import Mettapedia.Languages.MM0.Translation.FirstOrderModalMeaning
import Mettapedia.Languages.MM0.Translation.FirstOrderUniversality
import Mettapedia.Languages.MM0.Kernel.ProofComplexity
import Mettapedia.Languages.MM0.Formats.MMB.MachineCost
import Mettapedia.Languages.MM0.Translation.CertificateSimulation
import Mettapedia.Languages.MM0.Translation.CertificateEquivalence
import Mettapedia.Languages.MM0.Translation.UniversalTraceBound
import Mettapedia.Languages.MM0.Translation.CalculusSimulation

/-!
# MM0 theories, checking semantics, and language-definition translations

The kernel and retained MeTTa service are connected to MM0's specified
judgments by the imported session results. The syntax and artifact modules
retain the authored MM0 grammar and its boundary evidence.

`Translation.FirstOrderTyping` compiles ordinary, many-sorted constructor
declarations from a `LanguageDef`. Named patterns and MM0 application spines
have the same typing and admissible substitution judgments; every typed
target expression has a source representative. Constructor names and notation
remain in the source signature alongside its numeric MM0 signature.
`Translation.FirstOrderControls` exercises this interface through the existing
module quotation, including wrong-sort and conflicting-name refusals.

`Translation.FirstOrderRules` compiles the complete admitted inference
presentation into actual MM0 sort, term, definition and axiom tables. The
equations of the source language are its definitions: each is an authored
equation whose left side is a constructor applied to its formals, and each
compiles to one MM0 definition without dummy variables.
`Translation.FirstOrderConversion.converts_iff` identifies the language's
equation theory, on typed first-order terms, with MM0's typed conversion,
and computes the conversion evidence. `Presentation.derivability_iff`
preserves and reflects derivability modulo the definitions in open,
many-sorted contexts. `Presentation.derivability_iff_checked` connects it to
the existing supplied-certificate checker. Every rule instance checks its
entire argument vector against the declared formal sorts. A language without
equations is the case with no definitions, where a conversion step changes
nothing: `Presentation.derivability_iff_of_equationFree`.
`Translation.FirstOrderBasePresentation` gives the other exact route: unfold
every definition first and check in the definition-free theory of the base
presentation. `Presentation.definitions_conservative` states that the two
generated theories derive the same statements up to unfolding.

`Translation.FirstOrderFragment` states which MM0 theories these are. A
theory is first-order (`Kernel.Theory.FirstOrder`) when none of its
declarations binds a variable: no bound formal, no dependency, no dummy
variable. Every generated theory is first-order
(`FirstOrderFragment.generated_firstOrder`), and every first-order theory
with names is the generated theory of a presentation
(`FirstOrderTheoryPresentations.theory_sourcePresentation`), read off its
tables with the definitions in their order of admission. So the class of
presentations and the first-order fragment of MM0 are one class, and
`FirstOrderTheoryPresentations.derives_iff` restates MM0 derivability in a
first-order theory as derivability modulo the definitions of the language
read from it.

`Translation.FirstOrderPropositionalMeaning` attaches a semantics to two
generated theories. Intuitionistic and classical propositional logic are
authored as presentations whose rules are those of a standard Hilbert
system, one for one, and the presentation derives exactly what that system
proves (`PropositionalHilbert.derives_iff_hilbert`). With the soundness and
completeness theorems of the `Foundation` library, the MM0 checker accepts
a proof of a formula in the intuitionistic theory exactly when the formula
is valid on every Kripke frame (`mm0_checks_iff_kripke`), and in the
classical theory exactly when it is a tautology
(`mm0_checks_iff_tautology`). The two theories differ by one axiom, and
some formula is accepted in the classical one only
(`mm0_excludedMiddle_adds`).

`Translation.FirstOrderHOLMeaning` states the same acceptance in HOL. The
intuitionistic theory accepts exactly what HOL proves without excluded
middle, and exactly what holds in every Kripke-Henkin general model of HOL
(`accepted_iff_hol`, `accepted_iff_kripkeHenkin`). The classical theory
accepts exactly what HOL proves from the excluded-middle schema, and exactly
what every extensional Henkin model of HOL satisfies (`accepted_iff_hol_em`,
`accepted_iff_henkin`).

`Translation.FirstOrderModalMeaning` does the same for classical modal
logics. Each is a presentation with the RE rule and finitely many extra
axioms, and the checker accepts exactly the theorems of its Hilbert system
(`accepted_iff_hilbert`). For `E`, `EM`, `EN`, `EMN` and `EMT` this is
validity on the neighborhood frames of the logic
(`accepted_iff_neighborhood`). Read through the world-model calculus, whose
states are multisets of pointed neighborhood models, an implication is
accepted exactly when it orders the evidence strengths on every single point
of the class (`accepted_imp_iff_evidence`).

`Translation.FirstOrderUniversality` locates first-order MM0 among the
decision problems. One fixed theory, compiled from a presentation of the
partial recursive functions, accepts a proof that a code halts on an input
exactly when it does (`mm0_checks_halts_iff`). So every recursively
enumerable predicate on numbers is the set of inputs on which one code has
an accepted halting proof, provability in that theory is undecidable, and
its unprovable statements are not recursively enumerable. Conversely
`Kernel.FirstOrderEnumeration.derives_re` compiles every first-order theory,
in any context and under any hypotheses, to an elementary formal system and
proves that its derivable expressions are recursively enumerable. Together,
a predicate on numbers is recursively enumerable exactly when some
first-order theory derives exactly its instances (`re_iff_firstOrder_mm0`).

`Kernel.ProofComplexity` places the kernel's checker among proof systems in the
sense of Cook and Reckhow. A context, hypotheses and a witness determine the
sequent they prove (`functionForm_exact`), and computing it takes time polynomial
in the witness, the sequent and the width of the theory (`proofTime_le`), so every
finite theory's checker is such a proof system (`Theory.proofSystem`).
`Formats.MMB.MachineCost` counts the transitions of the binary format's reference
machine: a proof stream of `n` commands finishes within `(U + 2) * n + 1`
transitions, `U` the longest unify stream of the tables (`run_evalsToInTime`).
`Translation.CertificateSimulation` proves that MM0 p-simulates the tree
checker of every first-order presentation: compiled witnesses are at most twice
the tree, and the translation runs in linear time (`compileSimulation`), Frege
systems included (`fregeSimulation`). `Translation.CertificateEquivalence` reads
MM0 witnesses back as raw proof trees of a presentation without equations
(`decompile_accepted`), no larger and in polynomial time, so the two checkers
p-simulate each other (`pEquivalent`).
`Translation.UniversalTraceBound` separates explicit and computing certificates
in one theory. Every MM0 proof that `powCode (n + 1)` halts in the universal
theory has more than `2 ^ n` nodes, while a checker that runs the code accepts
the same claim with a fuel of `n + 2` bits, so the MM0 checker does not
size-simulate it (`no_sizeSimulation`). `Translation.CalculusSimulation`
extends the p-equivalence to every first-order calculus of the generic inference
checker, through one fixed sorted grammar of patterns (`pEquivalent`), and MM0
p-simulates every checker with a polynomial trace into such a calculus
(`traceSimulation`).

`Translation.FirstOrderCertificates.checksModulo_iff_compiled` retains and
checks the submitted named certificate tree, including local premise
occurrences and conversion steps; `checks_iff_compiled` is its case at
certificates without conversion steps.
`Translation.FirstOrderAdmission.admitted` derives sequential declaration
admission from the empty MM0 theory: sorts, primitive constructors, the
definitions in authored order, then the axioms. Each definition is admitted
over the terms that precede it. `Translation.FirstOrderSession` composes
this with the actual MeTTa start/submit/finish driver: source certificate
acceptance is equivalent to its PeTTa whole-run judgment and operational
GSLT path, with the supplied proof retained.
`source_certificate_iff_languageDef` reaches the authored PeTTa configuration
LanguageDef through `langGSLTUsing`, preserving the decoded final store and
ordered answer/input/output observation. Loading the program derives the
representation's finite-store support premises.

`Translation.FirstOrderModules.compile_join_relocated` relates separate
compilation and origin-sensitive module joins through explicit sort,
constructor and rule reference maps. Actual declaration payloads and proof
trees relocate; shared origins survive and source conflicts refuse.
`Translation.FirstOrderPrinting` emits MM0, MMU and explicit-argument MM1
using retained authored names and supported notation. Its native text boundary
is independently qualified rather than asserted by the derivability theorem.

The authoring surface is the shared `moduleTheory!` quotation extended by
typed `Judgments` and `Inferences` blocks (`inferenceTheory!`). The current
fragment has ordinary many-sorted constructors and inference rules, open
contexts and hypotheses, and definitions authored in the `Equations` block,
without bound or dummy variables. It has no object binders and no implicit
computation. The whole-run path uses the consolidated PeTTa GSLT; it is
not an assertion that a rewrite-only syntax language executes the checker.
-/
