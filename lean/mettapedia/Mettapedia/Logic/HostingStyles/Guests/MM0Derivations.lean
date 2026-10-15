import Mettapedia.Languages.MM0.Presentation.CalculusControls
import Mettapedia.Logic.HostingStyles.Guests.AuthoredProofSystems

/-!
# MM0 theories as proof systems, and what the candidate presentation hosts of them

An MM0 theory `T` is an authored calculus `mm0 T`: the seven rules of the MM0
kernel, and the three kernel operations (the theorem declared at an index, the
instance of a declaration, the conversion a witness establishes) as authored
facts with `T` as data.  Its proof system `mm0ProofSystem T` has the
derivations from those rules and facts, kept apart, and its derived rules as
contexts.

## The class

**For every MM0 theory the proof system is finitary and numbered**
(`mm0ProofSystem_numbered`).  Nothing is asked of the theory.  The names and
expressions of MM0 do not enter the numbering: a rule node is numbered by its
rule instance, which is a rule name with patterns, and a fact node carries no
data beyond its judgment.

## The cells

Under every evaluator of the premises of the candidate, for every theory `T`:

| | linear | regions | cartesian |
|---|---|---|---|
| derivations of a judgment, on terms | hosted, as numerals: `numeralsMap_hosting` | hosted | hosted |
| the theory with all its derived rules | **no map at all**: `presented_isEmpty_contextMap_mm0ProofSystem` | hosted, node by node: `atomsMap_hosting` | hosted: `cartesianAtomsMap_hosting` |

and as statements about the class: `presented_hostOf_mm0ProofSystem_terms`,
`regionProbe_hostOf_mm0ProofSystem_contexts`,
`cartesianProbe_hostOf_mm0ProofSystem_contexts`,
`presented_not_hostOf_mm0ProofSystem_contexts`.  The row of the theory with
its derived rules is one theorem, `mm0ProofSystems_separate_readings`.

The linear cell holds without a hypothesis on the theory, because every MM0
theory has a derivation: a local hypothesis derives itself
(`mm0_derivable_hypothesis`).

Each hosting map misses a term of the candidate
(`mm0_hosting_maps_miss_droppedAtom`).

## The hosted data are the theorems of MM0

For a judgment `context ⊢ expression` from local hypotheses:

* it has an atom of the candidate that stands for a derivation of it exactly
  when the MM0 kernel derives it (`exists_standsFor_iff_derives`);
* an atom stands for derivations of one such judgment at most: it determines
  the context, the hypotheses and the expression
  (`standsFor_derives_unique`).

One theory carried through: in the theory with one provable sort, one
constant and one axiom asserting it, the constant has an atom
(`withAxiom_constant_hosted`) and another term symbol has none
(`withAxiom_other_not_hosted`).
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HostingStyles.Guests

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef.Contexts (termSetoid)
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ContextualStep (BasePremiseEvaluator)
open Mettapedia.GSLT.LanguageDef.Authored
open Mettapedia.Languages.MM0
open Mettapedia.Languages.MM0.Presentation.Calculus
open Mettapedia.Languages.MeTTa.PrimeCandidates.LanguageDef (language)
open Mettapedia.Logic.HostingStyles.PrimeCandidate
open Mettapedia.Logic.HostingStyles.ContextReadings
open Mettapedia.Languages.MeTTa.PrimeCandidates.Language (Model)

/-! ## The class -/

/-- **The proof system of an MM0 theory**: the derivations from the rules of
the MM0 kernel and the kernel operations of the theory, kept apart, with the
derived rules as contexts. -/
noncomputable abbrev mm0ProofSystem (T : Kernel.Theory) : ContextTheory.{0} :=
  derivationTheory (mm0 T)

/-- **The proof system of every MM0 theory is finitary and numbered.** -/
theorem mm0ProofSystem_numbered (T : Kernel.Theory) : NumberedProofSystem (mm0ProofSystem T) :=
  derivationTheory_numbered (mm0 T)

/-- **The proof systems of the MM0 theories.** -/
def MM0ProofSystem (source : ContextTheory.{0}) : Prop :=
  ∃ T : Kernel.Theory, source = mm0ProofSystem T

/-- Each is the proof system of an authored calculus. -/
theorem MM0ProofSystem.authored (source : ContextTheory.{0}) (member : MM0ProofSystem source) :
    AuthoredProofSystem source := by
  obtain ⟨T, rfl⟩ := member
  exact ⟨mm0 T, rfl⟩

/-- **Negative**, for `MM0ProofSystem`: the proof system with an axiom for
each set of natural numbers is none. -/
theorem continuumAxioms_not_mm0ProofSystem :
    ¬ MM0ProofSystem
      (continuumAxioms.proofTheory (RuleSignature.ProofCongruence.identity continuumAxioms)) :=
  fun member => continuumAxioms_not_authoredProofSystem (MM0ProofSystem.authored _ member)

/-! ## Every theory has a derivation -/

/-- **In every MM0 theory a local hypothesis derives itself.** -/
theorem mm0_derivable_hypothesis (T : Kernel.Theory) (context : Kernel.Context)
    (expression : Kernel.Preterm) :
    (mm0 T).Derivable (derivesJ context [expression] expression) :=
  (factDerivation_iff context [expression] expression).mpr (.hypothesis List.mem_cons_self)

/-! ## The cells, for the class -/

/-- **Under every evaluator the candidate is a host of the proof systems of
the MM0 theories, on terms.** -/
theorem presented_hostOf_mm0ProofSystem_terms (base : BasePremiseEvaluator) :
    HostOf (presentedReading base) MM0ProofSystem .terms .hosting :=
  (presented_hostOf_authoredProofSystem_terms base).mono MM0ProofSystem.authored

/-- **Its reading with regions is a host of them with all their derived
rules.** -/
theorem regionProbe_hostOf_mm0ProofSystem_contexts (base : BasePremiseEvaluator) :
    HostOf (regionProbe base) MM0ProofSystem .contexts .hosting :=
  (regionProbe_hostOf_authoredProofSystem_contexts base).mono MM0ProofSystem.authored

/-- **So is its cartesian reading.** -/
theorem cartesianProbe_hostOf_mm0ProofSystem_contexts (base : BasePremiseEvaluator) :
    HostOf (cartesianProbe base) MM0ProofSystem .contexts .hosting :=
  (cartesianProbe_hostOf_authoredProofSystem_contexts base).mono MM0ProofSystem.authored

/-- **Under the linear reading no map of theories goes from the proof system
of an MM0 theory to the candidate**, whatever the theory. -/
theorem presented_isEmpty_contextMap_mm0ProofSystem (base : BasePremiseEvaluator)
    (T : Kernel.Theory) : IsEmpty (ContextMap (mm0ProofSystem T) (presentedReading base)) :=
  isEmpty_contextMap_presented_of_derivable (mm0 T) base
    (mm0_derivable_hypothesis T [] (.var 0))

/-- So the candidate is no host of the class with all contexts, under the
linear reading. -/
theorem presented_not_hostOf_mm0ProofSystem_contexts (base : BasePremiseEvaluator) :
    ¬ HostOf (presentedReading base) MM0ProofSystem .contexts .hosting := fun hosts =>
  let ⟨map, _⟩ := hosts (mm0ProofSystem {}) ⟨{}, rfl⟩
  (presented_isEmpty_contextMap_mm0ProofSystem base {}).false map

/-- **One class of guests, three readings**: with all their derived rules the
proof systems of the MM0 theories are not hosted under the linear reading and
are hosted under the reading with regions and under the cartesian reading. -/
theorem mm0ProofSystems_separate_readings (base : BasePremiseEvaluator) :
    ¬ HostOf (presentedReading base) MM0ProofSystem .contexts .hosting ∧
      HostOf (regionProbe base) MM0ProofSystem .contexts .hosting ∧
        HostOf (cartesianProbe base) MM0ProofSystem .contexts .hosting :=
  ⟨presented_not_hostOf_mm0ProofSystem_contexts base,
    regionProbe_hostOf_mm0ProofSystem_contexts base,
    cartesianProbe_hostOf_mm0ProofSystem_contexts base⟩

/-- **On terms the class is hosted under each of the three readings.** -/
theorem mm0ProofSystems_terms_row (base : BasePremiseEvaluator) :
    HostOf (presentedReading base) MM0ProofSystem .terms .hosting ∧
      HostOf (regionProbe base) MM0ProofSystem .terms .hosting ∧
        HostOf (cartesianProbe base) MM0ProofSystem .terms .hosting :=
  ⟨presented_hostOf_mm0ProofSystem_terms base,
    (regionProbe_hostOf_mm0ProofSystem_contexts base).terms,
    (cartesianProbe_hostOf_mm0ProofSystem_contexts base).terms⟩

/-- **The kernel reading of the candidate is a host of the class on terms**,
for every model: a derivation is kept as a quoted name. -/
theorem kernel_hostOf_mm0ProofSystem_terms (model : Model) :
    HostOf (kernelReading model) MM0ProofSystem .terms .hosting :=
  (kernel_hostOf_numberedProofSystem_terms model).mono fun source member =>
    AuthoredProofSystem.numbered source (MM0ProofSystem.authored source member)

/-- **With all derived rules no map goes into the kernel reading**, for any
model and theory: that reading has no context of two holes. -/
theorem kernel_isEmpty_contextMap_mm0ProofSystem (model : Model) (T : Kernel.Theory) :
    IsEmpty (ContextMap (mm0ProofSystem T) (kernelReading model)) :=
  kernel_isEmpty_contextMap_proofTheory model (derivationSignature (mm0 T)) _
    (derivesJ [] [] (.var 0))

/-- **Each hosting map misses a term of the candidate**: the dropping of the
quoted unit atom is the image of no derivation, under the map to numerals and
under the map to atoms, which the cartesian reading shares. -/
theorem mm0_hosting_maps_miss_droppedAtom (base : BasePremiseEvaluator) (T : Kernel.Theory)
    {goal : Pattern} (tree : (derivationSignature (mm0 T)).Proof goal) :
    ¬ ((presentedReading base).equations closedAtom).r droppedAtom
        ((numeralsMap (mm0 T) base goal).term (origin := PUnit.unit) tree) ∧
      ¬ ((regionProbe base).equations closedAtom).r droppedAtom
          ((atomsMap (mm0 T) base).term tree) ∧
        ¬ ((cartesianProbe base).equations closedAtom).r droppedAtom
          ((cartesianAtomsMap (mm0 T) base).term tree) :=
  ⟨droppedAtom_not_derivationNumeral (mm0 T) base tree,
    droppedAtom_not_derivationAtom (mm0 T) base tree,
    droppedAtom_not_derivationAtom (mm0 T) base tree⟩

/-! ## The hosted data are the theorems of MM0 -/

/-- **A judgment `context ⊢ expression` has a derivation in the proof system
exactly when the MM0 kernel derives it.** -/
theorem nonempty_tree_iff_derives (T : Kernel.Theory) (context : Kernel.Context)
    (hypotheses : List Kernel.Preterm) (expression : Kernel.Preterm) :
    Nonempty ((derivationSignature (mm0 T)).Proof (derivesJ context hypotheses expression)) ↔
      Kernel.Derives T.termSignature T.definitionSignature T.theoremSignature context hypotheses
        expression :=
  (nonempty_tree_iff_derivable (mm0 T) _).trans (factDerivation_iff context hypotheses expression)

/-- **A judgment `context ⊢ expression` has an atom of the candidate that
stands for a derivation of it exactly when the MM0 kernel derives it.** -/
theorem exists_standsFor_iff_derives (base : BasePremiseEvaluator) (T : Kernel.Theory)
    (context : Kernel.Context) (hypotheses : List Kernel.Preterm) (expression : Kernel.Preterm) :
    (∃ atom, StandsFor (mm0 T) base (derivesJ context hypotheses expression) atom) ↔
      Kernel.Derives T.termSignature T.definitionSignature T.theoremSignature context hypotheses
        expression :=
  (exists_standsFor_iff_derivable (mm0 T) base _).trans
    (factDerivation_iff context hypotheses expression)

/-- Different judgments `context ⊢ expression` are different patterns. -/
theorem derivesJ_injective {context other : Kernel.Context}
    {hypotheses otherHypotheses : List Kernel.Preterm} {expression otherExpression : Kernel.Preterm}
    (same : derivesJ context hypotheses expression =
      derivesJ other otherHypotheses otherExpression) :
    context = other ∧ hypotheses = otherHypotheses ∧ expression = otherExpression := by
  simp only [derivesJ, jDerives, Pattern.apply.injEq, List.cons.injEq, and_true, true_and] at same
  exact ⟨contextPattern_injective same.1, expressionsPattern_injective same.2.1,
    expressionPattern_injective same.2.2⟩

/-- **An atom stands for derivations of one judgment at most**: it determines
the context, the local hypotheses and the expression that it proves. -/
theorem standsFor_derives_unique (base : BasePremiseEvaluator) (T : Kernel.Theory)
    {context other : Kernel.Context} {hypotheses otherHypotheses : List Kernel.Preterm}
    {expression otherExpression : Kernel.Preterm} {atom : ProbeAtom}
    (first : StandsFor (mm0 T) base (derivesJ context hypotheses expression) atom)
    (second : StandsFor (mm0 T) base (derivesJ other otherHypotheses otherExpression) atom) :
    context = other ∧ hypotheses = otherHypotheses ∧ expression = otherExpression :=
  derivesJ_injective (standsFor_judgment (mm0 T) base first second)

/-! ## One theory carried through -/

/-- In the theory with one axiom, without local hypotheses, the kernel does not
derive a term symbol that the theory does not declare: it is no hypothesis, no
instance of the axiom, and the right side of no conversion, since it has no
sort. -/
theorem withAxiom_derives_ne_other : ∀ {expression : Kernel.Preterm},
    Kernel.Derives Controls.withAxiom.termSignature Controls.withAxiom.definitionSignature
        Controls.withAxiom.theoremSignature [] [] expression →
      expression ≠ .term 1
  | _, .hypothesis member => by cases member
  | _, .theoremApp (declaration := declaration) (arguments := arguments)
      (instantiation := instantiation) lookup instantiated _ => by
      intro same
      have found : declaration = Controls.axiomDecl := by
        simp only [Kernel.Theory.theoremSignature, Controls.withAxiom, List.lookup] at lookup
        split at lookup
        · exact (Option.some.inj lookup).symm
        · cases lookup
      subst found
      have substituted : Kernel.Preterm.substitute (Kernel.Substitution.ofList arguments)
          (.term 0) = some instantiation.conclusion := instantiated.conclusion.eval
      simp only [Kernel.Preterm.substitute, Option.some.injEq] at substituted
      rw [same] at substituted
      cases substituted
  | _, .conversion converted _ => by
      intro same
      subst same
      have evaluated : (none : Option Kernel.ExpressionType) = some ([], _) :=
        converted.typed.2.eval
      cases evaluated

/-- **Positive**: the constant that the axiom asserts has an atom of the
candidate that stands for a derivation of it. -/
theorem withAxiom_constant_hosted (base : BasePremiseEvaluator) :
    ∃ atom, StandsFor (mm0 Controls.withAxiom) base (derivesJ [] [] Controls.constant) atom :=
  (exists_standsFor_iff_derives base Controls.withAxiom [] [] Controls.constant).mpr
    (.theoremApp (index := 0) (declaration := Controls.axiomDecl) (arguments := []) rfl
      Controls.axiom_instance .nil)

/-- **Negative**: in the same theory another term symbol has none. -/
theorem withAxiom_other_not_hosted (base : BasePremiseEvaluator) :
    ¬ ∃ atom, StandsFor (mm0 Controls.withAxiom) base (derivesJ [] [] (.term 1)) atom := by
  intro hosted
  exact withAxiom_derives_ne_other
    ((exists_standsFor_iff_derives base Controls.withAxiom [] [] (.term 1)).mp hosted) rfl

/-- The two judgments, in the shared checker: a certificate is accepted for
the first and none for the second. -/
theorem withAxiom_accepts_constant_only :
    (mm0 Controls.withAxiom).Accepts (derivesJ [] [] Controls.constant) ∧
      ¬ (mm0 Controls.withAxiom).Accepts (derivesJ [] [] (.term 1)) :=
  ⟨Controls.axiom_certified, fun accepted =>
    withAxiom_derives_ne_other ((accepts_iff_derives [] [] (.term 1)).mp accepted) rfl⟩

#print axioms mm0ProofSystem_numbered
#print axioms continuumAxioms_not_mm0ProofSystem
#print axioms mm0_derivable_hypothesis
#print axioms presented_hostOf_mm0ProofSystem_terms
#print axioms regionProbe_hostOf_mm0ProofSystem_contexts
#print axioms cartesianProbe_hostOf_mm0ProofSystem_contexts
#print axioms presented_isEmpty_contextMap_mm0ProofSystem
#print axioms presented_not_hostOf_mm0ProofSystem_contexts
#print axioms mm0ProofSystems_separate_readings
#print axioms mm0ProofSystems_terms_row
#print axioms kernel_hostOf_mm0ProofSystem_terms
#print axioms kernel_isEmpty_contextMap_mm0ProofSystem
#print axioms mm0_hosting_maps_miss_droppedAtom
#print axioms nonempty_tree_iff_derives
#print axioms exists_standsFor_iff_derives
#print axioms standsFor_derives_unique
#print axioms withAxiom_derives_ne_other
#print axioms withAxiom_constant_hosted
#print axioms withAxiom_other_not_hosted
#print axioms withAxiom_accepts_constant_only

end Mettapedia.Logic.HostingStyles.Guests
