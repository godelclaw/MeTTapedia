import Mettapedia.OSLF.NativeTypes.Generation.BindingCenter
import Mettapedia.OSLF.NativeTypes.SortProfiles.Binding.CenterStability

open Mettapedia.OSLF.Framework

/-!
# Contextual consequences of the generator's accepted binding equations

The source relation retains original laws, computed carrier candidates,
successful source compilation, ordered provider guards and contextual
assignments. The independent consequence relation closes these source
instances under equivalence, every declaration-derived binder context and
actual simultaneous substitution. The generator's finite semantic checks
prove this complete relation sound in its binding valuation interpretation.

Directed laws remain a separate admission. This equation interpretation does
not identify a binding-model center with the universe-kind formation center.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Generation.BindingStability

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.GeneralPremise
open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.Binding.FreeBindingTerms
open Mettapedia.OSLF.Binding.BindingCloneFoldSubstitution
open Mettapedia.GSLT.LanguageDef.BindingSyntax
open Mettapedia.GSLT.LanguageDef.BindingSyntax.ScopedElaboration
open Mettapedia.OSLF.NativeTypes.SortProfiles.Laws.Compiler Mettapedia.OSLF.NativeTypes.SortProfiles.Laws.BindingCodec
open Mettapedia.OSLF.NativeTypes.SortProfiles.Laws.NullaryGuards Mettapedia.OSLF.NativeTypes.SortProfiles.Laws.FiniteBinding
open Mettapedia.OSLF.NativeTypes.Generation Mettapedia.OSLF.NativeTypes.Generation.BindingCenter Mettapedia.OSLF.NativeTypes.SortProfiles.Binding.CenterStability

theorem checked_carrier_contextual_satisfaction
    {language : LanguageDef} {provider : ProviderSnapshot}
    (constructors : Constructors language) {law : Law}
    (stable : BindingSemanticStable language provider constructors law)
    {type : TypeExpr} (candidate : type ∈ carrierCandidates language law)
    (compiled : CompiledLaw language law type)
    (sourceRead : compileLaw? language law type = some compiled)
    (guards : List Witness) (guardRead : GuardedBy provider 0 law.premises guards)
    (active : enabled guards = true) :
    BindingEquationInterpretation.Satisfies (Valuation.algebra constructors)
      [singletonEquation language
        (metaArities (language := language) (lawRule law) compiled.spec)
        compiled.left.term compiled.right.term] := by
  obtain ⟨checkedGuards, checkedGuardRead, _, carriers⟩ := stable
  obtain ⟨checkedCompiled, checkedRead, _, _, semantic⟩ := carriers type candidate
  have compiledSame : checkedCompiled = compiled := Option.some.inj (checkedRead.symm.trans sourceRead)
  subst checkedCompiled
  have guardsSame : checkedGuards = guards := Option.some.inj
    (((guards?_exact provider law.premises checkedGuards).mpr checkedGuardRead).symm.trans
      ((guards?_exact provider law.premises guards).mpr guardRead))
  subst checkedGuards
  exact singleton_satisfies_contextually constructors _ (semantic active)

inductive SourceInstance (language : LanguageDef) (provider : ProviderSnapshot) (laws : List Law) :
    {bound : List TypeExpr} → {type : TypeExpr} →
      Term (signatureOf language) bound type → Term (signatureOf language) bound type → Prop where
  | source (law : Law) (original : law ∈ laws) (type : TypeExpr)
      (candidate : type ∈ carrierCandidates language law)
      (compiled : CompiledLaw language law type)
      (sourceRead : compileLaw? language law type = some compiled)
      (guards : List Witness) (guardRead : GuardedBy provider 0 law.premises guards)
      (active : enabled guards = true)
      {captured bound : List TypeExpr}
      (body : ContextualAssignment (signatureOf language)
        (metaArities (language := language) (lawRule law) compiled.spec) captured)
      (ambient : Sub (signatureOf language) captured bound)
      (ordinary : Sub (signatureOf language) [] bound) :
      SourceInstance language provider laws
        (ContextualAssignment.instantiate body ambient ordinary compiled.left.term)
        (ContextualAssignment.instantiate body ambient ordinary compiled.right.term)

theorem source_instance_sound
    {language : LanguageDef} {provider : ProviderSnapshot} {laws : List Law}
    (constructors : Constructors language)
    (checked : ∀ law ∈ laws, BindingSemanticStable language provider constructors law)
    {bound : List TypeExpr} {type : TypeExpr}
    {first second : Term (signatureOf language) bound type}
    (receipt : SourceInstance language provider laws first second) :
    interpret (Valuation.algebra constructors) first =
      interpret (Valuation.algebra constructors) second := by
  cases receipt with
  | source law original type candidate compiled sourceRead guards guardRead active body ambient ordinary =>
      exact (checked_carrier_contextual_satisfaction constructors (checked law original)
        candidate compiled sourceRead guards guardRead active).interpret_instance
          ⟨0, by simp⟩ body ambient ordinary

mutual

inductive Consequence (language : LanguageDef) (provider : ProviderSnapshot) (laws : List Law) :
    {bound : List TypeExpr} → {type : TypeExpr} →
      Term (signatureOf language) bound type → Term (signatureOf language) bound type → Prop where
  | source {bound : List TypeExpr} {type : TypeExpr}
      {first second : Term (signatureOf language) bound type} :
      SourceInstance language provider laws first second → Consequence language provider laws first second
  | reflexive {bound : List TypeExpr} {type : TypeExpr}
      (term : Term (signatureOf language) bound type) : Consequence language provider laws term term
  | symmetric {bound : List TypeExpr} {type : TypeExpr}
      {first second : Term (signatureOf language) bound type} :
      Consequence language provider laws first second → Consequence language provider laws second first
  | transitive {bound : List TypeExpr} {type : TypeExpr}
      {first middle last : Term (signatureOf language) bound type} :
      Consequence language provider laws first middle → Consequence language provider laws middle last →
        Consequence language provider laws first last
  | constructor {bound : List TypeExpr} {type : TypeExpr} (op : (signatureOf language).Op type)
      {first second : Args (signatureOf language) ((signatureOf language).arity op) bound} :
      ArgumentConsequence language provider laws first second →
        Consequence language provider laws (.op op first) (.op op second)
  | substituted {bound target : List TypeExpr} {type : TypeExpr}
      (environment : Sub (signatureOf language) bound target)
      {first second : Term (signatureOf language) bound type} :
      Consequence language provider laws first second →
        Consequence language provider laws (bind environment first) (bind environment second)

inductive ArgumentConsequence (language : LanguageDef) (provider : ProviderSnapshot) (laws : List Law) :
    {arity : List (List TypeExpr × TypeExpr)} → {bound : List TypeExpr} →
      Args (signatureOf language) arity bound → Args (signatureOf language) arity bound → Prop where
  | nil {bound : List TypeExpr} : ArgumentConsequence language provider laws (Args.nil (Γ := bound)) .nil
  | cons {binders : List TypeExpr} {type : TypeExpr} {arity : List (List TypeExpr × TypeExpr)}
      {bound : List TypeExpr} {head head' : Term (signatureOf language) (binders ++ bound) type}
      {tail tail' : Args (signatureOf language) arity bound} :
      Consequence language provider laws head head' → ArgumentConsequence language provider laws tail tail' →
        ArgumentConsequence language provider laws (.cons head tail) (.cons head' tail')

end

mutual

theorem consequences_sound
    {language : LanguageDef} {provider : ProviderSnapshot} {laws : List Law}
    (constructors : Constructors language)
    (checked : ∀ law ∈ laws, BindingSemanticStable language provider constructors law) :
    ∀ {bound : List TypeExpr} {type : TypeExpr}
      {first second : Term (signatureOf language) bound type},
      Consequence language provider laws first second →
        interpret (Valuation.algebra constructors) first = interpret (Valuation.algebra constructors) second
  | _, _, _, _, .source receipt => source_instance_sound constructors checked receipt
  | _, _, _, _, .reflexive _ => rfl
  | _, _, _, _, .symmetric earlier => (consequences_sound constructors checked earlier).symm
  | _, _, _, _, .transitive first last =>
      (consequences_sound constructors checked first).trans (consequences_sound constructors checked last)
  | _, _, _, _, .constructor op arguments => by
      change (Valuation.algebra constructors).operation op _ = (Valuation.algebra constructors).operation op _
      exact congrArg ((Valuation.algebra constructors).operation op)
        (argument_consequences_sound constructors checked arguments)
  | _, _, _, _, .substituted environment earlier => by
      rw [interpret_bind, interpret_bind]
      exact congrArg ((Valuation.algebra constructors).substitution.substitute _)
        (consequences_sound constructors checked earlier)

theorem argument_consequences_sound
    {language : LanguageDef} {provider : ProviderSnapshot} {laws : List Law}
    (constructors : Constructors language)
    (checked : ∀ law ∈ laws, BindingSemanticStable language provider constructors law) :
    ∀ {arity : List (List TypeExpr × TypeExpr)} {bound : List TypeExpr}
      {first second : Args (signatureOf language) arity bound},
      ArgumentConsequence language provider laws first second →
        interpretArgs (Valuation.algebra constructors) first =
          interpretArgs (Valuation.algebra constructors) second
  | _, _, _, _, .nil => rfl
  | _, _, _, _, .cons head tail => congrArg₂ FamilyArgs.cons
      (consequences_sound constructors checked head) (argument_consequences_sound constructors checked tail)

end

theorem equivalence_closure_sound
    {language : LanguageDef} {provider : ProviderSnapshot} {laws : List Law}
    (constructors : Constructors language)
    (checked : ∀ law ∈ laws, BindingSemanticStable language provider constructors law)
    {bound : List TypeExpr} {type : TypeExpr}
    {first second : Term (signatureOf language) bound type}
    (equivalent : Relation.EqvGen (SourceInstance language provider laws) first second) :
    interpret (Valuation.algebra constructors) first = interpret (Valuation.algebra constructors) second := by
  induction equivalent with
  | rel first second source => exact source_instance_sound constructors checked source
  | refl term => rfl
  | symm first second _ previous => exact previous.symm
  | trans first middle last _ _ firstEqual lastEqual => exact firstEqual.trans lastEqual

theorem Consequence.renamed
    {language : LanguageDef} {provider : ProviderSnapshot} {laws : List Law}
    {bound target : List TypeExpr} {type : TypeExpr}
    {first second : Term (signatureOf language) bound type}
    (relation : Consequence language provider laws first second)
    (renameVariables : Ren (signatureOf language) bound target) :
    Consequence language provider laws (rename renameVariables first) (rename renameVariables second) := by
  rw [← bind_var_eq_rename renameVariables first, ← bind_var_eq_rename renameVariables second]
  exact .substituted (fun sort position => .var (renameVariables sort position)) relation

end Mettapedia.OSLF.NativeTypes.Generation.BindingStability

namespace Mettapedia.OSLF.NativeTypes.Generation

open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.Binding.BindingCloneFoldSubstitution
open Mettapedia.GSLT.LanguageDef.BindingSyntax
open Mettapedia.OSLF.NativeTypes.SortProfiles.Laws.FiniteBinding Mettapedia.OSLF.NativeTypes.Generation.BindingCenter Mettapedia.OSLF.NativeTypes.Generation.BindingStability

theorem generated_binding_consequences_sound
    (generated : Generated) (constructors : Constructors generated.snapshot.language)
    (accepted : generated.bindingLawAdmission? constructors = some true)
    {bound : List Mettapedia.OSLF.MeTTaIL.Syntax.TypeExpr}
    {type : Mettapedia.OSLF.MeTTaIL.Syntax.TypeExpr}
    {first second : Term (signatureOf generated.snapshot.language) bound type}
    (relation : Consequence generated.snapshot.language generated.snapshot.provider
      (selectedEquationLaws generated.snapshot.language generated.languageFragment.operational) first second) :
    interpret (Valuation.algebra constructors) first = interpret (Valuation.algebra constructors) second :=
  consequences_sound constructors ((generated_binding_equations_exact generated constructors).mp accepted) relation

theorem generated_binding_consequence_readouts
    (generated : Generated) (constructors : Constructors generated.snapshot.language)
    (accepted : generated.bindingLawAdmission? constructors = some true)
    {bound : List Mettapedia.OSLF.MeTTaIL.Syntax.TypeExpr}
    {type : Mettapedia.OSLF.MeTTaIL.Syntax.TypeExpr}
    {first second : Term (signatureOf generated.snapshot.language) bound type}
    (relation : Consequence generated.snapshot.language generated.snapshot.provider
      (selectedEquationLaws generated.snapshot.language generated.languageFragment.operational) first second)
    (assignment : (sort : Mettapedia.OSLF.MeTTaIL.Syntax.TypeExpr) → Var bound sort → Value sort) :
    Valuation.read constructors (Valuation.interpret constructors first) assignment =
      Valuation.read constructors (Valuation.interpret constructors second) assignment :=
  congrArg (fun value => Valuation.read constructors value assignment)
    (generated_binding_consequences_sound generated constructors accepted relation)

theorem generated_binding_substitution_readout
    (generated : Generated) (constructors : Constructors generated.snapshot.language)
    (accepted : generated.bindingLawAdmission? constructors = some true)
    {bound target : List Mettapedia.OSLF.MeTTaIL.Syntax.TypeExpr}
    {type : Mettapedia.OSLF.MeTTaIL.Syntax.TypeExpr}
    {first second : Term (signatureOf generated.snapshot.language) bound type}
    (relation : Consequence generated.snapshot.language generated.snapshot.provider
      (selectedEquationLaws generated.snapshot.language generated.languageFragment.operational) first second)
    (environment : Sub (signatureOf generated.snapshot.language) bound target)
    (assignment : (sort : Mettapedia.OSLF.MeTTaIL.Syntax.TypeExpr) → Var target sort → Value sort) :
    Valuation.read constructors (Valuation.interpret constructors (bind environment first)) assignment =
      Valuation.read constructors (Valuation.interpret constructors second)
        (fun sort position => Valuation.read constructors
          (Valuation.interpret constructors (environment sort position)) assignment) := by
  rw [Valuation.read_bind]
  exact generated_binding_consequence_readouts generated constructors accepted relation _

end Mettapedia.OSLF.NativeTypes.Generation
