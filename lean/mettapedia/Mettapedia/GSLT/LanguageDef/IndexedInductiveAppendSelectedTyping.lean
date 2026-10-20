import Mettapedia.GSLT.LanguageDef.IndexedInductiveAppendTyping
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeNaturalVectorComputationProfiles

/-!
# Represented append arguments under the selected checking policy

The natural-only policy checks the actual constructors, represented arguments
and canonical result at the same dependent type as the emitted function.
Addition conversion uses only the two permitted natural rows. Execution still
uses the original operational calculus, which also has vector computation.
These endpoint judgments do not assert preservation of every intermediate
contextual reduction.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.IndexedInductive.Guest.AppendTyping.Selected

open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open NativeNaturalVectorFamilies Declaration.IndexedFamily SchemaElaboration
open IndexedInductiveNatVec VectorMeaning AppendMeaning
open TypedEquality.Normalization

abbrev rules := Programs.ComputationProfiles.rules Programs.ComputationProfiles.naturalOnly
abbrev Typed {scope : Nat} (context : Tower.Ctx scope) (term type : Tower.Tm scope) :=
  FormationSensitive.Typing rules context term type

local instance : DecidableRel rules.headTyping :=
  fun h u => inferInstanceAs (Decidable (Tower.rules.headTyping h u))
local instance : DecidablePred rules.isUniverse :=
  fun h => inferInstanceAs (Decidable (Tower.rules.isUniverse h))
local instance : ∀ u v w, Decidable (rules.join u v w) :=
  fun u v w => inferInstanceAs (Decidable (Tower.rules.join u v w))
local instance : DecidableRel rules.cumulative :=
  fun h u => inferInstanceAs (Decidable (Tower.rules.cumulative h u))
local instance : DecidableRel rules.headEq :=
  fun h u => inferInstanceAs (Decidable (Tower.rules.headEq h u))

def submission (index : Fin 6) :=
  FormationSensitiveElaboration.elaborate rules
    (Programs.ComputationProfiles.decoder Programs.ComputationProfiles.naturalOnly)
    Programs.choices 24 (.nil : Tower.Ctx 0)
    (.const (constructor index).1) (constructor index).2

theorem constructors_checked (index : Fin 6) : (submission index).isSome = true := by
  fin_cases index <;> decide +kernel

theorem constructors : ConstructorFormation rules where
  judgments index := by
    obtain ⟨evidence, produced⟩ := Option.isSome_iff_exists.mp (constructors_checked index)
    exact FormationSensitiveElaboration.elaborate_sound rules
      (Programs.ComputationProfiles.decoder Programs.ComputationProfiles.naturalOnly) Programs.choices
      24 .nil _ _ evidence produced

/-- The inclusion is justified by the selected schemas' original iota
evidence. It does not grant the converse restriction of arbitrary proofs. -/
theorem include_reference {scope : Nat} {context : Tower.Ctx scope}
    {term type : Tower.Tm scope} (typed : Typed context term type) :
    AppendTyping.Typed context term type := by
  change FormationSensitive.Typing (Declaration.extendRules Tower.rules Programs.signature) context term type
  simpa only [Ctx.mapHead_id, Tm.mapHead_id] using typed.mapHead
    (Declaration.extensionMorphism Tower.rules
      (Programs.ComputationProfiles.includes_original Programs.ComputationProfiles.naturalOnly))

/-- Arithmetic index conversion is computed solely with licensed Nat roots. -/
theorem add_numerals {scope : Nat} (first second : Nat) :
    Relation.ReflTransGen (StepCore rules.computation rules.headEq)
      (Programs.add (numeral (n := scope) first) (numeral second))
      (numeral (first + second)) := by
  let motive : Tower.Tm scope := .lam natTm
  let method : Tower.Tm scope := .lam (.lam (succApp (.var 0)))
  induction first with
  | zero =>
      rw [Nat.zero_add]
      apply Relation.ReflTransGen.single
      apply StepCore.root
      apply Declaration.RootStep.declared
      have evidence := SchemaTableConversionCode.Evidence.instantiate
        (table := NativeNaturalVectorFamilies.Checking.table) (enabled := Programs.ComputationProfiles.naturalOnly) ⟨0, by decide⟩ rfl
        (fun index : Fin 3 => Fin.cases method
          (Fin.cases (numeral second) (fun _ => motive)) index)
      exact ⟨evidence⟩
  | succ first ih =>
      have root : StepCore rules.computation rules.headEq
          (Programs.add (numeral (n := scope) (first + 1)) (numeral second))
          (.app (.app (.lam (.lam (succApp (.var 0)))) (numeral first))
            (Programs.add (numeral first) (numeral second))) := by
        apply StepCore.root
        apply Declaration.RootStep.declared
        have evidence := SchemaTableConversionCode.Evidence.instantiate
          (table := NativeNaturalVectorFamilies.Checking.table) (enabled := Programs.ComputationProfiles.naturalOnly) ⟨1, by decide⟩ rfl
          (fun index : Fin 4 => Fin.cases (numeral (n := scope) first)
            (Fin.cases method
              (Fin.cases (numeral second) (fun _ => motive))) index)
        exact ⟨evidence⟩
      refine Relation.ReflTransGen.head root ?_
      refine Relation.ReflTransGen.head (.congAppFun (.betaPi _ _)) ?_
      change Relation.ReflTransGen (StepCore rules.computation rules.headEq)
        (.app (.lam (succApp (.var 0))) (Programs.add (numeral first) (numeral second))) _
      refine Relation.ReflTransGen.head (.betaPi _ _) ?_
      change Relation.ReflTransGen (StepCore rules.computation rules.headEq)
        (succApp (Programs.add (numeral first) (numeral second))) (numeral (first.succ + second))
      rw [Nat.succ_add]
      exact ih.lift succApp (fun _ _ step => .congAppArg step)

theorem application_typed {A : Type} (element : Tower.Tm 0) (payload : A → Tower.Tm 0)
    (elementTyped : Typed .nil element (sortTm elementLevel))
    (payloadTyped : ∀ value, Typed .nil (payload value) element)
    {n m : Natural.Carrier} (left : Vectors.Vector A n) (right : Vectors.Vector A m) :
    Typed .nil (applyArgs Programs.appendTerm [element, quoteIndex n, quoteIndex m,
      encodeVector element payload left, encodeVector element payload right])
      (vecApp element (Programs.add (quoteIndex n) (quoteIndex m))) := by
  have application := ConstructorFormation.applyClosed_typing
    (constructors.assignment_typed element payload elementTyped payloadTyped left right)
    (type := Programs.appendResult) (function := Programs.appendTerm)
    (by simpa only [TelescopeAbstraction.liftClosed_zero, Programs.appendType] using
      Programs.ComputationProfiles.append_typed_naturalOnly.typing)
  have result : subst (assignment element payload left right) Programs.appendResult =
      vecApp element (Programs.add (quoteIndex n) (quoteIndex m)) := by
    rw [Programs.appendResult, subst_vecApp, Programs.Computation.add_substitute]
    rfl
  rw [result] at application
  exact application

theorem result_typed {A : Type} (element : Tower.Tm 0) (payload : A → Tower.Tm 0)
    (elementTyped : Typed .nil element (sortTm elementLevel))
    (payloadTyped : ∀ value, Typed .nil (payload value) element)
    {n m : Natural.Carrier} (left : Vectors.Vector A n) (right : Vectors.Vector A m) :
    Typed .nil (encodeVector element payload (Vectors.append left right))
      (vecApp element (Programs.add (quoteIndex n) (quoteIndex m))) := by
  have application := application_typed element payload elementTyped payloadTyped left right
  have universes : FormationSensitive.UniverseRegularity rules :=
    FormationSensitive.towerUniverseRegularity.includeSignature
      (Programs.ComputationProfiles.signature Programs.ComputationProfiles.naturalOnly)
  obtain ⟨level, universeWitness, formed⟩ :=
    application.regularity universes FormationSensitive.ContextFormation.nil
  have reduction : Relation.ReflTransGen (StepCore rules.computation rules.headEq)
      (Programs.add (quoteIndex n) (quoteIndex m)) (quoteIndex (Natural.add n m)) := by
    unfold quoteIndex
    rw [Natural.toNat_add]
    exact add_numerals _ _
  have lengthConversion : Conv rules.headEq
      (Programs.add (quoteIndex n) (quoteIndex m)) (quoteIndex (Natural.add n m))
      rules.computation := Relation.EqvGen.reflTransGen_le_eqvGen _ _ _ reduction
  exact FormationSensitive.Typing.conv
    (constructors.encode_typed element payload elementTyped payloadTyped (Vectors.append left right))
    formed universeWitness (Conv.congApp (.refl _) (.symm _ _ lengthConversion))

theorem compiled_contract (term : Tower.Tm 0)
    (compiled : AppendSource.proposedAppend = some term)
    {A : Type} (element : Tower.Tm 0) (payload : A → Tower.Tm 0)
    (elementTyped : Typed .nil element (sortTm elementLevel))
    (payloadTyped : ∀ value, Typed .nil (payload value) element)
    {n m : Natural.Carrier} (left : Vectors.Vector A n) (right : Vectors.Vector A m) :
    FormationSensitive.Judgment rules .nil
      (applyArgs term [element, quoteIndex n, quoteIndex m,
        encodeVector element payload left, encodeVector element payload right])
      (vecApp element (Programs.add (quoteIndex n) (quoteIndex m))) ∧
    ProgramExecutes (applyArgs term [element, quoteIndex n, quoteIndex m,
      encodeVector element payload left, encodeVector element payload right])
      (encodeVector element payload (Vectors.append left right)) ∧
    FormationSensitive.Judgment rules .nil
      (encodeVector element payload (Vectors.append left right))
      (vecApp element (Programs.add (quoteIndex n) (quoteIndex m))) := by
  rw [AppendSource.append_matches_reference] at compiled
  cases Option.some.inj compiled
  exact ⟨⟨.nil, application_typed element payload elementTyped payloadTyped left right⟩,
    appendTerm_program element payload left right,
    ⟨.nil, result_typed element payload elementTyped payloadTyped left right⟩⟩

#print axioms constructors
#print axioms add_numerals
#print axioms compiled_contract

end Mettapedia.GSLT.LanguageDef.IndexedInductive.Guest.AppendTyping.Selected
