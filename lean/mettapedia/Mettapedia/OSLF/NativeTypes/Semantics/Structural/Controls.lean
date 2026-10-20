import Mettapedia.OSLF.NativeTypes.Semantics.Structural.Propositional
import Mettapedia.OSLF.NativeTypes.Semantics.Sorted.LambdaControls
import Mettapedia.OSLF.NativeTypes.Generation.PropositionalCodeControls
import Mettapedia.OSLF.NativeTypes.Modal.ContextControls

open Mettapedia.OSLF.Framework

/-!
# Native structural and propositional output controls

Actual lambda representation is distinguished from a bound variable of its
arrow carrier. Two nonempty interpreted sort subobjects control relative top
and complement. A nonempty equation identifies different constructor roots;
the resulting native image contains that whole class and excludes another.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Semantics.Structural.Controls

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.NativeTypes.Generation (Generated structuralDeclaration StructuralInputs)
open Mettapedia.OSLF.NativeTypes.Modal.Rules (TypeCode)
open Mettapedia.OSLF.NativeTypes.Semantics.Sorted.NativeCodes (Model)
open Mettapedia.OSLF.NativeTypes.Semantics.Sorted.NativeIntroduction (EquationsInterpreted)
open Mettapedia.OSLF.NativeTypes.Semantics.Structural
open GSLTTypeSynthesis
open ModalHypercube (HSort)

namespace Lambda

open Mettapedia.OSLF.NativeTypes.Instances.Lambda.GeneratorConsumer (generated term)
open Mettapedia.OSLF.NativeTypes.Semantics.Sorted.LambdaControls (model native_constructor_model native_equation_model)

def index : Fin generated.snapshot.language.terms.length := ⟨1, by decide +kernel⟩
def binder : Pattern := .lambda none (.bvar 0)
def program : Pattern := .apply "Lam" [binder]

def inputs (bound : List TypeExpr) : StructuralInputs generated bound index := fun position =>
  {meaning := fun native => HasType generated.snapshot.language generated.snapshot.free bound native
      (structuralDeclaration generated index).params[position].typeExpr
   bounded := fun _ typed => typed}

def value : Mettapedia.OSLF.NativeTypes.Structural.ConstructorValue generated.snapshot.language generated.snapshot.free []
    (structuralDeclaration generated index) :=
  .ordinary [binder] (by rintro ⟨name, kind, elementType, shape⟩; cases shape)
    (.cons trivial rfl (.lambda (.bvar rfl)) .nil)

theorem interpreted_arguments : ∀ position,
    (Mettapedia.OSLF.NativeTypes.Semantics.Sorted.NativeCodes.restrictCode (model []) (inputs [] position)).meaning
      (value.arguments[position.val]'(by rw [value.arguments_length]; exact position.isLt)) := by
  intro position
  fin_cases position
  exact ⟨⟨.lambda (.bvar rfl), rfl⟩, .lambda (.bvar rfl)⟩

def output : Family model [] index (inputs []) program :=
  introduce native_constructor_model index (inputs []) value interpreted_arguments

theorem binder_native_membership : predicate model [] index (inputs []) program :=
  (family_support model [] index (inputs []) program).mp ⟨output⟩

theorem binder_generated_native_readout :
    (Mettapedia.OSLF.NativeTypes.Semantics.Sorted.NativeCodes.structuralCode (model []) index (inputs [])).meaning program ∧
      (gsltOSLF (theory generated [] term)).satisfies (S := ()) program (nativeType model [] index (inputs [])).pred := by
  exact ⟨(generated_native_comparison model native_equation_model [] index (inputs []) program).mpr
    binder_native_membership, binder_native_membership⟩

def emitted : (sort : HSort) × TypeCode generated.plan []
    (.base (structuralDeclaration generated index).category) sort :=
  ⟨Mettapedia.OSLF.NativeTypes.Generation.structuralOutputSort generated index,
    Mettapedia.OSLF.NativeTypes.Generation.structuralCode generated [] index
      (Mettapedia.OSLF.NativeTypes.Semantics.Sorted.NativeCodes.restrictStructuralInputs (model []) (inputs []))⟩

theorem actual_structural_output_is_emitted : generated.structuralFormer? [] index
    (Mettapedia.OSLF.NativeTypes.Semantics.Sorted.NativeCodes.restrictStructuralInputs (model []) (inputs [])) = some emitted := by
  unfold Mettapedia.OSLF.NativeTypes.Generation.Generated.structuralFormer?
  rw [if_pos ⟨Mettapedia.OSLF.NativeTypes.Generation.ModalCheckingControls.actual_equation_admission, by decide +kernel⟩]
  rfl

theorem emitted_output_has_native_family (native : Pattern) :
    (Mettapedia.OSLF.NativeTypes.Semantics.Sorted.NativeCodes.restrictCode (model []) emitted.2).meaning native ↔
      Nonempty (Family model [] index (inputs []) native) :=
  compiled_structural_family_comparison model native_equation_model [] index (inputs [])
    actual_structural_output_is_emitted native

/-- The rejected argument has the right arrow carrier. Its representation is
still a variable, whereas the authored Lam parameter requires abstraction. -/
theorem arrow_value_is_not_an_abstraction :
    HasType generated.snapshot.language generated.snapshot.free [.arrow term term] (.bvar 0) (.arrow term term) ∧
      ¬ predicate model [.arrow term term] index (inputs [.arrow term term]) (.apply "Lam" [.bvar 0]) := by
  constructor
  · exact .bvar rfl
  · intro inhabited
    have typed := native_carrier_bounded native_equation_model inhabited
    have accepted := checkHasType_complete_of_object typed (by decide +kernel)
    have rejected : checkHasType generated.snapshot.language generated.snapshot.free [.arrow term term]
        (.apply "Lam" [.bvar 0]) (.base (structuralDeclaration generated index).category) = false := by
      decide +kernel
    rw [rejected] at accepted
    cases accepted

theorem native_output_retains_actual_lambda : output.val.value.arguments = [binder] := rfl

end Lambda

namespace RelativeSorts

open Mettapedia.OSLF.NativeTypes.SortProfiles.Source.AdmissionControls (generated carrier first second)
open Mettapedia.OSLF.NativeTypes.Generation.PropositionalCodeControls (leaves)
open Mettapedia.OSLF.NativeTypes.Semantics.Structural.Propositional

def model : Model generated := fun bound =>
  {sortDomain := fun type sort native =>
      HasType generated.snapshot.language generated.snapshot.free bound native type ∧
        native = match sort with | .star => first | .box => second
   carrierBounded := fun _ _ _ inhabited => inhabited.1}

theorem equations_interpreted : EquationsInterpreted model := by
  intro bound type sort native receipt complete
  have empty : generated.plan.equations = [] := by cbv
  have impossible := complete.job.1
  rw [empty] at impossible
  exact False.elim (List.not_mem_nil impossible)

theorem leaf_equations_interpreted : LeafEquationsInterpreted [] leaves := by
  intro index native receipt complete
  have empty : generated.plan.equations = [] := by cbv
  have impossible := complete.job.1
  rw [empty] at impossible
  exact False.elim (List.not_mem_nil impossible)

theorem both_native_tops_are_nonempty :
    denotation model equations_interpreted [] leaves carrier .star .top first ∧
      denotation model equations_interpreted [] leaves carrier .box .top second := by
  constructor
  · exact (denotation_comparison equations_interpreted leaf_equations_interpreted (.top rfl) first).mpr
      ⟨Mettapedia.OSLF.NativeTypes.Generation.PropositionalCodeControls.both_sort_subobjects_nonempty.1, trivial⟩
  · exact (denotation_comparison equations_interpreted leaf_equations_interpreted (.top rfl) second).mpr
      ⟨Mettapedia.OSLF.NativeTypes.Generation.PropositionalCodeControls.both_sort_subobjects_nonempty.2, trivial⟩

theorem native_sort_domains_remain_separate :
    ¬ denotation model equations_interpreted [] leaves carrier .star .top second ∧
      ¬ denotation model equations_interpreted [] leaves carrier .box .top first := by
  constructor
  · intro inhabited
    exact Mettapedia.OSLF.NativeTypes.Generation.PropositionalCodeControls.sort_subobjects_separate_actual_terms.1 inhabited
  · intro inhabited
    exact Mettapedia.OSLF.NativeTypes.Generation.PropositionalCodeControls.sort_subobjects_separate_actual_terms.2 inhabited

theorem complement_preserves_the_requested_sort :
    ¬ denotation model equations_interpreted [] leaves carrier .star (.negation (.leaf 0)) second ∧
      Mettapedia.OSLF.NativeTypes.Generation.PropositionalCodes.meaning generated [] leaves carrier (.negation (.leaf 0)) second := by
  constructor
  · intro inhabited
    exact Mettapedia.OSLF.NativeTypes.Generation.PropositionalCodeControls.sort_subobjects_separate_actual_terms.1 inhabited.1
  · exact Mettapedia.OSLF.NativeTypes.Generation.PropositionalCodeControls.carrier_only_complement_would_admit_box_term

theorem wrong_universe_is_still_refused :
    compile model [] leaves carrier .box (.leaf 0) = .error .incompatibleCarrierOrUniverse := by
  have refused := Mettapedia.OSLF.NativeTypes.Generation.PropositionalCodeControls.wrong_universe_is_formation_refusal
  simp only [compile, Mettapedia.OSLF.NativeTypes.Semantics.Sorted.PropositionalCodes.compile, refused, Except.map]

theorem native_bottom_has_no_family (native : Pattern) :
    ¬ Nonempty (Mettapedia.OSLF.NativeTypes.Semantics.Structural.Propositional.Family model [] leaves carrier .star .bottom native) := by
  rintro ⟨falsehood⟩
  cases falsehood

end RelativeSorts

namespace Equational

open GeneralExecutionAdmission
open Mettapedia.OSLF.NativeTypes.Modal.Counterexamples (carrier alpha beta done oriented)
open GSLTTypeSynthesis

def fragment : Mettapedia.OSLF.NativeTypes.Generation.LanguageFragment :=
  {operational := Mettapedia.OSLF.NativeTypes.Modal.Counterexamples.permissions}
def chosen := Mettapedia.OSLF.NativeTypes.Generation.selectedSnapshot Mettapedia.OSLF.NativeTypes.Modal.ContextControls.snapshot fragment
def vertex : Mettapedia.OSLF.NativeTypes.SortProfiles.Derived.CubeVertex chosen.language := (fun _ => .star, fun _ => .star)
def generated := Mettapedia.OSLF.NativeTypes.Generation.generate Mettapedia.OSLF.NativeTypes.Modal.ContextControls.snapshot fragment
  Mettapedia.OSLF.NativeTypes.Structural.heytingFragment vertex

theorem actual_plan : generated.plan = Mettapedia.OSLF.NativeTypes.Modal.ContextControls.runtimePlan := by
  have selected : chosen = Mettapedia.OSLF.NativeTypes.Modal.ContextControls.snapshot := by
    change ({Mettapedia.OSLF.NativeTypes.Modal.ContextControls.snapshot with
      language := Mettapedia.OSLF.NativeTypes.Generation.selectedLanguage Mettapedia.OSLF.NativeTypes.Modal.ContextControls.language fragment} : Snapshot) = _
    rw [show fragment = {operational := Mettapedia.OSLF.NativeTypes.Modal.Counterexamples.permissions} from rfl,
      Mettapedia.OSLF.NativeTypes.Generation.unrestricted_signature]
    rfl
  change compile chosen Mettapedia.OSLF.NativeTypes.Modal.Counterexamples.permissions = _
  rw [selected]
  exact Mettapedia.OSLF.NativeTypes.Modal.ContextControls.actual_plan

theorem nonempty_equation_source : generated.snapshot.language.equations ≠ [] := by
  decide +kernel

theorem equation_completion : GeneralEquationJobs.Completion generated.plan [] carrier alpha
    Mettapedia.OSLF.NativeTypes.Modal.ContextControls.equationReceipt := by
  rw [actual_plan]
  exact Mettapedia.OSLF.NativeTypes.Modal.ContextControls.equation_completed

theorem alpha_beta_equivalent : Relation.EqvGen
    (GeneralOccurrenceSemantics.Equation generated.plan [] carrier) alpha beta :=
  .rel _ _ ⟨Mettapedia.OSLF.NativeTypes.Modal.ContextControls.equationReceipt, equation_completion, rfl⟩

private theorem keeps_done {first second : Pattern}
    (related : Relation.EqvGen (GeneralOccurrenceSemantics.Equation generated.plan [] carrier) first second) :
    first = done ↔ second = done := by
  exact Mettapedia.OSLF.NativeTypes.Modal.Counterexamples.equation_keeps_nullary generated.plan
    (by rw [actual_plan]; rfl) "Done" (by decide) (by decide) related

theorem alpha_not_done_class : ¬ Relation.EqvGen
    (GeneralOccurrenceSemantics.Equation generated.plan [] carrier) alpha done := by
  intro related
  exact (by decide : alpha ≠ done) ((keeps_done related).mpr rfl)

def center : HSort → Pattern
  | .star => alpha
  | .box => done

def model : Model generated := fun bound =>
  {sortDomain := fun type sort native =>
      HasType generated.snapshot.language generated.snapshot.free bound native type ∧
        Relation.EqvGen (GeneralOccurrenceSemantics.Equation generated.plan bound type) native (center sort)
   carrierBounded := fun _ _ _ inhabited => inhabited.1}

theorem equations_interpreted : EquationsInterpreted model := by
  intro bound type sort source receipt complete
  have related : Relation.EqvGen
      (GeneralOccurrenceSemantics.Equation generated.plan bound type) source receipt.target :=
    .rel _ _ ⟨receipt, complete, rfl⟩
  apply and_congr (Mettapedia.OSLF.NativeTypes.Semantics.Sorted.NativeTransport.native_conversion_carrier related)
  exact ⟨fun holds => .trans _ _ _ (.symm _ _ related) holds,
    fun holds => .trans _ _ _ related holds⟩

theorem alpha_typed : HasType generated.snapshot.language generated.snapshot.free [] alpha carrier := by
  apply checkHasType_sound
  decide +kernel

theorem beta_typed : HasType generated.snapshot.language generated.snapshot.free [] beta carrier := by
  apply checkHasType_sound
  decide +kernel

theorem done_typed : HasType generated.snapshot.language generated.snapshot.free [] done carrier := by
  apply checkHasType_sound
  decide +kernel

theorem both_sort_subobjects_nonempty :
    (model []).sortDomain carrier .star alpha ∧ (model []).sortDomain carrier .box done :=
  ⟨⟨alpha_typed, .refl _⟩, ⟨done_typed, .refl _⟩⟩

def index : Fin generated.snapshot.language.terms.length := ⟨1, by decide +kernel⟩
def inputs : StructuralInputs generated [] index := fun position => Fin.elim0 position

def value : Mettapedia.OSLF.NativeTypes.Structural.ConstructorValue generated.snapshot.language generated.snapshot.free []
    (structuralDeclaration generated index) :=
  .ordinary [] (by rintro ⟨name, kind, elementType, shape⟩; cases shape) .nil

def introduction : Introduction model [] index inputs where
  value := value
  output := ⟨beta_typed, .symm _ _ alpha_beta_equivalent⟩
  arguments position := Fin.elim0 position

def output : Family model [] index inputs alpha :=
  ⟨introduction, Quotient.sound alpha_beta_equivalent⟩

/-- Alpha is in the native Beta constructor image through the actual authored
equation, although the authored representatives have different roots. -/
theorem equation_changes_native_constructor_root :
    predicate model [] index inputs alpha ∧
      ¬ ∃ arguments, alpha = .apply (structuralDeclaration generated index).label arguments := by
  constructor
  · exact (family_support model [] index inputs alpha).mp ⟨output⟩
  · rintro ⟨arguments, equal⟩
    have label : (structuralDeclaration generated index).label = "Beta" := by decide +kernel
    rw [label] at equal
    exact (by decide : ("Alpha" : String) ≠ "Beta") (Pattern.apply.inj equal).1

theorem generated_structural_class_contains_alpha :
    (Mettapedia.OSLF.NativeTypes.Semantics.Sorted.NativeCodes.structuralCode (model []) index inputs).meaning alpha :=
  (generated_native_comparison model equations_interpreted [] index inputs alpha).mpr
    equation_changes_native_constructor_root.1

theorem native_constructor_excludes_other_equation_class : ¬ predicate model [] index inputs done := by
  intro inhabited
  have sorted := native_bounded equations_interpreted inhabited
  exact alpha_not_done_class (.symm _ _ sorted.2)

theorem output_retains_beta_introduction : output.val.value.pattern = beta := rfl

def classLeaf : TypeCode generated.plan [] carrier .star where
  meaning native := Relation.EqvGen (GeneralOccurrenceSemantics.Equation generated.plan [] carrier) native alpha
  bounded _ related :=
    (Mettapedia.OSLF.NativeTypes.Semantics.Sorted.NativeTransport.native_conversion_carrier related).mpr alpha_typed

def leaves : Mettapedia.OSLF.NativeTypes.SortProfiles.Source.LeafCodes generated [] := fun _ => ⟨carrier, .star, classLeaf⟩

theorem leaf_equations_interpreted :
    Mettapedia.OSLF.NativeTypes.Semantics.Structural.Propositional.LeafEquationsInterpreted [] leaves := by
  intro index source receipt complete
  have related : Relation.EqvGen
      (GeneralOccurrenceSemantics.Equation generated.plan [] carrier) source receipt.target :=
    .rel _ _ ⟨receipt, complete, rfl⟩
  exact ⟨fun holds => .trans _ _ _ (.symm _ _ related) holds,
    fun holds => .trans _ _ _ related holds⟩

def expression : Mettapedia.OSLF.NativeTypes.Generation.PropositionalCodes.Expression := .conjunction (.leaf 0) (.negation .bottom)

theorem expression_formed : Mettapedia.OSLF.NativeTypes.Generation.PropositionalCodes.Formed generated.logicFragment
    (Mettapedia.OSLF.NativeTypes.SortProfiles.Source.leafCarriers leaves) (Mettapedia.OSLF.NativeTypes.SortProfiles.Source.leafSorts leaves) carrier .star expression :=
  .conjunction rfl (.leaf 0 rfl rfl) (.negation rfl (.bottom rfl))

theorem nonempty_equations_propositional_compile :
    ∃ nativeOutput : Mettapedia.OSLF.NativeTypes.Semantics.Structural.Propositional.Output model [] leaves carrier .star,
      Mettapedia.OSLF.NativeTypes.Semantics.Structural.Propositional.compile model [] leaves carrier .star expression = .ok nativeOutput ∧
      nativeOutput.predicate equations_interpreted alpha ∧
      nativeOutput.predicate equations_interpreted beta ∧
      ¬ nativeOutput.predicate equations_interpreted done := by
  obtain ⟨nativeOutput, checked, _⟩ :=
    Mettapedia.OSLF.NativeTypes.Semantics.Structural.Propositional.compilation_complete model [] leaves carrier .star expression expression_formed
  have readout := Mettapedia.OSLF.NativeTypes.Semantics.Structural.Propositional.compiled_native_comparison
    equations_interpreted leaf_equations_interpreted checked
  refine ⟨nativeOutput, checked, (readout alpha).mpr ?_, (readout beta).mpr ?_, ?_⟩
  · exact ⟨⟨alpha_typed, .refl _⟩, .refl _, fun falsehood => falsehood⟩
  · exact ⟨⟨beta_typed, .symm _ _ alpha_beta_equivalent⟩,
      .symm _ _ alpha_beta_equivalent, fun falsehood => falsehood⟩
  · intro inhabited
    exact alpha_not_done_class (.symm _ _ ((readout done).mp inhabited).1.2)

def singletonLeaf : TypeCode generated.plan [] carrier .star where
  meaning native := native = alpha
  bounded _ equal := equal.symm ▸ alpha_typed

def singletonLeaves : Mettapedia.OSLF.NativeTypes.SortProfiles.Source.LeafCodes generated [] := fun _ => ⟨carrier, .star, singletonLeaf⟩

/-- An authored singleton that distinguishes Alpha from Beta cannot supply
the primitive leaf-interpretation law required by the native compiler. -/
theorem equation_distinguishing_leaf_is_not_interpreted :
    ¬ Mettapedia.OSLF.NativeTypes.Semantics.Structural.Propositional.LeafEquationsInterpreted [] singletonLeaves := by
  intro interpreted
  have impossible : beta = alpha := (interpreted 0 alpha
    Mettapedia.OSLF.NativeTypes.Modal.ContextControls.equationReceipt equation_completion).mp rfl
  exact (by decide : beta ≠ alpha) impossible

end Equational

#print axioms Lambda.binder_native_membership
#print axioms Lambda.arrow_value_is_not_an_abstraction
#print axioms Lambda.emitted_output_has_native_family
#print axioms RelativeSorts.both_native_tops_are_nonempty
#print axioms RelativeSorts.complement_preserves_the_requested_sort
#print axioms Equational.equation_changes_native_constructor_root
#print axioms Equational.native_constructor_excludes_other_equation_class
#print axioms Equational.nonempty_equations_propositional_compile
#print axioms Equational.equation_distinguishing_leaf_is_not_interpreted

end Mettapedia.OSLF.NativeTypes.Semantics.Structural.Controls
