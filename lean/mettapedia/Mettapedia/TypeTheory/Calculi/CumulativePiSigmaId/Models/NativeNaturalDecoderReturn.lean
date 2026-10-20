import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Models.NativeNaturalDomain
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Annotated.SchemaConstantInstantiation

/-!
# Returning the Nat/Vec permission family's opaque decoder extension

The fresh proposition and decoder map to their existing universe and identity
definitions. Original declared names, types and natural rule templates stay
fixed. Arguments containing the new constants change, and their required
evidence changes with them. The maintained constant-instance interface then
transports complete judgments. All four original rows satisfy the support
conditions, so the comparison is uniform in their permission selection.
Logical-relation adequacy, annotation coherence, proof-data roundtrips and
execution costs remain separate obligations.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeNaturalVectorFamilies
namespace Programs.Annotated.NaturalDomain.Decoder

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open TypedEquality TypedEquality.Annotated Declaration

def interpret : DeclName → CTm Tower.Head 0 := RigidExtension.inst smallUniverse

abbrev originalDeclarations := NativeNaturalVectorFamilies.declarations

theorem interpret_prop : interpret RigidExtension.prop = .head smallUniverse :=
  RigidExtension.inst_prop smallUniverse

theorem interpret_holds : interpret RigidExtension.holds = .lam (.head smallUniverse) (.var 0) :=
  RigidExtension.inst_holds smallUniverse

theorem original_names_fixed (enabled : ComputationProfiles.Selection)
    {name : DeclName} {type : CTm Tower.Head 0}
    (declared : (church enabled).constantType name = some type) :
    interpret name = .const name := by
  change (church ComputationProfiles.naturalOnly).constantType name = some type at declared
  have notProp : name ≠ RigidExtension.prop := by
    intro same
    subst name
    rw [fresh_prop] at declared
    cases declared
  have notHolds : name ≠ RigidExtension.holds := by
    intro same
    subst name
    rw [fresh_holds] at declared
    cases declared
  simp only [interpret, RigidExtension.inst, if_neg notProp, if_neg notHolds]

def declarationTypeFixedCheck : Bool :=
  originalDeclarations.all fun declaration =>
    let type := elabClosed (naiveDeclarations
      (ComputationProfiles.rules ComputationProfiles.naturalOnly).constantType)
        (RussellTarski.substLevelsTm levels declaration.2.type)
    decide (type.instConsts interpret = type)

theorem declarationTypeFixedCheck_true : declarationTypeFixedCheck = true := by decide +kernel

theorem original_types_fixed (enabled : ComputationProfiles.Selection)
    {name : DeclName} {type : CTm Tower.Head 0}
    (declared : (church enabled).constantType name = some type) :
    type.instConsts interpret = type := by
  change ((ComputationProfiles.rules ComputationProfiles.naturalOnly).constantType name).map
    (elabClosed (naiveDeclarations (ComputationProfiles.rules
      ComputationProfiles.naturalOnly).constantType)) = some type at declared
  obtain ⟨raw, known, rfl⟩ := Option.map_eq_some_iff.mp declared
  change (rawSignature.instantiateLevels levels iotaComputation).typeOf? name = some raw at known
  rw [Signature.typeOf_instantiateLevels] at known
  obtain ⟨sourceType, sourceKnown, rfl⟩ := Option.map_eq_some_iff.mp known
  unfold Signature.typeOf? at sourceKnown
  obtain ⟨entry, entryKnown, rfl⟩ := Option.map_eq_some_iff.mp sourceKnown
  change (Signature.ofList originalDeclarations).entries name = some entry at entryKnown
  have member := Signature.entries_ofList_mem originalDeclarations entryKnown
  have fixed := List.all_eq_true.mp declarationTypeFixedCheck_true (name, entry) member
  exact of_decide_eq_true fixed

theorem row_left_fixed (index : Row) :
    (liftTm (left index)).instConsts interpret = liftTm (left index) := by
  fin_cases index <;> decide +kernel

theorem row_right_fixed (index : Row) :
    (liftTm (right index)).instConsts interpret = liftTm (right index) := by
  fin_cases index <;> decide +kernel

theorem row_variable_type_fixed (index : Row) (argument : Fin (arity index)) :
    ((context index).lookup argument).instConsts interpret = (context index).lookup argument := by
  fin_cases index <;> fin_cases argument <;> decide +kernel

theorem schema_support (enabled : ComputationProfiles.Selection) : SchemaConstantsFixed
    (church enabled).constantType (family enabled) interpret where
  left := by
    rintro arity L R ⟨index, _, row⟩
    rw [table_row index] at row
    cases row
    rw [elaborated_left enabled index]
    exact row_left_fixed index
  right := by
    rintro arity L R ⟨index, _, row⟩
    rw [table_row index] at row
    cases row
    rw [elaborated_right enabled index]
    exact row_right_fixed index
  knowledge := by
    rintro arity L R ⟨index, _, row⟩ argument type known
    rw [table_row index] at row
    cases row
    rw [knowledge enabled index argument] at known
    cases known
    exact row_variable_type_fixed index argument
  equations := by
    rintro arity L R ⟨index, _, row⟩ equation member
    rw [table_row index] at row
    cases row
    rw [equations_empty enabled index] at member
    cases member

/-- Even arguments containing fresh decoder names may be expanded. Their
root evidence and all required premises follow the same substitution. -/
theorem original_interpretation (enabled : ComputationProfiles.Selection) :
    ConstInstance (church enabled) (church enabled) interpret :=
  ChurchRules.ofSchemas_constInstance _ _ interpret
    (original_names_fixed enabled) (original_types_fixed enabled) (schema_support enabled)

/-- The new decoder declarations expand to the same existing definitions
used by the maintained opaque-extension interpretation. -/
theorem decoder_type_expansion {name : DeclName} {type : CTm Tower.Head 0}
    (declared : declarations.constantType name = some type) :
    type.instConsts interpret = type.instConsts (RigidExtension.back smallUniverse) := by
  change RigidExtension.decls smallUniverse successorUniverse name = some type at declared
  unfold RigidExtension.decls at declared
  split at declared
  · cases declared
    rfl
  · split at declared
    · cases declared
      rfl
    · cases declared

/-- Full judgment transport back to the original enabled package, including
its original root evidence and every required premise. This is a theorem-level
interpretation, not a serialized certificate translator. -/
theorem return_interpretation (enabled : ComputationProfiles.Selection) :
    ConstInstance ((church enabled).sum declarations) (church enabled) interpret where
  headTyping := id
  isUniverse := id
  join := id
  cumulative := id
  headEq := id
  typed := by
    intro name type level declared typed isUniverse
    cases original : (church enabled).constantType name with
    | some originalType =>
        rw [show ((church enabled).sum declarations).constantType name = some originalType from
          sumDecls_left original] at declared
        cases declared
        exact (original_interpretation enabled).typed original typed isUniverse
    | none =>
        rw [show ((church enabled).sum declarations).constantType name = declarations.constantType name from
          sumDecls_right original] at declared
        rw [decoder_type_expansion declared]
        exact RigidExtension.typed_back (P := church enabled)
          (levelModel enabled) (.sort _) (.sort _) declared
  steps := fun root => root.elim (original_interpretation enabled).steps False.elim
  requires := by
    intro n left right premises _ required
    rcases required with original | impossible
    · exact (original_interpretation enabled).requires original.1 original.2
    · exact impossible.1.elim

theorem returned_judgment (enabled : ComputationProfiles.Selection) {statement : CStatement Tower.Head}
    (derived : CDerivable ((church enabled).sum declarations) statement) :
    CDerivable (church enabled) (statement.instConsts interpret) :=
  derived.instConsts (return_interpretation enabled)

/-- The extension is conservative for the precisely specified old fragment:
statements unchanged by replacing the two fresh decoder constants. Contexts,
displayed types and terms are all included in that condition. -/
theorem fixed_statement_iff (enabled : ComputationProfiles.Selection) {statement : CStatement Tower.Head}
    (fixed : statement.instConsts interpret = statement) :
    CDerivable ((church enabled).sum declarations) statement ↔ CDerivable (church enabled) statement :=
  ⟨fun derived => fixed ▸ returned_judgment enabled derived, fun derived => derived.sum_left declarations⟩

theorem proposition_typed (enabled : ComputationProfiles.Selection) :
    CTyped ((church enabled).sum declarations) .nil
    (.const RigidExtension.prop) (.head successorUniverse) :=
  CDerivable.const (P := (church enabled).sum declarations) (Γ := .nil)
    (show ((church enabled).sum declarations).constantType RigidExtension.prop =
      some (.head successorUniverse) from prop_declared)
    (.headType (.sort _)) (.sort _)

theorem returned_proposition_typed (enabled : ComputationProfiles.Selection) : CTyped (church enabled) .nil
    (.head smallUniverse) (.head successorUniverse) :=
  returned_judgment enabled (proposition_typed enabled)

theorem proposition_statement_changes :
    (CStatement.typing .nil (.const RigidExtension.prop) (.head successorUniverse)).instConsts interpret ≠
      CStatement.typing .nil (.const RigidExtension.prop) (.head successorUniverse) := by
  intro equal
  cases equal

theorem original_addition_fixed :
    (CStatement.equality .nil
      (Functions.add (Functions.successor Functions.zero) Functions.zero)
      (Functions.successor Functions.zero) Functions.natural).instConsts interpret =
    CStatement.equality .nil
      (Functions.add (Functions.successor Functions.zero) Functions.zero)
      (Functions.successor Functions.zero) Functions.natural := rfl

theorem original_addition_reflected :
    CEqual (church ComputationProfiles.naturalOnly) .nil
      (Functions.add (Functions.successor Functions.zero) Functions.zero)
      (Functions.successor Functions.zero) Functions.natural :=
  (fixed_statement_iff ComputationProfiles.naturalOnly original_addition_fixed).mp one_plus_zero

theorem full_policy_addition_reflected :
    CEqual (church (fun _ => true)) .nil
      (Functions.add (Functions.successor Functions.zero) Functions.zero)
      (Functions.successor Functions.zero) Functions.natural := by
  have original := judgment_mono (large := fun _ => true) (fun _ _ => rfl) Functions.one_plus_zero
  exact (fixed_statement_iff (fun _ => true) original_addition_fixed).mp
    (original.sum_left declarations)

theorem false_equation_refused_by_return :
    ¬ CEqual package .nil Functions.zero
      (Functions.successor Functions.zero) Functions.natural := by
  intro equal
  exact NaturalDomain.zero_equal_successor_refused (returned_judgment ComputationProfiles.naturalOnly equal)

end Programs.Annotated.NaturalDomain.Decoder
end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeNaturalVectorFamilies
