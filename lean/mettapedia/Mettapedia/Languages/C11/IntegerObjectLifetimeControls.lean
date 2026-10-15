import Mettapedia.Languages.C11.IntegerObjectInitialization
import Mettapedia.Languages.C11.AutomaticObjectScopes
import Mettapedia.Languages.C11.CestaDeclarationReservations
import Mettapedia.Languages.C11.IntegerMemoryProfiles
import Mettapedia.Languages.C11.CestaLocatedExpressions

/-!
# Constructed integer declarations, scope exit and Cesta controls

Positive and negative controls retain byte storage, typed catalogs,
pointer descriptors and lexical frames. They distinguish zero contents,
owned indeterminate bytes and retired lifetime identities. Actual CDecl
constructor forms supply declarations for scalar/array reservation; zero
initializer descriptors remain separate from lifetime-entry contents.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.C11.IntegerObjectLifetimeControls

open Mettapedia.GSLT.Parsing.CanonicalGrammar (CanonicalTerm)
open IntegerObjectConstruction IntegerObjectInitialization

def model : IntegerMemoryModel.Model := IntegerMemoryProfiles.memoryModel .lp64 .little
def integerLayout : ObjectLayout.Layout := ⟨2, 4, by decide, by decide⟩
def wrongLayout : ObjectLayout.Layout := ⟨0, 2, by decide, by decide⟩
def intDeclaration : Declaration := ⟨"x", .int, .scalar⟩
def arrayDeclaration : Declaration := ⟨"a", .int, .array 3 (by decide)⟩
def oneArrayDeclaration : Declaration := ⟨"one", .int, .array 1 (by decide)⟩
def emptyMemory : ObjectAccessMemory.State model.characters := ⟨[], []⟩
def zeroByte : Option (ByteStorageData.Byte model.characters) := some (BitVec.ofNat 8 0)
def integerView : AccessTypes.View := ⟨.scalar (.integer .int), {}⟩
def scalarLocation (identity offset : Nat) : ObjectAccessMemory.Lvalue := ⟨⟨⟨identity, offset⟩, 4⟩, integerView⟩
def integerRecord : ObjectAccessMemory.Record := ObjectAccessMemory.declaredRecord integerView 4

def zeroMemory : ObjectAccessMemory.State model.characters :=
  ⟨[(10, ⟨true, List.replicate 4 zeroByte⟩)], [((scalarLocation 10 0).object, integerRecord)]⟩
def zeroObject : Constructed model := ⟨zeroMemory, [(10, ⟨10, 0, 4, 1⟩)], scalarLocation 10 0⟩
def unknownMemory : ObjectAccessMemory.State model.characters :=
  ⟨[(10, ⟨true, List.replicate 4 none⟩)], zeroMemory.catalog⟩
def unknownObject : Constructed model := ⟨unknownMemory, zeroObject.arrays, scalarLocation 10 0⟩

theorem scalar_zero_entry_constructs_complete_state :
    construct model emptyMemory [] intDeclaration integerLayout 10 .zero = some zeroObject := by decide +kernel
theorem scalar_indeterminate_entry_retains_owned_bytes :
    construct model emptyMemory [] intDeclaration integerLayout 10 .indeterminate = some unknownObject := by decide +kernel
theorem scalar_zero_reads_ordinary_integer_zero :
    ObjectAccessMemory.read (model.layout .int) zeroMemory (scalarLocation 10 0) = some (.integer (.value 0 false)) :=
  constructed_zero_read _ _ _ _ _ _ _ scalar_zero_entry_constructs_complete_state ⟨0, by decide⟩
theorem indeterminate_representation_is_not_an_initialized_value :
    ObjectAccessMemory.read (model.layout .int) unknownMemory (scalarLocation 10 0) = none :=
  constructed_indeterminate_read_refused _ _ _ _ _ _ _ scalar_indeterminate_entry_retains_owned_bytes ⟨0, by decide⟩
theorem indeterminate_raw_read_retains_markers :
    ByteRanges.readBytes unknownMemory.storage ⟨⟨10, 0⟩, 4⟩ = some [none, none, none, none] := by decide +kernel
theorem scalar_has_constructed_array_one_past :
    ArrayPointers.resolve zeroMemory.storage zeroObject.arrays ⟨10, 1⟩ = some ⟨10, 4⟩ := by decide +kernel
theorem scalar_one_past_cannot_be_dereferenced :
    ArrayPointers.elementRange zeroMemory.storage zeroObject.arrays ⟨10, 1⟩ = none := by decide +kernel

def arrayMemory : ObjectAccessMemory.State model.characters :=
  ⟨[(30, ⟨true, List.replicate 12 zeroByte⟩)],
    [((scalarLocation 30 0).object, integerRecord), ((scalarLocation 30 4).object, integerRecord),
      ((scalarLocation 30 8).object, integerRecord)]⟩
def arrayRoot : ObjectAccessMemory.Lvalue :=
  ⟨⟨⟨30, 0⟩, 12⟩, ⟨.array (.scalar (.integer .int)) 3, {}⟩⟩
def arrayObject : Constructed model := ⟨arrayMemory, [(30, ⟨30, 0, 4, 3⟩)], arrayRoot⟩

theorem three_element_array_constructs_each_typed_region :
    construct model emptyMemory [] arrayDeclaration integerLayout 30 .zero = some arrayObject := by decide +kernel
theorem every_constructed_array_element_reads_zero (index : Fin 3) :
    ObjectAccessMemory.read (model.layout .int) arrayMemory
      (elementLocation arrayDeclaration integerLayout 30 index) = some (.integer (.value 0 false)) :=
  constructed_zero_read _ _ _ _ _ _ _ three_element_array_constructs_each_typed_region index
theorem array_one_past_retains_stride :
    ArrayPointers.resolve arrayMemory.storage arrayObject.arrays ⟨30, 3⟩ = some ⟨30, 12⟩ := by decide +kernel
theorem array_outside_bounds_refused :
    ArrayPointers.resolve arrayMemory.storage arrayObject.arrays ⟨30, 4⟩ = none := by decide +kernel
theorem array_one_past_dereference_refused :
    ArrayPointers.elementRange arrayMemory.storage arrayObject.arrays ⟨30, 3⟩ = none := by decide +kernel
theorem wrong_model_extent_refused :
    construct model emptyMemory [] intDeclaration wrongLayout 10 .zero = none := by decide +kernel
theorem occupied_lifetime_refused :
    construct model zeroMemory zeroObject.arrays intDeclaration integerLayout 10 .zero = none := by decide +kernel
theorem fresh_lifetime_is_selected_past_retained_metadata : freshIdentity zeroMemory zeroObject.arrays = 11 := by decide +kernel
theorem admitted_declaration_gets_executable_fresh_allocation :
    ∃ identity result, constructFresh model zeroMemory zeroObject.arrays arrayDeclaration integerLayout .zero = some (identity, result) :=
  constructFresh_exists _ _ _ _ _ _ (by decide)

def oneArrayRoot : ObjectAccessMemory.Lvalue :=
  ⟨⟨⟨40, 0⟩, 4⟩, ⟨.array (.scalar (.integer .int)) 1, {}⟩⟩
def oneArrayMemory : ObjectAccessMemory.State model.characters :=
  ⟨[(40, ⟨true, List.replicate 4 zeroByte⟩)], [((scalarLocation 40 0).object, integerRecord)]⟩
def oneArrayObject : Constructed model := ⟨oneArrayMemory, [(40, ⟨40, 0, 4, 1⟩)], oneArrayRoot⟩
theorem array_one_keeps_array_binding_and_scalar_record :
    construct model emptyMemory [] oneArrayDeclaration integerLayout 40 .zero = some oneArrayObject := by decide +kernel
theorem array_one_element_has_declared_scalar_access :
    ObjectAccessMemory.read (model.layout .int) oneArrayMemory (scalarLocation 40 0) = some (.integer (.value 0 false)) := by decide +kernel
theorem array_root_is_not_misread_as_scalar :
    ObjectAccessMemory.read (model.layout .int) oneArrayMemory oneArrayRoot = none := by decide +kernel

def initial : AutomaticObjectScopes.State model := ⟨emptyMemory, [], [{}]⟩
def outer : AutomaticObjectScopes.State model :=
  ⟨zeroMemory, zeroObject.arrays, [⟨[("x", scalarLocation 10 0)], [10]⟩]⟩
def innerMemory : ObjectAccessMemory.State model.characters :=
  ⟨(20, ⟨true, List.replicate 4 zeroByte⟩) :: zeroMemory.storage,
    ((scalarLocation 20 0).object, integerRecord) :: zeroMemory.catalog⟩
def inner : AutomaticObjectScopes.State model :=
  ⟨innerMemory, (20, ⟨20, 0, 4, 1⟩) :: zeroObject.arrays,
    ⟨[("x", scalarLocation 20 0)], [20]⟩ :: outer.frames⟩
def resumedMemory : ObjectAccessMemory.State model.characters :=
  ⟨(20, ⟨false, List.replicate 4 zeroByte⟩) :: innerMemory.storage, innerMemory.catalog⟩
def resumed : AutomaticObjectScopes.State model := ⟨resumedMemory, inner.arrays, outer.frames⟩

theorem source_entry_constructs_and_binds :
    AutomaticObjectScopes.declare model initial intDeclaration integerLayout 10 .zero = some outer := by decide +kernel
theorem nested_entry_constructs_distinct_lifetime :
    AutomaticObjectScopes.declare model (AutomaticObjectScopes.enter outer) intDeclaration integerLayout 20 .zero = some inner := by decide +kernel
theorem inner_name_shadows_outer :
    ScopedLvalues.lookup (AutomaticObjectScopes.environment inner) "x" = some (scalarLocation 20 0) := by decide +kernel
theorem scope_exit_retires_inner_and_retains_outer : AutomaticObjectScopes.leave model inner = some resumed := by decide +kernel
theorem outer_binding_restored :
    ScopedLvalues.lookup (AutomaticObjectScopes.environment resumed) "x" = some (scalarLocation 10 0) := by decide +kernel
theorem outer_value_remains_readable :
    ScopedLvalues.read (model.layout .int) resumed.memory (AutomaticObjectScopes.environment resumed) "x" =
      some (.integer (.value 0 false)) := by decide +kernel
theorem escaped_inner_location_is_unreadable :
    ObjectAccessMemory.read (model.layout .int) resumed.memory (scalarLocation 20 0) = none := by decide +kernel
theorem escaped_inner_array_pointer_is_unresolvable :
    ArrayPointers.resolve resumed.memory.storage resumed.arrays ⟨20, 0⟩ = none := by decide +kernel
theorem escaped_inner_raw_bytes_are_unreadable :
    ByteRanges.readBytes resumed.memory.storage ⟨⟨20, 0⟩, 4⟩ = none := by decide +kernel
theorem repeated_retirement_refused : AutomaticObjectScopes.retireStorage resumed.memory.storage 20 = none := by decide +kernel
theorem retired_identity_is_not_fresh :
    construct model resumed.memory resumed.arrays intDeclaration integerLayout 20 .zero = none := by decide +kernel
theorem same_frame_redeclaration_refused :
    AutomaticObjectScopes.declare model outer intDeclaration integerLayout 21 .zero = none := by decide +kernel
theorem absent_scope_declaration_refused :
    AutomaticObjectScopes.declare model ⟨emptyMemory, [], []⟩ intDeclaration integerLayout 10 .zero = none := by decide +kernel
theorem resumed_expression_resolves_outer_location :
    CestaLocatedExpressions.readTerm model (AutomaticObjectScopes.environment resumed) (.node "Var" [.text "x"]) =
      some (.load ⟨scalarLocation 10 0, .int, rfl⟩) := by decide +kernel
theorem outer_scope_owned : AutomaticObjectScopes.WellScoped outer := by
  apply AutomaticObjectScopes.declare_wellScoped _ _ _ _ _ _ _ _ source_entry_constructs_and_binds
  simp [AutomaticObjectScopes.WellScoped, AutomaticObjectScopes.allocations, initial]
theorem nested_scope_owned : AutomaticObjectScopes.WellScoped inner :=
  AutomaticObjectScopes.declare_wellScoped _ _ _ _ _ _ _
    (AutomaticObjectScopes.enter_wellScoped _ _ outer_scope_owned) nested_entry_constructs_distinct_lifetime
theorem scope_exit_preserves_remaining_ownership : AutomaticObjectScopes.WellScoped resumed :=
  AutomaticObjectScopes.leave_wellScoped _ _ _ nested_scope_owned scope_exit_retires_inner_and_retains_outer
theorem valid_owned_scope_has_an_executable_exit : ∃ saved, AutomaticObjectScopes.leave model inner = some saved :=
  AutomaticObjectScopes.leave_exists _ _ nested_scope_owned ⟨[("x", scalarLocation 20 0)], [20]⟩ outer.frames rfl

def returnedMemory : ObjectAccessMemory.State model.characters :=
  ⟨(10, ⟨false, List.replicate 4 zeroByte⟩) :: resumedMemory.storage, resumedMemory.catalog⟩
def returnedScopes : AutomaticObjectScopes.State model := ⟨returnedMemory, inner.arrays, []⟩

theorem nested_unwind_ends_both_owned_lifetimes :
    AutomaticObjectScopes.unwind model 2 inner = some returnedScopes := by decide +kernel
theorem one_scope_slice_keeps_the_actual_outer_context :
    AutomaticObjectScopes.unwind model 1 inner = some resumed := by decide +kernel
theorem resumed_unwind_uses_the_paid_residual :
    AutomaticObjectScopes.unwind model 1 resumed = some returnedScopes := by decide +kernel
theorem return_unwind_keeps_catalog_and_pointer_provenance :
    returnedScopes.memory.catalog = inner.memory.catalog ∧ returnedScopes.arrays = inner.arrays := ⟨rfl, rfl⟩
theorem an_escaped_outer_object_is_dead_after_both_scopes_end :
    ObjectAccessMemory.read (model.layout .int) returnedScopes.memory (scalarLocation 10 0) = none := by decide +kernel
theorem an_escaped_inner_object_stays_dead_after_outer_exit :
    ObjectAccessMemory.read (model.layout .int) returnedScopes.memory (scalarLocation 20 0) = none := by decide +kernel
theorem no_binding_survives_the_function_scope_boundary :
    ScopedLvalues.lookup (AutomaticObjectScopes.environment returnedScopes) "x" = none := by decide +kernel
theorem an_overlarge_unwind_does_not_cross_the_empty_frame_boundary :
    AutomaticObjectScopes.unwind model 3 inner = none := by decide +kernel
theorem retired_scopes_cannot_be_unwound_again :
    AutomaticObjectScopes.unwind model 1 returnedScopes = none := by decide +kernel
theorem well_scoped_return_cleanup_has_a_constructed_execution :
    ∃ saved, AutomaticObjectScopes.unwind model 2 inner = some saved :=
  AutomaticObjectScopes.unwind_exists model 2 inner nested_scope_owned (by decide)
theorem nested_return_cleanup_preserves_well_scoped_remainder :
    AutomaticObjectScopes.WellScoped returnedScopes :=
  AutomaticObjectScopes.unwind_wellScoped model 2 inner returnedScopes nested_scope_owned
    nested_unwind_ends_both_owned_lifetimes

def intSpecifiers : CanonicalTerm := .node "PrimitiveDeclarationSpecifiers" [.node "Int" [], .seq []]
def named (name : String) : CanonicalTerm := .node "Declarator" [.node "NameDeclarator" [.text name]]
def arrayNamed (name spelling : String) : CanonicalTerm := .node "Declarator" [.node "ArrayDeclarator"
  [.node "NameDeclarator" [.text name], .node "NoTypeQualifiers" [], .node "SomeExpression" [.node "IntConst" [.text spelling]]]]
def zeroList : CanonicalTerm := .node "InitializerList" [.seq [.node "InitializerElement"
  [.node "InitializerExpression" [.node "IntConst" [.text "0"]]]]]
def arrayTerm : CanonicalTerm := .node "Declaration" [intSpecifiers, .node "InitDeclarators" [.seq
  [.node "InitDeclaratorValue" [arrayNamed "a" "3", zeroList], .node "InitDeclarator" [named "y"]]]]
def arrayEntries : List CestaIntegerDeclarations.Entry :=
  [⟨arrayDeclaration, .zero⟩, ⟨⟨"y", .int, .scalar⟩, .indeterminate⟩]

theorem cesta_declaration_keeps_order_bound_and_initializer :
    CestaIntegerDeclarations.readTerm model arrayTerm = some arrayEntries := by decide +kernel
theorem cesta_empty_array_bound_refused :
    CestaIntegerDeclarations.declarator? model (arrayNamed "a" "0") = none := by decide +kernel
theorem cesta_suffixed_bound_requires_another_profile :
    CestaIntegerDeclarations.declarator? model (arrayNamed "a" "3u") = none := by decide +kernel
theorem cesta_pointer_declaration_requires_another_profile :
    CestaIntegerDeclarations.declarator? model (.node "PointerDeclarator" [.node "Pointer" [.node "NoTypeQualifiers" []],
      .node "NameDeclarator" [.text "p"]]) = none := by decide +kernel
theorem cesta_unqualified_boolean_declaration :
    CestaIntegerDeclarations.specifiers? (.node "UniqueDeclarationSpecifiers" [.node "Bool" [], .seq []]) = some .boolean := by decide +kernel
theorem cesta_repeated_incompatible_specifiers_refused :
    CestaIntegerDeclarations.specifiers? (.node "PrimitiveDeclarationSpecifiers" [.node "Unsigned" [],
      .seq [.node "PrimitiveSpecifierTail" [.node "Signed" []]]]) = none := by decide +kernel
theorem cesta_declaration_keeps_arbitrary_parenthesized_shape :
    CestaIntegerDeclarations.declarator? model (.node "Declarator" [.node "ParenthesizedDeclarator" [
      .node "Declarator" [.node "ParenthesizedDeclarator" [arrayNamed "a" "3"]]]]) =
      some ("a", .array 3 (by decide)) := by decide +kernel

def reservations : CestaDeclarationReservations.Reserved model :=
  ⟨arrayEntries,
    ⟨⟨[(51, ⟨true, List.replicate 4 none⟩), (50, ⟨true, List.replicate 12 none⟩)],
      [((scalarLocation 51 0).object, integerRecord), ((scalarLocation 50 0).object, integerRecord),
        ((scalarLocation 50 4).object, integerRecord), ((scalarLocation 50 8).object, integerRecord)]⟩,
      [(51, ⟨51, 0, 4, 1⟩), (50, ⟨50, 0, 4, 3⟩)],
      [⟨⟨⟨50, 0⟩, 12⟩, ⟨.array (.scalar (.integer .int)) 3, {}⟩⟩, scalarLocation 51 0]⟩⟩
def layouts : CestaDeclarationReservations.LayoutSelection := fun _ => integerLayout

theorem cesta_source_constructs_complete_reserved_objects :
    CestaDeclarationReservations.reserveTerm model emptyMemory [] layouts [50, 51] arrayTerm = some reservations := by decide +kernel
theorem zero_initializer_descriptor_does_not_execute_at_lifetime_entry :
    ByteRanges.readBytes reservations.objects.memory.storage ⟨⟨50, 0⟩, 12⟩ = some (List.replicate 12 none) := by decide +kernel
theorem missing_allocation_choice_refused :
    CestaDeclarationReservations.reserveTerm model emptyMemory [] layouts [50] arrayTerm = none := by decide +kernel
theorem reused_allocation_choice_refused :
    CestaDeclarationReservations.reserveTerm model emptyMemory [] layouts [50, 50] arrayTerm = none := by decide +kernel
theorem incorrect_declaration_layout_refused :
    CestaDeclarationReservations.reserveTerm model emptyMemory [] (fun _ => wrongLayout) [50, 51] arrayTerm = none := by decide +kernel
theorem actual_source_to_owned_reservations_has_independent_judgment :
    CestaDeclarationReservations.Reservation model (ObjectAccessMemory.represent emptyMemory) [] layouts [50, 51]
      arrayTerm reservations.entries (ObjectAccessMemory.represent reservations.objects.memory)
      reservations.objects.arrays reservations.objects.locations :=
  CestaDeclarationReservations.reserveTerm_sound _ _ _ _ _ _ _ cesta_source_constructs_complete_reserved_objects

end Mettapedia.Languages.C11.IntegerObjectLifetimeControls
