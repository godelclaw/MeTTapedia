import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.ConstantExpansionRenaming
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.SchemaTableConstantExpansion
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorAllResultPrimitiveFormation
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationSensitiveConstantInterpretation

/-!
# Primitive support and definition expansion in the Vector result profile

The current base's declared constant names lie in the independently checked
primitive list. The four fresh definitions expand to their stored bodies;
expansion fixes every base primitive and its independently formed type.
The native Nat/Vector/List/J roots survive expansion, while each fresh delta
root becomes reflexivity. The resulting formation-sensitive interpretation
preserves complete judgments and reflects them on expansion-fixed syntax.
-/

set_option autoImplicit false
namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeVectorAllResultComparison.Named.Erasure
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation Declaration
open TypedEquality.Normalization
open NativeNaturalVectorFamilies
open NativeVectorAll.ResultView
abbrev base := Named.base

private theorem mapped_entry_support {entries : List (DeclName × Entry Tower.Head)}
    {map : Entry Tower.Head → Entry Tower.Head} {actual : DeclName} {selected : Entry Tower.Head}
    (known : ((Signature.ofList entries).entries actual).map map = some selected) :
    actual ∈ entries.map Prod.fst := by
  obtain ⟨original, found, _⟩ := Option.map_eq_some_iff.mp known
  exact List.mem_map.mpr ⟨(actual, original), Signature.entries_ofList_mem entries found, rfl⟩

private theorem covered_name {names : List DeclName}
    (covered : names.all (fun actual => decide (actual ∈ PrimitiveBase.primitiveNames)) = true)
    {actual : DeclName} (present : actual ∈ names) : actual ∈ PrimitiveBase.primitiveNames :=
  of_decide_eq_true ((List.all_eq_true.mp covered) actual present)

private theorem lower_support {actual : DeclName} {entry : Entry Tower.Head}
    (known : NativeVectorAllCommonRecursorProfile.lower.entries actual = some entry) :
    actual ∈ PrimitiveBase.primitiveNames := by
  change (NativeNaturalVectorFamilies.rawSignature.entries actual).map _ = some entry at known
  have present := mapped_entry_support (entries := NativeNaturalVectorFamilies.declarations) known
  exact covered_name (names := NativeNaturalVectorFamilies.declarations.map Prod.fst) (by decide +kernel) present

private theorem output_support {actual : DeclName} {entry : Entry Tower.Head}
    (known : NativeVectorAllCommonRecursorProfile.output.entries actual = some entry) :
    actual ∈ PrimitiveBase.primitiveNames := by
  change ((NativeNaturalVectorFamilies.rawSignature.entries (OriginalInputUniverses.names.symm actual)).map _).map _ =
    some entry at known
  rw [Option.map_map] at known
  have original := mapped_entry_support (entries := NativeNaturalVectorFamilies.declarations) known
  have selected : actual ∈ NativeNaturalVectorFamilies.declarations.map
      (fun row => OriginalInputUniverses.names row.1) := by
    obtain ⟨row, present, same⟩ := List.mem_map.mp original
    apply List.mem_map.mpr
    refine ⟨row, present, ?_⟩
    rw [same]
    exact OriginalInputUniverses.names.apply_symm_apply actual
  exact covered_name (names := NativeNaturalVectorFamilies.declarations.map (fun row => OriginalInputUniverses.names row.1)) (by decide +kernel) selected

private theorem identity_support {actual : DeclName} {entry : Entry Tower.Head}
    (known : NativeVectorIdentityComparison.identitySignature.entries actual = some entry) :
    actual ∈ PrimitiveBase.primitiveNames := by
  change (NativeIndexedFamilies.Intrinsic.rawSignature.entries actual).map _ = some entry at known
  have present := mapped_entry_support (entries := NativeIndexedFamilies.Intrinsic.declarations) known
  exact covered_name (names := NativeIndexedFamilies.Intrinsic.declarations.map Prod.fst) (by decide +kernel) present

theorem primitive_complete {actual : DeclName} {declared : Tower.Tm 0}
    (known : base.constantType actual = some declared) : actual ∈ PrimitiveBase.primitiveNames := by
  change NativeVectorAllResultComparison.signature.typeOf? actual = some declared at known
  obtain ⟨entry, found, _⟩ := Option.map_eq_some_iff.mp known
  change (Signature.merge NativeVectorAllResultComparison.common
    NativeVectorIdentityComparison.identitySignature).entries actual = some entry at found
  rcases Signature.merge_origin NativeVectorAllResultComparison.common
    NativeVectorIdentityComparison.identitySignature actual with common | identity
  · rw [common] at found
    change (Signature.merge NativeVectorAllCommonRecursorProfile.lower
      NativeVectorAllCommonRecursorProfile.output).entries actual = some entry at found
    rcases Signature.merge_origin NativeVectorAllCommonRecursorProfile.lower
      NativeVectorAllCommonRecursorProfile.output actual with lower | output
    · rw [lower] at found
      exact lower_support found
    · rw [output] at found
      exact output_support found
  · rw [identity] at found
    exact identity_support found

def bodies (actual : DeclName) : Tower.Tm 0 :=
  (Named.signature.valueOf? actual).getD (.const actual)

theorem operation_body (operation : Operation) : bodies (Named.name operation) = Named.body operation := by
  simp only [bodies, Named.value_lookup, Option.getD_some]

theorem primitive_body {actual : DeclName} (known : base.constantType actual ≠ none) :
    bodies actual = .const actual := by
  cases value : Named.signature.valueOf? actual with
  | none => simp only [bodies, value, Option.getD_none]
  | some body =>
    unfold Signature.valueOf? at value
    cases found : Named.signature.entries actual with
    | none => simp only [found, Option.bind_none] at value; cases value
    | some entry => exact False.elim (known (Named.formed.fresh found))

theorem primitive_type_fixed {actual : DeclName} {declared : Tower.Tm 0}
    (known : base.constantType actual = some declared) : ConstantExpansion.expand bodies declared = declared := by
  obtain ⟨_, _, formed⟩ := PrimitiveBase.primitive_type_formed (primitive_complete known) known
  exact formed.typing.expand_eq_of_declared_constants bodies (fun _ present => primitive_body present)

theorem operation_type_fixed (operation : Operation) :
    ConstantExpansion.expand bodies (Named.type operation) = Named.type operation := by
  obtain ⟨_, _, formed⟩ := Named.type_formed operation
  exact formed.typing.expand_eq_of_declared_constants bodies (fun _ present => primitive_body present)

theorem operation_body_fixed (operation : Operation) :
    ConstantExpansion.expand bodies (Named.body operation) = Named.body operation :=
  (Named.body_checked operation).typing.expand_eq_of_declared_constants bodies
    (fun _ present => primitive_body present)

theorem constant_interpreted {actual : DeclName} {declared : Tower.Tm 0}
    (known : Named.rules.constantType actual = some declared) :
    FormationSensitive.Typing base .nil (bodies actual) (ConstantExpansion.expand bodies declared) := by
  cases prior : base.constantType actual with
  | some original =>
    have included := combinedType_of_base base Named.signature prior
    have same : original = declared := Option.some.inj (included.symm.trans known)
    cases same
    rw [primitive_body (by rw [prior]; simp), primitive_type_fixed prior]
    exact (PrimitiveBase.primitive_typed (primitive_complete prior) prior).typing
  | none =>
    have selected : Named.signature.typeOf? actual = some declared := by
      change combinedType base Named.signature actual = some declared at known
      simpa only [combinedType, prior] using known
    obtain ⟨entry, found, typeExact⟩ := Option.map_eq_some_iff.mp selected
    have present := Signature.entries_ofList_mem Named.declarations found
    obtain ⟨operation, _, selected⟩ := List.mem_map.mp present
    rcases Prod.mk.inj selected with ⟨rfl, rfl⟩
    change Named.type operation = declared at typeExact
    cases typeExact
    rw [operation_body, operation_type_fixed]
    exact (Named.body_checked operation).typing

def naturalBodies (renamed : Bool) : ConstantExpansion.Bodies Tower.Head :=
  if renamed then ConstantExpansion.renameBodies OriginalInputUniverses.names.symm bodies else bodies

theorem natural_rows_fixed (renamed : Bool) (index : Fin NativeNaturalVectorFamilies.Checking.table.length) :
    ConstantExpansion.expand (naturalBodies renamed) (NativeNaturalVectorFamilies.Checking.table.get index).2.1 =
        (NativeNaturalVectorFamilies.Checking.table.get index).2.1 ∧
    ConstantExpansion.expand (naturalBodies renamed) (NativeNaturalVectorFamilies.Checking.table.get index).2.2 =
        (NativeNaturalVectorFamilies.Checking.table.get index).2.2 := by
  fin_cases index <;> cases renamed <;> decide +kernel

theorem natural_step_expansion (renamed : Bool) {n : Nat} {left right : Tower.Tm n}
    (step : NativeNaturalVectorFamilies.iotaComputation.step left right) :
    NativeNaturalVectorFamilies.iotaComputation.step
      (ConstantExpansion.expand (naturalBodies renamed) left)
      (ConstantExpansion.expand (naturalBodies renamed) right) := by
  obtain ⟨code, decoded⟩ := NativeNaturalVectorFamilies.Checking.iotaDecoder.complete step
  have source := SchemaTableConversionCode.decode_sound NativeNaturalVectorFamilies.Checking.table
    NativeNaturalVectorFamilies.Checking.enabled code decoded
  have expanded := SchemaTableConversionCode.root_expand (naturalBodies renamed)
    (natural_rows_fixed renamed) source
  obtain ⟨code, decoded⟩ := SchemaTableConversionCode.decode_complete NativeNaturalVectorFamilies.Checking.table
    NativeNaturalVectorFamilies.Checking.enabled expanded
  exact NativeNaturalVectorFamilies.Checking.iotaDecoder.sound code decoded

theorem output_step_expansion {n : Nat} {left right : Tower.Tm n}
    (step : NativeVectorAllCommonRecursorProfile.output.computation.step left right) :
    NativeVectorAllCommonRecursorProfile.output.computation.step
      (ConstantExpansion.expand bodies left) (ConstantExpansion.expand bodies right) := by
  have expanded := natural_step_expansion true step
  change NativeNaturalVectorFamilies.iotaComputation.step
    ((ConstantExpansion.expand bodies left).mapConst OriginalInputUniverses.names.symm)
    ((ConstantExpansion.expand bodies right).mapConst OriginalInputUniverses.names.symm)
  simpa only [naturalBodies, if_true, ConstantExpansion.expand_mapConst] using expanded

private theorem list_nil_fixed : bodies NativeIndexedFamilies.Intrinsic.nilName =
    .const NativeIndexedFamilies.Intrinsic.nilName := rfl
private theorem list_cons_fixed : bodies NativeIndexedFamilies.Intrinsic.consName =
    .const NativeIndexedFamilies.Intrinsic.consName := rfl
private theorem list_eliminate_fixed : bodies NativeIndexedFamilies.Intrinsic.eliminateName =
    .const NativeIndexedFamilies.Intrinsic.eliminateName := rfl
private theorem identity_eliminate_fixed : bodies NativeIndexedFamilies.Intrinsic.identityEliminateName =
    .const NativeIndexedFamilies.Intrinsic.identityEliminateName := rfl

theorem identity_step_expansion {n : Nat} {left right : Tower.Tm n}
    (step : NativeVectorIdentityComparison.identitySignature.computation.step left right) :
    NativeVectorIdentityComparison.identitySignature.computation.step
      (ConstantExpansion.expand bodies left) (ConstantExpansion.expand bodies right) := by
  obtain ⟨evidence⟩ := step
  change Nonempty (NativeIndexedFamilies.Intrinsic.IotaEvidence n
    (ConstantExpansion.expand bodies left) (ConstantExpansion.expand bodies right))
  cases evidence with
  | nil element motive nilCase consCase =>
    refine ⟨?_⟩
    simpa only [NativeIndexedFamilies.Intrinsic.eliminateApp, NativeIndexedFamilies.Intrinsic.nilApp,
      appSpine, List.foldl_cons, List.foldl_nil, ConstantExpansion.expand,
      list_eliminate_fixed, list_nil_fixed, liftClosed, rename] using
      (NativeIndexedFamilies.Intrinsic.IotaEvidence.nil
        (ConstantExpansion.expand bodies element) (ConstantExpansion.expand bodies motive)
        (ConstantExpansion.expand bodies right) (ConstantExpansion.expand bodies consCase))
  | cons element motive nilCase consCase head tail =>
    refine ⟨?_⟩
    simpa only [NativeIndexedFamilies.Intrinsic.eliminateApp, NativeIndexedFamilies.Intrinsic.consApp,
      appSpine, List.foldl_cons, List.foldl_nil, ConstantExpansion.expand,
      list_eliminate_fixed, list_cons_fixed, liftClosed, rename] using
      (NativeIndexedFamilies.Intrinsic.IotaEvidence.cons
        (ConstantExpansion.expand bodies element) (ConstantExpansion.expand bodies motive)
        (ConstantExpansion.expand bodies nilCase) (ConstantExpansion.expand bodies consCase)
        (ConstantExpansion.expand bodies head) (ConstantExpansion.expand bodies tail))
  | identity element point motive reflCase =>
    refine ⟨?_⟩
    simpa only [NativeIndexedFamilies.Intrinsic.identityEliminateApp, appSpine,
      List.foldl_cons, List.foldl_nil, ConstantExpansion.expand,
      identity_eliminate_fixed, liftClosed, rename] using
      (NativeIndexedFamilies.Intrinsic.IotaEvidence.identity
        (ConstantExpansion.expand bodies element) (ConstantExpansion.expand bodies point)
        (ConstantExpansion.expand bodies motive) (ConstantExpansion.expand bodies right))

private theorem merge_values_none {first second : Signature Tower.Head}
    (left : ∀ actual, first.valueOf? actual = none) (right : ∀ actual, second.valueOf? actual = none)
    (actual : DeclName) : (Signature.merge first second).valueOf? actual = none := by
  change ((Signature.merge first second).entries actual).bind Entry.value? = none
  rcases Signature.merge_origin first second actual with selected | selected
  · rw [selected]
    exact left actual
  · rw [selected]
    exact right actual

private theorem lower_values_none (actual : DeclName) :
    NativeVectorAllCommonRecursorProfile.lower.valueOf? actual = none := by
  change (NativeNaturalVectorFamilies.rawSignature.instantiateLevels
    NativeVectorAll.Universes.CumulativeElimination.levels NativeNaturalVectorFamilies.iotaComputation).valueOf? actual = none
  simp only [Signature.valueOf_instantiateLevels, NativeNaturalVectorFamilies.rawSignature_valueOf_none, Option.map_none]

private theorem output_values_none (actual : DeclName) :
    NativeVectorAllCommonRecursorProfile.output.valueOf? actual = none := by
  change (NativeVectorAllCommonRecursorProfile.outputInstance.signature.renameConst
    OriginalInputUniverses.names).valueOf? actual = none
  rw [Signature.valueOf_renameConst]
  change ((NativeNaturalVectorFamilies.rawSignature.instantiateLevels
    NativeVectorAllCommonRecursorProfile.outputLevels NativeNaturalVectorFamilies.iotaComputation).valueOf?
      (OriginalInputUniverses.names.symm actual)).map (Tm.mapConst OriginalInputUniverses.names) = none
  simp only [Signature.valueOf_instantiateLevels, NativeNaturalVectorFamilies.rawSignature_valueOf_none, Option.map_none]

private theorem identity_values_none (actual : DeclName) :
    NativeVectorIdentityComparison.identitySignature.valueOf? actual = none := by
  change (NativeIndexedFamilies.Intrinsic.rawSignature.instantiateLevels
    (NativeIndexedFamilies.IntrinsicMaps.sameLevelSubstitution evidenceUpperLevel)
      NativeIndexedFamilies.Intrinsic.iotaComputation).valueOf? actual = none
  simp only [Signature.valueOf_instantiateLevels, NativeIndexedFamilies.Intrinsic.rawSignature_valueOf_none, Option.map_none]

theorem base_values_none (actual : DeclName) :
    NativeVectorAllResultComparison.signature.valueOf? actual = none :=
  merge_values_none (merge_values_none lower_values_none output_values_none) identity_values_none actual

theorem base_step_expansion {n : Nat} {left right : Tower.Tm n}
    (step : base.computation.step left right) :
    base.computation.step (ConstantExpansion.expand bodies left) (ConstantExpansion.expand bodies right) := by
  change RootStep Tower.rules NativeVectorAllResultComparison.signature n left right at step
  cases step with
  | inherited impossible => exact impossible.elim
  | delta unfolding =>
    rw [base_values_none] at unfolding
    cases unfolding
  | declared declared =>
    rcases declared with common | identity
    · rcases common with lower | output
      · exact RootStep.declared (Or.inl (Or.inl (natural_step_expansion false lower)))
      · exact RootStep.declared (Or.inl (Or.inr (output_step_expansion output)))
    · exact RootStep.declared (Or.inr (identity_step_expansion identity))

theorem stored_value_fixed {actual : DeclName} {value : Tower.Tm 0}
    (known : Named.signature.valueOf? actual = some value) :
    ConstantExpansion.expand bodies value = value := by
  cases found : Named.signature.entries actual with
  | none => simp only [Signature.valueOf?, found, Option.bind_none] at known; cases known
  | some entry =>
    have selectedValue : entry.value? = some value := by
      simpa only [Signature.valueOf?, found, Option.bind_some] using known
    have present := Signature.entries_ofList_mem Named.declarations found
    obtain ⟨operation, _, selected⟩ := List.mem_map.mp present
    rcases Prod.mk.inj selected with ⟨rfl, rfl⟩
    cases Option.some.inj selectedValue
    exact operation_body_fixed operation

theorem named_step_conversion {n : Nat} {left right : Tower.Tm n}
    (step : Named.rules.computation.step left right) :
    Conv base.headEq (ConstantExpansion.expand bodies left) (ConstantExpansion.expand bodies right)
      base.computation := by
  cases step with
  | inherited previous => exact .rel _ _ (.root (base_step_expansion previous))
  | @delta actual value unfolding =>
    have selectedBody : bodies actual = value := by
      simp only [bodies, unfolding, Option.getD_some]
    change Conv base.headEq (liftClosed (bodies actual))
      (ConstantExpansion.expand bodies (liftClosed value)) base.computation
    rw [selectedBody, ConstantExpansion.expand_liftClosed, stored_value_fixed unfolding]
    exact .refl _
  | declared impossible => exact impossible.elim

theorem interpretation : ConstantExpansion.TypedInterpretation Named.rules base bodies where
  headTyping := fun known => known
  isUniverse := fun known => known
  join := fun known => known
  cumulative := fun known => known
  headEq := rfl
  constant := constant_interpreted
  root := named_step_conversion

theorem erase_judgment {n : Nat} {context : Tower.Ctx n} {term type : Tower.Tm n}
    (checked : FormationSensitive.Judgment Named.rules context term type) :
    FormationSensitive.Judgment base (ConstantExpansion.expandCtx bodies context)
      (ConstantExpansion.expand bodies term) (ConstantExpansion.expand bodies type) :=
  interpretation.judgment checked

theorem context_fixed {n : Nat} {context : Tower.Ctx n}
    (formed : FormationSensitive.ContextFormation base context) :
    ConstantExpansion.expandCtx bodies context = context := by
  induction formed with
  | nil => rfl
  | @snoc n prior domain domainUniverse priorFormation domainFormation domainIsUniverse ih =>
    change Ctx.snoc (ConstantExpansion.expandCtx bodies prior) (ConstantExpansion.expand bodies domain) =
      Ctx.snoc prior domain
    rw [ih, domainFormation.expand_eq_of_declared_constants bodies (fun _ known => primitive_body known)]

theorem conservative_on_fixed {n : Nat} {context : Tower.Ctx n} {term type : Tower.Tm n}
    (contextFixed : ConstantExpansion.expandCtx bodies context = context)
    (termFixed : ConstantExpansion.expand bodies term = term)
    (typeFixed : ConstantExpansion.expand bodies type = type) :
    FormationSensitive.Judgment Named.rules context term type ↔ FormationSensitive.Judgment base context term type := by
  constructor
  · intro checked
    simpa only [contextFixed, termFixed, typeFixed] using erase_judgment checked
  · intro checked
    exact checked.includeSignature Named.signature

#print axioms primitive_complete
#print axioms primitive_body
#print axioms primitive_type_fixed
#print axioms constant_interpreted
#print axioms natural_step_expansion
#print axioms output_step_expansion
#print axioms identity_step_expansion
#print axioms base_step_expansion
#print axioms named_step_conversion
#print axioms erase_judgment
#print axioms conservative_on_fixed
end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeVectorAllResultComparison.Named.Erasure
