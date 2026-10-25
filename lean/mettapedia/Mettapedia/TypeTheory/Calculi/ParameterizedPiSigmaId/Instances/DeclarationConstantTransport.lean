import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.RecursionComputation
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.ConstantRenamingComputation
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.DeclarationSignature
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.Tower

/-!
# Constant renaming and compatible declaration unions

A permutation of declaration names transports the actual cumulative-tower
signature, including delta and declared root steps, while preserving formation.
A compatible union retains both declaration inventories and root relations;
its formation proof reuses the existing signature-extension theorem for any
base calculus. Compatibility requires equal entries on overlapping names.
The finite union decoder preserves source codes as a tagged sum.

Formation does not establish computational preservation, normalization,
conservativity or equality of retained proof histories.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
variable {SourceHead TargetHead : Type} {n : Nat}
theorem Tm.mapConst_mapHead (names : DeclName → DeclName) (heads : SourceHead → TargetHead)
    (term : Tm SourceHead n) :
    (term.mapHead heads).mapConst names = (term.mapConst names).mapHead heads := by
  induction term <;> simp only [Tm.mapHead, Tm.mapConst, *]
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation


namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Declaration

variable {Head : Type}

def Entry.renameConst (names : DeclName ≃ DeclName) (entry : Entry Head) : Entry Head where
  type := entry.type.mapConst names
  value? := entry.value?.map (Tm.mapConst names)

def Signature.renameConst (names : DeclName ≃ DeclName) (source : Signature Head) : Signature Head where
  entries name := (source.entries (names.symm name)).map (Entry.renameConst names)
  computation := source.computation.pullbackConst names.symm

@[simp] theorem Signature.typeOf_renameConst (names : DeclName ≃ DeclName)
    (source : Signature Head) (name : DeclName) :
    (source.renameConst names).typeOf? name =
      (source.typeOf? (names.symm name)).map (Tm.mapConst names) := by
  unfold Signature.typeOf? Signature.renameConst Entry.renameConst
  cases found : source.entries (names.symm name) <;> simp [found]

@[simp] theorem Signature.valueOf_renameConst (names : DeclName ≃ DeclName)
    (source : Signature Head) (name : DeclName) :
    (source.renameConst names).valueOf? name =
      (source.valueOf? (names.symm name)).map (Tm.mapConst names) := by
  unfold Signature.valueOf? Signature.renameConst Entry.renameConst
  cases found : source.entries (names.symm name) with
  | none => simp [found]
  | some entry => cases valueFound : entry.value? <;> simp [found, valueFound]

namespace Signature

theorem renaming_morphism (names : DeclName ≃ DeclName) (source : Signature Tower.Head) :
    TypedEquality.RulesRenaming (extendRules Tower.rules source)
      (extendRules Tower.rules (source.renameConst names)) names where
  headTyping h := h
  isUniverse h := h
  join h := h
  cumulative h := h
  headEq h := h
  constantType := by
    intro name type known
    change source.typeOf? name = some type at known
    change (source.renameConst names).typeOf? (names name) = some (type.mapConst names)
    rw [typeOf_renameConst, names.symm_apply_apply, known]
    rfl
  computation := by
    intro n left right step
    change RootStep Tower.rules source n left right at step
    change RootStep Tower.rules (source.renameConst names) n
      (left.mapConst names) (right.mapConst names)
    cases step with
    | inherited old => exact old.elim
    | @delta name value found =>
        have targetFound : (source.renameConst names).valueOf? (names name) =
            some (value.mapConst names) := by
          rw [valueOf_renameConst, names.symm_apply_apply, found]
          rfl
        simpa only [Tm.mapConst, Tm.mapConst_liftClosed] using
          (RootStep.delta (n := n) targetFound)
    | declared old => exact .declared (source.computation.pullbackConst_forward names old)

theorem Formed.renameConst (names : DeclName ≃ DeclName) {source : Signature Tower.Head}
    (formed : source.Formed Tower.rules) : (source.renameConst names).Formed Tower.rules where
  fresh := by intros; rfl
  types := by
    intro name type known
    rw [typeOf_renameConst] at known
    obtain ⟨originalType, found, mappedType⟩ := Option.map_eq_some_iff.mp known
    obtain ⟨level, universeWitness, typed⟩ := formed.types found
    refine ⟨level, universeWitness, ?_⟩
    have mapped := typed.mapConst (renaming_morphism names source)
    simpa only [Ctx.mapConst, Tm.mapConst, mappedType] using mapped
  values := by
    intro name type value typeKnown valueKnown
    rw [typeOf_renameConst] at typeKnown
    rw [valueOf_renameConst] at valueKnown
    obtain ⟨originalType, typeFound, mappedType⟩ := Option.map_eq_some_iff.mp typeKnown
    obtain ⟨originalValue, valueFound, mappedValue⟩ := Option.map_eq_some_iff.mp valueKnown
    have mapped := (formed.values typeFound valueFound).mapConst (renaming_morphism names source)
    simpa only [Ctx.mapConst, mappedType, mappedValue] using mapped
  noSelfDelta := by
    intro name value known same
    rw [valueOf_renameConst] at known
    obtain ⟨originalValue, found, mappedValue⟩ := Option.map_eq_some_iff.mp known
    have originalEq := congrArg (Tm.mapConst names.symm) (mappedValue.trans same)
    have forbidden := formed.noSelfDelta found
    apply forbidden
    simpa only [Tm.mapConst_equiv_left, Tm.mapConst] using originalEq

end Signature

#print axioms Signature.renaming_morphism
#print axioms Signature.Formed.renameConst

namespace Signature

def Compatible (left right : Signature Head) : Prop :=
  ∀ name first second, left.entries name = some first → right.entries name = some second → first = second

def merge (left right : Signature Head) : Signature Head where
  entries name := (left.entries name).orElse (fun _ => right.entries name)
  computation := TypedEquality.Normalization.RootComputation.union left.computation right.computation

theorem merge_entries_left (left right : Signature Head) {name : DeclName} {entry : Entry Head}
    (found : left.entries name = some entry) : (merge left right).entries name = some entry := by
  simp only [merge, found, Option.orElse_some]

theorem merge_entries_right {left right : Signature Head} (compatible : Compatible left right)
    {name : DeclName} {entry : Entry Head} (found : right.entries name = some entry) :
    (merge left right).entries name = some entry := by
  cases old : left.entries name with
  | none => simp only [merge, old, Option.orElse_none, found]
  | some first =>
      have equal := compatible name first entry old found
      simp only [merge, old, Option.orElse_some, equal]

theorem merge_left (left right : Signature Head) : left.Extends (merge left right) where
  entries := fun found => merge_entries_left left right found
  computation := fun step => Or.inl step

theorem merge_right {left right : Signature Head} (compatible : Compatible left right) :
    right.Extends (merge left right) where
  entries := fun found => merge_entries_right compatible found
  computation := fun step => Or.inr step

end Signature

namespace Signature

theorem merge_origin (left right : Signature Head) (name : DeclName) :
    (merge left right).entries name = left.entries name ∨
      (merge left right).entries name = right.entries name := by
  cases found : left.entries name with
  | none => exact Or.inr (by simp only [merge, found, Option.orElse_none])
  | some entry => exact Or.inl (by simp only [merge, found, Option.orElse_some])

theorem Formed.merge {base : Rules Head} {left right : Signature Head}
    (first : left.Formed base) (second : right.Formed base)
    (compatible : Compatible left right) : (Signature.merge left right).Formed base where
  fresh := by
    intro name entry found
    rcases merge_origin left right name with selected | selected
    · rw [selected] at found
      exact first.fresh found
    · rw [selected] at found
      exact second.fresh found
  types := by
    intro name type known
    rcases merge_origin left right name with selected | selected
    · have typesEq : (Signature.merge left right).typeOf? name = left.typeOf? name :=
        congrArg (Option.map Entry.type) selected
      rw [typesEq] at known
      obtain ⟨level, witness, typed⟩ := first.types known
      refine ⟨level, witness, ?_⟩
      exact Declaration.HasType.monoSignature base (merge_left left right) typed
    · have typesEq : (Signature.merge left right).typeOf? name = right.typeOf? name :=
        congrArg (Option.map Entry.type) selected
      rw [typesEq] at known
      obtain ⟨level, witness, typed⟩ := second.types known
      refine ⟨level, witness, ?_⟩
      exact Declaration.HasType.monoSignature base (merge_right compatible) typed
  values := by
    intro name type value typeKnown valueKnown
    rcases merge_origin left right name with selected | selected
    · have typesEq : (Signature.merge left right).typeOf? name = left.typeOf? name :=
        congrArg (Option.map Entry.type) selected
      have valuesEq : (Signature.merge left right).valueOf? name = left.valueOf? name :=
        congrArg (fun entries => entries.bind Entry.value?) selected
      rw [typesEq] at typeKnown
      rw [valuesEq] at valueKnown
      exact Declaration.HasType.monoSignature base (merge_left left right) (first.values typeKnown valueKnown)
    · have typesEq : (Signature.merge left right).typeOf? name = right.typeOf? name :=
        congrArg (Option.map Entry.type) selected
      have valuesEq : (Signature.merge left right).valueOf? name = right.valueOf? name :=
        congrArg (fun entries => entries.bind Entry.value?) selected
      rw [typesEq] at typeKnown
      rw [valuesEq] at valueKnown
      exact Declaration.HasType.monoSignature base (merge_right compatible) (second.values typeKnown valueKnown)
  noSelfDelta := by
    intro name value known
    rcases merge_origin left right name with selected | selected
    · have valuesEq : (Signature.merge left right).valueOf? name = left.valueOf? name :=
        congrArg (fun entries => entries.bind Entry.value?) selected
      rw [valuesEq] at known
      exact first.noSelfDelta known
    · have valuesEq : (Signature.merge left right).valueOf? name = right.valueOf? name :=
        congrArg (fun entries => entries.bind Entry.value?) selected
      rw [valuesEq] at known
      exact second.noSelfDelta known

end Signature

#print axioms Signature.Formed.merge

end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Declaration

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.StructuralConversionCode
open TypedEquality.Normalization

def RootDecoder.union {Head : Type} {first second : RootComputation Head}
    (left : RootDecoder first) (right : RootDecoder second) :
    RootDecoder (RootComputation.union first second) where
  Code n := left.Code n ⊕ right.Code n
  decode := fun code => code.elim left.decode right.decode
  sound := by
    intro n code source target decoded
    cases code with
    | inl code => exact Or.inl (left.sound code decoded)
    | inr code => exact Or.inr (right.sound code decoded)
  complete := by
    intro n source target step
    rcases step with firstStep | secondStep
    · obtain ⟨code, decoded⟩ := left.complete firstStep
      exact ⟨.inl code, decoded⟩
    · obtain ⟨code, decoded⟩ := right.complete secondStep
      exact ⟨.inr code, decoded⟩
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.StructuralConversionCode
