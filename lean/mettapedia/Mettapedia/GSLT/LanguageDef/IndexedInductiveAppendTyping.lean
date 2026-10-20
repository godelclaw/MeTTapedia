import Mettapedia.GSLT.LanguageDef.IndexedInductiveAppendSourceMeaning
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationSensitiveTelescopeSpine
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationSensitiveSignaturePreservation
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.CumulativeRegularity

/-!
# Formed representations at the dependent append boundary

Constructor formation is checked in the selected declaration calculus.
Represented source naturals and vectors then receive formation-sensitive
typing by induction, retaining the actual element type and its payload
judgments. The resulting dependent argument assignment applies to the
independently checked textual append function.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.IndexedInductive.Guest.AppendTyping

open Mettapedia.TypeTheory
open IndexedPolynomial IndexedPolynomial.Description
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open NativeNaturalVectorFamilies Declaration.IndexedFamily SchemaElaboration
open IndexedInductiveNatVec VectorMeaning AppendMeaning
open TypedEquality.Normalization

abbrev Typed {scope : Nat} (context : Tower.Ctx scope) (term type : Tower.Tm scope) :=
  FormationSensitive.Typing Programs.rules context term type

local instance : DecidableRel Programs.rules.headTyping :=
  fun h u => inferInstanceAs (Decidable (Tower.rules.headTyping h u))
local instance : DecidablePred Programs.rules.isUniverse :=
  fun h => inferInstanceAs (Decidable (Tower.rules.isUniverse h))
local instance : ∀ u v w, Decidable (Programs.rules.join u v w) :=
  fun u v w => inferInstanceAs (Decidable (Tower.rules.join u v w))
local instance : DecidableRel Programs.rules.cumulative :=
  fun h u => inferInstanceAs (Decidable (Tower.rules.cumulative h u))
local instance : DecidableRel Programs.rules.headEq :=
  fun h u => inferInstanceAs (Decidable (Tower.rules.headEq h u))

/-- The original declaration names and types, without new inference rules. -/
def constructor : Fin 6 → DeclName × Tower.Tm 0 :=
  ![(natName, natType), (zeroName, zeroType), (succName, succType),
    (vecName, vecType), (vnilName, vnilType), (vconsName, vconsType)]

def submission (index : Fin 6) :=
  FormationSensitiveElaboration.elaborate Programs.rules Programs.decoder Programs.choices 24
    (.nil : Tower.Ctx 0) (.const (constructor index).1) (constructor index).2

theorem constructors_checked (index : Fin 6) : (submission index).isSome = true := by
  fin_cases index <;> decide +kernel

theorem constructor_judgment (index : Fin 6) :
    FormationSensitive.Judgment Programs.rules .nil
      (.const (constructor index).1) (constructor index).2 := by
  obtain ⟨evidence, produced⟩ := Option.isSome_iff_exists.mp (constructors_checked index)
  exact FormationSensitiveElaboration.elaborate_sound Programs.rules Programs.decoder Programs.choices
    24 .nil _ _ evidence produced

/-- The real lexical arguments are represented in the original telescope's
reverse de Bruijn order, including both independently represented lengths. -/
noncomputable def assignment {A : Type} (element : Tower.Tm 0) (payload : A → Tower.Tm 0)
    {n m : Natural.Carrier} (left : Vectors.Vector A n) (right : Vectors.Vector A m) :
    Sub Tower.Head 5 0 :=
  Fin.cases (encodeVector element payload right)
    (Fin.cases (encodeVector element payload left)
      (Fin.cases (quoteIndex m) (Fin.cases (quoteIndex n) (fun _ => element))))

/-- Constructor formation is supplied by the selected checking rules. This
record carries checked judgments; it adds no computation permission. -/
structure ConstructorFormation (R : Rules Tower.Head) : Prop where
  judgments : ∀ index : Fin 6, FormationSensitive.Judgment R .nil
    (.const (constructor index).1) (constructor index).2

namespace ConstructorFormation

private theorem constructor_typing {R : Rules Tower.Head} (formation : ConstructorFormation R)
    {scope : Nat} (context : Tower.Ctx scope) (index : Fin 6) :
    FormationSensitive.Typing R context (.const (constructor index).1) (liftClosed (constructor index).2) := by
  simpa only [rename, liftClosed] using
    (formation.judgments index).typing.renameTyping
      (ρ := (Fin.elim0 : Ren 0 scope)) (Δ := context) (fun i => Fin.elim0 i)

theorem nat_formed {R : Rules Tower.Head} (formation : ConstructorFormation R)
    {scope : Nat} (context : Tower.Ctx scope) :
    FormationSensitive.Typing R context natTm (sortTm natLevel) := by
  simpa only [constructor, Matrix.cons_val_zero, natType, natTm, sortTm, liftClosed, rename] using
    constructor_typing formation context 0

theorem zero_typed {R : Rules Tower.Head} (formation : ConstructorFormation R)
    {scope : Nat} (context : Tower.Ctx scope) : FormationSensitive.Typing R context zeroTm natTm := by
  exact constructor_typing formation context 1

theorem succ_typed {R : Rules Tower.Head} (formation : ConstructorFormation R)
    {scope : Nat} {context : Tower.Ctx scope} {number : Tower.Tm scope}
    (typed : FormationSensitive.Typing R context number natTm) : FormationSensitive.Typing R context (succApp number) natTm := by
  exact FormationSensitive.Typing.appElim (constructor_typing formation context 2) typed

theorem numeral_typed {R : Rules Tower.Head} (formation : ConstructorFormation R)
    {scope : Nat} (context : Tower.Ctx scope) (number : Nat) :
    FormationSensitive.Typing R context (numeral number) natTm := by
  induction number with
  | zero => exact zero_typed formation context
  | succ number ih => exact succ_typed formation ih

theorem index_typed {R : Rules Tower.Head} (formation : ConstructorFormation R)
    (number : Natural.Carrier) : FormationSensitive.Typing R .nil (quoteIndex number) natTm := by
  exact numeral_typed formation .nil (Natural.toNat number)

theorem vector_formed {R : Rules Tower.Head} (formation : ConstructorFormation R)
    {scope : Nat} {context : Tower.Ctx scope} {element length : Tower.Tm scope}
    (elementTyped : FormationSensitive.Typing R context element (sortTm elementLevel))
    (lengthTyped : FormationSensitive.Typing R context length natTm) :
    FormationSensitive.Typing R context (vecApp element length) (sortTm elementLevel) := by
  have first := FormationSensitive.Typing.appElim (constructor_typing formation context 3) elementTyped
  have second := FormationSensitive.Typing.appElim first lengthTyped
  simpa [constructor, vecType, liftClosed, rename, inst0, subst, sortTm, vecApp] using second

theorem nil_typed {R : Rules Tower.Head} (formation : ConstructorFormation R)
    {scope : Nat} {context : Tower.Ctx scope} {element : Tower.Tm scope}
    (elementTyped : FormationSensitive.Typing R context element (sortTm elementLevel)) :
    FormationSensitive.Typing R context (vnilApp element) (vecApp element zeroTm) := by
  have application := FormationSensitive.Typing.appElim (constructor_typing formation context 4) elementTyped
  simpa [constructor, vnilType, liftClosed, rename, inst0, subst, subst0,
    liftRen, liftSub, zeroTm, vecApp, vnilApp] using application

theorem cons_typed {R : Rules Tower.Head} (formation : ConstructorFormation R)
    {scope : Nat} {context : Tower.Ctx scope}
    {element length head tail : Tower.Tm scope}
    (elementTyped : FormationSensitive.Typing R context element (sortTm elementLevel))
    (lengthTyped : FormationSensitive.Typing R context length natTm) (headTyped : FormationSensitive.Typing R context head element)
    (tailTyped : FormationSensitive.Typing R context tail (vecApp element length)) :
    FormationSensitive.Typing R context (vconsApp element length head tail) (vecApp element (succApp length)) := by
  have bodyAsArrows : vconsBodyType =
      .pi natTm (arrow (.var (Fin.succ 0))
        (arrow (vecApp (.var (Fin.succ 0)) (.var 0))
          (vecApp (.var (Fin.succ 0)) (succApp (.var 0))))) := by decide +kernel
  have first := FormationSensitive.Typing.appElim (constructor_typing formation context 5) elementTyped
  have firstNormalized : FormationSensitive.Typing R context (.app (.const vconsName) element)
      (.pi natTm (arrow (rename wk element)
        (arrow (vecApp (rename wk element) (.var 0))
          (vecApp (rename wk element) (succApp (.var 0)))))) := by
    simpa [constructor, vconsType, bodyAsArrows, liftClosed, subst, liftSub] using first
  have second := FormationSensitive.Typing.appElim firstNormalized lengthTyped
  have secondNormalized : FormationSensitive.Typing R context (.app (.app (.const vconsName) element) length)
      (arrow element (arrow (vecApp element length) (vecApp element (succApp length)))) := by
    simpa only [inst0_arrow, inst0_rename_wk, inst0_vecApp, inst0_succApp, inst0_var_zero] using second
  have third := FormationSensitive.Typing.appElim secondNormalized headTyped
  have thirdNormalized : FormationSensitive.Typing R context (.app (.app (.app (.const vconsName) element) length) head)
      (arrow (vecApp element length) (vecApp element (succApp length))) := by
    simpa only [inst0_rename_wk] using third
  simpa only [vconsApp, arrow, inst0_rename_wk] using
    FormationSensitive.Typing.appElim thirdNormalized tailTyped

/-- Source vectors are formed from their actual encoded payloads. Merely
knowing a length or a carrier equivalence is not a payload typing proof. -/
theorem encode_typed {R : Rules Tower.Head} (formation : ConstructorFormation R)
    {A : Type} (element : Tower.Tm 0) (payload : A → Tower.Tm 0)
    (elementTyped : FormationSensitive.Typing R .nil element (sortTm elementLevel))
    (payloadTyped : ∀ value, FormationSensitive.Typing R .nil (payload value) element)
    {length : Natural.Carrier} (value : Vectors.Vector A length) :
    FormationSensitive.Typing R .nil (encodeVector element payload value) (vecApp element (quoteIndex length)) := by
  refine Fix.eliminate (Vectors.polynomial A) (fun environment length value =>
    FormationSensitive.Typing R .nil (Meaning.encode (Vectors.admitted A) (quoteData payload)
      (types A element).constructor environment length value) (vecApp element (quoteIndex length)))
    ?_ PUnit.unit length value
  intro environment length shape children hypotheses
  cases environment
  rcases shape with ⟨occurrence, shape⟩
  revert shape children hypotheses
  refine Fin.cases ?_ (fun occurrence => ?_) occurrence
  · intro shape _children _hypotheses
    rcases shape with ⟨⟨same⟩⟩
    cases same
    exact nil_typed formation elementTyped
  · refine Fin.cases ?_ (fun impossible => Fin.elim0 impossible) occurrence
    intro shape children hypotheses
    rcases shape with ⟨tailLength, head, ⟨⟨same⟩⟩⟩
    cases same
    exact cons_typed formation elementTyped (index_typed formation tailLength) (payloadTyped head) (hypotheses none)

theorem assignment_typed {R : Rules Tower.Head} (formation : ConstructorFormation R)
    {A : Type} (element : Tower.Tm 0) (payload : A → Tower.Tm 0)
    (elementTyped : FormationSensitive.Typing R .nil element (sortTm elementLevel))
    (payloadTyped : ∀ value, FormationSensitive.Typing R .nil (payload value) element)
    {n m : Natural.Carrier} (left : Vectors.Vector A n) (right : Vectors.Vector A m) :
    FormationSensitive.CtxMor R Programs.appendContext .nil
      (assignment element payload left right) := by
  intro index
  fin_cases index
  · exact encode_typed formation element payload elementTyped payloadTyped right
  · exact encode_typed formation element payload elementTyped payloadTyped left
  · exact index_typed formation m
  · exact index_typed formation n
  · exact elementTyped

theorem applyClosed_typing {R : Rules Tower.Head} {arity scope : Nat} {context : Tower.Ctx arity}
    {target : Tower.Ctx scope} {sigma : Sub Tower.Head arity scope} {type : Tower.Tm arity}
    {function : Tower.Tm scope}
    (typed : FormationSensitive.CtxMor R context target sigma)
    (functionTyped : FormationSensitive.Typing R target function (liftClosed (TelescopeAbstraction.closeType context type))) :
    FormationSensitive.Typing R target (TelescopeAbstraction.applyClosed context sigma function) (subst sigma type) := by
  induction context with
  | nil => simpa only [TelescopeAbstraction.applyClosed, TelescopeAbstraction.closeType,
      TelescopeAbstraction.subst_empty] using functionTyped
  | snoc prior domain ih =>
      have first := ih typed.dropNewest functionTyped
      have argument := typed 0
      simp only [Ctx.lookup_snoc_zero, TelescopeAbstraction.subst_prior] at argument
      simpa only [TelescopeAbstraction.applyClosed, subst, TelescopeAbstraction.subst_open] using
        FormationSensitive.Typing.appElim first argument

end ConstructorFormation

/-- The original reference policy retains its independently checked constructor judgments. -/
theorem referenceConstructors : ConstructorFormation Programs.rules := ⟨constructor_judgment⟩

theorem nat_formed {scope : Nat} (context : Tower.Ctx scope) :
    Typed context natTm (sortTm natLevel) := by
  exact ConstructorFormation.nat_formed referenceConstructors context

theorem zero_typed {scope : Nat} (context : Tower.Ctx scope) : Typed context zeroTm natTm := by
  exact ConstructorFormation.zero_typed referenceConstructors context

theorem succ_typed {scope : Nat} {context : Tower.Ctx scope} {number : Tower.Tm scope}
    (typed : Typed context number natTm) : Typed context (succApp number) natTm := by
  exact ConstructorFormation.succ_typed referenceConstructors typed

theorem numeral_typed {scope : Nat} (context : Tower.Ctx scope) (number : Nat) :
    Typed context (numeral number) natTm := by
  exact ConstructorFormation.numeral_typed referenceConstructors context number

theorem index_typed (number : Natural.Carrier) : Typed .nil (quoteIndex number) natTm := by
  exact ConstructorFormation.index_typed referenceConstructors number

theorem vector_formed {scope : Nat} {context : Tower.Ctx scope} {element length : Tower.Tm scope}
    (elementTyped : Typed context element (sortTm elementLevel))
    (lengthTyped : Typed context length natTm) :
    Typed context (vecApp element length) (sortTm elementLevel) := by
  exact ConstructorFormation.vector_formed referenceConstructors elementTyped lengthTyped

theorem nil_typed {scope : Nat} {context : Tower.Ctx scope} {element : Tower.Tm scope}
    (elementTyped : Typed context element (sortTm elementLevel)) :
    Typed context (vnilApp element) (vecApp element zeroTm) := by
  exact ConstructorFormation.nil_typed referenceConstructors elementTyped

theorem cons_typed {scope : Nat} {context : Tower.Ctx scope}
    {element length head tail : Tower.Tm scope}
    (elementTyped : Typed context element (sortTm elementLevel))
    (lengthTyped : Typed context length natTm) (headTyped : Typed context head element)
    (tailTyped : Typed context tail (vecApp element length)) :
    Typed context (vconsApp element length head tail) (vecApp element (succApp length)) := by
  exact ConstructorFormation.cons_typed referenceConstructors elementTyped lengthTyped headTyped tailTyped

theorem encode_typed {A : Type} (element : Tower.Tm 0) (payload : A → Tower.Tm 0)
    (elementTyped : Typed .nil element (sortTm elementLevel))
    (payloadTyped : ∀ value, Typed .nil (payload value) element)
    {length : Natural.Carrier} (value : Vectors.Vector A length) :
    Typed .nil (encodeVector element payload value) (vecApp element (quoteIndex length)) := by
  exact ConstructorFormation.encode_typed referenceConstructors element payload elementTyped payloadTyped value

theorem assignment_typed {A : Type} (element : Tower.Tm 0) (payload : A → Tower.Tm 0)
    (elementTyped : Typed .nil element (sortTm elementLevel))
    (payloadTyped : ∀ value, Typed .nil (payload value) element)
    {n m : Natural.Carrier} (left : Vectors.Vector A n) (right : Vectors.Vector A m) :
    FormationSensitive.CtxMor Programs.rules Programs.appendContext .nil
      (assignment element payload left right) := by
  exact ConstructorFormation.assignment_typed referenceConstructors element payload elementTyped payloadTyped left right

/-- The original full dependent function is applied through a derived typed
assignment, not an assumed typing statement for the completed application. -/
theorem application_typed {A : Type} (element : Tower.Tm 0) (payload : A → Tower.Tm 0)
    (elementTyped : Typed .nil element (sortTm elementLevel))
    (payloadTyped : ∀ value, Typed .nil (payload value) element)
    {n m : Natural.Carrier} (left : Vectors.Vector A n) (right : Vectors.Vector A m) :
    Typed .nil (applyArgs Programs.appendTerm [element, quoteIndex n, quoteIndex m,
      encodeVector element payload left, encodeVector element payload right])
      (vecApp element (Programs.add (quoteIndex n) (quoteIndex m))) := by
  have application := ConstructorFormation.applyClosed_typing
    (assignment_typed element payload elementTyped payloadTyped left right)
    (type := Programs.appendResult) (function := Programs.appendTerm)
    (by simpa only [TelescopeAbstraction.liftClosed_zero, Programs.appendType] using Programs.append_typed.typing)
  have result : subst (assignment element payload left right) Programs.appendResult =
      vecApp element (Programs.add (quoteIndex n) (quoteIndex m)) := by
    rw [Programs.appendResult, subst_vecApp, Programs.Computation.add_substitute]
    rfl
  rw [result] at application
  exact application

/-- The canonical output also has the application's original arithmetic
index. The conversion uses the proved addition execution; it does not
identify semantic index equality with judgmental equality by fiat. -/
theorem result_typed {A : Type} (element : Tower.Tm 0) (payload : A → Tower.Tm 0)
    (elementTyped : Typed .nil element (sortTm elementLevel))
    (payloadTyped : ∀ value, Typed .nil (payload value) element)
    {n m : Natural.Carrier} (left : Vectors.Vector A n) (right : Vectors.Vector A m) :
    Typed .nil (encodeVector element payload (Vectors.append left right))
      (vecApp element (Programs.add (quoteIndex n) (quoteIndex m))) := by
  have application := application_typed element payload elementTyped payloadTyped left right
  have universes : FormationSensitive.UniverseRegularity Programs.rules :=
    FormationSensitive.towerUniverseRegularity.includeSignature Programs.signature
  obtain ⟨level, universeWitness, formed⟩ := application.regularity universes FormationSensitive.ContextFormation.nil
  have lengthConversion : Conv Programs.rules.headEq
      (Programs.add (quoteIndex n) (quoteIndex m)) (quoteIndex (Natural.add n m))
      Programs.rules.computation :=
    Relation.EqvGen.reflTransGen_le_eqvGen _ _ _ (in_program (add_reduces n m))
  exact FormationSensitive.Typing.conv
    (encode_typed element payload elementTyped payloadTyped (Vectors.append left right))
    formed universeWitness (Conv.congApp (.refl _) (.symm _ _ lengthConversion))

/-- Actual typed inputs, a source-matching forward path, and an independently
formed result at the same dependent type. This endpoint theorem does not
claim uniform preservation of every intermediate raw reduction. -/
theorem compiled_contract (term : Tower.Tm 0)
    (compiled : AppendSource.proposedAppend = some term)
    {A : Type} (element : Tower.Tm 0) (payload : A → Tower.Tm 0)
    (elementTyped : Typed .nil element (sortTm elementLevel))
    (payloadTyped : ∀ value, Typed .nil (payload value) element)
    {n m : Natural.Carrier} (left : Vectors.Vector A n) (right : Vectors.Vector A m) :
    FormationSensitive.Judgment Programs.rules .nil
      (applyArgs term [element, quoteIndex n, quoteIndex m,
        encodeVector element payload left, encodeVector element payload right])
      (vecApp element (Programs.add (quoteIndex n) (quoteIndex m))) ∧
    ProgramExecutes (applyArgs term [element, quoteIndex n, quoteIndex m,
      encodeVector element payload left, encodeVector element payload right])
      (encodeVector element payload (Vectors.append left right)) ∧
    FormationSensitive.Judgment Programs.rules .nil
      (encodeVector element payload (Vectors.append left right))
      (vecApp element (Programs.add (quoteIndex n) (quoteIndex m))) := by
  rw [AppendSource.append_matches_reference] at compiled
  cases Option.some.inj compiled
  exact ⟨⟨.nil, application_typed element payload elementTyped payloadTyped left right⟩,
    appendTerm_program element payload left right,
    ⟨.nil, result_typed element payload elementTyped payloadTyped left right⟩⟩

#print axioms constructors_checked
#print axioms cons_typed
#print axioms encode_typed
#print axioms application_typed
#print axioms result_typed
#print axioms compiled_contract

end Mettapedia.GSLT.LanguageDef.IndexedInductive.Guest.AppendTyping
