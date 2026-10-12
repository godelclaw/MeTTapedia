import Mettapedia.Logic.HOL.TypeSubstitutionModelCoherence
import Mettapedia.Logic.HOL.DefinitionExtensionSemantics

/-!
# Witnessed type definitions in full-domain HOL models

A type definition adds the actual subtype of values satisfying a closed
predicate. Its abstraction sends values outside that subtype to the supplied
witness; representation is the inclusion. The old signature is embedded by
the existing type-derived translation. Its model reduct is the original model,
so all old-language sentences retain their truth value.

The witness is the semantic obligation discharged by the type-definition
premise. It is not an assumed model-extension or soundness interface.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HOL

universe u v w

namespace WitnessedTypeDefinition

/-- The new carrier is the actual predicate subtype. -/
abbrev Carrier {A : Type w} (predicate : A → Prop) := {x : A // predicate x}

/-- The representation map preserves the represented value. -/
def representation {A : Type w} {predicate : A → Prop}
    (value : Carrier predicate) : A := value.val

/-- A total abstraction, with its behavior outside the subtype explicit. -/
noncomputable def abstraction {A : Type w} (predicate : A → Prop)
    (witness : A) (valid : predicate witness) (value : A) : Carrier predicate := by
  classical
  exact if member : predicate value then ⟨value, member⟩ else ⟨witness, valid⟩

theorem abstraction_representation {A : Type w} (predicate : A → Prop)
    (witness : A) (valid : predicate witness) (value : Carrier predicate) :
    abstraction predicate witness valid (representation value) = value := by
  classical
  unfold abstraction representation
  split
  · exact Subtype.ext rfl
  · rename_i absent
    exact False.elim (absent value.property)

theorem predicate_iff_representation_abstraction {A : Type w}
    (predicate : A → Prop) (witness : A) (valid : predicate witness) (value : A) :
    predicate value ↔ representation (abstraction predicate witness valid value) = value := by
  classical
  by_cases member : predicate value
  · simp [abstraction, representation, member]
  · simp only [abstraction, dif_neg member, representation]
    constructor
    · exact fun impossible => False.elim (member impossible)
    · intro equal
      exact equal ▸ valid

theorem representation_injective {A : Type w} (predicate : A → Prop) :
    Function.Injective (@representation A predicate) := by
  intro left right equal
  exact Subtype.ext equal

/-- Inhabitance comes from the actual type-definition witness. -/
def inhabitant {A : Type w} (predicate : A → Prop)
    (witness : A) (valid : predicate witness) : Carrier predicate := ⟨witness, valid⟩

theorem no_empty_definition {A : Type w} :
    ¬ Nonempty (Carrier (fun _ : A => False)) := by
  rintro ⟨value⟩
  exact value.property

end WitnessedTypeDefinition

namespace TypeDefinitionModel

variable {Base : Type u} {Const : Ty Base → Type v}

/-- Freshness is structural: the old and new sorts occupy separate summands. -/
abbrev ExtendedBase (Base : Type u) := Sum Base Unit

def includeBase (base : Base) : Ty (ExtendedBase Base) := .base (.inl base)

abbrev includeType (type : Ty Base) : Ty (ExtendedBase Base) :=
  Ty.substitute includeBase type

abbrev newType : Ty (ExtendedBase Base) := .base (.inr ())

/-- The two defining functions are new symbols, distinct from every old one. -/
inductive Symbol (Const : Ty Base → Type v) (represented : Ty Base) :
    Ty (ExtendedBase Base) → Type (max u v) where
  | old {type : Ty Base} : Const type → Symbol Const represented (includeType type)
  | abstraction : Symbol Const represented (includeType represented ⇒ newType)
  | representation : Symbol Const represented (newType ⇒ includeType represented)

variable (M : HenkinModel.{u, v, w} Base Const) (represented : Ty Base)
  (predicate : Ty.denote M.Carrier represented → Prop)
  (witness : Ty.denote M.Carrier represented) (valid : predicate witness)

def carrier : ExtendedBase Base → Type (max (u + 1) w)
  | .inl base => M.Carrier base
  | .inr _ => WitnessedTypeDefinition.Carrier predicate

/-- The existing type-substitution equivalence transports old values. -/
def oldValue (type : Ty Base) :
    Ty.denote M.Carrier type ≃ Ty.denote (carrier M represented predicate) (includeType type) :=
  Ty.denoteSubstituteEquiv includeBase (carrier M represented predicate) type

noncomputable def interpret : {type : Ty (ExtendedBase Base)} →
    Symbol Const represented type → Ty.denote (carrier M represented predicate) type
  | _, .old symbol => oldValue M represented predicate _ (M.constDen symbol)
  | _, .abstraction => fun value =>
      WitnessedTypeDefinition.abstraction predicate witness valid
        ((oldValue M represented predicate represented).symm value)
  | _, .representation => fun value =>
      oldValue M represented predicate represented value.val

/-- A concrete model extension, with full function domains at every type. -/
noncomputable def model :
    HenkinModel.{u, max u v, w} (ExtendedBase Base) (Symbol Const represented) :=
  HenkinModel.standard (carrier M represented predicate)
    (interpret M represented predicate witness valid)

theorem fullDomains : (model M represented predicate witness valid).FullDomains :=
  HenkinModel.fullDomains_standard _ _

/-- Forgetting the new sort and its two maps recovers the original full model. -/
theorem reduct_eq (full : M.FullDomains) :
    HenkinModel.standardTypeReduct includeBase Symbol.old
      (model M represented predicate witness valid) = M := by
  calc
    _ = HenkinModel.standard M.Carrier M.constDen := by
      apply HenkinModel.standard_ext rfl
      intro type symbol
      apply heq_of_eq
      exact (oldValue M represented predicate type).symm_apply_apply (M.constDen symbol)
    _ = M := HenkinModel.standard_eq_of_fullDomains M full

/-- Every old-language sentence, including higher-type quantifiers, retains
its truth value in the constructed extension. -/
theorem models_include (full : M.FullDomains) (sentence : ClosedFormula Const) :
    (model M represented predicate witness valid).models
      (mapTypes includeBase Symbol.old sentence) ↔ M.models sentence := by
  have preservation := HenkinModel.models_mapTypes includeBase Symbol.old
    (model M represented predicate witness valid)
    (fullDomains M represented predicate witness valid) sentence
  rw [reduct_eq M represented predicate witness valid full] at preservation
  exact preservation.symm

/-- The actual abstraction and representation satisfy the first source law. -/
theorem abstraction_representation (value : WitnessedTypeDefinition.Carrier predicate) :
    (model M represented predicate witness valid).constDen Symbol.abstraction
      ((model M represented predicate witness valid).constDen Symbol.representation value) =
        value := by
  change WitnessedTypeDefinition.abstraction predicate witness valid
    ((oldValue M represented predicate represented).symm
      (oldValue M represented predicate represented value.val)) = value
  rw [(oldValue M represented predicate represented).symm_apply_apply]
  exact WitnessedTypeDefinition.abstraction_representation predicate witness valid value

/-- The second source law characterizes exactly the represented predicate. -/
theorem predicate_iff_representation_abstraction
    (value : Ty.denote (carrier M represented predicate) (includeType represented)) :
    predicate ((oldValue M represented predicate represented).symm value) ↔
      (model M represented predicate witness valid).constDen Symbol.representation
        ((model M represented predicate witness valid).constDen Symbol.abstraction value) =
          value := by
  change predicate ((oldValue M represented predicate represented).symm value) ↔
    oldValue M represented predicate represented
      (WitnessedTypeDefinition.representation
        (WitnessedTypeDefinition.abstraction predicate witness valid
          ((oldValue M represented predicate represented).symm value))) = value
  have law := WitnessedTypeDefinition.predicate_iff_representation_abstraction
    predicate witness valid ((oldValue M represented predicate represented).symm value)
  constructor
  · intro member
    exact (congrArg (oldValue M represented predicate represented) (law.mp member)).trans
      ((oldValue M represented predicate represented).apply_symm_apply value)
  · intro equal
    exact law.mpr ((oldValue M represented predicate represented).injective
      (equal.trans ((oldValue M represented predicate represented).apply_symm_apply value).symm))

/-- The first defining equation as an actual closed object-HOL sentence. -/
def abstractionRepresentationLaw : ClosedFormula (Symbol Const represented) :=
  .all (.eq
    (.app (.const Symbol.abstraction) (.app (.const Symbol.representation) (.var .vz)))
    (.var .vz : Term (Symbol Const represented) [newType] newType))

theorem models_abstractionRepresentationLaw :
    (model M represented predicate witness valid).models
      (abstractionRepresentationLaw (Const := Const) represented) := by
  change ∀ value, (model M represented predicate witness valid).adm newType value →
    (model M represented predicate witness valid).constDen Symbol.abstraction
      ((model M represented predicate witness valid).constDen Symbol.representation value) = value
  intro value _
  exact abstraction_representation M represented predicate witness valid value

/-- Old closed terms retain their denotations through the carrier equivalence,
including predicates used to admit a new type. -/
theorem denote_include_closed (full : M.FullDomains) {type : Ty Base}
    (term : ClosedTerm Const type) :
    (model M represented predicate witness valid).denote
      (mapTypes includeBase Symbol.old term) (fun index => nomatch index) =
      oldValue M represented predicate type
        (M.denote term (fun index => nomatch index)) := by
  have preservation := HenkinModel.denote_mapTypes includeBase Symbol.old
    (model M represented predicate witness valid)
    (fullDomains M represented predicate witness valid) term
    (fun index => nomatch index)
  have emptyValuation :
      (fun {a} (index : Var [] a) =>
        HenkinModel.typeReductValuation includeBase Symbol.old
          (model M represented predicate witness valid) (Γ := [])
          (fun index => nomatch index) index) =
      (fun {a} (index : Var [] a) => nomatch index) := by
    funext type index
    nomatch index
  rw [emptyValuation] at preservation
  have respectsModelEquality (left right : HenkinModel.{u, v, w} Base Const)
      (equal : left = right) :
      HEq (left.denote term (fun index => nomatch index))
        (right.denote term (fun index => nomatch index)) := by
    cases equal
    rfl
  have oldDenotation := eq_of_heq (respectsModelEquality
    (HenkinModel.standardTypeReduct includeBase Symbol.old
      (model M represented predicate witness valid)) M
    (reduct_eq M represented predicate witness valid full))
  exact preservation.symm.trans (congrArg (oldValue M represented predicate type) oldDenotation)

/-- The included predicate has an explicit function type in the new signature. -/
def includePredicate (body : ClosedTerm Const (represented ⇒ .prop)) :
    ClosedTerm (Symbol Const represented) (includeType represented ⇒ .prop) :=
  mapTypes includeBase Symbol.old body

/-- Close the pointwise second source equation by function abstraction. It
uses the actual old-language predicate, without adding a predicate symbol. -/
def representationAbstractionLaw
    (body : ClosedTerm Const (represented ⇒ .prop)) :
    ClosedFormula (Symbol Const represented) :=
  .eq (includePredicate represented body)
    (.lam
    (.eq
      (.app (.const Symbol.representation) (.app (.const Symbol.abstraction) (.var .vz)))
      (.var .vz : Term (Symbol Const represented) [includeType represented]
        (includeType represented))))

/-- Extract the predicate represented by a closed HOL predicate term. -/
def predicateOf (body : ClosedTerm Const (represented ⇒ .prop)) :
    Ty.denote M.Carrier represented → Prop :=
  fun value => (M.denote body (fun index => nomatch index) value).down

set_option backward.isDefEq.respectTransparency false in
/-- A witnessed source predicate validates its second defining equation in
the constructed model. The proof joins weakening, type-derived interpretation,
and the actual subtype's representation/abstraction law. -/
theorem models_representationAbstractionLaw
    (full : M.FullDomains) (body : ClosedTerm Const (represented ⇒ .prop))
    (sourceWitness : Ty.denote M.Carrier represented)
    (sourceValid : predicateOf M represented body sourceWitness) :
    (model M represented (predicateOf M represented body) sourceWitness sourceValid).models
      (representationAbstractionLaw represented body) := by
  let extension := model M represented (predicateOf M represented body) sourceWitness sourceValid
  simp only [representationAbstractionLaw, HenkinModel.models, PreModel.models,
    PreModel.denote, PreModel.Eqv, PreModel.extend]
  intro value _
  have transport := denote_include_closed M represented (predicateOf M represented body)
    sourceWitness sourceValid full body
  have predicateEquality :
      (extension.denote (includePredicate represented body) (fun index => nomatch index) value).down =
      predicateOf M represented body
        ((oldValue M represented (predicateOf M represented body) represented).symm value) :=
    congrArg (fun function : Ty.denote extension.Carrier (includeType represented ⇒ .prop) =>
      (function value).down) transport
  have law := predicate_iff_representation_abstraction M represented
    (predicateOf M represented body) sourceWitness sourceValid value
  have equalityLaw :
      predicateOf M represented body
        ((oldValue M represented (predicateOf M represented body) represented).symm value) ↔
      extension.Eqv (includeType represented)
        (extension.constDen Symbol.representation
          (extension.constDen Symbol.abstraction value)) value := by
    constructor
    · intro member
      rw [law.mp member]
      exact extension.eqv_refl
        (fullDomains M represented (predicateOf M represented body) sourceWitness sourceValid _ value)
    · intro equal
      exact law.mpr (extension.eq_of_eqv_of_fullDomains
        (fullDomains M represented (predicateOf M represented body) sourceWitness sourceValid) equal)
  convert (Iff.of_eq predicateEquality).trans equalityLaw using 1
  apply Iff.of_eq
  dsimp only [extension]
  have emptyUnique (left right : extension.Valuation []) : @left = @right := by
    funext type index
    nomatch index
  exact congrArg (fun valuation : extension.Valuation [] =>
    (extension.denote (includePredicate represented body) valuation value).down) (emptyUnique _ _)

/-- The universal closure of HOL Light's actual pointwise second result,
with the predicate on the left of the Boolean equality. -/
def representationAbstractionPointwiseLaw
    (body : ClosedTerm Const (represented ⇒ .prop)) :
    ClosedFormula (Symbol Const represented) :=
  .all (.eq
    (.app (weaken (includePredicate represented body)) (.var .vz))
    (.eq
      (.app (.const Symbol.representation) (.app (.const Symbol.abstraction) (.var .vz)))
      (.var .vz : Term (Symbol Const represented) [includeType represented]
        (includeType represented))))

set_option backward.isDefEq.respectTransparency false in
/-- The actual extension validates the source's pointwise equation as well
as its functional closure. Weakening cannot capture the closed predicate. -/
theorem models_representationAbstractionPointwiseLaw
    (full : M.FullDomains) (body : ClosedTerm Const (represented ⇒ .prop))
    (sourceWitness : Ty.denote M.Carrier represented)
    (sourceValid : predicateOf M represented body sourceWitness) :
    (model M represented (predicateOf M represented body) sourceWitness sourceValid).models
      (representationAbstractionPointwiseLaw represented body) := by
  let extension := model M represented (predicateOf M represented body) sourceWitness sourceValid
  have functional := models_representationAbstractionLaw M represented full body sourceWitness sourceValid
  simp only [representationAbstractionLaw, HenkinModel.models, PreModel.models,
    PreModel.denote, PreModel.Eqv, PreModel.extend] at functional
  simp only [representationAbstractionPointwiseLaw, HenkinModel.models, PreModel.models,
    PreModel.denote, PreModel.Eqv, PreModel.extend]
  intro value admissible
  let emptyValuation : extension.Valuation [] := fun index => nomatch index
  have weakened := extension.denote_weakenCtx [includeType represented]
    (includePredicate represented body) (extension.extend emptyValuation value)
  simp only [weakenCtx_cons, weakenCtx_nil] at weakened
  have observed := congrArg
    (fun function : Ty.denote extension.Carrier (includeType represented ⇒ .prop) =>
      (function value).down) weakened
  refine (Iff.of_eq ?_).trans (functional value admissible)
  convert observed using 1
  · apply Iff.of_eq
    exact congrArg (fun valuation : extension.Valuation [includeType represented] =>
      (extension.denote (weaken (includePredicate represented body)) valuation value).down)
      (by
        funext type index
        cases index with
        | vz => rfl
        | vs index => nomatch index)
  · apply Iff.of_eq
    exact congrArg (fun valuation : extension.Valuation [] =>
      (extension.denote (includePredicate represented body) valuation value).down)
      (by funext type index; nomatch index)

/-- A successful definition supplies the new base inhabitant. All other
base inhabitants are retained from the old model. -/
noncomputable def inhabitedDomains (old : M.InhabitedDomains) :
    (model M represented predicate witness valid).InhabitedDomains :=
  (model M represented predicate witness valid).inhabitedDomains_of_fullDomains
    (fullDomains M represented predicate witness valid)
    (fun base => match base with
      | .inl oldBase => old.witness (.base oldBase)
      | .inr _ => ⟨witness, valid⟩)

/-- Choice on new and old simple types is constructed in the full-domain
extension from its actual inhabitants. -/
noncomputable def choice (old : M.InhabitedDomains) :
    (model M represented predicate witness valid).HilbertChoice :=
  HenkinModel.HilbertChoice.ofFullInhabitedDomains
    (fullDomains M represented predicate witness valid)
    (inhabitedDomains M represented predicate witness valid old)

/-- The old infinite carrier, injection and omitted point survive adding the
new predicate subtype. No infinity obligation is assumed for the new sort. -/
noncomputable def infinity {base : Base} (old : M.DedekindInfinityWitness base) :
    (model M represented predicate witness valid).DedekindInfinityWitness (.inl base) where
  successor := old.successor
  successor_admissible := fullDomains M represented predicate witness valid _ _
  successor_injective := old.successor_injective
  omitted := old.omitted
  omitted_not_image := old.omitted_not_image

end TypeDefinitionModel

end Mettapedia.Logic.HOL
