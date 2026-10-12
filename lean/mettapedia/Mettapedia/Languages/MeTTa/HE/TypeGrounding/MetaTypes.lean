import Mettapedia.Languages.MeTTa.HE.Spec.Eval
import Mettapedia.Logic.HOL.Semantics.Henkin

/-!
# HE meta-types as HOL predicates over a base type of atoms

HE's meta-types `Symbol`, `Variable`, `Grounded` and `Expression` classify an
atom by its syntactic shape, and `Atom` admits every atom.  They are not types
of HOL terms: they are predicates on one base type `atom` whose elements are
atoms.

The HOL signature `MetaConst` has one base type, quotation constants for
symbols, variables and grounded values, the empty expression `nil`, the
element-prepending constructor `cons`, and one classification predicate for
each meta-type.  `quote` writes every HE atom as a closed HOL term of type
`atom`, and `metaFormula m t` is the HOL formula "`t` has meta-type `m`"
(`⊤` for `Atom`).  `MetaAxiom` is the classification theory: every quoted
leaf and every `nil` or `cons` application lies in its own class and in no
other.

`metaAccepts_iff_entailed`: HE's meta-type acceptance (`Atom`, or the atom's
own meta-type) holds exactly when the classification theory entails the HOL
formula in every Henkin model, and `metaRejects_iff_entailed`: it fails
exactly when the theory entails the negation.  The meta-type relation used is
the spec's `MetaTypeRel`.
-/

namespace Mettapedia.Languages.MeTTa.HE.TypeGrounding.MetaTypes

open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)
open Mettapedia.Logic.HOL
open Spec.Eval

/-! ## The HOL signature of atom classification -/

/-- The four syntactic classes of atoms. -/
inductive MetaClass where
  | symbol
  | variable
  | grounded
  | expression
  deriving DecidableEq, Repr

/-- The meta-type symbol of a class. -/
def MetaClass.type : MetaClass → Atom
  | .symbol => Atom.symbolType
  | .variable => Atom.variableType
  | .grounded => Atom.groundedType
  | .expression => Atom.expressionType

/-- The class of an atom. -/
def classOf : Atom → MetaClass
  | .symbol _ => .symbol
  | .var _ => .variable
  | .grounded _ => .grounded
  | .expression _ => .expression

/-- The one base type: atoms. -/
abbrev atomTy : Ty Unit := .base ()

/-- Constants of the classification signature. -/
inductive MetaConst : Ty Unit → Type where
  | leaf (atom : Atom) : MetaConst atomTy
  | nil : MetaConst atomTy
  | cons : MetaConst (.arr atomTy (.arr atomTy atomTy))
  | classify (kind : MetaClass) : MetaConst (.arr atomTy .prop)

/-- Leaves are the non-expression atoms. -/
def IsLeaf (atom : Atom) : Prop := ∀ atoms, atom ≠ .expression atoms

mutual

/-- The closed HOL term of type `atom` that writes an HE atom. -/
def quote : Atom → Term MetaConst [] atomTy
  | .symbol name => .const (.leaf (.symbol name))
  | .var name => .const (.leaf (.var name))
  | .grounded value => .const (.leaf (.grounded value))
  | .expression atoms => quoteList atoms

/-- The closed HOL term of the expression with the given elements. -/
def quoteList : List Atom → Term MetaConst [] atomTy
  | [] => .const .nil
  | atom :: atoms => .app (.app (.const .cons) (quote atom)) (quoteList atoms)

end

/-- HE meta-type names: `Atom` and the four classes. -/
inductive MetaTypeName where
  | atom
  | ofClass (kind : MetaClass)
  deriving DecidableEq, Repr

/-- The HE symbol of a meta-type name. -/
def MetaTypeName.type : MetaTypeName → Atom
  | .atom => Atom.atomType
  | .ofClass kind => kind.type

/-- "`term` has meta-type `name`" as a HOL formula. -/
def metaFormula : MetaTypeName → Term MetaConst [] atomTy → ClosedFormula MetaConst
  | .atom, _ => .top
  | .ofClass kind, term => .app (.const (.classify kind)) term

/-! ## The classification theory -/

/-- `∀ x y, P (cons x y)` for a predicate `P` on atoms. -/
def forallCons (predicate : Term MetaConst [atomTy, atomTy] (.arr atomTy .prop)) :
    ClosedFormula MetaConst :=
  .all (.all (.app predicate (.app (.app (.const .cons) (.var (.vs .vz))) (.var .vz))))

/-- The classification theory: each leaf, `nil` and each `cons` lies in
exactly its own class. -/
inductive MetaAxiom : ClosedFormula MetaConst → Prop where
  | leafIn (atom : Atom) : IsLeaf atom →
      MetaAxiom (.app (.const (.classify (classOf atom))) (.const (.leaf atom)))
  | leafOut (atom : Atom) (kind : MetaClass) : IsLeaf atom → kind ≠ classOf atom →
      MetaAxiom (.not (.app (.const (.classify kind)) (.const (.leaf atom))))
  | nilIn : MetaAxiom (.app (.const (.classify .expression)) (.const .nil))
  | nilOut (kind : MetaClass) : kind ≠ .expression →
      MetaAxiom (.not (.app (.const (.classify kind)) (.const .nil)))
  | consIn : MetaAxiom (forallCons (.const (.classify .expression)))
  | consOut (kind : MetaClass) : kind ≠ .expression →
      MetaAxiom (.all (.all (.not (.app (.const (.classify kind))
        (.app (.app (.const .cons) (.var (.vs .vz))) (.var .vz))))))

/-- Semantic consequence of the classification theory over Henkin models. -/
def Entailed (formula : ClosedFormula MetaConst) : Prop :=
  ∀ model : HenkinModel.{0, 0, 0} Unit MetaConst,
    (∀ axiomFormula, MetaAxiom axiomFormula → model.models axiomFormula) →
      model.models formula

/-- HE's meta-type acceptance: `Atom` admits every atom, and each class
admits the atoms of that class. -/
def MetaAccepts (atom : Atom) (name : MetaTypeName) : Prop :=
  name.type = Atom.atomType ∨ MetaTypeRel atom name.type

/-! ## Facts about classes -/

theorem metaTypeRel_classOf (atom : Atom) : MetaTypeRel atom (classOf atom).type := by
  cases atom <;> constructor

theorem MetaClass.type_injective : Function.Injective MetaClass.type := by
  intro left right equal
  cases left <;> cases right <;> first
    | rfl
    | simp [MetaClass.type, Atom.symbolType, Atom.variableType, Atom.groundedType,
        Atom.expressionType] at equal

theorem metaTypeRel_iff_classOf (atom : Atom) (kind : MetaClass) :
    MetaTypeRel atom kind.type ↔ classOf atom = kind := by
  constructor
  · intro related
    exact MetaClass.type_injective (MetaTypeRel.eq (metaTypeRel_classOf atom) related)
  · rintro rfl
    exact metaTypeRel_classOf atom

theorem classType_ne_atomType (kind : MetaClass) : kind.type ≠ Atom.atomType := by
  cases kind <;> simp [MetaClass.type, Atom.symbolType, Atom.variableType,
    Atom.groundedType, Atom.expressionType, Atom.atomType]

theorem metaAccepts_ofClass_iff (atom : Atom) (kind : MetaClass) :
    MetaAccepts atom (.ofClass kind) ↔ classOf atom = kind := by
  rw [MetaAccepts, MetaTypeName.type, ← metaTypeRel_iff_classOf]
  simp [classType_ne_atomType]

/-! ## Truth of quotations in models of the theory -/

section Models

variable (model : HenkinModel.{0, 0, 0} Unit MetaConst)

/-- Valuations of the empty context are unique. -/
private theorem leaf_symbol (name : String) : IsLeaf (.symbol name) :=
  fun _ equal => Atom.noConfusion equal

private theorem leaf_var (name : String) : IsLeaf (.var name) :=
  fun _ equal => Atom.noConfusion equal

private theorem leaf_grounded (value : GroundedValue) : IsLeaf (.grounded value) :=
  fun _ equal => Atom.noConfusion equal

/-- In every model of the theory, a quoted atom lies in its own class. -/
theorem models_own_class
    (axioms : ∀ axiomFormula, MetaAxiom axiomFormula → model.models axiomFormula)
    (atom : Atom) :
    model.models (.app (.const (.classify (classOf atom))) (quote atom)) := by
  cases atom with
  | symbol name => exact axioms _ (.leafIn (.symbol name) (leaf_symbol name))
  | var name => exact axioms _ (.leafIn (.var name) (leaf_var name))
  | grounded value => exact axioms _ (.leafIn (.grounded value) (leaf_grounded value))
  | expression atoms =>
      cases atoms with
      | nil => exact axioms _ .nilIn
      | cons head tail =>
          have consAxiom := axioms _ .consIn
          simp only [HenkinModel.models, PreModel.models, forallCons,
            PreModel.denote, PreModel.extend] at consAxiom
          simp only [HenkinModel.models, PreModel.models, quote, quoteList,
            PreModel.denote, classOf]
          refine consAxiom _ ?_ _ ?_ <;>
            · apply model.denote_admissible
              intro type index
              cases index

/-- In every model of the theory, a quoted atom lies in no other class. -/
theorem models_other_class
    (axioms : ∀ axiomFormula, MetaAxiom axiomFormula → model.models axiomFormula)
    (atom : Atom) (kind : MetaClass) (other : kind ≠ classOf atom) :
    model.models (.not (.app (.const (.classify kind)) (quote atom))) := by
  cases atom with
  | symbol name => exact axioms _ (.leafOut (.symbol name) kind (leaf_symbol name) other)
  | var name => exact axioms _ (.leafOut (.var name) kind (leaf_var name) other)
  | grounded value =>
      exact axioms _ (.leafOut (.grounded value) kind (leaf_grounded value) other)
  | expression atoms =>
      cases atoms with
      | nil => exact axioms _ (.nilOut kind other)
      | cons head tail =>
          have consAxiom := axioms _ (.consOut kind other)
          simp only [HenkinModel.models, PreModel.models,
            PreModel.denote, PreModel.extend] at consAxiom
          simp only [HenkinModel.models, PreModel.models, quote, quoteList,
            PreModel.denote]
          refine consAxiom _ ?_ _ ?_ <;>
            · apply model.denote_admissible
              intro type index
              cases index

end Models

/-! ## The standard model: atoms themselves -/

/-- Prepend an element to an expression; a non-expression tail is read as a
one-element expression so that the operation is total. -/
def consAtom (head tail : Atom) : Atom :=
  match tail with
  | .expression atoms => .expression (head :: atoms)
  | other => .expression [head, other]

/-- The standard model: the base type denotes the atoms, quotations denote
themselves, and each classifier is the class test. -/
def standardModel : HenkinModel.{0, 0, 0} Unit MetaConst :=
  HenkinModel.standard (fun _ => ULift.{1} Atom) fun {type} constant =>
    match type, constant with
    | _, .leaf atom => ULift.up atom
    | _, .nil => ULift.up (.expression [])
    | _, .cons => fun head tail => ULift.up (consAtom head.down tail.down)
    | _, .classify kind => fun atom => ULift.up (classOf atom.down = kind)

mutual

theorem standard_quote (atom : Atom) (valuation : HenkinModel.Valuation standardModel []) :
    standardModel.denote (quote atom) valuation = ULift.up atom := by
  cases atom with
  | symbol name => rfl
  | var name => rfl
  | grounded value => rfl
  | expression atoms =>
      simp only [quote]
      exact standard_quoteList atoms valuation

theorem standard_quoteList (atoms : List Atom)
    (valuation : HenkinModel.Valuation standardModel []) :
    standardModel.denote (quoteList atoms) valuation =
      ULift.up (.expression atoms) := by
  cases atoms with
  | nil => rfl
  | cons head tail =>
      have headEq := standard_quote head valuation
      have tailEq := standard_quoteList tail valuation
      simp only [quoteList, HenkinModel.denote, PreModel.denote] at headEq tailEq ⊢
      rw [headEq, tailEq]
      rfl

end

/-- In the standard model a classification formula holds exactly when the
quoted atom has that class. -/
theorem standard_models_classify (kind : MetaClass) (atom : Atom) :
    standardModel.models (.app (.const (.classify kind)) (quote atom)) ↔
      classOf atom = kind := by
  simp only [HenkinModel.models, PreModel.models, PreModel.denote]
  change classOf (standardModel.denote (quote atom) _).down = kind ↔ _
  rw [standard_quote]

theorem standardModel_axioms :
    ∀ axiomFormula, MetaAxiom axiomFormula → standardModel.models axiomFormula := by
  intro axiomFormula axiomRule
  cases axiomRule with
  | leafIn atom leaf =>
      cases atom with
      | symbol name => rfl
      | var name => rfl
      | grounded value => rfl
      | expression atoms => exact absurd rfl (leaf atoms)
  | leafOut atom kind leaf other =>
      simp only [HenkinModel.models, PreModel.models, PreModel.denote_not]
      intro holds
      exact other (by
        cases atom with
        | symbol name => exact (of_eq_true (eq_true holds)).symm
        | var name => exact (of_eq_true (eq_true holds)).symm
        | grounded value => exact (of_eq_true (eq_true holds)).symm
        | expression atoms => exact absurd rfl (leaf atoms))
  | nilIn => rfl
  | nilOut kind other =>
      simp only [HenkinModel.models, PreModel.models, PreModel.denote_not]
      intro holds
      exact other (of_eq_true (eq_true holds)).symm
  | consIn =>
      simp only [HenkinModel.models, PreModel.models, forallCons, PreModel.denote_all]
      intro head _ tail _
      show classOf (consAtom head.down tail.down) = MetaClass.expression
      unfold consAtom
      split <;> rfl
  | consOut kind other =>
      simp only [HenkinModel.models, PreModel.models, PreModel.denote_all,
        PreModel.denote_not]
      intro head _ tail _ holds
      apply other
      have classEq : classOf (consAtom head.down tail.down) = kind := holds
      rw [← classEq]
      unfold consAtom
      split <;> rfl

/-! ## Agreement -/

/-- **HE's meta-type acceptance is entailment in the classification
theory.**  An atom is accepted at a meta-type exactly when every Henkin model
of the theory satisfies the HOL formula. -/
theorem metaAccepts_iff_entailed (atom : Atom) (name : MetaTypeName) :
    MetaAccepts atom name ↔ Entailed (metaFormula name (quote atom)) := by
  cases name with
  | atom =>
      refine iff_of_true (Or.inl rfl) ?_
      intro model _
      exact HenkinModel.models_top model
  | ofClass kind =>
      rw [metaAccepts_ofClass_iff]
      constructor
      · rintro rfl model axioms
        exact models_own_class model axioms atom
      · intro entailed
        exact (standard_models_classify kind atom).mp
          (entailed standardModel standardModel_axioms)

/-- **HE's meta-type rejection is entailment of the negation.** -/
theorem metaRejects_iff_entailed (atom : Atom) (name : MetaTypeName) :
    ¬MetaAccepts atom name ↔ Entailed (.not (metaFormula name (quote atom))) := by
  cases name with
  | atom =>
      refine iff_of_false (fun rejected => rejected (Or.inl rfl)) ?_
      intro entailed
      have holds := entailed standardModel standardModel_axioms
      rw [HenkinModel.models_not] at holds
      exact holds (HenkinModel.models_top standardModel)
  | ofClass kind =>
      rw [metaAccepts_ofClass_iff]
      constructor
      · intro other model axioms
        exact models_other_class model axioms atom kind (Ne.symm other)
      · intro entailed same
        have holds := entailed standardModel standardModel_axioms
        rw [HenkinModel.models_not] at holds
        exact holds ((standard_models_classify kind atom).mpr same)

/-! ## Boundary examples -/

/-- Positive: `(a b)` is accepted at `Expression` and at `Atom`. -/
example : MetaAccepts (.expression [.symbol "a", .symbol "b"]) (.ofClass .expression) ∧
    MetaAccepts (.expression [.symbol "a", .symbol "b"]) .atom :=
  ⟨(metaAccepts_ofClass_iff _ _).mpr rfl, Or.inl rfl⟩

/-- Negative: `(a b)` is rejected at `Symbol`, and the theory entails it. -/
theorem expression_not_symbol :
    Entailed (.not (metaFormula (.ofClass .symbol)
      (quote (.expression [.symbol "a", .symbol "b"])))) :=
  (metaRejects_iff_entailed _ _).mp (by
    rw [metaAccepts_ofClass_iff]
    simp [classOf])

#print axioms metaAccepts_iff_entailed
#print axioms metaRejects_iff_entailed

end Mettapedia.Languages.MeTTa.HE.TypeGrounding.MetaTypes
