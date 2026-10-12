import Mettapedia.Languages.MeTTa.HE.TypeGrounding.Fragment
import Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.Completeness
import Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.MatchSolutionTheory
import Mettapedia.Languages.MeTTa.HE.LeaTTaTypePresentationSelectionConformance
import Mettapedia.Languages.MeTTa.HE.LeaTTaTypePresentationExactConformance
import MettaHyperonFull.Proofs.Gradual
import Mettapedia.Logic.TheoryModel.Consistency

/-!
# `%Undefined%` as the unknown type of Abstracting Gradual Typing

In "Abstracting Gradual Typing" (POPL 2016) a gradual type denotes the set
of static types it may stand for, and two gradual types are consistent when
those sets share a type.  HE's `%Undefined%` is the unknown type `?` of that
reading:

* `Concretizes G T` is the concretization `T ∈ γ(G)`: replace every
  `%Undefined%` in `G` by a static atom;
* read as satisfaction (`Concretization T G`), it makes `G₁` and `G₂`
  consistent when the theory `{G₁, G₂}` has a model,
  `TheoryModel.Consistent Concretization {G₁, G₂}`: `γ(G₁) ∩ γ(G₂) ≠ ∅`.

On variable-free types:

* `reducedTypeConsistent_iff_agt`: HE's recursive reduced-type consistency
  (the spec's R2 refinement) is exactly AGT consistency;
* `corePlusR2Consistent_iff_top`: adding HE's top-level `Atom` wildcard is
  AGT consistency for a concretization in which a top-level `Atom` stands for
  every static atom, while a nested `Atom` stays an ordinary symbol;
* `presentation_iff_top`: HE's finite-presentation matcher succeeds exactly
  on AGT-consistent pairs;
* `leattaMatchType_iff_top`: so does the executable matcher of the external
  LeaTTa interpreter.  Its gradual permissiveness theorems
  (`Metta.matchType_undefined_left` and its siblings) are the instances in
  which one side is `%Undefined%` or `Atom` (`gradual_permissiveness_is_agt`).

On static types AGT consistency is equality (`agt_static_iff_eq`): the
conservative-extension property of gradual typing.  Consistency is not
transitive (`agt_not_transitive`).

The declarative relation `Metta.Consistent` of the external package accepts
`Atom` at every depth.  HE's runtime, the spec and the executable matcher do
not (`metta_consistent_nested_atom_not_agt`).
-/

namespace Mettapedia.Languages.MeTTa.HE.TypeGrounding.Gradual

open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)
open Spec.Type
open Spec.Type.Presentation
open Spec.Type.Presentation.Theory
open Spec.Type.Presentation.Completeness
open Spec.Type.Presentation.MatchSolutionTheory
open Spec.Type.RuntimeRefinement
open LeaTTaBridge
open LeaTTaTypePresentationFoldConformance
open LeaTTaTypePresentationSelectionConformance
open LeaTTaTypePresentationExactConformance
open Mettapedia.Logic.TheoryModel (Consistent consistent_pair_iff)

/-! ## Concretization -/

/-- Static atoms: no type variable and no `%Undefined%`. -/
def StaticAtom (atom : Atom) : Prop :=
  TypeSubst.typeVars atom = [] ∧ UndefinedFree atom

/-- Concretization `T ∈ γ(G)` of a variable-free gradual type: every
`%Undefined%` may stand for any static atom, every other leaf for itself. -/
inductive Concretizes : Atom → Atom → Prop where
  | unknown {static : Atom} : StaticAtom static → Concretizes Atom.undefinedType static
  | symbol {name : String} : name ≠ "%Undefined%" →
      Concretizes (.symbol name) (.symbol name)
  | grounded (value : GroundedValue) : Concretizes (.grounded value) (.grounded value)
  | expression {gradual static : List Atom} :
      List.Forall₂ Concretizes gradual static →
      Concretizes (.expression gradual) (.expression static)

/-- Concretization read as satisfaction: a static atom satisfies every
gradual type it concretizes.  Two gradual types are AGT-consistent when they
are consistent for it, `Consistent Concretization {left, right}`. -/
abbrev Concretization (static gradual : Atom) : Prop :=
  Concretizes gradual static

/-- Concretization at the top of a type match: a top-level `Atom` stands for
every static atom; below the top `Atom` is an ordinary symbol. -/
def TopConcretizes (gradual static : Atom) : Prop :=
  (gradual = Atom.atomType ∧ StaticAtom static) ∨ Concretizes gradual static

/-- Top-level concretization read as satisfaction. -/
abbrev TopConcretization (static gradual : Atom) : Prop :=
  TopConcretizes gradual static

/-! ## Variable-free atoms -/

private theorem typeVars_expression (atoms : List Atom) :
    TypeSubst.typeVars (.expression atoms) = TypeSubst.typeVarsList atoms := by
  simp [TypeSubst.typeVars]

private theorem typeVarsList_cons (atom : Atom) (atoms : List Atom) :
    TypeSubst.typeVarsList (atom :: atoms) =
      TypeSubst.typeVars atom ++ TypeSubst.typeVarsList atoms := by
  simp [TypeSubst.typeVarsList]

/-- A homomorphic valuation fixes a variable-free atom. -/
theorem applyTypeValuation_of_typeVars_nil (valuation : String → Atom) (atom : Atom)
    (ground : TypeSubst.typeVars atom = []) : applyTypeValuation valuation atom = atom := by
  induction atom using Atom.rec (motive_2 := fun atoms =>
      TypeSubst.typeVarsList atoms = [] →
        atoms.map (applyTypeValuation valuation) = atoms) with
  | symbol name => simp [applyTypeValuation]
  | var name => simp [TypeSubst.typeVars] at ground
  | grounded value => simp [applyTypeValuation]
  | expression atoms ih =>
      rw [typeVars_expression] at ground
      simp [applyTypeValuation, ih ground]
  | nil => rfl
  | cons head tail headIH tailIH =>
      rename_i ground
      rw [typeVarsList_cons, List.append_eq_nil_iff] at ground
      simp [headIH ground.1, tailIH ground.2]

theorem StaticAtom.symbol {name : String} (notUndefined : name ≠ "%Undefined%") :
    StaticAtom (.symbol name) := by
  refine ⟨rfl, fun occurs => notUndefined ?_⟩
  have equal := occurs.symbol_eq
  simp only [Atom.undefinedType, Atom.symbol.injEq] at equal
  exact equal.symm

theorem StaticAtom.grounded (value : GroundedValue) : StaticAtom (.grounded value) := by
  refine ⟨rfl, fun occurs => ?_⟩
  have equal := occurs.grounded_eq
  simp [Atom.undefinedType] at equal

theorem StaticAtom.expression_iff {atoms : List Atom} :
    StaticAtom (.expression atoms) ↔ ∀ atom ∈ atoms, StaticAtom atom := by
  rw [StaticAtom, typeVars_expression]
  constructor
  · rintro ⟨ground, free⟩ atom member
    refine ⟨?_, free.of_child member⟩
    induction atoms with
    | nil => simp at member
    | cons head tail ih =>
        rw [typeVarsList_cons, List.append_eq_nil_iff] at ground
        simp only [List.mem_cons] at member
        rcases member with rfl | member
        · exact ground.1
        · exact ih ground.2
            (fun occurs => by
              rcases occurs.expression_cases with equal | ⟨child, childMember, inner⟩
              · cases equal
              · exact free (.child (List.mem_cons_of_mem _ childMember) inner))
            member
  · intro all
    refine ⟨?_, ?_⟩
    · induction atoms with
      | nil => rfl
      | cons head tail ih =>
          rw [typeVarsList_cons, (all head (by simp)).1,
            ih (fun atom member => all atom (List.mem_cons_of_mem _ member))]
          rfl
    · intro occurs
      rcases occurs.expression_cases with equal | ⟨child, member, inner⟩
      · cases equal
      · exact (all child member).2 inner

/-! ## Basic facts about concretization -/

/-- Every concretization is static. -/
theorem Concretizes.static {gradual static : Atom} (concrete : Concretizes gradual static) :
    StaticAtom static := by
  induction gradual using Atom.rec (motive_2 := fun gradual =>
      ∀ statics, List.Forall₂ Concretizes gradual statics →
        ∀ static ∈ statics, StaticAtom static) generalizing static with
  | symbol name =>
      cases concrete with
      | unknown isStatic => exact isStatic
      | symbol notUndefined => exact .symbol notUndefined
  | var name => cases concrete
  | grounded value =>
      cases concrete
      exact .grounded value
  | expression gradual ih =>
      cases concrete with
      | expression children => exact StaticAtom.expression_iff.mpr (ih _ children)
  | nil =>
      rename_i statics children static member
      cases children
      simp at member
  | cons head tail headIH tailIH =>
      rename_i statics children static member
      cases children with
      | cons headConcrete rest =>
          simp only [List.mem_cons] at member
          rcases member with rfl | member
          · exact headIH headConcrete
          · exact tailIH _ rest static member

/-- A static atom concretizes only to itself. -/
theorem Concretizes.eq_of_static {gradual static : Atom} (isStatic : StaticAtom gradual)
    (concrete : Concretizes gradual static) : static = gradual := by
  induction gradual using Atom.rec (motive_2 := fun gradual =>
      (∀ atom ∈ gradual, StaticAtom atom) →
        ∀ statics, List.Forall₂ Concretizes gradual statics → statics = gradual)
      generalizing static with
  | symbol name =>
      cases concrete with
      | unknown _ => exact absurd .refl isStatic.2
      | symbol _ => rfl
  | var name => cases concrete
  | grounded value => cases concrete; rfl
  | expression gradual ih =>
      cases concrete with
      | expression children =>
          rw [ih (StaticAtom.expression_iff.mp isStatic) _ children]
  | nil =>
      rename_i _ statics children
      cases children
      rfl
  | cons head tail headIH tailIH =>
      rename_i all statics children
      cases children with
      | cons headConcrete rest =>
          rw [headIH (all head (by simp)) headConcrete,
            tailIH (fun atom member => all atom (List.mem_cons_of_mem _ member)) _ rest]

/-- A static atom concretizes to itself. -/
theorem Concretizes.of_static {atom : Atom} (isStatic : StaticAtom atom) :
    Concretizes atom atom := by
  induction atom using Atom.rec (motive_2 := fun atoms =>
      (∀ atom ∈ atoms, StaticAtom atom) → List.Forall₂ Concretizes atoms atoms) with
  | symbol name =>
      refine .symbol fun equal => isStatic.2 ?_
      subst equal
      exact .refl
  | var name => simp [StaticAtom, TypeSubst.typeVars] at isStatic
  | grounded value => exact .grounded value
  | expression atoms ih => exact .expression (ih (StaticAtom.expression_iff.mp isStatic))
  | nil => exact .nil
  | cons head tail headIH tailIH =>
      rename_i all
      exact .cons (headIH (all head (by simp)))
        (tailIH (fun atom member => all atom (List.mem_cons_of_mem _ member)))

/-- The empty expression is a static atom; it witnesses that `γ(?)` is
inhabited. -/
theorem staticAtom_unit : StaticAtom (.expression []) :=
  StaticAtom.expression_iff.mpr (by simp)

/-- Every variable-free gradual type has a concretization. -/
theorem Concretizes.exists {gradual : Atom} (ground : TypeSubst.typeVars gradual = []) :
    ∃ static, Concretizes gradual static := by
  induction gradual using Atom.rec (motive_2 := fun gradual =>
      TypeSubst.typeVarsList gradual = [] →
        ∃ statics, List.Forall₂ Concretizes gradual statics) with
  | symbol name =>
      by_cases undefined : name = "%Undefined%"
      · subst undefined
        exact ⟨_, .unknown staticAtom_unit⟩
      · exact ⟨_, .symbol undefined⟩
  | var name => simp [TypeSubst.typeVars] at ground
  | grounded value => exact ⟨_, .grounded value⟩
  | expression atoms ih =>
      rw [typeVars_expression] at ground
      obtain ⟨statics, children⟩ := ih ground
      exact ⟨_, .expression children⟩
  | nil => exact ⟨[], .nil⟩
  | cons head tail headIH tailIH =>
      rename_i ground
      rw [typeVarsList_cons, List.append_eq_nil_iff] at ground
      obtain ⟨static, headConcrete⟩ := headIH ground.1
      obtain ⟨statics, rest⟩ := tailIH ground.2
      exact ⟨static :: statics, .cons headConcrete rest⟩

theorem Concretizes.typeVars_nil {gradual static : Atom}
    (concrete : Concretizes gradual static) : TypeSubst.typeVars gradual = [] := by
  induction gradual using Atom.rec (motive_2 := fun gradual =>
      ∀ statics, List.Forall₂ Concretizes gradual statics →
        TypeSubst.typeVarsList gradual = []) generalizing static with
  | symbol name => rfl
  | var name => cases concrete
  | grounded value => rfl
  | expression gradual ih =>
      cases concrete with
      | expression children =>
          rw [typeVars_expression]
          exact ih _ children
  | nil => rfl
  | cons head tail headIH tailIH =>
      rename_i statics children
      cases children with
      | cons headConcrete rest =>
          rw [typeVarsList_cons, headIH headConcrete, tailIH _ rest]
          rfl

/-! ## Reduced-type consistency is AGT consistency -/

private theorem rtc_undefined_left (valuation : String → Atom) (right : Atom) :
    ReducedTypeConsistent valuation Atom.undefinedType right := by
  trivial

private theorem rtc_undefined_right (valuation : String → Atom) (left : Atom) :
    ReducedTypeConsistent valuation left Atom.undefinedType := by
  cases left with
  | symbol name =>
      by_cases undefined : name = "%Undefined%"
      · subst undefined
        trivial
      · unfold ReducedTypeConsistent
        split <;> simp_all [Atom.undefinedType]
  | var => trivial
  | grounded => trivial
  | expression => trivial

private theorem rtc_expression (valuation : String → Atom) (left right : List Atom) :
    ReducedTypeConsistent valuation (.expression left) (.expression right) ↔
      ReducedTypeListConsistent valuation left right := by
  simp [ReducedTypeConsistent]

/-- Away from `%Undefined%` and from expression pairs, variable-free atoms
are consistent exactly when they are equal. -/
private theorem rtc_leaf {valuation : String → Atom} {left right : Atom}
    (leafShape : ReducedTypeLeafShape left right)
    (leftNotUndefined : left ≠ Atom.undefinedType)
    (rightNotUndefined : right ≠ Atom.undefinedType)
    (leftGround : TypeSubst.typeVars left = [])
    (rightGround : TypeSubst.typeVars right = []) :
    ReducedTypeConsistent valuation left right ↔ left = right := by
  rw [reducedTypeConsistent_iff_applied_eq_of_leaf valuation left right leafShape
      leftNotUndefined rightNotUndefined,
    applyTypeValuation_of_typeVars_nil valuation left leftGround,
    applyTypeValuation_of_typeVars_nil valuation right rightGround]

private theorem concretizes_symbol_iff {name : String} {static : Atom}
    (notUndefined : name ≠ "%Undefined%") :
    Concretizes (.symbol name) static ↔ static = .symbol name := by
  constructor
  · intro concrete
    cases concrete with
    | unknown _ => exact absurd rfl notUndefined
    | symbol _ => rfl
  · rintro rfl
    exact .symbol notUndefined

private theorem concretizes_grounded_iff {value : GroundedValue} {static : Atom} :
    Concretizes (.grounded value) static ↔ static = .grounded value := by
  constructor
  · intro concrete
    cases concrete
    rfl
  · rintro rfl
    exact .grounded value

private theorem concretizes_expression_iff {gradual : List Atom} {static : Atom} :
    Concretizes (.expression gradual) static ↔
      ∃ statics, static = .expression statics ∧ List.Forall₂ Concretizes gradual statics := by
  constructor
  · intro concrete
    cases concrete with
    | expression children => exact ⟨_, rfl, children⟩
  · rintro ⟨statics, rfl, children⟩
    exact .expression children

/-- **HE's recursive `%Undefined%` consistency is AGT consistency.**  On
variable-free types, the spec's R2 reduced-type consistency holds exactly when
the two concretizations share a static atom. -/
theorem reducedTypeConsistent_iff_agt (valuation : String → Atom) {left right : Atom}
    (leftGround : TypeSubst.typeVars left = [])
    (rightGround : TypeSubst.typeVars right = []) :
    ReducedTypeConsistent valuation left right ↔ Consistent Concretization {left, right} := by
  rw [consistent_pair_iff]
  induction left using Atom.rec (motive_2 := fun lefts =>
      ∀ rights, TypeSubst.typeVarsList lefts = [] → TypeSubst.typeVarsList rights = [] →
        (ReducedTypeListConsistent valuation lefts rights ↔
          ∃ statics, List.Forall₂ Concretizes lefts statics ∧
            List.Forall₂ Concretizes rights statics)) generalizing right with
  | symbol name =>
      by_cases leftUndefined : name = "%Undefined%"
      · subst leftUndefined
        obtain ⟨static, concrete⟩ := Concretizes.exists rightGround
        exact iff_of_true (rtc_undefined_left valuation right)
          ⟨static, .unknown concrete.static, concrete⟩
      · by_cases rightUndefined : right = Atom.undefinedType
        · subst rightUndefined
          exact iff_of_true (rtc_undefined_right valuation _)
            ⟨_, .symbol leftUndefined, .unknown (.symbol leftUndefined)⟩
        · have leftNe : (Atom.symbol name) ≠ Atom.undefinedType := by
            simpa [Atom.undefinedType] using leftUndefined
          rw [rtc_leaf (by cases right <;> trivial) leftNe rightUndefined leftGround
            rightGround]
          constructor
          · rintro rfl
            exact ⟨_, .symbol leftUndefined, .symbol leftUndefined⟩
          · rintro ⟨static, leftConcrete, rightConcrete⟩
            rw [(concretizes_symbol_iff leftUndefined).mp leftConcrete] at rightConcrete
            cases right with
            | symbol other =>
                have otherNe : other ≠ "%Undefined%" := by
                  simpa [Atom.undefinedType] using rightUndefined
                exact (concretizes_symbol_iff otherNe).mp rightConcrete
            | var other => cases rightConcrete
            | grounded value => cases rightConcrete
            | expression atoms => cases rightConcrete
  | var name => simp [TypeSubst.typeVars] at leftGround
  | grounded value =>
      by_cases rightUndefined : right = Atom.undefinedType
      · subst rightUndefined
        exact iff_of_true (rtc_undefined_right valuation _)
          ⟨_, .grounded value, .unknown (.grounded value)⟩
      · rw [rtc_leaf (by cases right <;> trivial) (by simp [Atom.undefinedType])
          rightUndefined leftGround rightGround]
        constructor
        · rintro rfl
          exact ⟨_, .grounded value, .grounded value⟩
        · rintro ⟨static, leftConcrete, rightConcrete⟩
          rw [concretizes_grounded_iff.mp leftConcrete] at rightConcrete
          cases right with
          | symbol other =>
              have otherNe : other ≠ "%Undefined%" := by
                simpa [Atom.undefinedType] using rightUndefined
              exact (concretizes_symbol_iff otherNe).mp rightConcrete
          | var other => cases rightConcrete
          | grounded other => cases rightConcrete; rfl
          | expression atoms => cases rightConcrete
  | expression lefts listIH =>
      by_cases rightUndefined : right = Atom.undefinedType
      · subst rightUndefined
        obtain ⟨static, concrete⟩ := Concretizes.exists leftGround
        exact iff_of_true (rtc_undefined_right valuation _)
          ⟨static, concrete, .unknown concrete.static⟩
      · rw [typeVars_expression] at leftGround
        cases right with
        | expression rights =>
            rw [typeVars_expression] at rightGround
            rw [rtc_expression, listIH rights leftGround rightGround]
            constructor
            · rintro ⟨statics, leftChildren, rightChildren⟩
              exact ⟨_, .expression leftChildren, .expression rightChildren⟩
            · rintro ⟨static, leftConcrete, rightConcrete⟩
              obtain ⟨statics, rfl, leftChildren⟩ :=
                concretizes_expression_iff.mp leftConcrete
              obtain ⟨statics', equal, rightChildren⟩ :=
                concretizes_expression_iff.mp rightConcrete
              cases equal
              exact ⟨_, leftChildren, rightChildren⟩
        | symbol other =>
            have otherNe : other ≠ "%Undefined%" := by
              simpa [Atom.undefinedType] using rightUndefined
            rw [rtc_leaf (by simp [ReducedTypeLeafShape]) (by simp [Atom.undefinedType])
              rightUndefined (by rw [typeVars_expression]; exact leftGround) rightGround]
            constructor
            · intro equal
              cases equal
            · rintro ⟨static, leftConcrete, rightConcrete⟩
              obtain ⟨statics, rfl, _⟩ := concretizes_expression_iff.mp leftConcrete
              cases (concretizes_symbol_iff otherNe).mp rightConcrete
        | var other => simp [TypeSubst.typeVars] at rightGround
        | grounded value =>
            rw [rtc_leaf (by simp [ReducedTypeLeafShape]) (by simp [Atom.undefinedType])
              rightUndefined (by rw [typeVars_expression]; exact leftGround) rightGround]
            constructor
            · intro equal
              cases equal
            · rintro ⟨static, leftConcrete, rightConcrete⟩
              obtain ⟨statics, rfl, _⟩ := concretizes_expression_iff.mp leftConcrete
              cases concretizes_grounded_iff.mp rightConcrete
  | nil =>
      rename_i rights _ _
      cases rights with
      | nil =>
          exact iff_of_true (by simp [ReducedTypeListConsistent]) ⟨[], .nil, .nil⟩
      | cons right rights =>
          constructor
          · intro consistent
            simp [ReducedTypeListConsistent] at consistent
          · rintro ⟨statics, leftChildren, rightChildren⟩
            cases leftChildren
            cases rightChildren
  | cons left lefts leftIH listIH =>
      rename_i rights leftsGround rightsGround
      rw [typeVarsList_cons, List.append_eq_nil_iff] at leftsGround
      cases rights with
      | nil =>
          constructor
          · intro consistent
            simp [ReducedTypeListConsistent] at consistent
          · rintro ⟨statics, leftChildren, rightChildren⟩
            cases rightChildren
            cases leftChildren
      | cons right rights =>
          rw [typeVarsList_cons, List.append_eq_nil_iff] at rightsGround
          simp only [ReducedTypeListConsistent]
          rw [leftIH leftsGround.1 rightsGround.1,
            listIH rights leftsGround.2 rightsGround.2]
          constructor
          · rintro ⟨⟨static, leftConcrete, rightConcrete⟩,
              ⟨statics, leftChildren, rightChildren⟩⟩
            exact ⟨static :: statics, .cons leftConcrete leftChildren,
              .cons rightConcrete rightChildren⟩
          · rintro ⟨statics, leftChildren, rightChildren⟩
            cases leftChildren with
            | cons leftConcrete leftRest =>
                cases rightChildren with
                | cons rightConcrete rightRest =>
                    exact ⟨⟨_, leftConcrete, rightConcrete⟩, ⟨_, leftRest, rightRest⟩⟩

/-! ## The top-level `Atom` wildcard -/

/-- **Published top-level matching is AGT consistency at the top.**  On
variable-free types, HE's core-plus-R2 consistency holds exactly when the
top-level concretizations share a static atom. -/
theorem corePlusR2Consistent_iff_top (valuation : String → Atom) {left right : Atom}
    (leftGround : TypeSubst.typeVars left = [])
    (rightGround : TypeSubst.typeVars right = []) :
    CorePlusR2TypeConsistent valuation left right ↔
      Consistent TopConcretization {left, right} := by
  rw [consistent_pair_iff]
  constructor
  · intro consistent
    rcases consistent with rfl | rfl | rfl | rfl | reduced
    · obtain ⟨static, concrete⟩ := Concretizes.exists rightGround
      exact ⟨static, Or.inr (.unknown concrete.static), Or.inr concrete⟩
    · obtain ⟨static, concrete⟩ := Concretizes.exists leftGround
      exact ⟨static, Or.inr concrete, Or.inr (.unknown concrete.static)⟩
    · obtain ⟨static, concrete⟩ := Concretizes.exists rightGround
      exact ⟨static, Or.inl ⟨rfl, concrete.static⟩, Or.inr concrete⟩
    · obtain ⟨static, concrete⟩ := Concretizes.exists leftGround
      exact ⟨static, Or.inr concrete, Or.inl ⟨rfl, concrete.static⟩⟩
    · obtain ⟨static, leftConcrete, rightConcrete⟩ := (consistent_pair_iff _).mp
        ((reducedTypeConsistent_iff_agt valuation leftGround rightGround).mp reduced)
      exact ⟨static, Or.inr leftConcrete, Or.inr rightConcrete⟩
  · rintro ⟨static, leftTop, rightTop⟩
    rcases leftTop with ⟨rfl, _⟩ | leftConcrete
    · exact Or.inr (Or.inr (Or.inl rfl))
    rcases rightTop with ⟨rfl, _⟩ | rightConcrete
    · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
    exact Or.inr (Or.inr (Or.inr (Or.inr
      ((reducedTypeConsistent_iff_agt valuation leftGround rightGround).mpr
        ((consistent_pair_iff _).mpr ⟨static, leftConcrete, rightConcrete⟩)))))

/-- **HE's finite-presentation matcher accepts exactly the AGT-consistent
pairs** of variable-free types, from any normal incoming presentation. -/
theorem presentation_iff_top {substitution : TypeSubst} (normal : substitution.Normal)
    {left right : Atom} (leftGround : TypeSubst.typeVars left = [])
    (rightGround : TypeSubst.typeVars right = []) :
    (∃ output, CorePlusR2TypePresentationMatchRel substitution left right output) ↔
      Consistent TopConcretization {left, right} := by
  constructor
  · rintro ⟨output, derivation⟩
    have outputNormal := derivation.output_normal normal
    have satisfied := normal_presentedValuation_satisfied outputNormal
    have consistent :=
      ((Spec.Type.Presentation.MatchSolutionTheory.CorePlusR2TypePresentationMatchRel.solutions
        derivation normal (presentedValuation output)).mp satisfied).2
    exact (corePlusR2Consistent_iff_top _ leftGround rightGround).mp consistent
  · intro consistent
    obtain ⟨output, derivation, _, _⟩ :=
      Spec.Type.Presentation.Completeness.CorePlusR2TypePresentationMatchRel.exists_of_satisfied
        normal
        (normal_presentedValuation_satisfied normal) left right
        ((corePlusR2Consistent_iff_top _ leftGround rightGround).mpr consistent)
    exact ⟨output, derivation⟩

/-- **The external LeaTTa interpreter's executable type matcher accepts
exactly the AGT-consistent pairs** of variable-free types. -/
theorem leattaMatchType_iff_top {left right : Atom}
    (leftGround : TypeSubst.typeVars left = [])
    (rightGround : TypeSubst.typeVars right = []) :
    Metta.Minimal.matchType Metta.Bindings.empty
        (toLeaTTaAtom left) (toLeaTTaAtom right) ≠ none ↔
      Consistent TopConcretization {left, right} := by
  have disjoint : VarsDisjoint left right := by
    intro name member
    rw [toLeaTTaAtom_vars_eq_typeVars, leftGround] at member
    simp at member
  rw [Ne, matchType_eq_none_iff_no_presentation typePresentationSimulationState_empty
    left right disjoint, ← presentation_iff_top TypeSubst.normal_empty leftGround rightGround]
  simp

/-! ## Consequences -/

/-- On static types AGT consistency is equality: gradual typing is a
conservative extension of the static fragment. -/
theorem agt_static_iff_eq {left right : Atom} (leftStatic : StaticAtom left)
    (rightStatic : StaticAtom right) :
    Consistent Concretization {left, right} ↔ left = right := by
  rw [consistent_pair_iff]
  constructor
  · rintro ⟨static, leftConcrete, rightConcrete⟩
    rw [← leftConcrete.eq_of_static leftStatic, rightConcrete.eq_of_static rightStatic]
  · rintro rfl
    exact ⟨left, .of_static leftStatic, .of_static leftStatic⟩

/-- `%Undefined%` is consistent with every variable-free type. -/
theorem undefined_topConsistent {type : Atom} (ground : TypeSubst.typeVars type = []) :
    Consistent TopConcretization {Atom.undefinedType, type} := by
  obtain ⟨static, concrete⟩ := Concretizes.exists ground
  exact (consistent_pair_iff _).mpr ⟨static, Or.inr (.unknown concrete.static), Or.inr concrete⟩

/-- The gradual permissiveness that the external LeaTTa package proves
(`Metta.matchType_undefined_left`, `Metta.matchType_atom_left` and their
right-hand siblings) is the instance of the AGT reading in which one side is
`%Undefined%` or a top-level `Atom`. -/
theorem gradual_permissiveness_is_agt {type : Atom} (ground : TypeSubst.typeVars type = []) :
    Consistent TopConcretization {Atom.undefinedType, type} ∧
      Consistent TopConcretization {type, Atom.undefinedType} ∧
      Consistent TopConcretization {Atom.atomType, type} ∧
      Consistent TopConcretization {type, Atom.atomType} ∧
      Metta.Minimal.matchType Metta.Bindings.empty
          (toLeaTTaAtom Atom.undefinedType) (toLeaTTaAtom type) = some Metta.Bindings.empty ∧
      Metta.Minimal.matchType Metta.Bindings.empty
          (toLeaTTaAtom type) (toLeaTTaAtom Atom.undefinedType) = some Metta.Bindings.empty ∧
      Metta.Minimal.matchType Metta.Bindings.empty
          (toLeaTTaAtom Atom.atomType) (toLeaTTaAtom type) = some Metta.Bindings.empty ∧
      Metta.Minimal.matchType Metta.Bindings.empty
          (toLeaTTaAtom type) (toLeaTTaAtom Atom.atomType) = some Metta.Bindings.empty := by
  obtain ⟨static, concrete⟩ := Concretizes.exists ground
  refine ⟨undefined_topConsistent ground,
    (consistent_pair_iff _).mpr ⟨static, Or.inr concrete, Or.inr (.unknown concrete.static)⟩,
    (consistent_pair_iff _).mpr ⟨static, Or.inl ⟨rfl, concrete.static⟩, Or.inr concrete⟩,
    (consistent_pair_iff _).mpr ⟨static, Or.inr concrete, Or.inl ⟨rfl, concrete.static⟩⟩,
    ?_, ?_, ?_, ?_⟩
  · exact Metta.matchType_undefined_left _ _
  · exact Metta.matchType_undefined_right _ _
  · exact Metta.matchType_atom_left _ _
  · exact Metta.matchType_atom_right _ _

private def number : Atom := .symbol "Number"
private def string : Atom := .symbol "String"

/-- AGT consistency is not transitive: `Number ~ ?` and `? ~ String`, yet
`Number ≁ String`. -/
theorem agt_not_transitive :
    Consistent Concretization {number, Atom.undefinedType} ∧
      Consistent Concretization {Atom.undefinedType, string} ∧
      ¬Consistent Concretization {number, string} := by
  have numberStatic : StaticAtom number := .symbol (by decide)
  have stringStatic : StaticAtom string := .symbol (by decide)
  refine ⟨(consistent_pair_iff _).mpr ⟨number, .of_static numberStatic, .unknown numberStatic⟩,
    (consistent_pair_iff _).mpr ⟨string, .unknown stringStatic, .of_static stringStatic⟩, ?_⟩
  rw [agt_static_iff_eq numberStatic stringStatic]
  simp [number, string]

private def listOf (element : Atom) : Atom := .expression [.symbol "List", element]

/-- A nested `Atom` is an ordinary symbol for AGT, so `(List Atom)` and
`(List Number)` are inconsistent, and the executable matcher rejects them;
the declarative `Metta.Consistent` of the external package nevertheless
relates them, because it treats `Atom` as a wildcard at every depth. -/
theorem metta_consistent_nested_atom_not_agt :
    Metta.Consistent (toLeaTTaAtom (listOf Atom.atomType)) (toLeaTTaAtom (listOf number)) ∧
      ¬Consistent TopConcretization {listOf Atom.atomType, listOf number} ∧
      Metta.Minimal.matchType Metta.Bindings.empty
        (toLeaTTaAtom (listOf Atom.atomType)) (toLeaTTaAtom (listOf number)) = none := by
  have notConsistent : ¬Consistent TopConcretization {listOf Atom.atomType, listOf number} := by
    have leftStatic : StaticAtom (listOf Atom.atomType) :=
      StaticAtom.expression_iff.mpr (by
        intro atom member
        simp at member
        rcases member with rfl | rfl <;> exact .symbol (by decide))
    have rightStatic : StaticAtom (listOf number) :=
      StaticAtom.expression_iff.mpr (by
        intro atom member
        simp [number] at member
        rcases member with rfl | rfl <;> exact .symbol (by decide))
    rw [consistent_pair_iff]
    rintro ⟨static, leftTop, rightTop⟩
    rcases leftTop with ⟨equal, _⟩ | leftConcrete
    · simp [listOf, Atom.atomType] at equal
    rcases rightTop with ⟨equal, _⟩ | rightConcrete
    · simp [listOf, number, Atom.atomType] at equal
    have leftEq := leftConcrete.eq_of_static leftStatic
    have rightEq := rightConcrete.eq_of_static rightStatic
    rw [leftEq] at rightEq
    simp [listOf, number, Atom.atomType] at rightEq
  refine ⟨?_, notConsistent, ?_⟩
  · simp only [listOf, toLeaTTaAtom, toLeaTTaAtoms, Atom.atomType, number]
    exact .expr (.cons (.same _) (.cons (.atomL _) .nil))
  · have ground : ∀ element : Atom, TypeSubst.typeVars element = [] →
        TypeSubst.typeVars (listOf element) = [] := by
      intro element elementGround
      simp [listOf, TypeSubst.typeVars, TypeSubst.typeVarsList, elementGround]
    by_contra accepted
    exact notConsistent ((leattaMatchType_iff_top (ground _ rfl) (ground _ rfl)).mp accepted)

#print axioms reducedTypeConsistent_iff_agt
#print axioms corePlusR2Consistent_iff_top
#print axioms presentation_iff_top
#print axioms leattaMatchType_iff_top
#print axioms gradual_permissiveness_is_agt
#print axioms agt_static_iff_eq
#print axioms agt_not_transitive
#print axioms metta_consistent_nested_atom_not_agt

end Mettapedia.Languages.MeTTa.HE.TypeGrounding.Gradual
