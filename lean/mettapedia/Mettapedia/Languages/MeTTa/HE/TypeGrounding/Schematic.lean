import Mettapedia.Languages.MeTTa.HE.TypeGrounding.SpecBoundary
import Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.ScopeObservation

/-!
# Type variables: first-order schematic declarations and HOL type instances

HE solves the type variables of a declaration such as
`(: cons (-> $t (List $t) (List $t)))` by unifying the declared argument types
with the types of the arguments, each side renamed apart in its own fresh
scope.  In HOL this is the reading of a polymorphic constant: every occurrence
of the constant carries an instance of its declared type scheme, and the
annotated term is simply typed.

The fragment is first-order:

* a first-order type mentions no reserved type name at any depth, so no
  arrow, no `%Undefined%` and no meta-type; type variables may occur anywhere;
* an instance substitutes ground first-order types for the type variables;
* a constant has one first-order declared type, and an application is a
  saturated application of a symbol whose single declaration is an arrow
  `(-> B₁ … Bₙ R)`, `n ≥ 1`, with first-order components.

`schematic_hol_iff_exact`: HOL elaborates some instance annotation of `e` at a
static type `T` exactly when no subatom of `e` falls back to `%Undefined%` and
HE's exact relation assigns `e` a single candidate `U` of which `T` is a
ground first-order instance.  The candidate HE computes is therefore the
principal type scheme of the HOL instances (`exact_candidates_same_instances`).
`operator_constant_hol_iff` covers a schematic arrow constant on its own.

Arrow types never occur inside first-order types, so an arrow-typed constant
can only be the head of an application.  The restriction is a genuine
boundary: HE's arrows are n-ary and its matching compares arities, while a HOL
type variable may stand for a curried arrow.  `arrow_variable_counterexample`
pins the disagreement: `(-> $a $b)` does not match `(-> A C B)` in HE, while
the instance `$a := A`, `$b := (-> C B)` has the same HOL type.
-/

namespace Mettapedia.Languages.MeTTa.HE.TypeGrounding.Schematic

open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)
open Mettapedia.Logic.HOL
open Mettapedia.Logic.HOL.NamedElaboration
open Spec.Type
open Spec.Type.Presentation
open Spec.Type.Presentation.Exact
open Spec.Type.Presentation.Theory
open Spec.Type.RuntimeRefinement
open Spec.Type.Presentation.ApplicationEquivariance
open Spec.Bindings.ScopeObservation

/-! ## First-order types -/

/-- No reserved type name occurs in the atom, at any depth.  Type variables
may occur anywhere.  In particular a first-order type contains no arrow, no
`%Undefined%` and no meta-type. -/
def ReservedFree (atom : Atom) : Prop :=
  ∀ sub, Subatom sub atom → ¬TopReserved sub

namespace ReservedFree

theorem of_child {atom : Atom} {atoms : List Atom}
    (free : ReservedFree (.expression atoms)) (member : atom ∈ atoms) :
    ReservedFree atom :=
  fun sub occurs => free sub (.child member occurs)

theorem not_topReserved {atom : Atom} (free : ReservedFree atom) :
    ¬TopReserved atom :=
  free atom .refl

theorem undefinedFree {atom : Atom} (free : ReservedFree atom) :
    UndefinedFree atom :=
  fun occurs => free _ occurs ⟨"%Undefined%", by simp [reservedTypeNames], rfl⟩

theorem ne_undefined {atom : Atom} (free : ReservedFree atom) :
    atom ≠ Atom.undefinedType :=
  free.undefinedFree.ne

theorem ne_atom {atom : Atom} (free : ReservedFree atom) :
    atom ≠ Atom.atomType := by
  rintro rfl
  exact free.not_topReserved ⟨"Atom", by simp [reservedTypeNames], rfl⟩

theorem not_arrowShaped {atom : Atom} (free : ReservedFree atom) :
    ¬ArrowShaped atom := by
  rintro ⟨components, rfl⟩
  exact free _ (.child (by simp) .refl) ⟨"->", by simp [reservedTypeNames], rfl⟩

end ReservedFree

theorem reservedFree_symbol_iff {name : String} :
    ReservedFree (.symbol name) ↔ name ∉ reservedTypeNames := by
  constructor
  · intro free member
    exact free _ .refl ⟨name, member, rfl⟩
  · intro notReserved sub occurs reserved
    rw [occurs.symbol_eq] at reserved
    obtain ⟨other, member, equal⟩ := reserved
    cases equal
    exact notReserved member

theorem reservedFree_var (name : String) : ReservedFree (.var name) := by
  intro sub occurs reserved
  cases occurs
  obtain ⟨_, _, equal⟩ := reserved
  cases equal

theorem reservedFree_grounded (value : GroundedValue) :
    ReservedFree (.grounded value) := by
  intro sub occurs reserved
  rw [occurs.grounded_eq] at reserved
  obtain ⟨_, _, equal⟩ := reserved
  cases equal

theorem reservedFree_expression_iff {atoms : List Atom} :
    ReservedFree (.expression atoms) ↔ ∀ atom ∈ atoms, ReservedFree atom := by
  constructor
  · intro free atom member
    exact free.of_child member
  · intro all sub occurs reserved
    rcases occurs.expression_cases with rfl | ⟨child, member, inner⟩
    · obtain ⟨_, _, equal⟩ := reserved
      cases equal
    · exact all child member sub inner reserved

/-- A ground first-order type: first-order and variable-free. -/
def GroundFirstOrder (atom : Atom) : Prop :=
  ReservedFree atom ∧ TypeSubst.typeVars atom = []

/-- A ground first-order type is a static base type. -/
theorem GroundFirstOrder.static {atom : Atom} (ground : GroundFirstOrder atom) :
    StaticType atom :=
  .base ground.1.not_arrowShaped ground.1.not_topReserved ground.1.undefinedFree ground.2

/-- The instances of first-order schemes: every type variable is valued by a
ground first-order type. -/
def FirstOrderValuation (valuation : String → Atom) : Prop :=
  ∀ name, GroundFirstOrder (valuation name)

/-! ## Valuations and renamings of first-order types -/

theorem reservedFree_applyTypeValuation {valuation : String → Atom} {atom : Atom}
    (free : ReservedFree atom)
    (values : ∀ name ∈ TypeSubst.typeVars atom, ReservedFree (valuation name)) :
    ReservedFree (applyTypeValuation valuation atom) := by
  induction atom using Atom.rec (motive_2 := fun atoms =>
      (∀ atom ∈ atoms, ReservedFree atom) →
        (∀ name ∈ TypeSubst.typeVarsList atoms, ReservedFree (valuation name)) →
        ∀ atom ∈ atoms.map (applyTypeValuation valuation), ReservedFree atom) with
  | symbol name => simpa [applyTypeValuation] using free
  | var name =>
      simpa [applyTypeValuation] using values name (by simp [TypeSubst.typeVars])
  | grounded value => simpa [applyTypeValuation] using free
  | expression atoms ih =>
      simp only [applyTypeValuation]
      exact reservedFree_expression_iff.mpr
        (ih (fun _ member => free.of_child member)
          (by simpa [TypeSubst.typeVars] using values))
  | nil =>
      rename_i _ _ atom member
      simp at member
  | cons head tail headIH tailIH =>
      rename_i all allValues atom member
      simp only [TypeSubst.typeVarsList, List.mem_append] at allValues
      simp only [List.map_cons, List.mem_cons] at member
      rcases member with rfl | member
      · exact headIH (all head (by simp)) (fun name occurs => allValues name (Or.inl occurs))
      · exact tailIH (fun atom member => all atom (List.mem_cons_of_mem _ member))
          (fun name occurs => allValues name (Or.inr occurs)) atom member

theorem reservedFree_of_applyTypeValuation {valuation : String → Atom} {atom : Atom}
    (free : ReservedFree (applyTypeValuation valuation atom)) : ReservedFree atom := by
  induction atom using Atom.rec (motive_2 := fun atoms =>
      (∀ atom ∈ atoms.map (applyTypeValuation valuation), ReservedFree atom) →
        ∀ atom ∈ atoms, ReservedFree atom) with
  | symbol name => simpa [applyTypeValuation] using free
  | var name => exact reservedFree_var name
  | grounded value => exact reservedFree_grounded value
  | expression atoms ih =>
      simp only [applyTypeValuation] at free
      exact reservedFree_expression_iff.mpr (ih (reservedFree_expression_iff.mp free))
  | nil =>
      rename_i _ atom member
      simp at member
  | cons head tail headIH tailIH =>
      rename_i all atom member
      simp only [List.map_cons, List.forall_mem_cons] at all
      simp only [List.mem_cons] at member
      rcases member with rfl | member
      · exact headIH all.1
      · exact tailIH all.2 atom member

theorem typeVars_applyTypeValuation_nil {valuation : String → Atom} {atom : Atom}
    (ground : ∀ name ∈ TypeSubst.typeVars atom, TypeSubst.typeVars (valuation name) = []) :
    TypeSubst.typeVars (applyTypeValuation valuation atom) = [] := by
  induction atom using Atom.rec (motive_2 := fun atoms =>
      (∀ name ∈ TypeSubst.typeVarsList atoms, TypeSubst.typeVars (valuation name) = []) →
        TypeSubst.typeVarsList (atoms.map (applyTypeValuation valuation)) = []) with
  | symbol name => simp [applyTypeValuation, TypeSubst.typeVars]
  | var name =>
      simpa [applyTypeValuation] using ground name (by simp [TypeSubst.typeVars])
  | grounded value => simp [applyTypeValuation, TypeSubst.typeVars]
  | expression atoms ih =>
      simp only [applyTypeValuation, TypeSubst.typeVars]
      exact ih (by simpa [TypeSubst.typeVars] using ground)
  | nil => simp [TypeSubst.typeVarsList]
  | cons head tail headIH tailIH =>
      rename_i all
      simp only [TypeSubst.typeVarsList, List.mem_append] at all
      simp only [List.map_cons, TypeSubst.typeVarsList, List.append_eq_nil_iff]
      exact ⟨headIH (fun name occurs => all name (Or.inl occurs)),
        tailIH (fun name occurs => all name (Or.inr occurs))⟩

/-- A first-order valuation instantiates a first-order type to a ground
first-order type. -/
theorem FirstOrderValuation.ground {valuation : String → Atom}
    (firstOrder : FirstOrderValuation valuation) {atom : Atom}
    (free : ReservedFree atom) : GroundFirstOrder (applyTypeValuation valuation atom) :=
  ⟨reservedFree_applyTypeValuation free (fun name _ => (firstOrder name).1),
    typeVars_applyTypeValuation_nil (fun name _ => (firstOrder name).2)⟩

theorem reservedFree_renameTypeVars (rename : String → String) {atom : Atom}
    (free : ReservedFree atom) : ReservedFree (renameTypeVars rename atom) := by
  induction atom using Atom.rec (motive_2 := fun atoms =>
      (∀ atom ∈ atoms, ReservedFree atom) →
        ∀ atom ∈ atoms.map (renameTypeVars rename), ReservedFree atom) with
  | symbol name => simpa [renameTypeVars] using free
  | var name => simpa [renameTypeVars] using reservedFree_var (rename name)
  | grounded value => simpa [renameTypeVars] using free
  | expression atoms ih =>
      simp only [renameTypeVars]
      exact reservedFree_expression_iff.mpr (ih (fun _ member => free.of_child member))
  | nil =>
      rename_i _ atom member
      simp at member
  | cons head tail headIH tailIH =>
      rename_i all atom member
      simp only [List.map_cons, List.mem_cons] at member
      rcases member with rfl | member
      · exact headIH (all head (by simp))
      · exact tailIH (fun atom member => all atom (List.mem_cons_of_mem _ member)) atom member

/-- A satisfying valuation stays satisfying after a further valuation. -/
theorem typeSubstSatisfied_comp {inner : String → Atom} {substitution : TypeSubst}
    (satisfied : TypeSubstSatisfied inner substitution) (outer : String → Atom) :
    TypeSubstSatisfied (fun name => applyTypeValuation outer (inner name)) substitution := by
  intro name value member
  show applyTypeValuation outer (inner name) = _
  rw [satisfied name value member, applyTypeValuation_comp]

/-! ## Projection onto first-order types -/

mutual

/-- Replace every reserved type name and every type variable by the symbol
`Type`.  The projection is the identity on ground first-order types and turns
every model of first-order equations into a first-order model. -/
def project : Atom → Atom
  | .symbol name => if name ∈ reservedTypeNames then .symbol "Type" else .symbol name
  | .var _ => .symbol "Type"
  | .grounded value => .grounded value
  | .expression atoms => .expression (projectList atoms)

/-- List companion of `project`. -/
def projectList : List Atom → List Atom
  | [] => []
  | atom :: atoms => project atom :: projectList atoms

end

theorem projectList_eq_map : ∀ atoms : List Atom, projectList atoms = atoms.map project
  | [] => rfl
  | atom :: atoms => by simp [projectList, projectList_eq_map atoms]

private theorem type_not_reserved : "Type" ∉ reservedTypeNames := by decide

theorem project_groundFirstOrder (atom : Atom) : GroundFirstOrder (project atom) := by
  induction atom using Atom.rec (motive_2 := fun atoms =>
      ∀ atom ∈ atoms.map project, GroundFirstOrder atom) with
  | symbol name =>
      by_cases reserved : name ∈ reservedTypeNames
      · simp only [project, if_pos reserved]
        exact ⟨reservedFree_symbol_iff.mpr type_not_reserved, rfl⟩
      · simp only [project, if_neg reserved]
        exact ⟨reservedFree_symbol_iff.mpr reserved, rfl⟩
  | var name =>
      simp only [project]
      exact ⟨reservedFree_symbol_iff.mpr type_not_reserved, rfl⟩
  | grounded value =>
      simp only [project]
      exact ⟨reservedFree_grounded value, rfl⟩
  | expression atoms ih =>
      simp only [project, projectList_eq_map]
      refine ⟨reservedFree_expression_iff.mpr (fun atom member => (ih atom member).1), ?_⟩
      simp only [TypeSubst.typeVars]
      rw [typeVarsList_eq_nil_iff]
      exact fun atom member => (ih atom member).2
  | nil =>
      rename_i atom member
      simp at member
  | cons head tail headIH tailIH =>
      rename_i atom member
      simp only [List.map_cons, List.mem_cons] at member
      rcases member with rfl | member
      · exact headIH
      · exact tailIH atom member

theorem project_applyTypeValuation (valuation : String → Atom) {atom : Atom}
    (free : ReservedFree atom) :
    project (applyTypeValuation valuation atom) =
      applyTypeValuation (fun name => project (valuation name)) atom := by
  induction atom using Atom.rec (motive_2 := fun atoms =>
      (∀ atom ∈ atoms, ReservedFree atom) →
        (atoms.map (applyTypeValuation valuation)).map project =
          atoms.map (applyTypeValuation (fun name => project (valuation name)))) with
  | symbol name =>
      have notReserved := reservedFree_symbol_iff.mp free
      simp [applyTypeValuation, project, notReserved]
  | var name => simp [applyTypeValuation]
  | grounded value => simp [applyTypeValuation, project]
  | expression atoms ih =>
      simp only [applyTypeValuation, project, projectList_eq_map]
      rw [ih (fun _ member => free.of_child member)]
  | nil => simp
  | cons head tail headIH tailIH =>
      rename_i all
      simp only [List.map_cons, List.cons.injEq]
      exact ⟨headIH (all head (by simp)),
        tailIH (fun atom member => all atom (List.mem_cons_of_mem _ member))⟩

theorem project_of_groundFirstOrder {atom : Atom} (ground : GroundFirstOrder atom) :
    project atom = atom := by
  obtain ⟨free, closed⟩ := ground
  induction atom using Atom.rec (motive_2 := fun atoms =>
      (∀ atom ∈ atoms, ReservedFree atom) → TypeSubst.typeVarsList atoms = [] →
        atoms.map project = atoms) with
  | symbol name =>
      have notReserved := reservedFree_symbol_iff.mp free
      simp [project, notReserved]
  | var name => simp [TypeSubst.typeVars] at closed
  | grounded value => simp [project]
  | expression atoms ih =>
      simp only [project, projectList_eq_map]
      rw [ih (fun _ member => free.of_child member)
        (by simpa [TypeSubst.typeVars] using closed)]
  | nil => simp
  | cons head tail headIH tailIH =>
      rename_i all allClosed
      simp only [TypeSubst.typeVarsList, List.append_eq_nil_iff] at allClosed
      simp only [List.map_cons, List.cons.injEq]
      exact ⟨headIH (all head (by simp)) allClosed.1,
        tailIH (fun atom member => all atom (List.mem_cons_of_mem _ member)) allClosed.2⟩

/-- The projection of a valuation is a first-order valuation. -/
theorem projected_firstOrder (valuation : String → Atom) :
    FirstOrderValuation (fun name => project (valuation name)) :=
  fun name => project_groundFirstOrder (valuation name)

/-! ## Consistency of first-order types is equality of instances -/

theorem reducedTypeConsistent_iff_eq (valuation : String → Atom) {left right : Atom}
    (leftFree : UndefinedFree left) (rightFree : UndefinedFree right) :
    ReducedTypeConsistent valuation left right ↔
      applyTypeValuation valuation left = applyTypeValuation valuation right := by
  induction left using Atom.rec (motive_2 := fun lefts =>
      ∀ rights : List Atom, (∀ atom ∈ lefts, UndefinedFree atom) →
        (∀ atom ∈ rights, UndefinedFree atom) →
        (ReducedTypeListConsistent valuation lefts rights ↔
          lefts.map (applyTypeValuation valuation) =
            rights.map (applyTypeValuation valuation))) generalizing right with
  | symbol name =>
      exact MatchSolutionTheory.reducedTypeConsistent_iff_applied_eq_of_leaf valuation _ _
        trivial leftFree.ne rightFree.ne
  | var name =>
      exact MatchSolutionTheory.reducedTypeConsistent_iff_applied_eq_of_leaf valuation _ _
        trivial leftFree.ne rightFree.ne
  | grounded value =>
      exact MatchSolutionTheory.reducedTypeConsistent_iff_applied_eq_of_leaf valuation _ _
        trivial leftFree.ne rightFree.ne
  | expression lefts ih =>
      cases right with
      | expression rights =>
          have unfolded : ReducedTypeConsistent valuation (.expression lefts)
              (.expression rights) ↔ ReducedTypeListConsistent valuation lefts rights := by
            simp [ReducedTypeConsistent]
          rw [unfolded]
          simp only [applyTypeValuation, Atom.expression.injEq]
          exact ih rights (fun _ member => leftFree.of_child member)
            (fun _ member => rightFree.of_child member)
      | symbol name =>
          exact MatchSolutionTheory.reducedTypeConsistent_iff_applied_eq_of_leaf valuation _ _
            trivial leftFree.ne rightFree.ne
      | var name =>
          exact MatchSolutionTheory.reducedTypeConsistent_iff_applied_eq_of_leaf valuation _ _
            trivial leftFree.ne rightFree.ne
      | grounded value =>
          exact MatchSolutionTheory.reducedTypeConsistent_iff_applied_eq_of_leaf valuation _ _
            trivial leftFree.ne rightFree.ne
  | nil =>
      rename_i rights _ _
      cases rights <;> simp [ReducedTypeListConsistent]
  | cons head tail headIH tailIH =>
      rename_i rights leftAll rightAll
      cases rights with
      | nil => simp [ReducedTypeListConsistent]
      | cons right rights =>
          simp only [ReducedTypeListConsistent, List.map_cons, List.cons.injEq]
          rw [headIH (leftAll head (by simp)) (rightAll right (by simp)),
            tailIH rights (fun atom member => leftAll atom (List.mem_cons_of_mem _ member))
              (fun atom member => rightAll atom (List.mem_cons_of_mem _ member))]

theorem corePlusR2_iff_eq (valuation : String → Atom) {left right : Atom}
    (leftFree : ReservedFree left) (rightFree : ReservedFree right) :
    CorePlusR2TypeConsistent valuation left right ↔
      applyTypeValuation valuation left = applyTypeValuation valuation right := by
  unfold CorePlusR2TypeConsistent
  simp only [leftFree.ne_undefined, rightFree.ne_undefined, leftFree.ne_atom,
    rightFree.ne_atom, false_or]
  exact reducedTypeConsistent_iff_eq valuation leftFree.undefinedFree rightFree.undefinedFree

theorem forall₂_corePlusR2_iff_eq (valuation : String → Atom) :
    ∀ {lefts rights : List Atom}, (∀ atom ∈ lefts, ReservedFree atom) →
      (∀ atom ∈ rights, ReservedFree atom) →
      (List.Forall₂ (CorePlusR2TypeConsistent valuation) lefts rights ↔
        List.Forall₂ (fun left right =>
          applyTypeValuation valuation left = applyTypeValuation valuation right) lefts rights)
  | [], [], _, _ => by simp
  | [], _ :: _, _, _ => by simp
  | _ :: _, [], _, _ => by simp
  | left :: lefts, right :: rights, leftFree, rightFree => by
      rw [List.forall₂_cons, List.forall₂_cons,
        corePlusR2_iff_eq valuation (leftFree left (by simp)) (rightFree right (by simp)),
        forall₂_corePlusR2_iff_eq valuation
          (fun atom member => leftFree atom (List.mem_cons_of_mem _ member))
          (fun atom member => rightFree atom (List.mem_cons_of_mem _ member))]

/-! ## The fragment -/

/-- A first-order operator scheme: an arrow with at least one argument and
first-order argument and return types. -/
structure OperatorScheme (scheme : Atom) (argumentTypes : List Atom)
    (returnType : Atom) : Prop where
  function : FunctionTypeRel scheme argumentTypes returnType
  nonempty : argumentTypes ≠ []
  arguments : ∀ argumentType ∈ argumentTypes, ReservedFree argumentType
  result : ReservedFree returnType

/-- Saturated first-order expressions over schematic declarations.  A constant
is a symbol with exactly one first-order declaration, or a literal.  An
application has a symbol head whose single declaration is a first-order
operator scheme with exactly as many argument types as there are arguments,
and no declaration annotates the application itself. -/
inductive SchematicTerm (space : Space) : Atom → Prop where
  | constant {atom scheme : Atom} :
      declaredType? space atom = some scheme → ReservedFree scheme →
      SchematicTerm space atom
  | application {name : String} {arguments argumentTypes : List Atom}
      {scheme returnType : Atom} :
      name ≠ "StateValue" →
      getAnnotatedTypes space (.expression (.symbol name :: arguments)) = [] →
      declaredType? space (.symbol name) = some scheme →
      OperatorScheme scheme argumentTypes returnType →
      arguments.length = argumentTypes.length →
      (∀ argument ∈ arguments, SchematicTerm space argument) →
      SchematicTerm space (.expression (.symbol name :: arguments))

theorem OperatorScheme.rename {scheme returnType : Atom} {argumentTypes : List Atom}
    (operator : OperatorScheme scheme argumentTypes returnType) (rename : String → String) :
    OperatorScheme (renameTypeVars rename scheme)
      (argumentTypes.map (renameTypeVars rename)) (renameTypeVars rename returnType) where
  function := (Spec.Type.Presentation.Alpha.functionTypeRel_renameTypeVars_iff
    rename scheme _ _).mpr ⟨_, _, operator.function, rfl, rfl⟩
  nonempty := by simpa using operator.nonempty
  arguments := by
    intro argumentType member
    obtain ⟨source, sourceMember, rfl⟩ := List.mem_map.mp member
    exact reservedFree_renameTypeVars rename (operator.arguments source sourceMember)
  result := reservedFree_renameTypeVars rename operator.result

/-- An instance of an operator scheme is a static arrow over the instances of
its components. -/
theorem OperatorScheme.instantiate {scheme returnType : Atom} {argumentTypes : List Atom}
    (operator : OperatorScheme scheme argumentTypes returnType)
    {valuation : String → Atom} (firstOrder : FirstOrderValuation valuation) :
    FunctionTypeRel (applyTypeValuation valuation scheme)
        (argumentTypes.map (applyTypeValuation valuation))
        (applyTypeValuation valuation returnType) ∧
      StaticType (applyTypeValuation valuation scheme) := by
  have function : FunctionTypeRel (applyTypeValuation valuation scheme)
      (argumentTypes.map (applyTypeValuation valuation))
      (applyTypeValuation valuation returnType) := by
    have shape := operator.function
    rw [FunctionTypeRel] at shape ⊢
    rw [shape]
    simp [applyTypeValuation, List.map_append]
  refine ⟨function, .arrow function (by simpa using operator.nonempty) ?_ ?_ ?_⟩
  · intro argumentType member
    obtain ⟨source, sourceMember, rfl⟩ := List.mem_map.mp member
    exact (firstOrder.ground (operator.arguments source sourceMember)).static
  · exact (firstOrder.ground operator.result).1.not_arrowShaped
  · exact (firstOrder.ground operator.result).static

theorem SchematicTerm.constant_shape {space : Space} {atom scheme : Atom}
    (declared : declaredType? space atom = some scheme) :
    (∃ name, atom = .symbol name) ∨ ∃ value, atom = .grounded value := by
  cases atom with
  | symbol name => exact Or.inl ⟨name, rfl⟩
  | grounded value => exact Or.inr ⟨value, rfl⟩
  | var name => simp [declaredType?] at declared
  | expression atoms => simp [declaredType?] at declared

/-! ## The HOL signature of type instances -/

/-- `instanceType` is a ground first-order instance of the declared type of
`constant`. -/
def InstanceOf (space : Space) (constant instanceType : Atom) : Prop :=
  ∃ scheme, declaredType? space constant = some scheme ∧
    ∃ valuation, FirstOrderValuation valuation ∧
      applyTypeValuation valuation scheme = instanceType

open Classical in
/-- The HOL type of a constant at an instance: the image of the instance, when
it is one. -/
noncomputable def instanceConstType (space : Space) (name : Atom × Atom) :
    Option (Ty Atom) :=
  if InstanceOf space name.1 name.2 then some (toTy name.2) else none

/-- HOL constants of a schematic declaration space: a declared atom at one of
its instances, indexed by the HOL type of the instance. -/
def InstanceConst (space : Space) (type : Ty Atom) : Type :=
  { name : Atom × Atom // instanceConstType space name = some type }

/-- The HOL signature of a schematic declaration space. -/
noncomputable def instanceSignature (space : Space) :
    Signature (Atom × Atom) (InstanceConst space) :=
  fun name =>
    match lookup : instanceConstType space name with
    | some type => some ⟨type, ⟨name, lookup⟩⟩
    | none => none

theorem instanceSignature_some {space : Space} {name : Atom × Atom} {type : Ty Atom}
    (lookup : instanceConstType space name = some type) :
    instanceSignature space name = some ⟨type, ⟨name, lookup⟩⟩ := by
  unfold instanceSignature
  split
  · next type' lookup' =>
      rw [lookup] at lookup'
      cases lookup'
      rfl
  · next lookup' =>
      rw [lookup] at lookup'
      cases lookup'

theorem instanceSignature_none {space : Space} {name : Atom × Atom}
    (lookup : instanceConstType space name = none) : instanceSignature space name = none := by
  unfold instanceSignature
  split
  · next type lookup' =>
      rw [lookup] at lookup'
      cases lookup'
  · rfl

/-- A constant elaborates exactly at the image of an instance of its declared
type. -/
theorem elaborates_instance_iff {space : Space} {name : Atom × Atom} {type : Ty Atom} :
    Elaborates (instanceSignature space) (.constant name) type ↔
      InstanceOf space name.1 name.2 ∧ type = toTy name.2 := by
  rw [elaborates_constant_iff]
  constructor
  · rintro ⟨constant, lookup⟩
    cases constantType : instanceConstType space name with
    | none =>
        rw [instanceSignature_none constantType] at lookup
        cases lookup
    | some found =>
        rw [instanceSignature_some constantType] at lookup
        simp only [Option.some.injEq] at lookup
        have typeEq : found = type := congrArg Sigma.fst lookup
        subst typeEq
        unfold instanceConstType at constantType
        split at constantType
        · next instanceOf =>
            simp only [Option.some.injEq] at constantType
            exact ⟨instanceOf, constantType.symm⟩
        · cases constantType
  · rintro ⟨instanceOf, rfl⟩
    have lookup : instanceConstType space name = some (toTy name.2) := by
      unfold instanceConstType
      rw [if_pos instanceOf]
    exact ⟨_, instanceSignature_some lookup⟩

/-! ## Instance annotations -/

/-- Named HOL terms whose constants carry an instance type. -/
abbrev InstanceTerm := NamedTerm Atom String (Atom × Atom)

/-- `term` is the curried HOL term of `expression` with an instance type
attached to every constant occurrence. -/
inductive Annotates : Atom → InstanceTerm → Prop where
  | symbol (name : String) (instanceType : Atom) :
      Annotates (.symbol name) (.constant (.symbol name, instanceType))
  | grounded (value : GroundedValue) (instanceType : Atom) :
      Annotates (.grounded value) (.constant (.grounded value, instanceType))
  | application {name : String} {instanceType : Atom} {arguments : List Atom}
      {terms : List InstanceTerm} :
      List.Forall₂ Annotates arguments terms →
      Annotates (.expression (.symbol name :: arguments))
        (terms.foldl .app (.constant (.symbol name, instanceType)))

/-- HOL elaborates an instance annotation of the expression at the image of
the type. -/
def SchematicHOLTyped (space : Space) (expression type : Atom) : Prop :=
  ∃ term, Annotates expression term ∧ Elaborates (instanceSignature space) term (toTy type)

theorem elaborates_foldl_iff {space : Space} (function : InstanceTerm)
    (terms : List InstanceTerm) (result : Ty Atom) :
    Elaborates (instanceSignature space) (terms.foldl .app function) result ↔
      ∃ argumentTypes : List (Ty Atom),
        Elaborates (instanceSignature space) function (argumentTypes.foldr Ty.arr result) ∧
          List.Forall₂ (Elaborates (instanceSignature space)) terms argumentTypes :=
  elaborates_foldl_app_iff (signature := instanceSignature space)
    (fun term : InstanceTerm => term) function terms result

/-- A saturated application of a constant at an arrow instance elaborates
exactly at the instance's return type, when the arguments elaborate at its
argument types. -/
theorem elaborates_application_instance_iff {space : Space} {name : String}
    {instanceType returnType : Atom} {argumentTypes : List Atom}
    {terms : List InstanceTerm} {result : Ty Atom}
    (function : FunctionTypeRel instanceType argumentTypes returnType)
    (nonempty : argumentTypes ≠ [])
    (lengths : terms.length = argumentTypes.length) :
    Elaborates (instanceSignature space)
        (terms.foldl .app (.constant (.symbol name, instanceType))) result ↔
      InstanceOf space (.symbol name) instanceType ∧ result = toTy returnType ∧
        List.Forall₂ (fun term argumentType =>
          Elaborates (instanceSignature space) term (toTy argumentType)) terms argumentTypes := by
  rw [elaborates_foldl_iff]
  constructor
  · rintro ⟨holArguments, head, all⟩
    obtain ⟨instanceOf, typeEq⟩ := elaborates_instance_iff.mp head
    rw [toTy_of_functionType function nonempty, spineTy_eq_foldr] at typeEq
    have holLength : holArguments.length = (argumentTypes.map toTy).length := by
      rw [List.length_map, ← lengths]
      exact all.length_eq.symm
    obtain ⟨holEq, resultEq⟩ := foldr_arr_injective holLength typeEq
    subst holEq
    exact ⟨instanceOf, resultEq, List.forall₂_map_right_iff.mp all⟩
  · rintro ⟨instanceOf, rfl, all⟩
    refine ⟨argumentTypes.map toTy, ?_, List.forall₂_map_right_iff.mpr all⟩
    rw [← spineTy_eq_foldr, ← toTy_of_functionType function nonempty]
    exact elaborates_instance_iff.mpr ⟨instanceOf, rfl⟩

/-- The instance of a declared constant is determined by its declaration. -/
theorem instanceOf_iff {space : Space} {constant scheme instanceType : Atom}
    (declared : declaredType? space constant = some scheme) :
    InstanceOf space constant instanceType ↔
      ∃ valuation, FirstOrderValuation valuation ∧
        applyTypeValuation valuation scheme = instanceType := by
  constructor
  · rintro ⟨scheme', declared', valuation, firstOrder, rfl⟩
    rw [declared] at declared'
    cases declared'
    exact ⟨valuation, firstOrder, rfl⟩
  · rintro ⟨valuation, firstOrder, rfl⟩
    exact ⟨scheme, declared, valuation, firstOrder, rfl⟩

/-! ## Fresh scopes of an application -/

/-- The variables of freshened argument candidates avoid the scope they were
freshened against. -/
theorem argumentAlphaVariants_avoid :
    ∀ {avoid : List String} {sources targets : List Atom},
      ArgumentAlphaVariantsRel avoid sources targets →
      ∀ name ∈ TypeSubst.typeVarsList targets, name ∉ avoid
  | _, _, _, .nil _ => by simp [TypeSubst.typeVarsList]
  | _, _, _, .cons head tail => by
      intro name member
      simp only [TypeSubst.typeVarsList, List.mem_append] at member
      rcases member with member | member
      · obtain ⟨rename, _, presentation, avoids⟩ := head
        rw [presentation,
          Spec.Type.Presentation.ScopeObservation.typeVars_renameTypeVars] at member
        obtain ⟨source, sourceMember, rfl⟩ := List.mem_map.mp member
        exact avoids source sourceMember
      · intro inAvoid
        exact argumentAlphaVariants_avoid tail name member (List.mem_append_left _ inAvoid)

/-- Freshened argument candidates are injective renamings of their sources. -/
theorem argumentAlphaVariants_renamings :
    ∀ {avoid : List String} {sources targets : List Atom},
      ArgumentAlphaVariantsRel avoid sources targets →
      List.Forall₂ (fun source target => ∃ rename : String → String,
        Function.Injective rename ∧ target = renameTypeVars rename source) sources targets
  | _, _, _, .nil _ => .nil
  | _, _, _, .cons head tail => by
      obtain ⟨rename, injective, presentation, _⟩ := head
      exact .cons ⟨rename, injective, presentation⟩ (argumentAlphaVariants_renamings tail)

/-- Independent instances of the sources of freshened candidates combine into
one model of the candidates: the candidates' variables are pairwise
disjoint, and every name outside them keeps its base value. -/
theorem exists_argument_model (base : String → Atom) {avoid : List String}
    {sources fresh : List Atom} (variants : ArgumentAlphaVariantsRel avoid sources fresh) :
    ∀ {targets : List Atom},
      List.Forall₂ (fun source target => ∃ valuation, FirstOrderValuation valuation ∧
        applyTypeValuation valuation source = target) sources targets →
      ∃ model : String → Atom,
        (∀ name, name ∉ TypeSubst.typeVarsList fresh → model name = base name) ∧
        (FirstOrderValuation base → FirstOrderValuation model) ∧
        List.Forall₂ (fun freshType target => applyTypeValuation model freshType = target)
          fresh targets := by
  induction variants with
  | nil avoid =>
      intro targets instances
      cases instances
      exact ⟨base, fun _ _ => rfl, id, .nil⟩
  | @cons avoid source freshType sources freshTypes head tail ih =>
      intro targets instances
      cases instances with
      | @cons _ target _ targets instanceFact rest =>
          obtain ⟨valuation, firstOrder, instanceEq⟩ := instanceFact
          obtain ⟨tailModel, outside, tailFirstOrder, tailEqs⟩ := ih rest
          obtain ⟨rename, injective, presentation, _⟩ := head
          have tailAvoids := argumentAlphaVariants_avoid tail
          classical
          let model : String → Atom := fun name =>
            if name ∈ TypeSubst.typeVars freshType then
              valuation (Function.invFun rename name)
            else tailModel name
          refine ⟨model, ?_, ?_, ?_⟩
          · intro name notMember
            simp only [TypeSubst.typeVarsList, List.mem_append, not_or] at notMember
            simp [model, notMember.1, outside name notMember.2]
          · intro baseFirstOrder name
            by_cases member : name ∈ TypeSubst.typeVars freshType
            · simp only [model, if_pos member]
              exact firstOrder _
            · simp only [model, if_neg member]
              exact tailFirstOrder baseFirstOrder name
          · refine .cons ?_ ?_
            · rw [presentation, applyTypeValuation_renameTypeVars, ← instanceEq]
              apply applyTypeValuation_congr_of_typeVars
              intro name member
              have renamed : rename name ∈ TypeSubst.typeVars freshType := by
                rw [presentation,
                  Spec.Type.Presentation.ScopeObservation.typeVars_renameTypeVars]
                exact List.mem_map.mpr ⟨name, member, rfl⟩
              simp only [Function.comp_apply, model, if_pos renamed]
              rw [Function.leftInverse_invFun injective name]
            · refine forall₂_imp_of_mem tailEqs ?_
              intro other otherMember target equal
              rw [← equal]
              apply applyTypeValuation_congr_of_typeVars
              intro name member
              have notHead : name ∉ TypeSubst.typeVars freshType := by
                intro headMember
                exact tailAvoids name
                  (Spec.Type.Presentation.Freshness.typeVars_mem_typeVarsList_of_mem
                    otherMember name member)
                  (List.mem_append_right _ headMember)
              simp [model, notHead]

/-- Inversion of HE's exact relation at a saturated application of a declared
operator scheme whose arguments have singleton candidates.  The operator is
renamed apart by an injective renaming, the candidates are freshened in
pairwise disjoint scopes disjoint from the operator's, and either the
renamed argument types match the fresh candidates and the instantiated
renamed return type is emitted, or no match exists and the gradual
`%Undefined%` candidate is emitted. -/
theorem schematic_application_cases {space : Space} {name : String}
    {arguments argumentTypes : List Atom} {scheme returnType : Atom}
    (notState : name ≠ "StateValue")
    (annotationFree : getAnnotatedTypes space (.expression (.symbol name :: arguments)) = [])
    (declared : declaredType? space (.symbol name) = some scheme)
    (function : FunctionTypeRel scheme argumentTypes returnType)
    {packages : List TypePackage}
    (derivation : RuntimeTypePackagesRel space
      (.expression (.symbol name :: arguments)) packages) :
    ∃ packageLists : List (List TypePackage),
      List.Forall₂ (RuntimeTypePackagesRel space) arguments packageLists ∧
      ∀ actualTypes : List Atom,
        packageLists.map observedTypes = actualTypes.map (fun type => [type]) →
        ∃ (rename : String → String) (avoid : List String) (freshTypes : List Atom),
          Function.Injective rename ∧
          ArgumentAlphaVariantsRel avoid actualTypes freshTypes ∧
          (∀ freshName ∈ TypeSubst.typeVars (renameTypeVars rename scheme),
            freshName ∉ TypeSubst.typeVarsList freshTypes) ∧
          ((∃ substitution,
              PresentationArgumentListMatchRel
                (argumentTypes.map (renameTypeVars rename)) freshTypes [] substitution ∧
              packages = [inferredPackage substitution (renameTypeVars rename returnType)]) ∨
            ((∀ substitution, ¬PresentationArgumentListMatchRel
                (argumentTypes.map (renameTypeVars rename)) freshTypes [] substitution) ∧
              packages = [publishedPackage Atom.undefinedType])) := by
  have renamedFunction : ∀ rename : String → String,
      FunctionTypeRel (renameTypeVars rename scheme)
        (argumentTypes.map (renameTypeVars rename)) (renameTypeVars rename returnType) :=
    fun rename => (Spec.Type.Presentation.Alpha.functionTypeRel_renameTypeVars_iff
      rename scheme _ _).mpr ⟨_, _, function, rfl, rfl⟩
  cases derivation with
  | stateValue _ => exact absurd rfl notState
  | expressionKnown _ annotated nonempty =>
      have none := AnnotationTypesRel.unique annotated
        (expression_annotations_nil annotationFree)
      exact absurd none nonempty
  | expressionInferred _ _ operatorRel argumentRel observedArguments observedOperators
      _ argumentVariants operatorVariants separated matrix nonempty =>
      refine ⟨_, argumentRel, ?_⟩
      intro actualTypes observed
      have operatorsEq := constant_packages_eq declared operatorRel
      subst operatorsEq
      rw [observed] at observedArguments
      subst observedArguments observedOperators
      rw [orderedCartesian_singletons] at argumentVariants
      cases argumentVariants with
      | cons variant rest =>
          cases rest
          simp only [observedTypes, publishedPackage,
            Spec.Type.Presentation.RuntimeTypePackage.published, List.map_cons,
            List.map_nil] at operatorVariants
          cases operatorVariants with
          | cons operatorVariant restOperators =>
              cases restOperators
              obtain ⟨rename, injective, presentation, _⟩ := operatorVariant
              subst presentation
              refine ⟨rename, _, _, injective, variant,
                fun freshName member => separated.atom (by simp) (by simp) member, ?_⟩
              obtain ⟨outcome, outcomeRel, resultsEq⟩ :=
                applicationPackageMatrix_single_iff.mp matrix
              cases outcomeRel with
              | success success =>
                  cases success with
                  | mk shape fold =>
                      obtain ⟨rfl, rfl⟩ := FunctionTypeRel.unique shape (renamedFunction rename)
                      exact Or.inl ⟨_, fold, resultsEq⟩
              | failure _ =>
                  simp at resultsEq
                  exact absurd resultsEq nonempty
  | expressionUndefined _ _ operatorRel argumentRel observedArguments observedOperators
      _ argumentVariants operatorVariants separated matrix =>
      refine ⟨_, argumentRel, ?_⟩
      intro actualTypes observed
      have operatorsEq := constant_packages_eq declared operatorRel
      subst operatorsEq
      rw [observed] at observedArguments
      subst observedArguments observedOperators
      rw [orderedCartesian_singletons] at argumentVariants
      cases argumentVariants with
      | cons variant rest =>
          cases rest
          simp only [observedTypes, publishedPackage,
            Spec.Type.Presentation.RuntimeTypePackage.published, List.map_cons,
            List.map_nil] at operatorVariants
          cases operatorVariants with
          | cons operatorVariant restOperators =>
              cases restOperators
              obtain ⟨rename, injective, presentation, _⟩ := operatorVariant
              subst presentation
              refine ⟨rename, _, _, injective, variant,
                fun freshName member => separated.atom (by simp) (by simp) member, ?_⟩
              obtain ⟨outcome, outcomeRel, resultsEq⟩ :=
                applicationPackageMatrix_single_iff.mp matrix
              cases outcomeRel with
              | success _ => simp at resultsEq
              | failure noSuccess =>
                  refine Or.inr ⟨fun substitution fold => ?_, rfl⟩
                  exact noSuccess _ (ApplicationPackageSuccessRel.mk (renamedFunction rename) fold)

/-! ## Singleton candidates -/

/-- Collect the singleton candidates of the arguments of an application. -/
theorem collect_singletons {space : Space} :
    ∀ {arguments : List Atom} {packageLists : List (List TypePackage)},
      List.Forall₂ (RuntimeTypePackagesRel space) arguments packageLists →
      (∀ argument ∈ arguments, ∀ {packages : List TypePackage},
        RuntimeTypePackagesRel space argument packages →
          ∃ type, observedTypes packages = [type]) →
      ∃ actualTypes : List Atom,
        packageLists.map observedTypes = actualTypes.map (fun type => [type]) ∧
        List.Forall₂ (fun argument type => ∃ packages,
          RuntimeTypePackagesRel space argument packages ∧
            observedTypes packages = [type]) arguments actualTypes
  | _, _, .nil, _ => ⟨[], rfl, .nil⟩
  | _, _, .cons head tail, shape => by
      obtain ⟨type, observed⟩ := shape _ (by simp) head
      obtain ⟨actualTypes, mapped, all⟩ := collect_singletons tail
        (fun argument member => shape argument (List.mem_cons_of_mem _ member))
      exact ⟨type :: actualTypes, by simp [observed, mapped],
        .cons ⟨_, head, observed⟩ all⟩

/-- On the fragment every exact candidate list is a singleton. -/
theorem schematic_shape {space : Space} {expression : Atom}
    (term : SchematicTerm space expression) :
    ∀ {packages : List TypePackage}, RuntimeTypePackagesRel space expression packages →
      ∃ type, observedTypes packages = [type] := by
  induction term with
  | constant declared _ =>
      intro packages derivation
      rw [constant_packages_eq declared derivation]
      exact ⟨_, rfl⟩
  | application notState annotationFree declared operator _ _ argumentIH =>
      intro packages derivation
      obtain ⟨packageLists, argumentRel, cases⟩ :=
        schematic_application_cases notState annotationFree declared operator.function
          derivation
      obtain ⟨actualTypes, mapped, _⟩ := collect_singletons argumentRel argumentIH
      obtain ⟨_, _, _, _, _, _, success | failure⟩ := cases actualTypes mapped
      · obtain ⟨substitution, _, rfl⟩ := success
        exact ⟨_, rfl⟩
      · rw [failure.2]
        exact ⟨_, rfl⟩

/-! ## From HE to HOL -/

private theorem forall₂_exists_choose {α β γ : Type} {first : α → γ → Prop}
    {second : γ → β → Prop} :
    ∀ {lefts : List α} {rights : List β},
      List.Forall₂ (fun left right => ∃ middle, first left middle ∧ second middle right)
        lefts rights →
      ∃ middles : List γ,
        List.Forall₂ first lefts middles ∧ List.Forall₂ second middles rights
  | _, _, .nil => ⟨[], .nil, .nil⟩
  | _, _, .cons ⟨middle, left, right⟩ tail => by
      obtain ⟨middles, lefts, rights⟩ := forall₂_exists_choose tail
      exact ⟨middle :: middles, .cons left lefts, .cons right rights⟩

private theorem forall₂_comp {α β γ : Type} {first : α → β → Prop}
    {second : β → γ → Prop} :
    ∀ {lefts : List α} {middles : List β} {rights : List γ},
      List.Forall₂ first lefts middles → List.Forall₂ second middles rights →
      List.Forall₂ (fun left right => ∃ middle, first left middle ∧ second middle right)
        lefts rights
  | _, _, _, .nil, .nil => .nil
  | _, _, _, .cons head tail, .cons head' tail' =>
      .cons ⟨_, head, head'⟩ (forall₂_comp tail tail')

/-- HE's exact candidate of a fragment expression, with no `%Undefined%`
fallback at any subatom, is first-order, and HOL elaborates an instance
annotation of the expression at every ground first-order instance of it. -/
theorem annotated_of_exact {space : Space} {expression : Atom}
    (term : SchematicTerm space expression) :
    NoUndefinedFallback space expression →
    ∀ {packages : List TypePackage}, RuntimeTypePackagesRel space expression packages →
    ∀ {principal : Atom}, observedTypes packages = [principal] →
      ReservedFree principal ∧
      ∀ valuation, FirstOrderValuation valuation →
        SchematicHOLTyped space expression (applyTypeValuation valuation principal) := by
  induction term with
  | @constant atom scheme declared free =>
      intro _ packages derivation principal observed
      rw [constant_packages_eq declared derivation] at observed
      simp only [observedTypes, publishedPackage,
        Spec.Type.Presentation.RuntimeTypePackage.published, List.map_cons, List.map_nil,
        List.cons.injEq, and_true] at observed
      subst observed
      refine ⟨free, fun valuation firstOrder => ?_⟩
      refine ⟨.constant (atom, applyTypeValuation valuation scheme), ?_, ?_⟩
      · rcases SchematicTerm.constant_shape declared with ⟨name, rfl⟩ | ⟨value, rfl⟩
        · exact .symbol _ _
        · exact .grounded _ _
      · exact elaborates_instance_iff.mpr
          ⟨⟨scheme, declared, valuation, firstOrder, rfl⟩, rfl⟩
  | @application name arguments argumentTypes scheme returnType notState annotationFree
      declared operator lengths fragmentArguments argumentIH =>
      intro noFallback packages derivation principal observed
      obtain ⟨packageLists, argumentRel, cases⟩ :=
        schematic_application_cases notState annotationFree declared operator.function
          derivation
      obtain ⟨actualTypes, mapped, actualAll⟩ := collect_singletons argumentRel
        (fun argument member => schematic_shape (fragmentArguments argument member))
      -- Each argument candidate is first-order and grounds HOL instances.
      have argumentFacts : List.Forall₂ (fun argument actual => ReservedFree actual ∧
          ∀ valuation, FirstOrderValuation valuation →
            SchematicHOLTyped space argument (applyTypeValuation valuation actual))
          arguments actualTypes := by
        refine forall₂_imp_of_mem actualAll ?_
        intro argument member actual ⟨argumentPackages, argumentDerivation, argumentObserved⟩
        exact argumentIH argument member
          (fun sub inner => noFallback sub
            (inner.trans (Subatom.of_mem (List.mem_cons_of_mem _ member))))
          argumentDerivation argumentObserved
      have actualFree : ∀ actual ∈ actualTypes, ReservedFree actual := by
        intro actual member
        obtain ⟨_, _, facts⟩ := forall₂_right_mem argumentFacts actual member
        exact facts.1
      obtain ⟨rename, avoid, freshTypes, _, variants, _, success | failure⟩ :=
        cases actualTypes mapped
      swap
      · rw [failure.2] at observed
        simp only [observedTypes, publishedPackage,
          Spec.Type.Presentation.RuntimeTypePackage.published, List.map_cons, List.map_nil,
          List.cons.injEq, and_true] at observed
        subst observed
        exact absurd ⟨_, derivation, by rw [failure.2]; rfl⟩ (noFallback _ .refl)
      obtain ⟨substitution, fold, rfl⟩ := success
      simp only [observedTypes, inferredPackage, List.map_cons, List.map_nil,
        List.cons.injEq, and_true] at observed
      subst observed
      have renamedOperator := operator.rename rename
      have expectedFree : ∀ atom ∈ argumentTypes.map (renameTypeVars rename),
          ReservedFree atom := renamedOperator.arguments
      have renamings := argumentAlphaVariants_renamings variants
      have freshFree : ∀ atom ∈ freshTypes, ReservedFree atom := by
        intro atom member
        obtain ⟨actual, actualMember, renameActual, _, rfl⟩ :=
          forall₂_right_mem renamings atom member
        exact reservedFree_renameTypeVars renameActual (actualFree actual actualMember)
      have normal :=
        Spec.Type.Presentation.ExactNormal.PresentationArgumentListMatchRel.output_normal
          fold TypeSubst.normal_empty
      have theory := presentationArgumentList_solutions fold TypeSubst.normal_empty
      have emptySatisfied : ∀ valuation, TypeSubstSatisfied valuation [] := by
        intro valuation name value member
        simp at member
      -- Every model of the output solves the argument equations, and conversely.
      have equations : ∀ valuation, TypeSubstSatisfied valuation substitution ↔
          List.Forall₂ (fun left right =>
            applyTypeValuation valuation left = applyTypeValuation valuation right)
            (argumentTypes.map (renameTypeVars rename)) freshTypes := by
        intro valuation
        rw [theory valuation, ← forall₂_corePlusR2_iff_eq valuation expectedFree freshFree]
        exact ⟨fun both => both.2, fun all => ⟨emptySatisfied valuation, all⟩⟩
      have projectedEquations : ∀ valuation, TypeSubstSatisfied valuation substitution →
          TypeSubstSatisfied (fun name => project (valuation name)) substitution := by
        intro valuation satisfied
        apply (equations _).mpr
        refine forall₂_imp_of_mem₂ ((equations valuation).mp satisfied) ?_
        intro left leftMember right rightMember equal
        rw [← project_applyTypeValuation valuation (expectedFree left leftMember),
          ← project_applyTypeValuation valuation (freshFree right rightMember), equal]
      have presented := normal_presentedValuation_satisfied normal
      have returnFree : ReservedFree (renameTypeVars rename returnType) :=
        renamedOperator.result
      -- The principal candidate is first-order.
      have principalFree :
          ReservedFree (substitution.apply (renameTypeVars rename returnType)) := by
        have absorbed := (projectedEquations _ presented).absorbs (renameTypeVars rename returnType)
        have ground := (projected_firstOrder (presentedValuation substitution)).ground returnFree
        rw [← absorbed] at ground
        exact reservedFree_of_applyTypeValuation ground.1
      refine ⟨principalFree, fun valuation firstOrder => ?_⟩
      -- A model of the output that sends the principal candidate to its instance.
      let model : String → Atom := fun name =>
        project (applyTypeValuation valuation (presentedValuation substitution name))
      have modelSatisfied : TypeSubstSatisfied model substitution :=
        projectedEquations _ (typeSubstSatisfied_comp presented valuation)
      have modelFirstOrder : FirstOrderValuation model :=
        projected_firstOrder (fun name =>
          applyTypeValuation valuation (presentedValuation substitution name))
      have principalInstance : applyTypeValuation model (renameTypeVars rename returnType) =
          applyTypeValuation valuation (substitution.apply (renameTypeVars rename returnType)) := by
        show applyTypeValuation (fun name => project (applyTypeValuation valuation
          (presentedValuation substitution name))) _ = _
        rw [← project_applyTypeValuation _ returnFree,
          ← applyTypeValuation_comp valuation (presentedValuation substitution),
          applyTypeValuation_presented_eq_apply]
        exact project_of_groundFirstOrder (firstOrder.ground principalFree)
      -- The operator instance and the argument instances read off the model.
      let operatorValuation : String → Atom := model ∘ rename
      have operatorFirstOrder : FirstOrderValuation operatorValuation :=
        fun name => modelFirstOrder (rename name)
      obtain ⟨instanceFunction, _⟩ := operator.instantiate operatorFirstOrder
      have modelEquations := (equations model).mp modelSatisfied
      have flipped : List.Forall₂ (fun freshType expected =>
          applyTypeValuation model (renameTypeVars rename expected) =
            applyTypeValuation model freshType) freshTypes argumentTypes :=
        List.forall₂_map_right_iff.mp
          (List.Forall₂.flip (R := fun freshType expected =>
            applyTypeValuation model expected = applyTypeValuation model freshType)
            modelEquations)
      have argumentTyped : List.Forall₂ (fun argument argumentType =>
          SchematicHOLTyped space argument
            (applyTypeValuation operatorValuation argumentType)) arguments argumentTypes := by
        refine (forall₂_comp (forall₂_comp argumentFacts renamings) flipped).imp ?_
        rintro argument argumentType
          ⟨freshType, ⟨actual, facts, renameActual, _, rfl⟩, equal⟩
        have typed := facts.2 (model ∘ renameActual)
          (fun name => modelFirstOrder (renameActual name))
        rw [← applyTypeValuation_renameTypeVars, ← equal,
          applyTypeValuation_renameTypeVars] at typed
        exact typed
      obtain ⟨terms, annotations, elaborations⟩ := forall₂_exists_choose argumentTyped
      refine ⟨terms.foldl .app (.constant (.symbol name,
        applyTypeValuation operatorValuation scheme)), .application annotations, ?_⟩
      apply (elaborates_application_instance_iff instanceFunction
        (by simpa using operator.nonempty)
        (by rw [List.length_map, ← lengths]; exact annotations.length_eq.symm)).mpr
      refine ⟨⟨scheme, declared, operatorValuation, operatorFirstOrder, rfl⟩, ?_,
        List.forall₂_map_right_iff.mpr elaborations⟩
      rw [← principalInstance, applyTypeValuation_renameTypeVars]

/-! ## From HOL to HE -/

/-- A first-order valuation that keeps the instance of an operator scheme on
the operator's renamed variables and gives every other name the filler
`Type`. -/
private theorem exists_operator_base (rename : String → String)
    (injective : Function.Injective rename) (scheme : Atom) {valuation : String → Atom}
    (firstOrder : FirstOrderValuation valuation) :
    ∃ base : String → Atom, FirstOrderValuation base ∧
      ∀ name ∈ TypeSubst.typeVars scheme, base (rename name) = valuation name := by
  classical
  refine ⟨fun name => if name ∈ TypeSubst.typeVars (renameTypeVars rename scheme)
    then valuation (Function.invFun rename name) else .symbol "Type", ?_, ?_⟩
  · intro name
    by_cases member : name ∈ TypeSubst.typeVars (renameTypeVars rename scheme)
    · simp only [if_pos member]
      exact firstOrder _
    · simp only [if_neg member]
      exact ⟨reservedFree_symbol_iff.mpr type_not_reserved, rfl⟩
  · intro name member
    have renamed : rename name ∈ TypeSubst.typeVars (renameTypeVars rename scheme) := by
      rw [Spec.Type.Presentation.ScopeObservation.typeVars_renameTypeVars]
      exact List.mem_map.mpr ⟨name, member, rfl⟩
    simp only [if_pos renamed]
    rw [Function.leftInverse_invFun injective name]

private theorem typeVars_component {scheme returnType component : Atom}
    {argumentTypes : List Atom} (function : FunctionTypeRel scheme argumentTypes returnType)
    (member : component ∈ argumentTypes ∨ component = returnType) :
    ∀ name ∈ TypeSubst.typeVars component, name ∈ TypeSubst.typeVars scheme := by
  intro name occurs
  rw [function]
  simp only [TypeSubst.typeVars]
  apply Spec.Type.Presentation.Freshness.typeVars_mem_typeVarsList_of_mem (atom := component)
  · rcases member with member | rfl
    · simp [member]
    · simp
  · exact occurs

/-- A HOL-typed instance annotation of a fragment expression has a ground
first-order type; the expression has no `%Undefined%` fallback, and every
exact candidate list of it is a single first-order candidate of which that
type is an instance. -/
theorem exact_of_annotated {space : Space} {expression : Atom}
    (term : SchematicTerm space expression) :
    ∀ {holTerm : InstanceTerm} {holType : Ty Atom},
      Annotates expression holTerm → Elaborates (instanceSignature space) holTerm holType →
      ∃ type, GroundFirstOrder type ∧ holType = toTy type ∧
        NoUndefinedFallback space expression ∧
        ∀ {packages : List TypePackage}, RuntimeTypePackagesRel space expression packages →
          ∃ principal, observedTypes packages = [principal] ∧ ReservedFree principal ∧
            ∃ valuation, FirstOrderValuation valuation ∧
              applyTypeValuation valuation principal = type := by
  induction term with
  | @constant atom scheme declared free =>
      intro holTerm holType annotates elaborates
      have shape := SchematicTerm.constant_shape declared
      have holTermEq : ∃ instanceType, holTerm = .constant (atom, instanceType) := by
        rcases shape with ⟨name, rfl⟩ | ⟨value, rfl⟩
        · cases annotates
          exact ⟨_, rfl⟩
        · cases annotates
          exact ⟨_, rfl⟩
      obtain ⟨instanceType, rfl⟩ := holTermEq
      obtain ⟨instanceOf, rfl⟩ := elaborates_instance_iff.mp elaborates
      obtain ⟨valuation, firstOrder, rfl⟩ := (instanceOf_iff declared).mp instanceOf
      have packagesOf : ∀ {packages : List TypePackage},
          RuntimeTypePackagesRel space atom packages → observedTypes packages = [scheme] := by
        intro packages derivation
        rw [constant_packages_eq declared derivation]
        rfl
      refine ⟨_, firstOrder.ground free, rfl, ?_, ?_⟩
      · intro sub occurs subExact
        have subEq : sub = atom := by
          rcases shape with ⟨name, rfl⟩ | ⟨value, rfl⟩
          · exact occurs.symbol_eq
          · exact occurs.grounded_eq
        subst subEq
        obtain ⟨packages, derivation, observed⟩ := subExact
        rw [packagesOf derivation] at observed
        simp only [List.cons.injEq, and_true] at observed
        exact free.ne_undefined observed
      · intro packages derivation
        exact ⟨scheme, packagesOf derivation, free, valuation, firstOrder, rfl⟩
  | @application name arguments argumentTypes scheme returnType notState annotationFree
      declared operator lengths _ argumentIH =>
      intro holTerm holType annotates elaborates
      cases annotates with
      | @application _ instanceType _ terms annotations =>
          -- The head is an instance of the operator scheme.
          obtain ⟨holArguments, headElaborates, _⟩ :=
            (elaborates_foldl_iff _ terms holType).mp elaborates
          obtain ⟨instanceOf, _⟩ := elaborates_instance_iff.mp headElaborates
          obtain ⟨operatorValuation, operatorFirstOrder, rfl⟩ :=
            (instanceOf_iff declared).mp instanceOf
          obtain ⟨instanceFunction, _⟩ := operator.instantiate operatorFirstOrder
          obtain ⟨_, rfl, argumentElaborations⟩ :=
            (elaborates_application_instance_iff instanceFunction
              (by simpa using operator.nonempty)
              (by rw [List.length_map, ← lengths]; exact annotations.length_eq.symm)).mp
              elaborates
          -- Each argument is HOL-typed at the instance of its argument type.
          have argumentFacts : List.Forall₂ (fun argument argumentType =>
              NoUndefinedFallback space argument ∧
              ∀ {packages : List TypePackage}, RuntimeTypePackagesRel space argument packages →
                ∃ principal, observedTypes packages = [principal] ∧ ReservedFree principal ∧
                  ∃ valuation, FirstOrderValuation valuation ∧
                    applyTypeValuation valuation principal =
                      applyTypeValuation operatorValuation argumentType)
              arguments argumentTypes := by
            have paired := forall₂_comp annotations
              (List.forall₂_map_right_iff.mp argumentElaborations)
            refine forall₂_imp_of_mem₂ paired ?_
            rintro argument member argumentType typeMember ⟨holArgument, annotated, typed⟩
            obtain ⟨found, ground, holEq, noFallback, all⟩ :=
              argumentIH argument member annotated typed
            have argumentGround : GroundFirstOrder
                (applyTypeValuation operatorValuation argumentType) :=
              operatorFirstOrder.ground (operator.arguments _ typeMember)
            have equal := toTy_injective argumentGround.static ground.static holEq
            subst equal
            exact ⟨noFallback, all⟩
          have operatorGround : GroundFirstOrder
              (applyTypeValuation operatorValuation returnType) :=
            operatorFirstOrder.ground operator.result
          -- Every exact candidate list of the application is a first-order
          -- candidate with the HOL type as an instance.
          have principalOf : ∀ {packages : List TypePackage},
              RuntimeTypePackagesRel space (.expression (.symbol name :: arguments)) packages →
              ∃ principal, observedTypes packages = [principal] ∧ ReservedFree principal ∧
                ∃ valuation, FirstOrderValuation valuation ∧
                  applyTypeValuation valuation principal =
                    applyTypeValuation operatorValuation returnType := by
            intro packages derivation
            obtain ⟨packageLists, argumentRel, cases⟩ :=
              schematic_application_cases notState annotationFree declared operator.function
                derivation
            have candidates : ∀ argument ∈ arguments, ∀ {packages : List TypePackage},
                RuntimeTypePackagesRel space argument packages →
                  ∃ type, observedTypes packages = [type] := by
              intro argument member packages argumentDerivation
              obtain ⟨argumentType, _, facts⟩ :=
                forall₂_left_mem argumentFacts argument member
              obtain ⟨principal, observed, _⟩ := facts.2 argumentDerivation
              exact ⟨principal, observed⟩
            obtain ⟨actualTypes, mapped, actualAll⟩ := collect_singletons argumentRel candidates
            obtain ⟨rename, avoid, freshTypes, injective, variants, separated, outcome⟩ :=
              cases actualTypes mapped
            -- The argument candidates are first-order, with instances at the
            -- operator instance's argument types.
            have instanceFacts : List.Forall₂ (fun actual argumentType =>
                ReservedFree actual ∧ ∃ valuation, FirstOrderValuation valuation ∧
                  applyTypeValuation valuation actual =
                    applyTypeValuation operatorValuation argumentType)
                actualTypes argumentTypes := by
              have paired := forall₂_comp (List.Forall₂.flip (R := fun actual argument =>
                ∃ packages, RuntimeTypePackagesRel space argument packages ∧
                  observedTypes packages = [actual]) actualAll) argumentFacts
              refine paired.imp ?_
              rintro actual argumentType ⟨argument, ⟨argumentPackages, argumentDerivation,
                argumentObserved⟩, facts⟩
              obtain ⟨principal, observed, free, valuation, firstOrder, equal⟩ :=
                facts.2 argumentDerivation
              rw [argumentObserved] at observed
              simp only [List.cons.injEq, and_true] at observed
              subst observed
              exact ⟨free, valuation, firstOrder, equal⟩
            have actualFree : ∀ actual ∈ actualTypes, ReservedFree actual := by
              intro actual member
              obtain ⟨_, _, facts⟩ := forall₂_left_mem instanceFacts actual member
              exact facts.1
            have instances : List.Forall₂ (fun actual target => ∃ valuation,
                FirstOrderValuation valuation ∧ applyTypeValuation valuation actual = target)
                actualTypes (argumentTypes.map (applyTypeValuation operatorValuation)) :=
              List.forall₂_map_right_iff.mpr (instanceFacts.imp (fun _ _ facts => facts.2))
            have renamings := argumentAlphaVariants_renamings variants
            have freshFree : ∀ atom ∈ freshTypes, ReservedFree atom := by
              intro atom member
              obtain ⟨actual, actualMember, renameActual, _, rfl⟩ :=
                forall₂_right_mem renamings atom member
              exact reservedFree_renameTypeVars renameActual (actualFree actual actualMember)
            -- One model of all argument equations, built from the operator
            -- instance and the argument instances.
            obtain ⟨base, baseFirstOrder, baseAgrees⟩ :=
              exists_operator_base rename injective scheme operatorFirstOrder
            obtain ⟨model, outside, modelFirstOrderOf, freshEquations⟩ :=
              exists_argument_model base variants instances
            have modelFirstOrder := modelFirstOrderOf baseFirstOrder
            have operatorAgrees : ∀ component,
                (component ∈ argumentTypes ∨ component = returnType) →
                applyTypeValuation model (renameTypeVars rename component) =
                  applyTypeValuation operatorValuation component := by
              intro component member
              rw [applyTypeValuation_renameTypeVars]
              apply applyTypeValuation_congr_of_typeVars
              intro variableName occurs
              have inScheme := typeVars_component operator.function member variableName occurs
              have renamedMember : rename variableName ∈
                  TypeSubst.typeVars (renameTypeVars rename scheme) := by
                rw [Spec.Type.Presentation.ScopeObservation.typeVars_renameTypeVars]
                exact List.mem_map.mpr ⟨variableName, inScheme, rfl⟩
              simp only [Function.comp_apply]
              rw [outside _ (separated _ renamedMember), baseAgrees variableName inScheme]
            have modelEquations : List.Forall₂ (fun left right =>
                applyTypeValuation model left = applyTypeValuation model right)
                (argumentTypes.map (renameTypeVars rename)) freshTypes := by
              have mappedFresh : List.Forall₂ (fun freshType argumentType =>
                  applyTypeValuation model freshType =
                    applyTypeValuation operatorValuation argumentType) freshTypes argumentTypes :=
                List.forall₂_map_right_iff.mp freshEquations
              have flippedFresh : List.Forall₂ (fun argumentType freshType =>
                  applyTypeValuation model freshType =
                    applyTypeValuation operatorValuation argumentType) argumentTypes freshTypes :=
                List.Forall₂.flip mappedFresh
              refine List.forall₂_map_left_iff.mpr (forall₂_imp_of_mem flippedFresh ?_)
              intro argumentType member freshType equal
              rw [operatorAgrees argumentType (Or.inl member), equal]
            have consistent := (forall₂_corePlusR2_iff_eq model
              (operator.rename rename).arguments freshFree).mpr modelEquations
            rcases outcome with ⟨substitution, fold, rfl⟩ | ⟨noFold, rfl⟩
            · have satisfied : TypeSubstSatisfied model substitution :=
                (presentationArgumentList_solutions fold TypeSubst.normal_empty model).mpr
                  ⟨fun _ _ member => by simp at member, consistent⟩
              have absorbed := satisfied.absorbs (renameTypeVars rename returnType)
              rw [operatorAgrees returnType (Or.inr rfl)] at absorbed
              refine ⟨substitution.apply (renameTypeVars rename returnType), ?_, ?_, model,
                modelFirstOrder, absorbed⟩
              · simp [observedTypes, inferredPackage]
              · have ground := operatorGround
                rw [← absorbed] at ground
                exact reservedFree_of_applyTypeValuation ground.1
            · exfalso
              obtain ⟨substitution, fold⟩ :=
                (presentationArgumentList_exists_iff _ _).mpr ⟨model, consistent⟩
              exact noFold substitution fold
          refine ⟨applyTypeValuation operatorValuation returnType, operatorGround, rfl, ?_,
            principalOf⟩
          intro sub occurs subExact
          rcases occurs.expression_cases with rfl | ⟨child, member, inner⟩
          · obtain ⟨packages, derivation, observed⟩ := subExact
            obtain ⟨principal, principalObserved, principalFree, _⟩ := principalOf derivation
            rw [principalObserved] at observed
            simp only [List.cons.injEq, and_true] at observed
            subst observed
            exact principalFree.ne_undefined rfl
          · simp only [List.mem_cons] at member
            rcases member with rfl | member
            · rw [inner.symbol_eq] at subExact
              obtain ⟨packages, derivation, observed⟩ := subExact
              rw [constant_packages_eq declared derivation] at observed
              simp only [observedTypes, publishedPackage,
                Spec.Type.Presentation.RuntimeTypePackage.published, List.map_cons,
                List.map_nil, List.cons.injEq, and_true] at observed
              have function := operator.function
              rw [observed] at function
              simp [FunctionTypeRel, Atom.undefinedType] at function
            · obtain ⟨argumentType, _, facts⟩ := forall₂_left_mem argumentFacts child member
              exact facts.1 sub inner subExact

/-! ## Agreement -/

/-- **Type variables are HOL type instances.**  For a saturated first-order
expression over schematic declarations and a static type `T`, HOL elaborates
an instance annotation of the expression at the image of `T` exactly when no
subatom of the expression falls back to `%Undefined%` and HE's exact relation
assigns it a single candidate `U` of which `T` is a ground first-order
instance. -/
theorem schematic_hol_iff_exact {space : Space} {expression type : Atom}
    (term : SchematicTerm space expression) (static : StaticType type) :
    SchematicHOLTyped space expression type ↔
      NoUndefinedFallback space expression ∧
        ∃ principal, ExactTypes space expression [principal] ∧
          ∃ valuation, FirstOrderValuation valuation ∧
            applyTypeValuation valuation principal = type := by
  constructor
  · rintro ⟨holTerm, annotates, elaborates⟩
    obtain ⟨found, ground, holEq, noFallback, all⟩ :=
      exact_of_annotated term annotates elaborates
    have equal := toTy_injective static ground.static holEq
    subst equal
    obtain ⟨packages, derivation⟩ :=
      Spec.Type.Presentation.Exact.runtimeTypePackages_exists space expression
    obtain ⟨principal, observed, _, valuation, firstOrder, instanceEq⟩ := all derivation
    exact ⟨noFallback, principal, ⟨packages, derivation, observed⟩, valuation, firstOrder,
      instanceEq⟩
  · rintro ⟨noFallback, principal, ⟨packages, derivation, observed⟩, valuation,
      firstOrder, rfl⟩
    exact (annotated_of_exact term noFallback derivation observed).2 valuation firstOrder

/-- **HE's candidate is the principal type scheme.**  Any two exact candidates
of a fragment expression without `%Undefined%` fallback have the same ground
first-order instances. -/
theorem exact_candidates_same_instances {space : Space} {expression : Atom}
    (term : SchematicTerm space expression) (noFallback : NoUndefinedFallback space expression)
    {left right : Atom} (leftExact : ExactTypes space expression [left])
    (rightExact : ExactTypes space expression [right]) (type : Atom) :
    (∃ valuation, FirstOrderValuation valuation ∧ applyTypeValuation valuation left = type) ↔
      ∃ valuation, FirstOrderValuation valuation ∧
        applyTypeValuation valuation right = type := by
  have oneWay : ∀ {first second : Atom}, ExactTypes space expression [first] →
      ExactTypes space expression [second] →
      (∃ valuation, FirstOrderValuation valuation ∧
        applyTypeValuation valuation first = type) →
      ∃ valuation, FirstOrderValuation valuation ∧
        applyTypeValuation valuation second = type := by
    rintro first second ⟨packages, derivation, observed⟩ ⟨packages', derivation', observed'⟩
      ⟨valuation, firstOrder, rfl⟩
    have firstFacts := annotated_of_exact term noFallback derivation observed
    obtain ⟨holTerm, annotates, elaborates⟩ := firstFacts.2 valuation firstOrder
    obtain ⟨found, ground, holEq, _, all⟩ := exact_of_annotated term annotates elaborates
    have equal := toTy_injective (firstOrder.ground firstFacts.1).static ground.static holEq
    obtain ⟨principal, principalObserved, _, valuation', firstOrder', instanceEq⟩ :=
      all derivation'
    rw [observed'] at principalObserved
    simp only [List.cons.injEq, and_true] at principalObserved
    subst principalObserved
    exact ⟨valuation', firstOrder', by rw [instanceEq, equal]⟩
  exact ⟨oneWay leftExact rightExact, oneWay rightExact leftExact⟩

/-- **A schematic arrow constant on its own.**  HOL elaborates the constant at
the image of a static type exactly when the type is a ground first-order
instance of its declared scheme, which is its single exact candidate. -/
theorem operator_constant_hol_iff {space : Space} {atom scheme returnType : Atom}
    {argumentTypes : List Atom} (declared : declaredType? space atom = some scheme)
    (operator : OperatorScheme scheme argumentTypes returnType) {type : Atom}
    (static : StaticType type) :
    SchematicHOLTyped space atom type ↔
      NoUndefinedFallback space atom ∧
        ∃ principal, ExactTypes space atom [principal] ∧
          ∃ valuation, FirstOrderValuation valuation ∧
            applyTypeValuation valuation principal = type := by
  have shape := SchematicTerm.constant_shape declared
  have packagesOf : ∀ {packages : List TypePackage},
      RuntimeTypePackagesRel space atom packages → observedTypes packages = [scheme] := by
    intro packages derivation
    rw [constant_packages_eq declared derivation]
    rfl
  have noFallback : NoUndefinedFallback space atom := by
    intro sub occurs subExact
    have subEq : sub = atom := by
      rcases shape with ⟨name, rfl⟩ | ⟨value, rfl⟩
      · exact occurs.symbol_eq
      · exact occurs.grounded_eq
    subst subEq
    obtain ⟨packages, derivation, observed⟩ := subExact
    rw [packagesOf derivation] at observed
    simp only [List.cons.injEq, and_true] at observed
    have function := operator.function
    rw [observed] at function
    simp [FunctionTypeRel, Atom.undefinedType] at function
  constructor
  · rintro ⟨holTerm, annotates, elaborates⟩
    have holTermEq : ∃ instanceType, holTerm = .constant (atom, instanceType) := by
      rcases shape with ⟨name, rfl⟩ | ⟨value, rfl⟩
      · cases annotates
        exact ⟨_, rfl⟩
      · cases annotates
        exact ⟨_, rfl⟩
    obtain ⟨instanceType, rfl⟩ := holTermEq
    obtain ⟨instanceOf, holEq⟩ := elaborates_instance_iff.mp elaborates
    obtain ⟨valuation, firstOrder, rfl⟩ := (instanceOf_iff declared).mp instanceOf
    have equal := toTy_injective static (operator.instantiate firstOrder).2 holEq
    subst equal
    exact ⟨noFallback, scheme, ⟨_, constant_packages declared, rfl⟩, valuation, firstOrder,
      rfl⟩
  · rintro ⟨_, principal, ⟨packages, derivation, observed⟩, valuation, firstOrder, rfl⟩
    rw [packagesOf derivation] at observed
    simp only [List.cons.injEq, and_true] at observed
    subst observed
    refine ⟨.constant (atom, applyTypeValuation valuation scheme), ?_,
      elaborates_instance_iff.mpr ⟨⟨_, declared, valuation, firstOrder, rfl⟩, rfl⟩⟩
    rcases shape with ⟨name, rfl⟩ | ⟨value, rfl⟩
    · exact .symbol _ _
    · exact .grounded _ _

/-! ## Boundary examples -/

private def listOf (element : Atom) : Atom := .expression [.symbol "List", element]

private def arrowType (arguments : List Atom) (result : Atom) : Atom :=
  .expression (.symbol "->" :: (arguments ++ [result]))

/-- `(: zero Nat)`, `(: nil (List $t))` and `(: cons (-> $t (List $t) (List $t)))`. -/
def listSpace : Space :=
  Space.ofList [SpecBoundary.annotation "zero" (.symbol "Nat"),
    SpecBoundary.annotation "nil" (listOf (.var "t")),
    SpecBoundary.annotation "cons"
      (arrowType [.var "t", listOf (.var "t")] (listOf (.var "t")))]

private theorem list_zero :
    declaredType? listSpace (.symbol "zero") = some (.symbol "Nat") := by
  decide

private theorem list_nil :
    declaredType? listSpace (.symbol "nil") = some (listOf (.var "t")) := by
  decide

private theorem list_cons : declaredType? listSpace (.symbol "cons") =
    some (arrowType [.var "t", listOf (.var "t")] (listOf (.var "t"))) := by
  decide

private theorem nat_free : ReservedFree (.symbol "Nat") :=
  reservedFree_symbol_iff.mpr (by decide)

private theorem listOf_free {element : Atom} (free : ReservedFree element) :
    ReservedFree (listOf element) := by
  refine reservedFree_expression_iff.mpr ?_
  intro atom member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact reservedFree_symbol_iff.mpr (by decide)
  · exact free

private theorem cons_operator :
    OperatorScheme (arrowType [.var "t", listOf (.var "t")] (listOf (.var "t")))
      [.var "t", listOf (.var "t")] (listOf (.var "t")) where
  function := rfl
  nonempty := by simp
  arguments := by
    intro argumentType member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact reservedFree_var "t"
    · exact listOf_free (reservedFree_var "t")
  result := listOf_free (reservedFree_var "t")

private def natValuation : String → Atom := fun _ => .symbol "Nat"

private theorem natValuation_firstOrder : FirstOrderValuation natValuation :=
  fun _ => ⟨nat_free, rfl⟩

/-- `(cons zero nil)`. -/
def consZeroNil : Atom := .expression [.symbol "cons", .symbol "zero", .symbol "nil"]

/-- `(cons zero zero)`. -/
def consZeroZero : Atom := .expression [.symbol "cons", .symbol "zero", .symbol "zero"]

theorem consZeroNil_fragment : SchematicTerm listSpace consZeroNil := by
  refine .application (by decide) (by decide) list_cons cons_operator rfl ?_
  intro argument member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact .constant list_zero nat_free
  · exact .constant list_nil (listOf_free (reservedFree_var "t"))

theorem consZeroZero_fragment : SchematicTerm listSpace consZeroZero := by
  refine .application (by decide) (by decide) list_cons cons_operator rfl ?_
  intro argument member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl <;> exact .constant list_zero nat_free

/-- Positive: HOL types `(cons zero nil)` at `(List Nat)`, with `cons` at
`(-> Nat (List Nat) (List Nat))` and `nil` at `(List Nat)`. -/
theorem consZeroNil_hol : SchematicHOLTyped listSpace consZeroNil (listOf (.symbol "Nat")) := by
  refine ⟨[NamedTerm.constant (.symbol "zero", .symbol "Nat"),
      NamedTerm.constant (.symbol "nil", listOf (.symbol "Nat"))].foldl .app
      (.constant (.symbol "cons",
        arrowType [.symbol "Nat", listOf (.symbol "Nat")] (listOf (.symbol "Nat")))),
    .application (.cons (.symbol _ _) (.cons (.symbol _ _) .nil)), ?_⟩
  apply (elaborates_application_instance_iff
    (argumentTypes := [.symbol "Nat", listOf (.symbol "Nat")])
    (returnType := listOf (.symbol "Nat")) rfl (by simp) rfl).mpr
  refine ⟨(instanceOf_iff list_cons).mpr ⟨natValuation, natValuation_firstOrder,
      by simp [applyTypeValuation, arrowType, listOf, natValuation]⟩,
    rfl, .cons ?_ (.cons ?_ .nil)⟩
  · exact elaborates_instance_iff.mpr
      ⟨(instanceOf_iff list_zero).mpr ⟨natValuation, natValuation_firstOrder,
        by simp [applyTypeValuation]⟩, rfl⟩
  · exact elaborates_instance_iff.mpr
      ⟨(instanceOf_iff list_nil).mpr ⟨natValuation, natValuation_firstOrder,
        by simp [applyTypeValuation, listOf, natValuation]⟩, rfl⟩

/-- Through the agreement, HE's exact relation gives `(cons zero nil)` a
candidate with `(List Nat)` as an instance, and nothing falls back to
`%Undefined%`. -/
theorem consZeroNil_exact : NoUndefinedFallback listSpace consZeroNil ∧
    ∃ principal, ExactTypes listSpace consZeroNil [principal] ∧
      ∃ valuation, FirstOrderValuation valuation ∧
        applyTypeValuation valuation principal = listOf (.symbol "Nat") :=
  (schematic_hol_iff_exact consZeroNil_fragment
    (GroundFirstOrder.static ⟨listOf_free nat_free, rfl⟩)).mp consZeroNil_hol

/-- Negative: no instance annotation of `(cons zero zero)` is HOL-typed; the
second argument would need a list type. -/
theorem consZeroZero_not_hol (type : Atom) : ¬SchematicHOLTyped listSpace consZeroZero type := by
  rintro ⟨holTerm, annotates, elaborates⟩
  cases annotates with
  | application annotations =>
      obtain ⟨holArguments, headElaborates, _⟩ := (elaborates_foldl_iff _ _ _).mp elaborates
      obtain ⟨instanceOf, _⟩ := elaborates_instance_iff.mp headElaborates
      obtain ⟨valuation, firstOrder, rfl⟩ := (instanceOf_iff list_cons).mp instanceOf
      obtain ⟨instanceFunction, _⟩ := cons_operator.instantiate firstOrder
      obtain ⟨_, _, all⟩ := (elaborates_application_instance_iff instanceFunction (by simp)
        (by rw [List.length_map]; exact annotations.length_eq.symm)).mp elaborates
      cases annotations with
      | cons _ rest =>
          cases rest with
          | cons secondAnnotation _ =>
              cases secondAnnotation
              cases all with
              | cons _ restAll =>
                  cases restAll with
                  | cons secondElaborates _ =>
                      obtain ⟨zeroInstance, holEq⟩ :=
                        elaborates_instance_iff.mp secondElaborates
                      obtain ⟨zeroValuation, _, rfl⟩ :=
                        (instanceOf_iff list_zero).mp zeroInstance
                      have listNotArrow : ¬ArrowShaped (applyTypeValuation valuation
                          (listOf (.var "t"))) := by
                        rintro ⟨_, equal⟩
                        simp [applyTypeValuation, listOf] at equal
                      rw [toTy_of_not_arrowShaped listNotArrow,
                        toTy_of_not_arrowShaped (by
                          rintro ⟨_, equal⟩
                          simp [applyTypeValuation] at equal)] at holEq
                      simp [applyTypeValuation, listOf] at holEq

/-- By the agreement, HE's exact relation has no fallback-free candidate for
`(cons zero zero)` with any static instance. -/
theorem consZeroZero_no_candidate {type : Atom} (static : StaticType type) :
    ¬(NoUndefinedFallback listSpace consZeroZero ∧
      ∃ principal, ExactTypes listSpace consZeroZero [principal] ∧
        ∃ valuation, FirstOrderValuation valuation ∧
          applyTypeValuation valuation principal = type) :=
  fun exact => consZeroZero_not_hol type
    ((schematic_hol_iff_exact consZeroZero_fragment static).mpr exact)

/-- **Arrow-valued type variables break agreement.**  HE's matching compares
arrow arities, so no presentation matches `(-> $a $b)` against `(-> A C B)`.
In curried HOL the instance `$a := A`, `$b := (-> C B)` of `(-> $a $b)` has
the HOL type of `(-> A C B)`. -/
theorem arrow_variable_counterexample :
    (∀ output, ¬CorePlusR2TypePresentationMatchRel []
        (arrowType [.var "a"] (.var "b"))
        (arrowType [.symbol "A", .symbol "C"] (.symbol "B")) output) ∧
      toTy (applyTypeValuation
          (fun name => if name = "a" then .symbol "A" else arrowType [.symbol "C"] (.symbol "B"))
          (arrowType [.var "a"] (.var "b"))) =
        toTy (arrowType [.symbol "A", .symbol "C"] (.symbol "B")) := by
  constructor
  · intro output derivation
    obtain ⟨valuation, satisfied⟩ :=
      MatchSolutionTheory.corePlusR2_output_satisfiable derivation TypeSubst.normal_empty
    have consistent := ((MatchSolutionTheory.CorePlusR2TypePresentationMatchRel.solutions
      derivation TypeSubst.normal_empty valuation).mp satisfied).2
    simp [CorePlusR2TypeConsistent, ReducedTypeConsistent, ReducedTypeListConsistent,
      arrowType, Atom.undefinedType, Atom.atomType] at consistent
  · simp [applyTypeValuation, arrowType, toTy, expressionTy, componentsSpine]

#print axioms schematic_hol_iff_exact
#print axioms exact_candidates_same_instances
#print axioms operator_constant_hol_iff
#print axioms annotated_of_exact
#print axioms exact_of_annotated
#print axioms consZeroNil_exact
#print axioms consZeroZero_no_candidate
#print axioms arrow_variable_counterexample

end Mettapedia.Languages.MeTTa.HE.TypeGrounding.Schematic
