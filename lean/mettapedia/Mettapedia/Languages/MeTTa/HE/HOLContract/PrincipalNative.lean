import Mettapedia.Languages.MeTTa.HE.HOLContract.Principal
import Mettapedia.Languages.MeTTa.HE.HOLContract.Runtime

/-!
# The principal-type checker is an admitted native checker

`Runtime.NativeChecker` states what a native checker must answer: a type scheme per expression,
whose ground first-order instances are exactly the contract's typings of the expression.  The
principal-type checker of `Principal` computes its answers by first-order unification over type
terms; this module reads them back as atoms and proves the obligations.

* `principalNative`: on the expressions with one way of typing, the computed principal type,
  read as an atom, is an admitted native answer.
* `principalOverloaded`: with overloads, one answer per way of typing; an expression has a
  ground first-order type exactly when one of the answers has it as an instance.
* `principal_same_instances_as_exact`: where HE's exact candidate also answers, it has the same
  ground first-order instances as the computed principal type.

A variable `(position, name)` of a type term becomes the atom variable named by `keyName`,
which is injective, so variables of different declaration occurrences stay apart.  A rigid
constant has no instance; it reads as `%Undefined%`, which has no ground first-order instance.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.HE.HOLContract.Principal

open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.HE.TypeGrounding
open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)
open Spec.Type
open Spec.Type.Presentation
open Spec.Type.RuntimeRefinement

/-! ## Naming the variables of type terms -/

/-- The characters of a position: each index as that many `a`s closed by a `b`. -/
def positionChars (position : List ℕ) : List Char :=
  position.flatMap fun index => List.replicate index 'a' ++ ['b']

/-- The name of the variable `(position, name)`: its position's characters, `c`, then the
name. -/
def keyName (key : List ℕ × String) : String :=
  String.ofList (positionChars key.1 ++ 'c' :: key.2.toList)

theorem replicate_b_cancel :
    ∀ {left right : ℕ} {rest other : List Char},
      List.replicate left 'a' ++ 'b' :: rest = List.replicate right 'a' ++ 'b' :: other →
        left = right ∧ rest = other
  | 0, 0, _, _, equal => ⟨rfl, by simpa using equal⟩
  | 0, _ + 1, _, _, equal => by simp [List.replicate_succ] at equal
  | _ + 1, 0, _, _, equal => by simp [List.replicate_succ] at equal
  | _ + 1, _ + 1, _, _, equal => by
      simp only [List.replicate_succ, List.cons_append, List.cons.injEq, true_and] at equal
      obtain ⟨same, rest⟩ := replicate_b_cancel equal
      exact ⟨by rw [same], rest⟩

theorem positionChars_cancel :
    ∀ {left right : List ℕ} {rest other : List Char},
      positionChars left ++ 'c' :: rest = positionChars right ++ 'c' :: other →
        left = right ∧ rest = other
  | [], [], _, _, equal => ⟨rfl, by simpa [positionChars] using equal⟩
  | [], index :: _, _, _, equal => by
      cases index <;> simp [positionChars, List.replicate_succ] at equal
  | index :: _, [], _, _, equal => by
      cases index <;> simp [positionChars, List.replicate_succ] at equal
  | _ :: _, _ :: _, _, _, equal => by
      simp only [positionChars, List.flatMap_cons, List.append_assoc, List.cons_append] at equal
      obtain ⟨same, tail⟩ := replicate_b_cancel equal
      obtain ⟨tails, rests⟩ := positionChars_cancel (left := _) (right := _) tail
      exact ⟨by rw [same, tails], rests⟩

theorem keyName_injective : Function.Injective keyName := by
  rintro ⟨leftPosition, leftName⟩ ⟨rightPosition, rightName⟩ equal
  obtain ⟨positions, names⟩ := positionChars_cancel (String.ofList_injective equal)
  dsimp only at positions names
  have : leftName = rightName := by
    rw [← String.ofList_toList (s := leftName), names, String.ofList_toList]
  rw [positions, this]

/-! ## Type terms as atoms -/

/-- A type term as an atom: the variable `(position, name)` is the atom variable `keyName`, and a
rigid constant, which has no instance, is `%Undefined%`. -/
def display : TypeTerm → Atom
  | .var key => .var (keyName key)
  | .const (.symbol name) => .symbol name
  | .const (.grounded value) => .grounded value
  | .const (.rigid _) => Atom.undefinedType
  | .app _ arguments => .expression (List.ofFn fun index => display (arguments index))

/-- Type terms without rigid constants. -/
inductive RigidFree : TypeTerm → Prop where
  | var (key : sig.vars) : RigidFree (.var key)
  | symbol (name : String) : RigidFree (.const (.symbol name))
  | grounded (value : GroundedValue) : RigidFree (.const (.grounded value))
  | app {n : ℕ} {arguments : Fin n → TypeTerm} :
      (∀ index, RigidFree (arguments index)) → RigidFree (.app n arguments)

theorem rigidFree_of_applyTerm {ρ : Unifier} :
    ∀ term : TypeTerm, RigidFree (ρ.applyTerm term) → RigidFree term := by
  intro term
  induction term with
  | var key => intro _; exact .var key
  | const leaf =>
      intro free
      cases leaf with
      | symbol name => exact .symbol name
      | grounded value => exact .grounded value
      | rigid _ => cases free
  | app n arguments ih =>
      intro free
      rw [Mettapedia.Logic.LP.Subst.applyTerm_app] at free
      cases free with
      | app children => exact .app fun index => ih index (children index)

theorem rigidFree_ofList {terms : List TypeTerm} (free : ∀ term ∈ terms, RigidFree term) :
    RigidFree (ofList terms) := by
  unfold ofList
  exact .app fun index => free _ (List.get_mem terms index)

/-- A variable-free atom has no rigid constant. -/
theorem rigidFree_rigid :
    ∀ atom : Atom, TypeSubst.typeVars atom = [] → RigidFree (rigid atom) := by
  intro atom
  induction atom using Atom.rec (motive_2 := fun atoms =>
      TypeSubst.typeVarsList atoms = [] → ∀ atom ∈ atoms, RigidFree (rigid atom)) with
  | symbol name => intro _; exact .symbol name
  | grounded value => intro _; exact .grounded value
  | var name => intro ground; simp [TypeSubst.typeVars] at ground
  | expression atoms ih =>
      intro ground
      rw [rigid_expression]
      apply rigidFree_ofList
      intro term member
      obtain ⟨atom, atomMember, rfl⟩ := List.mem_map.mp member
      exact ih (by simpa [TypeSubst.typeVars] using ground) atom atomMember
  | nil => rename_i member; simp at member
  | cons head tail headIH tailIH =>
      rename_i ground atom member
      simp only [TypeSubst.typeVarsList, List.append_eq_nil_iff] at ground
      rcases List.mem_cons.mp member with rfl | inTail
      · exact headIH ground.1
      · exact tailIH ground.2 atom inTail

/-- An atom read from a type term is reserved-free only if the term has no rigid constant. -/
theorem rigidFree_of_reservedFree {valuation : String → Atom} :
    ∀ term : TypeTerm,
      Schematic.ReservedFree (applyTypeValuation valuation (display term)) → RigidFree term := by
  intro term
  induction term with
  | var key => intro _; exact .var key
  | const leaf =>
      intro free
      cases leaf with
      | symbol name => exact .symbol name
      | grounded value => exact .grounded value
      | rigid _ =>
          simp only [display, Atom.undefinedType, applyTypeValuation] at free
          exact absurd (Schematic.reservedFree_symbol_iff.mp free) (by simp [reservedTypeNames])
  | app n arguments ih =>
      intro free
      simp only [display, applyTypeValuation] at free
      refine .app fun index => ih index ?_
      exact (Schematic.reservedFree_expression_iff.mp free) _
        (List.mem_map.mpr ⟨_, List.mem_ofFn.mpr ⟨index, rfl⟩, rfl⟩)

/-- **Reading a valued term.**  When the valuation gives each variable's name the reading of
its value, the valued reading of a term without rigid constants is the reading of its
substitution instance. -/
theorem applyTypeValuation_display {ρ : Unifier} {valuation : String → Atom} :
    ∀ {term : TypeTerm}, RigidFree term →
      (∀ key ∈ term.freeVars, valuation (keyName key) = decode (ρ key)) →
      applyTypeValuation valuation (display term) = decode (ρ.applyTerm term) := by
  intro term free
  induction free with
  | var key =>
      intro values
      simp only [display, applyTypeValuation, Mettapedia.Logic.LP.Subst.applyTerm_var]
      exact values key (by simp [Mettapedia.Logic.LP.Term.freeVars])
  | symbol name => intro _; simp [display, decode, applyTypeValuation]
  | grounded value => intro _; simp [display, decode, applyTypeValuation]
  | app _ ih =>
      rename_i n arguments
      intro values
      simp only [display, applyTypeValuation, Mettapedia.Logic.LP.Subst.applyTerm_app, decode,
        List.map_ofFn, Atom.expression.injEq]
      apply List.ofFn_inj.mpr
      funext index
      exact ih index fun key member =>
        values key (Mettapedia.Logic.LP.Term.mem_freeVars_app.mpr ⟨index, member⟩)

/-! ## Ground first-order types are clean -/

theorem typeVars_of_subatom {sub type : Atom} (subatom : Subatom sub type)
    (ground : TypeSubst.typeVars type = []) : TypeSubst.typeVars sub = [] := by
  induction subatom with
  | refl => exact ground
  | @child atom atoms member _ ih =>
      apply ih
      have all := (typeVarsList_eq_nil_iff atoms).mp (by simpa [TypeSubst.typeVars] using ground)
      exact all _ member

theorem groundFirstOrder_of_subatom {sub type : Atom} (subatom : Subatom sub type)
    (ground : Schematic.GroundFirstOrder type) : Schematic.GroundFirstOrder sub :=
  ⟨fun other occurs => ground.1 other (occurs.trans subatom), typeVars_of_subatom subatom ground.2⟩

/-- **Ground first-order types are clean.** -/
theorem clean_of_groundFirstOrder :
    ∀ type : Atom, Schematic.GroundFirstOrder type → Clean type := by
  intro type
  induction type using Atom.rec (motive_2 := fun atoms =>
      (∀ atom ∈ atoms, Schematic.GroundFirstOrder atom) → ∀ atom ∈ atoms, Clean atom) with
  | symbol name => intro ground; exact .symbol (Schematic.reservedFree_symbol_iff.mp ground.1)
  | grounded value => intro _; exact .grounded value
  | var name => intro ground; simp [Schematic.GroundFirstOrder, TypeSubst.typeVars] at ground
  | expression atoms ih =>
      intro ground
      have children : ∀ atom ∈ atoms, Schematic.GroundFirstOrder atom := fun atom member =>
        groundFirstOrder_of_subatom (.child member .refl) ground
      unfold Clean
      rw [rigid_expression]
      refine .compound ?_ ?_
      · intro element member
        obtain ⟨atom, atomMember, rfl⟩ := List.mem_map.mp member
        exact ih children atom atomMember
      · intro rest equal
        cases atoms with
        | nil => simp at equal
        | cons first others =>
            simp only [List.map_cons, List.cons.injEq] at equal
            have isArrow : first = .symbol "->" := by
              apply rigid_injective
              rw [equal.1]
              rfl
            have firstGround := children first (by simp)
            rw [isArrow] at firstGround
            exact absurd (Schematic.reservedFree_symbol_iff.mp firstGround.1)
              (by simp [reservedTypeNames])
  | nil => rename_i member; simp at member
  | cons head tail headIH tailIH =>
      rename_i all atom member
      rcases List.mem_cons.mp member with rfl | inTail
      · exact headIH (all _ (by simp))
      · exact tailIH (fun other inner => all other (List.mem_cons_of_mem _ inner)) atom inTail

/-- The value of a variable of a term whose instance is `rigid type` is the reading of a
subatom of `type`. -/
theorem subatom_of_applyTerm {ρ : Unifier} {key : sig.vars} :
    ∀ (term : TypeTerm) {type : Atom}, key ∈ term.freeVars → ρ.applyTerm term = rigid type →
      ∃ sub, Subatom sub type ∧ ρ key = rigid sub := by
  intro term
  induction term with
  | var other =>
      intro type member instance'
      simp only [Mettapedia.Logic.LP.Term.freeVars, Finset.mem_singleton] at member
      subst member
      exact ⟨type, .refl, instance'⟩
  | const _ =>
      intro type member
      simp [Mettapedia.Logic.LP.Term.freeVars] at member
  | app n arguments ih =>
      intro type member instance'
      obtain ⟨index, inner⟩ := Mettapedia.Logic.LP.Term.mem_freeVars_app.mp member
      cases type with
      | symbol _ => simp [rigid] at instance'
      | grounded _ => simp [rigid] at instance'
      | var _ => simp [rigid] at instance'
      | expression atoms =>
          rw [app_eq_ofList, applyTerm_ofList, rigid_expression] at instance'
          have lists := ofList_injective instance'
          have lengths : n = atoms.length := by
            simpa using congrArg List.length lists
          have bound : index.val < atoms.length := lengths ▸ index.isLt
          have entry : ρ.applyTerm (arguments index) = rigid atoms[index.val] := by
            have := congrArg (fun terms : List TypeTerm => terms[index.val]?) lists
            simpa [bound] using this
          obtain ⟨sub, subatom, value⟩ := ih index inner entry
          exact ⟨sub, .child (List.getElem_mem bound) subatom, value⟩

/-! ## The native checkers -/

/-- The expressions on which the principal checker finds exactly one way of typing. -/
def SingleWay (space : Space) (expression : Atom) : Prop :=
  ∃ answer, principal space expression = some [answer]

/-- The native answer of the principal checker: its single principal type read as an atom, and
`%Undefined%` when it finds no single way of typing. -/
def nativeAnswer (space : Space) (expression : Atom) : Atom :=
  match principal space expression with
  | some [answer] => display answer
  | _ => Atom.undefinedType

/-- The atoms read from the principal types, one per way of typing. -/
def nativeAnswers (space : Space) (expression : Atom) : List Atom :=
  ((principal space expression).getD []).map display

/-- Soundness of one computed answer: every ground first-order instance of its reading is a
typing. -/
theorem typed_of_groundInstance {space : Space} {expression : Atom} {answers : List TypeTerm}
    (computed : principal space expression = some answers) {answer : TypeTerm}
    (member : answer ∈ answers) {type : Atom}
    (instance' : GroundInstance (display answer) type) : Typed space expression type := by
  obtain ⟨ground, valuation, firstOrder, valued⟩ := instance'
  have free : RigidFree answer := by
    apply rigidFree_of_reservedFree (valuation := valuation)
    rw [valued]
    exact ground.1
  let ρ : Unifier := fun key => rigid (valuation (keyName key))
  have read : applyTypeValuation valuation (display answer) = decode (ρ.applyTerm answer) :=
    applyTypeValuation_display free fun key _ => (decode_rigid _).symm
  have clean : ∀ key ∈ answer.freeVars, CleanTerm (ρ key) := fun key _ =>
    clean_of_groundFirstOrder _ (firstOrder (keyName key))
  apply principal_sound computed member (ρ := ρ) _ clean
  rw [← rigid_decode_applyTerm answer clean, ← read, valued]

/-- Completeness: every ground first-order typing is an instance of the reading of one computed
answer. -/
theorem groundInstance_of_typed {space : Space} {expression : Atom} {answers : List TypeTerm}
    (computed : principal space expression = some answers) {type : Atom}
    (ground : Schematic.GroundFirstOrder type) (typed : Typed space expression type) :
    ∃ answer ∈ answers, GroundInstance (display answer) type := by
  classical
  obtain ⟨answer, member, ρ, instance', _⟩ := principal_complete computed typed
  refine ⟨answer, member, ground, ?_⟩
  have free : RigidFree answer :=
    rigidFree_of_applyTerm answer (by rw [instance']; exact rigidFree_rigid type ground.2)
  let valuation : String → Atom := fun name =>
    if named : ∃ key ∈ answer.freeVars, keyName key = name then decode (ρ named.choose)
    else .expression []
  have values : ∀ key ∈ answer.freeVars, valuation (keyName key) = decode (ρ key) := by
    intro key keyMember
    have named : ∃ other ∈ answer.freeVars, keyName other = keyName key := ⟨key, keyMember, rfl⟩
    simp only [valuation, dif_pos named]
    rw [keyName_injective named.choose_spec.2]
  refine ⟨valuation, ?_, ?_⟩
  · intro name
    by_cases named : ∃ key ∈ answer.freeVars, keyName key = name
    · simp only [valuation, dif_pos named]
      obtain ⟨sub, subatom, value⟩ :=
        subatom_of_applyTerm answer named.choose_spec.1 instance'
      rw [value, decode_rigid]
      exact groundFirstOrder_of_subatom subatom ground
    · simp only [valuation, dif_neg named]
      refine ⟨?_, by simp [TypeSubst.typeVars, TypeSubst.typeVarsList]⟩
      exact Schematic.reservedFree_expression_iff.mpr (by simp)
  · rw [applyTypeValuation_display free values, instance', decode_rigid]

/-- **The principal checker is an admitted native checker** on the expressions with one way of
typing: the ground first-order instances of its computed answer are exactly the contract's
typings. -/
def principalNative (space : Space) : NativeChecker space (SingleWay space) where
  answer := nativeAnswer space
  sound := by
    intro expression ⟨answer, computed⟩ type instance'
    simp only [nativeAnswer, computed] at instance'
    exact typed_of_groundInstance computed (List.mem_singleton_self answer) instance'
  complete := by
    intro expression ⟨answer, computed⟩ type ground typed
    obtain ⟨found, member, instance'⟩ := groundInstance_of_typed computed ground typed
    rw [List.mem_singleton] at member
    subst member
    simp only [nativeAnswer, computed]
    exact instance'

/-- **Overloads.**  On every expression where the principal checker answers, an expression has a
ground first-order type exactly when the type is an instance of one of the answers, one answer
per way of typing. -/
theorem principalOverloaded_decides {space : Space} {expression : Atom}
    (answers : (principal space expression).isSome) {type : Atom}
    (ground : Schematic.GroundFirstOrder type) :
    Typed space expression type ↔
      ∃ answer ∈ nativeAnswers space expression, GroundInstance answer type := by
  obtain ⟨found, computed⟩ := Option.isSome_iff_exists.mp answers
  simp only [nativeAnswers, computed, Option.getD_some, List.mem_map]
  constructor
  · intro typed
    obtain ⟨answer, member, instance'⟩ := groundInstance_of_typed computed ground typed
    exact ⟨display answer, ⟨answer, member, rfl⟩, instance'⟩
  · rintro ⟨_, ⟨answer, member, rfl⟩, instance'⟩
    exact typed_of_groundInstance computed member instance'

/-- **The computed principal type is HE's exact candidate, up to instances.**  Where HE's exact
candidate answers and the principal checker finds one way of typing, the two answers have the
same ground first-order instances. -/
theorem principal_same_instances_as_exact {space : Space} {expression : Atom}
    (schematic : SchematicFragment space expression) (single : SingleWay space expression)
    (type : Atom) :
    GroundInstance (nativeAnswer space expression) type ↔
      GroundInstance ((exactChecker space).answer expression) type := by
  constructor
  · intro instance'
    exact (exactChecker space).complete expression schematic type instance'.1
      ((principalNative space).sound expression single type instance')
  · intro instance'
    exact (principalNative space).complete expression single type instance'.1
      ((exactChecker space).sound expression schematic type instance')

end Mettapedia.Languages.MeTTa.HE.HOLContract.Principal

#print axioms Mettapedia.Languages.MeTTa.HE.HOLContract.Principal.keyName_injective
#print axioms Mettapedia.Languages.MeTTa.HE.HOLContract.Principal.principalNative
#print axioms Mettapedia.Languages.MeTTa.HE.HOLContract.Principal.principalOverloaded_decides
#print axioms Mettapedia.Languages.MeTTa.HE.HOLContract.Principal.principal_same_instances_as_exact
