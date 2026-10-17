import Mettapedia.Logic.TheoryModel.Consistency
import Mettapedia.Logic.TheoryModel.IdentityCarve

/-!
# Declared types: open, extended and closed

A type can be declared before any of its members are.  Read set-theoretically, a
declared type is a set of individuals of an ambient domain `V`, possibly empty, and
names denote individuals (`Interp`).  The sentences say that the type is inhabited or
empty, that a named individual is or is not a member, that two names denote
different individuals, and that every member is denoted by one of a given set of
names (`Sentence.exhaustive`).

* **Declared with no constructors** (`openDecl ∅`).  Every interpretation is a model
  (`models_openDecl_empty`): the declared type ranges over all subsets of the domain,
  the empty one included, as "let `A` be a set" does.  Its consequences are the
  validities (`entails_openDecl_empty_iff`), and its inhabitation is undetermined
  (`openDecl_empty_undetermined`).
* **Adding constructors** extends the theory (`openDecl_mono`).  The first
  constructor decides inhabitation (`entails_inhabited_iff`).  Every later one is
  conservative over the sentences that do not mention it (`conservative_insert`), and
  conservativity over those sentences holds exactly when a constructor was already
  declared (`conservative_iff`).
* **Closing** (`closedDecl`) says that the constructors denote all the members: the
  type is the set they enumerate (`mem_models_closedDecl`).  Closing with no
  constructors entails emptiness (`closedDecl_empty_entails_isEmpty`) and remains
  consistent.  Closing changes what can be refuted: membership of a name distinct
  from every constructor is undetermined while the type is open
  (`open_mem_undetermined`), refuted once it is closed (`closed_refutes_mem`), and a
  new constructor distinct from the old ones becomes inconsistent
  (`closed_new_constructor_inconsistent`).
* **Statuses.**  Declaration statuses (`Status`) are ordered by adding constructors
  and closing (`Status.Refines`); refinement adds sentences and shrinks the class of
  models (`Status.Refines.models_subset`).  The open declaration with no constructors
  is the least status (`Status.declared_empty_refines`), and a closed status refines
  only to itself (`Status.Refines.eq_of_closed`).
* **Hosts in which every type is inhabited.**  The universe of interpretations with a
  nonempty carrier, HOL's (`holUniverse`), is the carve of all interpretations by
  `inhabited` (`holUniverse_eq_carve`), so it adds exactly that commitment
  (`consequencesIn_holUniverse`).  It hosts no model of the closed empty type
  (`modelsIn_holUniverse_closedDecl_empty`), hosts the open empty declaration
  unfaithfully (`not_hostsFaithfully_holUniverse_openDecl_empty`), and hosts every
  declaration with a constructor faithfully
  (`hostsFaithfully_holUniverse_of_nonempty`).  A universe in which one designated
  individual belongs to every type (`pointedUniverse`) behaves in the same way for
  the two empty declarations.

Controls: two constructor names over the natural numbers, where membership of a third
name is undetermined while the type is open and refuted once it is closed
(`Control.third_undetermined_while_open`, `Control.third_refuted_once_closed`).
-/

set_option autoImplicit false

namespace Mettapedia.Logic.TheoryModel.OpenDeclarations

open Set
open Mettapedia.Logic.TheoryModel

universe uV uN

/-- An interpretation of one declared type in the domain `V`: the type as a set of
individuals, possibly empty, and each name as an individual. -/
structure Interp (V : Type uV) (N : Type uN) where
  carrier : Set V
  value : N → V

/-- Sentences about one declared type. -/
inductive Sentence (N : Type uN) where
  /-- The type has a member. -/
  | inhabited
  /-- The type has no member. -/
  | isEmpty
  /-- The individual named `n` is a member. -/
  | mem (n : N)
  /-- The individual named `n` is not a member. -/
  | nonMem (n : N)
  /-- The names denote different individuals. -/
  | distinct (n n' : N)
  /-- Every member is denoted by one of the names `ns`. -/
  | exhaustive (ns : Set N)

variable {V : Type uV} {N : Type uN}

/-- Satisfaction. -/
def Sat (m : Interp V N) : Sentence N → Prop
  | .inhabited => m.carrier.Nonempty
  | .isEmpty => m.carrier = ∅
  | .mem n => m.value n ∈ m.carrier
  | .nonMem n => m.value n ∉ m.carrier
  | .distinct n n' => m.value n ≠ m.value n'
  | .exhaustive ns => ∀ x ∈ m.carrier, ∃ n ∈ ns, m.value n = x

/-- A type declared with the constructors `ns`, left open. -/
def openDecl (ns : Set N) : Set (Sentence N) :=
  Sentence.mem '' ns

/-- The same constructors, closed: they denote all the members. -/
def closedDecl (ns : Set N) : Set (Sentence N) :=
  insert (.exhaustive ns) (openDecl ns)

/-- The name `n` denotes an individual different from those the names `ns` denote. -/
def distinctFrom (n : N) (ns : Set N) : Set (Sentence N) :=
  (fun n' => Sentence.distinct n n') '' ns

/-- The interpretation with the given carrier in which every name denotes `point`. -/
def constInterp (carrier : Set V) (point : V) : Interp V N :=
  ⟨carrier, fun _ => point⟩

theorem mem_models_openDecl {ns : Set N} {m : Interp V N} :
    m ∈ models Sat (openDecl ns) ↔ ∀ n ∈ ns, m.value n ∈ m.carrier := by
  constructor
  · intro model n member
    exact model ⟨n, member, rfl⟩
  · rintro all _ ⟨n, member, rfl⟩
    exact all n member

/-- **Closing makes the type the set its constructors enumerate.** -/
theorem mem_models_closedDecl {ns : Set N} {m : Interp V N} :
    m ∈ models Sat (closedDecl ns) ↔ m.carrier = m.value '' ns := by
  rw [closedDecl, mem_models_insert, mem_models_openDecl]
  constructor
  · rintro ⟨exhaustive, members⟩
    apply Subset.antisymm
    · intro x member
      obtain ⟨n, inNames, equal⟩ := exhaustive x member
      exact ⟨n, inNames, equal⟩
    · rintro _ ⟨n, inNames, rfl⟩
      exact members n inNames
  · intro equal
    refine ⟨fun x member => ?_, fun n inNames => ?_⟩
    · rw [equal] at member
      obtain ⟨n, inNames, rfl⟩ := member
      exact ⟨n, inNames, rfl⟩
    · rw [equal]
      exact ⟨n, inNames, rfl⟩

/-! ## Declared with no constructors -/

/-- **Declared with no constructors, a type may be any set**: every interpretation is a
model. -/
theorem models_openDecl_empty : models (Sat (V := V)) (openDecl (∅ : Set N)) = univ :=
  eq_univ_of_forall fun _ => mem_models_openDecl.mpr fun _ member => member.elim

/-- Every subset of the domain is the carrier of a model. -/
theorem exists_model_carrier (point : V) (carrier : Set V) :
    ∃ m ∈ models Sat (openDecl (∅ : Set N)), m.carrier = carrier :=
  ⟨constInterp carrier point, by rw [models_openDecl_empty]; trivial, rfl⟩

/-- Its consequences are the validities. -/
theorem entails_openDecl_empty_iff {φ : Sentence N} :
    Entails (Sat (V := V)) (openDecl ∅) φ ↔ ∀ m : Interp V N, Sat m φ := by
  unfold Entails
  rw [models_openDecl_empty]
  exact ⟨fun holds m => holds (mem_univ m), fun holds m _ => holds m⟩

/-- **Its inhabitation is undetermined.** -/
theorem openDecl_empty_undetermined (point : V) :
    ¬ Entails (Sat (V := V)) (openDecl (∅ : Set N)) .inhabited ∧
      ¬ Entails (Sat (V := V)) (openDecl (∅ : Set N)) .isEmpty := by
  constructor
  · intro entails
    have holds : Sat (constInterp (N := N) ∅ point) .inhabited :=
      entails (by rw [models_openDecl_empty]; trivial)
    exact not_nonempty_empty holds
  · intro entails
    have holds : Sat (constInterp (N := N) {point} point) .isEmpty :=
      entails (by rw [models_openDecl_empty]; trivial)
    exact singleton_ne_empty point holds

/-! ## Adding constructors -/

/-- Adding constructors extends the theory. -/
theorem openDecl_mono {ns ns' : Set N} (included : ns ⊆ ns') : openDecl ns ⊆ openDecl ns' :=
  image_mono included

/-- **The first constructor decides inhabitation.** -/
theorem entails_inhabited_iff (point : V) {ns : Set N} :
    Entails (Sat (V := V)) (openDecl ns) .inhabited ↔ ns.Nonempty := by
  constructor
  · intro entails
    by_contra empty
    rw [not_nonempty_iff_eq_empty] at empty
    subst empty
    exact (openDecl_empty_undetermined (N := N) point).1 entails
  · rintro ⟨n, member⟩ m model
    exact ⟨m.value n, mem_models_openDecl.mp model n member⟩

/-- A sentence that does not mention the name `d`. -/
def Avoids (d : N) : Sentence N → Prop
  | .inhabited => True
  | .isEmpty => True
  | .mem n => n ≠ d
  | .nonMem n => n ≠ d
  | .distinct n n' => n ≠ d ∧ n' ≠ d
  | .exhaustive ns => d ∉ ns

/-- The interpretation in which the name `d` denotes `x` instead. -/
def Interp.redirect [DecidableEq N] (m : Interp V N) (d : N) (x : V) : Interp V N :=
  ⟨m.carrier, Function.update m.value d x⟩

theorem sat_redirect_iff [DecidableEq N] {m : Interp V N} {d : N} {x : V} {φ : Sentence N}
    (avoids : Avoids d φ) : Sat (m.redirect d x) φ ↔ Sat m φ := by
  cases φ with
  | inhabited => exact Iff.rfl
  | isEmpty => exact Iff.rfl
  | mem n =>
      show Function.update m.value d x n ∈ m.carrier ↔ m.value n ∈ m.carrier
      rw [Function.update_of_ne avoids]
  | nonMem n =>
      show Function.update m.value d x n ∉ m.carrier ↔ m.value n ∉ m.carrier
      rw [Function.update_of_ne avoids]
  | distinct n n' =>
      show Function.update m.value d x n ≠ Function.update m.value d x n' ↔
        m.value n ≠ m.value n'
      rw [Function.update_of_ne avoids.1, Function.update_of_ne avoids.2]
  | exhaustive ns =>
      have same : ∀ n ∈ ns, Function.update m.value d x n = m.value n := fun n member =>
        Function.update_of_ne (fun (equal : n = d) => avoids (equal ▸ member)) _ _
      show (∀ y ∈ m.carrier, ∃ n ∈ ns, Function.update m.value d x n = y) ↔
        ∀ y ∈ m.carrier, ∃ n ∈ ns, m.value n = y
      constructor
      · intro cover y member
        obtain ⟨n, inNames, equal⟩ := cover y member
        exact ⟨n, inNames, (same n inNames).symm.trans equal⟩
      · intro cover y member
        obtain ⟨n, inNames, equal⟩ := cover y member
        exact ⟨n, inNames, (same n inNames).trans equal⟩

/-- **Adding a constructor to a declaration that already has one is conservative**
over the sentences that do not mention it. -/
theorem conservative_insert {ns : Set N} (nonempty : ns.Nonempty) (d : N) {φ : Sentence N}
    (avoids : Avoids d φ) (entails : Entails (Sat (V := V)) (openDecl (insert d ns)) φ) :
    Entails (Sat (V := V)) (openDecl ns) φ := by
  classical
  intro m model
  obtain ⟨c, member⟩ := nonempty
  have model' : m.redirect d (m.value c) ∈ models Sat (openDecl (insert d ns)) := by
    rw [mem_models_openDecl]
    intro n inserted
    by_cases equal : n = d
    · subst equal
      show Function.update m.value n (m.value c) n ∈ m.carrier
      rw [Function.update_self]
      exact mem_models_openDecl.mp model c member
    · rcases inserted with rfl | inNames
      · exact (equal rfl).elim
      · show Function.update m.value d (m.value c) n ∈ m.carrier
        rw [Function.update_of_ne equal]
        exact mem_models_openDecl.mp model n inNames
  exact (sat_redirect_iff avoids).mp (entails model')

/-- **Adding a constructor is conservative over the sentences not mentioning it
exactly when a constructor was already declared.** -/
theorem conservative_iff (point : V) (ns : Set N) (d : N) :
    (∀ φ : Sentence N, Avoids d φ →
        Entails (Sat (V := V)) (openDecl (insert d ns)) φ →
          Entails (Sat (V := V)) (openDecl ns) φ) ↔ ns.Nonempty := by
  constructor
  · intro conservative
    rw [← entails_inhabited_iff point]
    exact conservative .inhabited trivial ((entails_inhabited_iff point).mpr (insert_nonempty d ns))
  · intro nonempty φ avoids
    exact conservative_insert nonempty d avoids

/-! ## Closing -/

/-- **Closed with no constructors, the type is empty.** -/
theorem closedDecl_empty_entails_isEmpty :
    Entails (Sat (V := V)) (closedDecl (∅ : Set N)) .isEmpty := by
  intro m model
  show m.carrier = ∅
  rw [mem_models_closedDecl.mp model, image_empty]

/-- The closed empty declaration is consistent. -/
theorem closedDecl_empty_consistent (point : V) :
    Consistent (Sat (V := V)) (closedDecl (∅ : Set N)) :=
  ⟨constInterp ∅ point, mem_models_closedDecl.mpr (image_empty _).symm⟩

/-- **While the type is open, membership of a name distinct from every constructor is
undetermined**: both answers are consistent. -/
theorem open_mem_undetermined {ns : Set N} {d : N} (fresh : d ∉ ns) {a b : V} (apart : a ≠ b) :
    Consistent (Sat (V := V)) (insert (.mem d) (openDecl ns ∪ distinctFrom d ns)) ∧
      Consistent (Sat (V := V)) (insert (.nonMem d) (openDecl ns ∪ distinctFrom d ns)) := by
  classical
  let value : N → V := fun n => if n = d then b else a
  have constructorValue : ∀ n ∈ ns, value n = a := fun n member => by
    have notD : n ≠ d := fun equal => fresh (equal ▸ member)
    simp [value, notD]
  have nameValue : value d = b := by simp [value]
  have base : ∀ carrier : Set V, a ∈ carrier →
      (⟨carrier, value⟩ : Interp V N) ∈ models Sat (openDecl ns ∪ distinctFrom d ns) := by
    intro carrier containsA
    rw [models_union]
    refine ⟨mem_models_openDecl.mpr fun n member => ?_, ?_⟩
    · show value n ∈ carrier
      rw [constructorValue n member]
      exact containsA
    · rintro _ ⟨n, member, rfl⟩
      show value d ≠ value n
      rw [nameValue, constructorValue n member]
      exact apart.symm
  constructor
  · refine ⟨⟨{a, b}, value⟩, mem_models_insert.mpr ⟨?_, base _ (Or.inl rfl)⟩⟩
    show value d ∈ ({a, b} : Set V)
    rw [nameValue]
    exact Or.inr rfl
  · refine ⟨⟨{a}, value⟩, mem_models_insert.mpr ⟨?_, base _ rfl⟩⟩
    show value d ∉ ({a} : Set V)
    rw [nameValue]
    exact fun equal => apart equal.symm

/-- **Once the type is closed, membership of a name distinct from every constructor is
refuted.** -/
theorem closed_refutes_mem {ns : Set N} {d : N} :
    Entails (Sat (V := V)) (closedDecl ns ∪ distinctFrom d ns) (.nonMem d) := by
  intro m model member
  have closed : m ∈ models Sat (closedDecl ns) := models_anti subset_union_left model
  have distinct : ∀ n ∈ ns, m.value d ≠ m.value n := fun n inNames =>
    model (Or.inr ⟨n, inNames, rfl⟩)
  rw [mem_models_closedDecl.mp closed] at member
  obtain ⟨n, inNames, equal⟩ := member
  exact distinct n inNames equal.symm

/-- **A closed type admits no new constructor distinct from the old ones.** -/
theorem closed_new_constructor_inconsistent {ns : Set N} {d : N} :
    ¬ Consistent (Sat (V := V)) (insert (.mem d) (closedDecl ns ∪ distinctFrom d ns)) := by
  rintro ⟨m, model⟩
  rw [mem_models_insert] at model
  exact closed_refutes_mem model.2 model.1

/-! ## Declaration statuses -/

/-- The declaration status of a type. -/
inductive Status (N : Type uN) where
  /-- Declared and open, with the constructors `ns`, possibly none. -/
  | declared (ns : Set N)
  /-- Closed: `ns` are all the constructors. -/
  | closed (ns : Set N)

namespace Status

/-- The theory a status commits to. -/
def theory : Status N → Set (Sentence N)
  | .declared ns => openDecl ns
  | .closed ns => closedDecl ns

/-- Refinement of statuses: adding constructors to an open type, and closing it. -/
inductive Refines : Status N → Status N → Prop where
  | extend {ns ns' : Set N} (included : ns ⊆ ns') : Refines (.declared ns) (.declared ns')
  | close {ns ns' : Set N} (included : ns ⊆ ns') : Refines (.declared ns) (.closed ns')
  | closedRefl (ns : Set N) : Refines (.closed ns) (.closed ns)

/-- Refinement adds sentences. -/
theorem Refines.theory_subset {s s' : Status N} (refines : Refines s s') :
    s.theory ⊆ s'.theory := by
  cases refines with
  | extend included => exact openDecl_mono included
  | close included =>
      exact Subset.trans (openDecl_mono included) (subset_insert _ _)
  | closedRefl => exact Subset.rfl

/-- Refinement shrinks the class of models. -/
theorem Refines.models_subset {s s' : Status N} (refines : Refines s s') :
    models (Sat (V := V)) s'.theory ⊆ models Sat s.theory :=
  models_anti refines.theory_subset

/-- **The open declaration with no constructors is the least status.** -/
theorem declared_empty_refines (s : Status N) : Refines (.declared ∅) s := by
  cases s with
  | declared ns => exact .extend (empty_subset ns)
  | closed ns => exact .close (empty_subset ns)

/-- A closed status refines only to itself. -/
theorem Refines.eq_of_closed {ns : Set N} {s : Status N} (refines : Refines (.closed ns) s) :
    s = .closed ns := by
  cases refines
  rfl

end Status

/-! ## Hosts in which every type is inhabited -/

/-- HOL's universe: every type is inhabited. -/
def holUniverse : Set (Interp V N) :=
  {m | m.carrier.Nonempty}

/-- A universe in which the individual `point` belongs to every type. -/
def pointedUniverse (point : V) : Set (Interp V N) :=
  {m | point ∈ m.carrier}

theorem pointedUniverse_subset_holUniverse (point : V) :
    pointedUniverse (N := N) point ⊆ holUniverse :=
  fun _ member => ⟨point, member⟩

/-- HOL's universe is the carve of all interpretations by `inhabited`. -/
theorem holUniverse_eq_carve :
    (holUniverse : Set (Interp V N)) = carve Sat univ {.inhabited} := by
  ext m
  constructor
  · intro nonempty
    exact ⟨mem_univ m, fun φ member => by rw [mem_singleton_iff.mp member]; exact nonempty⟩
  · rintro ⟨-, model⟩
    exact model (mem_singleton _)

/-- **HOL adds exactly the commitment that the type is inhabited.** -/
theorem consequencesIn_holUniverse (T : Set (Sentence N)) :
    consequencesIn Sat (holUniverse : Set (Interp V N)) T =
      consequencesIn (Sat (V := V)) univ ({.inhabited} ∪ T) := by
  rw [holUniverse_eq_carve, consequencesIn_carve]

/-- **HOL hosts no model of the closed empty type.** -/
theorem modelsIn_holUniverse_closedDecl_empty :
    modelsIn Sat (holUniverse : Set (Interp V N)) (closedDecl ∅) = ∅ := by
  apply eq_empty_of_forall_notMem
  rintro m ⟨nonempty, model⟩
  exact nonempty.ne_empty (closedDecl_empty_entails_isEmpty model)

/-- Neither does a pointed universe. -/
theorem modelsIn_pointedUniverse_closedDecl_empty (point : V) :
    modelsIn Sat (pointedUniverse (N := N) point) (closedDecl ∅) = ∅ := by
  apply eq_empty_of_subset_empty
  rw [← modelsIn_holUniverse_closedDecl_empty]
  exact modelsIn_mono (pointedUniverse_subset_holUniverse point) _

/-- **HOL hosts the open empty declaration unfaithfully**: it validates `inhabited`,
which the declaration leaves undetermined. -/
theorem not_hostsFaithfully_holUniverse_openDecl_empty (point : V) :
    ¬ HostsFaithfully Sat (holUniverse : Set (Interp V N)) (openDecl ∅) :=
  not_hostsFaithfully_of (φ := .inhabited) (fun _ hosted => hosted.1)
    (openDecl_empty_undetermined point).1

theorem not_hostsFaithfully_pointedUniverse_openDecl_empty (point : V) :
    ¬ HostsFaithfully Sat (pointedUniverse (N := N) point) (openDecl ∅) :=
  not_hostsFaithfully_of (φ := .inhabited) (fun _ hosted => ⟨point, hosted.1⟩)
    (openDecl_empty_undetermined point).1

/-- **HOL hosts every declaration with a constructor faithfully.** -/
theorem hostsFaithfully_holUniverse_of_nonempty {ns : Set N} (nonempty : ns.Nonempty) :
    HostsFaithfully Sat (holUniverse : Set (Interp V N)) (openDecl ns) := by
  apply hostsFaithfully_iff_subset.mpr
  intro φ validated m model
  obtain ⟨n, member⟩ := nonempty
  exact validated ⟨⟨m.value n, mem_models_openDecl.mp model n member⟩, model⟩

/-! ## Controls -/

namespace Control

/-- Two constructor names. -/
def bits : Set String := {"zero", "one"}

theorem third_not_mem : "other" ∉ bits := by
  simp [bits]

/-- Positive control: while the type is open, membership of a third name is
undetermined. -/
theorem third_undetermined_while_open :
    Consistent (Sat (V := ℕ)) (insert (.mem "other") (openDecl bits ∪ distinctFrom "other" bits)) ∧
      Consistent (Sat (V := ℕ))
        (insert (.nonMem "other") (openDecl bits ∪ distinctFrom "other" bits)) :=
  open_mem_undetermined third_not_mem (a := 0) (b := 1) (by decide)

/-- Negative control: once the type is closed, it is refuted. -/
theorem third_refuted_once_closed :
    Entails (Sat (V := ℕ)) (closedDecl bits ∪ distinctFrom "other" bits) (.nonMem "other") :=
  closed_refutes_mem

/-- The open empty declaration over the natural numbers leaves inhabitation open, and
its closed counterpart is empty. -/
theorem empty_declarations :
    (¬ Entails (Sat (V := ℕ)) (openDecl (∅ : Set String)) .inhabited ∧
      ¬ Entails (Sat (V := ℕ)) (openDecl (∅ : Set String)) .isEmpty) ∧
      Entails (Sat (V := ℕ)) (closedDecl (∅ : Set String)) .isEmpty :=
  ⟨openDecl_empty_undetermined 0, closedDecl_empty_entails_isEmpty⟩

end Control

end Mettapedia.Logic.TheoryModel.OpenDeclarations
