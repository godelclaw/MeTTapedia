import Mettapedia.Languages.MeTTa.SpaceKindRefinement
import Mettapedia.Languages.MeTTa.CeTTaSpaceEngineRefinement

/-!
# From occurrence-level kind refinement to the support-level query seam

Two statements of "an engine implements a space" live side by side.
`SpaceKindRefinement` is occurrence level and quantifies over programs: an
engine refines the atom kind when, after every program, it shows the bag of
stored atoms the kind shows. `CeTTaSpaceEngineRefinement` is support level and
fixes one HE space: a backend refines it on the shared query lane when its
equation-query and type supports equal that space's
(`SharedQueryRefinement`, `HE.FaithfulBackend`). This module relates them.

* **HE's list space is an engine of the atom kind.** `Space.add` conses and
  `Space.remove` erases the first occurrence; read through its bag it refines
  the atom kind (`heSpaceEngine_refines`), so it answers every program as any
  other atom engine does.
* **Why the seam is not a function of the bag.** HE's equation query renames
  an equation's variables with a suffix taken from the equation's position in
  the list. Permuting two equations with variables changes the answers
  (`query_support_depends_on_positions`), so no store that knows only the bag
  of atoms answers equation queries as HE does
  (`no_bag_level_query_support`). Type support has no such dependence: it is a
  function of the atoms present (`typeSupport_congr`).
* **For closed equations the seam is support level.** When no stored equation
  has variables, the query support depends only on the atoms present
  (`queryResultSupport_closed`); a store of the present atoms
  (`PresentAtoms`) is then a faithful backend (`presentFaithful`).
* **The bridge.** After any program whose added atoms are closed, the atoms an
  engine refining the atom kind shows form a faithful backend of the HE space
  the same program builds, on the shared query lane of every engine
  (`sharedQueryRefinement_of_refines`).
* **The converse fails.** A store of the support alone gives the same seam
  after adding an atom twice, yet it is no atom engine
  (`seam_without_atom_refinement`); and after removing one of two copies it no
  longer has even the support right (`Controls.support_store_loses_support`):
  keeping the support under removal needs counts.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.SpaceKindSupportBridge

open Mettapedia.Languages.MeTTa.SpaceKinds
open Mettapedia.Languages.MeTTa.SpaceKindRefinement
open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.CeTTaSpaceEngineRefinement
open Mettapedia.Languages.MeTTa.SpaceEngineBoundary
open Mettapedia.Languages.MeTTa.AbstractMachineBoundary
open Mettapedia.Languages.MeTTa.OSLFCore (Atom instBEqAtom)

/-! ## HE's list space as an engine of the atom kind -/

/-- The two Boolean equalities of atoms agree. -/
theorem instBEqAtom_eq : (instBEqAtom : BEq Atom) = instBEqOfDecidableEq := by
  have agree : ∀ first second : Atom,
      (instBEqAtom : BEq Atom).beq first second =
        (instBEqOfDecidableEq : BEq Atom).beq first second := by
    intro first second
    show (first == second) = decide (first = second)
    by_cases same : first = second
    · subst same
      simp
    · simp [same]
  cases hInst : (instBEqAtom : BEq Atom)
  cases hDec : (instBEqOfDecidableEq : BEq Atom)
  congr
  funext first second
  have := agree first second
  rw [hInst, hDec] at this
  exact this

/-- HE's removal takes one occurrence off the bag. -/
theorem coe_remove (space : Space) (atom : Atom) :
    (((space.remove atom).atoms : List Atom) : Multiset Atom) =
      (space.atoms : Multiset Atom).erase atom := by
  rw [Multiset.coe_erase]
  show ((space.atoms.erase atom : List Atom) : Multiset Atom) = _
  congr 2
  exact instBEqAtom_eq

/-- HE's list space as an engine: `add` conses, `remove` erases the first
occurrence, and it shows the bag of its atoms. -/
abbrev heSpaceEngine : Machine.{0, 0, 0} (Command Atom) (Multiset Atom) where
  State := Space
  init := Space.empty
  step space
    | .add atom => space.add atom
    | .remove atom => space.remove atom
  observe space := (space.atoms : Multiset Atom)

/-- **HE's list space refines the atom kind.** -/
def heSpaceEngine_refines : Refinement heSpaceEngine atomMachine where
  abs space := (space.atoms : Multiset Atom)
  abs_init := rfl
  abs_step space command := by
    cases command with
    | add atom => rfl
    | remove atom => exact coe_remove space atom
  observe_abs _ := rfl

/-- HE's bag space (`HE.BagSpace`) inserts as the atom kind does. -/
theorem bagSpace_add (space : BagSpace) (atom : Atom) :
    (space.add atom).atoms = (atomKind (α := Atom)).add space.atoms atom := rfl

/-- After any program, every engine refining the atom kind shows the bag
HE's list space holds. -/
theorem observe_run_eq_heSpace {engine : Machine.{0, 0, 0} (Command Atom) (Multiset Atom)}
    (refines : Refinement engine atomMachine) (program : List (Command Atom)) :
    engine.observe (engine.run program) = ((heSpaceEngine.run program).atoms : Multiset Atom) :=
  congrFun (engines_agree refines heSpaceEngine_refines) program

/-! ## Equation queries by position -/

/-- The answers one stored atom, at a position, gives an equation query: the
body of `queryEquations`. -/
def equationAnswers (atom : Atom) (fuel : Nat) (equation : Atom) (index : Nat) :
    List (Atom × Bindings) :=
  match equation with
  | .expression [.symbol "=", lhs, rhs] =>
    let (lhs', rhs') := freshenEquation index lhs rhs fuel
    (matchAtoms atom lhs' fuel).flatMap fun qb =>
      (mergeBindings qb Bindings.empty fuel).filterMap fun merged =>
        if merged.hasLoop then none else some (rhs', merged)
  | _ => []

theorem queryEquations_eq (space : Space) (atom : Atom) :
    queryEquations space atom =
      space.atoms.zipIdx.flatMap (fun entry => equationAnswers atom 100 entry.1 entry.2) := rfl

/-- The variables the equation query renames in a stored atom: those of an
equation's two sides. -/
def equationVariables (equation : Atom) : List String :=
  match equation with
  | .expression [.symbol "=", lhs, rhs] => (collectVars lhs 100 ++ collectVars rhs 100).eraseDups
  | _ => []

/-- A stored atom whose answers do not depend on its position: an equation
without variables, or no equation. -/
def ClosedAtom (atom : Atom) : Prop := equationVariables atom = []

/-- A space all of whose atoms are closed. -/
def ClosedSpace (space : Space) : Prop := ∀ atom ∈ space.atoms, ClosedAtom atom

theorem equationAnswers_index (atom : Atom) (equation : Atom) (index : Nat)
    (closed : ClosedAtom equation) :
    equationAnswers atom 100 equation index = equationAnswers atom 100 equation 0 := by
  unfold equationAnswers
  split
  · simp only [ClosedAtom, equationVariables] at closed
    simp only [freshenEquation, closed, freshMapping, List.foldl_nil]
  · rfl

/-- **Over closed atoms, the equation query reads each stored atom on its
own.** -/
theorem queryEquations_closed (space : Space) (closed : ClosedSpace space) (atom : Atom) :
    queryEquations space atom = space.atoms.flatMap (fun equation => equationAnswers atom 100 equation 0) := by
  rw [queryEquations_eq]
  have positionFree : ∀ entry ∈ space.atoms.zipIdx,
      equationAnswers atom 100 entry.1 entry.2 = equationAnswers atom 100 entry.1 0 :=
    fun entry member => equationAnswers_index atom entry.1 entry.2
      (closed entry.1 (List.fst_mem_of_mem_zipIdx member))
  rw [List.flatMap_congr positionFree]
  conv_rhs => rw [← List.zipIdx_map_fst 0 space.atoms]
  rw [List.flatMap_map]

/-- **For closed spaces the query support depends only on the atoms
present.** -/
theorem queryResultSupport_closed (space : Space) (closed : ClosedSpace space) (atom : Atom) :
    SpaceQuerySupport.queryResultSupport space atom =
      space.atoms.toFinset.biUnion fun equation => (equationAnswers atom 100 equation 0).toFinset := by
  show (queryEquations space atom).toFinset = _
  rw [queryEquations_closed space closed]
  ext answer
  simp [List.mem_flatMap]

/-! ## Type support depends only on the atoms present -/

theorem mem_getAnnotatedTypes_congr {first second : Space}
    (same : first.atoms.toFinset = second.atoms.toFinset) (atom type : Atom) :
    type ∈ getAnnotatedTypes first atom ↔ type ∈ getAnnotatedTypes second atom := by
  have members : ∀ stored, stored ∈ first.atoms ↔ stored ∈ second.atoms := fun stored => by
    rw [← List.mem_toFinset, same, List.mem_toFinset]
  simp only [getAnnotatedTypes, List.mem_filterMap, members]

theorem mem_defaulted_congr {first second : List Atom} (same : ∀ x, x ∈ first ↔ x ∈ second)
    (fallback x : Atom) :
    x ∈ (if first.isEmpty then [fallback] else first) ↔
      x ∈ (if second.isEmpty then [fallback] else second) := by
  have empty : first.isEmpty = second.isEmpty := by
    rw [Bool.eq_iff_iff, List.isEmpty_iff, List.isEmpty_iff, List.eq_nil_iff_forall_not_mem,
      List.eq_nil_iff_forall_not_mem]
    exact forall_congr' fun y => not_congr (same y)
  rw [empty]
  split_ifs
  · exact Iff.rfl
  · exact same x

/-- **Type support is a function of the atoms present.** -/
theorem typeSupport_congr {first second : Space}
    (same : first.atoms.toFinset = second.atoms.toFinset) (atom : Atom) :
    SpaceQuerySupport.typeSupport first atom = SpaceQuerySupport.typeSupport second atom := by
  show (getAtomTypes first atom).toFinset = (getAtomTypes second atom).toFinset
  ext type
  simp only [List.mem_toFinset, getAtomTypes]
  apply mem_defaulted_congr
  intro x
  cases atom with
  | var _ => exact Iff.rfl
  | grounded _ => exact Iff.rfl
  | symbol _ => exact mem_getAnnotatedTypes_congr same _ x
  | expression elements =>
      by_cases empty : elements.isEmpty
      · simp [empty]
      · simp only [empty, Bool.false_eq_true, if_false]
        exact mem_getAnnotatedTypes_congr same _ x

/-! ## A store of the present atoms -/

/-- A store of the atoms present, answering at the support level. -/
structure PresentAtoms where
  present : Finset Atom

noncomputable instance : SpaceQuerySupport PresentAtoms where
  queryResultSupport store atom :=
    store.present.biUnion fun equation => (equationAnswers atom 100 equation 0).toFinset
  typeSupport store atom := SpaceQuerySupport.typeSupport (Space.ofList store.present.toList) atom

/-- **A store of the present atoms of a closed space is a faithful
backend.** -/
noncomputable def presentFaithful (space : Space) (closed : ClosedSpace space)
    (store : PresentAtoms) (same : store.present = space.atoms.toFinset) :
    FaithfulBackend PresentAtoms space where
  backend := store
  query_agree atom := by
    show (store.present.biUnion fun equation => (equationAnswers atom 100 equation 0).toFinset) =
      SpaceQuerySupport.queryResultSupport space atom
    rw [queryResultSupport_closed space closed, same]
  type_agree atom := by
    show SpaceQuerySupport.typeSupport (Space.ofList store.present.toList) atom =
      SpaceQuerySupport.typeSupport space atom
    apply typeSupport_congr
    show store.present.toList.toFinset = space.atoms.toFinset
    rw [Finset.toList_toFinset, same]

/-- Every engine lane hosts the shared query lane. -/
theorem queryLane_supported (lane : SpaceEngine) :
    AbstractMachineLane.supportedByEngine AbstractMachineLane.runtimeQueryLane lane = true := by
  cases lane
  · exact runtimeQuery_supported_by_native
  · exact runtimeQuery_supported_by_pathmap
  · exact runtimeQuery_supported_by_mork

/-! ## Programs, and the bridge -/

/-- The atoms a program adds. -/
def added : List (Command Atom) → List Atom
  | [] => []
  | .add atom :: rest => atom :: added rest
  | .remove _ :: rest => added rest

/-- A program whose added atoms are closed. -/
def ClosedProgram (program : List (Command Atom)) : Prop := ∀ atom ∈ added program, ClosedAtom atom

theorem mem_run_atoms (program : List (Command Atom)) :
    ∀ start : Space, ∀ atom ∈ (program.foldl heSpaceEngine.step start).atoms,
      atom ∈ start.atoms ∨ atom ∈ added program := by
  induction program with
  | nil => intro start atom member; exact Or.inl member
  | cons command rest ih =>
      intro start atom member
      rw [List.foldl_cons] at member
      rcases ih _ atom member with stored | later
      · cases command with
        | add new =>
            rcases List.mem_cons.mp stored with fresh | old
            · exact Or.inr (fresh ▸ List.mem_cons_self)
            · exact Or.inl old
        | remove old => exact Or.inl (List.mem_of_mem_erase stored)
      · cases command with
        | add new => exact Or.inr (List.mem_cons_of_mem new later)
        | remove old => exact Or.inr later

/-- The HE space a closed program builds is closed. -/
theorem closedSpace_run {program : List (Command Atom)} (closed : ClosedProgram program) :
    ClosedSpace (heSpaceEngine.run program) := by
  intro atom member
  rcases mem_run_atoms program Space.empty atom member with initial | addedAtom
  · cases initial
  · exact closed atom addedAtom

/-- **An occurrence-level refinement of the atom kind induces the
support-level seam**: after any program whose added atoms are closed, the atoms
the engine shows are a faithful backend of the HE space the same program
builds, on the shared query lane of every engine. -/
noncomputable def sharedQueryRefinement_of_refines
    {engine : Machine.{0, 0, 0} (Command Atom) (Multiset Atom)}
    (refines : Refinement engine atomMachine) (program : List (Command Atom))
    (closed : ClosedProgram program) (lane : SpaceEngine) :
    SharedQueryRefinement PresentAtoms lane (heSpaceEngine.run program) where
  faithful := presentFaithful (heSpaceEngine.run program) (closedSpace_run closed)
    ⟨(engine.observe (engine.run program)).toFinset⟩
    (by
      show (engine.observe (engine.run program)).toFinset = (heSpaceEngine.run program).atoms.toFinset
      rw [observe_run_eq_heSpace refines program, List.toFinset_coe])
  queryLaneSupported := queryLane_supported lane

/-- The backend of that seam is the support of the engine's bag. -/
theorem sharedQueryRefinement_of_refines_backend
    {engine : Machine.{0, 0, 0} (Command Atom) (Multiset Atom)}
    (refines : Refinement engine atomMachine) (program : List (Command Atom))
    (closed : ClosedProgram program) (lane : SpaceEngine) :
    (sharedQueryRefinement_of_refines refines program closed lane).backend =
      ⟨(engine.observe (engine.run program)).toFinset⟩ := rfl

/-! ## The obstruction, and the converse -/

/-- The equation `(= (f $x) $x)`. -/
def equationF : Atom := .expression [.symbol "=", .expression [.symbol "f", .var "x"], .var "x"]

/-- The equation `(= (g $y) $y)`. -/
def equationG : Atom := .expression [.symbol "=", .expression [.symbol "g", .var "y"], .var "y"]

/-- The query `(f a)`. -/
def queryF : Atom := .expression [.symbol "f", .symbol "a"]

set_option maxRecDepth 100000 in
theorem answers_first : (queryEquations (Space.ofList [equationF, equationG]) queryF).map Prod.fst =
    [.var "x#0"] := by
  decide

set_option maxRecDepth 100000 in
theorem answers_second : (queryEquations (Space.ofList [equationG, equationF]) queryF).map Prod.fst =
    [.var "x#1"] := by
  decide

theorem image_fst_toFinset (answers : List (Atom × Bindings)) :
    answers.toFinset.image Prod.fst = (answers.map Prod.fst).toFinset := by
  ext atom
  simp

/-- **The equation query depends on positions**: permuting two equations
with variables changes the answers, `$x#0` against `$x#1`. -/
theorem query_support_depends_on_positions :
    (Space.ofList [equationF, equationG]).BagEquiv (Space.ofList [equationG, equationF]) ∧
      SpaceQuerySupport.queryResultSupport (Space.ofList [equationF, equationG]) queryF ≠
        SpaceQuerySupport.queryResultSupport (Space.ofList [equationG, equationF]) queryF := by
  refine ⟨List.Perm.swap equationG equationF [], fun same => ?_⟩
  have imaged := congrArg (Finset.image Prod.fst) same
  change (queryEquations (Space.ofList [equationF, equationG]) queryF).toFinset.image Prod.fst =
    (queryEquations (Space.ofList [equationG, equationF]) queryF).toFinset.image Prod.fst at imaged
  rw [image_fst_toFinset, image_fst_toFinset, answers_first, answers_second] at imaged
  revert imaged
  decide

/-- **No store that knows only the bag of atoms answers equation queries as
HE does.** -/
theorem no_bag_level_query_support :
    ¬ ∃ answer : Multiset Atom → Atom → Finset (Atom × Bindings),
      ∀ (space : Space) (atom : Atom), SpaceQuerySupport.queryResultSupport space atom =
        answer (space.atoms : Multiset Atom) atom := by
  rintro ⟨answer, agrees⟩
  obtain ⟨permuted, differs⟩ := query_support_depends_on_positions
  apply differs
  rw [agrees, agrees]
  exact congrArg (answer · queryF) (Multiset.coe_eq_coe.mpr permuted)

/-- The atom `a`. -/
def atomA : Atom := .symbol "a"

theorem closedAtom_a : ClosedAtom atomA := rfl

/-- **The converse fails**: after adding `a` twice, the support-only store is
the backend of a seam for the HE space of the program, yet it is no atom
engine. -/
theorem seam_without_atom_refinement :
    (∃ seam : SharedQueryRefinement PresentAtoms SpaceEngine.native
        (heSpaceEngine.run [.add atomA, .add atomA]),
      seam.backend = ⟨(supportSet (α := Atom)).run [.add atomA, .add atomA]⟩) ∧
      IsEmpty (Refinement (supportSet (α := Atom)) atomMachine) := by
  refine ⟨⟨⟨presentFaithful _ (closedSpace_run ?_) ⟨(supportSet (α := Atom)).run [.add atomA, .add atomA]⟩
    ?_, queryLane_supported _⟩, rfl⟩, supportSet_not_refines_atom atomA⟩
  · intro atom member
    simp only [added, List.mem_cons, List.not_mem_nil, or_false, or_self] at member
    exact member ▸ closedAtom_a
  · decide

namespace Controls

/-- **A support-only store loses the support under removal**: after adding
`a` twice and removing it once, HE holds one `a`; the store holds none. -/
theorem support_store_loses_support :
    (supportSet (α := Atom)).run [.add atomA, .add atomA, .remove atomA] = ∅ ∧
      (heSpaceEngine.run [.add atomA, .add atomA, .remove atomA]).atoms.toFinset = {atomA} := by
  constructor <;> decide

end Controls

end Mettapedia.Languages.MeTTa.SpaceKindSupportBridge
