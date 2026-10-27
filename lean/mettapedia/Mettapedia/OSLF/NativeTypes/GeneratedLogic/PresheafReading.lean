import Mettapedia.OSLF.NativeTypes.GeneratedLogic.Invariance
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.HigherOrder

/-!
# The presheaf reading of native types

Native types read in the presheaf topos over a site of stages, by Kripke–Joyal forcing, compared with their classical
reading in a native structure (which is their reading in higher-order logic over the language's generators).

- **A site of stages** (`Site`): each stage has points (its valuations, at least one) and elements (families of
  elements of the carrier indexed by its points, constant families among them); arrows between stages map points to
  points, and elements pull back along arrows. A terminal stage has a single point, and every point of a stage is an
  arrow from it.
- **Forcing** (`NativeStructure.forces`): a formula is forced by a family at a stage. The relations of the structure are
  read at every point; disjunction is read at the stage; an existential former (a step, a constructor's arguments, a
  split, a member, a body, a witness of a type, distinct successors) needs a witness among the elements of the stage; a
  universal former and the negated atoms quantify over every later stage and every element there; fixed points are the
  least and greatest fixed points among the sets of families closed under pulling back.
- **The presheaf property** (`forces_pull`): forcing is closed under pulling back along arrows.
- **Soundness** (`forces_sound`): what a family forces holds, classically, at each of its points. So the classical
  judgment over valuations (`holdsAt`), itself closed under pulling back (`holdsAt_pull`), is implied by forcing.
- **Agreement on the negative fragment** (`forces_iff_of_negative`): for formulas built from atoms, negated atoms,
  conjunction, greatest fixed points and universal formers with at most one argument (`Formula.negative`), forcing is
  the classical judgment, at every stage.
- **Agreement at the closed stage** (`forces_terminal_iff`, `forces_terminal_iff_denote`): for existential formers,
  conjunction and disjunction over negative formulas (`Formula.settled`), forcing at the terminal stage is classical
  truth, and so the denotation of the formula's translation to higher-order logic.

Where these fragments are left, the readings part: a disjunction holds at every point without either side holding at
the stage, and a universal former quantifies over the generic elements of later stages.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.GeneratedLogic

open Mettapedia.OSLF.MeTTaIL.Syntax
open Formula

universe u

/-- **A site of stages** for a carrier: stages with points and elements, arrows acting on points, a terminal stage. -/
structure Site (Carrier : Type u) where
  /-- The stages. -/
  Stage : Type
  /-- The points of a stage: its valuations. -/
  Point : Stage → Type
  /-- Every stage has a point. -/
  inhabited : ∀ stage, Nonempty (Point stage)
  /-- The arrows from a stage to another, as maps of points. -/
  Arrow : (source target : Stage) → Set (Point source → Point target)
  arrow_id : ∀ stage, (fun point => point : Point stage → Point stage) ∈ Arrow stage stage
  arrow_comp : ∀ {first second third : Stage} {outer : Point second → Point third} {inner : Point first → Point second},
    outer ∈ Arrow second third → inner ∈ Arrow first second → (fun point => outer (inner point)) ∈ Arrow first third
  /-- The elements of a stage: families of elements of the carrier indexed by its points. -/
  Elem : (stage : Stage) → Set (Point stage → Carrier)
  elem_pull : ∀ {source target : Stage} {element : Point target → Carrier} {arrow : Point source → Point target},
    element ∈ Elem target → arrow ∈ Arrow source target → (fun point => element (arrow point)) ∈ Elem source
  const_mem : ∀ stage (value : Carrier), (fun _ => value) ∈ Elem stage
  /-- The terminal stage. -/
  terminal : Stage
  terminal_subsingleton : ∀ first second : Point terminal, first = second
  /-- Every point of a stage is an arrow from the terminal stage. -/
  global : ∀ stage (point : Point stage), (fun _ => point) ∈ Arrow terminal stage

namespace Site

variable {Carrier : Type u} (site : Site Carrier)

/-- A family of elements of the carrier at a stage. -/
abbrev Family (stage : site.Stage) : Type u := site.Point stage → Carrier

/-- Sets of families, one at each stage. -/
abbrev Sets : Type u := (stage : site.Stage) → Set (site.Family stage)

/-- **Closed under pulling back** along arrows: a subpresheaf. -/
def Stable (sets : site.Sets) : Prop :=
  ∀ {source target : site.Stage} {element : site.Family target} {arrow : site.Point source → site.Point target},
    element ∈ sets target → arrow ∈ site.Arrow source target → (fun point => element (arrow point)) ∈ sets source

/-- The families whose every value lies in a set. -/
def lift (set : Set Carrier) : site.Sets := fun _ => {element | ∀ point, element point ∈ set}

theorem lift_stable (set : Set Carrier) : site.Stable (site.lift set) :=
  fun inside _ _ => inside _

/-- An environment extended with sets of families. -/
def extend {n : ℕ} (env : Fin n → site.Sets) (sets : site.Sets) : Fin (n + 1) → site.Sets := Fin.cons sets env

/-- **A property refuted at every later stage**: at no later stage does it hold at every point. -/
def Refuted {stage : site.Stage} (holds : Carrier → Prop) (element : site.Family stage) : Prop :=
  ∀ (stage' : site.Stage) (arrow : site.Point stage' → site.Point stage), arrow ∈ site.Arrow stage' stage →
    ¬ ∀ point, holds (element (arrow point))

/-- An environment of sets of families whose values lie in a classical environment. -/
def Into {n : ℕ} (env : Fin n → site.Sets) (classical : Env Carrier n) : Prop :=
  ∀ index (stage : site.Stage) (element : site.Family stage), element ∈ env index stage → ∀ point, element point ∈ classical index

variable {site} in
theorem Into.extend {n : ℕ} {env : Fin n → site.Sets} {classical : Env Carrier n} (into : site.Into env classical)
    {sets : site.Sets} {set : Set Carrier} (inside : ∀ (stage : site.Stage) (element : site.Family stage),
      element ∈ sets stage → ∀ point, element point ∈ set) :
    site.Into (site.extend env sets) (classical.extend set) := by
  intro index
  refine Fin.cases ?_ (fun index' => ?_) index
  · simpa only [Site.extend, Env.extend, Fin.cons_zero] using inside
  · simpa only [Site.extend, Env.extend, Fin.cons_succ] using into index'

/-- An environment of sets of families containing every family whose values lie in a classical environment. -/
def Onto {n : ℕ} (env : Fin n → site.Sets) (classical : Env Carrier n) : Prop :=
  ∀ index (stage : site.Stage) (element : site.Family stage), (∀ point, element point ∈ classical index) → element ∈ env index stage

variable {site} in
theorem Onto.extend {n : ℕ} {env : Fin n → site.Sets} {classical : Env Carrier n} (onto : site.Onto env classical)
    {sets : site.Sets} {set : Set Carrier} (inside : ∀ (stage : site.Stage) (element : site.Family stage),
      (∀ point, element point ∈ set) → element ∈ sets stage) :
    site.Onto (site.extend env sets) (classical.extend set) := by
  intro index
  refine Fin.cases ?_ (fun index' => ?_) index
  · simpa only [Site.extend, Env.extend, Fin.cons_zero] using inside
  · simpa only [Site.extend, Env.extend, Fin.cons_succ] using onto index'

/-- At the terminal stage, a family is constant. -/
theorem terminal_const (element : site.Family site.terminal) (point : site.Point site.terminal) :
    element = fun _ => element point :=
  funext fun other => congrArg element (site.terminal_subsingleton other point)

end Site

namespace NativeStructure

variable {Carrier : Type u} (S : NativeStructure Carrier) (site : Site Carrier)

/-- **At least `count` elements of the stage satisfy the predicate**, apart from one another at every point. -/
def AtLeastAt {stage : site.Stage} (count : ℕ) (holds : site.Family stage → Prop) : Prop :=
  ∃ witnesses : List (site.Family stage), witnesses.length = count ∧ (∀ witness ∈ witnesses, witness ∈ site.Elem stage) ∧
    witnesses.Pairwise (fun first second => ∀ point, ¬ S.same (first point) (second point)) ∧
      ∀ witness ∈ witnesses, holds witness

mutual
/-- **Forcing** of a formula by a family at a stage, in an environment of sets of families. -/
def forces : {n : ℕ} → (Fin n → site.Sets) → (stage : site.Stage) → Formula n → site.Family stage → Prop
  | _, _, _, .top, _ => True
  | _, _, _, .bot, _ => False
  | _, env, stage, .and left right, element => forces env stage left element ∧ forces env stage right element
  | _, env, stage, .or left right, element => forces env stage left element ∨ forces env stage right element
  | _, env, stage, .var index, element => element ∈ env index stage
  | _, env, stage, .mu inner, element =>
      ∀ sets : site.Sets, site.Stable sets →
        (∀ (stage' : site.Stage) (other : site.Family stage'), forces (site.extend env sets) stage' inner other →
          other ∈ sets stage') → element ∈ sets stage
  | _, env, stage, .nu inner, element =>
      ∃ sets : site.Sets, site.Stable sets ∧ element ∈ sets stage ∧
        ∀ (stage' : site.Stage) (other : site.Family stage'), other ∈ sets stage' →
          forces (site.extend env sets) stage' inner other
  | _, env, stage, .possibly label formula, element =>
      ∃ next ∈ site.Elem stage, (∀ point, S.step (element point) label (next point)) ∧ forces env stage formula next
  | _, env, stage, .necessarily label formula, element =>
      ∀ (stage' : site.Stage) (arrow : site.Point stage' → site.Point stage), arrow ∈ site.Arrow stage' stage →
        ∀ next ∈ site.Elem stage', (∀ point, S.step (element (arrow point)) label (next point)) →
          forces env stage' formula next
  | _, env, stage, .sometimeBefore label formula, element =>
      ∃ previous ∈ site.Elem stage, (∀ point, S.step (previous point) label (element point)) ∧
        forces env stage formula previous
  | _, env, stage, .alwaysBefore label formula, element =>
      ∀ (stage' : site.Stage) (arrow : site.Point stage' → site.Point stage), arrow ∈ site.Arrow stage' stage →
        ∀ previous ∈ site.Elem stage', (∀ point, S.step (previous point) label (element (arrow point))) →
          forces env stage' formula previous
  | _, env, stage, .atLeast count direction label formula, element =>
      S.AtLeastAt site count fun other =>
        (∀ point, S.stepIn direction (element point) label (other point)) ∧ forces env stage formula other
  | _, env, stage, .allButFewer count direction label formula, element =>
      ∀ (stage' : site.Stage) (arrow : site.Point stage' → site.Point stage), arrow ∈ site.Arrow stage' stage →
        ¬ S.AtLeastAt site count fun other =>
          (∀ point, S.stepIn direction (element (arrow point)) label (other point)) ∧
            ∀ (stage'' : site.Stage) (arrow' : site.Point stage'' → site.Point stage'), arrow' ∈ site.Arrow stage'' stage' →
              ¬ forces env stage'' formula fun point => other (arrow' point)
  | _, env, stage, .built constructor arguments, element =>
      ∃ parts : List (site.Family stage), (∀ part ∈ parts, part ∈ site.Elem stage) ∧
        (∀ point, S.built (element point) constructor (parts.map fun part => part point)) ∧
          forcesAll env stage arguments parts
  | _, env, stage, .everyBuilt constructor arguments, element =>
      ∀ (stage' : site.Stage) (arrow : site.Point stage' → site.Point stage), arrow ∈ site.Arrow stage' stage →
        ∀ parts : List (site.Family stage'), (∀ part ∈ parts, part ∈ site.Elem stage') →
          (∀ point, S.built (element (arrow point)) constructor (parts.map fun part => part point)) →
            forcesSome env stage' arguments parts
  | _, env, stage, .split kind left right, element =>
      ∃ first ∈ site.Elem stage, ∃ second ∈ site.Elem stage,
        (∀ point, S.split (element point) kind (first point) (second point)) ∧
          forces env stage left first ∧ forces env stage right second
  | _, env, stage, .everySplit kind left right, element =>
      ∀ (stage' : site.Stage) (arrow : site.Point stage' → site.Point stage), arrow ∈ site.Arrow stage' stage →
        ∀ first ∈ site.Elem stage', ∀ second ∈ site.Elem stage',
          (∀ point, S.split (element (arrow point)) kind (first point) (second point)) →
            forces env stage' left first ∨ forces env stage' right second
  | _, _, _, .empty kind, element => ∀ point, S.empty (element point) kind
  | _, _, _, .nonEmpty kind, element => site.Refuted (fun value => S.empty value kind) element
  | _, env, stage, .single kind formula, element =>
      ∃ member ∈ site.Elem stage, (∀ point, S.single (element point) kind (member point)) ∧
        forces env stage formula member
  | _, env, stage, .everySingle kind formula, element =>
      ∀ (stage' : site.Stage) (arrow : site.Point stage' → site.Point stage), arrow ∈ site.Arrow stage' stage →
        ∀ member ∈ site.Elem stage', (∀ point, S.single (element (arrow point)) kind (member point)) →
          forces env stage' formula member
  | _, env, stage, .body formula, element =>
      ∃ inner ∈ site.Elem stage, (∀ point, S.body (element point) (inner point)) ∧ forces env stage formula inner
  | _, env, stage, .everyBody formula, element =>
      ∀ (stage' : site.Stage) (arrow : site.Point stage' → site.Point stage), arrow ∈ site.Arrow stage' stage →
        ∀ inner ∈ site.Elem stage', (∀ point, S.body (element (arrow point)) (inner point)) →
          forces env stage' formula inner
  | _, env, stage, .multiBody arity formula, element =>
      ∃ inner ∈ site.Elem stage, (∀ point, S.multiBody (element point) arity (inner point)) ∧
        forces env stage formula inner
  | _, env, stage, .everyMultiBody arity formula, element =>
      ∀ (stage' : site.Stage) (arrow : site.Point stage' → site.Point stage), arrow ∈ site.Arrow stage' stage →
        ∀ inner ∈ site.Elem stage', (∀ point, S.multiBody (element (arrow point)) arity (inner point)) →
          forces env stage' formula inner
  | _, _, _, .bound index, element => ∀ point, S.bound (element point) index
  | _, _, _, .notBound index, element => site.Refuted (fun value => S.bound value index) element
  | _, _, _, .typed type, element => ∀ point, S.typed (element point) type
  | _, _, _, .untyped type, element => site.Refuted (fun value => S.typed value type) element
  | _, _, _, .is term, element => ∀ point, S.named (element point) term
  | _, _, _, .isNot term, element => site.Refuted (fun value => S.named value term) element
  | _, env, stage, .mapsAll argument result, element =>
      ∃ inner ∈ site.Elem stage, (∀ point, S.body (element point) (inner point)) ∧
        ∀ (stage' : site.Stage) (arrow : site.Point stage' → site.Point stage), arrow ∈ site.Arrow stage' stage →
          ∀ value ∈ site.Elem stage', forces env stage' argument value ∨
            forces env stage' result fun point => S.apply (inner (arrow point)) (value point)
  | _, env, stage, .mapsSome argument result, element =>
      ∀ (stage' : site.Stage) (arrow : site.Point stage' → site.Point stage), arrow ∈ site.Arrow stage' stage →
        ∀ inner ∈ site.Elem stage', (∀ point, S.body (element (arrow point)) (inner point)) →
          ∃ value ∈ site.Elem stage', forces env stage' argument value ∧
            forces env stage' result fun point => S.apply (inner point) (value point)
  | _, env, stage, .someOf type formula, _ =>
      ∃ witness ∈ site.Elem stage, (∀ point, S.typed (witness point) type) ∧ forces env stage formula witness
  | _, env, stage, .everyOf type formula, _ =>
      ∀ (stage' : site.Stage) (arrow : site.Point stage' → site.Point stage), arrow ∈ site.Arrow stage' stage →
        ∀ witness ∈ site.Elem stage', (∀ point, S.typed (witness point) type) → forces env stage' formula witness
  | _, _, _, .inRelation relation, element => ∀ point, S.inRelation (element point) relation
  | _, _, _, .notInRelation relation, element => site.Refuted (fun value => S.inRelation value relation) element

/-- Every formula of the list is forced by the corresponding family, and the lengths agree. -/
def forcesAll : {n : ℕ} → (Fin n → site.Sets) → (stage : site.Stage) → Formulas n → List (site.Family stage) → Prop
  | _, _, _, .nil, [] => True
  | _, env, stage, .cons formula formulas, part :: parts => forces env stage formula part ∧ forcesAll env stage formulas parts
  | _, _, _, _, _ => False

/-- Some formula of the list is forced by the corresponding family, or the lengths differ. -/
def forcesSome : {n : ℕ} → (Fin n → site.Sets) → (stage : site.Stage) → Formulas n → List (site.Family stage) → Prop
  | _, _, _, .nil, [] => False
  | _, env, stage, .cons formula formulas, part :: parts => forces env stage formula part ∨ forcesSome env stage formulas parts
  | _, _, _, _, _ => True
end

/-- **The classical judgment over valuations**: the formula holds at each point of the family. -/
def holdsAt {n : ℕ} (classical : Env Carrier n) (formula : Formula n) {stage : site.Stage} (element : site.Family stage) :
    Prop :=
  ∀ point, S.sat classical formula (element point)

/-- **The classical judgment is closed under pulling back.** -/
theorem holdsAt_pull {n : ℕ} {classical : Env Carrier n} {formula : Formula n} {source target : site.Stage}
    {element : site.Family target} (holds : S.holdsAt site classical formula element)
    (arrow : site.Point source → site.Point target) :
    S.holdsAt site classical formula (fun point => element (arrow point)) :=
  fun point => holds (arrow point)

/-! ## The presheaf property -/

mutual
/-- **Forcing is closed under pulling back**, in an environment of stable sets. -/
theorem forces_pull : ∀ {n : ℕ} (formula : Formula n) {env : Fin n → site.Sets}, (∀ index, site.Stable (env index)) →
    ∀ {source target : site.Stage} {arrow : site.Point source → site.Point target}, arrow ∈ site.Arrow source target →
      ∀ (element : site.Family target), S.forces site env target formula element →
        S.forces site env source formula fun point => element (arrow point)
  | _, .top, _, _, _, _, _, _, _, _ => trivial
  | _, .bot, _, _, _, _, _, _, _, holds => holds
  | _, .and left right, _, stable, _, _, _, mem, element, holds =>
    ⟨forces_pull left stable mem element holds.1, forces_pull right stable mem element holds.2⟩
  | _, .or left right, _, stable, _, _, _, mem, element, holds =>
    holds.imp (forces_pull left stable mem element) (forces_pull right stable mem element)
  | _, .var index, _, stable, _, _, _, mem, _, holds => stable index holds mem
  | _, .mu _, _, _, _, _, _, mem, _, holds => fun sets stable' prefixed => stable' (holds sets stable' prefixed) mem
  | _, .nu _, _, _, _, _, _, mem, _, holds => by
    obtain ⟨sets, stable', inside, invariant⟩ := holds
    exact ⟨sets, stable', stable' inside mem, invariant⟩
  | _, .possibly _ formula, _, stable, _, _, arrow, mem, _, holds => by
    obtain ⟨next, nextMem, steps, nextHolds⟩ := holds
    exact ⟨fun point => next (arrow point), site.elem_pull nextMem mem, fun point => steps (arrow point),
      forces_pull formula stable mem next nextHolds⟩
  | _, .necessarily _ _, _, _, _, _, _, mem, _, holds => fun stage' _ mem' next nextMem steps =>
    holds stage' _ (site.arrow_comp mem mem') next nextMem steps
  | _, .sometimeBefore _ formula, _, stable, _, _, arrow, mem, _, holds => by
    obtain ⟨previous, previousMem, steps, previousHolds⟩ := holds
    exact ⟨fun point => previous (arrow point), site.elem_pull previousMem mem, fun point => steps (arrow point),
      forces_pull formula stable mem previous previousHolds⟩
  | _, .alwaysBefore _ _, _, _, _, _, _, mem, _, holds => fun stage' _ mem' previous previousMem steps =>
    holds stage' _ (site.arrow_comp mem mem') previous previousMem steps
  | _, .atLeast _ _ _ formula, _, stable, _, _, arrow, mem, _, holds => by
    obtain ⟨witnesses, length, members, apart, each⟩ := holds
    refine ⟨witnesses.map fun witness point => witness (arrow point), by rw [List.length_map, length], ?_, ?_, ?_⟩
    · intro pulled pulledMem
      obtain ⟨witness, witnessMem, rfl⟩ := List.mem_map.mp pulledMem
      exact site.elem_pull (members witness witnessMem) mem
    · exact List.pairwise_map.mpr (apart.imp fun distinct point => distinct (arrow point))
    · intro pulled pulledMem
      obtain ⟨witness, witnessMem, rfl⟩ := List.mem_map.mp pulledMem
      exact ⟨fun point => (each witness witnessMem).1 (arrow point),
        forces_pull formula stable mem witness (each witness witnessMem).2⟩
  | _, .allButFewer _ _ _ _, _, _, _, _, _, mem, _, holds => fun stage' _ mem' =>
    holds stage' _ (site.arrow_comp mem mem')
  | _, .built _ arguments, _, stable, _, _, arrow, mem, _, holds => by
    obtain ⟨parts, members, builtAt, all⟩ := holds
    refine ⟨parts.map fun part point => part (arrow point), ?_, fun point => ?_, forcesAll_pull arguments stable mem parts all⟩
    · intro pulled pulledMem
      obtain ⟨part, partMem, rfl⟩ := List.mem_map.mp pulledMem
      exact site.elem_pull (members part partMem) mem
    · rw [List.map_map]
      exact builtAt (arrow point)
  | _, .everyBuilt _ _, _, _, _, _, _, mem, _, holds => fun stage' _ mem' parts members builtAt =>
    holds stage' _ (site.arrow_comp mem mem') parts members builtAt
  | _, .split _ left right, _, stable, _, _, arrow, mem, _, holds => by
    obtain ⟨first, firstMem, second, secondMem, splits, leftHolds, rightHolds⟩ := holds
    exact ⟨fun point => first (arrow point), site.elem_pull firstMem mem, fun point => second (arrow point),
      site.elem_pull secondMem mem, fun point => splits (arrow point), forces_pull left stable mem first leftHolds,
      forces_pull right stable mem second rightHolds⟩
  | _, .everySplit _ _ _, _, _, _, _, _, mem, _, holds => fun stage' _ mem' first firstMem second secondMem splits =>
    holds stage' _ (site.arrow_comp mem mem') first firstMem second secondMem splits
  | _, .empty _, _, _, _, _, arrow, _, _, holds => fun point => holds (arrow point)
  | _, .nonEmpty _, _, _, _, _, _, mem, _, holds => fun stage' _ mem' => holds stage' _ (site.arrow_comp mem mem')
  | _, .single _ formula, _, stable, _, _, arrow, mem, _, holds => by
    obtain ⟨member, memberMem, singles, memberHolds⟩ := holds
    exact ⟨fun point => member (arrow point), site.elem_pull memberMem mem, fun point => singles (arrow point),
      forces_pull formula stable mem member memberHolds⟩
  | _, .everySingle _ _, _, _, _, _, _, mem, _, holds => fun stage' _ mem' member memberMem singles =>
    holds stage' _ (site.arrow_comp mem mem') member memberMem singles
  | _, .body formula, _, stable, _, _, arrow, mem, _, holds => by
    obtain ⟨inner, innerMem, bodies, innerHolds⟩ := holds
    exact ⟨fun point => inner (arrow point), site.elem_pull innerMem mem, fun point => bodies (arrow point),
      forces_pull formula stable mem inner innerHolds⟩
  | _, .everyBody _, _, _, _, _, _, mem, _, holds => fun stage' _ mem' inner innerMem bodies =>
    holds stage' _ (site.arrow_comp mem mem') inner innerMem bodies
  | _, .multiBody _ formula, _, stable, _, _, arrow, mem, _, holds => by
    obtain ⟨inner, innerMem, bodies, innerHolds⟩ := holds
    exact ⟨fun point => inner (arrow point), site.elem_pull innerMem mem, fun point => bodies (arrow point),
      forces_pull formula stable mem inner innerHolds⟩
  | _, .everyMultiBody _ _, _, _, _, _, _, mem, _, holds => fun stage' _ mem' inner innerMem bodies =>
    holds stage' _ (site.arrow_comp mem mem') inner innerMem bodies
  | _, .bound _, _, _, _, _, arrow, _, _, holds => fun point => holds (arrow point)
  | _, .notBound _, _, _, _, _, _, mem, _, holds => fun stage' _ mem' => holds stage' _ (site.arrow_comp mem mem')
  | _, .typed _, _, _, _, _, arrow, _, _, holds => fun point => holds (arrow point)
  | _, .untyped _, _, _, _, _, _, mem, _, holds => fun stage' _ mem' => holds stage' _ (site.arrow_comp mem mem')
  | _, .is _, _, _, _, _, arrow, _, _, holds => fun point => holds (arrow point)
  | _, .isNot _, _, _, _, _, _, mem, _, holds => fun stage' _ mem' => holds stage' _ (site.arrow_comp mem mem')
  | _, .mapsAll _ _, _, _, _, _, arrow, mem, _, holds => by
    obtain ⟨inner, innerMem, bodies, all⟩ := holds
    exact ⟨fun point => inner (arrow point), site.elem_pull innerMem mem, fun point => bodies (arrow point),
      fun stage' _ mem' value valueMem => all stage' _ (site.arrow_comp mem mem') value valueMem⟩
  | _, .mapsSome _ _, _, _, _, _, _, mem, _, holds => fun stage' _ mem' inner innerMem bodies =>
    holds stage' _ (site.arrow_comp mem mem') inner innerMem bodies
  | _, .someOf _ formula, _, stable, _, _, arrow, mem, _, holds => by
    obtain ⟨witness, witnessMem, typedAt, witnessHolds⟩ := holds
    exact ⟨fun point => witness (arrow point), site.elem_pull witnessMem mem, fun point => typedAt (arrow point),
      forces_pull formula stable mem witness witnessHolds⟩
  | _, .everyOf _ _, _, _, _, _, _, mem, _, holds => fun stage' _ mem' witness witnessMem typedAt =>
    holds stage' _ (site.arrow_comp mem mem') witness witnessMem typedAt
  | _, .inRelation _, _, _, _, _, arrow, _, _, holds => fun point => holds (arrow point)
  | _, .notInRelation _, _, _, _, _, _, mem, _, holds => fun stage' _ mem' => holds stage' _ (site.arrow_comp mem mem')

theorem forcesAll_pull : ∀ {n : ℕ} (formulas : Formulas n) {env : Fin n → site.Sets}, (∀ index, site.Stable (env index)) →
    ∀ {source target : site.Stage} {arrow : site.Point source → site.Point target}, arrow ∈ site.Arrow source target →
      ∀ (parts : List (site.Family target)), S.forcesAll site env target formulas parts →
        S.forcesAll site env source formulas (parts.map fun part point => part (arrow point))
  | _, .nil, _, _, _, _, _, _, [], _ => trivial
  | _, .cons formula formulas, _, stable, _, _, _, mem, part :: parts, holds =>
    ⟨forces_pull formula stable mem part holds.1, forcesAll_pull formulas stable mem parts holds.2⟩
  | _, .nil, _, _, _, _, _, _, _ :: _, holds => holds.elim
  | _, .cons _ _, _, _, _, _, _, _, [], holds => holds.elim

theorem forcesSome_pull : ∀ {n : ℕ} (formulas : Formulas n) {env : Fin n → site.Sets}, (∀ index, site.Stable (env index)) →
    ∀ {source target : site.Stage} {arrow : site.Point source → site.Point target}, arrow ∈ site.Arrow source target →
      ∀ (parts : List (site.Family target)), S.forcesSome site env target formulas parts →
        S.forcesSome site env source formulas (parts.map fun part point => part (arrow point))
  | _, .nil, _, _, _, _, _, _, [], holds => holds.elim
  | _, .cons formula formulas, _, stable, _, _, _, mem, part :: parts, holds =>
    holds.imp (forces_pull formula stable mem part) (forcesSome_pull formulas stable mem parts)
  | _, .nil, _, _, _, _, _, _, _ :: _, _ => trivial
  | _, .cons _ _, _, _, _, _, _, _, [], _ => trivial
end

/-! ## Soundness -/

mutual
/-- **Forcing is sound**: what a family forces holds, classically, at each of its points. -/
theorem forces_sound : ∀ {n : ℕ} (formula : Formula n) {env : Fin n → site.Sets} {classical : Env Carrier n},
    site.Into env classical → ∀ {stage : site.Stage} (element : site.Family stage),
      S.forces site env stage formula element → S.holdsAt site classical formula element
  | _, .top, _, _, _, _, _, _, _ => trivial
  | _, .bot, _, _, _, _, _, holds, _ => holds.elim
  | _, .and left right, _, _, into, _, element, holds, point =>
    ⟨forces_sound left into element holds.1 point, forces_sound right into element holds.2 point⟩
  | _, .or left right, _, _, into, _, element, holds, point =>
    holds.elim (fun holds => .inl (forces_sound left into element holds point))
      (fun holds => .inr (forces_sound right into element holds point))
  | _, .var index, _, _, into, stage, element, holds, point => into index stage element holds point
  | _, .mu inner, env, classical, into, stage, element, holds, point => by
    intro closed isClosed
    have prefixed : ∀ (stage' : site.Stage) (other : site.Family stage'),
        S.forces site (site.extend env (site.lift closed)) stage' inner other → other ∈ site.lift closed stage' :=
      fun stage' other forced point' => isClosed _
        (forces_sound inner (into.extend fun _ _ inside => inside) other forced point')
    exact holds (site.lift closed) (site.lift_stable closed) prefixed point
  | _, .nu inner, env, classical, into, stage, element, holds, point => by
    obtain ⟨sets, _, inside, invariant⟩ := holds
    let reached : Set Carrier := {value | ∃ (stage' : site.Stage) (other : site.Family stage') (point' : site.Point stage'),
      other ∈ sets stage' ∧ other point' = value}
    refine ⟨reached, ⟨stage, element, point, inside, rfl⟩, ?_⟩
    rintro _ ⟨stage', other, point', otherInside, rfl⟩
    exact forces_sound inner (into.extend (set := reached)
      fun stage'' element' inside' point'' => ⟨stage'', element', point'', inside', rfl⟩)
      other (invariant stage' other otherInside) point'
  | _, .possibly _ formula, _, _, into, _, _, holds, point => by
    obtain ⟨next, _, steps, nextHolds⟩ := holds
    exact ⟨next point, steps point, forces_sound formula into next nextHolds point⟩
  | _, .necessarily _ formula, _, _, into, stage, _, holds, point => fun next step => by
    obtain ⟨point'⟩ := site.inhabited site.terminal
    exact forces_sound formula into _ (holds site.terminal _ (site.global stage point) _ (site.const_mem _ next)
      fun _ => step) point'
  | _, .sometimeBefore _ formula, _, _, into, _, _, holds, point => by
    obtain ⟨previous, _, steps, previousHolds⟩ := holds
    exact ⟨previous point, steps point, forces_sound formula into previous previousHolds point⟩
  | _, .alwaysBefore _ formula, _, _, into, stage, _, holds, point => fun previous step => by
    obtain ⟨point'⟩ := site.inhabited site.terminal
    exact forces_sound formula into _ (holds site.terminal _ (site.global stage point) _ (site.const_mem _ previous)
      fun _ => step) point'
  | _, .atLeast _ _ _ formula, _, _, into, _, _, holds, point => by
    obtain ⟨witnesses, length, _, apart, each⟩ := holds
    refine ⟨witnesses.map fun witness => witness point, by rw [List.length_map, length],
      List.pairwise_map.mpr (apart.imp fun distinct => distinct point), ?_⟩
    intro value valueMem
    obtain ⟨witness, witnessMem, rfl⟩ := List.mem_map.mp valueMem
    exact ⟨(each witness witnessMem).1 point, forces_sound formula into witness (each witness witnessMem).2 point⟩
  | _, .allButFewer _ _ _ formula, _, _, into, stage, _, holds, point => by
    rintro ⟨witnesses, length, apart, each⟩
    refine holds site.terminal _ (site.global stage point) ⟨witnesses.map fun witness _ => witness,
      by rw [List.length_map, length], ?_, List.pairwise_map.mpr (apart.imp fun distinct _ => distinct), ?_⟩
    · intro constant constantMem
      obtain ⟨witness, _, rfl⟩ := List.mem_map.mp constantMem
      exact site.const_mem _ witness
    · intro constant constantMem
      obtain ⟨witness, witnessMem, rfl⟩ := List.mem_map.mp constantMem
      refine ⟨fun _ => (each witness witnessMem).1, fun stage'' arrow' _ forced => ?_⟩
      obtain ⟨point''⟩ := site.inhabited stage''
      exact (each witness witnessMem).2 (forces_sound formula into _ forced point'')
  | _, .built _ arguments, _, _, into, _, _, holds, point => by
    obtain ⟨parts, _, builtAt, all⟩ := holds
    exact ⟨parts.map fun part => part point, builtAt point, forcesAll_sound arguments into parts all point⟩
  | _, .everyBuilt _ arguments, _, _, into, stage, _, holds, point => fun parts builtAt => by
    obtain ⟨point'⟩ := site.inhabited site.terminal
    have constant : (parts.map fun value (_ : site.Point site.terminal) => value).map (fun part => part point') = parts := by
      rw [List.map_map]
      exact List.map_id' parts
    have forced := holds site.terminal _ (site.global stage point) (parts.map fun value _ => value)
      (fun part partMem => by
        obtain ⟨value, _, rfl⟩ := List.mem_map.mp partMem
        exact site.const_mem _ value)
      (fun point'' => by
        rw [List.map_map]
        simpa only [Function.comp_def, List.map_id'] using builtAt)
    have := forcesSome_sound arguments into _ forced point'
    rwa [constant] at this
  | _, .split _ left right, _, _, into, _, _, holds, point => by
    obtain ⟨first, _, second, _, splits, leftHolds, rightHolds⟩ := holds
    exact ⟨first point, second point, splits point, forces_sound left into first leftHolds point,
      forces_sound right into second rightHolds point⟩
  | _, .everySplit _ left right, _, _, into, stage, _, holds, point => fun first second splits => by
    obtain ⟨point'⟩ := site.inhabited site.terminal
    exact (holds site.terminal _ (site.global stage point) _ (site.const_mem _ first) _ (site.const_mem _ second)
      fun _ => splits).elim (fun holds => .inl (forces_sound left into _ holds point'))
        (fun holds => .inr (forces_sound right into _ holds point'))
  | _, .empty _, _, _, _, _, _, holds, point => holds point
  | _, .nonEmpty _, _, _, _, stage, _, holds, point => fun empty =>
    holds site.terminal _ (site.global stage point) fun _ => empty
  | _, .single _ formula, _, _, into, _, _, holds, point => by
    obtain ⟨member, _, singles, memberHolds⟩ := holds
    exact ⟨member point, singles point, forces_sound formula into member memberHolds point⟩
  | _, .everySingle _ formula, _, _, into, stage, _, holds, point => fun member single => by
    obtain ⟨point'⟩ := site.inhabited site.terminal
    exact forces_sound formula into _ (holds site.terminal _ (site.global stage point) _ (site.const_mem _ member)
      fun _ => single) point'
  | _, .body formula, _, _, into, _, _, holds, point => by
    obtain ⟨inner, _, bodies, innerHolds⟩ := holds
    exact ⟨inner point, bodies point, forces_sound formula into inner innerHolds point⟩
  | _, .everyBody formula, _, _, into, stage, _, holds, point => fun inner isBody => by
    obtain ⟨point'⟩ := site.inhabited site.terminal
    exact forces_sound formula into _ (holds site.terminal _ (site.global stage point) _ (site.const_mem _ inner)
      fun _ => isBody) point'
  | _, .multiBody _ formula, _, _, into, _, _, holds, point => by
    obtain ⟨inner, _, bodies, innerHolds⟩ := holds
    exact ⟨inner point, bodies point, forces_sound formula into inner innerHolds point⟩
  | _, .everyMultiBody _ formula, _, _, into, stage, _, holds, point => fun inner isBody => by
    obtain ⟨point'⟩ := site.inhabited site.terminal
    exact forces_sound formula into _ (holds site.terminal _ (site.global stage point) _ (site.const_mem _ inner)
      fun _ => isBody) point'
  | _, .bound _, _, _, _, _, _, holds, point => holds point
  | _, .notBound _, _, _, _, stage, _, holds, point => fun bound =>
    holds site.terminal _ (site.global stage point) fun _ => bound
  | _, .typed _, _, _, _, _, _, holds, point => holds point
  | _, .untyped _, _, _, _, stage, _, holds, point => fun typedAt =>
    holds site.terminal _ (site.global stage point) fun _ => typedAt
  | _, .is _, _, _, _, _, _, holds, point => holds point
  | _, .isNot _, _, _, _, stage, _, holds, point => fun named =>
    holds site.terminal _ (site.global stage point) fun _ => named
  | _, .mapsAll argument result, _, _, into, stage, _, holds, point => by
    obtain ⟨inner, _, bodies, all⟩ := holds
    obtain ⟨point'⟩ := site.inhabited site.terminal
    exact ⟨inner point, bodies point, fun value =>
      (all site.terminal _ (site.global stage point) _ (site.const_mem _ value)).elim
        (fun holds => .inl (forces_sound argument into _ holds point'))
        (fun holds => .inr (forces_sound result into _ holds point'))⟩
  | _, .mapsSome argument result, _, _, into, stage, _, holds, point => fun inner isBody => by
    obtain ⟨value, _, argumentHolds, resultHolds⟩ :=
      holds site.terminal _ (site.global stage point) _ (site.const_mem _ inner) fun _ => isBody
    obtain ⟨point'⟩ := site.inhabited site.terminal
    exact ⟨value point', forces_sound argument into value argumentHolds point',
      forces_sound result into _ resultHolds point'⟩
  | _, .someOf _ formula, _, _, into, _, _, holds, point => by
    obtain ⟨witness, _, typedAt, witnessHolds⟩ := holds
    exact ⟨witness point, typedAt point, forces_sound formula into witness witnessHolds point⟩
  | _, .everyOf _ formula, _, _, into, stage, _, holds, point => fun witness typedAt => by
    obtain ⟨point'⟩ := site.inhabited site.terminal
    exact forces_sound formula into _ (holds site.terminal _ (site.global stage point) _ (site.const_mem _ witness)
      fun _ => typedAt) point'
  | _, .inRelation _, _, _, _, _, _, holds, point => holds point
  | _, .notInRelation _, _, _, _, stage, _, holds, point => fun inRelation =>
    holds site.terminal _ (site.global stage point) fun _ => inRelation

theorem forcesAll_sound : ∀ {n : ℕ} (formulas : Formulas n) {env : Fin n → site.Sets} {classical : Env Carrier n},
    site.Into env classical → ∀ {stage : site.Stage} (parts : List (site.Family stage)),
      S.forcesAll site env stage formulas parts → ∀ point, S.satAll classical formulas (parts.map fun part => part point)
  | _, .nil, _, _, _, _, [], _, _ => trivial
  | _, .cons formula formulas, _, _, into, _, part :: parts, holds, point =>
    ⟨forces_sound formula into part holds.1 point, forcesAll_sound formulas into parts holds.2 point⟩
  | _, .nil, _, _, _, _, _ :: _, holds, _ => holds.elim
  | _, .cons _ _, _, _, _, _, [], holds, _ => holds.elim

theorem forcesSome_sound : ∀ {n : ℕ} (formulas : Formulas n) {env : Fin n → site.Sets} {classical : Env Carrier n},
    site.Into env classical → ∀ {stage : site.Stage} (parts : List (site.Family stage)),
      S.forcesSome site env stage formulas parts → ∀ point, S.satSome classical formulas (parts.map fun part => part point)
  | _, .nil, _, _, _, _, [], holds, _ => holds.elim
  | _, .cons formula formulas, _, _, into, _, part :: parts, holds, point =>
    holds.elim (fun holds => .inl (forces_sound formula into part holds point))
      (fun holds => .inr (forcesSome_sound formulas into parts holds point))
  | _, .nil, _, _, _, _, _ :: _, _, _ => trivial
  | _, .cons _ _, _, _, _, _, [], _, _ => trivial
end

end NativeStructure

/-! ## The negative fragment -/

mutual
/-- **Negative formulas**: atoms and negated atoms, truth, falsity, conjunction, variables, greatest fixed points, and
universal formers over negative formulas, with at most one argument for constructors. -/
def Formula.negative : {n : ℕ} → Formula n → Bool
  | _, .top => true
  | _, .bot => true
  | _, .and left right => left.negative && right.negative
  | _, .or _ _ => false
  | _, .var _ => true
  | _, .mu _ => false
  | _, .nu inner => inner.negative
  | _, .possibly _ _ => false
  | _, .necessarily _ formula => formula.negative
  | _, .sometimeBefore _ _ => false
  | _, .alwaysBefore _ formula => formula.negative
  | _, .atLeast _ _ _ _ => false
  | _, .allButFewer _ _ _ formula => formula.negative
  | _, .built _ _ => false
  | _, .everyBuilt _ arguments => Formulas.negativeShort arguments
  | _, .split _ _ _ => false
  | _, .everySplit _ _ _ => false
  | _, .empty _ => true
  | _, .nonEmpty _ => true
  | _, .single _ _ => false
  | _, .everySingle _ formula => formula.negative
  | _, .body _ => false
  | _, .everyBody formula => formula.negative
  | _, .multiBody _ _ => false
  | _, .everyMultiBody _ formula => formula.negative
  | _, .bound _ => true
  | _, .notBound _ => true
  | _, .typed _ => true
  | _, .untyped _ => true
  | _, .is _ => true
  | _, .isNot _ => true
  | _, .mapsAll _ _ => false
  | _, .mapsSome _ _ => false
  | _, .someOf _ _ => false
  | _, .everyOf _ formula => formula.negative
  | _, .inRelation _ => true
  | _, .notInRelation _ => true

/-- At most one formula, negative. -/
def Formulas.negativeShort : {n : ℕ} → Formulas n → Bool
  | _, .nil => true
  | _, .cons formula .nil => formula.negative
  | _, .cons _ (.cons _ _) => false
end

namespace NativeStructure

variable {Carrier : Type u} (S : NativeStructure Carrier) (site : Site Carrier)

/-- A classical greatest fixed point is kept by its body. -/
theorem sat_nu_kept {n : ℕ} (inner : Formula (n + 1)) (classical : Env Carrier n) (value : Carrier)
    (holds : S.sat classical (.nu inner) value) :
    S.sat (classical.extend {other | S.sat classical (.nu inner) other}) inner value := by
  obtain ⟨invariant, member, preserved⟩ := holds
  refine S.sat_mono inner (fun index => ?_) value (preserved value member)
  refine Fin.cases ?_ (fun index' => ?_) index
  · simp only [Env.extend, Fin.cons_zero]
    exact fun other inside => ⟨invariant, inside, preserved⟩
  · simp only [Env.extend, Fin.cons_succ]
    exact fun _ inside => inside

mutual
/-- **On negative formulas, the classical judgment forces.** -/
theorem forces_of_negative : ∀ {n : ℕ} (formula : Formula n), formula.negative = true →
    ∀ {env : Fin n → site.Sets} {classical : Env Carrier n}, site.Onto env classical →
      ∀ {stage : site.Stage} (element : site.Family stage), S.holdsAt site classical formula element →
        S.forces site env stage formula element
  | _, .top, _, _, _, _, _, _, _ => trivial
  | _, .bot, _, _, _, _, stage, _, holds => by
    obtain ⟨point⟩ := site.inhabited stage
    exact holds point
  | _, .and left right, negative, _, _, onto, _, element, holds => by
    simp only [Formula.negative, Bool.and_eq_true] at negative
    exact ⟨forces_of_negative left negative.1 onto element fun point => (holds point).1,
      forces_of_negative right negative.2 onto element fun point => (holds point).2⟩
  | _, .var index, _, _, _, onto, stage, element, holds => onto index stage element holds
  | _, .nu inner, negative, env, classical, onto, stage, element, holds => by
    simp only [Formula.negative] at negative
    let greatest : Set Carrier := {other | S.sat classical (.nu inner) other}
    refine ⟨site.lift greatest, site.lift_stable greatest, holds, fun stage' other inside => ?_⟩
    exact forces_of_negative inner negative (onto.extend fun _ _ everywhere => everywhere) other
      fun point => S.sat_nu_kept inner classical _ (inside point)
  | _, .necessarily _ formula, negative, _, _, onto, _, _, holds => fun _ arrow _ next _ steps => by
    simp only [Formula.negative] at negative
    exact forces_of_negative formula negative onto next fun point => holds (arrow point) _ (steps point)
  | _, .alwaysBefore _ formula, negative, _, _, onto, _, _, holds => fun _ arrow _ previous _ steps => by
    simp only [Formula.negative] at negative
    exact forces_of_negative formula negative onto previous fun point => holds (arrow point) _ (steps point)
  | _, .allButFewer _ _ _ formula, negative, _, _, onto, _, _, holds => by
    simp only [Formula.negative] at negative
    rintro stage' arrow _ ⟨witnesses, length, _, apart, each⟩
    obtain ⟨point⟩ := site.inhabited stage'
    refine holds (arrow point) ⟨witnesses.map fun witness => witness point, by rw [List.length_map, length],
      List.pairwise_map.mpr (apart.imp fun distinct => distinct point), ?_⟩
    intro value valueMem
    obtain ⟨witness, witnessMem, rfl⟩ := List.mem_map.mp valueMem
    refine ⟨(each witness witnessMem).1 point, fun holdsThere => ?_⟩
    refine (each witness witnessMem).2 site.terminal _ (site.global stage' point)
      (forces_of_negative formula negative onto _ fun _ => holdsThere)
  | _, .everyBuilt _ arguments, negative, _, _, onto, _, _, holds => fun _ arrow _ parts _ builtAt => by
    simp only [Formula.negative] at negative
    exact forcesSome_of_negativeShort arguments negative onto parts fun point => holds (arrow point) _ (builtAt point)
  | _, .empty _, _, _, _, _, _, _, holds => holds
  | _, .nonEmpty _, _, _, _, _, _, _, holds => fun stage' arrow _ everywhere => by
    obtain ⟨point⟩ := site.inhabited stage'
    exact holds (arrow point) (everywhere point)
  | _, .everySingle _ formula, negative, _, _, onto, _, _, holds => fun _ arrow _ member _ singles => by
    simp only [Formula.negative] at negative
    exact forces_of_negative formula negative onto member fun point => holds (arrow point) _ (singles point)
  | _, .everyBody formula, negative, _, _, onto, _, _, holds => fun _ arrow _ inner _ bodies => by
    simp only [Formula.negative] at negative
    exact forces_of_negative formula negative onto inner fun point => holds (arrow point) _ (bodies point)
  | _, .everyMultiBody _ formula, negative, _, _, onto, _, _, holds => fun _ arrow _ inner _ bodies => by
    simp only [Formula.negative] at negative
    exact forces_of_negative formula negative onto inner fun point => holds (arrow point) _ (bodies point)
  | _, .bound _, _, _, _, _, _, _, holds => holds
  | _, .notBound _, _, _, _, _, _, _, holds => fun stage' arrow _ everywhere => by
    obtain ⟨point⟩ := site.inhabited stage'
    exact holds (arrow point) (everywhere point)
  | _, .typed _, _, _, _, _, _, _, holds => holds
  | _, .untyped _, _, _, _, _, _, _, holds => fun stage' arrow _ everywhere => by
    obtain ⟨point⟩ := site.inhabited stage'
    exact holds (arrow point) (everywhere point)
  | _, .is _, _, _, _, _, _, _, holds => holds
  | _, .isNot _, _, _, _, _, _, _, holds => fun stage' arrow _ everywhere => by
    obtain ⟨point⟩ := site.inhabited stage'
    exact holds (arrow point) (everywhere point)
  | _, .everyOf _ formula, negative, _, _, onto, stage, _, holds => fun _ _ _ witness _ typedAt => by
    simp only [Formula.negative] at negative
    obtain ⟨point⟩ := site.inhabited stage
    exact forces_of_negative formula negative onto witness fun point' => holds point _ (typedAt point')
  | _, .inRelation _, _, _, _, _, _, _, holds => holds
  | _, .notInRelation _, _, _, _, _, _, _, holds => fun stage' arrow _ everywhere => by
    obtain ⟨point⟩ := site.inhabited stage'
    exact holds (arrow point) (everywhere point)
  | _, .or _ _, negative, _, _, _, _, _, _ => by simp [Formula.negative] at negative
  | _, .mu _, negative, _, _, _, _, _, _ => by simp [Formula.negative] at negative
  | _, .possibly _ _, negative, _, _, _, _, _, _ => by simp [Formula.negative] at negative
  | _, .sometimeBefore _ _, negative, _, _, _, _, _, _ => by simp [Formula.negative] at negative
  | _, .atLeast _ _ _ _, negative, _, _, _, _, _, _ => by simp [Formula.negative] at negative
  | _, .built _ _, negative, _, _, _, _, _, _ => by simp [Formula.negative] at negative
  | _, .split _ _ _, negative, _, _, _, _, _, _ => by simp [Formula.negative] at negative
  | _, .everySplit _ _ _, negative, _, _, _, _, _, _ => by simp [Formula.negative] at negative
  | _, .single _ _, negative, _, _, _, _, _, _ => by simp [Formula.negative] at negative
  | _, .body _, negative, _, _, _, _, _, _ => by simp [Formula.negative] at negative
  | _, .multiBody _ _, negative, _, _, _, _, _, _ => by simp [Formula.negative] at negative
  | _, .mapsAll _ _, negative, _, _, _, _, _, _ => by simp [Formula.negative] at negative
  | _, .mapsSome _ _, negative, _, _, _, _, _, _ => by simp [Formula.negative] at negative
  | _, .someOf _ _, negative, _, _, _, _, _, _ => by simp [Formula.negative] at negative

theorem forcesSome_of_negativeShort : ∀ {n : ℕ} (formulas : Formulas n), formulas.negativeShort = true →
    ∀ {env : Fin n → site.Sets} {classical : Env Carrier n}, site.Onto env classical →
      ∀ {stage : site.Stage} (parts : List (site.Family stage)),
        (∀ point, S.satSome classical formulas (parts.map fun part => part point)) →
          S.forcesSome site env stage formulas parts
  | _, .nil, _, _, _, _, stage, [], holds => by
    obtain ⟨point⟩ := site.inhabited stage
    exact holds point
  | _, .nil, _, _, _, _, _, _ :: _, _ => trivial
  | _, .cons _ .nil, _, _, _, _, _, [], _ => trivial
  | _, .cons formula .nil, negative, _, _, onto, _, [part], holds => .inl <| by
    simp only [Formulas.negativeShort] at negative
    exact forces_of_negative formula negative onto part fun point => (holds point).elim id fun impossible => impossible.elim
  | _, .cons _ .nil, _, _, _, _, _, _ :: _ :: _, _ => .inr trivial
  | _, .cons _ (.cons _ _), negative, _, _, _, _, _, _ => by simp [Formulas.negativeShort] at negative
end

/-- **Agreement on the negative fragment**: forcing is the classical judgment over valuations, at every stage. -/
theorem forces_iff_of_negative {n : ℕ} {formula : Formula n} (negative : formula.negative = true)
    (classical : Env Carrier n) {stage : site.Stage} (element : site.Family stage) :
    S.forces site (fun index => site.lift (classical index)) stage formula element ↔
      S.holdsAt site classical formula element :=
  ⟨S.forces_sound site formula (fun _ _ _ inside => inside) element,
    S.forces_of_negative site formula negative (fun _ _ _ everywhere => everywhere) element⟩

end NativeStructure

/-! ## The closed stage -/

mutual
/-- **Settled formulas**: existential formers, conjunction and disjunction over negative formulas. -/
def Formula.settled : {n : ℕ} → Formula n → Bool
  | _, .and left right => left.settled && right.settled
  | _, .or left right => left.settled && right.settled
  | _, .possibly _ formula => formula.settled
  | _, .sometimeBefore _ formula => formula.settled
  | _, .atLeast _ _ _ formula => formula.settled
  | _, .built _ arguments => Formulas.settled arguments
  | _, .split _ left right => left.settled && right.settled
  | _, .single _ formula => formula.settled
  | _, .body formula => formula.settled
  | _, .multiBody _ formula => formula.settled
  | _, .someOf _ formula => formula.settled
  | _, formula => formula.negative

/-- Every formula of the list is settled. -/
def Formulas.settled : {n : ℕ} → Formulas n → Bool
  | _, .nil => true
  | _, .cons formula formulas => formula.settled && Formulas.settled formulas
end

namespace NativeStructure

variable {Carrier : Type u} (S : NativeStructure Carrier) (site : Site Carrier)

/-- A family at the terminal stage forces a negative formula exactly when its value satisfies it. -/
theorem forces_terminal_iff_of_negative {n : ℕ} {formula : Formula n} (negative : formula.negative = true)
    (classical : Env Carrier n) (value : Carrier) :
    S.forces site (fun index => site.lift (classical index)) site.terminal formula (fun _ => value) ↔
      S.sat classical formula value := by
  rw [S.forces_iff_of_negative site negative classical]
  obtain ⟨point⟩ := site.inhabited site.terminal
  exact ⟨fun holds => holds point, fun holds _ => holds⟩

mutual
/-- **Agreement at the closed stage**: a settled formula is forced at the terminal stage by a constant family exactly
when it holds, classically, at the value. -/
theorem forces_terminal_iff : ∀ {n : ℕ} (formula : Formula n), formula.settled = true → ∀ (classical : Env Carrier n)
    (value : Carrier), S.forces site (fun index => site.lift (classical index)) site.terminal formula (fun _ => value) ↔
      S.sat classical formula value
  | _, .and left right, settled, classical, value => by
    simp only [Formula.settled, Bool.and_eq_true] at settled
    exact and_congr (forces_terminal_iff left settled.1 classical value) (forces_terminal_iff right settled.2 classical value)
  | _, .or left right, settled, classical, value => by
    simp only [Formula.settled, Bool.and_eq_true] at settled
    exact or_congr (forces_terminal_iff left settled.1 classical value) (forces_terminal_iff right settled.2 classical value)
  | _, .possibly label formula, settled, classical, value => by
    simp only [Formula.settled] at settled
    obtain ⟨point⟩ := site.inhabited site.terminal
    constructor
    · rintro ⟨next, _, steps, holds⟩
      rw [site.terminal_const next point] at holds
      exact ⟨next point, steps point, (forces_terminal_iff formula settled classical _).mp holds⟩
    · rintro ⟨next, step, holds⟩
      exact ⟨fun _ => next, site.const_mem _ next, fun _ => step, (forces_terminal_iff formula settled classical _).mpr holds⟩
  | _, .sometimeBefore label formula, settled, classical, value => by
    simp only [Formula.settled] at settled
    obtain ⟨point⟩ := site.inhabited site.terminal
    constructor
    · rintro ⟨previous, _, steps, holds⟩
      rw [site.terminal_const previous point] at holds
      exact ⟨previous point, steps point, (forces_terminal_iff formula settled classical _).mp holds⟩
    · rintro ⟨previous, step, holds⟩
      exact ⟨fun _ => previous, site.const_mem _ previous, fun _ => step,
        (forces_terminal_iff formula settled classical _).mpr holds⟩
  | _, .atLeast count direction label formula, settled, classical, value => by
    simp only [Formula.settled] at settled
    obtain ⟨point⟩ := site.inhabited site.terminal
    constructor
    · rintro ⟨witnesses, length, _, apart, each⟩
      refine ⟨witnesses.map fun witness => witness point, by rw [List.length_map, length],
        List.pairwise_map.mpr (apart.imp fun distinct => distinct point), ?_⟩
      intro other otherMem
      obtain ⟨witness, witnessMem, rfl⟩ := List.mem_map.mp otherMem
      have holds := (each witness witnessMem).2
      rw [site.terminal_const witness point] at holds
      exact ⟨(each witness witnessMem).1 point, (forces_terminal_iff formula settled classical _).mp holds⟩
    · rintro ⟨witnesses, length, apart, each⟩
      refine ⟨witnesses.map fun witness _ => witness, by rw [List.length_map, length], ?_,
        List.pairwise_map.mpr (apart.imp fun distinct _ => distinct), ?_⟩
      · intro constant constantMem
        obtain ⟨witness, _, rfl⟩ := List.mem_map.mp constantMem
        exact site.const_mem _ witness
      · intro constant constantMem
        obtain ⟨witness, witnessMem, rfl⟩ := List.mem_map.mp constantMem
        exact ⟨fun _ => (each witness witnessMem).1,
          (forces_terminal_iff formula settled classical _).mpr (each witness witnessMem).2⟩
  | _, .built constructor arguments, settled, classical, value => by
    simp only [Formula.settled] at settled
    obtain ⟨point⟩ := site.inhabited site.terminal
    constructor
    · rintro ⟨parts, _, builtAt, all⟩
      have constant : parts = (parts.map fun part => part point).map fun value _ => value := by
        rw [List.map_map]
        conv_lhs => rw [← List.map_id' parts]
        exact List.map_congr_left fun part _ => site.terminal_const part point
      rw [constant] at all
      exact ⟨parts.map fun part => part point, builtAt point,
        (forcesAll_terminal_iff arguments settled classical _).mp all⟩
    · rintro ⟨parts, builtAt, all⟩
      refine ⟨parts.map fun value _ => value, fun part partMem => ?_, fun _ => ?_,
        (forcesAll_terminal_iff arguments settled classical parts).mpr all⟩
      · obtain ⟨value, _, rfl⟩ := List.mem_map.mp partMem
        exact site.const_mem _ value
      · rw [List.map_map]
        simpa only [Function.comp_def, List.map_id'] using builtAt
  | _, .split kind left right, settled, classical, value => by
    simp only [Formula.settled, Bool.and_eq_true] at settled
    obtain ⟨point⟩ := site.inhabited site.terminal
    constructor
    · rintro ⟨first, _, second, _, splits, leftHolds, rightHolds⟩
      rw [site.terminal_const first point] at leftHolds
      rw [site.terminal_const second point] at rightHolds
      exact ⟨first point, second point, splits point, (forces_terminal_iff left settled.1 classical _).mp leftHolds,
        (forces_terminal_iff right settled.2 classical _).mp rightHolds⟩
    · rintro ⟨first, second, splits, leftHolds, rightHolds⟩
      exact ⟨fun _ => first, site.const_mem _ first, fun _ => second, site.const_mem _ second, fun _ => splits,
        (forces_terminal_iff left settled.1 classical _).mpr leftHolds,
        (forces_terminal_iff right settled.2 classical _).mpr rightHolds⟩
  | _, .single kind formula, settled, classical, value => by
    simp only [Formula.settled] at settled
    obtain ⟨point⟩ := site.inhabited site.terminal
    constructor
    · rintro ⟨member, _, singles, holds⟩
      rw [site.terminal_const member point] at holds
      exact ⟨member point, singles point, (forces_terminal_iff formula settled classical _).mp holds⟩
    · rintro ⟨member, single, holds⟩
      exact ⟨fun _ => member, site.const_mem _ member, fun _ => single,
        (forces_terminal_iff formula settled classical _).mpr holds⟩
  | _, .body formula, settled, classical, value => by
    simp only [Formula.settled] at settled
    obtain ⟨point⟩ := site.inhabited site.terminal
    constructor
    · rintro ⟨inner, _, bodies, holds⟩
      rw [site.terminal_const inner point] at holds
      exact ⟨inner point, bodies point, (forces_terminal_iff formula settled classical _).mp holds⟩
    · rintro ⟨inner, isBody, holds⟩
      exact ⟨fun _ => inner, site.const_mem _ inner, fun _ => isBody,
        (forces_terminal_iff formula settled classical _).mpr holds⟩
  | _, .multiBody arity formula, settled, classical, value => by
    simp only [Formula.settled] at settled
    obtain ⟨point⟩ := site.inhabited site.terminal
    constructor
    · rintro ⟨inner, _, bodies, holds⟩
      rw [site.terminal_const inner point] at holds
      exact ⟨inner point, bodies point, (forces_terminal_iff formula settled classical _).mp holds⟩
    · rintro ⟨inner, isBody, holds⟩
      exact ⟨fun _ => inner, site.const_mem _ inner, fun _ => isBody,
        (forces_terminal_iff formula settled classical _).mpr holds⟩
  | _, .someOf type formula, settled, classical, value => by
    simp only [Formula.settled] at settled
    obtain ⟨point⟩ := site.inhabited site.terminal
    constructor
    · rintro ⟨witness, _, typedAt, holds⟩
      rw [site.terminal_const witness point] at holds
      exact ⟨witness point, typedAt point, (forces_terminal_iff formula settled classical _).mp holds⟩
    · rintro ⟨witness, typedAt, holds⟩
      exact ⟨fun _ => witness, site.const_mem _ witness, fun _ => typedAt,
        (forces_terminal_iff formula settled classical _).mpr holds⟩
  | _, .top, settled, classical, value => S.forces_terminal_iff_of_negative site settled classical value
  | _, .bot, settled, classical, value => S.forces_terminal_iff_of_negative site settled classical value
  | _, .var _, settled, classical, value => S.forces_terminal_iff_of_negative site settled classical value
  | _, .mu _, settled, classical, value => S.forces_terminal_iff_of_negative site settled classical value
  | _, .nu _, settled, classical, value => S.forces_terminal_iff_of_negative site settled classical value
  | _, .necessarily _ _, settled, classical, value => S.forces_terminal_iff_of_negative site settled classical value
  | _, .alwaysBefore _ _, settled, classical, value => S.forces_terminal_iff_of_negative site settled classical value
  | _, .allButFewer _ _ _ _, settled, classical, value => S.forces_terminal_iff_of_negative site settled classical value
  | _, .everyBuilt _ _, settled, classical, value => S.forces_terminal_iff_of_negative site settled classical value
  | _, .everySplit _ _ _, settled, classical, value => S.forces_terminal_iff_of_negative site settled classical value
  | _, .empty _, settled, classical, value => S.forces_terminal_iff_of_negative site settled classical value
  | _, .nonEmpty _, settled, classical, value => S.forces_terminal_iff_of_negative site settled classical value
  | _, .everySingle _ _, settled, classical, value => S.forces_terminal_iff_of_negative site settled classical value
  | _, .everyBody _, settled, classical, value => S.forces_terminal_iff_of_negative site settled classical value
  | _, .everyMultiBody _ _, settled, classical, value => S.forces_terminal_iff_of_negative site settled classical value
  | _, .bound _, settled, classical, value => S.forces_terminal_iff_of_negative site settled classical value
  | _, .notBound _, settled, classical, value => S.forces_terminal_iff_of_negative site settled classical value
  | _, .typed _, settled, classical, value => S.forces_terminal_iff_of_negative site settled classical value
  | _, .untyped _, settled, classical, value => S.forces_terminal_iff_of_negative site settled classical value
  | _, .is _, settled, classical, value => S.forces_terminal_iff_of_negative site settled classical value
  | _, .isNot _, settled, classical, value => S.forces_terminal_iff_of_negative site settled classical value
  | _, .mapsAll _ _, settled, classical, value => S.forces_terminal_iff_of_negative site settled classical value
  | _, .mapsSome _ _, settled, classical, value => S.forces_terminal_iff_of_negative site settled classical value
  | _, .everyOf _ _, settled, classical, value => S.forces_terminal_iff_of_negative site settled classical value
  | _, .inRelation _, settled, classical, value => S.forces_terminal_iff_of_negative site settled classical value
  | _, .notInRelation _, settled, classical, value => S.forces_terminal_iff_of_negative site settled classical value

theorem forcesAll_terminal_iff : ∀ {n : ℕ} (formulas : Formulas n), formulas.settled = true →
    ∀ (classical : Env Carrier n) (values : List Carrier),
      S.forcesAll site (fun index => site.lift (classical index)) site.terminal formulas
        (values.map fun value _ => value) ↔ S.satAll classical formulas values
  | _, .nil, _, _, [] => Iff.rfl
  | _, .nil, _, _, _ :: _ => Iff.rfl
  | _, .cons _ _, _, _, [] => Iff.rfl
  | _, .cons formula formulas, settled, classical, value :: values => by
    simp only [Formulas.settled, Bool.and_eq_true] at settled
    exact and_congr (forces_terminal_iff formula settled.1 classical value)
      (forcesAll_terminal_iff formulas settled.2 classical values)
end

end NativeStructure

namespace NativeStructure

variable {Carrier : Type} (S : NativeStructure Carrier) (site : Site Carrier)

/-- **Agreement with higher-order logic at the closed stage**: a closed settled formula is forced at the terminal
stage by a constant family exactly when its translation to higher-order logic holds at the value in the standard
model. -/
theorem forces_terminal_iff_denote {formula : Formula 0} (settled : formula.settled = true) (value : Carrier) :
    S.forces site (fun index => index.elim0) site.terminal formula (fun _ => value) ↔
      ((HigherOrder.standardModel S).denote (HigherOrder.translate formula)
        (Mettapedia.OSLF.Framework.NativeBasis.nowhere (HigherOrder.presentation S)) (ULift.up value)).down := by
  have env : (fun index : Fin 0 => index.elim0 : Fin 0 → site.Sets) = fun index => site.lift (Env.closed index) :=
    funext fun index => index.elim0
  rw [env, S.forces_terminal_iff site formula settled, HigherOrder.denote_translate_closed]

end NativeStructure

end Mettapedia.OSLF.NativeTypes.GeneratedLogic
