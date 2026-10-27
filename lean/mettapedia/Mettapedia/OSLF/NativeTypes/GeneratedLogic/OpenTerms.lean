import Mettapedia.OSLF.NativeTypes.GeneratedLogic.PresheafReading

/-!
# Open terms: contexts, valuations and the judgment `Γ ⊢ t : φ`

Open terms have named free variables, declared with their types in a context; binders stay de Bruijn indices, so
substituting closed terms for free variables captures nothing.

- **Substitution for free variables** (`freeSubst`): identity (`freeSubst_fvar`), composition (`freeSubst_comp`), and
  dependence on the free variables only (`freeSubst_congr`), which are those a list of names covers (`freeWithin`).
- **Valuations** (`Valuation`): a closed value of each variable's type, every other name left as it is.
- **Substitutions between contexts** (`Substitution`): images of the target's variables, free in the source, whose
  instances under every valuation of the source form a valuation of the target.
- **The site of contexts** (`contextSite`): the stages are the inhabited contexts, their points the valuations, their
  elements the instances of open terms and the constant families, and the arrows the maps of valuations that
  substitutions induce. The empty context is terminal.
- **The open judgment** (`OpenHolds`): `Γ ⊢ t : φ` when the formula holds at every instance of the term under a
  valuation of the context. It is the classical judgment over valuations at the term's family (`openHolds_iff`), it is
  **closed under substitution** (`openHolds_subst`), and it is reached one variable at a time (`openHolds_cons`).
- **Forcing at a context** (`ForcesOpen`): the presheaf reading of the open judgment, sound for it (`openHolds_of_forces`)
  and equal to it on negative formulas (`forcesOpen_iff_of_negative`).
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.GeneratedLogic

open Mettapedia.OSLF.MeTTaIL.Syntax

/-! ## Substitution for free variables -/

mutual
/-- **Substitution for free variables**: each free variable becomes the term the assignment gives it. -/
def freeSubst (assignment : String → Pattern) : Pattern → Pattern
  | .bvar index => .bvar index
  | .fvar name => assignment name
  | .apply constructor arguments => .apply constructor (freeSubstList assignment arguments)
  | .lambda name body => .lambda name (freeSubst assignment body)
  | .multiLambda arity names body => .multiLambda arity names (freeSubst assignment body)
  | .subst body replacement => .subst (freeSubst assignment body) (freeSubst assignment replacement)
  | .collection kind elements rest => .collection kind (freeSubstList assignment elements) rest

/-- Substitution along a list. -/
def freeSubstList (assignment : String → Pattern) : List Pattern → List Pattern
  | [] => []
  | pattern :: patterns => freeSubst assignment pattern :: freeSubstList assignment patterns
end

@[simp] theorem freeSubstList_eq_map (assignment : String → Pattern) :
    ∀ patterns, freeSubstList assignment patterns = patterns.map (freeSubst assignment)
  | [] => rfl
  | pattern :: patterns => by
    simp only [freeSubstList, List.map_cons, freeSubstList_eq_map assignment patterns]

/-- **Substituting each variable for itself changes nothing.** -/
@[simp] theorem freeSubst_fvar (pattern : Pattern) : freeSubst Pattern.fvar pattern = pattern := by
  induction pattern using Pattern.inductionOn with
  | hbvar _ => rfl
  | hfvar _ => rfl
  | happly constructor arguments ih =>
    simp only [freeSubst, freeSubstList_eq_map]
    exact congrArg (Pattern.apply constructor) ((List.map_congr_left ih).trans (List.map_id' arguments))
  | hlambda name body ih => simp only [freeSubst, ih]
  | hmultiLambda arity names body ih => simp only [freeSubst, ih]
  | hsubst body replacement ihBody ihReplacement => simp only [freeSubst, ihBody, ihReplacement]
  | hcollection kind elements rest ih =>
    simp only [freeSubst, freeSubstList_eq_map]
    exact congrArg (fun elements => Pattern.collection kind elements rest)
      ((List.map_congr_left ih).trans (List.map_id' elements))

/-- **Substitutions compose** by substituting into the images. -/
theorem freeSubst_comp (first second : String → Pattern) (pattern : Pattern) :
    freeSubst second (freeSubst first pattern) = freeSubst (fun name => freeSubst second (first name)) pattern := by
  induction pattern using Pattern.inductionOn with
  | hbvar _ => rfl
  | hfvar _ => rfl
  | happly constructor arguments ih =>
    simp only [freeSubst, freeSubstList_eq_map, List.map_map]
    exact congrArg (Pattern.apply constructor) (List.map_congr_left ih)
  | hlambda name body ih => simp only [freeSubst, ih]
  | hmultiLambda arity names body ih => simp only [freeSubst, ih]
  | hsubst body replacement ihBody ihReplacement => simp only [freeSubst, ihBody, ihReplacement]
  | hcollection kind elements rest ih =>
    simp only [freeSubst, freeSubstList_eq_map, List.map_map]
    exact congrArg (fun elements => Pattern.collection kind elements rest) (List.map_congr_left ih)

mutual
/-- **Every free variable of the pattern is among the names.** -/
def freeWithin (names : List String) : Pattern → Bool
  | .bvar _ => true
  | .fvar name => decide (name ∈ names)
  | .apply _ arguments => freeWithinList names arguments
  | .lambda _ body => freeWithin names body
  | .multiLambda _ _ body => freeWithin names body
  | .subst body replacement => freeWithin names body && freeWithin names replacement
  | .collection _ elements _ => freeWithinList names elements

/-- Every free variable along the list is among the names. -/
def freeWithinList (names : List String) : List Pattern → Bool
  | [] => true
  | pattern :: patterns => freeWithin names pattern && freeWithinList names patterns
end

theorem freeWithinList_iff (names : List String) :
    ∀ patterns, freeWithinList names patterns = true ↔ ∀ pattern ∈ patterns, freeWithin names pattern = true
  | [] => by simp [freeWithinList]
  | pattern :: patterns => by
    simp only [freeWithinList, Bool.and_eq_true, freeWithinList_iff names patterns, List.mem_cons, forall_eq_or_imp]

/-- **Substitution depends only on the free variables.** -/
theorem freeSubst_congr {names : List String} {first second : String → Pattern} (agree : ∀ name ∈ names, first name = second name) :
    ∀ {pattern : Pattern}, freeWithin names pattern = true → freeSubst first pattern = freeSubst second pattern := by
  intro pattern
  induction pattern using Pattern.inductionOn with
  | hbvar _ => intro _; rfl
  | hfvar name =>
    intro within
    exact agree name (of_decide_eq_true within)
  | happly constructor arguments ih =>
    intro within
    rw [freeWithin, freeWithinList_iff] at within
    simp only [freeSubst, freeSubstList_eq_map]
    exact congrArg (Pattern.apply constructor) (List.map_congr_left fun pattern member => ih pattern member (within pattern member))
  | hlambda name body ih =>
    intro within
    simp only [freeSubst, ih within]
  | hmultiLambda arity binders body ih =>
    intro within
    simp only [freeSubst, ih within]
  | hsubst body replacement ihBody ihReplacement =>
    intro within
    simp only [freeWithin, Bool.and_eq_true] at within
    simp only [freeSubst, ihBody within.1, ihReplacement within.2]
  | hcollection kind elements rest ih =>
    intro within
    rw [freeWithin, freeWithinList_iff] at within
    simp only [freeSubst, freeSubstList_eq_map]
    exact congrArg (fun elements => Pattern.collection kind elements rest)
      (List.map_congr_left fun pattern member => ih pattern member (within pattern member))

/-- **The free variables of an instance are those of the images.** -/
theorem freeWithin_freeSubst {names names' : List String} {assignment : String → Pattern}
    (images : ∀ name ∈ names, freeWithin names' (assignment name) = true) :
    ∀ {pattern : Pattern}, freeWithin names pattern = true → freeWithin names' (freeSubst assignment pattern) = true := by
  intro pattern
  induction pattern using Pattern.inductionOn with
  | hbvar _ => intro _; rfl
  | hfvar name =>
    intro within
    exact images name (of_decide_eq_true within)
  | happly constructor arguments ih =>
    intro within
    rw [freeWithin, freeWithinList_iff] at within
    simp only [freeSubst, freeSubstList_eq_map, freeWithin, freeWithinList_iff, List.mem_map]
    rintro _ ⟨pattern, member, rfl⟩
    exact ih pattern member (within pattern member)
  | hlambda name body ih =>
    intro within
    exact ih within
  | hmultiLambda arity binders body ih =>
    intro within
    exact ih within
  | hsubst body replacement ihBody ihReplacement =>
    intro within
    simp only [freeWithin, Bool.and_eq_true] at within
    simp only [freeSubst, freeWithin, Bool.and_eq_true]
    exact ⟨ihBody within.1, ihReplacement within.2⟩
  | hcollection kind elements rest ih =>
    intro within
    rw [freeWithin, freeWithinList_iff] at within
    simp only [freeSubst, freeSubstList_eq_map, freeWithin, freeWithinList_iff, List.mem_map]
    rintro _ ⟨pattern, member, rfl⟩
    exact ih pattern member (within pattern member)

/-- **A closed pattern is left as it is.** -/
theorem freeSubst_of_closed {pattern : Pattern} (closed : freeWithin [] pattern = true) (assignment : String → Pattern) :
    freeSubst assignment pattern = pattern :=
  (freeSubst_congr (names := []) (fun _ member => nomatch member) closed).trans (freeSubst_fvar pattern)

/-- More names cover more. -/
theorem freeWithin_mono {names names' : List String} (sub : ∀ name ∈ names, name ∈ names') {pattern : Pattern}
    (within : freeWithin names pattern = true) : freeWithin names' pattern = true := by
  have := freeWithin_freeSubst (assignment := Pattern.fvar) (names' := names')
    (fun name member => decide_eq_true (sub name member)) within
  rwa [freeSubst_fvar] at this

/-- Substitution of a value for one variable. -/
def single (name : String) (value : Pattern) : String → Pattern :=
  fun other => if other = name then value else .fvar other

/-! ## Contexts and valuations -/

/-- **A context**: variables with their types. -/
abbrev Context := List (String × TypeExpr)

/-- The variables of a context. -/
def Context.names (context : Context) : List String := context.map Prod.fst

theorem Context.mem_names {context : Context} {name : String} : name ∈ context.names ↔ ∃ type, (name, type) ∈ context := by
  simp [Context.names]

/-- The assignment that agrees on the context's variables and leaves every other name as it is. -/
def restrictTo (context : Context) (assignment : String → Pattern) : String → Pattern :=
  fun name => if name ∈ context.names then assignment name else .fvar name

/-- **A closed value**: a state without free variables. -/
def ClosedValue (value : Pattern) : Prop := IsState value ∧ freeWithin [] value = true

instance (value : Pattern) : Decidable (ClosedValue value) := by
  unfold ClosedValue IsState IsObject
  infer_instance

variable (T : NativeStructure Pattern)

/-- **A valuation of a context**: a closed value of each variable's type; every other name is left as it is. -/
def Valuation (context : Context) (assignment : String → Pattern) : Prop :=
  (∀ entry ∈ context, ClosedValue (assignment entry.1) ∧ T.typed (assignment entry.1) entry.2) ∧
    ∀ name, name ∉ context.names → assignment name = .fvar name

/-- **A substitution from a context to another**: images of the target's variables, free in the source, whose
instances under every valuation of the source form a valuation of the target. -/
def Substitution (source target : Context) (images : String → Pattern) : Prop :=
  (∀ entry ∈ target, freeWithin source.names (images entry.1) = true) ∧
    ∀ assignment, Valuation T source assignment →
      Valuation T target (restrictTo target fun name => freeSubst assignment (images name))

/-- The valuation of the empty context. -/
theorem valuation_nil : Valuation T [] Pattern.fvar := by
  refine ⟨fun _ member => ?_, fun _ _ => rfl⟩
  cases member

theorem eq_fvar_of_valuation_nil {assignment : String → Pattern} (valuation : Valuation T [] assignment) :
    assignment = Pattern.fvar :=
  funext fun name => valuation.2 name (by simp [Context.names])

variable {T}

/-- A valuation leaves its context's variables as they are under restriction. -/
theorem restrictTo_of_valuation {context : Context} {assignment : String → Pattern} (valuation : Valuation T context assignment) :
    restrictTo context assignment = assignment := by
  funext name
  unfold restrictTo
  split
  · rfl
  · rename_i outside
    exact (valuation.2 name outside).symm

/-- Every value of a valuation on its context's variables is closed. -/
theorem valuation_closed {context : Context} {assignment : String → Pattern} (valuation : Valuation T context assignment)
    {name : String} (member : name ∈ context.names) : freeWithin [] (assignment name) = true := by
  obtain ⟨type, entry⟩ := Context.mem_names.mp member
  exact (valuation.1 _ entry).1.2

/-! ## The site of contexts -/

variable (T)

/-- **The stages of a language**: its inhabited contexts. -/
abbrev ContextStage : Type := {context : Context // ∃ assignment, Valuation T context assignment}

/-- **The site of contexts**: inhabited contexts, valuations as points, instances of open terms and constant families
as elements, and the maps of valuations that substitutions induce as arrows. -/
def contextSite : Site Pattern where
  Stage := ContextStage T
  Point stage := {assignment : String → Pattern // Valuation T stage.1 assignment}
  inhabited stage := by
    obtain ⟨assignment, valuation⟩ := stage.2
    exact ⟨⟨assignment, valuation⟩⟩
  Arrow source target := {map | ∃ images : String → Pattern,
    (∀ entry ∈ target.1, freeWithin source.1.names (images entry.1) = true) ∧
      ∀ point, (map point).1 = restrictTo target.1 fun name => freeSubst point.1 (images name)}
  arrow_id stage := ⟨Pattern.fvar, fun entry member => decide_eq_true (Context.mem_names.mpr ⟨entry.2, member⟩),
    fun point => by
      simp only [freeSubst]
      exact (restrictTo_of_valuation point.2).symm⟩
  arrow_comp := by
    rintro first second third outer inner ⟨outerImages, outerFree, outerIs⟩ ⟨innerImages, innerFree, innerIs⟩
    refine ⟨fun name => freeSubst innerImages (outerImages name), fun entry member => ?_, fun point => ?_⟩
    · refine freeWithin_freeSubst (names := second.1.names) (fun name nameMem => ?_) (outerFree entry member)
      obtain ⟨type, entry'⟩ := Context.mem_names.mp nameMem
      exact innerFree _ entry'
    · rw [outerIs, innerIs]
      funext name
      unfold restrictTo
      split
      · rename_i inside
        obtain ⟨type, entry⟩ := Context.mem_names.mp inside
        dsimp only
        rw [freeSubst_comp]
        refine freeSubst_congr (names := second.1.names) (fun name' member' => ?_) (outerFree _ entry)
        simp only [member', if_true]
      · rfl
  Elem stage := {family | (∃ term, freeWithin stage.1.names term = true ∧ family = fun point => freeSubst point.1 term) ∨
    ∃ value, family = fun _ => value}
  elem_pull := by
    rintro source target element map (⟨term, within, rfl⟩ | ⟨value, rfl⟩) ⟨images, imagesFree, mapIs⟩
    · refine .inl ⟨freeSubst images term, freeWithin_freeSubst (names := target.1.names) (fun name member => ?_) within,
        funext fun point => ?_⟩
      · obtain ⟨type, entry⟩ := Context.mem_names.mp member
        exact imagesFree _ entry
      · show freeSubst (map point).1 term = freeSubst point.1 (freeSubst images term)
        rw [mapIs, freeSubst_comp]
        refine freeSubst_congr (names := target.1.names) (fun name member => ?_) within
        simp only [restrictTo, member, if_true]
    · exact .inr ⟨value, rfl⟩
  const_mem _ value := .inr ⟨value, rfl⟩
  terminal := ⟨[], Pattern.fvar, valuation_nil T⟩
  terminal_subsingleton first second :=
    Subtype.ext ((eq_fvar_of_valuation_nil T first.2).trans (eq_fvar_of_valuation_nil T second.2).symm)
  global stage point := ⟨point.1, fun entry member => (point.2.1 entry member).1.2, fun _ => by
    funext name
    unfold restrictTo
    split
    · rename_i inside
      exact (freeSubst_of_closed (valuation_closed point.2 inside) _).symm
    · rename_i outside
      exact point.2.2 name outside⟩

/-- **The family of an open term** at a stage: its instances under the stage's valuations. -/
def instancesAt (stage : (contextSite T).Stage) (term : Pattern) : (contextSite T).Family stage :=
  fun point => freeSubst point.1 term

theorem instancesAt_mem {stage : (contextSite T).Stage} {term : Pattern} (within : freeWithin stage.1.names term = true) :
    instancesAt T stage term ∈ (contextSite T).Elem stage :=
  .inl ⟨term, within, rfl⟩

/-! ## The open judgment -/

/-- **The open judgment `Γ ⊢ t : φ`**: the formula holds at every instance of the term under a valuation of the
context. -/
def OpenHolds (context : Context) (formula : Formula 0) (term : Pattern) : Prop :=
  ∀ assignment, Valuation T context assignment → T.sat Env.closed formula (freeSubst assignment term)

/-- **The open judgment is the classical judgment over valuations** at the term's family. -/
theorem openHolds_iff (stage : (contextSite T).Stage) (formula : Formula 0) (term : Pattern) :
    OpenHolds T stage.1 formula term ↔ T.holdsAt (contextSite T) Env.closed formula (instancesAt T stage term) :=
  ⟨fun holds point => holds point.1 point.2, fun holds assignment valuation => holds ⟨assignment, valuation⟩⟩

variable {T}

/-- **The open judgment is closed under substitution.** -/
theorem openHolds_subst {source target : Context} {images : String → Pattern} {formula : Formula 0} {term : Pattern}
    (holds : OpenHolds T target formula term) (within : freeWithin target.names term = true)
    (substitution : Substitution T source target images) :
    OpenHolds T source formula (freeSubst images term) := by
  intro assignment valuation
  have instance' := holds _ (substitution.2 assignment valuation)
  have same : freeSubst (restrictTo target fun name => freeSubst assignment (images name)) term =
      freeSubst (fun name => freeSubst assignment (images name)) term :=
    freeSubst_congr (names := target.names) (fun name member => by simp only [restrictTo, member, if_true]) within
  rwa [same, ← freeSubst_comp] at instance'

/-- **A closed term**: the judgment is its formula, in an inhabited context. -/
theorem openHolds_closed_iff {context : Context} {formula : Formula 0} {term : Pattern}
    (closed : freeWithin [] term = true) (inhabited : ∃ assignment, Valuation T context assignment) :
    OpenHolds T context formula term ↔ T.sat Env.closed formula term := by
  constructor
  · intro holds
    obtain ⟨assignment, valuation⟩ := inhabited
    have := holds assignment valuation
    rwa [freeSubst_of_closed closed] at this
  · intro holds assignment _
    rwa [freeSubst_of_closed closed]

/-- In the empty context, the judgment is the formula. -/
theorem openHolds_nil_iff {formula : Formula 0} {term : Pattern} :
    OpenHolds T [] formula term ↔ T.sat Env.closed formula term := by
  constructor
  · intro holds
    have := holds _ (valuation_nil T)
    rwa [freeSubst_fvar] at this
  · intro holds assignment valuation
    rwa [eq_fvar_of_valuation_nil T valuation, freeSubst_fvar]

/-- **One variable at a time**: the judgment in a context with a first variable holds when it holds, in the rest of
the context, at the term with each closed value of the variable's type in its place. -/
theorem openHolds_cons {name : String} {type : TypeExpr} {context : Context} {formula : Formula 0} {term : Pattern}
    (fresh : name ∉ context.names) (within : freeWithin (name :: context.names) term = true) :
    OpenHolds T ((name, type) :: context) formula term ↔
      ∀ value, ClosedValue value → T.typed value type → OpenHolds T context formula (freeSubst (single name value) term) := by
  constructor
  · intro holds value closedValue typedValue assignment valuation
    rw [freeSubst_comp]
    have extended : Valuation T ((name, type) :: context) (fun other => if other = name then value else assignment other) := by
      refine ⟨fun entry member => ?_, fun other outside => ?_⟩
      · rcases List.mem_cons.mp member with rfl | member
        · simp only [if_true]
          exact ⟨closedValue, typedValue⟩
        · have different : entry.1 ≠ name := fun same =>
            fresh (same ▸ Context.mem_names.mpr ⟨entry.2, member⟩)
          simp only [different, if_false]
          exact valuation.1 entry member
      · have different : other ≠ name := fun same => outside (by simp [Context.names, same])
        have outside' : other ∉ context.names := fun inside => outside (by
          simp only [Context.names, List.map_cons, List.mem_cons] at inside ⊢
          exact .inr inside)
        simp only [different, if_false]
        exact valuation.2 other outside'
    have agree : ∀ other ∈ name :: context.names,
        (fun other => if other = name then value else assignment other) other =
          freeSubst assignment (single name value other) := by
      intro other _
      by_cases same : other = name
      · subst same
        simp only [single]
        exact (freeSubst_of_closed closedValue.2 _).symm
      · simp only [single, if_neg same, freeSubst]
    rw [← freeSubst_congr agree within]
    exact holds _ extended
  · intro holds assignment valuation
    have entry := valuation.1 (name, type) (List.mem_cons_self ..)
    have rest : Valuation T context (fun other => if other = name then .fvar name else assignment other) := by
      refine ⟨fun entry' member => ?_, fun other outside => ?_⟩
      · have different : entry'.1 ≠ name := fun same =>
          fresh (same ▸ Context.mem_names.mpr ⟨entry'.2, member⟩)
        simp only [different, if_false]
        exact valuation.1 entry' (List.mem_cons_of_mem _ member)
      · by_cases same : other = name
        · simp only [same, if_true]
        · simp only [same, if_false]
          refine valuation.2 other fun inside => ?_
          simp only [Context.names, List.map_cons, List.mem_cons] at inside
          exact inside.elim same outside
    have instance' := holds (assignment name) entry.1 entry.2 _ rest
    rw [freeSubst_comp] at instance'
    have agree : ∀ other ∈ name :: context.names,
        freeSubst (fun other => if other = name then .fvar name else assignment other)
          (single name (assignment name) other) = assignment other := by
      intro other _
      by_cases same : other = name
      · subst same
        simp only [single]
        exact freeSubst_of_closed entry.1.2 _
      · simp only [single, if_neg same, freeSubst]
    rwa [freeSubst_congr agree within] at instance'

/-! ## Forcing at a context -/

variable (T)

/-- **Forcing of a closed formula by an open term at a context**: the presheaf reading of the open judgment. -/
def ForcesOpen (stage : (contextSite T).Stage) (formula : Formula 0) (term : Pattern) : Prop :=
  T.forces (contextSite T) (fun index => index.elim0) stage formula (instancesAt T stage term)

variable {T}

/-- **Forcing is sound for the open judgment.** -/
theorem openHolds_of_forces {stage : (contextSite T).Stage} {formula : Formula 0} {term : Pattern}
    (forced : ForcesOpen T stage formula term) : OpenHolds T stage.1 formula term :=
  (openHolds_iff T stage formula term).mpr
    (T.forces_sound (contextSite T) formula (classical := Env.closed) (fun index => index.elim0) _ forced)

/-- **On negative formulas, forcing is the open judgment.** -/
theorem forcesOpen_iff_of_negative {formula : Formula 0} (negative : formula.negative = true) (stage : (contextSite T).Stage)
    (term : Pattern) : ForcesOpen T stage formula term ↔ OpenHolds T stage.1 formula term := by
  have env : (fun index : Fin 0 => index.elim0 : Fin 0 → (contextSite T).Sets) =
      fun index => (contextSite T).lift (Env.closed index) := funext fun index => index.elim0
  unfold ForcesOpen
  rw [env, T.forces_iff_of_negative (contextSite T) negative Env.closed, openHolds_iff]

end Mettapedia.OSLF.NativeTypes.GeneratedLogic
