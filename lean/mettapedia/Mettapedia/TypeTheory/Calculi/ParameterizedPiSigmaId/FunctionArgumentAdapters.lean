import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationSensitiveRegularity
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TelescopeAbstraction

/-!
# Typed adapters for curried function arguments

Each slot names an input type, an output type and a projection programme.
The generated lambda programme feeds the projected arguments to the original
function in the same order. Slot types may depend on the ambient context;
they do not depend on earlier slots. Explicit universe-product closure and
the typings of the individual projections earn the complete adapter typing.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace FunctionArgumentAdapters

open FormationSensitive

variable {Head TargetHead : Type} {n m : Nat}

def arrow (input output : Tm Head n) : Tm Head n := .pi input (rename wk output)

theorem arrow_substitute (sigma : Sub Head n m) (input output : Tm Head n) :
    subst sigma (arrow input output) = arrow (subst sigma input) (subst sigma output) := by
  simp only [arrow, subst, subst_liftSub_wk]

theorem arrow_rename (rho : Ren n m) (input output : Tm Head n) :
    rename rho (arrow input output) = arrow (rename rho input) (rename rho output) := by
  simpa only [subst_renSub] using arrow_substitute (renSub rho) input output

theorem arrow_apply {R : Rules Head} {context : Ctx Head n}
    {function argument input output : Tm Head n}
    (functionTyped : Typing R context function (arrow input output))
    (argumentTyped : Typing R context argument input) :
    Typing R context (.app function argument) output := by
  simpa only [arrow, inst0_rename_wk] using Typing.appElim functionTyped argumentTyped

def curriedType {n : Nat} (domains : List (Tm Head n)) (result : Tm Head n) : Tm Head n :=
  match domains with
  | [] => result
  | first :: rest => .pi first (curriedType (rest.map (rename wk)) (rename wk result))
termination_by domains.length
  decreasing_by simp_wf

theorem curriedType_substitute {n m : Nat} (domains : List (Tm Head n)) (result : Tm Head n)
    (sigma : Sub Head n m) :
    subst sigma (curriedType domains result) =
      curriedType (domains.map (subst sigma)) (subst sigma result) := by
  cases domains with
  | nil => simp only [curriedType, List.map_nil]
  | cons first rest =>
      simp only [curriedType, subst, List.map_cons]
      congr 1
      simpa only [List.map_map, Function.comp_def, subst_liftSub_wk] using
        curriedType_substitute (rest.map (rename wk)) (rename wk result) (liftSub sigma)
termination_by domains.length
  decreasing_by simp_wf

theorem curriedType_rename (domains : List (Tm Head n)) (result : Tm Head n) (rho : Ren n m) :
    rename rho (curriedType domains result) =
      curriedType (domains.map (rename rho)) (rename rho result) := by
  have same : (subst (renSub rho) : Tm Head n → Tm Head m) = rename rho := by
    funext term
    exact subst_renSub rho term
  simpa only [same] using curriedType_substitute domains result (renSub rho)

theorem curriedType_cons (domain : Tm Head n) (rest : List (Tm Head n)) (result : Tm Head n) :
    curriedType (domain :: rest) result = arrow domain (curriedType rest result) := by
  simpa only [curriedType, arrow] using
    congrArg (Tm.pi domain) (curriedType_rename rest result wk).symm

theorem curriedType_mapHead {n : Nat} (domains : List (Tm Head n)) (result : Tm Head n) (map : Head → TargetHead) :
    (curriedType domains result).mapHead map =
      curriedType (domains.map (Tm.mapHead map)) (result.mapHead map) := by
  cases domains with
  | nil => simp only [curriedType, List.map_nil]
  | cons first rest =>
      simp only [curriedType, Tm.mapHead, List.map_cons]
      congr 1
      simpa only [List.map_map, Function.comp_def, Tm.mapHead_rename] using
        curriedType_mapHead (rest.map (rename wk)) (rename wk result) map
termination_by domains.length
  decreasing_by simp_wf

structure Slot (Head : Type) (n : Nat) where
  input : Tm Head n
  output : Tm Head n
  projection : Tm Head n

def Slot.map (mapping : Tm Head n → Tm TargetHead m) (slot : Slot Head n) : Slot TargetHead m :=
  ⟨mapping slot.input, mapping slot.output, mapping slot.projection⟩

def Slot.weaken (slot : Slot Head n) : Slot Head (n + 1) := slot.map (rename wk)

theorem Slot.map_comp {ThirdHead : Type} {k : Nat}
    (first : Tm Head n → Tm TargetHead m) (second : Tm TargetHead m → Tm ThirdHead k)
    (slot : Slot Head n) :
    (slot.map first).map second = slot.map (second ∘ first) := rfl

theorem Slot.weaken_substitute (slot : Slot Head n) (sigma : Sub Head n m) :
    slot.weaken.map (subst (liftSub sigma)) = (slot.map (subst sigma)).weaken := by
  cases slot
  simp only [Slot.weaken, Slot.map, subst_liftSub_wk]

theorem Slot.weaken_open (slot : Slot Head n) (argument : Tm Head n) :
    slot.weaken.map (inst0 argument) = slot := by
  cases slot
  simp only [Slot.weaken, Slot.map, inst0_rename_wk]

theorem Slot.weaken_subst0 (slot : Slot Head n) (argument : Tm Head n) :
    slot.weaken.map (subst (subst0 argument)) = slot := Slot.weaken_open slot argument

theorem Slot.weaken_mapHead (slot : Slot Head n) (map : Head → TargetHead) :
    slot.weaken.map (Tm.mapHead map) = (slot.map (Tm.mapHead map)).weaken := by
  cases slot
  simp only [Slot.weaken, Slot.map, Tm.mapHead_rename]

def adapt {n : Nat} (slots : List (Slot Head n)) (function : Tm Head n) : Tm Head n :=
  match slots with
  | [] => function
  | first :: rest =>
      .lam (adapt (rest.map Slot.weaken)
        (.app (rename wk function) (.app (rename wk first.projection) (.var 0))))
termination_by slots.length
  decreasing_by simp_wf

theorem adapt_substitute {n m : Nat} (slots : List (Slot Head n))
    (function : Tm Head n) (sigma : Sub Head n m) :
    subst sigma (adapt slots function) =
      adapt (slots.map (Slot.map (subst sigma))) (subst sigma function) := by
  cases slots with
  | nil => simp only [adapt, List.map_nil]
  | cons first rest =>
      simp only [adapt, subst, List.map_cons]
      congr 1
      simpa only [List.map_map, Function.comp_def, Slot.weaken_substitute,
        subst, subst_liftSub_wk, liftSub, Fin.cases_zero, Slot.map, Slot.weaken] using
        adapt_substitute (rest.map Slot.weaken)
          (.app (rename wk function) (.app (rename wk first.projection) (.var 0)))
          (liftSub sigma)
termination_by slots.length
  decreasing_by simp_wf

theorem adapt_rename (slots : List (Slot Head n)) (function : Tm Head n) (rho : Ren n m) :
    rename rho (adapt slots function) =
      adapt (slots.map (Slot.map (rename rho))) (rename rho function) := by
  have same : (subst (renSub rho) : Tm Head n → Tm Head m) = rename rho := by
    funext term
    exact subst_renSub rho term
  simpa only [same] using adapt_substitute slots function (renSub rho)

theorem adapt_mapHead {n : Nat} (slots : List (Slot Head n)) (function : Tm Head n)
    (map : Head → TargetHead) :
    (adapt slots function).mapHead map =
      adapt (slots.map (Slot.map (Tm.mapHead map))) (function.mapHead map) := by
  cases slots with
  | nil => simp only [adapt, List.map_nil]
  | cons first rest =>
      simp only [adapt, Tm.mapHead, List.map_cons]
      congr 1
      simpa only [List.map_map, Function.comp_def, Slot.weaken_mapHead,
        Tm.mapHead, Tm.mapHead_rename, Slot.map, Slot.weaken] using
        adapt_mapHead (rest.map Slot.weaken)
          (.app (rename wk function) (.app (rename wk first.projection) (.var 0))) map
termination_by slots.length
  decreasing_by simp_wf

theorem adapt_cons_beta (first : Slot Head n) (rest : List (Slot Head n))
    (function argument : Tm Head n) :
    TelescopeAbstraction.BetaSteps (.app (adapt (first :: rest) function) argument)
      (adapt rest (.app function (.app first.projection argument))) := by
  have beta := StepCore.betaPi (root := (RootComputation.empty : RootComputation Head))
    (headEq := fun _ _ => False)
    (adapt (rest.map Slot.weaken)
      (.app (rename wk function) (.app (rename wk first.projection) (.var 0)))) argument
  have opened : inst0 argument
      (adapt (rest.map Slot.weaken)
        (.app (rename wk function) (.app (rename wk first.projection) (.var 0)))) =
      adapt rest (.app function (.app first.projection argument)) := by
    change subst (subst0 argument) _ = _
    rw [adapt_substitute]
    simp only [List.map_map, Function.comp_def, Slot.weaken_subst0,
      subst, show subst (subst0 argument) (rename wk function) = function from
        inst0_rename_wk argument function,
      show subst (subst0 argument) (rename wk first.projection) = first.projection from
        inst0_rename_wk argument first.projection, subst0, Fin.cases_zero]
    exact congrArg (fun slots => adapt slots (.app function (.app first.projection argument)))
      (List.map_id rest)
  rw [opened] at beta
  simpa only [adapt] using Relation.ReflTransGen.single beta

theorem step_apply (arguments : List (Tm Head n)) {source target : Tm Head n}
    (step : StepCore (RootComputation.empty : RootComputation Head)
      (fun _ _ => False) source target) :
    StepCore (RootComputation.empty : RootComputation Head) (fun _ _ => False)
      (arguments.foldl Tm.app source) (arguments.foldl Tm.app target) := by
  induction arguments generalizing source target with
  | nil => exact step
  | cons argument rest ih => exact ih (StepCore.congAppFun step)

/-- Applying the generated programme preserves all outer argument slots in
order. A nested bundle occupies one slot even when it contains many positions. -/
theorem adapt_apply {n : Nat} (slots : List (Slot Head n)) (arguments : List (Tm Head n))
    (function : Tm Head n) (arity : arguments.length = slots.length) :
    TelescopeAbstraction.BetaSteps
      (arguments.foldl Tm.app (adapt slots function))
      (((slots.zip arguments).map (fun pair => Tm.app pair.1.projection pair.2)).foldl
        Tm.app function) := by
  cases slots with
  | nil =>
      have empty : arguments = [] := by simpa using arity
      subst arguments
      simpa only [adapt, List.foldl_nil, List.zip_nil_left, List.map_nil] using
        (Relation.ReflTransGen.refl (a := function) : TelescopeAbstraction.BetaSteps function function)
  | cons first rest =>
      cases arguments with
      | nil => simp only [List.length_nil, List.length_cons] at arity; omega
      | cons argument remaining =>
          have step := (adapt_cons_beta first rest function argument).lift
            (fun term => remaining.foldl Tm.app term)
            (fun _ _ step => step_apply remaining step)
          exact step.trans (adapt_apply rest remaining
            (.app function (.app first.projection argument)) (by simpa using arity))
termination_by slots.length
  decreasing_by simp_all

def SlotsTyped (R : Rules Head) (context : Ctx Head n) (level : Head) (slots : List (Slot Head n)) : Prop :=
  ∀ slot ∈ slots,
    Typing R context slot.input (.head level) ∧
    Typing R context slot.output (.head level) ∧
    Typing R context slot.projection (arrow slot.input slot.output)

theorem SlotsTyped.weaken {R : Rules Head} {context : Ctx Head n} {level : Head}
    {slots : List (Slot Head n)} (typed : SlotsTyped R context level slots) (extension : Tm Head n) :
    SlotsTyped R (.snoc context extension) level (slots.map Slot.weaken) := by
  intro slot member
  obtain ⟨original, present, rfl⟩ := List.mem_map.mp member
  obtain ⟨input, output, projection⟩ := typed original present
  refine ⟨input.weaken, output.weaken, ?_⟩
  simpa only [Slot.weaken, Slot.map, arrow_rename] using projection.weaken (extension := extension)

theorem piForm_bounded {R : Rules Head} {context : Ctx Head n} {level : Head}
    (isUniverse : R.isUniverse level)
    (closure : ∃ result, R.join level level result ∧ (result = level ∨ R.cumulative result level))
    {domain : Tm Head n} {codomain : Tm Head (n + 1)}
    (input : Typing R context domain (.head level))
    (output : Typing R (.snoc context domain) codomain (.head level)) :
    Typing R context (.pi domain codomain) (.head level) := by
  obtain ⟨result, product, bound⟩ := closure
  have formed := Typing.piForm input isUniverse output isUniverse product
  rcases bound with same | cumulative
  · exact same ▸ formed
  · exact .cumul formed cumulative

theorem curriedType_formed {n : Nat} {R : Rules Head} {context : Ctx Head n} {level : Head}
    (isUniverse : R.isUniverse level)
    (closure : ∃ result, R.join level level result ∧ (result = level ∨ R.cumulative result level))
    (domains : List (Tm Head n)) (result : Tm Head n)
    (inputs : ∀ domain ∈ domains, Typing R context domain (.head level))
    (output : Typing R context result (.head level)) :
    Typing R context (curriedType domains result) (.head level) := by
  cases domains with
  | nil => simpa only [curriedType] using output
  | cons first rest =>
      rw [curriedType]
      apply piForm_bounded isUniverse closure (inputs first (List.mem_cons_self))
      apply curriedType_formed isUniverse closure
      · intro domain member
        obtain ⟨original, present, rfl⟩ := List.mem_map.mp member
        exact (inputs original (List.mem_cons_of_mem first present)).weaken
      · exact output.weaken
termination_by domains.length
  decreasing_by simp_all

/-- The generator derives a new function from independently typed slot
projections. No typing premise for the generated lambda term is assumed. -/
theorem adapt_typed {n : Nat} {R : Rules Head} {context : Ctx Head n} {level : Head}
    (isUniverse : R.isUniverse level)
    (closure : ∃ result, R.join level level result ∧ (result = level ∨ R.cumulative result level))
    (slots : List (Slot Head n)) (typed : SlotsTyped R context level slots)
    {function result : Tm Head n} (resultFormed : Typing R context result (.head level))
    (functionTyped : Typing R context function (curriedType (slots.map Slot.output) result)) :
    Typing R context (adapt slots function) (curriedType (slots.map Slot.input) result) := by
  cases slots with
  | nil => simpa only [adapt, List.map_nil, curriedType] using functionTyped
  | cons first rest =>
      obtain ⟨input, output, projection⟩ := typed first (List.mem_cons_self)
      have formed := curriedType_formed isUniverse closure ((first :: rest).map Slot.input) result
        (by intro domain member; obtain ⟨slot, present, rfl⟩ := List.mem_map.mp member; exact (typed slot present).1)
        resultFormed
      simp only [List.map_cons, curriedType] at formed
      rw [adapt, List.map_cons, curriedType]
      refine Typing.lamIntro formed isUniverse ?_
      have projected := Typing.appElim
        (show Typing R (.snoc context first.input) (rename wk first.projection)
          (arrow (rename wk first.input) (rename wk first.output)) from
          by simpa only [arrow_rename] using projection.weaken (extension := first.input))
        (Typing.var (R := R) (Γ := .snoc context first.input) 0)
      have projectedTyped : Typing R (.snoc context first.input)
          (.app (rename wk first.projection) (.var 0)) (rename wk first.output) := by
        simpa only [arrow, inst0_rename_wk] using projected
      have sourceArrow : Typing R context function
          (arrow first.output (curriedType (rest.map Slot.output) result)) := by
        simpa only [List.map_cons, curriedType_cons] using functionTyped
      have weakenedArrow : Typing R (.snoc context first.input) (rename wk function)
          (arrow (rename wk first.output)
            (rename wk (curriedType (rest.map Slot.output) result))) := by
        simpa only [arrow_rename] using sourceArrow.weaken (extension := first.input)
      have applied := arrow_apply weakenedArrow projectedTyped
      rw [curriedType_rename] at applied
      have restTyped : SlotsTyped R context level rest :=
        fun slot present => typed slot (List.mem_cons_of_mem first present)
      have checked := adapt_typed isUniverse closure (rest.map Slot.weaken)
        (restTyped.weaken first.input) resultFormed.weaken
        (by simpa only [List.map_map, Slot.weaken, Slot.map, Function.comp_def] using applied)
      simpa only [adapt, List.map_cons, curriedType, List.map_map, Slot.weaken, Slot.map,
        Function.comp_def] using checked
termination_by slots.length
  decreasing_by simp_all

#print axioms adapt_typed

theorem adapt_judgment {R : Rules Head} {context : Ctx Head n} {level : Head}
    (isUniverse : R.isUniverse level)
    (closure : ∃ result, R.join level level result ∧ (result = level ∨ R.cumulative result level))
    (slots : List (Slot Head n)) (typed : SlotsTyped R context level slots)
    {function result : Tm Head n} (resultFormed : Typing R context result (.head level))
    (functionJudgment : Judgment R context function (curriedType (slots.map Slot.output) result)) :
    Judgment R context (adapt slots function) (curriedType (slots.map Slot.input) result) :=
  ⟨functionJudgment.context,
    adapt_typed isUniverse closure slots typed resultFormed functionJudgment.typing⟩

#print axioms adapt_substitute
#print axioms adapt_mapHead
#print axioms adapt_apply
#print axioms adapt_judgment

end FunctionArgumentAdapters
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
