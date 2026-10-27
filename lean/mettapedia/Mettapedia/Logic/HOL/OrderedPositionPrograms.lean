import Mettapedia.Logic.HOL.ConstructorPositionPrograms
import Mettapedia.Logic.HOL.SuccessorOrder
import Mettapedia.TypeTheory.OrderedPositionSegments

/-!
# Typed programs for ordered position segments

Each segment supplies a count and a child index in the original context.
The compiled relation tests its first segment, then shifts later slots by that
count. Arithmetic is defined by successor closure, without extra constants.
The interpretation retains ordered lookup, including repeated child indices.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Mettapedia.Logic.HOL.OrderedPositionPrograms
universe u v w
variable {Base : Type u} {Const : Ty Base → Type v} {Γ Δ Ξ : Ctx Base}
  {number index : Ty Base}

abbrev Segment (Const : Ty Base → Type v) (Γ : Ctx Base) (number index : Ty Base) :=
  Term Const Γ number × Term Const Γ index
abbrev Plan (Const : Ty Base → Type v) (Γ : Ctx Base) (number index : Ty Base) :=
  List (Segment Const Γ number index)

def substitute (rho : Subst Const Γ Δ) (plan : Plan Const Γ number index) : Plan Const Δ number index :=
  plan.map (fun segment => (HOL.subst rho segment.1, HOL.subst rho segment.2))

@[simp] theorem substitute_cons (rho : Subst Const Γ Δ) (segment : Segment Const Γ number index)
    (rest : Plan Const Γ number index) :
    substitute rho (segment :: rest) = (HOL.subst rho segment.1, HOL.subst rho segment.2) :: substitute rho rest := rfl

variable (zero : ClosedTerm Const number) (successor : ClosedTerm Const (number ⇒ number))

/-- Binder insertion is performed uniformly by the supplied substitution. -/
def compileAt (zero : ClosedTerm Const number) (successor : ClosedTerm Const (number ⇒ number)) :
    Plan Const Γ number index → {Δ : Ctx Base} → Subst Const Γ Δ →
    Term Const Δ number → Term Const Δ index → Formula Const Δ
  | [], _, _, _, _ => .bot
  | (count, childIndex) :: rest, _, rho, slot, target =>
      .or (.and
        (.app (.app (weakenCtx _ (SuccessorOrder.less successor)) slot) (HOL.subst rho count))
        (.eq target (HOL.subst rho childIndex)))
        (.ex (.and
          (.app (.app (.app (weakenCtx _ (SuccessorOrder.sum zero successor))
            (weaken (HOL.subst rho count))) (.var .vz)) (weaken slot))
          (compileAt zero successor rest (fun entry => weaken (rho entry)) (.var .vz) (weaken target))))

def graph (plan : Plan Const Γ number index) : Term Const Γ (number ⇒ index ⇒ .prop) :=
  .lam (.lam (compileAt zero successor plan IndexedConstructorGuards.ConstructorPrograms.beneathTwo
    (.var (.vs .vz)) (.var .vz)))

@[simp] theorem compileAt_subst (plan : Plan Const Γ number index)
    (rho : Subst Const Γ Δ) (theta : Subst Const Δ Ξ)
    (slot : Term Const Δ number) (target : Term Const Δ index) :
    HOL.subst theta (compileAt zero successor plan rho slot target) =
      compileAt zero successor plan (fun entry => HOL.subst theta (rho entry))
        (HOL.subst theta slot) (HOL.subst theta target) := by
  induction plan generalizing Δ Ξ with
  | nil => rfl
  | cons segment rest hypothesis =>
      rcases segment with ⟨count, childIndex⟩
      simp only [compileAt, HOL.subst, HOL.subst_weakenCtx, HOL.subst_comp, hypothesis,
        HOL.subst_weaken, Subst.lift]
      rfl

theorem compileAt_substitute (plan : Plan Const Γ number index)
    (rho : Subst Const Γ Δ) (theta : Subst Const Δ Ξ)
    (slot : Term Const Ξ number) (target : Term Const Ξ index) :
    compileAt zero successor (substitute rho plan) theta slot target =
      compileAt zero successor plan (fun entry => HOL.subst theta (rho entry)) slot target := by
  induction plan generalizing Ξ with
  | nil => rfl
  | cons segment rest hypothesis =>
      rcases segment with ⟨count, childIndex⟩
      simp only [substitute_cons, compileAt, HOL.subst_comp, hypothesis]
      simp only [weaken, HOL.rename_subst, Subst.comp]
      rfl

@[simp] theorem graph_substitute (plan : Plan Const Γ number index) (rho : Subst Const Γ Δ) :
    HOL.subst rho (graph zero successor plan) = graph zero successor (substitute rho plan) := by
  simp only [graph, HOL.subst, compileAt_subst, compileAt_substitute,
    IndexedConstructorGuards.ConstructorPrograms.beneathTwo, Subst.lift]
  congr 3
  funext type entry
  calc
    _ = HOL.rename (fun entry => Var.vs (Var.vs entry)) (rho entry) := by
      rw [HOL.rename_comp]
      exact HOL.rename_ext (fun _ => rfl) _
    _ = _ := (HOL.subst_ofRename (fun entry => Var.vs (Var.vs entry)) (rho entry)).symm.trans
      (HOL.subst_ext (fun _ => rfl) _)

open FiniteConstructorEncoding CurriedPredicates

abbrev FieldPlan (Const : Ty Base → Type v) (Γ : Ctx Base) (fields : List (Ty Base))
    (number index : Ty Base) :=
  List (Term Const Γ (FunctionType fields number) × Term Const Γ (FunctionType fields index))

def fieldTerms (fields : List (Ty Base)) (plan : FieldPlan Const Γ fields number index)
    (rho : Subst Const Γ Δ) (arguments : Arguments Const Δ fields) : Plan Const Δ number index :=
  plan.map (fun segment => (applyFields fields (HOL.subst rho segment.1) arguments,
    applyFields fields (HOL.subst rho segment.2) arguments))

/-- The shared argument abstraction inserts all constructor fields. -/
def fieldGraph (fields : List (Ty Base)) (plan : FieldPlan Const Γ fields number index) :
    Term Const Γ (number ⇒ index ⇒ handlerType fields) :=
  .lam (.lam (abstractArguments fields (fun rho arguments =>
    compileAt zero successor (fieldTerms fields plan (fun entry => rho (.vs (.vs entry))) arguments)
      (fun entry => .var entry) (rho (.vs .vz)) (rho .vz))))

variable (model : HenkinModel.{u,v,w} Base Const)
  (numbers : Nat ≃ Ty.denote model.Carrier number)

def evaluate (values : model.Valuation Γ) (plan : Plan Const Γ number index) :
    List (Mettapedia.TypeTheory.OrderedPositionSegments.Segment (Ty.denote model.Carrier index)) :=
  plan.map (fun segment => (numbers.symm (model.denote segment.1 values), model.denote segment.2 values))

def evaluateFields (fields : List (Ty Base)) (values : model.Valuation Γ)
    (data : Mettapedia.TypeTheory.IndexedPolynomial.Description.Env (Ty.denote model.Carrier) fields)
    (plan : FieldPlan Const Γ fields number index) :
    List (Mettapedia.TypeTheory.OrderedPositionSegments.Segment (Ty.denote model.Carrier index)) :=
  plan.map (fun segment => (numbers.symm (applyValues model fields (model.denote segment.1 values) data),
    applyValues model fields (model.denote segment.2 values) data))

theorem evaluate_fieldTerms (fields : List (Ty Base)) (plan : FieldPlan Const Γ fields number index)
    (rho : Subst Const Γ Δ) (arguments : Arguments Const Δ fields) (values : model.Valuation Δ) :
    evaluate model numbers values (fieldTerms fields plan rho arguments) =
      evaluateFields model numbers fields (fun entry => model.denote (rho entry) values)
        (denoteArguments model fields arguments values) plan := by
  simp only [evaluate, fieldTerms, evaluateFields, List.map_map, Function.comp_def,
    applyFields_denote, Soundness.denote_subst]
  rfl

variable (full : model.FullDomains) (arithmeticValues : model.Valuation [])
  (zero_preserved : model.denote zero arithmeticValues = numbers 0)
  (successor_preserved : ∀ n, model.denote successor arithmeticValues (numbers n) = numbers (n + 1))
include full zero_preserved successor_preserved

theorem compileAt_denote (plan : Plan Const Γ number index)
    (environment : model.Valuation Γ) (rho : Subst Const Γ Δ)
    (slot : Term Const Δ number) (target : Term Const Δ index) (values : model.Valuation Δ)
    (represented : ∀ {type} (entry : Var Γ type), model.denote (rho entry) values = environment entry) :
    (model.denote (compileAt zero successor plan rho slot target) values).down ↔
      (Mettapedia.TypeTheory.OrderedPositionSegments.flatten (evaluate model numbers environment plan))[numbers.symm (model.denote slot values)]? = some (model.denote target values) := by
  have closedDenote {type : Ty Base} (term : ClosedTerm Const type) (context : Ctx Base)
      (later : model.Valuation context) :
      model.denote (weakenCtx context term) later = model.denote term arithmeticValues := by
    rw [model.denote_weakenCtx]
    apply congrArg (model.denote term)
    funext type entry
    exact nomatch entry
  induction plan generalizing Δ with
  | nil => simp [compileAt, evaluate, Mettapedia.TypeTheory.OrderedPositionSegments.flatten,
      HenkinModel.denote, PreModel.denote]
  | cons segment rest hypothesis =>
    rcases segment with ⟨count, childIndex⟩
    have translated {type : Ty Base} (term : Term Const Γ type) :
        model.denote (HOL.subst rho term) values = model.denote term environment := by
      rw [Soundness.denote_subst]
      apply congrArg (model.denote term)
      funext type entry
      exact represented entry
    have recursive (offset : Ty.denote model.Carrier number) :=
      hypothesis (fun entry => weaken (rho entry)) (.var .vz) (weaken target)
        (model.extend values offset) (fun entry =>
          (Soundness.denote_weaken model (rho entry) values offset).trans (represented entry))
    change ((model.denote (weakenCtx _ (SuccessorOrder.less successor)) values
        (model.denote slot values) (model.denote (HOL.subst rho count) values)).down ∧
      model.Eqv index (model.denote target values) (model.denote (HOL.subst rho childIndex) values)) ∨
      (∃ offset, model.adm number offset ∧
        (model.denote (weakenCtx _ (SuccessorOrder.sum zero successor)) (model.extend values offset)
          (model.denote (weaken (HOL.subst rho count)) (model.extend values offset)) offset
          (model.denote (weaken slot) (model.extend values offset))).down ∧
        (model.denote (compileAt zero successor rest (fun entry => weaken (rho entry))
          (.var .vz) (weaken target)) (model.extend values offset)).down) ↔ _
    simp only [closedDenote, Soundness.denote_weaken, translated,
      SuccessorOrder.less_iff model full successor arithmeticValues numbers successor_preserved,
      SuccessorOrder.sum_iff model full successor arithmeticValues zero numbers zero_preserved successor_preserved,
      model.eqv_iff_eq_of_fullDomains full, recursive, HenkinModel.denote, PreModel.denote, PreModel.extend]
    change (_ ∧ _) ∨ (∃ offset, _ ∧ _) ↔
      (Mettapedia.TypeTheory.OrderedPositionSegments.flatten
        ((numbers.symm (model.denote count environment), model.denote childIndex environment) ::
          evaluate model numbers environment rest))[numbers.symm (model.denote slot values)]? = some (model.denote target values)
    rw [Mettapedia.TypeTheory.OrderedPositionSegments.lookup_cons]
    apply or_congr Iff.rfl
    constructor
    · rintro ⟨offset, _, same, found⟩
      exact ⟨numbers.symm offset, same, found⟩
    · rintro ⟨offset, same, found⟩
      exact ⟨numbers offset, full _ _, by simpa only [Equiv.symm_apply_apply] using same,
        by simpa only [Equiv.symm_apply_apply] using found⟩

theorem graph_denote (plan : Plan Const Γ number index) (environment : model.Valuation Γ)
    (slot : Ty.denote model.Carrier number) (target : Ty.denote model.Carrier index) :
    (model.denote (graph zero successor plan) environment slot target).down ↔
      (Mettapedia.TypeTheory.OrderedPositionSegments.flatten (evaluate model numbers environment plan))[numbers.symm slot]? = some target := by
  have exactLookup := compileAt_denote zero successor model numbers full arithmeticValues
    zero_preserved successor_preserved plan environment
    IndexedConstructorGuards.ConstructorPrograms.beneathTwo (.var (.vs .vz)) (.var .vz)
    (model.extend (model.extend environment slot) target) (fun _ => rfl)
  exact exactLookup

theorem graph_functional (plan : Plan Const Γ number index) (environment : model.Valuation Γ)
    (slot : Ty.denote model.Carrier number) {first second : Ty.denote model.Carrier index}
    (one : (model.denote (graph zero successor plan) environment slot first).down)
    (two : (model.denote (graph zero successor plan) environment slot second).down) : first = second :=
  Mettapedia.TypeTheory.OrderedPositionSegments.lookup_functional _ _
    ((graph_denote zero successor model numbers full arithmeticValues zero_preserved successor_preserved
      plan environment slot first).mp one)
    ((graph_denote zero successor model numbers full arithmeticValues zero_preserved successor_preserved
      plan environment slot second).mp two)

theorem graph_active_iff (plan : Plan Const Γ number index) (environment : model.Valuation Γ)
    (slot : Ty.denote model.Carrier number) :
    (∃ target, (model.denote (graph zero successor plan) environment slot target).down) ↔
      numbers.symm slot < (Mettapedia.TypeTheory.OrderedPositionSegments.flatten
        (evaluate model numbers environment plan)).length :=
  (exists_congr (fun target => graph_denote zero successor model numbers full arithmeticValues
    zero_preserved successor_preserved plan environment slot target)).trans
      (Mettapedia.TypeTheory.OrderedPositionSegments.active_iff _ _)

theorem fieldGraph_denote (fields : List (Ty Base)) (plan : FieldPlan Const Γ fields number index)
    (environment : model.Valuation Γ)
    (data : Mettapedia.TypeTheory.IndexedPolynomial.Description.Env (Ty.denote model.Carrier) fields)
    (slot : Ty.denote model.Carrier number) (target : Ty.denote model.Carrier index) :
    (Mettapedia.TypeTheory.FiniteConstructorEncoding.apply (Ty.denote model.Carrier) fields
      (handlerEquivalence model fields (model.denote (fieldGraph zero successor fields plan) environment slot target)) data).down ↔
      (Mettapedia.TypeTheory.OrderedPositionSegments.flatten
        (evaluateFields model numbers fields environment data plan))[numbers.symm slot]? = some target := by
  have law := abstractArguments_denote model fields
    (fun rho arguments => compileAt zero successor
      (fieldTerms fields plan (fun entry => rho (.vs (.vs entry))) arguments)
      (fun entry => .var entry) (rho (.vs .vz)) (rho .vz))
    (fun values data => ULift.up
      ((Mettapedia.TypeTheory.OrderedPositionSegments.flatten
        (evaluateFields model numbers fields (fun entry => values (.vs (.vs entry))) data plan))[numbers.symm (values (.vs .vz))]? = some (values .vz)))
    (by
      intro Ξ rho arguments values
      apply ULift.ext
      apply propext
      have exactLookup := compileAt_denote zero successor model numbers full arithmeticValues
        zero_preserved successor_preserved
        (fieldTerms fields plan (fun entry => rho (.vs (.vs entry))) arguments)
        values (fun entry => .var entry) (rho (.vs .vz)) (rho .vz) values (fun _ => rfl)
      rw [evaluate_fieldTerms] at exactLookup
      exact exactLookup)
    (model.extend (model.extend environment slot) target) data
  exact Iff.of_eq (congrArg ULift.down law)

#print axioms fieldGraph_denote

#print axioms graph_functional
#print axioms graph_active_iff
#print axioms graph_substitute
#print axioms graph_denote

#print axioms compileAt_subst
#print axioms compileAt_denote
end Mettapedia.Logic.HOL.OrderedPositionPrograms

namespace Mettapedia.Logic.HOL.IndexedConstructorGuards.PositionPrograms
open OrderedPositionPrograms
universe u v w
variable {Base : Type u} {Const : Ty Base → Type v} {Γ : Ctx Base}

/-- Every constructor uses the same segment compiler and its own field telescope. -/
def ofSegments (constructors : ConstructorPrograms Const Γ)
    (zero : ClosedTerm Const constructors.number) (successor : ClosedTerm Const (constructors.number ⇒ constructors.number))
    (plans : (occurrence : Fin constructors.fields.length) →
      FieldPlan Const Γ (constructors.fields.get occurrence) constructors.number constructors.index) :
    PositionPrograms constructors where
  graph := fun occurrence => fieldGraph zero successor _ (plans occurrence)

theorem ofSegments_related (constructors : ConstructorPrograms Const Γ)
    (zero : ClosedTerm Const constructors.number) (successor : ClosedTerm Const (constructors.number ⇒ constructors.number))
    (plans : (occurrence : Fin constructors.fields.length) →
      FieldPlan Const Γ (constructors.fields.get occurrence) constructors.number constructors.index)
    (model : HenkinModel.{u,v,w} Base Const) (numbers : Nat ≃ Ty.denote model.Carrier constructors.number)
    (full : model.FullDomains) (arithmeticValues : model.Valuation [])
    (zero_preserved : model.denote zero arithmeticValues = numbers 0)
    (successor_preserved : ∀ n, model.denote successor arithmeticValues (numbers n) = numbers (n + 1))
    (values : model.Valuation Γ) (data : constructors.Data model)
    (slot : Ty.denote model.Carrier constructors.number) (target : Ty.denote model.Carrier constructors.index) :
    (ofSegments constructors zero successor plans).related model values data slot target ↔
      (Mettapedia.TypeTheory.OrderedPositionSegments.flatten
        (evaluateFields model numbers _ values data.2 (plans data.1)))[numbers.symm slot]? = some target :=
  fieldGraph_denote zero successor model numbers full arithmeticValues zero_preserved successor_preserved
    _ (plans data.1) values data.2 slot target

#print axioms ofSegments_related
end Mettapedia.Logic.HOL.IndexedConstructorGuards.PositionPrograms
