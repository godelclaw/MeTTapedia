import Mettapedia.Languages.Megalodon.NaturalRecursionEvidence
import Mettapedia.Languages.Megalodon.NaturalClosure
import Mettapedia.Logic.HOL.Soundness

/-!
# The generated recursion graph and its selected native evidence

The graph has an independent inductive presentation. Its encoding quantifies
only over the selected interpretation's predicates. Canonical carrier facts,
choice availability and full-domain assumptions stay on the comparisons that
use them; they are not supplied by proof publication.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Megalodon.NaturalRecursion

open Mettapedia.Logic.HOL
open MathdataKernel

universe u v w

/-- The mathematical graph is specified independently of the proof syntax. -/
inductive Graph {N : Type u} {A : Type v} (zero : N) (successor : N → N)
    (start : A) (step : N → A → A) : N → A → Prop where
  | zero : Graph zero successor start step zero start
  | successor {number : N} {value : A} : Graph zero successor start step number value →
      Graph zero successor start step (successor number) (step number value)

section Graph

variable {N : Type u} {A : Type v} {zero : N} {successor : N → N}
  {start : A} {step : N → A → A}

theorem Graph.fold {predicate : N → A → Prop} (initial : predicate zero start)
    (closed : ∀ number value, predicate number value → predicate (successor number) (step number value))
    {number : N} {value : A} (graph : Graph zero successor start step number value) :
    predicate number value := by
  induction graph with
  | zero => exact initial
  | @successor number value graph ih => exact closed number value ih

theorem Graph.zero_value (different : ∀ number, successor number ≠ zero)
    {number : N} {value : A} (graph : Graph zero successor start step number value)
    (atZero : number = zero) : value = start := by
  cases graph with
  | zero => rfl
  | successor graph => exact (different _ atZero).elim

theorem Graph.successor_value (different : ∀ number, successor number ≠ zero)
    (injective : Function.Injective successor) {number : N} {value : A}
    (graph : Graph zero successor start step number value)
    (previous : N) (atSuccessor : number = successor previous) :
    ∃ prior, Graph zero successor start step previous prior ∧ value = step previous prior := by
  cases graph with
  | zero => exact (different previous atSuccessor.symm).elim
  | @successor current prior graph =>
      have same := injective atSuccessor
      cases same
      exact ⟨prior, graph, rfl⟩

theorem Graph.functional (different : ∀ number, successor number ≠ zero)
    (injective : Function.Injective successor) {number : N} {left right : A}
    (first : Graph zero successor start step number left)
    (second : Graph zero successor start step number right) : left = right := by
  induction first generalizing right with
  | zero => exact (second.zero_value different rfl).symm
  | @successor number left first ih =>
      obtain ⟨prior, priorGraph, same⟩ := second.successor_value different injective number rfl
      rw [same, ih priorGraph]

/-- Graph induction proves agreement with any solution on the generated carrier. -/
theorem Graph.agrees (candidate : N → A) (atZero : candidate zero = start)
    (atSuccessor : ∀ number value, Graph zero successor start step number value →
      candidate (successor number) = step number (candidate number))
    {number : N} {value : A} (graph : Graph zero successor start step number value) :
    value = candidate number := by
  induction graph with
  | zero => exact atZero.symm
  | @successor number value graph ih => rw [atSuccessor number value graph, ih]

theorem Graph.generated {number : N} {value : A}
    (graph : Graph zero successor start step number value)
    (predicate : N → Prop) (initial : predicate zero)
    (closed : ∀ n, predicate n → predicate (successor n)) : predicate number :=
  graph.fold initial (fun n _ prior => closed n prior)

theorem Graph.exists_of_generated {number : N}
    (generated : ∀ predicate : N → Prop, predicate zero →
      (∀ n, predicate n → predicate (successor n)) → predicate number) :
    ∃ value, Graph zero successor start step number value :=
  generated (fun n => ∃ value, Graph zero successor start step n value) ⟨start, .zero⟩
    (fun _ ⟨value, graph⟩ => ⟨step _ value, .successor graph⟩)

def selected (choose : (A → Prop) → A) (zero : N) (successor : N → N)
    (start : A) (step : N → A → A) (number : N) : A :=
  choose (Graph zero successor start step number)

theorem selected_graph (choose : (A → Prop) → A)
    (selects : ∀ predicate : A → Prop, (∃ value, predicate value) → predicate (choose predicate))
    {number : N} (generated : ∀ predicate : N → Prop, predicate zero →
      (∀ n, predicate n → predicate (successor n)) → predicate number) :
    Graph zero successor start step number (selected choose zero successor start step number) :=
  selects _ (Graph.exists_of_generated generated)

theorem selected_zero (choose : (A → Prop) → A)
    (selects : ∀ predicate : A → Prop, (∃ value, predicate value) → predicate (choose predicate))
    (different : ∀ number, successor number ≠ zero) :
    selected choose zero successor start step zero = start :=
  (selected_graph choose selects (fun _ initial _ => initial)).zero_value different rfl

theorem selected_successor (choose : (A → Prop) → A)
    (selects : ∀ predicate : A → Prop, (∃ value, predicate value) → predicate (choose predicate))
    (different : ∀ number, successor number ≠ zero) (injective : Function.Injective successor)
    {number : N} (generated : ∀ predicate : N → Prop, predicate zero →
      (∀ n, predicate n → predicate (successor n)) → predicate number) :
    selected choose zero successor start step (successor number) =
      step number (selected choose zero successor start step number) := by
  have current := selected_graph (start := start) (step := step) choose selects generated
  have next := selected_graph (start := start) (step := step) choose selects
    (fun predicate initial closed => closed number (generated predicate initial closed))
  exact next.functional different injective (.successor current)

theorem selected_unique (choose : (A → Prop) → A)
    (selects : ∀ predicate : A → Prop, (∃ value, predicate value) → predicate (choose predicate))
    (candidate : N → A) (atZero : candidate zero = start)
    (atSuccessor : ∀ number,
      (∀ predicate : N → Prop, predicate zero →
        (∀ n, predicate n → predicate (successor n)) → predicate number) →
      candidate (successor number) = step number (candidate number))
    {number : N} (generated : ∀ predicate : N → Prop, predicate zero →
      (∀ n, predicate n → predicate (successor n)) → predicate number) :
    selected choose zero successor start step number = candidate number := by
  apply (selected_graph choose selects generated).agrees candidate atZero
  intro number value graph
  exact atSuccessor number graph.generated

end Graph

section Syntax

variable {Base : Type u} {Const : Ty Base → Type v} {Γ : Ctx Base}

private theorem denote_application (model : HenkinModel.{u, v, w} Base Const)
    {A B : Ty Base} (valuation : model.Valuation Γ)
    (function : Term Const Γ (A ⇒ B)) (argument : Term Const Γ A) :
    model.denote (.app function argument) valuation =
      model.denote function valuation (model.denote argument valuation) := rfl

private theorem denote_lambda (model : HenkinModel.{u, v, w} Base Const)
    {A B : Ty Base} (valuation : model.Valuation Γ)
    (body : Term Const (A :: Γ) B) (value : Ty.denote model.Carrier A) :
    model.denote (.lam body) valuation value =
      model.denote body (model.extend valuation value) := rfl

def falseBody : Formula Const Γ := .all (σ := .prop) (.var .vz)

def equalityBody (A : Ty Base) : Term Const Γ (A ⇒ A ⇒ .prop) :=
  .lam (.lam (.all (σ := A ⇒ .prop)
    (.imp (.app (.var .vz) (.var (.vs (.vs .vz))))
      (.app (.var .vz) (.var (.vs .vz))))))

def equality {A : Ty Base} (left right : Term Const Γ A) : Formula Const Γ :=
  .app (.app (equalityBody A) left) right

def existsBody (A : Ty Base) : Term Const Γ ((A ⇒ .prop) ⇒ .prop) :=
  .lam (.all (σ := .prop)
    (.imp (.all (σ := A) (.imp (.app (.var (.vs (.vs .vz))) (.var .vz)) (.var (.vs .vz))))
      (.var .vz)))

def existential {A : Ty Base} (predicate : Term Const Γ (A ⇒ .prop)) : Formula Const Γ :=
  .app (existsBody A) predicate

def conjunctionBody : Term Const Γ (.prop ⇒ .prop ⇒ .prop) :=
  .lam (.lam (.all (σ := .prop)
    (.imp (.imp (.var (.vs (.vs .vz))) (.imp (.var (.vs .vz)) (.var .vz))) (.var .vz))))

def conjunction (left right : Formula Const Γ) : Formula Const Γ :=
  .app (.app conjunctionBody left) right

theorem denote_false (model : HenkinModel.{u, v, w} Base Const) (valuation : model.Valuation Γ) :
    (model.denote falseBody valuation).down ↔ False := by
  constructor
  · intro all
    exact all ⟨False⟩ (model.prop_mem _)
  · intro impossible
    exact impossible.elim

theorem denote_equality (model : HenkinModel.{u, v, w} Base Const) (full : model.FullDomains)
    {A : Ty Base} (valuation : model.Valuation Γ) (left right : Term Const Γ A) :
    (model.denote (equality left right) valuation).down ↔
      model.denote left valuation = model.denote right valuation := by
  constructor
  · intro equal
    exact (equal (fun value => ⟨value = model.denote left valuation⟩) (full _ _) rfl).symm
  · intro equal predicate _ holds
    change (predicate (model.denote right valuation)).down
    rw [← equal]
    exact holds

theorem denote_existential (model : HenkinModel.{u, v, w} Base Const) (full : model.FullDomains)
    {A : Ty Base} (valuation : model.Valuation Γ) (predicate : Term Const Γ (A ⇒ .prop)) :
    (model.denote (existential predicate) valuation).down ↔
      ∃ value, (model.denote predicate valuation value).down := by
  constructor
  · intro inhabited
    exact inhabited ⟨∃ value, (model.denote predicate valuation value).down⟩
      (model.prop_mem _) (fun value _ holds => ⟨value, holds⟩)
  · rintro ⟨value, holds⟩ property _ eliminate
    exact eliminate value (full _ _) holds

theorem denote_conjunction (model : HenkinModel.{u, v, w} Base Const)
    (valuation : model.Valuation Γ) (left right : Formula Const Γ) :
    (model.denote (conjunction left right) valuation).down ↔
      (model.denote left valuation).down ∧ (model.denote right valuation).down := by
  constructor
  · intro both
    exact both ⟨(model.denote left valuation).down ∧ (model.denote right valuation).down⟩
      (model.prop_mem _) (fun hleft hright => ⟨hleft, hright⟩)
  · rintro ⟨hleft, hright⟩ property _ eliminate
    exact eliminate hleft hright

/-- The same graph, written in the maintained intrinsic HOL syntax. -/
def graphBody (N A : Ty Base) : Term Const Γ
    (N ⇒ (N ⇒ N) ⇒ A ⇒ (N ⇒ A ⇒ A) ⇒ N ⇒ A ⇒ .prop) :=
  .lam (.lam (.lam (.lam (.lam (.lam (.all (σ := N ⇒ A ⇒ .prop)
    (.imp
      (.app (.app (.var .vz) (.var (.vs (.vs (.vs (.vs (.vs (.vs .vz))))))))
        (.var (.vs (.vs (.vs (.vs .vz))))))
      (.imp
        (.all (σ := N) (.all (σ := A)
          (.imp (.app (.app (.var (.vs (.vs .vz))) (.var (.vs .vz))) (.var .vz))
            (.app (.app (.var (.vs (.vs .vz)))
                (.app (.var (.vs (.vs (.vs (.vs (.vs (.vs (.vs .vz)))))))) (.var (.vs .vz))))
              (.app (.app (.var (.vs (.vs (.vs (.vs (.vs .vz)))))) (.var (.vs .vz))) (.var .vz))))))
        (.app (.app (.var .vz) (.var (.vs (.vs .vz)))) (.var (.vs .vz)))))))))))

def graphPredicate {N A : Ty Base} (zero : Term Const Γ N)
    (successor : Term Const Γ (N ⇒ N)) (start : Term Const Γ A)
    (step : Term Const Γ (N ⇒ A ⇒ A)) (number : Term Const Γ N) (value : Term Const Γ A) :
    Formula Const Γ :=
  .app (.app (.app (.app (.app (.app (graphBody N A) zero) successor) start) step) number) value

def zeroExcluded {N : Ty Base} (zero : Term Const Γ N) (successor : Term Const Γ (N ⇒ N)) :
    Formula Const Γ :=
  .all (σ := N) (.imp (equality (.app (weaken successor) (.var .vz)) (weaken zero)) falseBody)

def successorInjective {N : Ty Base} (successor : Term Const Γ (N ⇒ N)) : Formula Const Γ :=
  .all (σ := N) (.all (σ := N)
    (.imp (equality (.app (weaken (weaken successor)) (.var (.vs .vz)))
      (.app (weaken (weaken successor)) (.var .vz)))
      (equality (.var (.vs .vz)) (.var .vz))))

def choiceCondition {A : Ty Base} (choose : Term Const Γ ((A ⇒ .prop) ⇒ A)) : Formula Const Γ :=
  .all (σ := A ⇒ .prop) (.imp (existential (.var .vz))
    (.app (.var .vz) (.app (weaken choose) (.var .vz))))

def zeroEquation {N A : Ty Base} (zero : Term Const Γ N) (start : Term Const Γ A)
    (candidate : Term Const Γ (N ⇒ A)) : Formula Const Γ :=
  equality start (.app candidate zero)

def stepEquation {N A : Ty Base} (zero : Term Const Γ N) (successor : Term Const Γ (N ⇒ N))
    (step : Term Const Γ (N ⇒ A ⇒ A)) (candidate : Term Const Γ (N ⇒ A)) : Formula Const Γ :=
  .all (σ := N) (.imp (Mettapedia.Logic.HOL.NaturalClosure.predicate (weaken zero) (weaken successor) (.var .vz))
    (equality (.app (.app (weaken step) (.var .vz)) (.app (weaken candidate) (.var .vz)))
      (.app (weaken candidate) (.app (weaken successor) (.var .vz)))))

def agreement {N A : Ty Base} (zero : Term Const Γ N) (successor : Term Const Γ (N ⇒ N))
    (first second : Term Const Γ (N ⇒ A)) : Formula Const Γ :=
  .all (σ := N) (.imp (Mettapedia.Logic.HOL.NaturalClosure.predicate (weaken zero) (weaken successor) (.var .vz))
    (equality (.app (weaken first) (.var .vz)) (.app (weaken second) (.var .vz))))

def uniqueness {N A : Ty Base} (zero : Term Const Γ N) (successor : Term Const Γ (N ⇒ N))
    (start : Term Const Γ A) (step : Term Const Γ (N ⇒ A ⇒ A)) (candidate : Term Const Γ (N ⇒ A)) :
    Formula Const Γ :=
  .all (σ := N ⇒ A) (.imp (zeroEquation (weaken zero) (weaken start) (.var .vz))
    (.imp (stepEquation (weaken zero) (weaken successor) (weaken step) (.var .vz))
      (agreement (weaken zero) (weaken successor) (weaken candidate) (.var .vz))))

def recursionProperty {N A : Ty Base} (zero : Term Const Γ N) (successor : Term Const Γ (N ⇒ N))
    (start : Term Const Γ A) (step : Term Const Γ (N ⇒ A ⇒ A)) (candidate : Term Const Γ (N ⇒ A)) :
    Formula Const Γ :=
  conjunction (zeroEquation zero start candidate)
    (conjunction (stepEquation zero successor step candidate) (uniqueness zero successor start step candidate))

/-- This statement independently specifies the equations and agreement on
the generated carrier. It does not equate arbitrary extensions outside it. -/
def recursionStatement (N A : Ty Base) : ClosedFormula Const :=
  .all (σ := N) (.all (σ := N ⇒ N)
    (.imp (zeroExcluded (.var (.vs .vz)) (.var .vz))
      (.imp (successorInjective (.var .vz))
        (.all (σ := A) (.all (σ := N ⇒ A ⇒ A) (.all (σ := (A ⇒ .prop) ⇒ A)
          (.imp (choiceCondition (.var .vz))
            (existential (.lam (recursionProperty
              (.var (.vs (.vs (.vs (.vs (.vs .vz))))))
              (.var (.vs (.vs (.vs (.vs .vz)))))
              (.var (.vs (.vs (.vs .vz))))
              (.var (.vs (.vs .vz))) (.var .vz)))))))))))

/-- In a full-domain interpretation, the encoded least graph is exactly
the independently specified inductive graph. -/
theorem denote_graph_iff (model : HenkinModel.{u, v, w} Base Const)
    (full : model.FullDomains) {N A : Ty Base} (valuation : model.Valuation Γ)
    (zero : Term Const Γ N) (successor : Term Const Γ (N ⇒ N)) (start : Term Const Γ A)
    (step : Term Const Γ (N ⇒ A ⇒ A)) (number : Term Const Γ N) (value : Term Const Γ A) :
    (model.denote (graphPredicate zero successor start step number value) valuation).down ↔
      Graph (model.denote zero valuation) (model.denote successor valuation)
        (model.denote start valuation) (model.denote step valuation)
        (model.denote number valuation) (model.denote value valuation) := by
  constructor
  · intro encoded
    let relation : Ty.denote model.Carrier (N ⇒ A ⇒ .prop) :=
      fun n a => ⟨Graph (model.denote zero valuation) (model.denote successor valuation)
        (model.denote start valuation) (model.denote step valuation) n a⟩
    exact encoded relation (full _ _) Graph.zero (by
      intro n _ a _ prior
      exact Graph.successor prior)
  · intro graph relation _ initial closed
    exact graph.fold initial (fun n a prior => closed n (full _ _) a (full _ _) prior)

theorem denote_stepEquation (model : HenkinModel.{u, v, w} Base Const) (full : model.FullDomains)
    {N A : Ty Base} (valuation : model.Valuation Γ) (zero : Term Const Γ N)
    (successor : Term Const Γ (N ⇒ N)) (step : Term Const Γ (N ⇒ A ⇒ A))
    (candidate : Term Const Γ (N ⇒ A)) :
    (model.denote (stepEquation zero successor step candidate) valuation).down ↔
      ∀ number, Mettapedia.Logic.HOL.NaturalClosure.ClosedUnder model N (model.denote zero valuation)
        (model.denote successor valuation) number →
        model.denote step valuation number (model.denote candidate valuation number) =
          model.denote candidate valuation (model.denote successor valuation number) := by
  have admitted : ∀ (type : Ty Base) (value : Ty.denote model.Carrier type),
      model.adm type value := full
  simp only [stepEquation, PreModel.denote_all, PreModel.denote_imp,
    denote_equality model full, Mettapedia.Logic.HOL.NaturalClosure.denote_predicate, denote_application,
    PreModel.denote_var, Soundness.denote_weaken, PreModel.extend, admitted, forall_true_left]

theorem denote_agreement (model : HenkinModel.{u, v, w} Base Const) (full : model.FullDomains)
    {N A : Ty Base} (valuation : model.Valuation Γ) (zero : Term Const Γ N)
    (successor : Term Const Γ (N ⇒ N)) (first second : Term Const Γ (N ⇒ A)) :
    (model.denote (agreement zero successor first second) valuation).down ↔
      ∀ number, Mettapedia.Logic.HOL.NaturalClosure.ClosedUnder model N (model.denote zero valuation)
        (model.denote successor valuation) number →
        model.denote first valuation number = model.denote second valuation number := by
  have admitted : ∀ (type : Ty Base) (value : Ty.denote model.Carrier type),
      model.adm type value := full
  simp only [agreement, PreModel.denote_all, PreModel.denote_imp,
    denote_equality model full, Mettapedia.Logic.HOL.NaturalClosure.denote_predicate, denote_application,
    PreModel.denote_var, Soundness.denote_weaken, PreModel.extend, admitted, forall_true_left]

theorem denote_uniqueness (model : HenkinModel.{u, v, w} Base Const) (full : model.FullDomains)
    {N A : Ty Base} (valuation : model.Valuation Γ) (zero : Term Const Γ N)
    (successor : Term Const Γ (N ⇒ N)) (start : Term Const Γ A)
    (step : Term Const Γ (N ⇒ A ⇒ A)) (candidate : Term Const Γ (N ⇒ A)) :
    (model.denote (uniqueness zero successor start step candidate) valuation).down ↔
      ∀ other : Ty.denote model.Carrier (N ⇒ A),
        model.denote start valuation = other (model.denote zero valuation) →
        (∀ number, Mettapedia.Logic.HOL.NaturalClosure.ClosedUnder model N (model.denote zero valuation)
          (model.denote successor valuation) number →
          model.denote step valuation number (other number) =
            other (model.denote successor valuation number)) →
        ∀ number, Mettapedia.Logic.HOL.NaturalClosure.ClosedUnder model N (model.denote zero valuation)
          (model.denote successor valuation) number →
          model.denote candidate valuation number = other number := by
  have admitted : ∀ (type : Ty Base) (value : Ty.denote model.Carrier type),
      model.adm type value := full
  simp only [uniqueness, PreModel.denote_all, PreModel.denote_imp,
    zeroEquation, denote_equality model full, denote_stepEquation model full,
    denote_agreement model full, denote_application, PreModel.denote_var,
    Soundness.denote_weaken, PreModel.extend, admitted, forall_true_left]

theorem denote_zeroExcluded (model : HenkinModel.{u, v, w} Base Const) (full : model.FullDomains)
    {N : Ty Base} (valuation : model.Valuation Γ) (zero : Term Const Γ N)
    (successor : Term Const Γ (N ⇒ N)) :
    (model.denote (zeroExcluded zero successor) valuation).down ↔
      ∀ number, model.denote successor valuation number ≠ model.denote zero valuation := by
  have admitted : ∀ (type : Ty Base) (value : Ty.denote model.Carrier type),
      model.adm type value := full
  simp only [zeroExcluded, PreModel.denote_all, PreModel.denote_imp,
    denote_equality model full, denote_false, denote_application,
    Soundness.denote_weaken, PreModel.denote_var, PreModel.extend, admitted, forall_true_left]

theorem denote_successorInjective (model : HenkinModel.{u, v, w} Base Const)
    (full : model.FullDomains) {N : Ty Base} (valuation : model.Valuation Γ)
    (successor : Term Const Γ (N ⇒ N)) :
    (model.denote (successorInjective successor) valuation).down ↔
      Function.Injective (model.denote successor valuation) := by
  have admitted : ∀ (type : Ty Base) (value : Ty.denote model.Carrier type),
      model.adm type value := full
  simp only [successorInjective, Function.Injective, PreModel.denote_all,
    PreModel.denote_imp, denote_equality model full, denote_application,
    Soundness.denote_weaken, PreModel.denote_var, PreModel.extend, admitted, forall_true_left]

theorem denote_choiceCondition (model : HenkinModel.{u, v, w} Base Const)
    (full : model.FullDomains) {A : Ty Base} (valuation : model.Valuation Γ)
    (choose : Term Const Γ ((A ⇒ .prop) ⇒ A)) :
    (model.denote (choiceCondition choose) valuation).down ↔
      ∀ predicate : Ty.denote model.Carrier (A ⇒ .prop),
        (∃ value, (predicate value).down) →
        (predicate (model.denote choose valuation predicate)).down := by
  have admitted : ∀ (type : Ty Base) (value : Ty.denote model.Carrier type),
      model.adm type value := full
  simp only [choiceCondition, PreModel.denote_all, PreModel.denote_imp,
    denote_existential model full, denote_application, Soundness.denote_weaken,
    PreModel.denote_var, PreModel.extend, admitted, forall_true_left]

theorem denote_recursionProperty (model : HenkinModel.{u, v, w} Base Const)
    (full : model.FullDomains) {N A : Ty Base} (valuation : model.Valuation Γ)
    (zero : Term Const Γ N) (successor : Term Const Γ (N ⇒ N)) (start : Term Const Γ A)
    (step : Term Const Γ (N ⇒ A ⇒ A)) (candidate : Term Const Γ (N ⇒ A)) :
    (model.denote (recursionProperty zero successor start step candidate) valuation).down ↔
      model.denote start valuation = model.denote candidate valuation (model.denote zero valuation) ∧
      (∀ number, Mettapedia.Logic.HOL.NaturalClosure.ClosedUnder model N (model.denote zero valuation)
        (model.denote successor valuation) number →
        model.denote step valuation number (model.denote candidate valuation number) =
          model.denote candidate valuation (model.denote successor valuation number)) ∧
      ∀ other : Ty.denote model.Carrier (N ⇒ A),
        model.denote start valuation = other (model.denote zero valuation) →
        (∀ number, Mettapedia.Logic.HOL.NaturalClosure.ClosedUnder model N (model.denote zero valuation)
          (model.denote successor valuation) number →
          model.denote step valuation number (other number) =
            other (model.denote successor valuation number)) →
        ∀ number, Mettapedia.Logic.HOL.NaturalClosure.ClosedUnder model N (model.denote zero valuation)
          (model.denote successor valuation) number →
          model.denote candidate valuation number = other number := by
  simp only [recursionProperty, denote_conjunction, zeroEquation, denote_equality model full,
    denote_application, denote_stepEquation model full, denote_uniqueness model full]

theorem closed_iff_generated (model : HenkinModel.{u, v, w} Base Const)
    (full : model.FullDomains) (N : Ty Base) (zero : Ty.denote model.Carrier N)
    (successor : Ty.denote model.Carrier (N ⇒ N)) (number : Ty.denote model.Carrier N) :
    Mettapedia.Logic.HOL.NaturalClosure.ClosedUnder model N zero successor number ↔
      ∀ predicate : Ty.denote model.Carrier N → Prop, predicate zero →
        (∀ n, predicate n → predicate (successor n)) → predicate number := by
  constructor
  · intro closed predicate initial step
    exact closed (fun n => .up (predicate n)) (full _ _) initial (fun n _ => step n)
  · intro generated predicate _ initial step
    exact generated (fun n => (predicate n).down) initial (fun n => step n (full _ _))

/-- The encoded theorem retains its successor and selector interfaces. The
full-domain comparison concerns meaning, independently of native replay. -/
theorem models_recursion (model : HenkinModel.{u, v, w} Base Const)
    (full : model.FullDomains) (N A : Ty Base) : model.models (recursionStatement N A) := by
  have admitted : ∀ (type : Ty Base) (value : Ty.denote model.Carrier type),
      model.adm type value := full
  change (model.denote (recursionStatement N A) (fun index => nomatch index)).down
  simp only [recursionStatement, PreModel.denote_all, PreModel.denote_imp,
    denote_zeroExcluded model full, denote_successorInjective model full,
    denote_choiceCondition model full, denote_existential model full, denote_lambda,
    denote_recursionProperty model full, PreModel.denote_var, PreModel.extend,
    admitted, forall_true_left]
  intro zero successor different injective start step choose selects
  let selector := fun predicate : Ty.denote model.Carrier A → Prop =>
    choose (fun value => .up (predicate value))
  have selects' : ∀ predicate : Ty.denote model.Carrier A → Prop,
      (∃ value, predicate value) → predicate (selector predicate) :=
    fun predicate inhabited => selects (fun value => .up (predicate value)) inhabited
  refine ⟨selected selector zero successor start step, ?_, ?_, ?_⟩
  · exact (selected_zero selector selects' different).symm
  · intro number closed
    exact (selected_successor selector selects' different injective
      ((closed_iff_generated model full N zero successor number).mp closed)).symm
  · intro candidate atZero atSuccessor number closed
    exact selected_unique selector selects' candidate atZero.symm
      (fun n generated => (atSuccessor n
        ((closed_iff_generated model full N zero successor n).mpr generated)).symm)
      ((closed_iff_generated model full N zero successor number).mp closed)

end Syntax

section SourceDefinitions

open HenkinTermInterpretation

private abbrev SourceBase := HenkinTermInterpretation.Base
private abbrev SourceConst := Constant ({} : Environment)
private abbrev N : Ty SourceBase := .base (.inr 0)
private abbrev A : Ty SourceBase := .base (.inl 0)

/-- The typed reference and the independently emitted source data have
different origins; this comparison checks the actual definition's binders. -/
theorem graph_source_definition :
    ∃ body, erase (graphBody N A (Const := SourceConst) (Γ := [])) = some body ∧
      Evidence.nrGraph = .definition
        "ad9228a14dce06c1cbff1f7336645797c843930d4066a43ea8871617dbd5e688"
        (.all (reifyType (N ⇒ (N ⇒ N) ⇒ A ⇒ (N ⇒ A ⇒ A) ⇒ N ⇒ A ⇒ .prop)))
        (.typeLam body) := by
  exact ⟨_, rfl, rfl⟩

theorem equality_source_definition :
    ∃ body, erase (equalityBody A (Const := SourceConst) (Γ := [])) = some body ∧
      Evidence.nrEq = .definition
        "0e7f6a08bb4627c0ddedda9151c907864644724fa34b3e850be0bfb73ba13e89"
        (.all (reifyType (A ⇒ A ⇒ .prop))) (.typeLam body) := by
  exact ⟨_, rfl, rfl⟩

theorem existential_source_definition :
    ∃ body, erase (existsBody A (Const := SourceConst) (Γ := [])) = some body ∧
      Evidence.nrExists = .definition
        "912ad2cdc2d23bb8aa0a5070945f2a90976a948b0e8308917244591f3747f099"
        (.all (reifyType ((A ⇒ .prop) ⇒ .prop))) (.typeLam body) := by
  exact ⟨_, rfl, rfl⟩

theorem false_source_definition :
    ∃ body, erase (falseBody (Base := SourceBase) (Const := SourceConst) (Γ := [])) = some body ∧
      Evidence.nrFalse = .definition
        "5bf697cb0d1cdefbe881504469f6c48cc388994115b82514dfc4fb5e67ac1a87" .prop body := by
  exact ⟨_, rfl, rfl⟩

theorem conjunction_source_definition :
    ∃ body, erase (conjunctionBody (Base := SourceBase) (Const := SourceConst) (Γ := [])) = some body ∧
      Evidence.ncAnd = .definition
        "87fba1d2da67f06ec37e7ab47c3ef935ef8137209b42e40205afb5afd835b738"
        (.arr .prop (.arr .prop .prop)) body := by
  exact ⟨_, rfl, rfl⟩

end SourceDefinitions

/-- The native goal is erased from the independent, interpreted statement,
rather than copied from the upstream theorem record. -/
def nativeStatement : Tm := .typeAll
  ((HenkinTermInterpretation.erase
    (recursionStatement (.base (.inr 0 : HenkinTermInterpretation.Base)) (.base (.inl 0)) :
      ClosedFormula (HenkinTermInterpretation.Constant ({} : Environment)))).getD (.db 0))

def recursionName : Name := "c68747a1a75e217cf39d616a8d4b4d58b3cb63e8e0a2cedb9e8b17094aaae1f4"

theorem native_statement_erases :
    ∃ body, HenkinTermInterpretation.erase
      (recursionStatement (.base (.inr 0 : HenkinTermInterpretation.Base)) (.base (.inl 0)) :
        ClosedFormula (HenkinTermInterpretation.Constant ({} : Environment))) = some body ∧
      nativeStatement = .typeAll body := by
  exact ⟨_, rfl, rfl⟩

theorem native_statement_formed : checkProposition {} 0 [] nativeStatement = true := by decide

def authority : NativeAdmission.Authority := ⟨.egal, [], []⟩

/-- A bound derived from this finite input, not a service-wide cutoff. -/
def evidenceBudget : Nat := Evidence.inputBytes + 1

def replay : Option Environment := SourceAdmission.checkAll authority evidenceBudget {} Evidence.items

def forged : NativeAdmission.Item :=
  .theorem_ "forged_natural_recursion" (.all .prop (.db 0))
    (.known "c68747a1a75e217cf39d616a8d4b4d58b3cb63e8e0a2cedb9e8b17094aaae1f4")

def forgedRefused : Bool := match replay with
  | none => false
  | some environment => (SourceAdmission.admit authority evidenceBudget environment forged).isNone

def verdicts : List (String × Bool) := [
  ("independently typed recursion statement is formed", checkProposition {} 0 [] nativeStatement),
  ("complete source recursion proof batch checks", replay.isSome),
  ("the batch starts without admitted axioms", authority.known.isEmpty && authority.parameters.isEmpty),
  ("the batch retains every source definition and theorem", Evidence.items.length == 31),
  ("a missing definition cannot be supplied by later proofs",
    (SourceAdmission.checkAll authority evidenceBudget {} Evidence.items.tail).isNone),
  ("checking fuel exhaustion cannot publish a proof batch",
    (SourceAdmission.checkAll authority 0 {} Evidence.items).isNone),
  ("the recursion proof does not certify falsehood",
    forgedRefused)]

-- These are executable controls. A kernel replay certificate for the full
-- batch remains separate from the proved semantic and syntax comparisons.
end Mettapedia.Languages.Megalodon.NaturalRecursion
