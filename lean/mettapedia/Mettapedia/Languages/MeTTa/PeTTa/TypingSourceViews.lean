import Mettapedia.Languages.MeTTa.PeTTa.SynthesisCandidateComposition

/-!
# Source views used by relational typing

Arrow and Hold/Eval recognition inspect finite syntax. They never solve an
equation merely to make a tag or a missing list cell fit. A scheme variable
is classified as an inference position before later type substitution.

The executable views below are proved against syntactic source rules. The
arrow parser preserves the flat list of domains, including zero domains.
Grounded leaves stay distinct from symbols with the same printed spelling.
SWI's tests also exercise open Prolog spines, which this finite expression
encoding does not represent. Attributed readiness and the source reader
remain separate realization obligations.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.TypingSourceViews

open Mettapedia.Logic.LP

inductive Leaf (Value : Type) where
  | symbol (name : String)
  | grounded (value : Value)
  deriving DecidableEq

abbrev signature (Value Variable : Type) := ListTerms.signature (Leaf Value) Variable

variable {Value Variable : Type}
local notation "τ" => signature Value Variable
local notation "Ty" => Term τ

def symbol (name : String) : Ty := .const (.symbol name)

def symbolName : Ty → Option String
  | .const (.symbol name) => some name
  | _ => none

theorem symbolName_exact (type : Ty) (name : String) :
    symbolName type = some name ↔ type = symbol name := by
  cases type with
  | var _ => simp [symbolName,symbol]
  | const leaf => cases leaf <;> simp [symbolName,symbol]
  | app _ _ => simp [symbolName,symbol]

def arrow (domains : List Ty) (result : Ty) : Ty :=
  ListTerms.ofList (symbol "->" :: domains ++ [result])

def arrowParts (type : Ty) : Option (List Ty × Ty) :=
  match ListTerms.toList type with
  | some (head :: tail) =>
      if symbolName head = some "->" then
        tail.getLast?.map fun result => (tail.dropLast,result)
      else none
  | _ => none

theorem arrowParts_exact (type : Ty) (domains : List Ty) (result : Ty) :
    arrowParts type = some (domains,result) ↔ type = arrow domains result := by
  constructor
  · intro parsed
    unfold arrowParts at parsed
    cases viewed : ListTerms.toList type with
    | none => simp [viewed] at parsed
    | some elements =>
        cases elements with
        | nil => simp [viewed] at parsed
        | cons head tail =>
            simp only [viewed] at parsed
            split at parsed
            · rename_i tag
              have headEqual := (symbolName_exact head "->").mp tag
              cases last : tail.getLast? with
              | none => simp [last] at parsed
              | some value =>
                  simp only [last,Option.map_some,Option.some.injEq,Prod.mk.injEq] at parsed
                  obtain ⟨front,rfl⟩ := List.getLast?_eq_some_iff.mp last
                  simp only [List.dropLast_append_cons, List.dropLast_singleton,
                    List.append_nil] at parsed
                  obtain ⟨rfl,rfl⟩ := parsed
                  exact (ListTerms.toList_eq_some_iff type _).mp
                    (by simpa [headEqual,arrow] using viewed)
            · simp at parsed
  · rintro rfl
    simp [arrowParts,arrow,symbolName,symbol]

inductive Mode where
  | hold
  | eval
  deriving DecidableEq

inductive Wrapped : Ty → Mode → Ty → Prop where
  | hold (type : Ty) : Wrapped (ListTerms.ofList [symbol "Hold",type]) .hold type
  | eval (type : Ty) : Wrapped (ListTerms.ofList [symbol "Eval",type]) .eval type

def wrapper (source : Ty) : Option (Mode × Ty) :=
  match ListTerms.toList source with
  | some [tag,type] =>
      match symbolName tag with
      | some "Hold" => some (.hold,type)
      | some "Eval" => some (.eval,type)
      | _ => none
  | _ => none

theorem wrapper_exact (source : Ty) (mode : Mode) (type : Ty) :
    wrapper source = some (mode,type) ↔ Wrapped source mode type := by
  constructor
  · intro parsed
    unfold wrapper at parsed
    split at parsed
    · rename_i tag expected view
      have sourceEqual := (ListTerms.toList_eq_some_iff source [tag,expected]).mp view
      subst source
      split at parsed
      · rename_i name
        obtain rfl := (symbolName_exact tag "Hold").mp name
        obtain ⟨rfl,rfl⟩ := Option.some.inj parsed
        exact .hold type
      · rename_i name
        obtain rfl := (symbolName_exact tag "Eval").mp name
        obtain ⟨rfl,rfl⟩ := Option.some.inj parsed
        exact .eval type
      · contradiction
    · contradiction
  · intro wrapped
    cases wrapped <;> simp [wrapper,symbolName,symbol]

inductive Parameter : Ty → Mode → Ty → Prop where
  | wrapped {source type : Ty} {mode : Mode} :
      Wrapped source mode type → Parameter source mode type
  | atom : Parameter (symbol "Atom") .hold (symbol "Atom")
  | underscore : Parameter (symbol "_") .eval (symbol "Any")
  | undefined : Parameter (symbol "%Undefined%") .eval (symbol "Any")
  | ordinary (source : Ty) :
      (∀ mode type, ¬ Wrapped source mode type) →
      source ≠ symbol "Atom" → source ≠ symbol "_" → source ≠ symbol "%Undefined%" →
      Parameter source .eval source

def parameter (source : Ty) : Mode × Ty :=
  match wrapper source with
  | some result => result
  | none =>
      match symbolName source with
      | some "Atom" => (.hold,source)
      | some "_" | some "%Undefined%" => (.eval,symbol "Any")
      | _ => (.eval,source)

private theorem no_wrapper_of_symbol (name : String) (mode : Mode) (type : Ty) :
    ¬ Wrapped (symbol name) mode type := by
  rw [← wrapper_exact]
  simp [wrapper,symbol,ListTerms.toList]

theorem parameter_sound (source : Ty) :
    Parameter source (parameter source).1 (parameter source).2 := by
  cases wrapped : wrapper source with
  | some result =>
      simpa only [parameter,wrapped] using
        Parameter.wrapped ((wrapper_exact source result.1 result.2).mp wrapped)
  | none =>
      have noWrapper : ∀ mode type, ¬ Wrapped source mode type := by
        intro mode type proof
        have some := (wrapper_exact source mode type).mpr proof
        simp [wrapped] at some
      simp only [parameter,wrapped]
      split
      · rename_i name
        obtain rfl := (symbolName_exact source "Atom").mp name
        exact .atom
      · rename_i name
        obtain rfl := (symbolName_exact source "_").mp name
        exact .underscore
      · rename_i name
        obtain rfl := (symbolName_exact source "%Undefined%").mp name
        exact .undefined
      · rename_i notAtom notUnderscore notUndefined
        exact .ordinary source noWrapper
          (fun equal => notAtom (by simp [equal,symbolName,symbol]))
          (fun equal => notUnderscore (by simp [equal,symbolName,symbol]))
          (fun equal => notUndefined (by simp [equal,symbolName,symbol]))

theorem parameter_complete {source type : Ty} {mode : Mode}
    (typed : Parameter source mode type) : parameter source = (mode,type) := by
  cases typed with
  | wrapped proof => simp [parameter,(wrapper_exact _ _ _).mpr proof]
  | atom => simp [parameter,wrapper,ListTerms.toList,symbol,symbolName]
  | underscore => simp [parameter,wrapper,ListTerms.toList,symbol,symbolName]
  | undefined => simp [parameter,wrapper,ListTerms.toList,symbol,symbolName]
  | ordinary source noWrapper notAtom notUnderscore notUndefined =>
      have absent : wrapper source = none := by
        cases found : wrapper source with
        | none => rfl
        | some result => exact (noWrapper result.1 result.2
            ((wrapper_exact source result.1 result.2).mp found)).elim
      simp only [parameter,absent]
      split
      · rename_i tag; exact (notAtom ((symbolName_exact _ _).mp tag)).elim
      · rename_i tag; exact (notUnderscore ((symbolName_exact _ _).mp tag)).elim
      · rename_i tag; exact (notUndefined ((symbolName_exact _ _).mp tag)).elim
      · rfl

theorem parameter_exact (source : Ty) (mode : Mode) (type : Ty) :
    parameter source = (mode,type) ↔ Parameter source mode type := by
  constructor
  · intro same
    have sound := parameter_sound source
    simpa [same] using sound
  · exact parameter_complete

/-- Direction is chosen before a shared scheme is instantiated. -/
inductive Formal where
  | infer (type : Ty)
  | check (type : Ty)

def freeze : Ty → Formal (Value := Value) (Variable := Variable)
  | .var slot => .infer (.var slot)
  | other => .check other

inductive Frozen : Ty → Formal (Value := Value) (Variable := Variable) → Prop where
  | variable (slot : Variable) : Frozen (.var slot) (.infer (.var slot))
  | constant (leaf : Leaf Value) : Frozen (.const leaf) (.check (.const leaf))
  | expression (arity : Nat) (children : Fin arity → Ty) :
      Frozen (.app arity children) (.check (.app arity children))

theorem freeze_exact (source : Ty) (formal : Formal (Value := Value) (Variable := Variable)) :
    freeze source = formal ↔ Frozen source formal := by
  constructor
  · rintro rfl
    cases source with
    | var slot => exact .variable slot
    | const leaf => exact .constant leaf
    | app arity children => exact .expression arity children
  · intro frozen
    cases frozen <;> rfl

def Formal.refine (witness : Subst τ) :
    Formal (Value := Value) (Variable := Variable) → Formal (Value := Value) (Variable := Variable)
  | .infer type => .infer (witness.applyTerm type)
  | .check type => .check (witness.applyTerm type)

theorem inferred_direction_survives (witness : Subst τ) (slot : Variable) :
    (freeze (.var slot)).refine witness = .infer (witness slot) := rfl

theorem freezing_again_changes_meaning (slot : Variable) :
    (freeze (.var slot)).refine (fun _ => symbol "Any") ≠
      freeze (Subst.applyTerm (fun _ => symbol "Any" : Subst τ) (.var slot)) := by
  intro same
  cases same

section Renaming

open UnificationRenaming

variable (f g : Variable → Variable) (inverse : Function.LeftInverse g f)

theorem rename_symbol (name : String) : UnificationRenaming.rename f (symbol name : Ty) = symbol name := rfl

theorem rename_list (types : List Ty) :
    UnificationRenaming.rename f (ListTerms.ofList types) = ListTerms.ofList (types.map (UnificationRenaming.rename f)) :=
  ListTerms.apply_ofList _ types

theorem rename_arrow (domains : List Ty) (result : Ty) :
    UnificationRenaming.rename f (arrow domains result) = arrow (domains.map (UnificationRenaming.rename f)) (UnificationRenaming.rename f result) := by
  simp [arrow,rename_list,rename_symbol]

theorem Wrapped.rename {source type : Ty} {mode : Mode}
    (wrapped : Wrapped source mode type) : Wrapped (UnificationRenaming.rename f source) mode (UnificationRenaming.rename f type) := by
  cases wrapped with
  | hold type => simpa only [rename_list,List.map_cons,List.map_nil,rename_symbol] using
      Wrapped.hold (UnificationRenaming.rename f type)
  | eval type => simpa only [rename_list,List.map_cons,List.map_nil,rename_symbol] using
      Wrapped.eval (UnificationRenaming.rename f type)

include g inverse in
theorem wrapper_renaming (source : Ty) :
    wrapper (UnificationRenaming.rename f source) = (wrapper source).map (fun (mode,type) => (mode,UnificationRenaming.rename f type)) := by
  cases original : wrapper source with
  | some pair =>
      simpa only [Option.map_some] using (wrapper_exact _ _ _).mpr
        (((wrapper_exact source pair.1 pair.2).mp original).rename f)
  | none =>
      cases renamed : wrapper (UnificationRenaming.rename f source) with
      | none => rfl
      | some pair =>
          have back := ((wrapper_exact _ _ _).mp renamed).rename g
          rw [rename_leftInverse (σ := τ) f g inverse] at back
          have impossible := (wrapper_exact _ _ _).mpr back
          simp [original] at impossible

include g inverse in
theorem Parameter.rename {source type : Ty} {mode : Mode}
    (typed : Parameter source mode type) : Parameter (UnificationRenaming.rename f source) mode (UnificationRenaming.rename f type) := by
  cases typed with
  | wrapped proof => exact .wrapped (proof.rename f)
  | atom => exact .atom
  | underscore => exact .underscore
  | undefined => exact .undefined
  | ordinary source noWrapper notAtom notUnderscore notUndefined =>
      have reflect (name : String) (distinct : source ≠ symbol name) :
          UnificationRenaming.rename f source ≠ symbol name := by
        intro equal
        have back := congrArg (UnificationRenaming.rename (σ := τ) g) equal
        rw [rename_leftInverse (σ := τ) f g inverse] at back
        exact distinct back
      refine .ordinary _ ?_ (reflect "Atom" notAtom)
        (reflect "_" notUnderscore) (reflect "%Undefined%" notUndefined)
      intro mode type wrapped
      have back := wrapped.rename g
      rw [rename_leftInverse (σ := τ) f g inverse] at back
      exact noWrapper _ _ back

include g inverse in
theorem parameter_renaming (source : Ty) :
    parameter (UnificationRenaming.rename f source) = ((parameter source).1,UnificationRenaming.rename f (parameter source).2) :=
  parameter_complete ((parameter_sound source).rename f g inverse)

include g inverse in
theorem arrowParts_renaming (source : Ty) :
    arrowParts (UnificationRenaming.rename f source) =
      (arrowParts source).map (fun (domains,result) =>
        (domains.map (UnificationRenaming.rename f),UnificationRenaming.rename f result)) := by
  cases original : arrowParts source with
  | some pair =>
      obtain rfl := (arrowParts_exact source pair.1 pair.2).mp original
      rw [rename_arrow]
      simpa only [Option.map_some] using (arrowParts_exact _ _ _).mpr rfl
  | none =>
      cases renamed : arrowParts (UnificationRenaming.rename f source) with
      | none => rfl
      | some pair =>
          have back := congrArg (UnificationRenaming.rename (σ := τ) g)
            ((arrowParts_exact _ _ _).mp renamed)
          rw [rename_leftInverse (σ := τ) f g inverse,rename_arrow] at back
          have impossible := (arrowParts_exact _ _ _).mpr back
          simp [original] at impossible

theorem freeze_renaming (source : Ty) :
    freeze (UnificationRenaming.rename f source) = (freeze source).refine (fun slot => .var (f slot)) := by
  cases source <;> rfl

end Renaming

structure ParameterPlan where
  mode : Mode
  formal : Formal (Value := Value) (Variable := Variable)

def parameterPlan (source : Ty) : ParameterPlan (Value := Value) (Variable := Variable) :=
  let (mode,type) := parameter source
  ⟨mode,freeze type⟩

def ParameterPlanOf (source : Ty) (plan : ParameterPlan (Value := Value) (Variable := Variable)) : Prop :=
  ∃ type, Parameter source plan.mode type ∧ Frozen type plan.formal

theorem parameterPlan_exact (source : Ty) (plan : ParameterPlan (Value := Value) (Variable := Variable)) :
    parameterPlan source = plan ↔ ParameterPlanOf source plan := by
  constructor
  · rintro rfl
    exact ⟨(parameter source).2,parameter_sound source,(freeze_exact _ _).mp rfl⟩
  · rintro ⟨type,mode,frozen⟩
    have parts := (parameter_exact _ _ _).mpr mode
    have direction := (freeze_exact _ _).mpr frozen
    cases plan
    simp_all [parameterPlan]

def resultType (source : Ty) : Ty :=
  match symbolName source with
  | some "Atom" | some "_" | some "%Undefined%" => symbol "Any"
  | _ => source

inductive ResultTypeOf : Ty → Ty → Prop where
  | atom : ResultTypeOf (symbol "Atom") (symbol "Any")
  | underscore : ResultTypeOf (symbol "_") (symbol "Any")
  | undefined : ResultTypeOf (symbol "%Undefined%") (symbol "Any")
  | ordinary (source : Ty) : source ≠ symbol "Atom" → source ≠ symbol "_" →
      source ≠ symbol "%Undefined%" → ResultTypeOf source source

theorem resultType_exact (source result : Ty) :
    resultType source = result ↔ ResultTypeOf source result := by
  constructor
  · rintro rfl
    unfold resultType
    split
    · rename_i tag; obtain rfl := (symbolName_exact _ _).mp tag; exact .atom
    · rename_i tag; obtain rfl := (symbolName_exact _ _).mp tag; exact .underscore
    · rename_i tag; obtain rfl := (symbolName_exact _ _).mp tag; exact .undefined
    · rename_i notAtom notUnderscore notUndefined
      exact .ordinary source
        (fun equal => notAtom (by simp [equal,symbolName,symbol]))
        (fun equal => notUnderscore (by simp [equal,symbolName,symbol]))
        (fun equal => notUndefined (by simp [equal,symbolName,symbol]))
  · intro adapted
    cases adapted with
    | atom => rfl
    | underscore => rfl
    | undefined => rfl
    | ordinary source notAtom notUnderscore notUndefined =>
        unfold resultType
        split
        · rename_i tag; exact (notAtom ((symbolName_exact _ _).mp tag)).elim
        · rename_i tag; exact (notUnderscore ((symbolName_exact _ _).mp tag)).elim
        · rename_i tag; exact (notUndefined ((symbolName_exact _ _).mp tag)).elim
        · rfl

def ResultPlanOf (source : Ty) (formal : Formal (Value := Value) (Variable := Variable)) : Prop :=
  ∃ type, ResultTypeOf source type ∧ Frozen type formal

theorem resultPlan_exact (source : Ty) (formal : Formal (Value := Value) (Variable := Variable)) :
    freeze (resultType source) = formal ↔ ResultPlanOf source formal := by
  constructor
  · intro same
    exact ⟨resultType source,(resultType_exact _ _).mp rfl,(freeze_exact _ _).mp same⟩
  · rintro ⟨type,adapted,frozen⟩
    rw [(resultType_exact _ _).mpr adapted]
    exact (freeze_exact _ _).mpr frozen

structure CallPlan where
  parameters : List (ParameterPlan (Value := Value) (Variable := Variable))
  result : Formal (Value := Value) (Variable := Variable)

def callPlan (source : Ty) : Option (CallPlan (Value := Value) (Variable := Variable)) :=
  (arrowParts source).map fun (domains,result) =>
    ⟨domains.map parameterPlan,freeze (resultType result)⟩

/-- Every compiled position keeps its source mode and frozen checking
direction. The result uses its separate legacy adapter. -/
inductive CallPlanOf (source : Ty) : CallPlan (Value := Value) (Variable := Variable) → Prop where
  | arrow (domains : List Ty) (result : Ty) (plan : CallPlan (Value := Value) (Variable := Variable)) :
      source = arrow domains result →
      List.Forall₂ ParameterPlanOf domains plan.parameters → ResultPlanOf result plan.result →
      CallPlanOf source plan

private theorem parameterPlans_exact (domains : List Ty)
    (plans : List (ParameterPlan (Value := Value) (Variable := Variable))) :
    domains.map parameterPlan = plans ↔ List.Forall₂ ParameterPlanOf domains plans := by
  induction domains generalizing plans with
  | nil => cases plans <;> simp
  | cons domain domains ih =>
      cases plans with
      | nil => simp
      | cons plan plans => simp [List.forall₂_cons,parameterPlan_exact,ih]

theorem callPlan_exact (source : Ty) (plan : CallPlan (Value := Value) (Variable := Variable)) :
    callPlan source = some plan ↔ CallPlanOf source plan := by
  constructor
  · intro built
    obtain ⟨⟨domains,result⟩,parsed,rfl⟩ := Option.map_eq_some_iff.mp built
    exact .arrow domains result _ ((arrowParts_exact _ _ _).mp parsed)
      ((parameterPlans_exact _ _).mp rfl) ((resultPlan_exact _ _).mp rfl)
  · intro built
    cases built with
    | arrow domains result plan same parameters returned =>
        cases plan
        simp [callPlan,(arrowParts_exact _ _ _).mpr same,
          (parameterPlans_exact _ _).mpr parameters,(resultPlan_exact _ _).mpr returned]

def ParameterPlan.rename (f : Variable → Variable)
    (plan : ParameterPlan (Value := Value) (Variable := Variable)) :
    ParameterPlan (Value := Value) (Variable := Variable) :=
  ⟨plan.mode,plan.formal.refine (fun slot => .var (f slot))⟩

def CallPlan.rename (f : Variable → Variable)
    (plan : CallPlan (Value := Value) (Variable := Variable)) :
    CallPlan (Value := Value) (Variable := Variable) :=
  ⟨plan.parameters.map (ParameterPlan.rename f),plan.result.refine (fun slot => .var (f slot))⟩

theorem symbolName_renaming (f : Variable → Variable) (source : Ty) :
    symbolName (UnificationRenaming.rename f source) = symbolName source := by
  cases source <;> rfl

theorem resultType_renaming (f : Variable → Variable) (source : Ty) :
    resultType (UnificationRenaming.rename f source) = UnificationRenaming.rename f (resultType source) := by
  simp only [resultType,symbolName_renaming]
  split <;> rfl

theorem parameterPlan_renaming (f g : Variable → Variable)
    (inverse : Function.LeftInverse g f) (source : Ty) :
    parameterPlan (UnificationRenaming.rename f source) = (parameterPlan source).rename f := by
  simp only [parameterPlan,parameter_renaming f g inverse,freeze_renaming,ParameterPlan.rename]

theorem callPlan_renaming (f g : Variable → Variable)
    (inverse : Function.LeftInverse g f) (source : Ty) :
    callPlan (UnificationRenaming.rename f source) = (callPlan source).map (CallPlan.rename f) := by
  simp only [callPlan,arrowParts_renaming f g inverse,Option.map_map]
  cases parsed : arrowParts source with
  | none => rfl
  | some parts =>
      simp [CallPlan.rename,List.map_map,parameterPlan_renaming f g inverse,
        resultType_renaming,freeze_renaming,Function.comp_def]

namespace Controls

abbrev sig := signature String JointSchemeContracts.Coordinate
def slot : Term sig := .var (.scheme 0 0)
def number : Term sig := symbol "Number"

theorem zero_domain_arrow : arrowParts (arrow [] number) = some ([],number) :=
  (arrowParts_exact _ _ _).mpr rfl

theorem bare_arrow_is_data : arrowParts (ListTerms.ofList [symbol "->"] : Term sig) = none := by
  simp [arrowParts,symbolName,symbol]

theorem unknown_tag_is_not_guessed :
    arrowParts (ListTerms.ofList [slot,number]) = none := by
  simp [arrowParts,slot,symbolName]

theorem grounded_spelling_is_not_a_tag :
    parameter (ListTerms.ofList [.const (.grounded "Hold"),number]) =
      (.eval,ListTerms.ofList [.const (.grounded "Hold"),number]) := by
  simp [parameter,wrapper,symbolName,ListTerms.toList,ListTerms.ofList]

theorem wrapped_unknown_and_bare_unknown_differ :
    parameter (ListTerms.ofList [symbol "Eval",symbol "%Undefined%"] : Term sig) =
      (.eval,symbol "%Undefined%") ∧
    parameter (symbol "%Undefined%" : Term sig) = (.eval,symbol "Any") := by
  constructor <;> simp [parameter,wrapper,symbolName,symbol,ListTerms.toList,ListTerms.ofList]

theorem polymorphic_plan_keeps_sharing :
    callPlan (arrow [slot,slot] slot) = some
      ⟨[⟨.eval,.infer slot⟩,⟨.eval,.infer slot⟩],.infer slot⟩ := by
  simp [callPlan,(arrowParts_exact _ _ _).mpr rfl,parameterPlan,parameter,
    wrapper,symbolName,freeze,resultType,slot,ListTerms.toList]

theorem modes_and_types_remain_separate :
    callPlan (arrow [ListTerms.ofList [symbol "Hold",number],
      ListTerms.ofList [symbol "Eval",symbol "Atom"]] number) = some
      ⟨[⟨.hold,.check number⟩,⟨.eval,.check (symbol "Atom")⟩],.check number⟩ := by
  simp [callPlan,(arrowParts_exact _ _ _).mpr rfl,parameterPlan,parameter,
    wrapper,symbolName,symbol,freeze,resultType,number,ListTerms.toList,ListTerms.ofList]

end Controls

#print axioms arrowParts_exact
#print axioms wrapper_exact
#print axioms parameter_exact
#print axioms freezing_again_changes_meaning
#print axioms parameter_renaming
#print axioms arrowParts_renaming
#print axioms callPlan_exact
#print axioms callPlan_renaming
#print axioms Controls.grounded_spelling_is_not_a_tag
#print axioms Controls.polymorphic_plan_keeps_sharing
#print axioms Controls.modes_and_types_remain_separate

end Mettapedia.Languages.MeTTa.PeTTa.TypingSourceViews
