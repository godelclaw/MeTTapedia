import Mettapedia.Languages.MM0.HOLKernelSyntax
import Mettapedia.Languages.MM0.HOLKernelTypeSupport

/-!
# Intrinsic HOL terms under native MM0 term assignments

Free source variables may be assigned native compound preterms. Each source
binder extends the assignment with its specified native bound image while
retaining the other images literally. This encoding agrees exactly with the
position encoding, commutes with source renaming, and preserves native sorting
for all source constructors.

Literal insertion and encoding of source substitution can have different bound
spellings, even for a closed lambda argument. The separation control retains
that distinction. A propositional alpha equation is a further proof obligation.
-/

set_option autoImplicit false
namespace Mettapedia.Languages.MM0.HOLKernelTermAssignments
open Mettapedia.Logic.HOL Kernel HOLKernelSyntax HOLKernelTypeSupport
universe u v
variable {Base : Type u} {Const : Ty Base → Type v}

abbrev Assignment (gamma : Ctx Base) := ∀ {type}, Var gamma type → Preterm

def Assignment.extend {gamma : Ctx Base} {domain : Ty Base}
    (head : Preterm) (tail : Assignment gamma) : Assignment (domain :: gamma)
  | _, .vz => head
  | _, .vs index => tail index

theorem Assignment.extend_positions {gamma : Ctx Base} {domain : Ty Base}
    (head : Nat) (positions : Positions gamma) :
    (Assignment.extend (domain := domain) (.var head) (fun index => .var (positions index)) :
      Assignment (domain :: gamma)) =
      (fun {type} (index : Var (domain :: gamma) type) => .var (Positions.extend head positions index)) := by
  funext type index
  cases index <;> rfl

theorem Assignment.extend_comp {gamma delta : Ctx Base} {domain : Ty Base}
    (head : Preterm) (assignment : Assignment delta) (rho : Rename Base gamma delta) :
    (fun {type} (index : Var (domain :: gamma) type) =>
      Assignment.extend head assignment (Rename.lift rho index)) =
      (Assignment.extend (domain := domain) head (fun index => assignment (rho index)) :
        Assignment (domain :: gamma)) := by
  funext type index
  cases index <;> rfl

def encodeWithAssignment (references : Symbol → Nat) (base : Base → Preterm)
    (constant : ∀ {type}, Const type → Preterm) (binders : Nat → Nat) :
    {gamma : Ctx Base} → {type : Ty Base} → Assignment gamma → Nat → Term Const gamma type → Preterm
  | _, _, assignment, _, .var index => assignment index
  | _, _, _, _, .const symbol => constant symbol
  | _, _, assignment, depth, .app function argument => applySymbol references .app
      [encodeWithAssignment references base constant binders assignment depth function,
       encodeWithAssignment references base constant binders assignment depth argument]
  | _, _, assignment, depth, .lam (σ := domain) body => applySymbol references .lam
      [.var (binders depth), encodeType references base domain,
       encodeWithAssignment references base constant binders (Assignment.extend (.var (binders depth)) assignment) (depth + 1) body]

  | _, _, _, _, .top => applySymbol references .truth []
  | _, _, _, _, .bot => applySymbol references .falsity []
  | _, _, assignment, depth, .and first second => applySymbol references .andc
      [encodeWithAssignment references base constant binders assignment depth first,
       encodeWithAssignment references base constant binders assignment depth second]
  | _, _, assignment, depth, .or first second => applySymbol references .orc
      [encodeWithAssignment references base constant binders assignment depth first,
       encodeWithAssignment references base constant binders assignment depth second]
  | _, _, assignment, depth, .imp first second => applySymbol references .impc
      [encodeWithAssignment references base constant binders assignment depth first,
       encodeWithAssignment references base constant binders assignment depth second]
  | _, _, assignment, depth, .not body => applySymbol references .notc
      [encodeWithAssignment references base constant binders assignment depth body]
  | _, _, assignment, depth, .eq (τ := type) first second => applySymbol references .eqc
      [encodeType references base type,
       encodeWithAssignment references base constant binders assignment depth first,
       encodeWithAssignment references base constant binders assignment depth second]
  | _, _, assignment, depth, .all (σ := domain) body => applySymbol references .allc
      [.var (binders depth), encodeType references base domain,
       encodeWithAssignment references base constant binders (Assignment.extend (.var (binders depth)) assignment) (depth + 1) body]
  | _, _, assignment, depth, .ex (σ := domain) body => applySymbol references .exc
      [.var (binders depth), encodeType references base domain,
       encodeWithAssignment references base constant binders (Assignment.extend (.var (binders depth)) assignment) (depth + 1) body]


theorem encode_positions (references : Symbol → Nat) (base : Base → Preterm)
    (constant : ∀ {type}, Const type → Preterm) (binders : Nat → Nat)
    {gamma : Ctx Base} {type : Ty Base} (source : Term Const gamma type) :
    ∀ (positions : Positions gamma) (depth : Nat),
      encodeWithAssignment references base constant binders (fun index => .var (positions index)) depth source =
        encodeTerm references base constant binders positions depth source := by
  induction source <;> intros <;>
    simp_all only [encodeWithAssignment, encodeTerm, Assignment.extend_positions]

theorem encode_rename (references : Symbol → Nat) (base : Base → Preterm)
    (constant : ∀ {type}, Const type → Preterm) (binders : Nat → Nat)
    {gamma : Ctx Base} {type : Ty Base} (source : Term Const gamma type) :
    ∀ {delta : Ctx Base} (rho : Rename Base gamma delta)
      (assignment : Assignment delta) (depth : Nat),
      encodeWithAssignment references base constant binders assignment depth (rename rho source) =
        encodeWithAssignment references base constant binders (fun index => assignment (rho index)) depth source := by
  induction source <;> intros <;>
    simp_all only [rename, encodeWithAssignment, Assignment.extend_comp]

variable {sorts : SortSignature} {terms : TermSignature}

theorem Assignment.extend_sorted {gamma : Ctx Base} {domain : Ty Base}
    (signature : Signature sorts terms) (context : Context) (head : Preterm) (assignment : Assignment gamma)
    (headSorted : Preterm.HasType terms context head [] signature.ids.object)
    (assignmentSorted : ∀ {type} (index : Var gamma type),
      Preterm.HasType terms context (assignment index) [] signature.ids.object) :
    ∀ {type} (index : Var (domain :: gamma) type),
      Preterm.HasType terms context (Assignment.extend head assignment index) [] signature.ids.object := by
  intro type index
  cases index with
  | vz => exact headSorted
  | vs index => exact assignmentSorted index

theorem encode_sorted (signature : Signature sorts terms) (context : Context)
    (base : Base → Preterm) (constant : ∀ {type}, Const type → Preterm) (binders : Nat → Nat)
    (baseSorted : ∀ index, Preterm.HasType terms context (base index) [] signature.ids.type)
    (constantSorted : ∀ {type} (symbol : Const type),
      Preterm.HasType terms context (constant symbol) [] signature.ids.object)
    {gamma : Ctx Base} {type : Ty Base} (source : Term Const gamma type) :
    ∀ (assignment : Assignment gamma) (depth : Nat),
      (∀ {type} (index : Var gamma type),
        Preterm.HasType terms context (assignment index) [] signature.ids.object) →
      (∀ offset < source.binderDepth,
        context[binders (depth + offset)]? = some (.bound signature.ids.object)) →
      Preterm.HasType terms context (encodeWithAssignment signature.symbol base constant binders assignment depth source)
        [] signature.ids.object := by
  induction source with
  | var index =>
      intro assignment depth assignmentSorted _
      exact assignmentSorted index
  | const symbol => intro _ _ _ _; exact constantSorted symbol
  | top => intro _ _ _ _; exact signature.application context .truth [] .nil
  | bot => intro _ _ _ _; exact signature.application context .falsity [] .nil
  | app first second ihf ihs | and first second ihf ihs | or first second ihf ihs
  | imp first second ihf ihs =>
      intro assignment depth assignmentSorted bindersSorted
      have firstSorted := ihf assignment depth assignmentSorted
        (fun offset smaller => bindersSorted offset
          (Nat.lt_of_lt_of_le smaller (Nat.le_max_left _ _)))
      have secondSorted := ihs assignment depth assignmentSorted
        (fun offset smaller => bindersSorted offset
          (Nat.lt_of_lt_of_le smaller (Nat.le_max_right _ _)))
      apply signature.application
      exact .cons (.regular firstSorted) (.cons (.regular secondSorted) .nil)
  | not body ih =>
      intro assignment depth assignmentSorted bindersSorted
      exact signature.application context .notc _
        (.cons (.regular (ih assignment depth assignmentSorted bindersSorted)) .nil)
  | @eq gamma type first second ihf ihs =>
      intro assignment depth assignmentSorted bindersSorted
      have firstSorted := ihf assignment depth assignmentSorted
        (fun offset smaller => bindersSorted offset
          (Nat.lt_of_lt_of_le smaller (Nat.le_max_left _ _)))
      have secondSorted := ihs assignment depth assignmentSorted
        (fun offset smaller => bindersSorted offset
          (Nat.lt_of_lt_of_le smaller (Nat.le_max_right _ _)))
      exact signature.application context .eqc _
        (.cons (.regular (encodeType_sorted signature context base baseSorted type))
          (.cons (.regular firstSorted) (.cons (.regular secondSorted) .nil)))
  | lam body ih | all body ih | ex body ih =>
      intro assignment depth assignmentSorted bindersSorted
      have head : context[binders depth]? = some (.bound signature.ids.object) := by
        simpa only [Nat.add_zero] using bindersSorted 0 (Nat.zero_lt_succ _)
      have bodyBinders : ∀ offset < body.binderDepth,
          context[binders (depth + 1 + offset)]? = some (.bound signature.ids.object) := by
        intro offset smaller
        have found := bindersSorted (offset + 1) (Nat.add_lt_add_right smaller 1)
        simpa only [Nat.add_assoc, Nat.add_comm 1 offset] using found
      have bodySorted := ih (Assignment.extend (.var (binders depth)) assignment) (depth + 1)
        (Assignment.extend_sorted signature context (.var (binders depth)) assignment
          (.var (binder := .bound signature.ids.object) head) assignmentSorted) bodyBinders
      apply signature.application
      exact .cons (.bound head) (.cons (.regular (encodeType_sorted signature context base baseSorted _))
        (.cons (.regular bodySorted) .nil))


def encodeSubstitution (references : Symbol → Nat) (base : Base → Preterm)
    (constant : ∀ {type}, Const type → Preterm) (binders : Nat → Nat)
    {gamma delta : Ctx Base} (assignment : Assignment delta) (depth : Nat)
    (substitution : Subst Const gamma delta) : Assignment gamma :=
  fun index => encodeWithAssignment references base constant binders assignment depth (substitution index)

theorem encodeSubstitution_lift (references : Symbol → Nat) (base : Base → Preterm)
    (constant : ∀ {type}, Const type → Preterm) (binders : Nat → Nat)
    {gamma delta : Ctx Base} {domain : Ty Base} (assignment : Assignment delta) (depth bound : Nat)
    (substitution : Subst Const gamma delta) :
    (encodeSubstitution references base constant binders (Assignment.extend (.var bound) assignment)
      depth (Subst.lift (σ := domain) substitution) : Assignment (domain :: gamma)) =
    (Assignment.extend (domain := domain) (.var bound)
      (encodeSubstitution references base constant binders assignment depth substitution) :
      Assignment (domain :: gamma)) := by
  funext type index
  cases index with
  | vz => rfl
  | vs index =>
      simpa only [encodeSubstitution, Subst.lift, Rename.weaken, Assignment.extend] using
        encode_rename references base constant binders (substitution index) Rename.weaken
          (Assignment.extend (.var bound) assignment) depth

theorem encodeSubstitution_sorted (signature : Signature sorts terms) (context : Context)
    (base : Base → Preterm) (constant : ∀ {type}, Const type → Preterm) (binders : Nat → Nat)
    (baseSorted : ∀ index, Preterm.HasType terms context (base index) [] signature.ids.type)
    (constantSorted : ∀ {type} (symbol : Const type),
      Preterm.HasType terms context (constant symbol) [] signature.ids.object)
    {gamma delta : Ctx Base} (substitution : Subst Const gamma delta)
    (assignment : Assignment delta) (depth : Nat)
    (assignmentSorted : ∀ {type} (index : Var delta type),
      Preterm.HasType terms context (assignment index) [] signature.ids.object)
    (slots : ∀ offset < Subst.maxBinderDepth substitution,
      context[binders (depth + offset)]? = some (.bound signature.ids.object)) :
    ∀ {type} (index : Var gamma type), Preterm.HasType terms context
      (encodeSubstitution signature.symbol base constant binders assignment depth substitution index)
      [] signature.ids.object := by
  intro type index
  exact encode_sorted signature context base constant binders baseSorted constantSorted
    (substitution index) assignment depth assignmentSorted
    (fun offset smaller => slots offset
      (Nat.lt_of_lt_of_le smaller (Subst.binderDepth_le_maxBinderDepth substitution index)))

theorem substitution_encodings_sorted (signature : Signature sorts terms) (context : Context)
    (base : Base → Preterm) (constant : ∀ {type}, Const type → Preterm) (binders : Nat → Nat)
    (baseSorted : ∀ index, Preterm.HasType terms context (base index) [] signature.ids.type)
    (constantSorted : ∀ {type} (symbol : Const type),
      Preterm.HasType terms context (constant symbol) [] signature.ids.object)
    {gamma delta : Ctx Base} {type : Ty Base} (source : Term Const gamma type)
    (substitution : Subst Const gamma delta) (assignment : Assignment delta) (depth : Nat)
    (assignmentSorted : ∀ {type} (index : Var delta type),
      Preterm.HasType terms context (assignment index) [] signature.ids.object)
    (slots : ∀ offset < source.binderDepth + Subst.maxBinderDepth substitution,
      context[binders (depth + offset)]? = some (.bound signature.ids.object)) :
    Preterm.HasType terms context
      (encodeWithAssignment signature.symbol base constant binders
        (encodeSubstitution signature.symbol base constant binders assignment depth substitution)
        depth source) [] signature.ids.object ∧
    Preterm.HasType terms context
      (encodeWithAssignment signature.symbol base constant binders assignment depth
        (subst substitution source)) [] signature.ids.object := by
  have images : ∀ {type} (index : Var gamma type), Preterm.HasType terms context
      (encodeSubstitution signature.symbol base constant binders assignment depth substitution index)
      [] signature.ids.object :=
    encodeSubstitution_sorted signature context base constant binders baseSorted constantSorted substitution
      assignment depth assignmentSorted (fun offset smaller => slots offset (by omega))
  constructor
  · exact encode_sorted signature context base constant binders baseSorted constantSorted source _ depth
      images (fun offset smaller => slots offset (by omega))
  · exact encode_sorted signature context base constant binders baseSorted constantSorted
      (subst substitution source) assignment depth assignmentSorted
      (fun offset smaller => slots offset
        (Nat.lt_of_lt_of_le smaller (Term.binderDepth_subst_le source substitution)))


theorem encode_independent (context : Context) (observer : Nat) (references : Symbol → Nat)
    (base : Base → Preterm) (constant : ∀ {type}, Const type → Preterm) (binders : Nat → Nat)
    (baseIndependent : ∀ index, ¬ Preterm.HasVar context observer (base index))
    (constantIndependent : ∀ {type} (symbol : Const type), ¬ Preterm.HasVar context observer (constant symbol))
    {gamma : Ctx Base} {type : Ty Base} (source : Term Const gamma type) :
    ∀ (assignment : Assignment gamma) (depth : Nat),
      (∀ {type} (index : Var gamma type), ¬ Preterm.HasVar context observer (assignment index)) →
      (∀ offset < source.binderDepth, ¬ Preterm.HasVar context observer (.var (binders (depth + offset)))) →
      ¬ Preterm.HasVar context observer (encodeWithAssignment references base constant binders assignment depth source) := by
  induction source with
  | var index => intro assignment depth independent slots; exact independent index
  | const symbol => intros; exact constantIndependent symbol
  | top | bot => intros; exact applySymbol_independent context observer references _ [] (by simp)
  | app first second ihFirst ihSecond | and first second ihFirst ihSecond
  | or first second ihFirst ihSecond | imp first second ihFirst ihSecond =>
      intro assignment depth independent slots
      apply applySymbol_independent context observer references _ _
      intro expression member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact ihFirst assignment depth independent (fun offset smaller => slots offset
          (Nat.lt_of_lt_of_le smaller (Nat.le_max_left _ _)))
      · exact ihSecond assignment depth independent (fun offset smaller => slots offset
          (Nat.lt_of_lt_of_le smaller (Nat.le_max_right _ _)))
  | @eq gamma type first second ihFirst ihSecond =>
      intro assignment depth independent slots
      apply applySymbol_independent context observer references .eqc _
      intro expression member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl
      · exact encodeType_independent context observer references base baseIndependent type
      · exact ihFirst assignment depth independent (fun offset smaller => slots offset
          (Nat.lt_of_lt_of_le smaller (Nat.le_max_left _ _)))
      · exact ihSecond assignment depth independent (fun offset smaller => slots offset
          (Nat.lt_of_lt_of_le smaller (Nat.le_max_right _ _)))
  | not body ih =>
      intro assignment depth independent slots
      apply applySymbol_independent context observer references .notc _
      intro expression member
      have same : expression = encodeWithAssignment references base constant binders assignment depth body := by simpa using member
      subst expression
      exact ih assignment depth independent slots
  | @lam domain gamma result body ih | @all domain gamma body ih | @ex domain gamma body ih =>
      intro assignment depth independent slots
      have head : ¬ Preterm.HasVar context observer (.var (binders depth)) := by
        simpa only [Nat.add_zero] using slots 0 (Nat.zero_lt_succ _)
      have extendedIndependent : ∀ {type} (index : Var (domain :: gamma) type),
          ¬ Preterm.HasVar context observer (Assignment.extend (.var (binders depth)) assignment index) := by
        intro type index
        cases index with
        | vz => exact head
        | vs index => exact independent index
      have bodyIndependent := ih (Assignment.extend (.var (binders depth)) assignment) (depth + 1)
        extendedIndependent (by
          intro offset smaller
          have found := slots (offset + 1) (Nat.add_lt_add_right smaller 1)
          simpa only [Nat.add_assoc, Nat.add_comm 1 offset] using found)
      apply applySymbol_independent context observer references _ _
      intro expression member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl
      · exact head
      · exact encodeType_independent context observer references base baseIndependent domain
      · exact bodyIndependent


namespace SubstitutionControl
abbrev NoConstants : Ty Unit → Type := fun _ => Empty

def noConstants {type : Ty Unit} (symbol : NoConstants type) : Preterm := nomatch symbol

def noAssignment : Assignment ([] : Ctx Unit) := fun index => nomatch index

def argument : Term NoConstants [] (.arr .prop .prop) := .lam (.var .vz)

def body : Term NoConstants [.arr .prop .prop] (.arr .prop (.arr .prop .prop)) :=
  .lam (.var (.vs .vz))

theorem literal_assignment_differs_from_source_instantiation (references : Symbol → Nat) :
    encodeWithAssignment references (fun _ => applySymbol references .bool []) noConstants id
      (Assignment.extend
        (encodeWithAssignment references (fun _ => applySymbol references .bool []) noConstants id
          noAssignment 0 argument) noAssignment) 0 body ≠
    encodeWithAssignment references (fun _ => applySymbol references .bool []) noConstants id
      noAssignment 0 (instantiate argument body) := by
  simp [body, argument, instantiate, subst, Subst.single, Subst.lift, rename, Rename.lift,
    encodeWithAssignment, Assignment.extend, encodeType, applySymbol, Preterm.applyArgs]
end SubstitutionControl

#print axioms encode_independent
#print axioms encodeSubstitution_lift
#print axioms encodeSubstitution_sorted
#print axioms substitution_encodings_sorted
#print axioms encode_positions
#print axioms encode_rename
#print axioms encode_sorted
#print axioms SubstitutionControl.literal_assignment_differs_from_source_instantiation
theorem Assignment.extend_varsBelow {gamma : Ctx Base} {domain : Ty Base} (bound : Nat)
    (head : Preterm) (assignment : Assignment gamma)
    (headBound : Preterm.VarsBelow bound head)
    (assignmentBound : ∀ {type} (index : Var gamma type), Preterm.VarsBelow bound (assignment index)) :
    ∀ {type} (index : Var (domain :: gamma) type),
      Preterm.VarsBelow bound (Assignment.extend head assignment index) := by
  intro type index
  cases index with
  | vz => exact headBound
  | vs index => exact assignmentBound index

theorem encode_varsBelow (references : Symbol → Nat) (base : Base → Preterm)
    (constant : ∀ {type}, Const type → Preterm) (binders : Nat → Nat) (bound : Nat)
    (baseBound : ∀ index, Preterm.VarsBelow bound (base index))
    (constantBound : ∀ {type} (symbol : Const type), Preterm.VarsBelow bound (constant symbol))
    {gamma : Ctx Base} {type : Ty Base} (source : Term Const gamma type) :
    ∀ (assignment : Assignment gamma) (depth : Nat),
      (∀ {type} (index : Var gamma type), Preterm.VarsBelow bound (assignment index)) →
      (∀ offset < source.binderDepth, binders (depth + offset) < bound) →
      Preterm.VarsBelow bound (encodeWithAssignment references base constant binders assignment depth source) := by
  induction source with
  | var index => intro assignment depth assignmentBound _; exact assignmentBound index
  | const symbol => intro _ _ _ _; exact constantBound symbol
  | top => intros; simp [encodeWithAssignment, applySymbol, Preterm.applyArgs, Preterm.VarsBelow]
  | bot => intros; simp [encodeWithAssignment, applySymbol, Preterm.applyArgs, Preterm.VarsBelow]
  | app first second ihFirst ihSecond | and first second ihFirst ihSecond | or first second ihFirst ihSecond | imp first second ihFirst ihSecond =>
      intro assignment depth assignmentBound bindersBound
      have left := ihFirst assignment depth assignmentBound
        (fun offset smaller => bindersBound offset (Nat.lt_of_lt_of_le smaller (Nat.le_max_left _ _)))
      have right := ihSecond assignment depth assignmentBound
        (fun offset smaller => bindersBound offset (Nat.lt_of_lt_of_le smaller (Nat.le_max_right _ _)))
      exact ⟨⟨trivial, left⟩, right⟩
  | not body ih =>
      intro assignment depth assignmentBound bindersBound
      exact ⟨trivial, ih assignment depth assignmentBound bindersBound⟩
  | eq first second ihFirst ihSecond =>
      intro assignment depth assignmentBound bindersBound
      have left := ihFirst assignment depth assignmentBound
        (fun offset smaller => bindersBound offset (Nat.lt_of_lt_of_le smaller (Nat.le_max_left _ _)))
      have right := ihSecond assignment depth assignmentBound
        (fun offset smaller => bindersBound offset (Nat.lt_of_lt_of_le smaller (Nat.le_max_right _ _)))
      exact ⟨⟨⟨trivial, encodeType_varsBelow references base bound baseBound _⟩, left⟩, right⟩
  | @lam domain gamma codomain body ih | @all domain gamma body ih | @ex domain gamma body ih =>
      intro assignment depth assignmentBound bindersBound
      have headBound : binders depth < bound := by
        simpa only [Nat.add_zero] using bindersBound 0 (Nat.zero_lt_succ _)
      have tailBound : ∀ offset < body.binderDepth, binders (depth + 1 + offset) < bound := by
        intro offset smaller
        have found := bindersBound (offset + 1) (Nat.add_lt_add_right smaller 1)
        simpa only [Nat.add_assoc, Nat.add_comm 1 offset] using found
      have bodyBound := ih (Assignment.extend (.var (binders depth)) assignment) (depth + 1)
        (Assignment.extend_varsBelow bound (.var (binders depth)) assignment headBound assignmentBound) tailBound
      exact ⟨⟨⟨trivial, headBound⟩, encodeType_varsBelow references base bound baseBound domain⟩, bodyBound⟩

#print axioms encode_varsBelow

end Mettapedia.Languages.MM0.HOLKernelTermAssignments
