import Mettapedia.Languages.MM0.Kernel.DeclarationAdmission
import Mettapedia.Logic.HOL.Syntax.BindingDepth

/-!
# Intrinsic HOL terms in the maintained MM0 kernel signature

Every source term constructor is represented by an actual MM0 application
spine. The signature interface retains the maintained constructor names and
their exact binder profiles, including the dependent body slot of lambda,
universal and existential binding.

MM0 sorting, the HOL typing statements represented inside its `wff` sort,
and theorem derivability are distinct judgments. The formation results here
concern the first of these. Substitution independence and interpretation of
the HOL typing and inference rules carry additional obligations.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.HOLKernelSyntax

open Mettapedia.Logic.HOL
open Kernel

structure SortIds where
  wff : Nat
  type : Nat
  object : Nat
  deriving DecidableEq

inductive Symbol where
  | im | an | bool | function | ty | app | lam | truth | falsity
  | andc | orc | impc | notc | eqc | allc | exc | thm
  deriving DecidableEq, Repr

def Symbol.all : List Symbol :=
  [.im, .an, .bool, .function, .ty, .app, .lam, .truth, .falsity,
    .andc, .orc, .impc, .notc, .eqc, .allc, .exc, .thm]

theorem Symbol.mem_all (constructor : Symbol) : constructor ∈ Symbol.all := by
  cases constructor <;> simp [Symbol.all]

def Symbol.name : Symbol → String
  | .im => "im"
  | .an => "an"
  | .bool => "bool"
  | .function => "fun"
  | .ty => "ty"
  | .app => "app"
  | .lam => "lam"
  | .truth => "T"
  | .falsity => "F"
  | .andc => "andc"
  | .orc => "orc"
  | .impc => "impc"
  | .notc => "notc"
  | .eqc => "eqc"
  | .allc => "allc"
  | .exc => "exc"
  | .thm => "thm"

theorem Symbol.name_injective : Function.Injective Symbol.name := by
  intro first second same
  cases first <;> cases second <;> simp_all [Symbol.name]

def Symbol.profile (sorts : SortIds) : Symbol → TermDecl
  | .im | .an => ⟨[.regular sorts.wff ∅, .regular sorts.wff ∅], sorts.wff, ∅⟩
  | .bool => ⟨[], sorts.type, ∅⟩
  | .function => ⟨[.regular sorts.type ∅, .regular sorts.type ∅], sorts.type, ∅⟩
  | .ty => ⟨[.regular sorts.object ∅, .regular sorts.type ∅], sorts.wff, ∅⟩
  | .app | .andc | .orc | .impc =>
      ⟨[.regular sorts.object ∅, .regular sorts.object ∅], sorts.object, ∅⟩
  | .lam | .allc | .exc =>
      ⟨[.bound sorts.object, .regular sorts.type ∅, .regular sorts.object {0}], sorts.object, ∅⟩
  | .truth | .falsity => ⟨[], sorts.object, ∅⟩
  | .notc => ⟨[.regular sorts.object ∅], sorts.object, ∅⟩
  | .eqc =>
      ⟨[.regular sorts.type ∅, .regular sorts.object ∅, .regular sorts.object ∅], sorts.object, ∅⟩
  | .thm => ⟨[.regular sorts.object ∅], sorts.wff, ∅⟩

/-- References into the actual kernel tables, with their retained names.
No theorem declaration or proof validity is a field of this interface. -/
structure Signature (sorts : SortSignature) (terms : TermSignature) where
  ids : SortIds
  wffDeclared : sorts ids.wff = some { strict := true, provable := true }
  typeDeclared : sorts ids.type = some { strict := true }
  objectDeclared : sorts ids.object = some {}
  symbol : Symbol → Nat
  names : Nat → Option String
  named : ∀ constructor, names (symbol constructor) = some constructor.name
  declared : ∀ constructor, terms (symbol constructor) = some (constructor.profile ids)

variable {sorts : SortSignature} {terms : TermSignature}

theorem Signature.symbol_injective (signature : Signature sorts terms) :
    Function.Injective signature.symbol := by
  intro first second same
  apply Symbol.name_injective
  have equal := congrArg signature.names same
  rw [signature.named, signature.named] at equal
  exact Option.some.inj equal

theorem Signature.wff_ne_type (signature : Signature sorts terms) :
    signature.ids.wff ≠ signature.ids.type := by
  intro same
  have declared := signature.wffDeclared
  rw [same, signature.typeDeclared] at declared
  cases declared

theorem Signature.type_ne_object (signature : Signature sorts terms) :
    signature.ids.type ≠ signature.ids.object := by
  intro same
  have declared := signature.typeDeclared
  rw [same, signature.objectDeclared] at declared
  cases declared

theorem Signature.wff_ne_object (signature : Signature sorts terms) :
    signature.ids.wff ≠ signature.ids.object := by
  intro same
  have declared := signature.wffDeclared
  rw [same, signature.objectDeclared] at declared
  cases declared

theorem Signature.profile_admissible (signature : Signature sorts terms) (constructor : Symbol) :
    TermDecl.Admissible sorts (constructor.profile signature.ids) := by
  apply (TermDecl.check_iff _ _).mp
  cases constructor <;>
    simp [Symbol.profile, TermDecl.check, Context.check, Context.checkFrom, Context.checkBinder,
      Context.isBound, signature.wffDeclared, signature.typeDeclared, signature.objectDeclared]

def applySymbol (references : Symbol → Nat) (constructor : Symbol)
    (arguments : List Preterm) : Preterm :=
  Preterm.applyArgs (.term (references constructor)) arguments

universe u v
variable {Base : Type u} {Const : Ty Base → Type v}

def encodeType (references : Symbol → Nat) (base : Base → Preterm) : Ty Base → Preterm
  | .prop => applySymbol references .bool []
  | .base index => base index
  | .arr domain result => applySymbol references .function
      [encodeType references base domain, encodeType references base result]

abbrev Positions (gamma : Ctx Base) := ∀ {type}, Var gamma type → Nat

def Positions.extend {gamma : Ctx Base} {domain : Ty Base}
    (head : Nat) (tail : Positions gamma) : Positions (domain :: gamma)
  | _, .vz => head
  | _, .vs index => tail index

theorem Positions.extend_comp {gamma delta : Ctx Base} {domain : Ty Base}
    (head : Nat) (positions : Positions delta) (rho : Rename Base gamma delta) :
    (fun {type} (index : Var (domain :: gamma) type) =>
      Positions.extend head positions (Rename.lift rho index)) =
      (Positions.extend (domain := domain) head (fun index => positions (rho index)) :
        Positions (domain :: gamma)) := by
  funext type index
  cases index <;> rfl

def encodeTerm (references : Symbol → Nat) (base : Base → Preterm)
    (constant : ∀ {type}, Const type → Preterm) (binders : Nat → Nat) :
    {gamma : Ctx Base} → {type : Ty Base} → Positions gamma → Nat → Term Const gamma type → Preterm
  | _, _, positions, _, .var index => .var (positions index)
  | _, _, _, _, .const symbol => constant symbol
  | _, _, positions, depth, .app function argument => applySymbol references .app
      [encodeTerm references base constant binders positions depth function,
       encodeTerm references base constant binders positions depth argument]
  | _, _, positions, depth, .lam (σ := domain) body => applySymbol references .lam
      [.var (binders depth), encodeType references base domain,
       encodeTerm references base constant binders (Positions.extend (binders depth) positions) (depth + 1) body]

  | _, _, _, _, .top => applySymbol references .truth []
  | _, _, _, _, .bot => applySymbol references .falsity []
  | _, _, positions, depth, .and first second => applySymbol references .andc
      [encodeTerm references base constant binders positions depth first,
       encodeTerm references base constant binders positions depth second]
  | _, _, positions, depth, .or first second => applySymbol references .orc
      [encodeTerm references base constant binders positions depth first,
       encodeTerm references base constant binders positions depth second]
  | _, _, positions, depth, .imp first second => applySymbol references .impc
      [encodeTerm references base constant binders positions depth first,
       encodeTerm references base constant binders positions depth second]
  | _, _, positions, depth, .not body => applySymbol references .notc
      [encodeTerm references base constant binders positions depth body]
  | _, _, positions, depth, .eq (τ := type) first second => applySymbol references .eqc
      [encodeType references base type,
       encodeTerm references base constant binders positions depth first,
       encodeTerm references base constant binders positions depth second]
  | _, _, positions, depth, .all (σ := domain) body => applySymbol references .allc
      [.var (binders depth), encodeType references base domain,
       encodeTerm references base constant binders (Positions.extend (binders depth) positions) (depth + 1) body]
  | _, _, positions, depth, .ex (σ := domain) body => applySymbol references .exc
      [.var (binders depth), encodeType references base domain,
       encodeTerm references base constant binders (Positions.extend (binders depth) positions) (depth + 1) body]

theorem encodeTerm_rename (references : Symbol → Nat) (base : Base → Preterm)
    (constant : ∀ {type}, Const type → Preterm) (binders : Nat → Nat)
    {gamma : Ctx Base} {type : Ty Base} (source : Term Const gamma type) :
    ∀ {delta : Ctx Base} (rho : Rename Base gamma delta)
      (positions : Positions delta) (depth : Nat),
      encodeTerm references base constant binders positions depth (Mettapedia.Logic.HOL.rename rho source) =
        encodeTerm references base constant binders (fun index => positions (rho index)) depth source := by
  induction source <;> intros <;>
    simp_all only [Mettapedia.Logic.HOL.rename, encodeTerm, Positions.extend_comp]

theorem Signature.application (signature : Signature sorts terms) (context : Context)
    (constructor : Symbol) (arguments : List Preterm)
    (fitting : List.Forall₂ (Preterm.FitsBinder terms context) arguments
      (constructor.profile signature.ids).arguments) :
    Preterm.HasType terms context (applySymbol signature.symbol constructor arguments) []
      (constructor.profile signature.ids).resultSort := by
  apply (Preterm.HasType.applyArgs_iff terms context _ _ _ _).mpr
  refine ⟨(constructor.profile signature.ids).arguments, ?_, fitting⟩
  simpa only [List.append_nil] using Preterm.HasType.term (signature.declared constructor)

theorem encodeType_sorted (signature : Signature sorts terms) (context : Context)
    (base : Base → Preterm)
    (baseSorted : ∀ index, Preterm.HasType terms context (base index) [] signature.ids.type)
    (source : Ty Base) :
    Preterm.HasType terms context (encodeType signature.symbol base source) [] signature.ids.type := by
  induction source with
  | prop => exact signature.application context .bool [] .nil
  | base index => exact baseSorted index
  | arr domain result ihd ihr =>
      exact signature.application context .function _ (.cons (.regular ihd) (.cons (.regular ihr) .nil))

private theorem variable_sorted (context : Context) (position sort : Nat)
    (lookup : (context[position]?).map Binder.sort = some sort) :
    Preterm.HasType terms context (.var position) [] sort := by
  cases found : context[position]? with
  | none => simp [found] at lookup
  | some binder =>
      have same : binder.sort = sort := by simpa only [found, Option.map_some, Option.some.injEq] using lookup
      exact same ▸ Preterm.HasType.var found

private theorem extended_positions_sorted {gamma : Ctx Base} {domain : Ty Base}
    (context : Context) (sort head : Nat) (positions : Positions gamma)
    (headBound : context[head]? = some (.bound sort))
    (original : ∀ {type} (index : Var gamma type),
      (context[positions index]?).map Binder.sort = some sort) :
    ∀ {type} (index : Var (domain :: gamma) type),
      (context[Positions.extend head positions index]?).map Binder.sort = some sort := by
  intro type index
  cases index with
  | vz => simp [Positions.extend, headBound, Binder.sort]
  | vs index => exact original index

/-- Sorting covers all source constructors. Exactly the upcoming binder
depth is requested from the native context; a binder-free term needs no
spare bound slot. Freshness and independence are not inferred from sorting. -/
theorem encodeTerm_sorted (signature : Signature sorts terms) (context : Context)
    (base : Base → Preterm) (constant : ∀ {type}, Const type → Preterm) (binders : Nat → Nat)
    (baseSorted : ∀ index, Preterm.HasType terms context (base index) [] signature.ids.type)
    (constantSorted : ∀ {type} (symbol : Const type),
      Preterm.HasType terms context (constant symbol) [] signature.ids.object)
    {gamma : Ctx Base} {type : Ty Base} (source : Term Const gamma type) :
    ∀ (positions : Positions gamma) (depth : Nat),
      (∀ {type} (index : Var gamma type),
        (context[positions index]?).map Binder.sort = some signature.ids.object) →
      (∀ offset < source.binderDepth,
        context[binders (depth + offset)]? = some (.bound signature.ids.object)) →
      Preterm.HasType terms context (encodeTerm signature.symbol base constant binders positions depth source)
        [] signature.ids.object := by
  induction source with
  | var index =>
      intro positions depth positionsSorted _
      exact variable_sorted context _ _ (positionsSorted index)
  | const symbol => intro _ _ _ _; exact constantSorted symbol
  | top => intro _ _ _ _; exact signature.application context .truth [] .nil
  | bot => intro _ _ _ _; exact signature.application context .falsity [] .nil
  | app first second ihf ihs | and first second ihf ihs | or first second ihf ihs
  | imp first second ihf ihs =>
      intro positions depth positionsSorted bindersSorted
      have firstSorted := ihf positions depth positionsSorted
        (fun offset smaller => bindersSorted offset
          (Nat.lt_of_lt_of_le smaller (Nat.le_max_left _ _)))
      have secondSorted := ihs positions depth positionsSorted
        (fun offset smaller => bindersSorted offset
          (Nat.lt_of_lt_of_le smaller (Nat.le_max_right _ _)))
      apply signature.application
      exact .cons (.regular firstSorted) (.cons (.regular secondSorted) .nil)
  | not body ih =>
      intro positions depth positionsSorted bindersSorted
      exact signature.application context .notc _
        (.cons (.regular (ih positions depth positionsSorted bindersSorted)) .nil)
  | @eq gamma type first second ihf ihs =>
      intro positions depth positionsSorted bindersSorted
      have firstSorted := ihf positions depth positionsSorted
        (fun offset smaller => bindersSorted offset
          (Nat.lt_of_lt_of_le smaller (Nat.le_max_left _ _)))
      have secondSorted := ihs positions depth positionsSorted
        (fun offset smaller => bindersSorted offset
          (Nat.lt_of_lt_of_le smaller (Nat.le_max_right _ _)))
      exact signature.application context .eqc _
        (.cons (.regular (encodeType_sorted signature context base baseSorted type))
          (.cons (.regular firstSorted) (.cons (.regular secondSorted) .nil)))
  | lam body ih | all body ih | ex body ih =>
      intro positions depth positionsSorted bindersSorted
      have head : context[binders depth]? = some (.bound signature.ids.object) := by
        simpa only [Nat.add_zero] using bindersSorted 0 (Nat.zero_lt_succ _)
      have bodyBinders : ∀ offset < body.binderDepth,
          context[binders (depth + 1 + offset)]? = some (.bound signature.ids.object) := by
        intro offset smaller
        have found := bindersSorted (offset + 1) (Nat.add_lt_add_right smaller 1)
        simpa only [Nat.add_assoc, Nat.add_comm 1 offset] using found
      have bodySorted := ih (Positions.extend (binders depth) positions) (depth + 1)
        (extended_positions_sorted context _ _ positions head positionsSorted) bodyBinders
      apply signature.application
      exact .cons (.bound head) (.cons (.regular (encodeType_sorted signature context base baseSorted _))
        (.cons (.regular bodySorted) .nil))

#print axioms Symbol.name_injective
#print axioms Signature.symbol_injective
#print axioms Signature.wff_ne_type
#print axioms Signature.type_ne_object
#print axioms Signature.wff_ne_object
#print axioms Signature.profile_admissible
#print axioms encodeTerm_rename
#print axioms encodeType_sorted
#print axioms encodeTerm_sorted

theorem encodeType_varsBelow (references : Symbol → Nat) (base : Base → Preterm) (bound : Nat)
    (baseBound : ∀ index, Preterm.VarsBelow bound (base index)) (type : Ty Base) :
    Preterm.VarsBelow bound (encodeType references base type) := by
  induction type <;> simp_all [encodeType, applySymbol, Preterm.applyArgs, Preterm.VarsBelow]

end Mettapedia.Languages.MM0.HOLKernelSyntax
