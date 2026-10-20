import Mettapedia.GSLT.LanguageDef.IndexedInductiveGuestInstantiation
import Mettapedia.GSLT.LanguageDef.IndexedInductiveElimination

/-!
# Dependent meaning of generated indexed eliminators

Source shapes retain data and recursive positions. Their guest encoding uses
the admitted constructor inventory and the caller's parameter assignment.
Forward reduction is compared with the polynomial displayed section, assuming
local implementations of its constructor methods. Only the indices occurring
in constructor telescopes require literal quotation compatibility here.
Computed indices needing conversion require a separate execution strategy.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.IndexedInductive.Guest.Meaning

open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.IndexedPolynomial
open Mettapedia.TypeTheory.IndexedPolynomial.Description
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open Declaration.IndexedFamily

universe u v
variable {I : Interface.{u}} {Head : Type} {n : Nat}

/-- Recover the ordered source fields from a shape and its recursive slots. -/
def fields (quoteData : ∀ sort, I.Value sort → Tm Head n) :
    {context : List I.SortCode} → (code : Code I context) →
    {environment : Env I.Value context} → {index : I.Index} →
    (shape : Shape code environment index) →
    (Position code shape → Tm Head n) → Fin (fieldCount code) → Tm Head n
  | _, .result _, _, _, _, _ => fun position => Fin.elim0 position
  | _, .data sort body, _, _, shape, children =>
      Fin.cases (quoteData sort shape.1) (fields quoteData body shape.2 children)
  | _, .recursive _ rest, _, _, shape, children =>
      Fin.cases (children none) (fields quoteData rest shape (fun p => children (some p)))

/-- Enumerate recursive results without discarding or reordering positions. -/
def results {α : Type} : {context : List I.SortCode} → (code : Code I context) →
    {environment : Env I.Value context} → {index : I.Index} →
    (shape : Shape code environment index) → (Position code shape → α) → List α
  | _, .result _, _, _, _, _ => []
  | _, .data _ body, _, _, shape, values => results body shape.2 values
  | _, .recursive _ rest, _, _, shape, values =>
      values none :: results rest shape (fun p => values (some p))

theorem fields_decode {family : I.Index → Type u}
    (quoteData : ∀ sort, I.Value sort → Tm Head n)
    (quoteChild : ∀ index, family index → Tm Head n)
    {context : List I.SortCode} (code : Code I context)
    {environment : Env I.Value context} {index : I.Index}
    (shape : Shape code environment index) (children : ∀ p, family (next code shape p)) :
    fields quoteData code shape (fun p => quoteChild _ (children p)) =
      sourceArguments quoteData quoteChild code (decode code ⟨shape, children⟩) := by
  induction code with
  | result => rfl
  | data sort body ih =>
      funext position
      cases position using Fin.cases with
      | zero => rfl
      | succ p => exact congrFun (ih shape.2 children) p
  | recursive expression rest ih =>
      funext position
      cases position using Fin.cases with
      | zero => rfl
      | succ p => exact congrFun (ih shape (fun p => children (some p))) p

/-- Compatibility is required for this telescope, not for unused expressions
in the index language. Data binders extend the environment before checking. -/
def QuotedCode (indices : IndexSyntax I Head)
    (quoteData : ∀ sort, I.Value sort → Tm Head n) (quoteIndex : I.Index → Tm Head n) :
    {context : List I.SortCode} → Code I context → Prop
  | _, .result expression => ∀ environment,
      indices.term expression (quoteEnv quoteData environment) = quoteIndex (I.evalIndex expression environment)
  | _, .data _ body => QuotedCode indices quoteData quoteIndex body
  | _, .recursive expression rest =>
      (∀ environment, indices.term expression (quoteEnv quoteData environment) =
        quoteIndex (I.evalIndex expression environment)) ∧ QuotedCode indices quoteData quoteIndex rest

theorem resultIndex_fields (indices : IndexSyntax I Head)
    (quoteData : ∀ sort, I.Value sort → Tm Head n) (quoteIndex : I.Index → Tm Head n)
    {context : List I.SortCode} (code : Code I context)
    (quoted : QuotedCode indices quoteData quoteIndex code)
    {environment : Env I.Value context} {index : I.Index}
    (shape : Shape code environment index) (children : Position code shape → Tm Head n) :
    resultIndex indices code (quoteEnv quoteData environment) (fields quoteData code shape children) =
      quoteIndex index := by
  induction code with
  | result expression => exact (quoted environment).trans (congrArg quoteIndex shape.down.down)
  | data sort body ih => exact ih quoted shape.2 children
  | recursive expression rest ih => exact ih quoted.2 shape (fun p => children (some p))

theorem recursiveArguments_fields (indices : IndexSyntax I Head)
    (quoteData : ∀ sort, I.Value sort → Tm Head n) (quoteIndex : I.Index → Tm Head n)
    {context : List I.SortCode} (code : Code I context)
    (quoted : QuotedCode indices quoteData quoteIndex code)
    {environment : Env I.Value context} {index : I.Index}
    (shape : Shape code environment index) (children : Position code shape → Tm Head n)
    (call : Tm Head n → Tm Head n → Tm Head n) :
    (recursiveArguments indices code (quoteEnv quoteData environment)
      (fields quoteData code shape children)).map (fun pair => call pair.1 pair.2) =
      results code shape (fun p => call (quoteIndex (next code shape p)) (children p)) := by
  induction code with
  | result => rfl
  | data sort body ih => exact ih quoted shape.2 children
  | recursive expression rest ih =>
      change call (indices.term expression (quoteEnv quoteData environment)) (children none) :: _ = _
      rw [quoted.1]
      exact congrArg (List.cons _) (ih quoted.2 shape (fun p => children (some p)))

variable (admitted : Admitted I [])

/-- Constructor encoding is a fold of the source polynomial, with explicit
guest prefixes. It is a semantic encoding, not an executable storage decoder. -/
noncomputable def encode (quoteData : ∀ sort, I.Value sort → Tm Head n)
    (constructor : String → Tm Head n) :
    ∀ environment index, admitted.Family environment index → Tm Head n :=
  Fix.fold admitted.polynomial (fun _ _ layer =>
    applyArgs (constructor (admitted.constructors.get layer.1.1).name)
      (List.ofFn (fields quoteData (admitted.constructors.get layer.1.1).body layer.1.2 layer.2)))

@[simp] theorem encode_roll (quoteData : ∀ sort, I.Value sort → Tm Head n)
    (constructor : String → Tm Head n) (environment : Env I.Value []) (index : I.Index)
    (shape : admitted.polynomial.Shape environment index)
    (children : ∀ p, admitted.Family environment (admitted.polynomial.next shape p)) :
    encode admitted quoteData constructor environment index (.roll shape children) =
      applyArgs (constructor (admitted.constructors.get shape.1).name)
        (List.ofFn (fields quoteData (admitted.constructors.get shape.1).body shape.2
          (fun p => encode admitted quoteData constructor environment _ (children p)))) := rfl

/-- The encoding agrees with the independent source argument interpretation,
including the selected constructor occurrence and all ordered fields. -/
theorem encode_construct (quoteData : ∀ sort, I.Value sort → Tm Head n)
    (constructor : String → Tm Head n) {environment : Env I.Value []} {index : I.Index}
    (arguments : InventoryArguments admitted.constructors environment
      (admitted.Family environment) index) :
    encode admitted quoteData constructor environment index (admitted.construct arguments) =
      applyArgs (constructor (admitted.constructors.get arguments.1).name)
        (List.ofFn (sourceArguments quoteData (encode admitted quoteData constructor environment)
          (admitted.constructors.get arguments.1).body arguments.2)) := by
  rcases arguments with ⟨occurrence, arguments⟩
  change encode admitted quoteData constructor environment index
    (.roll ⟨occurrence, (Description.encode _ arguments).1⟩ (Description.encode _ arguments).2) = _
  erw [encode_roll, fields_decode, decode_encode]

abbrev Steps (root : RootComputation Head) (left right : Tm Head n) : Prop :=
  Relation.ReflTransGen (StepCore root (fun _ _ => False)) left right

theorem steps_app {root : RootComputation Head} {f g a b : Tm Head n}
    (function : Steps root f g) (argument : Steps root a b) :
    Steps root (.app f a) (.app g b) := by
  have first : Steps root (.app f a) (.app g a) := by
    induction function with
    | refl => exact .refl
    | tail _ step ih => exact .tail ih (.congAppFun step)
  have second : Steps root (.app g a) (.app g b) := by
    induction argument with
    | refl => exact .refl
    | tail _ step ih => exact .tail ih (.congAppArg step)
  exact first.trans second

theorem steps_applyArgs {root : RootComputation Head} {args args' : List (Tm Head n)}
    (arguments : List.Forall₂ (Steps root) args args') {f g : Tm Head n}
    (function : Steps root f g) : Steps root (applyArgs f args) (applyArgs g args') := by
  induction arguments generalizing f g with
  | nil => exact function
  | cons head _ ih => exact ih (steps_app function head)

theorem results_related {α β : Type} {relation : α → β → Prop}
    {context : List I.SortCode} (code : Code I context)
    {environment : Env I.Value context} {index : I.Index}
    (shape : Shape code environment index) (first : Position code shape → α)
    (second : Position code shape → β) (related : ∀ p, relation (first p) (second p)) :
    List.Forall₂ relation (results code shape first) (results code shape second) := by
  induction code with
  | result => exact .nil
  | data sort body ih => exact ih shape.2 first second related
  | recursive expression rest ih =>
      exact .cons (related none)
        (ih shape (fun p => first (some p)) (fun p => second (some p)) (fun p => related (some p)))

private theorem related_append {α β : Type} {relation : α → β → Prop}
    {xs xs' : List α} {ys ys' : List β}
    (first : List.Forall₂ relation xs ys) (second : List.Forall₂ relation xs' ys') :
    List.Forall₂ relation (xs ++ xs') (ys ++ ys') := by
  induction first with
  | nil => exact second
  | cons head _ ih => exact .cons head ih

section Elimination

variable (indices : IndexSyntax I Head) (types : Types.TypeSyntax I Head n)
    (recursor motive : Tm Head n) (method : Fin admitted.constructors.length → Tm Head n)
    (quoteData : ∀ sort, I.Value sort → Tm Head n) (quoteIndex : I.Index → Tm Head n)
    (root : RootComputation Head)

/-- Each guest method implements one dependent constructor method. This
contract quantifies over arbitrary dependent child results; it does not
assume correctness of recursive elimination. -/
def MethodsRealize
    {family : ∀ environment index, admitted.Family environment index → Sort v}
    (displayed : Algebra.Displayed (Algebra.initial admitted.polynomial) family)
    (quoteResult : ∀ environment index value, family environment index value → Tm Head n) : Prop :=
  ∀ environment index (shape : admitted.polynomial.Shape environment index)
    (children : ∀ p, admitted.Family environment (admitted.polynomial.next shape p))
    (hypotheses : ∀ p, family environment (admitted.polynomial.next shape p) (children p)),
    Steps root
      (applyArgs (method shape.1)
        (List.ofFn (fields quoteData (admitted.constructors.get shape.1).body shape.2
          (fun p => encode admitted quoteData types.constructor environment _ (children p))) ++
          results (admitted.constructors.get shape.1).body shape.2
            (fun p => quoteResult environment _ (children p) (hypotheses p))))
      (quoteResult environment index (.roll shape children)
        (displayed.act environment index shape children hypotheses))

/-- Local constructor implementations suffice for the generated eliminator
to compute the actual dependent section at every finite source value.
The relation is forward compatible reduction, with no reverse index steps. -/
theorem recursor_reduces
    (quoted : ∀ occurrence, QuotedCode indices quoteData quoteIndex
      (admitted.constructors.get occurrence).body)
    (roots : ∀ occurrence arguments,
      root.step (Types.endpoints indices admitted occurrence types recursor motive method arguments).1
        (Types.endpoints indices admitted occurrence types recursor motive method arguments).2)
    {family : ∀ environment index, admitted.Family environment index → Sort v}
    (displayed : Algebra.Displayed (Algebra.initial admitted.polynomial) family)
    (quoteResult : ∀ environment index value, family environment index value → Tm Head n)
    (implements : MethodsRealize admitted types method quoteData root displayed quoteResult)
    (environment : Env I.Value []) (index : I.Index) (value : admitted.Family environment index) :
    Steps root
      (Types.recursorAt recursor motive (List.ofFn method) (quoteIndex index)
        (encode admitted quoteData types.constructor environment index value))
      (quoteResult environment index value (displayed.initialSection.toFun environment index value)) := by
  refine Fix.eliminate admitted.polynomial (fun environment index value => Steps root
    (Types.recursorAt recursor motive (List.ofFn method) (quoteIndex index)
      (encode admitted quoteData types.constructor environment index value))
    (quoteResult environment index value (displayed.initialSection.toFun environment index value)))
    ?_ environment index value
  intro environment index shape children ih
  cases environment
  erw [encode_roll, Algebra.Displayed.initialSection_roll]
  let args := fields quoteData (admitted.constructors.get shape.1).body shape.2
    (fun p => encode admitted quoteData types.constructor PUnit.unit _ (children p))
  have first := roots shape.1 args
  have resultIndexEq := resultIndex_fields indices quoteData quoteIndex
    (admitted.constructors.get shape.1).body (quoted shape.1) shape.2
    (fun p => encode admitted quoteData types.constructor PUnit.unit _ (children p))
  change resultIndex indices (admitted.constructors.get shape.1).body PUnit.unit args =
    quoteIndex index at resultIndexEq
  dsimp only [Types.endpoints] at first
  rw [resultIndexEq] at first
  refine Relation.ReflTransGen.head (.root first) ?_
  have recursiveEq := recursiveArguments_fields indices quoteData quoteIndex
    (admitted.constructors.get shape.1).body (quoted shape.1) shape.2
    (fun p => encode admitted quoteData types.constructor PUnit.unit _ (children p))
    (Types.recursorAt recursor motive (List.ofFn method))
  change (recursiveArguments indices (admitted.constructors.get shape.1).body PUnit.unit args).map _ = _
    at recursiveEq
  rw [recursiveEq]
  apply Relation.ReflTransGen.trans _ (implements PUnit.unit index shape children _)
  apply steps_applyArgs _ Relation.ReflTransGen.refl
  apply related_append
  · induction List.ofFn args with
    | nil => exact .nil
    | cons _ _ ih => exact .cons Relation.ReflTransGen.refl ih
  · exact results_related _ shape.2 _ _ ih

/-- The generated package supplies the root-step obligation. A realization
may use a larger root system, but must include the original generated rules. -/
theorem package_reduces {p : Nat} (parameters : Declarations.Parameters I Head p)
    (names : Declarations.Names) (parameterValues : Sub Head p n)
    (covers : ∀ {k} {left right : Tm Head k},
      (Package.computation indices parameters names admitted).support.step left right → root.step left right)
    (quoted : ∀ occurrence, QuotedCode indices quoteData quoteIndex
      (admitted.constructors.get occurrence).body)
    {family : ∀ environment index, admitted.Family environment index → Sort v}
    (displayed : Algebra.Displayed (Algebra.initial admitted.polynomial) family)
    (quoteResult : ∀ environment index value, family environment index value → Tm Head n)
    (implements : MethodsRealize admitted ((parameters.types names).map (subst parameterValues))
      method quoteData root displayed quoteResult)
    (environment : Env I.Value []) (index : I.Index) (value : admitted.Family environment index) :
    Steps root
      (Types.recursorAt (subst parameterValues (Package.recursor parameters names)) motive
        (List.ofFn method) (quoteIndex index)
        (encode admitted quoteData ((parameters.types names).map (subst parameterValues)).constructor
          environment index value))
      (quoteResult environment index value (displayed.initialSection.toFun environment index value)) := by
  apply recursor_reduces admitted indices _ _ motive method quoteData quoteIndex root quoted
    ?_ displayed quoteResult implements environment index value
  intro occurrence arguments
  apply covers
  apply (Instantiation.computation_iff_unfold admitted indices parameters names _ _).mpr
  exact .constructor occurrence parameterValues motive method arguments

end Elimination

#print axioms recursor_reduces
#print axioms package_reduces

end Mettapedia.GSLT.LanguageDef.IndexedInductive.Guest.Meaning
