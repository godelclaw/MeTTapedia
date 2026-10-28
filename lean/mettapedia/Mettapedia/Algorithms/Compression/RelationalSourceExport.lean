import Mettapedia.Algorithms.Compression.PortableValueWire
import Mettapedia.Algorithms.Compression.SourceClosureFrames

/-!
# Finite relational programs lowered to value-entry source operations

The source-side IR uses explicit input variables, primitive applications,
single-evaluation let bindings, alternatives and Cartesian sequence maps.
The compiler independently lowers the MIL identity/chain/choice/map grammar.
Its semantics preserve ordered answer occurrences, including duplicates and
empty failure. Primitive meanings are supplied independently, not defined by
the compiler's output. This is a finite pure relational model, not a proof of
native evaluation, source admission, exceptional control flow or arbitrary
effectful callbacks. Source-variable framing and ready/delayed adapters retain
their separate common owners.
-/

set_option autoImplicit false

namespace Mettapedia.Algorithms.Compression.RelationalSourceExport

abbrev Value := PortableValueWire.Value
abbrev Primitives := Nat → Value → List Value
abbrev Environment := Nat → Value

inductive Program where
  | ref (index : Nat)
  | identity (inner : Program)
  | chain (first second : Program)
  | choice (first second : Program)
  | map (inner : Program)

def mapAnswers (apply : Value → List Value) : List Value → List (List Value)
  | [] => [[]]
  | first :: rest => (apply first).flatMap fun value =>
      (mapAnswers apply rest).map (value :: ·)

def run (primitives : Primitives) : Program → Value → List Value
  | .ref index, input => primitives index input
  | .identity inner, input => run primitives inner input
  | .chain first second, input => (run primitives first input).flatMap (run primitives second)
  | .choice first second, input => run primitives first input ++ run primitives second input
  | .map inner, .expr items => (mapAnswers (run primitives inner) items).map PortableValueWire.Value.expr
  | .map _, _ => []

inductive Code where
  | variable (index : Nat)
  | primitive (index : Nat) (argument : Code)
  | bind (index : Nat) (value body : Code)
  | alternatives (first second : Code)
  | sequenceMap (index : Nat) (items body : Code)

def update (environment : Environment) (index : Nat) (value : Value) : Environment :=
  fun other => if other = index then value else environment other

def eval (primitives : Primitives) (environment : Environment) : Code → List Value
  | .variable index => [environment index]
  | .primitive index argument => (eval primitives environment argument).flatMap (primitives index)
  | .bind index value body => (eval primitives environment value).flatMap fun result =>
      eval primitives (update environment index result) body
  | .alternatives first second => eval primitives environment first ++ eval primitives environment second
  | .sequenceMap index items body => (eval primitives environment items).flatMap fun input =>
      match input with
      | .expr values => (mapAnswers (fun value => eval primitives (update environment index value) body) values).map PortableValueWire.Value.expr
      | _ => []

def compile : Program → Nat → Nat → Code × Nat
  | .ref index, input, next => (.primitive index (.variable input), next)
  | .identity inner, input, next => compile inner input next
  | .chain first second, input, next =>
      let left := compile first input (next + 1)
      let right := compile second next left.2
      (.bind next left.1 right.1, right.2)
  | .choice first second, input, next =>
      let left := compile first input next
      let right := compile second input left.2
      (.alternatives left.1 right.1, right.2)
  | .map inner, input, next =>
      let body := compile inner next (next + 1)
      (.sequenceMap next (.variable input) body.1, body.2)

def locals : Code → List Nat
  | .variable _ => []
  | .primitive _ argument => locals argument
  | .bind index value body => index :: (locals value ++ locals body)
  | .alternatives first second => locals first ++ locals second
  | .sequenceMap index items body => index :: (locals items ++ locals body)

theorem compile_allocations (program : Program) : ∀ input next,
    next ≤ (compile program input next).2 ∧
      ∀ index ∈ locals (compile program input next).1,
        next ≤ index ∧ index < (compile program input next).2 := by
  induction program with
  | ref index => intro input next; simp [compile, locals]
  | identity inner ih => exact ih
  | chain first second ihFirst ihSecond =>
      intro input next
      have left := ihFirst input (next + 1)
      have right := ihSecond next (compile first input (next + 1)).2
      simp only [compile, locals]
      refine ⟨by omega, fun index member => ?_⟩
      simp only [List.mem_cons, List.mem_append] at member
      rcases member with rfl | leftMember | rightMember
      · omega
      · have bounds := left.2 index leftMember; omega
      · have bounds := right.2 index rightMember; omega
  | choice first second ihFirst ihSecond =>
      intro input next
      have left := ihFirst input next
      have right := ihSecond input (compile first input next).2
      simp only [compile, locals]
      refine ⟨by omega, fun index member => ?_⟩
      rcases List.mem_append.mp member with leftMember | rightMember
      · have bounds := left.2 index leftMember; omega
      · have bounds := right.2 index rightMember; omega
  | map inner ih =>
      intro input next
      have body := ih next (next + 1)
      simp only [compile, locals, List.nil_append, List.mem_cons]
      refine ⟨by omega, fun index member => ?_⟩
      rcases member with rfl | inside
      · omega
      · have bounds := body.2 index inside; omega

/-- Reserved helper slots and the entered input cannot be shadowed by any
composition-local binder emitted after the source environment's fresh index. -/
theorem generated_locals_avoid_prefix (program : Program) (input next reserved index : Nat)
    (before : reserved < next) (generated : index ∈ locals (compile program input next).1) :
    index ≠ reserved := by
  have bounded := (compile_allocations program input next).2 index generated
  omega

theorem compile_preserves (primitives : Primitives) (program : Program) :
    ∀ environment input next,
      eval primitives environment (compile program input next).1 = run primitives program (environment input) := by
  induction program with
  | ref index => intro environment input next; simp [compile, eval, run]
  | identity inner ih => exact ih
  | chain first second ihFirst ihSecond =>
      intro environment input next
      simp only [compile, eval]
      rw [ihFirst]
      have body : (fun value => eval primitives (update environment next value)
          (compile second next (compile first input (next + 1)).2).1) = run primitives second := by
        funext value
        simpa [update] using
          ihSecond (update environment next value) next (compile first input (next + 1)).2
      rw [body]
      rfl
  | choice first second ihFirst ihSecond =>
      intro environment input next
      simp only [compile, eval, ihFirst, ihSecond, run]
  | map inner ih =>
      intro environment input next
      simp only [compile, eval, List.flatMap_singleton]
      have body : (fun value => eval primitives (update environment next value)
          (compile inner next (next + 1)).1) = run primitives inner := by
        funext value
        simpa [update] using ih (update environment next value) next (next + 1)
      rw [body]
      cases environment input <;> rfl

theorem exported_queries_preserve_occurrences (primitives : Primitives) (program : Program)
    (inputs : List Value) (environment : Value → Environment) (input next : Nat)
    (entered : ∀ value, environment value input = value) :
    inputs.map (fun value => eval primitives (environment value) (compile program input next).1) =
      inputs.map (run primitives program) := by
  apply List.map_congr_left
  intro value _
  rw [compile_preserves, entered]

theorem choice_multiplicity_preserved (primitives : Primitives) (program : Program)
    (environment : Environment) (input next : Nat) :
    eval primitives environment (compile (.choice program program) input next).1 =
      run primitives program (environment input) ++ run primitives program (environment input) := by
  rw [compile_preserves]
  rfl

theorem failed_prefix_stays_failed (primitives : Primitives) (first second : Program)
    (environment : Environment) (input next : Nat) (failed : run primitives first (environment input) = []) :
    eval primitives environment (compile (.chain first second) input next).1 = [] := by
  rw [compile_preserves]
  simp [run, failed]

theorem empty_map_has_one_empty_answer (primitives : Primitives) (program : Program)
    (environment : Environment) (input next : Nat) (empty : environment input = .expr []) :
    eval primitives environment (compile (.map program) input next).1 = [.expr []] := by
  rw [compile_preserves]
  simp [run, empty, mapAnswers]

theorem map_failed_element_has_no_answer (apply : Value → List Value) (first : Value) (rest : List Value)
    (failed : apply first = []) : mapAnswers apply (first :: rest) = [] := by
  simp [mapAnswers, failed]

namespace Controls

def token : Value := .literal .symbol (PortableValueWire.word [116, 111, 107, 101, 110])
def duplicate : Primitives := fun _ value => [value, value]
def nowhere : Primitives := fun _ _ => []
def environment : Environment := fun _ => token

theorem duplicate_choice_has_four_occurrences :
    eval duplicate environment (compile (.choice (.ref 0) (.ref 0)) 3 4).1 =
      [token, token, token, token] := by
  rw [compile_preserves]
  rfl

theorem failed_chain_cannot_return_original_input :
    eval nowhere environment (compile (.chain (.ref 0) (.ref 1)) 3 4).1 = [] := by
  rw [compile_preserves]
  rfl

theorem map_choice_has_cartesian_multiplicity :
    (mapAnswers (run duplicate (.choice (.ref 0) (.ref 0))) [token, token]).length = 16 := by decide

theorem reserved_helpers_are_not_generated_locals :
    ∀ index ∈ locals (compile (.chain (.ref 0) (.map (.ref 1))) 3 4).1, index ≠ 0 := by
  intro index generated
  exact generated_locals_avoid_prefix _ 3 4 0 index (by decide) generated

end Controls

#print axioms compile_allocations
#print axioms generated_locals_avoid_prefix
#print axioms compile_preserves
#print axioms exported_queries_preserve_occurrences
#print axioms choice_multiplicity_preserved
#print axioms failed_prefix_stays_failed
#print axioms empty_map_has_one_empty_answer
#print axioms map_failed_element_has_no_answer
#print axioms Controls.duplicate_choice_has_four_occurrences
#print axioms Controls.failed_chain_cannot_return_original_input
#print axioms Controls.map_choice_has_cartesian_multiplicity
#print axioms Controls.reserved_helpers_are_not_generated_locals

end Mettapedia.Algorithms.Compression.RelationalSourceExport
