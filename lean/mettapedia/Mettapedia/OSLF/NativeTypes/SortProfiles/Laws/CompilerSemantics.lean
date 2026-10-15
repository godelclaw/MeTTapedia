import Mettapedia.OSLF.NativeTypes.SortProfiles.Laws.Compiler

open Mettapedia.OSLF.Framework

/-!
# Source agreement of the display-law compiler

The source evaluator recursively interprets actual pattern headers and
children. It does not call the term compiler. The comparison accounts for
binders and explicit substitutions as retained display syntax; the execution
semantics of these nodes is a separate scoped contract.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.SortProfiles.Laws.Compiler

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.UniversalAlgebra
open Mettapedia.OSLF.Framework.ModalHypercube (HSort)

def interpret? (language : LanguageDef) (model : Model (signature language) HSort)
    (key : Key) (arguments : List HSort) : Option HSort := do
  let operation ← operation? language key
  if length : arguments.length = (signature language).arity operation then
    some (model.interpret operation fun index =>
      arguments[index.val]'(by rw [length]; exact index.isLt))
  else none

mutual

/-- Independent evaluation of the original authored pattern. -/
def evaluate? (language : LanguageDef) (names : List String)
    (model : Model (signature language) HSort) (valuation : Nat → HSort) :
    Pattern → Option HSort
  | .bvar index => interpret? language model (.bound index) []
  | .fvar name => (variableIndex? names name).map valuation
  | .apply constructor arguments =>
      (evaluateList? language names model valuation arguments).bind
        (interpret? language model (.constructor constructor arguments.length))
  | .lambda binder body =>
      (evaluate? language names model valuation body).bind fun value =>
        interpret? language model (.binder binder) [value]
  | .multiLambda arity binders body =>
      (evaluate? language names model valuation body).bind fun value =>
        interpret? language model (.multiBinder arity binders) [value]
  | .subst body replacement =>
      (evaluate? language names model valuation body).bind fun left =>
        (evaluate? language names model valuation replacement).bind fun right =>
          interpret? language model .substitution [left, right]
  | .collection kind elements rest =>
      (evaluateList? language names model valuation elements).bind fun values =>
        match rest with
        | none => interpret? language model (.collection kind elements.length false) values
        | some name => (variableIndex? names name).bind fun index =>
            interpret? language model (.collection kind elements.length true)
              (values ++ [valuation index])

def evaluateList? (language : LanguageDef) (names : List String)
    (model : Model (signature language) HSort) (valuation : Nat → HSort) :
    List Pattern → Option (List HSort)
  | [] => some []
  | pattern :: patterns => (evaluate? language names model valuation pattern).bind fun first =>
      (evaluateList? language names model valuation patterns).map (List.cons first)

end

theorem evaluate_assemble (language : LanguageDef) (model : Model (signature language) HSort)
    (valuation : Nat → HSort) (key : Key) (arguments : List (Term (signature language))) :
    (assemble? language key arguments).map (Term.evaluate model valuation) =
      interpret? language model key (arguments.map (Term.evaluate model valuation)) := by
  unfold assemble? interpret?
  cases chosen : operation? language key with
  | none => rfl
  | some operation =>
    dsimp only [Bind.bind, Option.bind]
    simp only [List.length_map]
    split
    · simp [Term.evaluate, List.getElem_map]
    · rfl

private theorem option_map_assemble (language : LanguageDef)
    (model : Model (signature language) HSort) (valuation : Nat → HSort) (key : Key)
    (arguments : Option (List (Term (signature language)))) :
    (arguments.bind (assemble? language key)).map (Term.evaluate model valuation) =
      (arguments.map (List.map (Term.evaluate model valuation))).bind (interpret? language model key) := by
  cases arguments with
  | none => rfl
  | some values => exact evaluate_assemble language model valuation key values

mutual

/-- The actual compiler agrees with the independently evaluated source tree. -/
theorem encode_evaluate (language : LanguageDef) (names : List String)
    (model : Model (signature language) HSort) (valuation : Nat → HSort) :
    (pattern : Pattern) →
      (encode language names pattern).map (Term.evaluate model valuation) =
        evaluate? language names model valuation pattern
  | .bvar index => evaluate_assemble language model valuation (.bound index) []
  | .fvar name => by
      simp only [encode, evaluate?, Option.map_map, Function.comp_def, Term.evaluate]
  | .apply constructor arguments => by
      simp only [encode, evaluate?]
      rw [option_map_assemble, encodeList_evaluate]
  | .lambda binder body => by
      simp only [encode, evaluate?, ← encode_evaluate language names model valuation body]
      cases encoded : encode language names body with
      | none => rfl
      | some value =>
        simpa only [Option.map_some, Option.bind_some, List.map_cons, List.map_nil] using
          evaluate_assemble language model valuation (.binder binder) [value]
  | .multiLambda arity binders body => by
      simp only [encode, evaluate?, ← encode_evaluate language names model valuation body]
      cases encoded : encode language names body with
      | none => rfl
      | some value =>
        simpa only [Option.map_some, Option.bind_some, List.map_cons, List.map_nil] using
          evaluate_assemble language model valuation (.multiBinder arity binders) [value]
  | .subst body replacement => by
      simp only [encode, evaluate?, ← encode_evaluate language names model valuation body,
        ← encode_evaluate language names model valuation replacement]
      cases encodedBody : encode language names body with
      | none => rfl
      | some left =>
        cases encodedReplacement : encode language names replacement with
        | none => rfl
        | some right =>
          simpa only [Option.map_some, Option.bind_some, List.map_cons, List.map_nil] using
            evaluate_assemble language model valuation .substitution [left, right]
  | .collection kind elements rest => by
      simp only [encode, evaluate?, ← encodeList_evaluate language names model valuation elements]
      cases encoded : encodeList language names elements with
      | none => rfl
      | some values =>
        cases rest with
        | none =>
            simpa only [Option.map_some, Option.bind_some] using
              evaluate_assemble language model valuation (.collection kind elements.length false) values
        | some name =>
            cases found : variableIndex? names name with
            | none => simp only [found, Option.bind_none, Option.bind_some, Option.map_some, Option.map_none]
            | some index =>
                have compared := evaluate_assemble language model valuation
                  (.collection kind elements.length true) (values ++ [.var index])
                rw [List.map_append, List.map_cons, List.map_nil] at compared
                simpa only [found, Option.map_some, Option.bind_some, Term.evaluate] using compared

theorem encodeList_evaluate (language : LanguageDef) (names : List String)
    (model : Model (signature language) HSort) (valuation : Nat → HSort) :
    (patterns : List Pattern) →
      (encodeList language names patterns).map (List.map (Term.evaluate model valuation)) =
        evaluateList? language names model valuation patterns
  | [] => rfl
  | pattern :: patterns => by
      simp only [encodeList, evaluateList?,
        ← encode_evaluate language names model valuation pattern,
        ← encodeList_evaluate language names model valuation patterns]
      cases encode language names pattern <;> cases encodeList language names patterns <;> rfl

end

theorem source_evaluation_of_encoding (language : LanguageDef) (names : List String)
    (model : Model (signature language) HSort) (valuation : Nat → HSort)
    (pattern : Pattern) (term : Term (signature language))
    (encoded : encode language names pattern = some term) :
    evaluate? language names model valuation pattern = some (term.evaluate model valuation) := by
  rw [← encode_evaluate, encoded]
  rfl

theorem encodeLaw_components (language : LanguageDef) (law : Law)
    (equation : Mettapedia.UniversalAlgebra.Equation (signature language))
    (encoded : encodeLaw language law = some equation) :
    unresolved language law = [] ∧
      encode language (law.context.map Prod.fst) law.left = some equation.1 ∧
      encode language (law.context.map Prod.fst) law.right = some equation.2 := by
  unfold encodeLaw at encoded
  split at encoded
  · rename_i complete
    obtain ⟨left, leftEncoded, rest⟩ := Option.bind_eq_some_iff.mp encoded
    obtain ⟨right, rightEncoded, pair⟩ := Option.bind_eq_some_iff.mp rest
    have same := Option.some.inj pair
    cases same
    exact ⟨complete, leftEncoded, rightEncoded⟩
  · cases encoded

theorem encodeLaw_exists_of_no_diagnostics (language : LanguageDef) (law : Law)
    (complete : unresolved language law = []) :
    ∃ equation, encodeLaw language law = some equation := by
  cases leftEncoded : encode language (law.context.map Prod.fst) law.left with
  | none => simp [unresolved, leftEncoded] at complete
  | some left =>
    cases rightEncoded : encode language (law.context.map Prod.fst) law.right with
    | none => simp [unresolved, rightEncoded] at complete
    | some right => exact ⟨(left, right), by simp [encodeLaw, complete, leftEncoded, rightEncoded]⟩

def SourceLawHolds (language : LanguageDef) (law : Law)
    (vertex : Mettapedia.OSLF.NativeTypes.SortProfiles.EquationalCenter.Vertex (signature language)) : Prop :=
  ∀ valuation, ∃ value,
    evaluate? language (law.context.map Prod.fst)
      (Mettapedia.OSLF.NativeTypes.SortProfiles.EquationalCenter.model _ vertex) valuation law.left = some value ∧
    evaluate? language (law.context.map Prod.fst)
      (Mettapedia.OSLF.NativeTypes.SortProfiles.EquationalCenter.model _ vertex) valuation law.right = some value

theorem encoded_law_source_iff (language : LanguageDef) (law : Law)
    (equation : Mettapedia.UniversalAlgebra.Equation (signature language))
    (encoded : encodeLaw language law = some equation)
    (vertex : Mettapedia.OSLF.NativeTypes.SortProfiles.EquationalCenter.Vertex (signature language)) :
    SourceLawHolds language law vertex ↔
      equation.Holds (Mettapedia.OSLF.NativeTypes.SortProfiles.EquationalCenter.model _ vertex) := by
  obtain ⟨_, leftEncoded, rightEncoded⟩ := encodeLaw_components language law equation encoded
  constructor
  · intro holds valuation
    obtain ⟨value, leftEval, rightEval⟩ := holds valuation
    rw [source_evaluation_of_encoding _ _ _ _ _ _ leftEncoded] at leftEval
    rw [source_evaluation_of_encoding _ _ _ _ _ _ rightEncoded] at rightEval
    exact (Option.some.inj leftEval).trans (Option.some.inj rightEval).symm
  · intro holds valuation
    refine ⟨equation.1.evaluate _ valuation,
      source_evaluation_of_encoding _ _ _ _ _ _ leftEncoded, ?_⟩
    rw [source_evaluation_of_encoding _ _ _ _ _ _ rightEncoded, holds valuation]

theorem complete_laws (language : LanguageDef) (laws : List Law)
    (complete : (compileLaws language laws).diagnostics = [])
    (law : Law) (member : law ∈ laws) : unresolved language law = [] := by
  apply List.flatMap_eq_nil_iff.mp complete law member

/-- A successful table check is exactly the universal interpretation of all
original source laws; unsupported laws remain unresolved. -/
theorem compiled_check_exact_source (language : LanguageDef) (laws : List Law)
    (vertex : Mettapedia.OSLF.NativeTypes.SortProfiles.EquationalCenter.Vertex (signature language)) :
    (compileLaws language laws).check? vertex = some true ↔
      (compileLaws language laws).diagnostics = [] ∧
        ∀ law ∈ laws, SourceLawHolds language law vertex := by
  rw [Compilation.check?_true_iff, Mettapedia.OSLF.NativeTypes.SortProfiles.EquationalCenter.stable_iff_satisfies]
  constructor
  · rintro ⟨complete, satisfies⟩
    refine ⟨complete, ?_⟩
    intro law member
    obtain ⟨equation, encoded⟩ := encodeLaw_exists_of_no_diagnostics language law
      (complete_laws language laws complete law member)
    exact (encoded_law_source_iff _ _ _ encoded vertex).mpr
      (satisfies equation ((compiled_equation_member _ _ _).mpr ⟨law, member, encoded⟩))
  · rintro ⟨complete, source⟩
    refine ⟨complete, ?_⟩
    intro equation member
    obtain ⟨law, declared, encoded⟩ := (compiled_equation_member _ _ _).mp member
    exact (encoded_law_source_iff _ _ _ encoded vertex).mp (source law declared)

end Mettapedia.OSLF.NativeTypes.SortProfiles.Laws.Compiler
