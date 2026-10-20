import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.SchemaTableConversionCode

/-!
# Linking retained schema citations between ordered tables

An embedding preserves every complete schema and keeps distinct occurrences
distinct. Relocation validates a citation against its source table before
changing the address. Replay then preserves every result, including refusal,
under the pulled-back target permissions. No typing or package admission is
inferred from this raw certificate comparison.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace SchemaTableConversionCode.Linking

open AlgebraicSchema

variable {Head : Type} {n : Nat}

structure Embedding (source target : SchemaTable Head) where
  address : Fin source.length ↪ Fin target.length
  row : ∀ index, target.get (address index) = source.get index

def Embedding.comp {source middle target : SchemaTable Head}
    (first : Embedding source middle) (second : Embedding middle target) :
    Embedding source target where
  address := first.address.trans second.address
  row index := (second.row (first.address index)).trans (first.row index)

def relocate {source target : SchemaTable Head} (embedding : Embedding source target)
    (code : Code Head n) : Option (Code Head n) :=
  if bound : code.row < source.length then
    some ⟨(embedding.address ⟨code.row, bound⟩).val, code.arguments⟩
  else none

/-- A chain of certificate links agrees with its composed address map.
Every link still validates the original source citation. -/
theorem relocate_comp {source middle target : SchemaTable Head}
    (first : Embedding source middle) (second : Embedding middle target)
    (code : Code Head n) :
    (relocate first code).bind (relocate second) = relocate (first.comp second) code := by
  by_cases bound : code.row < source.length
  · have middleBound := (first.address ⟨code.row, bound⟩).isLt
    simp [relocate, Embedding.comp, bound, middleBound]
  · simp [relocate, bound]

private theorem arguments_equal {first second : Σ arity, Tm Head arity × Tm Head arity}
    (same : first = second) (arguments : List (Tm Head n))
    (firstLength : arguments.length = first.1) (secondLength : arguments.length = second.1) :
    (subst (argumentSub arguments firstLength) first.2.1,
      subst (argumentSub arguments firstLength) first.2.2) =
    (subst (argumentSub arguments secondLength) second.2.1,
      subst (argumentSub arguments secondLength) second.2.2) := by
  cases same
  rfl

/-- Source bounds, exact arities and all finite arguments survive linking.
A target row cannot rescue an invalid source address. -/
theorem decode_relocate {source target : SchemaTable Head}
    (embedding : Embedding source target) (enabled : Fin target.length → Bool)
    (code : Code Head n) :
    (relocate embedding code).bind (decode target enabled) =
      decode source (fun index => enabled (embedding.address index)) code := by
  by_cases bound : code.row < source.length
  · have targetBound := (embedding.address ⟨code.row, bound⟩).isLt
    have row := embedding.row ⟨code.row, bound⟩
    simp only [List.get_eq_getElem] at row
    simp only [relocate, bound, dite_true, Option.bind_some, decode, decodeInstance,
      targetBound, List.get_eq_getElem, row]
    split_ifs <;> simp_all [Instance.endpoints, List.get_eq_getElem]
    exact Prod.mk.inj (arguments_equal row code.arguments _ _)
  · simp [relocate, decode, decodeInstance, bound]

theorem root_inclusion {source target : SchemaTable Head}
    (embedding : Embedding source target) (enabled : Fin target.length → Bool)
    {left right : Tm Head n}
    (step : (root source (fun index => enabled (embedding.address index))).step left right) :
    (root target enabled).step left right := by
  obtain ⟨code, accepted⟩ := decode_complete source _ step
  have linked := (decode_relocate embedding enabled code).trans accepted
  obtain ⟨relocated, _, decoded⟩ := Option.bind_eq_some_iff.mp linked
  exact decode_sound target enabled relocated decoded

def left (source suffix : SchemaTable Head) : Embedding source (source ++ suffix) where
  address := {
    toFun index := ⟨index.val, by simp only [List.length_append]; omega⟩
    inj' := by
      intro first second same
      exact Fin.ext (congrArg (fun value : Fin (source ++ suffix).length => value.val) same) }
  row := by
    intro index
    change (source ++ suffix).get ⟨index.val, _⟩ = source.get index
    simp [List.get_eq_getElem]

def right (prior source : SchemaTable Head) : Embedding source (prior ++ source) where
  address := {
    toFun index := ⟨prior.length + index.val, by simp only [List.length_append]; omega⟩
    inj' := by
      intro first second same
      apply Fin.ext
      have := congrArg (fun value : Fin (prior ++ source).length => value.val) same
      simpa using this }
  row := by
    intro index
    change (prior ++ source).get ⟨prior.length + index.val, _⟩ = source.get index
    simp [List.get_eq_getElem, List.getElem_append_right]

namespace Controls

def first : SchemaTable Unit := [⟨1, .app (.const `f) (.var 0), .var 0⟩]
def second : SchemaTable Unit := [⟨1, .app (.const `g) (.var 0), .var 0⟩]
def valid : Code Unit 1 := ⟨0, [.var 0]⟩
def foreign : Code Unit 1 := ⟨1, [.var 0]⟩

def verdicts : List (String × Bool) := [
  ("left schema links", ((relocate (left first second) valid).bind
    (decode (first ++ second) (fun _ => true))).isSome),
  ("right schema links", (relocate (right first second) valid).map Code.row == some 1),
  ("right schema retains its arguments", (relocate (right first second) valid).map
    Code.arguments == some valid.arguments),
  ("target has a row at the foreign source address", (decode (first ++ second)
    (fun _ => true) foreign).isSome),
  ("source-invalid left address cannot change owners", (relocate (left first second) foreign).isNone),
  ("source-invalid right address cannot change owners", (relocate (right first second) foreign).isNone),
  ("target permissions survive relocation", ((relocate (right first second) valid).bind
    (decode (first ++ second) (fun index => index.val == 0))).isNone)]

theorem all_verdicts : verdicts.all Prod.snd = true := by decide

end Controls
end SchemaTableConversionCode.Linking
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
