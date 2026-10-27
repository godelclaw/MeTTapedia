import Mettapedia.Algorithms.Compression.TemplateMatching
import Mathlib.Data.List.Basic

/-!
# Explicit parameter ports for first-order helper bodies

Original role/index keys are assigned distinct ports in first-occurrence order.
The helper body and transported argument environment reconstruct the same
source as the original schema. Uniform port storage does not grant permission
to evaluate code arguments: that is a separate argument-demand obligation.
-/

set_option autoImplicit false

namespace Mettapedia.Algorithms.Compression.TemplateExport

open Mettapedia.GSLT.LanguageDef.GauthierE1
open Mettapedia.GSLT.LanguageDef.GauthierRoleAntiUnification
open Mettapedia.GSLT.LanguageDef.GauthierCanonicalSchema
open TemplateMatching

mutual
def body (parameters : List SchemaHole) : SchemaPattern → SchemaPattern
  | .hole role index => .hole .value (parameters.idxOf (role, index))
  | .node op children => .node op (bodies parameters children)

def bodies (parameters : List SchemaHole) : List SchemaPattern → List SchemaPattern
  | [] => []
  | head :: tail => body parameters head :: bodies parameters tail
end

def arguments (parameters : List SchemaHole) (source : Environment) : Environment :=
  fun key => if key.1 = .value then parameters[key.2]?.bind source else none

theorem expand_body (parameters : List SchemaHole) (source : Environment) :
    ∀ pattern, (∀ key ∈ schemaOccurrences pattern, key ∈ parameters) →
      expand (arguments parameters source) (body parameters pattern) = expand source pattern := by
  apply SchemaPattern.rec
    (motive_1 := fun pattern => (∀ key ∈ schemaOccurrences pattern, key ∈ parameters) →
      expand (arguments parameters source) (body parameters pattern) = expand source pattern)
    (motive_2 := fun patterns => (∀ key ∈ schemaOccurrencesList patterns, key ∈ parameters) →
      expandList (arguments parameters source) (bodies parameters patterns) = expandList source patterns)
  · intro role index covered
    have present : (role, index) ∈ parameters := covered _ (by simp [schemaOccurrences])
    simp [body, expand, arguments, List.getElem?_idxOf present]
  · intro op children ih covered
    simpa only [body, expand] using congrArg (Option.map (Prog.node op)) (ih covered)
  · intro covered
    rfl
  · intro head tail headResult tailResult covered
    have headCovered : ∀ key ∈ schemaOccurrences head, key ∈ parameters := by
      intro key present
      exact covered key (List.mem_append_left _ present)
    have tailCovered : ∀ key ∈ schemaOccurrencesList tail, key ∈ parameters := by
      intro key present
      exact covered key (List.mem_append_right _ present)
    simp only [bodies, expandList, headResult headCovered, tailResult tailCovered]

def parameters (pattern : SchemaPattern) : List SchemaHole := (schemaOccurrences pattern).eraseDups

theorem expansion_preserved (pattern : SchemaPattern) (source : Environment) :
    expand (arguments (parameters pattern) source) (body (parameters pattern) pattern) =
      expand source pattern := by
  apply expand_body
  intro key present
  simpa [parameters] using present

theorem matched_source_reconstructed (pattern : SchemaPattern) (value : Prog)
    (before after : Environment) (matched : matchPattern before pattern value = some after) :
    expand (arguments (parameters pattern) after) (body (parameters pattern) pattern) = some value := by
  rw [expansion_preserved]
  exact (matchPattern_sound before after pattern value matched).2

theorem parameter_indices_distinct (ports : List SchemaHole) (left right : SchemaHole)
    (present : left ∈ ports) (different : left ≠ right) : ports.idxOf left ≠ ports.idxOf right := by
  intro same
  exact different ((List.idxOf_inj present).mp same)

theorem code_and_value_ports_remain_distinct :
    let ports : List SchemaHole := [(.code, 0), (.value, 0)]
    ports.idxOf (.code, 0) ≠ ports.idxOf (.value, 0) := by decide

theorem omitting_a_parameter_loses_reconstruction :
    let pattern := SchemaPattern.hole .value 0
    let source : Environment := fun key => if key = (.value, 0) then some (.node 7 []) else none
    expand source pattern = some (.node 7 []) ∧
      expand (arguments [] source) (body [] pattern) = none := by
  constructor <;> rfl

end Mettapedia.Algorithms.Compression.TemplateExport
