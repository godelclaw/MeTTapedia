import Mettapedia.Algorithms.Compression.TemplateMatching

/-! Stateful filling of named second-order skeleton holes. A vocabulary
supplies finite alternatives per role/name key. One environment is threaded
through all siblings, so choosing a predicate once constrains every later
occurrence of that hole. The ranked syntax and substitution laws are the
same ones used by source abstraction; type admission and example consistency
remain separate obligations. -/

set_option autoImplicit false

namespace Mettapedia.Algorithms.Compression.SkeletonInstantiation

open Mettapedia.GSLT.LanguageDef.GauthierE1
open Mettapedia.GSLT.LanguageDef.GauthierCanonicalSchema
open Mettapedia.GSLT.LanguageDef.GauthierRoleAntiUnification
open TemplateMatching

abbrev Choices := SchemaHole → List Prog

mutual

def terms (choices : Choices) (env : Environment) : SchemaPattern → List (Prog × Environment)
  | .hole role index =>
      let key := (role, index)
      match env key with
      | some value => [(value, env)]
      | none => (choices key).map fun value =>
          (value, fun other => if other = key then some value else env other)
  | .node op children => (forests choices env children).map fun (values, next) => (.node op values, next)

def forests (choices : Choices) (env : Environment) :
    List SchemaPattern → List (List Prog × Environment)
  | [] => [([], env)]
  | first :: rest => (terms choices env first).flatMap fun (value, middle) =>
      (forests choices middle rest).map fun (values, next) => (value :: values, next)

end

mutual

theorem terms_sound (choices : Choices) : ∀ (env next : Environment)
    (pattern : SchemaPattern) (value : Prog), (value, next) ∈ terms choices env pattern →
      Extends next env ∧ expand next pattern = some value
  | env, next, .hole role index, value, found => by
      cases present : env (role, index) with
      | none =>
          simp only [terms, present, List.mem_map] at found
          obtain ⟨chosen, _allowed, equal⟩ := found
          cases equal
          exact assign_sound (by simp [assign, present])
      | some previous =>
          simp only [terms, present, List.mem_singleton, Prod.mk.injEq] at found
          rcases found with ⟨rfl, rfl⟩
          exact ⟨Extends.refl _, present⟩
  | env, next, .node op children, value, found => by
      obtain ⟨⟨values, after⟩, member, equal⟩ := List.mem_map.mp found
      cases equal
      obtain ⟨extended, reconstructed⟩ := forests_sound choices env next children values member
      exact ⟨extended, by simp [expand, reconstructed]⟩

theorem forests_sound (choices : Choices) : ∀ (env next : Environment)
    (patterns : List SchemaPattern) (values : List Prog),
    (values, next) ∈ forests choices env patterns →
      Extends next env ∧ expandList next patterns = some values
  | env, next, [], values, found => by
      simp only [forests, List.mem_singleton, Prod.mk.injEq] at found
      rcases found with ⟨rfl, rfl⟩
      exact ⟨Extends.refl _, rfl⟩
  | env, next, first :: rest, values, found => by
      obtain ⟨⟨value, middle⟩, member, later⟩ := List.mem_flatMap.mp found
      obtain ⟨⟨tail, after⟩, remaining, equal⟩ := List.mem_map.mp later
      cases equal
      obtain ⟨firstExtends, firstResult⟩ := terms_sound choices env middle first value member
      obtain ⟨restExtends, restResult⟩ := forests_sound choices middle next rest tail remaining
      exact ⟨firstExtends.trans restExtends, by
        simp [expandList, expand_mono restExtends first value firstResult, restResult]⟩

end

mutual

/-- A fully assigned skeleton reuses its environment, even when its bound
values are not offered as new vocabulary choices. -/
theorem terms_existing (choices : Choices) : ∀ (env : Environment)
    (pattern : SchemaPattern) (value : Prog), expand env pattern = some value →
      (value, env) ∈ terms choices env pattern
  | env, .hole role index, value, found => by
      simp only [expand] at found
      simp [terms, found]
  | env, .node op children, value, found => by
      cases reconstructed : expandList env children with
      | none => simp [expand, reconstructed] at found
      | some values =>
          simp only [expand, reconstructed, Option.map_some, Option.some.injEq] at found
          subst value
          exact List.mem_map.mpr ⟨(values, env), forests_existing choices env children values reconstructed, rfl⟩

theorem forests_existing (choices : Choices) : ∀ (env : Environment)
    (patterns : List SchemaPattern) (values : List Prog), expandList env patterns = some values →
      (values, env) ∈ forests choices env patterns
  | env, [], values, found => by
      cases Option.some.inj found
      simp [forests]
  | env, first :: rest, values, found => by
      cases firstResult : expand env first with
      | none => simp [expandList, firstResult] at found
      | some head =>
          cases restResult : expandList env rest with
          | none => simp [expandList, firstResult, restResult] at found
          | some tail =>
              simp [expandList, firstResult, restResult] at found
              subst values
              exact List.mem_flatMap.mpr ⟨(head, env), terms_existing choices env first head firstResult,
                List.mem_map.mpr ⟨(tail, env), forests_existing choices env rest tail restResult, rfl⟩⟩

end

theorem chosen_binding_preserved (choices : Choices) (env next : Environment)
    (pattern : SchemaPattern) (value assigned : Prog) (key : SchemaHole)
    (present : env key = some assigned) (generated : (value, next) ∈ terms choices env pattern) :
    next key = some assigned :=
  (terms_sound choices env next pattern value generated).1 key assigned present

/-- Reconstructing the two sides of a rule uses the final shared assignment,
not two independently chosen predicate substitutions. -/
theorem rule_sides_share_environment (choices : Choices) (env next : Environment)
    (left right : SchemaPattern) (leftValue rightValue : Prog)
    (generated : ([leftValue, rightValue], next) ∈ forests choices env [left, right]) :
    expand next left = some leftValue ∧ expand next right = some rightValue := by
  have reconstructed := (forests_sound choices env next [left, right] [leftValue, rightValue] generated).2
  cases firstResult : expand next left <;> cases secondResult : expand next right <;>
    simp [expandList, firstResult, secondResult] at reconstructed
  rcases reconstructed with ⟨rfl, rfl⟩
  exact ⟨rfl, rfl⟩

end Mettapedia.Algorithms.Compression.SkeletonInstantiation
