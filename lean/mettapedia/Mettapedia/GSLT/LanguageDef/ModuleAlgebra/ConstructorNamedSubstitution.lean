import Mettapedia.GSLT.LanguageDef.ModuleAlgebra.NamedSubstitutionElaboration
import Mettapedia.GSLT.LanguageDef.WellSorted

/-!
# Direct constructor-profile named substitution

The module consumer specializes named substitution to resolved first-order
constructor patterns. Its direct structural action agrees with the independent
named action and with observation of the compiled core substitution. This does
not establish a byte-parser or native C implementation correspondence.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleAlgebra.ConstructorNamedSubstitution

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Substitution
open Mettapedia.GSLT.LanguageDef.ModuleAlgebra.NamedSubstitutionElaboration
open Mettapedia.GSLT.LanguageDef.WellSorted

def ConstructorOnly : Pattern → Prop
  | .fvar _ => True
  | .apply _ arguments => ∀ argument ∈ arguments, ConstructorOnly argument
  | _ => False
termination_by pattern => sizeOf pattern
decreasing_by all_goals sizeOf_pattern_dec

/-- A direct action, without allocating a temporary bound level. Other
patterns are outside its admitted profile and have no claimed binder meaning. -/
def substitute (name : String) (replacement : Pattern) : Pattern → Pattern
  | .fvar varName => if varName == name then replacement else .fvar varName
  | .apply head arguments => .apply head (arguments.map (substitute name replacement))
  | pattern => pattern
termination_by pattern => sizeOf pattern
decreasing_by all_goals sizeOf_pattern_dec

theorem agrees_named (name : String) (replacement body : Pattern)
    (profile : ConstructorOnly body) :
    substitute name replacement body = substituteNamedAt 0 name replacement body := by
  induction body using Pattern.inductionOn with
  | hbvar index => simp [ConstructorOnly] at profile
  | hfvar varName => simp [substitute, substituteNamedAt, liftBVars_zero]
  | happly head arguments ih =>
      simp only [ConstructorOnly] at profile
      simp only [substitute, substituteNamedAt]
      congr 1
      apply List.map_congr_left
      intro argument member
      exact ih argument member (profile argument member)
  | hlambda binder body ih => simp [ConstructorOnly] at profile
  | hmultiLambda arity binders body ih => simp [ConstructorOnly] at profile
  | hsubst body replacement ihBody ihReplacement => simp [ConstructorOnly] at profile
  | hcollection kind elements rest ih => simp [ConstructorOnly] at profile

theorem agrees_core (declaration : Declaration)
    (profile : ConstructorOnly declaration.body) :
    substitute declaration.target declaration.replacement declaration.body =
      observeCore (compileDeclaration declaration) := by
  rw [compileDeclaration_adequate]
  exact agrees_named _ _ _ profile

theorem profile_preserved (name : String) (replacement body : Pattern)
    (replacementProfile : ConstructorOnly replacement)
    (bodyProfile : ConstructorOnly body) :
    ConstructorOnly (substitute name replacement body) := by
  induction body using Pattern.inductionOn with
  | hbvar index => simp [ConstructorOnly] at bodyProfile
  | hfvar varName =>
      simp only [substitute]
      split
      · exact replacementProfile
      · simp [ConstructorOnly]
  | happly head arguments ih =>
      simp only [ConstructorOnly] at bodyProfile
      simp only [substitute, ConstructorOnly]
      intro argument member
      obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp member
      exact ih original originalMember (bodyProfile original originalMember)
  | hlambda binder body ih => simp [ConstructorOnly] at bodyProfile
  | hmultiLambda arity binders body ih => simp [ConstructorOnly] at bodyProfile
  | hsubst body replacement ihBody ihReplacement => simp [ConstructorOnly] at bodyProfile
  | hcollection kind elements rest ih => simp [ConstructorOnly] at bodyProfile

/-- The authored body's target has its own type; inserted variables are typed
in the surrounding context, even when they have the same spelling. -/
def withTarget (free : FreeTypeContext) (name : String) (type : TypeExpr) : FreeTypeContext :=
  fun varName => if varName = name then some type else free varName

private theorem representation_preserved (parameter : TermParam)
    (name : String) (replacement body : Pattern)
    (profile : ConstructorOnly body)
    (representation : MatchesParameterRepresentation parameter body) :
    MatchesParameterRepresentation parameter (substitute name replacement body) := by
  cases parameter <;> cases body <;>
    simp_all [ConstructorOnly, MatchesParameterRepresentation]

private theorem map_arguments_typing {language : LanguageDef}
    {source target : FreeTypeContext} {bound : List TypeExpr}
    {arguments : List Pattern} {parameters : List TermParam}
    (action : Pattern → Pattern)
    (typed : ArgumentsHaveTypes language source bound arguments parameters)
    (preserves : ∀ argument ∈ arguments, ∀ type,
      HasType language source bound argument type →
        HasType language target bound (action argument) type)
    (representation : ∀ argument ∈ arguments, ∀ parameter,
      MatchesParameterRepresentation parameter argument →
        MatchesParameterRepresentation parameter (action argument)) :
    ArgumentsHaveTypes language target bound (arguments.map action) parameters := by
  induction arguments generalizing parameters with
  | nil => cases typed; exact .nil
  | cons argument arguments ih =>
      cases typed with
      | cons shape type head tail =>
          exact .cons (representation _ (List.mem_cons_self ..) _ shape) type
            (preserves _ (List.mem_cons_self ..) _ head)
            (ih tail (fun argument member => preserves argument (List.mem_cons_of_mem _ member))
              (fun argument member => representation argument (List.mem_cons_of_mem _ member)))

/-- Sorted insertion preserves the result type without identifying the local
target with a same-named variable in the replacement's ambient context. -/
theorem typing_preserved {language : LanguageDef} {free : FreeTypeContext}
    {bound : List TypeExpr} {name : String} {domain type : TypeExpr}
    {replacement body : Pattern}
    (profile : ConstructorOnly body)
    (typed : HasType language (withTarget free name domain) bound body type)
    (replacementTyped : HasType language free bound replacement domain) :
    HasType language free bound (substitute name replacement body) type := by
  induction body using Pattern.inductionOn generalizing type with
  | hbvar index => simp [ConstructorOnly] at profile
  | hfvar varName =>
      cases typed with
      | fvar lookup =>
          by_cases same : varName = name
          · have typeSame : domain = type := by simpa [withTarget, same] using lookup
            subst type
            simpa [substitute, same] using replacementTyped
          · simpa [substitute, same] using
              (HasType.fvar (by simpa [withTarget, same] using lookup) :
                HasType language free bound (.fvar varName) type)
  | happly head arguments ih =>
      simp only [ConstructorOnly] at profile
      cases typed with
      | constructor member notBare argumentsTyped =>
          simpa only [substitute] using HasType.constructor member notBare
            (map_arguments_typing (substitute name replacement) argumentsTyped
              (fun argument membership type argumentTyped =>
                ih argument membership (profile argument membership) argumentTyped)
              (fun argument membership parameter shape =>
                representation_preserved parameter name replacement argument
                  (profile argument membership) shape))
  | hlambda binder body ih => simp [ConstructorOnly] at profile
  | hmultiLambda arity binders body ih => simp [ConstructorOnly] at profile
  | hsubst body replacement ihBody ihReplacement => simp [ConstructorOnly] at profile
  | hcollection kind elements rest ih => simp [ConstructorOnly] at profile

example : substitute "slot" (.apply "Zero" [])
    (.apply "Pair" [.fvar "slot", .fvar "other"]) =
      .apply "Pair" [.apply "Zero" [], .fvar "other"] := by simp [substitute]

/-- Insertion is simultaneous: occurrences inside the replacement are not
recursively re-substituted. -/
example : substitute "slot" (.apply "Wrap" [.fvar "slot"])
    (.apply "Pair" [.fvar "slot", .fvar "slot"]) =
      .apply "Pair" [.apply "Wrap" [.fvar "slot"], .apply "Wrap" [.fvar "slot"]] := by simp [substitute]

example : ¬ ConstructorOnly (.lambda "x" (.bvar 0)) := by simp [ConstructorOnly]

end Mettapedia.GSLT.LanguageDef.ModuleAlgebra.ConstructorNamedSubstitution
