import Mettapedia.Logic.HOL.Syntax.NamedElaboration

/-!
# Finite name decorations of intrinsic HOL contexts

A name decoration records one name per typed variable. Distinct decorations
support exact variable lookup, while the lookup soundness law also applies
when names shadow earlier entries. These laws concern names and scope;
no typing or theorem authority is inferred from a spelling.
-/

set_option autoImplicit false
namespace Mettapedia.Logic.HOL.NamedElaboration.BinderNames
universe u v
variable {Base : Type u} {Name : Type v}

def toList : {context : Ctx Base} → BinderNames Base Name context → List Name
  | [], .nil => []
  | _ :: _, .cons name tail => name :: toList tail

def nameOf : {context : Ctx Base} → BinderNames Base Name context →
    {type : Ty Base} → Var context type → Name
  | _, .cons name _, _, .vz => name
  | _, .cons _ tail, _, .vs index => nameOf tail index

theorem nameOf_mem {context : Ctx Base} (names : BinderNames Base Name context)
    {type : Ty Base} (index : Var context type) : nameOf names index ∈ toList names := by
  induction index with
  | vz => cases names; simp [nameOf, toList]
  | vs index ih => cases names; exact List.mem_cons_of_mem _ (ih _)

variable [DecidableEq Name]

theorem lookup?_nameOf {context : Ctx Base} (names : BinderNames Base Name context)
    (distinct : (toList names).Nodup) {type : Ty Base} (index : Var context type) :
    names.lookup? (nameOf names index) = some ⟨type, index⟩ := by
  induction index with
  | vz => cases names; simp [nameOf]
  | @vs context type head index ih =>
      cases names with
      | cons name tail =>
          obtain ⟨absent, tailDistinct⟩ := List.nodup_cons.mp distinct
          have different : name ≠ nameOf tail index := fun same => absent (same ▸ nameOf_mem tail index)
          simp only [nameOf, lookup?_cons_of_ne different, ih tail tailDistinct, Option.map_some]

theorem lookup?_sound {context : Ctx Base} (names : BinderNames Base Name context)
    {name : Name} {type : Ty Base} {index : Var context type}
    (found : names.lookup? name = some ⟨type, index⟩) : nameOf names index = name := by
  induction names with
  | nil => simp at found
  | @cons context head binder tail ih =>
      by_cases same : binder = name
      · subst binder
        simp only [lookup?_cons_self, Option.some.injEq, Sigma.mk.injEq] at found
        obtain ⟨rfl, equal⟩ := found
        cases equal
        rfl
      · rw [lookup?_cons_of_ne same] at found
        cases lookup : tail.lookup? name with
        | none => simp [lookup] at found
        | some resolved =>
            obtain ⟨otherType, otherIndex⟩ := resolved
            simp only [lookup, Option.map_some, Option.some.injEq, Sigma.mk.injEq] at found
            obtain ⟨rfl, equal⟩ := found
            cases equal
            exact ih lookup

theorem lookup?_none_of_not_mem {context : Ctx Base} (names : BinderNames Base Name context)
    {name : Name} (absent : name ∉ toList names) : names.lookup? name = none := by
  cases found : names.lookup? name with
  | none => rfl
  | some resolved =>
      obtain ⟨type, index⟩ := resolved
      exact False.elim (absent ((lookup?_sound names found) ▸ nameOf_mem names index))

theorem nameOf_injective {context : Ctx Base} (names : BinderNames Base Name context)
    (distinct : (toList names).Nodup) {leftType rightType : Ty Base}
    {left : Var context leftType} {right : Var context rightType}
    (same : nameOf names left = nameOf names right) : HEq left right := by
  have equal := (lookup?_nameOf names distinct left).symm.trans
    ((congrArg names.lookup? same).trans (lookup?_nameOf names distinct right))
  exact (Sigma.mk.inj (Option.some.inj equal)).2

#print axioms lookup?_nameOf
#print axioms lookup?_sound
#print axioms nameOf_injective
end Mettapedia.Logic.HOL.NamedElaboration.BinderNames
