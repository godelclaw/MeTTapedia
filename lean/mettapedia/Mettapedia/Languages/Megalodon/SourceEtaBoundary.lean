import Mettapedia.Languages.Megalodon.SourceNormalizationInvariant
import Mathlib.Tactic.SplitIfs

/-!
# The publication eta side condition and binder removal

The publication checker asks whether a variable occurs and then shifts by
minus one. Native syntax uses natural indices and a partial binder-removal
operation. They agree when removal is licensed. The publication term-variable
test deliberately stops at type regions; protected scope makes that boundary
sound, including in expanded definitions.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Megalodon.SourceEtaBoundary
open MathdataKernel SourceScopeInvariant

def freeTerm (index : Nat) : Tm → Bool
  | .db found => found == index
  | .app first second | .imp first second => freeTerm index first || freeTerm index second
  | .lam _ body | .all _ body => freeTerm (index + 1) body
  | _ => false

def lowerTerm (cutoff : Nat) : Tm → Tm
  | .db index => if index < cutoff then .db index else .db (index - 1)
  | .named name => .named name
  | .prim index => .prim index
  | .app first second => .app (lowerTerm cutoff first) (lowerTerm cutoff second)
  | .imp first second => .imp (lowerTerm cutoff first) (lowerTerm cutoff second)
  | .lam type body => .lam type (lowerTerm (cutoff + 1) body)
  | .all type body => .all type (lowerTerm (cutoff + 1) body)
  | .typeApp body type => .typeApp (lowerTerm cutoff body) type
  | .typeLam body => .typeLam (lowerTerm cutoff body)
  | .typeAll body => .typeAll (lowerTerm cutoff body)

theorem lowerTerm_closed {body : Tm} {bound : Nat} (scope : Scoped bound body)
    (cutoff : Nat) (inside : bound ≤ cutoff) : lowerTerm cutoff body = body := by
  induction body generalizing bound cutoff with
  | db index => simp [lowerTerm, show index < cutoff from Nat.lt_of_lt_of_le scope inside]
  | named | prim => rfl
  | app _ _ ihf iha | imp _ _ ihf iha => simp [lowerTerm, ihf scope.1 cutoff inside, iha scope.2 cutoff inside]
  | lam _ _ ih | all _ _ ih => simp [lowerTerm, ih scope (cutoff + 1) (by omega)]
  | typeApp _ _ ih | typeLam _ ih | typeAll _ ih => simp [lowerTerm, ih scope cutoff inside]

theorem term_removal {body : Tm} (safe : Protected body) (cutoff : Nat) :
    Tm.dropAt? cutoff body = if freeTerm cutoff body then none else some (lowerTerm cutoff body) := by
  induction body generalizing cutoff with
  | db index =>
      simp only [Tm.dropAt?, freeTerm, lowerTerm]
      split_ifs <;> simp_all
  | named | prim => rfl
  | app first second ihf iha | imp first second ihf iha =>
      simp only [Tm.dropAt?, freeTerm, lowerTerm, ihf safe.1 cutoff, iha safe.2 cutoff]
      by_cases firstFree : freeTerm cutoff first = true <;>
        by_cases secondFree : freeTerm cutoff second = true <;> simp_all
  | lam type body ih | all type body ih =>
      simp only [Tm.dropAt?, freeTerm, lowerTerm, ih safe (cutoff + 1)]
      by_cases bodyFree : freeTerm (cutoff + 1) body = true <;> simp_all
  | typeApp body type _ | typeLam body _ | typeAll body _ =>
      simp only [Tm.dropAt?, freeTerm, lowerTerm, drop_eq safe.1 cutoff (Nat.zero_le cutoff),
        lowerTerm_closed safe.1 cutoff (Nat.zero_le cutoff)]
      rfl

def freeType (index : Nat) : Tp → Bool
  | .var found => found == index
  | .arr domain codomain => freeType index domain || freeType index codomain
  | .all body => freeType (index + 1) body
  | _ => false

def lowerType (cutoff : Nat) : Tp → Tp
  | .var index => if index < cutoff then .var index else .var (index - 1)
  | .prop => .prop
  | .base index => .base index
  | .arr domain codomain => .arr (lowerType cutoff domain) (lowerType cutoff codomain)
  | .all body => .all (lowerType (cutoff + 1) body)

theorem type_removal (body : Tp) (cutoff : Nat) :
    Tp.dropAt? cutoff body = if freeType cutoff body then none else some (lowerType cutoff body) := by
  induction body generalizing cutoff with
  | var index =>
      simp only [Tp.dropAt?, freeType, lowerType]
      split_ifs <;> simp_all
  | prop | base => rfl
  | arr domain codomain ihd ihc =>
      simp only [Tp.dropAt?, freeType, lowerType, ihd cutoff, ihc cutoff]
      by_cases firstFree : freeType cutoff domain = true <;>
        by_cases secondFree : freeType cutoff codomain = true <;> simp_all
  | all body ih =>
      simp only [Tp.dropAt?, freeType, lowerType, ih (cutoff + 1)]
      by_cases bodyFree : freeType (cutoff + 1) body = true <;> simp_all

def freeTypeInTerm (index : Nat) : Tm → Bool
  | .app first second | .imp first second => freeTypeInTerm index first || freeTypeInTerm index second
  | .lam type body | .all type body => freeType index type || freeTypeInTerm index body
  | .typeApp body type => freeTypeInTerm index body || freeType index type
  | .typeLam body | .typeAll body => freeTypeInTerm (index + 1) body
  | _ => false

def lowerTypeInTerm (cutoff : Nat) : Tm → Tm
  | .db index => .db index
  | .named name => .named name
  | .prim index => .prim index
  | .app first second => .app (lowerTypeInTerm cutoff first) (lowerTypeInTerm cutoff second)
  | .imp first second => .imp (lowerTypeInTerm cutoff first) (lowerTypeInTerm cutoff second)
  | .lam type body => .lam (lowerType cutoff type) (lowerTypeInTerm cutoff body)
  | .all type body => .all (lowerType cutoff type) (lowerTypeInTerm cutoff body)
  | .typeApp body type => .typeApp (lowerTypeInTerm cutoff body) (lowerType cutoff type)
  | .typeLam body => .typeLam (lowerTypeInTerm (cutoff + 1) body)
  | .typeAll body => .typeAll (lowerTypeInTerm (cutoff + 1) body)

theorem term_type_removal (body : Tm) (cutoff : Nat) :
    Tm.typeDropAt? cutoff body = if freeTypeInTerm cutoff body then none else some (lowerTypeInTerm cutoff body) := by
  induction body generalizing cutoff with
  | db | named | prim => rfl
  | app first second ihf iha | imp first second ihf iha =>
      simp only [Tm.typeDropAt?, freeTypeInTerm, lowerTypeInTerm, ihf cutoff, iha cutoff]
      by_cases firstFree : freeTypeInTerm cutoff first = true <;>
        by_cases secondFree : freeTypeInTerm cutoff second = true <;> simp_all
  | lam type body ih | all type body ih =>
      simp only [Tm.typeDropAt?, freeTypeInTerm, lowerTypeInTerm, type_removal, ih cutoff]
      by_cases firstFree : freeType cutoff type = true <;>
        by_cases secondFree : freeTypeInTerm cutoff body = true <;> simp_all
  | typeApp body type ih =>
      simp only [Tm.typeDropAt?, freeTypeInTerm, lowerTypeInTerm, type_removal, ih cutoff]
      by_cases firstFree : freeTypeInTerm cutoff body = true <;>
        by_cases secondFree : freeType cutoff type = true <;> simp_all
  | typeLam body ih | typeAll body ih =>
      simp only [Tm.typeDropAt?, freeTypeInTerm, lowerTypeInTerm, ih (cutoff + 1)]
      by_cases bodyFree : freeTypeInTerm (cutoff + 1) body = true <;> simp_all

theorem occupied_term_binder_refused : Tm.dropAt? 0 (.db 0) = none := by decide
theorem higher_term_index_lowered : Tm.dropAt? 0 (.db 2) = some (.db 1) := by decide
theorem occupied_type_binder_refused : Tm.typeDropAt? 0 (.lam (.var 0) (.db 0)) = none := by decide

end Mettapedia.Languages.Megalodon.SourceEtaBoundary
