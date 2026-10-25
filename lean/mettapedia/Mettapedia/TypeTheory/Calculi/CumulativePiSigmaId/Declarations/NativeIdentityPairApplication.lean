import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorIdentityComparison
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.Constants

/-!
# Typed applications of the checked native pair-congruence program

The existing six-argument program is applied through its exact dependent
telescope. The caller supplies typed domain, family, endpoints and identity
evidence. Typed substitution retains each dependent annotation; the result
is the identity of pairs sharing that same first component.
-/

set_option autoImplicit false
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel
open Presentation TypedEquality

namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeIdentityPairApplication
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open NativeVectorIdentityComparison

def domainContext : Tower.Ctx 1 := .snoc .nil (sortTm NativeVectorAll.Universes.CumulativeElimination.upperLevel)
def familyContext : Tower.Ctx 2 := .snoc domainContext (.pi (.var 0) (sortTm NativeVectorAll.Universes.CumulativeElimination.upperLevel))
def headContext : Tower.Ctx 3 := .snoc familyContext (.var 1)
def leftContext : Tower.Ctx 4 := .snoc headContext (.app (.var 1) (.var 0))
def rightContext : Tower.Ctx 5 := .snoc leftContext (.app (.var 2) (.var 1))
def context : Tower.Ctx 6 := .snoc rightContext (.id (.app (.var 3) (.var 2)) (.var 1) (.var 0))

def resultType : Tower.Tm 6 :=
  .id (.sigma (.var 5) (.app (.var 5) (.var 0))) (.pair (.var 3) (.var 2)) (.pair (.var 3) (.var 1))

theorem type_readback : TelescopeAbstraction.closeType context resultType =
    RussellTarski.substLevelsTm (fun _ => NativeVectorAll.Universes.CumulativeElimination.upperLevel)
      NativeIdentityCongruence.Pair.type := rfl

def arguments {n : Nat} (domain family head left right path : Tower.Tm n) : Sub Tower.Head 6 n :=
  consSub path (consSub right (consSub left (consSub head (consSub family (consSub domain Fin.elim0)))))

def application {n : Nat} (domain family head left right path : Tower.Tm n) : Tower.Tm n :=
  TypedEquality.Normalization.appSpine Congruence.Pair.program [domain, family, head, left, right, path]

theorem arguments_typed {n : Nat} {ambient : Tower.Ctx n}
    {domain family head left right path : Tower.Tm n}
    (domainTyped : Typed rules ambient domain (sortTm NativeVectorAll.Universes.CumulativeElimination.upperLevel))
    (familyTyped : Typed rules ambient family (.pi domain (sortTm NativeVectorAll.Universes.CumulativeElimination.upperLevel)))
    (headTyped : Typed rules ambient head domain)
    (leftTyped : Typed rules ambient left (.app family head))
    (rightTyped : Typed rules ambient right (.app family head))
    (pathTyped : Typed rules ambient path (.id (.app family head) left right)) :
    SubstMor rules context ambient (arguments domain family head left right path) := by
  intro index
  fin_cases index
  · exact pathTyped
  · exact rightTyped
  · exact leftTyped
  · exact headTyped
  · exact familyTyped
  · exact domainTyped

theorem apply_typed {n : Nat} {ambient : Tower.Ctx n}
    {domain family head left right path : Tower.Tm n}
    (domainTyped : Typed rules ambient domain (sortTm NativeVectorAll.Universes.CumulativeElimination.upperLevel))
    (familyTyped : Typed rules ambient family (.pi domain (sortTm NativeVectorAll.Universes.CumulativeElimination.upperLevel)))
    (headTyped : Typed rules ambient head domain)
    (leftTyped : Typed rules ambient left (.app family head))
    (rightTyped : Typed rules ambient right (.app family head))
    (pathTyped : Typed rules ambient path (.id (.app family head) left right)) :
    Typed rules ambient (application domain family head left right path)
      (.id (Congruence.Pair.carrier domain family) (.pair head left) (.pair head right)) := by
  have operation : Typed rules ambient Congruence.Pair.program
      (liftClosed (TelescopeAbstraction.closeType context resultType)) := by
    rw [type_readback]
    exact Congruence.Pair.program_typed ambient
  have checked := TypedEquality.Normalization.Typed.telescope_apply
    (arguments_typed domainTyped familyTyped headTyped leftTyped rightTyped pathTyped) operation
  have programReadback : TelescopeAbstraction.applyClosed context (arguments domain family head left right path)
      (Congruence.Pair.program : Tower.Tm n) = application domain family head left right path := rfl
  have resultReadback : subst (arguments domain family head left right path) resultType =
      .id (Congruence.Pair.carrier domain family) (.pair head left) (.pair head right) := rfl
  rw [programReadback, resultReadback] at checked
  exact checked

#print axioms apply_typed

end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeIdentityPairApplication
