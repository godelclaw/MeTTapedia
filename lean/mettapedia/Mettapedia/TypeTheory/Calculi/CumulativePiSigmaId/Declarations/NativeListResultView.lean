import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.FormationSensitiveNativeListElimination
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.IntrinsicNativeListMaps
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.IntrinsicNativeListRelatorLevels
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationSensitiveElaboration
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.StructuralWeakHeadSearch

/-!
# Result projection from the native List relational bundle

The source bundle retains a List of child/result pairs and relation evidence
identifying every retained child with its source occurrence. The projection
maps second projection over that actual stored List. It uses the existing
native List-map program and leaves the relation evidence available in the
source bundle. Element and result types remain parameters of the program.

This profile instantiates the existing List/identity/relator declarations at
one common universe level. It introduces no additional computation roots.
-/

set_option autoImplicit false
namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeListResultView
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel
open Presentation Declaration RussellTarski NativeIndexedFamilies

def level : LevelExpr Nat := .param 0
abbrev instantiation := IntrinsicRelatorLevels.levelInstance level
abbrev rules := instantiation.rules

abbrev decoder := IntrinsicRelatorLevels.rootDecoder level

local instance : DecidableRel rules.headTyping :=
  fun a b => inferInstanceAs (Decidable (Tower.rules.headTyping a b))
local instance : DecidablePred rules.isUniverse :=
  fun a => inferInstanceAs (Decidable (Tower.rules.isUniverse a))
local instance : ∀ a b c, Decidable (rules.join a b c) :=
  fun a b c => inferInstanceAs (Decidable (Tower.rules.join a b c))
local instance : DecidableRel rules.cumulative :=
  fun a b => inferInstanceAs (Decidable (Tower.rules.cumulative a b))
local instance : DecidableRel rules.headEq :=
  LevelTower.instDecidableHeadEq

/-- Typing the stored map requires beta/projection comparison only. Native
iota remains part of the profile and its independently checked decoder. -/
def noRootSearch {n : Nat} (_ : Tower.Tm n) : Option (decoder.Code n) := none

def choices : FormationSensitiveElaboration.Choices Tower.Head decoder.Code where
  headType head := some (StructuralTypingReplay.TowerDecisions.headTarget head)
  join first second := match first, second with
    | .sort first, .sort second => some (.sort (.max first second))
    | _, _ => none
  cumulative first second := decide (rules.cumulative first second)
  normalize fuel term := (StructuralWeakHeadSearch.typeView decoder.decode noRootSearch fuel term).term
  conversion fuel left right := StructuralWeakHeadSearch.compareCore decoder.decode noRootSearch fuel left right

def constantPredicate {n : Nat} (result : Tower.Tm n) : Tower.Tm n := .lam (rename wk result)

def packedType {n : Nat} (element predicate : Tower.Tm n) : Tower.Tm n :=
  .sigma element (.app (rename wk predicate) (.var 0))

def packedRelation {n : Nat} (element : Tower.Tm n) : Tower.Tm n :=
  .lam (.lam (.id (rename (fun i => i.succ.succ) element) (.var 1) (.fst (.var 0))))

def bundleType {n : Nat} (element predicate children : Tower.Tm n) : Tower.Tm n :=
  let packed := packedType element predicate
  .sigma (Intrinsic.listApp packed)
    (IntrinsicRelator.mapRelApp (rename wk element) (rename wk packed)
      (rename wk (packedRelation element)) (rename wk children) (.var 0))

def project {n : Nat} (element result bundle : Tower.Tm n) : Tower.Tm n :=
  let packed := packedType element (constantPredicate result)
  subst (fun index : Fin 4 => Fin.cases (.fst bundle)
    (Fin.cases (.lam (.snd (.var 0))) (Fin.cases result (fun _ => packed))) index)
    IntrinsicMaps.nativeMapBody

@[simp] theorem substitute_constantPredicate {n m : Nat} (sigma : Sub Tower.Head n m)
    (result : Tower.Tm n) :
    subst sigma (constantPredicate result) = constantPredicate (subst sigma result) := by
  simp only [constantPredicate, subst, subst_liftSub_wk]

@[simp] theorem substitute_packedType {n m : Nat} (sigma : Sub Tower.Head n m)
    (element predicate : Tower.Tm n) :
    subst sigma (packedType element predicate) = packedType (subst sigma element) (subst sigma predicate) := by
  simp only [packedType, subst, subst_liftSub_wk, liftSub, Fin.cases_zero]

@[simp] theorem substitute_packedRelation {n m : Nat} (sigma : Sub Tower.Head n m)
    (element : Tower.Tm n) :
    subst sigma (packedRelation element) = packedRelation (subst sigma element) := by
  simp only [packedRelation, subst]
  congr 3
  rw [subst_rename, rename_subst]
  apply subst_ext
  intro index
  change rename wk (rename wk (sigma index)) = rename (fun i => i.succ.succ) (sigma index)
  exact rename_comp wk wk (sigma index)

@[simp] theorem substitute_bundleType {n m : Nat} (sigma : Sub Tower.Head n m)
    (element predicate children : Tower.Tm n) :
    subst sigma (bundleType element predicate children) =
      bundleType (subst sigma element) (subst sigma predicate) (subst sigma children) := by
  simp only [bundleType, Intrinsic.listApp, IntrinsicRelator.mapRelApp,
    subst, subst_liftSub_wk, substitute_packedType, substitute_packedRelation, liftSub, Fin.cases_zero]

theorem substitute_project {n m : Nat} (sigma : Sub Tower.Head n m)
    (element result bundle : Tower.Tm n) :
    subst sigma (project element result bundle) =
      project (subst sigma element) (subst sigma result) (subst sigma bundle) := by
  simp only [project, subst_comp]
  apply subst_ext
  intro index
  fin_cases index
  · rfl
  · rfl
  · rfl
  · change subst sigma (packedType element (constantPredicate result)) =
      packedType (subst sigma element) (constantPredicate (subst sigma result))
    simpa only [substitute_constantPredicate] using
      substitute_packedType sigma element (constantPredicate result)

def programme : Tower.Tm 0 :=
  .lam (.lam (.lam (.lam (project (.var 3) (.var 2) (.var 0)))))

def programmeType : Tower.Tm 0 :=
  .pi (sortTm level) (.pi (sortTm level)
    (.pi (Intrinsic.listApp (.var 1))
      (.pi (bundleType (.var 2) (constantPredicate (.var 1)) (.var 0))
        (Intrinsic.listApp (.var 2)))))

def checked (term type : Tower.Tm 0) : Bool :=
  (FormationSensitiveElaboration.elaborate rules decoder choices 128 .nil term type).isSome

theorem checked_sound {term type : Tower.Tm 0} (accepted : checked term type = true) :
    FormationSensitive.Judgment rules .nil term type := by
  obtain ⟨submission, produced⟩ := Option.isSome_iff_exists.mp accepted
  exact FormationSensitiveElaboration.elaborate_sound rules decoder choices 128 .nil term type submission produced

end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeListResultView
