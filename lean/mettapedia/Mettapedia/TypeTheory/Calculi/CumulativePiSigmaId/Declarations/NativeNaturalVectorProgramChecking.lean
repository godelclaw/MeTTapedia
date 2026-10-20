import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeNaturalVectorProgramEvidence
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.RecursorDerivation

/-!
# Kernel replay of the emitted dependent append evidence

The data file is produced outside the logical kernel. These checks use the
independently maintained formation-sensitive replay against the original
program, type and universe instance. No execution of the evidence producer
is part of the proof, and no claim of native C refinement is made here.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeNaturalVectorFamilies
namespace Programs

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation

local instance : DecidableRel rules.headTyping :=
  fun h u => inferInstanceAs (Decidable (Tower.rules.headTyping h u))
local instance : DecidablePred rules.isUniverse :=
  fun h => inferInstanceAs (Decidable (Tower.rules.isUniverse h))
local instance : ∀ u v w, Decidable (rules.join u v w) :=
  fun u v w => inferInstanceAs (Decidable (Tower.rules.join u v w))
local instance : DecidableRel rules.cumulative :=
  fun u v => inferInstanceAs (Decidable (Tower.rules.cumulative u v))
local instance : DecidableRel rules.headEq :=
  fun h u => inferInstanceAs (Decidable (Tower.rules.headEq h u))

def appendChecked : Bool :=
  FormationSensitiveElaboration.replay rules decoder .nil appendTerm appendType appendEvidence

theorem appendChecked_true : appendChecked = true := by decide +kernel

/-- The entire dependent function is checked in the selected declaration
instance, including the schematic element universe and both length indices. -/
theorem append_typed : FormationSensitive.Judgment rules .nil appendTerm appendType :=
  FormationSensitiveElaboration.replay_sound rules decoder appendChecked_true

def changedType : Tower.Tm 0 := TelescopeAbstraction.closeType appendContext
  (vecApp (.var 4) (.var 2))

def changedTerm : Tower.Tm 0 := TelescopeAbstraction.closeTerm appendContext (.var 0)

def changedTypeCheck :=
  FormationSensitiveElaboration.replay rules decoder .nil appendTerm changedType appendEvidence

def changedTermCheck :=
  FormationSensitiveElaboration.replay rules decoder .nil changedTerm appendType appendEvidence

def forgedRootCheck :=
  FormationSensitiveElaboration.replay rules decoder .nil appendTerm appendType
    { appendEvidence with term := .headType }

/-- Refusals concern these submitted certificates, not general unprovability. -/
theorem changedType_refused : changedTypeCheck = false := by decide +kernel
theorem changedTerm_refused : changedTermCheck = false := by decide +kernel
theorem forgedRoot_refused : forgedRootCheck = false := by decide +kernel

def verdicts : List (String × Bool) := [
  ("dependent append finite evidence checks", appendChecked),
  ("dependent append changed result index refused", !changedTypeCheck),
  ("dependent append changed program refused", !changedTermCheck),
  ("dependent append forged root rule refused", !forgedRootCheck)]

theorem all_verdicts : verdicts.all (·.2) = true := by
  simp [verdicts, appendChecked_true, changedType_refused, changedTerm_refused, forgedRoot_refused]

/-! ## Symbolic append equations

The conversion recipes cover open constructor cases. Capture-safe substitution
then gives both equations for arbitrary scoped arguments. These are conversion
judgments; they do not assert forward evaluation, termination, or a new rule.
-/

namespace Computation

open TypedEquality.Normalization

local instance : DecidableRel rules.headEq :=
  fun h u => inferInstanceAs (Decidable (Tower.rules.headEq h u))

theorem add_substitute {n m : Nat} (substitution : Sub Tower.Head n m)
    (first second : Tower.Tm n) :
    subst substitution (add first second) = add (subst substitution first) (subst substitution second) := rfl

theorem motive_substitute {n m : Nat} (substitution : Sub Tower.Head n m)
    (element length : Tower.Tm n) :
    subst substitution (appendMotive element length) =
      appendMotive (subst substitution element) (subst substitution length) := by
  simp only [appendMotive, subst, subst_vecApp, add_substitute]
  rw [show liftSub (liftSub substitution) = liftSubN substitution 2 from rfl]
  rw [subst_liftSubN_rename_wkN, subst_liftSubN_rename_wkN]
  rfl

theorem cons_substitute {n m : Nat} (substitution : Sub Tower.Head n m)
    (element length : Tower.Tm n) :
    subst substitution (appendCons element length) =
      appendCons (subst substitution element) (subst substitution length) := by
  simp only [appendCons, subst, vconsApp, add_substitute]
  rw [show liftSub (liftSub (liftSub (liftSub substitution))) = liftSubN substitution 4 from rfl]
  rw [subst_liftSubN_rename_wkN, subst_liftSubN_rename_wkN]
  rfl

def nilSource : Tower.Tm 3 := append (.var 2) zeroTm (.var 1) (vnilApp (.var 2)) (.var 0)
def consSource : Tower.Tm 6 := append (.var 5) (succApp (.var 3)) (.var 4)
  (vconsApp (.var 5) (.var 3) (.var 2) (.var 1)) (.var 0)
def consTarget : Tower.Tm 6 := vconsApp (.var 5) (add (.var 3) (.var 4)) (.var 2)
  (append (.var 5) (.var 3) (.var 4) (.var 1) (.var 0))

def nilComparison := StructuralConversionSearch.compare decoder searchRoot
  (headEq := rules.headEq) 48 nilSource (.var 0)
def consComparison := StructuralConversionSearch.compare decoder searchRoot
  (headEq := rules.headEq) 48 consSource consTarget

theorem nil_checked : nilComparison.isSome = true := by decide +kernel
theorem cons_checked : consComparison.isSome = true := by decide +kernel

theorem nil_conversion : Conv rules.headEq nilSource (.var 0) rules.computation := by
  have checked := nil_checked
  cases found : nilComparison with
  | none => simp [found] at checked
  | some recipe =>
      exact StructuralConversionSearch.compare_sound decoder searchRoot 48 _ _ recipe found

theorem cons_conversion : Conv rules.headEq consSource consTarget rules.computation := by
  have checked := cons_checked
  cases found : consComparison with
  | none => simp [found] at checked
  | some recipe =>
      exact StructuralConversionSearch.compare_sound decoder searchRoot 48 _ _ recipe found

theorem append_substitute {n m : Nat} (substitution : Sub Tower.Head n m)
    (element first second left right : Tower.Tm n) :
    subst substitution (append element first second left right) =
      append (subst substitution element) (subst substitution first) (subst substitution second)
        (subst substitution left) (subst substitution right) := by
  simp only [append, vecEliminateApp, subst, motive_substitute, cons_substitute]

theorem append_nil {n : Nat} (element second right : Tower.Tm n) :
    Conv rules.headEq (append element zeroTm second (vnilApp element) right) right
      rules.computation := by
  let assignment : Sub Tower.Head 3 n :=
    fun index => match index.val with | 0 => right | 1 => second | _ => element
  have conversion := Conv.substitute assignment nil_conversion
  simpa [nilSource, append_substitute, subst, vnilApp, zeroTm, assignment]
    using conversion

theorem append_cons {n : Nat} (element first second head tail right : Tower.Tm n) :
    Conv rules.headEq
      (append element (succApp first) second (vconsApp element first head tail) right)
      (vconsApp element (add first second) head (append element first second tail right))
      rules.computation := by
  let assignment : Sub Tower.Head 6 n :=
    fun index => match index.val with
      | 0 => right | 1 => tail | 2 => head | 3 => first | 4 => second | _ => element
  have conversion := Conv.substitute assignment cons_conversion
  simpa [consSource, consTarget, append_substitute, add_substitute, subst,
      succApp, vconsApp, assignment] using conversion

def wrongBranchTarget : Tower.Tm 6 :=
  vconsApp (.var 5) (add (.var 3) (.var 4)) (.var 2) (.var 1)

def wrongBranchComparison := StructuralConversionSearch.compare decoder searchRoot
  (headEq := rules.headEq) 48 consSource wrongBranchTarget

theorem wrongBranch_refused : wrongBranchComparison.isSome = false := by decide +kernel

def verdicts : List (String × Bool) := [
  ("append symbolic nil equation checks", nilComparison.isSome),
  ("append symbolic cons equation checks", consComparison.isSome),
  ("append omitted recursive computation refused", !wrongBranchComparison.isSome)]

theorem all_verdicts : verdicts.all (·.2) = true := by
  simp [verdicts, nil_checked, cons_checked, wrongBranch_refused]

end Computation

end Programs
end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeNaturalVectorFamilies
