import Mettapedia.GSLT.LanguageDef.IndexedInductiveCaseElaboration
import Mettapedia.GSLT.LanguageDef.IndexedInductiveGuestTypedControls
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeNaturalVectorProgramChecking
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeNaturalVectorComputationProfiles

/-!
# Scoped append clauses compiled against the admitted vector inventory

The input clauses contain the written recursive call. The compiler consumes
the existing authored vector inventory, abstracts the call on its recursive
tail, and builds the methods of the existing eliminator. Its output is
compared with the independently authored, checked dependent append function.

The source index syntax reuses the qualified vector comparison fixture.
Only zero, successor and the bound length occur in these constructor codes;
addition in the program is the reference eliminator-defined operation.
This is the scoped clause stage, not a textual frontend theorem.
The authored source interface carries a noncomputable natural interpretation;
this concrete comparison is kernel-evaluated theory. Executable source
reification must be connected separately rather than inferred from it.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.IndexedInductive.AppendElaboration

open Mettapedia.TypeTheory.IndexedPolynomial.Description
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeNaturalVectorFamilies
open Programs CaseElaboration

abbrev indices (A : Type) := Guest.TypedControls.indexSyntax A
abbrev admitted (A : Type) := IndexedInductiveNatVec.Vectors.admitted A

def self : DeclName := `Authored.append

/-- Original source argument order: A, first length, second length, left,
right. The last two template binders are the recursive index and child. -/
def callTemplate : Tower.Tm (5 + 2) := Declaration.IndexedFamily.applyArgs (.const self)
  [.var 6, .var 1, .var 4, .var 0, .var 2]

def nilClause : Clause Tower.Head 5 := ⟨"Nil", 0, .var 0⟩

def consClause : Clause Tower.Head 5 := ⟨"Cons", 3,
  vconsApp (.var 7) (add (.var 2) (.var 5)) (.var 1)
    (Declaration.IndexedFamily.applyArgs (.const self)
      [.var 7, .var 2, .var 5, .var 0, .var 3])⟩

def clauses : List (Clause Tower.Head 5) := [nilClause, consClause]

noncomputable def compiledMethods (A : Type) :=
  compileMethods (indices A) (admitted A) self callTemplate clauses

/-- Compute methods from source clauses; the reference methods were written
independently using the declared vector eliminator. -/
theorem methods_match_reference (A : Type) :
    compiledMethods A = some [(.var 0), appendCons (.var 4) (.var 2)] := by
  change compiledMethods Unit = _
  decide +kernel

noncomputable def compileClosed (A : Type) : Option (Tower.Tm 0) := do
  let methods ← compiledMethods A
  return TelescopeAbstraction.closeTerm appendContext
    (Guest.Types.recursorAt (.app (.const vecEliminateName) (.var 4))
      (appendMotive (.var 4) (.var 2)) methods (.var 3) (.var 1))

theorem compiled_matches_reference (A : Type) : compileClosed A = some appendTerm := by
  rw [compileClosed, methods_match_reference]
  rfl

/-- Typing is inherited through the proved source-compilation comparison,
from the independent replay of the complete dependent function. -/
theorem compiled_typed (A : Type) (term : Tower.Tm 0) (compiled : compileClosed A = some term) :
    FormationSensitive.Judgment Programs.rules .nil term appendType := by
  rw [compiled_matches_reference] at compiled
  cases Option.some.inj compiled
  exact append_typed

/-- Source compilation also reaches the genuinely restricted checking policy;
its full dependent typing proof replays only the natural iota permissions. -/
theorem compiled_typed_naturalOnly (A : Type) (term : Tower.Tm 0)
    (compiled : compileClosed A = some term) :
    FormationSensitive.Judgment (ComputationProfiles.rules ComputationProfiles.naturalOnly)
      .nil term appendType := by
  rw [compiled_matches_reference] at compiled
  cases Option.some.inj compiled
  exact ComputationProfiles.append_typed_naturalOnly

def changedName : Clause Tower.Head 5 := { consClause with constructor := "Other" }
def wrongArity : Clause Tower.Head 5 := ⟨"Cons", 2, .var 0⟩
def wrongChild : Clause Tower.Head 5 := ⟨"Cons", 3,
  vconsApp (.var 7) (add (.var 2) (.var 5)) (.var 1)
    (Declaration.IndexedFamily.applyArgs (.const self)
      [.var 7, .var 2, .var 5, .var 1, .var 3])⟩
def wrongIndex : Clause Tower.Head 5 := ⟨"Cons", 3,
  vconsApp (.var 7) (add (.var 2) (.var 5)) (.var 1)
    (Declaration.IndexedFamily.applyArgs (.const self)
      [.var 7, .var 5, .var 5, .var 0, .var 3])⟩
def unabstracted : Clause Tower.Head 5 := ⟨"Cons", 3, .const self⟩

noncomputable def accepted (A : Type) (submitted : List (Clause Tower.Head 5)) : Bool :=
  (compileMethods (indices A) (admitted A) self callTemplate submitted).isSome

noncomputable def verdicts (A : Type) : List (String × Bool) := [
  ("append source clauses compile", accepted A clauses),
  ("append compiled core matches independent reference", compileClosed A == some appendTerm),
  ("append missing constructor refused", !(accepted A [nilClause])),
  ("append extra constructor refused", !(accepted A (clauses ++ [nilClause]))),
  ("append reordered constructor inventory refused", !(accepted A [consClause, nilClause])),
  ("append renamed constructor refused", !(accepted A [nilClause, changedName])),
  ("append wrong constructor arity refused", !(accepted A [nilClause, wrongArity])),
  ("append call on a nonrecursive field refused", !(accepted A [nilClause, wrongChild])),
  ("append changed recursive index refused", !(accepted A [nilClause, wrongIndex])),
  ("append remaining recursive constant refused", !(accepted A [nilClause, unabstracted]))]

theorem all_verdicts (A : Type) : (verdicts A).all (·.2) = true := by
  change (verdicts Unit).all (·.2) = true
  decide +kernel

end Mettapedia.GSLT.LanguageDef.IndexedInductive.AppendElaboration
