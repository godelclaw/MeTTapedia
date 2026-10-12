import Mettapedia.OSLF.Syntax.SyntacticTermPresheaf
import Mathlib.CategoryTheory.EpiMono

/-!
# Syntactic contexts with retractable future substitutions

The arrows retain their actual syntactic substitutions and a proved section.
Opposite arrows are the permitted future changes. Fresh-variable extension
is admitted by an explicit assignment to the fresh variable; substitution
under every binder still uses the original term action.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.SyntacticRetractionContexts

open _root_.CategoryTheory

variable (S : Signature)

structure Object where
  context : Syntactic.Ctxt S

instance : Category (Object S) where
  Hom source target := {change : source.context ⟶ target.context // IsSplitEpi change}
  id world := ⟨𝟙 world.context, inferInstance⟩
  comp earlier later := by
    letI := earlier.property
    letI := later.property
    exact ⟨earlier.val ≫ later.val, inferInstance⟩
  id_comp change := by apply Subtype.ext; exact Category.id_comp change.val
  comp_id change := by apply Subtype.ext; exact Category.comp_id change.val
  assoc earlier middle later := by
    apply Subtype.ext
    exact Category.assoc earlier.val middle.val later.val

def forget : Object S ⥤ Syntactic.Ctxt S where
  obj world := world.context
  map change := change.val

variable {S}

def world (context : Ctx S) : Object S := ⟨⟨context⟩⟩

/-- The supplied assignment provides a section of fresh-variable extension. -/
def fresh (context : Ctx S) (sort : S.Srt) (supplied : Term S context sort) :
    world (sort :: context) ⟶ world context :=
  ⟨(fun _ position => .var (.succ position)),
    IsSplitEpi.mk' {
      section_ := extend supplied
      id := rfl }⟩

theorem fresh_action (context : Ctx S) (sort : S.Srt) (supplied : Term S context sort)
    {result : S.Srt} (term : Term S context result) :
    (Syntactic.termPresheaf S result).map (fresh context sort supplied).val.op term =
      weaken term :=
  bind_var_eq_rename (fun _ position => .succ position) term

/-- A chosen section acts backwards on complete terms, recovering the source. -/
noncomputable def backward {source target : Object S} (change : source ⟶ target) :
    target.context ⟶ source.context := by
  letI := change.property
  exact section_ change.val

theorem backward_section {source target : Object S} (change : source ⟶ target) :
    backward change ≫ change.val = 𝟙 target.context := by
  have := change.property
  exact IsSplitEpi.id change.val

end Mettapedia.OSLF.Binding.SyntacticRetractionContexts
