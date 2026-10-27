import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.NativeNaturalAnnotatedElaboration

/-!
# Checked simultaneous assignments for the annotated HOL reading

The reader checks every source argument at the simple carrier specified by
the original parameter context. It constructs one capture-safe HOL
substitution and its pointwise annotated reading. No source argument or
carrier is guessed from a shared erased endpoint.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeNaturalPredicateReading
namespace AnnotatedReading

open Mettapedia.Logic
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality.Annotated
open FormationSensitiveHOLInterface (variableIndex)

universe u v
variable {Base : Type u} {Const : HOL.Ty Base → Type v}

abbrev Assignment (operations : Operations Base Const) (source target : HOL.Ctx Base)
    (raw : CSub Tower.Head source.length target.length) :=
  {assignment : HOL.Subst Const source target //
    ∀ {type} (index : HOL.Var source type),
      AnnotatedReads operations (Γ := target) (raw (variableIndex index)) (assignment index)}

variable [DecidableEq Base]

def readAssignment? (operations : Operations Base Const) (source target : HOL.Ctx Base)
    (raw : CSub Tower.Head source.length target.length) : Option (Assignment operations source target raw) :=
  (AnnotatedPredicateReading.Reader.readAssignment? (lexicalReading operations) source target raw).map
    (fun assignment => ⟨assignment.val, by
      intro type index
      apply AnnotatedReads.ofGeneric
      simpa only [variableIndex_eq_toFin] using assignment.property index⟩)

/-- Every represented assignment is recovered by the common reader, with its
original component order and target terms unchanged. -/
theorem readAssignment?_complete (operations : Operations Base Const) (source target : HOL.Ctx Base)
    (raw : CSub Tower.Head source.length target.length) (assignment : HOL.Subst Const source target)
    (represented : ∀ {type} (index : HOL.Var source type),
      AnnotatedReads operations (Γ := target) (raw (variableIndex index)) (assignment index)) :
    readAssignment? operations source target raw = some ⟨assignment, represented⟩ := by
  have shared : ∀ {type} (index : HOL.Var source type),
      AnnotatedPredicateReading.Reads (lexicalReading operations) (Γ := target) (raw index.toFin) (assignment index) := by
    intro type index
    simpa only [variableIndex_eq_toFin] using (represented index).toGeneric
  simp only [readAssignment?, AnnotatedPredicateReading.Reader.readAssignment?_complete _ _ _ _ _ shared,
    Option.map_some]

#print axioms readAssignment?
#print axioms readAssignment?_complete

end AnnotatedReading
end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeNaturalPredicateReading
