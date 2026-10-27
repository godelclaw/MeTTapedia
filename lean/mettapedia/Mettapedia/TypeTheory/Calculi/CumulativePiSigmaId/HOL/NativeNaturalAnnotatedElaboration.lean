import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.NativeNaturalAnnotatedReading
import Mettapedia.Logic.HOL.CheckableFragment

/-!
# A certifying reader for the annotated natural predicate fragment

The reader traverses the actual annotated source syntax. Every successful
result includes a derivation in the independently specified annotated reading.
Binder domains are themselves read as predicate codes; applications check
their simple carrier types. Unsupported formers and mismatched applications
return no reading. This is a fragment reader, not a dependent typechecker or
a conversion search procedure.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeNaturalPredicateReading

open Mettapedia.Logic
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality.Annotated NativeNaturalVectorFamilies
open FormationSensitiveHOLInterface (variableIndex)

universe u v
variable {Base : Type u} {Const : HOL.Ty Base → Type v}

namespace AnnotatedReading

abbrev Result (operations : Operations Base Const) (Γ : HOL.Ctx Base)
    (source : CTm Tower.Head Γ.length) :=
  {value : (Σ type : HOL.Ty Base, HOL.Term Const Γ type) //
    AnnotatedReads operations source value.2}

variable [DecidableEq Base]

/-- The Nat instance delegates traversal and carrier checks to the shared reader.
Its evidence is returned in the original independent reading relation. -/
def read? (operations : Operations Base Const) (Γ : HOL.Ctx Base)
    (source : CTm Tower.Head Γ.length) : Option (Result operations Γ source) :=
  (AnnotatedPredicateReading.Reader.read? (lexicalReading operations) Γ source).map
    (fun result => ⟨result.val, AnnotatedReads.ofGeneric result.property⟩)

/-- The shared implementation recovers every original reading exactly. -/
theorem read?_complete {operations : Operations Base Const} {Γ : HOL.Ctx Base}
    {type : HOL.Ty Base} {source : CTm Tower.Head Γ.length} {code : HOL.Term Const Γ type}
    (reading : AnnotatedReads operations source code) :
    read? operations Γ source = some ⟨⟨type, code⟩, reading⟩ := by
  simp only [read?, AnnotatedPredicateReading.Reader.read?_complete reading.toGeneric, Option.map_some]

/-- The executable result omits the proof field, retaining its inferred
carrier and exact HOL term. -/
def infer? (operations : Operations Base Const) (Γ : HOL.Ctx Base)
    (source : CTm Tower.Head Γ.length) : Option (Σ type : HOL.Ty Base, HOL.Term Const Γ type) :=
  (read? operations Γ source).map Subtype.val

theorem infer?_shared (operations : Operations Base Const) (Γ : HOL.Ctx Base)
    (source : CTm Tower.Head Γ.length) :
    infer? operations Γ source = AnnotatedPredicateReading.Reader.infer? (lexicalReading operations) Γ source := by
  simp only [infer?, read?, AnnotatedPredicateReading.Reader.infer?, Option.map_map]
  rfl

theorem infer?_sound (operations : Operations Base Const) (Γ : HOL.Ctx Base)
    (source : CTm Tower.Head Γ.length) (type : HOL.Ty Base) (code : HOL.Term Const Γ type)
    (accepted : infer? operations Γ source = some ⟨type, code⟩) :
    AnnotatedReads operations source code := by
  obtain ⟨reading, _, same⟩ := Option.map_eq_some_iff.mp accepted
  exact Eq.mp (congrArg (fun value : (Σ type : HOL.Ty Base, HOL.Term Const Γ type) =>
    AnnotatedReads operations source value.2) same) reading.2

theorem infer?_complete {operations : Operations Base Const} {Γ : HOL.Ctx Base}
    {type : HOL.Ty Base} {source : CTm Tower.Head Γ.length} {code : HOL.Term Const Γ type}
    (reading : AnnotatedReads operations source code) :
    infer? operations Γ source = some ⟨type, code⟩ := by
  simp only [infer?, read?_complete reading, Option.map_some]

theorem infer?_iff (operations : Operations Base Const) (Γ : HOL.Ctx Base)
    (source : CTm Tower.Head Γ.length) (type : HOL.Ty Base) (code : HOL.Term Const Γ type) :
    infer? operations Γ source = some ⟨type, code⟩ ↔ AnnotatedReads operations source code :=
  ⟨infer?_sound operations Γ source type code, infer?_complete⟩

/-- The annotations determine both the simple carrier and the exact target
syntax. No equality of readings is added as an assumption. -/
theorem coherent {operations : Operations Base Const} {Γ : HOL.Ctx Base}
    {firstType secondType : HOL.Ty Base} {source : CTm Tower.Head Γ.length}
    {first : HOL.Term Const Γ firstType} {second : HOL.Term Const Γ secondType}
    (firstRead : AnnotatedReads operations source first)
    (secondRead : AnnotatedReads operations source second) :
    (⟨firstType, first⟩ : Σ type : HOL.Ty Base, HOL.Term Const Γ type) = ⟨secondType, second⟩ :=
  AnnotatedPredicateReading.Reader.coherent firstRead.toGeneric secondRead.toGeneric

theorem term_unique {operations : Operations Base Const} {Γ : HOL.Ctx Base}
    {type : HOL.Ty Base} {source : CTm Tower.Head Γ.length}
    {first second : HOL.Term Const Γ type}
    (firstRead : AnnotatedReads operations source first)
    (secondRead : AnnotatedReads operations source second) : first = second := by
  exact eq_of_heq (Sigma.mk.inj_iff.mp (coherent firstRead secondRead)).2

theorem infer?_substitute {operations : Operations Base Const} {Γ Ξ : HOL.Ctx Base}
    {type : HOL.Ty Base} {source : CTm Tower.Head Γ.length} {code : HOL.Term Const Γ type}
    (accepted : infer? operations Γ source = some ⟨type, code⟩)
    (θ : HOL.Subst Const Γ Ξ) (raw : CSub Tower.Head Γ.length Ξ.length)
    (components : ∀ {type} (index : HOL.Var Γ type),
      infer? operations Ξ (raw (variableIndex index)) = some ⟨type, θ index⟩) :
    infer? operations Ξ (source.subst raw) = some ⟨type, HOL.subst θ code⟩ :=
  infer?_complete ((infer?_sound _ _ _ _ _ accepted).substitute θ raw
    (fun index => infer?_sound _ _ _ _ _ (components index)))

theorem infer?_rename {operations : Operations Base Const} {Γ Ξ : HOL.Ctx Base}
    {type : HOL.Ty Base} {source : CTm Tower.Head Γ.length} {code : HOL.Term Const Γ type}
    (accepted : infer? operations Γ source = some ⟨type, code⟩)
    (ρ : HOL.Rename Base Γ Ξ) (raw : Ren Γ.length Ξ.length)
    (compatible : ∀ {type} (index : HOL.Var Γ type),
      variableIndex (ρ index) = raw (variableIndex index)) :
    infer? operations Ξ (source.rename raw) = some ⟨type, HOL.rename ρ code⟩ :=
  infer?_complete ((infer?_sound _ _ _ _ _ accepted).rename ρ raw compatible)

#print axioms read?
#print axioms infer?_sound
#print axioms read?_complete
#print axioms coherent
#print axioms term_unique
#print axioms infer?_substitute

end AnnotatedReading
end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeNaturalPredicateReading
