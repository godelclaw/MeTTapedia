import Mettapedia.OSLF.NativeTypes.Decision.Machine.Interface

open Mettapedia.OSLF.Framework

/-! Native predicate meanings shared by retained formula machines. -/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Decision.Machine

open Mettapedia.GSLT GSLTTypeSynthesis
open Mettapedia.OSLF.NativeTypes.Decision.Reference.Core

universe u w

def denotation {system : GSLT.{u}} {admitted : system.Term → Prop} {Leaf : Type w}
    (leaves : Leaf → LeafBackend system admitted) : Formula Leaf → EquationPredicate system
  | .atom leaf => (leaves leaf).predicate
  | .top => ⟨fun _ => True, by intro _ _ _; rfl⟩
  | .bottom => ⟨fun _ => False, by intro _ _ _; rfl⟩
  | .conj left right => meet system (denotation leaves left) (denotation leaves right)
  | .disj left right => join system (denotation leaves left) (denotation leaves right)
  | .neg formula => complement system (denotation leaves formula)
  | .imp left right => implies system (denotation leaves left) (denotation leaves right)
  | .possibility formula => semanticDiamond system (denotation leaves formula)
  | .outgoingUniversal formula => Mettapedia.OSLF.NativeTypes.Semantics.Operational.outgoingUniversal system (denotation leaves formula)

theorem denotation_comparison {system : GSLT.{u}} {admitted : system.Term → Prop} {Leaf : Type w}
    (leaves : Leaf → LeafBackend system admitted) (tests : Leaf → Test system admitted)
    (leaf_meaning : ∀ leaf, (leaves leaf).predicate = (tests leaf).predicate)
    (formula : Formula Leaf) : denotation leaves formula = Mettapedia.OSLF.NativeTypes.Decision.Reference.Core.denotation tests formula := by
  induction formula with
  | atom leaf => exact leaf_meaning leaf
  | top | bottom => rfl
  | conj left right ihl ihr | disj left right ihl ihr | imp left right ihl ihr =>
    simp only [denotation, Mettapedia.OSLF.NativeTypes.Decision.Reference.Core.denotation, ihl, ihr]
  | neg formula ih | possibility formula ih | outgoingUniversal formula ih =>
    simp only [denotation, Mettapedia.OSLF.NativeTypes.Decision.Reference.Core.denotation, ih]

end Mettapedia.OSLF.NativeTypes.Decision.Machine
