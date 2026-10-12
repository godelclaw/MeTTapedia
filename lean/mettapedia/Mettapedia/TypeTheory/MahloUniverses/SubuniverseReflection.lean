import Mettapedia.TypeTheory.UniverseClosureProfiles

/-!
# Whole-subuniverse closure against growth

`UniverseClosureProfiles.WholeSubuniverseClosure` asks, for every family operator, for an ordinary
subuniverse `S` such that the operator applied to `S` itself, as one internal family, embeds back
into `S`. On any universe with a strict growth of codes (for example powersets) no family is
closed in that sense, whatever predicate selects the ordinary subuniverses
(`not_wholeSubuniverseClosure_of_strictGrowth`). The notion measures the absence of growth, not
the strength of a universe: it holds in the universe with a single code
(`pointUniverse_wholeSubuniverseClosure`).

Mahlo reflection (`UniverseClosureProfiles.MahloReflection`) applies the operator to each family
drawn from the subuniverse instead, and asks that the result be equivalent to another family drawn
from it. Its definition and finite controls are part of `UniverseClosureProfiles`; its model on the
universe of `V_κ` is `MahloReflectionModel`.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MahloUniverses

open Mettapedia.TypeTheory.UniverseClosureProfiles

universe uOuter u

variable {outer : SemanticTarskiUniverse.{uOuter, u}}

/-- **Obstruction for whole-subuniverse closure.** If every code has a code whose decoded type
does not embed into its own, then no internal family is closed, as one family, under the operator
that replaces the index code by that larger code. Hence whole-subuniverse closure fails for every
predicate selecting ordinary subuniverses. -/
theorem not_wholeSubuniverseClosure_of_strictGrowth (grow : outer.Code → outer.Code)
    (strict : ∀ a, IsEmpty (outer.El (grow a) ↪ outer.El a))
    (IsOrdinary : outer.InternalFamily → Prop) : ¬ WholeSubuniverseClosure outer IsOrdinary := by
  intro whole
  obtain ⟨S, _, ⟨embedding⟩⟩ := whole.closed (fun F => ⟨grow F.1, fun _ => F.1⟩)
  exact (strict S.1).false embedding.onBase

/-- A universe with a single code decoding to a single point. -/
def pointUniverse : SemanticTarskiUniverse.{0, 0} where
  Code := PUnit
  El _ := PUnit

/-- **Closure without growth.** Whole-subuniverse closure, with the predicate admitting every
family, holds in the universe with one code: there every operator returns the only family. -/
theorem pointUniverse_wholeSubuniverseClosure :
    WholeSubuniverseClosure pointUniverse (fun _ => True) := by
  refine ⟨fun operator => ⟨⟨PUnit.unit, fun _ => PUnit.unit⟩, trivial, ⟨?_⟩⟩⟩
  exact
    { onBase := ⟨fun _ => PUnit.unit, fun (a b : PUnit) _ => Subsingleton.elim a b⟩
      onFibre := fun _ => Equiv.refl PUnit }

#print axioms not_wholeSubuniverseClosure_of_strictGrowth
#print axioms pointUniverse_wholeSubuniverseClosure

end Mettapedia.TypeTheory.MahloUniverses
