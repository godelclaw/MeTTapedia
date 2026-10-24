import Mettapedia.Computability.ComputationalTrinity
import Mathlib.CategoryTheory.Subfunctor.Image

/-!
# Base change of derivability along lossless translations

A judgment system's statements form a face on its contexts, and its derivable
statements a subset of each fibre.  A translation into another system is
natural along a functor of context categories when it commutes with the action
of context maps.  If the target's derivable statements are stable along its
context maps, a lossless translation pulls that stability back.

* `stable_of_lossless`: for faces, a lossless translation natural along a
  functor of context categories, into a target whose derivable statements form
  a subfunctor, makes the source's derivable statements stable along every
  source context map; `derivableSubfunctor` exhibits them as the preimage
  subfunctor.
* `stable_of_lossless_of_natural`: the same law for one change of context,
  without categories.
* `not_lossless_of_unstable`: so a source whose derivability is not stable
  along some context map admits no lossless translation natural along it into
  such a target.

The constraint is on the source maps along which the translation is natural.
A target whose contexts allow every renaming, as the cartesian contexts of LF
and of higher-order abstract syntax do, forces stability under identification
of variables; MM0 derivability does not have it
(`Languages.MM0.Translation.VariableIdentificationObstruction`).  A target whose
context maps between translated contexts come only from admissible source maps,
as with an apartness judgment for bound variables, imposes nothing new.
-/

set_option autoImplicit false

namespace Mettapedia.Computability.ComputationalTrinity

open CategoryTheory

universe u u' v v' w uJ uK

/-- **Base change for one context change.** A lossless translation that commutes
with a change of context, into a target whose derivability is stable under the
image change, makes the source's derivability stable under it. -/
theorem stable_of_lossless_of_natural {Judgment : Type uJ} {Judgment' : Type uK}
    (encode : Judgment → Judgment') {derivable : Judgment → Prop}
    {derivable' : Judgment' → Prop}
    (lossless : ∀ judgment, derivable judgment ↔ derivable' (encode judgment))
    {change : Judgment → Judgment} {change' : Judgment' → Judgment'}
    (natural : ∀ judgment, encode (change judgment) = change' (encode judgment))
    (stable : ∀ judgment', derivable' judgment' → derivable' (change' judgment')) :
    ∀ judgment, derivable judgment → derivable (change judgment) := by
  intro judgment derived
  rw [lossless, natural]
  exact stable _ ((lossless judgment).mp derived)

/-- **No lossless translation along an unstable change.** -/
theorem not_lossless_of_unstable {Judgment : Type uJ} {Judgment' : Type uK}
    {derivable : Judgment → Prop} {derivable' : Judgment' → Prop}
    {change : Judgment → Judgment} {change' : Judgment' → Judgment'}
    {judgment : Judgment} (derived : derivable judgment)
    (unstable : ¬ derivable (change judgment))
    (stable : ∀ judgment', derivable' judgment' → derivable' (change' judgment'))
    (encode : Judgment → Judgment')
    (natural : ∀ judgment, encode (change judgment) = change' (encode judgment)) :
    ¬ ∀ judgment, derivable judgment ↔ derivable' (encode judgment) :=
  fun lossless =>
    unstable (stable_of_lossless_of_natural encode lossless natural stable judgment derived)

section Faces

variable {Context : Type u} [Category.{v} Context] {Context' : Type u'} [Category.{v'} Context']

/-- The derivable statements of a lossless translation, as the preimage of the
target's derivable statements. -/
def derivableSubfunctor (functor : Context ⥤ Context') {statements : Face.{u, v, w} Context}
    {statements' : Face.{u', v', w} Context'} (translation : statements ⟶ functor.op ⋙ statements')
    (derivable' : Subfunctor statements') : Subfunctor statements :=
  Subfunctor.preimage
    { obj := fun context => derivable'.obj (functor.op.obj context)
      map := fun map => derivable'.map (functor.op.map map) }
    translation

/-- **Base change of derivability.** If the target's derivable statements form
a subfunctor and the translation is lossless and natural along the functor, the
source's derivable statements are stable along every source context map. -/
theorem stable_of_lossless (functor : Context ⥤ Context') {statements : Face.{u, v, w} Context}
    {statements' : Face.{u', v', w} Context'} (translation : statements ⟶ functor.op ⋙ statements')
    (derivable' : Subfunctor statements') (derivable : ∀ context, Set (statements.obj context))
    (lossless : ∀ context (statement : statements.obj context),
      statement ∈ derivable context ↔
        translation.app context statement ∈ derivable'.obj (functor.op.obj context)) :
    ∀ {source target : Contextᵒᵖ} (map : source ⟶ target),
      derivable source ⊆ statements.map map ⁻¹' derivable target := by
  intro source target map statement derived
  have pulled := (derivableSubfunctor functor translation derivable').map map
    ((lossless source statement).mp derived)
  exact (lossless target _).mpr pulled

end Faces

#print axioms stable_of_lossless_of_natural
#print axioms not_lossless_of_unstable
#print axioms stable_of_lossless

end Mettapedia.Computability.ComputationalTrinity
