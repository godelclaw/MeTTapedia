import Mettapedia.GSLT.Contexts.TermsAlone
import Mettapedia.GSLT.Dedukti.TableEvaluator
import Mettapedia.Logic.HostingStyles.Framework
import Mettapedia.Logic.HostingStyles.ProofTheory
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.BigOperators

/-!
# What the shape of contexts decides before any computation

A map of theories carries every context of its source to a context of its
target with the same holes (`ContextMap.context`).  Two properties of the
contexts of a target therefore exclude maps into it, whatever its reduction
is.

* **A linear size** (`ContextTheory.LinearSize`): a positive number on terms
  that the static equivalence keeps and that every context adds over its
  holes.  The contexts of such a theory use each hole once.  A theory with a
  linear size receives no map from a theory that *discards*
  (`ContextTheory.Discards`: a context of two holes that returns its first)
  or that *copies* (`ContextTheory.Copies`: a context of one hole that acts
  as a context of two holes filled twice) at an inhabited interface
  (`LinearSize.isEmpty_contextMap_of_discards`,
  `LinearSize.isEmpty_contextMap_of_copies`).
* **No context of two holes**: a theory given by its terms alone
  (`GSLT.termsAlone`) has none (`termsAlone_isEmpty_context_two`), so it
  receives no map from a theory that has one
  (`isEmpty_contextMap_into_termsAlone`).

The theories of the λΠ-calculus modulo (`rewritingTheory`), the rule-table
evaluator (`tableEvaluator`), the framework with rules as constants
(`frameworkTheory`) and the theory of a rule signature (`proofTheory`) all
discard, and the first three copy.  So none of them maps into a theory with
a linear size, nor into a theory given by its terms alone: a statement that
such a target hosts them has to take them by their terms.
-/

set_option autoImplicit false
set_option linter.dupNamespace false

namespace Mettapedia.GSLT

universe u

namespace ContextTheory

variable (theory : ContextTheory.{u})

/-- **A linear size**: a positive number on the terms of a theory that the
static equivalence keeps and that every context with finitely many holes adds
over its holes. -/
structure LinearSize where
  /-- The size of a term. -/
  size : {interface : theory.Interface} → theory.Term interface → Nat
  positive : ∀ {interface : theory.Interface} (term : theory.Term interface), 0 < size term
  respects : ∀ {interface : theory.Interface} {first second : theory.Term interface},
    (theory.equations interface).r first second → size first = size second
  additive : ∀ {arity : Type} [Fintype arity] {holes : arity → theory.Interface}
    {result : theory.Interface} (context : theory.Context holes result),
    ∃ weight : Nat, ∀ filling : (index : arity) → theory.Term (holes index),
      size (theory.fill context filling) = weight + ∑ index, size (filling index)

/-- **A theory discards** at an interface: some context of two holes returns
what fills its first hole, whatever fills the second. -/
def Discards (interface : theory.Interface) : Prop :=
  ∃ first : theory.Context (fun _ : Bool => interface) interface,
    ∀ filling : Bool → theory.Term interface,
      (theory.equations interface).r (theory.fill first filling) (filling false)

/-- **A theory copies** at an interface: some context of one hole acts as a
context of two holes filled twice with the same term. -/
def Copies (interface : theory.Interface) : Prop :=
  ∃ (pair : theory.Context (fun _ : Bool => interface) interface)
    (twice : theory.Label interface interface),
    ∀ term : theory.Term interface,
      (theory.equations interface).r (theory.apply twice term) (theory.fill pair fun _ => term)

end ContextTheory

/-- **A map out of a theory that discards finds, in its target, a context of
two holes that returns its first on the images.**  This is what a host with
contexts has to have. -/
theorem ContextMap.discards_on_image {source target : ContextTheory.{u}}
    (map : ContextMap source target) {interface : source.Interface}
    (discards : source.Discards interface) :
    ∃ first : target.Context (fun _ : Bool => map.interface interface) (map.interface interface),
      ∀ filling : Bool → source.Term interface,
        (target.equations (map.interface interface)).r
          (target.fill first fun index => map.term (filling index)) (map.term (filling false)) := by
  obtain ⟨first, returns⟩ := discards
  exact ⟨map.context first, fun filling =>
    (target.equations _).iseqv.trans
      ((target.equations _).iseqv.symm (map.equivariant first filling))
      (map.term_resp (returns filling))⟩

namespace ContextTheory.LinearSize

variable {source target : ContextTheory.{u}}

/-- The size of an image along a map. -/
theorem size_image_fill (sized : target.LinearSize) (map : ContextMap source target)
    {arity : Type} [Fintype arity] {holes : arity → source.Interface} {result : source.Interface}
    (context : source.Context holes result) :
    ∃ weight : Nat, ∀ filling : (index : arity) → source.Term (holes index),
      sized.size (map.term (source.fill context filling)) =
        weight + ∑ index, sized.size (map.term (filling index)) := by
  obtain ⟨weight, adds⟩ := sized.additive (map.context context)
  exact ⟨weight, fun filling =>
    (sized.respects (map.equivariant context filling)).trans (adds fun index => map.term (filling index))⟩

/-- **A theory with a linear size receives no map from a theory that
discards** at an inhabited interface. -/
theorem false_of_discards (sized : target.LinearSize) (map : ContextMap source target)
    {interface : source.Interface} (discards : source.Discards interface)
    (term : source.Term interface) : False := by
  obtain ⟨first, returns⟩ := discards
  obtain ⟨weight, adds⟩ := sized.size_image_fill map first
  have filled := adds fun _ => term
  rw [sized.respects (map.term_resp (returns fun _ => term)), Fintype.sum_bool] at filled
  have positive := sized.positive (map.term term)
  omega

/-- **A theory with a linear size receives no map from a theory that copies**
at an inhabited interface. -/
theorem false_of_copies (sized : target.LinearSize) (map : ContextMap source target)
    {interface : source.Interface} (copies : source.Copies interface)
    (term : source.Term interface) : False := by
  obtain ⟨pair, twice, same⟩ := copies
  obtain ⟨pairWeight, pairAdds⟩ := sized.size_image_fill map pair
  obtain ⟨twiceWeight, twiceAdds⟩ := sized.size_image_fill map twice
  have balance : ∀ other : source.Term interface,
      twiceWeight + sized.size (map.term other) =
        pairWeight + (sized.size (map.term other) + sized.size (map.term other)) := by
    intro other
    have left := twiceAdds fun _ => other
    have right := pairAdds fun _ => other
    rw [Fintype.sum_unique] at left
    rw [Fintype.sum_bool] at right
    have equal := sized.respects (map.term_resp (same other))
    have unfolded : source.apply twice other = source.fill twice fun _ => other := rfl
    rw [unfolded] at equal
    omega
  have once := balance term
  have again := balance (source.fill pair fun _ => term)
  have paired := pairAdds fun _ => term
  rw [Fintype.sum_bool] at paired
  have positive := sized.positive (map.term term)
  omega

theorem isEmpty_contextMap_of_discards (sized : target.LinearSize) {interface : source.Interface}
    (discards : source.Discards interface) (inhabited : Nonempty (source.Term interface)) :
    IsEmpty (ContextMap source target) :=
  ⟨fun map => inhabited.elim fun term => sized.false_of_discards map discards term⟩

theorem isEmpty_contextMap_of_copies (sized : target.LinearSize) {interface : source.Interface}
    (copies : source.Copies interface) (inhabited : Nonempty (source.Term interface)) :
    IsEmpty (ContextMap source target) :=
  ⟨fun map => inhabited.elim fun term => sized.false_of_copies map copies term⟩

/-- A theory with a linear size discards at no inhabited interface. -/
theorem not_discards (sized : target.LinearSize) {interface : target.Interface}
    (term : target.Term interface) : ¬ target.Discards interface :=
  fun discards => sized.false_of_discards (ContextMap.id target) discards term

/-- A theory with a linear size copies at no inhabited interface. -/
theorem not_copies (sized : target.LinearSize) {interface : target.Interface}
    (term : target.Term interface) : ¬ target.Copies interface :=
  fun copies => sized.false_of_copies (ContextMap.id target) copies term

end ContextTheory.LinearSize

/-! ## A theory given by its terms alone -/

namespace GSLT

variable (theory : GSLT.{u})

/-- **A theory given by its terms alone has no context of two holes.** -/
theorem termsAlone_isEmpty_context_two (holes : Bool → theory.termsAlone.Interface)
    (result : theory.termsAlone.Interface) : IsEmpty (theory.termsAlone.Context holes result) := by
  refine ⟨fun context => ?_⟩
  cases context with
  | hole position only => exact absurd ((only true).trans (only false).symm) (by decide)
  | constant term empty => exact empty.false true

/-- A theory given by its terms alone has a linear size, for want of
contexts: every term has size one. -/
def termsAloneLinearSize : theory.termsAlone.LinearSize where
  size := fun _ => 1
  positive := fun _ => Nat.one_pos
  respects := fun _ => rfl
  additive := fun {arity} _ _ _ context => by
    cases context with
    | hole position only =>
        refine ⟨0, fun _ => ?_⟩
        have single : (Finset.univ : Finset arity) = {position} :=
          Finset.eq_singleton_iff_unique_mem.mpr ⟨Finset.mem_univ _, fun other _ => only other⟩
        simp [single]
    | constant term empty =>
        refine ⟨1, fun _ => ?_⟩
        simp

end GSLT

/-- **A theory given by its terms alone receives no map from a theory with a
context of two holes.** -/
theorem isEmpty_contextMap_into_termsAlone {source : ContextTheory.{u}} (target : GSLT.{u})
    {holes : Bool → source.Interface} {result : source.Interface}
    (context : source.Context holes result) : IsEmpty (ContextMap source target.termsAlone) :=
  ⟨fun map => (target.termsAlone_isEmpty_context_two _ _).false (map.context context)⟩

/-! ## The theories that discard and copy -/

open Mettapedia.GSLT.Dedukti in
/-- The calculus as it runs discards: the context that is its first hole. -/
theorem rewritingTheory_discards (theory : Theory) : (rewritingTheory theory).Discards () :=
  ⟨TermContext.hole false, fun _ => rfl⟩

open Mettapedia.GSLT.Dedukti in
/-- The calculus as it runs copies: self-application of the hole. -/
theorem rewritingTheory_copies (theory : Theory) : (rewritingTheory theory).Copies () :=
  ⟨.app (.hole false) (.hole true), .app (.hole ()) (.hole ()), fun _ => rfl⟩

open Mettapedia.GSLT.Dedukti in
/-- The rule-table evaluator discards. -/
theorem tableEvaluator_discards : tableEvaluator.Discards () :=
  ⟨tabledShape.hole false, fun filling => tabledShape.fill_hole filling false⟩

open Mettapedia.GSLT.Dedukti in
/-- The rule-table evaluator copies. -/
theorem tableEvaluator_copies : tableEvaluator.Copies () :=
  ⟨⟨∅, .app (.hole false) (.hole true)⟩, ⟨∅, .app (.hole ()) (.hole ())⟩, fun _ => rfl⟩

open Mettapedia.Logic.HostingStyles.Framework in
/-- The framework discards at every type. -/
theorem frameworkTheory_discards {B : Type} (signature : Signature B) (type : Ty B) :
    (frameworkTheory signature).Discards type :=
  ⟨Tm.hole (holes := fun _ : Bool => type) false, fun filling =>
    Conv.of_eq ((filling false).rename_closed _)⟩

open Mettapedia.Logic.HostingStyles.Framework in
/-- The framework copies at every type of functions from a type to itself:
the composite of the hole with itself. -/
theorem frameworkTheory_copies {B : Type} (signature : Signature B) (type : Ty B) :
    (frameworkTheory signature).Copies (.arrow type type) :=
  ⟨Tm.lam (Tm.app (Tm.hole (holes := fun _ : Bool => Ty.arrow type type) false)
      (Tm.app (Tm.hole true) (Tm.var .zero))),
    Tm.lam (Tm.app (Tm.hole (holes := fun _ : Unit => Ty.arrow type type) ())
      (Tm.app (Tm.hole ()) (Tm.var .zero))),
    fun _ => Relation.EqvGen.refl _⟩

open Mettapedia.Logic.HostingStyles in
/-- The theory of a rule signature discards at every judgment: the derived
rule that is its first assumption. -/
theorem proofTheory_discards {J : Type} (P : RuleSignature J) (congruence : P.ProofCongruence)
    (j : J) : (P.proofTheory congruence).Discards j :=
  ⟨P.assume (holes := fun _ : Bool => j) false, fun _ => (congruence.setoid j).iseqv.refl _⟩

/-! ## Examples -/

open Mettapedia.GSLT.Dedukti in
/-- **Negative**: the rule-table evaluator has no linear size. -/
theorem tableEvaluator_not_linearSize : IsEmpty tableEvaluator.LinearSize :=
  ⟨fun sized => sized.not_discards (interface := ())
    (⟨∅, .srt .type⟩ : Tabled) tableEvaluator_discards⟩

/-- **Negative**: a theory given by its terms alone discards nowhere. -/
theorem termsAlone_not_discards (theory : GSLT.{u}) (interface : theory.termsAlone.Interface) :
    ¬ theory.termsAlone.Discards interface :=
  fun ⟨first, _⟩ => (theory.termsAlone_isEmpty_context_two _ _).false first

#print axioms ContextMap.discards_on_image
#print axioms ContextTheory.LinearSize.false_of_discards
#print axioms ContextTheory.LinearSize.false_of_copies
#print axioms GSLT.termsAlone_isEmpty_context_two
#print axioms GSLT.termsAloneLinearSize
#print axioms isEmpty_contextMap_into_termsAlone
#print axioms rewritingTheory_copies
#print axioms tableEvaluator_discards
#print axioms tableEvaluator_copies
#print axioms frameworkTheory_discards
#print axioms frameworkTheory_copies
#print axioms proofTheory_discards
#print axioms tableEvaluator_not_linearSize

end Mettapedia.GSLT
