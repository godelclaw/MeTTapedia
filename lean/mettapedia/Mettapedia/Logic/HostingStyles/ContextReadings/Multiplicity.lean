import Mettapedia.Logic.HostingStyles.ContextReadings.Readings
import Mettapedia.Logic.HostingStyles.ReductionRank

/-!
# What a reading conserves, and what it cannot receive

A linear size (`ContextTheory.LinearSize`) is a positive number on terms that
every context adds over its holes, each once.  The contexts of a reading use
a hole of a declared interface any number of times, so the size of a reading
counts each hole as often as the context uses it:

* `ContextTheory.MultiplicitySize`: a positive number on terms that the static
  equivalence keeps, and for every context a weight and a number of uses of
  each hole, such that the size of the filled context is the weight plus the
  sizes of the fillings, each as often as its hole is used; and a hole that is
  not used does not matter.
* A theory with a linear size has one, with every hole used once
  (`LinearSize.multiplicitySize`).  So has each of its readings, when the
  contexts of the theory have finitely many holes (`FiniteHoles`,
  `LinearSize.regionReading`); there a hole of an interface that is not
  declared is used once (`LinearSize.counted_regionReading`).

## The obstruction that remains when contexts may discard and copy

A context with a multiplicity size places its fillings in a fixed frame.  It
cannot *apply* one filling to another.  A theory applies
(`ContextTheory.Applies`) when a context of two holes returns its second hole
for one filling of the first and a fixed other term for another.  **No map
from a theory that applies into a theory with a multiplicity size reflects
the static equivalence** (`MultiplicitySize.not_reflectsEquations_of_applies`):
the image of the applying context either does not use its second hole, and
then it cannot return it; or it uses it, and then by the size it cannot use
the first, and so cannot tell the two fillings of the first apart.

## What a reading with regions receives

A map from a theory that discards at an inhabited interface, into a reading of
a theory with a linear size, sends that interface to a declared one
(`LinearSize.declared_of_discards`, and `declared_of_copies`).  When no term
of a declared interface has a step, such a map preserves no step taken at that
interface (`LinearSize.not_preserves_of_discards_of_static`): what a region of
data receives from a source that discards, it receives as data.

A rank of a theory is a rank of each of its readings (`Rank.regionReading`):
the readings have the terms and the steps of the theory.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT

universe u

namespace ContextTheory

variable (theory : ContextTheory.{u})

/-! ## Finitely many holes -/

/-- **Every context of the theory has finitely many holes.** -/
def FiniteHoles : Prop :=
  ∀ {arity : Type} {holes : arity → theory.Interface} {result : theory.Interface},
    theory.Context holes result → Finite arity

/-- **Positive**: a theory given by its terms alone; its contexts have one
hole or none. -/
theorem termsAlone_finiteHoles (theory : GSLT.{u}) : theory.termsAlone.FiniteHoles := by
  intro arity holes result context
  cases context with
  | hole position only =>
      have : Subsingleton arity := ⟨fun first second => (only first).trans (only second).symm⟩
      exact Finite.of_subsingleton
  | constant term empty =>
      have := empty
      exact Finite.of_subsingleton

open Mettapedia.GSLT.Dedukti in
/-- **Negative**: the λΠ-calculus as it runs.  A context may leave any family
of declared holes unused. -/
theorem rewritingTheory_not_finiteHoles (theory : Theory) : ¬ (rewritingTheory theory).FiniteHoles :=
  fun finite => @not_finite Nat _ (finite (arity := Nat) (holes := fun _ => ()) (result := ())
    (TermContext.srt .type))

/-! ## A size that counts each hole as often as it is used -/

/-- **A multiplicity size**: a positive number on the terms of a theory that
the static equivalence keeps, and that every context with finitely many holes
adds over its holes, each as often as the context uses it.  A hole that is
not used does not matter. -/
structure MultiplicitySize where
  /-- The size of a term. -/
  size : {interface : theory.Interface} → theory.Term interface → Nat
  positive : ∀ {interface : theory.Interface} (term : theory.Term interface), 0 < size term
  respects : ∀ {interface : theory.Interface} {first second : theory.Term interface},
    (theory.equations interface).r first second → size first = size second
  counted : ∀ {arity : Type} [Fintype arity] {holes : arity → theory.Interface}
    {result : theory.Interface} (context : theory.Context holes result),
    ∃ (weight : Nat) (uses : arity → Nat),
      (∀ filling : (index : arity) → theory.Term (holes index),
        size (theory.fill context filling) = weight + ∑ index, uses index * size (filling index)) ∧
      ∀ index, uses index = 0 → ∀ first second : (index : arity) → theory.Term (holes index),
        (∀ other, other ≠ index → first other = second other) →
          (theory.equations result).r (theory.fill context first) (theory.fill context second)

variable {theory}

/-- **A linear size is a multiplicity size**: every hole is used once. -/
def LinearSize.multiplicitySize (sized : theory.LinearSize) : theory.MultiplicitySize where
  size := sized.size
  positive := sized.positive
  respects := sized.respects
  counted := fun context => by
    obtain ⟨weight, adds⟩ := sized.additive context
    exact ⟨weight, fun _ => 1, fun filling => by simpa using adds filling,
      fun _ impossible => (Nat.one_ne_zero impossible).elim⟩

/-- **The size of a context of a reading**, for a theory with a linear size
whose contexts have finitely many holes: a hole counts as often as holes are
placed at it.  A hole at which no hole is placed does not matter, and a hole
of an interface that is not declared counts once. -/
theorem LinearSize.counted_regionReading (sized : theory.LinearSize) (finite : theory.FiniteHoles)
    {declared : theory.Interface → Prop} {arity : Type} [Fintype arity]
    {holes : arity → theory.Interface} {result : theory.Interface}
    (context : theory.RegionContext declared holes result) :
    ∃ (weight : Nat) (uses : arity → Nat),
      (∀ filling : (index : arity) → theory.Term (holes index),
        sized.size (context.act filling) =
          weight + ∑ index, uses index * sized.size (filling index)) ∧
      (∀ index, uses index = 0 → ∀ first second : (index : arity) → theory.Term (holes index),
        (∀ other, other ≠ index → first other = second other) →
          context.act first = context.act second) ∧
      ∀ index, ¬ declared (holes index) → uses index = 1 := by
  classical
  obtain ⟨positions, place, inner, admits, acts⟩ := context.realized
  have : Finite positions := finite inner
  have : Fintype positions := Fintype.ofFinite positions
  obtain ⟨weight, adds⟩ := sized.additive inner
  refine ⟨weight, fun index => (Finset.univ.filter fun position => place position = index).card,
    ?_, ?_, ?_⟩
  · intro filling
    rw [acts, adds]
    congr 1
    rw [← Finset.sum_fiberwise Finset.univ place fun position =>
      sized.size (filling (place position))]
    refine Finset.sum_congr rfl fun index _ => ?_
    have fibre : ∀ position ∈ Finset.univ.filter (fun position => place position = index),
        sized.size (filling (place position)) = sized.size (filling index) :=
      fun position member =>
        congrArg (fun other => sized.size (filling other)) (Finset.mem_filter.mp member).2
    rw [Finset.sum_congr rfl fibre, Finset.sum_const, smul_eq_mul]
  · intro index unused first second agree
    have absent : ∀ position, place position ≠ index := fun position placed =>
      Finset.notMem_empty position
        (Finset.card_eq_zero.mp unused ▸ Finset.mem_filter.mpr ⟨Finset.mem_univ _, placed⟩)
    have same : (fun position => first (place position)) = fun position => second (place position) :=
      funext fun position => agree (place position) (absent position)
    rw [acts first, acts second, same]
  · intro index linear
    obtain ⟨position, placed, only⟩ := admits.once index linear
    refine Finset.card_eq_one.mpr ⟨position, ?_⟩
    ext other
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    exact ⟨fun same => only other same, fun same => same ▸ placed⟩

/-- **Each reading of a theory with a linear size has a multiplicity size**,
when the contexts of the theory have finitely many holes. -/
def LinearSize.regionReading (sized : theory.LinearSize) (finite : theory.FiniteHoles)
    (declared : theory.Interface → Prop) : (theory.regionReading declared).MultiplicitySize where
  size := sized.size
  positive := sized.positive
  respects := sized.respects
  counted := fun context => by
    obtain ⟨weight, uses, adds, unused, -⟩ := sized.counted_regionReading finite context
    exact ⟨weight, uses, adds, fun index zero first second agree =>
      ContextMap.equations_of_eq (unused index zero first second agree)⟩

/-! ## Applying -/

/-- The interfaces of the two holes of an application: the function first,
then its argument. -/
abbrev applicationHoles (function argument : theory.Interface) : Bool → theory.Interface :=
  fun index => bif index then argument else function

/-- What fills the two holes of an application. -/
def applicationFilling {function argument : theory.Interface} (applied : theory.Term function)
    (operand : theory.Term argument) :
    (index : Bool) → theory.Term (applicationHoles function argument index)
  | false => applied
  | true => operand

variable (theory) in
/-- **A theory applies**: a context of two holes returns what fills its
second hole for one filling of the first, at two terms that are apart, and
returns the other of the two for another filling of the first.  The first
hole is filled with a function and the context applies it. -/
def Applies (function argument : theory.Interface) : Prop :=
  ∃ (application : theory.Context (applicationHoles function argument) argument)
    (identity constant : theory.Term function) (first second : theory.Term argument),
    ¬ (theory.equations argument).r first second ∧
      (theory.equations argument).r
        (theory.fill application (applicationFilling identity first)) first ∧
      (theory.equations argument).r
        (theory.fill application (applicationFilling identity second)) second ∧
      (theory.equations argument).r
        (theory.fill application (applicationFilling constant first)) second

/-- **No map from a theory that applies into a theory with a multiplicity
size reflects the static equivalence.**  The image of the applying context
does not use its second hole, and then cannot return it; or it uses it, and
then the size leaves no room to use the first. -/
theorem MultiplicitySize.not_reflectsEquations_of_applies {source target : ContextTheory.{u}}
    (sized : target.MultiplicitySize) (map : ContextMap source target)
    {function argument : source.Interface} (applies : source.Applies function argument) :
    ¬ map.ReflectsEquations := by
  obtain ⟨application, identity, constant, first, second, apart, onFirst, onSecond, toSecond⟩ :=
    applies
  obtain ⟨weight, uses, adds, unused⟩ := sized.counted (map.context application)
  intro reflects
  have image : ∀ (applied : source.Term function) (operand : source.Term argument),
      (target.equations (map.interface argument)).r
        (map.term (source.fill application (applicationFilling applied operand)))
        (target.fill (map.context application) fun index =>
          map.term (applicationFilling applied operand index)) :=
    fun applied operand => map.equivariant application _
  have sizeImage : ∀ (applied : source.Term function) (operand : source.Term argument),
      sized.size (map.term (source.fill application (applicationFilling applied operand))) =
        weight + (uses true * sized.size (map.term operand) +
          uses false * sized.size (map.term applied)) := by
    intro applied operand
    rw [sized.respects (image applied operand), adds, Fintype.sum_bool]
    rfl
  have sizeFirst := sizeImage identity first
  rw [sized.respects (map.term_resp onFirst)] at sizeFirst
  by_cases argumentUnused : uses true = 0
  · have same := unused true argumentUnused
      (fun index => map.term (applicationFilling identity first index))
      (fun index => map.term (applicationFilling identity second index))
      (fun other distinct => by
        cases other with
        | false => rfl
        | true => exact (distinct rfl).elim)
    exact apart (reflects ((target.equations _).iseqv.trans
      ((target.equations _).iseqv.symm (map.term_resp onFirst))
      ((target.equations _).iseqv.trans (image identity first)
        ((target.equations _).iseqv.trans same
          ((target.equations _).iseqv.trans
            ((target.equations _).iseqv.symm (image identity second))
            (map.term_resp onSecond))))))
  · have functionUnused : uses false = 0 := by
      have positiveIdentity := sized.positive (map.term identity)
      have atLeast : sized.size (map.term first) ≤ uses true * sized.size (map.term first) :=
        Nat.le_mul_of_pos_left _ (Nat.pos_of_ne_zero argumentUnused)
      have product : uses false * sized.size (map.term identity) = 0 := by
        generalize uses true * sized.size (map.term first) = argumentPart at sizeFirst atLeast
        generalize uses false * sized.size (map.term identity) = functionPart at sizeFirst ⊢
        omega
      rcases Nat.mul_eq_zero.mp product with zero | zero
      · exact zero
      · omega
    have same := unused false functionUnused
      (fun index => map.term (applicationFilling identity first index))
      (fun index => map.term (applicationFilling constant first index))
      (fun other distinct => by
        cases other with
        | false => exact (distinct rfl).elim
        | true => rfl)
    exact apart (reflects ((target.equations _).iseqv.trans
      ((target.equations _).iseqv.symm (map.term_resp onFirst))
      ((target.equations _).iseqv.trans (image identity first)
        ((target.equations _).iseqv.trans same
          ((target.equations _).iseqv.trans
            ((target.equations _).iseqv.symm (image constant first))
            (map.term_resp toSecond))))))

/-- **A theory with a multiplicity size hosts no theory that applies.** -/
theorem MultiplicitySize.not_hosting_of_applies {source target : ContextTheory.{u}}
    (sized : target.MultiplicitySize) (map : ContextMap source target)
    {function argument : source.Interface} (applies : source.Applies function argument) :
    ¬ map.Hosting :=
  fun hosting => sized.not_reflectsEquations_of_applies map applies
    (map.reflectsEquations_of_faithful hosting.faithful)

/-- **Negative**, for `Applies`: a theory with a multiplicity size does not
apply. -/
theorem MultiplicitySize.not_applies (sized : theory.MultiplicitySize)
    (function argument : theory.Interface) : ¬ theory.Applies function argument :=
  fun applies => sized.not_reflectsEquations_of_applies (ContextMap.id theory) applies
    fun related => related

/-- **Negative**, for `MultiplicitySize`: a theory that applies has none. -/
theorem isEmpty_multiplicitySize_of_applies {function argument : theory.Interface}
    (applies : theory.Applies function argument) : IsEmpty theory.MultiplicitySize :=
  ⟨fun sized => sized.not_applies function argument applies⟩

/-! ## What a reading with regions receives -/

section Regions

variable {source : ContextTheory.{u}} {declared : theory.Interface → Prop}

/-- **A map from a theory that discards, into a reading of a theory with a
linear size, sends the interface to a declared one.** -/
theorem LinearSize.declared_of_discards (sized : theory.LinearSize)
    (map : ContextMap source (theory.regionReading declared)) {interface : source.Interface}
    (discards : source.Discards interface) (term : source.Term interface) :
    declared (map.interface interface) := by
  by_contra linear
  obtain ⟨first, returns⟩ := map.discards_on_image discards
  obtain ⟨inner, same⟩ := RegionContext.exists_context first fun _ => linear
  obtain ⟨weight, adds⟩ := sized.additive inner
  have counted := adds fun _ => map.term term
  rw [Fintype.sum_bool] at counted
  have related : (theory.equations (map.interface interface)).r
      (first.act fun _ => map.term term) (map.term term) := returns fun _ => term
  have total : sized.size (map.term term) =
      weight + (sized.size (map.term term) + sized.size (map.term term)) :=
    (sized.respects related).symm.trans
      ((congrArg (fun image => sized.size image) (same fun _ => map.term term)).trans counted)
  have positive := sized.positive (map.term term)
  omega

/-- **The same for a theory that copies.** -/
theorem LinearSize.declared_of_copies (sized : theory.LinearSize)
    (map : ContextMap source (theory.regionReading declared)) {interface : source.Interface}
    (copies : source.Copies interface) (term : source.Term interface) :
    declared (map.interface interface) := by
  by_contra linear
  obtain ⟨pair, twice, copied⟩ := copies
  obtain ⟨innerPair, pairSame⟩ := RegionContext.exists_context (map.context pair) fun _ => linear
  obtain ⟨innerTwice, twiceSame⟩ :=
    RegionContext.exists_context (map.context twice) fun _ => linear
  obtain ⟨pairWeight, pairAdds⟩ := sized.additive innerPair
  obtain ⟨twiceWeight, twiceAdds⟩ := sized.additive innerTwice
  have pairSize : ∀ other : source.Term interface,
      sized.size (map.term (source.fill pair fun _ => other)) =
        pairWeight + (sized.size (map.term other) + sized.size (map.term other)) := by
    intro other
    have image : (theory.equations (map.interface interface)).r
        (map.term (source.fill pair fun _ => other))
        ((map.context pair).act fun _ => map.term other) := map.equivariant pair fun _ => other
    have counted := pairAdds fun _ => map.term other
    rw [Fintype.sum_bool] at counted
    exact (sized.respects image).trans
      ((congrArg (fun image => sized.size image) (pairSame fun _ => map.term other)).trans counted)
  have twiceSize : ∀ other : source.Term interface,
      sized.size (map.term (source.fill pair fun _ => other)) =
        twiceWeight + sized.size (map.term other) := by
    intro other
    have image : (theory.equations (map.interface interface)).r
        (map.term (source.fill twice fun _ => other))
        ((map.context twice).act fun _ => map.term other) := map.equivariant twice fun _ => other
    have moved : (theory.equations (map.interface interface)).r
        (map.term (source.fill twice fun _ => other))
        (map.term (source.fill pair fun _ => other)) := map.term_resp (copied other)
    have counted := twiceAdds fun _ => map.term other
    rw [Fintype.sum_unique] at counted
    exact (sized.respects moved).symm.trans ((sized.respects image).trans
      ((congrArg (fun image => sized.size image) (twiceSame fun _ => map.term other)).trans
        counted))
  have once := (pairSize term).symm.trans (twiceSize term)
  have again := (pairSize (source.fill pair fun _ => term)).symm.trans
    (twiceSize (source.fill pair fun _ => term))
  have paired := pairSize term
  have positive := sized.positive (map.term term)
  omega

/-- **A region of data receives a source that discards as data**: when no
term of a declared interface has a step, a map from a theory that discards at
an interface preserves no step taken there. -/
theorem LinearSize.not_preserves_of_discards_of_static (sized : theory.LinearSize)
    (static : ∀ interface, declared interface →
      ∀ term next : theory.Term interface, ¬ theory.rewrites term next)
    (map : ContextMap source (theory.regionReading declared)) {interface : source.Interface}
    (discards : source.Discards interface) {term next : source.Term interface}
    (step : source.rewrites term next) : ¬ map.PreservesTransitions :=
  fun preserves => static _ (sized.declared_of_discards map discards term) _ _
    (map.preservesRewrites_of_transitions preserves step)

end Regions

/-- **A rank of a theory is a rank of each of its readings.** -/
def Rank.regionReading (ranked : theory.Rank) (declared : theory.Interface → Prop) :
    (theory.regionReading declared).Rank where
  rank := ranked.rank
  lowers := ranked.lowers

/-! ## Examples -/

/-- **Positive**: the cartesian reading of a theory given by its terms alone
has a multiplicity size; every term has size one. -/
def termsAloneCartesianSize (theory : GSLT.{u}) :
    theory.termsAlone.cartesianReading.MultiplicitySize :=
  (GSLT.termsAloneLinearSize theory).regionReading (termsAlone_finiteHoles theory) fun _ => True

/-- So a context of two holes of that reading uses at most one of them. -/
theorem termsAlone_cartesian_uses_one (theory : GSLT.{u})
    (context : theory.termsAlone.cartesianReading.Context (fun _ : Bool => PUnit.unit) PUnit.unit)
    (inhabited : Nonempty theory.Term) :
    ∃ index : Bool, ∀ first second : Bool → theory.Term,
      (∀ other, other ≠ index → first other = second other) →
        context.act first = context.act second := by
  obtain ⟨weight, uses, adds, unused, -⟩ :=
    (GSLT.termsAloneLinearSize theory).counted_regionReading (termsAlone_finiteHoles theory) context
  obtain ⟨term⟩ := inhabited
  have filled := adds fun _ => term
  rw [Fintype.sum_bool] at filled
  change 1 = weight + (uses true * 1 + uses false * 1) at filled
  by_cases first : uses true = 0
  · exact ⟨true, unused true first⟩
  · exact ⟨false, unused false (by omega)⟩

end ContextTheory

#print axioms ContextTheory.termsAlone_finiteHoles
#print axioms ContextTheory.rewritingTheory_not_finiteHoles
#print axioms ContextTheory.LinearSize.multiplicitySize
#print axioms ContextTheory.LinearSize.counted_regionReading
#print axioms ContextTheory.LinearSize.regionReading
#print axioms ContextTheory.MultiplicitySize.not_reflectsEquations_of_applies
#print axioms ContextTheory.MultiplicitySize.not_hosting_of_applies
#print axioms ContextTheory.MultiplicitySize.not_applies
#print axioms ContextTheory.LinearSize.declared_of_discards
#print axioms ContextTheory.LinearSize.declared_of_copies
#print axioms ContextTheory.LinearSize.not_preserves_of_discards_of_static
#print axioms ContextTheory.Rank.regionReading
#print axioms ContextTheory.termsAlone_cartesian_uses_one

end Mettapedia.GSLT
