import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.Regions.Steps
import Mettapedia.Algebra.FootprintQuantale
import Mathlib.Logic.Function.DependsOn

/-!
# Footprints that are sets

`FootprintedSpaceTransactions` certifies a transition of a located state at a
finite set of locations.  A read of every atom that a pattern matches reads a
set of locations that need not be finite.  This module states the certificate,
the frame law and the diamond for a footprint that is any set of locations, and
shows that the finite certificate is the case of a finite set.

* `SetFootprinted`, `SetEffectFootprinted`, `SetIndependentEffects`: the
  certificates and independence, with `Set.EqOn` for agreement.  A value read
  from the state at a set of locations is Mathlib's `DependsOn`.
* `setFootprinted_coe_iff`, `setEffectFootprinted_coe_iff`,
  `setIndependentEffects_coe_iff`: at a finite set they are `Footprinted`,
  `EffectFootprinted` and `IndependentEffects`.
* `SetFootprinted.disjoint_commute`, `SetEffectFootprinted.independent_commute`:
  the two diamonds.  `SetEffectFootprinted.comp`: closure under sequential
  composition.  `SetEffectFootprinted.eq_none_of_eqOn`,
  `SetEffectFootprinted.bind_comm`: a refusal is local, and independent partial
  functions commute.  These three are what the laws of regions use of a footprint.
* `SetEffectFootprinted.guarded`: a certified transition with one more condition
  on firing, read at a set of locations.  This is how a read of a whole pattern
  enters a rule.
* `GradedBy`: the certificate read as a grade in the quantale of footprints of
  `Algebra.FootprintQuantale`, whose elements are sets and not finite sets.  The
  transition that changes nothing has the unit (`gradedBy_one`); composition
  multiplies (`GradedBy.comp`); a stronger grade gives every weaker one
  (`GradedBy.of_le`); two transitions whose grades have the unit as their join
  commute (`GradedBy.commute`).

## What finiteness is for

Every relation has the footprint of all locations (`SetFootprinted.univ`), and a
footprint may be enlarged (`SetFootprinted.mono`).  So a certificate at a set
says something only through which set it is.  None of the laws above uses that
the set is finite, or that membership in it is decidable.

Finiteness is used for three things, and all three are tests, not laws.

* *Validation.*  Whether two states agree on a footprint is decided location by
  location.  When one state comes from the other by a transition that writes
  finitely many locations, agreement on any set of reads is a finite check, given
  that membership in the set is decidable (`eqOn_iff_of_preservesOutside`,
  `decidableEqOnOfPreservesOutside`).
* *Independence.*  Whether finitely many written locations avoid a set of reads
  is a finite check, given decidable membership (`disjoint_coe_left_iff`,
  `decidableDisjointCoeLeft`).  Whether two infinite footprints are disjoint is
  not such a check; for two patterns it is unification
  (`PatternFootprints.Patterns`).
* *The firing of a rule as a function* asks every written location for what the
  rule consumes there.

One statement is about finiteness itself: a test that the whole bag is empty has
no finite footprint over an infinite alphabet
(`FootprintedSpaceTransactions.emptinessTest_not_effectFootprinted`).  As sets,
its footprints are exactly those that cover every location
(`emptinessTest_setEffectFootprinted_iff`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.PatternFootprints

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.FootprintedSpaceTransactions
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.Regions
open Mettapedia.GSLT.SeparationAlgebra

universe u v

variable {Location : Type u} {Value : Type v}

/-! ## One footprint -/

/-- **A transition certified at a set of locations.**  It leaves every location
outside the set as it was, and it can be replayed, with the same result on the
set, from every state that agrees with the source on the set. -/
structure SetFootprinted (relation : (Location → Value) → (Location → Value) → Prop)
    (footprint : Set Location) : Prop where
  preserves : ∀ {source target}, relation source target → Set.EqOn target source footprintᶜ
  frame : ∀ {source target}, relation source target →
    ∀ framedSource, Set.EqOn source framedSource footprint →
      ∃ framedTarget,
        relation framedSource framedTarget ∧
        Set.EqOn target framedTarget footprint ∧
        Set.EqOn framedTarget framedSource footprintᶜ

/-- Agreement on a finite footprint is agreement on its set of locations. -/
theorem agreesOn_iff_eqOn [DecidableEq Location] {footprint : Finset Location}
    {left right : Location → Value} :
    AgreesOn footprint left right ↔ Set.EqOn left right ↑footprint :=
  ⟨fun agrees location inside => agrees location (Finset.mem_coe.mp inside),
    fun agrees _ inside => agrees (Finset.mem_coe.mpr inside)⟩

/-- Preservation outside a finite footprint is agreement on the complement of its
set of locations. -/
theorem preservesOutside_iff_eqOn [DecidableEq Location] {footprint : Finset Location}
    {source target : Location → Value} :
    PreservesOutside footprint source target ↔ Set.EqOn target source (↑footprint)ᶜ :=
  ⟨fun preserves location outside =>
      preserves location fun inside => outside (Finset.mem_coe.mpr inside),
    fun preserves location outside =>
      preserves (show location ∈ (↑footprint : Set Location)ᶜ from
        fun inside => outside (Finset.mem_coe.mp inside))⟩

/-- **The finite certificate is the certificate at a finite set.** -/
theorem setFootprinted_coe_iff [DecidableEq Location]
    {relation : (Location → Value) → (Location → Value) → Prop} {footprint : Finset Location} :
    SetFootprinted relation ↑footprint ↔ Footprinted relation footprint := by
  constructor
  · intro certified
    constructor
    · intro source target step
      exact preservesOutside_iff_eqOn.mpr (certified.preserves step)
    · intro source target step framedSource agrees
      obtain ⟨framedTarget, framedStep, written, outside⟩ :=
        certified.frame step framedSource (agreesOn_iff_eqOn.mp agrees)
      exact ⟨framedTarget, framedStep, agreesOn_iff_eqOn.mpr written,
        preservesOutside_iff_eqOn.mpr outside⟩
  · intro certified
    constructor
    · intro source target step
      exact preservesOutside_iff_eqOn.mp (certified.preserves step)
    · intro source target step framedSource agrees
      obtain ⟨framedTarget, framedStep, written, outside⟩ :=
        certified.frame step framedSource (agreesOn_iff_eqOn.mpr agrees)
      exact ⟨framedTarget, framedStep, agreesOn_iff_eqOn.mp written,
        preservesOutside_iff_eqOn.mp outside⟩

namespace SetFootprinted

/-- **Every relation is certified at the set of all locations.**  A certificate
says something only through which set it names. -/
theorem univ (relation : (Location → Value) → (Location → Value) → Prop) :
    SetFootprinted relation Set.univ where
  preserves _ _ outside := absurd (Set.mem_univ _) outside
  frame {source target} step framedSource agrees := by
    have same : framedSource = source :=
      funext fun location => (agrees (Set.mem_univ location)).symm
    exact ⟨target, same ▸ step, fun _ _ => rfl, fun _ outside => absurd (Set.mem_univ _) outside⟩

/-- A footprint may be enlarged. -/
theorem mono {relation : (Location → Value) → (Location → Value) → Prop}
    {small large : Set Location} (certified : SetFootprinted relation small)
    (subset : small ⊆ large) : SetFootprinted relation large where
  preserves step _ outside := certified.preserves step fun inside => outside (subset inside)
  frame {source target} step framedSource agrees := by
    classical
    obtain ⟨framedTarget, framedStep, written, outside⟩ :=
      certified.frame step framedSource (agrees.mono subset)
    refine ⟨framedTarget, framedStep, ?_, fun _ notLarge =>
      outside fun inside => notLarge (subset inside)⟩
    intro location inside
    by_cases inSmall : location ∈ small
    · exact written inSmall
    · exact (certified.preserves step inSmall).trans ((agrees inside).trans (outside inSmall).symm)

/-- **The diamond of footprints that are sets.**  Two certified transitions from
one state commute when their footprints are disjoint. -/
theorem disjoint_commute
    {firstRelation secondRelation : (Location → Value) → (Location → Value) → Prop}
    {firstFootprint secondFootprint : Set Location}
    (firstCertified : SetFootprinted firstRelation firstFootprint)
    (secondCertified : SetFootprinted secondRelation secondFootprint)
    (disjoint : Disjoint firstFootprint secondFootprint)
    {source afterFirst afterSecond : Location → Value}
    (firstStep : firstRelation source afterFirst)
    (secondStep : secondRelation source afterSecond) :
    ∃ joined, secondRelation afterFirst joined ∧ firstRelation afterSecond joined := by
  classical
  have firstPreserves := firstCertified.preserves firstStep
  have secondPreserves := secondCertified.preserves secondStep
  have apart : ∀ {location}, location ∈ secondFootprint → location ∉ firstFootprint :=
    fun inSecond inFirst => Set.disjoint_left.mp disjoint inFirst inSecond
  have sourceAfterFirstAgree : Set.EqOn source afterFirst secondFootprint :=
    fun _ inSecond => (firstPreserves (apart inSecond)).symm
  have sourceAfterSecondAgree : Set.EqOn source afterSecond firstFootprint :=
    fun _ inFirst => (secondPreserves fun inSecond => apart inSecond inFirst).symm
  obtain ⟨joinedForward, secondAfterFirst, secondLocal, secondFrame⟩ :=
    secondCertified.frame secondStep afterFirst sourceAfterFirstAgree
  obtain ⟨joinedReverse, firstAfterSecond, firstLocal, firstFrame⟩ :=
    firstCertified.frame firstStep afterSecond sourceAfterSecondAgree
  have joinedEqual : joinedForward = joinedReverse := by
    funext location
    by_cases inSecond : location ∈ secondFootprint
    · exact (secondLocal inSecond).symm.trans (firstFrame (apart inSecond)).symm
    · have forwardAt : joinedForward location = afterFirst location := secondFrame inSecond
      by_cases inFirst : location ∈ firstFootprint
      · exact forwardAt.trans (firstLocal inFirst)
      · exact forwardAt.trans ((firstPreserves inFirst).trans
          ((secondPreserves inSecond).symm.trans (firstFrame inFirst).symm))
  exact ⟨joinedForward, secondAfterFirst, joinedEqual ▸ firstAfterSecond⟩

end SetFootprinted

/-- The finite diamond is the diamond of sets at two finite sets. -/
example [DecidableEq Location]
    {firstRelation secondRelation : (Location → Value) → (Location → Value) → Prop}
    {firstFootprint secondFootprint : Finset Location}
    (firstCertified : Footprinted firstRelation firstFootprint)
    (secondCertified : Footprinted secondRelation secondFootprint)
    (disjoint : Disjoint firstFootprint secondFootprint)
    {source afterFirst afterSecond : Location → Value}
    (firstStep : firstRelation source afterFirst) (secondStep : secondRelation source afterSecond) :
    ∃ joined, secondRelation afterFirst joined ∧ firstRelation afterSecond joined :=
  (setFootprinted_coe_iff.mpr firstCertified).disjoint_commute
    (setFootprinted_coe_iff.mpr secondCertified) (Finset.disjoint_coe.mpr disjoint)
    firstStep secondStep

/-! ## Reads and writes -/

/-- **A transition certified at a set of reads and a set of writes.**  It changes
nothing outside the writes, and it can be replayed, with the same values written,
from every state that agrees with the source on the reads and the writes. -/
structure SetEffectFootprinted (relation : (Location → Value) → (Location → Value) → Prop)
    (reads writes : Set Location) : Prop where
  preserves : ∀ {source target}, relation source target → Set.EqOn target source writesᶜ
  frame : ∀ {source target}, relation source target →
    ∀ framedSource, Set.EqOn source framedSource (reads ∪ writes) →
      ∃ framedTarget,
        relation framedSource framedTarget ∧
        Set.EqOn target framedTarget writes ∧
        Set.EqOn framedTarget framedSource writesᶜ

/-- **Independence of two read and write footprints that are sets**: the writes
of each meet neither the reads nor the writes of the other. -/
def SetIndependentEffects (firstReads firstWrites secondReads secondWrites : Set Location) :
    Prop :=
  Disjoint firstWrites (secondReads ∪ secondWrites) ∧
    Disjoint secondWrites (firstReads ∪ firstWrites)

theorem SetIndependentEffects.symm {firstReads firstWrites secondReads secondWrites : Set Location}
    (independent : SetIndependentEffects firstReads firstWrites secondReads secondWrites) :
    SetIndependentEffects secondReads secondWrites firstReads firstWrites :=
  ⟨independent.2, independent.1⟩

/-- At finite sets it is the independence of finite footprints. -/
theorem setIndependentEffects_coe_iff [DecidableEq Location]
    {firstReads firstWrites secondReads secondWrites : Finset Location} :
    SetIndependentEffects (firstReads : Set Location) (firstWrites : Set Location)
        (secondReads : Set Location) (secondWrites : Set Location) ↔
      IndependentEffects firstReads firstWrites secondReads secondWrites := by
  unfold SetIndependentEffects IndependentEffects
  rw [← Finset.coe_union, ← Finset.coe_union, Finset.disjoint_coe, Finset.disjoint_coe]

/-- **The finite read and write certificate is the certificate at finite sets.** -/
theorem setEffectFootprinted_coe_iff [DecidableEq Location]
    {relation : (Location → Value) → (Location → Value) → Prop} {reads writes : Finset Location} :
    SetEffectFootprinted relation ↑reads ↑writes ↔ EffectFootprinted relation reads writes := by
  constructor
  · intro certified
    constructor
    · intro source target step
      exact preservesOutside_iff_eqOn.mpr (certified.preserves step)
    · intro source target step framedSource agrees
      obtain ⟨framedTarget, framedStep, written, outside⟩ :=
        certified.frame step framedSource
          (by rw [← Finset.coe_union]; exact agreesOn_iff_eqOn.mp agrees)
      exact ⟨framedTarget, framedStep, agreesOn_iff_eqOn.mpr written,
        preservesOutside_iff_eqOn.mpr outside⟩
  · intro certified
    constructor
    · intro source target step
      exact preservesOutside_iff_eqOn.mp (certified.preserves step)
    · intro source target step framedSource agrees
      obtain ⟨framedTarget, framedStep, written, outside⟩ :=
        certified.frame step framedSource
          (agreesOn_iff_eqOn.mpr (by rw [Finset.coe_union]; exact agrees))
      exact ⟨framedTarget, framedStep, agreesOn_iff_eqOn.mp written,
        preservesOutside_iff_eqOn.mp outside⟩

namespace SetEffectFootprinted

/-- A read and write certificate is a certificate at the union of the two sets. -/
theorem setFootprinted {relation : (Location → Value) → (Location → Value) → Prop}
    {reads writes : Set Location} (certified : SetEffectFootprinted relation reads writes) :
    SetFootprinted relation (reads ∪ writes) where
  preserves step _ outside :=
    certified.preserves step fun written => outside (Or.inr written)
  frame {source target} step framedSource agrees := by
    classical
    obtain ⟨framedTarget, framedStep, writtenAgree, framedPreserves⟩ :=
      certified.frame step framedSource agrees
    refine ⟨framedTarget, framedStep, ?_, fun _ outside =>
      framedPreserves fun written => outside (Or.inr written)⟩
    intro location inside
    by_cases written : location ∈ writes
    · exact writtenAgree written
    · exact (certified.preserves step written).trans
        ((agrees inside).trans (framedPreserves written).symm)

/-- A certificate stays a certificate when more locations are declared read. -/
theorem mono_reads {relation : (Location → Value) → (Location → Value) → Prop}
    {reads moreReads writes : Set Location}
    (certified : SetEffectFootprinted relation reads writes) (subset : reads ⊆ moreReads) :
    SetEffectFootprinted relation moreReads writes where
  preserves := certified.preserves
  frame step framedSource agrees :=
    certified.frame step framedSource
      (agrees.mono (Set.union_subset_union_left writes subset))

/-- **The diamond of reads and writes that are sets.**  Shared reads are
permitted; the writes of each avoid everything the other reads or writes. -/
theorem independent_commute
    {firstRelation secondRelation : (Location → Value) → (Location → Value) → Prop}
    {firstReads firstWrites secondReads secondWrites : Set Location}
    (firstCertified : SetEffectFootprinted firstRelation firstReads firstWrites)
    (secondCertified : SetEffectFootprinted secondRelation secondReads secondWrites)
    (independent : SetIndependentEffects firstReads firstWrites secondReads secondWrites)
    {source afterFirst afterSecond : Location → Value}
    (firstStep : firstRelation source afterFirst)
    (secondStep : secondRelation source afterSecond) :
    ∃ joined, secondRelation afterFirst joined ∧ firstRelation afterSecond joined := by
  classical
  have firstPreserves := firstCertified.preserves firstStep
  have secondPreserves := secondCertified.preserves secondStep
  have sourceAfterFirstAgree : Set.EqOn source afterFirst (secondReads ∪ secondWrites) :=
    fun _ inside =>
      (firstPreserves fun written => Set.disjoint_left.mp independent.1 written inside).symm
  have sourceAfterSecondAgree : Set.EqOn source afterSecond (firstReads ∪ firstWrites) :=
    fun _ inside =>
      (secondPreserves fun written => Set.disjoint_left.mp independent.2 written inside).symm
  obtain ⟨joinedForward, secondAfterFirst, secondLocal, secondFrame⟩ :=
    secondCertified.frame secondStep afterFirst sourceAfterFirstAgree
  obtain ⟨joinedReverse, firstAfterSecond, firstLocal, firstFrame⟩ :=
    firstCertified.frame firstStep afterSecond sourceAfterSecondAgree
  have joinedEqual : joinedForward = joinedReverse := by
    funext location
    by_cases inSecondWrite : location ∈ secondWrites
    · have notFirstWrite : location ∉ firstWrites := fun inFirstWrite =>
        Set.disjoint_left.mp independent.1 inFirstWrite (Or.inr inSecondWrite)
      exact (secondLocal inSecondWrite).symm.trans (firstFrame notFirstWrite).symm
    · have forwardAt : joinedForward location = afterFirst location := secondFrame inSecondWrite
      by_cases inFirstWrite : location ∈ firstWrites
      · exact forwardAt.trans (firstLocal inFirstWrite)
      · exact forwardAt.trans ((firstPreserves inFirstWrite).trans
          ((secondPreserves inSecondWrite).symm.trans (firstFrame inFirstWrite).symm))
  exact ⟨joinedForward, secondAfterFirst, joinedEqual ▸ firstAfterSecond⟩

/-- **The certificate is closed under sequential composition**: one transition
after another reads what either reads and writes what either writes. -/
theorem comp {first second : (Location → Value) → (Location → Value) → Prop}
    {firstReads firstWrites secondReads secondWrites : Set Location}
    (firstCertified : SetEffectFootprinted first firstReads firstWrites)
    (secondCertified : SetEffectFootprinted second secondReads secondWrites) :
    SetEffectFootprinted
      (fun source target => ∃ middle, first source middle ∧ second middle target)
      (firstReads ∪ secondReads) (firstWrites ∪ secondWrites) where
  preserves := by
    rintro source target ⟨middle, firstStep, secondStep⟩ location outside
    exact (secondCertified.preserves secondStep fun written => outside (Or.inr written)).trans
      (firstCertified.preserves firstStep fun written => outside (Or.inl written))
  frame := by
    classical
    rintro source target ⟨middle, firstStep, secondStep⟩ framedSource agrees
    obtain ⟨framedMiddle, framedFirst, firstWritten, firstOutside⟩ :=
      firstCertified.frame firstStep framedSource
        (agrees.mono (Set.union_subset_union Set.subset_union_left Set.subset_union_left))
    have middleAgrees : Set.EqOn middle framedMiddle (secondReads ∪ secondWrites) := by
      intro location inside
      by_cases written : location ∈ firstWrites
      · exact firstWritten written
      · exact (firstCertified.preserves firstStep written).trans
          ((agrees (Set.union_subset_union Set.subset_union_right Set.subset_union_right
            inside)).trans (firstOutside written).symm)
    obtain ⟨framedTarget, framedSecond, secondWritten, secondOutside⟩ :=
      secondCertified.frame secondStep framedMiddle middleAgrees
    refine ⟨framedTarget, ⟨framedMiddle, framedFirst, framedSecond⟩, ?_, ?_⟩
    · intro location inside
      by_cases written : location ∈ secondWrites
      · exact secondWritten written
      · have inFirst : location ∈ firstWrites := inside.resolve_right written
        exact (secondCertified.preserves secondStep written).trans
          ((firstWritten inFirst).trans (secondOutside written).symm)
    · intro location outside
      exact (secondOutside fun written => outside (Or.inr written)).trans
        (firstOutside fun written => outside (Or.inl written))

/-- **A certified transition with one more condition on firing.**  The
condition is read at a set of locations, and the transition with the condition
reads that set as well.  A rule whose guard asks about every atom of a pattern is
certified this way, with the pattern among its reads. -/
theorem guarded {relation : (Location → Value) → (Location → Value) → Prop}
    {reads writes conditionReads : Set Location} {condition : (Location → Value) → Prop}
    (certified : SetEffectFootprinted relation reads writes)
    (conditionLocal : DependsOn condition conditionReads) :
    SetEffectFootprinted (fun source target => condition source ∧ relation source target)
      (conditionReads ∪ reads) writes where
  preserves step := certified.preserves step.2
  frame {source target} step framedSource agrees := by
    obtain ⟨framedTarget, framedStep, written, outside⟩ :=
      certified.frame step.2 framedSource
        (agrees.mono (Set.union_subset_union_left writes Set.subset_union_right))
    have sameCondition : condition source = condition framedSource :=
      conditionLocal fun location inside => agrees (Or.inl (Or.inl inside))
    exact ⟨framedTarget, ⟨sameCondition ▸ step.1, framedStep⟩, written, outside⟩

/-- **A refusal is local**: a certified partial function that refuses a state
refuses every state that agrees with it on what it reads or writes. -/
theorem eq_none_of_eqOn {act : (Location → Value) → Option (Location → Value)}
    {reads writes : Set Location}
    (certified : SetEffectFootprinted (fun source target => act source = some target) reads writes)
    {source framed : Location → Value} (agrees : Set.EqOn source framed (reads ∪ writes))
    (refused : act source = none) : act framed = none := by
  cases fired : act framed with
  | none => rfl
  | some target =>
      obtain ⟨back, backFired, -, -⟩ := certified.frame fired source agrees.symm
      rw [refused] at backFired
      cases backFired

/-- **Independent certified partial functions commute**: in either order both
fire with one result, or both orders are refused. -/
theorem bind_comm {firstAct secondAct : (Location → Value) → Option (Location → Value)}
    {firstReads firstWrites secondReads secondWrites : Set Location}
    (firstCertified :
      SetEffectFootprinted (fun source target => firstAct source = some target) firstReads
        firstWrites)
    (secondCertified :
      SetEffectFootprinted (fun source target => secondAct source = some target) secondReads
        secondWrites)
    (independent : SetIndependentEffects firstReads firstWrites secondReads secondWrites)
    (world : Location → Value) :
    (firstAct world).bind secondAct = (secondAct world).bind firstAct := by
  cases firstFired : firstAct world with
  | none =>
      cases secondFired : secondAct world with
      | none => rfl
      | some afterSecond =>
          have kept : Set.EqOn world afterSecond (firstReads ∪ firstWrites) := fun _ inside =>
            (secondCertified.preserves secondFired fun written =>
              Set.disjoint_left.mp independent.2 written inside).symm
          exact (firstCertified.eq_none_of_eqOn kept firstFired).symm
  | some afterFirst =>
      cases secondFired : secondAct world with
      | none =>
          have kept : Set.EqOn world afterFirst (secondReads ∪ secondWrites) := fun _ inside =>
            (firstCertified.preserves firstFired fun written =>
              Set.disjoint_left.mp independent.1 written inside).symm
          exact secondCertified.eq_none_of_eqOn kept secondFired
      | some afterSecond =>
          obtain ⟨joined, secondAfterFirst, firstAfterSecond⟩ :=
            firstCertified.independent_commute secondCertified independent firstFired secondFired
          exact secondAfterFirst.trans firstAfterSecond.symm

end SetEffectFootprinted

/-- The certificate of a local rule, at the sets of its read and written
locations. -/
theorem LocalRule.setEffectFootprinted [DecidableEq Location] [Zero Value] [Add Value]
    [SepAlgebra Value] (rule : LocalRule Location Value) :
    SetEffectFootprinted rule.Fires ↑rule.reads ↑rule.writes :=
  setEffectFootprinted_coe_iff.mpr rule.effectFootprinted

/-! ## Footprints as grades -/

section Grades

open Mettapedia.Algebra.FootprintQuantale

/-- A footprint certificate is a read and write certificate that reads nothing
besides what it writes. -/
theorem SetFootprinted.setEffectFootprinted
    {relation : (Location → Value) → (Location → Value) → Prop} {footprint : Set Location}
    (certified : SetFootprinted relation footprint) :
    SetEffectFootprinted relation ∅ footprint where
  preserves := certified.preserves
  frame step framedSource agrees :=
    certified.frame step framedSource (by rwa [Set.empty_union] at agrees)

/-- **A transition graded by a footprint** of the quantale of footprints
(`Algebra.FootprintQuantale`): it is certified at the labels of the grade.  In that
quantale a grade with fewer labels is the stronger claim, the unit uses nothing,
and the product of two grades has the labels of both. -/
def GradedBy (relation : (Location → Value) → (Location → Value) → Prop)
    (grade : Footprint Location) : Prop :=
  SetFootprinted relation grade.labels

/-- The transition that changes nothing has the unit as its grade. -/
theorem gradedBy_one :
    GradedBy (fun source target : Location → Value => target = source) 1 where
  preserves same _ _ := congrFun same _
  frame _ framedSource _ :=
    ⟨framedSource, rfl,
      fun location inside =>
        absurd (show location ∈ (∅ : Set Location) from inside) (Set.notMem_empty location),
      fun _ _ => rfl⟩

/-- **Composition multiplies grades**: one transition after another is graded by
the product. -/
theorem GradedBy.comp {first second : (Location → Value) → (Location → Value) → Prop}
    {firstGrade secondGrade : Footprint Location} (firstGraded : GradedBy first firstGrade)
    (secondGraded : GradedBy second secondGrade) :
    GradedBy (fun source target => ∃ middle, first source middle ∧ second middle target)
      (firstGrade * secondGrade) := by
  have composed :=
    (firstGraded.setEffectFootprinted.comp secondGraded.setEffectFootprinted).setFootprinted
  rw [Set.empty_union, Set.empty_union] at composed
  exact composed

/-- **A stronger grade gives every weaker one.** -/
theorem GradedBy.of_le {relation : (Location → Value) → (Location → Value) → Prop}
    {weaker stronger : Footprint Location} (graded : GradedBy relation stronger)
    (le : weaker ≤ stronger) : GradedBy relation weaker :=
  SetFootprinted.mono graded ((Footprint.le_iff_superset weaker stronger).mp le)

/-- **The diamond, in the quantale**: two transitions whose grades have the unit
as their join, that is, share no label, commute. -/
theorem GradedBy.commute {first second : (Location → Value) → (Location → Value) → Prop}
    {firstGrade secondGrade : Footprint Location} (firstGraded : GradedBy first firstGrade)
    (secondGraded : GradedBy second secondGrade) (apart : Codisjoint firstGrade secondGrade)
    {source afterFirst afterSecond : Location → Value} (firstStep : first source afterFirst)
    (secondStep : second source afterSecond) :
    ∃ joined, second afterFirst joined ∧ first afterSecond joined :=
  SetFootprinted.disjoint_commute firstGraded secondGraded (disjoint_ofDual_iff.mpr apart)
    firstStep secondStep

end Grades

/-! ## Tests that are finite checks -/

/-- **Validation of a set of reads against finitely many writes is a finite
check.**  When the target differs from the source at most on finitely many
written locations, the two agree on a set of reads exactly when they agree on
the written locations that are read. -/
theorem eqOn_iff_of_preservesOutside [DecidableEq Location] {writes : Finset Location}
    {reads : Set Location} {source target : Location → Value}
    (preserves : PreservesOutside writes source target) :
    Set.EqOn source target reads ↔
      ∀ location ∈ writes, location ∈ reads → source location = target location := by
  constructor
  · intro agrees location _ inside
    exact agrees inside
  · intro checked location inside
    by_cases written : location ∈ writes
    · exact checked location written inside
    · exact (preserves location written).symm

/-- So it is decided, when membership in the set of reads is. -/
def decidableEqOnOfPreservesOutside [DecidableEq Location] [DecidableEq Value]
    {writes : Finset Location} {reads : Set Location} [DecidablePred (· ∈ reads)]
    {source target : Location → Value} (preserves : PreservesOutside writes source target) :
    Decidable (Set.EqOn source target reads) :=
  decidable_of_iff _ (eqOn_iff_of_preservesOutside preserves).symm

/-- **Independence of finitely many writes from a set of reads is a finite
check.** -/
theorem disjoint_coe_left_iff {writes : Finset Location} {reads : Set Location} :
    Disjoint (↑writes : Set Location) reads ↔ ∀ location ∈ writes, location ∉ reads :=
  Set.disjoint_left

/-- So it is decided, when membership in the set of reads is. -/
instance decidableDisjointCoeLeft (writes : Finset Location) (reads : Set Location)
    [DecidablePred (· ∈ reads)] : Decidable (Disjoint (↑writes : Set Location) reads) :=
  decidable_of_iff _ disjoint_coe_left_iff.symm

/-! ## A test of the whole bag -/

/-- **The footprints of a test that the whole bag is empty are exactly those that
cover every location and write the atom it adds.**  Over an infinite alphabet
none of them is finite. -/
theorem emptinessTest_setEffectFootprinted_iff {Atom : Type u} [DecidableEq Atom] (atom : Atom)
    (reads writes : Set Atom) :
    SetEffectFootprinted (EmptinessTest atom) reads writes ↔
      reads ∪ writes = Set.univ ∧ atom ∈ writes := by
  classical
  constructor
  · intro certified
    have fires : EmptinessTest atom 0 (Pi.single atom 1) := ⟨rfl, rfl⟩
    constructor
    · apply Set.eq_univ_of_forall
      intro outside
      by_contra notMem
      obtain ⟨_, ⟨empty, -⟩, -, -⟩ :=
        certified.frame fires (Pi.single outside 1) (by
          intro other inside
          have different : other ≠ outside := fun same => notMem (same ▸ inside)
          simp [different])
      have := congrFun empty outside
      simp at this
    · by_contra notWritten
      have := certified.preserves fires notWritten
      simp at this
  · rintro ⟨covers, written⟩
    constructor
    · rintro source target ⟨rfl, rfl⟩ location outside
      have different : location ≠ atom := fun same => outside (same ▸ written)
      simp [different]
    · rintro source target ⟨rfl, rfl⟩ framedSource agrees
      have empty : framedSource = 0 := funext fun location =>
        (agrees (covers ▸ Set.mem_univ location)).symm
      refine ⟨Pi.single atom 1, ⟨empty, rfl⟩, fun _ _ => rfl, ?_⟩
      intro location outside
      have different : location ≠ atom := fun same => outside (same ▸ written)
      simp [empty, different]

/-- The statement about finite footprints follows: over an infinite alphabet no
finite sets cover every location. -/
example {Atom : Type u} [DecidableEq Atom] [Infinite Atom] (atom : Atom)
    (reads writes : Finset Atom) : ¬ EffectFootprinted (EmptinessTest atom) reads writes := by
  intro certified
  have covers := ((emptinessTest_setEffectFootprinted_iff atom ↑reads ↑writes).mp
    (setEffectFootprinted_coe_iff.mpr certified)).1
  rw [← Finset.coe_union] at covers
  exact Set.infinite_univ (covers ▸ (reads ∪ writes).finite_toSet)

/-! ## Controls -/

namespace Controls

/-- **Positive**: adding an atom to a space is certified at the set of that one
space. -/
theorem addAtom_setEffectFootprinted (atom : ℕ) :
    SetEffectFootprinted (SpaceRules.addAtom (Location := Bool) true atom).Fires ∅ {true} := by
  have certified := LocalRule.setEffectFootprinted (SpaceRules.addAtom (Location := Bool) true atom)
  simpa [SpaceRules.addAtom, LocalRule.unguarded] using certified

/-- **Negative**: it is not certified at the empty set of writes: it changes the
space. -/
theorem addAtom_not_setEffectFootprinted_empty (atom : ℕ) :
    ¬ SetEffectFootprinted (SpaceRules.addAtom (Location := Bool) true atom).Fires ∅ ∅ := by
  intro certified
  have fires : (SpaceRules.addAtom (Location := Bool) true atom).Fires 0 (Pi.single true {atom}) :=
    (SpaceRules.addAtom_fires_iff _ _ _ _).mpr (by simp)
  have unchanged := certified.preserves fires (Set.notMem_empty true)
  simp at unchanged

/-- **Negative, one footprint**: nor at the empty footprint. -/
theorem addAtom_not_setFootprinted_empty (atom : ℕ) :
    ¬ SetFootprinted (SpaceRules.addAtom (Location := Bool) true atom).Fires ∅ := by
  intro certified
  have fires : (SpaceRules.addAtom (Location := Bool) true atom).Fires 0 (Pi.single true {atom}) :=
    (SpaceRules.addAtom_fires_iff _ _ _ _).mpr (by simp)
  have unchanged := certified.preserves fires (Set.notMem_empty true)
  simp at unchanged

/-- **Positive, one footprint**: it is certified at the set of that one space. -/
theorem addAtom_setFootprinted (atom : ℕ) :
    SetFootprinted (SpaceRules.addAtom (Location := Bool) true atom).Fires {true} := by
  have certified := (addAtom_setEffectFootprinted atom).setFootprinted
  rwa [Set.empty_union] at certified

/-- **Positive, independence**: a write of one space and a read of another. -/
theorem independent_apart :
    SetIndependentEffects (∅ : Set Bool) {true} {false} ∅ := by
  constructor <;> simp

/-- **Negative, independence**: a write of the space the other reads. -/
theorem not_independent_when_read :
    ¬ SetIndependentEffects (∅ : Set Bool) {true} {true} ∅ := by
  intro independent
  exact Set.disjoint_left.mp independent.1 rfl (Or.inl rfl)

/-- **Positive, a grade**: adding an atom to a space is graded by the footprint of
that space.  **Negative**: it is not graded by the unit. -/
theorem gradedBy_instances (atom : ℕ) :
    GradedBy (SpaceRules.addAtom (Location := Bool) true atom).Fires
        (Mettapedia.Algebra.FootprintQuantale.Footprint.ofSet {true}) ∧
      ¬ GradedBy (SpaceRules.addAtom (Location := Bool) true atom).Fires 1 :=
  ⟨addAtom_setFootprinted atom, addAtom_not_setFootprinted_empty atom⟩

/-- **Positive, the finite test of independence**: the write of one space against
the reads of another.  **Negative**: against the reads of the same space. -/
theorem disjoint_test_instances :
    @decide (Disjoint (↑({true} : Finset Bool) : Set Bool) {space | space = false})
        (decidableDisjointCoeLeft _ _) = true ∧
      @decide (Disjoint (↑({true} : Finset Bool) : Set Bool) {space | space = true})
        (decidableDisjointCoeLeft _ _) = false := by
  decide

/-- Two spaces, a `7` added to the first. -/
def afterAdd : Bool → Multiset ℕ := Pi.single true {7}

theorem afterAdd_preserves :
    PreservesOutside ({true} : Finset Bool) (0 : Bool → Multiset ℕ) afterAdd := by
  intro location outside
  have different : location ≠ true := by simpa using outside
  simp [afterAdd, different]

/-- **Positive, the finite test of validation**: after the addition the reads of
the other space are kept.  **Negative**: the reads of the space written are not. -/
theorem validation_test_instances :
    @decide (Set.EqOn (0 : Bool → Multiset ℕ) afterAdd {space | space = false})
        (decidableEqOnOfPreservesOutside afterAdd_preserves) = true ∧
      @decide (Set.EqOn (0 : Bool → Multiset ℕ) afterAdd {space | space = true})
        (decidableEqOnOfPreservesOutside afterAdd_preserves) = false := by
  decide

end Controls

#print axioms agreesOn_iff_eqOn
#print axioms setFootprinted_coe_iff
#print axioms SetFootprinted.univ
#print axioms SetFootprinted.mono
#print axioms SetFootprinted.disjoint_commute
#print axioms setIndependentEffects_coe_iff
#print axioms setEffectFootprinted_coe_iff
#print axioms SetEffectFootprinted.setFootprinted
#print axioms SetEffectFootprinted.independent_commute
#print axioms SetEffectFootprinted.comp
#print axioms SetEffectFootprinted.guarded
#print axioms SetEffectFootprinted.eq_none_of_eqOn
#print axioms SetEffectFootprinted.bind_comm
#print axioms gradedBy_one
#print axioms GradedBy.comp
#print axioms GradedBy.of_le
#print axioms GradedBy.commute
#print axioms Controls.gradedBy_instances
#print axioms LocalRule.setEffectFootprinted
#print axioms eqOn_iff_of_preservesOutside
#print axioms disjoint_coe_left_iff
#print axioms emptinessTest_setEffectFootprinted_iff
#print axioms Controls.addAtom_setEffectFootprinted
#print axioms Controls.addAtom_not_setEffectFootprinted_empty
#print axioms Controls.addAtom_not_setFootprinted_empty
#print axioms Controls.addAtom_setFootprinted
#print axioms Controls.disjoint_test_instances
#print axioms Controls.validation_test_instances
#print axioms Controls.independent_apart
#print axioms Controls.not_independent_when_read

end Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.PatternFootprints
