import Mettapedia.GSLT.Core.StepFree
import Mathlib.Algebra.BigOperators.Fin
import Mettapedia.Logic.HostingStyles.Weighted.Composite
import Mettapedia.Logic.HostingStyles.Weighted.FibreSum

/-!
# Closed-sum weight preservation

`weightPreserving` sums one listed fibre. A kernel map is weight-preserving
along a read-back when every equation-closed set of source terms has the same
`closedSum` on the source row as the terms that read back into that set have
on the image row. The listed statement is that equality for rows carried by a
finite list of matches. Preserving maps compose. With unit weights, the fibre
count of a composite is the sum of the leaf counts over the middle fibre.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HostingStyles.Weighted

open Classical
open Mettapedia.GSLT
open Mettapedia.GSLT.Distinction.Probabilistic
open Mettapedia.GSLT.Dynamics.JoinAggregation

/-! ## Closed sums on an explicit finite carrier -/

theorem closedSum_onFinset {α : Type*} {K : Type*} [AddCommMonoid K]
    (s : Finset α) (f : α → K) (hf : ∀ a, f a ≠ 0 → a ∈ s) (C : α → Prop) :
    closedSum (Finsupp.onFinset s f hf) C = ∑ a ∈ s, if C a then f a else 0 := by
  unfold closedSum
  have hsub : (Finsupp.onFinset s f hf).support ⊆ s := Finsupp.support_onFinset_subset
  have zeros : ∀ a ∈ s, a ∉ (Finsupp.onFinset s f hf).support →
      (if C a then Finsupp.onFinset s f hf a else 0) = 0 := by
    intro a _ outside
    rw [Finsupp.onFinset_apply]
    have zero : f a = 0 := by
      by_contra nonzero
      exact outside ((Finsupp.mem_support_onFinset hf).mpr nonzero)
    rw [zero, ite_self]
  refine (Finset.sum_subset hsub zeros).trans ?_
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finsupp.onFinset_apply]

theorem closedSum_zero {α : Type*} {K : Type*} [AddCommMonoid K]
    (C : α → Prop) : closedSum (0 : α →₀ K) C = 0 := by
  unfold closedSum
  simp

theorem closedSum_outcomeKernel {K : Type*} [AddCommMonoid K] (w : K)
    (C : Option Bool → Prop) :
    closedSum (outcomeKernel w) C =
      (if C (some true) then w else 0) + (if C (some false) then w else 0) := by
  unfold outcomeKernel
  rw [closedSum_onFinset]
  have pair : ({some true, some false} : Finset (Option Bool)) =
      insert (some true) {some false} := by
    ext x
    simp
  rw [pair, Finset.sum_insert (by decide), Finset.sum_singleton]
  show (if C (some true) then outcomeCoeff w (some true) else 0) +
      (if C (some false) then outcomeCoeff w (some false) else 0) =
        (if C (some true) then w else 0) + (if C (some false) then w else 0)
  simp [outcomeCoeff]

theorem closedSum_fanKernel {K : Type*} [AddCommMonoid K] (k : ℕ) (w : K)
    (C : Option (Bool × Fin k) → Prop) :
    closedSum (fanKernel k w) C =
      ∑ p : Bool × Fin k, if C (some p) then w else 0 := by
  unfold fanKernel
  rw [closedSum_onFinset, Finset.sum_map]
  refine Finset.sum_congr rfl fun p _ => ?_
  cases p with
  | mk b i =>
    simp [fanCoeff]

/-! ## Kernel maps -/

set_option linter.checkUnivs false in
/-- A map of weighted systems, together with a read-back of target terms to
source terms that respects the equations. -/
structure KernelMap.{uS, uK, uAtom, uLabel, uAtom', uLabel'} (K : Type uK) [Semiring K]
    (sourceSpace targetSpace : GSLT.{uS}) where
  source : WeightedSystem.{uS, uK, uAtom, uLabel} sourceSpace K
  target : WeightedSystem.{uS, uK, uAtom', uLabel'} targetSpace K
  term : sourceSpace.Term → targetSpace.Term
  labelMap : source.Label → target.Label
  readBack : targetSpace.Term → sourceSpace.Term
  readBack_resp : ∀ {left right : targetSpace.Term},
    targetSpace.Equiv left right → sourceSpace.Equiv (readBack left) (readBack right)

/-- **Weight-preserving along a read-back.** For every label, source term, and
set of source terms closed under the equations, the closed sum of the source
row over that set equals the closed sum of the image row over the terms whose
read-back lies in the set. -/
def KernelPreserving {K : Type*} [Semiring K] {sourceSpace targetSpace : GSLT}
    (map : KernelMap K sourceSpace targetSpace) : Prop :=
  ∀ (label : map.source.Label) (s : sourceSpace.Term) (C : sourceSpace.Term → Prop),
    (∀ x y, sourceSpace.Equiv x y → (C x ↔ C y)) →
      closedSum (map.source.kernel label s) C =
        closedSum (map.target.kernel (map.labelMap label) (map.term s))
          (fun t => C (map.readBack t))

/-- The identity on one weighted system. The read-back is the identity. -/
def kernelId {K : Type*} [Semiring K] {space : GSLT} (system : WeightedSystem space K) :
    KernelMap K space space where
  source := system
  target := system
  term := id
  labelMap := id
  readBack := id
  readBack_resp := fun equivalent => equivalent

/-- **Positive.** The identity preserves every closed sum. -/
theorem kernelId_preserving {K : Type*} [Semiring K] {space : GSLT}
    (system : WeightedSystem space K) : KernelPreserving (kernelId system) := by
  intro _ _ _ _
  rfl

/-- Read a copied match back to its outcome. -/
def fanRead {k : ℕ} : (fanSpace k).Term → quiet.Term
  | none => none
  | some (b, _) => some b

/-- Send each outcome to its copy at index zero. -/
def quietEmbed (k : ℕ) (hk : 0 < k) : quiet.Term → (fanSpace k).Term
  | none => none
  | some b => some (b, ⟨0, hk⟩)

/-- Duplication: each outcome weight `1` is placed on both copies. -/
noncomputable def doubledFan : KernelMap ℕ quiet (fanSpace 2) where
  source := outcomeSystem 1
  target := fanSystem 2 1
  term := quietEmbed 2 (by decide)
  labelMap := id
  readBack := fanRead
  readBack_resp := by
    intro _ _ equivalent
    cases equivalent
    rfl

theorem fanRead_some {k : ℕ} (p : Bool × Fin k) : fanRead (some p) = some p.1 := by
  cases p
  rfl

theorem closedSum_doubled_source :
    closedSum ((outcomeSystem (1 : ℕ)).kernel () none) (fun t => t = some true) = 1 := by
  show closedSum (outcomeStep (1 : ℕ) none) (fun t => t = some true) = 1
  rw [outcomeStep, closedSum_outcomeKernel]
  simp

theorem closedSum_doubled_target :
    closedSum ((fanSystem 2 (1 : ℕ)).kernel () none) (fun t => fanRead t = some true) = 2 := by
  show closedSum (fanStep 2 (1 : ℕ) none) (fun t => fanRead t = some true) = 2
  rw [fanStep, closedSum_fanKernel]
  have each : ∀ p : Bool × Fin 2,
      (if fanRead (some p) = some true then (1 : ℕ) else 0) =
        if p.1 = true then 1 else 0 := by
    intro p
    cases p with
    | mk b i =>
      cases b
      · have reduced : fanRead (some (false, i)) = some false := rfl
        have neFan : fanRead (some (false, i)) ≠ some true := by
          intro h
          cases reduced.symm.trans h
        rw [if_neg neFan, if_neg (fun h : (false, i).1 = true => by cases h)]
      · have reduced : fanRead (some (true, i)) = some true := rfl
        rw [if_pos reduced, if_pos (show (true, i).1 = true from rfl)]
  simp_rw [each]
  have univ : (Finset.univ : Finset (Bool × Fin 2)) =
      insert (true, 0) (insert (true, 1) (insert (false, 0) {(false, 1)})) := by
    decide
  rw [univ, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton]
  decide

/-- **Negative.** Two unit copies do not preserve the closed sum of one outcome. -/
theorem doubledFan_not_preserving : ¬ KernelPreserving doubledFan := by
  intro preserves
  have closed : ∀ x y : quiet.Term, quiet.Equiv x y →
      ((fun t => t = some true) x ↔ (fun t => t = some true) y) := by
    intro _ _ equivalent
    cases equivalent
    rfl
  have sourceSide :
      closedSum (doubledFan.source.kernel () none) (fun t => t = some true) = 1 := by
    have fold :
        closedSum (doubledFan.source.kernel () none) (fun t => t = some true) =
          closedSum ((outcomeSystem (1 : ℕ)).kernel () none) (fun t => t = some true) := rfl
    exact fold.trans closedSum_doubled_source
  have targetSide :
      closedSum (doubledFan.target.kernel (doubledFan.labelMap ()) (doubledFan.term none))
        (fun t => doubledFan.readBack t = some true) = 2 := by
    have fold :
        closedSum (doubledFan.target.kernel (doubledFan.labelMap ()) (doubledFan.term none))
          (fun t => doubledFan.readBack t = some true) =
          closedSum ((fanSystem 2 (1 : ℕ)).kernel () none)
            (fun t => fanRead t = some true) := rfl
    exact fold.trans closedSum_doubled_target
  have eq := preserves () none (fun t => t = some true) closed
  exact absurd (sourceSide.symm.trans (eq.trans targetSide)) (by decide)

/-! ## Listed fibres -/

theorem groupSum_eq_map_ite {Copy Event K : Type*} [DecidableEq Event] [AddCommMonoid K]
    (key : Copy → Event) (weight : Copy → K) (copies : List Copy) (event : Event) :
    groupSum key weight copies event =
      (copies.map fun copy => if key copy = event then weight copy else 0).sum := by
  induction copies with
  | nil => simp [groupSum]
  | cons head tail ih =>
    rw [groupSum_cons, ih, List.map_cons, List.sum_cons]

theorem groupSum_list_eq_sum {Copy Event K : Type*} [DecidableEq Event] [AddCommMonoid K]
    (key : Copy → Event) (weight : Copy → K) (copies : List Copy) (event : Event) :
    groupSum key weight copies event =
      ∑ i : Fin copies.length, if key (copies.get i) = event then weight (copies.get i) else 0 := by
  rw [groupSum_eq_map_ite, ← Fin.sum_univ_fun_getElem]
  rfl

noncomputable def optionRow {Event : Type*} [DecidableEq Event] [Fintype Event]
    {K : Type*} [AddCommMonoid K] (weight : Event → K) : Option Event →₀ K :=
  Finsupp.onFinset (Finset.univ.map ⟨some, Option.some_injective _⟩)
    (fun
      | none => 0
      | some event => weight event)
    (by
      intro term nonzero
      cases term with
      | none => exact absurd rfl nonzero
      | some event => exact Finset.mem_map.mpr ⟨event, Finset.mem_univ _, rfl⟩)

noncomputable def indexRow {K : Type*} [AddCommMonoid K] (n : ℕ) (weight : Fin n → K) :
    Option (Fin n) →₀ K :=
  Finsupp.onFinset (Finset.univ.map ⟨some, Option.some_injective _⟩)
    (fun
      | none => 0
      | some index => weight index)
    (by
      intro term nonzero
      cases term with
      | none => exact absurd rfl nonzero
      | some index => exact Finset.mem_map.mpr ⟨index, Finset.mem_univ _, rfl⟩)

theorem closedSum_optionRow {Event : Type*} [DecidableEq Event] [Fintype Event]
    {K : Type*} [AddCommMonoid K] (weight : Event → K) (C : Option Event → Prop) :
    closedSum (optionRow weight) C = ∑ event, if C (some event) then weight event else 0 := by
  unfold optionRow
  rw [closedSum_onFinset, Finset.sum_map]
  refine Finset.sum_congr rfl fun event _ => ?_
  rfl

theorem closedSum_indexRow {K : Type*} [AddCommMonoid K] (n : ℕ) (weight : Fin n → K)
    (C : Option (Fin n) → Prop) :
    closedSum (indexRow n weight) C = ∑ index, if C (some index) then weight index else 0 := by
  unfold indexRow
  rw [closedSum_onFinset, Finset.sum_map]
  refine Finset.sum_congr rfl fun index _ => ?_
  rfl

theorem fibre_sum_closed {Event : Type*} [Fintype Event] [DecidableEq Event]
    {K : Type*} [AddCommMonoid K] {n : ℕ} (key : Fin n → Event) (weight : Fin n → K)
    (sourceWeight : Event → K)
    (keeps : ∀ event, sourceWeight event = ∑ i, if key i = event then weight i else 0)
    (C : Option Event → Prop) :
    (∑ event, if C (some event) then sourceWeight event else 0) =
      ∑ i, if C (some (key i)) then weight i else 0 := by
  have replaced : (fun event => if C (some event) then sourceWeight event else 0) =
      fun event => if C (some event) then (∑ i, if key i = event then weight i else 0) else 0 := by
    funext event
    rw [keeps event]
  rw [replaced]
  have expanded :
      (∑ event, if C (some event) then (∑ i, if key i = event then weight i else 0) else 0) =
        ∑ event, ∑ i, if C (some event) ∧ key i = event then weight i else 0 := by
    refine Finset.sum_congr rfl fun event _ => ?_
    by_cases holds : C (some event)
    · rw [if_pos holds]
      refine Finset.sum_congr rfl fun i _ => ?_
      by_cases keyed : key i = event
      · simp [holds, keyed]
      · simp [keyed]
    · rw [if_neg holds, eq_comm]
      apply Finset.sum_eq_zero
      intro i _
      simp [holds]
  rw [expanded, Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  have collapse : (∑ event, if C (some event) ∧ key i = event then weight i else 0) =
      if C (some (key i)) then weight i else 0 := by
    rw [Finset.sum_eq_single (key i)]
    · by_cases holds : C (some (key i))
      · simp [holds]
      · simp [holds]
    · intro event _ different
      apply if_neg
      intro contra
      exact different contra.2.symm
    · intro outside
      exact absurd (Finset.mem_univ (key i)) outside
  exact collapse

/-- The source term used as the row index. `some` carries an event. -/
def listedTerm {Event Copy : Type} (copies : List Copy) :
    Option Event → Option (Fin copies.length)
  | none => none
  | some _ =>
      if h : copies.length = 0 then none
      else some ⟨0, Nat.pos_of_ne_zero h⟩

noncomputable def listedSource {Event : Type} [DecidableEq Event] [Fintype Event]
    {K : Type*} [CommSemiring K] (sourceWeight : Event → K) :
    WeightedSystem (GSLT.stepFree (Option Event)) K where
  Atom := Unit
  observes := fun _ _ => True
  observes_resp := fun _ _ _ _ => Iff.rfl
  Label := Unit
  kernel := fun _ term =>
    match term with
    | none => optionRow sourceWeight
    | some _ => 0
  kernel_resp := by
    intro _ _ _ same _ _
    cases same
    rfl

noncomputable def listedTarget {Copy : Type} {K : Type*} [CommSemiring K]
    (copies : List Copy) (targetWeight : Copy → K) :
    WeightedSystem (GSLT.stepFree (Option (Fin copies.length))) K where
  Atom := Unit
  observes := fun _ _ => True
  observes_resp := fun _ _ _ _ => Iff.rfl
  Label := Unit
  kernel := fun _ term =>
    match term with
    | none => indexRow copies.length fun index => targetWeight (copies.get index)
    | some _ => 0
  kernel_resp := by
    intro _ _ _ same _ _
    cases same
    rfl

noncomputable def listedReadBack {Event Copy : Type} [DecidableEq Event]
    (key : Copy → Event) (copies : List Copy) :
    Option (Fin copies.length) → Option Event
  | none => none
  | some index => some (key (copies.get index))

/-- Rows given by a list of matches: the source row is the event weights, and
the target row is the match weights, read back by the key. -/
noncomputable def listedMap {Event Copy : Type} [DecidableEq Event] [Fintype Event]
    {K : Type*} [CommSemiring K] (sourceWeight : Event → K) (key : Copy → Event)
    (targetWeight : Copy → K) (copies : List Copy) :
    KernelMap K (GSLT.stepFree (Option Event)) (GSLT.stepFree (Option (Fin copies.length))) where
  source := listedSource sourceWeight
  target := listedTarget copies targetWeight
  term := listedTerm copies
  labelMap := id
  readBack := listedReadBack key copies
  readBack_resp := by
    intro _ _ equivalent
    cases equivalent
    rfl

theorem listed_closed_some {Event Copy : Type} [DecidableEq Event] [Fintype Event]
    {K : Type*} [CommSemiring K] (sourceWeight : Event → K) (key : Copy → Event)
    (targetWeight : Copy → K) (copies : List Copy) (event : Event)
    (C : Option Event → Prop) :
    closedSum ((listedMap sourceWeight key targetWeight copies).source.kernel () (some event)) C =
      0 ∧
    closedSum
      ((listedMap sourceWeight key targetWeight copies).target.kernel ()
        ((listedMap sourceWeight key targetWeight copies).term (some event)))
      (fun t => C ((listedMap sourceWeight key targetWeight copies).readBack t)) = 0 := by
  refine ⟨closedSum_zero _, ?_⟩
  unfold listedMap listedTerm
  dsimp
  split_ifs with empty
  · unfold listedTarget
    dsimp [GSLT.stepFree]
    rw [closedSum_indexRow]
    refine Finset.sum_eq_zero ?_
    intro index _
    exact (Nat.not_lt_zero _ (Nat.lt_of_lt_of_eq index.isLt empty)).elim
  · unfold listedTarget
    dsimp
    exact closedSum_zero _

/-- **Listed fibres.** `weightPreserving` is closed-sum preservation for the
rows carried by a list of matches. -/
theorem listed_weightPreserving_iff {Event Copy : Type} [DecidableEq Event] [Fintype Event]
    {K : Type*} [CommSemiring K] (sourceWeight : Event → K) (key : Copy → Event)
    (targetWeight : Copy → K) (copies : List Copy) :
    weightPreserving sourceWeight key targetWeight copies ↔
      KernelPreserving (listedMap sourceWeight key targetWeight copies) := by
  constructor
  · intro preserves label sourceTerm closedSet _
    cases label
    cases sourceTerm with
    | some event =>
      obtain ⟨sourceZero, targetZero⟩ :=
        listed_closed_some sourceWeight key targetWeight copies event closedSet
      exact sourceZero.trans targetZero.symm
    | none =>
      dsimp [listedMap, listedSource, listedTarget, listedTerm, listedReadBack, GSLT.stepFree]
      have sourceSum := closedSum_optionRow sourceWeight closedSet
      have targetSum :=
        closedSum_indexRow copies.length (fun index => targetWeight (copies.get index))
          (fun t => closedSet (listedReadBack key copies t))
      have joined :=
        fibre_sum_closed (fun index => key (copies.get index))
          (fun index => targetWeight (copies.get index)) sourceWeight
          (fun event => by rw [preserves event, groupSum_list_eq_sum]) closedSet
      exact sourceSum.trans (joined.trans targetSum.symm)
  · intro preserves event
    have closed : ∀ x y : Option Event, x = y →
        ((fun term => term = some event) x ↔ (fun term => term = some event) y) := by
      intro _ _ same
      cases same
      rfl
    have eq := preserves () none (fun term => term = some event) closed
    dsimp [listedMap, listedSource, listedTarget, listedTerm, GSLT.stepFree] at eq
    rw [closedSum_optionRow, closedSum_indexRow] at eq
    have sourceValue :
        (∑ other, @ite K (some other = some event) (Classical.propDecidable _)
            (sourceWeight other) 0) =
          sourceWeight event := by
      rw [Finset.sum_eq_single event]
      · rw [if_pos rfl]
      · intro other _ different
        exact if_neg fun same => different (Option.some_injective _ same)
      · intro outside
        exact absurd (Finset.mem_univ event) outside
    have targetValue :
        (∑ index, @ite K (listedReadBack key copies (some index) = some event)
            (Classical.propDecidable _) (targetWeight (copies.get index)) 0) =
          groupSum key targetWeight copies event := by
      rw [groupSum_list_eq_sum]
      refine Finset.sum_congr rfl fun index _ => ?_
      by_cases h : key (copies.get index) = event
      · have sameRead : listedReadBack key copies (some index) = some event := by
          unfold listedReadBack
          exact congrArg some h
        rw [if_pos sameRead, if_pos h]
      · have differentRead : listedReadBack key copies (some index) ≠ some event := by
          intro sameRead
          unfold listedReadBack at sameRead
          exact h (Option.some_injective _ sameRead)
        rw [if_neg differentRead, if_neg h]
    exact sourceValue.symm.trans (eq.trans targetValue)

/-- **Positive.** One listed match per Boolean event preserves the closed sums. -/
theorem listed_one_preserving (w : ℕ) :
    KernelPreserving (listedMap (fun _ : Bool => w) (fun p : Bool × Fin 1 => p.1)
      (fun _ => w) (bothCopies 1)) :=
  (listed_weightPreserving_iff (fun _ : Bool => w) (fun p : Bool × Fin 1 => p.1)
    (fun _ => w) (bothCopies 1)).mp
    (fun event => by rw [fibre_sum_mul, Nat.cast_one, one_mul])

/-- **Negative.** Two listed unit matches do not preserve a unit source weight. -/
theorem listed_two_not_preserving :
    ¬ KernelPreserving (listedMap (fun _ : Bool => (1 : ℕ)) (fun p : Bool × Fin 2 => p.1)
        (fun _ => (1 : ℕ)) (bothCopies 2)) := by
  intro preserves
  have kept :=
    (listed_weightPreserving_iff (fun _ : Bool => (1 : ℕ)) (fun p : Bool × Fin 2 => p.1)
      (fun _ => (1 : ℕ)) (bothCopies 2)).mpr preserves true
  rw [fibre_sum_mul] at kept
  exact absurd kept (by decide)

/-! ## Composition -/

set_option linter.checkUnivs false in
/-- Composition along one middle system. `same` says the first map lands on the
system the second map reads. Labels of a weighted system are a field of that
system, so the composite label map casts along `same`. The composite read-back
reads the target back through the middle. -/
def KernelMap.comp.{uS, uK, uAs, uLs, uAm, uLm, uAt, uLt}
    {K : Type uK} [Semiring K] {sourceSpace middleSpace targetSpace : GSLT.{uS}}
    (second : KernelMap.{uS, uK, uAm, uLm, uAt, uLt} K middleSpace targetSpace)
    (first : KernelMap.{uS, uK, uAs, uLs, uAm, uLm} K sourceSpace middleSpace)
    (same : first.target = second.source) :
    KernelMap.{uS, uK, uAs, uLs, uAt, uLt} K sourceSpace targetSpace where
  source := first.source
  target := second.target
  term := second.term ∘ first.term
  labelMap := fun label =>
    second.labelMap
      (cast (congrArg (fun system : WeightedSystem middleSpace K => system.Label) same)
        (first.labelMap label))
  readBack := first.readBack ∘ second.readBack
  readBack_resp := fun equivalent => first.readBack_resp (second.readBack_resp equivalent)

/-- Left identity does not change closed-sum preservation. -/
theorem KernelPreserving.comp_id_left {K : Type*} [Semiring K] {sourceSpace targetSpace : GSLT}
    (map : KernelMap K sourceSpace targetSpace) :
    KernelPreserving ((kernelId map.target).comp map rfl) ↔ KernelPreserving map := by
  constructor
  · intro preserves label sourceTerm closedSet closed
    have eq := preserves label sourceTerm closedSet closed
    dsimp [KernelMap.comp, kernelId] at eq
    exact eq
  · intro preserves label sourceTerm closedSet closed
    dsimp [KernelMap.comp, kernelId]
    exact preserves label sourceTerm closedSet closed

/-- **Preserving maps compose**, for arbitrary weighted systems that share the
middle system. -/
theorem KernelPreserving.comp.{uS, uK, uAs, uLs, uAm, uLm, uAt, uLt}
    {K : Type uK} [Semiring K] {sourceSpace middleSpace targetSpace : GSLT.{uS}}
    {second : KernelMap.{uS, uK, uAm, uLm, uAt, uLt} K middleSpace targetSpace}
    {first : KernelMap.{uS, uK, uAs, uLs, uAm, uLm} K sourceSpace middleSpace}
    (same : first.target = second.source)
    (secondPreserves : KernelPreserving second) (firstPreserves : KernelPreserving first) :
    KernelPreserving (second.comp first same) := by
  rcases first with ⟨source1, target1, term1, labelMap1, readBack1, resp1⟩
  rcases second with ⟨source2, target2, term2, labelMap2, readBack2, resp2⟩
  cases same
  intro label sourceTerm closedSet closed
  have middleClosed : ∀ x y, middleSpace.Equiv x y →
      ((fun middle => closedSet (readBack1 middle)) x ↔
        (fun middle => closedSet (readBack1 middle)) y) := by
    intro _ _ equivalent
    exact closed _ _ (resp1 equivalent)
  dsimp [KernelMap.comp]
  rw [firstPreserves label sourceTerm closedSet closed]
  exact secondPreserves (labelMap1 label) (term1 sourceTerm)
    (fun middle => closedSet (readBack1 middle)) middleClosed

/-- **Positive.** Identity maps compose to a preserving map. -/
theorem identity_comp_identity_preserving (w : ℕ) :
    KernelPreserving
      ((kernelId (outcomeSystem w)).comp (kernelId (outcomeSystem w)) rfl) :=
  KernelPreserving.comp rfl (kernelId_preserving _) (kernelId_preserving _)

/-- **Negative.** A preserving identity after the doubled fan is still not preserving. -/
theorem identity_comp_doubled_not_preserving :
    ¬ KernelPreserving ((kernelId (fanSystem 2 (1 : ℕ))).comp doubledFan rfl) := by
  intro preserves
  exact doubledFan_not_preserving ((KernelPreserving.comp_id_left doubledFan).mp preserves)

/-! ## Unit weights: leaf counts add along the middle fibre -/

inductive UnevenMid where
  | left
  | right
  deriving DecidableEq

inductive UnevenLeaf where
  | only
  | rightA
  | rightB
  deriving DecidableEq

def unevenParent : UnevenLeaf → UnevenMid
  | .only => .left
  | .rightA => .right
  | .rightB => .right

def unevenLeaves : List UnevenLeaf := [.only, .rightA, .rightB]

def unevenMiddles : List UnevenMid := [.left, .right]

/-- How many leaves sit over one middle match. -/
def unevenLeafCount (middle : UnevenMid) : ℕ :=
  unevenLeaves.countP fun leaf => unevenParent leaf = middle

theorem unevenLeafCount_left : unevenLeafCount .left = 1 := by
  unfold unevenLeafCount unevenLeaves
  rw [List.countP_cons, List.countP_cons, List.countP_cons, List.countP_nil]
  simp [unevenParent]

theorem unevenLeafCount_right : unevenLeafCount .right = 2 := by
  unfold unevenLeafCount unevenLeaves
  rw [List.countP_cons, List.countP_cons, List.countP_cons, List.countP_nil]
  simp [unevenParent]

theorem uneven_leaf_total :
    groupSum (fun _ : UnevenLeaf => ()) (fun _ => (1 : ℕ)) unevenLeaves () = 3 := by
  unfold unevenLeaves
  rw [groupSum_cons, if_pos rfl, groupSum_cons, if_pos rfl, groupSum_cons, if_pos rfl, groupSum_nil]
  decide

theorem uneven_middle_total :
    groupSum (fun _ : UnevenMid => ()) (fun middle => unevenLeafCount middle) unevenMiddles () =
      3 := by
  unfold unevenMiddles
  rw [groupSum_cons, if_pos rfl, groupSum_cons, if_pos rfl, groupSum_nil,
    unevenLeafCount_left, unevenLeafCount_right]
  decide

/-- **Unit-weight composite count.** The fibre count of the leaves is the sum of
the leaf counts of the middle matches. That sum is not the length of a uniform
`2 × 3` grid. -/
theorem uneven_composite_fibre_count :
    groupSum (fun _ : UnevenLeaf => ()) (fun _ => (1 : ℕ)) unevenLeaves () =
      groupSum (fun _ : UnevenMid => ()) (fun middle => unevenLeafCount middle) unevenMiddles () ∧
      unevenLeafCount .left + unevenLeafCount .right =
        groupSum (fun _ : UnevenLeaf => ()) (fun _ => (1 : ℕ)) unevenLeaves () ∧
      (grid 2 3).length = 2 * 3 ∧
      groupSum (fun _ : UnevenLeaf => ()) (fun _ => (1 : ℕ)) unevenLeaves () ≠
        (grid 2 3).length := by
  refine ⟨?_, ?_, grid_length 2 3, ?_⟩
  · rw [uneven_leaf_total, uneven_middle_total]
  · rw [unevenLeafCount_left, unevenLeafCount_right, uneven_leaf_total]
  · rw [uneven_leaf_total, grid_length]
    decide

end Mettapedia.Logic.HostingStyles.Weighted
