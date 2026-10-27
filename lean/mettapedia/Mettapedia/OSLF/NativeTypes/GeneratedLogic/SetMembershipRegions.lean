import Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetMembershipDerivations

/-!
# Fixed points of modal native types on the finite region of a hereditarily finite set

A hereditary term's region is the list of the term and, recursively, its members (`regionOf`); the sets they denote
form a finite set closed under membership (`zfRegion`). Modal native types look only forward, so on a set closed
under membership their truth depends on the fixed-point environment only within that set (`sat_local`). There a
least fixed point is reached by finitely many stages from below, and a greatest one by finitely many stages from
above (`lfpStage`, `gfpStage`), and the stages are stable from the region's size on (`lfpStage_stable`,
`gfpStage_stable`): at a set of the region, the least fixed point holds exactly at that stage (`sat_mu_iff`), and so
does the greatest (`sat_nu_iff`).

**Deciding on a region.** A region is a finite set of hereditarily finite sets closed under membership, with
hereditary terms naming them (`Region`). On its terms, a modal native type is decided by a program (`decideOn`):
steps go through members, named terms are compared by presentation (`sameSet`), one-element sets by their members
(`isSingleton`), counting chooses a member and counts the members presenting other sets (`countDecide`), and a fixed
point takes as many stages as there are terms (`stagesOn`). The decision is exact (`decideOn_iff`).

**Splits.** A set splits into two sets whose union it is, so its parts are its subsets. The regional fragment
(`Formula.regional`) adds splits and their duals to the modal fragment. On a set closed under membership and under
parts (`PartsClosed`), locality and the bounded stages hold for it (`sat_local_regional`, `sat_mu_iff_regional`,
`sat_nu_iff_regional`). The decision goes through the coverings of a term's members, each member in the first part,
the second, or both (`coverings`, `covering_split`, `split_covering`), and is exact on regions closed under parts
(`decideOn_iff_regional`).
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetReadings

open Mettapedia.OSLF.MeTTaIL.Syntax

/-! ## The region of a term -/

mutual
/-- **The region of a term**: the term, and the regions of its members. -/
def regionOf : Pattern → List Pattern
  | .collection kind values rest => .collection kind values rest :: regionOfList values
  | .bvar index => [.bvar index]
  | .fvar name => [.fvar name]
  | .apply label arguments => [.apply label arguments]
  | .lambda name body => [.lambda name body]
  | .multiLambda arity names body => [.multiLambda arity names body]
  | .subst body replacement => [.subst body replacement]

/-- The regions of the terms of a list. -/
def regionOfList : List Pattern → List Pattern
  | [] => []
  | value :: values => regionOf value ++ regionOfList values
end

theorem self_mem_regionOf : ∀ term : Pattern, term ∈ regionOf term
  | .collection _ _ _ | .bvar _ | .fvar _ | .apply _ _ | .lambda _ _ | .multiLambda _ _ _ | .subst _ _ =>
    List.mem_cons_self

theorem regionOf_sub_regionOfList {value : Pattern} {values : List Pattern} (member : value ∈ values) :
    ∀ other ∈ regionOf value, other ∈ regionOfList values := by
  induction values with
  | nil => exact absurd member List.not_mem_nil
  | cons head tail ih =>
    intro other inside
    rw [regionOfList, List.mem_append]
    rcases List.mem_cons.mp member with rfl | member
    · exact Or.inl inside
    · exact Or.inr (ih member other inside)

mutual
/-- **The region is closed under members.** -/
theorem members_mem_regionOf : ∀ (term : Pattern) {inner : Pattern}, inner ∈ regionOf term →
    ∀ value ∈ membersOf inner, value ∈ regionOf term
  | .collection kind values rest, inner, inside, value, member => by
    rcases List.mem_cons.mp inside with rfl | inside
    · exact List.mem_cons_of_mem _ (regionOf_sub_regionOfList member value (self_mem_regionOf value))
    · exact List.mem_cons_of_mem _ (members_mem_regionOfList values inside value member)
  | .bvar _, inner, inside, value, member | .fvar _, inner, inside, value, member
  | .apply _ _, inner, inside, value, member | .lambda _ _, inner, inside, value, member
  | .multiLambda _ _ _, inner, inside, value, member | .subst _ _, inner, inside, value, member => by
    rw [List.mem_singleton.mp inside] at member
    exact absurd member List.not_mem_nil

theorem members_mem_regionOfList : ∀ (values : List Pattern) {inner : Pattern}, inner ∈ regionOfList values →
    ∀ value ∈ membersOf inner, value ∈ regionOfList values
  | [], _, inside, _, _ => absurd inside List.not_mem_nil
  | head :: tail, inner, inside, value, member => by
    rw [regionOfList, List.mem_append] at inside ⊢
    rcases inside with inside | inside
    · exact Or.inl (members_mem_regionOf head inside value member)
    · exact Or.inr (members_mem_regionOfList tail inside value member)
end

mutual
/-- **The region of a hereditary term is hereditary.** -/
theorem hf_of_mem_regionOf : ∀ {term : Pattern}, IsHF term → ∀ {inner : Pattern}, inner ∈ regionOf term → IsHF inner
  | .collection kind values rest, holds, inner, inside => by
    rcases List.mem_cons.mp inside with rfl | inside
    · exact holds
    · obtain ⟨-, -, members⟩ := hf_collection holds
      exact hf_of_mem_regionOfList members inside
  | .bvar _, holds, _, _ => absurd holds hf_not_bvar
  | .fvar _, holds, _, _ => by
    obtain ⟨values, same, -⟩ := hf_set holds
    simp [set] at same
  | .apply _ _, holds, _, _ => absurd holds hf_not_apply
  | .lambda _ _, holds, _, _ => absurd holds hf_not_lambda
  | .multiLambda _ _ _, holds, _, _ => absurd holds hf_not_multiLambda
  | .subst _ _, holds, _, _ => by
    obtain ⟨values, same, -⟩ := hf_set holds
    simp [set] at same

theorem hf_of_mem_regionOfList : ∀ {values : List Pattern}, (∀ value ∈ values, IsHF value) →
    ∀ {inner : Pattern}, inner ∈ regionOfList values → IsHF inner
  | [], _, _, inside => absurd inside List.not_mem_nil
  | head :: tail, holds, inner, inside => by
    rw [regionOfList, List.mem_append] at inside
    rcases inside with inside | inside
    · exact hf_of_mem_regionOf (holds head List.mem_cons_self) inside
    · exact hf_of_mem_regionOfList (fun value member => holds value (List.mem_cons_of_mem _ member)) inside
end

/-- **The sets of the region.** -/
def zfRegion (term : Pattern) : Set ZFSet.{0} := {z | ∃ inner ∈ regionOf term, zfOf inner = z}

theorem zfRegion_finite (term : Pattern) : (zfRegion term).Finite := by
  have same : zfRegion term = {z | z ∈ (regionOf term).map zfOf} := by
    ext z
    simp [zfRegion, List.mem_map]
  rw [same]
  exact List.finite_toSet _

theorem self_mem_zfRegion (term : Pattern) : zfOf term ∈ zfRegion term := ⟨term, self_mem_regionOf term, rfl⟩

/-- **The sets of the region of a hereditary term are closed under membership.** -/
theorem zfRegion_closed {term : Pattern} (holds : IsHF term) : ∀ y ∈ zfRegion term, ∀ z ∈ y, z ∈ zfRegion term := by
  rintro y ⟨inner, inside, rfl⟩ z member
  have innerHolds := hf_of_mem_regionOf holds inside
  rw [hf_eq_set innerHolds, zfOf_set] at member
  obtain ⟨value, valueMember, rfl⟩ := mem_zfOfList.mp member
  exact ⟨value, members_mem_regionOf term inside value valueMember, rfl⟩

/-! ## Locality -/

/-- Two environments that agree on a set. -/
def EnvAgreeOn {n : ℕ} (region : Set ZFSet.{0}) (first second : Env ZFSet.{0} n) : Prop :=
  ∀ index, ∀ z ∈ region, z ∈ first index ↔ z ∈ second index

theorem EnvAgreeOn.extend {n : ℕ} {region : Set ZFSet.{0}} {first second : Env ZFSet.{0} n}
    (agree : EnvAgreeOn region first second) {small large : Set ZFSet.{0}}
    (same : ∀ z ∈ region, z ∈ small ↔ z ∈ large) : EnvAgreeOn region (first.extend small) (second.extend large) := by
  intro index z inside
  refine Fin.cases ?_ (fun index => ?_) index
  · exact same z inside
  · exact agree index z inside

/-- **Closed under parts**: every subset of a set of the collection is in it. -/
def PartsClosed (region : Set ZFSet.{0}) : Prop := ∀ y ∈ region, ∀ part : ZFSet.{0}, part ⊆ y → part ∈ region

theorem part_left {whole first second : ZFSet.{0}} (union : whole = first ∪ second) : first ⊆ whole := by
  rw [ZFSet.subset_def, union]
  exact fun _ member => ZFSet.mem_union.mpr (Or.inl member)

theorem part_right {whole first second : ZFSet.{0}} (union : whole = first ∪ second) : second ⊆ whole := by
  rw [ZFSet.subset_def, union]
  exact fun _ member => ZFSet.mem_union.mpr (Or.inr member)

/-- **Locality**: on a set closed under membership, and under parts when the type has splits, a native type of the
regional fragment depends on the environment only within the set. -/
theorem sat_local_regional {region : Set ZFSet.{0}} (closed : ∀ y ∈ region, ∀ z ∈ y, z ∈ region) :
    ∀ {n : ℕ} (formula : Formula n), formula.regional = true → formula.modal = true ∨ PartsClosed region →
      ∀ {first second : Env ZFSet.{0} n},
      EnvAgreeOn region first second → ∀ y ∈ region, (extensional.sat first formula y ↔ extensional.sat second formula y)
  | _, .top, _, _, _, _, _, _, _ => Iff.rfl
  | _, .bot, _, _, _, _, _, _, _ => Iff.rfl
  | _, .and left right, modal, parts, _, _, agree, y, inside => by
    simp only [Formula.regional, Bool.and_eq_true] at modal
    exact and_congr (sat_local_regional closed left modal.1 (parts.imp_left fun both => ((Bool.and_eq_true _ _).mp both).1) agree y inside) (sat_local_regional closed right modal.2 (parts.imp_left fun both => ((Bool.and_eq_true _ _).mp both).2) agree y inside)
  | _, .or left right, modal, parts, _, _, agree, y, inside => by
    simp only [Formula.regional, Bool.and_eq_true] at modal
    exact or_congr (sat_local_regional closed left modal.1 (parts.imp_left fun both => ((Bool.and_eq_true _ _).mp both).1) agree y inside) (sat_local_regional closed right modal.2 (parts.imp_left fun both => ((Bool.and_eq_true _ _).mp both).2) agree y inside)
  | _, .var index, _, _, _, _, agree, y, inside => agree index y inside
  | _, .mu inner, modal, parts, first, second, agree, y, inside => by
    simp only [Formula.regional] at modal
    have direction : ∀ {first second : Env ZFSet.{0} _}, EnvAgreeOn region first second →
        extensional.sat first (.mu inner) y → extensional.sat second (.mu inner) y := by
      intro first second agree holds closedSet isClosed
      let restricted : Set ZFSet.{0} := {z | z ∈ region → z ∈ closedSet}
      have restrictedClosed : ∀ other, extensional.sat (first.extend restricted) inner other → other ∈ restricted := by
        intro other holdsOther otherInside
        exact isClosed other ((sat_local_regional closed inner modal parts (agree.extend (small := restricted) (large := closedSet)
          fun z zInside => ⟨fun found => found zInside, fun found _ => found⟩) other otherInside).mp holdsOther)
      exact holds restricted restrictedClosed inside
    exact ⟨direction agree, direction fun index z zInside => (agree index z zInside).symm⟩
  | _, .nu inner, modal, parts, first, second, agree, y, inside => by
    simp only [Formula.regional] at modal
    have direction : ∀ {first second : Env ZFSet.{0} _}, EnvAgreeOn region first second →
        extensional.sat first (.nu inner) y → extensional.sat second (.nu inner) y := by
      rintro first second agree ⟨invariant, member, preserved⟩
      refine ⟨{z | z ∈ invariant ∧ z ∈ region}, ⟨member, inside⟩, fun other ⟨otherMember, otherInside⟩ => ?_⟩
      exact (sat_local_regional closed inner modal parts (agree.extend (small := invariant) (large := {z | z ∈ invariant ∧ z ∈ region})
        fun z zInside => ⟨fun found => ⟨found, zInside⟩, fun found => found.1⟩) other otherInside).mp
        (preserved other otherMember)
    exact ⟨direction agree, direction fun index z zInside => (agree index z zInside).symm⟩
  | _, .possibly _ inner, modal, parts, _, _, agree, y, inside => by
    simp only [Formula.regional, Bool.and_eq_true] at modal
    replace modal := modal.2
    replace parts := parts.imp_left fun inside => by
      simp only [Formula.modal, Bool.and_eq_true] at inside
      exact inside.2
    exact exists_congr fun next => and_congr_right fun step =>
      sat_local_regional closed inner modal parts agree next (closed y inside next step.2)
  | _, .necessarily _ inner, modal, parts, _, _, agree, y, inside => by
    simp only [Formula.regional, Bool.and_eq_true] at modal
    replace modal := modal.2
    replace parts := parts.imp_left fun inside => by
      simp only [Formula.modal, Bool.and_eq_true] at inside
      exact inside.2
    exact forall_congr' fun next => imp_congr_right fun step =>
      sat_local_regional closed inner modal parts agree next (closed y inside next step.2)
  | _, .atLeast _ .forward _ inner, modal, parts, _, _, agree, y, inside => by
    simp only [Formula.regional, Bool.and_eq_true] at modal
    replace modal := modal.2
    replace parts := parts.imp_left fun inside => by
      simp only [Formula.modal, Bool.and_eq_true] at inside
      exact inside.2
    exact ⟨fun many => many.mono fun other found => ⟨found.1,
        (sat_local_regional closed inner modal parts agree other (closed y inside other found.1.2)).mp found.2⟩,
      fun many => many.mono fun other found => ⟨found.1,
        (sat_local_regional closed inner modal parts agree other (closed y inside other found.1.2)).mpr found.2⟩⟩
  | _, .allButFewer _ .forward _ inner, modal, parts, _, _, agree, y, inside => by
    simp only [Formula.regional, Bool.and_eq_true] at modal
    replace modal := modal.2
    replace parts := parts.imp_left fun inside => by
      simp only [Formula.modal, Bool.and_eq_true] at inside
      exact inside.2
    exact not_congr ⟨fun many => many.mono fun other found => ⟨found.1, fun holds =>
        found.2 ((sat_local_regional closed inner modal parts agree other (closed y inside other found.1.2)).mpr holds)⟩,
      fun many => many.mono fun other found => ⟨found.1, fun holds =>
        found.2 ((sat_local_regional closed inner modal parts agree other (closed y inside other found.1.2)).mp holds)⟩⟩
  | _, .single _ inner, modal, parts, _, _, agree, y, inside => by
    simp only [Formula.regional] at modal
    exact exists_congr fun element => and_congr_right fun found =>
      sat_local_regional closed inner modal parts agree element (closed y inside element (by rw [found.2]; exact ZFSet.mem_singleton.mpr rfl))
  | _, .everySingle _ inner, modal, parts, _, _, agree, y, inside => by
    simp only [Formula.regional] at modal
    exact forall_congr' fun element => imp_congr_right fun found =>
      sat_local_regional closed inner modal parts agree element (closed y inside element (by rw [found.2]; exact ZFSet.mem_singleton.mpr rfl))
  | _, .split _ left right, modal, parts, _, _, agree, y, inside => by
    simp only [Formula.regional, Bool.and_eq_true] at modal
    have closedParts : PartsClosed region := parts.resolve_left Bool.false_ne_true
    exact exists_congr fun first => exists_congr fun second => and_congr_right fun isSplit =>
      and_congr (sat_local_regional closed left modal.1 (Or.inr closedParts) agree first
          (closedParts y inside first (part_left isSplit.2)))
        (sat_local_regional closed right modal.2 (Or.inr closedParts) agree second
          (closedParts y inside second (part_right isSplit.2)))
  | _, .everySplit _ left right, modal, parts, _, _, agree, y, inside => by
    simp only [Formula.regional, Bool.and_eq_true] at modal
    have closedParts : PartsClosed region := parts.resolve_left Bool.false_ne_true
    exact forall_congr' fun first => forall_congr' fun second => imp_congr_right fun isSplit =>
      or_congr (sat_local_regional closed left modal.1 (Or.inr closedParts) agree first
          (closedParts y inside first (part_left isSplit.2)))
        (sat_local_regional closed right modal.2 (Or.inr closedParts) agree second
          (closedParts y inside second (part_right isSplit.2)))
  | _, .is _, _, _, _, _, _, _, _ | _, .isNot _, _, _, _, _, _, _, _ | _, .empty _, _, _, _, _, _, _, _
  | _, .nonEmpty _, _, _, _, _, _, _, _ | _, .typed _, _, _, _, _, _, _, _ | _, .untyped _, _, _, _, _, _, _, _ => Iff.rfl
  | _, .sometimeBefore _ _, modal, _, _, _, _, _, _ | _, .alwaysBefore _ _, modal, _, _, _, _, _, _
  | _, .atLeast _ .backward _ _, modal, _, _, _, _, _, _ | _, .allButFewer _ .backward _ _, modal, _, _, _, _, _, _
  | _, .built _ _, modal, _, _, _, _, _, _ | _, .everyBuilt _ _, modal, _, _, _, _, _, _
  | _, .body _, modal, _, _, _, _, _, _ | _, .everyBody _, modal, _, _, _, _, _, _
  | _, .multiBody _ _, modal, _, _, _, _, _, _ | _, .everyMultiBody _ _, modal, _, _, _, _, _, _
  | _, .bound _, modal, _, _, _, _, _, _ | _, .notBound _, modal, _, _, _, _, _, _
  | _, .mapsAll _ _, modal, _, _, _, _, _, _ | _, .mapsSome _ _, modal, _, _, _, _, _, _
  | _, .someOf _ _, modal, _, _, _, _, _, _ | _, .everyOf _ _, modal, _, _, _, _, _, _ => absurd modal Bool.false_ne_true

theorem sat_local {region : Set ZFSet.{0}} (closed : ∀ y ∈ region, ∀ z ∈ y, z ∈ region) {n : ℕ} (formula : Formula n)
    (modal : formula.modal = true) {first second : Env ZFSet.{0} n} (agree : EnvAgreeOn region first second)
    (y : ZFSet.{0}) (inside : y ∈ region) : extensional.sat first formula y ↔ extensional.sat second formula y :=
  sat_local_regional closed formula (Formula.regional_of_modal formula modal) (Or.inl modal) agree y inside

/-! ## Stages -/

section Stages

variable {n : ℕ} (sets : Env ZFSet.{0} n) (inner : Formula (n + 1)) (region : Set ZFSet.{0})

/-- **The stages of a least fixed point from below**, within the region. -/
def lfpStage : ℕ → Set ZFSet.{0}
  | 0 => ∅
  | k + 1 => {z | z ∈ region ∧ extensional.sat (sets.extend (lfpStage k)) inner z}

/-- **The stages of a greatest fixed point from above**, within the region. -/
def gfpStage : ℕ → Set ZFSet.{0}
  | 0 => region
  | k + 1 => {z | z ∈ region ∧ extensional.sat (sets.extend (gfpStage k)) inner z}

theorem lfpStage_sub_region : ∀ k, lfpStage sets inner region k ⊆ region
  | 0 => fun _ none => none.elim
  | _ + 1 => fun _ found => found.1

theorem gfpStage_sub_region : ∀ k, gfpStage sets inner region k ⊆ region
  | 0 => fun _ inside => inside
  | _ + 1 => fun _ found => found.1

theorem lfpStage_mono : ∀ k, lfpStage sets inner region k ⊆ lfpStage sets inner region (k + 1)
  | 0 => fun _ none => none.elim
  | k + 1 => fun z found => ⟨found.1, extensional.sat_mono inner (fun index => by
      refine Fin.cases (lfpStage_mono k) (fun _ => le_rfl) index) z found.2⟩

theorem gfpStage_anti : ∀ k, gfpStage sets inner region (k + 1) ⊆ gfpStage sets inner region k
  | 0 => fun _ found => found.1
  | k + 1 => fun z found => ⟨found.1, extensional.sat_mono inner (fun index => by
      refine Fin.cases (gfpStage_anti k) (fun _ => le_rfl) index) z found.2⟩

/-- Once a stage repeats, every later stage repeats, when each stage is determined by the one before. -/
theorem stable_from {stages : ℕ → Set ZFSet.{0}} (next : ∀ k, stages (k + 1) = stages k → stages (k + 2) = stages (k + 1))
    {k : ℕ} (same : stages (k + 1) = stages k) : ∀ d, stages (k + d + 1) = stages (k + d)
  | 0 => same
  | d + 1 => next (k + d) (stable_from next same d)

theorem stable_at {stages : ℕ → Set ZFSet.{0}} (next : ∀ k, stages (k + 1) = stages k → stages (k + 2) = stages (k + 1))
    {k N : ℕ} (le : k ≤ N) (same : stages (k + 1) = stages k) : stages (N + 1) = stages N := by
  have later := stable_from next same (N - k)
  rwa [Nat.add_sub_cancel' le] at later

/-- **An increasing sequence of subsets of a finite set, each stage determined by the one before, is stable from the
set's size on.** -/
theorem stable_of_mono {stages : ℕ → Set ZFSet.{0}} (finite : region.Finite)
    (within : ∀ k, stages k ⊆ region) (mono : ∀ k, stages k ⊆ stages (k + 1))
    (next : ∀ k, stages (k + 1) = stages k → stages (k + 2) = stages (k + 1)) {N : ℕ} (bound : region.ncard ≤ N) :
    stages (N + 1) = stages N := by
  by_contra moving
  have count : ∀ k ≤ N + 1, k ≤ (stages k).ncard := by
    intro k
    induction k with
    | zero => exact fun _ => Nat.zero_le _
    | succ k ih =>
      intro le
      have strict : stages k ⊂ stages (k + 1) :=
        LE.le.ssubset_of_ne (mono k) fun same => moving (stable_at next (by omega) same.symm)
      exact Nat.succ_le_of_lt ((ih (by omega)).trans_lt (Set.ncard_lt_ncard strict (finite.subset (within _))))
  have large := count (N + 1) le_rfl
  have small := Set.ncard_le_ncard (within (N + 1)) finite
  omega

/-- **A decreasing sequence of subsets of a finite set, each stage determined by the one before, is stable from the
set's size on.** -/
theorem stable_of_anti {stages : ℕ → Set ZFSet.{0}} (finite : region.Finite)
    (within : ∀ k, stages k ⊆ region) (anti : ∀ k, stages (k + 1) ⊆ stages k)
    (next : ∀ k, stages (k + 1) = stages k → stages (k + 2) = stages (k + 1)) {N : ℕ} (bound : region.ncard ≤ N) :
    stages (N + 1) = stages N := by
  by_contra moving
  have count : ∀ k ≤ N + 1, (stages k).ncard + k ≤ region.ncard := by
    intro k
    induction k with
    | zero => exact fun _ => Set.ncard_le_ncard (within 0) finite
    | succ k ih =>
      intro le
      have strict : stages (k + 1) ⊂ stages k :=
        LE.le.ssubset_of_ne (anti k) fun same => moving (stable_at next (by omega) same)
      have shrink := Set.ncard_lt_ncard strict (finite.subset (within _))
      have := ih (by omega)
      omega
  have := count (N + 1) le_rfl
  omega

variable {N : ℕ} (finite : region.Finite) (bound : region.ncard ≤ N)

include finite bound in
/-- **The least fixed point's stages are stable from the region's size on.** -/
theorem lfpStage_stable : lfpStage sets inner region (N + 1) = lfpStage sets inner region N :=
  stable_of_mono region finite (lfpStage_sub_region sets inner region) (lfpStage_mono sets inner region)
    (fun k same => by
      change {z | z ∈ region ∧ extensional.sat (sets.extend (lfpStage sets inner region (k + 1))) inner z} =
        {z | z ∈ region ∧ extensional.sat (sets.extend (lfpStage sets inner region k)) inner z}
      rw [same]) bound

include finite bound in
/-- **The greatest fixed point's stages are stable from the region's size on.** -/
theorem gfpStage_stable : gfpStage sets inner region (N + 1) = gfpStage sets inner region N :=
  stable_of_anti region finite (gfpStage_sub_region sets inner region) (gfpStage_anti sets inner region)
    (fun k same => by
      change {z | z ∈ region ∧ extensional.sat (sets.extend (gfpStage sets inner region (k + 1))) inner z} =
        {z | z ∈ region ∧ extensional.sat (sets.extend (gfpStage sets inner region k)) inner z}
      rw [same]) bound

include finite bound in
/-- **At the least fixed point's stable stage, a set of the region is in it exactly when its body holds there.** -/
theorem lfpStage_fixed {z : ZFSet.{0}} (inside : z ∈ region) :
    z ∈ lfpStage sets inner region N ↔ extensional.sat (sets.extend (lfpStage sets inner region N)) inner z := by
  rw [← lfpStage_stable sets inner region finite bound]
  exact ⟨fun found => (lfpStage_stable sets inner region finite bound) ▸ found.2,
    fun holds => ⟨inside, (lfpStage_stable sets inner region finite bound).symm ▸ holds⟩⟩

include finite bound in
/-- **At the greatest fixed point's stable stage, a set of the region is in it exactly when its body holds there.** -/
theorem gfpStage_fixed {z : ZFSet.{0}} (inside : z ∈ region) :
    z ∈ gfpStage sets inner region N ↔ extensional.sat (sets.extend (gfpStage sets inner region N)) inner z := by
  rw [← gfpStage_stable sets inner region finite bound]
  exact ⟨fun found => (gfpStage_stable sets inner region finite bound) ▸ found.2,
    fun holds => ⟨inside, (gfpStage_stable sets inner region finite bound).symm ▸ holds⟩⟩

end Stages

section Fixpoints

variable {n : ℕ} (sets : Env ZFSet.{0} n) {inner : Formula (n + 1)} (regional : inner.regional = true)
  {region : Set ZFSet.{0}} (parts : inner.modal = true ∨ PartsClosed region) (finite : region.Finite)
  (closed : ∀ y ∈ region, ∀ z ∈ y, z ∈ region)
  {N : ℕ} (bound : region.ncard ≤ N)

include regional parts closed finite bound in
/-- **A least fixed point holds at a set of the region exactly at its stable stage.** -/
theorem sat_mu_iff_regional {y : ZFSet.{0}} (inside : y ∈ region) :
    extensional.sat sets (.mu inner) y ↔ y ∈ lfpStage sets inner region N := by
  constructor
  · intro holds
    let stable := lfpStage sets inner region N
    have isClosed : ∀ other, extensional.sat (sets.extend {z | z ∈ region → z ∈ stable}) inner other →
        other ∈ {z | z ∈ region → z ∈ stable} := by
      intro other holdsOther otherInside
      refine (lfpStage_fixed sets inner region finite bound otherInside).mpr ?_
      exact (sat_local_regional closed inner regional parts (EnvAgreeOn.extend (first := sets) (second := sets)
        (small := {z | z ∈ region → z ∈ stable}) (large := stable) (fun _ _ _ => Iff.rfl)
        fun z zInside => ⟨fun found => found zInside, fun found _ => found⟩) other otherInside).mp holdsOther
    exact holds _ isClosed inside
  · intro member closedSet isClosed
    have below : ∀ k, lfpStage sets inner region k ⊆ closedSet := by
      intro k
      induction k with
      | zero => exact fun _ none => none.elim
      | succ k ih =>
        intro z found
        exact isClosed z (extensional.sat_mono inner (fun index => Fin.cases ih (fun _ => le_rfl) index) z found.2)
    exact below _ member

include regional parts closed finite bound in
/-- **A greatest fixed point holds at a set of the region exactly at its stable stage.** -/
theorem sat_nu_iff_regional {y : ZFSet.{0}} (inside : y ∈ region) :
    extensional.sat sets (.nu inner) y ↔ y ∈ gfpStage sets inner region N := by
  constructor
  · rintro ⟨invariant, member, preserved⟩
    have within : ∀ k, ∀ z ∈ invariant, z ∈ region → z ∈ gfpStage sets inner region k := by
      intro k
      induction k with
      | zero => exact fun _ _ zInside => zInside
      | succ k ih =>
        intro z zMember zInside
        refine ⟨zInside, extensional.sat_mono inner (small := sets.extend {w | w ∈ invariant ∧ w ∈ region})
          (fun index => Fin.cases (fun w found => ih w found.1 found.2) (fun _ => le_rfl) index) z ?_⟩
        exact (sat_local_regional closed inner regional parts (EnvAgreeOn.extend (first := sets) (second := sets) (small := invariant)
          (large := {w | w ∈ invariant ∧ w ∈ region}) (fun _ _ _ => Iff.rfl) fun w wInside =>
          ⟨fun found => ⟨found, wInside⟩, fun found => found.1⟩) z zInside).mp (preserved z zMember)
    exact within _ y member inside
  · intro member
    refine ⟨gfpStage sets inner region N, member, fun z found => ?_⟩
    exact (gfpStage_fixed sets inner region finite bound (gfpStage_sub_region sets inner region _ found)).mp found

end Fixpoints

theorem sat_mu_iff {n : ℕ} (sets : Env ZFSet.{0} n) {inner : Formula (n + 1)} (modal : inner.modal = true)
    {region : Set ZFSet.{0}} (finite : region.Finite) (closed : ∀ y ∈ region, ∀ z ∈ y, z ∈ region) {N : ℕ}
    (bound : region.ncard ≤ N) {y : ZFSet.{0}} (inside : y ∈ region) :
    extensional.sat sets (.mu inner) y ↔ y ∈ lfpStage sets inner region N :=
  sat_mu_iff_regional sets (Formula.regional_of_modal inner modal) (Or.inl modal) finite closed bound inside

theorem sat_nu_iff {n : ℕ} (sets : Env ZFSet.{0} n) {inner : Formula (n + 1)} (modal : inner.modal = true)
    {region : Set ZFSet.{0}} (finite : region.Finite) (closed : ∀ y ∈ region, ∀ z ∈ y, z ∈ region) {N : ℕ}
    (bound : region.ncard ≤ N) {y : ZFSet.{0}} (inside : y ∈ region) :
    extensional.sat sets (.nu inner) y ↔ y ∈ gfpStage sets inner region N :=
  sat_nu_iff_regional sets (Formula.regional_of_modal inner modal) (Or.inl modal) finite closed bound inside


/-! ## A region to work in -/

/-- **A finite set of hereditarily finite sets closed under membership**, with hereditary terms naming each. -/
structure Region where
  sets : Set ZFSet.{0}
  terms : List Pattern
  closed : ∀ y ∈ sets, ∀ z ∈ y, z ∈ sets
  finite : sets.Finite
  covers : ∀ z ∈ sets, ∃ term ∈ terms, zfOf term = z
  hereditary : ∀ term ∈ terms, IsHF term
  inside : ∀ term ∈ terms, zfOf term ∈ sets

/-- **The region of a hereditary term.** -/
def Region.ofTerm (term : Pattern) (holds : IsHF term) : Region where
  sets := zfRegion term
  terms := regionOf term
  closed := zfRegion_closed holds
  finite := zfRegion_finite term
  covers := fun _ ⟨inner, inside, same⟩ => ⟨inner, inside, same⟩
  hereditary := fun _ inside => hf_of_mem_regionOf holds inside
  inside := fun inner inside => ⟨inner, inside, rfl⟩

/-- A region has at most as many sets as it lists terms. -/
theorem Region.ncard_le (region : Region) : region.sets.ncard ≤ region.terms.length := by
  classical
  have sub : region.sets ⊆ ↑((region.terms.map zfOf).toFinset) := by
    intro z inside
    obtain ⟨term, member, rfl⟩ := region.covers z inside
    simp only [Finset.mem_coe, List.mem_toFinset, List.mem_map]
    exact ⟨term, member, rfl⟩
  calc region.sets.ncard ≤ (↑((region.terms.map zfOf).toFinset) : Set ZFSet.{0}).ncard :=
        Set.ncard_le_ncard sub (Finset.finite_toSet _)
    _ = ((region.terms.map zfOf).toFinset).card := Set.ncard_coe_finset _
    _ ≤ (region.terms.map zfOf).length := List.toFinset_card_le _
    _ = region.terms.length := List.length_map ..

/-! ## Deciding on a region -/

theorem mem_zfOf_iff {term : Pattern} (holds : IsHF term) {z : ZFSet.{0}} :
    z ∈ zfOf term ↔ ∃ value ∈ membersOf term, zfOf value = z := by
  conv_lhs => rw [hf_eq_set holds, zfOf_set]
  exact mem_zfOfList

theorem zfOf_eq_empty_iff {term : Pattern} (holds : IsHF term) : zfOf term = ∅ ↔ membersOf term = [] := by
  constructor
  · intro isEmpty
    cases found : membersOf term with
    | nil => rfl
    | cons value values =>
      have inside := (mem_zfOf_iff holds).mpr ⟨value, by rw [found]; exact List.mem_cons_self, rfl⟩
      rw [isEmpty] at inside
      exact absurd inside (ZFSet.notMem_empty _)
  · intro none
    rw [hf_eq_set holds, zfOf_set, none]
    rfl

theorem zfOf_eq_singleton_iff {term : Pattern} (holds : IsHF term) {element : ZFSet.{0}} :
    zfOf term = {element} ↔ (∃ value ∈ membersOf term, zfOf value = element) ∧
      ∀ value ∈ membersOf term, zfOf value = element := by
  constructor
  · intro single
    refine ⟨(mem_zfOf_iff holds).mp (by rw [single]; exact ZFSet.mem_singleton.mpr rfl), fun value member => ?_⟩
    have inside := (mem_zfOf_iff holds).mpr ⟨value, member, rfl⟩
    rw [single] at inside
    exact ZFSet.mem_singleton.mp inside
  · rintro ⟨found, all⟩
    apply ZFSet.ext
    intro z
    rw [mem_zfOf_iff holds, ZFSet.mem_singleton]
    constructor
    · rintro ⟨value, member, rfl⟩
      exact all value member
    · rintro rfl
      exact found

/-- Whether a hereditary term presents a one-element set: it has members, and they all present one set. -/
def isSingleton (term : Pattern) : Bool :=
  decide (membersOf term ≠ []) && (membersOf term).all fun value => (membersOf term).all (sameSet value)

theorem isSingleton_iff {term : Pattern} (holds : IsHF term) : isSingleton term = true ↔ ∃ element, zfOf term = {element} := by
  simp only [isSingleton, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]
  constructor
  · rintro ⟨nonempty, same⟩
    obtain ⟨first, rest, found⟩ := List.exists_cons_of_ne_nil nonempty
    have firstMember : first ∈ membersOf term := by rw [found]; exact List.mem_cons_self
    refine ⟨zfOf first, (zfOf_eq_singleton_iff holds).mpr ⟨⟨first, firstMember, rfl⟩, fun value member => ?_⟩⟩
    exact (sameSet_iff value (hf_members holds value member) first (hf_members holds first firstMember)).mp
      (same value member first firstMember)
  · rintro ⟨element, single⟩
    obtain ⟨⟨value, member, -⟩, all⟩ := (zfOf_eq_singleton_iff holds).mp single
    refine ⟨List.ne_nil_of_mem member, fun first firstMember second secondMember => ?_⟩
    exact (sameSet_iff first (hf_members holds first firstMember) second (hf_members holds second secondMember)).mpr
      ((all first firstMember).trans (all second secondMember).symm)

/-- Whether a term presents a set that one of the listed terms presents. -/
def presentedIn (terms : List Pattern) (term : Pattern) : Bool := terms.any (sameSet term)

/-- **Stages on a list of terms**: from a start, each stage keeps the listed terms that the body accepts, given the
stage before. -/
def stagesOn (terms : List Pattern) (body : List Pattern → Pattern → Bool) (start : List Pattern) : ℕ → List Pattern
  | 0 => start
  | k + 1 => terms.filter (body (stagesOn terms body start k))

/-- Whether a hereditary set has a type, decided member by member. -/
def decideTyped : TypeExpr → Pattern → Bool
  | .base sort, _ => decide (sort = "Set")
  | .collection kind element, term => decide (kind = .hashSet) && (membersOf term).all (decideTyped element)
  | .arrow _ _, _ => false
  | .multiBinder _, _ => false

theorem decideTyped_iff : ∀ (type : TypeExpr) {term : Pattern}, IsHF term →
    (decideTyped type term = true ↔ SetTyped (zfOf term) type)
  | .base sort, _, _ => by simp [decideTyped, SetTyped]
  | .collection kind element, term, holds => by
    simp only [decideTyped, SetTyped, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]
    refine and_congr_right fun _ => ⟨fun all z member => ?_, fun all value member => ?_⟩
    · obtain ⟨value, valueMember, rfl⟩ := (mem_zfOf_iff holds).mp member
      exact (decideTyped_iff element (hf_members holds value valueMember)).mp (all value valueMember)
    · exact (decideTyped_iff element (hf_members holds value member)).mpr
        (all _ ((mem_zfOf_iff holds).mpr ⟨value, member, rfl⟩))
  | .arrow _ _, _, _ => by simp [decideTyped, SetTyped]
  | .multiBinder _, _, _ => by simp [decideTyped, SetTyped]

/-- Whether at least `k` of the listed terms pass the test, told apart by the sets they present: one passes, and at
least `k - 1` of those presenting other sets do. -/
def countDecide (good : Pattern → Bool) : ℕ → List Pattern → Bool
  | 0, _ => true
  | k + 1, values => values.any fun value =>
    good value && countDecide good k (values.filter fun other => !sameSet other value)

theorem zfOfList_filter_apart {values : List Pattern} (hereditary : ∀ value ∈ values, IsHF value) {term : Pattern}
    (holds : IsHF term) :
    zfOfList (values.filter fun other => !sameSet other term) = ZFSet.sep (fun z => z ≠ zfOf term) (zfOfList values) := by
  apply ZFSet.ext
  intro z
  rw [mem_zfOfList, ZFSet.mem_sep, mem_zfOfList]
  constructor
  · rintro ⟨value, member, rfl⟩
    obtain ⟨inside, apart⟩ := List.mem_filter.mp member
    refine ⟨⟨value, inside, rfl⟩, fun same => ?_⟩
    rw [(sameSet_iff value (hereditary value inside) term holds).mpr same] at apart
    simp at apart
  · rintro ⟨⟨value, inside, rfl⟩, differ⟩
    refine ⟨value, List.mem_filter.mpr ⟨inside, ?_⟩, rfl⟩
    cases same : sameSet value term
    · rfl
    · exact absurd ((sameSet_iff value (hereditary value inside) term holds).mp same) differ

/-- **Counting on the listed terms is counting on the set they present.** -/
theorem countDecide_iff (P : ZFSet.{0} → Prop) {good : Pattern → Bool} : ∀ (k : ℕ) (values : List Pattern),
    (∀ value ∈ values, IsHF value) → (∀ value ∈ values, good value = true ↔ P (zfOf value)) →
      (countDecide good k values = true ↔ CountIn P k (zfOfList values))
  | 0, _, _, _ => by simp [countDecide, CountIn]
  | k + 1, values, hereditary, agree => by
    rw [countDecide, List.any_eq_true, CountIn]
    constructor
    · rintro ⟨term, inside, accepted⟩
      rw [Bool.and_eq_true] at accepted
      refine ⟨zfOf term, mem_zfOfList.mpr ⟨term, inside, rfl⟩, (agree term inside).mp accepted.1, ?_⟩
      rw [← zfOfList_filter_apart hereditary (hereditary term inside)]
      exact (countDecide_iff P k _ (fun value member => hereditary value (List.mem_filter.mp member).1)
        (fun value member => agree value (List.mem_filter.mp member).1)).mp accepted.2
    · rintro ⟨y, inside, holdsY, rest⟩
      obtain ⟨term, termInside, rfl⟩ := mem_zfOfList.mp inside
      refine ⟨term, termInside, Bool.and_eq_true_iff.mpr ⟨(agree term termInside).mpr holdsY, ?_⟩⟩
      rw [← zfOfList_filter_apart hereditary (hereditary term termInside)] at rest
      exact (countDecide_iff P k _ (fun value member => hereditary value (List.mem_filter.mp member).1)
        (fun value member => agree value (List.mem_filter.mp member).1)).mpr rest

theorem zfOf_eq_zfOfList {term : Pattern} (holds : IsHF term) : zfOf term = zfOfList (membersOf term) := by
  conv_lhs => rw [hf_eq_set holds]
  exact zfOf_set _

/-- **The coverings of a list by two parts**: each item goes to the first part, to the second, or to both. -/
def coverings : List Pattern → List (List Pattern × List Pattern)
  | [] => [([], [])]
  | value :: values => (coverings values).flatMap fun parts =>
      [(value :: parts.1, parts.2), (parts.1, value :: parts.2), (value :: parts.1, value :: parts.2)]

theorem mem_coverings_parts : ∀ {values : List Pattern} {parts : List Pattern × List Pattern},
    parts ∈ coverings values → (∀ value ∈ parts.1, value ∈ values) ∧ (∀ value ∈ parts.2, value ∈ values) ∧
      ∀ value ∈ values, value ∈ parts.1 ∨ value ∈ parts.2
  | [], parts, member => by
    rw [coverings, List.mem_singleton] at member
    subst member
    simp
  | value :: values, parts, member => by
    obtain ⟨inner, innerMember, chosen⟩ := List.mem_flatMap.mp member
    obtain ⟨left, right, cover⟩ := mem_coverings_parts innerMember
    simp only [List.mem_cons, List.not_mem_nil, or_false] at chosen
    rcases chosen with rfl | rfl | rfl <;> refine ⟨fun other found => ?_, fun other found => ?_, fun other found => ?_⟩ <;>
      simp only [List.mem_cons] at found ⊢ <;> grind

theorem filter_mem_coverings (first second : Pattern → Bool) : ∀ {values : List Pattern},
    (∀ value ∈ values, first value = true ∨ second value = true) →
      (values.filter first, values.filter second) ∈ coverings values
  | [], _ => List.mem_singleton_self _
  | value :: values, covered => by
    have rest := filter_mem_coverings first second fun other member => covered other (List.mem_cons_of_mem _ member)
    refine List.mem_flatMap.mpr ⟨_, rest, ?_⟩
    have hit := covered value List.mem_cons_self
    cases hFirst : first value <;> cases hSecond : second value <;> simp_all

theorem zfOfList_filter_part {values : List Pattern} {part : ZFSet.{0}} {test : Pattern → Bool}
    (agree : ∀ value ∈ values, test value = true ↔ zfOf value ∈ part) (sub : part ⊆ zfOfList values) :
    zfOfList (values.filter test) = part := by
  apply ZFSet.ext
  intro z
  rw [mem_zfOfList]
  constructor
  · rintro ⟨value, member, rfl⟩
    obtain ⟨member, passes⟩ := List.mem_filter.mp member
    exact (agree value member).mp passes
  · intro inPart
    obtain ⟨value, member, rfl⟩ := mem_zfOfList.mp (ZFSet.subset_def.mp sub inPart)
    exact ⟨value, List.mem_filter.mpr ⟨member, (agree value member).mpr inPart⟩, rfl⟩

/-- **A covering of a term's members presents a split**: its parts are hereditary, and the term's set is the union
of theirs. -/
theorem covering_split {term : Pattern} (holds : IsHF term) {parts : List Pattern × List Pattern}
    (member : parts ∈ coverings (membersOf term)) :
    IsHF (set parts.1) ∧ IsHF (set parts.2) ∧ zfOf term = zfOf (set parts.1) ∪ zfOf (set parts.2) := by
  obtain ⟨left, right, cover⟩ := mem_coverings_parts member
  refine ⟨.members fun value found => hf_members holds value (left value found),
    .members fun value found => hf_members holds value (right value found), ?_⟩
  rw [zfOf_eq_zfOfList holds, zfOf_set, zfOf_set]
  apply ZFSet.ext
  intro z
  rw [ZFSet.mem_union, mem_zfOfList, mem_zfOfList, mem_zfOfList]
  constructor
  · rintro ⟨value, found, rfl⟩
    rcases cover value found with inLeft | inRight
    · exact Or.inl ⟨value, inLeft, rfl⟩
    · exact Or.inr ⟨value, inRight, rfl⟩
  · rintro (⟨value, found, rfl⟩ | ⟨value, found, rfl⟩)
    · exact ⟨value, left value found, rfl⟩
    · exact ⟨value, right value found, rfl⟩

/-- **Every split of a term's set is presented by a covering of its members.** -/
theorem split_covering {term : Pattern} (holds : IsHF term) {first second : ZFSet.{0}}
    (union : zfOf term = first ∪ second) :
    ∃ parts ∈ coverings (membersOf term), zfOf (set parts.1) = first ∧ zfOf (set parts.2) = second := by
  classical
  refine ⟨_, filter_mem_coverings (fun value => decide (zfOf value ∈ first)) (fun value => decide (zfOf value ∈ second))
    fun value member => ?_, ?_, ?_⟩
  · have inside : zfOf value ∈ zfOf term := (mem_zfOf_iff holds).mpr ⟨value, member, rfl⟩
    rw [union, ZFSet.mem_union] at inside
    simpa using inside
  · rw [zfOf_set]
    refine zfOfList_filter_part (fun value _ => decide_eq_true_iff) ?_
    rw [← zfOf_eq_zfOfList holds]
    exact part_left union
  · rw [zfOf_set]
    refine zfOfList_filter_part (fun value _ => decide_eq_true_iff) ?_
    rw [← zfOf_eq_zfOfList holds]
    exact part_right union

/-- **The decision of a modal native type at a term**, on a list of terms closed under members. A fixed point takes as
many stages as there are terms. -/
def decideOn (terms : List Pattern) : {n : ℕ} → Formula n → (Fin n → Pattern → Bool) → Pattern → Bool
  | _, .top, _, _ => true
  | _, .bot, _, _ => false
  | _, .and left right, env, term => decideOn terms left env term && decideOn terms right env term
  | _, .or left right, env, term => decideOn terms left env term || decideOn terms right env term
  | _, .var index, env, term => env index term
  | _, .mu inner, env, term =>
    presentedIn (stagesOn terms (fun stage => decideOn terms inner (Fin.cons (presentedIn stage) env)) [] terms.length) term
  | _, .nu inner, env, term =>
    presentedIn (stagesOn terms (fun stage => decideOn terms inner (Fin.cons (presentedIn stage) env)) terms
      terms.length) term
  | _, .possibly label inner, env, term => decide (memberLabel label) && (membersOf term).any (decideOn terms inner env)
  | _, .necessarily label inner, env, term =>
    !decide (memberLabel label) || (membersOf term).all (decideOn terms inner env)
  | _, .is name, _, term => hereditary membership hfRule.category name && sameSet term name
  | _, .isNot name, _, term => !(hereditary membership hfRule.category name && sameSet term name)
  | _, .empty kind, _, term => decide (kind = .hashSet) && (membersOf term).isEmpty
  | _, .nonEmpty kind, _, term => !(decide (kind = .hashSet) && (membersOf term).isEmpty)
  | _, .typed type, _, term => decideTyped type term
  | _, .untyped type, _, term => !decideTyped type term
  | _, .single kind inner, env, term =>
    decide (kind = .hashSet) && isSingleton term && (membersOf term).any (decideOn terms inner env)
  | _, .everySingle kind inner, env, term =>
    !(decide (kind = .hashSet) && isSingleton term) || (membersOf term).all (decideOn terms inner env)
  | _, .atLeast count .forward label inner, env, term =>
    if memberLabel label then countDecide (decideOn terms inner env) count (membersOf term) else decide (count = 0)
  | _, .allButFewer count .forward label inner, env, term =>
    if memberLabel label then !countDecide (fun value => !decideOn terms inner env value) count (membersOf term)
    else !decide (count = 0)
  | _, .split kind left right, env, term =>
    decide (kind = .hashSet) && (coverings (membersOf term)).any fun parts =>
      decideOn terms left env (set parts.1) && decideOn terms right env (set parts.2)
  | _, .everySplit kind left right, env, term =>
    !decide (kind = .hashSet) || (coverings (membersOf term)).all fun parts =>
      decideOn terms left env (set parts.1) || decideOn terms right env (set parts.2)
  | _, _, _, _ => false

/-- An evaluation of the fixed-point variables that agrees with an environment of sets on a region. -/
def Agrees {n : ℕ} (region : Region) (env : Fin n → Pattern → Bool) (sets : Env ZFSet.{0} n) : Prop :=
  ∀ index (term : Pattern), IsHF term → zfOf term ∈ region.sets → (env index term = true ↔ zfOf term ∈ sets index)

theorem Agrees.extend {n : ℕ} {region : Region} {env : Fin n → Pattern → Bool} {sets : Env ZFSet.{0} n}
    (agree : Agrees region env sets) {test : Pattern → Bool} {set : Set ZFSet.{0}}
    (same : ∀ term : Pattern, IsHF term → zfOf term ∈ region.sets → (test term = true ↔ zfOf term ∈ set)) :
    Agrees region (Fin.cons test env) (sets.extend set) := by
  intro index
  refine Fin.cases ?_ (fun index => ?_) index
  · exact same
  · exact agree index

theorem agrees_closed (region : Region) : Agrees region Fin.elim0 Env.closed := fun index => index.elim0

theorem presentedIn_filter (region : Region) {test : Pattern → Bool} {property : ZFSet.{0} → Prop}
    (agree : ∀ other ∈ region.terms, test other = true ↔ property (zfOf other)) {term : Pattern} (holds : IsHF term)
    (inside : zfOf term ∈ region.sets) : presentedIn (region.terms.filter test) term = true ↔ property (zfOf term) := by
  unfold presentedIn
  rw [List.any_eq_true]
  constructor
  · rintro ⟨other, member, same⟩
    obtain ⟨member, passes⟩ := List.mem_filter.mp member
    rw [(sameSet_iff term holds other (region.hereditary other member)).mp same]
    exact (agree other member).mp passes
  · intro holdsAt
    obtain ⟨other, member, same⟩ := region.covers _ inside
    exact ⟨other, List.mem_filter.mpr ⟨member, (agree other member).mpr (same ▸ holdsAt)⟩,
      (sameSet_iff term holds other (region.hereditary other member)).mpr same.symm⟩

theorem presentedIn_terms (region : Region) {term : Pattern} (holds : IsHF term) (inside : zfOf term ∈ region.sets) :
    presentedIn region.terms term = true := by
  obtain ⟨other, member, same⟩ := region.covers _ inside
  exact List.any_eq_true.mpr ⟨other, member, (sameSet_iff term holds other (region.hereditary other member)).mpr same.symm⟩

section StageLists

variable (region : Region) {n : ℕ} (sets : Env ZFSet.{0} n) (inner : Formula (n + 1))
  {body : List Pattern → Pattern → Bool}
  (bodyIff : ∀ (stage : List Pattern) (set : Set ZFSet.{0}),
    (∀ term : Pattern, IsHF term → zfOf term ∈ region.sets → (presentedIn stage term = true ↔ zfOf term ∈ set)) →
      ∀ other ∈ region.terms, (body stage other = true ↔ extensional.sat (sets.extend set) inner (zfOf other)))

include bodyIff in
/-- **The stages on the listed terms present the least fixed point's stages.** -/
theorem stagesOn_lfp : ∀ (k : ℕ) (term : Pattern), IsHF term → zfOf term ∈ region.sets →
    (presentedIn (stagesOn region.terms body [] k) term = true ↔ zfOf term ∈ lfpStage sets inner region.sets k)
  | 0, _, _, _ => by simp [stagesOn, presentedIn, lfpStage]
  | k + 1, term, holds, inside => by
    rw [stagesOn, presentedIn_filter region (property := fun z => extensional.sat
      (sets.extend (lfpStage sets inner region.sets k)) inner z)
      (bodyIff _ _ (stagesOn_lfp k)) holds inside]
    exact ⟨fun holdsAt => ⟨inside, holdsAt⟩, fun found => found.2⟩

include bodyIff in
/-- **The stages on the listed terms present the greatest fixed point's stages.** -/
theorem stagesOn_gfp : ∀ (k : ℕ) (term : Pattern), IsHF term → zfOf term ∈ region.sets →
    (presentedIn (stagesOn region.terms body region.terms k) term = true ↔ zfOf term ∈ gfpStage sets inner region.sets k)
  | 0, term, holds, inside => ⟨fun _ => inside, fun _ => presentedIn_terms region holds inside⟩
  | k + 1, term, holds, inside => by
    rw [stagesOn, presentedIn_filter region (property := fun z => extensional.sat
      (sets.extend (gfpStage sets inner region.sets k)) inner z)
      (bodyIff _ _ (stagesOn_gfp k)) holds inside]
    exact ⟨fun holdsAt => ⟨inside, holdsAt⟩, fun found => found.2⟩

end StageLists

/-- **The decision is exact**: on a region, closed under parts when the type has splits, it accepts a native type of
the regional fragment at a hereditary term exactly when the type holds at the set the term denotes. -/
theorem decideOn_iff_regional (region : Region) : ∀ {n : ℕ} (formula : Formula n), formula.regional = true →
    formula.modal = true ∨ PartsClosed region.sets → ∀ {env : Fin n → Pattern → Bool} {sets : Env ZFSet.{0} n}, Agrees region env sets → ∀ term : Pattern, IsHF term →
      zfOf term ∈ region.sets → (decideOn region.terms formula env term = true ↔ extensional.sat sets formula (zfOf term))
  | _, .top, _, _, _, _, _, _, _, _ => by simp [decideOn, NativeStructure.sat]
  | _, .bot, _, _, _, _, _, _, _, _ => by simp [decideOn, NativeStructure.sat]
  | _, .and left right, modal, parts, _, _, agree, term, holds, inside => by
    simp only [Formula.regional, Bool.and_eq_true] at modal
    rw [decideOn, Bool.and_eq_true, decideOn_iff_regional region left modal.1 (parts.imp_left fun both => ((Bool.and_eq_true _ _).mp both).1) agree term holds inside,
      decideOn_iff_regional region right modal.2 (parts.imp_left fun both => ((Bool.and_eq_true _ _).mp both).2) agree term holds inside]
    rfl
  | _, .or left right, modal, parts, _, _, agree, term, holds, inside => by
    simp only [Formula.regional, Bool.and_eq_true] at modal
    rw [decideOn, Bool.or_eq_true, decideOn_iff_regional region left modal.1 (parts.imp_left fun both => ((Bool.and_eq_true _ _).mp both).1) agree term holds inside,
      decideOn_iff_regional region right modal.2 (parts.imp_left fun both => ((Bool.and_eq_true _ _).mp both).2) agree term holds inside]
    rfl
  | _, .var index, _, _, _, _, agree, term, holds, inside => agree index term holds inside
  | _, .mu inner, modal, parts, env, sets, agree, term, holds, inside => by
    have modalInner : inner.regional = true := modal
    have partsInner : inner.modal = true ∨ PartsClosed region.sets := parts
    rw [decideOn, stagesOn_lfp region sets inner (fun stage set same other member =>
      decideOn_iff_regional region inner modalInner partsInner (agree.extend same) other (region.hereditary _ member)
        (region.inside _ member)) _ term holds inside]
    exact (sat_mu_iff_regional sets modalInner partsInner region.finite region.closed region.ncard_le inside).symm
  | _, .nu inner, modal, parts, env, sets, agree, term, holds, inside => by
    have modalInner : inner.regional = true := modal
    have partsInner : inner.modal = true ∨ PartsClosed region.sets := parts
    rw [decideOn, stagesOn_gfp region sets inner (fun stage set same other member =>
      decideOn_iff_regional region inner modalInner partsInner (agree.extend same) other (region.hereditary _ member)
        (region.inside _ member)) _ term holds inside]
    exact (sat_nu_iff_regional sets modalInner partsInner region.finite region.closed region.ncard_le inside).symm
  | _, .possibly label inner, modal, parts, env, sets, agree, term, holds, inside => by
    have modalInner : inner.regional = true := by
      simp only [Formula.regional, Bool.and_eq_true] at modal
      exact modal.2
    have partsInner : inner.modal = true ∨ PartsClosed region.sets := parts.imp_left fun inside => by
      simp only [Formula.modal, Bool.and_eq_true] at inside
      exact inside.2
    rw [decideOn, Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true]
    change _ ↔ ∃ next, (memberLabel label ∧ next ∈ zfOf term) ∧ extensional.sat sets inner next
    constructor
    · rintro ⟨labelled, value, member, accepted⟩
      have valueInside := region.closed _ inside _ ((mem_zfOf_iff holds).mpr ⟨value, member, rfl⟩)
      exact ⟨zfOf value, ⟨labelled, (mem_zfOf_iff holds).mpr ⟨value, member, rfl⟩⟩,
        (decideOn_iff_regional region inner modalInner partsInner agree value (hf_members holds value member) valueInside).mp accepted⟩
    · rintro ⟨next, ⟨labelled, member⟩, holdsAt⟩
      obtain ⟨value, valueMember, rfl⟩ := (mem_zfOf_iff holds).mp member
      exact ⟨labelled, value, valueMember, (decideOn_iff_regional region inner modalInner partsInner agree value
        (hf_members holds value valueMember) (region.closed _ inside _ member)).mpr holdsAt⟩
  | _, .necessarily label inner, modal, parts, env, sets, agree, term, holds, inside => by
    have modalInner : inner.regional = true := by
      simp only [Formula.regional, Bool.and_eq_true] at modal
      exact modal.2
    have partsInner : inner.modal = true ∨ PartsClosed region.sets := parts.imp_left fun inside => by
      simp only [Formula.modal, Bool.and_eq_true] at inside
      exact inside.2
    rw [decideOn, Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, List.all_eq_true]
    change _ ↔ ∀ next, (memberLabel label ∧ next ∈ zfOf term) → extensional.sat sets inner next
    constructor
    · rintro (unlabelled | all) next ⟨labelled, member⟩
      · exact absurd labelled unlabelled
      · obtain ⟨value, valueMember, rfl⟩ := (mem_zfOf_iff holds).mp member
        exact (decideOn_iff_regional region inner modalInner partsInner agree value (hf_members holds value valueMember)
          (region.closed _ inside _ member)).mp (all value valueMember)
    · intro all
      by_cases labelled : memberLabel label
      · refine Or.inr fun value member => ?_
        have inZ := (mem_zfOf_iff holds).mpr ⟨value, member, rfl⟩
        exact (decideOn_iff_regional region inner modalInner partsInner agree value (hf_members holds value member)
          (region.closed _ inside _ inZ)).mpr (all _ ⟨labelled, inZ⟩)
      · exact Or.inl labelled
  | _, .is name, _, _, _, _, _, term, holds, _ => by
    change _ ↔ IsHF name ∧ zfOf term = zfOf name
    rw [decideOn, Bool.and_eq_true]
    constructor
    · rintro ⟨named, same⟩
      have nameHolds := (hereditary_iff name).mp named
      exact ⟨nameHolds, (sameSet_iff term holds name nameHolds).mp same⟩
    · rintro ⟨nameHolds, same⟩
      exact ⟨(hereditary_iff name).mpr nameHolds, (sameSet_iff term holds name nameHolds).mpr same⟩
  | _, .isNot name, _, _, _, _, _, term, holds, _ => by
    change _ ↔ ¬ (IsHF name ∧ zfOf term = zfOf name)
    rw [decideOn, Bool.not_eq_true', Bool.and_eq_false_iff]
    constructor
    · rintro (unnamed | apart) ⟨nameHolds, same⟩
      · rw [(hereditary_iff name).mpr nameHolds] at unnamed
        exact Bool.noConfusion unnamed
      · rw [(sameSet_iff term holds name nameHolds).mpr same] at apart
        exact Bool.noConfusion apart
    · intro differ
      cases named : hereditary membership hfRule.category name
      · exact Or.inl rfl
      · cases same : sameSet term name
        · exact Or.inr rfl
        · exact absurd ⟨(hereditary_iff name).mp named, (sameSet_iff term holds name ((hereditary_iff name).mp named)).mp same⟩
            differ
  | _, .empty kind, _, _, _, _, _, term, holds, _ => by
    change _ ↔ kind = .hashSet ∧ zfOf term = ∅
    rw [decideOn, Bool.and_eq_true, decide_eq_true_eq, List.isEmpty_iff, zfOf_eq_empty_iff holds]
  | _, .nonEmpty kind, _, _, _, _, _, term, holds, _ => by
    change _ ↔ ¬ (kind = .hashSet ∧ zfOf term = ∅)
    rw [decideOn, Bool.not_eq_true', Bool.eq_false_iff, Ne, Bool.and_eq_true, decide_eq_true_eq, List.isEmpty_iff,
      zfOf_eq_empty_iff holds]
  | _, .typed type, _, _, _, _, _, term, holds, _ => decideTyped_iff type holds
  | _, .untyped type, _, _, _, _, _, term, holds, _ => by
    change _ ↔ ¬ SetTyped (zfOf term) type
    rw [decideOn, Bool.not_eq_true', Bool.eq_false_iff, Ne, decideTyped_iff type holds]
  | _, .single kind inner, modal, parts, env, sets, agree, term, holds, inside => by
    have modalInner : inner.regional = true := modal
    have partsInner : inner.modal = true ∨ PartsClosed region.sets := parts
    rw [decideOn, Bool.and_eq_true, Bool.and_eq_true, decide_eq_true_eq, isSingleton_iff holds, List.any_eq_true]
    change _ ↔ ∃ element, (kind = .hashSet ∧ zfOf term = {element}) ∧ extensional.sat sets inner element
    constructor
    · rintro ⟨⟨set, element, single⟩, value, member, accepted⟩
      have same := ((zfOf_eq_singleton_iff holds).mp single).2 value member
      refine ⟨element, ⟨set, single⟩, same ▸ ?_⟩
      exact (decideOn_iff_regional region inner modalInner partsInner agree value (hf_members holds value member)
        (region.closed _ inside _ ((mem_zfOf_iff holds).mpr ⟨value, member, rfl⟩))).mp accepted
    · rintro ⟨element, ⟨set, single⟩, holdsAt⟩
      obtain ⟨⟨value, member, same⟩, -⟩ := (zfOf_eq_singleton_iff holds).mp single
      refine ⟨⟨set, element, single⟩, value, member, ?_⟩
      exact (decideOn_iff_regional region inner modalInner partsInner agree value (hf_members holds value member)
        (region.closed _ inside _ ((mem_zfOf_iff holds).mpr ⟨value, member, rfl⟩))).mpr (same ▸ holdsAt)
  | _, .everySingle kind inner, modal, parts, env, sets, agree, term, holds, inside => by
    have modalInner : inner.regional = true := modal
    have partsInner : inner.modal = true ∨ PartsClosed region.sets := parts
    rw [decideOn, Bool.or_eq_true, Bool.not_eq_true', Bool.and_eq_false_iff, decide_eq_false_iff_not, List.all_eq_true]
    change _ ↔ ∀ element, (kind = .hashSet ∧ zfOf term = {element}) → extensional.sat sets inner element
    have accepts : ∀ value ∈ membersOf term, (decideOn region.terms inner env value = true ↔
        extensional.sat sets inner (zfOf value)) := fun value member =>
      decideOn_iff_regional region inner modalInner partsInner agree value (hf_members holds value member)
        (region.closed _ inside _ ((mem_zfOf_iff holds).mpr ⟨value, member, rfl⟩))
    constructor
    · rintro ((unset | notSingle) | all) element ⟨set, single⟩
      · exact absurd set unset
      · rw [Bool.eq_false_iff, Ne, isSingleton_iff holds] at notSingle
        exact absurd ⟨element, single⟩ notSingle
      · obtain ⟨⟨value, member, same⟩, -⟩ := (zfOf_eq_singleton_iff holds).mp single
        exact same ▸ (accepts value member).mp (all value member)
    · intro holdsAll
      by_cases set : kind = .hashSet
      · cases single : isSingleton term
        · exact Or.inl (Or.inr rfl)
        · obtain ⟨element, isSingle⟩ := (isSingleton_iff holds).mp single
          refine Or.inr fun value member => (accepts value member).mpr ?_
          rw [((zfOf_eq_singleton_iff holds).mp isSingle).2 value member]
          exact holdsAll element ⟨set, isSingle⟩
      · exact Or.inl (Or.inl set)
  | _, .atLeast count .forward label inner, modal, parts, env, sets, agree, term, holds, inside => by
    have modalInner : inner.regional = true := by
      simp only [Formula.regional, Bool.and_eq_true] at modal
      exact modal.2
    have partsInner : inner.modal = true ∨ PartsClosed region.sets := parts.imp_left fun inside => by
      simp only [Formula.modal, Bool.and_eq_true] at inside
      exact inside.2
    change _ ↔ extensional.AtLeast count fun other =>
      (memberLabel label ∧ other ∈ zfOf term) ∧ extensional.sat sets inner other
    by_cases labelled : memberLabel label
    · rw [decideOn, if_pos labelled, countDecide_iff (extensional.sat sets inner) count (membersOf term)
        (hf_members holds) (fun value member => decideOn_iff_regional region inner modalInner partsInner agree value
          (hf_members holds value member) (region.closed _ inside _ ((mem_zfOf_iff holds).mpr ⟨value, member, rfl⟩))),
        ← zfOf_eq_zfOfList holds, countIn_iff_atLeast]
      exact ⟨fun many => many.mono fun _ found => ⟨⟨labelled, found.1⟩, found.2⟩,
        fun many => many.mono fun _ found => ⟨found.1.2, found.2⟩⟩
    · rw [decideOn, if_neg labelled, decide_eq_true_eq, atLeast_unlabelled labelled]
  | _, .allButFewer count .forward label inner, modal, parts, env, sets, agree, term, holds, inside => by
    have modalInner : inner.regional = true := by
      simp only [Formula.regional, Bool.and_eq_true] at modal
      exact modal.2
    have partsInner : inner.modal = true ∨ PartsClosed region.sets := parts.imp_left fun inside => by
      simp only [Formula.modal, Bool.and_eq_true] at inside
      exact inside.2
    change _ ↔ ¬ extensional.AtLeast count fun other =>
      (memberLabel label ∧ other ∈ zfOf term) ∧ ¬ extensional.sat sets inner other
    by_cases labelled : memberLabel label
    · rw [decideOn, if_pos labelled, Bool.not_eq_true', Bool.eq_false_iff, Ne,
        countDecide_iff (fun z => ¬ extensional.sat sets inner z) count (membersOf term) (hf_members holds)
          (fun value member => by
            rw [Bool.not_eq_true', Bool.eq_false_iff, Ne, decideOn_iff_regional region inner modalInner partsInner agree value
              (hf_members holds value member) (region.closed _ inside _ ((mem_zfOf_iff holds).mpr ⟨value, member, rfl⟩))]),
        ← zfOf_eq_zfOfList holds, countIn_iff_atLeast]
      exact not_congr ⟨fun many => many.mono fun _ found => ⟨⟨labelled, found.1⟩, found.2⟩,
        fun many => many.mono fun _ found => ⟨found.1.2, found.2⟩⟩
    · rw [decideOn, if_neg labelled, Bool.not_eq_true', Bool.eq_false_iff, Ne, decide_eq_true_eq,
        atLeast_unlabelled labelled]
  | _, .split kind left right, modal, parts, env, sets, agree, term, holds, inside => by
    simp only [Formula.regional, Bool.and_eq_true] at modal
    have closedParts : PartsClosed region.sets := parts.resolve_left Bool.false_ne_true
    have decides : ∀ cover ∈ coverings (membersOf term),
        (decideOn region.terms left env (set cover.1) = true ↔ extensional.sat sets left (zfOf (set cover.1))) ∧
          (decideOn region.terms right env (set cover.2) = true ↔ extensional.sat sets right (zfOf (set cover.2))) := by
      intro cover member
      obtain ⟨leftHolds, rightHolds, union⟩ := covering_split holds member
      exact ⟨decideOn_iff_regional region left modal.1 (Or.inr closedParts) agree _ leftHolds
          (closedParts _ inside _ (part_left union)),
        decideOn_iff_regional region right modal.2 (Or.inr closedParts) agree _ rightHolds
          (closedParts _ inside _ (part_right union))⟩
    rw [decideOn, Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true]
    change _ ↔ ∃ first second, (kind = .hashSet ∧ zfOf term = first ∪ second) ∧ extensional.sat sets left first ∧
      extensional.sat sets right second
    constructor
    · rintro ⟨isSet, cover, member, accepted⟩
      rw [Bool.and_eq_true] at accepted
      exact ⟨_, _, ⟨isSet, (covering_split holds member).2.2⟩, (decides cover member).1.mp accepted.1,
        (decides cover member).2.mp accepted.2⟩
    · rintro ⟨first, second, ⟨isSet, union⟩, holdsLeft, holdsRight⟩
      obtain ⟨cover, member, firstEq, secondEq⟩ := split_covering holds union
      refine ⟨isSet, cover, member, ?_⟩
      rw [Bool.and_eq_true]
      exact ⟨(decides cover member).1.mpr (firstEq ▸ holdsLeft), (decides cover member).2.mpr (secondEq ▸ holdsRight)⟩
  | _, .everySplit kind left right, modal, parts, env, sets, agree, term, holds, inside => by
    simp only [Formula.regional, Bool.and_eq_true] at modal
    have closedParts : PartsClosed region.sets := parts.resolve_left Bool.false_ne_true
    have decides : ∀ cover ∈ coverings (membersOf term),
        (decideOn region.terms left env (set cover.1) = true ↔ extensional.sat sets left (zfOf (set cover.1))) ∧
          (decideOn region.terms right env (set cover.2) = true ↔ extensional.sat sets right (zfOf (set cover.2))) := by
      intro cover member
      obtain ⟨leftHolds, rightHolds, union⟩ := covering_split holds member
      exact ⟨decideOn_iff_regional region left modal.1 (Or.inr closedParts) agree _ leftHolds
          (closedParts _ inside _ (part_left union)),
        decideOn_iff_regional region right modal.2 (Or.inr closedParts) agree _ rightHolds
          (closedParts _ inside _ (part_right union))⟩
    rw [decideOn, Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, List.all_eq_true]
    change _ ↔ ∀ first second, (kind = .hashSet ∧ zfOf term = first ∪ second) →
      extensional.sat sets left first ∨ extensional.sat sets right second
    constructor
    · rintro (unset | all) first second ⟨isSet, union⟩
      · exact absurd isSet unset
      · obtain ⟨cover, member, firstEq, secondEq⟩ := split_covering holds union
        have accepted := all cover member
        rw [Bool.or_eq_true] at accepted
        rw [← firstEq, ← secondEq]
        exact accepted.imp (decides cover member).1.mp (decides cover member).2.mp
    · intro holdsAll
      by_cases isSet : kind = .hashSet
      · refine Or.inr fun cover member => ?_
        rw [Bool.or_eq_true]
        exact (holdsAll _ _ ⟨isSet, (covering_split holds member).2.2⟩).imp (decides cover member).1.mpr
          (decides cover member).2.mpr
      · exact Or.inl isSet
  | _, .sometimeBefore _ _, modal, _, _, _, _, _, _, _ | _, .alwaysBefore _ _, modal, _, _, _, _, _, _, _
  | _, .atLeast _ .backward _ _, modal, _, _, _, _, _, _, _ | _, .allButFewer _ .backward _ _, modal, _, _, _, _, _, _, _
  | _, .built _ _, modal, _, _, _, _, _, _, _ | _, .everyBuilt _ _, modal, _, _, _, _, _, _, _
  | _, .body _, modal, _, _, _, _, _, _, _ | _, .everyBody _, modal, _, _, _, _, _, _, _
  | _, .multiBody _ _, modal, _, _, _, _, _, _, _ | _, .everyMultiBody _ _, modal, _, _, _, _, _, _, _
  | _, .bound _, modal, _, _, _, _, _, _, _ | _, .notBound _, modal, _, _, _, _, _, _, _
  | _, .mapsAll _ _, modal, _, _, _, _, _, _, _ | _, .mapsSome _ _, modal, _, _, _, _, _, _, _
  | _, .someOf _ _, modal, _, _, _, _, _, _, _ | _, .everyOf _ _, modal, _, _, _, _, _, _, _ => absurd modal Bool.false_ne_true

/-- **The decision is exact on modal native types**, on any region. -/
theorem decideOn_iff (region : Region) {n : ℕ} (formula : Formula n) (modal : formula.modal = true)
    {env : Fin n → Pattern → Bool} {sets : Env ZFSet.{0} n} (agree : Agrees region env sets) (term : Pattern)
    (holds : IsHF term) (inside : zfOf term ∈ region.sets) :
    decideOn region.terms formula env term = true ↔ extensional.sat sets formula (zfOf term) :=
  decideOn_iff_regional region formula (Formula.regional_of_modal formula modal) (Or.inl modal) agree term holds inside

end Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetReadings
