import Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetMembershipTypes
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetMembershipRegions

/-!
# Types that count members up to a cap

The types of `SetMembershipTypes` are decided by which types the members have. Counting formulas ask how many members
have a type, so here a set is described by its members' types counted up to a cap (`countOf`): how many members have
each type, with every count from the cap on read as the cap. A closure is **count-local** when each of its formulas is
decided by these counts (`IsCountLocal`). Membership-local closures are count-local at every positive cap
(`Determined.counted`).

Steps back and sorts are decided by searching a finite stage. Replacing the members of a container by representatives
must now keep the counts, so the representatives of one type must be distinct, and a stage must hold enough sets of
each type:

- **Multiplicities** (`multAt`): how many sets of each type `V_k` holds, read up to one more than the cap. They grow
  with `k`, and once two consecutive stages agree all later ones do (`multAt_succ_eq`, `multAt_stable`): a set of
  `V_(k+2)` with a member outside `V_k` has a type of which `V_(k+1)` holds more sets than the cap, built from
  different choices of representatives (`many_candidates`).
- **A rich stage** (`Rich`) holds, for every type, as many sets of that type as any finite family of sets of that type
  has, up to one more than the cap. A stable stage is rich (`rich_of_stable`), and a stage is stable by
  `typeBound · (cap + 1)` (`exists_multStable_le`), so that stage is rich (`rich_countedBound`).
- **Steps back and sorts by a rich stage**: a set containing `x` may be taken to be `x` with distinct representatives
  of its other members from a rich stage (`exists_container_counted`), and some set has a formula of the closure
  exactly when some set of a rich stage has it (`sometimeBefore_iff_rich`, `someOf_iff_rich` and their duals).
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetReadings

open Mettapedia.OSLF.MeTTaIL.Syntax
open Classical

noncomputable section

/-! ## Binomials -/

/-- **A set of `n` has at least `n` subsets of each size strictly between `0` and `n`.** -/
theorem self_le_choose : ∀ {n s : ℕ}, 1 ≤ s → s < n → n ≤ n.choose s
  | 0, _, _, small => absurd small (Nat.not_lt_zero _)
  | n + 1, 0, positive, _ => absurd positive (by decide)
  | n + 1, 1, _, _ => by rw [Nat.choose_one_right]
  | n + 1, t + 2, _, small => by
    rw [Nat.choose_succ_succ']
    by_cases equal : t + 2 = n
    · subst equal
      rw [Nat.choose_self, Nat.choose_symm_of_eq_add (show t + 2 = (t + 1) + 1 by omega), Nat.choose_one_right]
    · have rest := self_le_choose (n := n) (s := t + 1 + 1) (by omega) (by omega)
      have positive : 0 < n.choose (t + 1) := Nat.choose_pos (by omega)
      omega

/-! ## Members as a finite set -/

/-- The members of a hereditarily finite set are finitely many. -/
theorem members_finite (x : HF) : {m : HF | m.1 ∈ x.1}.Finite := by
  obtain ⟨term, holds, same⟩ := x.2
  have image : {z : ZFSet.{0} | z ∈ x.1}.Finite := by
    refine ((membersOf term).map zfOf).toFinset.finite_toSet.subset fun z inside => ?_
    rw [← same] at inside
    obtain ⟨value, member, rfl⟩ := (mem_zfOf_iff holds).mp inside
    simpa using ⟨value, member, rfl⟩
  exact image.preimage Subtype.val_injective.injOn

/-- **The members of a set**, as a finite set. -/
def memberSet (x : HF) : Finset HF := (members_finite x).toFinset

theorem mem_memberSet {x m : HF} : m ∈ memberSet x ↔ m.1 ∈ x.1 := by simp [memberSet]

/-- `V_k`, as a hereditarily finite set. -/
def stageHF (k : ℕ) : HF := ⟨stage k, isHFSet_of_subset_vonNeumann (subset_refl _)⟩

/-- **The sets of `V_k`**, as a finite set. -/
def stageSet (k : ℕ) : Finset HF := memberSet (stageHF k)

theorem mem_stageSet {k : ℕ} {y : HF} : y ∈ stageSet k ↔ y.1 ∈ stage k := mem_memberSet

theorem stageSet_mono {k l : ℕ} (le : k ≤ l) : stageSet k ⊆ stageSet l := fun _ inside =>
  mem_stageSet.mpr (stage_mono le (mem_stageSet.mp inside))

/-- **A finite set of sets of `V_k`**, as a hereditarily finite set: the subset of `V_k` they form. -/
def ofFinset {k : ℕ} (parts : Finset HF) : ZFSet.{0} := ZFSet.sep (fun z => ∃ m ∈ parts, m.1 = z) (stage k)

theorem ofFinset_subset {k : ℕ} (parts : Finset HF) : ofFinset (k := k) parts ⊆ stage k := fun _ inside =>
  (ZFSet.mem_sep.mp inside).1

theorem mem_ofFinset {k : ℕ} {parts : Finset HF} (within : parts ⊆ stageSet k) {z : ZFSet.{0}} :
    z ∈ ofFinset (k := k) parts ↔ ∃ m ∈ parts, m.1 = z := by
  rw [ofFinset, ZFSet.mem_sep]
  constructor
  · exact fun inside => inside.2
  · rintro ⟨m, member, rfl⟩
    exact ⟨mem_stageSet.mp (within member), m, member, rfl⟩

theorem memberSet_ofStage {k : ℕ} {parts : Finset HF} (within : parts ⊆ stageSet k) :
    memberSet (ofStage (ofFinset_subset (k := k) parts)) = parts := by
  ext m
  rw [mem_memberSet]
  change m.1 ∈ ofFinset parts ↔ _
  rw [mem_ofFinset within]
  constructor
  · rintro ⟨other, member, same⟩
    rwa [← Subtype.ext same]
  · exact fun member => ⟨m, member, rfl⟩

theorem memberSet_insertStage {k : ℕ} (x : HF) {parts : Finset HF} (within : parts ⊆ stageSet k) :
    memberSet (insertStage x (ofFinset_subset (k := k) parts)) = insert x parts := by
  ext m
  rw [mem_memberSet, Finset.mem_insert]
  change m.1 ∈ insert x.1 (ofFinset parts) ↔ _
  rw [ZFSet.mem_insert_iff, mem_ofFinset within]
  constructor
  · rintro (same | ⟨other, member, same⟩)
    · exact .inl (Subtype.ext same)
    · exact .inr (by rwa [← Subtype.ext same])
  · rintro (rfl | member)
    · exact .inl rfl
    · exact .inr ⟨m, member, rfl⟩

/-! ## Counts of the members' types -/

section Counts

variable (closure : List (Formula 0)) (cap : ℕ)

/-- The members of a set with a type. -/
def membersOfType (x : HF) (τ : Finset (Formula 0)) : Finset HF := (memberSet x).filter fun m => typeOf closure m = τ

/-- **The members' types counted up to the cap.** -/
def countOf (x : HF) (τ : Finset (Formula 0)) : ℕ := min cap (membersOfType closure x τ).card

/-- **A property decided by the counts** of the members' types up to the cap. -/
def CountDetermined (p : HF → Prop) : Prop :=
  ∀ x y : HF, countOf closure cap x = countOf closure cap y → (p x ↔ p y)

/-- **A count-local closure**: each of its formulas is decided by the counts. -/
def IsCountLocal : Prop := ∀ φ ∈ closure, CountDetermined closure cap (HFSets.sat Env.closed φ)

variable {closure cap}

theorem IsCountLocal.typeOf_eq (loc : IsCountLocal closure cap) {x y : HF}
    (same : countOf closure cap x = countOf closure cap y) : typeOf closure x = typeOf closure y := by
  ext φ
  simp only [mem_typeOf]
  exact and_congr_right fun inside => loc φ inside x y same

theorem CountDetermined.mono {p : HF → Prop} {cap' : ℕ} (le : cap ≤ cap') (determined : CountDetermined closure cap p) :
    CountDetermined closure cap' p := by
  intro x y same
  refine determined x y (funext fun τ => ?_)
  have := congrFun same τ
  simp only [countOf] at this ⊢
  rw [← min_min_cancel_left le, this, min_min_cancel_left le]
where
  min_min_cancel_left {a b : ℕ} (le : a ≤ b) (n : ℕ) : min a (min b n) = min a n := by omega

theorem CountDetermined.of_iff {p q : HF → Prop} (same : ∀ x, p x ↔ q x) (determined : CountDetermined closure cap p) :
    CountDetermined closure cap q := fun x y counts => (same x).symm.trans ((determined x y counts).trans (same y))

theorem CountDetermined.const (P : Prop) : CountDetermined closure cap fun _ => P := fun _ _ _ => Iff.rfl

theorem CountDetermined.and {p q : HF → Prop} (left : CountDetermined closure cap p)
    (right : CountDetermined closure cap q) : CountDetermined closure cap fun x => p x ∧ q x :=
  fun x y same => and_congr (left x y same) (right x y same)

theorem CountDetermined.or {p q : HF → Prop} (left : CountDetermined closure cap p)
    (right : CountDetermined closure cap q) : CountDetermined closure cap fun x => p x ∨ q x :=
  fun x y same => or_congr (left x y same) (right x y same)

theorem mem_memberTypes_iff_count {x : HF} {τ : Finset (Formula 0)} (positive : 1 ≤ cap) :
    τ ∈ memberTypes closure x ↔ 0 < countOf closure cap x τ := by
  simp only [memberTypes, Set.mem_ofPred_eq, countOf, lt_min_iff, Finset.card_pos, membersOfType]
  constructor
  · rintro ⟨m, inside, rfl⟩
    exact ⟨positive, m, Finset.mem_filter.mpr ⟨mem_memberSet.mpr inside, rfl⟩⟩
  · rintro ⟨-, m, found⟩
    obtain ⟨inside, rfl⟩ := Finset.mem_filter.mp found
    exact ⟨m, mem_memberSet.mp inside, rfl⟩

/-- **What the members' types decide, their counts decide**, at every positive cap. -/
theorem Determined.counted {p : HF → Prop} (positive : 1 ≤ cap) (determined : Determined closure p) :
    CountDetermined closure cap p := by
  intro x y same
  refine determined x y (Set.ext fun τ => ?_)
  rw [mem_memberTypes_iff_count positive, mem_memberTypes_iff_count positive, congrFun same τ]

/-- A membership-local closure is count-local at every positive cap. -/
theorem IsLocal.counted (loc : IsLocal closure) (positive : 1 ≤ cap) : IsCountLocal closure cap :=
  fun φ inside => (loc φ inside).counted positive

end Counts

/-! ## Multiplicities -/

section Multiplicities

variable (closure : List (Formula 0)) (cap : ℕ)

/-- **The sets of `V_k` with a type.** -/
def typedAt (k : ℕ) (τ : Finset (Formula 0)) : Finset HF := (stageSet k).filter fun y => typeOf closure y = τ

/-- **How many sets of each type `V_k` holds**, up to one more than the cap. -/
def multAt (k : ℕ) (τ : Finset (Formula 0)) : ℕ := min (cap + 1) (typedAt closure k τ).card

/-- **A rich stage**: for every type, it holds as many sets of that type as any finite family of sets of that type
has, up to one more than the cap. -/
def Rich (k : ℕ) : Prop :=
  ∀ (τ : Finset (Formula 0)) (family : Finset HF), (∀ y ∈ family, typeOf closure y = τ) →
    min (cap + 1) family.card ≤ (typedAt closure k τ).card

variable {closure cap}

theorem mem_typedAt {k : ℕ} {τ : Finset (Formula 0)} {y : HF} :
    y ∈ typedAt closure k τ ↔ y.1 ∈ stage k ∧ typeOf closure y = τ := by
  rw [typedAt, Finset.mem_filter, mem_stageSet]

theorem typedAt_mono {k l : ℕ} (le : k ≤ l) (τ : Finset (Formula 0)) : typedAt closure k τ ⊆ typedAt closure l τ :=
  Finset.filter_subset_filter _ (stageSet_mono le)

theorem multAt_mono {k l : ℕ} (le : k ≤ l) (τ : Finset (Formula 0)) : multAt closure cap k τ ≤ multAt closure cap l τ :=
  min_le_min_left _ (Finset.card_le_card (typedAt_mono le τ))

theorem Rich.mono {k l : ℕ} (rich : Rich closure cap k) (le : k ≤ l) : Rich closure cap l :=
  fun τ family typed => (rich τ family typed).trans (Finset.card_le_card (typedAt_mono le τ))

/-- Where consecutive multiplicities agree, a type with a set of `V_(k+1)` outside `V_k` has more sets in `V_k` than the
cap. -/
theorem many_of_new {k : ℕ} (same : multAt closure cap k = multAt closure cap (k + 1)) {m : HF}
    (inside : m.1 ∈ stage (k + 1)) (outside : m.1 ∉ stage k) : cap + 1 ≤ (typedAt closure k (typeOf closure m)).card := by
  have strict : typedAt closure k (typeOf closure m) ⊂ typedAt closure (k + 1) (typeOf closure m) :=
    Finset.ssubset_iff_subset_ne.mpr ⟨typedAt_mono (Nat.le_succ k) _, fun equal => outside
      (mem_typedAt.mp (equal ▸ mem_typedAt.mpr ⟨inside, rfl⟩)).1⟩
  have counts := congrFun same (typeOf closure m)
  have bigger := Finset.card_lt_card strict
  simp only [multAt] at counts
  omega

/-- Where consecutive multiplicities agree, `V_k` holds as many sets of a type as the members of a set of `V_(k+2)`
of that type, up to one more than the cap. -/
theorem enough_below {k : ℕ} (same : multAt closure cap k = multAt closure cap (k + 1)) {y : HF}
    (inside : y.1 ⊆ stage (k + 1)) (ρ : Finset (Formula 0)) :
    min (cap + 1) (membersOfType closure y ρ).card ≤ (typedAt closure k ρ).card := by
  have within : membersOfType closure y ρ ⊆ typedAt closure (k + 1) ρ := fun m found => by
    obtain ⟨member, typed⟩ := Finset.mem_filter.mp found
    exact mem_typedAt.mpr ⟨inside (mem_memberSet.mp member), typed⟩
  have counts := congrFun same ρ
  have small := Finset.card_le_card within
  simp only [multAt] at counts
  omega

/-- **The types a set's members have.** -/
def memberTypeSet (y : HF) : Finset (Finset (Formula 0)) := (memberSet y).image (typeOf closure)

/-- **A set built from chosen representatives**: for each type of a member, the chosen sets of that type. -/
def chosenUnion (y : HF) (choice : Finset (Formula 0) → Finset HF) : Finset HF :=
  (memberTypeSet (closure := closure) y).biUnion choice

theorem filter_chosenUnion {k : ℕ} {y : HF} {choice : Finset (Formula 0) → Finset HF}
    (typed : ∀ ρ, ∀ m ∈ choice ρ, m ∈ typedAt closure k ρ) (ρ : Finset (Formula 0)) :
    (chosenUnion (closure := closure) y choice).filter (fun m => typeOf closure m = ρ) =
      if ρ ∈ memberTypeSet (closure := closure) y then choice ρ else ∅ := by
  ext m
  simp only [Finset.mem_filter, chosenUnion, Finset.mem_biUnion]
  constructor
  · rintro ⟨⟨σ, found, chosen⟩, rfl⟩
    have := (mem_typedAt.mp (typed σ m chosen)).2
    subst this
    rw [if_pos found]
    exact chosen
  · intro chosen
    split at chosen
    · rename_i found
      exact ⟨⟨ρ, found, chosen⟩, (mem_typedAt.mp (typed ρ m chosen)).2⟩
    · cases chosen

theorem membersOfType_chosen {k : ℕ} {y : HF} {choice : Finset (Formula 0) → Finset HF}
    (typed : ∀ ρ, ∀ m ∈ choice ρ, m ∈ typedAt closure k ρ) (ρ : Finset (Formula 0))
    (within : chosenUnion (closure := closure) y choice ⊆ stageSet k) :
    membersOfType closure (ofStage (ofFinset_subset (k := k) (chosenUnion (closure := closure) y choice))) ρ =
      if ρ ∈ memberTypeSet (closure := closure) y then choice ρ else ∅ := by
  simp only [membersOfType, memberSet_ofStage within]
  exact filter_chosenUnion typed ρ

theorem membersOfType_eq_empty {y : HF} {ρ : Finset (Formula 0)} (missing : ρ ∉ memberTypeSet (closure := closure) y) :
    membersOfType closure y ρ = ∅ :=
  Finset.eq_empty_of_forall_notMem fun other found => missing
    (Finset.mem_image.mpr ⟨other, (Finset.mem_filter.mp found).1, (Finset.mem_filter.mp found).2⟩)

/-- **A set of `V_(k+2)` with a member outside `V_k`** has, where consecutive multiplicities agree, more sets of its type
in `V_(k+1)` than the cap: its members replaced by representatives in `V_k`, the representatives of the new member's
type chosen in more than `cap` different ways. -/
theorem many_candidates (loc : IsCountLocal closure cap) (positive : 1 ≤ cap) {k : ℕ}
    (same : multAt closure cap k = multAt closure cap (k + 1)) {y m : HF} (inside : y.1 ⊆ stage (k + 1))
    (member : m.1 ∈ y.1) (outside : m.1 ∉ stage k) :
    cap + 1 ≤ (typedAt closure (k + 1) (typeOf closure y)).card := by
  -- the sizes the representatives must have
  let size : Finset (Formula 0) → ℕ := fun ρ => min cap (membersOfType closure y ρ).card
  have available : ∀ ρ, size ρ ≤ (typedAt closure k ρ).card := fun ρ =>
    le_trans (by simp only [size]; omega) (enough_below same inside ρ)
  -- a fixed choice for every type
  let fixed : Finset (Formula 0) → Finset HF := fun ρ =>
    (Finset.exists_subset_card_eq (available ρ)).choose
  have fixed_spec : ∀ ρ, fixed ρ ⊆ typedAt closure k ρ ∧ (fixed ρ).card = size ρ := fun ρ =>
    (Finset.exists_subset_card_eq (available ρ)).choose_spec
  -- the new member's type has more sets in `V_k` than the cap
  let σ := typeOf closure m
  have big := many_of_new same (inside member) outside
  have sizeσ : 1 ≤ size σ ∧ size σ ≤ cap := by
    have : 0 < (membersOfType closure y σ).card :=
      Finset.card_pos.mpr ⟨m, Finset.mem_filter.mpr ⟨mem_memberSet.mpr member, rfl⟩⟩
    simp only [size]
    omega
  -- the candidates: every choice for `σ`, the fixed choice elsewhere
  let choiceWith : Finset HF → Finset (Formula 0) → Finset HF := fun chosen ρ => if ρ = σ then chosen else fixed ρ
  let candidates := (typedAt closure k σ).powersetCard (size σ)
  have typedWith : ∀ chosen ∈ candidates, ∀ ρ, ∀ other ∈ choiceWith chosen ρ, other ∈ typedAt closure k ρ := by
    intro chosen picked ρ other found
    simp only [choiceWith] at found
    split at found
    · rename_i equal
      subst equal
      exact (Finset.mem_powersetCard.mp picked).1 found
    · exact (fixed_spec ρ).1 found
  have withinWith : ∀ chosen ∈ candidates, chosenUnion (closure := closure) y (choiceWith chosen) ⊆ stageSet k := by
    intro chosen picked other found
    obtain ⟨ρ, -, chosenFound⟩ := Finset.mem_biUnion.mp found
    exact Finset.filter_subset _ _ (typedWith chosen picked ρ other chosenFound)
  have σMember : σ ∈ memberTypeSet (closure := closure) y :=
    Finset.mem_image.mpr ⟨m, mem_memberSet.mpr member, rfl⟩
  -- each candidate has the counts of `y`, hence its type
  let build : Finset HF → HF := fun chosen =>
    ofStage (ofFinset_subset (k := k) (chosenUnion (closure := closure) y (choiceWith chosen)))
  have typeBuild : ∀ chosen ∈ candidates, typeOf closure (build chosen) = typeOf closure y := by
    intro chosen picked
    refine loc.typeOf_eq (funext fun ρ => ?_)
    simp only [countOf, build]
    rw [membersOfType_chosen (typedWith chosen picked) ρ (withinWith chosen picked)]
    split
    · rename_i found
      simp only [choiceWith]
      split
      · rename_i equal
        subst equal
        rw [(Finset.mem_powersetCard.mp picked).2]
        simp only [size]
        omega
      · rw [(fixed_spec ρ).2]
        simp only [size]
        omega
    · rename_i missing
      rw [membersOfType_eq_empty missing]
  -- different choices give different sets
  have injective : Set.InjOn build candidates := by
    intro first firstPicked second secondPicked equal
    have := congrArg (fun z => membersOfType closure z σ) equal
    simp only [build] at this
    rw [membersOfType_chosen (typedWith first firstPicked) σ (withinWith first firstPicked),
      membersOfType_chosen (typedWith second secondPicked) σ (withinWith second secondPicked), if_pos σMember,
      if_pos σMember] at this
    simpa [choiceWith] using this
  have into : ∀ chosen ∈ candidates, build chosen ∈ typedAt closure (k + 1) (typeOf closure y) := by
    intro chosen picked
    refine mem_typedAt.mpr ⟨mem_stage_succ.mpr (ofFinset_subset _), typeBuild chosen picked⟩
  have count : (candidates.image build).card = candidates.card := Finset.card_image_of_injOn injective
  have enough : cap + 1 ≤ candidates.card := by
    rw [Finset.card_powersetCard]
    exact le_trans big (self_le_choose sizeσ.1 (by omega))
  calc cap + 1 ≤ (candidates.image build).card := count ▸ enough
    _ ≤ _ := Finset.card_le_card fun other found => by
      obtain ⟨chosen, picked, rfl⟩ := Finset.mem_image.mp found
      exact into chosen picked

/-- **Once two consecutive stages hold as many sets of each type, so does the next.** -/
theorem multAt_succ_eq (loc : IsCountLocal closure cap) (positive : 1 ≤ cap) {k : ℕ}
    (same : multAt closure cap k = multAt closure cap (k + 1)) :
    multAt closure cap (k + 1) = multAt closure cap (k + 2) := by
  funext τ
  refine le_antisymm (multAt_mono (Nat.le_succ _) τ) ?_
  by_cases old : ∀ y ∈ typedAt closure (k + 2) τ, y.1 ⊆ stage k
  · have within : typedAt closure (k + 2) τ ⊆ typedAt closure (k + 1) τ := fun y found => by
      obtain ⟨inside, typed⟩ := mem_typedAt.mp found
      exact mem_typedAt.mpr ⟨mem_stage_succ.mpr (old y found), typed⟩
    exact min_le_min_left _ (Finset.card_le_card within)
  · push Not at old
    obtain ⟨y, found, notWithin⟩ := old
    obtain ⟨inside, typed⟩ := mem_typedAt.mp found
    obtain ⟨z, member, outside⟩ := Set.not_subset.mp notWithin
    have yInside : y.1 ⊆ stage (k + 1) := mem_stage_succ.mp inside
    let m : HF := memberOf y member
    have many := many_candidates loc positive same yInside (m := m) member outside
    rw [typed] at many
    simp only [multAt]
    omega

theorem multAt_stable (loc : IsCountLocal closure cap) (positive : 1 ≤ cap) {k : ℕ}
    (same : multAt closure cap k = multAt closure cap (k + 1)) (j : ℕ) :
    multAt closure cap (k + j) = multAt closure cap k := by
  have both : ∀ j, multAt closure cap (k + j) = multAt closure cap k ∧
      multAt closure cap (k + j) = multAt closure cap (k + j + 1) := by
    intro j
    induction j with
    | zero => exact ⟨rfl, same⟩
    | succ j ih => exact ⟨ih.2.symm.trans ih.1, multAt_succ_eq loc positive ih.2⟩
  exact (both j).1

/-- **A stable stage is rich.** -/
theorem rich_of_stable (loc : IsCountLocal closure cap) (positive : 1 ≤ cap) {k : ℕ}
    (same : multAt closure cap k = multAt closure cap (k + 1)) : Rich closure cap k := by
  intro τ family typed
  -- every member of the family lies in some stage; take one past all of them
  have bound : ∃ K, ∀ y ∈ family, y.1 ∈ stage K := by
    refine ⟨family.sup fun y => (exists_mem_stage y).choose, fun y found => ?_⟩
    exact stage_mono (Finset.le_sup (f := fun y => (exists_mem_stage y).choose) found) (exists_mem_stage y).choose_spec
  obtain ⟨K, inside⟩ := bound
  have within : family ⊆ typedAt closure (k + K) τ := fun y found =>
    mem_typedAt.mpr ⟨stage_mono (Nat.le_add_left K k) (inside y found), typed y found⟩
  have stable := congrFun (multAt_stable loc positive same K) τ
  have small := Finset.card_le_card within
  simp only [multAt] at stable
  omega

variable (closure cap) in
/-- **The stage by which every type has as many sets as it ever has**, up to one more than the cap. -/
def countedBound : ℕ := typeBound closure * (cap + 1)

theorem typedAt_eq_empty {k : ℕ} {τ : Finset (Formula 0)} (outside : τ ∉ closure.toFinset.powerset) :
    typedAt closure k τ = ∅ :=
  Finset.eq_empty_of_forall_notMem fun y found => outside
    (Finset.mem_powerset.mpr ((mem_typedAt.mp found).2 ▸ typeOf_subset closure y))

theorem exists_multStable_le : ∃ k ≤ countedBound closure cap, multAt closure cap k = multAt closure cap (k + 1) := by
  let total : ℕ → ℕ := fun k => ∑ τ ∈ closure.toFinset.powerset, multAt closure cap k τ
  have bounded : ∀ k, total k ≤ countedBound closure cap := fun k => by
    calc total k ≤ ∑ _τ ∈ closure.toFinset.powerset, (cap + 1) := Finset.sum_le_sum fun τ _ => min_le_left _ _
      _ = countedBound closure cap := by simp [countedBound, typeBound, mul_comm]
  by_contra none
  push Not at none
  have growing : ∀ k ≤ countedBound closure cap, total k < total (k + 1) := by
    intro k le
    obtain ⟨τ, differ⟩ := Function.ne_iff.mp (none k le)
    have inside : τ ∈ closure.toFinset.powerset := by
      by_contra outside
      simp [multAt, typedAt_eq_empty outside] at differ
    exact Finset.sum_lt_sum (fun σ _ => multAt_mono (Nat.le_succ k) σ)
      ⟨τ, inside, lt_of_le_of_ne (multAt_mono (Nat.le_succ k) τ) differ⟩
  have climb : ∀ k ≤ countedBound closure cap + 1, k ≤ total k := by
    intro k
    induction k with
    | zero => exact fun _ => Nat.zero_le _
    | succ k ih => exact fun le => Nat.succ_le_of_lt ((ih (by omega)).trans_lt (growing k (by omega)))
  have := (climb _ le_rfl).trans (bounded _)
  omega

/-- **The counted bound is a rich stage.** -/
theorem rich_countedBound (loc : IsCountLocal closure cap) (positive : 1 ≤ cap) :
    Rich closure cap (countedBound closure cap) := by
  obtain ⟨k, le, same⟩ := exists_multStable_le (closure := closure) (cap := cap)
  exact (rich_of_stable loc positive same).mono le

end Multiplicities

/-! ## Steps back and sorts by a rich stage -/

section Search

variable {closure : List (Formula 0)} {cap : ℕ}

theorem min_add_cap (cap a e : ℕ) : min cap (min cap a + e) = min cap (a + e) := by omega

/-- **A set containing `x` has the type of `x` with distinct representatives of its other members from a rich
stage.** -/
theorem exists_container_counted (loc : IsCountLocal closure cap) {k : ℕ} (rich : Rich closure cap k) {x z : HF}
    (member : x.1 ∈ z.1) :
    ∃ part, ∃ within : part ⊆ stage k, typeOf closure (insertStage x within) = typeOf closure z := by
  -- the other members of each type, and how many representatives they need
  let others : Finset (Formula 0) → Finset HF := fun ρ => (membersOfType closure z ρ).erase x
  have available : ∀ ρ, min cap (others ρ).card ≤ ((typedAt closure k ρ).erase x).card := by
    intro ρ
    have family := rich ρ (membersOfType closure z ρ) fun y found => (Finset.mem_filter.mp found).2
    by_cases typed : typeOf closure x = ρ
    · have xIn : x ∈ membersOfType closure z ρ := Finset.mem_filter.mpr ⟨mem_memberSet.mpr member, typed⟩
      have cardOthers := Finset.card_erase_of_mem xIn
      have cardBelow := Finset.pred_card_le_card_erase (s := typedAt closure k ρ) (a := x)
      have positive := Finset.card_pos.mpr ⟨x, xIn⟩
      simp only [others]
      omega
    · have xOut : x ∉ typedAt closure k ρ := fun found => typed (mem_typedAt.mp found).2
      have xOut' : x ∉ membersOfType closure z ρ := fun found => typed (Finset.mem_filter.mp found).2
      rw [Finset.erase_eq_of_notMem xOut]
      simp only [others, Finset.erase_eq_of_notMem xOut']
      omega
  let pick : Finset (Formula 0) → Finset HF := fun ρ => (Finset.exists_subset_card_eq (available ρ)).choose
  have pick_spec : ∀ ρ, pick ρ ⊆ (typedAt closure k ρ).erase x ∧ (pick ρ).card = min cap (others ρ).card := fun ρ =>
    (Finset.exists_subset_card_eq (available ρ)).choose_spec
  let parts : Finset HF := (memberTypeSet (closure := closure) z).biUnion pick
  have partsTyped : ∀ ρ, ∀ m ∈ pick ρ, m ∈ typedAt closure k ρ := fun ρ m found =>
    Finset.mem_of_mem_erase ((pick_spec ρ).1 found)
  have within : parts ⊆ stageSet k := fun m found => by
    obtain ⟨ρ, -, picked⟩ := Finset.mem_biUnion.mp found
    exact Finset.filter_subset _ _ (partsTyped ρ m picked)
  have xNotIn : x ∉ parts := fun found => by
    obtain ⟨ρ, -, picked⟩ := Finset.mem_biUnion.mp found
    exact (Finset.mem_erase.mp ((pick_spec ρ).1 picked)).1 rfl
  refine ⟨ofFinset (k := k) parts, ofFinset_subset parts, loc.typeOf_eq (funext fun ρ => ?_)⟩
  -- the members of the new container of type `ρ`: the picked ones, and `x` if it has type `ρ`
  have filterParts := filter_chosenUnion (y := z) (choice := pick) partsTyped ρ
  change min cap ((memberSet (insertStage x (ofFinset_subset (k := k) parts))).filter
      (fun m => typeOf closure m = ρ)).card = min cap (membersOfType closure z ρ).card
  rw [memberSet_insertStage x within, Finset.filter_insert]
  rw [show parts = chosenUnion (closure := closure) z pick from rfl, filterParts]
  by_cases typed : typeOf closure x = ρ
  · have found : ρ ∈ memberTypeSet (closure := closure) z :=
      Finset.mem_image.mpr ⟨x, mem_memberSet.mpr member, typed⟩
    have xIn : x ∈ membersOfType closure z ρ := Finset.mem_filter.mpr ⟨mem_memberSet.mpr member, typed⟩
    have xNotPicked : x ∉ pick ρ := fun picked => (Finset.mem_erase.mp ((pick_spec ρ).1 picked)).1 rfl
    rw [if_pos typed, if_pos found, Finset.card_insert_of_notMem xNotPicked, (pick_spec ρ).2,
      ← Finset.card_erase_add_one xIn]
    exact min_add_cap cap _ 1
  · rw [if_neg typed]
    have xOut : x ∉ membersOfType closure z ρ := fun found => typed (Finset.mem_filter.mp found).2
    split
    · rw [(pick_spec ρ).2]
      simp only [others, Finset.erase_eq_of_notMem xOut]
      omega
    · rename_i missing
      rw [membersOfType_eq_empty missing]

/-- **Some set of a rich stage has the type of any set.** -/
theorem exists_typed_in_stage {k : ℕ} (rich : Rich closure cap k) (y : HF) :
    ∃ y' : HF, y'.1 ∈ stage k ∧ typeOf closure y' = typeOf closure y := by
  have family := rich (typeOf closure y) {y} fun other found => by rw [Finset.mem_singleton.mp found]
  have positive : 0 < (typedAt closure k (typeOf closure y)).card := by
    simp only [Finset.card_singleton] at family
    omega
  obtain ⟨y', found⟩ := Finset.card_pos.mp positive
  exact ⟨y', (mem_typedAt.mp found).1, (mem_typedAt.mp found).2⟩

/-- **Some set containing `x` has a formula of a count-local closure exactly when `x` with some subset of a rich stage
has it.** -/
theorem sometimeBefore_iff_rich (loc : IsCountLocal closure cap) {k : ℕ} (rich : Rich closure cap k)
    {φ : Formula 0} (inside : φ ∈ closure) (label : StepLabel) (x : HF) :
    HFSets.sat Env.closed (.sometimeBefore label φ) x ↔
      memberLabel label ∧ ∃ part, ∃ within : part ⊆ stage k, HFSets.sat Env.closed φ (insertStage x within) := by
  constructor
  · rintro ⟨z, step, holds⟩
    obtain ⟨part, within, same⟩ := exists_container_counted loc rich step.2
    exact ⟨step.1, part, within, (sat_iff_of_typeOf_eq inside same).mpr holds⟩
  · rintro ⟨labelled, part, within, holds⟩
    exact ⟨insertStage x within, ⟨labelled, ZFSet.mem_insert_iff.mpr (Or.inl rfl)⟩, holds⟩

/-- **Every set containing `x` has a formula of a count-local closure exactly when `x` with every subset of a rich
stage has it.** -/
theorem alwaysBefore_iff_rich (loc : IsCountLocal closure cap) {k : ℕ} (rich : Rich closure cap k)
    {φ : Formula 0} (inside : φ ∈ closure) (label : StepLabel) (x : HF) :
    HFSets.sat Env.closed (.alwaysBefore label φ) x ↔
      (memberLabel label → ∀ part, ∀ within : part ⊆ stage k, HFSets.sat Env.closed φ (insertStage x within)) := by
  constructor
  · intro every labelled part within
    exact every (insertStage x within) ⟨labelled, ZFSet.mem_insert_iff.mpr (Or.inl rfl)⟩
  · intro every z step
    obtain ⟨part, within, same⟩ := exists_container_counted loc rich step.2
    exact (sat_iff_of_typeOf_eq inside same).mp (every step.1 part within)

/-- **Some set has a formula of the closure exactly when some set of a rich stage has it.** -/
theorem someOf_iff_rich {k : ℕ} (rich : Rich closure cap k) {φ : Formula 0} (inside : φ ∈ closure) (x : HF) :
    HFSets.sat Env.closed (.someOf (.base "Set") φ) x ↔ ∃ y : HF, y.1 ∈ stage k ∧ HFSets.sat Env.closed φ y := by
  constructor
  · rintro ⟨witness, -, holds⟩
    obtain ⟨y, found, same⟩ := exists_typed_in_stage rich witness
    exact ⟨y, found, (sat_iff_of_typeOf_eq inside same).mpr holds⟩
  · rintro ⟨y, -, holds⟩
    exact ⟨y, rfl, holds⟩

/-- **Every set has a formula of the closure exactly when every set of a rich stage has it.** -/
theorem everyOf_iff_rich {k : ℕ} (rich : Rich closure cap k) {φ : Formula 0} (inside : φ ∈ closure) (x : HF) :
    HFSets.sat Env.closed (.everyOf (.base "Set") φ) x ↔ ∀ y : HF, y.1 ∈ stage k → HFSets.sat Env.closed φ y := by
  constructor
  · intro every y _
    exact every y rfl
  · intro every witness _
    obtain ⟨y, found, same⟩ := exists_typed_in_stage rich witness
    exact (sat_iff_of_typeOf_eq inside same).mp (every y found)

end Search

end

end Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetReadings
