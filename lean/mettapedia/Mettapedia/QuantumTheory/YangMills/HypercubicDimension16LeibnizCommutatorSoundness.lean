import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16CommutatorRowEvaluation

/-!
# OUR soundness of the Leibniz-correct commutator row

Every Leibniz-correct covariant-commutator row vanishes on every gauge
background.  Write the commutator's field letter as
`X = D_{w₁} D_a D_b Z` with `Z = D_{w₂} F`.  Every other letter is the same in
all carriers of the row, so each carrier value is the contraction with only
the field's slot changed, and the row value is one contraction whose slot holds

`D_{w₁}(D_a D_b Z - D_b D_a Z) - ∑_{S ⊆ w₁} ((D_S F_ab)(D_{w₁∖S} Z) - (D_{w₁∖S} Z)(D_S F_ab))`.

The commutator identity `[D_a, D_b] Z = [F_ab, Z]` and the adjoint Leibniz rule
over subsets of the word `w₁` make that slot zero.

The proof identifies each letter as a covariant derivative along an ordered
list of positions.  The positions of the commutator's field are the outer ones,
the pair and the inner ones, in that order.  A curvature insertion retains all
positions but the pair, in the same order, and moves the positions of `S` to
the inserted letter.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Mettapedia.QuantumTheory.YangMills.HypercubicDimension16LeibnizCommutatorSoundness

open V14HypercubicFDCensus
open HypercubicRawFDDimension16Census
open HypercubicDimension16AlphaReduction
open HypercubicDimension16RelationEquivariance
open HypercubicDimension16CovariantCommutator
open HypercubicDimension16ContextualQuotient
open HypercubicDimension16ShuffleQuotient
open HypercubicDimension16TraceEvaluation
open HypercubicDimension16BackgroundCalculus
open HypercubicDimension16LeibnizCommutator
open HypercubicDimension16LeibnizJointRank
open HypercubicDimension16CommutatorRowEvaluation

/-! ## Strictly increasing position lists -/

instance finLtIrrefl {d : ℕ} : Std.Irrefl (fun a b : Fin d => a < b) :=
  ⟨fun a => lt_irrefl a⟩

instance finLtAntisymm {d : ℕ} : Std.Antisymm (fun a b : Fin d => a < b) :=
  ⟨fun a _ hab hba => absurd (lt_trans hab hba) (lt_irrefl a)⟩

/-- Two strictly increasing lists of positions with the same members are
equal. -/
theorem eq_of_pairwise_lt_of_mem_iff {d : ℕ} {first second : List (Fin d)}
    (hfirst : first.Pairwise (· < ·)) (hsecond : second.Pairwise (· < ·))
    (hmem : ∀ position, position ∈ first ↔ position ∈ second) :
    first = second :=
  List.Pairwise.eq_of_mem_iff hfirst hsecond hmem

variable {S : Type*} [CommRing S] [Algebra ℚ S]

/-! ## Covariant derivatives along a list of positions -/

theorem covDeriv_mul (bg : GaugeBackground S) (μ : Fin 4) (X Y : Mat S) :
    bg.covDeriv μ (X * Y) = bg.covDeriv μ X * Y + X * bg.covDeriv μ Y := by
  unfold GaugeBackground.covDeriv
  rw [DifferentialScalars.mderiv_mul]
  noncomm_ring

/-- The covariant derivative as an additive map. -/
def covDerivHom (bg : GaugeBackground S) (μ : Fin 4) : Mat S →+ Mat S where
  toFun := bg.covDeriv μ
  map_zero' := bg.covDeriv_zero μ
  map_add' := bg.covDeriv_add μ

/-- OUR covariant derivatives at a list of positions, the first outermost. -/
def wordFold (bg : GaugeBackground S) {d : ℕ} (axis : Fin d → Fin 4) :
    List (Fin d) → Mat S →+ Mat S
  | [] => AddMonoidHom.id _
  | position :: rest => (covDerivHom bg (axis position)).comp (wordFold bg axis rest)

@[simp] theorem wordFold_nil (bg : GaugeBackground S) {d : ℕ} (axis : Fin d → Fin 4)
    (M : Mat S) : wordFold bg axis [] M = M :=
  rfl

@[simp] theorem wordFold_cons (bg : GaugeBackground S) {d : ℕ} (axis : Fin d → Fin 4)
    (position : Fin d) (rest : List (Fin d)) (M : Mat S) :
    wordFold bg axis (position :: rest) M =
      bg.covDeriv (axis position) (wordFold bg axis rest M) :=
  rfl

theorem wordFold_append (bg : GaugeBackground S) {d : ℕ} (axis : Fin d → Fin 4)
    (first second : List (Fin d)) (M : Mat S) :
    wordFold bg axis (first ++ second) M =
      wordFold bg axis first (wordFold bg axis second M) := by
  induction first with
  | nil => rfl
  | cons position rest ih => simp [ih]

theorem wordFold_congr (bg : GaugeBackground S) {d : ℕ} {axis axis' : Fin d → Fin 4}
    (positions : List (Fin d))
    (haxis : ∀ position ∈ positions, axis position = axis' position) (M : Mat S) :
    wordFold bg axis positions M = wordFold bg axis' positions M := by
  induction positions with
  | nil => rfl
  | cons position rest ih =>
      simp only [wordFold_cons]
      rw [haxis position List.mem_cons_self,
        ih (fun other hother => haxis other (List.mem_cons_of_mem _ hother))]

theorem wordFold_map (bg : GaugeBackground S) {d d' : ℕ} (f : Fin d' → Fin d)
    (axis : Fin d → Fin 4) (positions : List (Fin d')) (M : Mat S) :
    wordFold bg (fun position => axis (f position)) positions M =
      wordFold bg axis (positions.map f) M := by
  induction positions with
  | nil => rfl
  | cons position rest ih => simp [ih]

theorem foldr_eq_wordFold (bg : GaugeBackground S) {d : ℕ} (axis : Fin d → Fin 4)
    (positions : List (Fin d)) (M : Mat S) :
    (positions.map axis).foldr (fun a matrix => bg.covDeriv a matrix) M =
      wordFold bg axis positions M := by
  induction positions with
  | nil => rfl
  | cons position rest ih => simp [ih]

/-! ## The adjoint Leibniz rule over subsets of a word -/

theorem insert_injOn_powerset {d : ℕ} (position : Fin d) (base : Finset (Fin d))
    (hposition : position ∉ base) :
    Set.InjOn (insert position) (base.powerset : Set (Finset (Fin d))) := by
  intro first hfirst second hsecond hequal
  have hfirst' : position ∉ first := fun h =>
    hposition (Finset.mem_powerset.mp hfirst h)
  have hsecond' : position ∉ second := fun h =>
    hposition (Finset.mem_powerset.mp hsecond h)
  have := congrArg (fun set : Finset (Fin d) => set.erase position) hequal
  simpa [Finset.erase_insert hfirst', Finset.erase_insert hsecond'] using this

theorem disjoint_powerset_image_insert {d : ℕ} (position : Fin d) (base : Finset (Fin d))
    (hposition : position ∉ base) :
    Disjoint base.powerset (base.powerset.image (insert position)) := by
  rw [Finset.disjoint_left]
  intro set hset hsetImage
  obtain ⟨other, _, rfl⟩ := Finset.mem_image.mp hsetImage
  exact hposition (Finset.mem_powerset.mp hset (Finset.mem_insert_self _ _))

theorem filter_mem_insert_eq {d : ℕ} (position : Fin d) (rest : List (Fin d))
    (hposition : position ∉ rest) (set : Finset (Fin d)) :
    rest.filter (fun q => q ∈ insert position set) = rest.filter (fun q => q ∈ set) := by
  apply List.filter_congr
  intro q hq
  have hqp : q ≠ position := fun h => hposition (h ▸ hq)
  simp [Finset.mem_insert, hqp]

theorem filter_not_mem_insert_eq {d : ℕ} (position : Fin d) (rest : List (Fin d))
    (hposition : position ∉ rest) (set : Finset (Fin d)) :
    rest.filter (fun q => q ∉ insert position set) = rest.filter (fun q => q ∉ set) := by
  apply List.filter_congr
  intro q hq
  have hqp : q ≠ position := fun h => hposition (h ▸ hq)
  simp [Finset.mem_insert, hqp]

/-- OUR adjoint Leibniz rule: derivatives at distinct positions distribute over
a product, the left factor taking the positions of each subset. -/
theorem wordFold_mul (bg : GaugeBackground S) {d : ℕ} (axis : Fin d → Fin 4)
    (word : List (Fin d)) (hword : word.Nodup) (A B : Mat S) :
    wordFold bg axis word (A * B) =
      ∑ set ∈ word.toFinset.powerset,
        wordFold bg axis (word.filter (fun q => q ∈ set)) A *
          wordFold bg axis (word.filter (fun q => q ∉ set)) B := by
  induction word with
  | nil => simp
  | cons position rest ih =>
      rw [List.nodup_cons] at hword
      obtain ⟨hposition, hrest⟩ := hword
      have hbase : position ∉ rest.toFinset := fun h =>
        hposition (List.mem_toFinset.mp h)
      have hnotin : ∀ set ∈ rest.toFinset.powerset, position ∉ set := fun set hset h =>
        hbase (Finset.mem_powerset.mp hset h)
      rw [List.toFinset_cons, Finset.powerset_insert,
        Finset.sum_union (disjoint_powerset_image_insert position _ hbase),
        Finset.sum_image (insert_injOn_powerset position _ hbase)]
      have hwithout : ∀ set ∈ rest.toFinset.powerset,
          wordFold bg axis ((position :: rest).filter (fun q => q ∈ set)) A *
              wordFold bg axis ((position :: rest).filter (fun q => q ∉ set)) B =
            wordFold bg axis (rest.filter (fun q => q ∈ set)) A *
              bg.covDeriv (axis position)
                (wordFold bg axis (rest.filter (fun q => q ∉ set)) B) := by
        intro set hset
        rw [List.filter_cons_of_neg (by simp [hnotin set hset]),
          List.filter_cons_of_pos (by simp [hnotin set hset]), wordFold_cons]
      have hwith : ∀ set ∈ rest.toFinset.powerset,
          wordFold bg axis ((position :: rest).filter (fun q => q ∈ insert position set)) A *
              wordFold bg axis
                ((position :: rest).filter (fun q => q ∉ insert position set)) B =
            bg.covDeriv (axis position)
                (wordFold bg axis (rest.filter (fun q => q ∈ set)) A) *
              wordFold bg axis (rest.filter (fun q => q ∉ set)) B := by
        intro set _
        rw [List.filter_cons_of_pos (by simp), List.filter_cons_of_neg (by simp),
          filter_mem_insert_eq position rest hposition set,
          filter_not_mem_insert_eq position rest hposition set, wordFold_cons]
      rw [Finset.sum_congr rfl hwithout, Finset.sum_congr rfl hwith,
        wordFold_cons, ih hrest]
      change covDerivHom bg (axis position) _ = _
      rw [map_sum]
      simp only [covDerivHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk, covDeriv_mul]
      rw [Finset.sum_add_distrib, add_comm]

/-- OUR adjoint Leibniz rule with the right factor taking the positions of each
subset. -/
theorem wordFold_mul' (bg : GaugeBackground S) {d : ℕ} (axis : Fin d → Fin 4)
    (word : List (Fin d)) (hword : word.Nodup) (A B : Mat S) :
    wordFold bg axis word (A * B) =
      ∑ set ∈ word.toFinset.powerset,
        wordFold bg axis (word.filter (fun q => q ∉ set)) A *
          wordFold bg axis (word.filter (fun q => q ∈ set)) B := by
  induction word with
  | nil => simp
  | cons position rest ih =>
      rw [List.nodup_cons] at hword
      obtain ⟨hposition, hrest⟩ := hword
      have hbase : position ∉ rest.toFinset := fun h =>
        hposition (List.mem_toFinset.mp h)
      have hnotin : ∀ set ∈ rest.toFinset.powerset, position ∉ set := fun set hset h =>
        hbase (Finset.mem_powerset.mp hset h)
      rw [List.toFinset_cons, Finset.powerset_insert,
        Finset.sum_union (disjoint_powerset_image_insert position _ hbase),
        Finset.sum_image (insert_injOn_powerset position _ hbase)]
      have hwithout : ∀ set ∈ rest.toFinset.powerset,
          wordFold bg axis ((position :: rest).filter (fun q => q ∉ set)) A *
              wordFold bg axis ((position :: rest).filter (fun q => q ∈ set)) B =
            bg.covDeriv (axis position)
                (wordFold bg axis (rest.filter (fun q => q ∉ set)) A) *
              wordFold bg axis (rest.filter (fun q => q ∈ set)) B := by
        intro set hset
        rw [List.filter_cons_of_pos (by simp [hnotin set hset]),
          List.filter_cons_of_neg (by simp [hnotin set hset]), wordFold_cons]
      have hwith : ∀ set ∈ rest.toFinset.powerset,
          wordFold bg axis
                ((position :: rest).filter (fun q => q ∉ insert position set)) A *
              wordFold bg axis ((position :: rest).filter (fun q => q ∈ insert position set)) B =
            wordFold bg axis (rest.filter (fun q => q ∉ set)) A *
              bg.covDeriv (axis position)
                (wordFold bg axis (rest.filter (fun q => q ∈ set)) B) := by
        intro set _
        rw [List.filter_cons_of_neg (by simp), List.filter_cons_of_pos (by simp),
          filter_mem_insert_eq position rest hposition set,
          filter_not_mem_insert_eq position rest hposition set, wordFold_cons]
      rw [Finset.sum_congr rfl hwithout, Finset.sum_congr rfl hwith,
        wordFold_cons, ih hrest]
      change covDerivHom bg (axis position) _ = _
      rw [map_sum]
      simp only [covDerivHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk, covDeriv_mul]
      rw [Finset.sum_add_distrib]

/-! ## The contraction as an additive function of one slot -/

/-- OUR contraction with the matrix at one label replaced. -/
def slotContraction {n : ℕ} (X : Fin n → Mat S) (σ : Equiv.Perm (Fin n)) (slot : Fin n) :
    Mat S →+ S where
  toFun Y := tracePermutationContraction (Function.update X slot Y) σ
  map_zero' := by
    unfold tracePermutationContraction
    apply Finset.sum_eq_zero
    intro state _
    exact Finset.prod_eq_zero (Finset.mem_univ slot) (by simp)
  map_add' Y Z := contraction_update_add X σ slot Y Z

theorem slotContraction_apply {n : ℕ} (X : Fin n → Mat S) (σ : Equiv.Perm (Fin n))
    (slot : Fin n) (Y : Mat S) :
    slotContraction X σ slot Y = tracePermutationContraction (Function.update X slot Y) σ :=
  rfl

/-! ## Letters as covariant derivatives along positions -/

theorem ownerAxisProjection_map_pair {d fieldCount : ℕ} (owner : Fin d → Fin fieldCount)
    (axis : Fin d → Fin 4) (field : Fin fieldCount) (positions : List (Fin d)) :
    ownerAxisProjection field (positions.map fun position => (owner position, axis position)) =
      (positions.filter fun position => owner position = field).map axis := by
  induction positions with
  | nil => rfl
  | cons position rest ih =>
      by_cases howner : owner position = field
      · simp [ownerAxisProjection_cons, howner, ih]
      · simp [ownerAxisProjection_cons, howner, ih]

theorem letterMatrix_eq_wordFold (bg : GaugeBackground S) {fieldCount d : ℕ}
    (sector : DerivativeAlphaReducedSector fieldCount d) (field : Fin fieldCount) :
    letterMatrix bg sector field =
      wordFold bg sector.derivativeWord.axisAtPosition
        ((List.finRange d).filter fun position =>
          sector.derivativeWord.ownerAtPosition position = field)
        (bg.curvature (sector.fieldFirst field) (sector.fieldSecond field)) := by
  unfold letterMatrix
  change (ownerAxisProjection field (sectorGlobalWord sector).toList).foldr _ _ = _
  rw [sectorGlobalWord_toList, List.ofFn_eq_map, ownerAxisProjection_map_pair,
    foldr_eq_wordFold]

/-! ## The positions of a commutator site -/

section Site

variable {carrier : RelationCarrier} (site : CovariantCommutatorSite carrier)

/-- OUR outer positions of the commutator's field, in order. -/
def outerPositionList : List (Fin (dimension16DerivativeCount carrier.1)) :=
  (List.finRange _).filter fun position => position ∈ outerSameOwnerPositions site

/-- OUR inner positions of the commutator's field, in order. -/
def innerPositionList : List (Fin (dimension16DerivativeCount carrier.1)) :=
  (List.finRange _).filter fun position =>
    site.inner < position ∧ carrier.2.derivativeWord.ownerAtPosition position = site.field

theorem mem_outerPositionList (position : Fin (dimension16DerivativeCount carrier.1)) :
    position ∈ outerPositionList site ↔
      position < site.outer ∧
        carrier.2.derivativeWord.ownerAtPosition position = site.field := by
  simp [outerPositionList]

theorem mem_innerPositionList (position : Fin (dimension16DerivativeCount carrier.1)) :
    position ∈ innerPositionList site ↔
      site.inner < position ∧
        carrier.2.derivativeWord.ownerAtPosition position = site.field := by
  simp [innerPositionList]

theorem outerPositionList_nodup : (outerPositionList site).Nodup :=
  (List.nodup_finRange _).filter _

theorem outerPositionList_toFinset :
    (outerPositionList site).toFinset = outerSameOwnerPositions site := by
  ext position
  simp [outerPositionList]

theorem outerPositionList_pairwise : (outerPositionList site).Pairwise (· < ·) :=
  (List.pairwise_lt_finRange _).filter _

theorem innerPositionList_pairwise : (innerPositionList site).Pairwise (· < ·) :=
  (List.pairwise_lt_finRange _).filter _

/-- The positions of the commutator's field are its outer positions, the pair,
and its inner positions, in that order. -/
theorem fieldPositions_decompose :
    (List.finRange _).filter (fun position =>
        carrier.2.derivativeWord.ownerAtPosition position = site.field) =
      outerPositionList site ++ site.outer :: site.inner :: innerPositionList site := by
  apply eq_of_pairwise_lt_of_mem_iff
  · exact (List.pairwise_lt_finRange _).filter _
  · rw [List.pairwise_append]
    refine ⟨outerPositionList_pairwise site, ?_, ?_⟩
    · rw [List.pairwise_cons, List.pairwise_cons]
      refine ⟨?_, ?_, innerPositionList_pairwise site⟩
      · intro other hother
        rcases List.mem_cons.mp hother with rfl | hother
        · exact site.outer_lt_inner
        · exact lt_trans site.outer_lt_inner ((mem_innerPositionList site other).mp hother).1
      · intro other hother
        exact ((mem_innerPositionList site other).mp hother).1
    · intro first hfirst second hsecond
      have hfirstLt := ((mem_outerPositionList site first).mp hfirst).1
      rcases List.mem_cons.mp hsecond with rfl | hsecond
      · exact hfirstLt
      rcases List.mem_cons.mp hsecond with rfl | hsecond
      · exact lt_trans hfirstLt site.outer_lt_inner
      · exact lt_trans hfirstLt (lt_trans site.outer_lt_inner
          ((mem_innerPositionList site second).mp hsecond).1)
  · intro position
    simp only [List.mem_filter, List.mem_finRange, true_and, decide_eq_true_eq,
      List.mem_append, List.mem_cons, mem_outerPositionList, mem_innerPositionList]
    constructor
    · intro howner
      rcases lt_trichotomy position site.outer with hlt | heq | hgt
      · exact Or.inl ⟨hlt, howner⟩
      · exact Or.inr (Or.inl heq)
      · rcases lt_trichotomy position site.inner with hlt' | heq' | hgt'
        · exact absurd howner (site.no_same_owner_between position hgt hlt')
        · exact Or.inr (Or.inr (Or.inl heq'))
        · exact Or.inr (Or.inr (Or.inr ⟨hgt', howner⟩))
    · rintro (⟨_, howner⟩ | rfl | rfl | ⟨_, howner⟩)
      · exact howner
      · exact site.owner_outer
      · exact site.owner_inner
      · exact howner

/-- OUR inner part of the commutator's field letter. -/
def innerLetter (bg : GaugeBackground S) : Mat S :=
  wordFold bg carrier.2.derivativeWord.axisAtPosition (innerPositionList site)
    (bg.curvature (carrier.2.fieldFirst site.field) (carrier.2.fieldSecond site.field))

theorem letterMatrix_site_field (bg : GaugeBackground S) :
    letterMatrix bg carrier.2 site.field =
      wordFold bg carrier.2.derivativeWord.axisAtPosition (outerPositionList site)
        (bg.covDeriv (carrier.2.derivativeWord.axisAtPosition site.outer)
          (bg.covDeriv (carrier.2.derivativeWord.axisAtPosition site.inner)
            (innerLetter site bg))) := by
  rw [letterMatrix_eq_wordFold, fieldPositions_decompose, wordFold_append,
    wordFold_cons, wordFold_cons]
  rfl

/-! ## The swapped carrier -/

theorem owner_swap (position : Fin (dimension16DerivativeCount carrier.1)) :
    carrier.2.derivativeWord.ownerAtPosition (Equiv.swap site.outer site.inner position) =
      carrier.2.derivativeWord.ownerAtPosition position := by
  rcases eq_or_ne position site.outer with rfl | hout
  · rw [Equiv.swap_apply_left, site.owner_inner, site.owner_outer]
  rcases eq_or_ne position site.inner with rfl | hin
  · rw [Equiv.swap_apply_right, site.owner_outer, site.owner_inner]
  · rw [Equiv.swap_apply_of_ne_of_ne hout hin]

theorem letterMatrix_swap_eq (bg : GaugeBackground S) (field : Fin carrier.1.1) :
    letterMatrix bg (swapExactDerivativePositions carrier site.outer site.inner).2 field =
      wordFold bg
        (fun position => carrier.2.derivativeWord.axisAtPosition
          (Equiv.swap site.outer site.inner position))
        ((List.finRange _).filter fun position =>
          carrier.2.derivativeWord.ownerAtPosition position = field)
        (bg.curvature (carrier.2.fieldFirst field) (carrier.2.fieldSecond field)) := by
  refine (letterMatrix_eq_wordFold bg _ _).trans ?_
  have hfilter :
      ((List.finRange (dimension16DerivativeCount carrier.1)).filter fun position =>
          carrier.2.derivativeWord.ownerAtPosition
            (Equiv.swap site.outer site.inner position) = field) =
        (List.finRange _).filter fun position =>
          carrier.2.derivativeWord.ownerAtPosition position = field :=
    List.filter_congr (fun position _ => by rw [owner_swap site position])
  exact congrArg (fun positions => wordFold bg _ positions _) hfilter

theorem letterMatrix_swap_of_ne (bg : GaugeBackground S) (field : Fin carrier.1.1)
    (hfield : field ≠ site.field) :
    letterMatrix bg (swapExactDerivativePositions carrier site.outer site.inner).2 field =
      letterMatrix bg carrier.2 field := by
  refine (letterMatrix_swap_eq site bg field).trans ?_
  refine Eq.trans ?_ (letterMatrix_eq_wordFold bg carrier.2 field).symm
  apply wordFold_congr
  intro position hposition
  have howner : carrier.2.derivativeWord.ownerAtPosition position = field := by
    simpa using hposition
  have hout : position ≠ site.outer := by
    rintro rfl
    exact hfield (howner.symm.trans site.owner_outer)
  have hin : position ≠ site.inner := by
    rintro rfl
    exact hfield (howner.symm.trans site.owner_inner)
  rw [Equiv.swap_apply_of_ne_of_ne hout hin]

theorem letterMatrix_swap_field (bg : GaugeBackground S) :
    letterMatrix bg (swapExactDerivativePositions carrier site.outer site.inner).2 site.field =
      wordFold bg carrier.2.derivativeWord.axisAtPosition (outerPositionList site)
        (bg.covDeriv (carrier.2.derivativeWord.axisAtPosition site.inner)
          (bg.covDeriv (carrier.2.derivativeWord.axisAtPosition site.outer)
            (innerLetter site bg))) := by
  refine (letterMatrix_swap_eq site bg site.field).trans ?_
  rw [fieldPositions_decompose, wordFold_append,
    wordFold_cons, wordFold_cons, Equiv.swap_apply_left, Equiv.swap_apply_right]
  have houter : ∀ position ∈ outerPositionList site,
      carrier.2.derivativeWord.axisAtPosition (Equiv.swap site.outer site.inner position) =
        carrier.2.derivativeWord.axisAtPosition position := by
    intro position hposition
    have hlt := ((mem_outerPositionList site position).mp hposition).1
    rw [Equiv.swap_apply_of_ne_of_ne (ne_of_lt hlt)
      (ne_of_lt (lt_trans hlt site.outer_lt_inner))]
  have hinner : ∀ position ∈ innerPositionList site,
      carrier.2.derivativeWord.axisAtPosition (Equiv.swap site.outer site.inner position) =
        carrier.2.derivativeWord.axisAtPosition position := by
    intro position hposition
    have hgt := ((mem_innerPositionList site position).mp hposition).1
    rw [Equiv.swap_apply_of_ne_of_ne (ne_of_gt (lt_trans site.outer_lt_inner hgt))
      (ne_of_gt hgt)]
  rw [wordFold_congr bg _ houter, wordFold_congr bg _ hinner]
  rfl

/-! ## The inserted carriers -/

/-- The retained positions, in order, are the retained-order embedding of all
positions of the inserted carrier. -/
theorem retained_map_eq_filter :
    (List.finRange _).map (retainedDerivativeOrderEmbedding site) =
      (List.finRange _).filter fun position =>
        position ∈ retainedDerivativePositions site.outer site.inner := by
  apply eq_of_pairwise_lt_of_mem_iff
  · rw [List.pairwise_map]
    exact (List.pairwise_lt_finRange _).imp
      (fun hlt => (retainedDerivativeOrderEmbedding site).strictMono hlt)
  · exact (List.pairwise_lt_finRange _).filter _
  · intro position
    simp only [List.mem_map, List.mem_finRange, true_and, List.mem_filter,
      decide_eq_true_eq]
    constructor
    · rintro ⟨index, rfl⟩
      exact retainedDerivativeOrderEmbedding_mem site index
    · intro hposition
      have hrange : position ∈ Set.range (retainedDerivativeOrderEmbedding site) := by
        unfold retainedDerivativeOrderEmbedding
        rw [Finset.range_orderEmbOfFin]
        exact hposition
      exact hrange

theorem map_filter_comp {α β : Type*} (f : α → β) (P : β → Bool) (L : List α) :
    (L.filter (fun a => P (f a))).map f = (L.map f).filter P := by
  rw [List.filter_map]
  rfl

/-- OUR owner of a source position after a Leibniz insertion moving `moved`. -/
def insertedOwner (moved : Finset (Fin (dimension16DerivativeCount carrier.1)))
    (position : Fin (dimension16DerivativeCount carrier.1)) : Fin (carrier.1.1 + 1) :=
  if position ∈ moved then Fin.last carrier.1.1
  else Fin.castSucc (carrier.2.derivativeWord.ownerAtPosition position)

theorem letterMatrix_insert_eq (bg : GaugeBackground S) (side : CurvatureInsertionSide)
    (moved : Finset (Fin (dimension16DerivativeCount carrier.1)))
    (field : Fin (carrier.1.1 + 1)) :
    letterMatrix bg (insertLeibnizCarrier site side moved).2 field =
      wordFold bg carrier.2.derivativeWord.axisAtPosition
        ((List.finRange _).filter fun position =>
          position ∈ retainedDerivativePositions site.outer site.inner ∧
            insertedOwner moved position = field)
        (bg.curvature
          (Fin.lastCases (carrier.2.derivativeWord.axisAtPosition site.outer)
            carrier.2.fieldFirst field)
          (Fin.lastCases (carrier.2.derivativeWord.axisAtPosition site.inner)
            carrier.2.fieldSecond field)) := by
  refine (letterMatrix_eq_wordFold bg _ _).trans ?_
  change wordFold bg
      (fun position => carrier.2.derivativeWord.axisAtPosition
        (retainedDerivativeOrderEmbedding site position))
      ((List.finRange _).filter fun position =>
        insertedOwner moved (retainedDerivativeOrderEmbedding site position) = field) _ = _
  rw [wordFold_map, map_filter_comp (retainedDerivativeOrderEmbedding site)
      (fun position => decide (insertedOwner moved position = field)),
    retained_map_eq_filter, List.filter_filter]
  congr 2
  apply List.filter_congr
  intro position _
  simp [Bool.and_comm]

theorem insertedOwner_eq_last (moved : Finset (Fin (dimension16DerivativeCount carrier.1)))
    (position : Fin (dimension16DerivativeCount carrier.1)) :
    insertedOwner moved position = Fin.last carrier.1.1 ↔ position ∈ moved := by
  unfold insertedOwner
  by_cases hposition : position ∈ moved
  · simp [hposition]
  · simp only [hposition, ↓reduceIte, iff_false]
    exact Fin.castSucc_ne_last _

theorem insertedOwner_eq_castSucc
    (moved : Finset (Fin (dimension16DerivativeCount carrier.1)))
    (position : Fin (dimension16DerivativeCount carrier.1)) (field : Fin carrier.1.1) :
    insertedOwner moved position = Fin.castSucc field ↔
      position ∉ moved ∧ carrier.2.derivativeWord.ownerAtPosition position = field := by
  unfold insertedOwner
  by_cases hposition : position ∈ moved
  · simp only [hposition, ↓reduceIte, not_true_eq_false, false_and, iff_false]
    exact fun h => Fin.castSucc_ne_last field h.symm
  · simp [hposition, Fin.castSucc_inj]

section Moved

variable (moved : Finset (Fin (dimension16DerivativeCount carrier.1)))
  (hmoved : moved ⊆ outerSameOwnerPositions site)

include hmoved in
theorem letterMatrix_insert_last (bg : GaugeBackground S) (side : CurvatureInsertionSide) :
    letterMatrix bg (insertLeibnizCarrier site side moved).2 (Fin.last carrier.1.1) =
      wordFold bg carrier.2.derivativeWord.axisAtPosition
        ((outerPositionList site).filter fun position => position ∈ moved)
        (bg.curvature (carrier.2.derivativeWord.axisAtPosition site.outer)
          (carrier.2.derivativeWord.axisAtPosition site.inner)) := by
  refine (letterMatrix_insert_eq site bg side moved (Fin.last carrier.1.1)).trans ?_
  rw [Fin.lastCases_last, Fin.lastCases_last]
  congr 2
  unfold outerPositionList
  rw [List.filter_filter]
  apply List.filter_congr
  intro position _
  have hretained : position ∈ moved →
      position ∈ retainedDerivativePositions site.outer site.inner := fun h =>
    outerSameOwnerPositions_subset_retained site (hmoved h)
  by_cases hposition : position ∈ moved
  · simp [hposition, hretained hposition, insertedOwner_eq_last, hmoved hposition]
  · simp [hposition, insertedOwner_eq_last]

include hmoved in
theorem letterMatrix_insert_field (bg : GaugeBackground S) (side : CurvatureInsertionSide) :
    letterMatrix bg (insertLeibnizCarrier site side moved).2 (Fin.castSucc site.field) =
      wordFold bg carrier.2.derivativeWord.axisAtPosition
        ((outerPositionList site).filter fun position => position ∉ moved)
        (innerLetter site bg) := by
  refine (letterMatrix_insert_eq site bg side moved (Fin.castSucc site.field)).trans ?_
  rw [Fin.lastCases_castSucc, Fin.lastCases_castSucc]
  have hpositions :
      ((List.finRange (dimension16DerivativeCount carrier.1)).filter fun position =>
          position ∈ retainedDerivativePositions site.outer site.inner ∧
            insertedOwner moved position = Fin.castSucc site.field) =
        (outerPositionList site).filter (fun position => position ∉ moved) ++
          innerPositionList site := by
    apply eq_of_pairwise_lt_of_mem_iff
    · exact (List.pairwise_lt_finRange _).filter _
    · rw [List.pairwise_append]
      refine ⟨(outerPositionList_pairwise site).filter _, innerPositionList_pairwise site, ?_⟩
      intro first hfirst second hsecond
      have hfirstLt := ((mem_outerPositionList site first).mp (List.mem_of_mem_filter hfirst)).1
      exact lt_trans hfirstLt (lt_trans site.outer_lt_inner
        ((mem_innerPositionList site second).mp hsecond).1)
    · intro position
      simp only [List.mem_filter, List.mem_finRange, true_and, decide_eq_true_eq,
        List.mem_append, mem_outerPositionList, mem_innerPositionList,
        insertedOwner_eq_castSucc, retainedDerivativePositions, Finset.mem_erase,
        Finset.mem_univ, and_true]
      constructor
      · rintro ⟨⟨hin, hout⟩, hnot, howner⟩
        rcases lt_trichotomy position site.outer with hlt | heq | hgt
        · exact Or.inl ⟨⟨hlt, howner⟩, hnot⟩
        · exact absurd heq hout
        · rcases lt_trichotomy position site.inner with hlt' | heq' | hgt'
          · exact absurd howner (site.no_same_owner_between position hgt hlt')
          · exact absurd heq' hin
          · exact Or.inr ⟨hgt', howner⟩
      · rintro (⟨⟨hlt, howner⟩, hnot⟩ | ⟨hgt, howner⟩)
        · exact ⟨⟨ne_of_lt (lt_trans hlt site.outer_lt_inner), ne_of_lt hlt⟩, hnot, howner⟩
        · have hnot : position ∉ moved := fun h =>
            absurd (lt_trans site.outer_lt_inner hgt)
              (not_lt.mpr (le_of_lt ((mem_outerSameOwnerPositions site position).mp
                (hmoved h)).1))
          exact ⟨⟨ne_of_gt hgt, ne_of_gt (lt_trans site.outer_lt_inner hgt)⟩, hnot, howner⟩
  rw [hpositions, wordFold_append]
  rfl

include hmoved in
theorem letterMatrix_insert_of_ne (bg : GaugeBackground S) (side : CurvatureInsertionSide)
    (field : Fin carrier.1.1) (hfield : field ≠ site.field) :
    letterMatrix bg (insertLeibnizCarrier site side moved).2 (Fin.castSucc field) =
      letterMatrix bg carrier.2 field := by
  refine (letterMatrix_insert_eq site bg side moved (Fin.castSucc field)).trans ?_
  refine Eq.trans ?_ (letterMatrix_eq_wordFold bg carrier.2 field).symm
  rw [Fin.lastCases_castSucc, Fin.lastCases_castSucc]
  congr 2
  apply List.filter_congr
  intro position _
  simp only [insertedOwner_eq_castSucc, retainedDerivativePositions, Finset.mem_erase,
    Finset.mem_univ, and_true, decide_eq_decide]
  constructor
  · rintro ⟨_, _, howner⟩
    exact howner
  · intro howner
    refine ⟨⟨?_, ?_⟩, ?_, howner⟩
    · rintro rfl
      exact hfield (howner.symm.trans site.owner_inner)
    · rintro rfl
      exact hfield (howner.symm.trans site.owner_outer)
    · intro hmem
      exact hfield (howner.symm.trans ((mem_outerSameOwnerPositions site position).mp
        (hmoved hmem)).2)

include hmoved in
/-- OUR letters of a Leibniz insertion: the source letters with the field's
slot replaced, followed by the inserted curvature with the moved derivatives. -/
theorem letterMatrix_insert (bg : GaugeBackground S) (side : CurvatureInsertionSide) :
    letterMatrix bg (insertLeibnizCarrier site side moved).2 =
      (Fin.snoc
        (Function.update (letterMatrix bg carrier.2) site.field
          (wordFold bg carrier.2.derivativeWord.axisAtPosition
            ((outerPositionList site).filter fun position => position ∉ moved)
            (innerLetter site bg)))
        (wordFold bg carrier.2.derivativeWord.axisAtPosition
          ((outerPositionList site).filter fun position => position ∈ moved)
          (bg.curvature (carrier.2.derivativeWord.axisAtPosition site.outer)
            (carrier.2.derivativeWord.axisAtPosition site.inner))) :
        Fin (carrier.1.1 + 1) → Mat S) := by
  funext field
  refine Fin.lastCases ?_ (fun index => ?_) field
  · rw [Fin.snoc_last]
    exact letterMatrix_insert_last site moved hmoved bg side
  · rw [Fin.snoc_castSucc]
    by_cases hindex : index = site.field
    · subst index
      rw [Function.update_self]
      exact letterMatrix_insert_field site moved hmoved bg side
    · rw [Function.update_of_ne hindex]
      exact letterMatrix_insert_of_ne site moved hmoved bg side index hindex

end Moved

/-! ## Values of the carriers of the row -/

theorem carrierValue_source (bg : GaugeBackground S) :
    carrierValue bg carrier =
      slotContraction (letterMatrix bg carrier.2) carrier.2.trace.traceOrder site.field
        (letterMatrix bg carrier.2 site.field) := by
  rw [slotContraction_apply, Function.update_eq_self]
  rfl

theorem carrierValue_swap (bg : GaugeBackground S) :
    carrierValue bg (swapExactDerivativePositions carrier site.outer site.inner) =
      slotContraction (letterMatrix bg carrier.2) carrier.2.trace.traceOrder site.field
        (letterMatrix bg (swapExactDerivativePositions carrier site.outer site.inner).2
          site.field) := by
  rw [slotContraction_apply]
  have hletters :
      letterMatrix bg (swapExactDerivativePositions carrier site.outer site.inner).2 =
        Function.update (letterMatrix bg carrier.2) site.field
          (letterMatrix bg (swapExactDerivativePositions carrier site.outer site.inner).2
            site.field) := by
    funext field
    by_cases hfield : field = site.field
    · subst field
      exact (Function.update_self site.field
        (letterMatrix bg (swapExactDerivativePositions carrier site.outer site.inner).2
          site.field) (letterMatrix bg carrier.2)).symm
    · exact (letterMatrix_swap_of_ne site bg field hfield).trans
        (Function.update_of_ne hfield _ _).symm
  unfold carrierValue
  conv_lhs => rw [hletters]
  rfl

theorem carrierValue_insert_before (bg : GaugeBackground S)
    (moved : Finset (Fin (dimension16DerivativeCount carrier.1)))
    (hmoved : moved ⊆ outerSameOwnerPositions site) :
    carrierValue bg (insertLeibnizCarrier site .before moved) =
      slotContraction (letterMatrix bg carrier.2) carrier.2.trace.traceOrder site.field
        (wordFold bg carrier.2.derivativeWord.axisAtPosition
            ((outerPositionList site).filter fun position => position ∈ moved)
            (bg.curvature (carrier.2.derivativeWord.axisAtPosition site.outer)
              (carrier.2.derivativeWord.axisAtPosition site.inner)) *
          wordFold bg carrier.2.derivativeWord.axisAtPosition
            ((outerPositionList site).filter fun position => position ∉ moved)
            (innerLetter site bg)) := by
  unfold carrierValue
  rw [letterMatrix_insert site moved hmoved bg .before]
  change tracePermutationContraction _
      (insertTraceBefore carrier.2.trace.traceOrder site.field) = _
  rw [contraction_insertTraceBefore, Function.update_self, Function.update_idem]
  rfl

theorem carrierValue_insert_after (bg : GaugeBackground S)
    (moved : Finset (Fin (dimension16DerivativeCount carrier.1)))
    (hmoved : moved ⊆ outerSameOwnerPositions site) :
    carrierValue bg (insertLeibnizCarrier site .after moved) =
      slotContraction (letterMatrix bg carrier.2) carrier.2.trace.traceOrder site.field
        (wordFold bg carrier.2.derivativeWord.axisAtPosition
            ((outerPositionList site).filter fun position => position ∉ moved)
            (innerLetter site bg) *
          wordFold bg carrier.2.derivativeWord.axisAtPosition
            ((outerPositionList site).filter fun position => position ∈ moved)
            (bg.curvature (carrier.2.derivativeWord.axisAtPosition site.outer)
              (carrier.2.derivativeWord.axisAtPosition site.inner))) := by
  unfold carrierValue
  rw [letterMatrix_insert site moved hmoved bg .after]
  change tracePermutationContraction _
      (insertTraceAfter carrier.2.trace.traceOrder site.field) = _
  rw [contraction_insertTraceAfter, Function.update_self, Function.update_idem]
  rfl

/-! ## Soundness -/

/-- The Leibniz-correct commutator row vanishes on every gauge background. -/
theorem relationValue_leibnizCommutatorRow (bg : GaugeBackground S) :
    relationValue bg (leibnizCommutatorRow site) = 0 := by
  unfold leibnizCommutatorRow
  simp only [map_sub, map_sum, relationValue_single, one_smul]
  rw [carrierValue_source site bg, carrierValue_swap site bg]
  rw [Finset.sum_congr rfl (fun moved hmoved => by
    rw [carrierValue_insert_before site bg moved (Finset.mem_powerset.mp hmoved),
      carrierValue_insert_after site bg moved (Finset.mem_powerset.mp hmoved), ← map_sub])]
  rw [← map_sum, ← map_sub, ← map_sub]
  convert map_zero (slotContraction (letterMatrix bg carrier.2) carrier.2.trace.traceOrder
    site.field) using 2
  rw [letterMatrix_site_field, letterMatrix_swap_field, ← map_sub,
    GaugeBackground.covDeriv_comm, map_sub,
    wordFold_mul bg carrier.2.derivativeWord.axisAtPosition _ (outerPositionList_nodup site),
    wordFold_mul' bg carrier.2.derivativeWord.axisAtPosition _ (outerPositionList_nodup site),
    outerPositionList_toFinset, ← Finset.sum_sub_distrib, sub_self]

end Site

#print axioms wordFold_mul
#print axioms fieldPositions_decompose
#print axioms retained_map_eq_filter
#print axioms letterMatrix_insert
#print axioms relationValue_leibnizCommutatorRow

end Mettapedia.QuantumTheory.YangMills.HypercubicDimension16LeibnizCommutatorSoundness
