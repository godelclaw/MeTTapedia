import Mathlib.Order.Ideal
import Mathlib.Order.CompletePartialOrder
import Mathlib.Order.ScottContinuity
import Mathlib.Order.Zorn

/-!
# Open-ended growth as an ideal completion of finite presentations

Let `P` be a preorder, for instance finitely presented profiles ordered by
extension (a thin category: at most one arrow between two profiles). An
open-ended growth of profiles is modeled here as a point of the free directed
completion of `P`, which for a thin category is the ideal completion: an ideal
is a nonempty, downward closed, directed family of profiles, a compatible
growing family. A profile `p` sits inside as its principal ideal
`principal p`; a growth without a largest stage is a non-principal ideal.

* **Universal property.** Every monotone map from profiles into a directed
  complete partial order extends uniquely to a Scott-continuous map out of the
  ideals (`extend_principal`, `extend_scottContinuous`, `extend_unique`).
  This is `Ind` of a thin category, constructed rather than assumed.
* **Compact elements are the finite profiles.** An ideal is compact exactly
  when it is principal (`isCompactElement_iff_principal`).
* **Finitary observations factor through a finite stage.** A Scott-continuous
  observation holds at an ideal exactly when it holds at one profile inside
  it (`scottContinuous_prop_factor`). An observation that needs infinitely
  many stages (`allStages`) holds at the top of an infinite growth while
  failing at every finite stage (`allStages_not_factor`).
* **When is there a strongest top?** There is a greatest point exactly when
  every two profiles have a common extension (`exists_greatest_iff_directed`).
  Incompatible profiles leave no strongest theory (`no_greatest_of_incompatible`).
  Every compatible family still extends to a maximal one
  (`exists_maximal_above`): a top exists per maximal compatible family.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.OpenEnded.IdealCompletion

open Order Set

universe u v

variable {P : Type u} [Preorder P]

/-! ## Directed unions of ideals -/

/-- The union of a nonempty directed family of ideals. -/
def directedUnion (family : Set (Ideal P)) (nonempty : family.Nonempty)
    (directed : DirectedOn (· ≤ ·) family) : Ideal P where
  carrier := ⋃ I ∈ family, (I : Set P)
  lower' := by
    intro x y below member
    simp only [mem_iUnion] at member ⊢
    obtain ⟨I, memberI, inI⟩ := member
    exact ⟨I, memberI, I.lower below inI⟩
  nonempty' := by
    obtain ⟨I, memberI⟩ := nonempty
    obtain ⟨x, inI⟩ := I.nonempty
    exact ⟨x, mem_biUnion memberI inI⟩
  directed' := by
    intro x memberX y memberY
    simp only [mem_iUnion] at memberX memberY
    obtain ⟨I, memberI, inI⟩ := memberX
    obtain ⟨K, memberK, inK⟩ := memberY
    obtain ⟨L, memberL, IL, KL⟩ := directed I memberI K memberK
    obtain ⟨z, inL, xz, yz⟩ := L.directed x (IL inI) y (KL inK)
    exact ⟨z, mem_biUnion memberL inL, xz, yz⟩

theorem mem_directedUnion {family : Set (Ideal P)} {nonempty : family.Nonempty}
    {directed : DirectedOn (· ≤ ·) family} {x : P} :
    x ∈ directedUnion family nonempty directed ↔ ∃ I ∈ family, x ∈ I := by
  change x ∈ ⋃ I ∈ family, (I : Set P) ↔ _
  simp only [mem_iUnion, SetLike.mem_coe, exists_prop]

theorem isLUB_directedUnion (family : Set (Ideal P)) (nonempty : family.Nonempty)
    (directed : DirectedOn (· ≤ ·) family) :
    IsLUB family (directedUnion family nonempty directed) := by
  constructor
  · intro I memberI x inI
    exact mem_directedUnion.mpr ⟨I, memberI, inI⟩
  · intro K upper x inUnion
    obtain ⟨I, memberI, inI⟩ := mem_directedUnion.mp inUnion
    exact upper memberI inI

/-- Every least upper bound of a nonempty directed family of ideals is its
union. -/
theorem mem_of_isLUB {family : Set (Ideal P)} (nonempty : family.Nonempty)
    (directed : DirectedOn (· ≤ ·) family) {top : Ideal P} (lub : IsLUB family top)
    {x : P} : x ∈ top ↔ ∃ I ∈ family, x ∈ I := by
  have same := lub.unique (isLUB_directedUnion family nonempty directed)
  rw [same]
  exact mem_directedUnion

/-- Every ideal is the directed union of the principal ideals of its members. -/
theorem principal_image_directed (I : Ideal P) :
    DirectedOn (· ≤ ·) (Ideal.principal '' (I : Set P)) := by
  rintro _ ⟨x, inX, rfl⟩ _ ⟨y, inY, rfl⟩
  obtain ⟨z, inZ, xz, yz⟩ := I.directed x inX y inY
  refine ⟨Ideal.principal z, ⟨z, inZ, rfl⟩, ?_, ?_⟩
  · intro w below
    exact Ideal.mem_principal.mpr ((Ideal.mem_principal.mp below).trans xz)
  · intro w below
    exact Ideal.mem_principal.mpr ((Ideal.mem_principal.mp below).trans yz)

theorem principal_image_nonempty (I : Ideal P) :
    (Ideal.principal '' (I : Set P)).Nonempty :=
  I.nonempty.image _

theorem isLUB_principal_image (I : Ideal P) :
    IsLUB (Ideal.principal '' (I : Set P)) I := by
  constructor
  · rintro _ ⟨x, inX, rfl⟩
    exact Ideal.principal_le_iff.mpr inX
  · intro K upper x inI
    exact Ideal.principal_le_iff.mp (upper ⟨x, inI, rfl⟩)

/-! ## The universal property -/

section Universal

variable {D : Type v} [CompletePartialOrder D]

/-- The Scott-continuous extension of a map on profiles. -/
noncomputable def extend (f : P → D) (I : Ideal P) : D :=
  sSup (f '' (I : Set P))

theorem image_directed {f : P → D} (monotone : Monotone f) (I : Ideal P) :
    DirectedOn (· ≤ ·) (f '' (I : Set P)) := by
  rintro _ ⟨x, inX, rfl⟩ _ ⟨y, inY, rfl⟩
  obtain ⟨z, inZ, xz, yz⟩ := I.directed x inX y inY
  exact ⟨f z, ⟨z, inZ, rfl⟩, monotone xz, monotone yz⟩

theorem extend_isLUB {f : P → D} (monotone : Monotone f) (I : Ideal P) :
    IsLUB (f '' (I : Set P)) (extend f I) :=
  CompletePartialOrder.lubOfDirected _ (image_directed monotone I)

/-- The extension agrees with the original map on finite profiles. -/
theorem extend_principal {f : P → D} (monotone : Monotone f) (p : P) :
    extend f (Ideal.principal p) = f p := by
  refine (extend_isLUB monotone _).unique ?_
  refine IsGreatest.isLUB ⟨⟨p, Ideal.mem_principal_self, rfl⟩, ?_⟩
  rintro _ ⟨x, inX, rfl⟩
  exact monotone (Ideal.mem_principal.mp inX)

theorem extend_monotone {f : P → D} (monotone : Monotone f) : Monotone (extend f) := by
  intro I K included
  refine (extend_isLUB monotone I).2 ?_
  rintro _ ⟨x, inX, rfl⟩
  exact (extend_isLUB monotone K).1 ⟨x, included inX, rfl⟩

/-- **The extension is Scott-continuous.** -/
theorem extend_scottContinuous {f : P → D} (monotone : Monotone f) :
    ScottContinuous (extend f) := by
  intro family nonempty directed top lub
  constructor
  · rintro _ ⟨I, memberI, rfl⟩
    exact extend_monotone monotone (lub.1 memberI)
  · intro bound upper
    refine (extend_isLUB monotone top).2 ?_
    rintro _ ⟨x, inTop, rfl⟩
    obtain ⟨I, memberI, inI⟩ := (mem_of_isLUB nonempty directed lub).mp inTop
    exact ((extend_isLUB monotone I).1 ⟨x, inI, rfl⟩).trans (upper ⟨I, memberI, rfl⟩)

/-- **Uniqueness of the extension.** -/
theorem extend_unique {f : P → D} (monotone : Monotone f) {g : Ideal P → D}
    (continuous : ScottContinuous g) (onPrincipal : ∀ p, g (Ideal.principal p) = f p) :
    g = extend f := by
  funext I
  have lub := continuous (principal_image_nonempty I) (principal_image_directed I)
    (isLUB_principal_image I)
  have sameImage : g '' (Ideal.principal '' (I : Set P)) = f '' (I : Set P) := by
    rw [image_image]
    exact image_congr fun p _ => onPrincipal p
  rw [sameImage] at lub
  exact lub.unique (extend_isLUB monotone I)

end Universal

/-! ## Compact elements -/

/-- An ideal is compact when it lies below a member of every directed family
whose least upper bound lies above it. -/
def IsCompactElement (x : Ideal P) : Prop :=
  ∀ family : Set (Ideal P), family.Nonempty → DirectedOn (· ≤ ·) family →
    ∀ top, IsLUB family top → x ≤ top → ∃ I ∈ family, x ≤ I

theorem principal_isCompactElement (p : P) : IsCompactElement (Ideal.principal p) := by
  intro family nonempty directed top lub below
  have inTop : p ∈ top := Ideal.principal_le_iff.mp below
  obtain ⟨I, memberI, inI⟩ := (mem_of_isLUB nonempty directed lub).mp inTop
  exact ⟨I, memberI, Ideal.principal_le_iff.mpr inI⟩

/-- **Compact ideals are exactly the finite profiles.** -/
theorem isCompactElement_iff_principal (x : Ideal P) :
    IsCompactElement x ↔ ∃ p, x = Ideal.principal p := by
  constructor
  · intro compact
    obtain ⟨_, ⟨p, inX, rfl⟩, below⟩ := compact _ (principal_image_nonempty x)
      (principal_image_directed x) x (isLUB_principal_image x) le_rfl
    exact ⟨p, le_antisymm below (Ideal.principal_le_iff.mpr inX)⟩
  · rintro ⟨p, rfl⟩
    exact principal_isCompactElement p

/-! ## Finitary observations factor through a finite stage -/

/-- **Factorization.** A Scott-continuous observation of the top holds exactly
when it holds at one finite stage inside it. -/
theorem scottContinuous_prop_factor {observe : Ideal P → Prop}
    (continuous : ScottContinuous observe) (I : Ideal P) :
    observe I ↔ ∃ p ∈ I, observe (Ideal.principal p) := by
  have monotone : Monotone (fun p : P => observe (Ideal.principal p)) := by
    intro p q le
    exact continuous.monotone (Ideal.principal_le_iff.mpr (Ideal.mem_principal.mpr le))
  have same : observe I = extend (fun p : P => observe (Ideal.principal p)) I :=
    congrFun (extend_unique monotone continuous (fun _ => rfl)) I
  rw [same]
  change sSup ((fun p => observe (Ideal.principal p)) '' (I : Set P)) ↔ _
  rw [sSup_Prop_eq]
  constructor
  · rintro ⟨_, ⟨p, inI, rfl⟩, holds⟩
    exact ⟨p, inI, holds⟩
  · rintro ⟨p, inI, holds⟩
    exact ⟨_, ⟨p, inI, rfl⟩, holds⟩

/-- An observation that needs every stage: every natural number is covered by
some finite stage. -/
def allStages (I : Ideal (Finset ℕ)) : Prop :=
  ∀ n : ℕ, ∃ s ∈ I, n ∈ s

/-- The ideal of all finite sets of naturals: an infinite growth. -/
def allFinite : Ideal (Finset ℕ) where
  carrier := univ
  lower' := fun _ _ _ _ => mem_univ _
  nonempty' := ⟨∅, mem_univ _⟩
  directed' := fun x _ y _ => ⟨x ∪ y, mem_univ _, Finset.subset_union_left,
    Finset.subset_union_right⟩

/-- **An infinitary observation does not factor**: it holds at the top of the
growth and at no finite stage. -/
theorem allStages_not_factor :
    allStages allFinite ∧ ∀ s : Finset ℕ, ¬ allStages (Ideal.principal s) := by
  refine ⟨fun n => ⟨{n}, mem_univ _, Finset.mem_singleton_self n⟩, fun s covers => ?_⟩
  obtain ⟨t, below, member⟩ := covers (s.sup id + 1)
  have inS : s.sup id + 1 ∈ s := Ideal.mem_principal.mp below member
  have bounded : s.sup id + 1 ≤ s.sup id := Finset.le_sup (f := id) inS
  omega

theorem allStages_not_scottContinuous : ¬ ScottContinuous allStages := by
  intro continuous
  obtain ⟨p, _, holds⟩ := (scottContinuous_prop_factor continuous allFinite).mp
    allStages_not_factor.1
  exact allStages_not_factor.2 p holds

/-! ## Strongest tops and compatible families -/

/-- **A greatest point exists exactly when every two profiles are
compatible.** -/
theorem exists_greatest_iff_directed :
    (∃ top : Ideal P, ∀ I : Ideal P, I ≤ top) ↔
      Nonempty P ∧ ∀ p q : P, ∃ r, p ≤ r ∧ q ≤ r := by
  constructor
  · rintro ⟨top, greatest⟩
    obtain ⟨x, _⟩ := top.nonempty
    refine ⟨⟨x⟩, fun p q => ?_⟩
    have inP : p ∈ top := Ideal.principal_le_iff.mp (greatest _)
    have inQ : q ∈ top := Ideal.principal_le_iff.mp (greatest _)
    obtain ⟨r, _, pr, qr⟩ := top.directed p inP q inQ
    exact ⟨r, pr, qr⟩
  · rintro ⟨⟨x⟩, compatible⟩
    refine ⟨⟨⟨univ, fun _ _ _ _ => mem_univ _⟩, ⟨x, mem_univ _⟩, ?_⟩, ?_⟩
    · intro p _ q _
      obtain ⟨r, pr, qr⟩ := compatible p q
      exact ⟨r, mem_univ _, pr, qr⟩
    · intro I y _
      exact mem_univ y

/-- **Incompatible profiles leave no strongest theory.** -/
theorem no_greatest_of_incompatible {p q : P} (incompatible : ∀ r, ¬ (p ≤ r ∧ q ≤ r)) :
    ¬ ∃ top : Ideal P, ∀ I : Ideal P, I ≤ top := by
  intro exists_top
  obtain ⟨_, compatible⟩ := exists_greatest_iff_directed.mp exists_top
  obtain ⟨r, both⟩ := compatible p q
  exact incompatible r both

/-- **Every compatible family extends to a maximal one.** -/
theorem exists_maximal_above (I : Ideal P) :
    ∃ M : Ideal P, I ≤ M ∧ ∀ K : Ideal P, M ≤ K → K ≤ M := by
  obtain ⟨M, below, maximal⟩ := zorn_le_nonempty₀ (univ : Set (Ideal P))
    (fun chain _ isChain K memberK => by
      have nonempty : chain.Nonempty := ⟨K, memberK⟩
      have directed : DirectedOn (· ≤ ·) chain := isChain.directedOn
      exact ⟨directedUnion chain nonempty directed, mem_univ _,
        fun J memberJ => (isLUB_directedUnion chain nonempty directed).1 memberJ⟩)
    I (mem_univ I)
  exact ⟨M, below, fun K above => maximal.2 (mem_univ K) above⟩

#print axioms isLUB_directedUnion
#print axioms extend_principal
#print axioms extend_scottContinuous
#print axioms extend_unique
#print axioms isCompactElement_iff_principal
#print axioms scottContinuous_prop_factor
#print axioms allStages_not_factor
#print axioms allStages_not_scottContinuous
#print axioms exists_greatest_iff_directed
#print axioms no_greatest_of_incompatible
#print axioms exists_maximal_above

end Mettapedia.GSLT.OpenEnded.IdealCompletion
