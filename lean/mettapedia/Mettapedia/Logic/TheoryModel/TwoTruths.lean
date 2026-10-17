import Mettapedia.Logic.TheoryModel.IdentityCarve

/-!
# Two truths: conventions and what holds without them

Madhyamaka distinguishes the truth of convention (*saṃvṛti-satya*) from ultimate truth
(*paramārtha-satya*), and holds that the ultimate cannot be taught without the
conventional (Nāgārjuna, *Mūlamadhyamakakārikā* XXIV.8–10).  Over a universe `U` of
candidate structures and a theory `T`:

* a **convention** is a set of sentences `Φ` adopted on top of `T`; the conventional
  truths are the consequences computed in the carved fragment `carve U Φ`
  (`conventional`);
* the **ultimate** truths are the consequences computed in `U` itself, under no
  convention (`ultimate`).

The layering:

* every ultimate truth is conventionally true under every convention
  (`ultimate_subset_conventional`), and the empty convention is the ultimate
  (`conventional_empty`);
* a conventional truth is an ultimate truth of the theory enlarged by the convention
  (`conventional_eq_ultimate`): a convention is a commitment, not a fact;
* **conventions that together cover the universe have the ultimate truths as their
  common part** (`ultimate_eq_iInter_of_covers`);
* **conventions can disagree**: two conventions, each with a hosted model, can make a
  sentence and an incompatible one conventionally true; then neither is ultimately
  true (`not_mem_ultimate_of_disagree`).

**Particulars and universals.**  Dharmakīrti's two realities are a different structure,
the Galois connection between structures and theories rather than a layering of
theories.  The ultimately real is the particular (*svalakṣaṇa*), a structure; the
conventionally real is the universal (*sāmānyalakṣaṇa*), an elementary class.  A
concept separates two particulars exactly when some sentence does
(`exists_isExtent_separating_iff`), so particulars satisfying the same sentences fall
under the same concepts (`mem_of_isExtent_of_theoryOf_eq`): in the layering both truths
are sets of sentences, while in the Galois connection the ultimate is not a sentence.

References: Nāgārjuna, *Mūlamadhyamakakārikā* XXIV.8–10; J. Garfield, *Taking
conventional truth seriously: authority regarding deceptive reality*, Philosophy East
and West 60 (2010); Dharmakīrti, *Pramāṇavārttika* III.3 (what is capable of causal
efficacy is ultimately real, the rest conventionally real); Th. Stcherbatsky, *Buddhist
Logic*, vol. 1 (1932), "What is ultimately real", pp. 181ff.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.TheoryModel.TwoTruths

open Set
open Mettapedia.Logic.TheoryModel

universe uStr uSent uι

variable {Str : Type uStr} {Sent : Type uSent} (Sat : Str → Sent → Prop)

/-- **Conventional truth**: the consequences of `T` under the convention `Φ`, computed
in the fragment of `U` that the convention carves out. -/
def conventional (U : Set Str) (Φ T : Set Sent) : Set Sent :=
  consequencesIn Sat (carve Sat U Φ) T

/-- **Ultimate truth**: the consequences of `T` computed in `U`, under no convention. -/
def ultimate (U : Set Str) (T : Set Sent) : Set Sent :=
  consequencesIn Sat U T

/-- A family of conventions covers `U` when every structure of `U` satisfies one of
them. -/
def Covers (U : Set Str) {ι : Sort uι} (conventions : ι → Set Sent) : Prop :=
  ∀ m ∈ U, ∃ i, m ∈ models Sat (conventions i)

variable {Sat}

/-- Every ultimate truth is conventionally true under every convention. -/
theorem ultimate_subset_conventional (U : Set Str) (Φ T : Set Sent) :
    ultimate Sat U T ⊆ conventional Sat U Φ T :=
  consequencesIn_subset_carve U Φ T

/-- **A conventional truth is an ultimate truth of the enlarged theory.** -/
theorem conventional_eq_ultimate (U : Set Str) (Φ T : Set Sent) :
    conventional Sat U Φ T = ultimate Sat U (Φ ∪ T) :=
  consequencesIn_carve U Φ T

theorem carve_empty (U : Set Str) : carve Sat U ∅ = U := by
  rw [carve, models_empty, inter_univ]

/-- The empty convention is the ultimate. -/
theorem conventional_empty (U : Set Str) (T : Set Sent) :
    conventional Sat U ∅ T = ultimate Sat U T := by
  rw [conventional, carve_empty, ultimate]

/-- **Conventions covering the universe have the ultimate truths as their common
part.** -/
theorem ultimate_eq_iInter_of_covers {ι : Sort uι} {U : Set Str} {conventions : ι → Set Sent}
    (covers : Covers Sat U conventions) (T : Set Sent) :
    ultimate Sat U T = ⋂ i, conventional Sat U (conventions i) T := by
  apply Subset.antisymm
  · intro φ member
    exact mem_iInter.mpr fun i => ultimate_subset_conventional U (conventions i) T member
  · intro φ member m hosted
    obtain ⟨i, model⟩ := covers m hosted.1
    exact mem_iInter.mp member i ⟨⟨hosted.1, model⟩, hosted.2⟩

/-- **When conventions disagree, neither side is ultimate**: if `φ` is conventionally
true under `Φ`, `ψ` under `Ψ`, each convention has a hosted model, and no structure of
the universe satisfies both `φ` and `ψ`, then neither `φ` nor `ψ` is ultimately true. -/
theorem not_mem_ultimate_of_disagree {U : Set Str} {Φ Ψ T : Set Sent} {φ ψ : Sent}
    (holdsΦ : φ ∈ conventional Sat U Φ T) (holdsΨ : ψ ∈ conventional Sat U Ψ T)
    (hostedΦ : (modelsIn Sat (carve Sat U Φ) T).Nonempty)
    (hostedΨ : (modelsIn Sat (carve Sat U Ψ) T).Nonempty)
    (incompatible : ∀ m ∈ U, Sat m φ → Sat m ψ → False) :
    φ ∉ ultimate Sat U T ∧ ψ ∉ ultimate Sat U T := by
  obtain ⟨mΦ, inΦ⟩ := hostedΦ
  obtain ⟨mΨ, inΨ⟩ := hostedΨ
  constructor
  · intro ultimateφ
    have atΨ : Sat mΨ φ := ultimate_subset_conventional U Ψ T ultimateφ inΨ
    exact incompatible mΨ inΨ.1.1 atΨ (holdsΨ inΨ)
  · intro ultimateψ
    have atΦ : Sat mΦ ψ := ultimate_subset_conventional U Φ T ultimateψ inΦ
    exact incompatible mΦ inΦ.1.1 (holdsΦ inΦ) atΦ

/-! ## Particulars and universals -/

/-- Two structures have the same theory exactly when they satisfy the same sentences. -/
theorem theoryOf_singleton_eq_iff {m m' : Str} :
    theoryOf Sat {m} = theoryOf Sat {m'} ↔ ∀ φ, Sat m φ ↔ Sat m' φ := by
  constructor
  · intro equal φ
    constructor
    · intro holds
      have member : φ ∈ theoryOf Sat {m} := fun _ inClass => (mem_singleton_iff.mp inClass) ▸ holds
      rw [equal] at member
      exact member rfl
    · intro holds
      have member : φ ∈ theoryOf Sat {m'} := fun _ inClass => (mem_singleton_iff.mp inClass) ▸ holds
      rw [← equal] at member
      exact member rfl
  · intro same
    ext φ
    constructor
    · intro member _ inClass
      rw [mem_singleton_iff.mp inClass]
      exact (same φ).mp (member rfl)
    · intro member _ inClass
      rw [mem_singleton_iff.mp inClass]
      exact (same φ).mpr (member rfl)

/-- **Concepts cannot separate particulars with the same theory.** -/
theorem mem_of_isExtent_of_theoryOf_eq {K : Set Str} (extent : Order.IsExtent Sat K)
    {m m' : Str} (equivalent : theoryOf Sat {m} = theoryOf Sat {m'}) (member : m ∈ K) :
    m' ∈ K := by
  obtain ⟨T, rfl⟩ := extent
  have included : T ⊆ theoryOf Sat {m} :=
    subset_theoryOf_iff.mpr (singleton_subset_iff.mpr member)
  rw [equivalent] at included
  exact singleton_subset_iff.mp (subset_theoryOf_iff.mp included)

/-- **A concept separates two particulars exactly when a sentence does.** -/
theorem exists_isExtent_separating_iff {m m' : Str} :
    (∃ K, Order.IsExtent Sat K ∧ m ∈ K ∧ m' ∉ K) ↔ ∃ φ, Sat m φ ∧ ¬ Sat m' φ := by
  constructor
  · rintro ⟨K, ⟨T, rfl⟩, member, notMember⟩
    by_contra none
    apply notMember
    intro φ inT
    by_contra notHolds
    exact none ⟨φ, member inT, notHolds⟩
  · rintro ⟨φ, holds, notHolds⟩
    exact ⟨models Sat {φ}, ⟨{φ}, rfl⟩, fun _ inSingleton => (mem_singleton_iff.mp inSingleton) ▸ holds,
      fun model => notHolds (model (mem_singleton φ))⟩

end Mettapedia.Logic.TheoryModel.TwoTruths
