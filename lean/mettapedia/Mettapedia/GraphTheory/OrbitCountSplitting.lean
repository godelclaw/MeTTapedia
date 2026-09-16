import Mathlib.Data.Set.Card
import Mettapedia.GraphTheory.FourColor.GoertzelV24PermutationOrbitSurgery
import Mettapedia.GraphTheory.FourColor.GoertzelV24WordReachability

/-!
# Counting orbits inside a region: splitting and transport

Two generic instruments for finite orbit counting.  Both are statements about
the classes of an equivalence relation on a finite carrier, and both are used
repeatedly — by hand, in ad hoc form — wherever a map is compared with a piece
of itself.

## Tool A — an orbit count splits over complementary invariant sets

`classCountOn_add_compl`.  If a region is *saturated* (closed under the
relation whose classes are being counted) then every class lies entirely
inside it or entirely outside it, so the two restricted counts add up to the
total.  Saturation is exactly the hypothesis needed: for a region that is not
closed, classes straddling the boundary are counted twice and the identity
fails.

## Tool B — transporting a count along a partially equivariant map

`classCountOn_preimage`.  Given a map `h : D' → D` between carriers, a region
`S ⊆ D` and two equivalence relations, the number of `S`-meeting classes
upstairs equals the number of `h ⁻¹' S`-meeting classes downstairs as soon as

* `S` is saturated (Tool A's hypothesis again);
* **unit / coverage**: every point of `S` is related to a point of the image —
  the region is covered by `h` *up to the relation*, not on the nose;
* **functor / faithfulness**: over the region, `h` reflects and preserves the
  relation.

Nothing else is needed.  In particular `h` need not be injective, need not be
equivariant *outside* the region, and need not land inside the region.  The
second hypothesis is where the "equivariant only off the ring" situation gets
used: `hfunctor` is asked for only at points whose image lies in `S`, so a map
that is equivariant on the region and arbitrary elsewhere still qualifies.

Both hypotheses are load-bearing: dropping either one falsifies the
conclusion already on carriers of size 4 and 6.  They are also satisfiable
without any further constraint on `h` — see
`orbitCountOn_eq_classCountOn_pullback`, which builds an adjunction out of an
arbitrary map and nothing else.

## Specialisations

The permutation layer (`orbitCountOn`, over `Equiv.Perm.SameCycle`) and the
generator-family layer (`wordOrbitCountOn`, over `WordReachable`) each get
Tool A, Tool B, and two derived instruments that are what actually gets used:

* `orbitCount_eq_add_subtypePerm` — the orbit count of a permutation is the
  sum of the orbit counts of its two restrictions to an invariant set and its
  complement.  This is the splitting that is otherwise done by exhibiting an
  explicit `Equiv.sumCompl` conjugation and appealing to a disjoint-sum law.
* `classCount_eq_card_of_completeInvariant` (and its two instances) — if a map
  out of the carrier is constant on classes and separates them, the class count
  is the cardinality of its range.  This is the "build the quotient equivalence
  by hand with `Equiv.ofBijective`" pattern, done once.

`orbitCount_sumCongr_of_splitting`, below, re-derives the disjoint-sum law of
`GoertzelV24OrbitCountCongr` from Tool A alone;
`Mettapedia.GraphTheory.OrbitCountSplittingApplications` re-derives four more
results of the four-colour lane, and guards the statement identities.
-/

namespace Mettapedia.GraphTheory.OrbitCountSplitting

open Equiv Equiv.Perm

/-! ## The generic core

Everything in this section is about a bare `Setoid` on a finite type; no
permutation, graph, or map is involved. -/

section Generic

variable {D D' A : Type*}

/-- The classes of `s` that meet `S`. -/
def classesOn (s : Setoid D) (S : Set D) : Set (Quotient s) := Quotient.mk s '' S

/-- The number of `s`-classes that meet `S`.  For saturated `S` this is the
number of classes contained in `S`. -/
noncomputable def classCountOn (s : Setoid D) (S : Set D) : ℕ := (classesOn s S).ncard

/-- `S` is a union of classes. -/
def Saturated (s : Setoid D) (S : Set D) : Prop := ∀ ⦃x y : D⦄, s x y → x ∈ S → y ∈ S

theorem Saturated.compl {s : Setoid D} {S : Set D} (h : Saturated s S) :
    Saturated s Sᶜ := by
  intro x y hxy hx hy
  exact hx (h (s.symm hxy) hy)

theorem saturated_univ (s : Setoid D) : Saturated s (Set.univ : Set D) :=
  fun _ _ _ _ => Set.mem_univ _

theorem classesOn_univ (s : Setoid D) : classesOn s (Set.univ : Set D) = Set.univ := by
  ext q
  simp only [Set.mem_univ, iff_true]
  obtain ⟨x, rfl⟩ := Quotient.mk_surjective q
  exact ⟨x, Set.mem_univ x, rfl⟩

theorem classCountOn_univ (s : Setoid D) :
    classCountOn s (Set.univ : Set D) = Nat.card (Quotient s) := by
  rw [classCountOn, classesOn_univ, Set.ncard_univ]

/-- **Tool A.  An orbit count splits over complementary invariant sets.**

Every class lies wholly inside a saturated region or wholly outside it, so the
two restricted counts add up to the total. -/
theorem classCountOn_add_compl [Finite D] {s : Setoid D} {S : Set D}
    (hS : Saturated s S) :
    classCountOn s S + classCountOn s Sᶜ = Nat.card (Quotient s) := by
  have hcover : classesOn s S ∪ classesOn s Sᶜ = (Set.univ : Set (Quotient s)) := by
    ext q
    simp only [Set.mem_union, Set.mem_univ, iff_true]
    obtain ⟨x, rfl⟩ := Quotient.mk_surjective q
    by_cases hx : x ∈ S
    · exact Or.inl ⟨x, hx, rfl⟩
    · exact Or.inr ⟨x, hx, rfl⟩
  have hdisj : Disjoint (classesOn s S) (classesOn s Sᶜ) := by
    rw [Set.disjoint_left]
    rintro q ⟨x, hx, rfl⟩ ⟨y, hy, hq⟩
    exact hy (hS (Quotient.exact hq.symm) hx)
  rw [classCountOn, classCountOn,
    ← Set.ncard_union_eq hdisj (Set.toFinite _) (Set.toFinite _), hcover, Set.ncard_univ]

/-- The preimage of a saturated region is saturated, provided the map reflects
the relation over that region. -/
theorem Saturated.preimage {s : Setoid D} {s' : Setoid D'} {h : D' → D} {S : Set D}
    (hS : Saturated s S)
    (hfunctor : ∀ x y : D', h x ∈ S → (s' x y ↔ s (h x) (h y))) :
    Saturated s' (h ⁻¹' S) :=
  fun _ _ hxy hx => hS ((hfunctor _ _ hx).1 hxy) hx

/-- **Tool B.  Transporting a class count along a partially equivariant map.**

`hunit` is coverage of the region by the image *up to the relation*; `hfunctor`
is preservation and reflection of the relation, demanded only at points whose
image already lies in the region.  Injectivity of `h` is not needed: over the
region it is a consequence of `hfunctor`. -/
theorem classCountOn_preimage [Finite D] [Finite D'] {s : Setoid D} {s' : Setoid D'}
    {h : D' → D} {S : Set D}
    (hS : Saturated s S)
    (hunit : ∀ x ∈ S, ∃ y : D', s x (h y))
    (hfunctor : ∀ x y : D', h x ∈ S → (s' x y ↔ s (h x) (h y))) :
    classCountOn s S = classCountOn s' (h ⁻¹' S) := by
  have hU : Saturated s' (h ⁻¹' S) := hS.preimage hfunctor
  -- a representative of a class meeting the region again lies in the region
  have hout : ∀ c : Quotient s', c ∈ classesOn s' (h ⁻¹' S) → h c.out ∈ S := by
    rintro c ⟨y, hy, rfl⟩
    exact hU (s'.symm (Quotient.mk_out y)) hy
  set Φ : Quotient s' → Quotient s := fun c => Quotient.mk s (h c.out) with hΦ
  have hinj : Set.InjOn Φ (classesOn s' (h ⁻¹' S)) := by
    intro c₁ hc₁ c₂ hc₂ heq
    have h₁ : h c₁.out ∈ S := hout c₁ hc₁
    have hrel : s (h c₁.out) (h c₂.out) := Quotient.exact heq
    have : s' c₁.out c₂.out := (hfunctor _ _ h₁).2 hrel
    calc c₁ = Quotient.mk s' c₁.out := (Quotient.out_eq c₁).symm
      _ = Quotient.mk s' c₂.out := Quotient.sound this
      _ = c₂ := Quotient.out_eq c₂
  have himg : Φ '' classesOn s' (h ⁻¹' S) = classesOn s S := by
    ext q
    constructor
    · rintro ⟨c, hc, rfl⟩
      exact ⟨h c.out, hout c hc, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨y, hy⟩ := hunit x hx
      have hyU : y ∈ h ⁻¹' S := hS hy hx
      refine ⟨Quotient.mk s' y, ⟨y, hyU, rfl⟩, ?_⟩
      have hoy : (Quotient.mk s' y).out ∈ h ⁻¹' S :=
        hU (s'.symm (Quotient.mk_out y)) hyU
      have : s (h (Quotient.mk s' y).out) (h y) :=
        (hfunctor _ _ hoy).1 (Quotient.mk_out y)
      exact Quotient.sound (s.trans this (s.symm hy))
  rw [classCountOn, classCountOn, ← himg, hinj.ncard_image]

/-! ### Transport onto a bare index type

The special case in which the source carrier has no interesting relation of its
own: the region is then indexed by the source type outright. -/

/-- Equality as a setoid. -/
def eqSetoid (A : Type*) : Setoid A := ⟨Eq, ⟨fun _ => rfl, Eq.symm, Eq.trans⟩⟩

/-- The quotient by equality is the type itself. -/
def quotEqSetoidEquiv (A : Type*) : Quotient (eqSetoid A) ≃ A where
  toFun := Quotient.lift id fun _ _ h => h
  invFun := Quotient.mk _
  left_inv c := by
    induction c using Quotient.inductionOn with
    | h a => rfl
  right_inv _ := rfl

theorem classCountOn_eqSetoid_univ (A : Type*) [Finite A] :
    classCountOn (eqSetoid A) (Set.univ : Set A) = Nat.card A := by
  rw [classCountOn_univ]
  exact Nat.card_congr (quotEqSetoidEquiv A)

/-- **Tool B, indexed form.**  A saturated region whose classes are enumerated
faithfully by a section `h : A → D` has exactly `Nat.card A` classes. -/
theorem classCountOn_eq_card_of_section [Finite D] [Finite A] {s : Setoid D} {S : Set D}
    (h : A → D) (hS : Saturated s S)
    (hmaps : ∀ a, h a ∈ S)
    (hunit : ∀ x ∈ S, ∃ a : A, s x (h a))
    (hfaithful : ∀ a b : A, s (h a) (h b) ↔ a = b) :
    classCountOn s S = Nat.card A := by
  have hpre : h ⁻¹' S = (Set.univ : Set A) := by
    ext a; simp [hmaps a]
  have := classCountOn_preimage (s := s) (s' := eqSetoid A) (h := h) hS hunit
    (fun a b _ => (hfaithful a b).symm)
  rw [this, hpre, classCountOn_eqSetoid_univ]

/-- **A complete invariant computes the class count.**  A map out of the
carrier that is constant on classes, separates distinct classes, and is onto
identifies the quotient with its codomain.

This is the content of every hand-built `Equiv.ofBijective` from a labelling
function: `hsep` is the two-sided well-definedness and injectivity, `hsurj` the
surjectivity. -/
theorem classCount_eq_card_of_completeInvariant [Finite D] [Finite A] {s : Setoid D}
    (f : D → A) (hsep : ∀ x y : D, s x y ↔ f x = f y) (hsurj : Function.Surjective f) :
    Nat.card (Quotient s) = Nat.card A := by
  classical
  refine (classCountOn_univ s).symm.trans ?_
  refine classCountOn_eq_card_of_section (fun a => (hsurj a).choose)
    (saturated_univ s) (fun _ => Set.mem_univ _) ?_ ?_
  · intro x _
    refine ⟨f x, (hsep _ _).2 ?_⟩
    exact ((hsurj (f x)).choose_spec).symm
  · intro a b
    rw [hsep, (hsurj a).choose_spec, (hsurj b).choose_spec]

end Generic

/-! ## The permutation layer

`orbitCount` counts the cycles of a permutation, fixed points included.  Its
regional refinement is `orbitCountOn`. -/

section Perm

open Mettapedia.GraphTheory.FourColor.GoertzelV24PermutationOrbitSurgery

variable {D D' A : Type*} [Fintype D]

/-- The number of `σ`-orbits meeting `S`. -/
noncomputable def orbitCountOn (σ : Perm D) (S : Set D) : ℕ :=
  classCountOn (SameCycle.setoid σ) S

theorem orbitCountOn_univ (σ : Perm D) :
    orbitCountOn σ (Set.univ : Set D) = orbitCount σ := by
  rw [orbitCountOn, classCountOn_univ, orbitCount, Nat.card_eq_fintype_card]

/-- An invariant set is saturated for the cycle relation: on a finite carrier a
set closed under `σ` is closed under `σ`'s whole orbit relation. -/
theorem saturated_sameCycle_of_invariant {σ : Perm D} {S : Set D}
    (hS : ∀ x ∈ S, σ x ∈ S) : Saturated (SameCycle.setoid σ) S := by
  intro x y hxy hx
  obtain ⟨n, rfl⟩ := exists_nat_pow_apply_eq (σ := σ) hxy
  clear hxy
  induction n with
  | zero => simpa using hx
  | succ n ih =>
      have hpow : (σ ^ (n + 1)) x = σ ((σ ^ n) x) := by
        rw [pow_succ', Perm.mul_apply]
      rw [hpow]
      exact hS _ ih

/-- **Tool A for permutations.**  The cycle count splits over an invariant set
and its complement. -/
theorem orbitCount_eq_orbitCountOn_add_compl (σ : Perm D) {S : Set D}
    (hS : ∀ x ∈ S, σ x ∈ S) :
    orbitCount σ = orbitCountOn σ S + orbitCountOn σ Sᶜ := by
  rw [orbitCountOn, orbitCountOn,
    classCountOn_add_compl (saturated_sameCycle_of_invariant hS), orbitCount,
    Nat.card_eq_fintype_card]

/-- **Tool B for permutations, strict form: the functor law from step
equivariance.**  A map that commutes with the two permutations at every point
of the region, and is injective over the region, preserves and reflects the
cycle relation there.  No condition at all is imposed off the region. -/
theorem sameCycle_iff_of_equivariantOn [Fintype D'] {σ : Perm D} {σ' : Perm D'}
    {h : D' → D} {S : Set D}
    (hS : ∀ x ∈ S, σ x ∈ S)
    (hinj : Set.InjOn h (h ⁻¹' S))
    (hequiv : ∀ y : D', h y ∈ S → h (σ' y) = σ (h y))
    {x y : D'} (hx : h x ∈ S) :
    (σ'.SameCycle x y) ↔ σ.SameCycle (h x) (h y) := by
  have key : ∀ n : ℕ, h ((σ' ^ n) x) = (σ ^ n) (h x) ∧ (σ ^ n) (h x) ∈ S := by
    intro n
    induction n with
    | zero => simpa using hx
    | succ n ih =>
        obtain ⟨hstep, hmem⟩ := ih
        have hx' : h ((σ' ^ n) x) ∈ S := by rw [hstep]; exact hmem
        constructor
        · rw [pow_succ', Perm.mul_apply, hequiv _ hx', hstep, pow_succ', Perm.mul_apply]
        · rw [pow_succ', Perm.mul_apply]
          exact hS _ hmem
  constructor
  · intro hxy
    obtain ⟨n, hn⟩ := exists_nat_pow_apply_eq hxy
    refine ⟨n, ?_⟩
    rw [zpow_natCast, ← (key n).1, hn]
  · intro hxy
    obtain ⟨n, hn⟩ := exists_nat_pow_apply_eq hxy
    refine ⟨n, ?_⟩
    rw [zpow_natCast]
    refine hinj ?_ ?_ ?_
    · show h ((σ' ^ n) x) ∈ S
      rw [(key n).1]; exact (key n).2
    · show h y ∈ S
      rw [← hn]; exact (key n).2
    · rw [(key n).1, hn]

/-- **Tool B for permutations.**  The number of `σ`-orbits meeting an invariant
region equals the number of `σ'`-orbits meeting the region's preimage, for any
map that covers the region up to connectivity and is injective and equivariant
over it. -/
theorem orbitCountOn_eq_orbitCountOn_of_equivariantOn [Fintype D']
    {σ : Perm D} {σ' : Perm D'} {h : D' → D} {S : Set D}
    (hS : ∀ x ∈ S, σ x ∈ S)
    (hinj : Set.InjOn h (h ⁻¹' S))
    (hequiv : ∀ y : D', h y ∈ S → h (σ' y) = σ (h y))
    (hunit : ∀ x ∈ S, ∃ y : D', σ.SameCycle x (h y)) :
    orbitCountOn σ S = orbitCountOn σ' (h ⁻¹' S) :=
  classCountOn_preimage (saturated_sameCycle_of_invariant hS) hunit
    (fun _ _ hx => sameCycle_iff_of_equivariantOn hS hinj hequiv hx)

/-- **Tool B for permutations, into-the-region form.**  The common case: the
transporting map lands inside the region, is injective, and is equivariant
there.  Then the source carrier's whole orbit count is what the region sees.

This is a corollary of `orbitCountOn_eq_orbitCountOn_of_equivariantOn`, not a
strengthening of it: the extra hypothesis only pins the preimage to be
everything, and is what removes `h ⁻¹' S` from the conclusion. -/
theorem orbitCountOn_eq_orbitCount_of_equivariantOn [Fintype D']
    {σ : Perm D} {σ' : Perm D'} {h : D' → D} {S : Set D}
    (hS : ∀ x ∈ S, σ x ∈ S)
    (hmaps : ∀ y : D', h y ∈ S)
    (hinj : Function.Injective h)
    (hequiv : ∀ y : D', h (σ' y) = σ (h y))
    (hunit : ∀ x ∈ S, ∃ y : D', σ.SameCycle x (h y)) :
    orbitCountOn σ S = orbitCount σ' := by
  have hpre : h ⁻¹' S = (Set.univ : Set D') := by
    ext y
    exact iff_of_true (hmaps y) (Set.mem_univ y)
  have hmain := orbitCountOn_eq_orbitCountOn_of_equivariantOn hS hinj.injOn
    (fun y _ => hequiv y) hunit
  rw [hmain, hpre, orbitCountOn_univ]

/-- **Carrier change.**  An equivariant bijection preserves the cycle count.
This is Tool B with the whole carrier as the region; it subsumes invariance of
the orbit count under conjugation by an equivalence of carriers. -/
theorem orbitCount_eq_of_equivariant_bijection [Fintype D']
    {σ : Perm D} {σ' : Perm D'} (h : D' → D) (hbij : Function.Bijective h)
    (hequiv : ∀ y : D', h (σ' y) = σ (h y)) :
    orbitCount σ = orbitCount σ' := by
  have hpre : h ⁻¹' (Set.univ : Set D) = (Set.univ : Set D') := rfl
  have := orbitCountOn_eq_orbitCountOn_of_equivariantOn (σ := σ) (σ' := σ')
    (h := h) (S := (Set.univ : Set D)) (fun _ _ => Set.mem_univ _)
    (hbij.injective.injOn) (fun y _ => hequiv y)
    (fun x _ => by
      obtain ⟨y, rfl⟩ := hbij.surjective x
      exact ⟨y, SameCycle.refl σ (h y)⟩)
  rwa [hpre, orbitCountOn_univ, orbitCountOn_univ] at this

/-- The cycle relation pulled back along an arbitrary map. -/
def pullbackSetoid (σ : Perm D) (h : D' → D) : Setoid D' :=
  ⟨fun y z => σ.SameCycle (h y) (h z),
    ⟨fun y => SameCycle.refl σ (h y), SameCycle.symm, SameCycle.trans⟩⟩

/-- **The hypotheses of Tool B are satisfiable in full generality.**  For *any*
map `h` whatsoever and any invariant region covered by its image up to the cycle
relation, the pullback relation makes `h` an adjunction.  `h` is unconstrained
here — not injective, not equivariant, not valued in the region — which is
exactly the slack the general statement has over the strict one, and the reason
the conclusion is about `h ⁻¹' S` rather than all of `D'`. -/
theorem orbitCountOn_eq_classCountOn_pullback [Finite D'] (σ : Perm D) (h : D' → D)
    {S : Set D} (hS : ∀ x ∈ S, σ x ∈ S)
    (hunit : ∀ x ∈ S, ∃ y : D', σ.SameCycle x (h y)) :
    orbitCountOn σ S = classCountOn (pullbackSetoid σ h) (h ⁻¹' S) :=
  classCountOn_preimage (saturated_sameCycle_of_invariant hS) hunit
    (fun _ _ _ => Iff.rfl)

/-- The regional count is the orbit count of the restricted permutation. -/
theorem orbitCountOn_eq_orbitCount_subtypePerm (σ : Perm D) {p : D → Prop}
    [DecidablePred p] (hp : ∀ x, p (σ x) ↔ p x) :
    orbitCountOn σ {x | p x} = orbitCount (σ.subtypePerm hp) := by
  have hS : ∀ x ∈ {x | p x}, σ x ∈ {x | p x} := fun x hx => (hp x).2 hx
  have hpre : (Subtype.val : {x // p x} → D) ⁻¹' {x | p x} = Set.univ := by
    ext y; simp [y.2]
  have := classCountOn_preimage (s := SameCycle.setoid σ)
    (s' := SameCycle.setoid (σ.subtypePerm hp)) (h := (Subtype.val : {x // p x} → D))
    (S := {x | p x}) (saturated_sameCycle_of_invariant hS)
    (fun x hx => ⟨⟨x, hx⟩, SameCycle.refl σ x⟩)
    (fun _ _ _ => sameCycle_subtypePerm)
  rw [orbitCountOn, this, hpre, classCountOn_univ, orbitCount, Nat.card_eq_fintype_card]

/-- **Tool A for permutations, restriction form.**  The cycle count of a
permutation is the sum of the cycle counts of its restrictions to an invariant
set and to the complementary set.

This is the numerical content of the "split the carrier along `Equiv.sumCompl`
and apply a disjoint-sum law" argument, with no conjugation to exhibit. -/
theorem orbitCount_eq_add_subtypePerm (σ : Perm D) {p : D → Prop} [DecidablePred p]
    (hp : ∀ x, p (σ x) ↔ p x) :
    orbitCount σ = orbitCount (σ.subtypePerm hp)
      + orbitCount (σ.subtypePerm (p := fun x => ¬ p x) (fun x => not_congr (hp x))) := by
  have hS : ∀ x ∈ {x | p x}, σ x ∈ {x | p x} := fun x hx => (hp x).2 hx
  have hcompl : ({x | p x}ᶜ : Set D) = {x | ¬ p x} := rfl
  rw [orbitCount_eq_orbitCountOn_add_compl σ hS, hcompl,
    orbitCountOn_eq_orbitCount_subtypePerm σ hp,
    orbitCountOn_eq_orbitCount_subtypePerm σ (p := fun x => ¬ p x)
      (fun x => not_congr (hp x))]

/-- **A complete invariant computes the cycle count.** -/
theorem orbitCount_eq_card_of_completeInvariant [Finite A] {σ : Perm D} (f : D → A)
    (hsep : ∀ x y : D, σ.SameCycle x y ↔ f x = f y) (hsurj : Function.Surjective f) :
    orbitCount σ = Nat.card A := by
  rw [orbitCount, ← Nat.card_eq_fintype_card]
  exact classCount_eq_card_of_completeInvariant f hsep hsurj

/-! ### A worked instance: disjoint sums

The orbit count of a disjoint sum of permutations is the sum of the orbit
counts.  It is Tool A applied to the summand tag — which is invariant, since no
orbit crosses between the summands — followed by a carrier change on each
restriction.  Stating it here also exhibits a nontrivial region for which every
hypothesis of both tools holds: the tag is invariant but not trivial, and the
inclusion of a summand is equivariant on its own side while saying nothing
about the other. -/

section Sum

variable {α β : Type*} [Fintype α] [Fintype β]

/-- **Orbit counts add over disjoint sums**, from the splitting tool. -/
theorem orbitCount_sumCongr_of_splitting (σ : Perm α) (τ : Perm β) :
    orbitCount (Equiv.sumCongr σ τ) = orbitCount σ + orbitCount τ := by
  have hp : ∀ x : α ⊕ β, (Equiv.sumCongr σ τ x).isLeft = true ↔ x.isLeft = true := by
    rintro (a | b) <;> simp
  rw [orbitCount_eq_add_subtypePerm (Equiv.sumCongr σ τ)
    (p := fun x : α ⊕ β => x.isLeft = true) hp]
  congr 1
  · refine orbitCount_eq_of_equivariant_bijection
      (fun a => (⟨Sum.inl a, rfl⟩ : {x : α ⊕ β // (x.isLeft = true)})) ?_ ?_
    · constructor
      · intro a b hab
        exact Sum.inl_injective (congrArg Subtype.val hab)
      · rintro ⟨a | b, hx⟩
        · exact ⟨a, rfl⟩
        · exact absurd hx (by simp)
    · intro a
      exact Subtype.ext (by simp [Perm.subtypePerm_apply])
  · refine orbitCount_eq_of_equivariant_bijection
      (fun b => (⟨Sum.inr b, by simp⟩ : {x : α ⊕ β // ¬ (x.isLeft = true)})) ?_ ?_
    · constructor
      · intro a b hab
        exact Sum.inr_injective (congrArg Subtype.val hab)
      · rintro ⟨a | b, hx⟩
        · exact absurd rfl hx
        · exact ⟨b, rfl⟩
    · intro b
      exact Subtype.ext (by simp [Perm.subtypePerm_apply])

end Sum

end Perm

/-! ## The generator-family layer

`wordOrbitCount` counts the connected components of the action of a finite list
of permutations.  Its regional refinement is `wordOrbitCountOn`. -/

section Word

open Mettapedia.GraphTheory.FourColor.GoertzelV24WordReachability

variable {D A : Type*} [Fintype D]

/-- The number of components of the family's action that meet `S`. -/
noncomputable def wordOrbitCountOn (L : List (Perm D)) (S : Set D) : ℕ :=
  classCountOn (wordSetoid L) S

theorem wordOrbitCountOn_univ (L : List (Perm D)) :
    wordOrbitCountOn L (Set.univ : Set D) = wordOrbitCount L := by
  rw [wordOrbitCountOn, classCountOn_univ, wordOrbitCount, Nat.card_eq_fintype_card]

/-- A set closed under every generator is saturated for reachability. -/
theorem saturated_wordReachable_of_invariant {L : List (Perm D)} {S : Set D}
    (hS : ∀ g ∈ L, ∀ x ∈ S, g x ∈ S) : Saturated (wordSetoid L) S := by
  intro x y hxy hx
  show y ∈ S
  induction hxy with
  | refl => exact hx
  | tail _ hstep ih =>
      obtain ⟨g, hg, rfl⟩ := hstep
      exact hS g hg _ ih

/-- **Tool A for generator families.**  The component count splits over an
invariant set and its complement. -/
theorem wordOrbitCount_eq_wordOrbitCountOn_add_compl (L : List (Perm D)) {S : Set D}
    (hS : ∀ g ∈ L, ∀ x ∈ S, g x ∈ S) :
    wordOrbitCount L = wordOrbitCountOn L S + wordOrbitCountOn L Sᶜ := by
  rw [wordOrbitCountOn, wordOrbitCountOn,
    classCountOn_add_compl (saturated_wordReachable_of_invariant hS), wordOrbitCount,
    Nat.card_eq_fintype_card]

/-- **Tool B for generator families, indexed form.** -/
theorem wordOrbitCountOn_eq_card_of_section [Finite A] {L : List (Perm D)} {S : Set D}
    (h : A → D) (hS : ∀ g ∈ L, ∀ x ∈ S, g x ∈ S)
    (hmaps : ∀ a, h a ∈ S)
    (hunit : ∀ x ∈ S, ∃ a : A, WordReachable L x (h a))
    (hfaithful : ∀ a b : A, WordReachable L (h a) (h b) ↔ a = b) :
    wordOrbitCountOn L S = Nat.card A :=
  classCountOn_eq_card_of_section h (saturated_wordReachable_of_invariant hS) hmaps
    hunit hfaithful

/-- **A complete invariant computes the component count.** -/
theorem wordOrbitCount_eq_card_of_completeInvariant [Finite A] {L : List (Perm D)}
    (f : D → A) (hsep : ∀ x y : D, WordReachable L x y ↔ f x = f y)
    (hsurj : Function.Surjective f) :
    wordOrbitCount L = Nat.card A := by
  rw [wordOrbitCount, ← Nat.card_eq_fintype_card]
  exact classCount_eq_card_of_completeInvariant f hsep hsurj

end Word

end Mettapedia.GraphTheory.OrbitCountSplitting
