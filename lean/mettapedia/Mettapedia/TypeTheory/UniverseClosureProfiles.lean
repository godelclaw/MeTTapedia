import Mettapedia.TypeTheory.FamilyEnclosingUniverse
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

/-!
# Closure profiles for type-theoretic universes

This module separates three increasingly demanding universe capabilities.

* A family-enclosing operator returns one closed Tarski universe above a
  selected dependent family.
* A superuniverse embeds, inside one outer universe, every universe produced
  by a selected small family-enclosing operator.
* A Mahlo reflection profile has, for every internal family operator, an
  ordinary subuniverse closed on the families drawn from it: the operator
  sends each such family to a family equivalent to another one drawn from the
  subuniverse.

The last two are capability interfaces, not new kernel rules and not existence
claims.  The ambient type hierarchy gives a positive semantic embedding one
level up.

Mahlo reflection is distinct from whole-subuniverse closure, which applies the
operator to the subuniverse itself, taken as one family.  Whole-subuniverse
closure fails in every universe whose codes grow strictly, so it measures the
absence of growth rather than the strength of a universe.  Finite-code
controls separate the notions: ordinary universe data does not give
whole-subuniverse closure under arbitrary operators, and Mahlo reflection holds
or fails in one and the same finite universe according to the predicate that
selects the ordinary subuniverses.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.UniverseClosureProfiles

open Mettapedia.TypeTheory.FamilyEnclosingUniverse

universe uOuter u

/-! ## Tarski universes and internal families -/

-- The code carrier and the decoded types have independent universe levels.
set_option linter.checkUnivs false in
/-- The data common to the universe-closure comparisons: codes and decoding.
No closure, cumulativity, or self-code property is implicit. -/
structure SemanticTarskiUniverse where
  Code : Type uOuter
  El : Code → Type u

/-- Forget the selected family and closure operations of a closed envelope. -/
def semanticUniverseOfEnvelope
    {A : Type u} {B : A → Type u}
    (envelope : ClosedTarskiUniverseOver.{uOuter, u} A B) :
    SemanticTarskiUniverse.{uOuter, u} where
  Code := envelope.Code
  El := envelope.El

namespace SemanticTarskiUniverse

variable (outer : SemanticTarskiUniverse.{uOuter, u})

/-- A family represented inside a Tarski universe.  Its first code decodes to
the index type; its second component assigns a code to each index. -/
abbrev InternalFamily :=
  Σ base : outer.Code, outer.El base → outer.Code

/-- Inclusion of one internally represented family in another.  Codes embed,
while the types decoded at corresponding codes remain equivalent. -/
structure InternalFamilyEmbedding
    (small large : outer.InternalFamily) where
  onBase : outer.El small.1 ↪ outer.El large.1
  onFibre : ∀ index,
    outer.El (small.2 index) ≃ outer.El (large.2 (onBase index))

namespace InternalFamilyEmbedding

variable {outer : SemanticTarskiUniverse.{uOuter, u}}
variable {first middle last : outer.InternalFamily}

/-- Every internal family embeds in itself. -/
def refl (family : outer.InternalFamily) :
    outer.InternalFamilyEmbedding family family where
  onBase := Function.Embedding.refl _
  onFibre := fun _ => Equiv.refl _

/-- Internal-family embeddings compose. -/
def trans
    (left : outer.InternalFamilyEmbedding first middle)
    (right : outer.InternalFamilyEmbedding middle last) :
    outer.InternalFamilyEmbedding first last where
  onBase := left.onBase.trans right.onBase
  onFibre := fun index =>
    (left.onFibre index).trans (right.onFibre (left.onBase index))

end InternalFamilyEmbedding

/-- Equivalence of internal families: equivalent index types, and equivalent
decoded fibres at corresponding indices. -/
structure InternalFamilyEquiv (left right : outer.InternalFamily) where
  onBase : outer.El left.1 ≃ outer.El right.1
  onFibre : ∀ index,
    outer.El (left.2 index) ≃ outer.El (right.2 (onBase index))

namespace InternalFamilyEquiv

variable {outer : SemanticTarskiUniverse.{uOuter, u}}

/-- Every internal family is equivalent to itself. -/
def refl (family : outer.InternalFamily) :
    outer.InternalFamilyEquiv family family where
  onBase := Equiv.refl _
  onFibre := fun _ => Equiv.refl _

/-- Equal internal families are equivalent. -/
def ofEq {left right : outer.InternalFamily} (h : left = right) :
    outer.InternalFamilyEquiv left right :=
  h ▸ refl left

/-- An equivalence of internal families is an embedding of internal families. -/
def toEmbedding {left right : outer.InternalFamily}
    (equivalence : outer.InternalFamilyEquiv left right) :
    outer.InternalFamilyEmbedding left right where
  onBase := equivalence.onBase.toEmbedding
  onFibre := equivalence.onFibre

end InternalFamilyEquiv

/-- An operator on families represented inside one universe. -/
abbrev FamilyOperator := outer.InternalFamily → outer.InternalFamily

/-- An internal family is closed under an operator when the operator's output
embeds back into the family. -/
def ClosedUnder (operator : outer.FamilyOperator)
    (family : outer.InternalFamily) : Prop :=
  Nonempty (outer.InternalFamilyEmbedding (operator family) family)

/-- A family operator that transports internal-family embeddings.  Functor
identity and composition laws are not needed for the finite-iteration theorem,
so this structure records exactly the monotonicity used there. -/
structure MonotoneFamilyOperator where
  onFamily : outer.FamilyOperator
  mapEmbedding : ∀ {small large},
    outer.InternalFamilyEmbedding small large →
      outer.InternalFamilyEmbedding (onFamily small) (onFamily large)

namespace MonotoneFamilyOperator

variable {outer : SemanticTarskiUniverse.{uOuter, u}}

/-- Finite iteration of an internal family operator. -/
def iterate (operator : outer.MonotoneFamilyOperator) :
    Nat → outer.InternalFamily → outer.InternalFamily
  | 0, family => family
  | n + 1, family => operator.onFamily (operator.iterate n family)

/-- Closure under one monotone family operator contains every finite iterate
of that operator. -/
theorem iterate_embeds_of_closed
    (operator : outer.MonotoneFamilyOperator)
    {family : outer.InternalFamily}
    (closed : outer.ClosedUnder operator.onFamily family) :
    ∀ n, Nonempty
      (outer.InternalFamilyEmbedding (operator.iterate n family) family) := by
  intro n
  induction n with
  | zero =>
      exact ⟨InternalFamilyEmbedding.refl family⟩
  | succ n inductionHypothesis =>
      rcases inductionHypothesis with ⟨earlier⟩
      rcases closed with ⟨oneStep⟩
      exact ⟨(operator.mapEmbedding earlier).trans oneStep⟩

end MonotoneFamilyOperator

end SemanticTarskiUniverse

/-! ## Universe embeddings and superuniverse closure -/

/-- Embedding of a small inner Tarski universe inside an outer one.  The
outer universe codes both the inner code carrier and every decoded inner type.
This is embedding data, not an assertion that the two universes are
definitionally identical. -/
structure UniverseEmbedding
    (outer : SemanticTarskiUniverse.{uOuter, u})
    (inner : SemanticTarskiUniverse.{u, u}) where
  codeCarrier : outer.Code
  decodeCodeCarrier : outer.El codeCarrier ≃ inner.Code
  decodedType : inner.Code → outer.Code
  decodeDecodedType : ∀ code,
    outer.El (decodedType code) ≃ inner.El code

/-- A universe-forming operation whose generated code carrier remains small at
the same object-language size.  This is the capability required before a
native superuniverse can internalize its outputs.  The ambient semantic
operator from `FamilyEnclosingUniverse` deliberately has a larger code
carrier, so it is not an inhabitant of this interface. -/
structure SmallFamilyEnclosingUniverseOperator where
  enclose : (A : Type u) → (B : A → Type u) →
    ClosedTarskiUniverseOver.{u, u} A B

/-- An outer universe has the superuniverse closure property for a selected
small universe operator when it embeds the generated universe for every
family already represented inside it. -/
def SuperuniverseFor
    (outer : SemanticTarskiUniverse.{uOuter, u})
    (operator : SmallFamilyEnclosingUniverseOperator.{u}) : Prop :=
  ∀ family : outer.InternalFamily,
    Nonempty
      (UniverseEmbedding outer
        (semanticUniverseOfEnvelope (operator.enclose
          (outer.El family.1)
          (fun index => outer.El (family.2 index)))))

/-! ## Whole-subuniverse closure -/

/-- Some ordinary subuniverse, taken as one internal family, is closed under
the operator: the operator applied to the whole subuniverse embeds back into
it. -/
def HasOperatorClosedSubuniverse
    (outer : SemanticTarskiUniverse.{uOuter, u})
    (IsOrdinarySubuniverse : outer.InternalFamily → Prop)
    (operator : outer.FamilyOperator) : Prop :=
  ∃ subuniverse : outer.InternalFamily,
    IsOrdinarySubuniverse subuniverse ∧
      outer.ClosedUnder operator subuniverse

/-- **Whole-subuniverse closure.** Every internal family operator has an
ordinary subuniverse closed under it, the operator being applied to the whole
subuniverse taken as one family.  This is not Mahlo reflection.  It fails
whenever codes grow strictly, that is, when every code has a code whose decoded
type does not embed into its own: the operator replacing the index code by the
larger code has no closed family, whatever predicate selects the ordinary
subuniverses (`MahloUniverses.not_wholeSubuniverseClosure_of_strictGrowth`;
here `Canary.finiteUniverse_not_wholeSubuniverseClosure`).  The powerset is
such a growth in the universe of `V_κ` for every infinite `κ`.
This notion was formerly named `MahloReflection`. -/
structure WholeSubuniverseClosure
    (outer : SemanticTarskiUniverse.{uOuter, u})
    (IsOrdinarySubuniverse : outer.InternalFamily → Prop) : Prop where
  closed : ∀ operator : outer.FamilyOperator,
    HasOperatorClosedSubuniverse outer IsOrdinarySubuniverse operator

/-! ## Mahlo reflection -/

namespace SemanticTarskiUniverse

/-- A family drawn from a subuniverse `(S, T)`: an index `a` of the
subuniverse, and for each element of the type decoded at `T a` another index
of the subuniverse. -/
abbrev SubuniverseFamily (outer : SemanticTarskiUniverse.{uOuter, u})
    (subuniverse : outer.InternalFamily) :=
  Σ index : outer.El subuniverse.1,
    outer.El (subuniverse.2 index) → outer.El subuniverse.1

/-- The internal family of the outer universe decoded from a family drawn from
a subuniverse. -/
def SubuniverseFamily.decode {outer : SemanticTarskiUniverse.{uOuter, u}}
    {subuniverse : outer.InternalFamily}
    (family : outer.SubuniverseFamily subuniverse) : outer.InternalFamily :=
  ⟨subuniverse.2 family.1, fun element => subuniverse.2 (family.2 element)⟩

/-- A subuniverse is closed on its families under an operator when the
operator sends the decoding of every family drawn from the subuniverse to a
family equivalent to the decoding of another family drawn from it. -/
def ClosedOnSubuniverseFamilies (outer : SemanticTarskiUniverse.{uOuter, u})
    (operator : outer.FamilyOperator) (subuniverse : outer.InternalFamily) :
    Prop :=
  ∀ family : outer.SubuniverseFamily subuniverse,
    ∃ image : outer.SubuniverseFamily subuniverse,
      Nonempty (outer.InternalFamilyEquiv (operator family.decode) image.decode)

/-- Positive example of closure: every subuniverse is closed on its families
under the identity operator. -/
theorem closedOnSubuniverseFamilies_id
    {outer : SemanticTarskiUniverse.{uOuter, u}}
    (subuniverse : outer.InternalFamily) :
    outer.ClosedOnSubuniverseFamilies id subuniverse :=
  fun family => ⟨family, ⟨InternalFamilyEquiv.refl _⟩⟩

end SemanticTarskiUniverse

/-- The outer universe reflects an operator into an ordinary subuniverse:
some subuniverse selected by the predicate is closed on its families under
the operator.  Formerly named `HasOperatorReflectingSubuniverse`. -/
def ReflectsOperator
    (outer : SemanticTarskiUniverse.{uOuter, u})
    (IsOrdinarySubuniverse : outer.InternalFamily → Prop)
    (operator : outer.FamilyOperator) : Prop :=
  ∃ subuniverse : outer.InternalFamily,
    IsOrdinarySubuniverse subuniverse ∧
      outer.ClosedOnSubuniverseFamilies operator subuniverse

/-- **Mahlo reflection.** Every internal family operator has an ordinary
subuniverse closed on its families under it: the operator, applied to each
family drawn from the subuniverse, returns a family equivalent to another
family drawn from the subuniverse.  Which internal families count as ordinary
subuniverses is an explicit parameter, and the content of the notion lies in
that predicate: a predicate admitting an empty subuniverse, one indexed by an
empty type, makes it trivial, since such a subuniverse has no families
(`mahloReflection_of_isEmpty`).  With the code families of `V_μ`, `μ < κ`
inaccessible, as the ordinary subuniverses of the universe of `V_κ`, it holds
exactly when `κ` is Mahlo (`MahloUniverses.mahloReflection_iff_isMahlo`).
Formerly named `SubuniverseMahloReflection`. -/
structure MahloReflection
    (outer : SemanticTarskiUniverse.{uOuter, u})
    (IsOrdinarySubuniverse : outer.InternalFamily → Prop) : Prop where
  reflect : ∀ operator : outer.FamilyOperator,
    ReflectsOperator outer IsOrdinarySubuniverse operator

/-- Mahlo reflection is monotone in the predicate selecting ordinary
subuniverses. -/
theorem MahloReflection.mono
    {outer : SemanticTarskiUniverse.{uOuter, u}}
    {IsOrdinary IsOrdinary' : outer.InternalFamily → Prop}
    (mahlo : MahloReflection outer IsOrdinary)
    (weaken : ∀ family, IsOrdinary family → IsOrdinary' family) :
    MahloReflection outer IsOrdinary' :=
  ⟨fun operator => by
    obtain ⟨subuniverse, ordinary, closed⟩ := mahlo.reflect operator
    exact ⟨subuniverse, weaken subuniverse ordinary, closed⟩⟩

/-- **A degenerate predicate.** A predicate admitting a subuniverse indexed by
an empty type gives Mahlo reflection: that subuniverse has no families, so it
is closed on its families under every operator. -/
theorem mahloReflection_of_isEmpty
    {outer : SemanticTarskiUniverse.{uOuter, u}}
    {IsOrdinarySubuniverse : outer.InternalFamily → Prop}
    (subuniverse : outer.InternalFamily)
    (ordinary : IsOrdinarySubuniverse subuniverse)
    (empty : IsEmpty (outer.El subuniverse.1)) :
    MahloReflection outer IsOrdinarySubuniverse :=
  ⟨fun _ => ⟨subuniverse, ordinary, fun family => (empty.false family.1).elim⟩⟩

/-- If some code decodes to an empty type, the predicate admitting every
family gives Mahlo reflection, through the subuniverse indexed by that code.
A predicate selecting ordinary subuniverses must exclude this subuniverse. -/
theorem mahloReflection_of_emptyCode
    {outer : SemanticTarskiUniverse.{uOuter, u}}
    (empty : outer.Code) (hempty : IsEmpty (outer.El empty)) :
    MahloReflection outer (fun _ => True) :=
  mahloReflection_of_isEmpty ⟨empty, fun index => (hempty.false index).elim⟩
    trivial hempty

/-! ## A positive one-level-up semantic host -/

/-- The ambient type hierarchy regarded only as an extensional embedding
host.  Its code carrier lives one level above the types it decodes. -/
def ambientUniverse : SemanticTarskiUniverse.{u + 1, u} where
  Code := Type u
  El := id

/-- The ambient host embeds every small Tarski universe. -/
def ambientEmbedding
    (inner : SemanticTarskiUniverse.{u, u}) :
    UniverseEmbedding ambientUniverse inner where
  codeCarrier := inner.Code
  decodeCodeCarrier := Equiv.refl inner.Code
  decodedType := inner.El
  decodeDecodedType := fun code => Equiv.refl (inner.El code)

/-- Consequently the one-level-up ambient host satisfies the embedding part
of superuniverse closure for any already-supplied small universe operator. -/
theorem ambient_superuniverseFor
    (operator : SmallFamilyEnclosingUniverseOperator.{u}) :
    SuperuniverseFor ambientUniverse operator := by
  intro family
  exact ⟨ambientEmbedding _⟩

/-- Negative control: the positive ambient embedding host really uses a
level shift.  Its code carrier cannot be represented by a type at the same
decoded level. -/
theorem ambient_embedding_requires_level_shift :
    ¬ ∃ code : Type u,
      Nonempty (code ≃ Type u) :=
  no_sameLevel_ambient_selfCode

/-! ## Finite controls -/

namespace Canary

/-- A small Tarski universe whose code `n` decodes to `Fin n`. -/
abbrev finiteUniverse : SemanticTarskiUniverse.{0, 0} where
  Code := Nat
  El := Fin

/-- A finite internal family with `n` base codes and singleton fibres. -/
def constantSingletonFamily (n : Nat) : finiteUniverse.InternalFamily :=
  ⟨n, fun _ => (1 : Nat)⟩

/-- The identity family operator, used only as a positive closure control. -/
def identityOperator : finiteUniverse.MonotoneFamilyOperator where
  onFamily := id
  mapEmbedding := fun embedding => embedding

theorem identityOperator_closed (n : Nat) :
    finiteUniverse.ClosedUnder identityOperator.onFamily
      (constantSingletonFamily n) :=
  ⟨SemanticTarskiUniverse.InternalFamilyEmbedding.refl _⟩

theorem identityOperator_all_iterates (n iterations : Nat) :
    Nonempty
      (finiteUniverse.InternalFamilyEmbedding
        (identityOperator.iterate iterations (constantSingletonFamily n))
        (constantSingletonFamily n)) :=
  identityOperator.iterate_embeds_of_closed (identityOperator_closed n) iterations

/-- A strict-growth family operator.  It adds one base code while retaining
singleton decoded fibres. -/
def successorOperator : finiteUniverse.FamilyOperator
  | ⟨base, _fibre⟩ => constantSingletonFamily (base + 1)

/-- No finite internal family is closed under strict base growth. -/
theorem successorOperator_not_closed
    (family : finiteUniverse.InternalFamily) :
    ¬ finiteUniverse.ClosedUnder successorOperator family := by
  rcases family with ⟨base, fibre⟩
  rintro ⟨embedding⟩
  have cardinality :=
    Nat.card_le_card_of_injective embedding.onBase embedding.onBase.injective
  change Nat.card (Fin (base + 1)) ≤ Nat.card (Fin base) at cardinality
  simp only [Nat.card_fin] at cardinality
  exact Nat.not_succ_le_self base cardinality

/-- The finite code universe has no whole-subuniverse closure, even with the
predicate admitting every family: no family is closed under strict base
growth.  Ordinary universe structure does not give closure of a whole
subuniverse under arbitrary family operators. -/
theorem finiteUniverse_not_wholeSubuniverseClosure :
    ¬ WholeSubuniverseClosure finiteUniverse (fun _ => True) := by
  intro whole
  rcases whole.closed successorOperator with
    ⟨subuniverse, _ordinary, closed⟩
  exact successorOperator_not_closed subuniverse closed

/-- Negative example of equivalence: families with one and with two indices
are not equivalent. -/
theorem not_internalFamilyEquiv_singleton_one_two :
    IsEmpty (finiteUniverse.InternalFamilyEquiv
      (constantSingletonFamily 1) (constantSingletonFamily 2)) :=
  ⟨fun equivalence => by
    have sizes := Fintype.card_congr equivalence.onBase
    change Fintype.card (Fin 1) = Fintype.card (Fin 2) at sizes
    simp at sizes⟩

/-- With the predicate admitting every family, the finite code universe has
Mahlo reflection although it has no strength: code `0` decodes to the empty
type. -/
theorem finiteUniverse_mahloReflection_trivial :
    MahloReflection finiteUniverse (fun _ => True) :=
  mahloReflection_of_emptyCode (outer := finiteUniverse) 0
    (show IsEmpty (Fin 0) by infer_instance)

/-- The subuniverse of the finite code universe with indices `0, …, n`, each
decoding to its own size. -/
def initialSegment (n : Nat) : finiteUniverse.InternalFamily :=
  ⟨n + 1, fun index => (index : Nat)⟩

/-- The constant operator returning a family with `n + 1` indices. -/
def constantOperator (n : Nat) : finiteUniverse.FamilyOperator :=
  fun _ => constantSingletonFamily (n + 1)

/-- Negative example of closure: the segment `0, …, n` is not closed on its
families under the operator returning a family with `n + 1` indices, since its
indices decode to types with at most `n` elements. -/
theorem initialSegment_not_closed (n : Nat) :
    ¬ finiteUniverse.ClosedOnSubuniverseFamilies (constantOperator n)
      (initialSegment n) := by
  intro closed
  obtain ⟨image, ⟨equivalence⟩⟩ :=
    closed ⟨(0 : Fin (n + 1)), fun _ => (0 : Fin (n + 1))⟩
  have sizes := Fintype.card_congr equivalence.onBase
  change Fintype.card (Fin (n + 1)) = Fintype.card (Fin (image.1 : Nat)) at sizes
  simp only [Fintype.card_fin] at sizes
  have below : (image.1 : Nat) < n + 1 := image.1.isLt
  omega

/-- The initial segments, as a predicate selecting ordinary subuniverses of
the finite code universe. -/
def IsInitialSegment (subuniverse : finiteUniverse.InternalFamily) : Prop :=
  ∃ n, subuniverse = initialSegment n

/-- No initial segment is an empty subuniverse. -/
theorem IsInitialSegment.nonempty {subuniverse : finiteUniverse.InternalFamily}
    (segment : IsInitialSegment subuniverse) :
    Nonempty (finiteUniverse.El subuniverse.1) := by
  obtain ⟨n, rfl⟩ := segment
  exact ⟨(0 : Fin (n + 1))⟩

/-- No initial segment is closed on its families under strict base growth:
the family at the largest index `n` is sent to a family with `n + 1` indices. -/
theorem initialSegment_not_closed_successorOperator (n : Nat) :
    ¬ finiteUniverse.ClosedOnSubuniverseFamilies successorOperator
      (initialSegment n) := by
  intro closed
  obtain ⟨image, ⟨equivalence⟩⟩ :=
    closed ⟨Fin.last n, fun _ => Fin.last n⟩
  have sizes := Fintype.card_congr equivalence.onBase
  change Fintype.card (Fin (n + 1)) = Fintype.card (Fin (image.1 : Nat)) at sizes
  simp only [Fintype.card_fin] at sizes
  have below : (image.1 : Nat) < n + 1 := image.1.isLt
  omega

/-- **The predicate decides.** With the initial segments as its ordinary
subuniverses, the finite code universe has no Mahlo reflection, while the
predicate admitting every family gives it
(`finiteUniverse_mahloReflection_trivial`). -/
theorem finiteUniverse_not_mahloReflection :
    ¬ MahloReflection finiteUniverse IsInitialSegment := by
  intro mahlo
  obtain ⟨_, ⟨n, rfl⟩, closed⟩ := mahlo.reflect successorOperator
  exact initialSegment_not_closed_successorOperator n closed

end Canary

#print axioms SemanticTarskiUniverse.MonotoneFamilyOperator.iterate_embeds_of_closed
#print axioms SemanticTarskiUniverse.closedOnSubuniverseFamilies_id
#print axioms MahloReflection.mono
#print axioms mahloReflection_of_isEmpty
#print axioms mahloReflection_of_emptyCode
#print axioms ambient_superuniverseFor
#print axioms ambient_embedding_requires_level_shift
#print axioms Canary.identityOperator_all_iterates
#print axioms Canary.successorOperator_not_closed
#print axioms Canary.finiteUniverse_not_wholeSubuniverseClosure
#print axioms Canary.not_internalFamilyEquiv_singleton_one_two
#print axioms Canary.finiteUniverse_mahloReflection_trivial
#print axioms Canary.initialSegment_not_closed
#print axioms Canary.IsInitialSegment.nonempty
#print axioms Canary.initialSegment_not_closed_successorOperator
#print axioms Canary.finiteUniverse_not_mahloReflection

end Mettapedia.TypeTheory.UniverseClosureProfiles
