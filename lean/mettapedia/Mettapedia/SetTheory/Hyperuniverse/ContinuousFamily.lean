import Mettapedia.SetTheory.Hyperuniverse.Capabilities
import Mettapedia.SetTheory.Hyperuniverse.Continuum
import Mathlib.Topology.Constructions.SumProd

/-!
# Continuous families of codes

A family of codes indexed by the members of one code is continuous when that
indexing map into the carrier is continuous. For every continuous family the
dependent sum of member types is equinumerous with a closed subset of a
product of two copies of the carrier, hence with the members of some code.
No hypothesis that the continuum is the first uncountable cardinal is used.
A family that jumps at the full thread is not continuous. Constant indexing
by a two-point code is continuous, and the corresponding dependent product is
too large to be the member type of any code.
-/

set_option autoImplicit false

namespace Mettapedia.SetTheory.Hyperuniverse

open Classical Set Filter Topology
open Mettapedia.TypeTheory.TarskiUniverseCapabilities

/-- The members of a code form a closed set. -/
theorem isClosed_members (s : N) : IsClosed {z : N | member z s} := by
  have h : {z : N | member z s} = (fixedHomeo s : Set N) := by
    ext z
    simp [member]
  rw [h]
  exact (fixedHomeo s).isCompact'.isClosed

example : IsClosed {z : N | member z emptySet} := isClosed_members emptySet

/-- The Quine atom at the full thread and the empty code at every other point. -/
noncomputable def jumpFamily (z : {w : N // member w univSet}) : N :=
  if z.1 = fullThread then quine else emptySet

theorem emptySet_ne_quine : emptySet ≠ quine := by
  intro h
  have hmem : member quine quine := (member_quine quine).2 rfl
  rw [← h] at hmem
  exact member_empty emptySet hmem

theorem not_continuous_jumpFamily : ¬ Continuous jumpFamily := by
  intro hcont
  let points : ℕ → {w : N // member w univSet} :=
    fun k => ⟨almostFull k, member_univ (almostFull k)⟩
  have hseq : Tendsto points atTop (𝓝 ⟨fullThread, member_univ fullThread⟩) := by
    rw [nhds_induced (Subtype.val : {w : N // member w univSet} → N)]
    rw [tendsto_comap_iff]
    have hcomp : Subtype.val ∘ points = almostFull := by
      funext k
      rfl
    rw [hcomp]
    exact tendsto_almostFull
  have htarget : jumpFamily ⟨fullThread, member_univ fullThread⟩ = quine := by
    rw [jumpFamily, if_pos rfl]
  have hlim : Tendsto (jumpFamily ∘ points) atTop (𝓝 quine) := by
    rw [← htarget]
    exact (hcont.tendsto _).comp hseq
  have hconstFun : jumpFamily ∘ points = fun _ => emptySet := by
    funext k
    rw [Function.comp_apply, jumpFamily, if_neg (almostFull_ne_full k)]
  have hlimEmpty : Tendsto (jumpFamily ∘ points) atTop (𝓝 emptySet) := by
    rw [hconstFun]
    exact tendsto_const_nhds
  exact emptySet_ne_quine (tendsto_nhds_unique hlimEmpty hlim)

example : jumpFamily ⟨fullThread, member_univ fullThread⟩ = quine := by
  rw [jumpFamily, if_pos rfl]

example : jumpFamily ⟨almostFull 0, member_univ (almostFull 0)⟩ = emptySet := by
  rw [jumpFamily, if_neg (almostFull_ne_full 0)]

example : Continuous (fun (_ : {z : N // member z univSet}) => emptySet) :=
  continuous_const

example : ¬ Continuous jumpFamily := not_continuous_jumpFamily

/-- Membership proofs do not distinguish dependent sums of member types. -/
theorem depSum_ext {a : N} {B : {x : N // member x a} → N}
    {p q : Σ arg : {x : N // member x a}, {y : N // member y (B arg)}}
    (hbase : p.1.1 = q.1.1) (hfiber : p.2.1 = q.2.1) : p = q := by
  rcases p with ⟨⟨px, hpx⟩, ⟨py, _⟩⟩
  rcases q with ⟨⟨qx, hqx⟩, ⟨qy, _⟩⟩
  cases hbase
  cases hfiber
  refine Sigma.ext (Subtype.ext rfl) ?_
  have hcode : B ⟨px, hpx⟩ = B ⟨px, hqx⟩ := congrArg B (Subtype.ext rfl)
  have hpred : ∀ z : N, member z (B ⟨px, hpx⟩) ↔ member z (B ⟨px, hqx⟩) := by
    intro z
    rw [hcode]
  exact (Subtype.heq_iff_coe_eq hpred).2 rfl

/-- Dependent-sum closure for families that vary continuously in the code. -/
def ContinuousFamilySigmaClosed : Prop :=
  ∀ (a : N) (B : {x : N // member x a} → N),
    Continuous B →
    ∃ s : N,
      Nonempty ({z : N // member z s} ≃
        (Σ arg : {x : N // member x a}, {y : N // member y (B arg)}))

/-- Every continuous family of codes has a code for its dependent sum. -/
theorem continuousFamily_sigmaClosed : ContinuousFamilySigmaClosed := by
  intro a B hB
  let sigmaType := Σ arg : {x : N // member x a}, {y : N // member y (B arg)}
  let pairOf : sigmaType → N × N := fun p => (p.1.1, p.2.1)
  have hinj : Function.Injective pairOf := by
    intro p q hpq
    exact depSum_ext (congrArg Prod.fst hpq) (congrArg Prod.snd hpq)
  let D := {x : N // member x a}
  let fiber : Set (D × N) := {p | member p.2 (B p.1)}
  have hmap : Continuous (fun p : D × N => (p.2, B p.1)) :=
    continuous_snd.prodMk (hB.comp continuous_fst)
  have hfiber : IsClosed fiber := isClosed_member_rel.preimage hmap
  let inc : D × N → N × N := Prod.map Subtype.val id
  have hinc : IsClosedEmbedding inc :=
    (isClosed_members a).isClosedEmbedding_subtypeVal.prodMap IsClosedEmbedding.id
  have himage : IsClosed (inc '' fiber) := hinc.isClosedMap fiber hfiber
  have hrange : range pairOf = inc '' fiber := by
    ext q
    constructor
    · rintro ⟨p, rfl⟩
      exact ⟨(p.1, p.2.1), p.2.2, rfl⟩
    · rintro ⟨p, hp, rfl⟩
      exact ⟨⟨p.1, ⟨p.2, hp⟩⟩, rfl⟩
  have hClosed : IsClosed (range pairOf) := by
    rw [hrange]
    exact himage
  have hmk : Cardinal.mk (range pairOf) = Cardinal.mk sigmaType :=
    Cardinal.mk_range_eq pairOf hinj
  have hcard :
      Cardinal.mk sigmaType ≤ Cardinal.aleph0 ∨
        Cardinal.mk sigmaType = Cardinal.continuum.{0} := by
    rw [← hmk]
    rcases closed_prod_trichotomy hClosed with hfin | ⟨hcount, _⟩ | hcont
    · have : Finite (range pairOf) := hfin
      exact Or.inl (Cardinal.mk_le_aleph0_iff.mpr inferInstance)
    · exact Or.inl (Cardinal.mk_le_aleph0_iff.mpr hcount)
    · exact Or.inr hcont
  exact exists_code_of_card hcard

example : ContinuousFamilySigmaClosed := continuousFamily_sigmaClosed

/-- Continuous indexing is still not closed under dependent products.
The constant two-point code over the universal set decodes to a function
space strictly larger than the carrier. -/
theorem not_continuous_pi_closed :
    ¬ ∀ (a : N) (B : {x : N // member x a} → N),
      Continuous B →
      ∃ p : N,
        Nonempty ({z : N // member z p} ≃
          ((arg : {x : N // member x a}) → {y : N // member y (B arg)})) := by
  intro h
  obtain ⟨p, ⟨e⟩⟩ := h univSet (fun _ => bitSet) continuous_const
  have ePi :
      ((arg : {x : N // member x univSet}) → {y : N // member y bitSet}) ≃ (N → Bool) :=
    Equiv.arrowCongr elUnivSet elBit
  have eAll : {z : N // member z p} ≃ (N → Bool) := e.trans ePi
  have hcard : Cardinal.mk {z : N // member z p} = 2 ^ Cardinal.mk N := by
    rw [Cardinal.mk_congr eAll, ← Cardinal.power_def, Cardinal.mk_bool]
  have hle : Cardinal.mk {z : N // member z p} ≤ Cardinal.mk N :=
    Cardinal.mk_le_of_injective Subtype.val_injective
  have hlt : Cardinal.mk N < 2 ^ Cardinal.mk N := Cardinal.cantor (Cardinal.mk N)
  rw [← hcard] at hlt
  exact not_le_of_gt hlt hle

end Mettapedia.SetTheory.Hyperuniverse
