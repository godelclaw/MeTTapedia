import Mettapedia.SetTheory.Hyperuniverse.Membership
import Mathlib.Data.Fintype.EquivFin
import Mathlib.SetTheory.Cardinal.Continuum
import Mathlib.SetTheory.Cardinal.Order
import Mathlib.Tactic
import Mathlib.Topology.MetricSpace.Perfect
import Mathlib.Topology.MetricSpace.Polish
import Mathlib.Topology.Metrizable.CompletelyMetrizable

/-!
# Cardinality of the closed-set limit

The limit is a countable inverse limit of finite discrete stages, hence a
compact metrizable Polish space of cardinality the continuum. A closed subset
is finite, countably infinite, or of that same cardinality, and each of these
three sizes is the member type of some code.
-/

set_option autoImplicit false

namespace Mettapedia.SetTheory.Hyperuniverse

open Set Topology TopologicalSpace TopologicalSpace.Compacts Filter Function

/-! ## Polish structure -/

instance (n : ℕ) : DiscreteTopology (Stage n) := Finite.instDiscreteTopology

instance : PolishSpace (∀ n : ℕ, Stage n) where
  toSecondCountableTopology := inferInstance
  toIsCompletelyMetrizableSpace := inferInstance

instance : PolishSpace N := toPi_isClosedEmbedding.polishSpace

instance : PolishSpace (N × N) where
  toSecondCountableTopology := inferInstance
  toIsCompletelyMetrizableSpace := inferInstance

/-! ## A proper preimage of the full stage -/

/-- Every point of the previous stage, except the full set. -/
def thin (n : ℕ) : Stage (n + 2) :=
  ⟨(univ : Set (Stage (n + 1))) \ {⊤}, (Set.toFinite _).isCompact⟩

theorem thin_ne_top (n : ℕ) : thin n ≠ ⊤ := by
  intro h
  have hset := congrArg (fun s : Stage (n + 2) => (s : Set (Stage (n + 1)))) h
  rw [thin, coe_mk] at hset
  have hmem : (⊤ : Stage (n + 1)) ∈ (univ \ {⊤} : Set (Stage (n + 1))) := by
    rw [hset]
    exact mem_univ _
  exact hmem.2 (mem_singleton _)

/-- The bonding map sends the full set to the full set. Stage zero has no full set,
so the index starts at the first compact-subset stage. -/
theorem bond_top (n : ℕ) : bond (n + 1) (⊤ : Stage (n + 2)) = ⊤ := by
  apply Compacts.ext
  simp only [bond_succ, coe_map]
  rw [coe_top, image_univ, coe_top]
  exact range_eq_univ.mpr (bond_surjective n)

/-- The full preimage of a stage point under the bonding map. -/
noncomputable def preimageAll {n : ℕ} (x : Stage (n + 1)) : Stage (n + 2) :=
  ⟨bond n ⁻¹' (x : Set (Stage n)),
    (x.isCompact.isClosed.preimage (bond_continuous n)).isCompact⟩

theorem bond_preimageAll {n : ℕ} (x : Stage (n + 1)) :
    bond (n + 1) (preimageAll x) = x := by
  apply Compacts.ext
  rw [preimageAll, bond_succ, coe_map, coe_mk]
  exact image_preimage_eq (x : Set (Stage n)) (bond_surjective n)

/-- One coherent step backward along the tower. -/
noncomputable def preimageStep : (n : ℕ) → Stage n → Stage (n + 1)
  | 0, _ => ⊤
  | _ + 1, x => preimageAll x

theorem preimageStep_bond : ∀ n (x : Stage n), bond n (preimageStep n x) = x
  | 0, _ => Subsingleton.elim _ _
  | _ + 1, x => bond_preimageAll x

theorem bond_thin (n : ℕ) : bond (n + 1) (thin n) = ⊤ := by
  induction n with
  | zero =>
    apply Compacts.ext
    ext z
    constructor
    · exact fun _ => mem_univ z
    · intro _
      rw [bond_succ, coe_map, thin, coe_mk, mem_image]
      exact ⟨⊥, ⟨mem_univ _, fun hmem => stage_one_bot_ne_top (mem_singleton_iff.mp hmem)⟩,
        Subsingleton.elim _ _⟩
  | succ n ih =>
    apply Compacts.ext
    ext z
    constructor
    · exact fun _ => mem_univ z
    · intro _
      rw [bond_succ, coe_map, thin, coe_mk, mem_image]
      by_cases hz : z = ⊤
      · exact ⟨thin n,
          ⟨mem_univ _, fun hmem => thin_ne_top n (mem_singleton_iff.mp hmem)⟩,
          ih.trans hz.symm⟩
      · obtain ⟨y, hy⟩ := bond_surjective (n + 1) z
        have hyne : y ≠ ⊤ := by
          intro hy_top
          apply hz
          rw [← hy, hy_top, bond_top n]
        exact ⟨y, ⟨mem_univ _, fun hmem => hyne (mem_singleton_iff.mp hmem)⟩, hy⟩

/-! ## Threads that agree with the full thread on longer and longer prefixes -/

/-- The full set at every positive stage, and the unique point at stage zero. -/
def topStage : (n : ℕ) → Stage n
  | 0 => PUnit.unit
  | _ + 1 => ⊤

theorem bond_topStage (n : ℕ) : bond n (topStage (n + 1)) = topStage n := by
  cases n with
  | zero => simp [topStage, bond_zero]
  | succ n =>
    simp only [topStage]
    exact bond_top n

theorem topStage_full (n : ℕ) : topStage n = fullStage n := by
  cases n <;> rfl

/-- Stage `n` of a thread that follows the full thread through stage `k + 1`
and then takes the thin preimage. -/
noncomputable def stageAt (k n : ℕ) : Stage n :=
  match n with
  | 0 => PUnit.unit
  | 1 => ⊤
  | n + 2 =>
    if _h : n < k then
      ⊤
    else if h : n = k then
      cast (congrArg Stage (congrArg (fun m => m + 2) h.symm)) (thin k)
    else
      preimageStep (n + 1) (stageAt k (n + 1))

theorem stageAt_of_lt (k n : ℕ) (h : n < k) : stageAt k (n + 2) = ⊤ := by
  rw [stageAt]
  exact dif_pos h

theorem stageAt_thin (k : ℕ) : stageAt k (k + 2) = thin k := by
  rw [stageAt]
  have hlt : ¬ k < k := lt_irrefl k
  rw [dif_neg hlt]
  have heq : k = k := rfl
  rw [dif_pos heq]
  rfl

theorem stageAt_of_gt (k n : ℕ) (hlt : ¬ n < k) (hne : n ≠ k) :
    stageAt k (n + 2) = preimageStep (n + 1) (stageAt k (n + 1)) := by
  rw [stageAt]
  rw [dif_neg hlt, dif_neg hne]

theorem stageAt_top (k n : ℕ) (hn : n ≤ k + 1) : stageAt k n = topStage n := by
  match n with
  | 0 => rfl
  | 1 => rfl
  | n + 2 =>
    rw [stageAt_of_lt k n (by omega)]
    rfl

theorem stageAt_compat (k n : ℕ) : bond n (stageAt k (n + 1)) = stageAt k n := by
  cases n with
  | zero => simp [stageAt, bond_zero]
  | succ n =>
    by_cases hlt : n < k
    · have hn1 : n + 1 ≤ k + 1 := by omega
      rw [stageAt_of_lt k n hlt, stageAt_top k (n + 1) hn1, bond_top n]
      simp [topStage]
    · by_cases heq : n = k
      · rw [heq, stageAt_thin k, bond_thin k, stageAt_top k (k + 1) le_rfl]
        simp [topStage]
      · rw [stageAt_of_gt k n hlt heq]
        exact preimageStep_bond (n + 1) (stageAt k (n + 1))

/-- The thread that first leaves the full thread at stage `k + 2`. -/
noncomputable def almostFull (k : ℕ) : N where
  atStage := stageAt k
  compat := stageAt_compat k

theorem proj_almostFull_top (k n : ℕ) (hn : n ≤ k + 1) :
    proj n (almostFull k) = topStage n :=
  stageAt_top k n hn

theorem proj_almostFull_thin (k : ℕ) : proj (k + 2) (almostFull k) = thin k :=
  stageAt_thin k

theorem almostFull_ne_full (k : ℕ) : almostFull k ≠ fullThread := by
  intro h
  have hproj := congrArg (proj (k + 2)) h
  rw [proj_almostFull_thin] at hproj
  have hfull : proj (k + 2) fullThread = ⊤ := by
    simp [proj, fullThread, fullStage]
  exact thin_ne_top k (hproj.trans hfull)

theorem almostFull_injective : Function.Injective almostFull := by
  intro k j h
  rcases lt_trichotomy k j with hlt | rfl | hgt
  · have hproj := congrArg (proj (k + 2)) h
    rw [proj_almostFull_thin, proj_almostFull_top j (k + 2) (by omega)] at hproj
    exact (thin_ne_top k hproj).elim
  · rfl
  · have hproj := congrArg (proj (j + 2)) h
    rw [proj_almostFull_thin, proj_almostFull_top k (j + 2) (by omega)] at hproj
    exact (thin_ne_top j hproj.symm).elim

example : almostFull 0 ≠ almostFull 1 :=
  fun h => almostFull_injective.ne (by decide : (0 : ℕ) ≠ 1) h

example : proj 2 (almostFull 0) = thin 0 := proj_almostFull_thin 0

theorem tendsto_almostFull : Tendsto almostFull atTop (𝓝 fullThread) := by
  rw [toPi_isClosedEmbedding.tendsto_nhds_iff]
  refine tendsto_pi_nhds.mpr ?_
  intro n
  refine tendsto_atTop_of_eventually_const (i₀ := n) ?_
  intro k hk
  change stageAt k n = fullStage n
  rw [stageAt_top k n (by omega), topStage_full]

/-! ## Compact subsets of the convergent sequence -/

/-- The full thread together with the threads that eventually leave it. -/
def threadSet : Set N := insert fullThread (range almostFull)

theorem isCompact_threadSet : IsCompact threadSet :=
  tendsto_almostFull.isCompact_insert_range

theorem isClosed_threadSet : IsClosed threadSet :=
  isCompact_threadSet.isClosed

theorem countable_threadSet : threadSet.Countable :=
  Set.Countable.insert fullThread (countable_range almostFull)

theorem infinite_threadSet : threadSet.Infinite :=
  Set.Infinite.mono (fun _ hx => Or.inr hx) (infinite_range_of_injective almostFull_injective)

instance : Infinite N := Infinite.of_injective almostFull almostFull_injective

/-- An open set meeting the convergent sequence only at the `k`-th term. -/
theorem exists_isolate (k : ℕ) :
    ∃ U : Set N, IsOpen U ∧ U ∩ threadSet = {almostFull k} := by
  obtain ⟨U, V, hU, hV, hkU, hfullV, hdisj⟩ := t2_separation (almostFull_ne_full k)
  obtain ⟨N0, hN⟩ :=
    Filter.eventually_atTop.mp
      (tendsto_almostFull.eventually (hV.mem_nhds hfullV))
  let bad : Set N := almostFull '' {n | n < N0 ∧ n ≠ k} ∪ {fullThread}
  have hbad_fin : bad.Finite := by
    refine Set.Finite.union ?_ (finite_singleton _)
    refine Set.Finite.image _ ?_
    exact (Finset.range N0).finite_toSet.subset fun n hn => Finset.mem_range.mpr hn.1
  have hbad_closed : IsClosed bad := hbad_fin.isClosed
  have hk_not : almostFull k ∉ bad := by
    intro hbad
    rcases hbad with ⟨n, ⟨_, hne⟩, heq⟩ | hfull
    · exact hne (almostFull_injective heq)
    · exact almostFull_ne_full k hfull
  refine ⟨U ∩ badᶜ, hU.inter hbad_closed.isOpen_compl, ?_⟩
  ext x
  constructor
  · intro hx
    rcases hx.2 with rfl | ⟨n, rfl⟩
    · exact absurd (Or.inr rfl) hx.1.2
    · have hnot_tail : ¬ N0 ≤ n := by
        intro hge
        exact hdisj.notMem_of_mem_left hx.1.1 (hN n hge)
      have hlt : n < N0 := Nat.lt_of_not_ge hnot_tail
      have heqk : n = k := by
        by_contra hne
        exact hx.1.2 (Or.inl ⟨n, ⟨hlt, hne⟩, rfl⟩)
      exact heqk ▸ rfl
  · intro hx
    rw [mem_singleton_iff] at hx
    subst hx
    exact ⟨⟨hkU, hk_not⟩, Or.inr ⟨k, rfl⟩⟩

/-- The full thread together with a selected subsequence. -/
def selected (S : Set ℕ) : Set N := insert fullThread (almostFull '' S)

theorem selected_injective : Function.Injective selected := by
  intro S T hST
  ext n
  have hmem (U : Set ℕ) : almostFull n ∈ selected U ↔ n ∈ U := by
    constructor
    · intro hn
      rcases hn with hfull | ⟨m, hm, heq⟩
      · exact absurd hfull (almostFull_ne_full n)
      · exact almostFull_injective heq ▸ hm
    · intro hn
      exact Or.inr ⟨n, hn, rfl⟩
  rw [← hmem S, hST, hmem T]

theorem isClosed_selected (S : Set ℕ) : IsClosed (selected S) := by
  classical
  choose U hU hsplit using exists_isolate
  let W : Set N := ⋃ k ∈ Sᶜ, U k
  have hW : IsOpen W := isOpen_biUnion fun _ _ => hU _
  have hEq : selected S = threadSet ∩ Wᶜ := by
    ext x
    constructor
    · intro hx
      have hxT : x ∈ threadSet := by
        rcases hx with rfl | ⟨n, _, rfl⟩
        · exact Or.inl rfl
        · exact Or.inr ⟨n, rfl⟩
      refine ⟨hxT, ?_⟩
      intro hxW
      obtain ⟨k, hk, hxk⟩ := mem_iUnion₂.mp hxW
      have hxeq : x = almostFull k := by
        have hxint : x ∈ U k ∩ threadSet := ⟨hxk, hxT⟩
        rw [hsplit k] at hxint
        exact mem_singleton_iff.mp hxint
      rcases hx with rfl | ⟨n, hn, rfl⟩
      · exact almostFull_ne_full k hxeq.symm
      · exact hk (almostFull_injective hxeq ▸ hn)
    · intro hx
      rcases hx.1 with rfl | ⟨n, rfl⟩
      · exact Or.inl rfl
      · have hn : n ∈ S := by
          by_contra hn
          have hmem : almostFull n ∈ W :=
            mem_iUnion₂.mpr ⟨n, hn, by
              have : almostFull n ∈ U n ∩ threadSet := by
                rw [hsplit n]
                exact mem_singleton _
              exact this.1⟩
          exact hx.2 hmem
        exact Or.inr ⟨n, hn, rfl⟩
  rw [hEq]
  exact isClosed_threadSet.inter hW.isClosed_compl

example : selected ∅ = {fullThread} := by
  ext x
  simp [selected]

example : almostFull 0 ∈ selected {0} := by
  refine Or.inr ⟨0, mem_singleton _, rfl⟩

noncomputable def codeOfSelected (S : Set ℕ) : N :=
  codeOfClosed (isClosed_selected S)

theorem codeOfSelected_injective : Function.Injective codeOfSelected := by
  intro S T h
  apply selected_injective
  ext z
  have hS : member z (codeOfSelected S) ↔ z ∈ selected S :=
    member_codeOfClosed (isClosed_selected S)
  have hT : member z (codeOfSelected T) ↔ z ∈ selected T :=
    member_codeOfClosed (isClosed_selected T)
  rw [← hS, ← hT, h]

/-! ## The carrier has the cardinality of the continuum -/

noncomputable def stageToNat (n : ℕ) : Stage n → ℕ :=
  fun x => (Fintype.equivFin (Stage n) x).val

theorem stageToNat_injective (n : ℕ) : Function.Injective (stageToNat n) := by
  intro a b h
  exact (Fintype.equivFin (Stage n)).injective (Fin.ext h)

noncomputable def piToNat : (∀ n, Stage n) → ℕ → ℕ :=
  fun f n => stageToNat n (f n)

theorem piToNat_injective : Function.Injective piToNat := by
  intro f g h
  funext n
  exact stageToNat_injective n (congrFun h n)

theorem mk_nat_arrow_nat : Cardinal.mk (ℕ → ℕ) = Cardinal.continuum.{0} := by
  rw [← Cardinal.power_def, Cardinal.mk_nat, Cardinal.aleph0_power_aleph0]

theorem mk_bool_arrow : Cardinal.mk (ℕ → Bool) = Cardinal.continuum.{0} := by
  rw [← Cardinal.power_def, Cardinal.mk_bool, Cardinal.mk_nat, Cardinal.two_power_aleph0]

theorem mk_carrier_le : Cardinal.mk N ≤ Cardinal.continuum.{0} :=
  calc
    Cardinal.mk N ≤ Cardinal.mk (∀ n, Stage n) :=
      Cardinal.mk_le_of_injective toPi_isClosedEmbedding.injective
    _ ≤ Cardinal.mk (ℕ → ℕ) := Cardinal.mk_le_of_injective piToNat_injective
    _ = Cardinal.continuum.{0} := mk_nat_arrow_nat

theorem continuum_le_mk_carrier : Cardinal.continuum.{0} ≤ Cardinal.mk N := by
  rw [← Cardinal.mk_set_nat]
  exact Cardinal.mk_le_of_injective codeOfSelected_injective

/-- The carrier has the cardinality of the continuum. -/
theorem mk_carrier : Cardinal.mk N = Cardinal.continuum.{0} :=
  le_antisymm mk_carrier_le continuum_le_mk_carrier

/-! ## Closed subsets are finite, countably infinite, or of size continuum -/

theorem closed_trichotomy {α : Type} [TopologicalSpace α] [PolishSpace α]
    (hα : Cardinal.mk α = Cardinal.continuum.{0}) {C : Set α} (hC : IsClosed C) :
    C.Finite ∨ (C.Countable ∧ ¬ C.Finite) ∨ Cardinal.mk C = Cardinal.continuum.{0} := by
  classical
  by_cases hfin : C.Finite
  · exact Or.inl hfin
  · by_cases hcount : C.Countable
    · exact Or.inr (Or.inl ⟨hcount, hfin⟩)
    · refine Or.inr (Or.inr ?_)
      obtain ⟨f, hf, _, hinj⟩ := hC.exists_nat_bool_injection_of_not_countable hcount
      let fC : (ℕ → Bool) → C := fun b => ⟨f b, hf (mem_range_self b)⟩
      have hfC : Function.Injective fC := by
        intro a b hab
        exact hinj (congrArg Subtype.val hab)
      have hle : Cardinal.continuum.{0} ≤ Cardinal.mk C := by
        rw [← mk_bool_arrow]
        exact Cardinal.mk_le_of_injective hfC
      have hge : Cardinal.mk C ≤ Cardinal.continuum.{0} := by
        rw [← hα]
        exact Cardinal.mk_le_of_injective
          (Subtype.val_injective : Function.Injective (fun z : C => (z : α)))
      exact le_antisymm hge hle

theorem closed_carrier_trichotomy {C : Set N} (hC : IsClosed C) :
    C.Finite ∨ (C.Countable ∧ ¬ C.Finite) ∨ Cardinal.mk C = Cardinal.continuum.{0} :=
  closed_trichotomy mk_carrier hC

theorem mk_prod_carrier : Cardinal.mk (N × N) = Cardinal.continuum.{0} := by
  rw [Cardinal.mk_prod, mk_carrier, Cardinal.lift_id, Cardinal.continuum_mul_self]

theorem closed_prod_trichotomy {C : Set (N × N)} (hC : IsClosed C) :
    C.Finite ∨ (C.Countable ∧ ¬ C.Finite) ∨ Cardinal.mk C = Cardinal.continuum.{0} :=
  closed_trichotomy mk_prod_carrier hC

/-! ## Each of the three sizes is the member type of a code -/

def membersUnivEquiv : {z : N // member z univSet} ≃ N where
  toFun z := z.1
  invFun z := ⟨z, member_univ z⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem finite_member_empty : Finite {z : N // member z emptySet} := by
  have : IsEmpty {z : N // member z emptySet} := ⟨fun z => member_empty z.1 z.2⟩
  infer_instance

noncomputable def memberThreadEquiv :
    {z : N // member z (codeOfClosed isClosed_threadSet)} ≃ threadSet where
  toFun z := ⟨z.1, (member_codeOfClosed isClosed_threadSet).mp z.2⟩
  invFun z := ⟨z.1, (member_codeOfClosed isClosed_threadSet).mpr z.2⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl

theorem exists_finite_code : ∃ s : N, Finite {z : N // member z s} :=
  ⟨emptySet, finite_member_empty⟩

theorem exists_countable_infinite_code :
    ∃ s : N, Countable {z : N // member z s} ∧ ¬ Finite {z : N // member z s} := by
  refine ⟨codeOfClosed isClosed_threadSet, ?_, ?_⟩
  · have : Countable threadSet := countable_threadSet
    exact Countable.of_equiv threadSet memberThreadEquiv.symm
  · intro hfin
    have : Finite threadSet := Finite.of_equiv _ memberThreadEquiv
    exact infinite_threadSet.not_finite this

theorem exists_continuum_code :
    ∃ s : N, Cardinal.mk {z : N // member z s} = Cardinal.continuum.{0} :=
  ⟨univSet, by rw [Cardinal.mk_congr membersUnivEquiv, mk_carrier]⟩

example : Finite {z : N // member z emptySet} := finite_member_empty

example : threadSet.Countable ∧ ¬ threadSet.Finite :=
  ⟨countable_threadSet, infinite_threadSet.not_finite⟩

example : Cardinal.mk N = Cardinal.continuum.{0} := mk_carrier

/-- A type of cardinality finite, countably infinite, or the continuum is the
member type of some code. -/
theorem exists_code_of_card {α : Type}
    (h : Cardinal.mk α ≤ Cardinal.aleph0 ∨ Cardinal.mk α = Cardinal.continuum.{0}) :
    ∃ s : N, Nonempty ({z : N // member z s} ≃ α) := by
  classical
  by_cases hc : Cardinal.mk α ≤ Cardinal.aleph0
  · rw [Cardinal.mk_le_aleph0_iff] at hc
    have : Countable α := hc
    by_cases hf : Finite α
    · obtain ⟨n, ⟨eFin⟩⟩ := Finite.exists_equiv_fin α
      obtain ⟨t, ht⟩ := Infinite.exists_subset_card_eq N n
      have hclosed : IsClosed (t : Set N) := t.finite_toSet.isClosed
      let code := codeOfClosed hclosed
      have eMem : {z : N // member z code} ≃ {z : N // z ∈ (t : Set N)} :=
        Equiv.subtypeEquivRight fun _ => member_codeOfClosed hclosed
      have eCoe : {z : N // z ∈ (t : Set N)} ≃ t :=
        Equiv.subtypeEquivRight fun _ => Finset.mem_coe
      have eCard : t ≃ Fin n := Finset.equivFinOfCardEq ht
      exact ⟨code, ⟨(eMem.trans eCoe).trans (eCard.trans eFin.symm)⟩⟩
    · have : Infinite α := not_finite_iff_infinite.mp hf
      have hmk : Cardinal.mk α = Cardinal.aleph0 :=
        (Cardinal.mk_le_aleph0_iff.mpr hc).antisymm (Cardinal.aleph0_le_mk α)
      have : Infinite threadSet := infinite_threadSet.to_subtype
      have hthread : Cardinal.mk threadSet = Cardinal.aleph0 :=
        (Cardinal.mk_le_aleph0_iff.mpr countable_threadSet).antisymm
          (Cardinal.aleph0_le_mk threadSet)
      obtain ⟨e⟩ := Cardinal.eq.mp (hthread.trans hmk.symm)
      exact ⟨codeOfClosed isClosed_threadSet, ⟨memberThreadEquiv.trans e⟩⟩
  · have hmk : Cardinal.mk α = Cardinal.continuum.{0} := h.resolve_left hc
    obtain ⟨e⟩ := Cardinal.eq.mp (hmk.trans mk_carrier.symm)
    exact ⟨univSet, ⟨membersUnivEquiv.trans e.symm⟩⟩

end Mettapedia.SetTheory.Hyperuniverse
