import Mettapedia.SetTheory.Hyperuniverse.Space
import Mettapedia.SetTheory.Profiles.Principles
import Mathlib.Topology.Maps.Proper.Basic
import Mathlib.Topology.Separation.Regular

/-!
# Membership read through the Vietoris fixed point

A point of the limit names the closed set which the homeomorphism assigns to it.
Extensionality, an empty set, and a universal set which belongs to itself follow.
Every closed class is named by a point. Formulas built from membership and
equality by conjunction, disjunction, both quantifiers, and bounded quantifiers
name closed classes. The Russell class is not named, and bounded separation
fails. Extensionality, an empty set, union, power, and a Quine atom hold.
Separation and membership induction fail.
-/

set_option autoImplicit false

namespace Mettapedia.SetTheory.Hyperuniverse

open Set Topology TopologicalSpace TopologicalSpace.Compacts
open Mettapedia.SetTheory.Profiles

/-! ## Membership -/

/-- `x` belongs to `y` when `x` lies in the closed set named by `y`. -/
def member (x y : N) : Prop := x ∈ (fixedHomeo y : Set N)

theorem fixedHomeo_decode (p : N) : fixedHomeo p = decode p := rfl

/-- The empty set, the point naming the empty closed set. -/
noncomputable def emptySet : N := fixedHomeo.symm ⊥

/-- The universal set, the point naming the whole space. -/
noncomputable def univSet : N := fixedHomeo.symm ⊤

theorem member_empty (z : N) : ¬ member z emptySet := by
  simp [member, emptySet]

theorem member_univ (z : N) : member z univSet := by
  simp [member, univSet]

theorem member_univ_self : member univSet univSet := member_univ univSet

example : ¬ member emptySet emptySet := member_empty emptySet

example : member emptySet univSet ∧ member univSet univSet :=
  ⟨member_univ emptySet, member_univ_self⟩

example : emptySet ≠ univSet := by
  intro h
  exact member_empty emptySet (h ▸ member_univ_self)

/-- Two points with the same members are equal. -/
theorem member_ext (x y : N) (h : ∀ z, member z x ↔ member z y) : x = y := by
  apply fixedHomeo.injective
  apply Compacts.ext
  ext z
  exact h z

theorem extensional_holds : Extensional member := member_ext

example : Extensional member := extensional_holds

example : emptySet ≠ univSet := by
  intro h
  exact member_empty emptySet (h ▸ member_univ_self)

/-- A closed class is named by a point. -/
noncomputable def codeOfClosed {s : Set N} (hs : IsClosed s) : N :=
  fixedHomeo.symm ⟨s, hs.isCompact⟩

theorem member_codeOfClosed {s : Set N} (hs : IsClosed s) {z : N} :
    member z (codeOfClosed hs) ↔ z ∈ s := by
  simp [member, codeOfClosed]

example : codeOfClosed isClosed_univ = univSet := by
  apply fixedHomeo.injective
  apply Compacts.ext
  rfl

example : codeOfClosed isClosed_empty ≠ univSet := by
  intro h
  have hmem : member emptySet (codeOfClosed isClosed_empty) := by
    rw [h]
    exact member_univ emptySet
  exact notMem_empty emptySet ((member_codeOfClosed isClosed_empty).mp hmem)

/-! ## The Russell class and separation -/

/-- No point names the Russell class. -/
theorem not_russell_set : ¬ ∃ s, ∀ x, member x s ↔ ¬ member x x := by
  rintro ⟨s, hs⟩
  have h := hs s
  by_cases hmem : member s s
  · exact (h.mp hmem) hmem
  · exact hmem (h.mpr hmem)

/-- Bounded separation by non-self-membership fails at the universal set. -/
theorem not_bounded_diagonal_separation :
    ¬ ∀ a, ∃ b, ∀ z, member z b ↔ member z a ∧ ¬ member z z := by
  intro h
  obtain ⟨b, hb⟩ := h univSet
  have hb' : ∀ z, member z b ↔ ¬ member z z := by
    intro z
    simpa [member_univ] using hb z
  by_cases hmem : member b b
  · exact ((hb' b).mp hmem) hmem
  · exact hmem ((hb' b).mpr hmem)

theorem not_separation : ¬ HasSeparation member := by
  intro h
  obtain ⟨b, hb⟩ := h univSet (fun z => ¬ member z z)
  have hb' : ∀ z, member z b ↔ ¬ member z z := by
    intro z
    simpa [member_univ] using hb z
  by_cases hmem : member b b
  · exact ((hb' b).mp hmem) hmem
  · exact hmem ((hb' b).mpr hmem)

example : ¬ HasSeparation member := not_separation

theorem has_empty : HasEmpty member := ⟨emptySet, member_empty⟩

example : HasEmpty member := has_empty

/-! ## Induction fails, because the universal set belongs to itself -/

theorem not_induction : ¬ HasMemInduction member := by
  intro h
  have hall : ∀ x, x ≠ univSet :=
    h (fun x => x ≠ univSet) fun x hx heq =>
      hx univSet (heq ▸ member_univ_self) rfl
  exact hall univSet rfl

example : ¬ HasMemInduction member := not_induction

example : HasEmpty member ∧ ¬ HasMemInduction member :=
  ⟨⟨emptySet, member_empty⟩, not_induction⟩

/-! ## A Quine atom -/

/-- The singleton compact subset. -/
def stageSingleton {n : ℕ} (x : Stage n) : Stage (n + 1) :=
  ⟨{x}, isCompact_singleton⟩

/-- The thread whose every stage is the singleton of the previous stage. -/
def quineStage : ∀ n, Stage n
  | 0 => PUnit.unit
  | n + 1 => stageSingleton (quineStage n)

theorem quine_compat : ∀ n, bond n (quineStage (n + 1)) = quineStage n
  | 0 => rfl
  | n + 1 => by
    apply Compacts.ext
    change (bond (n + 1) (quineStage (n + 2))).carrier = (quineStage (n + 1)).carrier
    rw [bond_succ, quineStage, quineStage, stageSingleton, stageSingleton]
    unfold Compacts.map
    change (bond n '' {quineStage (n + 1)}) = {quineStage n}
    rw [Set.image_singleton, quine_compat n]

/-- The Quine atom of the limit: its only member is itself. -/
def quine : N where
  atStage := quineStage
  compat := quine_compat

theorem quine_stage_succ (n : ℕ) :
    (quine.atStage (n + 1) : Set (Stage n)) = {quine.atStage n} := by
  change (quineStage (n + 1)).carrier = {quineStage n}
  rw [quineStage, stageSingleton]

theorem decode_quine : decode quine = ⟨{quine}, isCompact_singleton⟩ := by
  apply Compacts.ext
  ext q
  constructor
  · intro hq
    have hstage : ∀ n, proj n q = quine.atStage n := by
      intro n
      have hmem : proj n q ∈ (quine.atStage (n + 1) : Set (Stage n)) := by
        simpa [decode, decodeCarrier] using hq n
      rwa [quine_stage_succ, mem_singleton_iff] at hmem
    ext n
    exact hstage n
  · intro hq n
    have hq1 : q ∈ ({quine} : Set N) :=
      (Compacts.coe_mk {quine} isCompact_singleton) ▸ hq
    have hq' : q = quine := mem_singleton_iff.mp hq1
    subst hq'
    rw [quine_stage_succ, proj, mem_singleton_iff]

theorem fixedHomeo_quine : fixedHomeo quine = ⟨{quine}, isCompact_singleton⟩ := by
  rw [fixedHomeo_decode]
  exact decode_quine

theorem member_quine (z : N) : member z quine ↔ z = quine := by
  simp [member, fixedHomeo_quine, mem_singleton_iff]

theorem quine_holds : HasQuineAtom member := ⟨quine, member_quine⟩

example : member quine quine := (member_quine quine).mpr rfl

example : ¬ member emptySet quine := by
  intro h
  have heq : quine = emptySet := ((member_quine emptySet).mp h).symm
  exact member_empty emptySet (by simpa [heq] using (member_quine quine).mpr rfl)

/-! ## Union, power, and pairing -/

theorem isClosed_member_rel : IsClosed {p : N × N | member p.1 p.2} := by
  have hS : IsClosed {p : N × Compacts N | p.1 ∈ (p.2 : Set N)} := by
    rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
    intro ⟨x, K⟩ hx
    have hxK : x ∉ (K : Set N) := by simpa using hx
    have hdisj : Disjoint ({x} : Set N) (K : Set N) :=
      disjoint_singleton_left.mpr hxK
    obtain ⟨U, V, hU, hV, hxU, hKV, hUV⟩ :=
      normal_separation (isClosed_singleton (x := x)) K.isCompact.isClosed hdisj
    have hxU' : x ∈ U := hxU (mem_singleton x)
    refine mem_nhds_iff.mpr
      ⟨U ×ˢ {L : Compacts N | (L : Set N) ⊆ V}, ?_, hU.prod (isOpen_subsets_of_isOpen hV),
        ⟨hxU', subset_trans (by rfl : (K : Set N) ⊆ (K : Set N)) hKV⟩⟩
    intro ⟨y, L⟩ ⟨hy, hL⟩ hmem
    exact hUV.le_bot ⟨hy, hL (by simpa using hmem)⟩
  have hmap : Continuous fun p : N × N => (p.1, fixedHomeo p.2) :=
    continuous_fst.prodMk (fixedHomeo.continuous.comp continuous_snd)
  have hpre := hS.preimage hmap
  convert hpre using 1
  ext ⟨x, y⟩
  simp [member]

theorem union_holds : HasUnion member := by
  intro a
  let S : Set (Compacts N) := fixedHomeo '' (fixedHomeo a : Set N)
  have hS : IsCompact S :=
    (fixedHomeo a).isCompact.image fixedHomeo.continuous
  let unionCarrier : Set N := ⋃ K ∈ S, (K : Set N)
  have hunion : IsCompact unionCarrier := isCompact_biUnion_coe_of_isCompact hS
  refine ⟨fixedHomeo.symm ⟨unionCarrier, hunion⟩, ?_⟩
  intro z
  simp only [member, Homeomorph.apply_symm_apply]
  constructor
  · intro hz
    have hz' : z ∈ unionCarrier := (Compacts.coe_mk unionCarrier hunion) ▸ hz
    unfold unionCarrier at hz'
    rw [mem_iUnion₂] at hz'
    obtain ⟨K, hK, hzK⟩ := hz'
    obtain ⟨y, hy, rfl⟩ := hK
    exact ⟨y, hy, hzK⟩
  · rintro ⟨y, hy, hz⟩
    have hz' : z ∈ unionCarrier := by
      unfold unionCarrier
      rw [mem_iUnion₂]
      exact ⟨fixedHomeo y, ⟨y, hy, rfl⟩, hz⟩
    exact (Compacts.coe_mk unionCarrier hunion).symm ▸ hz'

theorem power_holds : HasPower member := by
  intro a
  let carrier : Set N := fixedHomeo ⁻¹' {K | (K : Set N) ⊆ fixedHomeo a}
  have hclosed : IsClosed carrier :=
    (isClosed_subsets_of_isClosed (fixedHomeo a).isCompact.isClosed).preimage fixedHomeo.continuous
  refine ⟨fixedHomeo.symm ⟨carrier, hclosed.isCompact⟩, ?_⟩
  intro z
  simp only [member, Homeomorph.apply_symm_apply, carrier]
  constructor
  · intro hz w hw
    exact hz hw
  · intro hz w hw
    exact hz w hw

theorem pairing_holds : HasPairing member := by
  intro x y
  refine ⟨fixedHomeo.symm ⟨{x, y}, (isCompact_singleton (x := y)).insert x⟩, ?_⟩
  intro z
  simp [member, mem_insert_iff, mem_singleton_iff]

example : HasUnion member := union_holds

example : ¬ HasSeparation member ∧ HasPower member := ⟨not_separation, power_holds⟩

/-! ## Positive formulas -/

/-- Positive formulas in `k` free variables. Parameters are points of the limit.
The last variable of a quantified formula is the bound variable. -/
inductive Pos : ℕ → Type where
  | varMem {k : ℕ} (i j : Fin k) : Pos k
  | varEq {k : ℕ} (i j : Fin k) : Pos k
  | memParam {k : ℕ} (i : Fin k) (p : N) : Pos k
  | paramMem {k : ℕ} (p : N) (i : Fin k) : Pos k
  | eqParam {k : ℕ} (i : Fin k) (p : N) : Pos k
  | conj {k : ℕ} (a b : Pos k) : Pos k
  | disj {k : ℕ} (a b : Pos k) : Pos k
  | univ {k : ℕ} (φ : Pos (k + 1)) : Pos k
  | ex {k : ℕ} (φ : Pos (k + 1)) : Pos k
  | bUniv {k : ℕ} (i : Fin k) (φ : Pos (k + 1)) : Pos k
  | bEx {k : ℕ} (i : Fin k) (φ : Pos (k + 1)) : Pos k

/-- The relation defined by a positive formula on an environment. -/
def realize {k : ℕ} : Pos k → (Fin k → N) → Prop
  | .varMem i j, e => member (e i) (e j)
  | .varEq i j, e => e i = e j
  | .memParam i p, e => member (e i) p
  | .paramMem p i, e => member p (e i)
  | .eqParam i p, e => e i = p
  | .conj a b, e => realize a e ∧ realize b e
  | .disj a b, e => realize a e ∨ realize b e
  | .univ φ, e => ∀ z, realize φ (Fin.cons z e)
  | .ex φ, e => ∃ z, realize φ (Fin.cons z e)
  | .bUniv i φ, e => ∀ z, member z (e i) → realize φ (Fin.cons z e)
  | .bEx i φ, e => ∃ z, member z (e i) ∧ realize φ (Fin.cons z e)

def classOf {k : ℕ} (φ : Pos k) : Set (Fin k → N) := {e | realize φ e}

example : realize (.varEq (0 : Fin 1) 0) (fun _ => emptySet) := rfl

example : ¬ realize (.memParam (0 : Fin 1) emptySet) (fun _ => emptySet) :=
  member_empty emptySet

theorem continuous_consEnv (k : ℕ) :
    Continuous fun p : N × (Fin k → N) =>
      Fin.cons (n := k) (α := fun _ => N) p.1 p.2 := by
  refine continuous_pi fun i => ?_
  cases i using Fin.cases with
  | zero => exact continuous_fst
  | succ i => exact (continuous_apply i).comp continuous_snd

theorem isClosed_forallSlice {E : Type} [TopologicalSpace E] {F : Set (N × E)}
    (hF : IsClosed F) :
    IsClosed {e : E | ∀ z, (z, e) ∈ F} := by
  have hcompl : {e : E | ∀ z, (z, e) ∈ F} = (Prod.snd '' Fᶜ)ᶜ := by
    ext e
    constructor
    · intro hall hmem
      rcases hmem with ⟨⟨z, e'⟩, hz, rfl⟩
      exact hz (hall z)
    · intro hall z
      classical
      exact by_contra fun hz =>
        hall ⟨(z, e), by simpa [mem_compl_iff] using hz, rfl⟩
  rw [hcompl]
  exact (isOpenMap_snd Fᶜ hF.isOpen_compl).isClosed_compl

theorem isClosed_existsSlice {E : Type} [TopologicalSpace E] {F : Set (N × E)}
    (hF : IsClosed F) :
    IsClosed {e : E | ∃ z, (z, e) ∈ F} := by
  have hset : {e : E | ∃ z, (z, e) ∈ F} = Prod.snd '' F := by
    ext e
    simp [mem_image, Prod.exists]
  rw [hset]
  exact isClosedMap_snd_of_compactSpace F hF

theorem isClosed_subsetSlice {E : Type} [TopologicalSpace E] {F : Set (N × E)}
    (hF : IsClosed F) :
    IsClosed {p : Compacts N × E | ∀ z ∈ (p.1 : Set N), (z, p.2) ∈ F} := by
  rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
  intro ⟨K, e⟩ hnot
  have hnot' : ∃ z, z ∈ (K : Set N) ∧ (z, e) ∉ F := by
    classical
    simpa [not_forall, Classical.not_imp] using hnot
  obtain ⟨z, hzK, hzF⟩ := hnot'
  have hnhds : Fᶜ ∈ 𝓝 (z, e) := hF.isOpen_compl.mem_nhds (by simpa using hzF)
  obtain ⟨U, V, hU, hzU, hV, heV, hUV⟩ := mem_nhds_prod_iff'.mp hnhds
  refine mem_nhds_iff.mpr
    ⟨({L : Compacts N | ((L : Set N) ∩ U).Nonempty}) ×ˢ V, ?_,
      (isOpen_inter_nonempty_of_isOpen hU).prod hV, ?_⟩
  · intro ⟨L, e'⟩ ⟨hL, he'⟩ hsub
    obtain ⟨z', hzL, hzU'⟩ := hL
    have : (z', e') ∈ F := hsub z' hzL
    exact (hUV ⟨hzU', he'⟩) this
  · exact ⟨⟨z, hzK, hzU⟩, heV⟩

theorem class_closed {k : ℕ} (φ : Pos k) : IsClosed (classOf φ) := by
  induction φ with
  | varMem i j =>
    have hmap : Continuous fun e : Fin _ → N => (e i, e j) :=
      (continuous_apply i).prodMk (continuous_apply j)
    simpa [classOf, realize] using isClosed_member_rel.preimage hmap
  | varEq i j =>
    simpa [classOf, realize] using (isClosed_eq (continuous_apply i) (continuous_apply j))
  | memParam i p =>
    have hset : IsClosed (fixedHomeo p : Set N) := (fixedHomeo p).isCompact.isClosed
    have happ : Continuous (fun e : Fin _ → N => e i) := continuous_apply i
    have hpre := hset.preimage happ
    rw [show classOf (.memParam i p) =
        (fun e => e i) ⁻¹' (fixedHomeo p : Set N) by
      ext e
      simp [classOf, realize, member]]
    exact hpre
  | paramMem p i =>
    have hset : IsClosed
        {K : Compacts N | ((K : Set N) ∩ ({p} : Set N)).Nonempty} :=
      isClosed_inter_nonempty_of_isClosed isClosed_singleton
    have hcarrier : {K : Compacts N | p ∈ (K : Set N)} =
        {K : Compacts N | ((K : Set N) ∩ ({p} : Set N)).Nonempty} := by
      ext K
      simp
    have hK : IsClosed {y : N | member p y} := by
      rw [show {y : N | member p y} =
          fixedHomeo ⁻¹' {K : Compacts N | p ∈ (K : Set N)} by
        ext y
        simp [member]]
      exact (hcarrier ▸ hset).preimage fixedHomeo.continuous
    have happ : Continuous (fun e : Fin _ → N => e i) := continuous_apply i
    have hpre := hK.preimage happ
    rw [show classOf (.paramMem p i) =
        (fun e => e i) ⁻¹' {y : N | member p y} by
      ext e
      simp [classOf, realize]]
    exact hpre
  | eqParam i p =>
    have happ : Continuous (fun e : Fin _ → N => e i) := continuous_apply i
    have hpre := (isClosed_singleton (x := p)).preimage happ
    rw [show classOf (.eqParam i p) = (fun e => e i) ⁻¹' ({p} : Set N) by
      ext e
      simp [classOf, realize]]
    exact hpre
  | conj a b iha ihb =>
    simpa [classOf, realize, ofPred_and] using iha.inter ihb
  | disj a b iha ihb =>
    simpa [classOf, realize, ofPred_or] using iha.union ihb
  | univ φ ih =>
    have hF : IsClosed {p : N × (Fin _ → N) | Fin.cons p.1 p.2 ∈ classOf φ} :=
      ih.preimage (continuous_consEnv _)
    simpa [classOf, realize] using isClosed_forallSlice hF
  | ex φ ih =>
    have hF : IsClosed {p : N × (Fin _ → N) | Fin.cons p.1 p.2 ∈ classOf φ} :=
      ih.preimage (continuous_consEnv _)
    simpa [classOf, realize] using isClosed_existsSlice hF
  | bUniv i φ ih =>
    have hF : IsClosed {p : N × (Fin _ → N) | Fin.cons p.1 p.2 ∈ classOf φ} :=
      ih.preimage (continuous_consEnv _)
    have hW := isClosed_subsetSlice hF
    have hmap : Continuous fun e : Fin _ → N => (fixedHomeo (e i), e) :=
      (fixedHomeo.continuous.comp (continuous_apply i)).prodMk continuous_id
    have hpre := hW.preimage hmap
    convert hpre using 1
    ext e
    constructor
    · intro hall z hz
      exact hall z hz
    · intro hall z hz
      exact hall z hz
  | bEx i φ ih =>
    have hmem : IsClosed {p : N × (Fin _ → N) | member p.1 (p.2 i)} := by
      have hfun : Continuous (fun p : N × (Fin _ → N) => (p.1, p.2 i)) :=
        continuous_fst.prodMk ((continuous_apply i).comp continuous_snd)
      exact isClosed_member_rel.preimage hfun
    have hF : IsClosed {p : N × (Fin _ → N) | Fin.cons p.1 p.2 ∈ classOf φ} :=
      ih.preimage (continuous_consEnv _)
    have hG : IsClosed {p : N × (Fin _ → N) | member p.1 (p.2 i) ∧ Fin.cons p.1 p.2 ∈ classOf φ} :=
      hmem.inter hF
    simpa [classOf, realize] using isClosed_existsSlice hG

/-- The class of a positive formula in one free variable, read as a subset of the limit. -/
def classOn (φ : Pos 1) : Set N := {x | realize φ fun _ => x}

theorem classOn_closed (φ : Pos 1) : IsClosed (classOn φ) := by
  have hmap : Continuous fun x : N => fun _ : Fin 1 => x := continuous_pi fun _ => continuous_id
  simpa [classOn, classOf] using (class_closed φ).preimage hmap

/-- The point naming the class of a positive formula in one free variable. -/
noncomputable def setOfFormula (φ : Pos 1) : N := codeOfClosed (classOn_closed φ)

theorem member_setOfFormula (φ : Pos 1) (x : N) :
    member x (setOfFormula φ) ↔ realize φ (fun _ => x) := by
  simp [setOfFormula, member_codeOfClosed, classOn]

example : setOfFormula (.varEq 0 0) = univSet := by
  apply member_ext
  intro z
  simp [member_setOfFormula, realize, member_univ]

example : setOfFormula (.memParam 0 emptySet) = emptySet := by
  apply member_ext
  intro z
  simp [member_setOfFormula, realize, member_empty]

end Mettapedia.SetTheory.Hyperuniverse
