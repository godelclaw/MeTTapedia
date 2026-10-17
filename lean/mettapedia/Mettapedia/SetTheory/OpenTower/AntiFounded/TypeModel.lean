import Mettapedia.SetTheory.OpenTower.AntiFounded.InternalAntiFoundation
import Mettapedia.TypeTheory.MaterialSets.Hypersets.FamilyCwf

/-!
# Π, Σ, identity and universes inside a closed stage

The hyperset model of dependent types (`FamilyCwf.hypersetCwf`) takes contexts to be hypersets,
types to be hyperset-valued families on the members of a context, and terms to be sections;
context extension is the set of Kuratowski pairs, `Π` is the set of function graphs and `Σ` the
set of pairs, with β, η and substitution laws proved there. This module shows that a closed stage
`U` carves out a sub-model: call a context *small* when it is a member of `U`, and a type *small*
(`SmallFamily U A`) when all its values are.

**Closure.** Small types are stable under substitution (`smallFamily_comp`), the terminal
context is small (`HClosed.terminalContext_mem`), the extension of a small context by a small
type is small (`HClosed.extension_mem`), and `Π`, `Σ` and the extensional identity type of small
types are small (`HClosed.smallFamily_pi`, `HClosed.smallFamily_sigma`,
`HClosed.smallFamily_identity`). The engine is that a closed stage contains the set of
dependent pairs and the set of dependent function graphs of its members
(`HClosed.sigmaSet_mem`, `HClosed.dependentProduct_mem`).

**Universes.** For `ℵ₀ ≤ μ < κ` with `κ` inaccessible, `B_μ` is a member of `B_κ`
(`branching_mem_branching`); it is included in it (`branching_mono`). So in the sub-model of
`B_κ` the constant family `B_μ` is a small type (`smallFamily_universe`) whose terms decode to
types small for `B_μ` (`smallFamily_decode`): a universe à la Tarski whose codes are the types
themselves, closed under `Π` and `Σ` because `B_μ` is itself a closed stage when `μ` is `ℵ₀` or
inaccessible. At the level of terms: `piCode` and `sigmaCode` are codes in the universe, and
decoding them gives `Π` and `Σ` of the decoded types (`decode_piCode`, `decode_sigmaCode`); a
smaller universe has a code in a larger one (`universeCode`, `decode_universeCode`). The universes are cumulative and form a chain. `B_κ` is not a member of itself
(`HClosed.notMem_self`): no universe contains itself.

Identity in this model is equality of hypersets, which is bisimilarity
(`HSet.bisimilar_iff_eq`); it is extensional, so the model validates uniqueness of identity
proofs. A finer identity lives on presentations, not in this model.

**Controls.** The family `{Ω}` over the terminal context is small in `B_ℵ₀`
(`quineFamily_small`), so cyclic types are types of the sub-model; `Π` from it to itself is the
singleton of the graph `{⟨Ω, Ω⟩}` (existing `HSet.dependentProduct_quine_singleton`). The
hyperset of `V_ω` does not contain `{Ω}` (`quineFamily_not_small_vonNeumann`).
-/

set_option autoImplicit false

namespace Mettapedia.SetTheory.OpenTower.AntiFounded

open Mettapedia.TypeTheory.MaterialSets
open Mettapedia.TypeTheory.MaterialSets.Hypersets
open Mettapedia.TypeTheory.MaterialSets.Hypersets.FamilyCwf
open Cardinal
open scoped ZFSet

universe u

/-! ## Replacement along the members of a member -/

/-- A hyperset whose members are the values of a family on the members of a member, all in the
stage, is in the stage. -/
theorem HClosed.mem_of_family {U X b : HSet.{u}} (hU : HClosed U) (hX : X ∈ U)
    {F : Elements X → HSet.{u}} (hb : ∀ y, y ∈ b ↔ ∃ a, F a = y) (hF : ∀ a, F a ∈ U) :
    b ∈ U := by
  classical
  refine hU.image_mem hX (fun y hy => ?_)
    ⟨fun x => if h : x ∈ X then F ⟨x, h⟩ else ∅, fun y => ?_⟩
  · obtain ⟨a, rfl⟩ := (hb y).mp hy
    exact hF a
  · rw [hb]
    constructor
    · rintro ⟨⟨x, hx⟩, rfl⟩
      exact ⟨x, hx, by simp only [dif_pos hx]⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, by simp only [dif_pos hx]⟩

/-! ## Dependent pairs and function graphs -/

section Sets

variable (p : HSet.Presentation.{u})

/-- The set of dependent pairs over a member, with fibres in the stage, is in the stage. -/
theorem HClosed.sigmaSet_mem {U X : HSet.{u}} (hU : HClosed U) (hX : X ∈ U)
    {B : Elements X → HSet.{u}} (hB : ∀ a, B a ∈ U) :
    sigmaSet (HSet.dependentReplacement p) HSet.union HSet.kuratowski X B ∈ U := by
  set S := sigmaSet (HSet.dependentReplacement p) HSet.union HSet.kuratowski X B
  let fibre : Elements X → HSet.{u} := fun a =>
    HSet.sep (fun z => ∃ b : Elements (B a), HSet.kpair a.1 b.1 = z) S
  have memFibre : ∀ a z, z ∈ fibre a ↔ ∃ b : Elements (B a), HSet.kpair a.1 b.1 = z := by
    intro a z
    simp only [fibre, HSet.mem_sep]
    exact ⟨fun h => h.2, fun h => ⟨HSet.mem_sigmaSet_iff.mpr ⟨a, h.choose, h.choose_spec⟩, h⟩⟩
  have fibreIn : ∀ a, fibre a ∈ U := fun a =>
    hU.mem_of_family (hB a) (memFibre a) fun b =>
      hU.kpair_mem (hU.transitive hX a.2) (hU.transitive (hB a) b.2)
  let C : HSet.{u} := HSet.sep (fun s => ∃ a, fibre a = s) (HSet.powerset S)
  have memC : ∀ s, s ∈ C ↔ ∃ a, fibre a = s := by
    intro s
    simp only [C, HSet.mem_sep, HSet.mem_powerset]
    refine ⟨fun h => h.2, fun h => ⟨?_, h⟩⟩
    obtain ⟨a, rfl⟩ := h
    exact HSet.subset_iff.mpr fun z hz => (HSet.mem_sep.mp hz).1
  have equal : S = HSet.sUnion C := by
    apply HSet.ext
    intro z
    rw [HSet.mem_sUnion]
    constructor
    · intro hz
      obtain ⟨a, b, rfl⟩ := HSet.mem_sigmaSet_iff.mp hz
      exact ⟨fibre a, (memC _).mpr ⟨a, rfl⟩, (memFibre a _).mpr ⟨b, rfl⟩⟩
    · rintro ⟨s, hs, hz⟩
      obtain ⟨a, rfl⟩ := (memC s).mp hs
      exact (HSet.mem_sep.mp hz).1
  rw [equal]
  exact hU.union_mem (hU.mem_of_family hX memC fibreIn)

/-- The set of dependent function graphs over a member, with fibres in the stage, is in the
stage. -/
theorem HClosed.dependentProduct_mem {U X : HSet.{u}} (hU : HClosed U) (hX : X ∈ U)
    {B : Elements X → HSet.{u}} (hB : ∀ a, B a ∈ U) :
    HSet.dependentProduct p X B ∈ U := by
  refine hU.subset_mem (hU.power_mem (hU.sigmaSet_mem p hX hB)) (HSet.subset_iff.mpr ?_)
  intro G hG
  exact HSet.mem_powerset.mpr (HSet.subset_iff.mpr (HSet.mem_dependentProduct_iff.mp hG).1)

end Sets

/-! ## The sub-model of small contexts and small types -/

/-- A type is small for `U` when every value is a member of `U`. -/
def SmallFamily (U : HSet.{u}) {Γ : HSet.{u}} (A : Family Γ) : Prop :=
  ∀ γ, A γ ∈ U

variable (p : HSet.Presentation.{u}) {U : HSet.{u}}

/-- Small types are stable under substitution. -/
theorem smallFamily_comp {Γ Δ : HSet.{u}} {A : Family Δ} (hA : SmallFamily U A)
    (σ : Substitution Γ Δ) : SmallFamily U (A ∘ σ) :=
  fun γ => hA (σ γ)

/-- The terminal context `{∅}` is small in every nonempty closed stage. -/
theorem HClosed.terminalContext_mem (hU : HClosed U) {x : HSet.{u}} (hx : x ∈ U) :
    terminalContext ∈ U :=
  hU.singleton_mem (hU.empty_mem hx)

/-- **Context extension**: a small context extended by a small type is small. -/
theorem HClosed.extension_mem (hU : HClosed U) {Γ : HSet.{u}} (hΓ : Γ ∈ U) {A : Family Γ}
    (hA : SmallFamily U A) : extension p A ∈ U :=
  hU.sigmaSet_mem p hΓ hA

/-- **Π of small types is small.** -/
theorem HClosed.smallFamily_pi (hU : HClosed U) {Γ : HSet.{u}} {A : Family Γ}
    {B : Family (extension p A)} (hA : SmallFamily U A) (hB : SmallFamily U B) :
    SmallFamily U (piFamily p A B) :=
  fun γ => hU.dependentProduct_mem p (hA γ) fun _ => hB _

/-- **Σ of small types is small.** -/
theorem HClosed.smallFamily_sigma (hU : HClosed U) {Γ : HSet.{u}} {A : Family Γ}
    {B : Family (extension p A)} (hA : SmallFamily U A) (hB : SmallFamily U B) :
    SmallFamily U (sigmaFamily p A B) :=
  fun γ => hU.sigmaSet_mem p (hA γ) fun _ => hB _

/-- The extensional identity type of two terms: `{∅}` when their values agree, `∅` otherwise. -/
def identityFamily {Γ : HSet.{u}} {A : Family Γ} (a b : Section A) : Family Γ :=
  fun γ => HSet.sep (fun _ => (a γ).1 = (b γ).1) {∅}

theorem mem_identityFamily {Γ : HSet.{u}} {A : Family Γ} {a b : Section A} {γ : Elements Γ}
    {z : HSet.{u}} : z ∈ identityFamily a b γ ↔ z = ∅ ∧ (a γ).1 = (b γ).1 := by
  rw [identityFamily, HSet.mem_sep, HSet.mem_singleton]

/-- **The identity type of small terms is small**, in every nonempty closed stage. -/
theorem HClosed.smallFamily_identity (hU : HClosed U) {x : HSet.{u}} (hx : x ∈ U)
    {Γ : HSet.{u}} {A : Family Γ} (a b : Section A) :
    SmallFamily U (identityFamily a b) :=
  fun _ => hU.sep_mem (hU.terminalContext_mem hx) _

/-! ## Universes -/

/-- The universe `B_μ` as a constant type. -/
noncomputable def universeFamily (μ : Cardinal.{u}) {Γ : HSet.{u}} : Family Γ :=
  fun _ => branching μ

/-- Decoding a term of a universe into a type. -/
def decode {μ : Cardinal.{u}} {Γ : HSet.{u}} (t : Section (universeFamily μ (Γ := Γ))) :
    Family Γ :=
  fun γ => (t γ).1

/-- **A term of the universe `B_μ` decodes to a type small for `B_μ`.** -/
theorem smallFamily_decode {μ : Cardinal.{u}} {Γ : HSet.{u}}
    (t : Section (universeFamily μ (Γ := Γ))) : SmallFamily (branching μ) (decode t) :=
  fun γ => (t γ).2

/-- The number of graphs on the lists over a type of `μ` elements is below an inaccessible
cardinal above `μ`. -/
theorem mk_listGraphs_lt {μ κ : Cardinal.{u}} (hμ : ℵ₀ ≤ μ) (hμκ : μ < κ)
    (hκ : κ.IsInaccessible) :
    #(List μ.ord.ToType → List μ.ord.ToType → Prop) < κ := by
  have list : #(List μ.ord.ToType) ≤ μ := by
    refine (mk_list_le_max _).trans ?_
    rw [mk_ord_toType]
    exact max_le hμ le_rfl
  have equal : #(List μ.ord.ToType → List μ.ord.ToType → Prop) =
      #(Set (List μ.ord.ToType × List μ.ord.ToType)) :=
    mk_congr (Equiv.curry _ _ _).symm
  rw [equal, mk_set, mk_prod, lift_id]
  calc (2 : Cardinal.{u}) ^ (#(List μ.ord.ToType) * #(List μ.ord.ToType))
      ≤ 2 ^ (μ * μ) := power_le_power_left two_ne_zero (mul_le_mul' list list)
    _ = 2 ^ μ := by rw [mul_eq_self hμ]
    _ < κ := hκ.isStrongLimit.isStrongPrelimit hμκ

/-- **The universe `B_μ` is a member of `B_κ`**, for `ℵ₀ ≤ μ < κ` with `κ` inaccessible. -/
theorem branching_mem_branching {μ κ : Cardinal.{u}} (hμ : ℵ₀ ≤ μ) (hμκ : μ < κ)
    (hκ : κ.IsInaccessible) : branching μ ∈ branching κ := by
  refine mem_branching.mpr (herSmall_iff.mpr ⟨?_, fun y hy =>
    (mem_branching.mp hy).mono hμκ.le⟩)
  refine ⟨{r : List μ.ord.ToType → List μ.ord.ToType → Prop // HerSmall μ (HSet.decorate r [])},
    fun r => HSet.decorate r.1 [], (mk_subtype_le _).trans_lt (mk_listGraphs_lt hμ hμκ hκ),
    fun y => ?_⟩
  rw [mem_branching]
  constructor
  · intro h
    obtain ⟨r, hr⟩ := exists_picture μ y h
    exact ⟨⟨r, hr ▸ h⟩, hr⟩
  · rintro ⟨r, rfl⟩
    exact r.2

/-- **The universe is a small type** of the sub-model of `B_κ`. -/
theorem smallFamily_universe {μ κ : Cardinal.{u}} (hμ : ℵ₀ ≤ μ) (hμκ : μ < κ)
    (hκ : κ.IsInaccessible) {Γ : HSet.{u}} :
    SmallFamily (branching κ) (universeFamily μ (Γ := Γ)) :=
  fun _ => branching_mem_branching hμ hμκ hκ

/-- Decoded types of `B_μ` are small types of the sub-model of `B_κ`, for `μ ≤ κ`. -/
theorem smallFamily_decode_mono {μ κ : Cardinal.{u}} (h : μ ≤ κ) {Γ : HSet.{u}}
    (t : Section (universeFamily μ (Γ := Γ))) : SmallFamily (branching κ) (decode t) :=
  fun γ => HSet.subset_iff.mp (branching_mono h) (smallFamily_decode t γ)

/-- **The universe is closed under Π and Σ of codes**, for `μ` equal to `ℵ₀` or inaccessible. -/
theorem universe_closed_pi_sigma {μ : Cardinal.{u}} (hμ : μ = ℵ₀ ∨ μ.IsInaccessible)
    {Γ : HSet.{u}} {A : Family Γ} {B : Family (extension p A)}
    (hA : SmallFamily (branching μ) A) (hB : SmallFamily (branching μ) B) :
    SmallFamily (branching μ) (piFamily p A B) ∧ SmallFamily (branching μ) (sigmaFamily p A B) :=
  have hU := hclosed_branching_iff.mpr (Or.inr hμ)
  ⟨hU.smallFamily_pi p hA hB, hU.smallFamily_sigma p hA hB⟩

/-- The code of a dependent product of codes: a term of the universe. -/
def piCode {μ : Cardinal.{u}} (hμ : μ = ℵ₀ ∨ μ.IsInaccessible) {Γ : HSet.{u}}
    (a : Section (universeFamily μ (Γ := Γ)))
    (b : Section (universeFamily μ (Γ := extension p (decode a)))) :
    Section (universeFamily μ (Γ := Γ)) :=
  fun γ => ⟨piFamily p (decode a) (decode b) γ,
    (universe_closed_pi_sigma p hμ (smallFamily_decode a) (smallFamily_decode b)).1 γ⟩

/-- The code of a dependent sum of codes: a term of the universe. -/
def sigmaCode {μ : Cardinal.{u}} (hμ : μ = ℵ₀ ∨ μ.IsInaccessible) {Γ : HSet.{u}}
    (a : Section (universeFamily μ (Γ := Γ)))
    (b : Section (universeFamily μ (Γ := extension p (decode a)))) :
    Section (universeFamily μ (Γ := Γ)) :=
  fun γ => ⟨sigmaFamily p (decode a) (decode b) γ,
    (universe_closed_pi_sigma p hμ (smallFamily_decode a) (smallFamily_decode b)).2 γ⟩

/-- **Decoding commutes with the type formers**: the universe is closed under `Π` and `Σ` at the
level of terms. -/
theorem decode_piCode {μ : Cardinal.{u}} (hμ : μ = ℵ₀ ∨ μ.IsInaccessible) {Γ : HSet.{u}}
    (a : Section (universeFamily μ (Γ := Γ)))
    (b : Section (universeFamily μ (Γ := extension p (decode a)))) :
    decode (piCode p hμ a b) = piFamily p (decode a) (decode b) := rfl

theorem decode_sigmaCode {μ : Cardinal.{u}} (hμ : μ = ℵ₀ ∨ μ.IsInaccessible) {Γ : HSet.{u}}
    (a : Section (universeFamily μ (Γ := Γ)))
    (b : Section (universeFamily μ (Γ := extension p (decode a)))) :
    decode (sigmaCode p hμ a b) = sigmaFamily p (decode a) (decode b) := rfl

/-- The code of a smaller universe inside a larger one: `B_μ` is a term of the universe `B_κ`
over every context, for `ℵ₀ ≤ μ < κ` with `κ` inaccessible. -/
noncomputable def universeCode {μ κ : Cardinal.{u}} (hμ : ℵ₀ ≤ μ) (hμκ : μ < κ)
    (hκ : κ.IsInaccessible) {Γ : HSet.{u}} : Section (universeFamily κ (Γ := Γ)) :=
  fun _ => ⟨branching μ, branching_mem_branching hμ hμκ hκ⟩

theorem decode_universeCode {μ κ : Cardinal.{u}} (hμ : ℵ₀ ≤ μ) (hμκ : μ < κ)
    (hκ : κ.IsInaccessible) {Γ : HSet.{u}} :
    decode (universeCode hμ hμκ hκ (Γ := Γ)) = universeFamily μ := rfl

/-! ## Controls -/

/-- The cyclic type `{Ω}` is a small type of the sub-model of `B_ℵ₀`. -/
theorem quineFamily_small : SmallFamily (branching ℵ₀) quineFamily.{u} :=
  fun _ => hclosed_branching_aleph0.singleton_mem quineAtom_mem_branching

/-- The hyperset of `V_ω` does not contain `{Ω}`. -/
theorem quineFamily_not_small_vonNeumann :
    ¬ SmallFamily (HSet.ofZFSet (V_ Ordinal.omega0 : ZFSet.{u})) quineFamily.{u} := by
  intro h
  have member := h ⟨∅, HSet.mem_singleton_self ∅⟩
  have wf := (HSet.wf_ofZFSet _).mem member
  exact HSet.not_wf_quineAtom (wf.mem (HSet.mem_singleton_self _))

#print axioms HClosed.sigmaSet_mem
#print axioms HClosed.dependentProduct_mem
#print axioms HClosed.extension_mem
#print axioms HClosed.smallFamily_pi
#print axioms HClosed.smallFamily_sigma
#print axioms HClosed.smallFamily_identity
#print axioms branching_mem_branching
#print axioms universe_closed_pi_sigma

end Mettapedia.SetTheory.OpenTower.AntiFounded
