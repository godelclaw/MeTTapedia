import Mettapedia.SetTheory.OpenTower.AntiFounded.AFAStages

/-!
# Anti-foundation inside a stage, with graphs and decorations as sets

`AFAClosed` asks that small graphs, given as graphs of the host, have their decorations in the
stage. Here the graph is itself a set of the stage: a node set `N`, an edge set `E` of Kuratowski
pairs of nodes. A *set decoration* of `(N, E)` is a set `D` of pairs that assigns to each node `n`
a value whose members are the values of the nodes `m` with `⟨n, m⟩ ∈ E` (`IsSetDecoration`).

**Anti-foundation holds inside the stage, as a statement about its own sets**
(`AFAClosed.existsUnique_setDecoration`): for every node set `N` that is a member of a stage
closed under anti-foundation, and every edge set on it, there is exactly one set decoration, and
it is a member of the stage. Uniqueness holds among all hypersets (`IsSetDecoration.unique`).
In particular it holds in `B_κ` for `κ = ℵ₀` and for `κ` inaccessible
(`branching_existsUnique_setDecoration`).

A closed stage is closed under Kuratowski pairs (`HClosed.kpair_mem`).

**Controls.** The one-node loop as a set graph, `N = {∅}` and `E = {⟨∅, ∅⟩}`, is decorated by
`{⟨∅, Ω⟩}` (`setDecoration_loop`). The hyperset of `V_ω` has the same node set and edge set as
members and has no set decoration among its members (`vonNeumann_omega_no_setDecoration`).
-/

set_option autoImplicit false

namespace Mettapedia.SetTheory.OpenTower.AntiFounded

open Mettapedia.TypeTheory.MaterialSets
open Mettapedia.TypeTheory.MaterialSets.Hypersets
open Cardinal
open scoped ZFSet

universe u

/-! ## Pairs in a closed stage -/

theorem HClosed.singleton_mem {U x : HSet.{u}} (hU : HClosed U) (hx : x ∈ U) :
    ({x} : HSet.{u}) ∈ U := by
  have h := hU.pair_mem hx hx
  have equal : ({x, x} : HSet.{u}) = {x} :=
    HSet.ext fun z => by rw [HSet.mem_pair, HSet.mem_singleton, or_self]
  rwa [equal] at h

/-- **A closed stage is closed under Kuratowski pairs.** -/
theorem HClosed.kpair_mem {U x y : HSet.{u}} (hU : HClosed U) (hx : x ∈ U) (hy : y ∈ U) :
    HSet.kpair x y ∈ U :=
  hU.pair_mem (hU.singleton_mem hx) (hU.pair_mem hx hy)

/-! ## Set decorations -/

/-- `D` is a set decoration of the node set `N` with edge set `E`: its members are pairs
`⟨n, y⟩` with `n ∈ N`, every node has a pair, and the value `y` of `n` has as members exactly
the values of the nodes `m` with `⟨n, m⟩ ∈ E`. -/
def IsSetDecoration (N E D : HSet.{u}) : Prop :=
  (∀ z ∈ D, ∃ n ∈ N, ∃ y, z = HSet.kpair n y) ∧
    (∀ n ∈ N, ∃ y, HSet.kpair n y ∈ D) ∧
    ∀ n y, HSet.kpair n y ∈ D → ∀ w, w ∈ y ↔
      ∃ m y', HSet.kpair n m ∈ E ∧ HSet.kpair m y' ∈ D ∧ w = y'

/-- A set decoration is single-valued, by extensionality. -/
theorem IsSetDecoration.functional {N E D : HSet.{u}} (hD : IsSetDecoration N E D)
    {n y y' : HSet.{u}} (h : HSet.kpair n y ∈ D) (h' : HSet.kpair n y' ∈ D) : y = y' :=
  HSet.ext fun w => (hD.2.2 n y h w).trans (hD.2.2 n y' h' w).symm

section Presented

variable {N E D : HSet.{u}} {ι : Type u} {g : ι → HSet.{u}}

/-- The graph on a presentation of the nodes. -/
def nodeGraph (E : HSet.{u}) (g : ι → HSet.{u}) (i j : ι) : Prop :=
  HSet.kpair (g i) (g j) ∈ E

/-- A set decoration read on a presentation of the nodes is a decoration of the node graph. -/
theorem IsSetDecoration.isDecoration (hD : IsSetDecoration N E D)
    (hN : ∀ y, y ∈ N ↔ ∃ i, g i = y) (value : ι → HSet.{u})
    (hvalue : ∀ i, HSet.kpair (g i) (value i) ∈ D) :
    HSet.IsDecoration (nodeGraph E g) value := by
  intro i w
  rw [hD.2.2 _ _ (hvalue i) w]
  constructor
  · rintro ⟨m, y', hE, hD', rfl⟩
    have hm : m ∈ N := by
      obtain ⟨n', hn', y'', hz⟩ := hD.1 _ hD'
      rw [(HSet.kpair_inj.mp hz).1]
      exact hn'
    obtain ⟨j, rfl⟩ := (hN m).mp hm
    exact ⟨j, hE, hD.functional (hvalue j) hD'⟩
  · rintro ⟨j, hE, rfl⟩
    exact ⟨g j, value j, hE, hvalue j, rfl⟩

end Presented

/-- **Set decorations are unique**, among all hypersets. -/
theorem IsSetDecoration.unique {N E D D' : HSet.{u}} (hD : IsSetDecoration N E D)
    (hD' : IsSetDecoration N E D') : D = D' := by
  obtain ⟨ι, g, _, hN⟩ := exists_injective_members N
  have node : ∀ i, g i ∈ N := fun i => (hN _).mpr ⟨i, rfl⟩
  choose value hvalue using fun i => hD.2.1 (g i) (node i)
  choose value' hvalue' using fun i => hD'.2.1 (g i) (node i)
  have same : value = value' :=
    (hD.isDecoration hN value hvalue).unique (hD'.isDecoration hN value' hvalue')
  have transfer : ∀ {D₁ D₂ : HSet.{u}} (h₁ : IsSetDecoration N E D₁)
      (v₂ : ι → HSet.{u}) (_ : ∀ i, HSet.kpair (g i) (v₂ i) ∈ D₂)
      (v₁ : ι → HSet.{u}) (_ : ∀ i, HSet.kpair (g i) (v₁ i) ∈ D₁) (_ : v₁ = v₂),
      ∀ z, z ∈ D₁ → z ∈ D₂ := by
    intro D₁ D₂ h₁ v₂ hv₂ v₁ hv₁ e z hz
    obtain ⟨n, hn, y, rfl⟩ := h₁.1 z hz
    obtain ⟨i, rfl⟩ := (hN n).mp hn
    rw [h₁.functional hz (hv₁ i), e]
    exact hv₂ i
  exact HSet.ext fun z =>
    ⟨transfer hD value' hvalue' value hvalue same z,
      transfer hD' value hvalue value' hvalue' same.symm z⟩

/-- **Anti-foundation inside a stage closed under anti-foundation, as sets.** Every node set
that is a member, with every edge set on it, has exactly one set decoration, and it is a
member. -/
theorem AFAClosed.existsUnique_setDecoration {U N E : HSet.{u}} (hU : AFAClosed U)
    (hN : N ∈ U) :
    ∃ D, IsSetDecoration N E D ∧ D ∈ U ∧ ∀ D', IsSetDecoration N E D' → D' = D := by
  obtain ⟨ι, g, injective, hNg⟩ := exists_injective_members N
  have node : ∀ i, g i ∈ N := fun i => (hNg _).mpr ⟨i, rfl⟩
  let value : ι → HSet.{u} := HSet.decorate (nodeGraph E g)
  let D : HSet.{u} := HSet.range fun i =>
    HSet.Presentation.choice.graph (HSet.kpair (g i) (value i))
  have memD : ∀ z, z ∈ D ↔ ∃ i, HSet.kpair (g i) (value i) = z := fun z => by
    simp only [D, HSet.mem_range, HSet.Presentation.choice.mk_graph]
  have pairInD : ∀ i, HSet.kpair (g i) (value i) ∈ D := fun i => (memD _).mpr ⟨i, rfl⟩
  have decoration : IsSetDecoration N E D := by
    refine ⟨fun z hz => ?_, fun n hn => ?_, fun n y hy w => ?_⟩
    · obtain ⟨i, rfl⟩ := (memD z).mp hz
      exact ⟨g i, node i, value i, rfl⟩
    · obtain ⟨i, rfl⟩ := (hNg n).mp hn
      exact ⟨value i, pairInD i⟩
    · obtain ⟨i, hi⟩ := (memD _).mp hy
      obtain ⟨rfl, rfl⟩ := HSet.kpair_inj.mp hi.symm
      show w ∈ HSet.decorate (nodeGraph E g) i ↔ _
      rw [HSet.mem_decorate]
      constructor
      · rintro ⟨j, hE, rfl⟩
        exact ⟨g j, value j, hE, pairInD j, rfl⟩
      · rintro ⟨m, y', hE, hm, rfl⟩
        obtain ⟨j, hj⟩ := (memD _).mp hm
        obtain ⟨rfl, rfl⟩ := HSet.kpair_inj.mp hj.symm
        exact ⟨j, hE, rfl⟩
  have valueInU : ∀ i, value i ∈ U := fun i =>
    hU.decorate_mem hN (nodeGraph E g) ⟨g, injective, node⟩ i
  have DInU : D ∈ U := by
    classical
    refine hU.toHClosed.image_mem hN (fun z hz => ?_)
      ⟨fun n => if h : ∃ i, g i = n then HSet.kpair n (value h.choose) else ∅, fun z => ?_⟩
    · obtain ⟨i, rfl⟩ := (memD z).mp hz
      exact hU.toHClosed.kpair_mem (hU.toHClosed.transitive hN (node i)) (valueInU i)
    · rw [memD]
      constructor
      · rintro ⟨i, rfl⟩
        have h : ∃ i', g i' = g i := ⟨i, rfl⟩
        refine ⟨g i, node i, ?_⟩
        simp only [dif_pos h, injective h.choose_spec]
      · rintro ⟨n, hn, rfl⟩
        have h : ∃ i, g i = n := (hNg n).mp hn
        refine ⟨h.choose, ?_⟩
        simp only [dif_pos h, h.choose_spec]
  exact ⟨D, decoration, DInU, fun D' hD' => hD'.unique decoration⟩

/-- **Anti-foundation holds inside `B_κ` as sets**, for `κ = ℵ₀` and for `κ` inaccessible. -/
theorem branching_existsUnique_setDecoration {κ : Cardinal.{u}} (hκ : κ = ℵ₀ ∨ κ.IsInaccessible)
    {N E : HSet.{u}} (hN : N ∈ branching κ) :
    ∃ D, IsSetDecoration N E D ∧ D ∈ branching κ ∧
      ∀ D', IsSetDecoration N E D' → D' = D :=
  (afaClosed_branching hκ).existsUnique_setDecoration hN

/-! ## Controls -/

/-- The one-node loop as a set graph is decorated by `{⟨∅, Ω⟩}`. -/
theorem setDecoration_loop :
    IsSetDecoration ({∅} : HSet.{u}) {HSet.kpair ∅ ∅} {HSet.kpair ∅ HSet.quineAtom} := by
  refine ⟨fun z hz => ?_, fun n hn => ?_, fun n y hy w => ?_⟩
  · exact ⟨∅, HSet.mem_singleton_self ∅, HSet.quineAtom, HSet.mem_singleton.mp hz⟩
  · rw [HSet.mem_singleton.mp hn]
    exact ⟨HSet.quineAtom, HSet.mem_singleton_self _⟩
  · obtain ⟨rfl, rfl⟩ := HSet.kpair_inj.mp (HSet.mem_singleton.mp hy)
    rw [HSet.mem_quineAtom]
    constructor
    · rintro rfl
      exact ⟨∅, HSet.quineAtom, HSet.mem_singleton_self _, HSet.mem_singleton_self _, rfl⟩
    · rintro ⟨m, y', hE, hD, rfl⟩
      exact (HSet.kpair_inj.mp (HSet.mem_singleton.mp hD)).2

/-- A set decoration of the one-node loop is never well-founded: its value is `Ω`. -/
theorem setDecoration_loop_unique {D : HSet.{u}}
    (hD : IsSetDecoration ({∅} : HSet.{u}) {HSet.kpair ∅ ∅} D) :
    D = {HSet.kpair ∅ HSet.quineAtom} :=
  hD.unique setDecoration_loop

/-- The hyperset of `V_ω` holds the node set `{∅}` and the edge set `{⟨∅, ∅⟩}` of the loop and no
set decoration of it: closure of `ZFSet` does not give anti-foundation inside. -/
theorem vonNeumann_omega_no_setDecoration :
    ({∅} : HSet.{u}) ∈ HSet.ofZFSet (V_ Ordinal.omega0) ∧
      HSet.kpair (∅ : HSet.{u}) ∅ ∈ HSet.ofZFSet (V_ Ordinal.omega0) ∧
      ¬ ∃ D ∈ HSet.ofZFSet (V_ Ordinal.omega0 : ZFSet.{u}),
        IsSetDecoration ({∅} : HSet.{u}) {HSet.kpair ∅ ∅} D := by
  have closed : HClosed (HSet.ofZFSet (V_ Ordinal.omega0 : ZFSet.{u})) :=
    hclosed_ofZFSet_iff.mpr
      ((Strength.InaccessibleLevels.closed_iff _).mpr (Or.inr (Or.inl rfl)))
  have empty : (∅ : HSet.{u}) ∈ HSet.ofZFSet (V_ Ordinal.omega0 : ZFSet.{u}) := by
    rw [← HSet.ofZFSet_empty, HSet.ofZFSet_mem_ofZFSet_iff, ZFSet.mem_vonNeumann,
      ZFSet.rank_empty]
    exact Ordinal.omega0_pos
  refine ⟨closed.singleton_mem empty, closed.kpair_mem empty empty, ?_⟩
  rintro ⟨D, hD, decoration⟩
  rw [setDecoration_loop_unique decoration] at hD
  have member : HSet.kpair ∅ HSet.quineAtom ∈ ({HSet.kpair ∅ HSet.quineAtom} : HSet.{u}) :=
    HSet.mem_singleton_self _
  have wf : (HSet.kpair ∅ HSet.quineAtom).WF := ((HSet.wf_ofZFSet _).mem hD).mem member
  have pairMem : ({∅, HSet.quineAtom} : HSet.{u}) ∈ HSet.kpair ∅ HSet.quineAtom :=
    HSet.mem_kpair.mpr (Or.inr rfl)
  exact HSet.not_wf_quineAtom ((wf.mem pairMem).mem (HSet.mem_pair.mpr (Or.inr rfl)))

#print axioms HClosed.kpair_mem
#print axioms IsSetDecoration.unique
#print axioms AFAClosed.existsUnique_setDecoration
#print axioms branching_existsUnique_setDecoration
#print axioms vonNeumann_omega_no_setDecoration

end Mettapedia.SetTheory.OpenTower.AntiFounded
