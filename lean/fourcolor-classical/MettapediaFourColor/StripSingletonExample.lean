import MettapediaFourColor.StripSingletonRepair
import MettapediaFourColor.StripStrongAnchorTrap
import MettapediaFourColor.PatchBoundaryGluing

/-!
# Deriving the spherical escape from a uniform repair law

Only the initial colouring and first component are checked. The second
component follows from singleton release. The source witness follows from
the common list argument and is glued to the actual ambient sphere.
The old checks for the second closure and completed colouring are not used.
-/

namespace FourColor.StripSingletonExample

open SimpleGraph Color StripStrongAnchorTrap
open Mettapedia.GraphTheory.FourColor.KempeChainCertificate

theorem initial_proper : ∀ u v, exterior.Adj u v → values 0 u ≠ values 0 v := by
  decide +kernel
def initial : exterior.Coloring Color := .mk (values 0) (fun h => initial_proper _ _ h)

def chain : List (Fin 16) := [0,1,2,12,14,12,2,1,0,10,0]
theorem first_checked :
    (1 : Fin 16) ∈ chain ∧ chain.IsChain exterior.Adj ∧
    (∀ x ∈ chain, initial x = c0 ∨ initial x = c1) ∧
    (∀ x ∈ chain, ∀ y, exterior.Adj x y →
      (initial y = c0 ∨ initial y = c1) → y ∈ chain) := by decide +kernel

def first : KempeSeparatedChains.Certificate initial c0 c1 where
  vertices := chain
  root := 1
  root_mem := first_checked.1
  connected := first_checked.2.1
  active := first_checked.2.2.1
  closed := first_checked.2.2.2

theorem ready : ∀ i, initial (port i) ∈ StripSingletonRepair.before i := by decide +kernel
theorem member : port 1 ∈ initial.kempeComponentSet c0 c1 first.component :=
  (first.component_mem _).mpr first.root_mem
theorem missing : ∀ y, exterior.Adj (port 1) y → initial y ≠ c2 := by decide +kernel
theorem port_edges : ∀ i j,
    TriangleStripAnchors.input0099.graph.Adj (StripResponseSummary.port i)
      (StripResponseSummary.port j) → exterior.Adj (port i) (port j) := by decide +kernel
theorem port_injective : Function.Injective port := by
  intro i j h
  exact Fin.ext (congrArg (fun x : Fin 16 => x.val) h)
theorem separated : ∀ i ∈ StripSingletonRepair.retainedPorts,
    port i ∉ initial.kempeComponentSet c0 c1 first.component := by
  intro i hi hm
  have absent : ∀ i ∈ StripSingletonRepair.retainedPorts, port i ∉ chain := by decide +kernel
  exact absent i hi ((first.component_mem _).mp hm)

noncomputable def repaired :=
  StripSingletonRepair.released initial port first.component ready member missing
noncomputable def repairHistory : History initial repaired :=
  StripSingletonRepair.history initial port first.component ready member missing
theorem repair_length : repairHistory.length = 2 := rfl

theorem source : ∃ k : TriangleStripAnchors.input0099.graph.Coloring Color,
    ∀ i, k (StripResponseSummary.port i) = repaired (port i) :=
  StripSingletonRepair.source initial port first.component ready member missing
    port_edges port_injective separated

def sourceHom : TriangleStripAnchors.input0099.graph →g ambient := ⟨sourceVertex,fun h =>
  source_edges _ _ h⟩
def interior : Set (Fin 19) := {v | 11 ≤ v.val}
def exteriorVertex (v : Fin 24) : Fin 16 := ⟨v.val % 16,Nat.mod_lt _ (by decide)⟩

instance (v : Fin 24) : Decidable (v ∈ sourceHom '' interior) :=
  inferInstanceAs (Decidable (∃ a : Fin 19, 11 ≤ a.val ∧ sourceVertex a = v))

theorem source_core (i : Fin 8) : sourceHom (i.natAdd 11) = i.natAdd 16 := by
  simp [sourceHom,sourceVertex]

theorem no_capture (a : Fin 19) (ha : a ∉ interior) : sourceHom a ∉ sourceHom '' interior := by
  rintro ⟨i,hi,heq⟩
  exact ha ((source_injective heq) ▸ hi)

theorem covers (i : Fin 19) (hi : i ∈ interior) (v : Fin 24)
    (edge : ambient.Adj (sourceHom i) v) :
    ∃ a, TriangleStripAnchors.input0099.graph.Adj i a ∧ sourceHom a = v := by
  revert hi edge
  refine Fin.addCases (m := 11) (n := 8)
    (motive := fun i => i ∈ interior → ambient.Adj (sourceHom i) v →
      ∃ a, TriangleStripAnchors.input0099.graph.Adj i a ∧ sourceHom a = v)
    (fun j hj _ => ?_) (fun j _ edge => ?_) i
  · have h : 11 ≤ j.val := hj
    omega
  · rw [source_core] at edge
    exact (core_stars j v).mp edge

theorem exterior_edges : ∀ v w,
    v ∉ sourceHom '' interior → w ∉ sourceHom '' interior → ambient.Adj v w →
      exterior.Adj (exteriorVertex v) (exteriorVertex w) := by decide +kernel
theorem boundary_position : ∀ i,
    exteriorVertex (sourceHom (StripResponseSummary.port i)) = port i := by decide +kernel
theorem exterior_position : ∀ v, exteriorVertex (includeExterior v) = v := by decide +kernel
theorem exterior_outside : ∀ v, includeExterior v ∉ sourceHom '' interior := by decide +kernel

/-- Every source witness fitting an actual exterior colours the whole sphere. -/
theorem assemble (D : exterior.Coloring Color)
    (k : TriangleStripAnchors.input0099.graph.Coloring Color)
    (agree : ∀ i, k (StripResponseSummary.port i) = D (port i)) :
    ∃ whole : ambient.Coloring Color, ∀ v, whole (includeExterior v) = D v := by
  obtain ⟨whole,_,outside⟩ := PatchBoundaryGluing.reconstruct sourceHom interior
    source_injective.injOn no_capture covers k (fun v => D (exteriorVertex v))
    (fun hv hw edge => D.valid (exterior_edges _ _ hv hw edge)) (by
      intro a
      refine Fin.addCases (m := 11) (n := 8)
        (motive := fun a => a ∉ interior → k a = D (exteriorVertex (sourceHom a)))
        (fun i _ => ?_) (fun i hi => ?_) a
      · have eq : Fin.castAdd 8 i = StripResponseSummary.port i := by ext; rfl
        rw [eq,boundary_position]
        exact agree i
      · exact (hi (by change 11 ≤ 11 + i.val; omega)).elim)
  refine ⟨whole,fun v => ?_⟩
  rw [outside _ (exterior_outside v),exterior_position]

/-- Actual two-step history and reconstruction consume the uniform source repair. -/
theorem reconstructed : ∃ D : exterior.Coloring Color, ∃ h : History initial D,
    h.length = 2 ∧ ∃ whole : ambient.Coloring Color,
      ∀ v, whole (includeExterior v) = D v := by
  obtain ⟨k,hk⟩ := source
  exact ⟨repaired,repairHistory,repair_length,assemble repaired k hk⟩

theorem first_values : ∀ v, first.swap v = values 1 v := by
  intro v
  rw [KempeSeparatedChains.Certificate.swap_apply]
  exact (by decide +kernel : ∀ v : Fin 16,
    (if v ∈ chain then Equiv.swap c0 c1 (values 0 v) else values 0 v) = values 1 v) v

theorem repaired_values : ∀ v, repaired v = values 2 v := by
  intro v
  unfold repaired
  rw [StripSingletonRepair.released_apply]
  change (if v = port 1 then c2 else first.swap v) = _
  rw [first_values]
  exact (by decide +kernel : ∀ v : Fin 16,
    (if v = port 1 then c2 else values 1 v) = values 2 v) v

end FourColor.StripSingletonExample
