import Mettapedia.GraphTheory.FourColor.LocalRepairRadius
import Mettapedia.GraphTheory.Kempe.SeparatedChains

/-! # Two commuting physical switches repair the radius obstruction

The radius-two obstruction has a repair inside radius three. Its two
supports contain seven and three vertices and have no connecting edge.
The generic separated-chain law supplies both orders as physical GSLT
histories, with the same reconstructed full colouring. This is a concrete
consumer, not a universal radius-three or occurrence-supply theorem.
-/

namespace SimpleGraph.LocalRepairHistory

open LocalRepairRadius KempeSeparatedChains
open Mettapedia.GraphTheory.FourColor.KempeChainCertificate

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

abbrev E := {v : V // v ∉ core}
abbrev exterior : SimpleGraph E := graph.induce {v | v ∉ core}

def firstChain : List E := [⟨104, by decide⟩, ⟨102, by decide⟩, ⟨13, by decide⟩,
  ⟨106, by decide⟩, ⟨46, by decide⟩, ⟨16, by decide⟩, ⟨46, by decide⟩, ⟨45, by decide⟩]
def secondChain : List E := [⟨51, by decide⟩, ⟨118, by decide⟩, ⟨120, by decide⟩]

private def closes (L : List E) (a b : Palette) (u v : V) : Prop :=
  u ∈ L.map Subtype.val → v ∉ core → (initial v = a ∨ initial v = b) → v ∈ L.map Subtype.val

private instance (L : List E) (a b : Palette) (u v : V) : Decidable (closes L a b u v) :=
  inferInstanceAs (Decidable (_ → _ → _ → _))

private theorem closed_of_edges (L : List E) (a b : Palette)
    (checked : edges.all (fun e => decide
      (closes L a b e.1 e.2 ∧ closes L a b e.2 e.1)) = true) :
    ∀ x ∈ L, ∀ y, exterior.Adj x y →
      (exteriorColouring y = a ∨ exteriorColouring y = b) → y ∈ L := by
  intro x hx y edge active
  have start : x.val ∈ L.map Subtype.val := List.mem_map.mpr ⟨x, hx, rfl⟩
  have finish : y.val ∈ L.map Subtype.val := by
    rcases edge.2 with edge | edge
    · exact (of_decide_eq_true (List.all_eq_true.mp checked _ edge)).1 start y.property active
    · exact (of_decide_eq_true (List.all_eq_true.mp checked _ edge)).2 start y.property active
  obtain ⟨z, hz, eq⟩ := List.mem_map.mp finish
  exact (Subtype.ext eq : z = y) ▸ hz

private theorem first_closed : edges.all (fun e => decide
    (closes firstChain 0 2 e.1 e.2 ∧ closes firstChain 0 2 e.2 e.1)) = true := by
  decide +kernel

private theorem second_closed : edges.all (fun e => decide
    (closes secondChain 0 3 e.1 e.2 ∧ closes secondChain 0 3 e.2 e.1)) = true := by
  decide +kernel

def first : Certificate exteriorColouring 0 2 where
  vertices := firstChain
  root := ⟨13, by decide⟩
  root_mem := by decide
  connected := by decide +kernel
  active := by decide +kernel
  closed := closed_of_edges _ _ _ first_closed

def second : Certificate exteriorColouring 0 3 where
  vertices := secondChain
  root := ⟨51, by decide⟩
  root_mem := by decide
  connected := by decide +kernel
  active := by decide +kernel
  closed := closed_of_edges _ _ _ second_closed

theorem apart : ∀ x ∈ first.vertices, x ∉ second.vertices := by decide +kernel
theorem noEdge : ∀ x ∈ first.vertices, ∀ y ∈ second.vertices, ¬ exterior.Adj x y := by
  decide +kernel

noncomputable def endpoint : exterior.Coloring Palette := (first.after second apart noEdge).swap
noncomputable def history : History exteriorColouring endpoint := first.history second apart noEdge

theorem history_length : history.length = 2 := rfl

/-- Both ways of stitching the two physical repairs reach the same endpoint. -/
theorem orders_agree : endpoint =
    (second.after first (fun x hx hs => apart x hs hx)
      (fun x hx y hy edge => noEdge y hy x hx edge.symm)).swap :=
  first.commute second apart noEdge

noncomputable def reverseHistory : History exteriorColouring endpoint :=
  orders_agree.symm ▸ second.history first (fun x hx hs => apart x hs hx)
    (fun x hx y hy edge => noEdge y hy x hx edge.symm)

theorem reverseHistory_length : reverseHistory.length = 2 := by
  have cast_length {D F : exterior.Coloring Palette} (eq : D = F)
      (p : History exteriorColouring D) : (eq ▸ p).length = p.length := by
    cases eq
    rfl
  exact (cast_length orders_agree.symm _).trans rfl

/-- Only the seven reconstructed core values are supplied; all exterior
values are obtained from the two physical commands. -/
private def fullColour (v : V) : Palette :=
  if v ∈ core then
    if v = 1 ∨ v = 12 ∨ v = 105 then 3 else
    if v = 47 then 1 else if v = 49 then 2 else 0
  else
    let firstColour := if v ∈ firstChain.map Subtype.val then
      Equiv.swap 0 2 (initial v) else initial v
    if v ∈ secondChain.map Subtype.val then Equiv.swap 0 3 firstColour else firstColour

private theorem full_edges : edges.all (fun e => decide
    (fullColour e.1 ≠ fullColour e.2)) = true := by decide +kernel

def reconstructed : graph.Coloring Palette := .mk fullColour (by
  intro u v h
  rcases h.2 with h | h
  · exact of_decide_eq_true (List.all_eq_true.mp full_edges _ h)
  · exact (of_decide_eq_true (List.all_eq_true.mp full_edges _ h)).symm)

private theorem endpoint_formula (x : E) : endpoint x =
    if x ∈ secondChain then Equiv.swap 0 3
      (if x ∈ firstChain then Equiv.swap 0 2 (initial x.val) else initial x.val)
    else if x ∈ firstChain then Equiv.swap 0 2 (initial x.val) else initial x.val := by
  simp only [endpoint, Certificate.swap_apply, Certificate.after, first, second]
  have col : exteriorColouring x = initial x.val := rfl
  by_cases ht : x ∈ secondChain <;> by_cases hs : x ∈ firstChain <;> simp [ht, hs, col]

theorem reconstructed_agrees (x : E) : reconstructed x.val = endpoint x := by
  rw [endpoint_formula]
  exact (by decide +kernel : ∀ x : E, reconstructed x.val =
    if x ∈ secondChain then Equiv.swap 0 3
      (if x ∈ firstChain then Equiv.swap 0 2 (initial x.val) else initial x.val)
    else if x ∈ firstChain then Equiv.swap 0 2 (initial x.val) else initial x.val) x

/-- The entire route, not just its endpoint, fixes the farther exterior. -/
theorem history_fixed (x : E) (outside : x.val ∉ ballThree) :
    first.swap x = initial x.val ∧ endpoint x = initial x.val := by
  have supports : ∀ x : E, x ∈ first.vertices ∨ x ∈ second.vertices → x.val ∈ ballThree := by
    decide +kernel
  exact first.fixed_outside second apart noEdge x
    (fun h => outside (supports x (Or.inl h))) (fun h => outside (supports x (Or.inr h)))

theorem both_orders_fixed (x : E) (outside : x.val ∉ ballThree) :
    first.swap x = initial x.val ∧ second.swap x = initial x.val ∧ endpoint x = initial x.val := by
  have forward := history_fixed x outside
  refine ⟨forward.1, ?_, forward.2⟩
  have supports : ∀ x : E, x ∈ second.vertices → x.val ∈ ballThree := by decide +kernel
  have absent : x ∉ second.vertices := fun h => outside (supports x h)
  simpa only [Certificate.swap_apply, ite_eq_right absent] using
    (show exteriorColouring x = initial x.val from rfl)

/-- Every changed exterior vertex in either order has an actual route
from the deleted core using at most three edges, with idle hops allowed. -/
theorem changes_near (x : E)
    (changed : first.swap x ≠ initial x.val ∨ second.swap x ≠ initial x.val ∨
      endpoint x ≠ initial x.val) :
    ∃ r ∈ core, ∃ u v, Hop r u ∧ Hop u v ∧ Hop v x.val := by
  have inside : x ∈ first.vertices ∨ x ∈ second.vertices := by
    by_contra! h
    have fixed := first.fixed_outside second apart noEdge x h.1 h.2
    have other : second.swap x = initial x.val := by
      rw [Certificate.swap_apply, ite_eq_right h.2]
      rfl
    rcases changed with changed | changed | changed
    · exact changed fixed.1
    · exact changed other
    · exact changed fixed.2
  have checked : ∀ x : E, x ∈ first.vertices ∨ x ∈ second.vertices →
      parent (parent (parent x.val)) ∈ core ∧
      Hop (parent (parent (parent x.val))) (parent (parent x.val)) ∧
      Hop (parent (parent x.val)) (parent x.val) ∧ Hop (parent x.val) x.val := by
    decide +kernel
  obtain ⟨root, one, two, three⟩ := checked x inside
  exact ⟨_, root, _, _, one, two, three⟩

theorem reconstruction : ∃ path : History exteriorColouring endpoint,
    path.length = 2 ∧ ∀ x : E, reconstructed x.val = endpoint x :=
  ⟨history, history_length, reconstructed_agrees⟩

/-- The reconstructed endpoint necessarily uses the newly admitted shell. -/
theorem radius_two_insufficient :
    ∃ v : V, v ∉ ballTwo ∧ reconstructed v ≠ initial v := by
  classical
  by_contra! h
  exact no_local_extension reconstructed h

end SimpleGraph.LocalRepairHistory
