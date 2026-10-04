import MettapediaFourColor.StripPartialColouring
import MettapediaFourColor.StripSymbolicRepair

/-!
# Source elimination with omitted vertices

The same six triangle joins describe partial colourings for every boundary
and every set of omitted core vertices. A hole removes all its incident
constraints; the other vertices retain their joint choices. The terminal
relation reconstructs an actual colouring of the induced source graph.
-/

namespace FourColor.StripPuncturedExtension

open Color StripResponseSummary StripSourceExtension StripPartialColouring
open TriangleStripAnchors

abbrev Holes := Finset (Fin 8)

def unary (h : Holes) (b : Boundary) (v : Fin 8) (a : Color) : Prop :=
  v ∈ h ∨ StripResponseSummary.unary b v a

def edge (h : Holes) (u v : Fin 8) (a b : Color) : Prop :=
  u ∈ h ∨ v ∈ h ∨ a ≠ b

instance (h b v a) : Decidable (unary h b v a) := by unfold unary; infer_instance
instance (h u v a b) : Decidable (edge h u v a b) := by unfold edge; infer_instance

theorem edge_comm (h u v a b) : edge h u v a b ↔ edge h v u b a := by
  simp only [edge, ne_comm, or_comm, or_left_comm, or_assoc]

def Relaxed (h : Holes) (b : Boundary) (f : Fin 8 → Color) : Prop :=
  (∀ v, unary h b v (f v)) ∧ ∀ e ∈ edges, edge h e.1 e.2 (f e.1) (f e.2)

theorem relaxed_iff (h : Holes) (b : Boundary) (f : Fin 8 → Color) :
    Relaxed h b f ↔ ValidExcept b h f := by
  constructor
  · rintro ⟨hu,he⟩
    exact ⟨fun v hv => (hu v).resolve_left hv,
      fun e hm hx hy => ((he e hm).resolve_left hx).resolve_left hy⟩
  · rintro ⟨hu,he⟩
    constructor
    · intro v
      by_cases hv : v ∈ h
      · exact Or.inl hv
      · exact Or.inr (hu v hv)
    · intro e hm
      by_cases hx : e.1 ∈ h
      · exact Or.inl hx
      · by_cases hy : e.2 ∈ h
        · exact Or.inr (Or.inl hy)
        · exact Or.inr (Or.inr (he e hm hx hy))

def join (h : Holes) (b : Boundary) (u v w : Fin 8)
    (R S : Color → Color → Prop) (a d : Color) : Prop :=
  unary h b u a ∧ unary h b v d ∧ edge h u v a d ∧
    ∃ c, unary h b w c ∧ R a c ∧ S c d

instance (h b u v w) (R S : Color → Color → Prop)
    [DecidableRel R] [DecidableRel S] (a d) : Decidable (join h b u v w R S a d) := by
  unfold join; infer_instance

def r0 (h : Holes) (b : Boundary) := join h b 1 3 0 (edge h 1 0) (edge h 0 3)
def r1 (h : Holes) (b : Boundary) := join h b 1 2 3 (r0 h b) (edge h 3 2)
def r2 (h : Holes) (b : Boundary) := join h b 2 4 1 (fun a c => r1 h b c a) (edge h 1 4)
def r3 (h : Holes) (b : Boundary) := join h b 2 6 4 (r2 h b) (edge h 4 6)
def r4 (h : Holes) (b : Boundary) := join h b 5 6 2 (edge h 5 2) (r3 h b)
def r5 (h : Holes) (b : Boundary) := join h b 6 7 5 (fun a c => r4 h b c a) (edge h 5 7)

instance (h b) : DecidableRel (r0 h b) := by unfold r0; infer_instance
instance (h b) : DecidableRel (r1 h b) := by unfold r1; infer_instance
instance (h b) : DecidableRel (r2 h b) := by unfold r2; infer_instance
instance (h b) : DecidableRel (r3 h b) := by unfold r3; infer_instance
instance (h b) : DecidableRel (r4 h b) := by unfold r4; infer_instance
instance (h b) : DecidableRel (r5 h b) := by unfold r5; infer_instance

/-- All six joins keep the witnesses on shared triangle edges. -/
theorem terminal_iff (h : Holes) (b : Boundary) :
    (∃ a c, r5 h b a c) ↔ ∃ f, ValidExcept b h f := by
  constructor
  · rintro ⟨a6,a7,h6,h7,h67,a5,h5,h4,h57⟩
    rcases h4 with ⟨_,_,h56,a2,h2,h52,h3⟩
    rcases h3 with ⟨_,_,h26,a4,h4,hR2,h46⟩
    rcases hR2 with ⟨_,_,h24,a1,h1,hR1,h14⟩
    rcases hR1 with ⟨_,_,h12,a3,h3,hR0,h32⟩
    rcases hR0 with ⟨_,_,h13,a0,h0,h10,h03⟩
    have h25 := (edge_comm h 2 5 a2 a5).mpr h52
    have h23 := (edge_comm h 2 3 a2 a3).mpr h32
    have h01 := (edge_comm h 0 1 a0 a1).mpr h10
    refine ⟨![a0,a1,a2,a3,a4,a5,a6,a7], (relaxed_iff _ _ _).mp ?_⟩
    simp [Relaxed, edges, Fin.forall_fin_succ, h0,h1,h2,h3,h4,h5,h6,h7,
      h67,h57,h56,h25,h26,h46,h24,h14,h12,h23,h13,h01,h03]
  · rintro ⟨f,hf⟩
    obtain ⟨hu,he⟩ := (relaxed_iff h b f).mpr hf
    have e {i j : Fin 8} (hm : (i,j) ∈ edges) : edge h i j (f i) (f j) := he _ hm
    refine ⟨f 6,f 7,hu 6,hu 7,e (by decide),f 5,hu 5,?_,e (by decide)⟩
    refine ⟨hu 5,hu 6,e (by decide),f 2,hu 2,(edge_comm _ _ _ _ _).mp (e (by decide)),?_⟩
    refine ⟨hu 2,hu 6,e (by decide),f 4,hu 4,?_,e (by decide)⟩
    refine ⟨hu 2,hu 4,e (by decide),f 1,hu 1,?_,e (by decide)⟩
    refine ⟨hu 1,hu 2,e (by decide),f 3,hu 3,?_,(edge_comm _ _ _ _ _).mp (e (by decide))⟩
    exact ⟨hu 1,hu 3,e (by decide),f 0,hu 0,
      (edge_comm _ _ _ _ _).mp (e (by decide)),e (by decide)⟩

/-- At most one core hole, with a proper retained source and exact boundary. -/
def Terminal (et : List Color) : Prop := ∃ h : Fin 8, ∃ b : Boundary,
  trace (List.ofFn b) = et ∧ ProperBoundary b ∧ ∃ f, ValidExcept b {h} f

def Direct (et : List Color) : Prop :=
  let b := StripSymbolicRepair.readBoundary et
  trace (List.ofFn b) = et ∧ ProperBoundary b ∧ ∃ h : Fin 8, ∃ a c, r5 {h} b a c

instance (et) : Decidable (Direct et) := by unfold Direct; infer_instance

theorem direct_sound {et} (h : Direct et) : Terminal et := by
  obtain ⟨ht,hb,v,a,c,hr⟩ := h
  exact ⟨v,_,ht,hb,(terminal_iff {v} _).mp ⟨a,c,hr⟩⟩

theorem direct_coclosure {et} (h : Direct et) : KempeCoclosure Terminal et :=
  fun _outside _ hold => ⟨et,direct_sound h,hold⟩

/-- The remaining seven core vertices and every ordered port are really
coloured, not merely supported in separate marginal relations. -/
theorem reconstruct {et} (ht : Terminal et) :
    ∃ h : Fin 8, ∃ b : Boundary, ∃ k : (input0099.graph.induce {v | Live {h} v}).Coloring Color,
      trace (List.ofFn b) = et ∧ ∀ i, k ⟨port i,live_port {h} i⟩ = b i := by
  obtain ⟨h,b,ht,hb,f,hf⟩ := ht
  exact ⟨h,b,.mk (fun v => completeColour b f v.val)
    (fun {u v} e => partial_valid b {h} f hb hf u.val v.val u.property v.property e),
    ht,fun i => colour_port b f i⟩

end FourColor.StripPuncturedExtension
