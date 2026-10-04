import MettapediaFourColor.StripPuncturedExtension

/-!
# Joint anchors in punctured source elimination

The six triangle joins retain prescribed colours at core vertices 1 and 6.
One-hole choices count genuine partial colourings, with neither anchor
omitted. Arbitrary palette bijections preserve this count.
-/

namespace FourColor.StripAnchoredExtension

open Color StripResponseSummary StripPartialColouring
open StripPuncturedExtension (Holes edge edge_comm join)

def r2 (h : Holes) (b : Boundary) (x : Color) :=
  join h b 2 4 1 (fun a c => StripPuncturedExtension.r1 h b c a ∧ c = x) (edge h 1 4)
def r3 (h : Holes) (b : Boundary) (x : Color) := join h b 2 6 4 (r2 h b x) (edge h 4 6)
def r4 (h : Holes) (b : Boundary) (x : Color) := join h b 5 6 2 (edge h 5 2) (r3 h b x)
def r5 (h : Holes) (b : Boundary) (x : Color) :=
  join h b 6 7 5 (fun a c => r4 h b x c a) (edge h 5 7)

instance (h b x) : DecidableRel (r2 h b x) := by unfold r2; infer_instance
instance (h b x) : DecidableRel (r3 h b x) := by unfold r3; infer_instance
instance (h b x) : DecidableRel (r4 h b x) := by unfold r4; infer_instance
instance (h b x) : DecidableRel (r5 h b x) := by unfold r5; infer_instance

theorem terminal_iff (h : Holes) (b : Boundary) (x y : Color) :
    (∃ z, r5 h b x y z) ↔ ∃ f, ValidExcept b h f ∧ f 1 = x ∧ f 6 = y := by
  constructor
  · rintro ⟨a7,h6,h7,h67,a5,h5,hR4,h57⟩
    rcases hR4 with ⟨_,_,h56,a2,h2,h52,hR3⟩
    rcases hR3 with ⟨_,_,h26,a4,h4,hR2,h46⟩
    rcases hR2 with ⟨_,_,h24,a1,h1,⟨hR1,hx⟩,h14⟩
    rcases hR1 with ⟨_,_,h12,a3,h3,hR0,h32⟩
    rcases hR0 with ⟨_,_,h13,a0,h0,h10,h03⟩
    have h25 := (edge_comm h 2 5 a2 a5).mpr h52
    have h23 := (edge_comm h 2 3 a2 a3).mpr h32
    have h01 := (edge_comm h 0 1 a0 a1).mpr h10
    refine ⟨![a0,a1,a2,a3,a4,a5,y,a7], ?_, hx, rfl⟩
    apply (StripPuncturedExtension.relaxed_iff _ _ _).mp
    simp [StripPuncturedExtension.Relaxed, edges, Fin.forall_fin_succ,
      h0,h1,h2,h3,h4,h5,h6,h7,h67,h57,h56,h25,h26,h46,h24,h14,h12,h23,h13,h01,h03]
  · rintro ⟨f,hf,hx,hy⟩
    obtain ⟨hu,he⟩ := (StripPuncturedExtension.relaxed_iff h b f).mpr hf
    have e {i j : Fin 8} (hm : (i,j) ∈ edges) : edge h i j (f i) (f j) := he _ hm
    subst x; subst y
    refine ⟨f 7,hu 6,hu 7,e (by decide),f 5,hu 5,?_,e (by decide)⟩
    refine ⟨hu 5,hu 6,e (by decide),f 2,hu 2,(edge_comm _ _ _ _ _).mp (e (by decide)),?_⟩
    refine ⟨hu 2,hu 6,e (by decide),f 4,hu 4,?_,e (by decide)⟩
    refine ⟨hu 2,hu 4,e (by decide),f 1,hu 1,⟨?_,rfl⟩,e (by decide)⟩
    refine ⟨hu 1,hu 2,e (by decide),f 3,hu 3,?_,(edge_comm _ _ _ _ _).mp (e (by decide))⟩
    exact ⟨hu 1,hu 3,e (by decide),f 0,hu 0,
      (edge_comm _ _ _ _ _).mp (e (by decide)),e (by decide)⟩

def Possible (b : Boundary) (p : Color × Color) : Prop :=
  ∃ h : Fin 8, h ≠ 1 ∧ h ≠ 6 ∧ ∃ z, r5 {h} b p.1 p.2 z
instance (b p) : Decidable (Possible b p) := by unfold Possible; infer_instance

def choices (b : Boundary) : Finset (Color × Color) := Finset.univ.filter (Possible b)

theorem possible_iff (b : Boundary) (p : Color × Color) :
    Possible b p ↔ ∃ h : Fin 8, h ≠ 1 ∧ h ≠ 6 ∧
      ∃ f, ValidExcept b {h} f ∧ f 1 = p.1 ∧ f 6 = p.2 := by
  simp only [Possible, terminal_iff]

/-- Every counted choice constructs a colouring of the actual induced source,
fixing all ports and both anchors. -/
theorem reconstruct (b : Boundary) (p : Color × Color)
    (hb : StripSourceExtension.ProperBoundary b) (hp : Possible b p) :
    ∃ h : Fin 8, ∃ h1 : (1 : Fin 8) ∉ ({h} : Holes),
      ∃ h6 : (6 : Fin 8) ∉ ({h} : Holes),
      ∃ k : (TriangleStripAnchors.input0099.graph.induce {v | Live {h} v}).Coloring Color,
        (∀ i, k ⟨port i,live_port {h} i⟩ = b i) ∧
        k ⟨TriangleStripAnchors.vertex0099 1,(live_core {h} 1).mpr h1⟩ = p.1 ∧
        k ⟨TriangleStripAnchors.vertex0099 6,(live_core {h} 6).mpr h6⟩ = p.2 := by
  obtain ⟨h,h1,h6,f,hf,hx,hy⟩ := (possible_iff b p).mp hp
  refine ⟨h,by simpa [ne_comm] using h1,by simpa [ne_comm] using h6,
    .mk (fun v => StripSourceExtension.completeColour b f v.val)
      (fun {u v} e => partial_valid b {h} f hb hf u.val v.val u.property v.property e),
    fun i => StripSourceExtension.colour_port b f i,?_,?_⟩
  · exact (StripSourceExtension.colour_core b f 1).trans hx
  · exact (StripSourceExtension.colour_core b f 6).trans hy

theorem partial_map (g : Equiv.Perm Color) {b : Boundary} {h : Holes}
    {f : Fin 8 → Color} (hf : ValidExcept b h f) :
    ValidExcept (fun i => g (b i)) h (fun i => g (f i)) :=
  ⟨fun v hv i hi eq => hf.1 v hv i hi (g.injective eq),
    fun e he hu hv eq => hf.2 e he hu hv (g.injective eq)⟩

theorem possible_map (g : Equiv.Perm Color) (b : Boundary) (p : Color × Color) :
    Possible (fun i => g (b i)) (g p.1,g p.2) ↔ Possible b p := by
  rw [possible_iff, possible_iff]
  constructor
  · rintro ⟨h,h1,h6,f,hf,hx,hy⟩
    exact ⟨h,h1,h6,(fun i => g.symm (f i)), by simpa using partial_map g.symm hf,
      by simp [hx], by simp [hy]⟩
  · rintro ⟨h,h1,h6,f,hf,hx,hy⟩
    exact ⟨h,h1,h6,(fun i => g (f i)), partial_map g hf, congrArg g hx, congrArg g hy⟩

theorem count_map (g : Equiv.Perm Color) (b : Boundary) :
    (choices (fun i => g (b i))).card = (choices b).card := by
  let e := Equiv.prodCongr g g
  have eq : choices (fun i => g (b i)) = (choices b).map e.toEmbedding := by
    ext p
    simp only [choices, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map]
    constructor
    · intro hp
      exact ⟨(g.symm p.1,g.symm p.2),
        (possible_map g b _).mp (by simpa using hp), by simp [e]⟩
    · rintro ⟨q,hq,rfl⟩
      exact (possible_map g b q).mpr hq
  rw [eq,Finset.card_map]

def Full (b : Boundary) : Prop := ∃ a c, StripResponseSummary.r5 b a c
instance (b) : Decidable (Full b) := by unfold Full; infer_instance

theorem full_iff (b : Boundary) : Full b ↔ ∃ f, ValidCore b f :=
  StripResponseSummary.terminal_iff b

theorem full_map (g : Equiv.Perm Color) (b : Boundary) :
    Full (fun i => g (b i)) ↔ Full b := by
  rw [full_iff,full_iff]
  have maps (g : Equiv.Perm Color) {b : Boundary} {f} (hf : ValidCore b f) :
      ValidCore (fun i => g (b i)) (fun i => g (f i)) :=
    ⟨fun v i hi eq => hf.1 v i hi (g.injective eq),
      fun e he eq => hf.2 e he (g.injective eq)⟩
  constructor
  · rintro ⟨f,hf⟩
    exact ⟨_, by simpa using maps g.symm hf⟩
  · rintro ⟨f,hf⟩
    exact ⟨_, maps g hf⟩

end FourColor.StripAnchoredExtension
