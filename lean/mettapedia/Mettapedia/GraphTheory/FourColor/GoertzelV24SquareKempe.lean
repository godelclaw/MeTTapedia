import Mettapedia.GraphTheory.FourColor.GoertzelV24Square

namespace Mettapedia.GraphTheory.FourColor

open SimpleGraph

/-- In the all-equal square fiber, opposite internal edges have equal colors
and consecutive internal edges form a valid nonzero color pair. -/
theorem squareAllEqual_internalPattern :
    ∀ w : SquareBoundaryWord, ∀ x : SquareInternalColoring,
      IsSquareExtension w x → w.AllEqual →
        x 0 = x 2 ∧ x 1 = x 3 ∧
          x 0 ≠ 0 ∧ x 1 ≠ 0 ∧ x 0 ≠ x 1 := by
  intro w x hx hall
  rcases hx with ⟨h0, h1, h2, h3⟩
  have third_unique {p a b c : Color}
      (hab : ProperColorTriple p a b)
      (hbc : ProperColorTriple p b c) : a = c := by
    by_contra hac
    exact false_of_four_pairwise_distinct_nonzero_colors
      hab.1 hab.2.2.1 hab.2.1 hbc.2.2.1
      hab.2.2.2.2.1 hab.2.2.2.1 hbc.2.2.2.2.1
      hab.2.2.2.2.2.symm hbc.2.2.2.2.2 hac
  have h01 : w 0 = w 1 := hall.1
  have h12 : w 1 = w 2 := hall.2.1
  have hx31 : x 3 = x 1 := by
    apply third_unique h0
    simpa [← h01] using h1
  have hx02 : x 0 = x 2 := by
    apply third_unique h1
    simpa [← h12] using h2
  exact ⟨hx02, hx31.symm, h0.2.2.1, h1.2.2.1,
    h1.2.2.2.2.2⟩

namespace RotationSystem

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E]
variable (RS : RotationSystem V E)

omit [Fintype V] in
private theorem pairwise_ne_of_quad_card_eq_four {a b c d : V}
    (hcard : ({a, b, c, d} : Finset V).card = 4) :
    a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d := by
  constructor
  · intro hab
    subst b
    have h' : ({a, c, d} : Finset V).card = 4 := by simpa using hcard
    have hle : ({a, c, d} : Finset V).card ≤ 3 := Finset.card_le_three
    omega
  · constructor
    · intro hac
      subst c
      have h' : ({b, a, d} : Finset V).card = 4 := by simpa using hcard
      have hle : ({b, a, d} : Finset V).card ≤ 3 := Finset.card_le_three
      omega
    · constructor
      · intro had
        subst d
        have h' : ({b, c, a} : Finset V).card = 4 := by simpa using hcard
        have hle : ({b, c, a} : Finset V).card ≤ 3 := Finset.card_le_three
        omega
      · constructor
        · intro hbc
          subst c
          have h' : ({a, b, d} : Finset V).card = 4 := by simpa using hcard
          have hle : ({a, b, d} : Finset V).card ≤ 3 := Finset.card_le_three
          omega
        · constructor
          · intro hbd
            subst d
            have h' : ({a, c, b} : Finset V).card = 4 := by simpa using hcard
            have hle : ({a, c, b} : Finset V).card ≤ 3 := Finset.card_le_three
            omega
          · intro hcd
            subst d
            have h' : ({a, b, c} : Finset V).card = 4 := by simpa using hcard
            have hle : ({a, b, c} : Finset V).card ≤ 3 := Finset.card_le_three
            omega

/-- Two distinct vertices already exhaust the two endpoints of an edge when
both are incident to that edge. -/
theorem endpoints_eq_pair_of_mem_incidentEdges
    {e : E} {u v : V} (hne : u ≠ v)
    (hu : e ∈ RS.incidentEdges u) (hv : e ∈ RS.incidentEdges v) :
    RS.endpoints e = {u, v} := by
  have hsubset : ({u, v} : Finset V) ⊆ RS.endpoints e := by
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact RS.mem_endpoints_iff_mem_incidentEdges.mpr hu
    · have : x = v := Finset.mem_singleton.mp hx
      subst x
      exact RS.mem_endpoints_iff_mem_incidentEdges.mpr hv
  have hcardle : (RS.endpoints e).card ≤ ({u, v} : Finset V).card := by
    rw [RS.endpoints_card_two, Finset.card_pair hne]
  exact (Finset.eq_of_subset_of_card_le hsubset hcardle).symm

namespace FacialSquareData

/-- The four internal edges of a named facial square. -/
def squareEdges (Q : @FacialSquareData V E) : Finset E :=
  {Q.wx, Q.xy, Q.yz, Q.zw}

end FacialSquareData

/-- The four square edges have the expected two endpoint sets, derived from
the computed incidence data and distinctness of the four square vertices. -/
theorem facialSquare_edgeEndpoints
    (Q : @FacialSquareData V E) (hQ : Q.WellFormed RS) :
    RS.endpoints Q.wx = {Q.w, Q.x} ∧
    RS.endpoints Q.xy = {Q.x, Q.y} ∧
    RS.endpoints Q.yz = {Q.y, Q.z} ∧
    RS.endpoints Q.zw = {Q.z, Q.w} := by
  have hv := pairwise_ne_of_quad_card_eq_four hQ.1
  constructor
  · apply RS.endpoints_eq_pair_of_mem_incidentEdges hv.1
    · rw [hQ.2.1]; simp
    · rw [hQ.2.2.1]; simp
  · constructor
    · apply RS.endpoints_eq_pair_of_mem_incidentEdges hv.2.2.2.1
      · rw [hQ.2.2.1]; simp
      · rw [hQ.2.2.2.1]; simp
    · constructor
      · apply RS.endpoints_eq_pair_of_mem_incidentEdges hv.2.2.2.2.2
        · rw [hQ.2.2.2.1]; simp
        · rw [hQ.2.2.2.2.1]; simp
      · apply RS.endpoints_eq_pair_of_mem_incidentEdges hv.2.2.1.symm
        · rw [hQ.2.2.2.2.1]; simp
        · rw [hQ.2.1]; simp

/-- A selected-color edge adjacent to an all-equal facial square cannot
leave the square. Exact incidence leaves only the two square edges and the
outer third-color edge at either endpoint. -/
theorem bicolored_adjacent_to_facialSquare_mem_squareEdges
    (Q : @FacialSquareData V E) (hQ : Q.WellFormed RS)
    (hCubic : RS.IsCubic) (C : RS.EdgeColoring Color)
    (hC : RS.IsTaitEdgeColoring C)
    (hall : (Q.boundaryWord C).AllEqual)
    {q : E} (hq : q ∈ Q.squareEdges)
    (g : C.bicoloredSet (C Q.wx) (C Q.xy))
    (hadj : RS.edgeAdjacencyGraph.Adj q g.val) :
    g.val ∈ Q.squareEdges := by
  have hext := RS.facialSquare_internalColoring_isSquareExtension
    Q hQ hCubic C hC
  have hproper :
      ProperColorTriple (C Q.outerW) (C Q.zw) (C Q.wx) ∧
      ProperColorTriple (C Q.outerX) (C Q.wx) (C Q.xy) ∧
      ProperColorTriple (C Q.outerY) (C Q.xy) (C Q.yz) ∧
      ProperColorTriple (C Q.outerZ) (C Q.yz) (C Q.zw) := by
    simpa [IsSquareExtension, FacialSquareData.boundaryWord,
      FacialSquareData.internalColoring, FacialSquareData.colorQuad] using hext
  have hpattern := squareAllEqual_internalPattern
    (Q.boundaryWord C) (Q.internalColoring C) hext hall
  have hcolors :
      C Q.wx = C Q.yz ∧ C Q.xy = C Q.zw ∧
      C Q.wx ≠ 0 ∧ C Q.xy ≠ 0 ∧ C Q.wx ≠ C Q.xy := by
    simpa [FacialSquareData.internalColoring,
      FacialSquareData.colorQuad] using hpattern
  have atW {e : E} (he : e ∈ RS.incidentEdges Q.w)
      (heColor : C e = C Q.wx ∨ C e = C Q.xy) :
      e ∈ Q.squareEdges := by
    rw [hQ.2.1] at he
    simp only [Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with rfl | rfl | rfl
    · exfalso
      rcases heColor with heColor | heColor
      · exact hproper.1.2.2.2.2.1 heColor
      · exact hproper.1.2.2.2.1 (heColor.trans hcolors.2.1)
    · simp [FacialSquareData.squareEdges]
    · simp [FacialSquareData.squareEdges]
  have atX {e : E} (he : e ∈ RS.incidentEdges Q.x)
      (heColor : C e = C Q.wx ∨ C e = C Q.xy) :
      e ∈ Q.squareEdges := by
    rw [hQ.2.2.1] at he
    simp only [Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with rfl | rfl | rfl
    · exfalso
      rcases heColor with heColor | heColor
      · exact hproper.2.1.2.2.2.1 heColor
      · exact hproper.2.1.2.2.2.2.1 heColor
    · simp [FacialSquareData.squareEdges]
    · simp [FacialSquareData.squareEdges]
  have atY {e : E} (he : e ∈ RS.incidentEdges Q.y)
      (heColor : C e = C Q.wx ∨ C e = C Q.xy) :
      e ∈ Q.squareEdges := by
    rw [hQ.2.2.2.1] at he
    simp only [Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with rfl | rfl | rfl
    · exfalso
      rcases heColor with heColor | heColor
      · exact hproper.2.2.1.2.2.2.2.1 (heColor.trans hcolors.1)
      · exact hproper.2.2.1.2.2.2.1 heColor
    · simp [FacialSquareData.squareEdges]
    · simp [FacialSquareData.squareEdges]
  have atZ {e : E} (he : e ∈ RS.incidentEdges Q.z)
      (heColor : C e = C Q.wx ∨ C e = C Q.xy) :
      e ∈ Q.squareEdges := by
    rw [hQ.2.2.2.2.1] at he
    simp only [Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with rfl | rfl | rfl
    · exfalso
      have hZ := hproper.2.2.2
      rcases heColor with heColor | heColor
      · exact hZ.2.2.2.1 (heColor.trans hcolors.1)
      · exact hZ.2.2.2.2.1 (heColor.trans hcolors.2.1)
    · simp [FacialSquareData.squareEdges]
    · simp [FacialSquareData.squareEdges]
  have hends := RS.facialSquare_edgeEndpoints Q hQ
  rcases (RS.edgeAdjacencyGraph_adj_iff).1 hadj with
    ⟨_hne, v, hvq, hvg⟩
  have hgv : g.val ∈ RS.incidentEdges v :=
    RS.mem_endpoints_iff_mem_incidentEdges.mp hvg
  simp only [FacialSquareData.squareEdges, Finset.mem_insert,
    Finset.mem_singleton] at hq
  rcases hq with rfl | rfl | rfl | rfl
  · rw [hends.1] at hvq
    simp only [Finset.mem_insert, Finset.mem_singleton] at hvq
    rcases hvq with rfl | rfl
    · exact atW hgv g.property
    · exact atX hgv g.property
  · rw [hends.2.1] at hvq
    simp only [Finset.mem_insert, Finset.mem_singleton] at hvq
    rcases hvq with rfl | rfl
    · exact atX hgv g.property
    · exact atY hgv g.property
  · rw [hends.2.2.1] at hvq
    simp only [Finset.mem_insert, Finset.mem_singleton] at hvq
    rcases hvq with rfl | rfl
    · exact atY hgv g.property
    · exact atZ hgv g.property
  · rw [hends.2.2.2] at hvq
    simp only [Finset.mem_insert, Finset.mem_singleton] at hvq
    rcases hvq with rfl | rfl
    · exact atZ hgv g.property
    · exact atW hgv g.property

/-- In an all-equal square fiber, the bicolored component through one square
edge is exactly the set of four square edges. -/
theorem facialSquare_kempeComponentSet_eq_squareEdges
    (Q : @FacialSquareData V E) (hQ : Q.WellFormed RS)
    (hCubic : RS.IsCubic) (C : RS.EdgeColoring Color)
    (hC : RS.IsTaitEdgeColoring C)
    (hall : (Q.boundaryWord C).AllEqual) :
    C.kempeComponentSet (C Q.wx) (C Q.xy)
        ((C.bicoloredSubgraph (C Q.wx) (C Q.xy)).connectedComponentMk
          ⟨Q.wx, Or.inl rfl⟩) =
      (Q.squareEdges : Set E) := by
  have hext := RS.facialSquare_internalColoring_isSquareExtension
    Q hQ hCubic C hC
  have hpattern := squareAllEqual_internalPattern
    (Q.boundaryWord C) (Q.internalColoring C) hext hall
  have hcolors :
      C Q.wx = C Q.yz ∧ C Q.xy = C Q.zw ∧
      C Q.wx ≠ 0 ∧ C Q.xy ≠ 0 ∧ C Q.wx ≠ C Q.xy := by
    simpa [FacialSquareData.internalColoring,
      FacialSquareData.colorQuad] using hpattern
  have hneWX_XY : Q.wx ≠ Q.xy := fun h => hcolors.2.2.2.2 (congrArg C h)
  have hneXY_YZ : Q.xy ≠ Q.yz := by
    intro h
    apply hcolors.2.2.2.2.symm
    exact (congrArg C h).trans hcolors.1.symm
  have hneZW_WX : Q.zw ≠ Q.wx := by
    intro h
    apply hcolors.2.2.2.2.symm
    exact hcolors.2.1.trans (congrArg C h)
  have hAdjWX_XY : RS.edgeAdjacencyGraph.Adj Q.wx Q.xy := by
    apply RS.edgeAdjacencyGraph_adj_of_mem_incidentEdges hneWX_XY
    · rw [hQ.2.2.1]; simp
    · rw [hQ.2.2.1]; simp
  have hAdjXY_YZ : RS.edgeAdjacencyGraph.Adj Q.xy Q.yz := by
    apply RS.edgeAdjacencyGraph_adj_of_mem_incidentEdges hneXY_YZ
    · rw [hQ.2.2.2.1]; simp
    · rw [hQ.2.2.2.1]; simp
  have hAdjWX_ZW : RS.edgeAdjacencyGraph.Adj Q.wx Q.zw := by
    apply RS.edgeAdjacencyGraph_adj_of_mem_incidentEdges hneZW_WX.symm
    · rw [hQ.2.1]; simp
    · rw [hQ.2.1]; simp
  let K :=
    (C.bicoloredSubgraph (C Q.wx) (C Q.xy)).connectedComponentMk
      ⟨Q.wx, Or.inl rfl⟩
  have hWX : Q.wx ∈ C.kempeComponentSet (C Q.wx) (C Q.xy) K :=
    C.mem_kempeComponentSet_self (Or.inl rfl)
  have hXY : Q.xy ∈ C.kempeComponentSet (C Q.wx) (C Q.xy) K :=
    C.mem_kempeComponentSet_of_adj hWX hAdjWX_XY (Or.inr rfl)
  have hYZ : Q.yz ∈ C.kempeComponentSet (C Q.wx) (C Q.xy) K :=
    C.mem_kempeComponentSet_of_adj hXY hAdjXY_YZ
      (Or.inl hcolors.1.symm)
  have hZW : Q.zw ∈ C.kempeComponentSet (C Q.wx) (C Q.xy) K :=
    C.mem_kempeComponentSet_of_adj hWX hAdjWX_ZW
      (Or.inr hcolors.2.1.symm)
  ext e
  constructor
  · rintro ⟨heBi, heComponent⟩
    let H := C.bicoloredSubgraph (C Q.wx) (C Q.xy)
    let eH : C.bicoloredSet (C Q.wx) (C Q.xy) := ⟨e, heBi⟩
    let wxH : C.bicoloredSet (C Q.wx) (C Q.xy) :=
      ⟨Q.wx, Or.inl rfl⟩
    have hreach : H.Reachable eH wxH :=
      ConnectedComponent.exact heComponent
    have hrt : Relation.ReflTransGen H.Adj eH wxH :=
      (SimpleGraph.reachable_iff_reflTransGen eH wxH).1 hreach
    exact Relation.ReflTransGen.head_induction_on
      (motive := fun a _ => a.val ∈ Q.squareEdges)
      hrt (by change Q.wx ∈ Q.squareEdges
              simp [FacialSquareData.squareEdges]) (by
        intro a c hac _ ih
        exact RS.bicolored_adjacent_to_facialSquare_mem_squareEdges
          Q hQ hCubic C hC hall ih a hac.symm)
  · intro he
    have hcases :
        e = Q.wx ∨ e = Q.xy ∨ e = Q.yz ∨ e = Q.zw := by
      simpa [FacialSquareData.squareEdges] using he
    rcases hcases with he | he | he | he
    · exact he.symm ▸ hWX
    · exact he.symm ▸ hXY
    · exact he.symm ▸ hYZ
    · exact he.symm ▸ hZW

private theorem colorSwap_eq_equivSwap (a b x : Color) :
    Color.swap a b x = Equiv.swap a b x := by
  by_cases hxa : x = a
  · subst x
    simp
  · by_cases hxb : x = b
    · subst x
      simp
    · simp [Color.swap, hxa, hxb, Equiv.swap_apply_def]

/-- Exact pointwise formula for the all-equal square-cycle switch: it swaps
the two internal colors on the four square edges and fixes every other
ambient edge. -/
theorem facialSquare_cycleSwap_apply
    (Q : @FacialSquareData V E) (hQ : Q.WellFormed RS)
    (hCubic : RS.IsCubic) (C : RS.EdgeColoring Color)
    (hC : RS.IsTaitEdgeColoring C)
    (hall : (Q.boundaryWord C).AllEqual) (e : E) :
    C.swapOnKempeComponent (C Q.wx) (C Q.xy)
        ((C.bicoloredSubgraph (C Q.wx) (C Q.xy)).connectedComponentMk
          ⟨Q.wx, Or.inl rfl⟩) e =
      if e ∈ Q.squareEdges
      then Color.swap (C Q.wx) (C Q.xy) (C e)
      else C e := by
  have hcomponent :=
    RS.facialSquare_kempeComponentSet_eq_squareEdges Q hQ hCubic C hC hall
  by_cases he : e ∈ Q.squareEdges
  · rw [C.swapOnKempeComponent_apply_of_mem]
    · rw [colorSwap_eq_equivSwap]
      simp [he]
    · rw [hcomponent]
      exact he
  · rw [C.swapOnKempeComponent_apply_of_not_mem]
    · simp [he]
    · rw [hcomponent]
      exact he

/-- SQ1 at graph level: the two states of an all-equal facial-square fiber
are connected by a genuine ambient Kempe step whose component is exactly the
four-edge square cycle. -/
theorem facialSquare_allEqualFiber_cycleKempeStep
    (Q : @FacialSquareData V E) (hQ : Q.WellFormed RS)
    (hCubic : RS.IsCubic) (C : RS.EdgeColoring Color)
    (hC : RS.IsTaitEdgeColoring C)
    (hall : (Q.boundaryWord C).AllEqual) :
    RS.edgeAdjacencyGraph.KempeStep C
        (C.swapOnKempeComponent (C Q.wx) (C Q.xy)
          ((C.bicoloredSubgraph (C Q.wx) (C Q.xy)).connectedComponentMk
            ⟨Q.wx, Or.inl rfl⟩)) ∧
    C.kempeComponentSet (C Q.wx) (C Q.xy)
        ((C.bicoloredSubgraph (C Q.wx) (C Q.xy)).connectedComponentMk
          ⟨Q.wx, Or.inl rfl⟩) = (Q.squareEdges : Set E) ∧
    ∀ e : E,
      C.swapOnKempeComponent (C Q.wx) (C Q.xy)
          ((C.bicoloredSubgraph (C Q.wx) (C Q.xy)).connectedComponentMk
            ⟨Q.wx, Or.inl rfl⟩) e =
        if e ∈ Q.squareEdges
        then Color.swap (C Q.wx) (C Q.xy) (C e)
        else C e := by
  exact ⟨RS.edgeAdjacencyGraph.kempeStep_swapOnKempeComponent
      C (C Q.wx) (C Q.xy) _,
    RS.facialSquare_kempeComponentSet_eq_squareEdges Q hQ hCubic C hC hall,
    RS.facialSquare_cycleSwap_apply Q hQ hCubic C hC hall⟩

end RotationSystem

end Mettapedia.GraphTheory.FourColor
