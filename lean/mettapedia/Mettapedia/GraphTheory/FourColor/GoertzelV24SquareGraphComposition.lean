import Mettapedia.GraphTheory.FourColor.GoertzelV24SquareGraphSplit

namespace Mettapedia.GraphTheory.FourColor

open SimpleGraph

private abbrev SelectedComponentStep {N : Type*}
    (G H : SimpleGraph N) (Selected : N → Prop) (u v : N) : Prop :=
  Selected u ∧ Selected v ∧ (G.Reachable u v ∨ H.Reachable u v)

private def SelectedSplitState {N : Type*}
    (G H : SimpleGraph N) (Selected : N → Prop) (start current : N) : Prop :=
  (Selected current ∧
      Relation.ReflTransGen (SelectedComponentStep G H Selected) start current) ∨
  (∃ last, Selected last ∧
      Relation.ReflTransGen (SelectedComponentStep G H Selected) start last ∧
      last ≠ current ∧ G.Reachable last current) ∨
  (∃ last, Selected last ∧
      Relation.ReflTransGen (SelectedComponentStep G H Selected) start last ∧
      last ≠ current ∧ H.Reachable last current)

private theorem selectedSplitState_step
    {N : Type*} (G H : SimpleGraph N) (Selected : N → Prop) (start u v : N)
    (hswitch : ∀ {x m y}, x ≠ m → m ≠ y →
      G.Reachable x m → H.Reachable m y → Selected m)
    (hu : SelectedSplitState G H Selected start u)
    (huv : G.Adj u v ∨ H.Adj u v) :
    SelectedSplitState G H Selected start v := by
  rcases huv with hG | hH
  · rcases hu with ⟨huSel, hstart⟩ | ⟨last, hlastSel, hstart, hne, hreach⟩ |
        ⟨last, hlastSel, hstart, hne, hreach⟩
    · exact Or.inr (Or.inl ⟨u, huSel, hstart, hG.ne, hG.reachable⟩)
    · by_cases hlv : last = v
      · subst v
        exact Or.inl ⟨hlastSel, hstart⟩
      · exact Or.inr (Or.inl
          ⟨last, hlastSel, hstart, hlv, hreach.trans hG.reachable⟩)
    · have huSel : Selected u :=
        hswitch hG.ne.symm hne.symm hG.reachable.symm hreach.symm
      exact Or.inr (Or.inl ⟨u, huSel,
        hstart.tail ⟨hlastSel, huSel, Or.inr hreach⟩, hG.ne, hG.reachable⟩)
  · rcases hu with ⟨huSel, hstart⟩ | ⟨last, hlastSel, hstart, hne, hreach⟩ |
        ⟨last, hlastSel, hstart, hne, hreach⟩
    · exact Or.inr (Or.inr ⟨u, huSel, hstart, hH.ne, hH.reachable⟩)
    · have huSel : Selected u :=
        hswitch hne hH.ne hreach hH.reachable
      exact Or.inr (Or.inr ⟨u, huSel,
        hstart.tail ⟨hlastSel, huSel, Or.inl hreach⟩, hH.ne, hH.reachable⟩)
    · by_cases hlv : last = v
      · subst v
        exact Or.inl ⟨hlastSel, hstart⟩
      · exact Or.inr (Or.inr
          ⟨last, hlastSel, hstart, hlv, hreach.trans hH.reachable⟩)

private theorem selectedSplitState_of_reflTransGen
    {N : Type*} (G H : SimpleGraph N) (Selected : N → Prop) (start current : N)
    (hswitch : ∀ {x m y}, x ≠ m → m ≠ y →
      G.Reachable x m → H.Reachable m y → Selected m)
    (hstart : Selected start)
    (hpath : Relation.ReflTransGen (fun x y => G.Adj x y ∨ H.Adj x y)
      start current) :
    SelectedSplitState G H Selected start current := by
  induction hpath with
  | refl => exact Or.inl ⟨hstart, Relation.ReflTransGen.refl⟩
  | tail hxy hyz ih =>
      exact selectedSplitState_step G H Selected start _ _ hswitch ih hyz

private theorem reachable_sup_iff_selected_componentClosure
    {N : Type*} (G H : SimpleGraph N) (Selected : N → Prop) (u v : N)
    (hu : Selected u) (hv : Selected v)
    (hswitch : ∀ {x m y}, x ≠ m → m ≠ y →
      G.Reachable x m → H.Reachable m y → Selected m) :
    (G ⊔ H).Reachable u v ↔
      Relation.ReflTransGen (SelectedComponentStep G H Selected) u v := by
  constructor
  · intro huv
    have hpath : Relation.ReflTransGen (fun x y => G.Adj x y ∨ H.Adj x y) u v := by
      have h := (SimpleGraph.reachable_iff_reflTransGen u v).mp huv
      exact h.mono fun x y hxy => (SimpleGraph.sup_adj G H x y).mp hxy
    have hstate : SelectedSplitState G H Selected u v :=
      selectedSplitState_of_reflTransGen G H Selected u v hswitch hu hpath
    rcases hstate with ⟨_, h⟩ | ⟨last, hlastSel, h, _, hreach⟩ |
        ⟨last, hlastSel, h, _, hreach⟩
    · exact h
    · exact h.tail ⟨hlastSel, hv, Or.inl hreach⟩
    · exact h.tail ⟨hlastSel, hv, Or.inr hreach⟩
  · intro huv
    exact Relation.ReflTransGen.trans_induction_on
      (motive := fun {x y} _ => (G ⊔ H).Reachable x y) huv
      (fun _ => SimpleGraph.Reachable.rfl)
      (fun hxy => hxy.2.2.elim
        (SimpleGraph.Reachable.mono le_sup_left)
        (SimpleGraph.Reachable.mono le_sup_right))
      (fun _ _ ihxy ihyz => ihxy.trans ihyz)

private theorem selectedClosure_to_subtype
    {N : Type*} (G H : SimpleGraph N) (Selected : N → Prop) {u v : N}
    (hu : Selected u) (hv : Selected v)
    (h : Relation.ReflTransGen (SelectedComponentStep G H Selected) u v) :
    Relation.ReflTransGen
      (fun x y : Subtype Selected => G.Reachable x y ∨ H.Reachable x y)
      ⟨u, hu⟩ ⟨v, hv⟩ := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail hxy hyz ih =>
      exact (ih hyz.1).tail hyz.2.2

/-- If every genuine change from a `G` component to an `H` component occurs
inside `Selected`, reachability in `G ⊔ H` between selected vertices is the
closure of whole-factor component moves on the selected subtype. -/
theorem reachable_sup_iff_subtype_componentClosure
    {N : Type*} (G H : SimpleGraph N) (Selected : N → Prop) (u v : N)
    (hu : Selected u) (hv : Selected v)
    (hswitch : ∀ {x m y}, x ≠ m → m ≠ y →
      G.Reachable x m → H.Reachable m y → Selected m) :
    (G ⊔ H).Reachable u v ↔
      Relation.ReflTransGen
        (fun x y : Subtype Selected => G.Reachable x y ∨ H.Reachable x y)
        ⟨u, hu⟩ ⟨v, hv⟩ := by
  rw [reachable_sup_iff_selected_componentClosure G H Selected u v hu hv hswitch]
  constructor
  · exact selectedClosure_to_subtype G H Selected hu hv
  · intro h
    exact h.lift Subtype.val fun x y hxy => ⟨x.2, y.2, hxy⟩

/-- Reachability is reflected as well as preserved when a graph is mapped
along an embedding. -/
theorem reachable_map_embedding_iff
    {A B : Type*} (G : SimpleGraph A) (f : A ↪ B) (u v : A) :
    (G.map f).Reachable (f u) (f v) ↔ G.Reachable u v := by
  constructor
  · intro huv
    have hpath := (SimpleGraph.reachable_iff_reflTransGen (f u) (f v)).mp huv
    have lift {y : B}
        (hpath : Relation.ReflTransGen (G.map f).Adj (f u) y) :
        ∃ w, f w = y ∧ G.Reachable u w := by
      induction hpath with
      | refl => exact ⟨u, rfl, SimpleGraph.Reachable.rfl⟩
      | tail hxy hyz ih =>
          rcases ih with ⟨w, hw, huw⟩
          rcases (SimpleGraph.map_adj f G _ _).mp hyz with
            ⟨p, q, hpq, hp, hq⟩
          have hwp : w = p := f.injective (hw.trans hp.symm)
          subst p
          exact ⟨q, hq, huw.trans hpq.reachable⟩
    rcases lift hpath with ⟨w, hw, huw⟩
    exact f.injective hw ▸ huw
  · intro huv
    have hpath := (SimpleGraph.reachable_iff_reflTransGen u v).mp huv
    exact (SimpleGraph.reachable_iff_reflTransGen (f u) (f v)).mpr
      (hpath.lift f fun x y hxy => SimpleGraph.map_adj_apply.mpr hxy)

/-- At distinct portals, reachability in the local square line graph already
supplies the tracked-color guards recorded by its Boolean profile. -/
theorem squareLineGraph_reachable_portal_iff_profile
    (w : SquareBoundaryWord) (x : SquareInternalColoring)
    (a b : Color) (i j : Fin 4) (hij : i ≠ j) :
    (squareLineGraph w x a b).Reachable
        (squarePortalNode i) (squarePortalNode j) ↔
      squareLineTrackedProfile w x a b i j = true := by
  rw [squareLineTrackedProfile_eq_true_iff]
  constructor
  · intro hreach
    have hnode : squarePortalNode i ≠ squarePortalNode j := by
      intro h
      apply hij
      exact Fin.ext (congrArg (fun z : SquareLocalNode => z.val) h)
    have hiSupport := SimpleGraph.mem_support_of_reachable hnode hreach
    have hjSupport := SimpleGraph.mem_support_of_reachable hnode.symm hreach.symm
    rcases (SimpleGraph.mem_support _).mp hiSupport with ⟨u, hiu⟩
    rcases (SimpleGraph.mem_support _).mp hjSupport with ⟨v, hjv⟩
    have hi : IsTrackedColor a b (w i) := by
      fin_cases i <;> fin_cases u <;>
        simp [squareLineGraph, SquareLineAdj, SquareLineAdjProp,
          SquareUndirectedEdge, squarePortalNode, squareCornerNode] at hiu ⊢ <;>
        aesop
    have hj : IsTrackedColor a b (w j) := by
      fin_cases j <;> fin_cases v <;>
        simp [squareLineGraph, SquareLineAdj, SquareLineAdjProp,
          SquareUndirectedEdge, squarePortalNode, squareCornerNode] at hjv ⊢ <;>
        aesop
    exact ⟨hi, hj, hreach⟩
  · exact fun h => h.2.2

namespace RotationSystem

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E]
variable (RS : RotationSystem V E)

namespace FacialSquareData

/-- The four exterior edges incident to the corners of a facial square. -/
def outerEdges (Q : @FacialSquareData V E) : Finset E :=
  {Q.outerW, Q.outerX, Q.outerY, Q.outerZ}

/-- The ambient edge represented by a local portal node. -/
def portalEdge (Q : @FacialSquareData V E) (i : Fin 4) : E :=
  Q.lineEdge (squarePortalNode i)

theorem portalEdge_mem_outerEdges
    (Q : @FacialSquareData V E) (i : Fin 4) :
    Q.portalEdge i ∈ Q.outerEdges := by
  fin_cases i <;> simp [portalEdge, outerEdges, lineEdge, squarePortalNode]

theorem portalEdge_not_mem_squareEdges
    (Q : @FacialSquareData V E) (hdist : Q.LocalEdgesDistinct) (i : Fin 4) :
    Q.portalEdge i ∉ Q.squareEdges := by
  simp only [squareEdges, Finset.mem_insert, Finset.mem_singleton]
  rintro (h | h | h | h)
  · apply hdist.ne (show squarePortalNode i ≠ 4 by fin_cases i <;> decide)
    simpa [portalEdge, lineEdge] using h
  · apply hdist.ne (show squarePortalNode i ≠ 5 by fin_cases i <;> decide)
    simpa [portalEdge, lineEdge] using h
  · apply hdist.ne (show squarePortalNode i ≠ 6 by fin_cases i <;> decide)
    simpa [portalEdge, lineEdge] using h
  · apply hdist.ne (show squarePortalNode i ≠ 7 by fin_cases i <;> decide)
    simpa [portalEdge, lineEdge] using h

theorem lineEdge_mem_outerEdges_or_squareEdges
    (Q : @FacialSquareData V E) (u : SquareLocalNode) :
    Q.lineEdge u ∈ Q.outerEdges ∨ Q.lineEdge u ∈ Q.squareEdges := by
  fin_cases u <;> simp [outerEdges, squareEdges, lineEdge]

theorem localSupport_mem_outerEdges_or_squareEdges
    (Q : @FacialSquareData V E) (C : E → Color) (a b : Color) {e : E}
    (he : e ∈ (Q.localTrackedEdgeGraph C a b).support) :
    e ∈ Q.outerEdges ∨ e ∈ Q.squareEdges := by
  rcases (SimpleGraph.mem_support _).mp he with ⟨f, hef⟩
  rcases (SimpleGraph.map_adj' Q.lineEdge _ e f).mp hef with
    ⟨_, u, v, huv, rfl, rfl⟩
  exact Q.lineEdge_mem_outerEdges_or_squareEdges u

theorem localSupport_mem_outerEdges_of_not_mem_squareEdges
    (Q : @FacialSquareData V E) (C : E → Color) (a b : Color) {e : E}
    (he : e ∈ (Q.localTrackedEdgeGraph C a b).support)
    (hext : e ∉ Q.squareEdges) :
    e ∈ Q.outerEdges :=
  (Q.localSupport_mem_outerEdges_or_squareEdges C a b he).resolve_right hext

theorem mem_outerEdges_iff_exists_portalEdge
    (Q : @FacialSquareData V E) (e : E) :
    e ∈ Q.outerEdges ↔ ∃ i : Fin 4, Q.portalEdge i = e := by
  constructor
  · simp only [outerEdges, Finset.mem_insert, Finset.mem_singleton]
    rintro (rfl | rfl | rfl | rfl)
    · exact ⟨0, by simp [portalEdge, lineEdge, squarePortalNode]⟩
    · exact ⟨1, by simp [portalEdge, lineEdge, squarePortalNode]⟩
    · exact ⟨2, by simp [portalEdge, lineEdge, squarePortalNode]⟩
    · exact ⟨3, by simp [portalEdge, lineEdge, squarePortalNode]⟩
  · rintro ⟨i, rfl⟩
    exact Q.portalEdge_mem_outerEdges i

/-- The ambient edge domain after deleting the four internal square edges. -/
abbrev ExteriorEdge (Q : @FacialSquareData V E) :=
  {e : E // e ∉ Q.squareEdges}

def portalExteriorEdge
    (Q : @FacialSquareData V E) (hdist : Q.LocalEdgesDistinct)
    (i : Fin 4) : Q.ExteriorEdge :=
  ⟨Q.portalEdge i, Q.portalEdge_not_mem_squareEdges hdist i⟩

def lineEdgeEmbedding
    (Q : @FacialSquareData V E) (hdist : Q.LocalEdgesDistinct) :
    SquareLocalNode ↪ E := ⟨Q.lineEdge, hdist⟩

theorem localTrackedEdgeGraph_reachable_lineEdge_iff
    (Q : @FacialSquareData V E) (hdist : Q.LocalEdgesDistinct)
    (C : E → Color) (a b : Color) (u v : SquareLocalNode) :
    (Q.localTrackedEdgeGraph C a b).Reachable (Q.lineEdge u) (Q.lineEdge v) ↔
      (squareLineGraph (Q.boundaryWord C) (Q.internalColoring C) a b).Reachable u v := by
  simpa [localTrackedEdgeGraph, lineEdgeEmbedding] using
    reachable_map_embedding_iff
      (squareLineGraph (Q.boundaryWord C) (Q.internalColoring C) a b)
      (Q.lineEdgeEmbedding hdist) u v

/-- A local square component between exterior edges is either reflexive or
is a component between two of the four portal edges. -/
theorem localTrackedEdgeGraph_reachable_exterior_iff
    (Q : @FacialSquareData V E) (hdist : Q.LocalEdgesDistinct)
    (C : E → Color) (a b : Color) (e f : Q.ExteriorEdge) :
    (Q.localTrackedEdgeGraph C a b).Reachable e f ↔
      e = f ∨ ∃ i j : Fin 4,
        e = Q.portalExteriorEdge hdist i ∧
        f = Q.portalExteriorEdge hdist j ∧
        (squareLineGraph (Q.boundaryWord C) (Q.internalColoring C) a b).Reachable
          (squarePortalNode i) (squarePortalNode j) := by
  constructor
  · intro hef
    by_cases heq : e = f
    · exact Or.inl heq
    · right
      have heqVal : (e : E) ≠ f := fun h => heq (Subtype.ext h)
      have heSupport : (e : E) ∈ (Q.localTrackedEdgeGraph C a b).support :=
        SimpleGraph.mem_support_of_reachable heqVal hef
      have hfSupport : (f : E) ∈ (Q.localTrackedEdgeGraph C a b).support :=
        SimpleGraph.mem_support_of_reachable heqVal.symm hef.symm
      have heOuter := Q.localSupport_mem_outerEdges_of_not_mem_squareEdges
        C a b heSupport e.2
      have hfOuter := Q.localSupport_mem_outerEdges_of_not_mem_squareEdges
        C a b hfSupport f.2
      rcases (Q.mem_outerEdges_iff_exists_portalEdge e).mp heOuter with ⟨i, hi⟩
      rcases (Q.mem_outerEdges_iff_exists_portalEdge f).mp hfOuter with ⟨j, hj⟩
      have he : e = Q.portalExteriorEdge hdist i := Subtype.ext hi.symm
      have hf : f = Q.portalExteriorEdge hdist j := Subtype.ext hj.symm
      refine ⟨i, j, he, hf, ?_⟩
      rw [he, hf] at hef
      apply (Q.localTrackedEdgeGraph_reachable_lineEdge_iff hdist C a b
        (squarePortalNode i) (squarePortalNode j)).mp
      simpa [portalExteriorEdge, portalEdge] using hef
  · rintro (rfl | ⟨i, j, rfl, rfl, hij⟩)
    · exact SimpleGraph.Reachable.rfl
    · apply (Q.localTrackedEdgeGraph_reachable_lineEdge_iff hdist C a b
        (squarePortalNode i) (squarePortalNode j)).mpr
      exact hij

/-- The component relation obtained after contracting the exterior factor
and the local square factor, on the exact non-square edge domain. -/
def facialSquareComponentStep
    (Q : @FacialSquareData V E) (hdist : Q.LocalEdgesDistinct)
    (C : E → Color) (a b : Color) (x y : Q.ExteriorEdge) : Prop :=
  x = y ∨
  (Q.exteriorTrackedEdgeGraph RS C a b).Reachable x y ∨
  ∃ i j : Fin 4,
    x = Q.portalExteriorEdge hdist i ∧
    y = Q.portalExteriorEdge hdist j ∧
    (squareLineGraph (Q.boundaryWord C) (Q.internalColoring C) a b).Reachable
      (squarePortalNode i) (squarePortalNode j)

theorem facialSquareComponentStep_symmetric
    (Q : @FacialSquareData V E) (hdist : Q.LocalEdgesDistinct)
    (C : E → Color) (a b : Color) :
    ∀ x y, Q.facialSquareComponentStep RS hdist C a b x y →
      Q.facialSquareComponentStep RS hdist C a b y x := by
  intro x y hxy
  rcases hxy with rfl | hExt | ⟨i, j, rfl, rfl, hij⟩
  · exact Or.inl rfl
  · exact Or.inr (Or.inl hExt.symm)
  · exact Or.inr (Or.inr ⟨j, i, rfl, rfl, hij.symm⟩)

/-- The graph of whole-component moves after contracting the local square
and the exterior along their four-edge portal interface. -/
def facialSquareContractedGraph
    (Q : @FacialSquareData V E) (hdist : Q.LocalEdgesDistinct)
    (C : E → Color) (a b : Color) : SimpleGraph Q.ExteriorEdge where
  Adj x y := x ≠ y ∧ Q.facialSquareComponentStep RS hdist C a b x y
  symm := ⟨by
    intro x y hxy
    exact ⟨hxy.1.symm,
      Q.facialSquareComponentStep_symmetric RS hdist C a b x y hxy.2⟩⟩
  loopless := ⟨by simp⟩

/-- Component relation with the local square factor supplied directly as a
four-portal Boolean connectivity profile. -/
def facialSquareProfileComponentStep
    (Q : @FacialSquareData V E) (hdist : Q.LocalEdgesDistinct)
    (C : E → Color) (a b : Color) (localProfile : SquareTrackedProfile)
    (x y : Q.ExteriorEdge) : Prop :=
  x = y ∨
  (Q.exteriorTrackedEdgeGraph RS C a b).Reachable x y ∨
  ∃ i j : Fin 4,
    x = Q.portalExteriorEdge hdist i ∧
    y = Q.portalExteriorEdge hdist j ∧
    localProfile i j = true

theorem facialSquareProfileComponentStep_symmetric
    (Q : @FacialSquareData V E) (hdist : Q.LocalEdgesDistinct)
    (C : E → Color) (a b : Color) (localProfile : SquareTrackedProfile)
    (hloc : ∀ i j, localProfile i j = localProfile j i) :
    ∀ x y, Q.facialSquareProfileComponentStep RS hdist C a b localProfile x y →
      Q.facialSquareProfileComponentStep RS hdist C a b localProfile y x := by
  intro x y hxy
  rcases hxy with rfl | hExt | ⟨i, j, rfl, rfl, hij⟩
  · exact Or.inl rfl
  · exact Or.inr (Or.inl hExt.symm)
  · exact Or.inr (Or.inr ⟨j, i, rfl, rfl, by simpa [hloc]⟩)

/-- Contracted component graph whose local factor is an explicit computed
four-portal profile. -/
def facialSquareProfileContractedGraph
    (Q : @FacialSquareData V E) (hdist : Q.LocalEdgesDistinct)
    (C : E → Color) (a b : Color) (localProfile : SquareTrackedProfile)
    (hloc : ∀ i j, localProfile i j = localProfile j i) :
    SimpleGraph Q.ExteriorEdge where
  Adj x y := x ≠ y ∧
    Q.facialSquareProfileComponentStep RS hdist C a b localProfile x y
  symm := ⟨by
    intro x y hxy
    exact ⟨hxy.1.symm,
      Q.facialSquareProfileComponentStep_symmetric RS hdist C a b localProfile
        hloc x y hxy.2⟩⟩
  loopless := ⟨by simp⟩

/-- Decidable adjacency underlying the profile-contracted graph. Unlike the
graph constructor, this definition does not require a symmetry proof and can
therefore be mapped uniformly over a multiset of local profiles. -/
noncomputable def facialSquareProfileAdj
    (Q : @FacialSquareData V E) (hdist : Q.LocalEdgesDistinct)
    (C : E → Color) (a b : Color) (localProfile : SquareTrackedProfile)
    (x y : Q.ExteriorEdge) : Bool := by
  classical
  exact decide (x ≠ y) &&
    decide (Q.facialSquareProfileComponentStep RS hdist C a b localProfile x y)

theorem facialSquareProfileAdj_eq_true_iff
    (Q : @FacialSquareData V E) (hdist : Q.LocalEdgesDistinct)
    (C : E → Color) (a b : Color) (localProfile : SquareTrackedProfile)
    (hloc : ∀ i j, localProfile i j = localProfile j i)
    (x y : Q.ExteriorEdge) :
    Q.facialSquareProfileAdj RS hdist C a b localProfile x y = true ↔
      (Q.facialSquareProfileContractedGraph RS hdist C a b localProfile hloc).Adj x y := by
  simp [facialSquareProfileAdj, facialSquareProfileContractedGraph]

/-- Connectivity profile on every non-square edge after composing a fixed
exterior coloring with an arbitrary four-portal local profile. Tracked-color
guards keep isolated untracked edges out of the diagonal. -/
noncomputable def facialSquareComposedTrackedProfile
    (Q : @FacialSquareData V E) (hdist : Q.LocalEdgesDistinct)
    (C : E → Color) (a b : Color) (localProfile : SquareTrackedProfile) :
    Q.ExteriorEdge → Q.ExteriorEdge → Bool := by
  classical
  exact fun e f =>
    decide (IsTrackedColor a b (C e)) &&
    decide (IsTrackedColor a b (C f)) &&
    decide (f ∈ finsetReachWithin
      (Q.facialSquareProfileAdj RS hdist C a b localProfile) e
      (Fintype.card Q.ExteriorEdge))

/-- Semantic interpretation of the computed exterior composition profile. -/
theorem facialSquareComposedTrackedProfile_eq_true_iff
    (Q : @FacialSquareData V E) (hdist : Q.LocalEdgesDistinct)
    (C : E → Color) (a b : Color) (localProfile : SquareTrackedProfile)
    (hloc : ∀ i j, localProfile i j = localProfile j i)
    (e f : Q.ExteriorEdge) :
    Q.facialSquareComposedTrackedProfile RS hdist C a b localProfile e f = true ↔
      IsTrackedColor a b (C e) ∧ IsTrackedColor a b (C f) ∧
      (Q.facialSquareProfileContractedGraph RS hdist C a b localProfile hloc).Reachable
        e f := by
  unfold facialSquareComposedTrackedProfile
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  have hreach :
      f ∈ finsetReachWithin
          (Q.facialSquareProfileAdj RS hdist C a b localProfile) e
          (Fintype.card Q.ExteriorEdge) ↔
        (Q.facialSquareProfileContractedGraph RS hdist C a b localProfile hloc).Reachable
          e f := by
    simpa using mem_finsetReachWithin_card_iff_reachable
      (Q.facialSquareProfileContractedGraph RS hdist C a b localProfile hloc)
      (Q.facialSquareProfileAdj RS hdist C a b localProfile)
      (Q.facialSquareProfileAdj_eq_true_iff RS hdist C a b localProfile hloc)
      e f
  rw [hreach]
  tauto

/-- Actual ambient tracked-color connectivity profile, restricted to the
non-square edge domain. -/
noncomputable def ambientTrackedExteriorProfile
    (Q : @FacialSquareData V E) (C : E → Color) (a b : Color) :
    Q.ExteriorEdge → Q.ExteriorEdge → Bool := by
  classical
  exact fun e f =>
    decide (IsTrackedColor a b (C e)) &&
    decide (IsTrackedColor a b (C f)) &&
    decide ((RS.trackedEdgeGraph C a b).Reachable e f)

/-- For a proper local extension and a genuine tracked color pair, the
structural square contraction is exactly the contraction obtained from the
computed four-portal profile. -/
theorem facialSquareContractedGraph_eq_profileContractedGraph
    (Q : @FacialSquareData V E) (hdist : Q.LocalEdgesDistinct)
    (C : E → Color) (a b : Color)
    (hx : Q.internalColoring C ∈ squareExtensions (Q.boundaryWord C))
    (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ≠ b) :
    Q.facialSquareContractedGraph RS hdist C a b =
      Q.facialSquareProfileContractedGraph RS hdist C a b
        (squareTrackedProfile (Q.boundaryWord C) (Q.internalColoring C) a b)
        (squareTrackedProfile_symmetric
          (Q.boundaryWord C) (Q.internalColoring C) a b) := by
  ext e f
  simp only [facialSquareContractedGraph, facialSquareProfileContractedGraph]
  constructor
  · rintro ⟨hne, hstep⟩
    refine ⟨hne, ?_⟩
    rcases hstep with heq | hExt | ⟨i, j, hi, hj, hij⟩
    · exact Or.inl heq
    · exact Or.inr (Or.inl hExt)
    · refine Or.inr (Or.inr ⟨i, j, hi, hj, ?_⟩)
      have hPortalNe : i ≠ j := by
        intro hEq
        subst j
        exact hne (hi.trans hj.symm)
      have hLine : squareLineTrackedProfile
          (Q.boundaryWord C) (Q.internalColoring C) a b i j = true :=
        (squareLineGraph_reachable_portal_iff_profile
          (Q.boundaryWord C) (Q.internalColoring C) a b i j hPortalNe).mp hij
      rw [squareLineProfile_eq_squareProfile
        (Q.boundaryWord C) (Q.internalColoring C) a b hx ha hb hab] at hLine
      exact hLine
  · rintro ⟨hne, hstep⟩
    refine ⟨hne, ?_⟩
    rcases hstep with heq | hExt | ⟨i, j, hi, hj, hij⟩
    · exact Or.inl heq
    · exact Or.inr (Or.inl hExt)
    · refine Or.inr (Or.inr ⟨i, j, hi, hj, ?_⟩)
      have hLine : squareLineTrackedProfile
          (Q.boundaryWord C) (Q.internalColoring C) a b i j = true := by
        rw [squareLineProfile_eq_squareProfile
          (Q.boundaryWord C) (Q.internalColoring C) a b hx ha hb hab]
        exact hij
      exact (squareLineTrackedProfile_eq_true_iff
        (Q.boundaryWord C) (Q.internalColoring C) a b i j).mp hLine |>.2.2

private theorem componentClosure_iff_contractedReachable
    (Q : @FacialSquareData V E) (hdist : Q.LocalEdgesDistinct)
    (C : E → Color) (a b : Color) (e f : Q.ExteriorEdge) :
    Relation.ReflTransGen (Q.facialSquareComponentStep RS hdist C a b) e f ↔
      (Q.facialSquareContractedGraph RS hdist C a b).Reachable e f := by
  constructor
  · intro hef
    apply Relation.ReflTransGen.trans_induction_on
      (motive := fun {x y} _ =>
        (Q.facialSquareContractedGraph RS hdist C a b).Reachable x y) hef
    · intro x
      exact SimpleGraph.Reachable.rfl
    · intro x y hxy
      by_cases heq : x = y
      · subst y
        exact SimpleGraph.Reachable.rfl
      · exact (show (Q.facialSquareContractedGraph RS hdist C a b).Adj x y
          from ⟨heq, hxy⟩).reachable
    · intro x y z hxy hyz ihxy ihyz
      exact ihxy.trans ihyz
  · intro hef
    have hpath := (SimpleGraph.reachable_iff_reflTransGen e f).mp hef
    exact hpath.mono fun x y hxy => hxy.2

/-- Exact graph-level composition theorem for a facial square. Between any
two edges outside the square, ambient tracked-color reachability is precisely
reachability after contracting exterior components and local square
components. The only structural hypotheses are the computed facial-square
incidence predicate and injectivity of its eight named edges. -/
theorem trackedEdgeGraph_reachable_exterior_iff_contracted
    (Q : @FacialSquareData V E) (hQ : Q.WellFormed RS)
    (hdist : Q.LocalEdgesDistinct)
    (C : E → Color) (a b : Color) (e f : Q.ExteriorEdge) :
    (RS.trackedEdgeGraph C a b).Reachable e f ↔
      (Q.facialSquareContractedGraph RS hdist C a b).Reachable e f := by
  rw [trackedEdgeGraph_eq_exterior_sup_facialSquareLocal RS Q hQ hdist C a b]
  rw [reachable_sup_iff_subtype_componentClosure
    (Q.exteriorTrackedEdgeGraph RS C a b)
    (Q.localTrackedEdgeGraph C a b) (fun e => e ∉ Q.squareEdges)
    e f e.2 f.2 (by
      intro x m y hxm _hmy hExt _hLocal
      have hmSupport : m ∈ (Q.exteriorTrackedEdgeGraph RS C a b).support :=
        SimpleGraph.mem_support_of_reachable hxm.symm hExt.symm
      rcases (SimpleGraph.mem_support _).mp hmSupport with ⟨z, hmz⟩
      exact hmz.2.1)]
  calc
    Relation.ReflTransGen
        (fun x y : Q.ExteriorEdge =>
          (Q.exteriorTrackedEdgeGraph RS C a b).Reachable x y ∨
          (Q.localTrackedEdgeGraph C a b).Reachable x y) e f ↔
      Relation.ReflTransGen (Q.facialSquareComponentStep RS hdist C a b) e f := by
        constructor
        · intro h
          exact h.mono fun x y hxy => by
            rcases hxy with hExt | hLocal
            · exact Or.inr (Or.inl hExt)
            · rcases (Q.localTrackedEdgeGraph_reachable_exterior_iff
                  hdist C a b x y).mp hLocal with heq | hPortal
              · exact Or.inl heq
              · exact Or.inr (Or.inr hPortal)
        · intro h
          exact h.mono fun x y hxy => by
            rcases hxy with rfl | hExt | hPortal
            · exact Or.inl SimpleGraph.Reachable.rfl
            · exact Or.inl hExt
            · exact Or.inr
                ((Q.localTrackedEdgeGraph_reachable_exterior_iff
                  hdist C a b x y).mpr (Or.inr hPortal))
    _ ↔ _ := Q.componentClosure_iff_contractedReachable RS hdist C a b e f

/-- Ambient tracked-color reachability on all non-square edges is computed
by gluing the actual exterior components to the finite square profile. This
is the graph-level extraction needed to apply the compositional square
profile identity. -/
theorem trackedEdgeGraph_reachable_exterior_iff_profileContracted
    (Q : @FacialSquareData V E) (hQ : Q.WellFormed RS)
    (hdist : Q.LocalEdgesDistinct)
    (C : E → Color) (a b : Color)
    (hx : Q.internalColoring C ∈ squareExtensions (Q.boundaryWord C))
    (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ≠ b)
    (e f : Q.ExteriorEdge) :
    (RS.trackedEdgeGraph C a b).Reachable e f ↔
      (Q.facialSquareProfileContractedGraph RS hdist C a b
        (squareTrackedProfile (Q.boundaryWord C) (Q.internalColoring C) a b)
        (squareTrackedProfile_symmetric
          (Q.boundaryWord C) (Q.internalColoring C) a b)).Reachable e f := by
  rw [Q.trackedEdgeGraph_reachable_exterior_iff_contracted RS hQ hdist C a b e f]
  rw [Q.facialSquareContractedGraph_eq_profileContractedGraph RS hdist C a b
    hx ha hb hab]

/-- The computed exterior/local composition profile is the actual ambient
tracked-color profile of a properly colored facial square. -/
theorem ambientTrackedExteriorProfile_eq_composed
    (Q : @FacialSquareData V E) (hQ : Q.WellFormed RS)
    (hdist : Q.LocalEdgesDistinct)
    (C : E → Color) (a b : Color)
    (hx : Q.internalColoring C ∈ squareExtensions (Q.boundaryWord C))
    (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ≠ b) :
    Q.ambientTrackedExteriorProfile RS C a b =
      Q.facialSquareComposedTrackedProfile RS hdist C a b
        (squareTrackedProfile (Q.boundaryWord C) (Q.internalColoring C) a b) := by
  funext e f
  rw [Bool.eq_iff_iff]
  simp only [ambientTrackedExteriorProfile, Bool.and_eq_true, decide_eq_true_eq]
  rw [Q.facialSquareComposedTrackedProfile_eq_true_iff RS hdist C a b
    (squareTrackedProfile (Q.boundaryWord C) (Q.internalColoring C) a b)
    (squareTrackedProfile_symmetric
      (Q.boundaryWord C) (Q.internalColoring C) a b)]
  rw [Q.trackedEdgeGraph_reachable_exterior_iff_profileContracted RS hQ hdist
    C a b hx ha hb hab e f]
  tauto

/-- Tait-coloring form of the graph-level square-profile extraction. The
local extension premise is discharged from cubicity, properness, and the
stored rotation-system incidence data. -/
theorem taitColoring_trackedEdgeGraph_reachable_exterior_iff_profileContracted
    (Q : @FacialSquareData V E) (hQ : Q.WellFormed RS)
    (hdist : Q.LocalEdgesDistinct) (hCubic : RS.IsCubic)
    (C : RS.EdgeColoring Color) (hC : RS.IsTaitEdgeColoring C)
    (a b : Color) (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ≠ b)
    (e f : Q.ExteriorEdge) :
    (RS.trackedEdgeGraph C a b).Reachable e f ↔
      (Q.facialSquareProfileContractedGraph RS hdist C a b
        (squareTrackedProfile (Q.boundaryWord C) (Q.internalColoring C) a b)
        (squareTrackedProfile_symmetric
          (Q.boundaryWord C) (Q.internalColoring C) a b)).Reachable e f := by
  apply Q.trackedEdgeGraph_reachable_exterior_iff_profileContracted RS hQ hdist
    C a b _ ha hb hab e f
  rw [mem_squareExtensions_iff]
  exact RS.facialSquare_internalColoring_isSquareExtension Q hQ hCubic C hC

/-- Profiles produced by composing a fixed rotation-system exterior coloring
with every proper local square extension. -/
noncomputable def facialSquareComposedExtensionProfileMultiset
    (Q : @FacialSquareData V E) (hdist : Q.LocalEdgesDistinct)
    (C : E → Color) (w : SquareBoundaryWord) (a b : Color) :
    Multiset (Q.ExteriorEdge → Q.ExteriorEdge → Bool) :=
  (squareExtensionProfileMultiset w a b).map
    (Q.facialSquareComposedTrackedProfile RS hdist C a b)

/-- Profiles produced by composing the same exterior coloring with one named
planar square-reduction side. -/
noncomputable def facialSquareComposedReductionSideProfileMultiset
    (Q : @FacialSquareData V E) (hdist : Q.LocalEdgesDistinct)
    (C : E → Color) (side : SquareReductionSide)
    (w : SquareBoundaryWord) (a b : Color) :
    Multiset (Q.ExteriorEdge → Q.ExteriorEdge → Bool) :=
  (squareReductionSideProfileMultiset side w a b).map
    (Q.facialSquareComposedTrackedProfile RS hdist C a b)

/-- Rotation-system form of the additive square-profile identity for a fixed
exterior coloring. It preserves the full connectivity profile on every
non-square edge and the multiplicity of local extensions. -/
theorem facialSquareComposedAdditiveProfileMultisetIdentity
    (Q : @FacialSquareData V E) (hdist : Q.LocalEdgesDistinct)
    (C : E → Color) (w : SquareBoundaryWord) (a b : Color)
    (hw : w.Nonzero) (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ≠ b) :
    Q.facialSquareComposedExtensionProfileMultiset RS hdist C w a b =
      Q.facialSquareComposedReductionSideProfileMultiset
        RS hdist C .join01_23 w a b +
      Q.facialSquareComposedReductionSideProfileMultiset
        RS hdist C .join12_30 w a b := by
  unfold facialSquareComposedExtensionProfileMultiset
    facialSquareComposedReductionSideProfileMultiset
  rw [squareLocalProfileIdentity w a b hw ha hb hab]
  rw [squareReductionProfileMultiset_eq_side_sum]
  simp

/-- Per-target count form of the rotation-system additive square-profile
identity. -/
theorem facialSquareComposedAdditiveProfileCountIdentity
    (Q : @FacialSquareData V E) (hdist : Q.LocalEdgesDistinct)
    (C : E → Color) (target : Q.ExteriorEdge → Q.ExteriorEdge → Bool)
    (w : SquareBoundaryWord) (a b : Color)
    (hw : w.Nonzero) (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ≠ b) :
    (Q.facialSquareComposedExtensionProfileMultiset RS hdist C w a b).count target =
      (Q.facialSquareComposedReductionSideProfileMultiset
        RS hdist C .join01_23 w a b).count target +
      (Q.facialSquareComposedReductionSideProfileMultiset
        RS hdist C .join12_30 w a b).count target := by
  rw [Q.facialSquareComposedAdditiveProfileMultisetIdentity RS hdist C w a b
    hw ha hb hab]
  simp

/-- The actual ambient profile of a proper facial-square coloring is one of
the profiles counted on the extension side of the rotation-system identity. -/
theorem ambientTrackedExteriorProfile_mem_composedExtensionProfiles
    (Q : @FacialSquareData V E) (hQ : Q.WellFormed RS)
    (hdist : Q.LocalEdgesDistinct)
    (C : E → Color) (a b : Color)
    (hx : Q.internalColoring C ∈ squareExtensions (Q.boundaryWord C))
    (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ≠ b) :
    Q.ambientTrackedExteriorProfile RS C a b ∈
      Q.facialSquareComposedExtensionProfileMultiset RS hdist C
        (Q.boundaryWord C) a b := by
  rw [Q.ambientTrackedExteriorProfile_eq_composed RS hQ hdist C a b
    hx ha hb hab]
  unfold facialSquareComposedExtensionProfileMultiset squareExtensionProfileMultiset
  apply Multiset.mem_map.mpr
  exact ⟨squareTrackedProfile (Q.boundaryWord C) (Q.internalColoring C) a b,
    Multiset.mem_map.mpr ⟨Q.internalColoring C, by simpa using hx, rfl⟩, rfl⟩

/-- Tait-coloring specialization of the per-target additive count identity.
The boundary word and its nonzero proof are extracted from the graph coloring. -/
theorem taitColoring_facialSquareComposedAdditiveProfileCountIdentity
    (Q : @FacialSquareData V E) (hdist : Q.LocalEdgesDistinct)
    (C : RS.EdgeColoring Color) (hC : RS.IsTaitEdgeColoring C)
    (target : Q.ExteriorEdge → Q.ExteriorEdge → Bool)
    (a b : Color) (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ≠ b) :
    (Q.facialSquareComposedExtensionProfileMultiset RS hdist C
      (Q.boundaryWord C) a b).count target =
      (Q.facialSquareComposedReductionSideProfileMultiset RS hdist C
        .join01_23 (Q.boundaryWord C) a b).count target +
      (Q.facialSquareComposedReductionSideProfileMultiset RS hdist C
        .join12_30 (Q.boundaryWord C) a b).count target := by
  exact Q.facialSquareComposedAdditiveProfileCountIdentity RS hdist C target
    (Q.boundaryWord C) a b (RS.facialSquare_boundaryWord_nonzero Q C hC)
    ha hb hab

end FacialSquareData
end RotationSystem

end Mettapedia.GraphTheory.FourColor
