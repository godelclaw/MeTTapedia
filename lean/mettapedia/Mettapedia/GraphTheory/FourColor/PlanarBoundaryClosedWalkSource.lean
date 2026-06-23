import Mettapedia.GraphTheory.FourColor.PlanarBoundaryClosedWalkSourceCore

namespace Mettapedia.GraphTheory.FourColor

variable {V : Type*} [DecidableEq V]

/-- Graph-level existence form of the explicit closed-walk source attached to the annulus
boundary-reachability interface. -/
def AdmitsPlanarBoundaryClosedWalkAnnulusBoundarySource (G : SimpleGraph V) : Prop :=
  Exists fun emb : PlaneEmbeddingWithBoundary G =>
    Nonempty (PlanarBoundaryClosedWalkAnnulusBoundarySource emb)

/-- Graph-level constructor from the three independent same-embedding fields. This is the exact
existential form of `PlanarBoundaryClosedWalkAnnulusBoundarySource.ofFields`. -/
theorem admitsPlanarBoundaryClosedWalkAnnulusBoundarySource_of_exists_fields
    {G : SimpleGraph V}
    (hG : Exists fun emb : PlaneEmbeddingWithBoundary G =>
      Exists fun _ : PlanarBoundaryAnnulusBoundaryReachabilityData emb =>
        Exists fun closedWalks : PlanarBoundaryClosedWalkEmbeddingData emb =>
          (f : AmbientFace emb.faces) ->
            (closedWalks.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) :
    AdmitsPlanarBoundaryClosedWalkAnnulusBoundarySource G := by
  cases hG with
  | intro emb hfields =>
      cases hfields with
      | intro boundaryReachability hclosed =>
          cases hclosed with
          | intro closedWalks selectedBoundaryArc =>
              exact Exists.intro emb <|
                Nonempty.intro <|
                  PlanarBoundaryClosedWalkAnnulusBoundarySource.ofFields
                    boundaryReachability closedWalks selectedBoundaryArc

/-- Graph-level constructor from same-embedding boundary reachability, successor facial dart
cycles, and selected-boundary arc contiguity on the induced closed-walk boundary runs. -/
theorem
    admitsPlanarBoundaryClosedWalkAnnulusBoundarySource_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc
    {G : SimpleGraph V}
    (hG : Exists fun emb : PlaneEmbeddingWithBoundary G =>
      Exists fun _ : PlanarBoundaryAnnulusBoundaryReachabilityData emb =>
        Exists fun dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb =>
          (f : AmbientFace emb.faces) ->
            (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
              |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) :
    AdmitsPlanarBoundaryClosedWalkAnnulusBoundarySource G := by
  cases hG with
  | intro emb hfields =>
      cases hfields with
      | intro boundaryReachability hdarts =>
          cases hdarts with
          | intro dartCycles selectedBoundaryArc =>
              exact Exists.intro emb <|
                Nonempty.intro <|
                  PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
                    boundaryReachability dartCycles selectedBoundaryArc

/-- Generic same-embedding failed-converse principle for the honest closed-walk annulus source.
Any explicit source embedding missing a source-indexed target refutes a universal theorem from
that source package to the target. -/
theorem not_forall_target_of_exists_embedding_closedWalkAnnulusBoundarySource_without_target
    {G : SimpleGraph V}
    (Target : (emb : PlaneEmbeddingWithBoundary G) →
      PlanarBoundaryClosedWalkAnnulusBoundarySource emb → Prop)
    (hWitness :
      ∃ emb : PlaneEmbeddingWithBoundary G,
        ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
          ¬ Target emb source) :
    ¬ ∀ emb : PlaneEmbeddingWithBoundary G,
        ∀ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
          Target emb source := by
  intro h
  rcases hWitness with ⟨emb, source, hno⟩
  exact hno (h emb source)

/-- Generic same-embedding failed-converse principle for the successor-dart source fields used by
the route-facing positive wrappers. Any explicit embedding with boundary reachability,
successor-cycle facial data, selected-boundary arc contiguity, and a missing embedding-indexed
target refutes a universal theorem from those source fields to the target. -/
theorem
    not_forall_target_of_exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_without_target
    {G : SimpleGraph V}
    (Target : PlaneEmbeddingWithBoundary G → Prop)
    (hWitness :
      ∃ emb : PlaneEmbeddingWithBoundary G,
        ∃ _boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
        ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
          (∀ f : AmbientFace emb.faces,
            (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
              |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
            ¬ Target emb) :
    ¬ ∀ emb : PlaneEmbeddingWithBoundary G,
        ∀ _boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
        ∀ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
          (∀ f : AmbientFace emb.faces,
            (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
              |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) →
          Target emb := by
  intro h
  rcases hWitness with ⟨emb, boundaryData, dartCycles, hArc, hno⟩
  exact hno (h emb boundaryData dartCycles hArc)

/-- On a fixed embedding, the bundled source package is exactly the three independent fields.
-/
theorem nonempty_planarBoundaryClosedWalkAnnulusBoundarySource_iff_exists_fields
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G} :
    Nonempty (PlanarBoundaryClosedWalkAnnulusBoundarySource emb) <->
      Exists fun _ : PlanarBoundaryAnnulusBoundaryReachabilityData emb =>
        Exists fun closedWalks : PlanarBoundaryClosedWalkEmbeddingData emb =>
          (f : AmbientFace emb.faces) ->
            (closedWalks.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f := by
  constructor
  · intro hsource
    cases hsource with
    | intro source =>
        exact Exists.intro source.boundaryReachability <|
          Exists.intro source.closedWalks source.selectedBoundaryArc
  · intro hfields
    cases hfields with
    | intro boundaryReachability hclosed =>
        cases hclosed with
        | intro closedWalks selectedBoundaryArc =>
            exact Nonempty.intro <|
              PlanarBoundaryClosedWalkAnnulusBoundarySource.ofFields
                boundaryReachability closedWalks selectedBoundaryArc

/-- On a fixed embedding, the honest closed-walk annulus source already contains the stronger
cyclic ordered face-arc shell. -/
theorem
    nonempty_planarBoundaryCyclicOrderedFaceArcEmbeddingData_of_nonempty_planarBoundaryClosedWalkAnnulusBoundarySource
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (hsource : Nonempty (PlanarBoundaryClosedWalkAnnulusBoundarySource emb)) :
    Nonempty (PlanarBoundaryCyclicOrderedFaceArcEmbeddingData emb) := by
  rcases hsource with ⟨source⟩
  exact ⟨source.toPlanarBoundaryCyclicOrderedFaceArcEmbeddingData⟩

/-- On a fixed embedding, the honest closed-walk annulus source also contains the weaker bundled
selected-boundary arc shell. -/
theorem
    nonempty_planarBoundarySelectedBoundaryArcGeometry_of_nonempty_planarBoundaryClosedWalkAnnulusBoundarySource
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (hsource : Nonempty (PlanarBoundaryClosedWalkAnnulusBoundarySource emb)) :
    Nonempty (PlanarBoundarySelectedBoundaryArcGeometry emb) := by
  rcases hsource with ⟨source⟩
  exact ⟨source.toPlanarBoundarySelectedBoundaryArcGeometry⟩

/-- Graph-level exactness of the source package against its independent same-embedding fields. -/
theorem admitsPlanarBoundaryClosedWalkAnnulusBoundarySource_iff_exists_fields
    {G : SimpleGraph V} :
    AdmitsPlanarBoundaryClosedWalkAnnulusBoundarySource G <->
      Exists fun emb : PlaneEmbeddingWithBoundary G =>
        Exists fun _ : PlanarBoundaryAnnulusBoundaryReachabilityData emb =>
          Exists fun closedWalks : PlanarBoundaryClosedWalkEmbeddingData emb =>
            (f : AmbientFace emb.faces) ->
              (closedWalks.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f := by
  constructor
  · intro hsource
    cases hsource with
    | intro emb hnonempty =>
        exact Exists.intro emb <|
          (nonempty_planarBoundaryClosedWalkAnnulusBoundarySource_iff_exists_fields).1
            hnonempty
  · intro hfields
    exact admitsPlanarBoundaryClosedWalkAnnulusBoundarySource_of_exists_fields hfields

/-- The explicit annulus boundary source retains the strengthened facial closed-walk field as a
graph-level source, rather than reconstructing it from cyclic selected-boundary data. -/
theorem
    admitsPlanarBoundaryClosedWalkEmbeddingData_of_admitsPlanarBoundaryClosedWalkAnnulusBoundarySource
    {G : SimpleGraph V}
    (hG : AdmitsPlanarBoundaryClosedWalkAnnulusBoundarySource G) :
    AdmitsPlanarBoundaryClosedWalkEmbeddingData G := by
  cases hG with
  | intro emb hsource =>
      cases hsource with
      | intro source =>
          exact Exists.intro emb (Nonempty.intro source.toPlanarBoundaryClosedWalkEmbeddingData)

/-- On a fixed embedding, the explicit closed-walk annulus-boundary source is impossible on an
acyclic graph with at least one edge, because its `closedWalks` field already gives the honest
facial closed-walk interface. -/
theorem not_nonempty_planarBoundaryClosedWalkAnnulusBoundarySource_of_isAcyclic_of_nonempty_edgeSet
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G} (hAcyc : G.IsAcyclic)
    (hE : Nonempty G.edgeSet) :
    ¬ Nonempty (PlanarBoundaryClosedWalkAnnulusBoundarySource emb) := by
  intro hsource
  rcases hsource with ⟨source⟩
  exact
    not_nonempty_planarBoundaryClosedWalkEmbeddingData_of_isAcyclic_of_nonempty_edgeSet hAcyc hE
      ⟨source.closedWalks⟩

/-- Consequently, the explicit closed-walk annulus-boundary source is impossible at graph level on
an acyclic graph with at least one edge. -/
theorem not_admitsPlanarBoundaryClosedWalkAnnulusBoundarySource_of_isAcyclic_of_nonempty_edgeSet
    {G : SimpleGraph V} (hAcyc : G.IsAcyclic) (hE : Nonempty G.edgeSet) :
    ¬ AdmitsPlanarBoundaryClosedWalkAnnulusBoundarySource G := by
  intro hsource
  exact
    not_admitsPlanarBoundaryClosedWalkEmbeddingData_of_isAcyclic_of_nonempty_edgeSet hAcyc hE
      (admitsPlanarBoundaryClosedWalkEmbeddingData_of_admitsPlanarBoundaryClosedWalkAnnulusBoundarySource
        hsource)

/-- Any explicit acyclic positive-edge witness carrying a graph-level property `P` refutes a
generic derivation theorem from `P` to the honest closed-walk annulus-boundary source. -/
theorem not_forall_admitsPlanarBoundaryClosedWalkAnnulusBoundarySource_of_exists_isAcyclic_of_nonempty_edgeSet_and_property
    (P : SimpleGraph V → Prop)
    (hWitness : ∃ G : SimpleGraph V, G.IsAcyclic ∧ Nonempty G.edgeSet ∧ P G) :
    ¬ ∀ G : SimpleGraph V, P G → AdmitsPlanarBoundaryClosedWalkAnnulusBoundarySource G := by
  intro h
  rcases hWitness with ⟨G, hAcyc, hE, hP⟩
  exact
    not_admitsPlanarBoundaryClosedWalkAnnulusBoundarySource_of_isAcyclic_of_nonempty_edgeSet
      hAcyc hE (h G hP)

/-- The same explicit source lowers to the split closed-walk-plus-selected-arc interface used by
the selected-boundary route. -/
theorem
    admitsPlanarBoundaryClosedWalkEmbeddingDataAndSelectedBoundaryArcOnFace_of_admitsPlanarBoundaryClosedWalkAnnulusBoundarySource
    {G : SimpleGraph V}
    (hG : AdmitsPlanarBoundaryClosedWalkAnnulusBoundarySource G) :
    AdmitsPlanarBoundaryClosedWalkEmbeddingDataAndSelectedBoundaryArcOnFace G := by
  cases hG with
  | intro emb hsource =>
      cases hsource with
      | intro source =>
          exact Exists.intro emb (Exists.intro source.closedWalks source.selectedBoundaryArc)

/-- The explicit source retains the concrete shared-endpoint annulus-boundary reachability
witness, not only the abstract outer/inner boundary partition extracted from it. -/
theorem
    admitsPlanarBoundaryAnnulusBoundaryReachabilityData_of_admitsPlanarBoundaryClosedWalkAnnulusBoundarySource
    {G : SimpleGraph V}
    (hG : AdmitsPlanarBoundaryClosedWalkAnnulusBoundarySource G) :
    AdmitsPlanarBoundaryAnnulusBoundaryReachabilityData G := by
  cases hG with
  | intro emb hsource =>
      cases hsource with
      | intro source =>
          exact Exists.intro emb (Nonempty.intro source.boundaryReachability)

/-- The explicit closed-walk annulus source lowers directly to the weaker cyclic ordered
face-arc shell on the same embedding. -/
theorem
    admitsPlanarBoundaryCyclicOrderedFaceArcEmbeddingData_of_admitsPlanarBoundaryClosedWalkAnnulusBoundarySource
    {G : SimpleGraph V}
    (hG : AdmitsPlanarBoundaryClosedWalkAnnulusBoundarySource G) :
    AdmitsPlanarBoundaryCyclicOrderedFaceArcEmbeddingData G := by
  cases hG with
  | intro emb hsource =>
      cases hsource with
      | intro source =>
          exact Exists.intro emb
            (Nonempty.intro source.toPlanarBoundaryCyclicOrderedFaceArcEmbeddingData)

/-- Consequently, the explicit closed-walk annulus source also lowers to the split
face-boundary-run plus selected-boundary-arc interface. -/
theorem
    admitsPlanarBoundaryFaceBoundaryRunGeometryAndSelectedBoundaryArcOnFace_of_admitsPlanarBoundaryClosedWalkAnnulusBoundarySource
    {G : SimpleGraph V}
    (hG : AdmitsPlanarBoundaryClosedWalkAnnulusBoundarySource G) :
    AdmitsPlanarBoundaryFaceBoundaryRunGeometryAndSelectedBoundaryArcOnFace G := by
  cases hG with
  | intro emb hsource =>
      cases hsource with
      | intro source =>
          exact Exists.intro emb <|
            Exists.intro source.closedWalks.toPlanarBoundaryFaceBoundaryRunGeometry
              source.selectedBoundaryArc

/-- Consequently, the explicit closed-walk annulus source also lowers to the still weaker
selected-boundary arc shell. -/
theorem
    admitsPlanarBoundarySelectedBoundaryArcGeometry_of_admitsPlanarBoundaryClosedWalkAnnulusBoundarySource
    {G : SimpleGraph V}
    (hG : AdmitsPlanarBoundaryClosedWalkAnnulusBoundarySource G) :
    AdmitsPlanarBoundarySelectedBoundaryArcGeometry G := by
  cases hG with
  | intro emb hsource =>
      cases hsource with
      | intro source =>
          exact Exists.intro emb
            (Nonempty.intro source.toPlanarBoundarySelectedBoundaryArcGeometry)

/-- The explicit closed-walk source also feeds the existing abstract annulus-boundary split. -/
theorem
    admitsPlanarBoundaryAnnulusBoundaryData_of_admitsPlanarBoundaryClosedWalkAnnulusBoundarySource
    {G : SimpleGraph V}
    (hG : AdmitsPlanarBoundaryClosedWalkAnnulusBoundarySource G) :
    AdmitsPlanarBoundaryAnnulusBoundaryData G := by
  cases hG with
  | intro emb hsource =>
      cases hsource with
      | intro source =>
          exact Exists.intro emb (Nonempty.intro source.toPlanarBoundaryAnnulusBoundaryData)

/-- Under the current boundary API, the honest closed-walk annulus source already reaches the
pure annulus decomposition surface: the source supplies the annulus boundary split, and that split
admits a canonical one-collar decomposition with all ambient faces in the unique collar. -/
theorem
    admitsPlanarBoundaryAnnulusDecomposition_of_admitsPlanarBoundaryClosedWalkAnnulusBoundarySource
    {G : SimpleGraph V}
    (hG : AdmitsPlanarBoundaryClosedWalkAnnulusBoundarySource G) :
    AdmitsPlanarBoundaryAnnulusDecomposition G := by
  exact
    admitsPlanarBoundaryAnnulusDecomposition_of_admitsPlanarBoundaryAnnulusBoundaryData
      (admitsPlanarBoundaryAnnulusBoundaryData_of_admitsPlanarBoundaryClosedWalkAnnulusBoundarySource
        hG)

/-- Combined lowering to the concrete shared-endpoint annulus witness and the weaker cyclic
face-arc shell. This exposes the exact positive route surface that the double-star regression
shows is still insufficient to force the honest closed-walk annulus source. -/
theorem
    admitsPlanarBoundaryAnnulusBoundaryReachabilityData_and_cyclicOrderedFaceArcEmbeddingData_of_admitsPlanarBoundaryClosedWalkAnnulusBoundarySource
    {G : SimpleGraph V}
    (hG : AdmitsPlanarBoundaryClosedWalkAnnulusBoundarySource G) :
    And (AdmitsPlanarBoundaryAnnulusBoundaryReachabilityData G)
      (AdmitsPlanarBoundaryCyclicOrderedFaceArcEmbeddingData G) := by
  exact And.intro
    (admitsPlanarBoundaryAnnulusBoundaryReachabilityData_of_admitsPlanarBoundaryClosedWalkAnnulusBoundarySource
      hG)
    (admitsPlanarBoundaryCyclicOrderedFaceArcEmbeddingData_of_admitsPlanarBoundaryClosedWalkAnnulusBoundarySource
      hG)

/-- Combined lowering to the concrete shared-endpoint annulus witness and the weaker bundled
selected-boundary arc shell. -/
theorem
    admitsPlanarBoundaryAnnulusBoundaryReachabilityData_and_selectedBoundaryArcGeometry_of_admitsPlanarBoundaryClosedWalkAnnulusBoundarySource
    {G : SimpleGraph V}
    (hG : AdmitsPlanarBoundaryClosedWalkAnnulusBoundarySource G) :
    And (AdmitsPlanarBoundaryAnnulusBoundaryReachabilityData G)
      (AdmitsPlanarBoundarySelectedBoundaryArcGeometry G) := by
  exact And.intro
    (admitsPlanarBoundaryAnnulusBoundaryReachabilityData_of_admitsPlanarBoundaryClosedWalkAnnulusBoundarySource
      hG)
    (admitsPlanarBoundarySelectedBoundaryArcGeometry_of_admitsPlanarBoundaryClosedWalkAnnulusBoundarySource
      hG)

/-- On any acyclic graph with at least one edge, the paired annulus-rooted shell
`boundary reachability + cyclic ordered face arcs` is still strictly weaker than the honest
closed-walk annulus source. This packages the generic graph-level separation independently of any
particular witness graph. -/
theorem
    admitsPlanarBoundaryAnnulusBoundaryReachabilityData_and_cyclicOrderedFaceArcEmbeddingData_withoutClosedWalkAnnulusBoundarySource_of_isAcyclic_of_nonempty_edgeSet
    {G : SimpleGraph V} (hAcyc : G.IsAcyclic) (hE : Nonempty G.edgeSet)
    (hG : And (AdmitsPlanarBoundaryAnnulusBoundaryReachabilityData G)
      (AdmitsPlanarBoundaryCyclicOrderedFaceArcEmbeddingData G)) :
    And (AdmitsPlanarBoundaryAnnulusBoundaryReachabilityData G)
      (AdmitsPlanarBoundaryCyclicOrderedFaceArcEmbeddingData G) ∧
        ¬ AdmitsPlanarBoundaryClosedWalkAnnulusBoundarySource G := by
  exact ⟨hG,
    not_admitsPlanarBoundaryClosedWalkAnnulusBoundarySource_of_isAcyclic_of_nonempty_edgeSet
      hAcyc hE⟩

/-- Likewise, on any acyclic graph with at least one edge, the paired annulus-rooted shell
`boundary reachability + selected-boundary arc geometry` does not force the honest closed-walk
annulus source. -/
theorem
    admitsPlanarBoundaryAnnulusBoundaryReachabilityData_and_selectedBoundaryArcGeometry_withoutClosedWalkAnnulusBoundarySource_of_isAcyclic_of_nonempty_edgeSet
    {G : SimpleGraph V} (hAcyc : G.IsAcyclic) (hE : Nonempty G.edgeSet)
    (hG : And (AdmitsPlanarBoundaryAnnulusBoundaryReachabilityData G)
      (AdmitsPlanarBoundarySelectedBoundaryArcGeometry G)) :
    And (AdmitsPlanarBoundaryAnnulusBoundaryReachabilityData G)
      (AdmitsPlanarBoundarySelectedBoundaryArcGeometry G) ∧
        ¬ AdmitsPlanarBoundaryClosedWalkAnnulusBoundarySource G := by
  exact ⟨hG,
    not_admitsPlanarBoundaryClosedWalkAnnulusBoundarySource_of_isAcyclic_of_nonempty_edgeSet
      hAcyc hE⟩

/-- Therefore, any explicit acyclic positive-edge witness carrying the paired shell
`boundary reachability + cyclic ordered face arcs` refutes a generic derivation theorem to the
honest closed-walk annulus source. -/
theorem
    not_forall_admitsPlanarBoundaryClosedWalkAnnulusBoundarySource_of_exists_isAcyclic_of_nonempty_edgeSet_and_admitsPlanarBoundaryAnnulusBoundaryReachabilityData_and_cyclicOrderedFaceArcEmbeddingData
    (hWitness : ∃ G : SimpleGraph V,
      G.IsAcyclic ∧ Nonempty G.edgeSet ∧
        And (AdmitsPlanarBoundaryAnnulusBoundaryReachabilityData G)
          (AdmitsPlanarBoundaryCyclicOrderedFaceArcEmbeddingData G)) :
    ¬ ∀ G : SimpleGraph V,
        And (AdmitsPlanarBoundaryAnnulusBoundaryReachabilityData G)
          (AdmitsPlanarBoundaryCyclicOrderedFaceArcEmbeddingData G) →
            AdmitsPlanarBoundaryClosedWalkAnnulusBoundarySource G := by
  intro h
  rcases hWitness with ⟨G, hAcyc, hE, hG⟩
  exact
    not_admitsPlanarBoundaryClosedWalkAnnulusBoundarySource_of_isAcyclic_of_nonempty_edgeSet
      hAcyc hE
      (h G hG)

/-- The same abstract failed-converse criterion for the weaker paired shell
`boundary reachability + selected-boundary arc geometry`. -/
theorem
    not_forall_admitsPlanarBoundaryClosedWalkAnnulusBoundarySource_of_exists_isAcyclic_of_nonempty_edgeSet_and_admitsPlanarBoundaryAnnulusBoundaryReachabilityData_and_selectedBoundaryArcGeometry
    (hWitness : ∃ G : SimpleGraph V,
      G.IsAcyclic ∧ Nonempty G.edgeSet ∧
        And (AdmitsPlanarBoundaryAnnulusBoundaryReachabilityData G)
          (AdmitsPlanarBoundarySelectedBoundaryArcGeometry G)) :
    ¬ ∀ G : SimpleGraph V,
        And (AdmitsPlanarBoundaryAnnulusBoundaryReachabilityData G)
          (AdmitsPlanarBoundarySelectedBoundaryArcGeometry G) →
            AdmitsPlanarBoundaryClosedWalkAnnulusBoundarySource G := by
  intro h
  rcases hWitness with ⟨G, hAcyc, hE, hG⟩
  exact
    not_admitsPlanarBoundaryClosedWalkAnnulusBoundarySource_of_isAcyclic_of_nonempty_edgeSet
      hAcyc hE
      (h G hG)

/-- Combined route-facing lowering: the annulus boundary split is available while the honest
closed-walk source remains an explicit graph-level obligation. -/
theorem
    admitsPlanarBoundaryAnnulusBoundaryData_and_closedWalkEmbeddingData_of_admitsPlanarBoundaryClosedWalkAnnulusBoundarySource
    {G : SimpleGraph V}
    (hG : AdmitsPlanarBoundaryClosedWalkAnnulusBoundarySource G) :
    And (AdmitsPlanarBoundaryAnnulusBoundaryData G)
      (AdmitsPlanarBoundaryClosedWalkEmbeddingData G) := by
  exact And.intro
    (admitsPlanarBoundaryAnnulusBoundaryData_of_admitsPlanarBoundaryClosedWalkAnnulusBoundarySource
      hG)
    (admitsPlanarBoundaryClosedWalkEmbeddingData_of_admitsPlanarBoundaryClosedWalkAnnulusBoundarySource
      hG)

end Mettapedia.GraphTheory.FourColor
