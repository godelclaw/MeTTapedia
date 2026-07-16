import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairKempeFusionChiralMonodromy
import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairInsertion

namespace SimpleGraph.Hom

variable {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}

/-- An injective graph homomorphism is injective on oriented darts. -/
theorem mapDart_injective_of_injective (f : G →g H)
    (hinjective : Function.Injective f) :
    Function.Injective f.mapDart := by
  intro first second heq
  apply SimpleGraph.Dart.ext
  apply Prod.ext
  · apply hinjective
    exact congrArg (fun dart ↦ dart.fst) heq
  · apply hinjective
    exact congrArg (fun dart ↦ dart.snd) heq

/-- Mapping a reversed dart reverses the mapped dart. -/
theorem mapDart_symm (f : G →g H) (dart : G.Dart) :
    f.mapDart dart.symm = (f.mapDart dart).symm := by
  apply SimpleGraph.Dart.ext
  rfl

end SimpleGraph.Hom

namespace Mettapedia.GraphTheory.FourColor

open SimpleGraph
open GoertzelV24AdjacentPairBoundary
open GoertzelV24FourDefectBoundary

namespace GoertzelV24FourDefectBoundary.DegreeTwoBoundaryData

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance fusionDartGraphEdgeSetDecidableEq : DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

/-- The shared primal edge oriented according to its `(a,b)` route
traversal. -/
def EvenKempeFusionLens.bFusionDart {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hab : a ≠ b) (site : lens.FusionSite) : G.Dart :=
  ⟨(lens.bEntryVertex hab site, lens.bExitVertex hab site), by
    rw [← SimpleGraph.mem_edgeSet,
      ← lens.fusionEdge_eq_bEntry_bExit hab site]
    exact site.1.2⟩

/-- The shared primal edge oriented according to its `(a,c)` route
traversal. -/
def EvenKempeFusionLens.cFusionDart {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hac : a ≠ c) (site : lens.FusionSite) : G.Dart :=
  ⟨(lens.cEntryVertex hac site, lens.cExitVertex hac site), by
    rw [← SimpleGraph.mem_edgeSet,
      ← lens.fusionEdge_eq_cEntry_cExit hac site]
    exact site.1.2⟩

@[simp] theorem EvenKempeFusionLens.bFusionDart_fst {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hab : a ≠ b) (site : lens.FusionSite) :
    (lens.bFusionDart hab site).fst = lens.bEntryVertex hab site :=
  rfl

@[simp] theorem EvenKempeFusionLens.bFusionDart_snd {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hab : a ≠ b) (site : lens.FusionSite) :
    (lens.bFusionDart hab site).snd = lens.bExitVertex hab site :=
  rfl

@[simp] theorem EvenKempeFusionLens.cFusionDart_fst {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hac : a ≠ c) (site : lens.FusionSite) :
    (lens.cFusionDart hac site).fst = lens.cEntryVertex hac site :=
  rfl

@[simp] theorem EvenKempeFusionLens.cFusionDart_snd {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hac : a ≠ c) (site : lens.FusionSite) :
    (lens.cFusionDart hac site).snd = lens.cExitVertex hac site :=
  rfl

@[simp] theorem EvenKempeFusionLens.bFusionDart_edge {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hab : a ≠ b) (site : lens.FusionSite) :
    (lens.bFusionDart hab site).edge = site.1.1 := by
  change s(lens.bEntryVertex hab site, lens.bExitVertex hab site) = site.1.1
  exact (lens.fusionEdge_eq_bEntry_bExit hab site).symm

@[simp] theorem EvenKempeFusionLens.cFusionDart_edge {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hac : a ≠ c) (site : lens.FusionSite) :
    (lens.cFusionDart hac site).edge = site.1.1 := by
  change s(lens.cEntryVertex hac site, lens.cExitVertex hac site) = site.1.1
  exact (lens.fusionEdge_eq_cEntry_cExit hac site).symm

/-- The two route orientations of a fusion edge agree exactly in the
positive local-chirality state. -/
theorem EvenKempeFusionLens.fusionChirality_eq_true_iff_cFusionDart_eq_bFusionDart
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hab : a ≠ b) (hac : a ≠ c) (site : lens.FusionSite) :
    lens.fusionChirality hab hac site = true ↔
      lens.cFusionDart hac site = lens.bFusionDart hab site := by
  rw [lens.fusionChirality_eq_true_iff_endpoints_agree]
  constructor
  · intro hagree
    apply SimpleGraph.Dart.ext
    exact Prod.ext hagree.1 hagree.2
  · intro hdarts
    exact ⟨congrArg (fun dart ↦ dart.fst) hdarts,
      congrArg (fun dart ↦ dart.snd) hdarts⟩

/-- The two route orientations of a fusion edge are reversals exactly in
the negative local-chirality state. -/
theorem EvenKempeFusionLens.fusionChirality_eq_false_iff_cFusionDart_eq_bFusionDart_symm
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hab : a ≠ b) (hac : a ≠ c) (site : lens.FusionSite) :
    lens.fusionChirality hab hac site = false ↔
      lens.cFusionDart hac site = (lens.bFusionDart hab site).symm := by
  rw [lens.fusionChirality_eq_false_iff_endpoints_reverse]
  constructor
  · intro hreverse
    apply SimpleGraph.Dart.ext
    exact Prod.ext hreverse.1 hreverse.2
  · intro hdarts
    exact ⟨congrArg (fun dart ↦ dart.fst) hdarts,
      congrArg (fun dart ↦ dart.snd) hdarts⟩

/-- Independently of the Boolean presentation, the two oriented fusion
darts agree directly or after reversal. -/
theorem EvenKempeFusionLens.cFusionDart_eq_or_eq_bFusionDart_symm
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hab : a ≠ b) (hac : a ≠ c) (site : lens.FusionSite) :
    lens.cFusionDart hac site = lens.bFusionDart hab site ∨
      lens.cFusionDart hac site = (lens.bFusionDart hab site).symm := by
  exact (SimpleGraph.dart_edge_eq_iff
    (lens.cFusionDart hac site) (lens.bFusionDart hab site)).1 (by simp)

end

end GoertzelV24FourDefectBoundary.DegreeTwoBoundaryData

namespace GoertzelV24AdjacentPairInsertion.AdjacentPairData

open GoertzelV24FourDefectBoundary.DegreeTwoBoundaryData

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance ambientFusionDartGraphEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

local instance ambientFusionDartRetainedVertexFintype
    (first second : V) :
    Fintype (retainedVertexSet first second) :=
  Subtype.fintype _

local instance ambientFusionDartRetainedVertexDecidableEq
    (first second : V) :
    DecidableEq (retainedVertexSet first second) :=
  Subtype.instDecidableEq

/-- Lift a dart of the adjacent-pair deletion into the ambient graph. -/
def retainedDartToAmbientDart (data : AdjacentPairData G)
    (dart : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).Dart) : G.Dart :=
  (retainedGraphEmbedding data).toHom.mapDart dart

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
@[simp] theorem retainedDartToAmbientDart_fst
    (data : AdjacentPairData G)
    (dart : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).Dart) :
    (retainedDartToAmbientDart data dart).fst = dart.fst.1 :=
  rfl

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
@[simp] theorem retainedDartToAmbientDart_snd
    (data : AdjacentPairData G)
    (dart : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).Dart) :
    (retainedDartToAmbientDart data dart).snd = dart.snd.1 :=
  rfl

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem retainedDartToAmbientDart_injective
    (data : AdjacentPairData G) :
    Function.Injective (retainedDartToAmbientDart data) := by
  exact SimpleGraph.Hom.mapDart_injective_of_injective
    (retainedGraphEmbedding data).toHom
    (retainedGraphEmbedding data).injective

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
@[simp] theorem retainedDartToAmbientDart_symm
    (data : AdjacentPairData G)
    (dart : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).Dart) :
    retainedDartToAmbientDart data dart.symm =
      (retainedDartToAmbientDart data dart).symm :=
  SimpleGraph.Hom.mapDart_symm (retainedGraphEmbedding data).toHom dart

/-- The `(a,b)`-oriented fusion edge lifted to the ambient graph. -/
def ambientBFusionDart (data : AdjacentPairData G)
    {C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color}
    {a b c : Color} {left right : Fin 4}
    (lens : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c left right)
    (hab : a ≠ b) (site : lens.FusionSite) : G.Dart :=
  retainedDartToAmbientDart data (lens.bFusionDart hab site)

/-- The `(a,c)`-oriented fusion edge lifted to the ambient graph. -/
def ambientCFusionDart (data : AdjacentPairData G)
    {C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color}
    {a b c : Color} {left right : Fin 4}
    (lens : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c left right)
    (hac : a ≠ c) (site : lens.FusionSite) : G.Dart :=
  retainedDartToAmbientDart data (lens.cFusionDart hac site)

@[simp] theorem ambientBFusionDart_edge
    (data : AdjacentPairData G)
    {C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color}
    {a b c : Color} {left right : Fin 4}
    (lens : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c left right)
    (hab : a ≠ b) (site : lens.FusionSite) :
    (ambientBFusionDart data lens hab site).edge =
      (retainedEdgeToAmbientEdge data site.1).1 := by
  change s((lens.bEntryVertex hab site).1,
      (lens.bExitVertex hab site).1) = site.1.1.map Subtype.val
  rw [lens.fusionEdge_eq_bEntry_bExit hab site]
  rfl

@[simp] theorem ambientCFusionDart_edge
    (data : AdjacentPairData G)
    {C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color}
    {a b c : Color} {left right : Fin 4}
    (lens : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c left right)
    (hac : a ≠ c) (site : lens.FusionSite) :
    (ambientCFusionDart data lens hac site).edge =
      (retainedEdgeToAmbientEdge data site.1).1 := by
  change s((lens.cEntryVertex hac site).1,
      (lens.cExitVertex hac site).1) = site.1.1.map Subtype.val
  rw [lens.fusionEdge_eq_cEntry_cExit hac site]
  rfl

/-- Local chirality is unchanged by lifting the two oriented fusion darts
to the ambient graph. -/
theorem fusionChirality_eq_true_iff_ambientCFusionDart_eq_ambientBFusionDart
    (data : AdjacentPairData G)
    {C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color}
    {a b c : Color} {left right : Fin 4}
    (lens : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c left right)
    (hab : a ≠ b) (hac : a ≠ c) (site : lens.FusionSite) :
    lens.fusionChirality hab hac site = true ↔
      ambientCFusionDart data lens hac site =
        ambientBFusionDart data lens hab site := by
  rw [lens.fusionChirality_eq_true_iff_cFusionDart_eq_bFusionDart]
  exact ⟨fun heq ↦ congrArg (retainedDartToAmbientDart data) heq,
    fun heq ↦ retainedDartToAmbientDart_injective data heq⟩

/-- Negative local chirality is likewise exactly ambient dart reversal. -/
theorem fusionChirality_eq_false_iff_ambientCFusionDart_eq_ambientBFusionDart_symm
    (data : AdjacentPairData G)
    {C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color}
    {a b c : Color} {left right : Fin 4}
    (lens : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c left right)
    (hab : a ≠ b) (hac : a ≠ c) (site : lens.FusionSite) :
    lens.fusionChirality hab hac site = false ↔
      ambientCFusionDart data lens hac site =
        (ambientBFusionDart data lens hab site).symm := by
  rw [lens.fusionChirality_eq_false_iff_cFusionDart_eq_bFusionDart_symm]
  constructor
  · intro heq
    change retainedDartToAmbientDart data (lens.cFusionDart hac site) = _
    rw [heq, retainedDartToAmbientDart_symm]
    rfl
  · intro heq
    apply retainedDartToAmbientDart_injective data
    rw [retainedDartToAmbientDart_symm]
    exact heq

/-- The ambient fusion dart carries exactly the ambient edge identifier
obtained from the retained fusion site. -/
theorem toRotationSystem_edgeOf_ambientBFusionDart
    (graphData : SimpleGraphDartRotation.Data G)
    (data : AdjacentPairData G)
    {C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color}
    {a b c : Color} {left right : Fin 4}
    (lens : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c left right)
    (hab : a ≠ b) (site : lens.FusionSite) :
    graphData.toRotationSystem.edgeOf
        (ambientBFusionDart data lens hab site) =
      retainedEdgeToAmbientEdge data site.1 := by
  apply Subtype.ext
  exact ambientBFusionDart_edge data lens hab site

theorem toRotationSystem_edgeOf_ambientCFusionDart
    (graphData : SimpleGraphDartRotation.Data G)
    (data : AdjacentPairData G)
    {C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color}
    {a b c : Color} {left right : Fin 4}
    (lens : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c left right)
    (hac : a ≠ c) (site : lens.FusionSite) :
    graphData.toRotationSystem.edgeOf
        (ambientCFusionDart data lens hac site) =
      retainedEdgeToAmbientEdge data site.1 := by
  apply Subtype.ext
  exact ambientCFusionDart_edge data lens hac site

/-- Negative local chirality is rotation-system edge reversal after the
canonical ambient lift. -/
theorem fusionChirality_eq_false_iff_ambientCFusionDart_eq_alpha
    (graphData : SimpleGraphDartRotation.Data G)
    (data : AdjacentPairData G)
    {C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color}
    {a b c : Color} {left right : Fin 4}
    (lens : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c left right)
    (hab : a ≠ b) (hac : a ≠ c) (site : lens.FusionSite) :
    lens.fusionChirality hab hac site = false ↔
      ambientCFusionDart data lens hac site =
        graphData.toRotationSystem.alpha
          (ambientBFusionDart data lens hab site) := by
  simpa using
    (fusionChirality_eq_false_iff_ambientCFusionDart_eq_ambientBFusionDart_symm
      data lens hab hac site)

end

end GoertzelV24AdjacentPairInsertion.AdjacentPairData

end Mettapedia.GraphTheory.FourColor
