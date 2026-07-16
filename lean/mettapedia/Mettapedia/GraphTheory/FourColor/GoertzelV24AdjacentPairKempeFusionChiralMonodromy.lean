import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairKempeFusionOrientation

namespace Mettapedia.GraphTheory.FourColor

open SimpleGraph
open GoertzelV24FourDefectBoundary

namespace GoertzelV24FourDefectBoundary.DegreeTwoBoundaryData

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance chiralMonodromyGraphEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

/-- The fusion site at a position in the `(a,b)` route order. -/
def EvenKempeFusionLens.bFusionSiteAt {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (position : Fin lens.bFusionSites.length) : lens.FusionSite :=
  ⟨lens.bFusionSites.get position, List.get_mem _ position⟩

/-- The fusion site at a position in the `(a,c)` route order. -/
def EvenKempeFusionLens.cFusionSiteAt {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (position : Fin lens.cFusionSites.length) : lens.FusionSite :=
  ⟨lens.cFusionSites.get position,
    lens.bFusionSites_perm_cFusionSites.mem_iff.2
      (List.get_mem _ position)⟩

@[simp] theorem EvenKempeFusionLens.bFusionSiteAt_val
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (position : Fin lens.bFusionSites.length) :
    (lens.bFusionSiteAt position).1 = lens.bFusionSites.get position :=
  rfl

@[simp] theorem EvenKempeFusionLens.cFusionSiteAt_val
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (position : Fin lens.cFusionSites.length) :
    (lens.cFusionSiteAt position).1 = lens.cFusionSites.get position :=
  rfl

/-- The fusion-order equivalence identifies positions naming the same
fusion site. -/
theorem EvenKempeFusionLens.cFusionSiteAt_fusionOrderEquiv
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (position : Fin lens.bFusionSites.length) :
    lens.cFusionSiteAt (lens.fusionOrderEquiv position) =
      lens.bFusionSiteAt position := by
  apply Subtype.ext
  exact lens.fusionOrderEquiv_preserves_edge position

/-- Local chirality read in `(a,b)` route order. -/
def EvenKempeFusionLens.bOrderedFusionChirality {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hab : a ≠ b) (hac : a ≠ c)
    (position : Fin lens.bFusionSites.length) : Bool :=
  lens.fusionChirality hab hac (lens.bFusionSiteAt position)

/-- Local chirality read in `(a,c)` route order. -/
def EvenKempeFusionLens.cOrderedFusionChirality {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hab : a ≠ b) (hac : a ≠ c)
    (position : Fin lens.cFusionSites.length) : Bool :=
  lens.fusionChirality hab hac (lens.cFusionSiteAt position)

/-- Corresponding route-order positions carry the same intrinsic local
chirality. -/
theorem EvenKempeFusionLens.cOrderedFusionChirality_fusionOrderEquiv
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hab : a ≠ b) (hac : a ≠ c)
    (position : Fin lens.bFusionSites.length) :
    lens.cOrderedFusionChirality hab hac
        (lens.fusionOrderEquiv position) =
      lens.bOrderedFusionChirality hab hac position := by
  simp only [EvenKempeFusionLens.bOrderedFusionChirality,
    EvenKempeFusionLens.cOrderedFusionChirality,
    lens.cFusionSiteAt_fusionOrderEquiv position]

/-- The finite word of local chiralities in `(a,b)` route order. -/
def EvenKempeFusionLens.bFusionChiralityWord {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hab : a ≠ b) (hac : a ≠ c) : List Bool :=
  List.ofFn (lens.bOrderedFusionChirality hab hac)

/-- The same finite chirality labels in `(a,c)` route order. -/
def EvenKempeFusionLens.cFusionChiralityWord {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hab : a ≠ b) (hac : a ≠ c) : List Bool :=
  List.ofFn (lens.cOrderedFusionChirality hab hac)

@[simp] theorem EvenKempeFusionLens.bFusionChiralityWord_length
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hab : a ≠ b) (hac : a ≠ c) :
    (lens.bFusionChiralityWord hab hac).length =
      lens.fusionSiteCount := by
  simp [EvenKempeFusionLens.bFusionChiralityWord]

@[simp] theorem EvenKempeFusionLens.cFusionChiralityWord_length
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hab : a ≠ b) (hac : a ≠ c) :
    (lens.cFusionChiralityWord hab hac).length =
      lens.cFusionSites.length := by
  simp [EvenKempeFusionLens.cFusionChiralityWord]

@[simp] theorem EvenKempeFusionLens.bFusionChiralityWord_get
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hab : a ≠ b) (hac : a ≠ c)
    (position : Fin (lens.bFusionChiralityWord hab hac).length) :
    (lens.bFusionChiralityWord hab hac).get position =
      lens.bOrderedFusionChirality hab hac
        ⟨position, by simpa using position.isLt⟩ := by
  simp [EvenKempeFusionLens.bFusionChiralityWord]

@[simp] theorem EvenKempeFusionLens.cFusionChiralityWord_get
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hab : a ≠ b) (hac : a ≠ c)
    (position : Fin (lens.cFusionChiralityWord hab hac).length) :
    (lens.cFusionChiralityWord hab hac).get position =
      lens.cOrderedFusionChirality hab hac
        ⟨position, by simpa using position.isLt⟩ := by
  simp [EvenKempeFusionLens.cFusionChiralityWord]

/-- The `c`-order chirality state transported to the common `Fin`
carrier used by the fusion monodromy. -/
def EvenKempeFusionLens.cOrderedFusionChiralityOnCount
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hab : a ≠ b) (hac : a ≠ c)
    (position : Fin lens.fusionSiteCount) : Bool :=
  lens.cOrderedFusionChirality hab hac
    (finCongr lens.fusionSites_length_eq position)

/-- The finite fusion monodromy preserves the local chirality label when
its output is interpreted in the second route order. -/
theorem EvenKempeFusionLens.fusionMonodromy_preserves_chirality
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hab : a ≠ b) (hac : a ≠ c)
    (position : Fin lens.fusionSiteCount) :
    lens.cOrderedFusionChiralityOnCount hab hac
        (lens.fusionMonodromy position) =
      lens.bOrderedFusionChirality hab hac position := by
  have hposition :
      finCongr lens.fusionSites_length_eq
          (lens.fusionMonodromy position) =
        lens.fusionOrderEquiv position := by
    apply Fin.ext
    rfl
  rw [EvenKempeFusionLens.cOrderedFusionChiralityOnCount, hposition]
  exact lens.cOrderedFusionChirality_fusionOrderEquiv hab hac position

end

end GoertzelV24FourDefectBoundary.DegreeTwoBoundaryData

end Mettapedia.GraphTheory.FourColor
