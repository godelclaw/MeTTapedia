import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairKempeFusionCrossChannels
import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairKempeFusionOrderObstruction

namespace Mettapedia.GraphTheory.FourColor

open SimpleGraph
open GoertzelV24FourDefectBoundary

/-- Two duplicate-free lists carrying the same entries, with their possibly
different linear orders retained. -/
structure OrderedListTransport {α : Type*} [DecidableEq α]
    (first second : List α) where
  perm : first.Perm second
  firstNodup : first.Nodup

namespace OrderedListTransport

variable {α : Type*} [DecidableEq α]
  {first second : List α}

theorem secondNodup (transport : OrderedListTransport first second) :
    second.Nodup :=
  transport.perm.nodup_iff.mp transport.firstNodup

/-- The identity-on-entries equivalence between the two membership types. -/
def membershipEquiv (transport : OrderedListTransport first second) :
    {entry : α // entry ∈ first} ≃ {entry : α // entry ∈ second} where
  toFun entry := ⟨entry.1, transport.perm.mem_iff.mp entry.2⟩
  invFun entry := ⟨entry.1, transport.perm.mem_iff.mpr entry.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The position of an entry in the first order is sent to the position of
the same entry in the second order. -/
def orderEquiv (transport : OrderedListTransport first second) :
    Fin first.length ≃ Fin second.length :=
  (List.Nodup.getEquiv first transport.firstNodup).trans
    (transport.membershipEquiv.trans
      (List.Nodup.getEquiv second transport.secondNodup).symm)

theorem orderEquiv_preserves_entry
    (transport : OrderedListTransport first second)
    (position : Fin first.length) :
    second.get (transport.orderEquiv position) = first.get position := by
  simp [orderEquiv, membershipEquiv]

/-- Transporting the second order back across the length equality gives a
permutation of the first position type. -/
def monodromy (transport : OrderedListTransport first second) :
    Equiv.Perm (Fin first.length) :=
  transport.orderEquiv.trans (finCongr transport.perm.length_eq.symm)

@[simp] theorem monodromy_apply_val
    (transport : OrderedListTransport first second)
    (position : Fin first.length) :
    (transport.monodromy position : Nat) =
      (transport.orderEquiv position : Nat) :=
  rfl

/-- Trivial monodromy says precisely that the same ordinal position names an
entry in both list orders. -/
theorem monodromy_eq_refl_iff_orderEquiv_eq_finCongr
    (transport : OrderedListTransport first second) :
    transport.monodromy = Equiv.refl (Fin first.length) ↔
      ∀ position : Fin first.length,
        transport.orderEquiv position =
          finCongr transport.perm.length_eq position := by
  constructor
  · intro hmonodromy position
    have hposition := DFunLike.congr_fun hmonodromy position
    apply Fin.ext
    change (transport.monodromy position).val =
      ((Equiv.refl (Fin first.length)) position).val
    exact congrArg Fin.val hposition
  · intro hpositions
    apply Equiv.ext
    intro position
    apply Fin.ext
    change (transport.orderEquiv position).val =
      (finCongr transport.perm.length_eq position).val
    exact congrArg Fin.val (hpositions position)

/-- Equivalently, trivial monodromy means that the two ordered lists agree
entry-by-entry after transporting their equal lengths. -/
theorem monodromy_eq_refl_iff_entries_aligned
    (transport : OrderedListTransport first second) :
    transport.monodromy = Equiv.refl (Fin first.length) ↔
      ∀ position : Fin first.length,
        second.get (finCongr transport.perm.length_eq position) =
          first.get position := by
  constructor
  · intro hmonodromy position
    rw [← (transport.monodromy_eq_refl_iff_orderEquiv_eq_finCongr.mp
      hmonodromy position)]
    exact transport.orderEquiv_preserves_entry position
  · intro haligned
    apply transport.monodromy_eq_refl_iff_orderEquiv_eq_finCongr.mpr
    intro position
    apply transport.secondNodup.get_inj_iff.mp
    calc
      second.get (transport.orderEquiv position) = first.get position :=
        transport.orderEquiv_preserves_entry position
      _ = second.get (finCongr transport.perm.length_eq position) :=
        (haligned position).symm

/-- Zero or one common entry cannot carry nontrivial order monodromy. -/
theorem monodromy_eq_refl_of_length_le_one
    (transport : OrderedListTransport first second)
    (hcount : first.length ≤ 1) :
    transport.monodromy = Equiv.refl (Fin first.length) := by
  apply Equiv.ext
  intro position
  apply Fin.ext
  have hposition := position.isLt
  have himage := (transport.monodromy position).isLt
  omega

theorem two_le_length_of_monodromy_ne_refl
    (transport : OrderedListTransport first second)
    (hmonodromy : transport.monodromy ≠
      Equiv.refl (Fin first.length)) :
    2 ≤ first.length := by
  by_contra hcount
  apply hmonodromy
  exact transport.monodromy_eq_refl_of_length_le_one (by omega)

/-- A nonidentity comparison of two finite orders contains an inversion. -/
theorem exists_inversion_of_monodromy_ne_refl
    (transport : OrderedListTransport first second)
    (hmonodromy : transport.monodromy ≠
      Equiv.refl (Fin first.length)) :
    ∃ firstPosition secondPosition : Fin first.length,
      firstPosition < secondPosition ∧
        transport.monodromy secondPosition <
          transport.monodromy firstPosition :=
  finPermutation_exists_inversion_of_ne_refl
    transport.monodromy hmonodromy

/-- The canonical order embedding of the positions of a sublist into the
positions of its ambient list. -/
noncomputable def sublistOrderEmbedding
    {entries support : List α} (hsublist : entries.Sublist support) :
    Fin entries.length ↪o Fin support.length :=
  Classical.choose
    (List.sublist_iff_exists_fin_orderEmbedding_get_eq.mp hsublist)

omit [DecidableEq α] in
theorem sublistOrderEmbedding_preserves_entry
    {entries support : List α} (hsublist : entries.Sublist support)
    (position : Fin entries.length) :
    entries.get position =
      support.get (sublistOrderEmbedding hsublist position) :=
  Classical.choose_spec
    (List.sublist_iff_exists_fin_orderEmbedding_get_eq.mp hsublist) position

/-- A position and its monodromy image select the same entry in the two
ambient supports. -/
theorem support_get_monodromy_eq
    (transport : OrderedListTransport first second)
    {firstSupport secondSupport : List α}
    (hfirst : first.Sublist firstSupport)
    (hsecond : second.Sublist secondSupport)
    (position : Fin first.length) :
    firstSupport.get (sublistOrderEmbedding hfirst position) =
      secondSupport.get
        (sublistOrderEmbedding hsecond
          (finCongr transport.perm.length_eq
            (transport.monodromy position))) := by
  have hposition :
      finCongr transport.perm.length_eq
          (transport.monodromy position) =
        transport.orderEquiv position := by
    apply Fin.ext
    rfl
  calc
    firstSupport.get (sublistOrderEmbedding hfirst position) =
        first.get position :=
      (sublistOrderEmbedding_preserves_entry hfirst position).symm
    _ = second.get (transport.orderEquiv position) :=
      (transport.orderEquiv_preserves_entry position).symm
    _ = secondSupport.get
          (sublistOrderEmbedding hsecond
            (finCongr transport.perm.length_eq
              (transport.monodromy position))) := by
      rw [hposition]
      exact sublistOrderEmbedding_preserves_entry hsecond _

/-- A nontrivial order transport is realized by two actual ambient entries
whose positions increase in the first support and decrease in the second. -/
theorem exists_supportOrderInversion_of_monodromy_ne_refl
    (transport : OrderedListTransport first second)
    {firstSupport secondSupport : List α}
    (hfirst : first.Sublist firstSupport)
    (hsecond : second.Sublist secondSupport)
    (hmonodromy : transport.monodromy ≠
      Equiv.refl (Fin first.length)) :
    ∃ firstPosition secondPosition : Fin first.length,
      sublistOrderEmbedding hfirst firstPosition <
          sublistOrderEmbedding hfirst secondPosition ∧
        sublistOrderEmbedding hsecond
            (finCongr transport.perm.length_eq
              (transport.monodromy secondPosition)) <
          sublistOrderEmbedding hsecond
            (finCongr transport.perm.length_eq
              (transport.monodromy firstPosition)) ∧
        firstSupport.get (sublistOrderEmbedding hfirst firstPosition) =
          secondSupport.get
            (sublistOrderEmbedding hsecond
              (finCongr transport.perm.length_eq
                (transport.monodromy firstPosition))) ∧
        firstSupport.get (sublistOrderEmbedding hfirst secondPosition) =
          secondSupport.get
            (sublistOrderEmbedding hsecond
              (finCongr transport.perm.length_eq
                (transport.monodromy secondPosition))) := by
  rcases transport.exists_inversion_of_monodromy_ne_refl hmonodromy with
    ⟨firstPosition, secondPosition, hfirstSecond, hreverse⟩
  refine ⟨firstPosition, secondPosition,
    (sublistOrderEmbedding hfirst).lt_iff_lt.mpr hfirstSecond,
    ?_, transport.support_get_monodromy_eq hfirst hsecond firstPosition,
    transport.support_get_monodromy_eq hfirst hsecond secondPosition⟩
  exact (sublistOrderEmbedding hsecond).lt_iff_lt.mpr hreverse

end OrderedListTransport

namespace GoertzelV24FourDefectBoundary.DegreeTwoBoundaryData

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance crossChannelOrderGraphEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

/-- The ordered correspondence for intersections of the first lens's
`(a,b)` route with the second lens's `(a,c)` route. -/
def EvenKempeFusionLens.bcCrossOrderTransport
    {data : DegreeTwoBoundaryData G 4}
    {C : G.EdgeColoring Color} {a b c : Color}
    (lens01 : data.EvenKempeFusionLens C a b c 0 1)
    (lens23 : data.EvenKempeFusionLens C a b c 2 3) :
    OrderedListTransport (lens01.bcCrossSites lens23)
      (lens01.bcCrossSitesOnSecond lens23) where
  perm := lens01.bcCrossSites_perm_onSecond lens23
  firstNodup := lens01.bcCrossSites_nodup lens23

theorem EvenKempeFusionLens.bcCrossSites_length_eq
    {data : DegreeTwoBoundaryData G 4}
    {C : G.EdgeColoring Color} {a b c : Color}
    (lens01 : data.EvenKempeFusionLens C a b c 0 1)
    (lens23 : data.EvenKempeFusionLens C a b c 2 3) :
    (lens01.bcCrossSites lens23).length =
      (lens01.bcCrossSitesOnSecond lens23).length :=
  (lens01.bcCrossSites_perm_onSecond lens23).length_eq

/-- The position equivalence that sends each first-channel site to the same
edge in the second route order. -/
def EvenKempeFusionLens.bcCrossOrderEquiv
    {data : DegreeTwoBoundaryData G 4}
    {C : G.EdgeColoring Color} {a b c : Color}
    (lens01 : data.EvenKempeFusionLens C a b c 0 1)
    (lens23 : data.EvenKempeFusionLens C a b c 2 3) :
    Fin (lens01.bcCrossSites lens23).length ≃
      Fin (lens01.bcCrossSitesOnSecond lens23).length :=
  (lens01.bcCrossOrderTransport lens23).orderEquiv

theorem EvenKempeFusionLens.bcCrossOrderEquiv_preserves_edge
    {data : DegreeTwoBoundaryData G 4}
    {C : G.EdgeColoring Color} {a b c : Color}
    (lens01 : data.EvenKempeFusionLens C a b c 0 1)
    (lens23 : data.EvenKempeFusionLens C a b c 2 3)
    (position : Fin (lens01.bcCrossSites lens23).length) :
    (lens01.bcCrossSitesOnSecond lens23).get
        (lens01.bcCrossOrderEquiv lens23 position) =
      (lens01.bcCrossSites lens23).get position := by
  exact OrderedListTransport.orderEquiv_preserves_entry
    (lens01.bcCrossOrderTransport lens23) position

/-- The permutation comparing the two route-induced orders on the first
cross channel. -/
def EvenKempeFusionLens.bcCrossMonodromy
    {data : DegreeTwoBoundaryData G 4}
    {C : G.EdgeColoring Color} {a b c : Color}
    (lens01 : data.EvenKempeFusionLens C a b c 0 1)
    (lens23 : data.EvenKempeFusionLens C a b c 2 3) :
    Equiv.Perm (Fin (lens01.bcCrossSites lens23).length) :=
  (lens01.bcCrossOrderTransport lens23).monodromy

@[simp] theorem EvenKempeFusionLens.bcCrossMonodromy_apply_val
    {data : DegreeTwoBoundaryData G 4}
    {C : G.EdgeColoring Color} {a b c : Color}
    (lens01 : data.EvenKempeFusionLens C a b c 0 1)
    (lens23 : data.EvenKempeFusionLens C a b c 2 3)
    (position : Fin (lens01.bcCrossSites lens23).length) :
    (lens01.bcCrossMonodromy lens23 position : Nat) =
      (lens01.bcCrossOrderEquiv lens23 position : Nat) :=
  rfl

/-- A nontrivial first cross-channel order has two sites met in opposite
orders along its two ambient routes. -/
theorem EvenKempeFusionLens.exists_bcCrossOrderInversion_of_monodromy_ne_refl
    {data : DegreeTwoBoundaryData G 4}
    {C : G.EdgeColoring Color} {a b c : Color}
    (lens01 : data.EvenKempeFusionLens C a b c 0 1)
    (lens23 : data.EvenKempeFusionLens C a b c 2 3)
    (hmonodromy : lens01.bcCrossMonodromy lens23 ≠
      Equiv.refl (Fin (lens01.bcCrossSites lens23).length)) :
    ∃ first second : Fin (lens01.bcCrossSites lens23).length,
      first < second ∧
        lens01.bcCrossMonodromy lens23 second <
          lens01.bcCrossMonodromy lens23 first := by
  exact OrderedListTransport.exists_inversion_of_monodromy_ne_refl
    (lens01.bcCrossOrderTransport lens23) hmonodromy

/-- With at most one site, the first cross-channel monodromy is trivial. -/
theorem EvenKempeFusionLens.bcCrossMonodromy_eq_refl_of_length_le_one
    {data : DegreeTwoBoundaryData G 4}
    {C : G.EdgeColoring Color} {a b c : Color}
    (lens01 : data.EvenKempeFusionLens C a b c 0 1)
    (lens23 : data.EvenKempeFusionLens C a b c 2 3)
    (hcount : (lens01.bcCrossSites lens23).length ≤ 1) :
    lens01.bcCrossMonodromy lens23 =
      Equiv.refl (Fin (lens01.bcCrossSites lens23).length) := by
  exact OrderedListTransport.monodromy_eq_refl_of_length_le_one
    (lens01.bcCrossOrderTransport lens23) hcount

/-- Identity monodromy is exactly entrywise agreement of the two route
orders on the first cross channel. -/
theorem EvenKempeFusionLens.bcCrossMonodromy_eq_refl_iff_sites_aligned
    {data : DegreeTwoBoundaryData G 4}
    {C : G.EdgeColoring Color} {a b c : Color}
    (lens01 : data.EvenKempeFusionLens C a b c 0 1)
    (lens23 : data.EvenKempeFusionLens C a b c 2 3) :
    lens01.bcCrossMonodromy lens23 =
        Equiv.refl (Fin (lens01.bcCrossSites lens23).length) ↔
      ∀ position : Fin (lens01.bcCrossSites lens23).length,
        (lens01.bcCrossSitesOnSecond lens23).get
            (finCongr (lens01.bcCrossSites_length_eq lens23) position) =
          (lens01.bcCrossSites lens23).get position := by
  exact OrderedListTransport.monodromy_eq_refl_iff_entries_aligned
    (lens01.bcCrossOrderTransport lens23)

theorem EvenKempeFusionLens.bcCrossSites_sublist_firstRouteSupport
    {data : DegreeTwoBoundaryData G 4}
    {C : G.EdgeColoring Color} {a b c : Color}
    (lens01 : data.EvenKempeFusionLens C a b c 0 1)
    (lens23 : data.EvenKempeFusionLens C a b c 2 3) :
    (lens01.bcCrossSites lens23).Sublist
      lens01.bRoute.ambientPath.support := by
  exact List.filter_sublist

theorem EvenKempeFusionLens.bcCrossSitesOnSecond_sublist_secondRouteSupport
    {data : DegreeTwoBoundaryData G 4}
    {C : G.EdgeColoring Color} {a b c : Color}
    (lens01 : data.EvenKempeFusionLens C a b c 0 1)
    (lens23 : data.EvenKempeFusionLens C a b c 2 3) :
    (lens01.bcCrossSitesOnSecond lens23).Sublist
      lens23.cRoute.ambientPath.support := by
  exact List.filter_sublist

/-- Cross-site positions embedded in the first `(a,b)` route support. -/
def EvenKempeFusionLens.bcFirstSupportOrderEmbedding
    {data : DegreeTwoBoundaryData G 4}
    {C : G.EdgeColoring Color} {a b c : Color}
    (lens01 : data.EvenKempeFusionLens C a b c 0 1)
    (lens23 : data.EvenKempeFusionLens C a b c 2 3) :
    Fin (lens01.bcCrossSites lens23).length ↪o
      Fin lens01.bRoute.ambientPath.support.length :=
  OrderedListTransport.sublistOrderEmbedding
    (lens01.bcCrossSites_sublist_firstRouteSupport lens23)

/-- The same sites embedded in the second `(a,c)` route support. -/
def EvenKempeFusionLens.bcSecondSupportOrderEmbedding
    {data : DegreeTwoBoundaryData G 4}
    {C : G.EdgeColoring Color} {a b c : Color}
    (lens01 : data.EvenKempeFusionLens C a b c 0 1)
    (lens23 : data.EvenKempeFusionLens C a b c 2 3) :
    Fin (lens01.bcCrossSitesOnSecond lens23).length ↪o
      Fin lens23.cRoute.ambientPath.support.length :=
  OrderedListTransport.sublistOrderEmbedding
    (lens01.bcCrossSitesOnSecond_sublist_secondRouteSupport lens23)

theorem EvenKempeFusionLens.bcFirstSupportOrderEmbedding_preserves_edge
    {data : DegreeTwoBoundaryData G 4}
    {C : G.EdgeColoring Color} {a b c : Color}
    (lens01 : data.EvenKempeFusionLens C a b c 0 1)
    (lens23 : data.EvenKempeFusionLens C a b c 2 3)
    (position : Fin (lens01.bcCrossSites lens23).length) :
    (lens01.bcCrossSites lens23).get position =
      lens01.bRoute.ambientPath.support.get
        (lens01.bcFirstSupportOrderEmbedding lens23 position) := by
  exact OrderedListTransport.sublistOrderEmbedding_preserves_entry
    (lens01.bcCrossSites_sublist_firstRouteSupport lens23) position

theorem EvenKempeFusionLens.bcSecondSupportOrderEmbedding_preserves_edge
    {data : DegreeTwoBoundaryData G 4}
    {C : G.EdgeColoring Color} {a b c : Color}
    (lens01 : data.EvenKempeFusionLens C a b c 0 1)
    (lens23 : data.EvenKempeFusionLens C a b c 2 3)
    (position : Fin (lens01.bcCrossSitesOnSecond lens23).length) :
    (lens01.bcCrossSitesOnSecond lens23).get position =
      lens23.cRoute.ambientPath.support.get
        (lens01.bcSecondSupportOrderEmbedding lens23 position) := by
  exact OrderedListTransport.sublistOrderEmbedding_preserves_entry
    (lens01.bcCrossSitesOnSecond_sublist_secondRouteSupport lens23) position

/-- A cross position and its monodromy image select the same graph edge in
the two ambient route supports. -/
theorem EvenKempeFusionLens.support_get_bcCrossMonodromy_eq
    {data : DegreeTwoBoundaryData G 4}
    {C : G.EdgeColoring Color} {a b c : Color}
    (lens01 : data.EvenKempeFusionLens C a b c 0 1)
    (lens23 : data.EvenKempeFusionLens C a b c 2 3)
    (position : Fin (lens01.bcCrossSites lens23).length) :
    lens01.bRoute.ambientPath.support.get
        (lens01.bcFirstSupportOrderEmbedding lens23 position) =
      lens23.cRoute.ambientPath.support.get
        (lens01.bcSecondSupportOrderEmbedding lens23
          (finCongr (lens01.bcCrossSites_length_eq lens23)
            (lens01.bcCrossMonodromy lens23 position))) := by
  have hposition :
      finCongr (lens01.bcCrossSites_length_eq lens23)
          (lens01.bcCrossMonodromy lens23 position) =
        lens01.bcCrossOrderEquiv lens23 position := by
    apply Fin.ext
    rfl
  calc
    lens01.bRoute.ambientPath.support.get
          (lens01.bcFirstSupportOrderEmbedding lens23 position) =
        (lens01.bcCrossSites lens23).get position :=
      (lens01.bcFirstSupportOrderEmbedding_preserves_edge
        lens23 position).symm
    _ = (lens01.bcCrossSitesOnSecond lens23).get
          (lens01.bcCrossOrderEquiv lens23 position) :=
      (lens01.bcCrossOrderEquiv_preserves_edge lens23 position).symm
    _ = lens23.cRoute.ambientPath.support.get
          (lens01.bcSecondSupportOrderEmbedding lens23
            (finCongr (lens01.bcCrossSites_length_eq lens23)
              (lens01.bcCrossMonodromy lens23 position))) := by
      rw [hposition]
      exact lens01.bcSecondSupportOrderEmbedding_preserves_edge lens23 _

/-- Nontrivial first-channel monodromy is realized by two actual common
edges whose positions increase in the first ambient route and decrease in
the second. -/
theorem EvenKempeFusionLens.exists_bcAmbientSupportOrderInversion_of_monodromy_ne_refl
    {data : DegreeTwoBoundaryData G 4}
    {C : G.EdgeColoring Color} {a b c : Color}
    (lens01 : data.EvenKempeFusionLens C a b c 0 1)
    (lens23 : data.EvenKempeFusionLens C a b c 2 3)
    (hmonodromy : lens01.bcCrossMonodromy lens23 ≠
      Equiv.refl (Fin (lens01.bcCrossSites lens23).length)) :
    ∃ first second : Fin (lens01.bcCrossSites lens23).length,
      lens01.bcFirstSupportOrderEmbedding lens23 first <
          lens01.bcFirstSupportOrderEmbedding lens23 second ∧
        lens01.bcSecondSupportOrderEmbedding lens23
            (finCongr (lens01.bcCrossSites_length_eq lens23)
              (lens01.bcCrossMonodromy lens23 second)) <
          lens01.bcSecondSupportOrderEmbedding lens23
            (finCongr (lens01.bcCrossSites_length_eq lens23)
              (lens01.bcCrossMonodromy lens23 first)) ∧
        lens01.bRoute.ambientPath.support.get
            (lens01.bcFirstSupportOrderEmbedding lens23 first) =
          lens23.cRoute.ambientPath.support.get
            (lens01.bcSecondSupportOrderEmbedding lens23
              (finCongr (lens01.bcCrossSites_length_eq lens23)
                (lens01.bcCrossMonodromy lens23 first))) ∧
        lens01.bRoute.ambientPath.support.get
            (lens01.bcFirstSupportOrderEmbedding lens23 second) =
          lens23.cRoute.ambientPath.support.get
            (lens01.bcSecondSupportOrderEmbedding lens23
              (finCongr (lens01.bcCrossSites_length_eq lens23)
                (lens01.bcCrossMonodromy lens23 second))) := by
  rcases lens01.exists_bcCrossOrderInversion_of_monodromy_ne_refl
      lens23 hmonodromy with
    ⟨first, second, hfirstSecond, hreverse⟩
  refine ⟨first, second,
    (lens01.bcFirstSupportOrderEmbedding lens23).lt_iff_lt.mpr
      hfirstSecond,
    ?_, lens01.support_get_bcCrossMonodromy_eq lens23 first,
    lens01.support_get_bcCrossMonodromy_eq lens23 second⟩
  exact (lens01.bcSecondSupportOrderEmbedding lens23).lt_iff_lt.mpr
    hreverse

/-- The ordered correspondence for intersections of the first lens's
`(a,c)` route with the second lens's `(a,b)` route. -/
def EvenKempeFusionLens.cbCrossOrderTransport
    {data : DegreeTwoBoundaryData G 4}
    {C : G.EdgeColoring Color} {a b c : Color}
    (lens01 : data.EvenKempeFusionLens C a b c 0 1)
    (lens23 : data.EvenKempeFusionLens C a b c 2 3) :
    OrderedListTransport (lens01.cbCrossSites lens23)
      (lens01.cbCrossSitesOnSecond lens23) where
  perm := lens01.cbCrossSites_perm_onSecond lens23
  firstNodup := lens01.cbCrossSites_nodup lens23

theorem EvenKempeFusionLens.cbCrossSites_length_eq
    {data : DegreeTwoBoundaryData G 4}
    {C : G.EdgeColoring Color} {a b c : Color}
    (lens01 : data.EvenKempeFusionLens C a b c 0 1)
    (lens23 : data.EvenKempeFusionLens C a b c 2 3) :
    (lens01.cbCrossSites lens23).length =
      (lens01.cbCrossSitesOnSecond lens23).length :=
  (lens01.cbCrossSites_perm_onSecond lens23).length_eq

/-- The position equivalence that sends each second-channel site to the same
edge in the second route order. -/
def EvenKempeFusionLens.cbCrossOrderEquiv
    {data : DegreeTwoBoundaryData G 4}
    {C : G.EdgeColoring Color} {a b c : Color}
    (lens01 : data.EvenKempeFusionLens C a b c 0 1)
    (lens23 : data.EvenKempeFusionLens C a b c 2 3) :
    Fin (lens01.cbCrossSites lens23).length ≃
      Fin (lens01.cbCrossSitesOnSecond lens23).length :=
  (lens01.cbCrossOrderTransport lens23).orderEquiv

theorem EvenKempeFusionLens.cbCrossOrderEquiv_preserves_edge
    {data : DegreeTwoBoundaryData G 4}
    {C : G.EdgeColoring Color} {a b c : Color}
    (lens01 : data.EvenKempeFusionLens C a b c 0 1)
    (lens23 : data.EvenKempeFusionLens C a b c 2 3)
    (position : Fin (lens01.cbCrossSites lens23).length) :
    (lens01.cbCrossSitesOnSecond lens23).get
        (lens01.cbCrossOrderEquiv lens23 position) =
      (lens01.cbCrossSites lens23).get position := by
  exact OrderedListTransport.orderEquiv_preserves_entry
    (lens01.cbCrossOrderTransport lens23) position

/-- The permutation comparing the two route-induced orders on the second
cross channel. -/
def EvenKempeFusionLens.cbCrossMonodromy
    {data : DegreeTwoBoundaryData G 4}
    {C : G.EdgeColoring Color} {a b c : Color}
    (lens01 : data.EvenKempeFusionLens C a b c 0 1)
    (lens23 : data.EvenKempeFusionLens C a b c 2 3) :
    Equiv.Perm (Fin (lens01.cbCrossSites lens23).length) :=
  (lens01.cbCrossOrderTransport lens23).monodromy

@[simp] theorem EvenKempeFusionLens.cbCrossMonodromy_apply_val
    {data : DegreeTwoBoundaryData G 4}
    {C : G.EdgeColoring Color} {a b c : Color}
    (lens01 : data.EvenKempeFusionLens C a b c 0 1)
    (lens23 : data.EvenKempeFusionLens C a b c 2 3)
    (position : Fin (lens01.cbCrossSites lens23).length) :
    (lens01.cbCrossMonodromy lens23 position : Nat) =
      (lens01.cbCrossOrderEquiv lens23 position : Nat) :=
  rfl

/-- A nontrivial second cross-channel order has two sites met in opposite
orders along its two ambient routes. -/
theorem EvenKempeFusionLens.exists_cbCrossOrderInversion_of_monodromy_ne_refl
    {data : DegreeTwoBoundaryData G 4}
    {C : G.EdgeColoring Color} {a b c : Color}
    (lens01 : data.EvenKempeFusionLens C a b c 0 1)
    (lens23 : data.EvenKempeFusionLens C a b c 2 3)
    (hmonodromy : lens01.cbCrossMonodromy lens23 ≠
      Equiv.refl (Fin (lens01.cbCrossSites lens23).length)) :
    ∃ first second : Fin (lens01.cbCrossSites lens23).length,
      first < second ∧
        lens01.cbCrossMonodromy lens23 second <
          lens01.cbCrossMonodromy lens23 first := by
  exact OrderedListTransport.exists_inversion_of_monodromy_ne_refl
    (lens01.cbCrossOrderTransport lens23) hmonodromy

/-- With at most one site, the second cross-channel monodromy is trivial. -/
theorem EvenKempeFusionLens.cbCrossMonodromy_eq_refl_of_length_le_one
    {data : DegreeTwoBoundaryData G 4}
    {C : G.EdgeColoring Color} {a b c : Color}
    (lens01 : data.EvenKempeFusionLens C a b c 0 1)
    (lens23 : data.EvenKempeFusionLens C a b c 2 3)
    (hcount : (lens01.cbCrossSites lens23).length ≤ 1) :
    lens01.cbCrossMonodromy lens23 =
      Equiv.refl (Fin (lens01.cbCrossSites lens23).length) := by
  exact OrderedListTransport.monodromy_eq_refl_of_length_le_one
    (lens01.cbCrossOrderTransport lens23) hcount

/-- Identity monodromy is exactly entrywise agreement of the two route
orders on the second cross channel. -/
theorem EvenKempeFusionLens.cbCrossMonodromy_eq_refl_iff_sites_aligned
    {data : DegreeTwoBoundaryData G 4}
    {C : G.EdgeColoring Color} {a b c : Color}
    (lens01 : data.EvenKempeFusionLens C a b c 0 1)
    (lens23 : data.EvenKempeFusionLens C a b c 2 3) :
    lens01.cbCrossMonodromy lens23 =
        Equiv.refl (Fin (lens01.cbCrossSites lens23).length) ↔
      ∀ position : Fin (lens01.cbCrossSites lens23).length,
        (lens01.cbCrossSitesOnSecond lens23).get
            (finCongr (lens01.cbCrossSites_length_eq lens23) position) =
          (lens01.cbCrossSites lens23).get position := by
  exact OrderedListTransport.monodromy_eq_refl_iff_entries_aligned
    (lens01.cbCrossOrderTransport lens23)

theorem EvenKempeFusionLens.cbCrossSites_sublist_firstRouteSupport
    {data : DegreeTwoBoundaryData G 4}
    {C : G.EdgeColoring Color} {a b c : Color}
    (lens01 : data.EvenKempeFusionLens C a b c 0 1)
    (lens23 : data.EvenKempeFusionLens C a b c 2 3) :
    (lens01.cbCrossSites lens23).Sublist
      lens01.cRoute.ambientPath.support := by
  exact List.filter_sublist

theorem EvenKempeFusionLens.cbCrossSitesOnSecond_sublist_secondRouteSupport
    {data : DegreeTwoBoundaryData G 4}
    {C : G.EdgeColoring Color} {a b c : Color}
    (lens01 : data.EvenKempeFusionLens C a b c 0 1)
    (lens23 : data.EvenKempeFusionLens C a b c 2 3) :
    (lens01.cbCrossSitesOnSecond lens23).Sublist
      lens23.bRoute.ambientPath.support := by
  exact List.filter_sublist

/-- Cross-site positions embedded in the first `(a,c)` route support. -/
def EvenKempeFusionLens.cbFirstSupportOrderEmbedding
    {data : DegreeTwoBoundaryData G 4}
    {C : G.EdgeColoring Color} {a b c : Color}
    (lens01 : data.EvenKempeFusionLens C a b c 0 1)
    (lens23 : data.EvenKempeFusionLens C a b c 2 3) :
    Fin (lens01.cbCrossSites lens23).length ↪o
      Fin lens01.cRoute.ambientPath.support.length :=
  OrderedListTransport.sublistOrderEmbedding
    (lens01.cbCrossSites_sublist_firstRouteSupport lens23)

/-- The same sites embedded in the second `(a,b)` route support. -/
def EvenKempeFusionLens.cbSecondSupportOrderEmbedding
    {data : DegreeTwoBoundaryData G 4}
    {C : G.EdgeColoring Color} {a b c : Color}
    (lens01 : data.EvenKempeFusionLens C a b c 0 1)
    (lens23 : data.EvenKempeFusionLens C a b c 2 3) :
    Fin (lens01.cbCrossSitesOnSecond lens23).length ↪o
      Fin lens23.bRoute.ambientPath.support.length :=
  OrderedListTransport.sublistOrderEmbedding
    (lens01.cbCrossSitesOnSecond_sublist_secondRouteSupport lens23)

theorem EvenKempeFusionLens.cbFirstSupportOrderEmbedding_preserves_edge
    {data : DegreeTwoBoundaryData G 4}
    {C : G.EdgeColoring Color} {a b c : Color}
    (lens01 : data.EvenKempeFusionLens C a b c 0 1)
    (lens23 : data.EvenKempeFusionLens C a b c 2 3)
    (position : Fin (lens01.cbCrossSites lens23).length) :
    (lens01.cbCrossSites lens23).get position =
      lens01.cRoute.ambientPath.support.get
        (lens01.cbFirstSupportOrderEmbedding lens23 position) := by
  exact OrderedListTransport.sublistOrderEmbedding_preserves_entry
    (lens01.cbCrossSites_sublist_firstRouteSupport lens23) position

theorem EvenKempeFusionLens.cbSecondSupportOrderEmbedding_preserves_edge
    {data : DegreeTwoBoundaryData G 4}
    {C : G.EdgeColoring Color} {a b c : Color}
    (lens01 : data.EvenKempeFusionLens C a b c 0 1)
    (lens23 : data.EvenKempeFusionLens C a b c 2 3)
    (position : Fin (lens01.cbCrossSitesOnSecond lens23).length) :
    (lens01.cbCrossSitesOnSecond lens23).get position =
      lens23.bRoute.ambientPath.support.get
        (lens01.cbSecondSupportOrderEmbedding lens23 position) := by
  exact OrderedListTransport.sublistOrderEmbedding_preserves_entry
    (lens01.cbCrossSitesOnSecond_sublist_secondRouteSupport lens23) position

/-- A position in the second channel and its monodromy image select the same
graph edge in the two ambient route supports. -/
theorem EvenKempeFusionLens.support_get_cbCrossMonodromy_eq
    {data : DegreeTwoBoundaryData G 4}
    {C : G.EdgeColoring Color} {a b c : Color}
    (lens01 : data.EvenKempeFusionLens C a b c 0 1)
    (lens23 : data.EvenKempeFusionLens C a b c 2 3)
    (position : Fin (lens01.cbCrossSites lens23).length) :
    lens01.cRoute.ambientPath.support.get
        (lens01.cbFirstSupportOrderEmbedding lens23 position) =
      lens23.bRoute.ambientPath.support.get
        (lens01.cbSecondSupportOrderEmbedding lens23
          (finCongr (lens01.cbCrossSites_length_eq lens23)
            (lens01.cbCrossMonodromy lens23 position))) := by
  have hposition :
      finCongr (lens01.cbCrossSites_length_eq lens23)
          (lens01.cbCrossMonodromy lens23 position) =
        lens01.cbCrossOrderEquiv lens23 position := by
    apply Fin.ext
    rfl
  calc
    lens01.cRoute.ambientPath.support.get
          (lens01.cbFirstSupportOrderEmbedding lens23 position) =
        (lens01.cbCrossSites lens23).get position :=
      (lens01.cbFirstSupportOrderEmbedding_preserves_edge
        lens23 position).symm
    _ = (lens01.cbCrossSitesOnSecond lens23).get
          (lens01.cbCrossOrderEquiv lens23 position) :=
      (lens01.cbCrossOrderEquiv_preserves_edge lens23 position).symm
    _ = lens23.bRoute.ambientPath.support.get
          (lens01.cbSecondSupportOrderEmbedding lens23
            (finCongr (lens01.cbCrossSites_length_eq lens23)
              (lens01.cbCrossMonodromy lens23 position))) := by
      rw [hposition]
      exact lens01.cbSecondSupportOrderEmbedding_preserves_edge lens23 _

/-- Nontrivial second-channel monodromy is realized by two actual common
edges whose positions increase in the first ambient route and decrease in
the second. -/
theorem EvenKempeFusionLens.exists_cbAmbientSupportOrderInversion_of_monodromy_ne_refl
    {data : DegreeTwoBoundaryData G 4}
    {C : G.EdgeColoring Color} {a b c : Color}
    (lens01 : data.EvenKempeFusionLens C a b c 0 1)
    (lens23 : data.EvenKempeFusionLens C a b c 2 3)
    (hmonodromy : lens01.cbCrossMonodromy lens23 ≠
      Equiv.refl (Fin (lens01.cbCrossSites lens23).length)) :
    ∃ first second : Fin (lens01.cbCrossSites lens23).length,
      lens01.cbFirstSupportOrderEmbedding lens23 first <
          lens01.cbFirstSupportOrderEmbedding lens23 second ∧
        lens01.cbSecondSupportOrderEmbedding lens23
            (finCongr (lens01.cbCrossSites_length_eq lens23)
              (lens01.cbCrossMonodromy lens23 second)) <
          lens01.cbSecondSupportOrderEmbedding lens23
            (finCongr (lens01.cbCrossSites_length_eq lens23)
              (lens01.cbCrossMonodromy lens23 first)) ∧
        lens01.cRoute.ambientPath.support.get
            (lens01.cbFirstSupportOrderEmbedding lens23 first) =
          lens23.bRoute.ambientPath.support.get
            (lens01.cbSecondSupportOrderEmbedding lens23
              (finCongr (lens01.cbCrossSites_length_eq lens23)
                (lens01.cbCrossMonodromy lens23 first))) ∧
        lens01.cRoute.ambientPath.support.get
            (lens01.cbFirstSupportOrderEmbedding lens23 second) =
          lens23.bRoute.ambientPath.support.get
            (lens01.cbSecondSupportOrderEmbedding lens23
              (finCongr (lens01.cbCrossSites_length_eq lens23)
                (lens01.cbCrossMonodromy lens23 second))) := by
  rcases lens01.exists_cbCrossOrderInversion_of_monodromy_ne_refl
      lens23 hmonodromy with
    ⟨first, second, hfirstSecond, hreverse⟩
  refine ⟨first, second,
    (lens01.cbFirstSupportOrderEmbedding lens23).lt_iff_lt.mpr
      hfirstSecond,
    ?_, lens01.support_get_cbCrossMonodromy_eq lens23 first,
    lens01.support_get_cbCrossMonodromy_eq lens23 second⟩
  exact (lens01.cbSecondSupportOrderEmbedding lens23).lt_iff_lt.mpr
    hreverse

end

end GoertzelV24FourDefectBoundary.DegreeTwoBoundaryData

end Mettapedia.GraphTheory.FourColor
