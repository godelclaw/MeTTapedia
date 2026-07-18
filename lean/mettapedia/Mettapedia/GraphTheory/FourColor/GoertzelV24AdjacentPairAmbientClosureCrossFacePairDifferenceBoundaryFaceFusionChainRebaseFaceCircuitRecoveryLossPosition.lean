import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairAmbientClosureCrossFacePairDifferenceBoundaryFaceFusionChainRebaseFaceCircuitRecoveryProperSubcircuit

namespace Mettapedia.GraphTheory.FourColor

open GoertzelV24AdjacentPairBoundary
open GoertzelV24AdjacentPairInsertion
open GoertzelV24FaceOrbitIncidence
open GoertzelV24FourDefectBoundary
open GoertzelV24TwoEdgeCutMinimality
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

namespace GoertzelV24RebaseFaceCircuit

variable {State Entry : Type*}

private def transitionScore
    (source target : Entry → State) (property : State → Prop)
    [DecidablePred property] (entry : Entry) : ℤ :=
  (if property (target entry) then 1 else 0) -
    (if property (source entry) then 1 else 0)

private theorem sum_transitionScore_eq_gain_sub_loss
    (source target : Entry → State) (property : State → Prop)
    [DecidablePred property] (entries : List Entry) :
    (entries.map (transitionScore source target property)).sum =
      ((entries.filter fun entry =>
        ¬ property (source entry) ∧ property (target entry)).length : ℤ) -
      ((entries.filter fun entry =>
        property (source entry) ∧ ¬ property (target entry)).length : ℤ) := by
  induction entries with
  | nil => simp
  | cons entry entries ih =>
      by_cases hsource : property (source entry)
      · by_cases htarget : property (target entry)
        · simp [transitionScore, hsource, htarget, ih]
        · simp [transitionScore, hsource, htarget, ih]
          omega
      · by_cases htarget : property (target entry)
        · simp [transitionScore, hsource, htarget, ih]
          omega
        · simp [transitionScore, hsource, htarget, ih]

private theorem sum_transitionScore_eq_endpoints
    (source target : Entry → State) (property : State → Prop)
    [DecidablePred property]
    (first : Entry) (rest : List Entry)
    (chain : List.IsChain (fun left right =>
      target left = source right) (first :: rest)) :
    ((first :: rest).map
      (transitionScore source target property)).sum =
        (if property (target ((first :: rest).getLast (by simp)))
          then 1 else 0) -
        (if property (source first) then 1 else 0) := by
  induction rest generalizing first with
  | nil => simp [transitionScore]
  | cons second rest ih =>
      have hparts := List.isChain_cons_cons.mp chain
      rw [List.map_cons, List.sum_cons, ih second hparts.2]
      simp only [transitionScore, List.getLast_cons_cons]
      rw [hparts.1]
      ring_nf

/-- Along a finite cyclic composable trace, a Boolean property is gained
and lost equally many times. -/
theorem cyclic_gain_count_eq_loss_count
    (source target : Entry → State) (property : State → Prop)
    [DecidablePred property]
    (first : Entry) (rest : List Entry)
    (chain : List.IsChain (fun left right =>
      target left = source right) (first :: rest))
    (closing : target ((first :: rest).getLast (by simp)) =
      source first) :
    ((first :: rest).filter fun entry =>
      ¬ property (source entry) ∧ property (target entry)).length =
    ((first :: rest).filter fun entry =>
      property (source entry) ∧ ¬ property (target entry)).length := by
  have hzero : ((first :: rest).map
      (transitionScore source target property)).sum = 0 := by
    rw [sum_transitionScore_eq_endpoints source target property first rest
      chain, closing]
    simp
  have hcount :=
    sum_transitionScore_eq_gain_sub_loss source target property
      (first :: rest)
  have hdiff :
      (((first :: rest).filter fun entry =>
        ¬ property (source entry) ∧ property (target entry)).length : ℤ) -
      (((first :: rest).filter fun entry =>
        property (source entry) ∧ ¬ property (target entry)).length : ℤ) =
        0 := hcount.symm.trans hzero
  have hcast := sub_eq_zero.mp hdiff
  exact_mod_cast hcast

/-- Filtering all positions of a list by a predicate on `get` has the
same cardinality as filtering the list itself. -/
theorem card_filter_univ_get_eq_length_filter
    (entries : List Entry) (test : Entry → Bool) :
    (Finset.univ.filter fun position : Fin entries.length =>
      test (entries.get position)).card =
        (entries.filter test).length := by
  induction entries with
  | nil => simp
  | cons first rest ih =>
      change (Finset.univ.filter fun position : Fin (rest.length + 1) =>
        test ((first :: rest).get position)).card =
          ((first :: rest).filter test).length
      rw [Fin.card_filter_univ_succ']
      change (if test first then 1 else 0) +
          (Finset.univ.filter fun position : Fin rest.length =>
            test (rest.get position)).card =
        ((first :: rest).filter test).length
      rw [ih]
      cases hfirst : test first <;> simp [hfirst, Nat.add_comm]

/-- A nonempty finite set whose elements either enter a second set or
equal one fixed point must either meet that set or be the singleton point. -/
theorem inter_nonempty_or_eq_singleton_of_mem_or_eq
    {Element : Type*} [DecidableEq Element]
    (source target : Finset Element) (point : Element)
    (hsource : source.Nonempty)
    (hcases : ∀ element ∈ source, element ∈ target ∨ element = point) :
    (source ∩ target).Nonempty ∨ source = {point} := by
  by_cases hinter : (source ∩ target).Nonempty
  · exact Or.inl hinter
  · right
    have hoff : ∀ element ∈ source, element ∉ target := by
      intro element hmem htarget
      exact hinter ⟨element, Finset.mem_inter.mpr ⟨hmem, htarget⟩⟩
    have heq : ∀ element ∈ source, element = point := by
      intro element hmem
      exact (hcases element hmem).resolve_left (hoff element hmem)
    rcases hsource with ⟨element, hmem⟩
    have helement : element = point := heq element hmem
    exact Finset.eq_singleton_iff_unique_mem.mpr
      ⟨helement ▸ hmem, heq⟩

end GoertzelV24RebaseFaceCircuit

namespace GoertzelV24AdjacentPairInsertion.AdjacentPairData

open GoertzelV24AdjacentPairBoundary.AdjacentPairData
open GoertzelV24FourDefectBoundary.DegreeTwoBoundaryData

attribute [local instance]
  fusionFaceNetworkGraphEdgeSetDecidableEq
  fusionFaceNetworkRetainedVertexFintype
  fusionFaceNetworkRetainedVertexDecidableEq

variable {graphData : Data G}
  {minimal : GraphBackedVertexMinimalTaitCounterexample graphData}
  {baseData : AdjacentPairData G}

namespace ClosureRecoveryFaceArc

variable {rebaseCircuit :
  CrossCentralExactFaceCertifiedRebaseCircuit graphData minimal baseData}

/-- All displayed rebase positions at which this recovery code gains its
support edge. -/
noncomputable def gainPositions
    (recovery : ClosureRecoveryFaceArc rebaseCircuit) :
    Finset (Fin rebaseCircuit.arcLength) :=
  Finset.univ.filter fun position =>
    let arc := (rebaseCircuit.first :: rebaseCircuit.rest).get position
    recovery.edge.1 ∉ recovery.channel.edges arc.source ∧
      recovery.edge.1 ∈ recovery.channel.edges arc.target

/-- All displayed rebase positions at which this recovery code loses its
support edge. -/
noncomputable def lossPositions
    (recovery : ClosureRecoveryFaceArc rebaseCircuit) :
    Finset (Fin rebaseCircuit.arcLength) :=
  Finset.univ.filter fun position =>
    let arc := (rebaseCircuit.first :: rebaseCircuit.rest).get position
    recovery.edge.1 ∈ recovery.channel.edges arc.source ∧
      recovery.edge.1 ∉ recovery.channel.edges arc.target

/-- A rebase position is neutral for a recovery code when traversing its
displayed arc preserves membership of the code's support edge. -/
def SupportNeutralAt
    (recovery : ClosureRecoveryFaceArc rebaseCircuit)
    (position : Fin rebaseCircuit.arcLength) : Prop :=
  recovery.edge.1 ∈ recovery.channel.edges
      ((rebaseCircuit.first :: rebaseCircuit.rest).get position).source ↔
    recovery.edge.1 ∈ recovery.channel.edges
      ((rebaseCircuit.first :: rebaseCircuit.rest).get position).target

@[simp]
theorem mem_gainPositions_iff
    (recovery : ClosureRecoveryFaceArc rebaseCircuit)
    (position : Fin rebaseCircuit.arcLength) :
    position ∈ recovery.gainPositions ↔
      recovery.edge.1 ∉ recovery.channel.edges
          ((rebaseCircuit.first :: rebaseCircuit.rest).get position).source ∧
        recovery.edge.1 ∈ recovery.channel.edges
          ((rebaseCircuit.first :: rebaseCircuit.rest).get position).target := by
  classical
  simp [gainPositions]

@[simp]
theorem mem_lossPositions_iff
    (recovery : ClosureRecoveryFaceArc rebaseCircuit)
    (position : Fin rebaseCircuit.arcLength) :
    position ∈ recovery.lossPositions ↔
      recovery.edge.1 ∈ recovery.channel.edges
          ((rebaseCircuit.first :: rebaseCircuit.rest).get position).source ∧
        recovery.edge.1 ∉ recovery.channel.edges
          ((rebaseCircuit.first :: rebaseCircuit.rest).get position).target := by
  classical
  simp [lossPositions]

/-- The stored restoring position belongs to the complete gain carrier. -/
theorem restoringPosition_mem_gainPositions
    (recovery : ClosureRecoveryFaceArc rebaseCircuit) :
    recovery.restoringPosition ∈ recovery.gainPositions := by
  rw [recovery.mem_gainPositions_iff]
  rw [recovery.get_restoringPosition]
  exact ⟨recovery.edge_not_mem_recoverySource,
    recovery.edge_mem_recoveryTarget⟩

/-- Gain and loss positions for one channel/edge code are disjoint. -/
theorem disjoint_gainPositions_lossPositions
    (recovery : ClosureRecoveryFaceArc rebaseCircuit) :
    Disjoint recovery.gainPositions recovery.lossPositions := by
  rw [Finset.disjoint_left]
  intro position hgain hloss
  have hgain' := (recovery.mem_gainPositions_iff position).mp hgain
  have hloss' := (recovery.mem_lossPositions_iff position).mp hloss
  exact hgain'.1 hloss'.1

/-- In particular, the restoring gain is not itself a loss. -/
theorem restoringPosition_not_mem_lossPositions
    (recovery : ClosureRecoveryFaceArc rebaseCircuit) :
    recovery.restoringPosition ∉ recovery.lossPositions := by
  exact Finset.disjoint_left.mp recovery.disjoint_gainPositions_lossPositions
    recovery.restoringPosition_mem_gainPositions

/-- Cyclic support conservation gives exactly as many gains as losses for
every recovery channel/edge code. -/
theorem card_gainPositions_eq_card_lossPositions
    (recovery : ClosureRecoveryFaceArc rebaseCircuit) :
    recovery.gainPositions.card = recovery.lossPositions.card := by
  classical
  let displayed := rebaseCircuit.first :: rebaseCircuit.rest
  let property := fun state : CrossCentralExactFaceCutState graphData
      (baseData.rotationOrderedData graphData minimal.spherical.cubic
        minimal.vertexRotationCyclic) =>
    recovery.edge.1 ∈ recovery.channel.edges state
  let gainTest := fun arc :
      CrossCentralExactFaceCertifiedRebaseArc graphData minimal baseData =>
    decide (¬ property arc.source ∧ property arc.target)
  let lossTest := fun arc :
      CrossCentralExactFaceCertifiedRebaseArc graphData minimal baseData =>
    decide (property arc.source ∧ ¬ property arc.target)
  have hbalanceRaw :=
    GoertzelV24RebaseFaceCircuit.cyclic_gain_count_eq_loss_count
      CrossCentralExactFaceCertifiedRebaseArc.source
      CrossCentralExactFaceCertifiedRebaseArc.target property
      rebaseCircuit.first rebaseCircuit.rest rebaseCircuit.consecutive
      rebaseCircuit.closing
  have hbalance : (displayed.filter gainTest).length =
      (displayed.filter lossTest).length := by
    simpa [displayed, gainTest, lossTest, property] using hbalanceRaw
  have hgainSet : recovery.gainPositions =
      Finset.univ.filter fun position : Fin rebaseCircuit.arcLength =>
        gainTest ((rebaseCircuit.first :: rebaseCircuit.rest).get
          position) := by
    ext position
    rw [recovery.mem_gainPositions_iff]
    rw [Finset.mem_filter]
    simp only [Finset.mem_univ, true_and]
    change (¬ property
          ((rebaseCircuit.first :: rebaseCircuit.rest).get position).source ∧
        property
          ((rebaseCircuit.first :: rebaseCircuit.rest).get position).target) ↔
      gainTest ((rebaseCircuit.first :: rebaseCircuit.rest).get
        position) = true
    simp [gainTest]
  have hlossSet : recovery.lossPositions =
      Finset.univ.filter fun position : Fin rebaseCircuit.arcLength =>
        lossTest ((rebaseCircuit.first :: rebaseCircuit.rest).get
          position) := by
    ext position
    rw [recovery.mem_lossPositions_iff]
    rw [Finset.mem_filter]
    simp only [Finset.mem_univ, true_and]
    change (property
          ((rebaseCircuit.first :: rebaseCircuit.rest).get position).source ∧
        ¬ property
          ((rebaseCircuit.first :: rebaseCircuit.rest).get position).target) ↔
      lossTest ((rebaseCircuit.first :: rebaseCircuit.rest).get
        position) = true
    simp [lossTest]
  have hgain : recovery.gainPositions.card =
      (displayed.filter gainTest).length := by
    rw [hgainSet]
    change (Finset.univ.filter fun position :
        Fin (rebaseCircuit.first :: rebaseCircuit.rest).length =>
      gainTest ((rebaseCircuit.first :: rebaseCircuit.rest).get
        position)).card =
      ((rebaseCircuit.first :: rebaseCircuit.rest).filter gainTest).length
    exact
      GoertzelV24RebaseFaceCircuit.card_filter_univ_get_eq_length_filter
        (rebaseCircuit.first :: rebaseCircuit.rest) gainTest
  have hloss : recovery.lossPositions.card =
      (displayed.filter lossTest).length := by
    rw [hlossSet]
    change (Finset.univ.filter fun position :
        Fin (rebaseCircuit.first :: rebaseCircuit.rest).length =>
      lossTest ((rebaseCircuit.first :: rebaseCircuit.rest).get
        position)).card =
      ((rebaseCircuit.first :: rebaseCircuit.rest).filter lossTest).length
    exact
      GoertzelV24RebaseFaceCircuit.card_filter_univ_get_eq_length_filter
        (rebaseCircuit.first :: rebaseCircuit.rest) lossTest
  rw [hgain, hloss]
  exact hbalance

/-- Every recovery code has a nonempty finite loss carrier. -/
theorem lossPositions_nonempty
    (recovery : ClosureRecoveryFaceArc rebaseCircuit) :
    recovery.lossPositions.Nonempty := by
  rw [← Finset.card_pos, ← recovery.card_gainPositions_eq_card_lossPositions]
  exact Finset.card_pos.mpr
    ⟨recovery.restoringPosition,
      recovery.restoringPosition_mem_gainPositions⟩

/-- Outside both transition carriers, support membership is unchanged by
the displayed rebase arc. -/
theorem support_mem_iff_of_not_mem_gainPositions_of_not_mem_lossPositions
    (recovery : ClosureRecoveryFaceArc rebaseCircuit)
    (position : Fin rebaseCircuit.arcLength)
    (hgain : position ∉ recovery.gainPositions)
    (hloss : position ∉ recovery.lossPositions) :
    recovery.edge.1 ∈ recovery.channel.edges
          ((rebaseCircuit.first :: rebaseCircuit.rest).get position).source ↔
      recovery.edge.1 ∈ recovery.channel.edges
          ((rebaseCircuit.first :: rebaseCircuit.rest).get position).target := by
  constructor
  · intro hsource
    by_contra htarget
    exact hloss ((recovery.mem_lossPositions_iff position).mpr
      ⟨hsource, htarget⟩)
  · intro htarget
    by_contra hsource
    exact hgain ((recovery.mem_gainPositions_iff position).mpr
      ⟨hsource, htarget⟩)

/-- If a recovery code has one loss position, then its stored restoring
position is its unique gain position. -/
theorem gainPositions_eq_singleton_restoring_of_lossPositions_eq_singleton
    (recovery : ClosureRecoveryFaceArc rebaseCircuit)
    {position : Fin rebaseCircuit.arcLength}
    (hloss : recovery.lossPositions = {position}) :
    recovery.gainPositions = {recovery.restoringPosition} := by
  classical
  have hlossCard : recovery.lossPositions.card = 1 := by simp [hloss]
  have hgainCard : recovery.gainPositions.card = 1 := by
    rw [recovery.card_gainPositions_eq_card_lossPositions, hlossCard]
  rcases Finset.card_eq_one.mp hgainCard with ⟨gain, hgain⟩
  have hrestore := recovery.restoringPosition_mem_gainPositions
  rw [hgain] at hrestore
  have hrestoreEq : recovery.restoringPosition = gain := by
    simpa using hrestore
  have hgainEq : gain = recovery.restoringPosition := hrestoreEq.symm
  simpa [hgainEq] using hgain

end ClosureRecoveryFaceArc

namespace ClosureRecoveryComplementLoss

variable {rebaseCircuit :
  CrossCentralExactFaceCertifiedRebaseCircuit graphData minimal baseData}
  {recovery : ClosureRecoveryFaceArc rebaseCircuit}

/-- The first displayed position of a balancing loss arc. -/
noncomputable def lossPosition
    (loss : ClosureRecoveryComplementLoss rebaseCircuit recovery) :
    Fin rebaseCircuit.arcLength := by
  classical
  exact
    ⟨(rebaseCircuit.first :: rebaseCircuit.rest).idxOf loss.lossArc,
      by
        rw [CrossCentralExactFaceCertifiedRebaseCircuit.arcLength]
        exact List.idxOf_lt_length_iff.mpr loss.lossArc_mem_displayed⟩

/-- Reading the rebase circuit at the loss position recovers the stored
loss arc. -/
@[simp] theorem get_lossPosition
    (loss : ClosureRecoveryComplementLoss rebaseCircuit recovery) :
    (rebaseCircuit.first :: rebaseCircuit.rest).get loss.lossPosition =
      loss.lossArc := by
  classical
  apply List.idxOf_get

/-- The balancing loss position differs from the restoring gain position
that it balances. -/
theorem lossPosition_ne_restoringPosition
    (loss : ClosureRecoveryComplementLoss rebaseCircuit recovery) :
    loss.lossPosition ≠ recovery.restoringPosition := by
  intro hposition
  apply loss.lossArc_ne_recoveryArc
  calc
    loss.lossArc =
        (rebaseCircuit.first :: rebaseCircuit.rest).get
          loss.lossPosition := loss.get_lossPosition.symm
    _ = (rebaseCircuit.first :: rebaseCircuit.rest).get
          recovery.restoringPosition := by rw [hposition]
    _ = recovery.recoveryArc := recovery.get_restoringPosition

/-- Every stored balancing loss lies in the complete loss-position
carrier of its recovery code. -/
theorem lossPosition_mem_lossPositions
    (loss : ClosureRecoveryComplementLoss rebaseCircuit recovery) :
    loss.lossPosition ∈ recovery.lossPositions := by
  rw [recovery.mem_lossPositions_iff]
  rw [loss.get_lossPosition]
  exact ⟨loss.lossArc_source_mem, loss.lossArc_target_not_mem⟩

end ClosureRecoveryComplementLoss

namespace ClosureRecoveryFaceCircuit

variable {rebaseCircuit :
  CrossCentralExactFaceCertifiedRebaseCircuit graphData minimal baseData}

/-- Every displayed recovery occurrence has its restoring position in the
claimed-position image. -/
theorem restoringPosition_mem_claimedRebasePositions_of_mem
    (circuit : ClosureRecoveryFaceCircuit rebaseCircuit)
    (recovery : ClosureRecoveryFaceArc rebaseCircuit)
    (hrecovery : recovery ∈ circuit.first :: circuit.rest) :
    recovery.restoringPosition ∈ circuit.claimedRebasePositions := by
  rcases List.mem_iff_get.mp hrecovery with ⟨position, hposition⟩
  rw [circuit.mem_claimedRebasePositions_iff]
  let recoveryPosition : Fin circuit.arcLength :=
    Fin.cast (by rfl) position
  refine ⟨recoveryPosition, ?_⟩
  have hdependency : circuit.dependencyAt recoveryPosition = recovery := by
    simpa [recoveryPosition, dependencyAt] using hposition
  simp [restoringPositionAt, hdependency]

/-- Every position in the complete loss carrier either lies in the
unclaimed rebase complement or is the restoring gain of a different
recovery occurrence. -/
theorem lossPosition_mem_unclaimed_or_eq_other_restoring
    (circuit : ClosureRecoveryFaceCircuit rebaseCircuit)
    (recoveryPosition : Fin circuit.arcLength)
    (position : Fin rebaseCircuit.arcLength)
    (hloss : position ∈
      (circuit.dependencyAt recoveryPosition).lossPositions) :
    position ∈ circuit.unclaimedRebasePositions ∨
      ∃ otherPosition : Fin circuit.arcLength,
        otherPosition ≠ recoveryPosition ∧
          circuit.restoringPositionAt otherPosition = position ∧
          (rebaseCircuit.first :: rebaseCircuit.rest).get position =
            (circuit.dependencyAt otherPosition).recoveryArc := by
  classical
  by_cases hunclaimed : position ∈ circuit.unclaimedRebasePositions
  · exact Or.inl hunclaimed
  · right
    have hnotAll : ¬ ∀ otherPosition : Fin circuit.arcLength,
        circuit.restoringPositionAt otherPosition ≠ position := by
      intro hall
      exact hunclaimed
        ((circuit.mem_unclaimedRebasePositions_iff position).mpr hall)
    push Not at hnotAll
    rcases hnotAll with ⟨otherPosition, hotherPosition⟩
    have hne : otherPosition ≠ recoveryPosition := by
      intro heq
      subst otherPosition
      have hrestore :
          (circuit.dependencyAt recoveryPosition).restoringPosition =
            position := by
        simpa [restoringPositionAt] using hotherPosition
      rw [← hrestore] at hloss
      exact
        (circuit.dependencyAt
          recoveryPosition).restoringPosition_not_mem_lossPositions hloss
    have harc :
        (rebaseCircuit.first :: rebaseCircuit.rest).get position =
          (circuit.dependencyAt otherPosition).recoveryArc := by
      calc
        (rebaseCircuit.first :: rebaseCircuit.rest).get position =
            (rebaseCircuit.first :: rebaseCircuit.rest).get
              (circuit.dependencyAt otherPosition).restoringPosition := by
          rw [← hotherPosition]
          rfl
        _ = (circuit.dependencyAt otherPosition).recoveryArc :=
          (circuit.dependencyAt otherPosition).get_restoringPosition
    exact ⟨otherPosition, hne, hotherPosition, harc⟩

/-- A complement loss either occupies an unclaimed rebase position or is
the restoring gain of a different recovery occurrence. -/
theorem complementLoss_position_mem_unclaimed_or_eq_other_restoring
    (circuit : ClosureRecoveryFaceCircuit rebaseCircuit)
    (recoveryPosition : Fin circuit.arcLength)
    (loss : ClosureRecoveryComplementLoss rebaseCircuit
      (circuit.dependencyAt recoveryPosition)) :
    loss.lossPosition ∈ circuit.unclaimedRebasePositions ∨
      ∃ otherPosition : Fin circuit.arcLength,
        otherPosition ≠ recoveryPosition ∧
          circuit.restoringPositionAt otherPosition = loss.lossPosition ∧
          loss.lossArc =
            (circuit.dependencyAt otherPosition).recoveryArc := by
  rcases circuit.lossPosition_mem_unclaimed_or_eq_other_restoring
      recoveryPosition loss.lossPosition loss.lossPosition_mem_lossPositions with
    hunclaimed | ⟨otherPosition, hne, hposition, harc⟩
  · exact Or.inl hunclaimed
  · right
    exact ⟨otherPosition, hne, hposition,
      loss.get_lossPosition.symm.trans harc⟩

/-- Every loss position for the first code of a recovery digon is either
unclaimed or displays the second restoring arc. -/
theorem lossPosition_first_mem_unclaimed_or_get_eq_second_of_rest_eq_singleton
    (circuit : ClosureRecoveryFaceCircuit rebaseCircuit)
    (second : ClosureRecoveryFaceArc rebaseCircuit)
    (hrest : circuit.rest = [second])
    (position : Fin rebaseCircuit.arcLength)
    (hloss : position ∈ circuit.first.lossPositions) :
    position ∈ circuit.unclaimedRebasePositions ∨
      (rebaseCircuit.first :: rebaseCircuit.rest).get position =
        second.recoveryArc := by
  classical
  by_cases hunclaimed : position ∈ circuit.unclaimedRebasePositions
  · exact Or.inl hunclaimed
  · right
    have hclaimed : position ∈ circuit.claimedRebasePositions := by
      simpa [unclaimedRebasePositions] using hunclaimed
    rcases (circuit.mem_claimedRebasePositions_iff position).mp hclaimed with
      ⟨otherPosition, hotherPosition⟩
    have harc : (rebaseCircuit.first :: rebaseCircuit.rest).get position =
        (circuit.dependencyAt otherPosition).recoveryArc := by
      calc
        (rebaseCircuit.first :: rebaseCircuit.rest).get position =
            (rebaseCircuit.first :: rebaseCircuit.rest).get
              (circuit.dependencyAt otherPosition).restoringPosition := by
          rw [← hotherPosition]
          rfl
        _ = (circuit.dependencyAt otherPosition).recoveryArc :=
          (circuit.dependencyAt otherPosition).get_restoringPosition
    have hmem : circuit.dependencyAt otherPosition = circuit.first ∨
        circuit.dependencyAt otherPosition = second := by
      simpa [hrest] using circuit.dependencyAt_mem otherPosition
    rcases hmem with hfirst | hsecond
    · have hloss' := (circuit.first.mem_lossPositions_iff position).mp hloss
      rw [harc, hfirst] at hloss'
      exact False.elim
        (circuit.first.edge_not_mem_recoverySource hloss'.1)
    · simpa [hsecond] using harc

/-- Every loss position for the second code of a recovery digon is either
unclaimed or displays the first restoring arc. -/
theorem lossPosition_second_mem_unclaimed_or_get_eq_first_of_rest_eq_singleton
    (circuit : ClosureRecoveryFaceCircuit rebaseCircuit)
    (second : ClosureRecoveryFaceArc rebaseCircuit)
    (hrest : circuit.rest = [second])
    (position : Fin rebaseCircuit.arcLength)
    (hloss : position ∈ second.lossPositions) :
    position ∈ circuit.unclaimedRebasePositions ∨
      (rebaseCircuit.first :: rebaseCircuit.rest).get position =
        circuit.first.recoveryArc := by
  classical
  by_cases hunclaimed : position ∈ circuit.unclaimedRebasePositions
  · exact Or.inl hunclaimed
  · right
    have hclaimed : position ∈ circuit.claimedRebasePositions := by
      simpa [unclaimedRebasePositions] using hunclaimed
    rcases (circuit.mem_claimedRebasePositions_iff position).mp hclaimed with
      ⟨otherPosition, hotherPosition⟩
    have harc : (rebaseCircuit.first :: rebaseCircuit.rest).get position =
        (circuit.dependencyAt otherPosition).recoveryArc := by
      calc
        (rebaseCircuit.first :: rebaseCircuit.rest).get position =
            (rebaseCircuit.first :: rebaseCircuit.rest).get
              (circuit.dependencyAt otherPosition).restoringPosition := by
          rw [← hotherPosition]
          rfl
        _ = (circuit.dependencyAt otherPosition).recoveryArc :=
          (circuit.dependencyAt otherPosition).get_restoringPosition
    have hmem : circuit.dependencyAt otherPosition = circuit.first ∨
        circuit.dependencyAt otherPosition = second := by
      simpa [hrest] using circuit.dependencyAt_mem otherPosition
    rcases hmem with hfirst | hsecond
    · simpa [hfirst] using harc
    · have hloss' := (second.mem_lossPositions_iff position).mp hloss
      rw [harc, hsecond] at hloss'
      exact False.elim (second.edge_not_mem_recoverySource hloss'.1)

/-- If the underlying rebase circuit is shortest, the claimed alternative
for a first-code loss is the unique second restoring position itself. -/
theorem lossPosition_first_mem_unclaimed_or_eq_secondRestoring_of_rest_eq_singleton
    (circuit : ClosureRecoveryFaceCircuit rebaseCircuit)
    (second : ClosureRecoveryFaceArc rebaseCircuit)
    (hrest : circuit.rest = [second])
    (hrebaseMinimal : rebaseCircuit.IsLengthMinimal)
    (position : Fin rebaseCircuit.arcLength)
    (hloss : position ∈ circuit.first.lossPositions) :
    position ∈ circuit.unclaimedRebasePositions ∨
      position = second.restoringPosition := by
  rcases
      circuit.lossPosition_first_mem_unclaimed_or_get_eq_second_of_rest_eq_singleton
        second hrest position hloss with hunclaimed | harc
  · exact Or.inl hunclaimed
  · right
    have hinjective : Function.Injective
        ((rebaseCircuit.first :: rebaseCircuit.rest).get) :=
      List.nodup_iff_injective_get.mp hrebaseMinimal.displayedArcs_nodup
    apply hinjective
    exact harc.trans second.get_restoringPosition.symm

/-- The second-code loss carrier has the symmetric exact positional
alternative on a shortest rebase circuit. -/
theorem lossPosition_second_mem_unclaimed_or_eq_firstRestoring_of_rest_eq_singleton
    (circuit : ClosureRecoveryFaceCircuit rebaseCircuit)
    (second : ClosureRecoveryFaceArc rebaseCircuit)
    (hrest : circuit.rest = [second])
    (hrebaseMinimal : rebaseCircuit.IsLengthMinimal)
    (position : Fin rebaseCircuit.arcLength)
    (hloss : position ∈ second.lossPositions) :
    position ∈ circuit.unclaimedRebasePositions ∨
      position = circuit.first.restoringPosition := by
  rcases
      circuit.lossPosition_second_mem_unclaimed_or_get_eq_first_of_rest_eq_singleton
        second hrest position hloss with hunclaimed | harc
  · exact Or.inl hunclaimed
  · right
    have hinjective : Function.Injective
        ((rebaseCircuit.first :: rebaseCircuit.rest).get) :=
      List.nodup_iff_injective_get.mp hrebaseMinimal.displayedArcs_nodup
    apply hinjective
    exact harc.trans circuit.first.get_restoringPosition.symm

/-- The complete first-code loss carrier of a recovery digon either meets
the unclaimed complement or is the singleton second restoring position. -/
theorem lossPositions_first_inter_unclaimed_nonempty_or_eq_singleton_secondRestoring
    (circuit : ClosureRecoveryFaceCircuit rebaseCircuit)
    (second : ClosureRecoveryFaceArc rebaseCircuit)
    (hrest : circuit.rest = [second])
    (hrebaseMinimal : rebaseCircuit.IsLengthMinimal) :
    (circuit.first.lossPositions ∩
        circuit.unclaimedRebasePositions).Nonempty ∨
      circuit.first.lossPositions = {second.restoringPosition} := by
  apply GoertzelV24RebaseFaceCircuit.inter_nonempty_or_eq_singleton_of_mem_or_eq
    circuit.first.lossPositions circuit.unclaimedRebasePositions
      second.restoringPosition circuit.first.lossPositions_nonempty
  intro position hloss
  exact
    circuit.lossPosition_first_mem_unclaimed_or_eq_secondRestoring_of_rest_eq_singleton
      second hrest hrebaseMinimal position hloss

/-- The second-code loss carrier has the symmetric complete-set
dichotomy. -/
theorem lossPositions_second_inter_unclaimed_nonempty_or_eq_singleton_firstRestoring
    (circuit : ClosureRecoveryFaceCircuit rebaseCircuit)
    (second : ClosureRecoveryFaceArc rebaseCircuit)
    (hrest : circuit.rest = [second])
    (hrebaseMinimal : rebaseCircuit.IsLengthMinimal) :
    (second.lossPositions ∩
        circuit.unclaimedRebasePositions).Nonempty ∨
      second.lossPositions = {circuit.first.restoringPosition} := by
  apply GoertzelV24RebaseFaceCircuit.inter_nonempty_or_eq_singleton_of_mem_or_eq
    second.lossPositions circuit.unclaimedRebasePositions
      circuit.first.restoringPosition second.lossPositions_nonempty
  intro position hloss
  exact
    circuit.lossPosition_second_mem_unclaimed_or_eq_firstRestoring_of_rest_eq_singleton
      second hrest hrebaseMinimal position hloss

/-- On a shortest underlying rebase circuit, every recovery digon has one
of two genuine complement losses, or else the two codes form an exact
singleton gain/loss swap. -/
theorem IsDigon.lossCarrier_inter_unclaimed_or_exact_swap
    {circuit : ClosureRecoveryFaceCircuit rebaseCircuit}
    (hdigon : circuit.IsDigon)
    (hrebaseMinimal : rebaseCircuit.IsLengthMinimal) :
    ∃ second : ClosureRecoveryFaceArc rebaseCircuit,
      circuit.rest = [second] ∧
        ((circuit.first.lossPositions ∩
            circuit.unclaimedRebasePositions).Nonempty ∨
          (second.lossPositions ∩
            circuit.unclaimedRebasePositions).Nonempty ∨
          (circuit.first.lossPositions = {second.restoringPosition} ∧
            second.lossPositions = {circuit.first.restoringPosition} ∧
            circuit.first.gainPositions =
              {circuit.first.restoringPosition} ∧
            second.gainPositions = {second.restoringPosition})) := by
  rcases hdigon with
    ⟨second, hrest, _hfirstSecond, _hsecondFirst⟩
  refine ⟨second, hrest, ?_⟩
  rcases
      circuit.lossPositions_first_inter_unclaimed_nonempty_or_eq_singleton_secondRestoring
        second hrest hrebaseMinimal with hfirst | hfirst
  · exact Or.inl hfirst
  · rcases
        circuit.lossPositions_second_inter_unclaimed_nonempty_or_eq_singleton_firstRestoring
          second hrest hrebaseMinimal with hsecond | hsecond
    · exact Or.inr (Or.inl hsecond)
    · right
      right
      exact ⟨hfirst, hsecond,
        circuit.first.gainPositions_eq_singleton_restoring_of_lossPositions_eq_singleton
          hfirst,
        second.gainPositions_eq_singleton_restoring_of_lossPositions_eq_singleton
          hsecond⟩

/-- In the exact-swap branch, every unclaimed rebase arc preserves the
support status of both recovery codes. -/
theorem support_neutral_on_unclaimed_of_exact_digon_swap
    (circuit : ClosureRecoveryFaceCircuit rebaseCircuit)
    (second : ClosureRecoveryFaceArc rebaseCircuit)
    (hrest : circuit.rest = [second])
    (hfirstLoss :
      circuit.first.lossPositions = {second.restoringPosition})
    (hsecondLoss :
      second.lossPositions = {circuit.first.restoringPosition})
    (position : Fin rebaseCircuit.arcLength)
    (hunclaimed : position ∈ circuit.unclaimedRebasePositions) :
    circuit.first.SupportNeutralAt position ∧
      second.SupportNeutralAt position := by
  have hfirstClaimed : circuit.first.restoringPosition ∈
      circuit.claimedRebasePositions :=
    circuit.restoringPosition_mem_claimedRebasePositions_of_mem
      circuit.first (by simp)
  have hsecondClaimed : second.restoringPosition ∈
      circuit.claimedRebasePositions :=
    circuit.restoringPosition_mem_claimedRebasePositions_of_mem
      second (by simp [hrest])
  have hnotClaimed : position ∉ circuit.claimedRebasePositions := by
    simpa [unclaimedRebasePositions] using hunclaimed
  have hfirstNe : position ≠ circuit.first.restoringPosition := by
    intro heq
    exact hnotClaimed (heq ▸ hfirstClaimed)
  have hsecondNe : position ≠ second.restoringPosition := by
    intro heq
    exact hnotClaimed (heq ▸ hsecondClaimed)
  have hfirstGain :=
    circuit.first.gainPositions_eq_singleton_restoring_of_lossPositions_eq_singleton
      hfirstLoss
  have hsecondGain :=
    second.gainPositions_eq_singleton_restoring_of_lossPositions_eq_singleton
      hsecondLoss
  have hfirstGainOff : position ∉ circuit.first.gainPositions := by
    simp [hfirstGain, hfirstNe]
  have hfirstLossOff : position ∉ circuit.first.lossPositions := by
    simp [hfirstLoss, hsecondNe]
  have hsecondGainOff : position ∉ second.gainPositions := by
    simp [hsecondGain, hsecondNe]
  have hsecondLossOff : position ∉ second.lossPositions := by
    simp [hsecondLoss, hfirstNe]
  constructor
  · simpa [ClosureRecoveryFaceArc.SupportNeutralAt] using
      circuit.first.support_mem_iff_of_not_mem_gainPositions_of_not_mem_lossPositions
        position hfirstGainOff hfirstLossOff
  · simpa [ClosureRecoveryFaceArc.SupportNeutralAt] using
      second.support_mem_iff_of_not_mem_gainPositions_of_not_mem_lossPositions
        position hsecondGainOff hsecondLossOff

/-- A shortest recovery digon either loses one of its two codes on an
unclaimed rebase position, or its codes make an exact two-position swap
and every unclaimed position is neutral for both codes. -/
theorem IsDigon.lossCarrier_inter_unclaimed_or_exact_swap_neutral
    {circuit : ClosureRecoveryFaceCircuit rebaseCircuit}
    (hdigon : circuit.IsDigon)
    (hrebaseMinimal : rebaseCircuit.IsLengthMinimal) :
    ∃ second : ClosureRecoveryFaceArc rebaseCircuit,
      circuit.rest = [second] ∧
        ((circuit.first.lossPositions ∩
            circuit.unclaimedRebasePositions).Nonempty ∨
          (second.lossPositions ∩
            circuit.unclaimedRebasePositions).Nonempty ∨
          (circuit.first.lossPositions = {second.restoringPosition} ∧
            second.lossPositions = {circuit.first.restoringPosition} ∧
            circuit.first.gainPositions =
              {circuit.first.restoringPosition} ∧
            second.gainPositions = {second.restoringPosition} ∧
            ∀ position : Fin rebaseCircuit.arcLength,
              position ∈ circuit.unclaimedRebasePositions →
                circuit.first.SupportNeutralAt position ∧
                  second.SupportNeutralAt position)) := by
  rcases hdigon.lossCarrier_inter_unclaimed_or_exact_swap hrebaseMinimal with
    ⟨second, hrest, hfirst | hsecond | hexact⟩
  · exact ⟨second, hrest, Or.inl hfirst⟩
  · exact ⟨second, hrest, Or.inr (Or.inl hsecond)⟩
  · rcases hexact with
      ⟨hfirstLoss, hsecondLoss, hfirstGain, hsecondGain⟩
    refine ⟨second, hrest, Or.inr (Or.inr
      ⟨hfirstLoss, hsecondLoss, hfirstGain, hsecondGain, ?_⟩)⟩
    intro position hunclaimed
    exact circuit.support_neutral_on_unclaimed_of_exact_digon_swap
      second hrest hfirstLoss hsecondLoss position hunclaimed

/-- In a recovery digon, a loss balancing the first gain is either
unclaimed or is exactly the second restoring gain. -/
theorem complementLoss_first_mem_unclaimed_or_eq_second_of_rest_eq_singleton
    (circuit : ClosureRecoveryFaceCircuit rebaseCircuit)
    (second : ClosureRecoveryFaceArc rebaseCircuit)
    (hrest : circuit.rest = [second])
    (loss : ClosureRecoveryComplementLoss rebaseCircuit circuit.first) :
    loss.lossPosition ∈ circuit.unclaimedRebasePositions ∨
      loss.lossArc = second.recoveryArc := by
  classical
  by_cases hunclaimed :
      loss.lossPosition ∈ circuit.unclaimedRebasePositions
  · exact Or.inl hunclaimed
  · right
    have hclaimed :
        loss.lossPosition ∈ circuit.claimedRebasePositions := by
      simpa [unclaimedRebasePositions] using hunclaimed
    rcases (circuit.mem_claimedRebasePositions_iff
        loss.lossPosition).mp hclaimed with
      ⟨otherPosition, hotherPosition⟩
    have harc : loss.lossArc =
        (circuit.dependencyAt otherPosition).recoveryArc := by
      calc
        loss.lossArc =
            (rebaseCircuit.first :: rebaseCircuit.rest).get
              loss.lossPosition := loss.get_lossPosition.symm
        _ = (rebaseCircuit.first :: rebaseCircuit.rest).get
              (circuit.dependencyAt otherPosition).restoringPosition := by
          rw [← hotherPosition]
          rfl
        _ = (circuit.dependencyAt otherPosition).recoveryArc :=
          (circuit.dependencyAt otherPosition).get_restoringPosition
    have hmem : circuit.dependencyAt otherPosition = circuit.first ∨
        circuit.dependencyAt otherPosition = second := by
      simpa [hrest] using circuit.dependencyAt_mem otherPosition
    rcases hmem with hfirst | hsecond
    · exfalso
      apply loss.lossArc_ne_recoveryArc
      simpa [hfirst] using harc
    · simpa [hsecond] using harc

/-- Symmetrically, a loss balancing the second gain of a recovery digon
is either unclaimed or is exactly the first restoring gain. -/
theorem complementLoss_second_mem_unclaimed_or_eq_first_of_rest_eq_singleton
    (circuit : ClosureRecoveryFaceCircuit rebaseCircuit)
    (second : ClosureRecoveryFaceArc rebaseCircuit)
    (hrest : circuit.rest = [second])
    (loss : ClosureRecoveryComplementLoss rebaseCircuit second) :
    loss.lossPosition ∈ circuit.unclaimedRebasePositions ∨
      loss.lossArc = circuit.first.recoveryArc := by
  classical
  by_cases hunclaimed :
      loss.lossPosition ∈ circuit.unclaimedRebasePositions
  · exact Or.inl hunclaimed
  · right
    have hclaimed :
        loss.lossPosition ∈ circuit.claimedRebasePositions := by
      simpa [unclaimedRebasePositions] using hunclaimed
    rcases (circuit.mem_claimedRebasePositions_iff
        loss.lossPosition).mp hclaimed with
      ⟨otherPosition, hotherPosition⟩
    have harc : loss.lossArc =
        (circuit.dependencyAt otherPosition).recoveryArc := by
      calc
        loss.lossArc =
            (rebaseCircuit.first :: rebaseCircuit.rest).get
              loss.lossPosition := loss.get_lossPosition.symm
        _ = (rebaseCircuit.first :: rebaseCircuit.rest).get
              (circuit.dependencyAt otherPosition).restoringPosition := by
          rw [← hotherPosition]
          rfl
        _ = (circuit.dependencyAt otherPosition).recoveryArc :=
          (circuit.dependencyAt otherPosition).get_restoringPosition
    have hmem : circuit.dependencyAt otherPosition = circuit.first ∨
        circuit.dependencyAt otherPosition = second := by
      simpa [hrest] using circuit.dependencyAt_mem otherPosition
    rcases hmem with hfirst | hsecond
    · simpa [hfirst] using harc
    · exfalso
      apply loss.lossArc_ne_recoveryArc
      simpa [hsecond] using harc

/-- Every recovery digon therefore admits two balancing losses, each of
which either enters the unclaimed carrier or forms the exact two-gain
swap with the opposite restoring arc. -/
theorem IsDigon.exists_complementLosses_with_unclaimed_or_swap
    {circuit : ClosureRecoveryFaceCircuit rebaseCircuit}
    (hdigon : circuit.IsDigon) :
    ∃ (second : ClosureRecoveryFaceArc rebaseCircuit)
        (firstLoss : ClosureRecoveryComplementLoss rebaseCircuit
          circuit.first)
        (secondLoss : ClosureRecoveryComplementLoss rebaseCircuit second),
      circuit.rest = [second] ∧
        (firstLoss.lossPosition ∈ circuit.unclaimedRebasePositions ∨
          firstLoss.lossArc = second.recoveryArc) ∧
        (secondLoss.lossPosition ∈ circuit.unclaimedRebasePositions ∨
          secondLoss.lossArc = circuit.first.recoveryArc) := by
  rcases hdigon with
    ⟨second, hrest, _hfirstSecond, _hsecondFirst⟩
  rcases circuit.first.exists_complementLoss with ⟨firstLoss⟩
  rcases second.exists_complementLoss with ⟨secondLoss⟩
  exact ⟨second, firstLoss, secondLoss, hrest,
    circuit.complementLoss_first_mem_unclaimed_or_eq_second_of_rest_eq_singleton
      second hrest firstLoss,
    circuit.complementLoss_second_mem_unclaimed_or_eq_first_of_rest_eq_singleton
      second hrest secondLoss⟩

end ClosureRecoveryFaceCircuit

end GoertzelV24AdjacentPairInsertion.AdjacentPairData

end

end Mettapedia.GraphTheory.FourColor
