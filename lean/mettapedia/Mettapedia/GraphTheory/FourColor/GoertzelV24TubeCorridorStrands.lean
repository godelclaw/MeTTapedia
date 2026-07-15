import Mettapedia.GraphTheory.FourColor.GoertzelV24TubeRingTransfer

namespace Mettapedia.GraphTheory.FourColor.GoertzelV24TubeRingTransfer

/-- Embed one local ring edge into the shared edge set of a whole corridor. -/
def embedRingEdge {rings : Nat} (ring : Fin rings) :
    TubeRingEdge → TubeCorridorEdge rings
  | .old position => .inl (ring.castSucc, position)
  | .middle edge => .inr (ring, edge)
  | .new position => .inl (ring.succ, position)

theorem embedRingEdge_injective {rings : Nat} (ring : Fin rings) :
    Function.Injective (embedRingEdge ring) := by
  intro left right heq
  cases left with
  | old left =>
      cases right with
      | old right =>
          simp only [embedRingEdge, Sum.inl.injEq, Prod.mk.injEq] at heq
          exact congrArg TubeRingEdge.old heq.2
      | middle right => simp [embedRingEdge] at heq
      | new right =>
          simp only [embedRingEdge, Sum.inl.injEq, Prod.mk.injEq] at heq
          exfalso
          have := congrArg Fin.val heq.1
          simp at this
  | middle left =>
      cases right with
      | old right => simp [embedRingEdge] at heq
      | middle right =>
          simp only [embedRingEdge, Sum.inr.injEq, Prod.mk.injEq] at heq
          exact congrArg TubeRingEdge.middle heq.2
      | new right => simp [embedRingEdge] at heq
  | new left =>
      cases right with
      | old right =>
          simp only [embedRingEdge, Sum.inl.injEq, Prod.mk.injEq] at heq
          exfalso
          have := congrArg Fin.val heq.1
          simp at this
      | middle right => simp [embedRingEdge] at heq
      | new right =>
          simp only [embedRingEdge, Sum.inl.injEq, Prod.mk.injEq] at heq
          exact congrArg TubeRingEdge.new heq.2

/-- The global tracked-edge graph of the normalized tube incidence model.
Its vertices are tube edges; adjacency means sharing an internal split or
merge vertex in some ring while carrying one of the two tracked colors.
Shared frontier edges occur only once. -/
def TubeCorridorTaitColoring.trackedGraph
    {rings : Nat} {start finish : TubeFrontierState}
    (coloring : TubeCorridorTaitColoring rings start finish) :
    SimpleGraph (TubeCorridorEdge rings) where
  Adj left right := ∃ ring localLeft localRight,
    (trackedRingGraph (coloring.frontierState ring.castSucc)
      (coloring.ringChoice ring)).Adj localLeft localRight ∧
    embedRingEdge ring localLeft = left ∧
    embedRingEdge ring localRight = right
  symm := ⟨by
    rintro left right ⟨ring, localLeft, localRight, hadj, rfl, rfl⟩
    exact ⟨ring, localRight, localLeft, hadj.symm, rfl, rfl⟩⟩
  loopless := ⟨by
    rintro edge ⟨ring, localLeft, localRight, hadj, hleft, hright⟩
    apply hadj.ne
    apply embedRingEdge_injective ring
    exact hleft.trans hright.symm⟩

/-- Each local tracked ring graph embeds into the global tracked graph. -/
def TubeCorridorTaitColoring.ringHom
    {rings : Nat} {start finish : TubeFrontierState}
    (coloring : TubeCorridorTaitColoring rings start finish)
    (ring : Fin rings) :
    trackedRingGraph (coloring.frontierState ring.castSucc)
      (coloring.ringChoice ring) →g coloring.trackedGraph where
  toFun := embedRingEdge ring
  map_rel' := by
    intro left right hadj
    exact ⟨ring, left, right, hadj, rfl, rfl⟩

/-- Local two-color reachability remains reachability after gluing rings. -/
theorem TubeCorridorTaitColoring.localReachable_global
    {rings : Nat} {start finish : TubeFrontierState}
    (coloring : TubeCorridorTaitColoring rings start finish)
    (ring : Fin rings) {left right : TubeRingEdge}
    (hreachable :
      (trackedRingGraph (coloring.frontierState ring.castSucc)
        (coloring.ringChoice ring)).Reachable left right) :
    coloring.trackedGraph.Reachable
      (embedRingEdge ring left) (embedRingEdge ring right) :=
  hreachable.map (coloring.ringHom ring)

/-- A successor certificate carries each named terminal across its ring in
the global tracked graph. -/
theorem TubeCorridorTaitColoring.ringTerminal_reachable
    {rings : Nat} {start finish : TubeFrontierState}
    (coloring : TubeCorridorTaitColoring rings start finish)
    (ring : Fin rings) (terminal : Fin 4) :
    coloring.trackedGraph.Reachable
      (.inl (ring.castSucc,
        (coloring.frontierState ring.castSucc).terminal terminal))
      (.inl (ring.succ,
        (coloring.frontierState ring.succ).terminal terminal)) := by
  have hsuccessor := coloring.successor ring
  have hbool :
      trackedRingReachable
        (coloring.frontierState ring.castSucc)
        (coloring.ringChoice ring)
        (.old ((coloring.frontierState ring.castSucc).terminal terminal))
        (.new ((coloring.frontierState ring.succ).terminal terminal)) = true :=
    (hsuccessor.2.2.2.2.2 terminal
      ((coloring.frontierState ring.succ).terminal terminal)).2 rfl
  have hlocal :=
    (trackedRingReachable_eq_true_iff_reachable
      (coloring.frontierState ring.castSucc)
      (coloring.ringChoice ring)
      (.old ((coloring.frontierState ring.castSucc).terminal terminal))
      (.new ((coloring.frontierState ring.succ).terminal terminal))).1 hbool
  exact coloring.localReachable_global ring hlocal

/-- Local terminal paths concatenate through every requested frontier level. -/
theorem TubeCorridorTaitColoring.terminal_reachable_at_level
    {rings : Nat} {start finish : TubeFrontierState}
    (coloring : TubeCorridorTaitColoring rings start finish)
    (terminal : Fin 4) :
    ∀ level : Nat, ∀ hlevel : level ≤ rings,
      coloring.trackedGraph.Reachable
        (.inl (0, (coloring.frontierState 0).terminal terminal))
        (.inl (⟨level, Nat.lt_succ_of_le hlevel⟩,
          (coloring.frontierState
            ⟨level, Nat.lt_succ_of_le hlevel⟩).terminal terminal)) := by
  intro level
  induction level with
  | zero =>
      intro hlevel
      have hzero :
          (⟨0, Nat.lt_succ_of_le hlevel⟩ : Fin (rings + 1)) = 0 :=
        Fin.ext rfl
      rw [hzero]
  | succ level ih =>
      intro hlevel
      have hlt : level < rings := Nat.lt_of_succ_le hlevel
      let ring : Fin rings := ⟨level, hlt⟩
      have hprefix := ih (Nat.le_of_lt hlt)
      have hstep := coloring.ringTerminal_reachable ring terminal
      simpa [ring] using hprefix.trans hstep

/-- Each named terminal survives from the first to the last frontier. -/
theorem TubeCorridorTaitColoring.terminal_reachable
    {rings : Nat} {start finish : TubeFrontierState}
    (coloring : TubeCorridorTaitColoring rings start finish)
    (terminal : Fin 4) :
    coloring.trackedGraph.Reachable
      (.inl (0, start.terminal terminal))
      (.inl (Fin.last rings, finish.terminal terminal)) := by
  have hreach := coloring.terminal_reachable_at_level terminal rings (Nat.le_refl rings)
  rw [coloring.first_state] at hreach
  have hlast :
      (⟨rings, Nat.lt_succ_of_le (Nat.le_refl rings)⟩ : Fin (rings + 1)) =
        Fin.last rings := Fin.ext rfl
  rw [hlast, coloring.last_state] at hreach
  exact hreach

/-- Distinct named source terminals lie in distinct local components. -/
theorem IsTubeRingSuccessor.old_reachable_iff
    {source target : TubeFrontierState} {choice : TubeRingChoice}
    (hsuccessor : IsTubeRingSuccessor source target choice)
    (left right : Fin 4) :
    (trackedRingGraph source choice).Reachable
        (.old (source.terminal left)) (.old (source.terminal right)) ↔
      left = right := by
  rw [← trackedRingReachable_eq_true_iff_reachable]
  exact hsuccessor.2.2.2.2.1 left right

/-- A local component reaches exactly the target position carrying the same
terminal identity. -/
theorem IsTubeRingSuccessor.old_new_reachable_iff
    {source target : TubeFrontierState} {choice : TubeRingChoice}
    (hsuccessor : IsTubeRingSuccessor source target choice)
    (terminal : Fin 4) (position : Fin 5) :
    (trackedRingGraph source choice).Reachable
        (.old (source.terminal terminal)) (.new position) ↔
      target.terminal terminal = position := by
  rw [← trackedRingReachable_eq_true_iff_reachable]
  exact hsuccessor.2.2.2.2.2 terminal position

theorem IsTubeRingSuccessor.old_reachable_unique
    {source target : TubeFrontierState} {choice : TubeRingChoice}
    (hsuccessor : IsTubeRingSuccessor source target choice)
    {left right : Fin 4} {edge : TubeRingEdge}
    (hleft : (trackedRingGraph source choice).Reachable
      (.old (source.terminal left)) edge)
    (hright : (trackedRingGraph source choice).Reachable
      (.old (source.terminal right)) edge) :
    left = right :=
  (hsuccessor.old_reachable_iff left right).1 (hleft.trans hright.symm)

/-- Recover the unique terminal identity at a frontier position, when one is
present. -/
noncomputable def frontierTerminalLabel
    (state : TubeFrontierState) (position : Fin 5) : Option (Fin 4) :=
  if h : ∃ terminal, state.terminal terminal = position then
    some (Classical.choose h)
  else
    none

theorem frontierTerminalLabel_eq_some_iff
    {state : TubeFrontierState} (hinjective : Function.Injective state.terminal)
    (position : Fin 5) (terminal : Fin 4) :
    frontierTerminalLabel state position = some terminal ↔
      state.terminal terminal = position := by
  unfold frontierTerminalLabel
  split_ifs with hexists
  · constructor
    · intro heq
      have hchosen : Classical.choose hexists = terminal := Option.some.inj heq
      rw [← hchosen]
      exact Classical.choose_spec hexists
    · intro hterminal
      have hchosen : Classical.choose hexists = terminal := by
        apply hinjective
        exact (Classical.choose_spec hexists).trans hterminal.symm
      rw [hchosen]
  · constructor
    · simp
    · intro hterminal
      exact False.elim (hexists ⟨terminal, hterminal⟩)

/-- Label a local tracked component by its unique originating terminal. A
closed internal component receives `none`. -/
noncomputable def TubeCorridorTaitColoring.localTerminalLabel
    {rings : Nat} {start finish : TubeFrontierState}
    (coloring : TubeCorridorTaitColoring rings start finish)
    (ring : Fin rings) (edge : TubeRingEdge) : Option (Fin 4) := by
  classical
  exact if h : ∃ terminal,
      (trackedRingGraph (coloring.frontierState ring.castSucc)
        (coloring.ringChoice ring)).Reachable
        (.old ((coloring.frontierState ring.castSucc).terminal terminal)) edge then
    some (Classical.choose h)
  else
    none

theorem TubeCorridorTaitColoring.localTerminalLabel_eq_some_iff
    {rings : Nat} {start finish : TubeFrontierState}
    (coloring : TubeCorridorTaitColoring rings start finish)
    (ring : Fin rings) (edge : TubeRingEdge) (terminal : Fin 4) :
    coloring.localTerminalLabel ring edge = some terminal ↔
      (trackedRingGraph (coloring.frontierState ring.castSucc)
        (coloring.ringChoice ring)).Reachable
        (.old ((coloring.frontierState ring.castSucc).terminal terminal)) edge := by
  unfold localTerminalLabel
  split_ifs with hexists
  · constructor
    · intro heq
      have hchosen : Classical.choose hexists = terminal := Option.some.inj heq
      rw [← hchosen]
      exact Classical.choose_spec hexists
    · intro hterminal
      have hchosen : Classical.choose hexists = terminal :=
        (coloring.successor ring).old_reachable_unique
          (Classical.choose_spec hexists) hterminal
      rw [hchosen]
  · constructor
    · simp
    · intro hterminal
      exact False.elim (hexists ⟨terminal, hterminal⟩)

theorem TubeCorridorTaitColoring.localTerminalLabel_eq_of_adj
    {rings : Nat} {start finish : TubeFrontierState}
    (coloring : TubeCorridorTaitColoring rings start finish)
    (ring : Fin rings) {left right : TubeRingEdge}
    (hadj : (trackedRingGraph (coloring.frontierState ring.castSucc)
      (coloring.ringChoice ring)).Adj left right) :
    coloring.localTerminalLabel ring left =
      coloring.localTerminalLabel ring right := by
  apply Option.ext
  intro terminal
  rw [coloring.localTerminalLabel_eq_some_iff,
    coloring.localTerminalLabel_eq_some_iff]
  exact ⟨fun hreach => hreach.trans hadj.reachable,
    fun hreach => hreach.trans hadj.symm.reachable⟩

/-- A terminal label on every edge of the global corridor. -/
noncomputable def TubeCorridorTaitColoring.terminalLabel
    {rings : Nat} {start finish : TubeFrontierState}
    (coloring : TubeCorridorTaitColoring rings start finish) :
    TubeCorridorEdge rings → Option (Fin 4)
  | .inl (level, position) =>
      frontierTerminalLabel (coloring.frontierState level) position
  | .inr (ring, edge) => coloring.localTerminalLabel ring (.middle edge)

theorem TubeCorridorTaitColoring.localTerminalLabel_eq_terminalLabel_of_tracked
    {rings : Nat} {start finish : TubeFrontierState}
    (coloring : TubeCorridorTaitColoring rings start finish)
    (ring : Fin rings) (edge : TubeRingEdge)
    (htracked : IsTracked (ringColor
      (coloring.frontierState ring.castSucc) (coloring.ringChoice ring) edge)) :
    coloring.localTerminalLabel ring edge =
      coloring.terminalLabel (embedRingEdge ring edge) := by
  have hsuccessor := coloring.successor ring
  cases edge with
  | middle edge => rfl
  | old position =>
      obtain ⟨terminal, hterminal⟩ :=
        (hsuccessor.1.2 position).1 htracked
      calc
        coloring.localTerminalLabel ring (.old position) = some terminal :=
          (coloring.localTerminalLabel_eq_some_iff ring (.old position) terminal).2
            (by
              rw [← hterminal])
        _ = coloring.terminalLabel (embedRingEdge ring (.old position)) := by
          symm
          change frontierTerminalLabel
            (coloring.frontierState ring.castSucc) position = some terminal
          exact (frontierTerminalLabel_eq_some_iff hsuccessor.1.1
            position terminal).2 hterminal
  | new position =>
      have hcolor := hsuccessor.2.2.2.1 position
      have htargetTracked : IsTracked
          ((coloring.frontierState ring.succ).color position) := by
        rw [hcolor]
        exact htracked
      obtain ⟨terminal, hterminal⟩ :=
        (hsuccessor.2.2.1.2 position).1 htargetTracked
      calc
        coloring.localTerminalLabel ring (.new position) = some terminal :=
          (coloring.localTerminalLabel_eq_some_iff ring (.new position) terminal).2
            ((hsuccessor.old_new_reachable_iff terminal position).2 hterminal)
        _ = coloring.terminalLabel (embedRingEdge ring (.new position)) := by
          symm
          change frontierTerminalLabel
            (coloring.frontierState ring.succ) position = some terminal
          exact (frontierTerminalLabel_eq_some_iff hsuccessor.2.2.1.1
            position terminal).2 hterminal

theorem TubeCorridorTaitColoring.terminalLabel_eq_of_adj
    {rings : Nat} {start finish : TubeFrontierState}
    (coloring : TubeCorridorTaitColoring rings start finish)
    {left right : TubeCorridorEdge rings}
    (hadj : coloring.trackedGraph.Adj left right) :
    coloring.terminalLabel left = coloring.terminalLabel right := by
  rcases hadj with ⟨ring, localLeft, localRight, hlocal, rfl, rfl⟩
  rw [← coloring.localTerminalLabel_eq_terminalLabel_of_tracked ring localLeft
      hlocal.2.1,
    ← coloring.localTerminalLabel_eq_terminalLabel_of_tracked ring localRight
      hlocal.2.2.1]
  exact coloring.localTerminalLabel_eq_of_adj ring hlocal

/-- Terminal labels are invariant on global tracked components. -/
theorem TubeCorridorTaitColoring.terminalLabel_eq_of_reachable
    {rings : Nat} {start finish : TubeFrontierState}
    (coloring : TubeCorridorTaitColoring rings start finish)
    {left right : TubeCorridorEdge rings}
    (hreachable : coloring.trackedGraph.Reachable left right) :
    coloring.terminalLabel left = coloring.terminalLabel right := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at hreachable
  induction hreachable with
  | refl => rfl
  | tail hreachable hadj ih =>
      exact ih.trans (coloring.terminalLabel_eq_of_adj hadj)

/-- Complete end-to-end classification: an input terminal reaches an output
terminal exactly when their identities agree. In particular the four live
strands remain in four distinct components. -/
theorem TubeCorridorTaitColoring.terminal_reachable_iff
    {rings : Nat} {start finish : TubeFrontierState}
    (coloring : TubeCorridorTaitColoring rings start finish)
    (hstart : start.Valid) (hfinish : finish.Valid)
    (left right : Fin 4) :
    coloring.trackedGraph.Reachable
        (.inl (0, start.terminal left))
        (.inl (Fin.last rings, finish.terminal right)) ↔
      left = right := by
  constructor
  · intro hreachable
    have hlabels := coloring.terminalLabel_eq_of_reachable hreachable
    change frontierTerminalLabel (coloring.frontierState 0)
        (start.terminal left) =
      frontierTerminalLabel (coloring.frontierState (Fin.last rings))
        (finish.terminal right) at hlabels
    rw [coloring.first_state, coloring.last_state] at hlabels
    have hleft : frontierTerminalLabel start (start.terminal left) = some left :=
      (frontierTerminalLabel_eq_some_iff hstart.1 _ _).2 rfl
    have hright : frontierTerminalLabel finish (finish.terminal right) = some right :=
      (frontierTerminalLabel_eq_some_iff hfinish.1 _ _).2 rfl
    rw [hleft, hright] at hlabels
    exact Option.some.inj hlabels
  · intro heq
    subst right
    exact coloring.terminal_reachable left

theorem normalizedTubeSeed_valid : normalizedTubeSeed.Valid := by decide

/-- Every multiple of four normalized rings has one proper Tait coloring in
which the four seed strands survive in four distinct global components. -/
theorem normalizedTubeSeed_periodicFourStrandTaitCorridor
    (repetitions : Nat) :
    ∃ coloring : TubeCorridorTaitColoring (repetitions * 4)
        normalizedTubeSeed normalizedTubeSeed,
      coloring.LocallyTait ∧
      ∀ left right : Fin 4,
        coloring.trackedGraph.Reachable
            (.inl (0, normalizedTubeSeed.terminal left))
            (.inl (Fin.last (repetitions * 4),
              normalizedTubeSeed.terminal right)) ↔
          left = right := by
  obtain ⟨coloring, hTait⟩ := normalizedTubeSeed_periodicTaitColoring repetitions
  exact ⟨coloring, hTait, fun left right =>
    coloring.terminal_reachable_iff
      normalizedTubeSeed_valid normalizedTubeSeed_valid left right⟩

/-- Tube Seed theorem for the good cap word in reflected ring coordinates:
every four-ring padding preserves all four tracked strand identities in a
proper glued coloring of the normalized `(5,0)` tube incidence model. -/
theorem goodTubeCap_periodicFourStrandTaitCorridor
    (repetitions : Nat) :
    ∃ coloring : TubeCorridorTaitColoring (repetitions * 4)
        (goodTubeCapState.reindex goodTubeCapReflection)
        (goodTubeCapState.reindex goodTubeCapReflection),
      coloring.LocallyTait ∧
      ∀ left right : Fin 4,
        coloring.trackedGraph.Reachable
            (.inl (0,
              (goodTubeCapState.reindex goodTubeCapReflection).terminal left))
            (.inl (Fin.last (repetitions * 4),
              (goodTubeCapState.reindex goodTubeCapReflection).terminal right)) ↔
          left = right := by
  rw [goodTubeCapState_reindex_eq_normalizedTubeSeed]
  exact normalizedTubeSeed_periodicFourStrandTaitCorridor repetitions

end Mettapedia.GraphTheory.FourColor.GoertzelV24TubeRingTransfer
