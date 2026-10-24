import Mettapedia.Logic.LP.UnificationIdempotence

/-!
# Fresh cells through selected control-flow prefixes

A fresh cell is both unbound and absent from every other cell's image.
Occurs-checked unification of equations not mentioning it preserves that
property, including when equations are first read through the current store.
Inactive branch equations need not exclude the cell: they are not executed.

The solver is the existing total Martelli--Montanari implementation. This
proves a logical-store invariant, not correspondence of a native compiler's
control-flow analysis or allocation of fresh frames.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.FreshFrameNoninterference

open Mettapedia.Logic.LP

variable {σ : LPSignature} [DecidableEq σ.vars]

/-- No alias can expose this unbound cell to an unrelated equation. -/
structure PrivateCell (θ : Subst σ) (cell : σ.vars) : Prop where
  unbound : θ cell = .var cell
  isolated : ∀ other, other ≠ cell → cell ∉ (θ other).freeVars

theorem private_id (cell : σ.vars) : PrivateCell (Subst.id σ) cell where
  unbound := rfl
  isolated other different := by
    simpa only [Subst.id_apply, Term.mem_freeVars_var] using Ne.symm different

theorem PrivateCell.absent_apply {θ : Subst σ} {cell : σ.vars}
    (privateCell : PrivateCell θ cell) {term : Term σ}
    (absent : cell ∉ term.freeVars) : cell ∉ (θ.applyTerm term).freeVars := by
  intro occurs
  obtain ⟨other, present, image⟩ := Subst.mem_freeVars_applyTerm.mp occurs
  by_cases same : other = cell
  · exact absent (same ▸ present)
  · exact privateCell.isolated other same image

theorem private_of_relevant {θ : Subst σ} {cells : Finset σ.vars}
    (relevant : θ.RelevantIdempotent cells) {cell : σ.vars}
    (absent : cell ∉ cells) : PrivateCell θ cell where
  unbound := relevant.fixes cell absent
  isolated other different := by
    by_cases present : other ∈ cells
    · exact fun occurs => absent (relevant.range other present occurs)
    · rw [relevant.fixes other present, Term.mem_freeVars_var]
      exact Ne.symm different

theorem PrivateCell.comp {first second : Subst σ} {cell : σ.vars}
    (outer : PrivateCell second cell) (inner : PrivateCell first cell) :
    PrivateCell (second ∘ₛ first) cell where
  unbound := by simp only [Subst.comp_apply, inner.unbound,
    Subst.applyTerm_var, outer.unbound]
  isolated other different := outer.absent_apply (inner.isolated other different)

theorem PrivateCell.absent_applyEqs {θ : Subst σ} {cell : σ.vars}
    (privateCell : PrivateCell θ cell) {equations : List (Term σ × Term σ)}
    (absent : cell ∉ eqVars equations) : cell ∉ eqVars (θ.applyEqs equations) := by
  intro present
  obtain ⟨equation, member, occurs⟩ := mem_eqVars.mp present
  obtain ⟨⟨left, right⟩, original, rfl⟩ := List.mem_map.mp member
  rcases occurs with onLeft | onRight
  · exact privateCell.absent_apply
      (fun occurrence => absent (mem_eqVars.mpr ⟨_, original, .inl occurrence⟩)) onLeft
  · exact privateCell.absent_apply
      (fun occurrence => absent (mem_eqVars.mpr ⟨_, original, .inr occurrence⟩)) onRight

variable [DecidableEq σ.constants] [DecidableEq σ.functionSymbols]

/-- A real constraint step reads the current store before solving. -/
def solveStep (θ : Subst σ) (equations : List (Term σ × Term σ)) : Option (Subst σ) :=
  (unifyTotal (θ.applyEqs equations)).map (fun next => next ∘ₛ θ)

theorem solveStep_private {θ result : Subst σ} {cell : σ.vars}
    {equations : List (Term σ × Term σ)} (privateCell : PrivateCell θ cell)
    (absent : cell ∉ eqVars equations) (accepted : solveStep θ equations = some result) :
    PrivateCell result cell := by
  unfold solveStep at accepted
  cases solved : unifyTotal (θ.applyEqs equations) with
  | none => simp [solved] at accepted
  | some next =>
    simp only [solved, Option.map_some, Option.some.injEq] at accepted
    subst result
    exact (private_of_relevant (unifyTotal_relevantIdempotent _ next solved)
      (privateCell.absent_applyEqs absent)).comp privateCell

/-- Execute each reached constraint group in order. -/
def solvePrefix (θ : Subst σ) : List (List (Term σ × Term σ)) → Option (Subst σ)
  | [] => some θ
  | equations :: rest => (solveStep θ equations).bind (fun next => solvePrefix next rest)

theorem solvePrefix_private {groups : List (List (Term σ × Term σ))}
    {θ result : Subst σ} {cell : σ.vars} (privateCell : PrivateCell θ cell)
    (absent : ∀ equations ∈ groups, cell ∉ eqVars equations)
    (accepted : solvePrefix θ groups = some result) : PrivateCell result cell := by
  induction groups generalizing θ with
  | nil =>
      simp only [solvePrefix, Option.some.injEq] at accepted
      exact accepted ▸ privateCell
  | cons equations rest ih =>
    cases first : solveStep θ equations with
    | none => simp [solvePrefix, first] at accepted
    | some next =>
      have privateNext := solveStep_private privateCell (absent _ List.mem_cons_self) first
      exact ih privateNext (fun group present => absent group (List.mem_cons_of_mem _ present))
        (by simpa only [solvePrefix, first, Option.bind_some] using accepted)

/-- A path to a pattern. `selected` has already committed to one branch.
Its condition prefix is still checked; its inactive sibling is excluded.
`after` records a future continuation, which has not yet run. -/
inductive PatternPath (σ : LPSignature) where
  | hole
  | before (equations : List (Term σ × Term σ)) (inner : PatternPath σ)
  | after (inner : PatternPath σ) (equations : List (Term σ × Term σ))
  | selected (condition : List (Term σ × Term σ)) (inner : PatternPath σ)
      (inactive : List (Term σ × Term σ))

def PatternPath.reached : PatternPath σ → List (List (Term σ × Term σ))
  | .hole => []
  | .before equations inner => equations :: inner.reached
  | .after inner _ => inner.reached
  | .selected condition inner _ => condition :: inner.reached

/-- A conservative support summary includes future active uses, but never
uses in a sibling that has already been excluded by control flow. -/
def PatternPath.activeSupport : PatternPath σ → Finset σ.vars
  | .hole => ∅
  | .before equations inner => eqVars equations ∪ inner.activeSupport
  | .after inner equations => inner.activeSupport ∪ eqVars equations
  | .selected condition inner _ => eqVars condition ∪ inner.activeSupport

omit [DecidableEq σ.constants] [DecidableEq σ.functionSymbols] in
theorem PatternPath.reached_subset (path : PatternPath σ)
    {equations : List (Term σ × Term σ)} (present : equations ∈ path.reached) :
    eqVars equations ⊆ path.activeSupport := by
  induction path with
  | hole => simp [reached] at present
  | before group inner ih =>
    rcases List.mem_cons.mp present with rfl | later
    · exact Finset.subset_union_left
    · exact (ih later).trans Finset.subset_union_right
  | after inner group ih => exact (ih present).trans Finset.subset_union_left
  | selected condition inner inactive ih =>
    rcases List.mem_cons.mp present with rfl | later
    · exact Finset.subset_union_left
    · exact (ih later).trans Finset.subset_union_right

/-- The admission conclusion follows from syntactic support and fresh-frame
formation, not from an assumption that the desired cell stays unbound. -/
theorem PatternPath.fresh_at_pattern (path : PatternPath σ)
    {θ result : Subst σ} {cell : σ.vars} (privateCell : PrivateCell θ cell)
    (absent : cell ∉ path.activeSupport)
    (accepted : solvePrefix θ path.reached = some result) : result cell = .var cell :=
  (solvePrefix_private privateCell
    (fun _ present occurs => absent (path.reached_subset present occurs)) accepted).unbound

namespace Controls

abbrev signature : LPSignature where
  vars := ℕ
  constants := Unit
  functionSymbols := Empty
  functionArity := Empty.elim
  relationSymbols := Empty
  relationArity := Empty.elim

def unrelated : List (Term signature × Term signature) := [(.var 1, .const ())]
def bindsHead : List (Term signature × Term signature) := [(.var 0, .const ())]

def aliased : Subst signature := Subst.single 1 (.var 0)

def selectedPath : PatternPath signature := .selected unrelated .hole bindsHead

/-- The unused sibling mentions the head. The selected prefix binds another
cell and really executes a successful unification, leaving the head free. -/
theorem selected_branch_control :
    0 ∉ selectedPath.activeSupport ∧
    0 ∈ eqVars bindsHead ∧
    (solvePrefix (Subst.id signature) selectedPath.reached).map
      (fun θ => (θ 0, θ 1)) = some (.var 0, .const ()) := by
  simp [selectedPath, PatternPath.activeSupport, PatternPath.reached, unrelated,
    bindsHead, eqVars, Term.freeVars, solvePrefix, solveStep, Subst.applyEqs,
    Subst.applyTerm, Subst.id, unifyTotal, Subst.comp, Subst.single, Term.occursIn]

/-- If the receiver binds the head before the pattern, it is not fresh. -/
theorem early_output_control :
    0 ∈ (PatternPath.before bindsHead selectedPath).activeSupport ∧
    (solvePrefix (Subst.id signature)
      (PatternPath.before bindsHead selectedPath).reached).map
      (fun θ => θ 0) = some (.const ()) := by
  simp [selectedPath, PatternPath.activeSupport, PatternPath.reached, unrelated,
    bindsHead, eqVars, Term.freeVars, solvePrefix, solveStep, Subst.applyEqs,
    Subst.applyTerm, Subst.id, unifyTotal, Subst.comp, Subst.single, Term.occursIn]

/-- Being unbound alone is insufficient: a pre-existing alias exposes the
head through an equation whose source syntax does not mention it. -/
theorem alias_control :
    aliased 0 = .var 0 ∧ 0 ∉ eqVars unrelated ∧
    (solveStep aliased unrelated).map (fun θ => θ 0) = some (.const ()) := by
  simp [aliased, unrelated, eqVars, Term.freeVars, solveStep, Subst.applyEqs,
    Subst.applyTerm, unifyTotal, Subst.comp, Subst.single, Subst.id, Term.occursIn]

end Controls

end Mettapedia.Machines.FreshFrameNoninterference
