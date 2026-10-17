import Mettapedia.GSLT.LanguageDef.RegexSourceCorrespondence
import Mettapedia.GSLT.LanguageDef.RegexRepetitionEquationExecution
import Mettapedia.Computability.RegularLanguages.RegexPikeSimple
import Std.Data.String.ToNat

/-!
# Authored compiler results realize the independent source observation

The actual extracted module equations return encoded instruction packets.
Injectivity of their encoding prevents a returned packet from being mistaken
for a different program. This connects real equation execution, counted-source
lowering, the checked finite graph, and structural source selected captures.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.RegexSelection.Source.Authored

open Mettapedia.Computability.RegularLanguages
open RegexTaggedGraph
open OrderedGraphSearch (Probe)
open DeterministicEquations EquationExecution

theorem natural_injective : Function.Injective natural := by
  intro first second same
  apply Nat.repr_injective
  exact Term.lit.inj same

theorem natural_inj (first second : Nat) : natural first = natural second ↔ first = second :=
  natural_injective.eq_iff

theorem address_injective : Function.Injective address := by
  intro first
  induction first with
  | root | ending => intro second same; cases second <;> simp_all [address]
  | left first ih | right first ih | body first ih | loop first ih | close first ih =>
      intro second same
      cases second <;> simp_all [address]
      exact ih rfl

theorem address_inj (first second : Address) : address first = address second ↔ first = second :=
  address_injective.eq_iff

theorem list_injective : Function.Injective list := by
  intro first
  induction first with
  | nil => intro second same; cases second <;> simp_all [list]
  | cons head tail ih =>
      intro second same
      cases second with
      | nil => simp [list] at same
      | cons other rest =>
          have unpack : head = other ∧ list tail = list rest := by simpa [list] using same
          cases unpack.1
          exact congrArg (head :: ·) (ih unpack.2)

theorem ranges_injective : Function.Injective ranges := by
  intro first second same
  have lists := list_injective same
  apply (List.map_injective_iff.mpr ?_) lists
  intro one two same
  have unpack : natural one.1 = natural two.1 ∧ natural one.2 = natural two.2 := by
    simpa using same
  exact Prod.ext (natural_injective unpack.1) (natural_injective unpack.2)

theorem ranges_inj (first second : List ScalarRange) : ranges first = ranges second ↔ first = second :=
  ranges_injective.eq_iff

theorem boundary_injective : Function.Injective boundary := by
  intro first second same
  cases first <;> cases second <;> simp_all [boundary]

theorem boundary_inj (first second : Boundary) : boundary first = boundary second ↔ first = second :=
  boundary_injective.eq_iff

set_option maxHeartbeats 1000000 in
theorem instruction_injective : Function.Injective instruction := by
  intro first second same
  cases first <;> cases second <;>
    simp_all [instruction, address_inj, natural_inj, ranges_inj, boundary_inj]

theorem rows_injective : Function.Injective rows := by
  intro first second same
  exact (List.map_injective_iff.mpr instruction_injective) (list_injective same)

theorem code_injective : Function.Injective code := by
  intro first second same
  have unpack : address first.entry = address second.entry ∧ rows first.rows = rows second.rows := by
    simpa [code] using same
  cases first
  cases second
  have entrySame := address_injective unpack.1
  have rowsSame := rows_injective unpack.2
  cases entrySame
  cases rowsSame
  rfl

/-- The existing module equation family is already an exact enumerator of
independent source operations. A second source-operation compiler is not
required to give those declarations a checked meaning. -/
theorem returned_operations_iff (pattern : Pattern) (continuation occurrence : Address)
    (actualRows : List Instruction)
    (produced : Applies program host "re:emit"
      [source pattern, address continuation, address occurrence] (rows actualRows))
    (pc : Address) (operation : Operation) :
    At pattern continuation occurrence pc operation ↔
      ∃ row ∈ actualRows, row.address = pc ∧ Graph.nodeOf row id = operation := by
  have packetSame := (emit_result_exact pattern continuation occurrence (rows actualRows)).mp produced
  have rowsSame := rows_injective packetSame
  subst actualRows
  exact at_iff_emitted pattern continuation occurrence pc operation

/-- The fast, tail-threaded authored entry has the same complete source
operation interpretation, not merely the same recognized words. -/
theorem accumulator_returned_operations_iff (pattern : Pattern) (continuation occurrence : Address)
    (actualRows : List Instruction)
    (produced : Applies program host "re:emit-acc"
      [source pattern, address continuation, address occurrence, rows []] (rows actualRows))
    (pc : Address) (operation : Operation) :
    At pattern continuation occurrence pc operation ↔
      ∃ row ∈ actualRows, row.address = pc ∧ Graph.nodeOf row id = operation := by
  have packetSame :=
    (AccumulatorExecution.emitAcc_result_exact pattern continuation occurrence [] (rows actualRows)).mp produced
  have rowsSame : actualRows = emit pattern continuation occurrence := by
    apply rows_injective
    simpa only [List.append_nil] using packetSame
  subst actualRows
  exact at_iff_emitted pattern continuation occurrence pc operation

/-- Both authoring presentations recover the actual equation program used by
the source-operation interpretation, rather than a separate native-only table. -/
theorem portable_program_recovery :
    (ModuleFormat.RegexSelectionAuthoring.readPortable? ModuleFormat.RegexSelectionAuthoring.portableText).map
      (fun definition => (definition.equations.mapM equation?).getD []) = some program := by
  rw [ModuleFormat.RegexSelectionAuthoring.portable_recovery]
  rfl

/-- Returned data is the actual program, not merely another packet with an
unproved relationship to it. Arbitrarily nested counted sources are included. -/
theorem returned_program_iff {input : Term} {pattern : Pattern}
    (lowered : RepetitionExecution.Lowers input pattern) (actual : Program) :
    Applies program host "re:compile-authored" [input] (code actual) ↔ actual = compile pattern := by
  exact (RepetitionExecution.compile_authored_result_exact lowered (code actual)).trans code_injective.eq_iff

theorem returned_checked_eq {input : Term} {pattern : Pattern}
    (lowered : RepetitionExecution.Lowers input pattern) (checked : Graph.CheckedProgram)
    (produced : Applies program host "re:compile-authored" [input] (code checked.program)) :
    checked = Graph.checkedCompile pattern := by
  have same := (returned_program_iff lowered checked.program).mp produced
  cases checked with
  | mk actual unique entryOwned targetsOwned =>
      dsimp only at same
      subst actual
      rfl

/-- Selected observations of a returned checked artifact preserve and reflect
the independent source behavior, including the full capture register valuation.
The premise is actual execution of the module's equations, not an asserted
compiler-correctness proposition. -/
theorem returned_selected_iff_source {input : Term} {pattern : Pattern} {length : Nat}
    (lowered : RepetitionExecution.Lowers input pattern) (checked : Graph.CheckedProgram)
    (produced : Applies program host "re:compile-authored" [input] (code checked.program))
    (probe : Probe Graph.CharacterClass String length) (eligible : Thread Address length → Bool)
    (first last : Thread (Graph.Owned checked.program) length) :
    RegexSelectionCorrespondence.LeastSimple (Graph.graphOf checked) probe
      (eligible ∘ mapThread Subtype.val) first last ↔
      Selected pattern probe eligible (mapThread Subtype.val first) (mapThread Subtype.val last) := by
  have same := returned_checked_eq lowered checked produced
  subst checked
  exact compiled_selected_iff_source probe eligible first last

/-- Successful results of the fast authored compiler are handled without
reinterpreting their rows or dropping capture operations. -/
theorem accumulator_returned_program_iff (pattern : Pattern) (actual : Program) :
    Applies program host "re:compile-acc" [source pattern] (code actual) ↔ actual = compile pattern :=
  (AccumulatorExecution.compileAcc_result_exact pattern (code actual)).trans code_injective.eq_iff

/-- An actual successful Pike execution of an authored returned artifact has
an independent simple source execution with exactly its returned captures.
The general preferred-winner theorem is a strictly stronger obligation. -/
theorem returned_pike_success_source {input : Term} {pattern : Pattern} {length : Nat}
    (lowered : RepetitionExecution.Lowers input pattern) (checked : Graph.CheckedProgram)
    (produced : Applies program host "re:compile-authored" [input] (code checked.program))
    (probe : Probe Graph.CharacterClass String length) (eligible : Thread Address length → Bool)
    (closureFuel inputFuel : Nat) (first last : Thread (Graph.Owned checked.program) length)
    (finished : RegexPikeVM.run (Graph.graphOf checked) probe
      (eligible ∘ mapThread Subtype.val) closureFuel inputFuel [first] = .finished (some (last, ()))) :
    ∃ choices points,
      Trace pattern probe eligible (mapThread Subtype.val first) choices points (mapThread Subtype.val last) ∧
        points.Nodup := by
  have same := returned_checked_eq lowered checked produced
  subst checked
  obtain ⟨choices, points, trace, simple⟩ := RegexPikeSimple.run_match_simple
    (Graph.graphOf (Graph.checkedCompile pattern)) probe (eligible ∘ mapThread Subtype.val)
    closureFuel inputFuel first last () finished
  exact ⟨choices, points.map (mapPoint Subtype.val), compiled_trace_source trace,
    simple.map (mapPoint_injective Subtype.val_injective)⟩

/-- A completed empty result is exactly absence of every finite independent
source execution, including cyclic ones. Adequate fuel is a proved execution
precondition, not a default cap or a claim that a cutoff establishes absence. -/
theorem returned_pike_absence_iff_source {input : Term} {pattern : Pattern} {length : Nat}
    (lowered : RepetitionExecution.Lowers input pattern) (checked : Graph.CheckedProgram)
    (produced : Applies program host "re:compile-authored" [input] (code checked.program))
    (probe : Probe Graph.CharacterClass String length) (eligible : OrderedGraphSearch.Point Address length → Bool)
    (closureFuel inputFuel : Nat)
    (closureEnough : 3 * Fintype.card (Graph.Owned checked.program) + 1 ≤ closureFuel)
    (inputEnough : length + 1 ≤ inputFuel) (first : Thread (Graph.Owned checked.program) length) :
    RegexPikeVM.run (Graph.graphOf checked) probe
      (fun thread => eligible (mapPoint Subtype.val thread.point)) closureFuel inputFuel [first] =
      .finished none ↔
      ¬ ∃ choices points last,
        Trace pattern probe (fun thread => eligible thread.point)
          (mapThread Subtype.val first) choices points last := by
  have same := returned_checked_eq lowered checked produced
  subst checked
  refine (RegexPikeCoverage.run_none_iff_no_trace (Graph.graphOf (Graph.checkedCompile pattern)) probe
    (fun point => eligible (mapPoint Subtype.val point)) closureFuel inputFuel closureEnough inputEnough first).trans ?_
  constructor
  · intro absent
    rintro ⟨choices, points, last, source⟩
    obtain ⟨final, targetPoints, trace, _, _⟩ := source_trace_compiled source first rfl
    exact absent ⟨choices, targetPoints, final, (), trace⟩
  · intro absent
    rintro ⟨choices, points, last, tag, trace⟩
    exact absent ⟨choices, points.map (mapPoint Subtype.val), mapThread Subtype.val last,
      compiled_trace_source trace⟩

namespace Controls

theorem counted_nullable_plus_returns_the_real_program :
    Applies program host "re:compile-authored"
      [.expr [.sym "re:repeat-at-least", source (.capture 1 (.alt (.literal 97) .epsilon)),
        RepetitionExecution.count 1, preference true]]
      (code (compile (.plus (.capture 1 (.alt (.literal 97) .epsilon)) true))) :=
  RepetitionExecution.compile_authored_computes
    (.atLeast 1 true (RepetitionExecution.canonical_source_lowers _))

theorem zero_count_retains_layout_but_returns_epsilon :
    RepetitionExecution.sourceGroups
      (.expr [.sym "re:repeat-exact", source (.capture 3 (.literal 97)), RepetitionExecution.count 0]) =
      [natural 3] ∧
    Applies program host "re:compile-authored"
      [.expr [.sym "re:repeat-exact", source (.capture 3 (.literal 97)), RepetitionExecution.count 0]]
      (code (compile .epsilon)) :=
  ⟨rfl, RepetitionExecution.compile_authored_computes
    (.exact 0 (RepetitionExecution.canonical_source_lowers _))⟩

theorem returned_program_cannot_erase_assertion :
    ¬ Applies program host "re:compile-authored" [source (.assertion "word-boundary")]
      (code (compile .epsilon)) := by
  intro produced
  have same := (returned_program_iff (RepetitionExecution.canonical_source_lowers _) _).mp produced
  cases same

end Controls
end Mettapedia.GSLT.LanguageDef.RegexSelection.Source.Authored
