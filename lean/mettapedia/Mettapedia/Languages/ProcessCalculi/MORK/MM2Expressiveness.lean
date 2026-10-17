import Mettapedia.Languages.ProcessCalculi.MORK.ScheduledMinimum
import Mettapedia.Languages.ProcessCalculi.MORK.MM2MainlineProviders

/-!
# What MM2 cannot express locally

MM2 fires the least `(exec …)` atom of the space: it removes it, matches its
conjunctive input against the space (the read copy, which contains the exec
itself), and applies the instantiated output sinks.  A translation into MM2 is
*local* in Felleisen's sense (eliminability, Definition 3.3) when it is
homomorphic in MM2's constructs: data atoms, the `exec` shell, its location
and input, and the ordinary sinks are kept, and only the new construct is
replaced, by MM2 syntax that may depend on that construct alone.

This module proves, on the work-queue model of MM2 and on its variant with
open templates:

* **A synchronous call is not eliminable** (`call_not_eliminable`), even for
  programs that never read code.  The extension adds an output sink
  `(call F A $r S…)` whose results return into the caller's sinks within the
  caller's firing.  A caller and a watcher at the least location, with an
  equation `(= (f a) N)` for a fresh `N`: in the source the watcher reports
  exactly `(out N)`; in any local translation the call has not returned when
  the watcher fires, because firing only instantiates sinks and every
  executable that could read the equation sorts after the watcher
  (`conjuncts_below_watcher`, on the exact byte keys).  The translation then
  never reports `(out N)`, or first reports something else.  The argument
  (`waiting_run`, `window_disagrees`) holds for every step semantics that
  fires the least executable (`FiresLeast`), so it also holds with **open
  templates** (`call_not_eliminable_open`), which write instances that keep
  unbound variables, as the MORK engine does: a translated caller may write a
  lookup executable, and it still runs too late.
* **A reserved band returns in time** (`band_reports`): with open templates,
  a global translation that moves the user's executables out of the least
  location and writes each lookup there reproduces the source's report.  What
  the window rules out is locality.
* **Reflection refutes every local translation** (`call_not_eliminable_reflective`):
  a program whose pattern reads executables copies the head of a call sink
  into its report; the translation has no `call` left, and MM2 creates no
  symbol.  The argument applies to any new construct with a reserved symbol,
  sugar included.
* **Absence is not eliminable** (`absence_not_eliminable`).  An input
  conjunct `(not P)` (fire only if nothing matches `P`) has no local
  translation: conjunctive matching is monotone in the space, so whatever
  replaces the conjunct lets the executable fire in a space with more atoms
  whenever it fires in one with fewer.  Absence needs a frontier: a later
  stage that decides it, which a local translation cannot place.
* Both classes of local translations are inhabited (`dropCalls`,
  `dropAbsence`), so neither theorem holds vacuously.
* The supporting facts: matching binds variables to subterms of matched atoms
  (`matchAtom_binding`), substitution creates no new leaf
  (`applySubst_occurs`), and a step of the support model creates no new leaf
  (`workQueueStep_leafFree`, `FiresLeast.leafFree`).

**Scope.**  Every result above is a theorem about the support model: add, remove,
head and tail sinks, comma inputs, and a parser that drops every other sink.  The
kernel differs in ways that matter here, and the last sections re-check the results
against it (`Mainline`):

* the kernel cannot be built without its `pure` sink, which computes new symbols and
  values, so its steps are not leaf-free;
* an executable whose input is the empty expression `()`, as in the callers below, is
  consumed without firing (`unit_input_inert`, `callers_inert`);
* with a valid input, translations inside `CallElimination` reproduce the reports of both
  call witnesses by computing the report symbols (`MM2FunctionCalls`), so the syntactic
  conditions `expand_plain` and `expand_quiet` do not exclude forged reports there;
* compared by their reports in every context of the window family instead, no expansion
  of the caller is correct in the kernel, whatever it computes
  (`MM2CallLocality.call_not_locally_eliminable`), and the identity on call-free atoms
  is what that uses: relocating the context's executables closes the window
  (`MM2CallLocality.relocation_closes_window`);
* absence is still not eliminable by replacing the input, with every factor form
  (`no_mainline_input_decides_absence`), but a translation that may also rewrite the
  output decides it at a stratum boundary (`downward_staging_decides_absence`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.MORK.Expressiveness

open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)
open Mettapedia.Languages.ProcessCalculi.MORK

/-! ## Occurrence -/

/-- `leaf` occurs in an atom (as a subterm). -/
inductive Occurs (leaf : Atom) : Atom → Prop
  | here : Occurs leaf leaf
  | child {children : List Atom} {child : Atom} :
      child ∈ children → Occurs leaf child → Occurs leaf (.expression children)

theorem Occurs.trans {a b c : Atom} (first : Occurs a b) (second : Occurs b c) : Occurs a c := by
  induction second with
  | here => exact first
  | child member _ ih => exact .child member ih

/-- A leaf that cannot be produced by substituting for a variable: a symbol or a
grounded value. -/
def IsLeaf (leaf : Atom) : Prop :=
  (∃ name, leaf = .symbol name) ∨ ∃ value, leaf = .grounded value

theorem Subst.lookup_mem {σ : Subst} {name : String} {value : Atom}
    (found : σ.lookup name = some value) : ∃ p ∈ σ, p.2 = value := by
  unfold Subst.lookup at found
  cases search : σ.find? (fun p => p.1 == name) with
  | none => simp [search] at found
  | some p =>
      simp only [search, Option.map_some, Option.some.injEq] at found
      exact ⟨p, List.mem_of_find?_eq_some search, found⟩

/-- **Matching binds variables only to subterms of the matched atom.** -/
theorem matchAtom_binding (σ : Subst) (pat conc : Atom) (σ' : Subst)
    (h : matchAtom σ pat conc = some σ') : ∀ p ∈ σ', p ∈ σ ∨ Occurs p.2 conc := by
  match pat, conc with
  | .var v, b =>
      simp only [matchAtom] at h
      cases found : σ.lookup v with
      | some a =>
          rw [found] at h
          simp only at h
          split_ifs at h
          cases h
          exact fun p hp => Or.inl hp
      | none =>
          rw [found] at h
          simp only [Option.some.injEq] at h
          subst h
          intro p hp
          rcases List.mem_cons.mp hp with rfl | hp
          · exact Or.inr .here
          · exact Or.inl hp
  | .symbol s, .symbol t =>
      simp only [matchAtom] at h
      split_ifs at h
      cases h
      exact fun p hp => Or.inl hp
  | .grounded g, .grounded k =>
      simp only [matchAtom] at h
      split_ifs at h
      cases h
      exact fun p hp => Or.inl hp
  | .expression ps, .expression cs =>
      simp only [matchAtom] at h
      intro p hp
      rcases listCase σ ps cs σ' h p hp with old | ⟨c, member, inside⟩
      · exact Or.inl old
      · exact Or.inr (.child member inside)
  | .symbol _, .var _ => simp [matchAtom] at h
  | .symbol _, .grounded _ => simp [matchAtom] at h
  | .symbol _, .expression _ => simp [matchAtom] at h
  | .grounded _, .var _ => simp [matchAtom] at h
  | .grounded _, .symbol _ => simp [matchAtom] at h
  | .grounded _, .expression _ => simp [matchAtom] at h
  | .expression _, .var _ => simp [matchAtom] at h
  | .expression _, .symbol _ => simp [matchAtom] at h
  | .expression _, .grounded _ => simp [matchAtom] at h
where
  listCase (σ : Subst) (ps cs : List Atom) (σ' : Subst)
      (h : matchAtom.matchAtomList σ ps cs = some σ') :
      ∀ p ∈ σ', p ∈ σ ∨ ∃ c ∈ cs, Occurs p.2 c := by
    match ps, cs with
    | [], [] =>
        simp only [matchAtom.matchAtomList, Option.some.injEq] at h
        subst h
        exact fun p hp => Or.inl hp
    | [], _ :: _ => simp [matchAtom.matchAtomList] at h
    | _ :: _, [] => simp [matchAtom.matchAtomList] at h
    | p :: ps, c :: cs =>
        simp only [matchAtom.matchAtomList] at h
        cases first : matchAtom σ p c with
        | none => rw [first] at h; simp at h
        | some σ'' =>
            rw [first] at h
            intro q hq
            rcases listCase σ'' ps cs σ' h q hq with inner | ⟨d, member, inside⟩
            · rcases matchAtom_binding σ p c σ'' first q inner with old | found
              · exact Or.inl old
              · exact Or.inr ⟨c, List.mem_cons_self, found⟩
            · exact Or.inr ⟨d, List.mem_cons_of_mem c member, inside⟩


theorem applySubstList_eq_map (σ : Subst) :
    ∀ terms : List Atom, applySubst.applySubstList σ terms = terms.map (applySubst σ)
  | [] => rfl
  | term :: rest => by simp [applySubst.applySubstList, applySubstList_eq_map σ rest]

/-- **Substitution creates no leaf**: a symbol or grounded value occurring in an
instance occurs in the term or in a substituted value. -/
theorem applySubst_occurs {leaf : Atom} (isLeaf : IsLeaf leaf) (σ : Subst) :
    ∀ term : Atom, Occurs leaf (applySubst σ term) → Occurs leaf term ∨ ∃ p ∈ σ, Occurs leaf p.2
  | .var name, h => by
      simp only [applySubst] at h
      cases found : σ.lookup name with
      | none =>
          rw [found] at h
          exact Or.inl h
      | some value =>
          rw [found] at h
          obtain ⟨p, member, equal⟩ := Subst.lookup_mem found
          exact Or.inr ⟨p, member, equal ▸ h⟩
  | .symbol _, h => Or.inl h
  | .grounded _, h => Or.inl h
  | .expression terms, h => by
      simp only [applySubst] at h
      cases h with
      | here => rcases isLeaf with ⟨_, equal⟩ | ⟨_, equal⟩ <;> cases equal
      | child member inside =>
          rcases listCase terms _ member inside with ⟨term, termMember, termInside⟩ | fromValue
          · exact Or.inl (.child termMember termInside)
          · exact Or.inr fromValue
where
  listCase : ∀ (terms : List Atom) (child : Atom), child ∈ applySubst.applySubstList σ terms →
      Occurs leaf child → (∃ term ∈ terms, Occurs leaf term) ∨ ∃ p ∈ σ, Occurs leaf p.2
    | [], _, member, _ => by simp [applySubst.applySubstList] at member
    | term :: rest, child, member, inside => by
        simp only [applySubst.applySubstList, List.mem_cons] at member
        rcases member with rfl | member
        · rcases applySubst_occurs isLeaf σ term inside with inTerm | inValue
          · exact Or.inl ⟨term, List.mem_cons_self, inTerm⟩
          · exact Or.inr inValue
        · rcases listCase rest child member inside with ⟨other, otherMember, inOther⟩ | inValue
          · exact Or.inl ⟨other, List.mem_cons_of_mem term otherMember, inOther⟩
          · exact Or.inr inValue

/-- A row of a conjunctive match binds each variable to a subterm of an atom of
the space that some conjunct matched. -/
theorem matchPattern_go_binding (space : Space) :
    ∀ (conjuncts : List Atom) (σ₀ : Subst) (witnesses : Finset Atom) (row : Subst × Finset Atom),
      row ∈ matchPattern.go space conjuncts σ₀ witnesses → ∀ p ∈ row.1, p ∈ σ₀ ∨
        ∃ conjunct ∈ conjuncts, ∃ atom ∈ space, (∃ σ₁ σ₂, matchAtom σ₁ conjunct atom = some σ₂) ∧
          Occurs p.2 atom
  | [], σ₀, witnesses, row, member => by
      simp only [matchPattern.go, List.mem_singleton] at member
      subst member
      exact fun p hp => Or.inl hp
  | conjunct :: rest, σ₀, witnesses, row, member => by
      simp only [matchPattern.go, List.mem_flatMap] at member
      obtain ⟨⟨σ₁, atom⟩, matched, inRest⟩ := member
      obtain ⟨atomMember, matchedEq⟩ := matchOneInSpace_spec σ₀ conjunct space σ₁ atom matched
      intro p hp
      rcases matchPattern_go_binding space rest σ₁ _ row inRest p hp with fromFirst | ⟨other, otherMember, otherAtom, otherAtomMember, otherMatched, inOther⟩
      · rcases matchAtom_binding σ₀ conjunct atom σ₁ matchedEq p fromFirst with old | inAtom
        · exact Or.inl old
        · exact Or.inr ⟨conjunct, List.mem_cons_self, atom, atomMember, ⟨σ₀, σ₁, matchedEq⟩, inAtom⟩
      · exact Or.inr ⟨other, List.mem_cons_of_mem _ otherMember, otherAtom, otherAtomMember,
          otherMatched, inOther⟩

theorem matchPattern_binding {space : Space} {pattern : Pattern} {σ : Subst}
    (member : σ ∈ (matchPattern [] space pattern).map Prod.fst) :
    ∀ p ∈ σ, ∃ conjunct ∈ pattern.atoms, ∃ atom ∈ space,
      (∃ σ₁ σ₂, matchAtom σ₁ conjunct atom = some σ₂) ∧ Occurs p.2 atom := by
  obtain ⟨row, rowMember, rfl⟩ := List.mem_map.mp member
  intro p hp
  rcases matchPattern_go_binding space pattern.atoms [] ∅ row rowMember p hp with impossible | found
  · simp at impossible
  · exact found

/-- An expression pattern matches only expressions of its arity. -/
theorem matchAtom_expression_arity {σ σ' : Subst} {children : List Atom} {atom : Atom}
    (h : matchAtom σ (.expression children) atom = some σ') :
    ∃ others : List Atom, atom = .expression others ∧ others.length = children.length := by
  cases atom with
  | expression others =>
      refine ⟨others, rfl, ?_⟩
      simp only [matchAtom] at h
      exact listLength σ children others σ' h
  | var _ => simp [matchAtom] at h
  | symbol _ => simp [matchAtom] at h
  | grounded _ => simp [matchAtom] at h
where
  listLength : ∀ (σ : Subst) (ps cs : List Atom) (σ' : Subst),
      matchAtom.matchAtomList σ ps cs = some σ' → cs.length = ps.length
    | _, [], [], _, _ => rfl
    | _, [], _ :: _, _, h => by simp [matchAtom.matchAtomList] at h
    | _, _ :: _, [], _, h => by simp [matchAtom.matchAtomList] at h
    | σ, p :: ps, c :: cs, σ', h => by
        simp only [matchAtom.matchAtomList] at h
        cases first : matchAtom σ p c with
        | none => rw [first] at h; simp at h
        | some σ'' =>
            rw [first] at h
            simp [listLength σ'' ps cs σ' h]

/-- Staging a sink collects instances of its atom. -/
theorem stage_mem {sink : Sink} :
    ∀ (rows : List Subst) (staged : List Atom) {x : Atom},
      x ∈ rows.foldl (stageSupportSink sink) staged → x ∈ staged ∨ ∃ σ ∈ rows, x = applySubst σ sink.atom
  | [], staged, x, member => Or.inl member
  | σ :: rest, staged, x, member => by
      simp only [List.foldl_cons] at member
      rcases stage_mem rest _ member with inStage | ⟨σ', σ'Member, equal⟩
      · have : x ∈ staged ∨ x = applySubst σ sink.atom := by
          unfold stageSupportSink insertSupport at inStage
          cases sink <;> simp only at inStage <;> split_ifs at inStage <;>
            simp_all [List.mem_append]
        rcases this with old | new
        · exact Or.inl old
        · exact Or.inr ⟨σ, List.mem_cons_self, new⟩
      · exact Or.inr ⟨σ', List.mem_cons_of_mem σ σ'Member, equal⟩

theorem stage_keeps {sink : Sink} (σ : Subst) (staged : List Atom) {x : Atom} (h : x ∈ staged) :
    x ∈ stageSupportSink sink staged σ := by
  have insertKeeps : ∀ y : Atom, x ∈ insertSupport staged y := by
    intro y
    unfold insertSupport
    by_cases present : y ∈ staged
    · rw [if_pos present]; exact h
    · rw [if_neg present]; exact List.mem_append_left _ h
  unfold stageSupportSink
  cases sink with
  | remove body => exact insertKeeps _
  | add body =>
      by_cases ground : isGroundAtom (applySubst σ body) = true
      · simp only [Sink.atom, ground, ↓reduceIte]; exact insertKeeps _
      · simp only [Sink.atom, ground]; exact h
  | head count body =>
      by_cases ground : isGroundAtom (applySubst σ body) = true
      · simp only [Sink.atom, ground, ↓reduceIte]; exact insertKeeps _
      · simp only [Sink.atom, ground]; exact h
  | tail count body =>
      by_cases ground : isGroundAtom (applySubst σ body) = true
      · simp only [Sink.atom, ground, ↓reduceIte]; exact insertKeeps _
      · simp only [Sink.atom, ground]; exact h

theorem stage_fold_keeps {sink : Sink} :
    ∀ (rows : List Subst) (staged : List Atom) {x : Atom}, x ∈ staged →
      x ∈ rows.foldl (stageSupportSink sink) staged
  | [], _, _, h => h
  | σ :: rest, staged, _, h => stage_fold_keeps rest _ (stage_keeps σ staged h)

/-- Staging an insertion keeps every ground instance. -/
theorem stage_add_mem {body : Atom} :
    ∀ (rows : List Subst) (staged : List Atom) {σ : Subst}, σ ∈ rows →
      isGroundAtom (applySubst σ body) = true →
        applySubst σ body ∈ rows.foldl (stageSupportSink (.add body)) staged
  | [], _, _, member, _ => by simp at member
  | σ' :: rest, staged, σ, member, ground => by
      simp only [List.foldl_cons]
      rcases List.mem_cons.mp member with rfl | member
      · apply stage_fold_keeps
        unfold stageSupportSink
        simp only [Sink.atom, ground, ↓reduceIte]
        unfold insertSupport
        by_cases present : applySubst σ body ∈ staged
        · rw [if_pos present]; exact present
        · rw [if_neg present]; simp
      · exact stage_add_mem rest _ member ground

/-! ### Support-valued sink providers

The work-queue provider stages only ground instances of insertions; the open
provider below stages every instance.  Both finalize alike, so what they add
and keep is described once. -/

/-- A support-valued sink provider, given by how it stages one row. -/
def supportProvider (stage : Sink → List Atom → Subst → List Atom) : BatchSinkProvider Sink where
  Stage := fun _ => List Atom
  init := fun _ => []
  stage := stage
  finalize := finalizeSupportSink

/-- Staging collects instances of the sink's atom. -/
def StagesInstances (stage : Sink → List Atom → Subst → List Atom) : Prop :=
  ∀ (sink : Sink) (rows : List Subst) (staged : List Atom) {x : Atom},
    x ∈ rows.foldl (stage sink) staged → x ∈ staged ∨ ∃ σ ∈ rows, x = applySubst σ sink.atom

theorem stageSupportSink_instances : StagesInstances stageSupportSink :=
  fun _ rows staged _ member => stage_mem rows staged member

/-- What a support-valued batch adds is an instance of one of its sink atoms. -/
theorem supportProvider_mem {stage : Sink → List Atom → Subst → List Atom}
    (stages : StagesInstances stage) {rows : List Subst} :
    ∀ (sinks : List Sink) (space : Space) {x : Atom},
      x ∈ (supportProvider stage).run rows space sinks →
        x ∈ space ∨ ∃ sink ∈ sinks, ∃ σ ∈ rows, x = applySubst σ sink.atom
  | [], space, x, member => Or.inl member
  | sink :: rest, space, x, member => by
      rw [BatchSinkProvider.run_cons] at member
      rcases supportProvider_mem stages rest _ member with inFinal | ⟨other, otherMember, σ, σMember, equal⟩
      · have staged : ∀ y ∈ rows.foldl (stage sink) [], ∃ σ ∈ rows, y = applySubst σ sink.atom := by
          intro y hy
          rcases stages sink rows [] hy with impossible | found
          · simp at impossible
          · exact found
        change x ∈ finalizeSupportSink sink (rows.foldl (stage sink) []) space at inFinal
        unfold finalizeSupportSink at inFinal
        cases sink with
        | add body =>
            rcases Finset.mem_union.mp inFinal with old | new
            · exact Or.inl old
            · obtain ⟨σ, σMember, equal⟩ := staged x (List.mem_toFinset.mp new)
              exact Or.inr ⟨_, List.mem_cons_self, σ, σMember, equal⟩
        | remove body => exact Or.inl (Finset.mem_sdiff.mp inFinal).1
        | head count body =>
            rcases Finset.mem_union.mp inFinal with old | new
            · exact Or.inl old
            · unfold compactExtrema compactExtremaList at new
              obtain ⟨σ, σMember, equal⟩ :=
                staged x (List.mem_mergeSort.mp (List.mem_of_mem_take (List.mem_toFinset.mp new)))
              exact Or.inr ⟨_, List.mem_cons_self, σ, σMember, equal⟩
        | tail count body =>
            rcases Finset.mem_union.mp inFinal with old | new
            · exact Or.inl old
            · unfold compactExtrema compactExtremaList at new
              obtain ⟨σ, σMember, equal⟩ :=
                staged x (List.mem_mergeSort.mp (List.mem_of_mem_take (List.mem_toFinset.mp new)))
              exact Or.inr ⟨_, List.mem_cons_self, σ, σMember, equal⟩
      · exact Or.inr ⟨other, List.mem_cons_of_mem _ otherMember, σ, σMember, equal⟩

/-- A support-valued batch keeps every atom that no removal instance names. -/
theorem supportProvider_keeps {stage : Sink → List Atom → Subst → List Atom}
    (stages : StagesInstances stage) {rows : List Subst} :
    ∀ (sinks : List Sink) (space : Space) {x : Atom}, x ∈ space →
      (∀ sink ∈ sinks, ∀ σ ∈ rows, x ≠ applySubst σ sink.atom) →
        x ∈ (supportProvider stage).run rows space sinks
  | [], _, _, member, _ => member
  | sink :: rest, space, x, member, notInstance => by
      rw [BatchSinkProvider.run_cons]
      apply supportProvider_keeps stages rest _ _ fun other otherMember =>
        notInstance other (List.mem_cons_of_mem _ otherMember)
      change x ∈ finalizeSupportSink sink (rows.foldl (stage sink) []) space
      unfold finalizeSupportSink
      cases sink with
      | add body => exact Finset.mem_union_left _ member
      | head count body => exact Finset.mem_union_left _ member
      | tail count body => exact Finset.mem_union_left _ member
      | remove body =>
          refine Finset.mem_sdiff.mpr ⟨member, fun staged => ?_⟩
          rcases stages _ rows [] (List.mem_toFinset.mp staged) with impossible | ⟨σ, σMember, equal⟩
          · simp at impossible
          · exact notInstance _ List.mem_cons_self σ σMember equal

/-- What a sink batch adds is an instance of one of its sink atoms. -/
theorem applyMorkSinkBatch_mem {rows : List Subst} :
    ∀ (sinks : List Sink) (space : Space) {x : Atom},
      x ∈ morkSupportSinkProvider.run rows space sinks →
        x ∈ space ∨ ∃ sink ∈ sinks, ∃ σ ∈ rows, x = applySubst σ sink.atom :=
  supportProvider_mem stageSupportSink_instances

/-- Open staging: every instance of a sink is staged, ground or not, as the
MORK engine writes template instances that keep unbound variables. -/
def stageOpenSink (sink : Sink) (staged : List Atom) (substitution : Subst) : List Atom :=
  insertSupport staged (applySubst substitution sink.atom)

theorem stageOpenSink_instances : StagesInstances stageOpenSink := by
  intro sink rows
  induction rows with
  | nil => intro staged x member; exact Or.inl member
  | cons σ rest ih =>
      intro staged x member
      simp only [List.foldl_cons] at member
      rcases ih _ member with inStage | ⟨σ', σ'Member, equal⟩
      · unfold stageOpenSink insertSupport at inStage
        split_ifs at inStage
        · exact Or.inl inStage
        · rcases List.mem_append.mp inStage with old | new
          · exact Or.inl old
          · exact Or.inr ⟨σ, List.mem_cons_self, List.mem_singleton.mp new⟩
      · exact Or.inr ⟨σ', List.mem_cons_of_mem σ σ'Member, equal⟩

/-- On ground instances the two stagings agree. -/
theorem stageOpenSink_eq_of_ground (sink : Sink) (staged : List Atom) (σ : Subst)
    (ground : isGroundAtom (applySubst σ sink.atom) = true) :
    stageOpenSink sink staged σ = stageSupportSink sink staged σ := by
  cases sink <;> simp_all [stageOpenSink, stageSupportSink, Sink.atom]

theorem stageOpen_fold_eq_of_ground {sink : Sink} :
    ∀ (rows : List Subst) (staged : List Atom),
      (∀ σ ∈ rows, isGroundAtom (applySubst σ sink.atom) = true) →
        rows.foldl (stageOpenSink sink) staged = rows.foldl (stageSupportSink sink) staged
  | [], _, _ => rfl
  | σ :: rest, staged, ground => by
      simp only [List.foldl_cons]
      rw [stageOpenSink_eq_of_ground sink staged σ (ground σ List.mem_cons_self)]
      exact stageOpen_fold_eq_of_ground rest _ fun σ' member => ground σ' (List.mem_cons_of_mem _ member)

/-- When every instance is ground, the open batch is the ground-only batch. -/
theorem openRun_eq_of_ground {rows : List Subst} :
    ∀ (sinks : List Sink) (space : Space),
      (∀ sink ∈ sinks, ∀ σ ∈ rows, isGroundAtom (applySubst σ sink.atom) = true) →
        (supportProvider stageOpenSink).run rows space sinks = morkSupportSinkProvider.run rows space sinks
  | [], _, _ => rfl
  | sink :: rest, space, ground => by
      rw [BatchSinkProvider.run_cons, BatchSinkProvider.run_cons]
      change (supportProvider stageOpenSink).run rows
          (finalizeSupportSink sink (rows.foldl (stageOpenSink sink) []) space) rest =
        morkSupportSinkProvider.run rows
          (finalizeSupportSink sink (rows.foldl (stageSupportSink sink) []) space) rest
      rw [stageOpen_fold_eq_of_ground rows [] (ground sink List.mem_cons_self)]
      exact openRun_eq_of_ground rest _ fun other member => ground other (List.mem_cons_of_mem _ member)


/-! ## What a step can produce -/

/-- The input conjuncts of an executable, as the work queue reads them. -/
def conjunctsOf : Atom → List Atom
  | .expression (.symbol "," :: rest) => rest
  | _ => []

/-- An extracted executable: its shell, its conjuncts, and sinks whose atoms
occur in its output. -/
theorem extractExecFact_spec {a : Atom} {ef : ExecFact} (h : extractExecFact a = some ef) :
    ∃ loc input output, a = .expression [.symbol "exec", loc, input, output] ∧ ef.atom = a ∧
      ef.rule.pat.atoms = conjunctsOf input ∧ ∀ sink ∈ ef.rule.tmpl.sinks, Occurs sink.atom output := by
  unfold extractExecFact at h
  split at h
  · rename_i loc input output
    simp only [Option.some.injEq] at h
    subst h
    refine ⟨loc, input, output, rfl, rfl, ?_, ?_⟩
    · simp only [mkExecRule, mkPattern]
      split <;> simp_all [conjunctsOf]
    · intro sink member
      simp only [mkExecRule, mkTemplate] at member
      split at member
      · rename_i rest
        obtain ⟨s, sMember, parsed⟩ := List.mem_filterMap.mp member
        have inS : Occurs sink.atom s := by
          split at parsed
          · cases parsed
            exact .child (List.mem_cons_of_mem _ List.mem_cons_self) .here
          · cases parsed
            exact .child (List.mem_cons_of_mem _ List.mem_cons_self) .here
          · rename_i count body
            rw [parseExtremaSink_atom_eq_body true count body sink parsed]
            exact .child (by simp) .here
          · rename_i count body
            rw [parseExtremaSink_atom_eq_body false count body sink parsed]
            exact .child (by simp) .here
          · cases parsed
        exact .child (List.mem_cons_of_mem _ sMember) inS
      · simp at member
  · cases h

/-- A selected executable is an extracted atom of the space. -/
theorem workQueueStep_spec {space next : Space} (step : workQueueStep space = some next) :
    ∃ ef, extractExecFact ef.atom = some ef ∧ ef.atom ∈ space ∧
      selectNextExec (execFactsOfSpace space) = some ef ∧ next = fireExecFact space ef := by
  unfold workQueueStep at step
  simp only at step
  cases selected : selectNextExec (execFactsOfSpace space) with
  | none => rw [selected] at step; cases step
  | some ef =>
      rw [selected] at step
      cases step
      have member := selectNextScheduled_mem selected
      obtain ⟨a, aMember, extracted⟩ := List.mem_filterMap.mp member
      have atomEq := extractExecFact_atom a ef extracted
      subst atomEq
      exact ⟨ef, extracted, Finset.mem_toList.mp aMember, rfl, rfl⟩

/-- **A firing creates no leaf**: a symbol or grounded value absent from the
space is absent after any firing. -/
theorem fireExecFact_leafFree {leaf : Atom} (isLeaf : IsLeaf leaf) {space : Space} {ef : ExecFact}
    (extracted : extractExecFact ef.atom = some ef) (present : ef.atom ∈ space)
    (free : ∀ a ∈ space, ¬ Occurs leaf a) : ∀ a ∈ fireExecFact space ef, ¬ Occurs leaf a := by
  intro a member inside
  obtain ⟨loc, input, output, shape, _, _, sinksOccur⟩ := extractExecFact_spec extracted
  rcases applyMorkSinkBatch_mem ef.rule.tmpl.sinks _ member with old | ⟨sink, sinkMember, σ, σMember, rfl⟩
  · exact free a (Finset.mem_of_mem_erase old) inside
  · rcases applySubst_occurs isLeaf σ sink.atom inside with inSink | ⟨p, pMember, inValue⟩
    · apply free ef.atom present
      rw [shape]
      exact (inSink.trans (sinksOccur sink sinkMember)).trans (.child (by simp) .here)
    · obtain ⟨_, _, atom, atomMember, _, inAtom⟩ := matchPattern_binding σMember p pMember
      rw [readCopy_eq_of_mem space ef present] at atomMember
      exact free atom atomMember (inValue.trans inAtom)

theorem workQueueStep_leafFree {leaf : Atom} (isLeaf : IsLeaf leaf) {space next : Space}
    (step : workQueueStep space = some next) (free : ∀ a ∈ space, ¬ Occurs leaf a) :
    ∀ a ∈ next, ¬ Occurs leaf a := by
  obtain ⟨ef, extracted, present, _, rfl⟩ := workQueueStep_spec step
  exact fireExecFact_leafFree isLeaf extracted present free

/-- Leaf-free spaces stay leaf-free along every run. -/
theorem workQueueRunN_leafFree {leaf : Atom} (isLeaf : IsLeaf leaf) :
    ∀ (fuel : ℕ) (space : Space), (∀ a ∈ space, ¬ Occurs leaf a) →
      ∀ a ∈ (workQueueRunN fuel space).1, ¬ Occurs leaf a
  | 0, _, free => free
  | fuel + 1, space, free => by
      simp only [workQueueRunN]
      cases step : workQueueStep space with
      | none => exact free
      | some next => exact workQueueRunN_leafFree isLeaf fuel next (workQueueStep_leafFree isLeaf step free)

/-! ## Monotonicity of conjunctive matching -/

theorem matchPattern_go_mono {small large : Space} (sub : small ⊆ large) :
    ∀ (conjuncts : List Atom) (σ₀ : Subst) (witnesses : Finset Atom) (row : Subst × Finset Atom),
      row ∈ matchPattern.go small conjuncts σ₀ witnesses →
        ∃ row' ∈ matchPattern.go large conjuncts σ₀ witnesses, row'.1 = row.1
  | [], σ₀, witnesses, row, member => ⟨row, member, rfl⟩
  | conjunct :: rest, σ₀, witnesses, row, member => by
      simp only [matchPattern.go, List.mem_flatMap] at member ⊢
      obtain ⟨⟨σ₁, atom⟩, matched, inRest⟩ := member
      obtain ⟨atomMember, matchedEq⟩ := matchOneInSpace_spec σ₀ conjunct small σ₁ atom matched
      obtain ⟨row', member', same⟩ := matchPattern_go_mono sub rest σ₁ _ row inRest
      exact ⟨row', ⟨(σ₁, atom), matchOneInSpace_mem σ₀ conjunct large atom (sub atomMember) σ₁ matchedEq,
        member'⟩, same⟩

/-- **Conjunctive matching is monotone**: a row found in a space is found in
every larger space. -/
theorem matchPattern_mono {small large : Space} (sub : small ⊆ large) (pattern : Pattern)
    {σ : Subst} (member : σ ∈ (matchPattern [] small pattern).map Prod.fst) :
    σ ∈ (matchPattern [] large pattern).map Prod.fst := by
  obtain ⟨row, rowMember, rfl⟩ := List.mem_map.mp member
  obtain ⟨row', member', same⟩ := matchPattern_go_mono sub pattern.atoms [] ∅ row rowMember
  exact List.mem_map.mpr ⟨row', member', same⟩

/-! ## Absence is not eliminable -/

/-- An absence conjunct `(not P)`. -/
def absenceOf? : Atom → Option Atom
  | .expression [.symbol "not", inner] => some inner
  | _ => none

/-- The rows of an executable with absence conjuncts: the rows of the other
conjuncts that leave every `(not P)` unmatched in the read copy. -/
noncomputable def absenceRows (space : Space) (ef : ExecFact) : List Subst :=
  ((matchPattern [] (readCopy space ef)
      ⟨ef.rule.pat.atoms.filter fun conjunct => (absenceOf? conjunct).isNone⟩).map Prod.fst).filter
    fun σ => (ef.rule.pat.atoms.filterMap absenceOf?).all fun inner =>
      (matchOneInSpace σ inner (readCopy space ef)).isEmpty

/-- MM2 with absence conjuncts. -/
noncomputable def fireAbsence (space : Space) (ef : ExecFact) : Space :=
  applyMorkSinkBatch (consumeExec space ef) (absenceRows space ef) ef.rule.tmpl

/-- One step of MM2 with absence conjuncts. -/
noncomputable def absenceStep (space : Space) : Option Space :=
  match selectNextExec (execFactsOfSpace space) with
  | none => none
  | some ef => some (fireAbsence space ef)

/-- Runs of MM2 with absence conjuncts. -/
noncomputable def absenceRunN : ℕ → Space → Space
  | 0, space => space
  | fuel + 1, space =>
      match absenceStep space with
      | none => space
      | some next => absenceRunN fuel next

/-- The extension is conservative: an executable without absence conjuncts fires
as in MM2. -/
theorem fireAbsence_eq_of_no_absence (space : Space) (ef : ExecFact)
    (none : ∀ conjunct ∈ ef.rule.pat.atoms, absenceOf? conjunct = none) :
    fireAbsence space ef = fireExecFact space ef := by
  unfold fireAbsence fireExecFact absenceRows
  have positive : ef.rule.pat.atoms.filter (fun conjunct => (absenceOf? conjunct).isNone) =
      ef.rule.pat.atoms :=
    List.filter_eq_self.mpr fun conjunct member => by simp [none conjunct member]
  have negative : ef.rule.pat.atoms.filterMap absenceOf? = [] :=
    List.filterMap_eq_nil_iff.mpr fun conjunct member => none conjunct member
  simp only [positive, negative, List.all_nil, List.filter_true]

/-- A local translation of absence conjuncts (Felleisen's eliminability): atoms
without the reserved symbol `not` are kept, unions are kept, and an
executable whose input is one absence conjunct keeps its location and output,
its conjunct being replaced by MM2 conjuncts that depend only on it.  The class
is not empty (`dropAbsence`). -/
structure AbsenceElimination where
  map : Space → Space
  expand : Atom → List Atom
  map_union : ∀ first second : Space, map (first ∪ second) = map first ∪ map second
  map_plain : ∀ a : Atom, ¬ Occurs (.symbol "not") a → map {a} = {a}
  map_exec : ∀ (loc inner output : Atom), ¬ Occurs (.symbol "not") loc → ¬ Occurs (.symbol "not") output →
    map {.expression [.symbol "exec", loc,
      .expression [.symbol ",", .expression [.symbol "not", inner]], output]} =
    {.expression [.symbol "exec", loc, .expression (.symbol "," :: expand inner), output]}

/-- The observed output `(out)`. -/
def outAtom : Atom := .expression [.symbol "out"]

/-- The location `(z)`. -/
def locZ : Atom := .expression [.symbol "z"]

/-- `(O (+ (out)))`. -/
def outputOut : Atom := .expression [.symbol "O", .expression [.symbol "+", outAtom]]

/-- `(exec (z) (, (not (p))) (O (+ (out))))`: output `(out)` if `(p)` is absent. -/
def absenceExec : Atom :=
  .expression [.symbol "exec", locZ,
    .expression [.symbol ",", .expression [.symbol "not", .expression [.symbol "p"]]], outputOut]

/-- The atom `(p)`. -/
def pAtom : Atom := .expression [.symbol "p"]


/-! ### Runs of small programs -/

theorem filterMap_single {α β : Type} {f : α → Option β} :
    ∀ {l : List α} {x : α} {y : β}, l.Nodup → x ∈ l → f x = some y →
      (∀ a ∈ l, a ≠ x → f a = none) → l.filterMap f = [y]
  | [], _, _, _, member, _, _ => by simp at member
  | a :: rest, x, y, nodup, member, image, others => by
      obtain ⟨notIn, restNodup⟩ := List.nodup_cons.mp nodup
      by_cases same : a = x
      · subst same
        have restNone : rest.filterMap f = [] :=
          List.filterMap_eq_nil_iff.mpr fun b hb =>
            others b (List.mem_cons_of_mem _ hb) fun equal => notIn (equal ▸ hb)
        simp [image, restNone]
      · have restMember : x ∈ rest := (List.mem_cons.mp member).resolve_left (Ne.symm same)
        rw [List.filterMap_cons, others a List.mem_cons_self same]
        exact filterMap_single restNodup restMember image
          fun b hb hne => others b (List.mem_cons_of_mem _ hb) hne

theorem execFactsOfSpace_single {space : Space} {x : Atom} {ef : ExecFact}
    (extracted : extractExecFact x = some ef) (member : x ∈ space)
    (others : ∀ a ∈ space, a ≠ x → extractExecFact a = none) :
    execFactsOfSpace space = [ef] :=
  filterMap_single (Finset.nodup_toList space) (Finset.mem_toList.mpr member) extracted
    fun a ha hne => others a (Finset.mem_toList.mp ha) hne

theorem execFactsOfSpace_nil {space : Space} (noExec : ∀ a ∈ space, extractExecFact a = none) :
    execFactsOfSpace space = [] :=
  List.filterMap_eq_nil_iff.mpr fun a ha => noExec a (Finset.mem_toList.mp ha)

theorem workQueueStep_of_single {space : Space} {x : Atom} {ef : ExecFact}
    (extracted : extractExecFact x = some ef) (member : x ∈ space)
    (others : ∀ a ∈ space, a ≠ x → extractExecFact a = none) :
    workQueueStep space = some (fireExecFact space ef) := by
  unfold workQueueStep
  simp only [execFactsOfSpace_single extracted member others]
  rfl

theorem workQueueStep_of_none {space : Space} (noExec : ∀ a ∈ space, extractExecFact a = none) :
    workQueueStep space = none := by
  unfold workQueueStep
  simp only [execFactsOfSpace_nil noExec]
  rfl

/-- After a step into a space without executables, the run stays there. -/
theorem workQueueRunN_after_last {space next : Space} (step : workQueueStep space = some next)
    (noExec : ∀ a ∈ next, extractExecFact a = none) :
    ∀ fuel, (workQueueRunN (fuel + 1) space).1 = next := by
  intro fuel
  have stays : ∀ fuel, (workQueueRunN fuel next).1 = next := by
    intro fuel
    cases fuel with
    | zero => rfl
    | succ fuel => simp [workQueueRunN, workQueueStep_of_none noExec]
  simp [workQueueRunN, step, stays]

theorem absenceStep_of_single {space : Space} {x : Atom} {ef : ExecFact}
    (extracted : extractExecFact x = some ef) (member : x ∈ space)
    (others : ∀ a ∈ space, a ≠ x → extractExecFact a = none) :
    absenceStep space = some (fireAbsence space ef) := by
  unfold absenceStep
  simp only [execFactsOfSpace_single extracted member others]
  rfl

theorem absenceRunN_after_last {space next : Space} (step : absenceStep space = some next)
    (noExec : ∀ a ∈ next, extractExecFact a = none) :
    ∀ fuel, absenceRunN (fuel + 1) space = next := by
  intro fuel
  have stays : ∀ fuel, absenceRunN fuel next = next := by
    intro fuel
    cases fuel with
    | zero => rfl
    | succ fuel =>
        have noStep : absenceStep next = Option.none := by
          unfold absenceStep
          simp only [execFactsOfSpace_nil noExec]
          rfl
        simp [absenceRunN, noStep]
  simp [absenceRunN, step, stays]

/-- An added ground atom is in the result of a one-sink batch with a row. -/
theorem add_mem_of_row {space : Space} {rows : List Subst} {body : Atom} {σ : Subst}
    (member : σ ∈ rows) (ground : isGroundAtom (applySubst σ body) = true) :
    applySubst σ body ∈ applyMorkSinkBatch space rows ⟨[.add body]⟩ := by
  show applySubst σ body ∈ finalizeSupportSink (.add body) (rows.foldl (stageSupportSink (.add body)) []) space
  unfold finalizeSupportSink
  exact Finset.mem_union_right _ (List.mem_toFinset.mpr (stage_add_mem rows [] member ground))

/-! ### The theorem -/

/-- The translated executable. -/
def absenceTarget (E : AbsenceElimination) : Atom :=
  .expression [.symbol "exec", locZ, .expression (.symbol "," :: E.expand pAtom), outputOut]

/-- What the work queue reads from it. -/
def absenceTargetFact (E : AbsenceElimination) : ExecFact :=
  ⟨absenceTarget E, locZ, mkExecRule 0 "unnamed" ⟨E.expand pAtom⟩ ⟨[.add outAtom]⟩⟩

theorem extract_absenceTarget (E : AbsenceElimination) :
    extractExecFact (absenceTarget E) = some (absenceTargetFact E) := rfl

/-- What the work queue reads from the source executable. -/
def absenceFact : ExecFact :=
  ⟨absenceExec, locZ, mkExecRule 0 "unnamed" ⟨[.expression [.symbol "not", pAtom]]⟩ ⟨[.add outAtom]⟩⟩

theorem extract_absenceExec : extractExecFact absenceExec = some absenceFact := rfl

theorem extract_pAtom : extractExecFact pAtom = none := rfl

theorem extract_outAtom : extractExecFact outAtom = none := rfl

/-- Occurrence, decided. -/
def occursB (leaf : Atom) : Atom → Bool
  | .expression children => decide (Atom.expression children = leaf) || childrenB children
  | other => decide (other = leaf)
where
  childrenB : List Atom → Bool
    | [] => false
    | child :: rest => occursB leaf child || childrenB rest

theorem occursB_iff (leaf : Atom) : ∀ a : Atom, occursB leaf a = true ↔ Occurs leaf a
  | .expression children => by
      simp only [occursB, Bool.or_eq_true, decide_eq_true_eq]
      constructor
      · rintro (rfl | inChildren)
        · exact .here
        · obtain ⟨child, member, inside⟩ := (childrenCase children).mp inChildren
          exact .child member inside
      · intro h
        cases h with
        | here => exact Or.inl rfl
        | child member inside => exact Or.inr ((childrenCase children).mpr ⟨_, member, inside⟩)
  | .var name => by
      simp only [occursB, decide_eq_true_eq]
      constructor
      · rintro rfl; exact .here
      · intro h; cases h; rfl
  | .symbol name => by
      simp only [occursB, decide_eq_true_eq]
      constructor
      · rintro rfl; exact .here
      · intro h; cases h; rfl
  | .grounded value => by
      simp only [occursB, decide_eq_true_eq]
      constructor
      · rintro rfl; exact .here
      · intro h; cases h; rfl
where
  childrenCase : ∀ children : List Atom,
      occursB.childrenB leaf children = true ↔ ∃ child ∈ children, Occurs leaf child
    | [] => by simp [occursB.childrenB]
    | child :: rest => by
        simp only [occursB.childrenB, Bool.or_eq_true, occursB_iff leaf child, childrenCase rest,
          List.mem_cons]
        constructor
        · rintro (inside | ⟨other, member, inside⟩)
          · exact ⟨child, Or.inl rfl, inside⟩
          · exact ⟨other, Or.inr member, inside⟩
        · rintro ⟨other, rfl | member, inside⟩
          · exact Or.inl inside
          · exact Or.inr ⟨other, member, inside⟩

theorem not_occurs_of_occursB {leaf a : Atom} (h : occursB leaf a = false) : ¬ Occurs leaf a :=
  fun inside => by rw [(occursB_iff leaf a).mpr inside] at h; cases h

theorem occursB_false {leaf a : Atom} (absent : ¬ Occurs leaf a) : occursB leaf a = false := by
  cases h : occursB leaf a
  · rfl
  · exact absurd ((occursB_iff leaf a).mp h) absent

/-- Erase an absence conjunct that is an executable's whole input. -/
def dropAbsenceAtom (a : Atom) : Atom :=
  match a with
  | .expression [.symbol "exec", loc, .expression [.symbol ",", .expression [.symbol "not", inner]],
      output] =>
      if occursB (.symbol "not") loc = false ∧ occursB (.symbol "not") output = false then
        .expression [.symbol "exec", loc, .expression [.symbol ","], output]
      else .expression [.symbol "exec", loc,
        .expression [.symbol ",", .expression [.symbol "not", inner]], output]
  | other => other

/-- **The class of local translations is not empty**: dropping every absence
conjunct is one (a wrong one, as all are). -/
def dropAbsence : AbsenceElimination where
  map space := space.image dropAbsenceAtom
  expand _ := []
  map_union first second := Finset.image_union first second
  map_plain a free := by
    rw [Finset.image_singleton]
    congr 1
    unfold dropAbsenceAtom
    split
    · rename_i loc inner output
      exact (free (.child (child := .expression [.symbol ",", .expression [.symbol "not", inner]])
        (by simp) (.child (child := .expression [.symbol "not", inner]) (by simp)
          (.child (by simp) .here)))).elim
    · rfl
  map_exec loc inner output freeLoc freeOutput := by
    rw [Finset.image_singleton]
    congr 1
    simp only [dropAbsenceAtom]
    rw [if_pos ⟨occursB_false freeLoc, occursB_false freeOutput⟩]

theorem notFree_locZ : ¬ Occurs (.symbol "not") locZ := not_occurs_of_occursB (by decide)

theorem notFree_outputOut : ¬ Occurs (.symbol "not") outputOut := not_occurs_of_occursB (by decide)

theorem notFree_pAtom : ¬ Occurs (.symbol "not") pAtom := not_occurs_of_occursB (by decide)

theorem matchAtom_p_absenceExec : matchAtom [] pAtom absenceExec = none := by decide

theorem matchAtom_p_p : matchAtom [] pAtom pAtom = some [] := by decide

theorem absenceFact_atoms : absenceFact.rule.pat.atoms = [.expression [.symbol "not", pAtom]] := rfl

theorem absenceFact_positive :
    absenceFact.rule.pat.atoms.filter (fun conjunct => (absenceOf? conjunct).isNone) = [] := rfl

theorem absenceFact_negative : absenceFact.rule.pat.atoms.filterMap absenceOf? = [pAtom] := rfl

theorem matchPattern_nil_rows (space : Space) :
    (matchPattern [] space ⟨[]⟩).map Prod.fst = [[]] := rfl

/-- Without `(p)`, the source executable has the empty row. -/
theorem absenceRows_small : [] ∈ absenceRows {absenceExec} absenceFact := by
  unfold absenceRows
  rw [readCopy_eq_of_mem {absenceExec} absenceFact (Finset.mem_singleton_self _), absenceFact_positive,
    absenceFact_negative, matchPattern_nil_rows]
  have unmatched : matchOneInSpace [] pAtom {absenceExec} = [] := by
    unfold matchOneInSpace
    rw [Finset.toList_singleton]
    simp [matchAtom_p_absenceExec]
  simp [unmatched]

/-- With `(p)`, it has no row. -/
theorem absenceRows_large : absenceRows ({absenceExec} ∪ {pAtom}) absenceFact = [] := by
  unfold absenceRows
  rw [readCopy_eq_of_mem ({absenceExec} ∪ {pAtom}) absenceFact (by simp [absenceFact]),
    absenceFact_positive, absenceFact_negative, matchPattern_nil_rows]
  have matched : (matchOneInSpace [] pAtom ({absenceExec} ∪ {pAtom})).isEmpty = false := by
    have found := matchOneInSpace_mem [] pAtom ({absenceExec} ∪ {pAtom}) pAtom (by simp) [] matchAtom_p_p
    cases h : matchOneInSpace [] pAtom ({absenceExec} ∪ {pAtom}) with
    | nil => rw [h] at found; simp at found
    | cons _ _ => rfl
  simp only [List.filter_cons, List.filter_nil, List.all_cons, List.all_nil, Bool.and_true, matched]
  rfl

/-- **Absence is not eliminable from MM2.**  For every local translation, one
of the programs `{(exec (z) (, (not (p))) (O (+ (out))))}` and the same with
`(p)` added is observed differently: the translated input is a conjunctive
pattern, monotone in the space, so its executable fires in the larger space
whenever it fires in the smaller one. -/
theorem absence_not_eliminable (E : AbsenceElimination) :
    ∃ program : Space,
      ¬ ((∃ fuel, outAtom ∈ absenceRunN fuel program) ↔
        ∃ fuel, outAtom ∈ (workQueueRunN fuel (E.map program)).1) := by
  have mapSmall : E.map {absenceExec} = {absenceTarget E} :=
    E.map_exec locZ pAtom outputOut notFree_locZ notFree_outputOut
  have mapLarge : E.map ({absenceExec} ∪ {pAtom}) = {absenceTarget E} ∪ {pAtom} := by
    rw [E.map_union, mapSmall, E.map_plain pAtom notFree_pAtom]
  have outGround : ∀ σ : Subst, isGroundAtom (applySubst σ outAtom) = true := fun _ => rfl
  have outNotExec : ∀ a : Atom, a = outAtom → extractExecFact a = none := by
    rintro a rfl; exact extract_outAtom
  by_cases rowsEmpty :
      (matchPattern [] {absenceTarget E} ⟨E.expand pAtom⟩).map Prod.fst = []
  · -- The translation does not fire without `(p)`; the source does.
    refine ⟨{absenceExec}, fun same => ?_⟩
    have sourceStep := absenceStep_of_single extract_absenceExec (Finset.mem_singleton_self _)
      (fun a ha hne => absurd (Finset.mem_singleton.mp ha) hne)
    have sourceReaches : ∃ fuel, outAtom ∈ absenceRunN fuel {absenceExec} := by
      refine ⟨1, ?_⟩
      simp only [absenceRunN, sourceStep]
      exact add_mem_of_row (body := outAtom) absenceRows_small (outGround [])
    obtain ⟨fuel, reached⟩ := same.mp sourceReaches
    rw [mapSmall] at reached
    have targetStep := workQueueStep_of_single (extract_absenceTarget E) (Finset.mem_singleton_self _)
      (fun a ha hne => absurd (Finset.mem_singleton.mp ha) hne)
    have targetNext : fireExecFact {absenceTarget E} (absenceTargetFact E) = ∅ := by
      show applyMorkSinkBatch (consumeExec {absenceTarget E} (absenceTargetFact E))
        ((matchPattern [] (readCopy {absenceTarget E} (absenceTargetFact E)) ⟨E.expand pAtom⟩).map
          Prod.fst) ⟨[.add outAtom]⟩ = ∅
      rw [readCopy_eq_of_mem {absenceTarget E} (absenceTargetFact E) (Finset.mem_singleton_self _),
        rowsEmpty, applyMorkSinkBatch_empty]
      simp [consumeExec, absenceTargetFact]
    rw [targetNext] at targetStep
    cases fuel with
    | zero =>
        have : outAtom ≠ absenceTarget E := by simp [outAtom, absenceTarget]
        simp [workQueueRunN, this] at reached
    | succ fuel =>
        rw [workQueueRunN_after_last targetStep (fun a ha => by simp at ha) fuel] at reached
        simp at reached
  · -- The translation fires without `(p)`, hence with it; the source does not.
    refine ⟨{absenceExec} ∪ {pAtom}, fun same => ?_⟩
    obtain ⟨σ, σMember⟩ := List.exists_mem_of_ne_nil _ rowsEmpty
    have largeRow :
        σ ∈ (matchPattern [] ({absenceTarget E} ∪ {pAtom}) ⟨E.expand pAtom⟩).map Prod.fst :=
      matchPattern_mono Finset.subset_union_left _ σMember
    have others : ∀ a ∈ ({absenceTarget E} ∪ {pAtom} : Space), a ≠ absenceTarget E →
        extractExecFact a = none := by
      intro a ha hne
      rcases Finset.mem_union.mp ha with ha | ha
      · exact absurd (Finset.mem_singleton.mp ha) hne
      · rw [Finset.mem_singleton.mp ha]; exact extract_pAtom
    have targetStep := workQueueStep_of_single (extract_absenceTarget E) (by simp) others
    have targetReaches :
        ∃ fuel, outAtom ∈ (workQueueRunN fuel (E.map ({absenceExec} ∪ {pAtom}))).1 := by
      refine ⟨1, ?_⟩
      rw [mapLarge]
      simp only [workQueueRunN, targetStep]
      show outAtom ∈ applyMorkSinkBatch (consumeExec ({absenceTarget E} ∪ {pAtom}) (absenceTargetFact E))
        ((matchPattern [] (readCopy ({absenceTarget E} ∪ {pAtom}) (absenceTargetFact E))
          ⟨E.expand pAtom⟩).map Prod.fst) ⟨[.add outAtom]⟩
      rw [readCopy_eq_of_mem _ (absenceTargetFact E) (by simp [absenceTargetFact])]
      exact add_mem_of_row (body := outAtom) largeRow (outGround σ)
    obtain ⟨fuel, reached⟩ := same.mpr targetReaches
    have sourceStep := absenceStep_of_single (space := {absenceExec} ∪ {pAtom}) extract_absenceExec
      (by simp) (fun a ha hne => by
      rcases Finset.mem_union.mp ha with ha | ha
      · exact absurd (Finset.mem_singleton.mp ha) hne
      · rw [Finset.mem_singleton.mp ha]; exact extract_pAtom)
    have sourceNext : fireAbsence ({absenceExec} ∪ {pAtom}) absenceFact ⊆ {pAtom} := by
      intro a ha
      unfold fireAbsence at ha
      rw [absenceRows_large, applyMorkSinkBatch_empty] at ha
      simp only [consumeExec, Finset.mem_erase, Finset.mem_union, Finset.mem_singleton] at ha
      rcases ha with ⟨hne, rfl | rfl⟩
      · exact absurd rfl hne
      · exact Finset.mem_singleton_self _
    cases fuel with
    | zero =>
        have : outAtom ≠ absenceExec := by simp [outAtom, absenceExec]
        have : outAtom ≠ pAtom := by simp [outAtom, pAtom]
        simp_all [absenceRunN]
    | succ fuel =>
        rw [absenceRunN_after_last sourceStep (fun a ha => by
          rw [Finset.mem_singleton.mp (sourceNext ha)]; exact extract_pAtom) fuel] at reached
        have : outAtom ≠ pAtom := by simp [outAtom, pAtom]
        exact this (Finset.mem_singleton.mp (sourceNext reached))

#print axioms absence_not_eliminable


/-! ## Synchronous call and return

The extension adds an output sink `(call F A $r S₁ … Sₖ)`: in the same firing,
call `F` on `A`, and for each result `b` of an equation `(= (F A) b)` of the
read copy, run the sinks `Sᵢ` with `$r` bound to `b` and every binding of the
caller kept.  This is call and return at its simplest: the result returns
into the caller's continuation, within the caller's firing. -/

/-- A call sink. -/
structure CallSink where
  function : Atom
  argument : Atom
  result : String
  sinks : List Sink

/-- Ordinary sinks, read as the work queue reads them. -/
def parseBaseSink : Atom → Option Sink
  | .expression [.symbol "+", body] => some (.add body)
  | .expression [.symbol "-", body] => some (.remove body)
  | .expression [.symbol "head", count, body] => parseExtremaSink true count body
  | .expression [.symbol "tail", count, body] => parseExtremaSink false count body
  | _ => none

/-- `(call F A $r S₁ … Sₖ)`. -/
def parseCallSink : Atom → Option CallSink
  | .expression (.symbol "call" :: function :: argument :: .var result :: sinks) =>
      some ⟨function, argument, result, sinks.filterMap parseBaseSink⟩
  | _ => none

/-- The call sinks of an executable's output. -/
def callSinksOf : Atom → List CallSink
  | .expression [.symbol "exec", _, _, .expression (.symbol "O" :: sinks)] =>
      sinks.filterMap parseCallSink
  | _ => []

/-- The results of `(F A)`: every `b` with `(= (F A) b)` in the space. -/
noncomputable def callResults (space : Space) (function argument : Atom) : List Atom :=
  space.toList.filterMap fun atom =>
    match atom with
    | .expression [.symbol "=", .expression [f, a], b] =>
        if f = function ∧ a = argument then some b else none
    | _ => none

/-- The rows a call sink runs its sinks on. -/
noncomputable def callRows (readSpace : Space) (rows : List Subst) (call : CallSink) : List Subst :=
  rows.flatMap fun σ =>
    (callResults readSpace (applySubst σ call.function) (applySubst σ call.argument)).map
      fun result => (call.result, result) :: σ

/-- MM2 with synchronous calls: the ordinary sinks, then each call sink, in one
firing. -/
noncomputable def fireCall (space : Space) (ef : ExecFact) : Space :=
  (callSinksOf ef.atom).foldl
    (fun current call =>
      applyMorkSinkBatch current
        (callRows (readCopy space ef) ((matchPattern [] (readCopy space ef) ef.rule.pat).map Prod.fst)
          call)
        ⟨call.sinks⟩)
    (fireExecFact space ef)

/-- One step of MM2 with synchronous calls. -/
noncomputable def callStep (space : Space) : Option Space :=
  match selectNextExec (execFactsOfSpace space) with
  | none => none
  | some ef => some (fireCall space ef)

/-- Runs of MM2 with synchronous calls. -/
noncomputable def callRunN : ℕ → Space → Space
  | 0, space => space
  | fuel + 1, space =>
      match callStep space with
      | none => space
      | some next => callRunN fuel next

/-- The extension is conservative: an executable without call sinks fires as in
MM2. -/
theorem fireCall_eq_of_no_calls (space : Space) (ef : ExecFact) (none : callSinksOf ef.atom = []) :
    fireCall space ef = fireExecFact space ef := by
  simp [fireCall, none]

theorem callStep_of_single {space : Space} {x : Atom} {ef : ExecFact}
    (extracted : extractExecFact x = some ef) (member : x ∈ space)
    (others : ∀ a ∈ space, a ≠ x → extractExecFact a = none) :
    callStep space = some (fireCall space ef) := by
  unfold callStep
  simp only [execFactsOfSpace_single extracted member others]
  rfl

theorem callRunN_after_last {space next : Space} (step : callStep space = some next)
    (noExec : ∀ a ∈ next, extractExecFact a = none) :
    ∀ fuel, callRunN (fuel + 1) space = next := by
  intro fuel
  have stays : ∀ fuel, callRunN fuel next = next := by
    intro fuel
    cases fuel with
    | zero => rfl
    | succ fuel =>
        have noStep : callStep next = Option.none := by
          unfold callStep
          simp only [execFactsOfSpace_nil noExec]
          rfl
        simp [callRunN, noStep]
  simp [callRunN, step, stays]

/-- A local translation of the call sink (Felleisen's eliminability): unions
are kept, atoms without the reserved symbol `call` are kept, and an executable
whose output is one sink mentioning `call` keeps its location and input, that
sink being replaced by MM2 sinks that depend only on it (E2).  The replacement
mentions no `call` (E1), and it writes on the observation channel `out` only
if the sink it replaces does: a translation does not forge reports.  The class
is not empty (`dropCalls`). -/
structure CallElimination where
  map : Space → Space
  expand : Atom → List Atom
  map_union : ∀ first second : Space, map (first ∪ second) = map first ∪ map second
  map_plain : ∀ a : Atom, ¬ Occurs (.symbol "call") a → map {a} = {a}
  map_exec : ∀ (loc input call : Atom), Occurs (.symbol "call") call → ¬ Occurs (.symbol "call") loc →
    ¬ Occurs (.symbol "call") input →
    map {.expression [.symbol "exec", loc, input, .expression [.symbol "O", call]]} =
      {.expression [.symbol "exec", loc, input, .expression (.symbol "O" :: expand call)]}
  expand_plain : ∀ call : Atom, Occurs (.symbol "call") call →
    ∀ sink ∈ expand call, ¬ Occurs (.symbol "call") sink
  expand_quiet : ∀ call : Atom, Occurs (.symbol "call") call →
    ∀ sink ∈ expand call, Occurs (.symbol "out") sink → Occurs (.symbol "out") call

/-- The observation channel: `(out X)`. -/
def outOf (value : Atom) : Atom := .expression [.symbol "out", value]

theorem isLeaf_out : IsLeaf (.symbol "out") := Or.inl ⟨"out", rfl⟩

/-- An atom inside the output sink of an executable occurs in the executable. -/
theorem occurs_exec_sink {leaf loc input call : Atom} (inside : Occurs leaf call) :
    Occurs leaf (.expression [.symbol "exec", loc, input, .expression [.symbol "O", call]]) :=
  .child (child := .expression [.symbol "O", call]) (by simp) (.child (by simp) inside)

/-- Erase a call sink that is an executable's whole output. -/
def dropCallAtom (a : Atom) : Atom :=
  match a with
  | .expression [.symbol "exec", loc, input, .expression [.symbol "O", call]] =>
      if occursB (.symbol "call") call = true ∧ occursB (.symbol "call") loc = false ∧
          occursB (.symbol "call") input = false then
        .expression [.symbol "exec", loc, input, .expression [.symbol "O"]]
      else .expression [.symbol "exec", loc, input, .expression [.symbol "O", call]]
  | other => other

/-- **The class of local translations is not empty**: dropping every call sink
is one (a wrong one, as all are). -/
def dropCalls : CallElimination where
  map space := space.image dropCallAtom
  expand _ := []
  map_union first second := Finset.image_union first second
  map_plain a free := by
    rw [Finset.image_singleton]
    congr 1
    unfold dropCallAtom
    split
    · rename_i loc input call
      rw [if_neg]
      rintro ⟨inCall, -, -⟩
      exact free (occurs_exec_sink ((occursB_iff _ _).mp inCall))
    · rfl
  map_exec loc input call inCall freeLoc freeInput := by
    rw [Finset.image_singleton]
    congr 1
    simp only [dropCallAtom]
    rw [if_pos ⟨(occursB_iff _ _).mpr inCall, occursB_false freeLoc, occursB_false freeInput⟩]
  expand_plain _ _ _ member := absurd member List.not_mem_nil
  expand_quiet _ _ _ member := absurd member List.not_mem_nil


/-! ### Reflection: a program that reads code exposes every translation -/

/-- A row found by matching the single conjunct of a pattern. -/
theorem row_of_match {space : Space} {conjunct atom : Atom} {σ : Subst}
    (member : atom ∈ space) (matched : matchAtom [] conjunct atom = some σ) :
    σ ∈ (matchPattern [] space ⟨[conjunct]⟩).map Prod.fst := by
  have found := matchOneInSpace_mem [] conjunct space atom member σ matched
  simp only [matchPattern, matchPattern.go, List.map_flatMap, List.mem_flatMap]
  exact ⟨(σ, atom), found, by simp⟩

/-- A program's executables are selected in key order: the least present
executable is fired. -/
theorem selectNextExec_eq_of_least {space : Space} {x : Atom} {ef : ExecFact}
    (extracted : extractExecFact x = some ef) (member : x ∈ space)
    (least : ∀ a ∈ space, a ≠ x → ∀ other, extractExecFact a = some other →
      lexLt (totalMorkCompactKey x) (totalMorkCompactKey a) = true) :
    selectNextExec (execFactsOfSpace space) = some ef := by
  have atomEq := extractExecFact_atom x ef extracted
  apply selectNextScheduled_eq_some_of_mem_of_strict_minimum
  · exact List.mem_filterMap.mpr ⟨x, Finset.mem_toList.mpr member, extracted⟩
  · intro candidate candidateMember different
    obtain ⟨a, aMember, aExtracted⟩ := List.mem_filterMap.mp candidateMember
    have candidateAtom := extractExecFact_atom a candidate aExtracted
    have aNe : a ≠ x := by
      rintro rfl
      exact different (Option.some.inj (aExtracted.symm.trans extracted))
    show lexLt (totalMorkCompactKey ef.atom) (totalMorkCompactKey candidate.atom) = true
    rw [atomEq, candidateAtom]
    exact least a (Finset.mem_toList.mp aMember) aNe candidate aExtracted

/-- `(exec () (, (exec $l $i (O ($c $f $a $r $s)))) (O (+ (out $c))))`: copy the
head of any five-part output sink of any executable. -/
def readerExec : Atom :=
  .expression [.symbol "exec", .expression [],
    .expression [.symbol ",", .expression [.symbol "exec", .var "l", .var "i",
      .expression [.symbol "O", .expression [.var "c", .var "f", .var "a", .var "r", .var "s"]]]],
    .expression [.symbol "O", .expression [.symbol "+", outOf (.var "c")]]]

/-- `(call f a $r (+ (g $r)))`. -/
def callAtom : Atom :=
  .expression [.symbol "call", .symbol "f", .symbol "a", .var "r",
    .expression [.symbol "+", .expression [.symbol "g", .var "r"]]]

/-- `(exec (z) () (O (call f a $r (+ (g $r)))))`. -/
def callerExec : Atom :=
  .expression [.symbol "exec", locZ, .expression [], .expression [.symbol "O", callAtom]]

def readerFact : ExecFact :=
  ⟨readerExec, .expression [], mkExecRule 0 "unnamed"
    ⟨[.expression [.symbol "exec", .var "l", .var "i",
      .expression [.symbol "O", .expression [.var "c", .var "f", .var "a", .var "r", .var "s"]]]]⟩
    ⟨[.add (outOf (.var "c"))]⟩⟩

theorem extract_readerExec : extractExecFact readerExec = some readerFact := rfl

theorem readerExec_first :
    lexLt (totalMorkCompactKey readerExec) (totalMorkCompactKey callerExec) = true := by decide

theorem reader_matches_caller :
    matchAtom [] (.expression [.symbol "exec", .var "l", .var "i",
      .expression [.symbol "O", .expression [.var "c", .var "f", .var "a", .var "r", .var "s"]]])
      callerExec =
    some [("s", .expression [.symbol "+", .expression [.symbol "g", .var "r"]]), ("r", .var "r"),
      ("a", .symbol "a"), ("f", .symbol "f"), ("c", .symbol "call"), ("i", .expression []),
      ("l", locZ)] := by decide

theorem callFree_readerExec : ¬ Occurs (.symbol "call") readerExec := not_occurs_of_occursB (by decide)

theorem callAtom_has_call : Occurs (.symbol "call") callAtom := (occursB_iff _ _).mp (by decide)

theorem outFree_callAtom : ¬ Occurs (.symbol "out") callAtom := not_occurs_of_occursB (by decide)

theorem callFree_locZ : ¬ Occurs (.symbol "call") locZ := not_occurs_of_occursB (by decide)

theorem callFree_unit : ¬ Occurs (.symbol "call") (.expression []) := not_occurs_of_occursB (by decide)

/-- The translated caller writes no `call`. -/
theorem callFree_translated (E : CallElimination) (loc input call : Atom)
    (callIn : Occurs (.symbol "call") call)
    (freeLoc : ¬ Occurs (.symbol "call") loc) (freeInput : ¬ Occurs (.symbol "call") input) :
    ¬ Occurs (.symbol "call")
      (.expression [.symbol "exec", loc, input, .expression (.symbol "O" :: E.expand call)]) := by
  intro inside
  cases inside with
  | child member inside =>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl
      · exact not_occurs_of_occursB (by decide) inside
      · exact freeLoc inside
      · exact freeInput inside
      · cases inside with
        | child member' inside' =>
            rcases List.mem_cons.mp member' with rfl | member'
            · exact not_occurs_of_occursB (by decide) inside'
            · exact E.expand_plain call callIn _ member' inside'

/-- **Reflection: no local translation of the call sink is correct** in the support
model.  The program `{readerExec, callerExec}` copies the head of the caller's call
sink into `(out call)`; every translation removes the symbol `call`, and the support
model cannot create a symbol, so the translated program never shows `(out call)`.  The
kernel's `pure` sink can create it (`MM2FunctionCalls.forged_reflection_agrees`).  The
argument uses only these two facts, so it applies to every new construct with
a reserved symbol, sugar included: under an observer that reads code, nothing
is eliminable. -/
theorem call_not_eliminable_reflective (E : CallElimination) :
    ∃ program : Space, ¬ ((∃ fuel, outOf (.symbol "call") ∈ callRunN fuel program) ↔
      ∃ fuel, outOf (.symbol "call") ∈ (workQueueRunN fuel (E.map program)).1) := by
  refine ⟨{readerExec} ∪ {callerExec}, fun same => ?_⟩
  -- The source fires the reader first and shows `(out call)`.
  have selected : selectNextExec (execFactsOfSpace ({readerExec} ∪ {callerExec})) = some readerFact := by
    apply selectNextExec_eq_of_least extract_readerExec (by simp)
    intro a ha hne other _
    rcases Finset.mem_union.mp ha with ha | ha
    · exact absurd (Finset.mem_singleton.mp ha) hne
    · rw [Finset.mem_singleton.mp ha]; exact readerExec_first
  have sourceReaches : ∃ fuel, outOf (.symbol "call") ∈ callRunN fuel ({readerExec} ∪ {callerExec}) := by
    refine ⟨1, ?_⟩
    have step : callStep ({readerExec} ∪ {callerExec}) =
        some (fireCall ({readerExec} ∪ {callerExec}) readerFact) := by
      unfold callStep
      rw [selected]
    simp only [callRunN, step]
    rw [fireCall_eq_of_no_calls _ _ rfl]
    show outOf (.symbol "call") ∈ applyMorkSinkBatch (consumeExec ({readerExec} ∪ {callerExec}) readerFact)
      ((matchPattern [] (readCopy ({readerExec} ∪ {callerExec}) readerFact) readerFact.rule.pat).map
        Prod.fst) readerFact.rule.tmpl
    rw [readCopy_eq_of_mem _ readerFact (by simp [readerFact])]
    exact add_mem_of_row (body := outOf (.var "c"))
      (row_of_match (by simp) reader_matches_caller) rfl
  obtain ⟨fuel, reached⟩ := same.mp sourceReaches
  -- The target contains no `call`, before and after every step.
  have mapped : E.map ({readerExec} ∪ {callerExec}) =
      {readerExec} ∪ {.expression [.symbol "exec", locZ, .expression [],
        .expression (.symbol "O" :: E.expand callAtom)]} := by
    rw [E.map_union, E.map_plain readerExec callFree_readerExec,
      show callerExec = .expression [.symbol "exec", locZ, .expression [],
        .expression [.symbol "O", callAtom]] from rfl,
      E.map_exec locZ (.expression []) callAtom callAtom_has_call callFree_locZ callFree_unit]
  have free : ∀ a ∈ E.map ({readerExec} ∪ {callerExec}), ¬ Occurs (.symbol "call") a := by
    rw [mapped]
    intro a ha
    rcases Finset.mem_union.mp ha with ha | ha
    · rw [Finset.mem_singleton.mp ha]; exact callFree_readerExec
    · rw [Finset.mem_singleton.mp ha]
      exact callFree_translated E locZ (.expression []) callAtom callAtom_has_call callFree_locZ callFree_unit
  exact workQueueRunN_leafFree (Or.inl ⟨"call", rfl⟩) fuel _ free _ reached
    (.child (by simp) .here)

#print axioms call_not_eliminable_reflective


/-! ## The window: a synchronous call is not eliminable from MM2

Programs below do not read code.  A caller at the least location fires its
call; a watcher at the least location with a two-part pattern fires next and
reports what it sees.  In the source the call has already returned.  A local
translation cannot have returned: the translated caller's firing only
instantiates sinks, any later work is scheduled by executables, and every
executable that could look at the equation sorts after the watcher. -/

/-! ### Fresh values -/

/-- A bound on the grounded integers occurring in an atom. -/
def intBound : Atom → ℕ
  | .grounded (.int value) => value.natAbs
  | .expression children => boundList children
  | _ => 0
where
  boundList : List Atom → ℕ
    | [] => 0
    | child :: rest => intBound child + boundList rest

theorem intBound_le_boundList : ∀ {children : List Atom} {child : Atom}, child ∈ children →
    intBound child ≤ intBound.boundList children
  | [], _, member => by simp at member
  | head :: rest, child, member => by
      rcases List.mem_cons.mp member with rfl | member
      · simp [intBound.boundList]
      · have := intBound_le_boundList member
        simp only [intBound.boundList]
        omega

theorem intBound_occurs {value : Int} {a : Atom} (inside : Occurs (.grounded (.int value)) a) :
    value.natAbs ≤ intBound a := by
  induction inside with
  | here => simp [intBound]
  | @child children child member _ ih =>
      exact ih.trans (by simpa [intBound] using intBound_le_boundList member)

/-- An integer occurring in none of the given atoms. -/
def freshInt (atoms : List Atom) : Int := ((atoms.map intBound).sum + 1 : ℕ)

theorem freshInt_fresh (atoms : List Atom) : ∀ a ∈ atoms, ¬ Occurs (.grounded (.int (freshInt atoms))) a := by
  intro a member inside
  have bound := intBound_occurs inside
  have le : intBound a ≤ (atoms.map intBound).sum :=
    List.le_sum_of_mem (List.mem_map_of_mem member)
  simp only [freshInt, Int.natAbs_natCast] at bound
  omega

/-! ### Byte order -/

theorem lexLt_cons (x y : ℕ) (xs ys : List ℕ) :
    lexLt (x :: xs) (y :: ys) = if x < y then true else if x > y then false else lexLt xs ys := rfl

theorem lexLt_append_left : ∀ (common xs ys : List ℕ), lexLt (common ++ xs) (common ++ ys) = lexLt xs ys
  | [], _, _ => rfl
  | c :: rest, xs, ys => by
      simp only [List.cons_append, lexLt_cons, Nat.lt_irrefl, gt_iff_lt, ↓reduceIte]
      exact lexLt_append_left rest xs ys

theorem lexLt_of_lt {x y : ℕ} (lt : x < y) (xs ys : List ℕ) : lexLt (x :: xs) (y :: ys) = true := by
  simp [lexLt_cons, lt]

theorem encode_expression {environment : List String} {children : List Atom}
    {result : List ℕ × List String}
    (h : morkCompactEncodeAtom environment (.expression children) = some result) :
    ∃ tail, morkCompactEncodeAtom.encodeList environment children = some (tail, result.2) ∧
      result.1 = children.length :: tail := by
  simp only [morkCompactEncodeAtom] at h
  split_ifs at h
  cases list : morkCompactEncodeAtom.encodeList environment children with
  | none => rw [list] at h; cases h
  | some r =>
      rw [list] at h
      simp only [Option.some.injEq] at h
      subst h
      exact ⟨r.1, rfl, rfl⟩

theorem encode_head_ge_of_not_expression {environment : List String} {a : Atom}
    {bytes : List ℕ} {environment' : List String}
    (h : morkCompactEncodeAtom environment a = some (bytes, environment'))
    (notExpression : ∀ children, a ≠ .expression children) :
    ∃ first rest, bytes = first :: rest ∧ 128 ≤ first := by
  cases a with
  | expression children => exact absurd rfl (notExpression children)
  | grounded _ => simp [morkCompactEncodeAtom] at h
  | symbol name =>
      simp only [morkCompactEncodeAtom] at h
      split_ifs at h with bounds
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      exact ⟨_, _, h.1.symm, by omega⟩
  | var name =>
      simp only [morkCompactEncodeAtom] at h
      split at h
      · split_ifs at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        exact ⟨_, _, h.1.symm, by omega⟩
      · split_ifs at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        exact ⟨_, _, h.1.symm, by omega⟩

theorem encodeList_cons {environment : List String} {a : Atom} {rest : List Atom}
    {result : List ℕ × List String}
    (h : morkCompactEncodeAtom.encodeList environment (a :: rest) = some result) :
    ∃ first environment' tail, morkCompactEncodeAtom environment a = some (first, environment') ∧
      morkCompactEncodeAtom.encodeList environment' rest = some (tail, result.2) ∧
      result.1 = first ++ tail := by
  simp only [morkCompactEncodeAtom.encodeList] at h
  cases firstEq : morkCompactEncodeAtom environment a with
  | none => rw [firstEq] at h; cases h
  | some r =>
      rw [firstEq] at h
      simp only at h
      cases tailEq : morkCompactEncodeAtom.encodeList r.2 rest with
      | none => rw [tailEq] at h; cases h
      | some t =>
          rw [tailEq] at h
          simp only [Option.some.injEq] at h
          subst h
          exact ⟨r.1, r.2, t.1, rfl, by rw [tailEq], rfl⟩

/-- Every byte encoding starts with a byte. -/
theorem encode_nonempty {environment : List String} {a : Atom} {bytes : List ℕ}
    {environment' : List String} (h : morkCompactEncodeAtom environment a = some (bytes, environment')) :
    ∃ first rest, bytes = first :: rest := by
  cases a with
  | expression children =>
      obtain ⟨tail, _, equal⟩ := encode_expression h
      exact ⟨_, _, equal⟩
  | _ =>
      obtain ⟨first, rest, equal, _⟩ := encode_head_ge_of_not_expression h (by intro children; simp)
      exact ⟨first, rest, equal⟩


/-! ### The watcher -/

/-- `(g $z)`. -/
def gPattern : Atom := .expression [.symbol "g", .var "z"]

/-- `(exec () (, (g $z)) (O (+ (out $z))))`: report every `(g X)` as `(out X)`. -/
def watcherExec : Atom :=
  .expression [.symbol "exec", .expression [], .expression [.symbol ",", gPattern],
    .expression [.symbol "O", .expression [.symbol "+", outOf (.var "z")]]]

def watcherFact : ExecFact :=
  ⟨watcherExec, .expression [], mkExecRule 0 "unnamed" ⟨[gPattern]⟩ ⟨[.add (outOf (.var "z"))]⟩⟩

theorem extract_watcherExec : extractExecFact watcherExec = some watcherFact := rfl

theorem watcherKey : totalMorkCompactKey watcherExec =
    [4, 196, 101, 120, 101, 99, 0, 2, 193, 44, 2, 193, 103, 192, 2, 193, 79, 2, 193, 43, 2, 195,
      111, 117, 116, 128] := by decide

theorem encode_exec_symbol : morkCompactEncodeAtom [] (.symbol "exec") = some ([196, 101, 120, 101, 99], []) :=
  rfl

theorem encode_comma (environment : List String) :
    morkCompactEncodeAtom environment (.symbol ",") = some ([193, 44], environment) := rfl

/-- **Below the watcher, nothing can read an atom of arity three or more**: an
executable whose key does not exceed the watcher's has at most one conjunct,
and it is an expression of arity at most two. -/
theorem conjuncts_below_watcher {x : Atom} {ef : ExecFact} (extracted : extractExecFact x = some ef)
    (notAbove : lexLt (totalMorkCompactKey watcherExec) (totalMorkCompactKey x) = false) :
    ∀ conjunct ∈ ef.rule.pat.atoms, ∃ children : List Atom,
      conjunct = .expression children ∧ children.length ≤ 2 := by
  intro conjunct member
  obtain ⟨loc, input, output, shape, _, atoms, _⟩ := extractExecFact_spec extracted
  rw [atoms] at member
  obtain ⟨rest, inputEq, restMember⟩ :
      ∃ rest, input = .expression (.symbol "," :: rest) ∧ conjunct ∈ rest := by
    unfold conjunctsOf at member
    split at member
    · exact ⟨_, rfl, member⟩
    · simp at member
  subst shape inputEq
  rw [watcherKey] at notAbove
  unfold totalMorkCompactKey at notAbove
  cases key : morkCompactKey? (.expression [.symbol "exec", loc,
      .expression (.symbol "," :: rest), output]) with
  | none =>
      rw [key] at notAbove
      simp [lexLt_cons] at notAbove
  | some k =>
      rw [key, Option.getD_some] at notAbove
      unfold morkCompactKey? at key
      obtain ⟨⟨bytes, environment⟩, encoded, rfl⟩ := Option.map_eq_some_iff.mp key
      obtain ⟨tail₀, list₀, bytesEq⟩ := encode_expression encoded
      simp only at bytesEq
      subst bytesEq
      obtain ⟨b₁, e₁, t₁, encExec, list₁, tail₀Eq⟩ := encodeList_cons list₀
      rw [encode_exec_symbol] at encExec
      simp only [Option.some.injEq, Prod.mk.injEq] at encExec
      obtain ⟨rfl, rfl⟩ := encExec
      subst tail₀Eq
      obtain ⟨b₂, e₂, t₂, encLoc, list₂, t₁Eq⟩ := encodeList_cons list₁
      subst t₁Eq
      have prefixEq : ∀ tail : List ℕ, (List.length [Atom.symbol "exec", loc,
          Atom.expression (Atom.symbol "," :: rest), output]) :: ([196, 101, 120, 101, 99] ++ tail) =
          [4, 196, 101, 120, 101, 99] ++ tail := fun _ => rfl
      rw [prefixEq,
        show ([4, 196, 101, 120, 101, 99, 0, 2, 193, 44, 2, 193, 103, 192, 2, 193, 79, 2, 193, 43, 2, 195,
          111, 117, 116, 128] : List ℕ) = [4, 196, 101, 120, 101, 99] ++
          [0, 2, 193, 44, 2, 193, 103, 192, 2, 193, 79, 2, 193, 43, 2, 195, 111, 117, 116, 128] from rfl,
        lexLt_append_left] at notAbove
      -- The location is `()`.
      have locUnit : loc = .expression [] ∧ b₂ = [0] ∧ e₂ = [] := by
        cases loc with
        | expression children =>
            obtain ⟨tailLoc, listLoc, b₂Eq⟩ := encode_expression encLoc
            simp only at b₂Eq listLoc
            subst b₂Eq
            cases children with
            | nil =>
                simp only [morkCompactEncodeAtom.encodeList, Option.some.injEq, Prod.mk.injEq] at listLoc
                obtain ⟨rfl, rfl⟩ := listLoc
                exact ⟨rfl, rfl, rfl⟩
            | cons child more =>
                simp [lexLt_cons] at notAbove
        | _ =>
            obtain ⟨first, more, b₂Eq, large⟩ :=
              encode_head_ge_of_not_expression encLoc (by intro children; simp)
            subst b₂Eq
            have : (0 : ℕ) < first := by omega
            simp [lexLt_cons, this] at notAbove
      obtain ⟨rfl, rfl, rfl⟩ := locUnit
      simp only [List.cons_append, List.nil_append, lexLt_cons, Nat.lt_irrefl, gt_iff_lt,
        ↓reduceIte] at notAbove
      -- The input has one conjunct.
      obtain ⟨b₃, e₃, t₃, encInput, list₃, t₂Eq⟩ := encodeList_cons list₂
      subst t₂Eq
      obtain ⟨tailInput, listInput, b₃Eq⟩ := encode_expression encInput
      simp only at b₃Eq listInput
      subst b₃Eq
      have restSingle : rest = [conjunct] := by
        cases rest with
        | nil => simp at restMember
        | cons first more =>
            cases more with
            | nil =>
                simp only [List.mem_singleton] at restMember
                rw [restMember]
            | cons second others =>
                simp [List.cons_append, lexLt_cons] at notAbove
      subst restSingle
      obtain ⟨bComma, eComma, tComma, encComma, listConjunct, tailInputEq⟩ := encodeList_cons listInput
      rw [encode_comma] at encComma
      simp only [Option.some.injEq, Prod.mk.injEq] at encComma
      obtain ⟨rfl, rfl⟩ := encComma
      subst tailInputEq
      obtain ⟨bConjunct, eConjunct, tConjunct, encConjunct, _, tCommaEq⟩ := encodeList_cons listConjunct
      subst tCommaEq
      simp only [List.length_cons, List.length_nil, List.cons_append, List.nil_append,
        List.append_assoc, lexLt_cons, Nat.lt_irrefl, gt_iff_lt, ↓reduceIte] at notAbove
      cases conjunct with
      | expression children =>
          obtain ⟨tailConjunct, _, bConjunctEq⟩ := encode_expression encConjunct
          simp only at bConjunctEq
          subst bConjunctEq
          refine ⟨children, rfl, ?_⟩
          by_contra large
          have : 2 < children.length := by omega
          simp [List.cons_append, lexLt_cons, this] at notAbove
      | _ =>
          obtain ⟨first, more, bEq, large⟩ :=
            encode_head_ge_of_not_expression encConjunct (by intro children; simp)
          subst bEq
          have : (2 : ℕ) < first := by omega
          simp [List.cons_append, lexLt_cons, this] at notAbove


/-! ### The least key is selected -/

/-- The scheduler's fold step. -/
def schedulerStep {α : Type} [SchedulerKey α] (best : Option α) (candidate : α) : Option α :=
  match best with
  | none => some candidate
  | some incumbent =>
      if lexLt (SchedulerKey.key candidate) (SchedulerKey.key incumbent) then some candidate
      else some incumbent

/-- The incumbent beats everything seen so far. -/
def Beats {α : Type} [SchedulerKey α] (best : Option α) (seen : List α) : Prop :=
  (∀ current, best = some current → ∀ other ∈ seen,
    lexLt (SchedulerKey.key other) (SchedulerKey.key current) = false) ∧ (best = none → seen = [])

theorem Beats.step {α : Type} [SchedulerKey α] {best : Option α} {seen : List α}
    (beats : Beats best seen) (candidate : α) :
    Beats (schedulerStep best candidate) (seen ++ [candidate]) := by
  constructor
  · intro current currentEq other member
    rcases List.mem_append.mp member with old | new
    · cases best with
      | none => simp [beats.2 rfl] at old
      | some incumbent =>
          have before := beats.1 incumbent rfl other old
          by_cases smaller : lexLt (SchedulerKey.key candidate) (SchedulerKey.key incumbent) = true
          · simp only [schedulerStep, smaller, ↓reduceIte, Option.some.injEq] at currentEq
            subst currentEq
            cases h : lexLt (SchedulerKey.key other) (SchedulerKey.key candidate) with
            | false => rfl
            | true => rw [lexLt_trans _ _ _ h smaller] at before; cases before
          · simp only [schedulerStep, smaller, Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at currentEq
            subst currentEq
            exact before
    · rw [List.mem_singleton.mp new]
      cases best with
      | none =>
          simp only [schedulerStep, Option.some.injEq] at currentEq
          subst currentEq
          exact lexLt_irrefl _
      | some incumbent =>
          by_cases smaller : lexLt (SchedulerKey.key candidate) (SchedulerKey.key incumbent) = true
          · simp only [schedulerStep, smaller, ↓reduceIte, Option.some.injEq] at currentEq
            subst currentEq
            exact lexLt_irrefl _
          · simp only [schedulerStep, smaller, Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at currentEq
            subst currentEq
            simpa using smaller
  · intro h
    cases best with
    | none => simp [schedulerStep] at h
    | some incumbent =>
        simp only [schedulerStep] at h
        split at h <;> cases h

theorem Beats.foldl {α : Type} [SchedulerKey α] :
    ∀ (remaining : List α) (best : Option α) (seen : List α), Beats best seen →
      Beats (remaining.foldl schedulerStep best) (seen ++ remaining)
  | [], best, seen, beats => by simpa using beats
  | candidate :: rest, best, seen, beats => by
      have := Beats.foldl rest _ _ (beats.step candidate)
      simpa using this

theorem selectNextScheduled_least {α : Type} [SchedulerKey α] {facts : List α} {selected : α}
    (equal : selectNextScheduled facts = some selected) :
    ∀ other ∈ facts, lexLt (SchedulerKey.key other) (SchedulerKey.key selected) = false := by
  have start : Beats (none : Option α) [] := ⟨fun _ _ _ member => absurd member (List.not_mem_nil),
    fun _ => rfl⟩
  have beats := Beats.foldl facts none [] start
  change facts.foldl schedulerStep none = some selected at equal
  rw [equal] at beats
  intro other member
  exact beats.1 selected rfl other (by simpa using member)


/-! ### What one firing adds and keeps -/

theorem fireExecFact_mem {space : Space} {ef : ExecFact} {a : Atom} (member : a ∈ fireExecFact space ef) :
    (a ∈ space ∧ a ≠ ef.atom) ∨ ∃ sink ∈ ef.rule.tmpl.sinks,
      ∃ σ ∈ (matchPattern [] (readCopy space ef) ef.rule.pat).map Prod.fst, a = applySubst σ sink.atom := by
  rcases applyMorkSinkBatch_mem ef.rule.tmpl.sinks _ member with old | found
  · exact Or.inl ⟨Finset.mem_of_mem_erase old, Finset.ne_of_mem_erase old⟩
  · exact Or.inr found

theorem batch_keeps {rows : List Subst} :
    ∀ (sinks : List Sink) (space : Space) {x : Atom}, x ∈ space →
      (∀ sink ∈ sinks, ∀ σ ∈ rows, x ≠ applySubst σ sink.atom) →
        x ∈ morkSupportSinkProvider.run rows space sinks :=
  supportProvider_keeps stageSupportSink_instances

theorem fireExecFact_keeps {space : Space} {ef : ExecFact} {a : Atom} (member : a ∈ space)
    (notExec : a ≠ ef.atom)
    (notInstance : ∀ sink ∈ ef.rule.tmpl.sinks,
      ∀ σ ∈ (matchPattern [] (readCopy space ef) ef.rule.pat).map Prod.fst, a ≠ applySubst σ sink.atom) :
    a ∈ fireExecFact space ef :=
  batch_keeps ef.rule.tmpl.sinks _ (Finset.mem_erase.mpr ⟨notExec, member⟩) notInstance

/-- A leaf in an instance comes from the executable or from an atom a conjunct
matched. -/
theorem instance_leaf {leaf : Atom} (isLeaf : IsLeaf leaf) {space : Space} {ef : ExecFact}
    (extracted : extractExecFact ef.atom = some ef) {sink : Sink} (sinkMember : sink ∈ ef.rule.tmpl.sinks)
    {σ : Subst} (σMember : σ ∈ (matchPattern [] space ef.rule.pat).map Prod.fst)
    (inside : Occurs leaf (applySubst σ sink.atom)) :
    Occurs leaf ef.atom ∨ ∃ conjunct ∈ ef.rule.pat.atoms, ∃ atom ∈ space,
      (∃ σ₁ σ₂, matchAtom σ₁ conjunct atom = some σ₂) ∧ Occurs leaf atom := by
  obtain ⟨loc, input, output, shape, _, _, sinksOccur⟩ := extractExecFact_spec extracted
  rcases applySubst_occurs isLeaf σ sink.atom inside with inSink | ⟨p, pMember, inValue⟩
  · refine Or.inl ?_
    rw [shape]
    exact (inSink.trans (sinksOccur sink sinkMember)).trans (.child (by simp) .here)
  · obtain ⟨conjunct, conjunctMember, atom, atomMember, matched, inAtom⟩ :=
      matchPattern_binding σMember p pMember
    exact Or.inr ⟨conjunct, conjunctMember, atom, atomMember, matched, inValue.trans inAtom⟩

/-! ### Step semantics that fire the least executable

The window argument uses only what a firing does, not how templates are
staged.  It holds for the work queue, which stages only ground instances,
and for open templates, which stage every instance as the MORK engine does. -/

/-- Runs of a step semantics. -/
noncomputable def runWith (step : Space → Option Space) : ℕ → Space → Space
  | 0, space => space
  | fuel + 1, space =>
      match step space with
      | none => space
      | some next => runWith step fuel next

theorem workQueueRunN_eq_runWith :
    ∀ (fuel : ℕ) (space : Space), (workQueueRunN fuel space).1 = runWith workQueueStep fuel space
  | 0, _ => rfl
  | fuel + 1, space => by
      simp only [workQueueRunN, runWith]
      cases workQueueStep space with
      | none => rfl
      | some next => exact workQueueRunN_eq_runWith fuel next

theorem callRunN_eq_runWith : ∀ (fuel : ℕ) (space : Space), callRunN fuel space = runWith callStep fuel space
  | 0, _ => rfl
  | fuel + 1, space => by
      simp only [callRunN, runWith]
      cases callStep space with
      | none => rfl
      | some next => exact callRunN_eq_runWith fuel next

/-- A step semantics **fires the least executable**: a step selects an
extracted executable of the space that no executable of the space undercuts,
adds only instances of its sinks under rows of its input, and keeps every
other atom that is no such instance. -/
def FiresLeast (step : Space → Option Space) : Prop :=
  ∀ {space next : Space}, step space = some next →
    ∃ ef : ExecFact, extractExecFact ef.atom = some ef ∧ ef.atom ∈ space ∧
      (∀ other ∈ execFactsOfSpace space,
        lexLt (SchedulerKey.key other) (SchedulerKey.key ef) = false) ∧
      (∀ a ∈ next, (a ∈ space ∧ a ≠ ef.atom) ∨ ∃ sink ∈ ef.rule.tmpl.sinks,
        ∃ σ ∈ (matchPattern [] space ef.rule.pat).map Prod.fst, a = applySubst σ sink.atom) ∧
      (∀ a ∈ space, a ≠ ef.atom → (∀ sink ∈ ef.rule.tmpl.sinks,
        ∀ σ ∈ (matchPattern [] space ef.rule.pat).map Prod.fst, a ≠ applySubst σ sink.atom) →
          a ∈ next)

/-- A step that fires the least executable creates no leaf. -/
theorem FiresLeast.leafFree {step : Space → Option Space} (fires : FiresLeast step) {leaf : Atom}
    (isLeaf : IsLeaf leaf) {space next : Space} (stepEq : step space = some next)
    (free : ∀ a ∈ space, ¬ Occurs leaf a) : ∀ a ∈ next, ¬ Occurs leaf a := by
  obtain ⟨ef, extracted, present, _, mem, _⟩ := fires stepEq
  intro a member inside
  rcases mem a member with ⟨old, _⟩ | ⟨sink, sinkMember, σ, σMember, rfl⟩
  · exact free a old inside
  · rcases instance_leaf isLeaf extracted sinkMember σMember inside with
      inExec | ⟨_, _, atom, atomMember, _, inAtom⟩
    · exact free _ present inExec
    · exact free atom atomMember inAtom

theorem runWith_leafFree {step : Space → Option Space} (fires : FiresLeast step) {leaf : Atom}
    (isLeaf : IsLeaf leaf) :
    ∀ (fuel : ℕ) (space : Space), (∀ a ∈ space, ¬ Occurs leaf a) →
      ∀ a ∈ runWith step fuel space, ¬ Occurs leaf a
  | 0, _, free => free
  | fuel + 1, space, free => by
      simp only [runWith]
      cases stepEq : step space with
      | none => exact free
      | some next => exact runWith_leafFree fires isLeaf fuel next (fires.leafFree isLeaf stepEq free)

/-- The selected executable is an extracted atom of the space. -/
theorem selectNextExec_spec {space : Space} {ef : ExecFact}
    (selected : selectNextExec (execFactsOfSpace space) = some ef) :
    extractExecFact ef.atom = some ef ∧ ef.atom ∈ space := by
  have member := selectNextScheduled_mem selected
  obtain ⟨a, aMember, extracted⟩ := List.mem_filterMap.mp member
  have atomEq := extractExecFact_atom a ef extracted
  subst atomEq
  exact ⟨extracted, Finset.mem_toList.mp aMember⟩

/-- The work queue fires the least executable. -/
theorem workQueueStep_firesLeast : FiresLeast workQueueStep := by
  intro space next stepEq
  obtain ⟨ef, extracted, present, selected, rfl⟩ := workQueueStep_spec stepEq
  have readSpace := readCopy_eq_of_mem space ef present
  refine ⟨ef, extracted, present, selectNextScheduled_least selected, ?_, ?_⟩
  · intro a member
    have := fireExecFact_mem member
    rwa [readSpace] at this
  · intro a member notExec notInstance
    apply fireExecFact_keeps member notExec
    rw [readSpace]
    exact notInstance

/-- Firing with open templates: as `fireExecFact`, staging every instance. -/
noncomputable def fireOpen (space : Space) (ef : ExecFact) : Space :=
  (supportProvider stageOpenSink).run ((matchPattern [] (readCopy space ef) ef.rule.pat).map Prod.fst)
    (consumeExec space ef) ef.rule.tmpl.sinks

/-- One step of MM2 with open templates. -/
noncomputable def openStep (space : Space) : Option Space :=
  match selectNextExec (execFactsOfSpace space) with
  | none => none
  | some ef => some (fireOpen space ef)

/-- With open templates, MM2 still fires the least executable. -/
theorem openStep_firesLeast : FiresLeast openStep := by
  intro space next stepEq
  unfold openStep at stepEq
  cases selected : selectNextExec (execFactsOfSpace space) with
  | none => rw [selected] at stepEq; cases stepEq
  | some ef =>
      rw [selected] at stepEq
      cases stepEq
      obtain ⟨extracted, present⟩ := selectNextExec_spec selected
      have readSpace := readCopy_eq_of_mem space ef present
      refine ⟨ef, extracted, present, selectNextScheduled_least selected, ?_, ?_⟩
      · intro a member
        unfold fireOpen at member
        rw [readSpace] at member
        rcases supportProvider_mem stageOpenSink_instances _ _ member with old | found
        · exact Or.inl ⟨Finset.mem_of_mem_erase old, Finset.ne_of_mem_erase old⟩
        · exact Or.inr found
      · intro a member notExec notInstance
        unfold fireOpen
        rw [readSpace]
        exact supportProvider_keeps stageOpenSink_instances _ _ (Finset.mem_erase.mpr ⟨notExec, member⟩)
          notInstance

/-! ### The waiting watcher -/

/-- `(= (f a) VALUE)`. -/
def equationOf (value : Atom) : Atom := .expression [.symbol "=", .expression [.symbol "f", .symbol "a"], value]

theorem watcher_has_out : Occurs (.symbol "out") watcherExec := (occursB_iff _ _).mp (by decide)

/-- The watcher waits: it is present, `out` occurs only in it, and the value
occurs only in its equation. -/
structure Waiting (value : Atom) (space : Space) : Prop where
  present : watcherExec ∈ space
  outOnly : ∀ a ∈ space, Occurs (.symbol "out") a → a = watcherExec
  valueOnly : ∀ a ∈ space, Occurs value a → a = equationOf value

theorem watcherFact_mem {space : Space} (present : watcherExec ∈ space) :
    watcherFact ∈ execFactsOfSpace space :=
  List.mem_filterMap.mpr ⟨watcherExec, Finset.mem_toList.mpr present, extract_watcherExec⟩

theorem exec_ne_equation {ef : ExecFact} (extracted : extractExecFact ef.atom = some ef) (value : Atom) :
    ef.atom ≠ equationOf value := by
  obtain ⟨loc, input, output, shape, _, _, _⟩ := extractExecFact_spec extracted
  rw [shape]
  simp [equationOf]

/-- **One step from a waiting space**, for any step semantics that fires the
least executable: still waiting; or `out` is gone for good; or a report other
than the value has appeared. -/
theorem waiting_step {step : Space → Option Space} (fires : FiresLeast step) {value : Atom}
    (isLeaf : IsLeaf value) {space next : Space}
    (waiting : Waiting value space) (stepEq : step space = some next) :
    Waiting value next ∨ (∀ a ∈ next, ¬ Occurs (.symbol "out") a) ∨
      ∃ other, other ≠ value ∧ outOf other ∈ next := by
  obtain ⟨ef, extracted, present, least, mem, keeps⟩ := fires stepEq
  by_cases isWatcher : ef.atom = watcherExec
  · -- The watcher fires.
    have efEq : ef = watcherFact := by
      have := extracted
      rw [isWatcher, extract_watcherExec] at this
      exact (Option.some.inj this).symm
    subst efEq
    by_cases anyOut : ∃ a ∈ next, Occurs (.symbol "out") a
    · obtain ⟨a, aMember, aOut⟩ := anyOut
      right; right
      rcases mem a aMember with ⟨old, notWatcher⟩ | ⟨sink, sinkMember, σ, σMember, rfl⟩
      · exact absurd (waiting.outOnly a old aOut) notWatcher
      · have sinkEq : sink = .add (outOf (.var "z")) := by
          simpa [watcherFact, mkExecRule, mkTemplate] using sinkMember
        subst sinkEq
        refine ⟨applySubst σ (.var "z"), fun same => ?_, ?_⟩
        · have inside : Occurs value (applySubst σ (.var "z")) := same ▸ .here
          rcases applySubst_occurs isLeaf σ (.var "z") inside with inVar | ⟨p, pMember, inValue⟩
          · cases inVar
            rcases isLeaf with ⟨_, h⟩ | ⟨_, h⟩ <;> cases h
          · obtain ⟨conjunct, conjunctMember, atom, atomMember, ⟨σ₁, σ₂, matched⟩, inAtom⟩ :=
              matchPattern_binding σMember p pMember
            have conjunctEq : conjunct = gPattern := by
              simpa [watcherFact, mkExecRule, mkPattern] using conjunctMember
            subst conjunctEq
            obtain ⟨others, atomEq, lengthEq⟩ := matchAtom_expression_arity matched
            have isEquation := waiting.valueOnly atom atomMember (inValue.trans inAtom)
            rw [isEquation] at atomEq
            simp [equationOf] at atomEq
            rw [← atomEq] at lengthEq
            simp at lengthEq
        · exact aMember
    · exact Or.inr (Or.inl fun a aMember aOut => anyOut ⟨a, aMember, aOut⟩)
  · -- Another executable fires; it sorts below the watcher.
    left
    have narrow := conjuncts_below_watcher extracted (least watcherFact (watcherFact_mem waiting.present))
    -- Atoms its conjuncts match contain neither `out` nor the value.
    have matchedClean : ∀ conjunct ∈ ef.rule.pat.atoms, ∀ atom ∈ space,
        (∃ σ₁ σ₂, matchAtom σ₁ conjunct atom = some σ₂) →
          ¬ Occurs (.symbol "out") atom ∧ ¬ Occurs value atom := by
      intro conjunct conjunctMember atom atomMember ⟨σ₁, σ₂, matched⟩
      obtain ⟨children, rfl, small⟩ := narrow conjunct conjunctMember
      obtain ⟨others, atomEq, lengthEq⟩ := matchAtom_expression_arity matched
      constructor
      · intro inside
        have := waiting.outOnly atom atomMember inside
        rw [this] at atomEq
        simp [watcherExec] at atomEq
        rw [← atomEq] at lengthEq
        simp at lengthEq
        omega
      · intro inside
        have := waiting.valueOnly atom atomMember inside
        rw [this] at atomEq
        simp [equationOf] at atomEq
        rw [← atomEq] at lengthEq
        simp at lengthEq
        omega
    have efClean : ¬ Occurs (.symbol "out") ef.atom ∧ ¬ Occurs value ef.atom :=
      ⟨fun inside => isWatcher (waiting.outOnly ef.atom present inside),
        fun inside => exec_ne_equation extracted value (waiting.valueOnly ef.atom present inside)⟩
    have instanceClean : ∀ sink ∈ ef.rule.tmpl.sinks,
        ∀ σ ∈ (matchPattern [] space ef.rule.pat).map Prod.fst,
          ¬ Occurs (.symbol "out") (applySubst σ sink.atom) ∧ ¬ Occurs value (applySubst σ sink.atom) := by
      intro sink sinkMember σ σMember
      constructor
      · intro inside
        rcases instance_leaf (Or.inl ⟨"out", rfl⟩) extracted sinkMember σMember inside with
          inExec | ⟨conjunct, conjunctMember, atom, atomMember, matched, inAtom⟩
        · exact efClean.1 inExec
        · exact (matchedClean conjunct conjunctMember atom atomMember matched).1 inAtom
      · intro inside
        rcases instance_leaf isLeaf extracted sinkMember σMember inside with
          inExec | ⟨conjunct, conjunctMember, atom, atomMember, matched, inAtom⟩
        · exact efClean.2 inExec
        · exact (matchedClean conjunct conjunctMember atom atomMember matched).2 inAtom
    refine ⟨?_, ?_, ?_⟩
    · apply keeps watcherExec waiting.present (Ne.symm isWatcher)
      intro sink sinkMember σ σMember same
      exact (instanceClean sink sinkMember σ σMember).1 (same ▸ watcher_has_out)
    · intro a aMember aOut
      rcases mem a aMember with ⟨old, _⟩ | ⟨sink, sinkMember, σ, σMember, rfl⟩
      · exact waiting.outOnly a old aOut
      · exact absurd aOut (instanceClean sink sinkMember σ σMember).1
    · intro a aMember aValue
      rcases mem a aMember with ⟨old, _⟩ | ⟨sink, sinkMember, σ, σMember, rfl⟩
      · exact waiting.valueOnly a old aValue
      · exact absurd aValue (instanceClean sink sinkMember σ σMember).2

/-- **Along a run from a waiting space, the true report never comes first**:
if `(out VALUE)` ever appears, some other report has appeared.  This holds for
every step semantics that fires the least executable. -/
theorem waiting_run {step : Space → Option Space} (fires : FiresLeast step) {value : Atom}
    (isLeaf : IsLeaf value) :
    ∀ (fuel : ℕ) (space : Space), Waiting value space → outOf value ∈ runWith step fuel space →
      ∃ fuel' other, other ≠ value ∧ outOf other ∈ runWith step fuel' space := by
  have notIn : ∀ space, Waiting value space → outOf value ∉ space := by
    intro space waiting member
    have := waiting.outOnly _ member (.child (by simp) .here)
    simp [outOf, watcherExec] at this
  intro fuel
  induction fuel with
  | zero => intro space waiting member; exact absurd member (notIn space waiting)
  | succ fuel ih =>
      intro space waiting member
      cases stepEq : step space with
      | none =>
          simp only [runWith, stepEq] at member
          exact absurd member (notIn space waiting)
      | some next =>
          simp only [runWith, stepEq] at member
          rcases waiting_step fires isLeaf waiting stepEq with stillWaiting | quiet | ⟨other, different, reported⟩
          · obtain ⟨fuel', other, different, reported⟩ := ih next stillWaiting member
            exact ⟨fuel' + 1, other, different, by simpa [runWith, stepEq] using reported⟩
          · exact absurd (.child (by simp) .here)
              (runWith_leafFree fires (Or.inl ⟨"out", rfl⟩) fuel next quiet _ member)
          · exact ⟨1, other, different, by simpa [runWith, stepEq] using reported⟩


/-! ### The window program -/

/-- `(exec () () (O (call f a $r (+ (g $r)))))`: call `f` on `a` at the least
location and record each result as `(g RESULT)`.  The kernel consumes an executable
with the input `()` without firing it (`unit_input_inert`). -/
def callerUnit : Atom :=
  .expression [.symbol "exec", .expression [], .expression [], .expression [.symbol "O", callAtom]]

def callerUnitFact : ExecFact := ⟨callerUnit, .expression [], mkExecRule 0 "unnamed" ⟨[]⟩ ⟨[]⟩⟩

theorem extract_callerUnit : extractExecFact callerUnit = some callerUnitFact := rfl

/-- The call sink as the extension reads it. -/
def callSinkFA : CallSink := ⟨.symbol "f", .symbol "a", "r", [.add (.expression [.symbol "g", .var "r"])]⟩

theorem callSinksOf_callerUnit : callSinksOf callerUnit = [callSinkFA] := rfl

theorem callSinksOf_watcher : callSinksOf watcherExec = [] := rfl

theorem callerUnit_first :
    lexLt (totalMorkCompactKey callerUnit) (totalMorkCompactKey watcherExec) = true := by decide

theorem extract_equation (value : Atom) : extractExecFact (equationOf value) = none := rfl

theorem extract_g (value : Atom) : extractExecFact (.expression [.symbol "g", value]) = none := rfl

theorem extract_out (value : Atom) : extractExecFact (outOf value) = none := rfl

/-- The program: the caller, the watcher and the equation `(= (f a) VALUE)`. -/
def windowProgram (value : Atom) : Space := {callerUnit} ∪ {watcherExec} ∪ {equationOf value}

theorem rows_single_conjunct {space : Space} {conjunct : Atom} {σ : Subst}
    (member : σ ∈ (matchPattern [] space ⟨[conjunct]⟩).map Prod.fst) :
    ∃ atom ∈ space, matchAtom [] conjunct atom = some σ := by
  simp only [matchPattern, matchPattern.go, List.map_flatMap, List.mem_flatMap] at member
  obtain ⟨⟨σ', atom⟩, found, inner⟩ := member
  simp at inner
  subst inner
  exact ⟨atom, (matchOneInSpace_spec [] conjunct space _ atom found).1,
    (matchOneInSpace_spec [] conjunct space _ atom found).2⟩

theorem callResults_window (value : Atom) :
    callResults (windowProgram value) (.symbol "f") (.symbol "a") = [value] := by
  unfold callResults
  apply filterMap_single (Finset.nodup_toList _) (x := equationOf value)
  · exact Finset.mem_toList.mpr (by simp [windowProgram])
  · simp [equationOf]
  · intro a aMember notEquation
    have : a = callerUnit ∨ a = watcherExec := by
      simpa [windowProgram, notEquation] using Finset.mem_toList.mp aMember
    rcases this with rfl | rfl <;> rfl

/-- The first firing: the call returns `(g VALUE)`. -/
noncomputable def windowFirst (value : Atom) : Space :=
  applyMorkSinkBatch ((windowProgram value).erase callerUnit) [[("r", value)]]
    ⟨[.add (.expression [.symbol "g", .var "r"])]⟩

theorem window_first_step (value : Atom) :
    callStep (windowProgram value) = some (windowFirst value) := by
  have selected : selectNextExec (execFactsOfSpace (windowProgram value)) = some callerUnitFact := by
    apply selectNextExec_eq_of_least extract_callerUnit (by simp [windowProgram])
    intro a aMember notCaller other extracted
    have : a = watcherExec ∨ a = equationOf value := by simpa [windowProgram, notCaller] using aMember
    rcases this with rfl | rfl
    · exact callerUnit_first
    · rw [extract_equation] at extracted; cases extracted
  unfold callStep
  rw [selected]
  simp only [Option.some.injEq]
  unfold fireCall
  rw [show callSinksOf callerUnitFact.atom = [callSinkFA] from rfl,
    readCopy_eq_of_mem _ _ (by simp [windowProgram, callerUnitFact])]
  simp only [List.foldl_cons, List.foldl_nil]
  have base : fireExecFact (windowProgram value) callerUnitFact = (windowProgram value).erase callerUnit := by
    show applyMorkSinkBatch (consumeExec (windowProgram value) callerUnitFact) _ ⟨[]⟩ = _
    rfl
  have rows : (matchPattern [] (windowProgram value) callerUnitFact.rule.pat).map Prod.fst = [[]] := rfl
  rw [base, rows]
  unfold windowFirst callRows
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, callSinkFA]
  rw [show applySubst [] (Atom.symbol "f") = .symbol "f" from rfl,
    show applySubst [] (Atom.symbol "a") = .symbol "a" from rfl, callResults_window]
  rfl

theorem windowFirst_mem (value : Atom) {a : Atom} (member : a ∈ windowFirst value) :
    a = watcherExec ∨ a = equationOf value ∨ a = .expression [.symbol "g", value] := by
  rcases applyMorkSinkBatch_mem _ _ member with old | ⟨sink, sinkMember, σ, σMember, rfl⟩
  · have := Finset.mem_erase.mp old
    have inProgram : a = callerUnit ∨ a = watcherExec ∨ a = equationOf value := by
      simpa [windowProgram, or_assoc] using this.2
    rcases inProgram with h | h | h
    · exact absurd h this.1
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · simp only [List.mem_singleton] at sinkMember σMember
    subst sinkMember σMember
    exact Or.inr (Or.inr rfl)

theorem watcher_mem_windowFirst (value : Atom) : watcherExec ∈ windowFirst value := by
  apply batch_keeps _ _ (by simp [windowProgram, Finset.mem_erase, watcherExec, callerUnit])
  intro sink sinkMember σ σMember same
  simp only [List.mem_singleton] at sinkMember σMember
  subst sinkMember σMember
  simp [watcherExec, Sink.atom, applySubst, applySubst.applySubstList] at same

theorem g_mem_windowFirst {value : Atom} (ground : isGroundAtom value = true) :
    .expression [.symbol "g", value] ∈ windowFirst value := by
  unfold windowFirst
  exact add_mem_of_row (body := .expression [.symbol "g", .var "r"]) (σ := [("r", value)])
    (List.mem_singleton_self _) (by simp [applySubst, applySubst.applySubstList, Subst.lookup,
      isGroundAtom, isGroundAtom.isGroundList, ground])

/-- The second firing: the watcher reports `(out VALUE)`. -/
noncomputable def windowSecond (value : Atom) : Space := fireExecFact (windowFirst value) watcherFact

theorem window_second_step (value : Atom) :
    callStep (windowFirst value) = some (windowSecond value) := by
  have step := callStep_of_single extract_watcherExec (watcher_mem_windowFirst value) (by
    intro a aMember notWatcher
    rcases windowFirst_mem value aMember with h | h | h
    · exact absurd h notWatcher
    · rw [h]; exact extract_equation value
    · rw [h]; exact extract_g value)
  rw [step, fireCall_eq_of_no_calls _ _ callSinksOf_watcher]
  rfl

theorem gPattern_match (value : Atom) :
    matchAtom [] gPattern (.expression [.symbol "g", value]) = some [("z", value)] := rfl

theorem out_mem_windowSecond {value : Atom} (ground : isGroundAtom value = true) :
    outOf value ∈ windowSecond value := by
  unfold windowSecond
  show outOf value ∈ applyMorkSinkBatch (consumeExec (windowFirst value) watcherFact)
    ((matchPattern [] (readCopy (windowFirst value) watcherFact) ⟨[gPattern]⟩).map Prod.fst)
    ⟨[.add (outOf (.var "z"))]⟩
  rw [readCopy_eq_of_mem _ _ (watcher_mem_windowFirst value)]
  exact add_mem_of_row (body := outOf (.var "z")) (σ := [("z", value)])
    (row_of_match (g_mem_windowFirst ground) (gPattern_match value))
    (by simp [outOf, applySubst, applySubst.applySubstList, Subst.lookup, isGroundAtom,
      isGroundAtom.isGroundList, ground])

theorem windowSecond_mem (value : Atom) {a : Atom} (member : a ∈ windowSecond value) :
    a = equationOf value ∨ a = .expression [.symbol "g", value] ∨ a = outOf value := by
  rcases fireExecFact_mem member with ⟨old, notWatcher⟩ | ⟨sink, sinkMember, σ, σMember, rfl⟩
  · rcases windowFirst_mem value old with h | h | h
    · exact absurd h notWatcher
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · have sinkEq : sink = .add (outOf (.var "z")) := by
      simpa [watcherFact, mkExecRule, mkTemplate] using sinkMember
    subst sinkEq
    obtain ⟨atom, atomMember, matched⟩ := rows_single_conjunct σMember
    rw [readCopy_eq_of_mem _ _ (watcher_mem_windowFirst value)] at atomMember
    rcases windowFirst_mem value atomMember with rfl | rfl | rfl
    · simp [gPattern, watcherExec, matchAtom, matchAtom.matchAtomList] at matched
    · simp [gPattern, equationOf, matchAtom, matchAtom.matchAtomList] at matched
    · rw [gPattern_match] at matched
      cases matched
      exact Or.inr (Or.inr rfl)

/-- The source shows exactly the true report. -/
theorem window_source {value : Atom} (ground : isGroundAtom value = true) :
    (∃ fuel, outOf value ∈ callRunN fuel (windowProgram value)) ∧
      ∀ fuel other, outOf other ∈ callRunN fuel (windowProgram value) → other = value := by
  have terminal : ∀ a ∈ windowSecond value, extractExecFact a = none := by
    intro a aMember
    rcases windowSecond_mem value aMember with rfl | rfl | rfl
    · exact extract_equation value
    · exact extract_g value
    · exact extract_out value
  have after : ∀ fuel, callRunN (fuel + 2) (windowProgram value) = windowSecond value := by
    intro fuel
    simp only [callRunN, window_first_step]
    exact callRunN_after_last (window_second_step value) terminal fuel
  refine ⟨⟨2, by rw [after 0]; exact out_mem_windowSecond ground⟩, ?_⟩
  intro fuel other member
  match fuel with
  | 0 =>
      have : outOf other = callerUnit ∨ outOf other = watcherExec ∨ outOf other = equationOf value := by
        simpa [callRunN, windowProgram, or_assoc] using member
      rcases this with h | h | h <;> simp [outOf, callerUnit, watcherExec, equationOf] at h
  | 1 =>
      simp only [callRunN, window_first_step] at member
      rcases windowFirst_mem value member with h | h | h <;> simp [outOf, watcherExec, equationOf] at h
  | fuel + 2 =>
      rw [after fuel] at member
      rcases windowSecond_mem value member with h | h | h
      · simp [outOf, equationOf] at h
      · simp [outOf] at h
      · simpa [outOf] using h


/-! ### The translated window program -/

/-- The translated caller. -/
def callerUnitTarget (E : CallElimination) : Atom :=
  .expression [.symbol "exec", .expression [], .expression [], .expression (.symbol "O" :: E.expand callAtom)]

theorem callFree_watcher : ¬ Occurs (.symbol "call") watcherExec := not_occurs_of_occursB (by decide)

theorem leaf_free_callerUnitTarget (E : CallElimination) {leaf : Atom} (isLeaf : IsLeaf leaf)
    (fixed : leaf ≠ .symbol "exec" ∧ leaf ≠ .symbol "O")
    (expansion : ∀ sink ∈ E.expand callAtom, ¬ Occurs leaf sink) :
    ¬ Occurs leaf (callerUnitTarget E) := by
  intro inside
  cases inside with
  | here => rcases isLeaf with ⟨_, h⟩ | ⟨_, h⟩ <;> cases h
  | child member inside =>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl
      · cases inside; exact fixed.1 rfl
      · cases inside with
        | here => rcases isLeaf with ⟨_, h⟩ | ⟨_, h⟩ <;> cases h
        | child member _ => simp at member
      · cases inside with
        | here => rcases isLeaf with ⟨_, h⟩ | ⟨_, h⟩ <;> cases h
        | child member _ => simp at member
      · cases inside with
        | here => rcases isLeaf with ⟨_, h⟩ | ⟨_, h⟩ <;> cases h
        | child member inside =>
            rcases List.mem_cons.mp member with rfl | member
            · cases inside; exact fixed.2 rfl
            · exact expansion _ member inside

theorem map_windowProgram (E : CallElimination) (value : Atom)
    (equationFree : ¬ Occurs (.symbol "call") (equationOf value)) :
    E.map (windowProgram value) = {callerUnitTarget E} ∪ {watcherExec} ∪ {equationOf value} := by
  unfold windowProgram
  rw [E.map_union, E.map_union, E.map_plain watcherExec callFree_watcher,
    E.map_plain (equationOf value) equationFree,
    show callerUnit = .expression [.symbol "exec", .expression [], .expression [],
      .expression [.symbol "O", callAtom]] from rfl,
    E.map_exec (.expression []) (.expression []) callAtom callAtom_has_call callFree_unit callFree_unit]
  rfl

/-- The value of the window program for a translation: a number that its
expansion of the call does not mention. -/
def windowValue (E : CallElimination) : Atom := .grounded (.int (freshInt (E.expand callAtom)))

theorem windowValue_ground (E : CallElimination) : isGroundAtom (windowValue E) = true := rfl

/-- The translated window program is waiting: `out` occurs only in the watcher,
the value only in the equation. -/
theorem waiting_map_window (E : CallElimination) :
    Waiting (windowValue E) (E.map (windowProgram (windowValue E))) := by
  have isLeaf : IsLeaf (windowValue E) := Or.inr ⟨_, rfl⟩
  have equationFree : ¬ Occurs (.symbol "call") (equationOf (windowValue E)) :=
    not_occurs_of_occursB (by simp [occursB, occursB.childrenB, equationOf, windowValue])
  rw [map_windowProgram E (windowValue E) equationFree]
  refine ⟨by simp, ?_, ?_⟩
  · intro a member inside
    simp only [Finset.mem_union, Finset.mem_singleton] at member
    rcases member with (rfl | rfl) | rfl
    · exact absurd inside (leaf_free_callerUnitTarget E isLeaf_out ⟨by simp, by simp⟩
        fun sink member inSink => outFree_callAtom (E.expand_quiet callAtom callAtom_has_call sink member inSink))
    · rfl
    · exact absurd inside (not_occurs_of_occursB (by simp [occursB, occursB.childrenB, equationOf, windowValue]))
  · intro a member inside
    simp only [Finset.mem_union, Finset.mem_singleton] at member
    rcases member with (rfl | rfl) | rfl
    · exact absurd inside (leaf_free_callerUnitTarget E isLeaf ⟨by simp [windowValue], by simp [windowValue]⟩
        (freshInt_fresh (E.expand callAtom)))
    · exact absurd inside (not_occurs_of_occursB (by simp [occursB, occursB.childrenB, watcherExec,
        gPattern, outOf, windowValue]))
    · rfl

/-- **The window argument**: if the source reports exactly `(out N)` on the
window program, a target semantics that fires the least executable disagrees
with it on some report. -/
theorem window_disagrees {step : Space → Option Space} (fires : FiresLeast step)
    (sourceRun : ℕ → Space → Space) (E : CallElimination)
    (source : (∃ fuel, outOf (windowValue E) ∈ sourceRun fuel (windowProgram (windowValue E))) ∧
      ∀ fuel other, outOf other ∈ sourceRun fuel (windowProgram (windowValue E)) → other = windowValue E) :
    ∃ (program : Space) (value : Atom),
      ¬ ((∃ fuel, outOf value ∈ sourceRun fuel program) ↔
        ∃ fuel, outOf value ∈ runWith step fuel (E.map program)) := by
  have isLeaf : IsLeaf (windowValue E) := Or.inr ⟨_, rfl⟩
  obtain ⟨sourceReaches, sourceOnly⟩ := source
  by_cases targetReaches :
      ∃ fuel, outOf (windowValue E) ∈ runWith step fuel (E.map (windowProgram (windowValue E)))
  · obtain ⟨fuel, reached⟩ := targetReaches
    obtain ⟨fuel', other, different, reported⟩ :=
      waiting_run fires isLeaf fuel _ (waiting_map_window E) reached
    refine ⟨windowProgram (windowValue E), other, fun same => ?_⟩
    obtain ⟨sourceFuel, sourceReported⟩ := same.mpr ⟨fuel', reported⟩
    exact different (sourceOnly sourceFuel other sourceReported)
  · exact ⟨windowProgram (windowValue E), windowValue E, fun same => targetReaches (same.mp sourceReaches)⟩

/-- **A synchronous call is not eliminable from MM2**, even for programs that
never read code: for every local translation of the call sink there is a
program and a report `(out X)` that the program and its translation disagree
on.  The program is a caller and a watcher at the least location and an
equation `(= (f a) N)` with a fresh number `N`: the source reports exactly
`(out N)`; the translation either never reports `(out N)` or first reports
something else. -/
theorem call_not_eliminable (E : CallElimination) :
    ∃ (program : Space) (value : Atom),
      ¬ ((∃ fuel, outOf value ∈ callRunN fuel program) ↔
        ∃ fuel, outOf value ∈ (workQueueRunN fuel (E.map program)).1) := by
  simp only [workQueueRunN_eq_runWith]
  exact window_disagrees workQueueStep_firesLeast callRunN E (window_source (windowValue_ground E))

#print axioms call_not_eliminable


/-! ## Open templates

The MORK engine writes template instances that keep unbound variables, so an
executable can write an executable that looks something up later.  With open
templates the call is still not eliminable locally (`call_not_eliminable_open`):
the window argument does not depend on how templates are staged.  A global
translation, which moves user executables out of a reserved band and writes
each lookup into the band, does return in time (`band_reports`). -/

/-- Runs that stop stay. -/
theorem runWith_stop {step : Space → Option Space} {space : Space} (stop : step space = none) :
    ∀ fuel, runWith step fuel space = space
  | 0 => rfl
  | fuel + 1 => by simp [runWith, stop]

theorem stageOpen_fold_keeps {sink : Sink} :
    ∀ (rows : List Subst) (staged : List Atom) {x : Atom}, x ∈ staged →
      x ∈ rows.foldl (stageOpenSink sink) staged
  | [], _, _, h => h
  | σ :: rest, staged, x, h => by
      apply stageOpen_fold_keeps rest
      unfold stageOpenSink insertSupport
      split_ifs
      · exact h
      · exact List.mem_append_left _ h

theorem stageOpen_fold_mem {sink : Sink} :
    ∀ (rows : List Subst) (staged : List Atom) {σ : Subst}, σ ∈ rows →
      applySubst σ sink.atom ∈ rows.foldl (stageOpenSink sink) staged
  | [], _, _, member => by simp at member
  | σ' :: rest, staged, σ, member => by
      simp only [List.foldl_cons]
      rcases List.mem_cons.mp member with rfl | member
      · apply stageOpen_fold_keeps
        unfold stageOpenSink insertSupport
        split_ifs with present
        · exact present
        · simp
      · exact stageOpen_fold_mem rest _ member

/-- With open templates every instance of an insertion is written. -/
theorem openRun_add_mem {space : Space} {rows : List Subst} {body : Atom} {σ : Subst}
    (member : σ ∈ rows) :
    applySubst σ body ∈ (supportProvider stageOpenSink).run rows space [.add body] := by
  show applySubst σ body ∈ finalizeSupportSink (.add body) (rows.foldl (stageOpenSink (.add body)) []) space
  unfold finalizeSupportSink
  exact Finset.mem_union_right _ (List.mem_toFinset.mpr (stageOpen_fold_mem (sink := .add body) rows [] member))

/-! ### The source with open templates -/

/-- MM2 with synchronous calls and open templates. -/
noncomputable def fireCallOpen (space : Space) (ef : ExecFact) : Space :=
  (callSinksOf ef.atom).foldl
    (fun current call =>
      (supportProvider stageOpenSink).run
        (callRows (readCopy space ef) ((matchPattern [] (readCopy space ef) ef.rule.pat).map Prod.fst) call)
        current call.sinks)
    (fireOpen space ef)

/-- One step of MM2 with synchronous calls and open templates. -/
noncomputable def callOpenStep (space : Space) : Option Space :=
  match selectNextExec (execFactsOfSpace space) with
  | none => none
  | some ef => some (fireCallOpen space ef)

theorem window_first_step_open {value : Atom} (ground : isGroundAtom value = true) :
    callOpenStep (windowProgram value) = some (windowFirst value) := by
  have selected : selectNextExec (execFactsOfSpace (windowProgram value)) = some callerUnitFact := by
    apply selectNextExec_eq_of_least extract_callerUnit (by simp [windowProgram])
    intro a aMember notCaller other extracted
    have : a = watcherExec ∨ a = equationOf value := by simpa [windowProgram, notCaller] using aMember
    rcases this with rfl | rfl
    · exact callerUnit_first
    · rw [extract_equation] at extracted; cases extracted
  unfold callOpenStep
  rw [selected]
  simp only [Option.some.injEq]
  unfold fireCallOpen
  rw [show callSinksOf callerUnitFact.atom = [callSinkFA] from rfl,
    readCopy_eq_of_mem _ _ (by simp [windowProgram, callerUnitFact])]
  simp only [List.foldl_cons, List.foldl_nil]
  have base : fireOpen (windowProgram value) callerUnitFact = (windowProgram value).erase callerUnit := rfl
  have rows : (matchPattern [] (windowProgram value) callerUnitFact.rule.pat).map Prod.fst = [[]] := rfl
  rw [base, rows]
  unfold windowFirst callRows
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, callSinkFA]
  rw [show applySubst [] (Atom.symbol "f") = .symbol "f" from rfl,
    show applySubst [] (Atom.symbol "a") = .symbol "a" from rfl, callResults_window]
  apply openRun_eq_of_ground
  intro sink sinkMember σ σMember
  simp only [List.mem_singleton, List.map_cons, List.map_nil] at sinkMember σMember
  subst sinkMember σMember
  simp [Sink.atom, applySubst, applySubst.applySubstList, Subst.lookup, isGroundAtom,
    isGroundAtom.isGroundList, ground]

theorem window_second_step_open {value : Atom} (ground : isGroundAtom value = true) :
    callOpenStep (windowFirst value) = some (windowSecond value) := by
  have selected : selectNextExec (execFactsOfSpace (windowFirst value)) = some watcherFact := by
    apply selectNextExec_eq_of_least extract_watcherExec (watcher_mem_windowFirst value)
    intro a aMember notWatcher other extracted
    rcases windowFirst_mem value aMember with h | h | h
    · exact absurd h notWatcher
    · rw [h, extract_equation] at extracted; cases extracted
    · rw [h, extract_g] at extracted; cases extracted
  unfold callOpenStep
  rw [selected]
  simp only [Option.some.injEq]
  unfold fireCallOpen
  rw [show callSinksOf watcherFact.atom = [] from rfl]
  simp only [List.foldl_nil]
  show (supportProvider stageOpenSink).run
      ((matchPattern [] (readCopy (windowFirst value) watcherFact) watcherFact.rule.pat).map Prod.fst)
      (consumeExec (windowFirst value) watcherFact) watcherFact.rule.tmpl.sinks =
    morkSupportSinkProvider.run
      ((matchPattern [] (readCopy (windowFirst value) watcherFact) watcherFact.rule.pat).map Prod.fst)
      (consumeExec (windowFirst value) watcherFact) watcherFact.rule.tmpl.sinks
  apply openRun_eq_of_ground
  intro sink sinkMember σ σMember
  have sinkEq : sink = .add (outOf (.var "z")) := by
    simpa [watcherFact, mkExecRule, mkTemplate] using sinkMember
  subst sinkEq
  obtain ⟨atom, atomMember, matched⟩ := rows_single_conjunct σMember
  rw [readCopy_eq_of_mem _ _ (watcher_mem_windowFirst value)] at atomMember
  rcases windowFirst_mem value atomMember with rfl | rfl | rfl
  · simp [gPattern, watcherExec, matchAtom, matchAtom.matchAtomList] at matched
  · simp [gPattern, equationOf, matchAtom, matchAtom.matchAtomList] at matched
  · rw [gPattern_match] at matched
    cases matched
    simp [outOf, Sink.atom, applySubst, applySubst.applySubstList, Subst.lookup, isGroundAtom,
      isGroundAtom.isGroundList, ground]

theorem window_last_open (value : Atom) : callOpenStep (windowSecond value) = none := by
  have terminal : ∀ a ∈ windowSecond value, extractExecFact a = none := by
    intro a aMember
    rcases windowSecond_mem value aMember with rfl | rfl | rfl
    · exact extract_equation value
    · exact extract_g value
    · exact extract_out value
  unfold callOpenStep
  rw [execFactsOfSpace_nil terminal]
  rfl

/-- The source with open templates shows exactly the true report, as with
ground templates. -/
theorem window_source_open {value : Atom} (ground : isGroundAtom value = true) :
    (∃ fuel, outOf value ∈ runWith callOpenStep fuel (windowProgram value)) ∧
      ∀ fuel other, outOf other ∈ runWith callOpenStep fuel (windowProgram value) → other = value := by
  have after : ∀ fuel, runWith callOpenStep (fuel + 2) (windowProgram value) = windowSecond value := by
    intro fuel
    simp only [runWith, window_first_step_open ground, window_second_step_open ground]
    exact runWith_stop (window_last_open value) fuel
  refine ⟨⟨2, by rw [after 0]; exact out_mem_windowSecond ground⟩, ?_⟩
  intro fuel other member
  match fuel with
  | 0 =>
      have : outOf other = callerUnit ∨ outOf other = watcherExec ∨ outOf other = equationOf value := by
        simpa [runWith, windowProgram, or_assoc] using member
      rcases this with h | h | h <;> simp [outOf, callerUnit, watcherExec, equationOf] at h
  | 1 =>
      simp only [runWith, window_first_step_open ground] at member
      rcases windowFirst_mem value member with h | h | h <;> simp [outOf, watcherExec, equationOf] at h
  | fuel + 2 =>
      rw [after fuel] at member
      rcases windowSecond_mem value member with h | h | h
      · simp [outOf, equationOf] at h
      · simp [outOf] at h
      · simpa [outOf] using h

/-- **With open templates a synchronous call is still not eliminable**: for
every local translation the window program and its translation disagree on a
report, now with templates that may write executables with unbound
variables. -/
theorem call_not_eliminable_open (E : CallElimination) :
    ∃ (program : Space) (value : Atom),
      ¬ ((∃ fuel, outOf value ∈ runWith callOpenStep fuel program) ↔
        ∃ fuel, outOf value ∈ runWith openStep fuel (E.map program)) :=
  window_disagrees openStep_firesLeast (runWith callOpenStep) E (window_source_open (windowValue_ground E))

#print axioms call_not_eliminable_open

/-! ### A reserved band returns in time -/

/-- `(exec () (, (= (f a) $r)) (O (+ (g $r))))`: the lookup a call becomes. -/
def bandLookup : Atom :=
  .expression [.symbol "exec", .expression [],
    .expression [.symbol ",", .expression [.symbol "=", .expression [.symbol "f", .symbol "a"], .var "r"]],
    .expression [.symbol "O", .expression [.symbol "+", .expression [.symbol "g", .var "r"]]]]

/-- `(exec () () (O (+ LOOKUP)))`: the caller writes the lookup, an open template. -/
def bandCaller : Atom :=
  .expression [.symbol "exec", .expression [], .expression [],
    .expression [.symbol "O", .expression [.symbol "+", bandLookup]]]

/-- The watcher moved out of the band, to the location `(u ())`. -/
def bandWatcher : Atom :=
  .expression [.symbol "exec", .expression [.symbol "u", .expression []],
    .expression [.symbol ",", gPattern],
    .expression [.symbol "O", .expression [.symbol "+", outOf (.var "z")]]]

/-- The window program translated globally: the user's executables leave the
band of the least location, and the call becomes a lookup written into the
band. -/
def bandProgram (value : Atom) : Space := {bandCaller} ∪ {bandWatcher} ∪ {equationOf value}

def bandCallerFact : ExecFact := ⟨bandCaller, .expression [], mkExecRule 0 "unnamed" ⟨[]⟩ ⟨[.add bandLookup]⟩⟩

def bandLookupFact : ExecFact :=
  ⟨bandLookup, .expression [], mkExecRule 0 "unnamed"
    ⟨[.expression [.symbol "=", .expression [.symbol "f", .symbol "a"], .var "r"]]⟩
    ⟨[.add (.expression [.symbol "g", .var "r"])]⟩⟩

def bandWatcherFact : ExecFact :=
  ⟨bandWatcher, .expression [.symbol "u", .expression []], mkExecRule 0 "unnamed" ⟨[gPattern]⟩
    ⟨[.add (outOf (.var "z"))]⟩⟩

theorem extract_bandCaller : extractExecFact bandCaller = some bandCallerFact := rfl
theorem extract_bandLookup : extractExecFact bandLookup = some bandLookupFact := rfl
theorem extract_bandWatcher : extractExecFact bandWatcher = some bandWatcherFact := rfl

theorem bandCaller_first :
    lexLt (totalMorkCompactKey bandCaller) (totalMorkCompactKey bandWatcher) = true := by decide

theorem bandLookup_first :
    lexLt (totalMorkCompactKey bandLookup) (totalMorkCompactKey bandWatcher) = true := by decide

/-- The first firing writes the lookup. -/
noncomputable def bandFirst (value : Atom) : Space := fireOpen (bandProgram value) bandCallerFact

theorem bandFirst_mem (value : Atom) {a : Atom} (member : a ∈ bandFirst value) :
    a = bandWatcher ∨ a = equationOf value ∨ a = bandLookup := by
  unfold bandFirst fireOpen at member
  rcases supportProvider_mem stageOpenSink_instances _ _ member with old | ⟨sink, sinkMember, σ, σMember, rfl⟩
  · have := Finset.mem_erase.mp old
    have inProgram : a = bandCaller ∨ a = bandWatcher ∨ a = equationOf value := by
      simpa [bandProgram, or_assoc] using this.2
    rcases inProgram with h | h | h
    · exact absurd h this.1
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · have sinkEq : sink = .add bandLookup := by
      simpa [bandCallerFact, mkExecRule, mkTemplate] using sinkMember
    subst sinkEq
    have rows : (matchPattern [] (readCopy (bandProgram value) bandCallerFact)
        bandCallerFact.rule.pat).map Prod.fst = [[]] := rfl
    rw [rows, List.mem_singleton] at σMember
    subst σMember
    exact Or.inr (Or.inr rfl)

theorem bandLookup_mem_bandFirst (value : Atom) : bandLookup ∈ bandFirst value := by
  unfold bandFirst fireOpen
  have rows : (matchPattern [] (readCopy (bandProgram value) bandCallerFact)
      bandCallerFact.rule.pat).map Prod.fst = [[]] := rfl
  rw [rows]
  exact openRun_add_mem (body := bandLookup) (σ := []) (List.mem_singleton_self _)

theorem kept_bandFirst (value : Atom) {a : Atom} (member : a ∈ bandProgram value) (notCaller : a ≠ bandCaller)
    (notLookup : a ≠ bandLookup) : a ∈ bandFirst value := by
  unfold bandFirst fireOpen
  apply supportProvider_keeps stageOpenSink_instances _ _ (Finset.mem_erase.mpr ⟨notCaller, member⟩)
  intro sink sinkMember σ σMember same
  have sinkEq : sink = .add bandLookup := by
    simpa [bandCallerFact, mkExecRule, mkTemplate] using sinkMember
  subst sinkEq
  have rows : (matchPattern [] (readCopy (bandProgram value) bandCallerFact)
      bandCallerFact.rule.pat).map Prod.fst = [[]] := rfl
  rw [rows, List.mem_singleton] at σMember
  subst σMember
  exact notLookup same

theorem band_first_step (value : Atom) : openStep (bandProgram value) = some (bandFirst value) := by
  have selected : selectNextExec (execFactsOfSpace (bandProgram value)) = some bandCallerFact := by
    apply selectNextExec_eq_of_least extract_bandCaller (by simp [bandProgram])
    intro a aMember notCaller other extracted
    have : a = bandWatcher ∨ a = equationOf value := by simpa [bandProgram, notCaller] using aMember
    rcases this with rfl | rfl
    · exact bandCaller_first
    · rw [extract_equation] at extracted; cases extracted
  unfold openStep
  rw [selected]
  rfl

/-- The second firing: the lookup returns `(g VALUE)` before any user
executable runs. -/
noncomputable def bandSecond (value : Atom) : Space := fireOpen (bandFirst value) bandLookupFact

theorem equationPattern_match (value : Atom) :
    matchAtom [] (.expression [.symbol "=", .expression [.symbol "f", .symbol "a"], .var "r"])
      (equationOf value) = some [("r", value)] := rfl

theorem bandSecond_mem (value : Atom) {a : Atom} (member : a ∈ bandSecond value) :
    a = bandWatcher ∨ a = equationOf value ∨ a = .expression [.symbol "g", value] := by
  unfold bandSecond fireOpen at member
  rcases supportProvider_mem stageOpenSink_instances _ _ member with old | ⟨sink, sinkMember, σ, σMember, rfl⟩
  · have := Finset.mem_erase.mp old
    rcases bandFirst_mem value this.2 with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact absurd h this.1
  · have sinkEq : sink = .add (.expression [.symbol "g", .var "r"]) := by
      simpa [bandLookupFact, mkExecRule, mkTemplate] using sinkMember
    subst sinkEq
    obtain ⟨atom, atomMember, matched⟩ := rows_single_conjunct σMember
    rw [readCopy_eq_of_mem _ _ (bandLookup_mem_bandFirst value)] at atomMember
    rcases bandFirst_mem value atomMember with rfl | rfl | rfl
    · simp [bandWatcher, matchAtom, matchAtom.matchAtomList] at matched
    · rw [equationPattern_match] at matched
      cases matched
      exact Or.inr (Or.inr rfl)
    · simp [bandLookup, matchAtom, matchAtom.matchAtomList] at matched

theorem g_mem_bandSecond (value : Atom) : .expression [.symbol "g", value] ∈ bandSecond value := by
  unfold bandSecond fireOpen
  rw [readCopy_eq_of_mem _ _ (bandLookup_mem_bandFirst value)]
  exact openRun_add_mem (body := .expression [.symbol "g", .var "r"]) (σ := [("r", value)])
    (row_of_match (kept_bandFirst value (by simp [bandProgram]) (by simp [equationOf, bandCaller])
      (by simp [equationOf, bandLookup])) (equationPattern_match value))

theorem bandWatcher_mem_bandSecond (value : Atom) : bandWatcher ∈ bandSecond value := by
  unfold bandSecond fireOpen
  apply supportProvider_keeps stageOpenSink_instances _ _
    (Finset.mem_erase.mpr ⟨by decide,
      kept_bandFirst value (by simp [bandProgram]) (by simp [bandWatcher, bandCaller])
        (by simp [bandWatcher, bandLookup])⟩)
  intro sink sinkMember σ σMember same
  have sinkEq : sink = .add (.expression [.symbol "g", .var "r"]) := by
    simpa [bandLookupFact, mkExecRule, mkTemplate] using sinkMember
  subst sinkEq
  simp [bandWatcher, Sink.atom, applySubst, applySubst.applySubstList] at same

theorem band_second_step (value : Atom) : openStep (bandFirst value) = some (bandSecond value) := by
  have selected : selectNextExec (execFactsOfSpace (bandFirst value)) = some bandLookupFact := by
    apply selectNextExec_eq_of_least extract_bandLookup (bandLookup_mem_bandFirst value)
    intro a aMember notLookup other extracted
    rcases bandFirst_mem value aMember with rfl | rfl | rfl
    · exact bandLookup_first
    · rw [extract_equation] at extracted; cases extracted
    · exact absurd rfl notLookup
  unfold openStep
  rw [selected]
  rfl

/-- The third firing: the relocated watcher reports `(out VALUE)`. -/
noncomputable def bandThird (value : Atom) : Space := fireOpen (bandSecond value) bandWatcherFact

theorem bandThird_mem (value : Atom) {a : Atom} (member : a ∈ bandThird value) :
    a = equationOf value ∨ a = .expression [.symbol "g", value] ∨ a = outOf value := by
  unfold bandThird fireOpen at member
  rcases supportProvider_mem stageOpenSink_instances _ _ member with old | ⟨sink, sinkMember, σ, σMember, rfl⟩
  · have := Finset.mem_erase.mp old
    rcases bandSecond_mem value this.2 with h | h | h
    · exact absurd h this.1
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · have sinkEq : sink = .add (outOf (.var "z")) := by
      simpa [bandWatcherFact, mkExecRule, mkTemplate] using sinkMember
    subst sinkEq
    obtain ⟨atom, atomMember, matched⟩ := rows_single_conjunct σMember
    rw [readCopy_eq_of_mem _ _ (bandWatcher_mem_bandSecond value)] at atomMember
    rcases bandSecond_mem value atomMember with rfl | rfl | rfl
    · simp [gPattern, bandWatcher, matchAtom, matchAtom.matchAtomList] at matched
    · simp [gPattern, equationOf, matchAtom, matchAtom.matchAtomList] at matched
    · rw [gPattern_match] at matched
      cases matched
      exact Or.inr (Or.inr rfl)

theorem out_mem_bandThird (value : Atom) : outOf value ∈ bandThird value := by
  unfold bandThird fireOpen
  rw [readCopy_eq_of_mem _ _ (bandWatcher_mem_bandSecond value)]
  exact openRun_add_mem (body := outOf (.var "z")) (σ := [("z", value)])
    (row_of_match (g_mem_bandSecond value) (gPattern_match value))

theorem band_third_step (value : Atom) : openStep (bandSecond value) = some (bandThird value) := by
  have selected : selectNextExec (execFactsOfSpace (bandSecond value)) = some bandWatcherFact := by
    apply selectNextExec_eq_of_least extract_bandWatcher (bandWatcher_mem_bandSecond value)
    intro a aMember notWatcher other extracted
    rcases bandSecond_mem value aMember with h | h | h
    · exact absurd h notWatcher
    · rw [h, extract_equation] at extracted; cases extracted
    · rw [h, extract_g] at extracted; cases extracted
  unfold openStep
  rw [selected]
  rfl

theorem band_last_step (value : Atom) : openStep (bandThird value) = none := by
  have terminal : ∀ a ∈ bandThird value, extractExecFact a = none := by
    intro a aMember
    rcases bandThird_mem value aMember with rfl | rfl | rfl
    · exact extract_equation value
    · exact extract_g value
    · exact extract_out value
  unfold openStep
  rw [execFactsOfSpace_nil terminal]
  rfl

/-- **A reserved band returns in time**: with open templates, the globally
translated window program reports exactly `(out VALUE)`, as the source does.
So what the window theorem rules out is locality: a translation that keeps the
user's executables where they are. -/
theorem band_reports (value : Atom) :
    (∃ fuel, outOf value ∈ runWith openStep fuel (bandProgram value)) ∧
      ∀ fuel other, outOf other ∈ runWith openStep fuel (bandProgram value) → other = value := by
  have after : ∀ fuel, runWith openStep (fuel + 3) (bandProgram value) = bandThird value := by
    intro fuel
    simp only [runWith, band_first_step, band_second_step, band_third_step]
    exact runWith_stop (band_last_step value) fuel
  refine ⟨⟨3, by rw [after 0]; exact out_mem_bandThird value⟩, ?_⟩
  intro fuel other member
  match fuel with
  | 0 =>
      have : outOf other = bandCaller ∨ outOf other = bandWatcher ∨ outOf other = equationOf value := by
        simpa [runWith, bandProgram, or_assoc] using member
      rcases this with h | h | h <;> simp [outOf, bandCaller, bandWatcher, equationOf] at h
  | 1 =>
      simp only [runWith, band_first_step] at member
      rcases bandFirst_mem value member with h | h | h <;> simp [outOf, bandWatcher, equationOf, bandLookup] at h
  | 2 =>
      simp only [runWith, band_first_step, band_second_step] at member
      rcases bandSecond_mem value member with h | h | h <;> simp [outOf, bandWatcher, equationOf] at h
  | fuel + 3 =>
      rw [after fuel] at member
      rcases bandThird_mem value member with h | h | h
      · simp [outOf, equationOf] at h
      · simp [outOf] at h
      · simpa [outOf] using h

#print axioms band_reports


/-! ## Mainline MM2: the absence and multiplicity results against the kernel

The results above concern the support model: add, remove, head and tail sinks, the
comma input, and a parser that drops every other sink.  The kernel at the pinned
revision always contains `pure` (it does not compile without the grounding feature),
dispatches eighteen sink forms and five factor forms, writes adds eagerly, and consumes
an executable whose input is the empty expression `()` without firing it.  This section
re-checks the absence and multiplicity results in that model (`Mainline`); the call
results are re-checked in `MM2FunctionCalls`, which adds the call semantics they need.

* `unit_input_inert`: the callers of the call theorems above, whose input is `()`,
  never fire in the kernel.  Their translations never fire either.
* `no_mainline_input_decides_absence`: absence is not eliminable by replacing the input,
  even with every factor form, including `==`, `!=`, files and solver models.
* `count_gadget_reproduces_witness` and `downward_staging_reproduces_witness`: a
  translation that may also rewrite the output reproduces the absence witness pair,
  with a count guard over a reflective self-match or with decision stages generated
  below its own scheduling key.  The count gadget is wrong on other contexts; the
  staged gadget is not. -/

open Mainline in
/-- A directive whose input is `()` is consumed without effect. -/
theorem unit_input_inert (profile : BuildProfile) (raw : RawExecFact)
    (unit : raw.inputExpr = .expression []) : decodeDirective profile raw = .ok none := by
  unfold decodeDirective
  rw [unit]
  rfl

open Mainline in
/-- The callers of the window and reflection theorems do not fire in the kernel. -/
theorem callers_inert :
    (mainlineStep defaultProfile inertPrimitives ExternalState.empty [callerUnit]).space? =
        some [] ∧
      (mainlineStep defaultProfile inertPrimitives ExternalState.empty [callerExec]).space? =
        some [] := by
  decide +kernel

/-! ### No input decides absence -/

/-- `(exec (z) INPUT (O (+ (out))))`: the absence executable with its input replaced. -/
def absenceTargetWith (input : Atom) : Atom :=
  .expression [.symbol "exec", locZ, input, outputOut]

theorem compactKey_head {children : List Atom} {key : List ℕ}
    (h : morkCompactKey? (.expression children) = some key) :
    key.head? = some children.length := by
  simp only [morkCompactKey?, Option.map_eq_some_iff] at h
  obtain ⟨⟨bytes, environment⟩, encoded, rfl⟩ := h
  obtain ⟨tail, _, equal⟩ := encode_expression encoded
  simp only at equal
  rw [equal]
  rfl

theorem supportKey_p_ne_target (input : Atom) :
    morkSupportKey pAtom ≠ morkSupportKey (absenceTargetWith input) := by
  intro same
  have pKey : morkCompactKey? pAtom = some [1, 193, 112] := by decide
  unfold morkSupportKey at same
  rw [pKey] at same
  cases targetKey : morkCompactKey? (absenceTargetWith input) with
  | none => rw [targetKey] at same; cases same
  | some key =>
      rw [targetKey] at same
      have equal : key = [1, 193, 112] := by
        injection same with equal
        exact equal.symm
      have head := compactKey_head targetKey
      rw [equal] at head
      simp at head

theorem erase_single (atom : Atom) : morkEraseSupport [atom] atom = [] := by
  simp [morkEraseSupport, sameMorkSupportAtom]

theorem out_instance (input : InputSpec) (row : Subst) :
    instantiateRuleTemplateAtom? input row outAtom = some outAtom := by
  simp [instantiateRuleTemplateAtom?, outAtom, ruleTemplateCovered, ruleTemplatesCovered,
    applySubst, applySubst.applySubstList]

open Mainline in
theorem staged_out (input : InputSpec) (rows : List Subst) :
    staged input rows outAtom = if rows = [] then [] else [outAtom] := by
  unfold staged instances
  simp only [out_instance]
  cases rows with
  | nil => rfl
  | cons first rest =>
      simp only [List.filterMap_cons, List.foldl_cons, reduceCtorEq, if_false]
      show List.foldl morkInsertSupport [outAtom] (rest.filterMap fun _ => some outAtom) = [outAtom]
      apply foldl_insert_of_all_contained
      intro atom member
      simp only [List.mem_filterMap, Option.some.injEq] at member
      obtain ⟨_, _, rfl⟩ := member
      exact contains_of_mem [outAtom] outAtom (by simp)

open Mainline in
theorem union_staged_out_mem (live : List Atom) (input : InputSpec) (rows : List Subst)
    (absent : morkSupportContains live outAtom = false) :
    outAtom ∈ morkUnionSupport live (staged input rows outAtom) ↔ rows ≠ [] := by
  rw [staged_out]
  by_cases empty : rows = []
  · simp only [empty, if_true, ne_eq, not_true_eq_false, iff_false]
    intro member
    have := contains_of_mem live outAtom member
    rw [this] at absent
    cases absent
  · simp only [empty, if_false, ne_eq, not_false_eq_true, iff_true]
    simp [morkUnionSupport, morkInsertSupport, absent]

/-- The scheduler shell of the replaced absence executable. -/
def absenceRaw (input : Atom) : RawExecFact := ⟨absenceTargetWith input, locZ, input, outputOut⟩

open Mainline in
/-- Firing a directive whose output is `(O (+ (out)))`. -/
theorem fire_add_out (prims : Primitives) (external : ExternalState) (space : List Atom)
    (atom : Atom) (input : MainlineInput) :
    fireDirective prims external space ⟨atom, input, .sinks [.core (.add outAtom)]⟩ =
      (mainlineRows prims external (factorTag atom) (morkInsertSupport (morkEraseSupport space atom) atom)
          input).map
        fun solved =>
          (morkUnionSupport (morkEraseSupport space atom)
            (staged input.coverage (solved.map (inputRow (inputSpecVariables input.coverage))) outAtom),
            external) := by
  simp only [fireDirective]
  cases mainlineRows prims external (factorTag atom) (morkInsertSupport (morkEraseSupport space atom) atom)
      input with
  | error fault => rfl
  | ok rows =>
      simp [applyMainlineSinks, eagerOutputs, finalizeMainlineSink, bind, Except.bind, pure,
        Except.pure, Except.map]

open Mainline in
/-- **No input decides absence, whatever factors it uses.**  Whatever input replaces
`(, (not (p)))` in `(exec (z) (, (not (p))) (O (+ (out))))`, the kernel cannot report
`(out)` for the executable alone and stay silent beside `(p)`, as the absence executable
does: every factor is monotone in the read copy, and whether it aborts does not depend
on the read copy. -/
theorem no_mainline_input_decides_absence (profile : BuildProfile) (prims : Primitives)
    (external : ExternalState) (input : Atom) :
    ¬ (outAtom ∈ ((mainlineStep profile prims external [absenceTargetWith input]).space?).getD [] ∧
       outAtom ∉
        ((mainlineStep profile prims external [absenceTargetWith input, pAtom]).space?).getD []) := by
  rintro ⟨alone, beside⟩
  have selectAlone : selectNextScheduled (WQComputable.cRawExecFacts [absenceTargetWith input]) =
      some (absenceRaw input) := rfl
  have selectBeside :
      selectNextScheduled (WQComputable.cRawExecFacts [absenceTargetWith input, pAtom]) =
        some (absenceRaw input) := rfl
  have keyDifferent := supportKey_p_ne_target input
  have liveBeside : morkEraseSupport [absenceTargetWith input, pAtom] (absenceTargetWith input) =
      [pAtom] := by
    simp only [morkEraseSupport, List.filter_cons, List.filter_nil, sameMorkSupportAtom]
    simp only [decide_true, Bool.not_true, Bool.false_eq_true, if_false]
    simp only [show decide (morkSupportKey pAtom = morkSupportKey (absenceTargetWith input)) = false
      from decide_eq_false keyDifferent, Bool.not_false, if_true]
  have readBeside : morkInsertSupport [pAtom] (absenceTargetWith input) =
      [pAtom, absenceTargetWith input] := by
    simp [morkInsertSupport, morkSupportContains, morkSupportFind?, sameMorkSupportAtom,
      keyDifferent]
  have outputDecoded : decodeOutput profile (kernelOutput locZ input outputOut) =
      some (.ok (.sinks [.core (.add outAtom)])) := by
    have unchanged : kernelOutput locZ input outputOut = outputOut := by
      unfold kernelOutput
      split
      · rename_i sinks shape
        simp only [outputOut, Atom.expression.injEq, List.cons.injEq, true_and] at shape
        subst shape
        rfl
      · rfl
    rw [unchanged]
    simp [decodeOutput, outputOut, decodeAll, decodeSink, recognizeSink, requireFeature,
      MainlineSink.feature?, bind, Except.bind, pure, Except.pure, Except.map]
  unfold mainlineStep at alone beside
  rw [selectAlone] at alone
  rw [selectBeside] at beside
  cases decoded : decodeDirective profile (absenceRaw input) with
  | error fault => simp [decoded, StepOutcome.space?] at alone
  | ok result =>
      cases result with
      | none =>
          simp only [decoded, StepOutcome.space?, Option.getD_some] at alone
          simp [absenceRaw, erase_single] at alone
      | some directive =>
          obtain ⟨atomEq, outputEq⟩ :=
            decodeDirective_some (raw := absenceRaw input) outputDecoded decoded
          obtain ⟨atom, minput, output⟩ := directive
          simp only [absenceRaw] at atomEq outputEq
          subst atomEq outputEq
          simp only [decoded, fire_add_out, erase_single, liveBeside, readBeside] at alone beside
          have readAlone : morkInsertSupport [] (absenceTargetWith input) =
              [absenceTargetWith input] := rfl
          rw [readAlone] at alone
          cases rowsAlone : mainlineRows prims external (factorTag (absenceTargetWith input))
              [absenceTargetWith input] minput with
          | error fault => simp [rowsAlone, Except.map, StepOutcome.space?] at alone
          | ok rowsA =>
              obtain ⟨rowsB, rowsBeside⟩ :=
                (mainlineRows_aborts_independently prims external (factorTag (absenceTargetWith input))
                  [absenceTargetWith input] [pAtom, absenceTargetWith input] minput).1
                  ⟨rowsA, rowsAlone⟩
              have mono := mainlineRows_mono prims external (factorTag (absenceTargetWith input))
                (small := [absenceTargetWith input]) (large := [pAtom, absenceTargetWith input])
                (by intro atom member; simp at member; simp [member]) minput rowsAlone rowsBeside
              simp only [rowsAlone, rowsBeside, Except.map, StepOutcome.space?,
                Option.getD_some] at alone beside
              have nonempty : rowsA.map (inputRow (inputSpecVariables minput.coverage)) ≠ [] :=
                (union_staged_out_mem [] _ _ rfl).1 alone
              have nonemptyB : rowsB.map (inputRow (inputSpecVariables minput.coverage)) ≠ [] := by
                rw [ne_eq, List.map_eq_nil_iff] at nonempty ⊢
                obtain ⟨row, rowMember⟩ := List.exists_mem_of_ne_nil rowsA nonempty
                exact List.ne_nil_of_mem (mono row rowMember)
              exact beside ((union_staged_out_mem [pAtom] _ _ (by decide)).2 nonemptyB)

/-! ### Translations that also rewrite the output

The class `AbsenceElimination` keeps the executable's output.  A local translation that
may also rewrite it is not caught by the witness pair `{absenceExec}` and
`{absenceExec, (p)}` in the kernel. -/

/-- `(q)`: an atom unrelated to `(p)`. -/
def qAtom : Atom := .expression [.symbol "q"]

/-- `(exec (z) (, (exec (z) $i (O (- $c) $a)) $x) (O (- (out)) (count $c 1 $x)))`: the
executable reads itself to bind `$c` to `(out)` and writes `(out)` exactly when the read
copy holds one atom. -/
def countGadget : Atom :=
  .expression [.symbol "exec", locZ,
    .expression [.symbol ",",
      .expression [.symbol "exec", locZ, .var "i",
        .expression [.symbol "O", .expression [.symbol "-", .var "c"], .var "a"]],
      .var "x"],
    .expression [.symbol "O", .expression [.symbol "-", outAtom],
      .expression [.symbol "count", .var "c", .symbol "1", .var "x"]]]

open Mainline in
/-- **A count guard reproduces the witness pair**, and fails on another context: beside
`(q)` it is silent although no `(p)` is present. -/
theorem count_gadget_reproduces_witness :
    (mainlineStep defaultProfile inertPrimitives ExternalState.empty [countGadget]).space? =
        some [outAtom] ∧
      (mainlineStep defaultProfile inertPrimitives ExternalState.empty
        [countGadget, pAtom]).space? = some [pAtom] ∧
      (mainlineStep defaultProfile inertPrimitives ExternalState.empty
        [countGadget, qAtom]).space? = some [qAtom] := by
  decide +kernel

/-- `(cand (not))`: a marker no context can contain, since every atom mentioning `not` is
translated. -/
def candAtom : Atom := .expression [.symbol "cand", .expression [.symbol "not"]]

/-- `(exec () (, (p)) (O (- (cand (not)))))`. -/
def absenceStageRemove : Atom :=
  .expression [.symbol "exec", .expression [], .expression [.symbol ",", pAtom],
    .expression [.symbol "O", .expression [.symbol "-", candAtom]]]

/-- `(exec () (, (cand (not))) (O (- (cand (not))) (+ (out))))`. -/
def absenceStageReport : Atom :=
  .expression [.symbol "exec", .expression [], .expression [.symbol ",", candAtom],
    .expression [.symbol "O", .expression [.symbol "-", candAtom],
      .expression [.symbol "+", outAtom]]]

/-- The absence executable translated into a marker and two decision stages.  The stages
sit at the location `()`, below every executable that remains when `(z)` is selected, so
they fire next. -/
def stagedAbsence : Atom :=
  .expression [.symbol "exec", locZ, .expression [.symbol ","],
    .expression [.symbol "O", .expression [.symbol "+", candAtom],
      .expression [.symbol "+", absenceStageRemove],
      .expression [.symbol "+", absenceStageReport]]]

/-- `(exec (zz) (,) (O (+ (p))))`: an executable after `(z)` that writes `(p)`. -/
def laterWriter : Atom :=
  .expression [.symbol "exec", .expression [.symbol "zz"], .expression [.symbol ","],
    .expression [.symbol "O", .expression [.symbol "+", pAtom]]]

open Mainline in
/-- **Downward staging reproduces absence** on the witness pair, beside the unrelated
`(q)`, and before a later executable that writes `(p)`; every run ends without a fault. -/
theorem downward_staging_reproduces_witness :
    (mainlineRun defaultProfile inertPrimitives 5 ExternalState.empty [stagedAbsence]).1 =
        [outAtom] ∧
      (mainlineRun defaultProfile inertPrimitives 5 ExternalState.empty
        [stagedAbsence, pAtom]).1 = [pAtom] ∧
      (mainlineRun defaultProfile inertPrimitives 5 ExternalState.empty
        [stagedAbsence, qAtom]).1 = [qAtom, outAtom] ∧
      (mainlineRun defaultProfile inertPrimitives 6 ExternalState.empty
        [stagedAbsence, laterWriter]).1 = [outAtom, pAtom] ∧
      (mainlineRun defaultProfile inertPrimitives 6 ExternalState.empty
        [stagedAbsence, laterWriter]).2.2 = none := by
  decide +kernel


/-! ### Absence at a stratum boundary, in every context

The staged gadget is not only right on the witness pair.  Above every executable-free
context whose atoms share no key with the gadget, it reports `(out)` exactly when no
`(p)` is present: the least-key schedule places its two stages before anything else,
so the stages read a stable snapshot. -/

section StratumBoundary

open Mainline

mutual
theorem ruleTemplateCovered_ground (input : InputSpec) (σ : Subst) : ∀ (atom : Atom),
    isGroundAtom atom = true → ruleTemplateCovered input σ atom = true
  | .var _, ground => by simp [isGroundAtom] at ground
  | .symbol _, _ => by simp [ruleTemplateCovered]
  | .grounded _, _ => by simp [ruleTemplateCovered]
  | .expression children, ground => by
      simp only [ruleTemplateCovered]
      exact ruleTemplatesCovered_ground input σ children (by simpa [isGroundAtom] using ground)
theorem ruleTemplatesCovered_ground (input : InputSpec) (σ : Subst) : ∀ (atoms : List Atom),
    isGroundAtom.isGroundList atoms = true → ruleTemplatesCovered input σ atoms = true
  | [], _ => by simp [ruleTemplatesCovered]
  | atom :: rest, ground => by
      simp only [isGroundAtom.isGroundList, Bool.and_eq_true] at ground
      simp [ruleTemplatesCovered, ruleTemplateCovered_ground input σ atom ground.1,
        ruleTemplatesCovered_ground input σ rest ground.2]
end

theorem instantiate_ground (input : InputSpec) (σ : Subst) (atom : Atom) (ground : isGroundAtom atom = true) :
    instantiateRuleTemplateAtom? input σ atom = some atom := by
  simp [instantiateRuleTemplateAtom?, ruleTemplateCovered_ground input σ atom ground,
    applySubst_of_ground σ atom ground]

theorem staged_ground (input : InputSpec) (rows : List Subst) (atom : Atom) (ground : isGroundAtom atom = true) :
    staged input rows atom = if rows = [] then [] else [atom] := by
  unfold staged instances
  simp only [instantiate_ground input _ atom ground]
  cases rows with
  | nil => rfl
  | cons first rest =>
      simp only [List.filterMap_cons, List.foldl_cons, reduceCtorEq, if_false]
      show List.foldl morkInsertSupport [atom] (rest.filterMap fun _ => some atom) = [atom]
      apply foldl_insert_of_all_contained
      intro other member
      simp only [List.mem_filterMap, Option.some.injEq] at member
      obtain ⟨_, _, equal⟩ := member
      rw [← equal]
      exact contains_of_mem [atom] atom (by simp)

/-! Frame lemmas: a context without the relevant keys passes through unchanged. -/

def KeyFree (context : List Atom) (atom : Atom) : Prop :=
  ∀ other ∈ context, morkSupportKey other ≠ morkSupportKey atom

theorem contains_frame (context rest : List Atom) (atom : Atom) (free : KeyFree context atom) :
    morkSupportContains (context ++ rest) atom = morkSupportContains rest atom := by
  cases containsRest : morkSupportContains rest atom with
  | true =>
      rw [morkSupportContains_eq_true_iff_key_mem] at containsRest ⊢
      simp only [List.map_append, List.mem_append]
      exact Or.inr containsRest
  | false =>
      apply Bool.eq_false_iff.mpr
      intro present
      rw [morkSupportContains_eq_true_iff_key_mem] at present
      simp only [List.map_append, List.mem_append, List.mem_map] at present
      rcases present with ⟨other, member, equal⟩ | inRest
      · exact free other member equal
      · have : morkSupportContains rest atom = true :=
          (morkSupportContains_eq_true_iff_key_mem rest atom).2 (List.mem_map.2 inRest)
        rw [this] at containsRest
        cases containsRest

theorem insert_frame (context rest : List Atom) (atom : Atom) (free : KeyFree context atom) :
    morkInsertSupport (context ++ rest) atom = context ++ morkInsertSupport rest atom := by
  unfold morkInsertSupport
  rw [contains_frame context rest atom free]
  split <;> simp

theorem erase_frame (context rest : List Atom) (atom : Atom) (free : KeyFree context atom) :
    morkEraseSupport (context ++ rest) atom = context ++ morkEraseSupport rest atom := by
  unfold morkEraseSupport
  rw [List.filter_append]
  congr 1
  apply List.filter_eq_self.mpr
  intro other member
  simp [sameMorkSupportAtom, free other member]

theorem union_frame (context : List Atom) : ∀ (rest staged : List Atom),
    (∀ atom ∈ staged, KeyFree context atom) →
      morkUnionSupport (context ++ rest) staged = context ++ morkUnionSupport rest staged
  | rest, [], _ => rfl
  | rest, atom :: more, free => by
      simp only [morkUnionSupport, List.foldl_cons]
      rw [insert_frame context rest atom (free atom (by simp))]
      exact union_frame context _ more (fun other member => free other (by simp [member]))

theorem subtract_frame (context : List Atom) : ∀ (rest staged : List Atom),
    (∀ atom ∈ staged, KeyFree context atom) →
      morkSubtractSupport (context ++ rest) staged = context ++ morkSubtractSupport rest staged
  | rest, [], _ => rfl
  | rest, atom :: more, free => by
      simp only [morkSubtractSupport, List.foldl_cons]
      rw [erase_frame context rest atom (free atom (by simp))]
      exact subtract_frame context _ more (fun other member => free other (by simp [member]))

theorem rawExecFacts_frame (context rest : List Atom)
    (execFree : ∀ atom ∈ context, extractRawExecFact atom = none) :
    WQComputable.cRawExecFacts (context ++ rest) = WQComputable.cRawExecFacts rest := by
  unfold WQComputable.cRawExecFacts
  rw [List.filterMap_append, List.filterMap_eq_nil_iff.mpr execFree, List.nil_append]


section Gadget

theorem union_frame_nil (context staged : List Atom) (free : ∀ atom ∈ staged, KeyFree context atom) :
    morkUnionSupport context staged = context ++ morkUnionSupport [] staged := by
  simpa using union_frame context [] staged free

def stagedRaw : RawExecFact :=
  ⟨stagedAbsence, locZ, .expression [.symbol ","],
    .expression [.symbol "O", .expression [.symbol "+", candAtom],
      .expression [.symbol "+", absenceStageRemove], .expression [.symbol "+", absenceStageReport]]⟩

def removeRaw : RawExecFact :=
  ⟨absenceStageRemove, .expression [], .expression [.symbol ",", pAtom],
    .expression [.symbol "O", .expression [.symbol "-", candAtom]]⟩

def reportRaw : RawExecFact :=
  ⟨absenceStageReport, .expression [], .expression [.symbol ",", candAtom],
    .expression [.symbol "O", .expression [.symbol "-", candAtom], .expression [.symbol "+", outAtom]]⟩

theorem ground_cand : isGroundAtom candAtom = true := rfl
theorem ground_out : isGroundAtom outAtom = true := rfl
theorem ground_p : isGroundAtom pAtom = true := rfl
theorem ground_remove : isGroundAtom absenceStageRemove = true := rfl
theorem ground_report : isGroundAtom absenceStageReport = true := rfl

variable (profile : BuildProfile) (prims : Primitives) (external : ExternalState) (context : List Atom)
  (contextGround : ∀ atom ∈ context, isGroundAtom atom = true)
  (execFree : ∀ atom ∈ context, extractRawExecFact atom = none)
  (freeCand : KeyFree context candAtom) (freeOut : KeyFree context outAtom)
  (freeStaged : KeyFree context stagedAbsence) (freeRemove : KeyFree context absenceStageRemove)
  (freeReport : KeyFree context absenceStageReport)

include execFree freeCand freeStaged freeRemove freeReport in
theorem gadget_step1 :
    mainlineStep profile prims external (context ++ [stagedAbsence]) =
      .next (context ++ [candAtom, absenceStageRemove, absenceStageReport]) external := by
  have select : selectNextScheduled (WQComputable.cRawExecFacts (context ++ [stagedAbsence])) =
      some stagedRaw := by
    rw [rawExecFacts_frame context _ execFree]; rfl
  have live : morkEraseSupport (context ++ [stagedAbsence]) stagedAbsence = context := by
    rw [erase_frame context _ _ freeStaged, erase_single, List.append_nil]
  have read : morkInsertSupport context stagedAbsence = context ++ [stagedAbsence] := by
    have framed := insert_frame context [] stagedAbsence freeStaged
    rw [List.append_nil] at framed
    rw [framed]
    rfl
  have rows : (conjunctionRows (factorTag stagedAbsence) (context ++ [stagedAbsence]) 0 [] []).map
      (inputRow (inputSpecVariables (MainlineInput.compat []).coverage)) = [[]] := rfl
  unfold mainlineStep
  rw [select]
  simp only [show decodeDirective profile stagedRaw = .ok (some ⟨stagedAbsence, .compat [],
    .sinks [.core (.add candAtom), .core (.add absenceStageRemove), .core (.add absenceStageReport)]⟩)
    from rfl]
  simp only [fireDirective, live, read, mainlineRows, rows, bind, Except.bind, applyMainlineSinks,
    List.foldl_cons, List.foldl_nil, eagerOutputs, staged_ground _ _ _ ground_cand,
    staged_ground _ _ _ ground_remove, staged_ground _ _ _ ground_report, List.cons_ne_nil,
    if_false, List.foldlM_cons, List.foldlM_nil, finalizeMainlineSink, pure, Except.pure]
  rw [union_frame_nil context [candAtom] (by simpa using freeCand),
    union_frame context _ [absenceStageRemove] (by simpa using freeRemove),
    union_frame context _ [absenceStageReport] (by simpa using freeReport)]
  rfl

/-- The rows of a ground single pattern over a ground read copy, as the outputs see them. -/
theorem ground_rows (tag : ℕ → String) (pattern : Atom) (groundPattern : isGroundAtom pattern = true)
    (read : List Atom) (groundRead : ∀ atom ∈ read, isGroundAtom atom = true) :
    (conjunctionRows tag read 0 [] [pattern]).map
        (inputRow (inputSpecVariables (MainlineInput.compat [pattern]).coverage)) =
      (read.filter fun atom => atom = pattern).map fun _ => [] := by
  rw [conjunctionRows_single_ground tag 0 [] pattern groundPattern read groundRead, List.map_map]
  have noVariables : inputSpecVariables (MainlineInput.compat [pattern]).coverage = [] := by
    simp only [MainlineInput.coverage, inputSpecVariables]
    simp [atomFreeVars.atomFreeVarsList, atomFreeVars_of_ground pattern groundPattern]
  rw [noVariables]
  rfl

include contextGround in
theorem rows_p (tag : ℕ → String) (rest : List Atom) (restFree : pAtom ∉ rest)
    (restGround : ∀ atom ∈ rest, isGroundAtom atom = true) :
    (conjunctionRows tag (context ++ rest) 0 [] [pAtom]).map
        (inputRow (inputSpecVariables (MainlineInput.compat [pAtom]).coverage)) =
      (context.filter fun atom => atom = pAtom).map fun _ => [] := by
  rw [ground_rows tag pAtom ground_p (context ++ rest) (by
    intro atom member
    rcases List.mem_append.1 member with inContext | inRest
    · exact contextGround atom inContext
    · exact restGround atom inRest), List.filter_append]
  have restEmpty : (rest.filter fun atom => atom = pAtom) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro atom member same
    simp only [decide_eq_true_eq] at same
    exact restFree (same ▸ member)
  rw [restEmpty, List.append_nil]

include contextGround execFree freeCand freeRemove in
theorem gadget_step2 :
    mainlineStep profile prims external
        (context ++ [candAtom, absenceStageRemove, absenceStageReport]) =
      .next (if pAtom ∈ context then context ++ [absenceStageReport]
        else context ++ [candAtom, absenceStageReport]) external := by
  have select : selectNextScheduled (WQComputable.cRawExecFacts
      (context ++ [candAtom, absenceStageRemove, absenceStageReport])) = some removeRaw := by
    rw [rawExecFacts_frame context _ execFree]; rfl
  have live : morkEraseSupport (context ++ [candAtom, absenceStageRemove, absenceStageReport])
      absenceStageRemove = context ++ [candAtom, absenceStageReport] := by
    rw [erase_frame context _ _ freeRemove]; rfl
  have read : morkInsertSupport (context ++ [candAtom, absenceStageReport]) absenceStageRemove =
      context ++ [candAtom, absenceStageReport, absenceStageRemove] := by
    rw [insert_frame context _ _ freeRemove]; rfl
  unfold mainlineStep
  rw [select]
  simp only [show decodeDirective profile removeRaw = .ok (some ⟨absenceStageRemove,
    .compat [pAtom], .sinks [.core (.remove candAtom)]⟩) from rfl]
  simp only [fireDirective, live, read, mainlineRows, bind, Except.bind]
  rw [rows_p context contextGround _ _ (by decide) (by decide)]
  simp only [applyMainlineSinks, List.foldl_cons, List.foldl_nil, eagerOutputs, union_nil,
    List.foldlM_cons, List.foldlM_nil, finalizeMainlineSink, staged_ground _ _ _ ground_cand,
    pure, Except.pure]
  by_cases present : pAtom ∈ context
  · have nonempty : (context.filter fun atom => atom = pAtom).map (fun _ => ([] : Subst)) ≠ [] := by
      simp only [ne_eq, List.map_eq_nil_iff, List.filter_eq_nil_iff, decide_eq_true_eq, not_forall,
        not_not]
      exact ⟨pAtom, present, rfl⟩
    simp only [nonempty, if_false, present, if_true]
    rw [subtract_frame context _ [candAtom] (by simpa using freeCand)]
    rfl
  · have empty : (context.filter fun atom => atom = pAtom).map (fun _ => ([] : Subst)) = [] := by
      simp only [List.map_eq_nil_iff, List.filter_eq_nil_iff, decide_eq_true_eq]
      intro atom member same
      exact present (same ▸ member)
    simp only [empty, if_true, present, if_false]
    rfl

theorem not_mem_of_keyFree {atom : Atom} (free : KeyFree context atom) : atom ∉ context :=
  fun member => free atom member rfl

include contextGround execFree freeCand freeReport in
theorem gadget_step3_present :
    mainlineStep profile prims external (context ++ [absenceStageReport]) = .next context external := by
  have select : selectNextScheduled (WQComputable.cRawExecFacts (context ++ [absenceStageReport])) =
      some reportRaw := by
    rw [rawExecFacts_frame context _ execFree]; rfl
  have live : morkEraseSupport (context ++ [absenceStageReport]) absenceStageReport = context := by
    rw [erase_frame context _ _ freeReport, erase_single, List.append_nil]
  have read : morkInsertSupport context absenceStageReport = context ++ [absenceStageReport] := by
    have framed := insert_frame context [] absenceStageReport freeReport
    rw [List.append_nil] at framed
    rw [framed]
    rfl
  have rows : (conjunctionRows (factorTag absenceStageReport) (context ++ [absenceStageReport]) 0 []
      [candAtom]).map (inputRow (inputSpecVariables (MainlineInput.compat [candAtom]).coverage)) = [] := by
    rw [ground_rows _ candAtom ground_cand _ (by
      intro atom member
      rcases List.mem_append.1 member with inContext | inRest
      · exact contextGround atom inContext
      · simp at inRest; subst inRest; rfl), List.filter_append]
    have none : (context.filter fun atom => atom = candAtom) = [] := by
      apply List.filter_eq_nil_iff.mpr
      intro atom member same
      simp only [decide_eq_true_eq] at same
      exact not_mem_of_keyFree context freeCand (same ▸ member)
    rw [none]
    rfl
  unfold mainlineStep
  rw [select]
  simp only [show decodeDirective profile reportRaw = .ok (some ⟨absenceStageReport,
    .compat [candAtom], .sinks [.core (.remove candAtom), .core (.add outAtom)]⟩) from rfl]
  simp only [fireDirective, live, read, mainlineRows, rows, bind, Except.bind, applyMainlineSinks,
    List.foldl_cons, List.foldl_nil, eagerOutputs, staged_no_rows, union_nil, List.foldlM_cons,
    List.foldlM_nil, finalizeMainlineSink, pure, Except.pure]
  rfl

include contextGround execFree freeCand freeOut freeReport in
theorem gadget_step3_absent :
    mainlineStep profile prims external (context ++ [candAtom, absenceStageReport]) =
      .next (context ++ [outAtom]) external := by
  have select : selectNextScheduled (WQComputable.cRawExecFacts
      (context ++ [candAtom, absenceStageReport])) = some reportRaw := by
    rw [rawExecFacts_frame context _ execFree]; rfl
  have live : morkEraseSupport (context ++ [candAtom, absenceStageReport]) absenceStageReport =
      context ++ [candAtom] := by
    rw [erase_frame context _ _ freeReport]; rfl
  have read : morkInsertSupport (context ++ [candAtom]) absenceStageReport =
      context ++ [candAtom, absenceStageReport] := by
    rw [insert_frame context _ _ freeReport]; rfl
  have rows : (conjunctionRows (factorTag absenceStageReport) (context ++ [candAtom, absenceStageReport])
      0 [] [candAtom]).map (inputRow (inputSpecVariables (MainlineInput.compat [candAtom]).coverage)) =
      [[]] := by
    rw [ground_rows _ candAtom ground_cand _ (by
      intro atom member
      rcases List.mem_append.1 member with inContext | inRest
      · exact contextGround atom inContext
      · simp at inRest; rcases inRest with rfl | rfl <;> rfl), List.filter_append]
    have none : (context.filter fun atom => atom = candAtom) = [] := by
      apply List.filter_eq_nil_iff.mpr
      intro atom member same
      simp only [decide_eq_true_eq] at same
      exact not_mem_of_keyFree context freeCand (same ▸ member)
    rw [none]
    rfl
  unfold mainlineStep
  rw [select]
  simp only [show decodeDirective profile reportRaw = .ok (some ⟨absenceStageReport,
    .compat [candAtom], .sinks [.core (.remove candAtom), .core (.add outAtom)]⟩) from rfl]
  simp only [fireDirective, live, read, mainlineRows, rows, bind, Except.bind, applyMainlineSinks,
    List.foldl_cons, List.foldl_nil, eagerOutputs, union_nil, staged_ground _ _ _ ground_out,
    staged_ground _ _ _ ground_cand, List.cons_ne_nil, if_false, List.foldlM_cons, List.foldlM_nil,
    finalizeMainlineSink, pure, Except.pure]
  rw [union_frame context _ [outAtom] (by simpa using freeOut),
    subtract_frame context _ [candAtom] (by simpa using freeCand)]
  rfl

include execFree in
theorem gadget_quiescent (extra : List Atom) (extraFree : WQComputable.cRawExecFacts extra = []) :
    mainlineStep profile prims external (context ++ extra) = .quiescent := by
  unfold mainlineStep
  rw [rawExecFacts_frame context _ execFree, extraFree]
  rfl

include contextGround execFree freeCand freeOut freeStaged freeRemove freeReport in
/-- **Absence at a stratum boundary.**  In every ground context without executables whose
atoms share no key with the gadget, the translated absence executable leaves the context
and adds `(out)` exactly when `(p)` is absent, in four steps.  Groundness matters: the
kernel unifies, so a stored atom with variables, such as `$x` or `($y)`, meets the
pattern `(p)` and counts as present. -/
theorem downward_staging_decides_absence :
    (mainlineRun profile prims 4 external (context ++ [stagedAbsence])).1 =
      if pAtom ∈ context then context else context ++ [outAtom] := by
  simp only [mainlineRun, gadget_step1 profile prims external context execFree freeCand freeStaged
    freeRemove freeReport, gadget_step2 profile prims external context contextGround execFree freeCand
    freeRemove]
  by_cases present : pAtom ∈ context
  · simp only [present, if_true, gadget_step3_present profile prims external context contextGround
      execFree freeCand freeReport]
    rw [show context = context ++ [] from (List.append_nil context).symm,
      gadget_quiescent profile prims external context execFree [] rfl]
  · simp only [present, if_false, gadget_step3_absent profile prims external context contextGround
      execFree freeCand freeOut freeReport, gadget_quiescent profile prims external context execFree
      [outAtom] rfl]

end Gadget

end StratumBoundary

/-! ### One conjunct and a generated stage reproduce a join

Under a global criterion, as for rule priorities in CHR, a conjunction need not be
primitive: an executable with one conjunct can write, for every row, an executable that
tests the next conjunct, placed below its own key so that it runs before anything
else.  The instance below reproduces a two-conjunct join and what a later executable
sees. -/

/-- `(p x)`. -/
def pOf (name : String) : Atom := .expression [.symbol "p", .symbol name]

/-- `(q x)`. -/
def qOf (name : String) : Atom := .expression [.symbol "q", .symbol name]

/-- `(exec (zz) (, (r $y)) (O (+ (seen $y))))`. -/
def joinObserver : Atom :=
  .expression [.symbol "exec", .expression [.symbol "zz"],
    .expression [.symbol ",", .expression [.symbol "r", .var "y"]],
    .expression [.symbol "O", .expression [.symbol "+", .expression [.symbol "seen", .var "y"]]]]

/-- `(exec (z) (, (p $x) (q $x)) (O (+ (r $x))))`. -/
def twoConjunctJoin : Atom :=
  .expression [.symbol "exec", locZ,
    .expression [.symbol ",", .expression [.symbol "p", .var "x"], .expression [.symbol "q", .var "x"]],
    .expression [.symbol "O", .expression [.symbol "+", .expression [.symbol "r", .var "x"]]]]

/-- `(exec (z) (, (p $x)) (O (+ (exec () (, (q $x)) (O (+ (r $x)))))))`. -/
def stagedJoin : Atom :=
  .expression [.symbol "exec", locZ,
    .expression [.symbol ",", .expression [.symbol "p", .var "x"]],
    .expression [.symbol "O", .expression [.symbol "+",
      .expression [.symbol "exec", .expression [],
        .expression [.symbol ",", .expression [.symbol "q", .var "x"]],
        .expression [.symbol "O", .expression [.symbol "+", .expression [.symbol "r", .var "x"]]]]]]]

open Mainline in
/-- **The staged single-conjunct translation reproduces the join** and its observer. -/
theorem staged_join_reproduces_join :
    (mainlineRun defaultProfile inertPrimitives 6 ExternalState.empty
        [pOf "a", pOf "b", qOf "b", qOf "c", twoConjunctJoin, joinObserver]).1 =
      (mainlineRun defaultProfile inertPrimitives 6 ExternalState.empty
        [pOf "a", pOf "b", qOf "b", qOf "c", stagedJoin, joinObserver]).1 := by
  decide +kernel

end Mettapedia.Languages.ProcessCalculi.MORK.Expressiveness
