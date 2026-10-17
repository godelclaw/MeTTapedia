import Mettapedia.Computability.RegularLanguages.RegexPikeVM

/-!
# Composition of first-visit closures

The derivation records the final visited set, which the executable closure
does not return. Its serial-composition law connects a closure of an ordered
root list to incremental closure calls sharing the visited set. Thread data
is retained literally, including capture snapshots. This is a closure law,
not the whole Pike winner-selection theorem.
-/

set_option autoImplicit false

namespace Mettapedia.Computability.RegularLanguages.RegexClosureComposition

open RegexTaggedGraph

universe u v

variable {Value : Type u} {Key : Type v} [DecidableEq Key]

/-- A finite derivation of ordered first visits, with the actual final memo.
There is no recursion budget in this judgment. -/
inductive Closure (key : Value → Key) (children : Value → List Value) (emit : Value → Bool) :
    List Value → Finset Key → List Value → Finset Key → Prop
  | nil (seen) : Closure key children emit [] seen [] seen
  | skip {first rest seen output final} : key first ∈ seen →
      Closure key children emit rest seen output final →
      Closure key children emit (first :: rest) seen output final
  | visit {first rest seen later final} : key first ∉ seen →
      Closure key children emit (children first ++ rest) (insert (key first) seen) later final →
      Closure key children emit (first :: rest) seen
        (if emit first then first :: later else later) final

variable {key : Value → Key} {children : Value → List Value} {emit : Value → Bool}

theorem Closure.seen_mono {pending seen output final}
    (closed : Closure key children emit pending seen output final) : seen ⊆ final := by
  induction closed with
  | nil => exact Finset.Subset.refl _
  | skip _ _ ih => exact ih
  | visit _ _ ih => exact (Finset.subset_insert _ _).trans ih

theorem Closure.roots_seen {pending seen output final}
    (closed : Closure key children emit pending seen output final) :
    ∀ value ∈ pending, key value ∈ final := by
  induction closed with
  | nil => simp
  | @skip first rest seen output final visited tail ih =>
      intro value member
      rcases List.mem_cons.mp member with same | member
      · subst value; exact tail.seen_mono visited
      · exact ih value member
  | @visit first rest seen later final fresh tail ih =>
      intro value member
      rcases List.mem_cons.mp member with same | member
      · subst value; exact tail.seen_mono (Finset.mem_insert_self _ _)
      · exact ih value (List.mem_append_right _ member)

theorem Closure.all_seen (pending : List Value) (seen : Finset Key)
    (covered : ∀ value ∈ pending, key value ∈ seen) :
    Closure key children emit pending seen [] seen := by
  induction pending with
  | nil => exact .nil _
  | cons first rest ih =>
      exact .skip (covered first (by simp))
        (ih (fun value member => covered value (by simp [member])))

/-- Sequential roots preserve their complete ordered output, not only keys. -/
theorem Closure.append {first seen before middle}
    (left : Closure key children emit first seen before middle) :
    ∀ {second after final}, Closure key children emit second middle after final →
      Closure key children emit (first ++ second) seen (before ++ after) final := by
  induction left with
  | nil => intro second after final right; exact right
  | skip visited tail ih =>
      intro second after final right
      exact .skip visited (ih right)
  | @visit current rest seen later middle fresh tail ih =>
      intro second after final right
      have combined := ih right
      rw [List.append_assoc] at combined
      have visited := Closure.visit (emit := emit) fresh combined
      cases emitted : emit current <;> simpa [emitted] using visited

/-- Conversely, a combined closure can be cut at any root-list boundary.
The cut memo includes non-emitted epsilon states as well as frontier states. -/
theorem Closure.split {pending seen output final}
    (closed : Closure key children emit pending seen output final) :
    ∀ first second, pending = first ++ second →
      ∃ before middle after,
        Closure key children emit first seen before middle ∧
        Closure key children emit second middle after final ∧ output = before ++ after := by
  induction closed with
  | nil seen =>
      intro first second same
      have empty : first = [] ∧ second = [] := by simpa using same.symm
      rcases empty with ⟨rfl, rfl⟩
      exact ⟨[], seen, [], .nil _, .nil _, rfl⟩
  | @skip current rest seen output final visited tail ih =>
      intro first second same
      cases first with
      | nil =>
          have secondRest : second = current :: rest := by simpa using same.symm
          subst second
          exact ⟨[], seen, output, .nil _, .skip visited tail, rfl⟩
      | cons head first =>
          obtain ⟨rfl, restSame⟩ := List.cons.inj same
          obtain ⟨before, middle, after, left, right, outputSame⟩ := ih first second restSame
          exact ⟨before, middle, after, .skip visited left, right, outputSame⟩
  | @visit current rest seen later final fresh tail ih =>
      intro first second same
      cases first with
      | nil =>
          have secondRest : second = current :: rest := by simpa using same.symm
          subst second
          exact ⟨[], seen, _, .nil _, .visit fresh tail, rfl⟩
      | cons head first =>
          obtain ⟨rfl, restSame⟩ := List.cons.inj same
          have cut : children current ++ rest = (children current ++ first) ++ second := by
            rw [restSame, List.append_assoc]
            rfl
          obtain ⟨before, middle, after, left, right, outputSame⟩ := ih _ second cut
          refine ⟨if emit current then current :: before else before, middle, after,
            .visit fresh left, right, ?_⟩
          cases emit current <;> simp [outputSame]

theorem closure_append_iff (first second : List Value) (seen : Finset Key)
    (output : List Value) (final : Finset Key) :
    Closure key children emit (first ++ second) seen output final ↔
      ∃ before middle after,
        Closure key children emit first seen before middle ∧
        Closure key children emit second middle after final ∧ output = before ++ after := by
  constructor
  · intro closed; exact closed.split first second rfl
  · rintro ⟨before, middle, after, left, right, rfl⟩
    exact left.append right

/-- A later root batch whose keys were covered by an earlier batch cannot
overwrite the earlier captures or add frontier occurrences. -/
theorem Closure.covered_suffix {first seen output final}
    (left : Closure key children emit first seen output final)
    (second : List Value) (covered : ∀ value ∈ second, key value ∈ final) :
    Closure key children emit (first ++ second) seen output final := by
  simpa using left.append (Closure.all_seen (children := children) (emit := emit) second final covered)

/-- Every completed executable closure has a finite memo derivation. -/
theorem firstVisits_derivation (fuel : Nat) :
    ∀ pending seen output,
      firstVisits key children emit fuel pending seen = some output →
      ∃ final, Closure key children emit pending seen output final := by
  induction fuel with
  | zero => simp [firstVisits]
  | succ fuel ih =>
      intro pending seen output finished
      cases pending with
      | nil =>
          simp only [firstVisits, Option.some.injEq] at finished
          subst output
          exact ⟨seen, .nil _⟩
      | cons first rest =>
          by_cases visited : key first ∈ seen
          · simp only [firstVisits, visited, ↓reduceIte] at finished
            obtain ⟨final, tail⟩ := ih rest seen output finished
            exact ⟨final, .skip visited tail⟩
          · simp only [firstVisits, visited, ↓reduceIte] at finished
            cases next : firstVisits key children emit fuel (children first ++ rest)
                (insert (key first) seen) with
            | none => simp [next] at finished
            | some later =>
                simp only [next, Option.map_some, Option.some.injEq] at finished
                subst output
                obtain ⟨final, tail⟩ := ih _ _ later next
                exact ⟨final, .visit visited tail⟩

/-- A semantic closure is realizable by the existing executable closure at
every sufficiently large fuel. The threshold is proved, not an API ceiling. -/
theorem Closure.eventually_firstVisits {pending seen output final}
    (closed : Closure key children emit pending seen output final) :
    ∃ threshold, ∀ fuel, threshold ≤ fuel →
      firstVisits key children emit fuel pending seen = some output := by
  induction closed with
  | nil seen =>
      refine ⟨1, ?_⟩
      intro fuel enough
      cases fuel with
      | zero => omega
      | succ fuel => rfl
  | skip visited tail ih =>
      obtain ⟨threshold, enough⟩ := ih
      refine ⟨threshold + 1, ?_⟩
      intro fuel bound
      cases fuel with
      | zero => omega
      | succ fuel => simpa [firstVisits, visited] using enough fuel (by omega)
  | visit fresh tail ih =>
      obtain ⟨threshold, enough⟩ := ih
      refine ⟨threshold + 1, ?_⟩
      intro fuel bound
      cases fuel with
      | zero => omega
      | succ fuel => simp [firstVisits, fresh, enough fuel (by omega)]

theorem Closure.output_unique {pending seen first final second otherFinal}
    (left : Closure key children emit pending seen first final)
    (right : Closure key children emit pending seen second otherFinal) : first = second := by
  obtain ⟨leftFuel, leftEnough⟩ := left.eventually_firstVisits
  obtain ⟨rightFuel, rightEnough⟩ := right.eventually_firstVisits
  exact Option.some.inj ((leftEnough (leftFuel + rightFuel) (by omega)).symm.trans
    (rightEnough (leftFuel + rightFuel) (by omega)))

theorem firstVisits_exists_iff (pending : List Value) (seen : Finset Key) (output : List Value) :
    (∃ fuel, firstVisits key children emit fuel pending seen = some output) ↔
      ∃ final, Closure key children emit pending seen output final := by
  constructor
  · rintro ⟨fuel, finished⟩; exact firstVisits_derivation fuel pending seen output finished
  · rintro ⟨final, closed⟩
    obtain ⟨fuel, enough⟩ := closed.eventually_firstVisits
    exact ⟨fuel, enough fuel (Nat.le_refl _)⟩

/-- Adding lower-priority roots cannot alter the completed frontier of the
earlier roots. Sufficient fuel for both calls is supplied by their outcomes. -/
theorem firstVisits_append_prefix (fuel : Nat) (first second : List Value) (seen : Finset Key)
    (before output : List Value)
    (left : firstVisits key children emit fuel first seen = some before)
    (whole : firstVisits key children emit fuel (first ++ second) seen = some output) :
    ∃ after, output = before ++ after := by
  obtain ⟨leftFinal, leftClosed⟩ := firstVisits_derivation fuel first seen before left
  obtain ⟨final, wholeClosed⟩ := firstVisits_derivation fuel _ seen output whole
  obtain ⟨portion, middle, after, prefixClosed, _, same⟩ := wholeClosed.split first second rfl
  have prefixSame := prefixClosed.output_unique leftClosed
  exact ⟨after, prefixSame ▸ same⟩

section Rekey

variable {OtherKey : Type*} [DecidableEq OtherKey]

/-- Keys may be embedded in a larger key space when all reachable values obey
the same embedding. This does not identify keys across different input layers. -/
theorem Closure.rekey (embed : Key → OtherKey) (injective : Function.Injective embed)
    (otherKey : Value → OtherKey) (valid : Value → Prop)
    (keyEq : ∀ value, valid value → otherKey value = embed (key value))
    (preserved : ∀ first, valid first → ∀ next ∈ children first, valid next)
    {pending seen output final} (closed : Closure key children emit pending seen output final) :
    (∀ value ∈ pending, valid value) →
    Closure otherKey children emit pending (seen.image embed) output (final.image embed) := by
  induction closed with
  | nil seen => intro _; exact .nil _
  | @skip first rest seen output final visited tail ih =>
      intro initial
      have firstValid := initial first (by simp)
      apply Closure.skip
      · rw [keyEq first firstValid]
        exact Finset.mem_image.mpr ⟨key first, visited, rfl⟩
      · exact ih (fun value member => initial value (by simp [member]))
  | @visit first rest seen later final fresh tail ih =>
      intro initial
      have firstValid := initial first (by simp)
      have freshOther : otherKey first ∉ seen.image embed := by
        rw [keyEq first firstValid]
        intro member
        obtain ⟨old, oldMember, same⟩ := Finset.mem_image.mp member
        exact fresh ((injective same) ▸ oldMember)
      have next := ih (by
        intro value member
        rcases List.mem_append.mp member with child | root
        · exact preserved first firstValid value child
        · exact initial value (by simp [root]))
      rw [Finset.image_insert, ← keyEq first firstValid] at next
      exact .visit freshOther next

end Rekey

section Graph

universe w z

variable {State : Type u} {Class : Type v} {Assertion : Type w} {Tag : Type z} {length : Nat}

/-- Within one synchronous input layer, PC keys and full point keys implement
the same closure. The position hypothesis is proved stable through epsilon
transitions, rather than assumed for arbitrary graph edges. -/
theorem same_position_rekey [DecidableEq State]
    (graph : State → Node State Class Assertion Tag) (probe : OrderedGraphSearch.Probe Class Assertion length)
    (position : Fin (length + 1)) {pending seen output final}
    (closed : Closure (fun thread : Thread State length => thread.point.1)
      (epsilonChildren graph probe) (fun thread => isFrontier (graph thread.point.1))
      pending seen output final)
    (same : ∀ thread ∈ pending, thread.point.2 = position) :
    Closure (fun thread : Thread State length => thread.point)
      (epsilonChildren graph probe) (fun thread => isFrontier (graph thread.point.1))
      pending (seen.image (fun state => (state, position)))
      output (final.image (fun state => (state, position))) := by
  apply closed.rekey (fun state => (state, position)) ?_ (fun thread => thread.point)
    (fun thread => thread.point.2 = position) ?_ ?_ same
  · intro first second equal
    exact congrArg Prod.fst equal
  · intro thread valid
    exact Prod.ext rfl valid
  · intro first valid next edge
    exact (epsilonChildren_same_position graph probe first next edge).trans valid

end Graph

namespace Controls

private def graph : Fin 3 → Node (Fin 3) Unit Unit Unit := fun pc =>
  match pc.val with
  | 0 => .save 0 1
  | 1 => .accept ()
  | _ => .jump 1

private def probe : OrderedGraphSearch.Probe Unit Unit 1 := ⟨fun _ _ => false, fun _ _ => false⟩

private def initial (pc : Fin 3) (old : Option (Fin 2)) : Thread (Fin 3) 1 :=
  ⟨(pc, 0), fun _ => old, []⟩

private def observed (result : Option (List (Thread (Fin 3) 1))) : Option (List (Nat × Option Nat)) :=
  result.map (List.map (fun thread => (thread.point.1.val, (thread.registers 0).map Fin.val)))

theorem earlier_save_retains_its_capture :
    observed (close graph probe 20 [initial 0 none, initial 2 (some 1)]) =
      some [(1, some 0)] := by decide

theorem reversing_roots_changes_the_preferred_snapshot :
    observed (close graph probe 20 [initial 2 (some 1), initial 0 none]) =
      some [(1, some 1)] := by decide

/-- Starting every root with an empty memo is not equivalent to the combined
closure: it duplicates a frontier and keeps a discarded capture snapshot. -/
theorem resetting_memo_between_roots_changes_the_frontier :
    observed (close graph probe 20 [initial 0 none, initial 2 (some 1)]) ≠
      observed ((close graph probe 20 [initial 0 none]).bind (fun first =>
        (close graph probe 20 [initial 2 (some 1)]).map (first ++ ·))) := by decide

end Controls

end Mettapedia.Computability.RegularLanguages.RegexClosureComposition
