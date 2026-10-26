import Mettapedia.GSLT.LanguageDef.DeterministicEquations.ClosureSpecialization

/-!
# Closure-specialization controls

These run the actual evaluator with closure calls on small programs.  The
positive controls establish the lifting's hypotheses for a map over cons
cells and for a relation that returns its closure, and compute both sides of
the square.  The negative controls show the two hypotheses that close it:
an equation that matches the closure against a pattern, and a `let` that
binds the closure parameter again, each make the source and the lifted call
answer differently.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.DeterministicEquations.ClosureSpecialization.Controls

open Mettapedia.GSLT.LanguageDef.DeterministicEquations
open Mettapedia.GSLT.LanguageDef.DeterministicEquations.Closures

private def equation (name head : String) (parameters : List Term) (body : Term) : Equation :=
  { name, head, params := parameters, body }

private def pureHost : Host := { primitive := fun _ _ => .unhandled }

/-! ## A map over cons cells -/

/-- `(tag $c $x) = (Tagged $c $x)`. -/
private def tagEquation : Equation :=
  equation "tag" "tag" [.var "c", .var "x"] (.expr [.sym "Tagged", .var "c", .var "x"])

private def mapNil : Equation :=
  equation "map-nil" "map-cells" [.var "k", .sym "Nil"] (.sym "Nil")

/-- `(map-cells $k (Cons $x $xs)) = (Cons ($k $x) (map-cells $k $xs))`. -/
private def mapCons : Equation :=
  equation "map-cons" "map-cells"
    [.var "k", .expr [.sym "Cons", .var "x", .var "xs"]]
    (.expr [.sym "Cons", .expr [.var "k", .var "x"],
      .expr [.sym "map-cells", .var "k", .var "xs"]])

private def mapProgram : Program := [tagEquation, mapNil, mapCons]

private def mapLifting : Lifting :=
  { source := "map-cells", lifted := "map-cells/tag", callee := "tag", holes := ["h"] }

private def cells : Term :=
  .expr [.sym "Cons", .lit "1", .expr [.sym "Cons", .lit "2", .sym "Nil"]]

private def tagged : Term :=
  .expr [.sym "Cons", .expr [.sym "Tagged", .sym "a", .lit "1"],
    .expr [.sym "Cons", .expr [.sym "Tagged", .sym "a", .lit "2"], .sym "Nil"]]

private theorem clean_var (x : String) (hx : x ∉ mapLifting.holes) :
    Clean mapLifting "k" (.var x) := Clean.var hx

private theorem mapCons_clean : Clean mapLifting "k" mapCons.body := by
  refine Clean.expr ⟨fun h => by simp at h, fun h => by simp at h⟩ ?_
  intro t ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl
  · exact Clean.sym _
  · refine Clean.expr ⟨fun h => by simp at h, fun h => by simp at h⟩ ?_
    intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl <;> exact clean_var _ (by decide)
  · refine Clean.expr ⟨fun h => by simp at h, fun h => by simp at h⟩ ?_
    intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl
    · exact Clean.sym _
    · exact clean_var _ (by decide)
    · exact clean_var _ (by decide)

/-- The map over cons cells satisfies every hypothesis of the lifting. -/
theorem map_lifts : Lifts mapLifting mapProgram pureHost where
  source := ⟨by decide, by decide⟩
  lifted := ⟨by decide, by decide⟩
  callee := ⟨by decide, by decide⟩
  source_ne_lifted := by decide
  lifted_ne_partial := by decide
  holes_nodup := by decide
  fresh := by
    intro e he
    simp only [mapProgram, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl <;> decide
  defined := rfl
  equations := by
    intro e he hs
    simp only [mapProgram, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl
    · exact absurd hs (by decide)
    · exact ⟨"k", [.sym "Nil"], rfl, Clean.sym _⟩
    · exact ⟨"k", [.expr [.sym "Cons", .var "x", .var "xs"]], rfl, mapCons_clean⟩
  partial_free := rfl
  partial_host := fun _ => rfl

/-- The source relation maps the closure over the cells. -/
theorem map_source_answer :
    Closures.apply (withLifted mapLifting mapProgram) pureHost 8 "map-cells"
      [closure "tag" [.sym "a"], cells] = .value tagged := rfl

/-- The lifted relation, given only the captured value, answers the same. -/
theorem map_lifted_answer :
    Closures.apply (withLifted mapLifting mapProgram) pureHost 8 "map-cells/tag"
      ([.sym "a"] ++ [cells]) = .value tagged := rfl

/-- The same lifted relation serves another captured value. -/
theorem map_lifted_other_value :
    Closures.apply (withLifted mapLifting mapProgram) pureHost 8 "map-cells/tag"
      [.sym "b", .expr [.sym "Cons", .lit "1", .sym "Nil"]] =
      .value (.expr [.sym "Cons", .expr [.sym "Tagged", .sym "b", .lit "1"], .sym "Nil"]) :=
  rfl

/-- The theorem's instance for this program and every captured value. -/
theorem map_square (c : Term) (n : Nat) (vs : List Term)
    (h : Closures.apply (withLifted mapLifting mapProgram) pureHost n "map-cells"
      (closure "tag" [c] :: vs) ≠ .exhausted) :
    Closures.apply (withLifted mapLifting mapProgram) pureHost (n + 2) "map-cells/tag"
      (c :: vs) =
      Closures.apply (withLifted mapLifting mapProgram) pureHost n "map-cells"
        (closure "tag" [c] :: vs) :=
  apply_lifted_eq mapLifting map_lifts (cs := [c]) rfl n vs h

/-! ## A closure that escapes -/

/-- `(keep $k $x) = (Kept $k ($k $x))`: the closure is returned as data. -/
private def keepEquation : Equation :=
  equation "keep" "keep" [.var "k", .var "x"]
    (.expr [.sym "Kept", .var "k", .expr [.var "k", .var "x"]])

private def keepProgram : Program := [tagEquation, keepEquation]

private def keepLifting : Lifting :=
  { source := "keep", lifted := "keep/tag", callee := "tag", holes := ["h"] }

/-- The lifted relation rebuilds the escaping closure. -/
theorem keep_answers_agree :
    Closures.apply (withLifted keepLifting keepProgram) pureHost 6 "keep"
        [closure "tag" [.sym "a"], .lit "1"] =
      .value (.expr [.sym "Kept", closure "tag" [.sym "a"],
        .expr [.sym "Tagged", .sym "a", .lit "1"]]) ∧
    Closures.apply (withLifted keepLifting keepProgram) pureHost 6 "keep/tag"
        [.sym "a", .lit "1"] =
      .value (.expr [.sym "Kept", closure "tag" [.sym "a"],
        .expr [.sym "Tagged", .sym "a", .lit "1"]]) := ⟨rfl, rfl⟩

/-! ## Negative controls -/

/-- `(pick (partial tag (list a))) = yes` and `(pick $k) = no`: the first
equation reads the captured value. -/
private def pickProgram : Program :=
  [equation "pick-a" "pick" [closure "tag" [.sym "a"]] (.sym "yes"),
   equation "pick-any" "pick" [.var "k"] (.sym "no")]

private def pickLifting : Lifting :=
  { source := "pick", lifted := "pick/tag", callee := "tag", holes := ["h"] }

/-- An equation that matches the closure against a pattern is outside the
lifting's hypotheses. -/
theorem pick_not_lifts : ¬ Lifts pickLifting pickProgram pureHost := by
  intro h
  obtain ⟨k, rest, hp, _⟩ := h.equations
    (equation "pick-a" "pick" [closure "tag" [.sym "a"]] (.sym "yes"))
    (by simp [pickProgram]) rfl
  simp [equation, closure] at hp

/-- Without that hypothesis the square does not close: the source call
answers `yes` and the lifted call answers `no`. -/
theorem inspection_breaks_lifting :
    Closures.apply (withLifted pickLifting pickProgram) pureHost 4 "pick"
        [closure "tag" [.sym "a"]] = .value (.sym "yes") ∧
    Closures.apply (withLifted pickLifting pickProgram) pureHost 4 "pick/tag"
        [.sym "a"] = .value (.sym "no") := ⟨rfl, rfl⟩

/-- `(again $k) = (let $k (partial tag (list b)) ($k z))` binds the closure
parameter again. -/
private def againProgram : Program :=
  [tagEquation,
   equation "again" "again" [.var "k"]
     (.expr [.sym "let", .var "k",
       .expr [.sym "partial", .sym "tag", .list [.sym "b"]],
       .expr [.var "k", .sym "z"]])]

private def againLifting : Lifting :=
  { source := "again", lifted := "again/tag", callee := "tag", holes := ["h"] }

/-- A body whose `let` binds the closure parameter is not clean. -/
theorem again_not_clean :
    ¬ Clean againLifting "k" (.expr [.sym "let", .var "k",
      .expr [.sym "partial", .sym "tag", .list [.sym "b"]],
      .expr [.var "k", .sym "z"]]) := by
  intro h
  cases h with
  | expr hsp _ =>
    obtain ⟨x, e, b, heq, hxk⟩ := hsp.1 rfl
    simp only [List.cons.injEq, Term.var.injEq] at heq
    exact hxk heq.2.1.symm

/-- Without cleanliness the square does not close: the source rebinds the
closure and answers with the new one, the lifted call fails. -/
theorem rebinding_breaks_lifting :
    Closures.apply (withLifted againLifting againProgram) pureHost 6 "again"
        [closure "tag" [.sym "a"]] =
      .value (.expr [.sym "Tagged", .sym "b", .sym "z"]) ∧
    Closures.apply (withLifted againLifting againProgram) pureHost 6 "again/tag"
        [.sym "a"] = .failure := ⟨rfl, rfl⟩

end Mettapedia.GSLT.LanguageDef.DeterministicEquations.ClosureSpecialization.Controls
