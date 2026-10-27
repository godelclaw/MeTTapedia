import Mettapedia.Algorithms.Compression.ScopedGuidance
import Mettapedia.Algorithms.Compression.CostedArtifact

/-!
# Finite variable and contextual-parameter choices

This instantiates guided refinement with variables at their actual context
positions and declared metavariables applied only to bound variables. All
sort-preserving spines are enumerated; the existing scoped matcher then
refuses repeated arguments or references outside the chosen dependency map.
No ordinary variable is mistaken for an object-language bound dependency.
-/

set_option autoImplicit false

namespace Mettapedia.Algorithms.Compression.ScopedChoices

open Mettapedia.OSLF.Binding

variable {S : Signature} {M : List (MetaArity S)} [DecidableEq S.Srt]

def positions : (context : Ctx S) → (sort : S.Srt) → List (Var context sort)
  | [], _ => []
  | head :: tail, sort =>
      (if same : head = sort then
        [cast (congrArg (fun result => Var (head :: tail) result) same) .zero] else []) ++
        (positions tail sort).map Var.succ

theorem positions_complete : ∀ (context : Ctx S) (sort : S.Srt) (position : Var context sort),
    position ∈ positions context sort
  | [], _, position => nomatch position
  | head :: tail, sort, position => by
      cases position with
      | zero => simp [positions]
      | succ earlier =>
          exact List.mem_append_right _ (List.mem_map.mpr ⟨earlier, positions_complete tail sort earlier, rfl⟩)

def spines (bound ordinary : Ctx S) : (dependencies : Ctx S) →
    List (Args (withMetas S M) (dependencies.map (fun sort => ([], sort))) (bound ++ ordinary))
  | [] => [.nil]
  | sort :: rest => (positions bound sort).flatMap fun position =>
      (spines bound ordinary rest).map fun tail =>
        .cons (.var (injPrefix (Γ := ordinary) bound position)) tail

def chosenSpine (bound ordinary : Ctx S) : (dependencies : Ctx S) →
    Ren S dependencies bound →
      Args (withMetas S M) (dependencies.map (fun sort => ([], sort))) (bound ++ ordinary)
  | [], _ => .nil
  | _ :: rest, choose =>
      .cons (.var (injPrefix (Γ := ordinary) bound (choose _ .zero)))
        (chosenSpine bound ordinary rest (fun sort position => choose sort (.succ position)))

theorem chosenSpine_present (bound ordinary : Ctx S) :
    ∀ (dependencies : Ctx S) (choose : Ren S dependencies bound),
      chosenSpine (M := M) bound ordinary dependencies choose ∈ spines bound ordinary dependencies
  | [], _ => List.mem_singleton_self _
  | sort :: rest, choose =>
      List.mem_flatMap.mpr ⟨choose sort .zero, positions_complete _ _ _,
        List.mem_map.mpr ⟨chosenSpine bound ordinary rest (fun s v => choose s (.succ v)),
          chosenSpine_present bound ordinary rest _, rfl⟩⟩

def parameterChoices (bound ordinary : Ctx S) (sort : S.Srt) :
    List (Term (withMetas S M) (bound ++ ordinary) sort) :=
  (List.finRange M.length).flatMap fun index =>
    if same : (M.get index).2 = sort then
      (spines (M := M) bound ordinary (M.get index).1).map fun arguments =>
        cast (congrArg (fun result => Term (withMetas S M) (bound ++ ordinary) result) same)
          (.op (.inr (.mk index)) arguments)
    else []

def leaves (ordinary : Ctx S) : ScopedGuidance.LeafChoices S M ordinary :=
  fun bound sort => (positions (bound ++ ordinary) sort).map (Term.var (S := withMetas S M)) ++
    parameterChoices (M := M) bound ordinary sort

theorem variable_present (ordinary bound : Ctx S) (sort : S.Srt)
    (position : Var (bound ++ ordinary) sort) :
    Term.var (S := withMetas S M) position ∈ leaves (M := M) ordinary bound sort :=
  List.mem_append_left _ (List.mem_map.mpr ⟨position, positions_complete _ _ _, rfl⟩)

theorem parameter_present (ordinary bound : Ctx S) (index : Fin M.length)
    (arguments : Args (withMetas S M) ((M.get index).1.map (fun sort => ([], sort))) (bound ++ ordinary))
    (present : arguments ∈ spines bound ordinary (M.get index).1) :
    Term.op (S := withMetas S M) (.inr (.mk index)) arguments ∈ leaves ordinary bound (M.get index).2 := by
  apply List.mem_append_right
  apply List.mem_flatMap.mpr
  refine ⟨index, List.mem_finRange _, ?_⟩
  rw [dif_pos rfl]
  exact List.mem_map.mpr ⟨arguments, present, rfl⟩

/-- Moving capture checks into traversal preserves the exact checked
refinement, including tie behavior and any complete encoded-cost function. -/
theorem checked_refinement_eq_late {Artifact : Type}
    [opDec : ∀ sort, DecidableEq (S.Op sort)]
    (ordinary bound : Ctx S) {sort : S.Srt} (depth : Nat)
    (before : MAcc S M ordinary) (source : Term S (bound ++ []) sort)
    (propose : Term (withMetas S M) (bound ++ ordinary) sort × MAcc S M ordinary → Artifact)
    (valid : Artifact → Bool) (cost : Artifact → Nat) (current : Artifact) :
    CostedArtifact.refine valid cost current
      ((ScopedGuidance.terms (leaves ordinary) depth bound before source).map propose) =
    CostedArtifact.refine valid cost current
      (((ScopedGuidance.shapes (leaves ordinary) depth bound source).filterMap fun pattern =>
        (smatchAtT bound before pattern source).map (pattern, ·)).map propose) := by
  rw [ScopedGuidance.terms_eq_late]

end Mettapedia.Algorithms.Compression.ScopedChoices
