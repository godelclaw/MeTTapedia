import Mettapedia.Algorithms.Compression.ScopedTemplates

/-!
# Factoring scoped occurrence forests

A proposal replaces disjoint source occurrences by calls to one scoped
template. Matching and expansion are the existing shared algorithms. A later
whole-artifact checker charges the signature, template, captures and residuals;
this reconstruction law does not substitute a node-count cost model.
-/

set_option autoImplicit false

namespace Mettapedia.Algorithms.Compression.ScopedFactor

open Mettapedia.OSLF.Binding

variable {S : Signature} {M : List (MetaArity S)} {ordinary : Ctx S}
variable {arity : List (List S.Srt × S.Srt)} {Origin : Type}

inductive Occurrence (S : Signature) (M : List (MetaArity S))
    (ordinary : Ctx S) (arity : List (List S.Srt × S.Srt)) (Origin : Type) where
  | raw : Origin → Args S arity [] → Occurrence S M ordinary arity Origin
  | call : Origin → MAcc S M ordinary → Occurrence S M ordinary arity Origin

variable [DecidableEq S.Srt]
variable [opDec : ∀ sort, DecidableEq (S.Op sort)]

def factorOne (pattern : Args (withMetas S M) arity ordinary)
    (source : Origin × Args S arity []) : Occurrence S M ordinary arity Origin :=
  match smatchA emptyMAcc pattern source.2 with
  | none => .raw source.1 source.2
  | some captures => .call source.1 captures

def restoreOne (pattern : Args (withMetas S M) arity ordinary) :
    Occurrence S M ordinary arity Origin → Option (Origin × Args S arity [])
  | .raw origin source => some (origin, source)
  | .call origin captures => (ScopedTemplates.expandAtA [] captures pattern).map (origin, ·)

theorem restore_factorOne (pattern : Args (withMetas S M) arity ordinary)
    (source : Origin × Args S arity []) :
    restoreOne pattern (factorOne pattern source) = some source := by
  cases found : smatchA (emptyMAcc : MAcc S M ordinary) pattern source.2 with
  | none => simp [factorOne, restoreOne, found]
  | some captures =>
      have expanded := ScopedTemplates.matched_expandsAtA [] emptyMAcc captures captures
        pattern source.2 found (MAccLe.refl captures)
      simp [factorOne, restoreOne, found, expanded]

def factor (pattern : Args (withMetas S M) arity ordinary)
    (sources : List (Origin × Args S arity [])) : List (Occurrence S M ordinary arity Origin) :=
  sources.map (factorOne pattern)

def restore (pattern : Args (withMetas S M) arity ordinary)
    (items : List (Occurrence S M ordinary arity Origin)) : Option (List (Origin × Args S arity [])) :=
  items.mapM (restoreOne pattern)

/-- Origins, order and duplicate occurrences survive independently of whether
the supported matcher accepts a particular source. No total completion is used. -/
theorem restore_factor (pattern : Args (withMetas S M) arity ordinary)
    (sources : List (Origin × Args S arity [])) :
    restore pattern (factor pattern sources) = some sources := by
  induction sources with
  | nil => rfl
  | cons first rest ih =>
      simp only [factor, List.map_cons, restore, List.mapM_cons, restore_factorOne]
      have tail := ih
      simp only [factor, restore] at tail
      simp only [Bind.bind, Option.bind, tail]
      rfl

theorem factor_length (pattern : Args (withMetas S M) arity ordinary)
    (sources : List (Origin × Args S arity [])) :
    (factor pattern sources).length = sources.length := by simp [factor]

/-- The whole rule forest is matched at once. Separate independent component
matches are not substituted for its one shared accumulator. -/
theorem call_records_shared_match (pattern : Args (withMetas S M) arity ordinary)
    (source : Origin × Args S arity []) (origin : Origin) (captures : MAcc S M ordinary)
    (called : factorOne pattern source = .call origin captures) :
    origin = source.1 ∧ smatchA emptyMAcc pattern source.2 = some captures := by
  unfold factorOne at called
  cases found : smatchA (emptyMAcc : MAcc S M ordinary) pattern source.2 with
  | none => simp [found] at called
  | some actual =>
      simp only [found, Occurrence.call.injEq] at called
      exact ⟨called.1.symm, congrArg some called.2⟩

end Mettapedia.Algorithms.Compression.ScopedFactor
